// おぼろ将棋 中継サーバー(Cloudflare Workers + Durable Objects)
// ・1つのルーム(4文字のルームID)ごとに、Durable Object「Room」が1つ動く。
// ・ルームの状態と、すべての駒の本当の種類は、このサーバーだけが持つ。
//   各プレイヤーには「公開情報+自分の駒の正体」だけを送り、相手の伏せ駒の正体は送らない。
// ・指し手は、サーバーが本当の駒でルールどおりか検査してから反映する。
// ・プレイヤーの端末どうしは直接つながらないので、相手にIPアドレスは見えない。
import { DurableObject } from "cloudflare:workers";

/* =========================================================
   1. ルール(index.html のゲーム本体と同じ内容。ルールを変える時は、両方を同じように直す)
   ========================================================= */
const N = 5;
const TYPES = ['K', 'R', 'B', 'G', 'S', 'P'];
const NAME = {K: '玉', R: '飛', B: '角', G: '金', S: '銀', P: '歩'};
const PROM_NAME = {R: '龍', B: '馬', S: '全', P: 'と'};
const PROMOTABLE = {R: true, B: true, S: true, P: true};
const ZONE_DEPTH = 1, SETUP_ROWS = 2;
const SIDE_NAME = ['先手', '後手'];
const fwd = o => (o === 0 ? -1 : 1);
const inBoard = (r, c) => r >= 0 && r < N && c >= 0 && c < N;
const inZone = (o, r) => (o === 0 ? r < ZONE_DEPTH : r >= N - ZONE_DEPTH);
const isLastRank = (o, r) => (o === 0 ? r === 0 : r === N - 1);
const inSetupZone = (o, r) => (o === 0 ? r >= N - SETUP_ROWS : r < SETUP_ROWS);
const isDeadSquare = (type, owner, r) => type === 'P' && isLastRank(owner, r);
const DIRS = {
  KING: [[1, -1], [1, 0], [1, 1], [0, -1], [0, 1], [-1, -1], [-1, 0], [-1, 1]],
  GOLD: [[1, -1], [1, 0], [1, 1], [0, -1], [0, 1], [-1, 0]],
  SILVER: [[1, -1], [1, 0], [1, 1], [-1, -1], [-1, 1]],
  PAWN: [[1, 0]],
  DIAG: [[1, 1], [1, -1], [-1, 1], [-1, -1]],
  ORTH: [[1, 0], [-1, 0], [0, 1], [0, -1]],
};
const RULES = {K: {steps: DIRS.KING}, G: {steps: DIRS.GOLD}, S: {steps: DIRS.SILVER}, P: {steps: DIRS.PAWN}, B: {slides: DIRS.DIAG}, R: {slides: DIRS.ORTH}};
const PROMOTED_RULES = {S: {steps: DIRS.GOLD}, P: {steps: DIRS.GOLD}, B: {slides: DIRS.DIAG, steps: DIRS.ORTH}, R: {slides: DIRS.ORTH, steps: DIRS.DIAG}};
const ruleOf = (t, pr) => (pr ? PROMOTED_RULES[t] : RULES[t]);
const pname = p => (p.promoted ? PROM_NAME[p.trueType] : NAME[p.trueType]);

function movesFor(board, r, c, type, promoted, owner) {
  const rule = ruleOf(type, promoted), out = [], f = fwd(owner);
  if (!rule) return out;
  for (const [a, b] of rule.steps || []) {
    const nr = r + a * f, nc = c + b;
    if (!inBoard(nr, nc)) continue;
    const t = board[nr][nc];
    if (!t || t.owner !== owner) out.push([nr, nc]);
  }
  for (const [a, b] of rule.slides || []) {
    let nr = r + a * f, nc = c + b;
    while (inBoard(nr, nc)) {
      const t = board[nr][nc];
      if (!t) out.push([nr, nc]);
      else { if (t.owner !== owner) out.push([nr, nc]); break; }
      nr += a * f; nc += b;
    }
  }
  return out;
}
const canMakeMove = (board, from, to, type, promoted, owner) => movesFor(board, from[0], from[1], type, promoted, owner).some(([r, c]) => r === to[0] && c === to[1]);
const typesThatCanMake = (board, from, to, owner) => TYPES.filter(t => canMakeMove(board, from, to, t, false, owner));
function eachPiece(g, fn) { for (let r = 0; r < N; r++) for (let c = 0; c < N; c++) if (g.board[r][c]) fn(g.board[r][c], r, c); }
function reveal(p) { p.revealed = true; p.candidates = [p.trueType]; }
// 公開情報だけを使って、伏せ駒の候補を絞る(矛盾しない割り当てを全列挙)
function propagate(g, side) {
  const hidden = [], known = [...g.capturedOrig[side]];
  eachPiece(g, p => { if (p.orig !== side) return; if (p.revealed) known.push(p.trueType); else hidden.push(p); });
  if (!hidden.length) return;
  const remaining = TYPES.filter(t => !known.includes(t));
  const possible = hidden.map(() => new Set());
  const used = remaining.map(() => false), cur = [];
  (function rec(k) {
    if (k === hidden.length) { cur.forEach((t, i) => possible[i].add(t)); return; }
    for (let i = 0; i < remaining.length; i++) {
      if (used[i] || !hidden[k].candidates.includes(remaining[i])) continue;
      used[i] = true; cur.push(remaining[i]); rec(k + 1); cur.pop(); used[i] = false;
    }
  })(0);
  if (possible.some(s => s.size === 0)) return;
  hidden.forEach((p, i) => { p.candidates = TYPES.filter(t => possible[i].has(t)); if (p.candidates.length === 1) p.revealed = true; });
}
function promoOptions(p, from, to) {
  if (p.promoted || !PROMOTABLE[p.trueType]) return [false];
  if (!(inZone(p.owner, from[0]) || inZone(p.owner, to[0]))) return [false];
  if (isDeadSquare(p.trueType, p.owner, to[0])) return [true];
  return [false, true];
}
function legalMoves(g, side) {
  const out = [];
  eachPiece(g, (p, r, c) => {
    if (p.owner !== side) return;
    for (const to of movesFor(g.board, r, c, p.trueType, p.promoted, side)) for (const pr of promoOptions(p, [r, c], to)) out.push({kind: 'move', from: [r, c], to, promote: pr});
  });
  for (const t of TYPES) if (g.hands[side][t] > 0) for (let r = 0; r < N; r++) for (let c = 0; c < N; c++) if (!g.board[r][c] && !isDeadSquare(t, side, r)) out.push({kind: 'drop', ptype: t, to: [r, c]});
  return out;
}
function ownPawnInFile(g, side, c, except) {
  for (let r = 0; r < N; r++) { const q = g.board[r][c]; if (q && q !== except && q.owner === side && q.trueType === 'P' && !q.promoted) return q; }
  return null;
}
const blankHand = () => ({K: 0, R: 0, B: 0, G: 0, S: 0, P: 0});
// 双方の配置から対局を始める。駒のidは「陣営ごとにマス番号の小さい順」(index.html の棋譜の再現と同じ決め方)
function newGame(layouts) {
  const g = {board: Array.from({length: N}, () => Array(N).fill(null)), hands: [blankHand(), blankHand()], turn: 0, ply: 0, capturedOrig: [[], []],
    lastMove: null, winner: null, reason: '', log: '', note: '', moves: [], nextId: 13, over: false};
  for (const s of [0, 1]) {
    const lay = layouts[s], sqs = Object.values(lay).sort((a, b) => a - b);
    for (const t of TYPES) { const q = lay[t]; g.board[Math.floor(q / N)][q % N] = {id: s * 6 + sqs.indexOf(q) + 1, owner: s, trueType: t, candidates: [...TYPES], revealed: false, promoted: false, orig: s}; }
  }
  propagate(g, 0); propagate(g, 1);
  return g;
}
// 指し手を検査して反映する。おかしければ理由の文字列を返す
function applyMove(g, m) {
  if (g.over) return 'over';
  const me = g.turn, B = g.board;
  let note = '';
  if (m.kind === 'move') {
    const [fr, fc] = m.from, [tr, tc] = m.to, p = B[fr][fc], t = B[tr][tc];
    if (!p || p.owner !== me) return 'nopiece';
    if (!canMakeMove(B, m.from, m.to, p.trueType, p.promoted, me)) return 'illegal';
    if (!promoOptions(p, m.from, m.to).includes(!!m.promote)) return 'promote';
    if (!p.revealed) {   // 動きから候補を絞る(公開情報)
      const possible = typesThatCanMake(B, m.from, m.to, me);
      let c = p.candidates.filter(x => possible.includes(x));
      if (!m.promote) c = c.filter(x => !isDeadSquare(x, me, tr));
      p.candidates = c;
    }
    let capTxt = '';
    if (t) {
      const wasHidden = !t.revealed;
      reveal(t);
      if (t.orig >= 0) g.capturedOrig[t.orig].push(t.trueType);
      if (t.trueType === 'K') { g.over = true; g.winner = me; g.reason = `${SIDE_NAME[me]}が玉を取りました${wasHidden ? '(正体不明のままの玉でした)' : ''}`; }
      else g.hands[me][t.trueType]++;
      capTxt = `${NAME[t.trueType]}を取った`;
      note = `取った駒の正体:${NAME[t.trueType]}${t.promoted ? '(' + pname(t) + ')' : ''}`;
    }
    B[tr][tc] = p; B[fr][fc] = null;
    if (m.promote) { p.promoted = true; reveal(p); }
    propagate(g, 0); propagate(g, 1);
    g.log = `${SIDE_NAME[me]}の${p.revealed ? pname(p) : '伏せた駒'}が${capTxt || '移動'}${m.promote ? '(成り)' : ''}`;
    g.moves.push({k: 'm', f: fr * N + fc, t: tr * N + tc, p: m.promote ? 1 : 0});
  } else if (m.kind === 'drop') {
    const [tr, tc] = m.to;
    if (!TYPES.includes(m.ptype) || !(g.hands[me][m.ptype] > 0)) return 'nohand';
    if (B[tr][tc] || isDeadSquare(m.ptype, me, tr)) return 'illegal';
    const p = {id: g.nextId++, owner: me, trueType: m.ptype, candidates: [m.ptype], revealed: true, promoted: false, orig: -1};
    g.hands[me][m.ptype]--; B[tr][tc] = p;
    if (m.ptype === 'P') {   // 二歩:同じ筋に自分の歩があれば反則負け(伏せていた歩も公開する)
      const q = ownPawnInFile(g, me, tc, p);
      if (q) { reveal(q); g.over = true; g.winner = 1 - me; g.reason = `${SIDE_NAME[me]}の二歩(反則)。同じ筋に伏せていた歩がありました`; }
    }
    propagate(g, 0); propagate(g, 1);
    g.log = `${SIDE_NAME[me]}が${NAME[m.ptype]}を打った`;
    g.moves.push({k: 'd', y: m.ptype, t: tr * N + tc});
  } else return 'kind';
  g.note = note;
  g.lastMove = {from: m.kind === 'move' ? m.from : null, to: m.to};
  g.ply++;
  if (!g.over) {
    g.turn = 1 - me;
    if (!legalMoves(g, g.turn).length) { g.over = true; g.winner = me; g.reason = `${SIDE_NAME[g.turn]}は指せる手がありません`; }
  }
  return null;
}
// プレイヤーに見せてよい形(公開情報)。伏せ駒の正体は null にする
function publicView(g) {
  const board = [];
  for (let r = 0; r < N; r++) for (let c = 0; c < N; c++) {
    const p = g.board[r][c];
    board.push(p ? {id: p.id, owner: p.owner, trueType: p.revealed ? p.trueType : null, candidates: [...p.candidates], revealed: !!p.revealed, promoted: !!p.promoted, orig: p.orig} : null);
  }
  return {board, hands: g.hands, turn: g.turn, ply: g.ply, capturedOrig: g.capturedOrig, lastMove: g.lastMove, winner: g.winner, reason: g.reason,
    log: g.log, note: g.note, moves: g.moves, pending: null, nextId: g.nextId, over: g.over};
}
function mineFor(g, seat) {   // 自分の伏せ駒の正体(本人にだけ送る)
  const m = {}; eachPiece(g, p => { if (p.owner === seat && !p.revealed) m[p.id] = p.trueType; }); return m;
}

/* =========================================================
   2. 入力の検査
   ========================================================= */
const isInt = (v, lo, hi) => Number.isInteger(v) && v >= lo && v <= hi;
const cleanName = v => (typeof v === 'string' ? v.replace(/[<>&"'`]/g, '').trim().slice(0, 8) : '');
const PALETTE_N = 6;
const clampCol = v => (isInt(v, 0, PALETTE_N - 1) ? v : 0);
const sqOk = a => Array.isArray(a) && a.length === 2 && isInt(a[0], 0, N - 1) && isInt(a[1], 0, N - 1);
const rid = () => crypto.randomUUID().replace(/-/g, '').slice(0, 12);
function cleanLayout(lay, side) {
  if (!lay || typeof lay !== 'object') return null;
  const o = {};
  for (const t of TYPES) { if (!isInt(lay[t], 0, N * N - 1) || !inSetupZone(side, Math.floor(lay[t] / N))) return null; o[t] = lay[t]; }
  return new Set(Object.values(o)).size === 6 ? o : null;
}

/* =========================================================
   3. ルーム(Durable Object)
   ========================================================= */
const MAX_MEMBERS = 12, MAX_SPEC = 8;
const IDLE_MS = 7 * 24 * 3600 * 1000;   // 7日間 使われなかったルームは消す

export class Room extends DurableObject {
  constructor(ctx, env) {
    super(ctx, env);
    this.room = null;
    this.rate = new WeakMap();
    ctx.blockConcurrencyWhile(async () => { this.room = (await ctx.storage.get('room')) || null; });
    // 「ping」には、ルームを起こさずに「pong」と自動で返す(待機中の費用を抑える)
    ctx.setWebSocketAutoResponse(new WebSocketRequestResponsePair('ping', 'pong'));
  }
  async fetch(req) {
    if (req.headers.get('Upgrade') !== 'websocket') return new Response('WebSocket で接続してください', {status: 426});
    const url = new URL(req.url);
    const pair = new WebSocketPair();
    const [client, server] = Object.values(pair);
    this.ctx.acceptWebSocket(server);
    server.serializeAttachment({code: url.searchParams.get('room') || '', create: url.searchParams.get('create') === '1', ok: false});
    return new Response(null, {status: 101, webSocket: client});
  }
  // ---- 送受信の道具 ----
  send(ws, m) { try { ws.send(JSON.stringify(m)); } catch (e) {} }
  fail(ws, e) { this.send(ws, {t: 'err', e}); try { ws.close(4000, e); } catch (_) {} }
  sockets(except) { return this.ctx.getWebSockets().filter(s => s !== except && (s.readyState === undefined || s.readyState === 1)); }
  att(ws) { try { return ws.deserializeAttachment() || {}; } catch (e) { return {}; } }
  onlineToks(except) { const s = new Set(); for (const w of this.sockets(except)) { const a = this.att(w); if (a.ok && !a.spec) s.add(a.tok); } return s; }
  async save() {
    this.room.at = Date.now();
    await this.ctx.storage.put('room', this.room);
    if (!(await this.ctx.storage.getAlarm())) await this.ctx.storage.setAlarm(Date.now() + IDLE_MS);
  }
  // 受け取り手ごとの部屋の状態(合言葉 tok は外に出さない)
  view(a, except) {
    const R = this.room, on = this.onlineToks(except);
    const mem = t => R.members.find(x => x.tok === t);
    const seat = a.spec ? -1 : R.seats.indexOf(a.tok);
    const g = R.game;
    return {
      phase: R.phase, gen: R.gen, spec: R.spec,
      seats: R.seats.map(t => { const x = t && mem(t); return x ? {n: x.name, c: x.col, on: on.has(t)} : null; }),
      mem: R.members.map(x => ({n: x.name, c: x.col, on: on.has(x.tok), seat: R.seats.indexOf(x.tok)})),
      nspec: this.sockets(except).filter(w => { const b = this.att(w); return b.ok && b.spec; }).length,
      me: {seat, spec: !!a.spec},
      ready: [!!R.layouts[0], !!R.layouts[1]],
      game: g ? publicView(g) : null,
      mine: g && !g.over && seat >= 0 ? mineFor(g, seat) : null,
      final: g && g.over ? {layouts: R.layouts, moves: g.moves} : null
    };
  }
  push(except, only) {   // 全員(または1人)に、部屋の状態を送る
    for (const w of only ? [only] : this.sockets(except)) { const a = this.att(w); if (a.ok) this.send(w, {t: 'room', d: this.view(a, except)}); }
  }

  // ---- 受信 ----
  async webSocketMessage(ws, raw) {
    if (typeof raw !== 'string' || raw.length > 4000) { try { ws.close(1009, 'too big'); } catch (e) {} return; }
    const now = Date.now(), r = this.rate.get(ws) || {win: 0, cnt: 0};   // 送信が多すぎる相手は無視し、さらに続けば切断する
    if (now - r.win > 1000) { r.win = now; r.cnt = 0; }
    this.rate.set(ws, r);
    if (++r.cnt > 20) { if (r.cnt > 60) { try { ws.close(1008, 'too many'); } catch (e) {} } return; }
    let m; try { m = JSON.parse(raw); } catch (e) { return; }
    if (!m || typeof m !== 'object') return;
    const a = this.att(ws);
    if (!a.ok) { if (m.t === 'hello') await this.hello(ws, a, m); return; }
    if (!this.room) { this.fail(ws, 'noroom'); return; }
    if (m.t === 'sync') { this.push(null, ws); return; }
    if (a.spec) { if (m.t === 'leave') { try { ws.close(1000, 'bye'); } catch (e) {} } return; }
    const R = this.room, seat = R.seats.indexOf(a.tok), me = R.members.find(x => x.tok === a.tok);
    if (!me) { this.fail(ws, 'closed'); return; }
    switch (m.t) {
      case 'me':
        if (R.phase !== 'lobby') return;
        if ('name' in m) me.name = cleanName(m.name);
        if ('col' in m) me.col = clampCol(m.col);
        break;
      case 'seat': {
        if (R.phase !== 'lobby') return;
        const n = m.n;
        if (n === -1) R.seats = R.seats.map(t => (t === a.tok ? '' : t));
        else if ((n === 0 || n === 1) && (!R.seats[n] || R.seats[n] === a.tok)) { R.seats = R.seats.map(t => (t === a.tok ? '' : t)); R.seats[n] = a.tok; }
        else return;
        break;
      }
      case 'start':
      case 'again': {
        if (seat < 0 || !(R.seats[0] && R.seats[1])) return;
        if (m.t === 'start' ? R.phase !== 'lobby' : R.phase !== 'over') return;
        if (m.t === 'again') R.seats = [R.seats[1], R.seats[0]];   // もう一局は、先手と後手を入れ替える
        const x = R.members.find(y => y.tok === R.seats[0]), y = R.members.find(z => z.tok === R.seats[1]);
        if (x && y && x.col === y.col) y.col = (y.col + 1) % PALETTE_N;   // 色が同じなら後手側をずらす
        Object.assign(R, {phase: 'setup', gen: R.gen + 1, layouts: [null, null], game: null});
        break;
      }
      case 'setup': {
        if (R.phase !== 'setup' || seat < 0 || R.layouts[seat]) return;
        const lay = cleanLayout(m.layout, seat);
        if (!lay) { this.send(ws, {t: 'err', e: 'badsetup'}); return; }
        R.layouts[seat] = lay;
        if (R.layouts[0] && R.layouts[1]) { R.game = newGame(R.layouts); R.phase = 'play'; }
        break;
      }
      case 'move':
      case 'drop': {
        const g = R.game;
        if (R.phase !== 'play' || !g || seat !== g.turn) { this.send(ws, {t: 'err', e: 'notyourturn'}); this.push(null, ws); return; }
        let mv = null;
        if (m.t === 'move' && sqOk(m.from) && sqOk(m.to)) mv = {kind: 'move', from: m.from.slice(), to: m.to.slice(), promote: !!m.promote};
        if (m.t === 'drop' && sqOk(m.to) && TYPES.includes(m.ptype)) mv = {kind: 'drop', ptype: m.ptype, to: m.to.slice()};
        const bad = mv ? applyMove(g, mv) : 'shape';
        if (bad) { this.send(ws, {t: 'err', e: 'badmove'}); this.push(null, ws); return; }   // 正本で上書きしてもらう
        if (g.over) R.phase = 'over';
        break;
      }
      case 'resign': {
        const g = R.game;
        if (R.phase !== 'play' || !g || seat < 0) return;
        g.over = true; g.winner = 1 - seat; g.reason = `${SIDE_NAME[seat]}が投了しました`; g.note = '';
        R.phase = 'over';
        break;
      }
      case 'leave':
        if (R.phase === 'lobby') { R.members = R.members.filter(x => x.tok !== a.tok); R.seats = R.seats.map(t => (t === a.tok ? '' : t)); }
        await this.save(); this.push(ws);
        try { ws.close(1000, 'bye'); } catch (e) {}
        return;
      default: return;
    }
    await this.save();
    this.push();
  }
  async hello(ws, a, m) {
    const tok = typeof m.tok === 'string' && /^[0-9a-f]{16,64}$/.test(m.tok) ? m.tok : '';
    if (!tok) { this.fail(ws, 'closed'); return; }
    if (!this.room) {
      if (!a.create || !/^[A-Z0-9]{4}$/.test(a.code)) { this.fail(ws, 'noroom'); return; }
      this.room = {code: a.code, phase: 'lobby', gen: 0, spec: true, seats: ['', ''], members: [], layouts: [null, null], game: null, at: Date.now()};
    } else if (a.create) { this.fail(ws, 'exists'); return; }   // 同じIDのルームがもうある(作る側で別のIDを選び直す)
    const R = this.room;
    if (m.spec) {   // 観戦者:席を取らずに、公開情報だけを受け取る
      if (!R.spec) { this.fail(ws, 'nospec'); return; }
      const specs = this.sockets(ws).filter(w => { const b = this.att(w); return b.ok && b.spec; });
      if (specs.length >= MAX_SPEC) { this.fail(ws, 'full'); return; }
      ws.serializeAttachment({code: a.code, ok: true, spec: true, tok});
      this.send(ws, {t: 'welcome'});
      this.push();
      return;
    }
    let me = R.members.find(x => x.tok === tok);
    if (!me) {
      if (R.phase !== 'lobby') { this.fail(ws, 'playing'); return; }
      if (R.members.length >= MAX_MEMBERS) { this.fail(ws, 'full'); return; }
      me = {tok, name: cleanName(m.name), col: clampCol(m.col)};
      R.members.push(me);
    }
    for (const w of this.sockets(ws)) { const b = this.att(w); if (b.ok && !b.spec && b.tok === tok) { try { w.close(4001, 'replaced'); } catch (e) {} } }   // 同じ人が入り直した:古い接続を切る
    ws.serializeAttachment({code: a.code, ok: true, spec: false, tok});
    this.send(ws, {t: 'welcome'});
    await this.save();
    this.push();
  }
  async dropped(ws) {
    const a = this.att(ws);
    if (!a.ok || !this.room) return;
    const R = this.room;
    if (!a.spec && R.phase === 'lobby' && !this.onlineToks(ws).has(a.tok)) {   // 待合室で接続が切れた人は、一覧と席から外す
      R.members = R.members.filter(x => x.tok !== a.tok); R.seats = R.seats.map(t => (t === a.tok ? '' : t));
      await this.save();
    }
    this.push(ws);
  }
  async webSocketClose(ws, code) { try { ws.close(1000, 'bye'); } catch (e) {} await this.dropped(ws); }
  async webSocketError(ws) { await this.dropped(ws); }
  async alarm() {   // 長く使われていないルームを消す
    if (!this.room) return;
    if (Date.now() - (this.room.at || 0) > IDLE_MS && this.sockets().length === 0) { await this.ctx.storage.deleteAll(); this.room = null; }
    else await this.ctx.storage.setAlarm(Date.now() + IDLE_MS);
  }
}

/* =========================================================
   4. 入口(Worker)
   ========================================================= */
export default {
  async fetch(req, env) {
    const url = new URL(req.url);
    // ALLOWED_ORIGINS(カンマ区切り)を設定すると、そのサイトから開いたページだけが使える
    const allow = String(env.ALLOWED_ORIGINS || '').split(',').map(s => s.trim()).filter(Boolean);
    const origin = req.headers.get('Origin') || '';
    if (allow.length && origin && !allow.includes(origin)) return new Response('このサイトからは使えません', {status: 403});
    if (url.pathname === '/ws') {
      const code = url.searchParams.get('room') || '';
      if (!/^[A-Z0-9]{4}$/.test(code)) return new Response('ルームIDが正しくありません', {status: 400});
      return env.ROOMS.get(env.ROOMS.idFromName(code)).fetch(req);
    }
    if (url.pathname === '/') return new Response('おぼろ将棋 中継サーバー:動作中', {headers: {'content-type': 'text/plain; charset=utf-8'}});
    return new Response('見つかりません', {status: 404});
  }
};
