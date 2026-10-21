// おぼろ将棋 中継サーバー(Cloudflare Workers + Durable Objects)
// ・1つのルーム(4文字のルームID)ごとに、Durable Object「Room」が1つ動く。
// ・ルームの状態と、すべての駒の本当の種類は、このサーバーだけが持つ。
//   各プレイヤーには「公開情報+自分の駒の正体」だけを送り、相手の伏せ駒の正体は送らない。
// ・指し手は、サーバーが本当の駒でルールどおりか検査してから反映する。
// ・プレイヤーの端末どうしは直接つながらないので、相手にIPアドレスは見えない。
// ・ランダム対戦(レートあり)は、Durable Object「Lobby」(1つだけ)が待ち行列とレートを持つ。
//   組み合わせが決まると、Lobby がルームを作り(Room の /init)、終局したら Room が結果を Lobby に知らせる(/result)。
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
const hex = n => { const a = new Uint8Array(n); crypto.getRandomValues(a); return [...a].map(b => b.toString(16).padStart(2, '0')).join(''); };
const rint = n => { const a = new Uint32Array(1); crypto.getRandomValues(a); return a[0] % n; };
const CODE_CH = 'ABCDEFGHJKLMNPQRSTUVWXYZ23456789';   // 見間違えやすい I・O・0・1 は使わない(index.html と同じ)
const genCode = () => Array.from({length: 4}, () => CODE_CH[rint(CODE_CH.length)]).join('');
async function sha256(t) { const b = await crypto.subtle.digest('SHA-256', new TextEncoder().encode(t)); return [...new Uint8Array(b)].map(x => x.toString(16).padStart(2, '0')).join(''); }
const json = (o, status = 200) => new Response(JSON.stringify(o), {status, headers: {'content-type': 'application/json'}});
// 配置の時間切れ用:自陣2段にランダムに置く
function randomLayout(side) {
  const sq = []; for (let q = 0; q < N * N; q++) if (inSetupZone(side, Math.floor(q / N))) sq.push(q);
  for (let i = sq.length - 1; i > 0; i--) { const j = rint(i + 1); [sq[i], sq[j]] = [sq[j], sq[i]]; }
  const o = {}; TYPES.forEach((t, i) => { o[t] = sq[i]; }); return o;
}
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
// レート戦の持ち時間(切れたら負け。配置だけは時間切れでランダム配置にして対局を始める)
const SETUP_MS = 120 * 1000, MOVE_MS = 90 * 1000;
const REPORT_RETRY_MS = 15000, REPORT_TRIES = 20;

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
    const url = new URL(req.url);
    // Lobby からだけ届く(入口の Worker は /ws しかルームに渡さないので、外からは呼べない)
    if (url.pathname === '/init' && req.method === 'POST') return this.initRated(await req.json().catch(() => null));
    if (req.headers.get('Upgrade') !== 'websocket') return new Response('WebSocket で接続してください', {status: 426});
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
    await this.ctx.storage.setAlarm(this.nextAlarm());
  }
  // 次に起きる時刻:持ち時間の期限、結果の送り直し、どちらもなければ削除の確認
  nextAlarm() {
    const R = this.room, t = [Date.now() + IDLE_MS];
    if (R && R.deadline) t.push(R.deadline);
    if (R && R.rated && !R.rated.done && R.phase === 'over') t.push(R.rated.retry || Date.now() + 1000);
    return Math.min(...t);
  }
  // ---- レート戦 ----
  async initRated(d) {   // Lobby が組み合わせたルームを作る。席・名前・合言葉は Lobby が決めたもの
    const ok = d && /^[A-Z0-9]{4}$/.test(d.code) && typeof d.mid === 'string' && Array.isArray(d.players) && d.players.length === 2
      && d.players.every(p => p && /^[0-9a-f]{32}$/.test(p.tok) && Number.isFinite(p.r));
    if (!ok) return new Response('bad', {status: 400});
    if (this.room) return new Response('exists', {status: 409});   // このIDは使用中(Lobby が別のIDで作り直す)
    const [a, b] = d.players.map(p => ({tok: p.tok, name: cleanName(p.name), col: clampCol(p.col), r: Math.round(p.r)}));
    if (a.col === b.col) b.col = (b.col + 1) % PALETTE_N;
    this.room = {code: d.code, phase: 'setup', gen: 1, spec: true, seats: [a.tok, b.tok],
      members: [a, b].map(x => ({tok: x.tok, name: x.name, col: x.col})), layouts: [null, null], game: null, at: Date.now(),
      rated: {mid: d.mid, r: [a.r, b.r], nr: null, d: null, done: false, tries: 0, retry: 0}, auto: [false, false], deadline: Date.now() + SETUP_MS};
    await this.save();
    return new Response('ok');
  }
  timeUp() {   // 持ち時間が切れた
    const R = this.room;
    if (R.phase === 'setup') {   // 配置していない側はランダムに置いて、対局を始める
      for (const s of [0, 1]) if (!R.layouts[s]) { R.layouts[s] = randomLayout(s); R.auto[s] = true; }
      R.game = newGame(R.layouts); R.phase = 'play'; R.deadline = Date.now() + MOVE_MS;
    } else if (R.phase === 'play' && R.game && !R.game.over) {
      const g = R.game, s = g.turn;
      g.over = true; g.winner = 1 - s; g.reason = `${SIDE_NAME[s]}の時間切れ`; g.note = '';
      R.phase = 'over';
    } else R.deadline = 0;
  }
  async settle() {   // 終局したら持ち時間を止め、レート戦なら結果を Lobby に知らせる
    const R = this.room;
    if (!R || R.phase !== 'over') return;
    R.deadline = 0;
    const rt = R.rated;
    if (!rt || rt.done || (rt.retry && Date.now() < rt.retry)) return;
    let st = 0, j = null;
    try {
      const res = await this.env.LOBBY.get(this.env.LOBBY.idFromName('main')).fetch('https://lobby/result', {method: 'POST', body: JSON.stringify({mid: rt.mid, winner: R.game.winner})});
      st = res.status; if (res.ok) j = await res.json();
    } catch (e) { st = 0; }
    if (j && Array.isArray(j.r) && Array.isArray(j.d)) { rt.nr = j.r.map(Number); rt.d = j.d.map(Number); rt.done = true; rt.retry = 0; }
    else if (st === 404 || st === 400 || ++rt.tries >= REPORT_TRIES) { rt.done = true; rt.retry = 0; }   // 送り直しても無駄なので、あきらめる
    else rt.retry = Date.now() + REPORT_RETRY_MS;
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
      final: g && g.over ? {layouts: R.layouts, moves: g.moves} : null,
      rated: R.rated ? {r: R.rated.r, nr: R.rated.nr, d: R.rated.d, done: !!R.rated.done} : null,
      auto: R.auto || [false, false],
      deadline: R.deadline || 0, now: Date.now()
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
        if (R.rated) return;   // レート戦は1局だけ(もう一局はランダム対戦から)
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
        if (R.layouts[0] && R.layouts[1]) { R.game = newGame(R.layouts); R.phase = 'play'; if (R.rated) R.deadline = Date.now() + MOVE_MS; }
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
        else if (R.rated) R.deadline = Date.now() + MOVE_MS;   // 手番が替わったので、持ち時間を新しく数える
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
    await this.settle();
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
  async alarm() {   // 持ち時間の期限・結果の送り直し・長く使われていないルームの削除
    if (!this.room) return;
    const R = this.room, now = Date.now();
    let changed = false;
    if (R.rated && R.deadline && now >= R.deadline - 300) { this.timeUp(); changed = true; }
    if (R.rated && R.phase === 'over' && !R.rated.done) { await this.settle(); changed = true; }
    if (changed) { await this.save(); this.push(); return; }
    if (now - (R.at || 0) > IDLE_MS && this.sockets().length === 0) { await this.ctx.storage.deleteAll(); this.room = null; }
    else await this.ctx.storage.setAlarm(this.nextAlarm());
  }
}

/* =========================================================
   3b. ランダム対戦の待合所とレート(Durable Object「Lobby」。名前 'main' の1つだけを使う)
   ・端末は /mm に WebSocket でつなぎ、hi(プレイヤーID と鍵)→ q(待ち行列に入る)を送る。
   ・プレイヤーID(pid)は端末が作る。鍵(key)はハッシュだけを保存し、他人がそのIDのレートを使えないようにする。
   ・レートの近い人から組む。待つほど許す差を広げ、30秒ほどで誰とでも組む。
   ・組み合わせが決まったら、ルームを作り(Room の /init)、2人に match(ルームIDと合言葉)を送る。
   ・終局すると Room から /result が届き、イロレーティングで更新する(同じ対局は1回だけ数える)。
   ========================================================= */
const RATE0 = 1500;
const WIN0 = 150, WIN_STEP = 60, WIN_STEP_MS = 5000;   // 許すレート差:最初150、5秒ごとに+60
const MM_TICK_MS = 3000;
const PM_MS = 2 * 3600 * 1000;          // 組み合わせ済みの対局に戻れる時間(終局したら消す)
const MATCH_KEEP_MS = 3 * 24 * 3600 * 1000;
const kFactor = n => (n < 30 ? 32 : 16);   // 対局数が少ないうちは大きく動かす

export class Lobby extends DurableObject {
  constructor(ctx, env) {
    super(ctx, env);
    this.rate = new WeakMap();
    this.pairing = false; this.pairAgain = false;
    ctx.setWebSocketAutoResponse(new WebSocketRequestResponsePair('ping', 'pong'));
  }
  async fetch(req) {
    const url = new URL(req.url);
    // Room からだけ届く(入口の Worker は /mm しか Lobby に渡さないので、外からは呼べない)
    if (url.pathname === '/result' && req.method === 'POST') return this.result(await req.json().catch(() => null));
    if (req.headers.get('Upgrade') !== 'websocket') return new Response('WebSocket で接続してください', {status: 426});
    const pair = new WebSocketPair();
    const [client, server] = Object.values(pair);
    this.ctx.acceptWebSocket(server);
    server.serializeAttachment({ok: false});
    return new Response(null, {status: 101, webSocket: client});
  }
  send(ws, m) { try { ws.send(JSON.stringify(m)); } catch (e) {} }
  att(ws) { try { return ws.deserializeAttachment() || {}; } catch (e) { return {}; } }
  live() { return this.ctx.getWebSockets().filter(s => s.readyState === undefined || s.readyState === 1); }
  async webSocketMessage(ws, raw) {
    if (typeof raw !== 'string' || raw.length > 1000) { try { ws.close(1009, 'too big'); } catch (e) {} return; }
    const now = Date.now(), r = this.rate.get(ws) || {win: 0, cnt: 0};
    if (now - r.win > 1000) { r.win = now; r.cnt = 0; }
    this.rate.set(ws, r);
    if (++r.cnt > 10) { if (r.cnt > 30) { try { ws.close(1008, 'too many'); } catch (e) {} } return; }
    let m; try { m = JSON.parse(raw); } catch (e) { return; }
    if (!m || typeof m !== 'object') return;
    const a = this.att(ws);
    if (m.t === 'hi') {
      const pid = typeof m.pid === 'string' && /^[0-9a-f]{24}$/.test(m.pid) ? m.pid : '';
      const key = typeof m.key === 'string' && /^[0-9a-f]{32}$/.test(m.key) ? m.key : '';
      if (!pid || !key) { this.send(ws, {t: 'err', e: 'badplayer'}); return; }
      const kh = await sha256(key);
      let p = await this.ctx.storage.get('p:' + pid);
      if (p && p.kh !== kh) { this.send(ws, {t: 'err', e: 'badkey'}); return; }
      if (!p) p = {kh, r: RATE0, n: 0, w: 0, l: 0};
      p.name = cleanName(m.name); p.at = now;
      await this.ctx.storage.put('p:' + pid, p);
      ws.serializeAttachment({ok: true, pid, name: p.name, col: clampCol(m.col), r: p.r, q: 0});
      this.send(ws, {t: 'me', r: p.r, n: p.n, w: p.w, l: p.l});
      return;
    }
    if (!a.ok) return;
    if (m.t === 'q') {
      let pm = await this.ctx.storage.get('pm:' + a.pid);   // 組み合わせ済みで、まだ終わっていない対局があれば、そこへ戻す
      if (pm && Array.isArray(m.done) && m.done.slice(0, 20).includes(pm.mid)) { await this.ctx.storage.delete('pm:' + a.pid); pm = null; }   // 端末側では終局済み(戻っても時間切れで負けるだけなので、本人の申告で外してよい)
      if (pm && now - pm.at < PM_MS) { this.send(ws, {t: 'match', ...pm, back: true}); return; }
      for (const w of this.live()) { if (w === ws) continue; const b = this.att(w); if (b.ok && b.pid === a.pid && b.q) { b.q = 0; w.serializeAttachment(b); this.send(w, {t: 'err', e: 'replaced'}); try { w.close(4001, 'replaced'); } catch (e) {} } }
      if (!a.q) { a.q = now; ws.serializeAttachment(a); }
      this.send(ws, {t: 'queued'});
      await this.pair();
      return;
    }
    if (m.t === 'cancel') { a.q = 0; ws.serializeAttachment(a); this.send(ws, {t: 'cancelled'}); return; }
  }
  async webSocketClose(ws) { try { ws.close(1000, 'bye'); } catch (e) {} }
  async webSocketError() {}
  // 待ち行列から2人ずつ組む(同時に2回走らないようにする)
  async pair() {
    if (this.pairing) { this.pairAgain = true; return; }
    this.pairing = true;
    try {
      do {
        this.pairAgain = false;
        const now = Date.now();
        const qs = this.live().map(w => ({w, a: this.att(w)})).filter(x => x.a.ok && x.a.q).sort((x, y) => x.a.q - y.a.q);
        const used = new Set(), jobs = [];
        const win = x => WIN0 + WIN_STEP * Math.floor((now - x.a.q) / WIN_STEP_MS);
        for (let i = 0; i < qs.length; i++) {
          if (used.has(i)) continue;
          let best = -1, bd = Infinity;
          for (let j = i + 1; j < qs.length; j++) {
            if (used.has(j) || qs[j].a.pid === qs[i].a.pid) continue;
            const diff = Math.abs(qs[i].a.r - qs[j].a.r);
            if (diff <= Math.max(win(qs[i]), win(qs[j])) && diff < bd) { best = j; bd = diff; }
          }
          if (best >= 0) {
            used.add(i); used.add(best);
            for (const x of [qs[i], qs[best]]) { x.a.q = 0; x.w.serializeAttachment(x.a); }   // 先に行列から外す
            jobs.push([qs[i], qs[best]]);
          }
        }
        for (const [x, y] of jobs) await this.makeMatch(x, y);
        if (this.live().some(w => { const b = this.att(w); return b.ok && b.q; })) await this.ctx.storage.setAlarm(Date.now() + MM_TICK_MS);
      } while (this.pairAgain);
    } finally { this.pairing = false; }
  }
  async makeMatch(x, y) {
    const now = Date.now(), mid = hex(12);
    const seats = rint(2) ? [x, y] : [y, x];   // 先手後手はランダム
    const players = seats.map(s => ({tok: hex(16), name: s.a.name, col: s.a.col, pid: s.a.pid, r: s.a.r}));
    await this.ctx.storage.put('m:' + mid, {pids: players.map(p => p.pid), at: now, done: false});
    let code = '';
    for (let i = 0; i < 8 && !code; i++) {
      const c = genCode();
      try {
        const res = await this.env.ROOMS.get(this.env.ROOMS.idFromName(c)).fetch('https://room/init', {method: 'POST',
          body: JSON.stringify({code: c, mid, players: players.map(p => ({tok: p.tok, name: p.name, col: p.col, r: p.r}))})});
        if (res.ok) code = c;
      } catch (e) {}
    }
    if (!code) {   // ルームを作れなかった:2人を行列に戻す
      await this.ctx.storage.delete('m:' + mid);
      for (const s of seats) { const b = this.att(s.w); if (b.ok) { b.q = now; s.w.serializeAttachment(b); this.send(s.w, {t: 'queued'}); } }
      return;
    }
    for (const k of [0, 1]) {
      const o = players[1 - k];
      const pm = {room: code, tok: players[k].tok, seat: k, mid, opp: {n: o.name, r: o.r}, me: {r: players[k].r}, at: now};
      await this.ctx.storage.put('pm:' + players[k].pid, pm);
      this.send(seats[k].w, {t: 'match', ...pm});
    }
  }
  // 終局の結果(Room から)。イロレーティングで更新し、新しいレートと増減を返す
  async result(d) {
    if (!d || typeof d.mid !== 'string' || !/^[0-9a-f]{24}$/.test(d.mid)) return json({e: 'bad'}, 400);
    const m = await this.ctx.storage.get('m:' + d.mid);
    if (!m) return json({e: 'nomatch'}, 404);
    if (m.done) return json({r: m.nr, d: m.d});   // 送り直し:同じ答えを返す(二重に数えない)
    if (!(d.winner === 0 || d.winner === 1)) return json({e: 'bad'}, 400);
    const ps = await Promise.all(m.pids.map(async id => (await this.ctx.storage.get('p:' + id)) || {kh: '', r: RATE0, n: 0, w: 0, l: 0}));
    const [a, b] = ps, ea = 1 / (1 + 10 ** ((b.r - a.r) / 400)), sa = d.winner === 0 ? 1 : 0;
    const da = Math.round(kFactor(a.n) * (sa - ea)), db = Math.round(kFactor(b.n) * ((1 - sa) - (1 - ea)));
    a.r += da; b.r += db; a.n++; b.n++;
    if (sa) { a.w++; b.l++; } else { a.l++; b.w++; }
    Object.assign(m, {done: true, d: [da, db], nr: [a.r, b.r], winner: d.winner, end: Date.now()});
    await this.ctx.storage.put({['p:' + m.pids[0]]: a, ['p:' + m.pids[1]]: b, ['m:' + d.mid]: m});
    await this.ctx.storage.delete(m.pids.map(id => 'pm:' + id));
    return json({r: m.nr, d: m.d});
  }
  async alarm() {   // 待っている人がいれば組み直す。ときどき古い記録を片付ける
    await this.pair();
    const now = Date.now(), last = (await this.ctx.storage.get('prunedAt')) || 0;
    if (now - last > 3600 * 1000) {
      const del = [];
      for (const [k, v] of await this.ctx.storage.list({prefix: 'm:'})) if (now - (v.at || 0) > MATCH_KEEP_MS) del.push(k);
      for (const [k, v] of await this.ctx.storage.list({prefix: 'pm:'})) if (now - (v.at || 0) > PM_MS) del.push(k);
      for (let i = 0; i < del.length; i += 128) await this.ctx.storage.delete(del.slice(i, i + 128));
      await this.ctx.storage.put('prunedAt', now);
    }
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
    if (url.pathname === '/mm') {   // ランダム対戦の待合所
      if (req.headers.get('Upgrade') !== 'websocket') return new Response('WebSocket で接続してください', {status: 426});
      return env.LOBBY.get(env.LOBBY.idFromName('main')).fetch(req);
    }
    if (url.pathname === '/') return new Response('おぼろ将棋 中継サーバー:動作中', {headers: {'content-type': 'text/plain; charset=utf-8'}});
    return new Response('見つかりません', {status: 404});
  }
};
