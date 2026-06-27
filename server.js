/**
 * こんにちは、みんな — server.js  (セキュリティ強化版)
 * =====================================================
 * セキュリティ対策一覧
 *   [S1] メッセージサイズ上限 (MAX_MSG_BYTES) → 巨大JSON拒否
 *   [S2] IP単位の接続数上限 (MAX_CONN_PER_IP) → DoS対策
 *   [S3] チャットレート制限 (CHAT_RATE_*) → スパム対策
 *   [S4] Heartbeat / ping-pong → ゾンビ接続の自動切断
 *   [S5] 入力サニタイズ → 制御文字・HTML除去
 *   [S6] 数値の厳密検証 → NaN/Infinity拒否
 *   [S7] avatar ホワイトリスト → 想定外絵文字排除
 *   [S8] profile 更新レート制限 → 連打対策
 *   [S9] エラー時も安全にクリーンアップ
 */

const { WebSocketServer } = require("ws");

// ══════════════════════════════════════════════════════════════════
//  定数
// ══════════════════════════════════════════════════════════════════
const PORT             = process.env.PORT || 8080;
const WORLD_W          = 10000;
const WORLD_H          = 8000;
const CELL             = 800;
const AOI_RADIUS       = 2;
const TICK_MS          = 50;          // 20fps tick
const MAX_SPEED        = 10;          // px / tick

// [S1] メッセージサイズ上限
const MAX_MSG_BYTES    = 512;         // バイト

// [S2] IP単位の接続数上限
const MAX_CONN_PER_IP  = 5;

// [S3] チャットレート制限
const CHAT_RATE_LIMIT  = 5;          // CHAT_RATE_WINDOW ms 内の最大発言数
const CHAT_RATE_WINDOW = 5000;       // ms

// [S4] Heartbeat
const PING_INTERVAL    = 30_000;     // ms
const PING_TIMEOUT     = 10_000;     // ms（pongが来なければ切断）

// [S8] profile更新レート制限
const PROFILE_COOLDOWN = 3000;       // ms

// チャット
const MAX_CHAT_LEN     = 60;
const MAX_NICK_LEN     = 16;
const MAX_TITLE_LEN    = 20;
const MAX_HOBBY_LEN    = 10;
const MAX_HOBBIES      = 3;

const COLS = Math.ceil(WORLD_W / CELL);
const ROWS = Math.ceil(WORLD_H / CELL);

// [S7] 許可アバター絵文字ホワイトリスト
const ALLOWED_AVATARS = new Set([
  "👴","👵","🧑","👩","👨","🧓","🐱","🐶","🦊","🐼",
]);

// [S5] 許可ホビーホワイトリスト（GASと同期させること）
const ALLOWED_HOBBIES = new Set([
  "旅行","料理","読書","音楽","映画","園芸","写真",
  "手芸","釣り","将棋","囲碁","お茶","俳句","書道",
  "散歩","ヨガ","登山","温泉","野球","相撲観戦",
]);

// [S5] 許可称号ホワイトリスト（GASと同期させること）
const ALLOWED_TITLES = new Set([
  "🌸 花見名人","🍵 お茶好き","🎵 音楽好き","📚 読書家",
  "🌿 園芸家","🎨 絵かき","🚶 散歩好き","🍳 料理上手",
  "🐾 動物好き","✈️ 旅好き","♟ 将棋愛好家","🎣 釣り人",
  "🏮 お祭り好き","🌙 夜型人間","☀️ 朝型人間","",
]);

// ══════════════════════════════════════════════════════════════════
//  状態
// ══════════════════════════════════════════════════════════════════
const players   = new Map();  // id → PlayerState
const ipCount   = new Map();  // ip → 接続数
let   nextId    = 1;

const cells = Array.from({ length: ROWS }, () =>
  Array.from({ length: COLS }, () => new Set())
);

// ══════════════════════════════════════════════════════════════════
//  ユーティリティ
// ══════════════════════════════════════════════════════════════════
const clamp = (v, lo, hi) => Math.max(lo, Math.min(hi, v));

/** 制御文字・HTMLタグを除去してトリムする */
function sanitize(str, maxLen) {
  return String(str)
    .replace(/[\u0000-\u001F\u007F<>&"'`]/g, "")  // 制御文字・HTML特殊文字
    .trim()
    .slice(0, maxLen);
}

/** 安全な整数か（NaN/Infinity/非数値を拒否） */
function safeInt(v, lo, hi) {
  const n = Number(v);
  if (!Number.isFinite(n)) return null;
  return clamp(Math.floor(n), lo, hi);
}

function cellOf(x, y) {
  return {
    col: clamp(Math.floor(x / CELL), 0, COLS - 1),
    row: clamp(Math.floor(y / CELL), 0, ROWS - 1),
  };
}
function addCell(id, x, y) {
  const c = cellOf(x, y);
  cells[c.row][c.col].add(id);
  return c;
}
function removeCell(id, col, row) { cells[row][col].delete(id); }

function aoiPeers(col, row) {
  const ids = new Set();
  for (let r = row - AOI_RADIUS; r <= row + AOI_RADIUS; r++) {
    if (r < 0 || r >= ROWS) continue;
    for (let c = col - AOI_RADIUS; c <= col + AOI_RADIUS; c++) {
      if (c < 0 || c >= COLS) continue;
      cells[r][c].forEach(id => ids.add(id));
    }
  }
  return ids;
}

function safeSend(ws, obj) {
  if (ws.readyState === 1) {
    try { ws.send(JSON.stringify(obj)); } catch { /* 送信失敗は無視 */ }
  }
}

/** IP文字列の取得（プロキシ環境にも対応） */
function getIP(req) {
  const forwarded = req.headers["x-forwarded-for"];
  if (forwarded) return forwarded.split(",")[0].trim();
  return req.socket.remoteAddress || "unknown";
}

// ══════════════════════════════════════════════════════════════════
//  WebSocket サーバー
// ══════════════════════════════════════════════════════════════════
const wss = new WebSocketServer({ port: PORT });
console.log(`[server] ws://localhost:${PORT}  world=${WORLD_W}×${WORLD_H}`);

wss.on("connection", (ws, req) => {
  const ip = getIP(req);

  // [S2] IP単位の接続数チェック
  const connCount = ipCount.get(ip) || 0;
  if (connCount >= MAX_CONN_PER_IP) {
    ws.close(1008, "Too many connections from this IP");
    return;
  }
  ipCount.set(ip, connCount + 1);

  const id  = String(nextId++);
  const spX = clamp(Math.floor(Math.random() * (WORLD_W - 400)) + 200, 0, WORLD_W);
  const spY = clamp(Math.floor(Math.random() * (WORLD_H - 400)) + 200, 0, WORLD_H);

  const p = {
    id, ws, ip,
    x: spX, y: spY,
    nick:   `みんな${id}`,
    avatar: "👴",
    title:  "",
    hobbies: [],
    col: 0, row: 0,
    // [S3] チャットレート制限
    chatTimes: [],
    // [S8] profile更新クールダウン
    lastProfileAt: 0,
    // [S4] Heartbeat
    isAlive: true,
  };
  const { col, row } = addCell(id, spX, spY);
  p.col = col; p.row = row;
  players.set(id, p);

  safeSend(ws, {
    type: "init", id,
    x: spX, y: spY,
    nick: p.nick, avatar: p.avatar,
    worldW: WORLD_W, worldH: WORLD_H,
  });

  // [S4] pong 受信でアライブフラグを立て直す
  ws.on("pong", () => { p.isAlive = true; });

  // ── メッセージ受信 ─────────────────────────────────────────────
  ws.on("message", (rawBuf, isBinary) => {
    // [S1] バイナリ拒否 & サイズ上限
    if (isBinary) return;
    if (rawBuf.length > MAX_MSG_BYTES) {
      ws.close(1009, "Message too large");
      return;
    }

    let msg;
    try { msg = JSON.parse(rawBuf.toString("utf8")); }
    catch { return; }  // 不正JSONは無視

    // typeは文字列のみ
    if (typeof msg.type !== "string") return;

    switch (msg.type) {

      // ── 移動 ──────────────────────────────────────────────────
      case "move": {
        // [S6] 数値の厳密検証
        const nx = safeInt(msg.x, 0, WORLD_W);
        const ny = safeInt(msg.y, 0, WORLD_H);
        if (nx === null || ny === null) return;

        // [S1 extension] 速度チェック
        const dx = clamp(nx - p.x, -MAX_SPEED, MAX_SPEED);
        const dy = clamp(ny - p.y, -MAX_SPEED, MAX_SPEED);
        p.x = clamp(p.x + dx, 0, WORLD_W);
        p.y = clamp(p.y + dy, 0, WORLD_H);

        const nc = cellOf(p.x, p.y);
        if (nc.col !== p.col || nc.row !== p.row) {
          removeCell(id, p.col, p.row);
          addCell(id, p.x, p.y);
          p.col = nc.col; p.row = nc.row;
        }
        break;
      }

      // ── プロフィール設定 ───────────────────────────────────────
      case "profile": {
        // [S8] 連打対策
        const now = Date.now();
        if (now - p.lastProfileAt < PROFILE_COOLDOWN) return;
        p.lastProfileAt = now;

        // [S5] nick：制御文字除去・長さ制限
        if (typeof msg.nick === "string") {
          const clean = sanitize(msg.nick, MAX_NICK_LEN);
          if (clean) p.nick = clean;
        }

        // [S7] avatar：ホワイトリスト
        if (typeof msg.avatar === "string") {
          if (ALLOWED_AVATARS.has(msg.avatar)) p.avatar = msg.avatar;
        }

        // [S5][S7] title：ホワイトリスト
        if (typeof msg.title === "string") {
          if (ALLOWED_TITLES.has(msg.title)) p.title = msg.title;
        }

        // [S5][S7] hobbies：ホワイトリスト & 件数制限
        if (Array.isArray(msg.hobbies)) {
          p.hobbies = msg.hobbies
            .filter(h => typeof h === "string" && ALLOWED_HOBBIES.has(h))
            .slice(0, MAX_HOBBIES);
        }
        break;
      }

      // ── チャット ───────────────────────────────────────────────
      case "chat": {
        // [S3] レート制限
        const now = Date.now();
        p.chatTimes = p.chatTimes.filter(t => now - t < CHAT_RATE_WINDOW);
        if (p.chatTimes.length >= CHAT_RATE_LIMIT) return;  // 無視（切断しない）
        p.chatTimes.push(now);

        // [S5] テキストサニタイズ
        const text = sanitize(String(msg.text || ""), MAX_CHAT_LEN);
        if (!text) return;

        // AOI内 & 距離内のピアにのみ配信
        const peers = aoiPeers(p.col, p.row);
        peers.forEach(pid => {
          const peer = players.get(pid);
          if (!peer) return;
          if (Math.hypot(peer.x - p.x, peer.y - p.y) > 400) return;
          safeSend(peer.ws, {
            type: "chat", from: id,
            nick: p.nick, avatar: p.avatar,
            text,           // サニタイズ済み
            x: p.x, y: p.y,
          });
        });
        break;
      }

      // 未知のtypeは完全無視（エラー応答も返さない）
    }
  });

  // ── 切断・エラー ───────────────────────────────────────────────
  function cleanup() {
    if (!players.has(id)) return;  // 二重呼び出し防止
    removeCell(id, p.col, p.row);
    players.delete(id);
    const c = (ipCount.get(ip) || 1) - 1;
    if (c <= 0) ipCount.delete(ip); else ipCount.set(ip, c);
  }

  ws.on("close", cleanup);
  ws.on("error", () => { try { ws.terminate(); } catch {} cleanup(); });
});

// ══════════════════════════════════════════════════════════════════
//  [S4] Heartbeat — ゾンビ接続の定期切断
// ══════════════════════════════════════════════════════════════════
setInterval(() => {
  players.forEach((p, id) => {
    if (!p.isAlive) {
      // pong未返答 → 強制切断
      try { p.ws.terminate(); } catch {}
      return;
    }
    p.isAlive = false;
    try { p.ws.ping(); } catch {}
  });
}, PING_INTERVAL);

// ══════════════════════════════════════════════════════════════════
//  AOI スナップショット tick
// ══════════════════════════════════════════════════════════════════
setInterval(() => {
  players.forEach(p => {
    if (p.ws.readyState !== 1) return;
    const peerIds  = aoiPeers(p.col, p.row);
    const snapshot = [];
    peerIds.forEach(pid => {
      const q = players.get(pid);
      if (!q) return;
      snapshot.push({
        id: q.id, x: q.x, y: q.y,
        nick: q.nick, avatar: q.avatar,
        title: q.title, hobbies: q.hobbies,
      });
    });
    safeSend(p.ws, { type: "snapshot", players: snapshot, total: players.size });
  });
}, TICK_MS);

// ══════════════════════════════════════════════════════════════════
//  死活ログ
// ══════════════════════════════════════════════════════════════════
setInterval(() => {
  console.log(`[health] online=${players.size}  unique_ips=${ipCount.size}`);
}, 15_000);
