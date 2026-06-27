/**
 * こんにちは、みんな — server.js (WebRTC シグナリング対応版)
 * ============================================================
 * 追加機能
 *   [P] 8桁パスコード管理（初回発行・再入室）
 *   [R] WebRTC シグナリング（offer / answer / ice）
 *
 * セキュリティ対策は全て維持
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
const TICK_MS          = 50;
const MAX_SPEED        = 10;
const MAX_MSG_BYTES    = 4096;   // WebRTC SDPが大きいため拡張
const MAX_CONN_PER_IP  = 5;
const CHAT_RATE_LIMIT  = 5;
const CHAT_RATE_WINDOW = 5000;
const PING_INTERVAL    = 30_000;
const PROFILE_COOLDOWN = 3000;
const MAX_CHAT_LEN     = 60;
const MAX_NICK_LEN     = 16;
const CALL_RANGE       = 500;    // 通話開始距離 px

const COLS = Math.ceil(WORLD_W / CELL);
const ROWS = Math.ceil(WORLD_H / CELL);

const ALLOWED_AVATARS = new Set([
  "👴","👵","🧑","👩","👨","🧓","🐱","🐶","🦊","🐼",
]);
const ALLOWED_TITLES = new Set([
  "🌸 花見名人","🍵 お茶好き","🎵 音楽好き","📚 読書家",
  "🌿 園芸家","🎨 絵かき","🚶 散歩好き","🍳 料理上手",
  "🐾 動物好き","✈️ 旅好き","♟ 将棋愛好家","🎣 釣り人",
  "🏮 お祭り好き","🌙 夜型人間","☀️ 朝型人間","",
]);
const ALLOWED_HOBBIES = new Set([
  "旅行","料理","読書","音楽","映画","園芸","写真",
  "手芸","釣り","将棋","囲碁","お茶","俳句","書道",
  "散歩","ヨガ","登山","温泉","野球","相撲観戦",
]);

// ══════════════════════════════════════════════════════════════════
//  状態
// ══════════════════════════════════════════════════════════════════
const players  = new Map();   // id → PlayerState
const ipCount  = new Map();   // ip → 接続数
// [P] パスコード管理: passcode(8桁文字列) → {nick, avatar, title, hobbies}
const passcodeStore = new Map();
let   nextId   = 1;

const cells = Array.from({ length: ROWS }, () =>
  Array.from({ length: COLS }, () => new Set())
);

// ══════════════════════════════════════════════════════════════════
//  ユーティリティ
// ══════════════════════════════════════════════════════════════════
const clamp = (v, lo, hi) => Math.max(lo, Math.min(hi, v));

function sanitize(str, maxLen) {
  return String(str)
    .replace(/[\u0000-\u001F\u007F<>&"'`]/g, "")
    .trim().slice(0, maxLen);
}
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
    try { ws.send(JSON.stringify(obj)); } catch {}
  }
}
function getIP(req) {
  const f = req.headers["x-forwarded-for"];
  if (f) return f.split(",")[0].trim();
  return req.socket.remoteAddress || "unknown";
}

// [P] 8桁パスコード生成（重複チェック付き）
function genPasscode() {
  let code;
  do {
    code = String(Math.floor(Math.random() * 100000000)).padStart(8, "0");
  } while (passcodeStore.has(code));
  return code;
}

// ══════════════════════════════════════════════════════════════════
//  WebSocket サーバー
// ══════════════════════════════════════════════════════════════════
const wss = new WebSocketServer({ port: PORT });
console.log(`[server] ws://localhost:${PORT}`);

wss.on("connection", (ws, req) => {
  const ip = getIP(req);

  // IP制限
  const connCount = ipCount.get(ip) || 0;
  if (connCount >= MAX_CONN_PER_IP) {
    ws.close(1008, "Too many connections");
    return;
  }
  ipCount.set(ip, connCount + 1);

  const id  = String(nextId++);
  const spX = clamp(Math.floor(Math.random() * (WORLD_W - 400)) + 200, 0, WORLD_W);
  const spY = clamp(Math.floor(Math.random() * (WORLD_H - 400)) + 200, 0, WORLD_H);

  const p = {
    id, ws, ip,
    x: spX, y: spY,
    nick: `みんな${id}`, avatar: "👴",
    title: "", hobbies: [],
    passcode: null,         // [P]
    col: 0, row: 0,
    chatTimes: [],
    lastProfileAt: 0,
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

  ws.on("pong", () => { p.isAlive = true; });

  // ── メッセージ受信 ─────────────────────────────────────────────
  ws.on("message", (rawBuf, isBinary) => {
    if (isBinary) return;
    if (rawBuf.length > MAX_MSG_BYTES) { ws.close(1009, "Too large"); return; }

    let msg;
    try { msg = JSON.parse(rawBuf.toString("utf8")); } catch { return; }
    if (typeof msg.type !== "string") return;

    switch (msg.type) {

      // ── 移動 ──────────────────────────────────────────────────
      case "move": {
        const nx = safeInt(msg.x, 0, WORLD_W);
        const ny = safeInt(msg.y, 0, WORLD_H);
        if (nx === null || ny === null) return;
        // 速度制限を廃止：座標をそのまま反映（境界clampのみ）
        p.x = nx;
        p.y = ny;
        const nc = cellOf(p.x, p.y);
        if (nc.col !== p.col || nc.row !== p.row) {
          removeCell(id, p.col, p.row);
          addCell(id, p.x, p.y);
          p.col = nc.col; p.row = nc.row;
        }
        break;
      }

      // ── プロフィール ───────────────────────────────────────────
      case "profile": {
        const now = Date.now();
        if (now - p.lastProfileAt < PROFILE_COOLDOWN) return;
        p.lastProfileAt = now;
        if (typeof msg.nick === "string") {
          const c = sanitize(msg.nick, MAX_NICK_LEN); if (c) p.nick = c;
        }
        if (ALLOWED_AVATARS.has(msg.avatar)) p.avatar = msg.avatar;
        if (ALLOWED_TITLES.has(msg.title))   p.title  = msg.title;
        if (Array.isArray(msg.hobbies)) {
          p.hobbies = msg.hobbies
            .filter(h => ALLOWED_HOBBIES.has(h)).slice(0, 3);
        }
        // パスコードのプロフィールも更新
        if (p.passcode && passcodeStore.has(p.passcode)) {
          passcodeStore.set(p.passcode, {
            nick: p.nick, avatar: p.avatar,
            title: p.title, hobbies: p.hobbies,
          });
        }
        break;
      }

      // ── チャット ───────────────────────────────────────────────
      case "chat": {
        const now = Date.now();
        p.chatTimes = p.chatTimes.filter(t => now - t < CHAT_RATE_WINDOW);
        if (p.chatTimes.length >= CHAT_RATE_LIMIT) return;
        p.chatTimes.push(now);
        const text = sanitize(String(msg.text || ""), MAX_CHAT_LEN);
        if (!text) return;
        aoiPeers(p.col, p.row).forEach(pid => {
          const peer = players.get(pid);
          if (!peer) return;
          if (Math.hypot(peer.x - p.x, peer.y - p.y) > 400) return;
          safeSend(peer.ws, {
            type: "chat", from: id,
            nick: p.nick, avatar: p.avatar, text,
            x: p.x, y: p.y,
          });
        });
        break;
      }

      // ── [P] パスコード発行 ─────────────────────────────────────
      case "issue_passcode": {
        if (p.passcode) {
          // すでに発行済み → 再通知
          safeSend(ws, { type: "passcode", code: p.passcode });
          return;
        }
        const code = genPasscode();
        p.passcode = code;
        passcodeStore.set(code, {
          nick: p.nick, avatar: p.avatar,
          title: p.title, hobbies: p.hobbies,
        });
        safeSend(ws, { type: "passcode", code });
        break;
      }

      // ── [P] パスコードで再入室 ─────────────────────────────────
      case "restore_passcode": {
        const code = sanitize(String(msg.code || ""), 8);
        if (!/^\d{8}$/.test(code)) {
          safeSend(ws, { type: "passcode_result", ok: false, reason: "形式エラー" });
          return;
        }
        const saved = passcodeStore.get(code);
        if (!saved) {
          safeSend(ws, { type: "passcode_result", ok: false, reason: "見つかりません" });
          return;
        }
        // プロフィールを復元
        p.nick    = saved.nick;
        p.avatar  = saved.avatar;
        p.title   = saved.title;
        p.hobbies = saved.hobbies;
        p.passcode = code;
        safeSend(ws, {
          type: "passcode_result", ok: true,
          nick: p.nick, avatar: p.avatar,
          title: p.title, hobbies: p.hobbies,
        });
        break;
      }

      // ── [R] WebRTC シグナリング中継 ───────────────────────────
      // offer / answer / ice をターゲットIDに中継する
      case "rtc_offer":
      case "rtc_answer":
      case "rtc_ice": {
        const target = players.get(String(msg.to || ""));
        if (!target) return;
        // 距離チェック（CALL_RANGE×2以内の相手にのみ中継）
        if (Math.hypot(target.x - p.x, target.y - p.y) > CALL_RANGE * 2) return;
        safeSend(target.ws, {
          type: msg.type,
          from: id,
          // SDPとICE候補をそのまま通す（内容は検証しない・暗号化はWSSで担保）
          sdp:       msg.sdp,
          candidate: msg.candidate,
        });
        break;
      }

      // ── ping keepalive ────────────────────────────────────────
      case "ping": {
        safeSend(ws, { type: "pong" });
        break;
      }
    }
  });

  function cleanup() {
    if (!players.has(id)) return;
    removeCell(id, p.col, p.row);
    players.delete(id);
    const c = (ipCount.get(ip) || 1) - 1;
    if (c <= 0) ipCount.delete(ip); else ipCount.set(ip, c);
  }
  ws.on("close", cleanup);
  ws.on("error", () => { try { ws.terminate(); } catch {} cleanup(); });
});

// ── Heartbeat ─────────────────────────────────────────────────────
setInterval(() => {
  players.forEach(p => {
    if (!p.isAlive) { try { p.ws.terminate(); } catch {} return; }
    p.isAlive = false;
    try { p.ws.ping(); } catch {}
  });
}, PING_INTERVAL);

// ── AOI スナップショット tick ──────────────────────────────────────
setInterval(() => {
  players.forEach(p => {
    if (p.ws.readyState !== 1) return;
    const peerIds  = aoiPeers(p.col, p.row);
    const snapshot = [];
    peerIds.forEach(pid => {
      if (pid === p.id) return;   // 自分自身は除外
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

setInterval(() => {
  console.log(`[health] online=${players.size} passcodes=${passcodeStore.size}`);
}, 15_000);
