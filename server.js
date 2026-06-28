/**
 * こんにちは、みんな — server.js (100万人対応・シャード設計版)
 * ============================================================
 *
 * ── スケール設計 ──────────────────────────────────────────────────
 *  ワールド : 3,162,000 × 3,162,000 px（1000倍面積）
 *  AOIセル  : 8,000 px → 396×396 = 156,816 セル
 *  AOI範囲  : 自セル±1 → 3×3 = 9セル（通信量最小化）
 *  1シャード: 最大 MAX_PLAYERS_PER_SHARD 人
 *  シャードID: 環境変数 SHARD_ID（0,1,2...）で識別
 *
 * ── 水平スケール方法 ─────────────────────────────────────────────
 *  1台 : ～10,000人
 *  10台 : ～100,000人
 *  100台: ～1,000,000人
 *  → Railway/Fly.io で SHARD_ID を変えてデプロイを増やすだけ
 *    フロントは SHARD_ID = Math.floor(Math.random()*SHARD_COUNT)
 *    で接続先を振り分ける
 *
 * ── AOI 通信量 ────────────────────────────────────────────────────
 *  1セルあたり平均人数 = 10,000 ÷ 156,816 ≒ 0.06人
 *  9セル範囲の平均人数 = 約0.54人
 *  → 超疎ら。密集エリアでは最大 MAX_PLAYERS_PER_SHARD 人規模でも安全
 */

const { WebSocketServer } = require("ws");

// ══════════════════════════════════════════════════════════════════
//  定数
// ══════════════════════════════════════════════════════════════════
const PORT               = process.env.PORT            || 8080;
const SHARD_ID           = Number(process.env.SHARD_ID || 0);
const MAX_PLAYERS        = Number(process.env.MAX_PLAYERS || 10000); // 1シャード最大

// ワールドサイズ（1000倍面積 = 辺√1000≒31.6倍）
const WORLD_W            = 3_162_000;   // px
const WORLD_H            = 3_162_000;   // px

// AOI
const CELL               = 8_000;       // セルサイズ px
const AOI_RADIUS         = 1;           // 自セル±1 → 3×3=9セル
const TICK_MS            = 100;         // 10fps（CPU節約）

// セキュリティ
const MAX_MSG_BYTES      = 1024;
const MAX_CONN_PER_IP    = 3;
const CHAT_RATE_LIMIT    = 5;
const CHAT_RATE_WINDOW   = 5000;
const PING_INTERVAL      = 30_000;
const PROFILE_COOLDOWN   = 3000;

// 文字数制限
const MAX_CHAT_LEN       = 60;
const MAX_NICK_LEN       = 16;

const COLS = Math.ceil(WORLD_W / CELL);   // 396
const ROWS = Math.ceil(WORLD_H / CELL);   // 396

// ホワイトリスト
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
const players      = new Map();
const ipCount      = new Map();
const passcodeStore= new Map();
let   nextId       = 1;

// AOIグリッド（疎らなので実体セルのみMapで保持→メモリ節約）
// cells[row][col] = Set<id>  ただし空セルは作らない
const cells = new Map();  // key = `${row},${col}` → Set<id>

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

function cellKey(col, row) { return `${row},${col}`; }

function addCell(id, x, y) {
  const c = cellOf(x, y);
  const k = cellKey(c.col, c.row);
  if (!cells.has(k)) cells.set(k, new Set());
  cells.get(k).add(id);
  return c;
}
function removeCell(id, col, row) {
  const k = cellKey(col, row);
  const s = cells.get(k);
  if (!s) return;
  s.delete(id);
  if (s.size === 0) cells.delete(k); // 空セルは削除（メモリ節約）
}

function aoiPeers(col, row) {
  const ids = new Set();
  for (let r = row - AOI_RADIUS; r <= row + AOI_RADIUS; r++) {
    if (r < 0 || r >= ROWS) continue;
    for (let c = col - AOI_RADIUS; c <= col + AOI_RADIUS; c++) {
      if (c < 0 || c >= COLS) continue;
      const s = cells.get(cellKey(c, r));
      if (s) s.forEach(id => ids.add(id));
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
console.log(`[shard:${SHARD_ID}] ws://localhost:${PORT}  world=${WORLD_W}×${WORLD_H}  maxPlayers=${MAX_PLAYERS}`);

wss.on("connection", (ws, req) => {
  const ip = getIP(req);

  // 満員チェック
  if (players.size >= MAX_PLAYERS) {
    ws.close(1013, "Server full");
    return;
  }

  // IP制限
  const connCount = ipCount.get(ip) || 0;
  if (connCount >= MAX_CONN_PER_IP) {
    ws.close(1008, "Too many connections");
    return;
  }
  ipCount.set(ip, connCount + 1);

  const id  = `${SHARD_ID}-${nextId++}`;
  const spX = clamp(Math.floor(Math.random() * (WORLD_W - 2000)) + 1000, 0, WORLD_W);
  const spY = clamp(Math.floor(Math.random() * (WORLD_H - 2000)) + 1000, 0, WORLD_H);

  const p = {
    id, ws, ip,
    x: spX, y: spY,
    nick: `みんな${nextId}`, avatar: "👴",
    title: "", hobbies: [],
    passcode: null,
    gasUserId: "",
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
    shardId: SHARD_ID,
  });

  ws.on("pong", () => { p.isAlive = true; });

  ws.on("message", (rawBuf, isBinary) => {
    if (isBinary) return;
    if (rawBuf.length > MAX_MSG_BYTES) { ws.close(1009, "Too large"); return; }
    let msg;
    try { msg = JSON.parse(rawBuf.toString("utf8")); } catch { return; }
    if (typeof msg.type !== "string") return;

    switch (msg.type) {

      case "move": {
        const nx = safeInt(msg.x, 0, WORLD_W);
        const ny = safeInt(msg.y, 0, WORLD_H);
        if (nx === null || ny === null) return;
        p.x = nx; p.y = ny;
        const nc = cellOf(p.x, p.y);
        if (nc.col !== p.col || nc.row !== p.row) {
          removeCell(id, p.col, p.row);
          addCell(id, p.x, p.y);
          p.col = nc.col; p.row = nc.row;
        }
        break;
      }

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
          p.hobbies = msg.hobbies.filter(h => ALLOWED_HOBBIES.has(h)).slice(0, 3);
        }
        if (typeof msg.gasUserId === "string") {
          p.gasUserId = sanitize(msg.gasUserId, 40);
        }
        if (p.passcode && passcodeStore.has(p.passcode)) {
          passcodeStore.set(p.passcode, {
            nick: p.nick, avatar: p.avatar,
            title: p.title, hobbies: p.hobbies,
          });
        }
        break;
      }

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

      case "call_invite":
      case "sns_card": {
        const label = sanitize(String(msg.label || ""), 20);
        const url   = sanitize(String(msg.url   || ""), 300);
        if (!url.startsWith("https://") || !label) return;
        aoiPeers(p.col, p.row).forEach(pid => {
          const peer = players.get(pid);
          if (!peer || pid === id) return;
          if (Math.hypot(peer.x - p.x, peer.y - p.y) > 400) return;
          safeSend(peer.ws, { type: msg.type, from: id,
            nick: p.nick, avatar: p.avatar, label, url });
        });
        break;
      }

      case "issue_passcode": {
        if (p.passcode) { safeSend(ws, { type: "passcode", code: p.passcode }); return; }
        const code = genPasscode();
        p.passcode = code;
        passcodeStore.set(code, {
          nick: p.nick, avatar: p.avatar, title: p.title, hobbies: p.hobbies,
        });
        safeSend(ws, { type: "passcode", code });
        const gasUrl = process.env.GAS_URL;
        if (gasUrl && p.gasUserId) {
          fetch(gasUrl, {
            method: "POST",
            headers: { "Content-Type": "text/plain" },
            body: JSON.stringify({ action: "save_passcode", user_id: p.gasUserId, passcode: code }),
          }).catch(() => {});
        }
        break;
      }

      case "restore_passcode": {
        const code = sanitize(String(msg.code || ""), 8);
        if (!/^\d{8}$/.test(code)) {
          safeSend(ws, { type: "passcode_result", ok: false, reason: "形式エラー" }); return;
        }
        const saved = passcodeStore.get(code);
        if (!saved) {
          safeSend(ws, { type: "passcode_result", ok: false, reason: "見つかりません" }); return;
        }
        p.nick = saved.nick; p.avatar = saved.avatar;
        p.title = saved.title; p.hobbies = saved.hobbies;
        p.passcode = code;
        safeSend(ws, { type: "passcode_result", ok: true,
          nick: p.nick, avatar: p.avatar, title: p.title, hobbies: p.hobbies });
        break;
      }

      case "ping": safeSend(ws, { type: "pong" }); break;
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
      if (pid === p.id) return;
      const q = players.get(pid);
      if (!q) return;
      snapshot.push({ id: q.id, x: q.x, y: q.y,
        nick: q.nick, avatar: q.avatar,
        title: q.title, hobbies: q.hobbies });
    });
    safeSend(p.ws, { type: "snapshot", players: snapshot, total: players.size });
  });
}, TICK_MS);

// ── ヘルスログ ────────────────────────────────────────────────────
setInterval(() => {
  const usedCells = cells.size;
  const totalPeers = [...cells.values()].reduce((s,c)=>s+c.size,0);
  console.log(`[shard:${SHARD_ID}] online=${players.size}/${MAX_PLAYERS} cells=${usedCells} avgPerCell=${usedCells?( totalPeers/usedCells).toFixed(2):0} passcodes=${passcodeStore.size}`);
}, 15_000);
