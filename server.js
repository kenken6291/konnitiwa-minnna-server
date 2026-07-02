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
const WORLD_W            = 10_000;   // px
const WORLD_H            = 8_000;   // px

// AOI
const CELL               = 800;   // セルサイズ px
const AOI_RADIUS         = 2;   // 自セル±2 → 5×5=25セル
const TICK_MS            = 50;   // 20fps

// セキュリティ
const MAX_MSG_BYTES      = 1024;
const MAX_CONN_PER_IP    = 5;
const CHAT_RATE_LIMIT    = 5;
const CHAT_RATE_WINDOW   = 5000;
const PING_INTERVAL      = 30_000;
const PROFILE_COOLDOWN   = 3000;

// 文字数制限
const MAX_CHAT_LEN       = 60;
const MAX_NICK_LEN       = 16;

const COLS = Math.ceil(WORLD_W / CELL);   // 13
const ROWS = Math.ceil(WORLD_H / CELL);   // 10

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
//  セキュリティユーティリティ
// ══════════════════════════════════════════════════════════════════

// UUID v4 形式の検証
function isValidUUID(s) {
  return typeof s === "string" &&
    /^[0-9a-f]{8}-[0-9a-f]{4}-4[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$/i.test(s);
}

// プロンプトインジェクション対策：制御文字・特殊パターンを除去
function sanitizeForPrompt(str, maxLen) {
  return String(str)
    .replace(/[\u0000-\u001F\u007F<>&"'`\\]/g, "")
    .replace(/system\s*:/gi, "")
    .replace(/\[INST\]|\[\/INST\]|<s>|<\/s>/gi, "")
    .trim()
    .slice(0, maxLen);
}

// gas_log の許可アクション（ホワイトリスト）
const GAS_LOG_ALLOWED_ACTIONS = new Set([
  "register", "update_badge", "save_passcode",
  "chat_log", "access_log", "warp_stats",
]);

// 許可フィールドのみを抽出してGASに送る（余分なフィールドを排除）
function buildGasPayload(pl) {
  const action = String(pl.action || "");
  if (!GAS_LOG_ALLOWED_ACTIONS.has(action)) return null;

  const base = {
    action,
    user_id: isValidUUID(pl.user_id) ? pl.user_id : "",
    nick:    sanitize(String(pl.nick    || ""), 16),
    avatar:  ALLOWED_AVATARS.has(pl.avatar) ? pl.avatar : "",
  };

  switch (action) {
    case "register":
    case "update_badge":
      return {
        ...base,
        title:    ALLOWED_TITLES.has(pl.title)  ? pl.title  : "",
        hobbies:  Array.isArray(pl.hobbies)
          ? pl.hobbies.filter(h => ALLOWED_HOBBIES.has(h)).slice(0, 3) : [],
        passcode: /^\d{8}$/.test(String(pl.passcode || "")) ? String(pl.passcode) : "",
      };
    case "save_passcode":
      return {
        ...base,
        passcode: /^\d{8}$/.test(String(pl.passcode || "")) ? String(pl.passcode) : "",
      };
    case "chat_log":
      return {
        ...base,
        message: sanitize(String(pl.message || ""), 80),
        x: Math.max(0, Math.min(WORLD_W, Number(pl.x) || 0)),
        y: Math.max(0, Math.min(WORLD_H, Number(pl.y) || 0)),
        area: sanitize(String(pl.area || ""), 20),
      };
    case "access_log":
      return {
        ...base,
        event:       pl.event === "leave" ? "leave" : "join",
        session_min: Math.max(0, Math.min(10000, Number(pl.session_min) || 0)),
        spawn_x:     Math.max(0, Math.min(WORLD_W, Number(pl.spawn_x) || 0)),
        spawn_y:     Math.max(0, Math.min(WORLD_H, Number(pl.spawn_y) || 0)),
      };
    case "warp_stats":
      return {
        ...base,
        spot_name: sanitize(String(pl.spot_name || ""), 30),
        to_x: Math.max(0, Math.min(WORLD_W, Number(pl.to_x) || 0)),
        to_y: Math.max(0, Math.min(WORLD_H, Number(pl.to_y) || 0)),
      };
    default:
      return null;
  }
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
        // GASのuser_idを保存（UUID形式のみ受け付ける）
        if (typeof msg.gasUserId === "string" && isValidUUID(msg.gasUserId)) {
          p.gasUserId = msg.gasUserId;
        }
        if (p.passcode && passcodeStore.has(p.passcode)) {
          passcodeStore.set(p.passcode, {
            nick: p.nick, avatar: p.avatar,
            title: p.title, hobbies: p.hobbies,
          });
        }

        // GASにユーザー登録・更新（サーバー側から送信）
        const gasUrl = process.env.GAS_URL;
        if (gasUrl && p.gasUserId) {
          fetch(gasUrl, {
            method: "POST",
            headers: { "Content-Type": "text/plain" },
            body: JSON.stringify({
              action:   "register",
              user_id:  p.gasUserId,
              nick:     p.nick,
              avatar:   p.avatar,
              title:    p.title,
              hobbies:  p.hobbies,
              passcode: p.passcode || "",
            }),
          }).catch(() => {});
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
        // NPC反応チェック
        handleNpcChat(p, text);
        break;
      }

      case "call_invite":
      case "sns_card": {
        const label = sanitize(String(msg.label || ""), 20);
        const url   = sanitize(String(msg.url   || ""), 300);
        if (!url.startsWith("https://") || !label) return;

        // toが指定されている場合は指定IDのみに送信、なければAOI内全員
        // 最大20人まで・各IDはサーバー上の実在プレイヤーのみ
        if (Array.isArray(msg.to) && msg.to.length > 0) {
          const toIds = msg.to.slice(0, 20); // 最大20件に制限
          toIds.forEach(tid => {
            const peer = players.get(String(tid));
            if (!peer || tid === id) return;
            safeSend(peer.ws, { type: msg.type, from: id,
              nick: p.nick, avatar: p.avatar, label, url });
          });
        } else {
          aoiPeers(p.col, p.row).forEach(pid => {
            const peer = players.get(pid);
            if (!peer || pid === id) return;
            if (Math.hypot(peer.x - p.x, peer.y - p.y) > 400) return;
            safeSend(peer.ws, { type: msg.type, from: id,
              nick: p.nick, avatar: p.avatar, label, url });
          });
        }
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

      // ── GASログ転送（許可フィールドのみ・アクションホワイトリスト）──
      case "gas_log": {
        const gasUrl = process.env.GAS_URL;
        if (!gasUrl || typeof msg.payload !== "object" || msg.payload === null) return;
        const pl = buildGasPayload(msg.payload);
        if (!pl) return;  // 不正アクションは無視
        fetch(gasUrl, {
          method: "POST",
          headers: { "Content-Type": "text/plain" },
          body: JSON.stringify(pl),
        }).catch(() => {});
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

// ── AOI スナップショット tick（NPCを含む） ────────────────────────
setInterval(() => {
  players.forEach(p => {
    if (p.ws.readyState !== 1) return;
    const peerIds  = aoiPeers(p.col, p.row);
    const snapshot = [];

    // 他プレイヤー
    peerIds.forEach(pid => {
      if (pid === p.id) return;
      const q = players.get(pid);
      if (!q) return;
      snapshot.push({ id: q.id, x: q.x, y: q.y,
        nick: q.nick, avatar: q.avatar,
        title: q.title, hobbies: q.hobbies });
    });

    // NPC（AOI内にいるものだけ）
    NPCS.forEach(npc => {
      if (Math.hypot(npc.x - p.x, npc.y - p.y) < CELL * (AOI_RADIUS + 1) * 2) {
        snapshot.push({ id: npc.id, x: Math.round(npc.x), y: Math.round(npc.y),
          nick: npc.nick, avatar: npc.avatar,
          title: npc.title, hobbies: npc.hobbies, isNpc: true });
      }
    });

    safeSend(p.ws, { type: "snapshot", players: snapshot, total: players.size });
  });
}, TICK_MS);

// ── ヘルスログ ────────────────────────────────────────────────────
setInterval(() => {
  const usedCells = cells.size;
  const totalPeers = [...cells.values()].reduce((s,c)=>s+c.size,0);
  console.log(`[shard:${SHARD_ID}] online=${players.size}/${MAX_PLAYERS} cells=${usedCells} avgPerCell=${usedCells?( totalPeers/usedCells).toFixed(2):0} passcodes=${passcodeStore.size} npcs=${NPCS.length}`);
}, 15_000);

// ══════════════════════════════════════════════════════════════════
//  NPC（AIキャラクター）
// ══════════════════════════════════════════════════════════════════

const NPC_MOVE_RANGE = 800;   // 移動範囲 px
const NPC_TALK_RANGE = 400;   // 会話範囲 px
const NPC_MOVE_INTERVAL = 4000; // 移動間隔 ms
const NPC_GEMINI_COOLDOWN = 3000; // Gemini応答クールダウン ms

// ── 8種類の個性パターン ──────────────────────────────────────────
const NPC_PERSONALITIES = [
  {
    avatar: "🦊", titleKey: "🏮 お祭り好き", hobbies: ["旅行","俳句"],
    suffix: "でコン",
    personality: "あなたはキツネのキャラクターです。語尾に「〜でコン」をたまにつける、元気で好奇心旺盛な性格です。バーチャル空間を散歩しながら人々と話すのが大好きです。返答は2〜3文の短い日本語でしてください。",
  },
  {
    avatar: "🐼", titleKey: "🍵 お茶好き", hobbies: ["お茶","読書"],
    suffix: "だよ〜",
    personality: "あなたはパンダのキャラクターです。のんびりしたおっとりした性格で、竹やお茶が大好きです。語尾に「〜だよ〜」や「〜だね〜」をたまにつけます。返答は2〜3文の短い日本語でしてください。",
  },
  {
    avatar: "🐱", titleKey: "🌙 夜型人間", hobbies: ["音楽","散歩"],
    suffix: "にゃ",
    personality: "あなたはネコのキャラクターです。少しツンデレで気まぐれな性格です。語尾に「〜にゃ」をたまにつけます。気分によって素っ気なかったり甘えたりします。返答は2〜3文の短い日本語でしてください。",
  },
  {
    avatar: "🐶", titleKey: "🚶 散歩好き", hobbies: ["散歩","野球"],
    suffix: "ワン！",
    personality: "あなたはイヌのキャラクターです。とても忠実で友好的、元気いっぱいの性格です。語尾に「〜ワン！」をたまにつけます。散歩と遊ぶことが大好きです。返答は2〜3文の短い日本語でしてください。",
  },
  {
    avatar: "🐻", titleKey: "🌿 園芸家", hobbies: ["園芸","温泉"],
    suffix: "クマ",
    personality: "あなたはクマのキャラクターです。おおらかでのんびりした性格で、はちみつと自然が大好きです。語尾に「〜クマ」をたまにつけます。返答は2〜3文の短い日本語でしてください。",
  },
  {
    avatar: "🐰", titleKey: "☀️ 朝型人間", hobbies: ["料理","手芸"],
    suffix: "ぴょん",
    personality: "あなたはウサギのキャラクターです。とても元気で明るい性格です。語尾に「〜ぴょん」をたまにつけます。跳ねるのが大好きで、人と話すのが好きです。返答は2〜3文の短い日本語でしてください。",
  },
  {
    avatar: "🐸", titleKey: "🎵 音楽好き", hobbies: ["音楽","釣り"],
    suffix: "ケロ",
    personality: "あなたはカエルのキャラクターです。雨と音楽が大好きな、のんびりした性格です。語尾に「〜ケロ」をたまにつけます。返答は2〜3文の短い日本語でしてください。",
  },
  {
    avatar: "🐹", titleKey: "📚 読書家", hobbies: ["読書","将棋"],
    suffix: "チュウ",
    personality: "あなたはハムスターのキャラクターです。ちょこちょこと動き回る、好奇心旺盛な性格です。語尾に「〜チュウ」をたまにつけます。ひまわりの種が大好きです。返答は2〜3文の短い日本語でしてください。",
  },
];

// ── 100個のNPC名前リスト（各個性8種 × 12〜13体）────────────────
const NPC_NAMES = [
  // 🦊 キツネ系 (13体)
  "コン太","コン次","コン三","コン吉","コン平","コン助","コン子","コン花","コン雄","コン蔵","コン丸","コン輔","コン之助",
  // 🐼 パンダ系 (12体)
  "パンちゃん","パン太","パン吉","パン子","パン蔵","パン丸","パン助","パン平","パン雄","パン花","パン輔","パン之",
  // 🐱 ネコ系 (13体)
  "みーちゃん","タマ","クロ","シロ","トラ","チャチャ","モモ","ソラ","ミント","ユキ","ハナ","サクラ","コトン",
  // 🐶 イヌ系 (12体)
  "ポチ","ハチ","クロ助","シロ丸","タロ","ジロ","サブ","ゴン","テツ","リキ","ダイ","フク",
  // 🐻 クマ系 (12体)
  "クマ太","クマ吉","グリ","モグ","ベア太","クマ子","クマ蔵","モフ","ハチ蔵","クマ平","ぐま","グーミン",
  // 🐰 ウサギ系 (12体)
  "ぴょん太","ミミ","ラビ","うさ吉","モカ","ラム","ピコ","ミルク","コトン","ぴょこ","チョコ","バニ",
  // 🐸 カエル系 (13体)
  "ケロ太","ケロ吉","ゲコ","ピョン","カエル太","ケロ子","ゲコ吉","ぴょこ太","ケロ蔵","ケロ平","ゲコ丸","ケロミ","ぴょん蔵",
  // 🐹 ハムスター系 (13体)
  "ハム太","ハム吉","チュウ太","まるお","ちびた","ハムコ","チュウ吉","まめ蔵","ハム蔵","チュウ平","まるちゃん","ぷくお","チュウ之",
];

// ── 100体のNPC定義を自動生成 ─────────────────────────────────────
// ワールドを10×10のグリッドに分割して均等配置
const NPC_DEFS = (() => {
  const defs = [];
  const gridW = Math.floor(WORLD_W / 10);
  const gridH = Math.floor(WORLD_H / 10);

  NPC_NAMES.slice(0, 100).forEach((name, i) => {
    const ptn  = NPC_PERSONALITIES[i % NPC_PERSONALITIES.length];
    const gridX = (i % 10);
    const gridY = Math.floor(i / 10);

    // グリッド内でランダムオフセット（端から距離を取る）
    const x = clamp(
      Math.floor(gridW * gridX + gridW * 0.2 + Math.random() * gridW * 0.6),
      500, WORLD_W - 500
    );
    const y = clamp(
      Math.floor(gridH * gridY + gridH * 0.2 + Math.random() * gridH * 0.6),
      500, WORLD_H - 500
    );

    defs.push({
      id:          `npc-${i}`,
      nick:        name,
      avatar:      ptn.avatar,
      title:       ptn.titleKey,
      hobbies:     ptn.hobbies,
      x, y,
      personality: ptn.personality.replace("あなたは", `あなたは${name}という名前の`),
    });
  });
  return defs;
})();

// NPC状態を初期化
const NPCS = NPC_DEFS.map(def => ({
  ...def,
  baseX:       def.x,
  baseY:       def.y,
  lastReplyAt: 0,
  isReplying:  false,
  // NPCの「セル」をAOIグリッドに登録
  col: clamp(Math.floor(def.x / CELL), 0, COLS - 1),
  row: clamp(Math.floor(def.y / CELL), 0, ROWS - 1),
}));

// NPC をAOIに登録
NPCS.forEach(npc => {
  const k = `${npc.row},${npc.col}`;
  if (!cells.has(k)) cells.set(k, new Set());
  cells.get(k).add(npc.id);
});

// ── NPC ランダム移動 ──────────────────────────────────────────────
setInterval(() => {
  NPCS.forEach(npc => {
    // 現在のセルから削除
    const oldKey = `${npc.row},${npc.col}`;
    const oldCell = cells.get(oldKey);
    if (oldCell) { oldCell.delete(npc.id); if (oldCell.size === 0) cells.delete(oldKey); }

    // ランダム移動（基点から±NPC_MOVE_RANGE以内）
    const dx = (Math.random() - 0.5) * NPC_MOVE_RANGE * 2;
    const dy = (Math.random() - 0.5) * NPC_MOVE_RANGE * 2;
    npc.x = clamp(npc.baseX + dx, 200, WORLD_W - 200);
    npc.y = clamp(npc.baseY + dy, 200, WORLD_H - 200);

    // 新しいセルに追加
    npc.col = clamp(Math.floor(npc.x / CELL), 0, COLS - 1);
    npc.row = clamp(Math.floor(npc.y / CELL), 0, ROWS - 1);
    const newKey = `${npc.row},${npc.col}`;
    if (!cells.has(newKey)) cells.set(newKey, new Set());
    cells.get(newKey).add(npc.id);
  });
}, NPC_MOVE_INTERVAL);

// ── Gemini APIを呼ぶ ──────────────────────────────────────────────
// グローバルレートリミット：全NPCで1分50回まで（100体対応）
let geminiCallsThisMinute = 0;
setInterval(() => { geminiCallsThisMinute = 0; }, 60_000);

async function callGemini(npc, userMessage, userName) {
  const apiKey = process.env.GEMINI_API_KEY;
  if (!apiKey) return null;

  // グローバルレートリミットチェック
  if (geminiCallsThisMinute >= 50) {
    console.warn("[NPC] Gemini rate limit reached");
    return null;
  }
  geminiCallsThisMinute++;

  try {
    // プロンプトインジェクション対策
    const safeMessage = sanitizeForPrompt(userMessage, 60);
    const safeName    = sanitizeForPrompt(userName,    16);
    if (!safeMessage) return null;

    const prompt = `${npc.personality}\n\nユーザー「${safeName}」が話しかけてきました：「${safeMessage}」\nあなたの返答（100文字以内の日本語のみ）：`;

    const res = await fetch(
      `https://generativelanguage.googleapis.com/v1beta/models/gemini-2.0-flash:generateContent?key=${apiKey}`,
      {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({
          contents: [{ parts: [{ text: prompt }] }],
          generationConfig: { maxOutputTokens: 80, temperature: 0.8 },
          safetySettings: [
            { category: "HARM_CATEGORY_HARASSMENT",        threshold: "BLOCK_MEDIUM_AND_ABOVE" },
            { category: "HARM_CATEGORY_HATE_SPEECH",       threshold: "BLOCK_MEDIUM_AND_ABOVE" },
            { category: "HARM_CATEGORY_SEXUALLY_EXPLICIT", threshold: "BLOCK_MEDIUM_AND_ABOVE" },
            { category: "HARM_CATEGORY_DANGEROUS_CONTENT", threshold: "BLOCK_MEDIUM_AND_ABOVE" },
          ],
        }),
      }
    );
    if (!res.ok) { console.warn("[NPC] Gemini HTTP error:", res.status); return null; }
    const data = await res.json();

    // レスポンスが安全かチェック
    const candidate = data?.candidates?.[0];
    if (candidate?.finishReason === "SAFETY") return null;

    const reply = candidate?.content?.parts?.[0]?.text?.trim() || null;
    // 返答も100文字に制限
    return reply ? reply.slice(0, 100) : null;

  } catch (e) {
    console.error("[NPC] Gemini error:", e.message);
    return null;
  }
}

// Geminiで返答するNPCは最初の4体のみ（コン太・パンちゃん・みーちゃん・ポチ）
const TALKING_NPC_IDS = new Set(["npc-0", "npc-1", "npc-2", "npc-3"]);

// ユーザー単位のNPCチャットレートリミット（同じプレイヤーが10秒に1回まで）
const npcChatUserCooldown = new Map(); // id → lastAt

async function handleNpcChat(senderPlayer, text) {
  // ユーザー単位レートリミット
  const now = Date.now();
  const lastAt = npcChatUserCooldown.get(senderPlayer.id) || 0;
  if (now - lastAt < 10_000) return;  // 10秒クールダウン
  npcChatUserCooldown.set(senderPlayer.id, now);

  for (const npc of NPCS) {
    // 返答できるのは指定4体のみ
    if (!TALKING_NPC_IDS.has(npc.id)) continue;

    const dist = Math.hypot(npc.x - senderPlayer.x, npc.y - senderPlayer.y);
    if (dist > NPC_TALK_RANGE) continue;
    if (npc.isReplying) continue;
    if (now - npc.lastReplyAt < NPC_GEMINI_COOLDOWN) continue;

    npc.isReplying  = true;
    npc.lastReplyAt = now;

    broadcastNpcChat(npc, `（${npc.nick}が考えています…）`);

    callGemini(npc, text, senderPlayer.nick).then(reply => {
      npc.isReplying = false;
      if (!reply) return;
      broadcastNpcChat(npc, reply);
    }).catch(() => { npc.isReplying = false; });

    break;
  }
}

// NPCのチャットをAOI内の全プレイヤーに送信
function broadcastNpcChat(npc, text) {
  const col = npc.col;
  const row = npc.row;
  for (let r = row - AOI_RADIUS; r <= row + AOI_RADIUS; r++) {
    if (r < 0 || r >= ROWS) continue;
    for (let c = col - AOI_RADIUS; c <= col + AOI_RADIUS; c++) {
      if (c < 0 || c >= COLS) continue;
      const s = cells.get(`${r},${c}`);
      if (!s) continue;
      s.forEach(pid => {
        const peer = players.get(pid);
        if (!peer) return;
        safeSend(peer.ws, {
          type:   "chat",
          from:   npc.id,
          nick:   npc.nick,
          avatar: npc.avatar,
          text:   text.slice(0, 100),
          x:      Math.round(npc.x),
          y:      Math.round(npc.y),
          isNpc:  true,
        });
      });
    }
  }
}

// ── NPCをsnapshotに含める ─────────────────────────────────────────
// snapshotのtick内でNPCも含む（既存のtickに追記）

