#!/usr/bin/env node
'use strict';
/* ============================================================================
 * 砚 · INKBOARD 协作服务端
 *
 * 零依赖：只用了 Node 内置的 http / crypto / fs / path / url，
 * WebSocket 握手与帧编解码全部手写（RFC 6455），不需要 npm install。
 *
 *   node server.js            # 默认 8080
 *   PORT=3000 node server.js
 *
 * 协议（JSON over WebSocket，全部为文本帧）：
 *   客户端 → 服务端
 *     {t:'hello',  name?}              进入房间，服务端回 init
 *     {t:'ops',    ops:[...]}          一组画布操作
 *     {t:'cursor', x, y}               光标世界坐标（高频，不落盘）
 *     {t:'edit',   id|null}            正在编辑某张便签
 *     {t:'name',   name}               改名
 *   服务端 → 客户端
 *     {t:'init',   you, peers, board}
 *     {t:'ops',    from, ops}
 *     {t:'cursor', id, x, y}
 *     {t:'peer',   peer}               新成员加入
 *     {t:'leave',  id}
 *     {t:'edit',   id, note}
 *     {t:'name',   id, name}
 *
 * 操作（op）种类：
 *   n+ 新增便签   {k:'n+', note}
 *   n~ 修改便签   {k:'n~', id, patch:{x,y,w,h,color,text}}
 *   n- 删除便签   {k:'n-', ids:[]}          （级联删除相关连线）
 *   s+ 新增笔迹   {k:'s+', stroke}
 *   s- 删除笔迹   {k:'s-', ids:[]}
 *   c+ 新增连线   {k:'c+', conn}
 *   c- 删除连线   {k:'c-', ids:[]}
 * ========================================================================== */

const http = require('http');
const crypto = require('crypto');
const fs = require('fs');
const path = require('path');

const PORT = Number(process.env.PORT) || 8080;
const HOST = process.env.HOST || '0.0.0.0';
const ROOT = __dirname;
const DATA_DIR = path.join(ROOT, 'data');
const WS_GUID = '258EAFA5-E914-47DA-95CA-C5AB0DC85B11';

/* 容量护栏：防止单条消息或单个房间无限膨胀 */
const LIMITS = { msgBytes: 512 * 1024, text: 4000, notes: 800, strokes: 4000, conns: 1500, peers: 20 };

const NAMES = ['林川', 'Ava', '柯屿', '青梧', '沈砚', 'Mira', '知白', 'Rye', '子期', 'Noe', '南屿', 'Kai'];
const COLORS = ['#2F5FD0', '#0E8A6A', '#A63E9B', '#C2410C', '#0369A1', '#7C3AED', '#15803D', '#BE123C'];

/* ---------------------------------------------------------------- 工具 */
const num = (v, dflt) => (typeof v === 'number' && isFinite(v) ? v : dflt);
const clamp = (v, a, b) => (v < a ? a : v > b ? b : v);
const str = (v, max) => (typeof v === 'string' ? v.slice(0, max) : '');
const safeColor = v => (/^#[0-9a-fA-F]{6}$/.test(v || '') ? v : '#FFE066');
const safeId = v => (/^[A-Za-z0-9_-]{1,40}$/.test(v || '') ? v : 'anon');
const pick = arr => arr[Math.floor(Math.random() * arr.length)];

function newId() {
  return Date.now().toString(36) + Math.random().toString(36).slice(2, 8);
}

/* ------------------------------------------------------- WebSocket 帧编解码 */

/** 编码一帧（服务端→客户端不掩码） */
function encodeFrame(opcode, payload) {
  const len = payload.length;
  let head;
  if (len < 126) {
    head = Buffer.alloc(2);
    head[1] = len;
  } else if (len < 65536) {
    head = Buffer.alloc(4);
    head[1] = 126;
    head.writeUInt16BE(len, 2);
  } else {
    head = Buffer.alloc(10);
    head[1] = 127;
    head.writeBigUInt64BE(BigInt(len), 2);
  }
  head[0] = 0x80 | opcode; // FIN + opcode
  return Buffer.concat([head, payload]);
}

/**
 * 增量解析器：处理分片、掩码、16/64 位长度、ping/pong/close。
 * 返回 feed(chunk) 函数。
 */
function createFrameParser(handlers) {
  let buf = Buffer.alloc(0);
  let fragOpcode = 0;
  let fragChunks = null;

  return function feed(chunk) {
    buf = Buffer.concat([buf, chunk]);

    for (;;) {
      if (buf.length < 2) return;
      const b0 = buf[0], b1 = buf[1];
      const fin = (b0 & 0x80) !== 0;
      const opcode = b0 & 0x0f;
      const masked = (b1 & 0x80) !== 0;
      let len = b1 & 0x7f;
      let off = 2;

      if (len === 126) {
        if (buf.length < 4) return;
        len = buf.readUInt16BE(2);
        off = 4;
      } else if (len === 127) {
        if (buf.length < 10) return;
        const big = buf.readBigUInt64BE(2);
        if (big > BigInt(LIMITS.msgBytes)) { handlers.tooBig(); return; }
        len = Number(big);
        off = 10;
      }

      let mask = null;
      if (masked) {
        if (buf.length < off + 4) return;
        mask = buf.subarray(off, off + 4);
        off += 4;
      }
      if (buf.length < off + len) return;

      const payload = Buffer.from(buf.subarray(off, off + len));
      if (mask) for (let i = 0; i < payload.length; i++) payload[i] ^= mask[i & 3];
      buf = buf.subarray(off + len);

      if (opcode === 0x8) { handlers.close(1000); return; }          // close
      if (opcode === 0x9) { handlers.ping(payload); continue; }      // ping → 回 pong
      if (opcode === 0xa) { handlers.pong(); continue; }             // pong

      if (opcode === 0x0) {                                          // continuation
        if (fragChunks === null) { handlers.close(1002); return; }
        fragChunks.push(payload);
      } else {
        fragOpcode = opcode;
        fragChunks = [payload];
      }

      if (fin && fragChunks !== null) {
        const data = Buffer.concat(fragChunks);
        const op = fragOpcode;
        fragChunks = null;
        if (op === 0x1) handlers.text(data.toString('utf8'));
        // 0x2 二进制帧：本服务不使用，直接丢弃
      }
    }
  };
}

/* ------------------------------------------------------------------ 房间 */

const rooms = new Map();

function loadRoom(id) {
  try {
    const p = path.join(DATA_DIR, id + '.json');
    if (!fs.existsSync(p)) return null;
    const d = JSON.parse(fs.readFileSync(p, 'utf8'));
    return {
      notes: Array.isArray(d.notes) ? d.notes : [],
      strokes: Array.isArray(d.strokes) ? d.strokes : [],
      conns: Array.isArray(d.conns) ? d.conns : []
    };
  } catch (e) {
    console.warn('[warn] 读取房间快照失败，按空房间启动:', id, e.message);
    return null;
  }
}

function getRoom(id) {
  let r = rooms.get(id);
  if (r) return r;
  const disk = loadRoom(id);
  r = {
    id,
    notes: disk ? disk.notes : [],
    strokes: disk ? disk.strokes : [],
    conns: disk ? disk.conns : [],
    peers: new Map(),
    saveTimer: null
  };
  rooms.set(id, r);
  return r;
}

function markDirty(room) {
  if (room.saveTimer) return;
  room.saveTimer = setTimeout(() => {
    room.saveTimer = null;
    saveRoom(room);
  }, 1500);
}

function saveRoom(room) {
  try {
    fs.mkdirSync(DATA_DIR, { recursive: true });
    const tmp = path.join(DATA_DIR, room.id + '.json.tmp');
    fs.writeFileSync(tmp, JSON.stringify({
      savedAt: new Date().toISOString(),
      notes: room.notes, strokes: room.strokes, conns: room.conns
    }));
    fs.renameSync(tmp, path.join(DATA_DIR, room.id + '.json'));
  } catch (e) {
    console.warn('[warn] 写入房间快照失败:', room.id, e.message);
  }
}

/* ---------------------------------------------------------- 操作校验与应用 */

function sanitizeOp(op) {
  if (!op || typeof op !== 'object') return null;
  switch (op.k) {
    case 'n+': {
      const n = op.note;
      if (!n || typeof n.id !== 'string') return null;
      return {
        k: 'n+',
        note: {
          id: safeId(n.id),
          x: num(n.x, 0), y: num(n.y, 0),
          w: clamp(num(n.w, 200), 60, 1200), h: clamp(num(n.h, 132), 40, 1200),
          color: safeColor(n.color), text: str(n.text, LIMITS.text)
        }
      };
    }
    case 'n~': {
      if (typeof op.id !== 'string') return null;
      const p = op.patch || {};
      const out = { k: 'n~', id: safeId(op.id), patch: {} };
      if (typeof p.x === 'number' && isFinite(p.x)) out.patch.x = p.x;
      if (typeof p.y === 'number' && isFinite(p.y)) out.patch.y = p.y;
      if (typeof p.w === 'number' && isFinite(p.w)) out.patch.w = clamp(p.w, 60, 1200);
      if (typeof p.h === 'number' && isFinite(p.h)) out.patch.h = clamp(p.h, 40, 1200);
      if (typeof p.color === 'string') out.patch.color = safeColor(p.color);
      if (typeof p.text === 'string') out.patch.text = str(p.text, LIMITS.text);
      return Object.keys(out.patch).length ? out : null;
    }
    case 'n-':
    case 's-':
    case 'c-': {
      if (!Array.isArray(op.ids)) return null;
      const ids = op.ids.filter(x => typeof x === 'string').map(safeId).slice(0, 200);
      return ids.length ? { k: op.k, ids } : null;
    }
    case 's+': {
      const s = op.stroke;
      if (!s || typeof s.id !== 'string' || !Array.isArray(s.pts)) return null;
      const pts = s.pts.slice(0, 6000).map(p => ({ x: num(p && p.x, 0), y: num(p && p.y, 0) }));
      if (!pts.length) return null;
      return { k: 's+', stroke: { id: safeId(s.id), color: safeColor(s.color), w: clamp(num(s.w, 4), 1, 40), pts } };
    }
    case 'c+': {
      const c = op.conn;
      if (!c || typeof c.id !== 'string' || typeof c.a !== 'string' || typeof c.b !== 'string') return null;
      return { k: 'c+', conn: { id: safeId(c.id), a: safeId(c.a), b: safeId(c.b) } };
    }
    /* 笔迹增量追加：绘制过程中持续补点，避免整条重传造成的 O(n²) 流量 */
    case 's.': {
      if (typeof op.id !== 'string' || !Array.isArray(op.pts)) return null;
      const pts = op.pts.slice(0, 2000).map(p => ({ x: num(p && p.x, 0), y: num(p && p.y, 0) }));
      if (!pts.length) return null;
      return { k: 's.', id: safeId(op.id), pts };
    }
    default:
      return null;
  }
}

function applyOps(room, ops) {
  for (const op of ops) {
    switch (op.k) {
      case 'n+':
        if (room.notes.length < LIMITS.notes && !room.notes.some(n => n.id === op.note.id)) {
          room.notes.push(op.note);
        }
        break;
      case 'n~': {
        const n = room.notes.find(x => x.id === op.id);
        if (n) Object.assign(n, op.patch);
        break;
      }
      case 'n-': {
        const ids = new Set(op.ids);
        room.notes = room.notes.filter(n => !ids.has(n.id));
        room.conns = room.conns.filter(c => !ids.has(c.a) && !ids.has(c.b));
        break;
      }
      case 's+':
        if (!room.strokes.some(s => s.id === op.stroke.id)) {
          room.strokes.push(op.stroke);
          if (room.strokes.length > LIMITS.strokes) {
            room.strokes.splice(0, room.strokes.length - LIMITS.strokes);
          }
        }
        break;
      case 's-': {
        const ids = new Set(op.ids);
        room.strokes = room.strokes.filter(s => !ids.has(s.id));
        break;
      }
      case 'c+':
        if (room.conns.length < LIMITS.conns && !room.conns.some(c => c.id === op.conn.id)) {
          room.conns.push(op.conn);
        }
        break;
      case 'c-': {
        const ids = new Set(op.ids);
        room.conns = room.conns.filter(c => !ids.has(c.id));
        break;
      }
      case 's.': {
        const s = room.strokes.find(x => x.id === op.id);
        if (!s) break;
        s.pts = s.pts.concat(op.pts);
        if (s.pts.length > 6000) s.pts.splice(0, s.pts.length - 6000);
        break;
      }
    }
  }
  markDirty(room);
}

/* ------------------------------------------------------------------ 广播 */

function sendRaw(client, obj) {
  if (client.sock.destroyed) return;
  try {
    client.sock.write(encodeFrame(0x1, Buffer.from(JSON.stringify(obj), 'utf8')));
  } catch (e) { /* 客户端已断开，忽略 */ }
}

function broadcast(room, obj, exceptId) {
  const buf = encodeFrame(0x1, Buffer.from(JSON.stringify(obj), 'utf8'));
  room.peers.forEach(p => {
    if (p.id === exceptId) return;
    if (p.sock.destroyed) return;
    try { p.sock.write(buf); } catch (e) { /* ignore */ }
  });
}

function peerPublic(p) {
  return { id: p.id, name: p.name, color: p.color, x: p.x, y: p.y, note: p.note };
}

/* -------------------------------------------------------------- 消息处理 */

function handleMessage(client, room, text) {
  if (text.length > LIMITS.msgBytes) return;
  let msg;
  try { msg = JSON.parse(text); } catch (e) { return; }
  if (!msg || typeof msg !== 'object') return;

  switch (msg.t) {
    case 'hello':
      if (typeof msg.name === 'string' && msg.name.trim()) {
        client.name = str(msg.name.trim(), 16);
        broadcast(room, { t: 'name', id: client.id, name: client.name }, client.id);
      }
      break;

    case 'name': {
      const n = str((msg.name || '').trim(), 16);
      if (n) { client.name = n; broadcast(room, { t: 'name', id: client.id, name: n }, client.id); }
      break;
    }

    case 'ops': {
      if (!Array.isArray(msg.ops)) return;
      const ops = msg.ops.slice(0, 200).map(sanitizeOp).filter(Boolean);
      if (!ops.length) return;
      applyOps(room, ops);
      broadcast(room, { t: 'ops', from: client.id, ops }, client.id);
      break;
    }

    case 'cursor': {
      client.x = num(msg.x, 0);
      client.y = num(msg.y, 0);
      // 高频消息，不做 JSON 广播以外的处理
      broadcast(room, { t: 'cursor', id: client.id, x: client.x, y: client.y }, client.id);
      break;
    }

    case 'edit': {
      client.note = typeof msg.id === 'string' ? safeId(msg.id) : null;
      broadcast(room, { t: 'edit', id: client.id, note: client.note }, client.id);
      break;
    }
  }
}

/* -------------------------------------------------------------- 连接管理 */

function onConnection(sock, roomId, req) {
  const room = getRoom(roomId);
  if (room.peers.size >= LIMITS.peers) {
    sock.end('HTTP/1.1 503 Service Unavailable\r\n\r\n房间已满');
    return;
  }

  const key = req.headers['sec-websocket-key'];
  if (!key) { sock.destroy(); return; }
  const accept = crypto.createHash('sha1').update(key + WS_GUID).digest('base64');
  sock.write(
    'HTTP/1.1 101 Switching Protocols\r\n' +
    'Upgrade: websocket\r\n' +
    'Connection: Upgrade\r\n' +
    'Sec-WebSocket-Accept: ' + accept + '\r\n\r\n'
  );
  sock.setNoDelay(true);

  const used = new Set([...room.peers.values()].map(p => p.name));
  const free = NAMES.filter(n => !used.has(n));

  const client = {
    id: newId(),
    sock,
    room,
    name: free.length ? pick(free) : pick(NAMES) + Math.floor(Math.random() * 90 + 10),
    color: pick(COLORS),
    x: 0, y: 0,
    note: null,
    alive: true
  };
  room.peers.set(client.id, client);

  // 先让本人知道全部状态
  sendRaw(client, {
    t: 'init',
    you: { id: client.id, name: client.name, color: client.color },
    peers: [...room.peers.values()].filter(p => p.id !== client.id).map(peerPublic),
    board: { notes: room.notes, strokes: room.strokes, conns: room.conns }
  });
  // 再告诉其他人
  broadcast(room, { t: 'peer', peer: peerPublic(client) }, client.id);

  console.log('[join ] %s  room=%s  %s（在线 %d）', client.name, room.id, client.id, room.peers.size);

  const feed = createFrameParser({
    text: t => handleMessage(client, room, t),
    ping: p => { try { sock.write(encodeFrame(0xa, p)); } catch (e) {} },
    pong: () => { client.alive = true; },
    close: () => { try { sock.destroy(); } catch (e) {} },
    tooBig: () => { try { sock.destroy(); } catch (e) {} }
  });

  sock.on('data', feed);
  sock.on('error', () => cleanup(client));
  sock.on('close', () => cleanup(client));
  // 半关闭兜底：对端 FIN 后主动销毁，确保 leave 广播一定发出
  sock.on('end', () => { try { sock.destroy(); } catch (e) {} });
}

function cleanup(client) {
  const room = client.room;
  if (!room.peers.has(client.id)) return;
  room.peers.delete(client.id);
  broadcast(room, { t: 'leave', id: client.id });
  console.log('[leave] %s  room=%s（在线 %d）', client.name, room.id, room.peers.size);
}

/* 心跳：25 秒一次 ping，连续两次无 pong 视为掉线 */
setInterval(() => {
  const now = Date.now();
  rooms.forEach(room => {
    room.peers.forEach(p => {
      if (!p.alive) { try { p.sock.destroy(); } catch (e) {} return; }
      p.alive = false;
      try { p.sock.write(encodeFrame(0x9, Buffer.from(String(now)))); } catch (e) {}
    });
  });
}, 25000);

/* ------------------------------------------------------------ 静态文件 */

const MIME = {
  '.html': 'text/html; charset=utf-8',
  '.js': 'text/javascript; charset=utf-8',
  '.css': 'text/css; charset=utf-8',
  '.json': 'application/json; charset=utf-8',
  '.svg': 'image/svg+xml',
  '.png': 'image/png',
  '.ico': 'image/x-icon'
};

const server = http.createServer((req, res) => {
  let pathname;
  try {
    pathname = decodeURIComponent(new URL(req.url, 'http://x').pathname);
  } catch (e) {
    res.writeHead(400); res.end('bad request'); return;
  }

  if (pathname === '/healthz') {
    res.writeHead(200, { 'Content-Type': 'application/json' });
    res.end(JSON.stringify({
      ok: true,
      rooms: [...rooms.values()].map(r => ({ id: r.id, peers: r.peers.size, notes: r.notes.length }))
    }));
    return;
  }

  let file = pathname === '/' ? 'index.html' : pathname.replace(/^\/+/, '');
  const full = path.resolve(ROOT, file);
  if (!full.startsWith(ROOT)) { res.writeHead(403); res.end('forbidden'); return; }

  fs.readFile(full, (err, data) => {
    if (err) {
      res.writeHead(404, { 'Content-Type': 'text/plain; charset=utf-8' });
      res.end('404');
      return;
    }
    res.writeHead(200, {
      'Content-Type': MIME[path.extname(full).toLowerCase()] || 'application/octet-stream',
      'Cache-Control': 'no-cache'
    });
    res.end(data);
  });
});

server.on('upgrade', (req, sock, head) => {
  const u = new URL(req.url, 'http://x');
  if (u.pathname !== '/ws') { sock.destroy(); return; }
  const roomId = safeId(u.searchParams.get('room') || 'main');
  sock.on('error', () => {});
  onConnection(sock, roomId, req);
  if (head && head.length) sock.emit('data', head);
});

server.listen(PORT, HOST, () => {
  console.log('砚 · INKBOARD 协作服务已启动');
  console.log('  本地: http://localhost:%d/', PORT);
  console.log('  房间: http://localhost:%d/?room=main', PORT);
  console.log('  成员上限 %d 人/房间，状态写入 %s', LIMITS.peers, DATA_DIR);
});

function shutdown() {
  console.log('\n正在保存房间状态…');
  rooms.forEach(saveRoom);
  process.exit(0);
}
process.on('SIGINT', shutdown);
process.on('SIGTERM', shutdown);
