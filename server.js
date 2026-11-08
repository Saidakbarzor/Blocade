const express = require('express');
const http = require('http');
const { Server } = require('socket.io');
const path = require('path');
const fs = require('fs');
const crypto = require('crypto');

const app = express();
const server = http.createServer(app);
const io = new Server(server);
app.use(express.static(path.join(__dirname, 'public')));

/* ---------- База игроков (файл data.json) ---------- */
const DB_FILE = process.env.DB_FILE || path.join(__dirname, 'data.json');
let users = {};
try { users = JSON.parse(fs.readFileSync(DB_FILE, 'utf8')); } catch (e) {}
let dirty = false;
const save = () => { dirty = true; };
setInterval(() => { if (dirty) { dirty = false; fs.writeFile(DB_FILE, JSON.stringify(users), () => {}); } }, 5000);

const COUNTRIES = ['UZ','RU','KZ','KG','TJ','TM','AZ','AM','GE','UA','BY','TR','US','GB','DE','FR','ES','IT','CN','JP','KR','IN','BR','MA','EG','SA','AE','PL','CL','CU'];
const pub = (u) => u && u.nick ? { id: u.id, nick: u.nick, country: u.country, rating: u.rating, games: u.games, wins: u.wins } : null;

/* ---------- Проверка Telegram ---------- */
function tgUser(initData) {
  if (!initData || !process.env.BOT_TOKEN) return null;
  try {
    const p = new URLSearchParams(initData);
    const hash = p.get('hash'); p.delete('hash');
    const str = [...p.entries()].sort(([a], [b]) => (a < b ? -1 : 1)).map(([k, v]) => k + '=' + v).join('\n');
    const secret = crypto.createHmac('sha256', 'WebAppData').update(process.env.BOT_TOKEN).digest();
    if (crypto.createHmac('sha256', secret).update(str).digest('hex') !== hash) return null;
    return JSON.parse(p.get('user'));
  } catch (e) { return null; }
}

/* ---------- Правила игры ---------- */
const MODES = {
  classic: { s: [[4, 8], [4, 0]], goal: (i, x, y) => y === (i ? 8 : 0) },
  finish:  { s: [[1, 6], [7, 6]], goal: (i, x, y) => y === 0 },
  quad:    { s: [[4, 8], [4, 0], [0, 4], [8, 4]], goal: (i, x, y) => x === 4 && y === 4 }
};
const TIMES = { dash: [180000, 1000], sprint: [45000, 1000] };
const D = [[0, 1], [0, -1], [1, 0], [-1, 0]];
const inb = (x, y) => x >= 0 && y >= 0 && x < 9 && y < 9;
const has = (g, o, x, y) => g.set.has(o + x + ',' + y);

function blocked(g, x, y, dx, dy) {
  if (dy === 1) return has(g, 'h', x, y) || has(g, 'h', x - 1, y);
  if (dy === -1) return has(g, 'h', x, y - 1) || has(g, 'h', x - 1, y - 1);
  if (dx === 1) return has(g, 'v', x, y) || has(g, 'v', x, y - 1);
  return has(g, 'v', x - 1, y) || has(g, 'v', x - 1, y - 1);
}

function moves(g, pi) {
  const me = g.pl[pi], res = [];
  const occ = (x, y) => g.pl.some((q, j) => j !== pi && q.alive && q.x === x && q.y === y);
  for (const [dx, dy] of D) {
    const nx = me.x + dx, ny = me.y + dy;
    if (!inb(nx, ny) || blocked(g, me.x, me.y, dx, dy)) continue;
    if (!occ(nx, ny)) { res.push([nx, ny]); continue; }
    const jx = nx + dx, jy = ny + dy;
    if (inb(jx, jy) && !blocked(g, nx, ny, dx, dy) && !occ(jx, jy)) { res.push([jx, jy]); continue; }
    for (const [sx, sy] of (dx ? [[0, 1], [0, -1]] : [[1, 0], [-1, 0]])) {
      const tx = nx + sx, ty = ny + sy;
      if (inb(tx, ty) && !blocked(g, nx, ny, sx, sy) && !occ(tx, ty)) res.push([tx, ty]);
    }
  }
  return res;
}

function hasPath(g, i) {
  const p = g.pl[i], seen = new Set([p.x + ',' + p.y]), q = [[p.x, p.y]];
  while (q.length) {
    const [x, y] = q.shift();
    if (g.M.goal(i, x, y)) return true;
    for (const [dx, dy] of D) {
      const nx = x + dx, ny = y + dy, k = nx + ',' + ny;
      if (inb(nx, ny) && !seen.has(k) && !blocked(g, x, y, dx, dy)) { seen.add(k); q.push([nx, ny]); }
    }
  }
  return false;
}

function wallOk(g, o, x, y) {
  if (o !== 'h' && o !== 'v') return false;
  if (!Number.isInteger(x) || !Number.isInteger(y) || x < 0 || y < 0 || x > 7 || y > 7) return false;
  const O = o === 'h' ? 'v' : 'h';
  if (has(g, o, x, y) || has(g, O, x, y)) return false;
  if (o === 'h' && (has(g, 'h', x - 1, y) || has(g, 'h', x + 1, y))) return false;
  if (o === 'v' && (has(g, 'v', x, y - 1) || has(g, 'v', x, y + 1))) return false;
  g.set.add(o + x + ',' + y);
  const ok = g.pl.every((p, i) => !p.alive || hasPath(g, i));
  g.set.delete(o + x + ',' + y);
  return ok;
}

/* ---------- Игры ---------- */
const games = {};
const queues = {};

function snap(g, i) {
  const now = Date.now();
  return {
    mode: g.mode, turn: g.turn, walls: g.walls,
    pl: g.pl.map((p, k) => ({
      nick: p.u.nick, country: p.u.country, rating: p.u.rating,
      x: p.x, y: p.y, w: p.w, alive: p.alive,
      ms: Math.max(0, p.ms - (k === g.turn && p.alive ? now - g.t0 : 0))
    })),
    moves: g.turn === i && g.pl[i].alive ? moves(g, i) : []
  };
}
const push = (g) => g.pl.forEach((p, i) => { if (p.s.gid === g.id) p.s.emit('state', snap(g, i)); });

function createGame(es, mode, time) {
  const M = MODES[mode], [ms, inc] = TIMES[time];
  es.sort(() => Math.random() - 0.5);
  const g = {
    id: 'g' + Math.random().toString(36).slice(2, 10), mode, M, inc, set: new Set(), walls: [],
    turn: 0, t0: Date.now(), over: false,
    pl: es.map((e, i) => ({ s: e.s, u: e.s.user, x: M.s[i][0], y: M.s[i][1], w: 10, alive: true, ms }))
  };
  games[g.id] = g;
  g.pl.forEach((p, i) => { p.s.gid = g.id; p.s.idx = i; p.s.emit('match_found', { you: i, mode, total: g.pl.length }); });
  push(g);
}

function nextTurn(g) {
  do { g.turn = (g.turn + 1) % g.pl.length; } while (!g.pl[g.turn].alive);
  g.t0 = Date.now();
}

function finish(g, w, reason) {
  if (g.over) return;
  g.over = true;
  const deltas = g.pl.map(() => 0);
  if (g.pl.length === 2) {
    const a = g.pl[w].u.rating, b = g.pl[1 - w].u.rating;
    const d = Math.round(32 * (1 - 1 / (1 + Math.pow(10, (b - a) / 400))));
    deltas[w] = d; deltas[1 - w] = -d;
  } else {
    g.pl.forEach((p, i) => { deltas[i] = i === w ? 20 : -7; });
  }
  g.pl.forEach((p, i) => {
    p.u.rating = Math.max(100, p.u.rating + deltas[i]);
    p.u.games++; if (i === w) p.u.wins++;
  });
  save();
  g.pl.forEach((p, i) => {
    if (p.s.gid === g.id) {
      p.s.emit('game_over', { winner: w, reason, delta: deltas[i], you: i });
      p.s.emit('profile', pub(p.u));
      p.s.gid = null;
    }
  });
  delete games[g.id];
}

function eliminate(g, i, reason) {
  if (g.over || !g.pl[i].alive) return;
  g.pl[i].alive = false;
  const alive = g.pl.map((p, k) => k).filter((k) => g.pl[k].alive);
  if (alive.length === 1) return finish(g, alive[0], reason);
  if (g.turn === i) nextTurn(g);
  push(g);
}

function act(s, fn) {
  const g = games[s.gid];
  if (!g || g.over || g.turn !== s.idx) return;
  const p = g.pl[s.idx];
  if (p.ms - (Date.now() - g.t0) <= 0) return eliminate(g, s.idx, 'timeout');
  if (!fn(g, p)) return s.emit('err', 'Недопустимый ход');
  if (g.over) return;
  p.ms = p.ms - (Date.now() - g.t0) + g.inc;
  nextTurn(g);
  push(g);
}

setInterval(() => {
  const now = Date.now();
  for (const id in games) {
    const g = games[id];
    if (!g.over && g.pl[g.turn].ms - (now - g.t0) <= 0) eliminate(g, g.turn, 'timeout');
  }
}, 250);

/* ---------- Подбор соперника ---------- */
function dequeue(s) { for (const k in queues) queues[k] = queues[k].filter((e) => e.s !== s); }

setInterval(() => {
  const now = Date.now();
  for (const key in queues) {
    const [mode, time] = key.split(':');
    let q = queues[key].filter((e) => e.s.connected);
    if (mode === 'quad') {
      while (q.length >= 4) createGame(q.splice(0, 4), mode, time);
    } else {
      q.sort((a, b) => a.s.user.rating - b.s.user.rating);
      for (let i = 0; i < q.length - 1; i++) {
        const a = q[i], b = q[i + 1];
        const win = 100 + 60 * Math.max(now - a.t, now - b.t) / 1000;
        if (Math.abs(a.s.user.rating - b.s.user.rating) <= win) {
          createGame([a, b], mode, time);
          q.splice(i, 2); i--;
        }
      }
    }
    queues[key] = q;
  }
}, 1000);

/* ---------- Сокеты ---------- */
io.on('connection', (s) => {
  s.user = null; s.gid = null;

  s.on('auth', ({ initData, guestId } = {}) => {
    let id = null, name = '';
    const t = tgUser(initData);
    if (t) { id = 'tg' + t.id; name = t.first_name || t.username || ''; }
    else if (process.env.ALLOW_GUEST !== 'false' && typeof guestId === 'string' && /^[\w-]{6,40}$/.test(guestId)) id = 'g' + guestId;
    if (!id) return s.emit('auth_fail', 'Открой игру через Telegram');
    if (!users[id]) users[id] = { id, nick: null, country: null, rating: 1000, games: 0, wins: 0 };
    s.user = users[id];
    s.emit('auth_ok', { profile: pub(s.user), suggest: name.replace(/[^\w.\-а-яА-ЯёЁ]/g, '').slice(0, 16), countries: COUNTRIES });
  });

  s.on('register', ({ nick, country } = {}) => {
    if (!s.user || s.user.nick) return;
    nick = String(nick || '').trim();
    if (!/^[\wа-яА-ЯёЁ.\-]{3,16}$/.test(nick)) return s.emit('reg_err', 'Ник: 3–16 символов, буквы, цифры, _ . -');
    if (!COUNTRIES.includes(country)) return s.emit('reg_err', 'Выбери страну');
    if (Object.values(users).some((u) => u.nick && u.nick.toLowerCase() === nick.toLowerCase())) return s.emit('reg_err', 'Этот ник уже занят');
    s.user.nick = nick; s.user.country = country; save();
    s.emit('profile', pub(s.user));
    s.emit('registered');
  });

  s.on('find_match', ({ mode, time } = {}) => {
    if (!s.user || !s.user.nick || !MODES[mode] || !TIMES[time]) return;
    const g = games[s.gid];
    if (g && !g.over && g.pl[s.idx].alive) return;
    s.gid = null; dequeue(s);
    const key = mode + ':' + time;
    (queues[key] = queues[key] || []).push({ s, t: Date.now() });
  });

  s.on('cancel_search', () => dequeue(s));
  s.on('move', ({ x, y } = {}) => act(s, (g, p) => {
    if (!moves(g, s.idx).some((m) => m[0] === x && m[1] === y)) return false;
    p.x = x; p.y = y;
    if (g.M.goal(s.idx, x, y)) finish(g, s.idx, 'goal');
    return true;
  }));
  s.on('wall', ({ o, x, y } = {}) => act(s, (g, p) => {
    if (p.w <= 0 || !wallOk(g, o, x, y)) return false;
    g.set.add(o + x + ',' + y); g.walls.push({ o, x, y, p: s.idx }); p.w--;
    return true;
  }));
  s.on('surrender', () => {
    const g = games[s.gid];
    if (g) { const i = s.idx; eliminate(g, i, 'surrender'); if (s.gid === g.id && g.pl[i]) s.gid = null; }
  });
  s.on('emoji', ({ e } = {}) => {
    const g = games[s.gid];
    if (!g || !['😂', '🤔', '😎', '😱', '😡'].includes(e)) return;
    g.pl.forEach((p) => { if (p.s.gid === g.id) p.s.emit('emoji', { from: s.idx, e }); });
  });

  s.on('leaders', ({ scope } = {}) => {
    if (!s.user) return;
    let all = Object.values(users).filter((u) => u.nick && u.games > 0);
    if (scope === 'country') all = all.filter((u) => u.country === s.user.country);
    all.sort((a, b) => b.rating - a.rating);
    const idx = all.findIndex((u) => u.id === s.user.id);
    s.emit('leaders', { rows: all.slice(0, 50).map(pub), rank: idx >= 0 ? idx + 1 : null });
  });

  s.on('disconnect', () => {
    dequeue(s);
    const g = games[s.gid];
    if (g) eliminate(g, s.idx, 'disconnect');
  });
});

const PORT = process.env.PORT || 3000;
server.listen(PORT, () => console.log(`Сервер запущен на порту ${PORT}`));
