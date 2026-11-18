// LyricsFx relay server.
// No packages needed: only Node.js 18 or newer.
//
// What it does:
//   1. A player proves who they are with their real Minecraft account (Mojang "hasJoined" check).
//   2. The mod sends "what I wear" + "my friend list" every few seconds.
//   3. The mod asks "what do these players near me wear?" and gets the answer back.
// It never sees your Minecraft password or access token. Everything is kept in memory only.

'use strict';
const http = require('http');
const crypto = require('crypto');
const fs = require('fs');
const path_ = require('path');

const PORT = process.env.PORT || 8080;
const DEV_MODE = process.env.DEV_MODE === '1'; // testing only: skips the Mojang check
const ONLINE_MS = 30 * 1000;                   // seen in the last 30 s = online
const FORGET_MS = 24 * 60 * 60 * 1000;         // forget players after 24 h
const SESSION_MS = 6 * 60 * 60 * 1000;         // login lasts 6 h
const MAX_BODY = 32 * 1024;
const MAX_FRIENDS = 200;
const MAX_QUERY = 100;

const CAPE_IDS = new Set(['lighthouse', 'terminal', 'sunset', 'galaxy', 'flame', 'ocean', 'forest', 'royal', 'racer', 'glitch', 'pirate', 'rainbow', 'frost', 'matrix', 'lyricsfx', 'silver', 'snow', 'blood', 'shadow', 'crimson', 'kaorushka', 'aurora', 'lava', 'neon', 'sakura', 'void', 'toxic', 'candy', 'storm', 'gold', 'cyber', 'autumn', 'abyss']);
const PATTERNS = new Set(['SOLID', 'FADE', 'LINES', 'BARS', 'CHECK', 'DIAMOND']);
// hat ids look like s_top_hat or m_crown (the game itself checks that the hat really exists)
// the owner of the mod gets a tag everywhere (decided by the verified Minecraft name)
const OWNER_NAME = 'lyriiccs';
// ranks the owner can give (the owner rank itself is automatic and cannot be given)
const ROLE_IDS = new Set(['admin', 'mod', 'tester', 'vip', 'youtuber', 'builder']);
const MAX_ROLES = 500;
const ROLES_FILE = process.env.ROLES_FILE || path_.join(__dirname, 'roles.json');
const WING_RE = /^[a-z]{1,20}$/;
const HAT_RE = /^([sm]|c)_[a-z0-9_]{1,40}$/;
const PETS = new Set(['none', 'partridge', 'ghast', 'creeper', 'cannon', 'fox', 'llama', 'slingshot', 'pillager', 'witch']);
const VISIBILITY = new Set(['everyone', 'friends', 'nobody']);

const challenges = new Map(); // serverId -> expires
const sessions = new Map();   // token -> { uuid, name, expires, lastSync }
const players = new Map();    // uuid -> { name, lastSeen, share, visibility, look, friends:Set }
const loginsByIp = new Map(); // ip -> { count, reset }
const lookups = new Map();    // name(lowercase) -> { uuid, name, at }
const roles = new Map();      // uuid -> { role, name }   (given by the owner)

const now = () => Date.now();
const isUuid = (s) => typeof s === 'string' && /^[0-9a-f]{32}$/.test(s);
const isName = (s) => typeof s === 'string' && /^[A-Za-z0-9_]{1,16}$/.test(s);
const int = (v, lo, hi, dflt) => (Number.isInteger(v) && v >= lo && v <= hi ? v : dflt);

function send(res, code, obj) {
  const body = JSON.stringify(obj);
  res.writeHead(code, { 'Content-Type': 'application/json', 'Content-Length': Buffer.byteLength(body) });
  res.end(body);
}

function readJson(req) {
  return new Promise((resolve, reject) => {
    let size = 0;
    const chunks = [];
    req.on('data', (c) => {
      size += c.length;
      if (size > MAX_BODY) { reject(new HttpError(413, 'too_big')); req.destroy(); return; }
      chunks.push(c);
    });
    req.on('end', () => {
      if (size === 0) return resolve({});
      try { resolve(JSON.parse(Buffer.concat(chunks).toString('utf8'))); }
      catch (e) { reject(new HttpError(400, 'bad_json')); }
    });
    req.on('error', reject);
  });
}

class HttpError extends Error {
  constructor(code, message) { super(message); this.code = code; }
}

function auth(req) {
  const h = req.headers['authorization'] || '';
  const token = h.startsWith('Bearer ') ? h.slice(7) : '';
  const s = sessions.get(token);
  if (!s || s.expires < now()) throw new HttpError(401, 'login_needed');
  return s;
}

// ---- cleaning what players send us (never trust the mod) ----
function cleanLook(look) {
  if (!look || typeof look !== 'object') return { cape: null, mask: 0, pet: 'none', petRight: true, hat: 'none', wing: 'none' };
  let cape = null;
  const c = look.cape;
  if (c && typeof c === 'object') {
    if (c.kind === 'preset' && CAPE_IDS.has(c.id)) {
      cape = { kind: 'preset', id: c.id };
    } else if (c.kind === 'builder' && PATTERNS.has(c.pattern)) {
      cape = {
        kind: 'builder', pattern: c.pattern,
        main: int(c.main, 0, 0xFFFFFF, 0x1565C0), second: int(c.second, 0, 0xFFFFFF, 0x0D1B4A),
        trim: int(c.trim, 0, 0xFFFFFF, 0xFFFFFF), trimOn: c.trimOn === true,
      };
    }
  }
  return {
    cape,
    mask: int(look.mask, 0, 31, 0),
    pet: PETS.has(look.pet) ? look.pet : 'none',
    petRight: look.petRight !== false,
    hat: typeof look.hat === 'string' && HAT_RE.test(look.hat) ? look.hat : 'none',
    wing: typeof look.wing === 'string' && WING_RE.test(look.wing) ? look.wing : 'none',
  };
}

function cleanFriends(list) {
  const out = new Set();
  if (Array.isArray(list)) {
    for (const f of list) {
      if (isUuid(f)) out.add(f);
      if (out.size >= MAX_FRIENDS) break;
    }
  }
  return out;
}

// ---- ranks: saved in a file (best effort) and also backed up by the owner's mod ----
function loadRoles() {
  try {
    const j = JSON.parse(fs.readFileSync(ROLES_FILE, 'utf8'));
    for (const e of Array.isArray(j) ? j : []) {
      if (isUuid(e.uuid) && ROLE_IDS.has(e.role) && isName(e.name)) roles.set(e.uuid, { role: e.role, name: e.name });
    }
  } catch (e) { /* no file yet */ }
}
function saveRoles() {
  try {
    const list = [...roles].map(([uuid, v]) => ({ uuid, role: v.role, name: v.name }));
    fs.writeFileSync(ROLES_FILE, JSON.stringify(list));
  } catch (e) { /* read-only disk: fine, the owner's mod keeps a copy */ }
}
const isOwnerSession = (s) => !!s && typeof s.name === 'string' && s.name.toLowerCase() === OWNER_NAME;
function roleOf(uuid) {
  const g = roles.get(uuid);
  if (g) return g.role;
  const p = players.get(uuid);
  if (p && typeof p.name === 'string' && p.name.toLowerCase() === OWNER_NAME) return 'owner';
  return '';
}
function roleList() {
  return [...roles].map(([uuid, v]) => ({ uuid, name: v.name, role: v.role }));
}
if (process.env.NO_ROLES_FILE !== '1') loadRoles();

function isOnline(p) { return p && now() - p.lastSeen < ONLINE_MS; }

// Can "viewer" see what "target" wears?
function canSee(viewerUuid, target) {
  if (!target || !isOnline(target) || !target.share) return false;
  if (target.visibility === 'everyone') return true;
  if (target.visibility === 'friends') return target.friends.has(viewerUuid);
  return false;
}

// ---- Mojang ----
async function mojangHasJoined(name, serverId) {
  const url = 'https://sessionserver.mojang.com/session/minecraft/hasJoined?username=' +
    encodeURIComponent(name) + '&serverId=' + encodeURIComponent(serverId);
  const r = await fetch(url, { signal: AbortSignal.timeout(8000) });
  if (r.status !== 200) return null;
  const j = await r.json();
  return isUuid(j.id) ? { uuid: j.id, name: j.name } : null;
}

async function mojangLookup(name) {
  const r = await fetch('https://api.minecraftservices.com/minecraft/profile/lookup/name/' + encodeURIComponent(name),
    { signal: AbortSignal.timeout(8000) });
  if (r.status === 404 || r.status === 204) return null;
  if (r.status !== 200) throw new HttpError(502, 'mojang_error');
  const j = await r.json();
  return isUuid(j.id) ? { uuid: j.id, name: j.name } : null;
}

function devUuid(name) {
  return crypto.createHash('sha1').update('lyricsfx-dev:' + name.toLowerCase()).digest('hex').slice(0, 32);
}

// ---- routes ----
async function handle(req, res) {
  const url = new URL(req.url, 'http://x');
  const path = url.pathname;

  if (req.method === 'GET' && path === '/') {
    return send(res, 200, { ok: true, name: 'LyricsFx relay', players: players.size, dev: DEV_MODE });
  }

  if (req.method === 'GET' && path === '/challenge') {
    if (challenges.size > 5000) throw new HttpError(503, 'busy');
    const serverId = crypto.randomBytes(12).toString('hex');
    challenges.set(serverId, now() + 2 * 60 * 1000);
    return send(res, 200, { serverId });
  }

  if (req.method === 'POST' && path === '/login') {
    const ip = (req.headers['x-forwarded-for'] || req.socket.remoteAddress || '?').toString().split(',')[0].trim();
    const l = loginsByIp.get(ip) || { count: 0, reset: now() + 60000 };
    if (l.reset < now()) { l.count = 0; l.reset = now() + 60000; }
    if (++l.count > 30) throw new HttpError(429, 'too_many_logins');
    loginsByIp.set(ip, l);

    const b = await readJson(req);
    if (typeof b.serverId !== 'string' || !isName(b.name)) throw new HttpError(400, 'bad_request');
    const exp = challenges.get(b.serverId);
    if (!exp || exp < now()) throw new HttpError(400, 'bad_challenge');
    challenges.delete(b.serverId);

    let who;
    if (DEV_MODE) who = { uuid: devUuid(b.name), name: b.name };
    else who = await mojangHasJoined(b.name, b.serverId);
    if (!who) throw new HttpError(401, 'minecraft_login_failed');

    const token = crypto.randomBytes(24).toString('hex');
    sessions.set(token, { uuid: who.uuid, name: who.name, expires: now() + SESSION_MS, lastSync: 0 });
    return send(res, 200, { token, uuid: who.uuid, name: who.name });
  }

  if (req.method === 'POST' && path === '/sync') {
    const s = auth(req);
    if (now() - s.lastSync < 1000) throw new HttpError(429, 'slow_down');
    s.lastSync = now();
    const b = await readJson(req);

    // 1) save my own state
    const p = players.get(s.uuid) || { friends: new Set(), look: cleanLook(null) };
    p.name = s.name;
    p.lastSeen = now();
    const mine = b.profile && typeof b.profile === 'object' ? b.profile : {};
    p.share = mine.share === true;
    p.visibility = VISIBILITY.has(mine.visibility) ? mine.visibility : 'friends';
    p.look = cleanLook(mine.look);
    p.friends = cleanFriends(mine.friends);
    // kill counter: never goes down, and can only grow a little per sync (a light anti-cheat)
    const rep = Number.isInteger(mine.kills) ? Math.max(0, Math.min(1000000, mine.kills)) : 0;
    if (p.kills === undefined) p.kills = rep;
    else p.kills = Math.max(p.kills, Math.min(rep, p.kills + 20));
    players.set(s.uuid, p);

    // the owner's mod keeps a copy of the ranks and gives it back after the server slept
    if (isOwnerSession(s) && Array.isArray(b.rolesBackup)) {
      let changed = false;
      for (const e of b.rolesBackup.slice(0, MAX_ROLES)) {
        if (!e || !isUuid(e.uuid) || !ROLE_IDS.has(e.role) || !isName(e.name)) continue;
        if (!roles.has(e.uuid) && roles.size < MAX_ROLES) { roles.set(e.uuid, { role: e.role, name: e.name }); changed = true; }
      }
      if (changed) saveRoles();
    }

    // 2) what do the players near me wear?
    const out = {};
    const query = Array.isArray(b.query) ? b.query.slice(0, MAX_QUERY) : [];
    for (const u of query) {
      if (!isUuid(u) || u === s.uuid) continue;
      const t = players.get(u);
      if (canSee(s.uuid, t)) out[u] = { name: t.name, ...t.look };
    }

    // 3) how are my friends doing?
    const fr = {};
    for (const u of p.friends) {
      const t = players.get(u);
      fr[u] = {
        name: t ? t.name : null,
        online: !!(t && isOnline(t)),
        mutual: !!(t && t.friends.has(s.uuid)),
      };
      fr[u].kills = fr[u].mutual ? (t.kills || 0) : 0;
      fr[u].role = roleOf(u);
    }
    // 4) ranks (shown in the tab list): of nearby players, tab list players, me and my friends
    const rl = {};
    const want = new Set([s.uuid, ...query.filter(isUuid), ...p.friends]);
    for (const u of want) {
      const rr = roleOf(u);
      if (rr) rl[u] = rr;
    }
    const answer = { players: out, friends: fr, roles: rl };
    if (isOwnerSession(s)) answer.roleList = roleList();
    return send(res, 200, answer);
  }

  if (req.method === 'POST' && path === '/roles/set') {
    const s = auth(req);
    if (!isOwnerSession(s)) throw new HttpError(403, 'owner_only');
    const b = await readJson(req);
    if (!isUuid(b.uuid) || !isName(b.name)) throw new HttpError(400, 'bad_player');
    if (b.role === 'none') {
      roles.delete(b.uuid);
    } else {
      if (!ROLE_IDS.has(b.role)) throw new HttpError(400, 'bad_role');
      if (roleOf(b.uuid) === 'owner') throw new HttpError(400, 'is_owner');
      if (!roles.has(b.uuid) && roles.size >= MAX_ROLES) throw new HttpError(400, 'too_many');
      roles.set(b.uuid, { role: b.role, name: b.name });
    }
    saveRoles();
    return send(res, 200, { ok: true, roleList: roleList() });
  }

  if (req.method === 'POST' && path === '/lookup') {
    const s = auth(req);
    if (now() - (s.lastLookup || 0) < 1500) throw new HttpError(429, 'slow_down');
    s.lastLookup = now();
    const b = await readJson(req);
    if (!isName(b.name)) throw new HttpError(400, 'bad_name');
    const key = b.name.toLowerCase();

    // players who are on the relay are found without asking Mojang
    for (const [uuid, p] of players) {
      if (p.name && p.name.toLowerCase() === key) return send(res, 200, { uuid, name: p.name });
    }
    const cached = lookups.get(key);
    if (cached && now() - cached.at < 10 * 60 * 1000) return send(res, 200, { uuid: cached.uuid, name: cached.name });

    let found;
    if (DEV_MODE) found = { uuid: devUuid(b.name), name: b.name };
    else found = await mojangLookup(b.name);
    if (!found) throw new HttpError(404, 'not_found');
    lookups.set(key, { ...found, at: now() });
    return send(res, 200, found);
  }

  throw new HttpError(404, 'not_found');
}

const server = http.createServer((req, res) => {
  handle(req, res).catch((e) => {
    if (e instanceof HttpError) return send(res, e.code, { error: e.message });
    console.error('Error:', e && e.message);
    send(res, 500, { error: 'server_error' });
  });
});
server.requestTimeout = 15000;

// tidy up old stuff every minute
setInterval(() => {
  const t = now();
  for (const [k, v] of challenges) if (v < t) challenges.delete(k);
  for (const [k, v] of sessions) if (v.expires < t) sessions.delete(k);
  for (const [k, v] of players) if (t - v.lastSeen > FORGET_MS) players.delete(k);
  for (const [k, v] of loginsByIp) if (v.reset < t) loginsByIp.delete(k);
  for (const [k, v] of lookups) if (t - v.at > 60 * 60 * 1000) lookups.delete(k);
}, 60 * 1000).unref();

if (require.main === module) {
  server.listen(PORT, () => console.log(`LyricsFx relay running on port ${PORT}` + (DEV_MODE ? ' (DEV MODE: no Minecraft check!)' : '')));
}
module.exports = { server, roles };
