// THE BACKROOMS — Level 0
// Infinite procedural maze, PBR materials, analytic area-style ceiling lights with
// wall-occlusion shadows evaluated per pixel, rendered through a low-res digital camera filter.
import * as THREE from './lib/three.module.min.js';
import { EffectComposer } from './lib/jsm/postprocessing/EffectComposer.js';
import { RenderPass } from './lib/jsm/postprocessing/RenderPass.js';
import { ShaderPass } from './lib/jsm/postprocessing/ShaderPass.js';
import { OutputPass } from './lib/jsm/postprocessing/OutputPass.js';
import { GTAOPass } from './lib/jsm/postprocessing/GTAOPass.js';
import { Reflector } from './lib/jsm/objects/Reflector.js';

const TEST = location.hash === '#test';

// ───────────────────────────── world constants ─────────────────────────────
const S = 3.0;          // cell size (m)
let H = 2.7;            // ceiling height (m) — per level
let LEVEL = 0;          // 0 = Level 0 (the lobby), 1 = the Poolrooms
let FLOOR = 0;          // Poolrooms storey: 0 ground, 1 and 2 above (linked by the tiled staircases)
const TOP_FLOOR = 2;
const stairLinks = new Map();   // 'floor:cx,cz' -> floor the doorway at the top of those stairs leads to
const PD = 0.5;         // pool depth below the walkway
const WATER_Y = -0.14;  // water surface height
const CH = 8;           // cells per chunk side
const CHW = S * CH;     // chunk width (m)
const HT = 0.1;         // half wall thickness
const DOOR = 0.55;      // half door width
const EYE = 1.62;
const RADIUS = 0.28;    // player collision radius
const WT = 64;          // world-data texture size (cells, toroidal)

let SEED = (Math.random() * 0x7fffffff) | 0;
const TP = new URLSearchParams(location.search);
if (TEST && TP.get('seed')) SEED = +TP.get('seed');

// ───────────────────────────── deterministic world ─────────────────────────
function hash(x, z, s) {
  let h = (Math.imul(x | 0, 0x27d4eb2d) ^ Math.imul(z | 0, 0x165667b1) ^ Math.imul(s | 0, 0x9e3779b9) ^ SEED) >>> 0;
  h ^= h >>> 15; h = Math.imul(h, 0x2c1b3c6d) >>> 0;
  h ^= h >>> 12; h = Math.imul(h, 0x297a2d39) >>> 0;
  h ^= h >>> 15;
  return h >>> 0;
}
// ── region-based architecture ──────────────────────────────────────────────
// The world is tiled into 6×6-cell regions (18 m). Each region picks an archetype and lays
// itself out deterministically; walls still live on grid edges so the GPU shadow test works.
const RG = 6;
const ARCH = { OFFICE: 0, CORRIDOR: 1, HALL: 2, MAZE: 3, DARK: 4, VOID: 5, CUBICLE: 6 };
const fdiv = (a, b) => Math.floor(a / b);
function rngOf(seed) { let a = seed >>> 0; return () => { a = (a + 0x6D2B79F5) >>> 0; let t = a; t = Math.imul(t ^ (t >>> 15), t | 1); t ^= t + Math.imul(t ^ (t >>> 7), t | 61); return ((t ^ (t >>> 14)) >>> 0) / 4294967296; }; }
function archOf(rx, rz) {
  if (rx === 0 && rz === 0) return ARCH.OFFICE;
  const b = (hash(rx, rz, 1) >>> 8) % 100;
  return b < 33 ? ARCH.OFFICE : b < 51 ? ARCH.CORRIDOR : b < 64 ? ARCH.HALL : b < 75 ? ARCH.MAZE : b < 84 ? ARCH.DARK : b < 91 ? ARCH.VOID : ARCH.CUBICLE;
}
const OPENISH = a => a === ARCH.HALL || a === ARCH.VOID;
const FULL = 50, HALF_LO = 150, HALF_HI = 200;
const doorCode = r => 100 + Math.floor(r() * 50);
const regions = new Map();
function region(rx, rz) { return LEVEL === 1 ? poolRegion(rx, rz) : region0(rx, rz); }
function region0(rx, rz) {
  const key = rx + ',' + rz; let L = regions.get(key); if (L) return L;
  if (regions.size > 3000) regions.clear();
  const A = archOf(rx, rz), r = rngOf(hash(rx, rz, 99));
  const N = RG * RG;
  L = { a: A, w0: new Uint8Array(N), w1: new Uint8Array(N), lt: new Uint8Array(N), ph: new Uint8Array(N), pil: new Uint8Array(N), pool: new Uint8Array(N), portal: -1 };
  const I = (x, z) => z * RG + x;
  const line0 = (x, z0, len, doors = 1) => { // wall along z at local x, with doorways
    for (let z = z0; z < z0 + len; z++) L.w0[I(x, z)] = FULL;
    for (let k = 0; k < doors; k++) { const z = z0 + Math.floor(r() * len); L.w0[I(x, z)] = r() < 0.28 ? 0 : doorCode(r); }
  };
  const line1 = (z, x0, len, doors = 1) => {
    for (let x = x0; x < x0 + len; x++) L.w1[I(x, z)] = FULL;
    for (let k = 0; k < doors; k++) { const x = x0 + Math.floor(r() * len); L.w1[I(x, z)] = r() < 0.28 ? 0 : doorCode(r); }
  };
  const roomCells = [];
  if (A === ARCH.OFFICE || A === ARCH.DARK) {
    const split = (x, z, w, d, depth) => {
      const area = w * d;
      const stop = depth > 4 || (w < 2 && d < 2) || (area <= 4 && r() < 0.55) || (depth >= 2 && r() < 0.18);
      if (stop) { roomCells.push([x, z, w, d]); return; }
      const vert = d < 2 ? true : w < 2 ? false : (w > d ? r() < 0.78 : w < d ? r() < 0.22 : r() < 0.5);
      if (vert) { const s = 1 + Math.floor(r() * (w - 1)); line0(x + s, z, d, d >= 4 ? 2 : 1); split(x, z, s, d, depth + 1); split(x + s, z, w - s, d, depth + 1); }
      else { const s = 1 + Math.floor(r() * (d - 1)); line1(z + s, x, w, w >= 4 ? 2 : 1); split(x, z, w, s, depth + 1); split(x, z + s, w, d - s, depth + 1); }
    };
    split(0, 0, RG, RG, 0);
    if (r() < 0.35) { const x = Math.floor(r() * RG), z = Math.floor(r() * RG); L.pil[I(x, z)] = 1; } // a lone support column
  } else if (A === ARCH.CORRIDOR) {
    // long parallel hallways, occasionally pierced, plus one cross passage
    const alongZ = r() < 0.5, cross = 1 + Math.floor(r() * 4);
    for (let p = 1 + Math.floor(r() * 2); p < RG; p += 1 + (r() < 0.3 ? 1 : 0)) {
      for (let q = 0; q < RG; q++) {
        let c = FULL; const u = r();
        if (q === cross) c = 0; else if (u < 0.07) c = doorCode(r); else if (u < 0.1) c = 0;
        if (alongZ) L.w0[I(p, q)] = c; else L.w1[I(q, p)] = c;
      }
    }
  } else if (A === ARCH.HALL) {
    const step = r() < 0.6 ? 2 : 1;
    for (let z = 0; z < RG; z++) for (let x = 0; x < RG; x++) if (x % step === 0 && z % step === 0 && r() < 0.93) L.pil[I(x, z)] = 1;
  } else if (A === ARCH.MAZE) {
    for (let z = 0; z < RG; z++) for (let x = 0; x < RG; x++) { if (x > 0) L.w0[I(x, z)] = FULL; if (z > 0) L.w1[I(x, z)] = FULL; }
    const seen = new Uint8Array(N), st = [[Math.floor(r() * RG), Math.floor(r() * RG)]]; seen[I(...st[0])] = 1;
    while (st.length) {
      const [x, z] = st[st.length - 1];
      const nb = [[x - 1, z, 0, x, z], [x + 1, z, 0, x + 1, z], [x, z - 1, 1, x, z], [x, z + 1, 1, x, z + 1]]
        .filter(([nx, nz]) => nx >= 0 && nz >= 0 && nx < RG && nz < RG && !seen[I(nx, nz)]);
      if (!nb.length) { st.pop(); continue; }
      const [nx, nz, dir, ex, ez] = nb[Math.floor(r() * nb.length)];
      (dir ? L.w1 : L.w0)[I(ex, ez)] = 0; seen[I(nx, nz)] = 1; st.push([nx, nz]);
    }
    for (let i = 0; i < N; i++) { if (L.w0[i] && r() < 0.12) L.w0[i] = 0; if (L.w1[i] && r() < 0.12) L.w1[i] = 0; }
  } else if (A === ARCH.CUBICLE) {
    const alongZ = r() < 0.5;
    for (let p = 1; p < RG; p += 1) for (let q = 0; q < RG; q++) {
      const u = r(); const c = u < 0.34 ? HALF_LO : u < 0.68 ? HALF_HI : u < 0.8 ? FULL : 0;
      if (alongZ) L.w0[I(p, q)] = c; else L.w1[I(q, p)] = c;
    }
  }
  // borders (owned: west edge x=0 and south edge z=0) — keep regions connected
  for (const dir of [0, 1]) {
    const nbA = dir === 0 ? archOf(rx - 1, rz) : archOf(rx, rz - 1);
    for (let i = 0; i < RG; i++) {
      const idx = dir === 0 ? I(0, i) : I(i, 0); const arr = dir === 0 ? L.w0 : L.w1;
      if (OPENISH(A) && OPENISH(nbA)) arr[idx] = 0;
      else if (OPENISH(A) || OPENISH(nbA)) arr[idx] = r() < 0.35 ? (r() < 0.5 ? FULL : doorCode(r)) : 0;
      else arr[idx] = FULL;
    }
    if (!(OPENISH(A) || OPENISH(nbA))) {
      const k = 2 + (r() < 0.5 ? 1 : 0);
      for (let j = 0; j < k; j++) { const i = Math.floor(r() * RG); (dir === 0 ? L.w0 : L.w1)[dir === 0 ? I(0, i) : I(i, 0)] = r() < 0.4 ? 0 : doorCode(r); }
    }
  }
  // lighting: fixtures sit in a regular ceiling grid; some die, some buzz, whole rooms go dark
  const P = { // [fixture, on, flicker] probabilities
    [ARCH.OFFICE]: [0.99, 0.95, 0.035], [ARCH.CORRIDOR]: [0.99, 0.95, 0.06], [ARCH.HALL]: [1, 0.96, 0.03],
    [ARCH.MAZE]: [0.97, 0.86, 0.05], [ARCH.DARK]: [0.9, 0.1, 0.1], [ARCH.VOID]: [1, 0.92, 0.02], [ARCH.CUBICLE]: [0.99, 0.93, 0.04] }[A];
  for (let z = 0; z < RG; z++) for (let x = 0; x < RG; x++) {
    const i = I(x, z); L.ph[i] = Math.floor(r() * 256);
    if (A === ARCH.VOID && (x + z) % 2) { L.lt[i] = 0; continue; }
    if (r() >= P[0]) { L.lt[i] = 0; continue; }
    const u = r(); L.lt[i] = u < P[2] ? 2 : u < P[1] ? 1 : 3;
  }
  for (const [x, z, w, d] of roomCells) { // room-level moods
    const u = r(), mode = A === ARCH.DARK ? (u < 0.25 ? 1 : 0) : (u < 0.07 ? 3 : u < 0.11 ? 2 : -1);
    if (mode < 0) continue;
    for (let zz = z; zz < z + d; zz++) for (let xx = x; xx < x + w; xx++) if (L.lt[I(xx, zz)]) L.lt[I(xx, zz)] = mode === 1 ? (r() < 0.2 ? 2 : 1) : mode === 2 ? (r() < 0.5 ? 2 : 1) : 3;
  }
  // rare special rooms
  if (!(rx === 0 && rz === 0) && A !== ARCH.DARK) {
    const sp = hash(rx, rz, 91) >>> 24, pick = (hash(rx, rz, 92) >>> 8) % N;
    if (sp < 7) L.special = { t: 'chair', i: pick };                                    // a lone office chair facing the wall
    else if (sp < 13) { L.special = { t: 'onelight' };                                  // everything dark but one light
      const keep = I(2, 3); for (let i = 0; i < N; i++) if (L.lt[i]) L.lt[i] = i === keep ? 1 : 3; L.lt[keep] = 1; }
    else if (sp < 18) { L.special = { t: 'red' }; for (let i = 0; i < N; i++) { L.ph[i] = 255; if (L.lt[i] === 3) L.lt[i] = 1; } }   // red room
    else if (sp < 26) { for (let k = 0; k < N; k++) { const i = (pick + k) % N; if (L.w0[i] === FULL && i % RG > 0) { L.special = { t: 'exit', i }; break; } } }   // an EXIT sign on a blank wall
  }
  // a rare strange puddle: step in it and you slip through to the Poolrooms
  if (!(rx === 0 && rz === 0) && A !== ARCH.DARK && (hash(rx, rz, 77) >>> 24) < 60) L.portal = (hash(rx, rz, 78) >>> 8) % N;
  if (rx === 0 && rz === 0) { L.lt[I(0, 0)] = 1; L.w0[I(1, 0)] = L.w0[I(1, 0)] ? doorCode(r) : 0; L.w1[I(0, 1)] = L.w1[I(0, 1)] ? doorCode(r) : 0; }
  regions.set(key, L); return L;
}
// ── the Poolrooms: white-tiled halls, basins, colonnades and flooded rooms ──
const PA = { HALL: 10, ROOMS: 11, COLON: 12, TUNNEL: 13, OPEN: 14 };
function archPool(rx, rz) {
  if (rx === 0 && rz === 0) return PA.HALL;
  const b = (hash(rx + FLOOR * 7919, rz - FLOOR * 6007, 31) >>> 8) % 100;
  return b < 18 ? PA.HALL : b < 50 ? PA.ROOMS : b < 62 ? PA.COLON : b < 82 ? PA.TUNNEL : PA.OPEN;
}
const POPEN = a => a === PA.HALL || a === PA.OPEN || a === PA.COLON;
const ARCH_CODE = 250;                              // wall kind 5: tiled wall pierced by a circular arch
const pregions = new Map();
function poolRegion(rx, rz) {
  const key = FLOOR + ':' + rx + ',' + rz; let L = pregions.get(key); if (L) return L;
  if (pregions.size > 3000) pregions.clear();
  const A = archPool(rx, rz), r = rngOf(hash(rx + FLOOR * 7919, rz - FLOOR * 6007, 199)), N = RG * RG;
  L = { a: A, w0: new Uint8Array(N), w1: new Uint8Array(N), lt: new Uint8Array(N), ph: new Uint8Array(N), pil: new Uint8Array(N), pool: new Uint8Array(N), portal: -1, ladders: [] };
  const I = (x, z) => z * RG + x;
  const rect = (x0, z0, w, d) => { for (let z = z0; z < z0 + d; z++) for (let x = x0; x < x0 + w; x++) L.pool[I(x, z)] = 1; };
  const opening = () => r() < 0.5 ? 0 : (r() < 0.5 ? ARCH_CODE : doorCode(r));
  const line0 = (x, z0, len) => { for (let z = z0; z < z0 + len; z++) L.w0[I(x, z)] = FULL; L.w0[I(x, z0 + Math.floor(r() * len))] = opening(); if (len > 3) L.w0[I(x, z0 + Math.floor(r() * len))] = opening(); };
  const line1 = (z, x0, len) => { for (let x = x0; x < x0 + len; x++) L.w1[I(x, z)] = FULL; L.w1[I(x0 + Math.floor(r() * len), z)] = opening(); if (len > 3) L.w1[I(x0 + Math.floor(r() * len), z)] = opening(); };
  let skyP = 0.3;
  if (A === PA.HALL) {                              // dry tiled deck around a sunken pool, columns, a ladder
    const w = 2 + Math.floor(r() * 3), d = 2 + Math.floor(r() * 3);
    const x0 = 1 + Math.floor(r() * (RG - 1 - w)), z0 = 1 + Math.floor(r() * (RG - 1 - d));
    rect(x0, z0, w, d);
    for (let vz = z0; vz <= z0 + d; vz += 2) for (let vx = x0; vx <= x0 + w; vx += 2) if (vx < RG && vz < RG && r() < 0.7) L.pil[I(vx, vz)] = 1;
    L.ladders.push([x0 + Math.floor(r() * w), z0, 1]);   // ladder on the pool's south edge (dir 1 = edge along x)
    if (r() < 0.6) L.ladders.push([x0, z0 + Math.floor(r() * d), 0]);
    skyP = 0.35;
  } else if (A === PA.ROOMS) {                      // flooded tiled rooms joined by arches and openings
    rect(0, 0, RG, RG);
    const split = (x, z, w, d, depth) => {
      if (depth >= 3 || (w < 2 && d < 2) || (w * d <= 6 && r() < 0.5)) return;
      if (w >= d) { const s = 1 + Math.floor(r() * (w - 1)); line0(x + s, z, d); split(x, z, s, d, depth + 1); split(x + s, z, w - s, d, depth + 1); }
      else { const s = 1 + Math.floor(r() * (d - 1)); line1(z + s, x, w); split(x, z, w, s, depth + 1); split(x, z + s, w, d - s, depth + 1); }
    };
    split(0, 0, RG, RG, 0);
    if (r() < 0.5) { const x = 1 + Math.floor(r() * 4), z = 1 + Math.floor(r() * 4); L.pil[I(x, z)] = 1; }
    skyP = 0.28;
  } else if (A === PA.TUNNEL) {                     // flooded corridors: a march of circular arches
    rect(0, 0, RG, RG);
    const alongZ = r() < 0.5;
    for (let p = 1; p < RG; p++) for (let q = 0; q < RG; q++) {   // side walls every corridor line
      const c = r() < 0.12 ? ARCH_CODE : FULL;
      if (alongZ) L.w0[I(p, q)] = c; else L.w1[I(q, p)] = c;
    }
    for (let p = 0; p < RG; p++) for (let q = 1; q < RG; q++) {   // arches across each corridor
      if (alongZ) { if (!L.w1[I(p, q)]) L.w1[I(p, q)] = ARCH_CODE; } else { if (!L.w0[I(q, p)]) L.w0[I(q, p)] = ARCH_CODE; }
    }
    skyP = 0.22;
  } else if (A === PA.OPEN) {                       // a vast flooded hall: few huge columns, sun patches
    rect(0, 0, RG, RG);
    for (let vz = 1; vz < RG; vz += 2) for (let vx = 1; vx < RG; vx += 2) if (r() < 0.45) L.pil[I(vx, vz)] = 1;
    skyP = 0.22;
  } else if (A === PA.COLON) {                      // a flooded channel flanked by columns and dry decks
    const alongX = r() < 0.5;
    for (let q = 0; q < RG; q++) for (let c = 2; c < 5; c++) L.pool[alongX ? I(q, c) : I(c, q)] = 1;
    for (let q = 0; q < RG; q += 1) { L.pil[alongX ? I(q, 2) : I(2, q)] = 1; L.pil[alongX ? I(q, 5) : I(5, q)] = 1; }
    skyP = 0.3;
  }
  for (const dir of [0, 1]) {                       // borders keep regions connected
    const nbA = dir === 0 ? archPool(rx - 1, rz) : archPool(rx, rz - 1);
    for (let i = 0; i < RG; i++) {
      const idx = dir === 0 ? I(0, i) : I(i, 0), arr = dir === 0 ? L.w0 : L.w1;
      if (POPEN(A) && POPEN(nbA)) arr[idx] = 0;
      else if (POPEN(A) || POPEN(nbA)) arr[idx] = r() < 0.35 ? FULL : 0;
      else arr[idx] = r() < 0.7 ? FULL : opening();
    }
    if (!POPEN(A) && !POPEN(nbA)) { const i = Math.floor(r() * RG); (dir === 0 ? L.w0 : L.w1)[dir === 0 ? I(0, i) : I(i, 0)] = ARCH_CODE; }
  }
  for (let i = 0; i < N; i++) { L.ph[i] = Math.floor(r() * 256); L.lt[i] = r() < skyP ? 1 : 0; }   // 1 = sunlit skylight shaft
  if (!(rx === 0 && rz === 0) && (hash(rx + FLOOR * 7919, rz - FLOOR * 6007, 177) >>> 24) < 60) { const i = (hash(rx + FLOOR * 7919, rz - FLOOR * 6007, 178) >>> 8) % N; if (!L.pool[i]) L.portal = i; }
  if (!(rx === 0 && rz === 0)) {                    // rare special rooms
    const sp = hash(rx + FLOOR * 7919, rz - FLOOR * 6007, 191) >>> 24, pick = (hash(rx + FLOOR * 7919, rz - FLOOR * 6007, 192) >>> 8) % N;
    if (sp < 26 && A !== PA.HALL && FLOOR < TOP_FLOOR) { for (let k = 0; k < N; k++) { const i = (pick + k) % N; if (L.w1[i] === FULL && i >= RG && L.portal !== i) { L.special = { t: 'stairs', i }; break; } } }   // steps up out of the water into a dark doorway
    else if (sp < 44) { L.special = { t: 'onebeam' }; for (let i = 0; i < N; i++) L.lt[i] = 0; L.lt[I(2, 3)] = 1; }   // a dim flooded hall lit by a single shaft
  }
  if (rx === 0 && rz === 0) { L.pool[I(0, 0)] = 0; L.lt[I(0, 0)] = 1; }
  // staircases you arrived by (or left from) always exist on this floor: steps against a wall, the way back behind you
  for (let lz = 0; lz < RG; lz++) for (let lx = 0; lx < RG; lx++) {
    const cx = rx * RG + lx, cz = rz * RG + lz;
    if (!stairLinks.has(FLOOR + ':' + cx + ',' + cz)) continue;
    const i = I(lx, lz);
    L.special = { t: 'stairs', i }; if (L.portal === i) L.portal = -1;
    L.w1[i] = FULL;                                   // the wall the steps climb against
    L.w0[i] = 0; if (lx + 1 < RG) L.w0[I(lx + 1, lz)] = 0; if (lz + 1 < RG) L.w1[I(lx, lz + 1)] = 0;   // keep the way out open
    L.lt[i] = 1;
  }
  pregions.set(key, L); return L;
}
const lvKey = () => LEVEL === 1 ? '1f' + FLOOR : '0';
function isPool(cx, cz) { if (LEVEL !== 1) return false; const [L, i] = cellRef(cx, cz); return L.pool[i] === 1; }
const STAIR = { n: 9, depth: 0.18, top: 1.75, x0: 0.6, x1: 2.4 };   // tiled steps rising out of the water
function stairHeight(cx, cz, x, z) {                                   // walkable height of the steps at (x,z), or -Infinity
  const lx = x - cx * S, d = z - (cz * S + HT);
  if (lx < STAIR.x0 || lx > STAIR.x1 || d < 0 || d > STAIR.n * STAIR.depth) return -Infinity;
  const g0 = isPool(cx, cz) ? -PD : 0, k = Math.min(STAIR.n - 1, Math.ceil(STAIR.n - d / STAIR.depth) - 1);
  return g0 + (k + 1) * (STAIR.top - g0) / STAIR.n;
}
function groundAt(x, z) {
  const cx = Math.floor(x / S), cz = Math.floor(z / S);
  let g = isPool(cx, cz) ? -PD : 0;
  if (LEVEL === 1) { const sp = specialAt(cx, cz); if (sp && sp.t === 'stairs') g = Math.max(g, stairHeight(cx, cz, x, z)); }
  return g;
}
function cellRef(cx, cz) { const rx = fdiv(cx, RG), rz = fdiv(cz, RG); return [region(rx, rz), (cz - rz * RG) * RG + (cx - rx * RG)]; }
// returns code: 0 none, else kind*50+cq  (kind 1 full, 2 door, 3 half-low, 4 half-high)
function wallCode(cx, cz, dir) { const [L, i] = cellRef(cx, cz); return dir ? L.w1[i] : L.w0[i]; }
const hasHeader = code => LEVEL === 0 && Math.floor(code / 50) === 2 && (code % 50) < 34;
function intervals(code) {
  if (!code) return [];
  const kind = Math.floor(code / 50), cq = code - kind * 50;
  if (kind === 1) return [[HT, S - HT]];
  if (kind === 2) { const c = S * (0.3 + 0.4 * cq / 49); return [[HT, c - DOOR], [c + DOOR, S - HT]]; }
  if (kind === 3) return [[HT, S * 0.5]];
  if (kind === 5) return [[HT, S * 0.5 - 1.0], [S * 0.5 + 1.0, S - HT]];
  return [[S * 0.5, S - HT]];
}
function wallSD(code, t) { // signed distance into solid along the edge
  if (!code) return -10;
  const kind = Math.floor(code / 50), cq = code - kind * 50;
  if (kind === 1) return 10;
  if (kind === 2) { const c = S * (0.3 + 0.4 * cq / 49); return Math.abs(t - c) - DOOR; }
  if (kind === 3) return S * 0.5 - t;
  if (kind === 5) return Math.abs(t - S * 0.5) - 1.15;
  return t - S * 0.5;
}
const touches0 = code => { const k = Math.floor(code / 50); return k === 1 || k === 2 || k === 3 || k === 5; };
const touchesS = code => { const k = Math.floor(code / 50); return k === 1 || k === 2 || k === 4 || k === 5; };
function postSize(vx, vz) {
  const [L, i] = cellRef(vx, vz);
  if (L.pil[i]) return 0.35;
  if (touches0(wallCode(vx, vz, 0)) || touchesS(wallCode(vx, vz - 1, 0)) ||
      touches0(wallCode(vx, vz, 1)) || touchesS(wallCode(vx - 1, vz, 1))) return HT;
  return 0;
}
// light: 0 none / no fixture, 1 on, 2 flicker, 3 fixture but dead
function lightState(cx, cz) { const [L, i] = cellRef(cx, cz); return { s: L.lt[i], ph: L.ph[i] }; }
function flicker(t, ph) {
  const s = Math.sin(t * 11.0 + ph * 7.0) + 0.7 * Math.sin(t * 17.3 + ph * 3.0) + 0.6 * Math.sin(t * 3.1 + ph);
  return s > 0.9 ? 0.04 : (s > 0.75 ? 0.5 : 1.0);
}
function lightOnJS(cx, cz, t) {
  const L = lightState(cx, cz);
  if (L.s === 1) return 1; if (L.s === 2) return flicker(t, L.ph / 255 * 6.2831853); return 0;
}
// line visibility in xz through grid edges (binary-ish, used for gameplay)
function visJS(px, pz, lx, lz) {
  let vis = 1; const dx = lx - px, dz = lz - pz;
  let a = Math.floor(px / S), b = Math.floor(lx / S);
  for (let i = 0, n = Math.abs(b - a), st = b > a ? 1 : -1; i < n; i++) {
    const k = st > 0 ? a + 1 + i : a - i; const s = (k * S - px) / dx;
    const zc = pz + s * dz, cz = Math.floor(zc / S);
    if (wallSD(wallCode(k, cz, 0), zc - cz * S) > -0.05) vis = 0;
  }
  a = Math.floor(pz / S); b = Math.floor(lz / S);
  for (let i = 0, n = Math.abs(b - a), st = b > a ? 1 : -1; i < n; i++) {
    const k = st > 0 ? a + 1 + i : a - i; const s = (k * S - pz) / dz;
    const xc = px + s * dx, cx = Math.floor(xc / S);
    if (wallSD(wallCode(cx, k, 1), xc - cx * S) > -0.05) vis = 0;
  }
  return vis;
}
function localLight(x, z, t) {
  const pcx = Math.floor(x / S), pcz = Math.floor(z / S); let sum = 0;
  for (let i = -2; i <= 2; i++) for (let j = -2; j <= 2; j++) {
    const cx = pcx + i, cz = pcz + j; const on = lightOnJS(cx, cz, t); if (!on) continue;
    const lx = (cx + 0.5) * S, lz = (cz + 0.5) * S; const d2 = (lx - x) ** 2 + (lz - z) ** 2;
    if (d2 > 49) continue;
    const v = visJS(x, z, lx, lz); sum += on * v / (1 + d2 * 0.12);
  }
  return sum;
}
function bottleAt(cx, cz) {
  if (cx === 0 && cz === 0) return null;
  const h = hash(cx, cz, 8);
  if ((h >>> 24) >= (cellRef(cx, cz)[0].a === ARCH.DARK ? 9 : 4)) return null;
  return { x: cx * S + 0.6 + 1.8 * (((h >>> 8) & 255) / 255), z: cz * S + 0.6 + 1.8 * (((h >>> 16) & 255) / 255) };
}

// ───────────────────────────── renderer / scene ────────────────────────────
const renderer = new THREE.WebGLRenderer({ antialias: false, powerPreference: 'high-performance' });
renderer.setSize(innerWidth, innerHeight);
renderer.toneMapping = THREE.ACESFilmicToneMapping;
renderer.toneMappingExposure = 1.05;
renderer.outputColorSpace = THREE.SRGBColorSpace;
renderer.shadowMap.enabled = true;
renderer.shadowMap.type = THREE.PCFSoftShadowMap;
renderer.shadowMap.autoUpdate = false; // only re-render shadows while the flashlight is on
document.body.prepend(renderer.domElement);

const scene = new THREE.Scene();
scene.background = new THREE.Color(0x000000);
scene.fog = new THREE.FogExp2(new THREE.Color(0, 0, 0), 0.014);
const camera = new THREE.PerspectiveCamera(72, innerWidth / innerHeight, 0.08, 140);
scene.add(camera);

// world data texture (lights + walls around the player), read by every surface shader
const worldData = new Uint8Array(WT * WT * 4);
const worldTex = new THREE.DataTexture(worldData, WT, WT, THREE.RGBAFormat, THREE.UnsignedByteType);
worldTex.magFilter = worldTex.minFilter = THREE.NearestFilter;
worldTex.generateMipmaps = false;
let worldCenter = null;
function updateWorldTex(pcx, pcz) {
  const key = pcx + ',' + pcz; if (worldCenter === key) return; worldCenter = key;
  for (let cz = pcz - 32; cz < pcz + 32; cz++) for (let cx = pcx - 32; cx < pcx + 32; cx++) {
    const o = (((cz & 63) * WT) + (cx & 63)) * 4; const L = lightState(cx, cz);
    worldData[o] = (L.s === 1 ? 1 : L.s === 2 ? 2 : 0) + (postSize(cx, cz) > 0.3 ? 8 : 0); worldData[o + 1] = L.ph;
    worldData[o + 2] = wallCode(cx, cz, 0); worldData[o + 3] = wallCode(cx, cz, 1);
  }
  worldTex.needsUpdate = true;
}

// environment for PBR reflections / indirect light: a tiny lit yellow room
function buildEnv(level) {
  const env = new THREE.Scene(), h = level === 1 ? 4.0 : 2.7;
  const C = level === 1
    ? { wall: [0.58, 0.6, 0.54], ceil: [0.52, 0.54, 0.5], floor: [0.42, 0.5, 0.44], lamp: [10, 9.5, 8.4] }
    : { wall: [0.30, 0.27, 0.12], ceil: [0.42, 0.40, 0.33], floor: [0.22, 0.17, 0.06], lamp: [6, 5.6, 4.6] };
  const mb = c => new THREE.MeshBasicMaterial({ color: new THREE.Color(...c), side: THREE.BackSide });
  const box = new THREE.Mesh(new THREE.BoxGeometry(12, h, 12), [mb(C.wall), mb(C.wall), mb(C.ceil), mb(C.floor), mb(C.wall), mb(C.wall)]);
  if (level === 1) { const patch = new THREE.Mesh(new THREE.PlaneGeometry(2.2, 2.6), new THREE.MeshBasicMaterial({ color: new THREE.Color(3.2, 3.0, 2.6) })); patch.position.set(5.95, 0.2, 0); patch.rotation.y = -Math.PI / 2; env.add(patch); }
  box.position.y = h / 2 - 1.3; env.add(box);
  const pm = new THREE.MeshBasicMaterial({ color: new THREE.Color(...C.lamp), side: THREE.DoubleSide });
  for (let i = -1; i <= 1; i++) for (let j = -1; j <= 1; j++) {
    const p = new THREE.Mesh(level === 1 ? new THREE.CircleGeometry(0.55, 24) : new THREE.PlaneGeometry(1, 1), pm); p.rotation.x = Math.PI / 2;
    p.position.set(i * 3, h - 1.31, j * 3); env.add(p);
  }
  const pmrem = new THREE.PMREMGenerator(renderer);
  const rt = pmrem.fromScene(env, 0.035, 0.05, 50);
  pmrem.dispose();
  return rt.texture;
}
const ENVS = [buildEnv(0), null];
scene.environment = ENVS[0];

// ───────────────────────────── textures & materials ────────────────────────
const manager = new THREE.LoadingManager();
// ── loading screen bookkeeping ──
const LOAD = { tex: [0, 1], texDone: false, aud: [0, 0], audDone: false, world: false, shaders: false, fails: [], finished: false, t0: performance.now() };
function loaderUI() {
  const el = id => document.getElementById(id);
  const set = (id, state, txt) => { const li = el(id); if (!li) return; const st = li.querySelector('.st');
    st.textContent = state === 'ok' ? '✓' : state === 'bad' ? '!' : '…'; st.className = 'st ' + (state || ''); li.querySelector('em').textContent = txt || ''; };
  const texBad = LOAD.fails.some(f => f.kind === 'tex'), audBad = LOAD.fails.some(f => f.kind === 'aud');
  set('lc-tex', LOAD.texDone ? (texBad ? 'bad' : 'ok') : '', `${LOAD.tex[0]}/${LOAD.tex[1]}`);
  set('lc-aud', LOAD.audDone ? (audBad ? 'bad' : 'ok') : '', `${LOAD.aud[0]}/${LOAD.aud[1]}`);
  set('lc-wld', LOAD.world ? 'ok' : '', LOAD.world ? 'generated' : '');
  set('lc-shd', LOAD.shaders ? 'ok' : '', LOAD.shaders ? 'compiled' : '');
  const p = (LOAD.tex[0] / Math.max(1, LOAD.tex[1])) * 0.45 + (LOAD.aud[0] / Math.max(1, LOAD.aud[1])) * 0.35 + (LOAD.world ? 0.1 : 0) + (LOAD.shaders ? 0.1 : 0);
  const bar = el('lBar'); if (bar) bar.style.width = Math.round(Math.min(1, p) * 100) + '%';
  const w = el('lWarn'); if (w) w.textContent = LOAD.fails.length ? `${LOAD.fails.length} file${LOAD.fails.length > 1 ? 's' : ''} failed to load — you can still enter.` : '';
}
function loaderCheck() {
  loaderUI();
  if (LOAD.finished || !(LOAD.texDone && LOAD.audDone && LOAD.world && LOAD.shaders)) return;
  LOAD.finished = true;
  if (!document.getElementById('lSub')) return;
  document.getElementById('lSub').textContent = LOAD.fails.length ? 'LOADED WITH ERRORS' : 'ALL LOADED';
  const go = document.getElementById('lGo'); go.hidden = false;
  const enter = e => { e.preventDefault(); e.stopPropagation(); go.hidden = true; enterGame(); };
  go.addEventListener('click', enter, { once: true });
  if (new URLSearchParams(location.search).has('autoenter')) setTimeout(() => go.click(), 300);   // for automated checks
}
manager.onProgress = (url, loaded, total) => { LOAD.tex = [loaded, total]; loaderUI(); };
manager.onError = url => { LOAD.fails.push({ kind: 'tex', url }); console.warn('texture failed', url); };
manager.onLoad = () => { LOAD.texDone = true; loaderCheck(); };
const loader = new THREE.TextureLoader(manager);
const maxAniso = renderer.capabilities.getMaxAnisotropy();
function tex(name, srgb) {
  const t = loader.load('tex/' + name + '.jpg');
  t.wrapS = t.wrapT = THREE.RepeatWrapping; t.anisotropy = maxAniso;
  t.colorSpace = srgb ? THREE.SRGBColorSpace : THREE.NoColorSpace; return t;
}
const T = {
  carpetD: tex('carpet-diffuse', true), carpetN: tex('carpet-normal'),
  wallD: tex('wall-diffuse', true), wallN: tex('wall-normal'),
  ceilD: tex('ceiling-tile-diffuse', true), ceilN: tex('ceiling-tile-normal'), ceilR: tex('ceiling-tile-roughness'),
  lightD: tex('ceiling-light-diffuse', true), lightN: tex('ceiling-light-normal'), lightR: tex('ceiling-light-roughness'),
  lightE: tex('ceiling-light-emission', true),
  ptD: tex('pool-big-albedo', true), ptN: tex('pool-big-normal'), ptR: tex('pool-big-roughness'),
  paD: tex('pool-small-albedo', true), paN: tex('pool-small-normal'), paR: tex('pool-small-roughness'),
};

const U = {
  uTime: { value: 0 }, uWorld: { value: worldTex }, uLightI: { value: 11.0 }, uEnvScale: { value: 0.55 },
  uAmbient: { value: 0.012 }, uEmissive: { value: 4.2 }, uH: { value: 2.7 }, uCool: { value: 0 }, uEnvFloor: { value: 0 },
};
const QUALITY = { n: 2, r: 7.2 };

const GLSL_COMMON = /* glsl */`
varying vec3 vBRWorld;
uniform float uTime; uniform float uLightI; uniform float uEnvScale; uniform float uAmbient; uniform float uEmissive;
uniform sampler2D uWorld;
#define BR_S 3.0
#define WATER_Y_GLSL -0.14
uniform float uH; uniform float uCool; uniform float uEnvFloor;
#define BR_H uH
vec4 brCell(int cx, int cz){ return floor(texelFetch(uWorld, ivec2(cx & 63, cz & 63), 0) * 255.0 + 0.5); }
float brFlicker(float t, float ph){
  float s = sin(t*11.0 + ph*7.0) + 0.7*sin(t*17.3 + ph*3.0) + 0.6*sin(t*3.1 + ph);
  return s > 0.9 ? 0.04 : (s > 0.75 ? 0.5 : 1.0);
}
float brLightOn(vec4 c){
  float st = mod(c.r, 8.0);
  if (st < 0.5) return 0.0;
  if (st > 1.5) return brFlicker(uTime, c.g / 255.0 * 6.2831853);
  return 1.0;
}
vec3 brTint(vec4 c){
  float g = c.g / 255.0; float li = 0.8 + 0.3 * fract(g * 7.13);
  vec3 warm = vec3(1.0, 0.93, 0.76), cool = vec3(0.92, 0.97, 0.93), old = vec3(1.0, 0.84, 0.58);
  vec3 col = g > 0.88 ? cool : (g < 0.08 ? old : warm);
  col = mix(col, vec3(0.97, 0.99, 1.02), uCool);
  if (g > 0.997) return vec3(1.0, 0.1, 0.06) * 1.15;   // the red rooms
  return col * li;
}
float brH(vec2 p){ return fract(sin(dot(p, vec2(127.1, 311.7))) * 43758.5453); }
float brN(vec2 p){ vec2 i = floor(p), f = fract(p); f = f * f * (3.0 - 2.0 * f);
  return mix(mix(brH(i), brH(i + vec2(1, 0)), f.x), mix(brH(i + vec2(0, 1)), brH(i + vec2(1, 1)), f.x), f.y); }
vec2 brH2(vec2 p){ return fract(sin(vec2(dot(p, vec2(127.1, 311.7)), dot(p, vec2(269.5, 183.3)))) * 43758.5453); }
// caustic filaments: distance between nearest and 2nd-nearest animated cell points (thin bright ridges)
float brCaustic(vec2 p, float t){
  vec2 i = floor(p), f = fract(p); float d1 = 8.0, d2 = 8.0;
  for (int y = -1; y <= 1; y++) for (int x = -1; x <= 1; x++) {
    vec2 g = vec2(float(x), float(y)); vec2 o = brH2(i + g);
    o = 0.5 + 0.42 * sin(t + 6.2831 * o);
    float d = length(g + o - f);
    if (d < d1) { d2 = d1; d1 = d; } else if (d < d2) d2 = d;
  }
  return 1.0 - smoothstep(0.0, 0.11, d2 - d1);
}
float brSD(float code, float t){
  if (code < 0.5) return -10.0;
  float kind = floor(code / 50.0); float cq = code - kind * 50.0;
  if (kind < 1.5) return 10.0;
  if (kind < 2.5) { float c = BR_S * (0.3 + 0.4 * cq / 49.0); return abs(t - c) - 0.55; }
  if (kind < 3.5) return BR_S * 0.5 - t;
  if (kind > 4.5) return abs(t - BR_S * 0.5) - 1.15;
  return t - BR_S * 0.5;
}
// distance to a full-height wall face along an edge (big if none at t)
float brWallDist(float code, float t, float dPlane){ return brSD(code, t) > 0.0 ? max(dPlane - 0.1, 0.0) : 9.0; }
// soft visibility from receiver p to light L across full-height walls on grid edges
float brVis(vec2 p, vec2 L){
  float vis = 1.0; vec2 d = L - p;
  int a = int(floor(p.x / BR_S)); int b = int(floor(L.x / BR_S));
  int n = abs(b - a); int st = b > a ? 1 : -1;
  for (int i = 0; i < 4; i++) {
    if (i >= n) break;
    int k = st > 0 ? a + 1 + i : a - i;
    float s = (float(k) * BR_S - p.x) / d.x;
    float zc = p.y + s * d.y; int cz = int(floor(zc / BR_S));
    float w = max(0.5 * s, 0.02);
    vis *= smoothstep(-w, w, -brSD(brCell(k, cz).b, zc - float(cz) * BR_S));
    { int m = int(floor(zc / BR_S + 0.5)); if (brCell(k, m).r > 7.5) {           // square column at grid vertex
        float perp = abs(zc - float(m) * BR_S) * abs(d.x) * inversesqrt(dot(d, d));
        vis *= smoothstep(-w, w, perp - 0.42); } }
  }
  a = int(floor(p.y / BR_S)); b = int(floor(L.y / BR_S));
  n = abs(b - a); st = b > a ? 1 : -1;
  for (int i = 0; i < 4; i++) {
    if (i >= n) break;
    int k = st > 0 ? a + 1 + i : a - i;
    float s = (float(k) * BR_S - p.y) / d.y;
    float xc = p.x + s * d.x; int cx = int(floor(xc / BR_S));
    float w = max(0.5 * s, 0.02);
    vis *= smoothstep(-w, w, -brSD(brCell(cx, k).a, xc - float(cx) * BR_S));
    { int m = int(floor(xc / BR_S + 0.5)); if (brCell(m, k).r > 7.5) {
        float perp = abs(xc - float(m) * BR_S) * abs(d.y) * inversesqrt(dot(d, d));
        vis *= smoothstep(-w, w, perp - 0.42); } }
  }
  return vis;
}
`;

const GLSL_LIGHTS = /* glsl */`
float brLocal = 0.0;
{
  vec3 wp = vBRWorld;
  vec3 nW = normalize((vec4(geometryNormal, 0.0) * viewMatrix).xyz);
  int pcx = int(floor(wp.x / BR_S)); int pcz = int(floor(wp.z / BR_S));
  // soft corner darkening (floor/wall/ceiling junctions)
  float fx = wp.x - float(pcx) * BR_S, fz = wp.z - float(pcz) * BR_S;
  float ao = 1.0;
  if (abs(nW.x) < 0.5) {
    float dw = min(brWallDist(brCell(pcx, pcz).b, fz, fx), brWallDist(brCell(pcx + 1, pcz).b, fz, BR_S - fx));
    ao *= 1.0 - 0.22 * (1.0 - smoothstep(0.0, 0.6, dw));
  }
  if (abs(nW.z) < 0.5) {
    float dw = min(brWallDist(brCell(pcx, pcz).a, fx, fz), brWallDist(brCell(pcx, pcz + 1).a, fx, BR_S - fz));
    ao *= 1.0 - 0.22 * (1.0 - smoothstep(0.0, 0.6, dw));
  }
  if (nW.y < 0.5)  ao *= 1.0 - 0.22 * (1.0 - smoothstep(0.0, 0.45, wp.y));
  if (nW.y > -0.5) ao *= 1.0 - 0.18 * (1.0 - smoothstep(0.0, 0.4, BR_H - wp.y));
  float aoD = mix(1.0, ao, 0.35);
  for (int i = -BR_N; i <= BR_N; i++) {
    for (int j = -BR_N; j <= BR_N; j++) {
      int cx = pcx + i; int cz = pcz + j;
      vec3 Lw = vec3((float(cx) + 0.5) * BR_S, BR_H - 0.03, (float(cz) + 0.5) * BR_S);
      vec3 dv = Lw - wp; float d2 = dot(dv, dv);
      float q = d2 / (BR_R * BR_R);
      if (q >= 1.0) continue;
      vec4 bcell = brCell(cx, cz);
      float on = brLightOn(bcell);
      if (on <= 0.0) continue;
      float win = 1.0 - q * q; win *= win;
      float vis = brVis(wp.xz, Lw.xz);
      if (vis <= 0.001) continue;
      vec3 ld = dv * inversesqrt(max(d2, 1e-4));
      float emit = max(ld.y, 0.0) + 0.10;               // lambertian panel + diffuser spill
      float e = uLightI * on * emit * win * vis * aoD / (d2 + 0.3);
      directLight.color = brTint(bcell) * e;
      directLight.direction = normalize((viewMatrix * vec4(ld, 0.0)).xyz);
      directLight.visible = true;
      RE_Direct(directLight, geometryPosition, geometryNormal, geometryViewDir, geometryClearcoatNormal, material, reflectedLight);
      brLocal += on * win * vis / (1.0 + d2 * 0.12);
    }
  }
  float brLN0 = clamp(brLocal * 0.3, 0.0, 1.5);
  #if defined( RE_IndirectDiffuse )
    iblIrradiance *= uEnvScale * max(brLN0, uEnvFloor) * ao;
    irradiance += vec3(uAmbient) * ao;
  #endif
  #if defined( RE_IndirectSpecular )
    radiance *= uEnvScale * max(brLN0, uEnvFloor) * ao;
  #endif
}
float brLN = clamp(brLocal * 0.3, 0.0, 1.5);
#include <lights_fragment_end>
`;

const GLSL_SURFACE = /* glsl */`
float brWet = 0.0;
{
  vec3 wp = vBRWorld;
#ifdef BR_FLOOR
  vec2 q = wp.xz;
  float n = brN(q * 0.3) * 0.6 + brN(q * 1.1 + 13.0) * 0.28 + brN(q * 3.7) * 0.12;
  float stain = smoothstep(0.66, 0.8, n);
  float wear = brN(q * 0.09 + 41.0);
  diffuseColor.rgb *= mix(1.0, 0.5, stain) * (0.86 + 0.24 * wear);
  diffuseColor.rgb = mix(diffuseColor.rgb, diffuseColor.rgb * vec3(0.9, 0.85, 0.7), smoothstep(0.55, 0.8, n) * 0.5);
  brWet = stain * 0.8;
#endif
#ifdef BR_WALL
  float al = wp.x + wp.z;
  float grime = 1.0 - 0.2 * (1.0 - smoothstep(0.05, 0.7, wp.y));
  float streak = smoothstep(0.68, 0.92, brN(vec2(al * 1.6, 3.7))) * (0.45 + 0.55 * brN(vec2(al * 7.0, wp.y * 0.9))) * smoothstep(0.6, 2.65, wp.y);
  float fade = 0.88 + 0.22 * brN(vec2(al * 0.12, wp.y * 0.2) + 7.0);
  diffuseColor.rgb *= grime * fade;
  diffuseColor.rgb = mix(diffuseColor.rgb, diffuseColor.rgb * vec3(0.72, 0.62, 0.4), streak * 0.75);
  float mold = smoothstep(0.78, 0.95, brN(vec2(al * 2.5, wp.y * 2.5) + 91.0)) * (1.0 - smoothstep(0.0, 0.5, wp.y));
  diffuseColor.rgb *= 1.0 - mold * 0.45;
#endif
#ifdef BR_CEIL
  vec2 tile = floor(wp.xz); vec2 f = fract(wp.xz);
  float th = brH(tile), th2 = brH(tile + 17.3), th3 = brH(tile + 51.1);
  bool fixtureTile = (mod(tile.x, 3.0) == 1.0) && (mod(tile.y, 3.0) == 1.0);
  diffuseColor.rgb *= 0.91 + 0.14 * th;
  if (th2 > 0.93 && !fixtureTile) {                         // water-stained tile
    vec2 c = vec2(0.3) + 0.4 * vec2(brH(tile + 3.0), brH(tile + 9.0));
    float d = length(f - c) + 0.12 * brN(f * 6.0 + tile);
    float rr = 0.18 + 0.25 * th3;
    float blot = smoothstep(rr, rr - 0.12, d), ring = smoothstep(0.05, 0.0, abs(d - rr)) * 0.8;
    diffuseColor.rgb = mix(diffuseColor.rgb, diffuseColor.rgb * vec3(0.78, 0.62, 0.38), max(blot * 0.55, ring));
  }
  if (th3 > 0.992 && !fixtureTile) diffuseColor.rgb = vec3(0.012, 0.011, 0.009);   // missing tile: the dark above
#endif
#ifdef BR_PTILE
  // underwater: absorption tint + fine caustic network (thin bright filaments, ~25 cm cells, two drifting layers)
  float uw = smoothstep(-0.125, -0.165, wp.y);
  if (uw > 0.0) {
    float tt = uTime;
    float c = clamp(0.6 * brCaustic(wp.xz * 3.6 + vec2(tt * 0.11, tt * 0.07), tt * 0.55)
                  + 0.45 * brCaustic(wp.xz * 2.9 - vec2(tt * 0.08, -tt * 0.1) + 3.7, tt * 0.47 + 1.3), 0.0, 1.0);
    float depth = clamp((WATER_Y_GLSL - wp.y) / 0.5, 0.0, 1.0);
    vec3 tint = mix(vec3(0.66, 0.86, 0.77), vec3(0.42, 0.66, 0.56), depth);
    diffuseColor.rgb *= mix(vec3(1.0), tint * (0.93 + 0.55 * c), uw);
    brWet = 0.6 * uw;
  }
#endif
#ifdef BR_VENT
  diffuseColor.rgb *= 0.5 + 0.5 * step(0.45, fract(wp.x * 11.0));
#endif
}
`;

const GLSL_FOG = /* glsl */`
#ifdef USE_FOG
  #ifdef FOG_EXP2
    float fogFactor = 1.0 - exp( - fogDensity * fogDensity * vFogDepth * vFogDepth );
  #else
    float fogFactor = smoothstep( fogNear, fogFar, vFogDepth );
  #endif
  gl_FragColor.rgb = mix( gl_FragColor.rgb, fogColor, fogFactor );
#endif
`;

const patched = [];
function patch(mat, kind = '') {
  const fixture = kind === true;
  mat.onBeforeCompile = (sh) => {
    Object.assign(sh.uniforms, U);
    sh.vertexShader = sh.vertexShader
      .replace('#include <common>', '#include <common>\nvarying vec3 vBRWorld;')
      .replace('#include <project_vertex>', '#include <project_vertex>\nvBRWorld = (modelMatrix * vec4(transformed, 1.0)).xyz;');
    sh.fragmentShader = `#define BR_N ${QUALITY.n}\n#define BR_R ${QUALITY.r.toFixed(2)}\n` + (fixture ? '#define BR_FIXTURE\n' : '') + (typeof kind === 'string' && kind ? `#define BR_${kind}\n` : '') +
      sh.fragmentShader
        .replace('#include <common>', '#include <common>\n' + GLSL_COMMON)
        .replace('#include <lights_fragment_end>', GLSL_LIGHTS)
        .replace('#include <fog_fragment>', GLSL_FOG)
        .replace('#include <map_fragment>', '#include <map_fragment>\n' + GLSL_SURFACE)
        .replace('#include <roughnessmap_fragment>', '#include <roughnessmap_fragment>\nroughnessFactor = mix(roughnessFactor, 0.55, brWet);')
        .replace('#include <emissivemap_fragment>', `#include <emissivemap_fragment>
#ifdef BR_FIXTURE
  { vec4 bc = brCell(int(floor(vBRWorld.x / BR_S)), int(floor(vBRWorld.z / BR_S))); totalEmissiveRadiance *= uEmissive * brLightOn(bc) * brTint(bc); }
#endif`);
  };
  mat.customProgramCacheKey = () => 'br' + (fixture ? 'F' : '') + kind + QUALITY.n;
  patched.push(mat);
  return mat;
}

const M = {
  floor: patch(new THREE.MeshStandardMaterial({ map: T.carpetD, normalMap: T.carpetN, normalScale: new THREE.Vector2(1.1, 1.1), roughness: 1.0, metalness: 0, envMapIntensity: 0.6 }), 'FLOOR'),
  wall: patch(new THREE.MeshStandardMaterial({ map: T.wallD, normalMap: T.wallN, roughness: 0.78, metalness: 0, envMapIntensity: 0.8 }), 'WALL'),
  ceil: patch(new THREE.MeshStandardMaterial({ map: T.ceilD, normalMap: T.ceilN, roughnessMap: T.ceilR, roughness: 1.0, metalness: 0, envMapIntensity: 0.9 }), 'CEIL'),
  base: patch(new THREE.MeshStandardMaterial({ color: new THREE.Color(0.62, 0.56, 0.38), roughness: 0.45, metalness: 0, envMapIntensity: 1.0 })),
  fixture: patch(new THREE.MeshStandardMaterial({ map: T.lightD, normalMap: T.lightN, roughnessMap: T.lightR, emissiveMap: T.lightE,
    emissive: new THREE.Color(1.0, 0.95, 0.82), roughness: 1.0, metalness: 0.1 }), true),
  bottle: patch(new THREE.MeshStandardMaterial({ color: new THREE.Color(0.92, 0.88, 0.78), roughness: 0.12, metalness: 0, transparent: true, opacity: 0.82,
    emissive: new THREE.Color(0.08, 0.075, 0.05) })),
  plate: patch(new THREE.MeshStandardMaterial({ color: new THREE.Color(0.78, 0.76, 0.68), roughness: 0.38 })),
  vent: patch(new THREE.MeshStandardMaterial({ color: new THREE.Color(0.32, 0.31, 0.27), roughness: 0.55, metalness: 0.5 }), 'VENT'),
  label: patch(new THREE.MeshStandardMaterial({ color: new THREE.Color(0.85, 0.82, 0.7), roughness: 0.6 })),
  cap: patch(new THREE.MeshStandardMaterial({ color: new THREE.Color(0.25, 0.42, 0.75), roughness: 0.35 })),
};
M.ptile = patch(new THREE.MeshStandardMaterial({ map: T.ptD, normalMap: T.ptN, normalScale: new THREE.Vector2(0.45, 0.45), roughnessMap: T.ptR, roughness: 1.0, metalness: 0, envMapIntensity: 1.0 }), 'PTILE');
M.pceil = patch(new THREE.MeshStandardMaterial({ map: T.ptD, normalMap: T.ptN, normalScale: new THREE.Vector2(0.3, 0.3), roughness: 0.92, metalness: 0, envMapIntensity: 1.6 }), 'PTILE');
M.pacc = patch(new THREE.MeshStandardMaterial({ map: T.paD, normalMap: T.paN, normalScale: new THREE.Vector2(0.6, 0.6), roughnessMap: T.paR, roughness: 1.0, metalness: 0, envMapIntensity: 1.0 }), 'PTILE');
M.metal = patch(new THREE.MeshStandardMaterial({ color: new THREE.Color(0.86, 0.87, 0.88), roughness: 0.16, metalness: 1.0, envMapIntensity: 1.6 }));
M.chair = patch(new THREE.MeshStandardMaterial({ color: new THREE.Color(0.05, 0.05, 0.055), roughness: 0.85 }));
M.sky = patch(new THREE.MeshStandardMaterial({ color: new THREE.Color(0.9, 0.9, 0.9), emissive: new THREE.Color(1, 1, 1), roughness: 1.0 }), true);
M.puddle = patch(new THREE.MeshStandardMaterial({ color: new THREE.Color(0.02, 0.035, 0.04), roughness: 0.02, metalness: 0, envMapIntensity: 1.4, emissive: new THREE.Color(0.02, 0.075, 0.085) }));
M.portalCarpet = patch(new THREE.MeshStandardMaterial({ map: T.carpetD, normalMap: T.carpetN, roughness: 1.0, metalness: 0, envMapIntensity: 0.6 }), 'FLOOR');
for (const m of [M.fixture, M.vent, M.sky, M.puddle, M.portalCarpet]) { m.polygonOffset = true; m.polygonOffsetFactor = -1; m.polygonOffsetUnits = -4; } // never fight the ceiling


// ───────────────────────────── chunk geometry ──────────────────────────────
class GB {
  constructor() { this.p = []; this.n = []; this.u = []; this.i = []; }
  quad(a, b, c, d, n, ua, ub, uc, ud) {
    const o = this.p.length / 3;
    this.p.push(...a, ...b, ...c, ...d);
    for (let k = 0; k < 4; k++) this.n.push(...n);
    this.u.push(...ua, ...ub, ...uc, ...ud);
    this.i.push(o, o + 1, o + 2, o, o + 2, o + 3);
  }
  // vertical box sides with world-space UVs (u along surface, v up)
  box(x0, x1, y0, y1, z0, z1, sc, top = false, sides = true, bottom = false) {
    const v0 = y0 * sc, v1 = y1 * sc;
    if (sides) {
      this.quad([x1, y0, z1], [x1, y0, z0], [x1, y1, z0], [x1, y1, z1], [1, 0, 0], [-z1 * sc, v0], [-z0 * sc, v0], [-z0 * sc, v1], [-z1 * sc, v1]);
      this.quad([x0, y0, z0], [x0, y0, z1], [x0, y1, z1], [x0, y1, z0], [-1, 0, 0], [z0 * sc, v0], [z1 * sc, v0], [z1 * sc, v1], [z0 * sc, v1]);
      this.quad([x0, y0, z1], [x1, y0, z1], [x1, y1, z1], [x0, y1, z1], [0, 0, 1], [x0 * sc, v0], [x1 * sc, v0], [x1 * sc, v1], [x0 * sc, v1]);
      this.quad([x1, y0, z0], [x0, y0, z0], [x0, y1, z0], [x1, y1, z0], [0, 0, -1], [-x1 * sc, v0], [-x0 * sc, v0], [-x0 * sc, v1], [-x1 * sc, v1]);
    }
    if (top) this.quad([x0, y1, z1], [x1, y1, z1], [x1, y1, z0], [x0, y1, z0], [0, 1, 0], [x0 * sc, z1 * sc], [x1 * sc, z1 * sc], [x1 * sc, z0 * sc], [x0 * sc, z0 * sc]);
    if (bottom) this.quad([x0, y0, z0], [x1, y0, z0], [x1, y0, z1], [x0, y0, z1], [0, -1, 0], [x0 * sc, z0 * sc], [x1 * sc, z0 * sc], [x1 * sc, z1 * sc], [x0 * sc, z1 * sc]);
  }
  disc(cx, y, cz, r, seg, down = true, wob = 0) {   // flat disc (fan), UV 0..1; wob = irregular puddle edge
    const o = this.p.length / 3; this.p.push(cx, y, cz); this.n.push(0, down ? -1 : 1, 0); this.u.push(0.5, 0.5);
    for (let k = 0; k <= seg; k++) { const a = k / seg * Math.PI * 2, c = Math.cos(a), s = Math.sin(a), rr = r * (1 + wob * (0.55 * Math.sin(3 * a + cx) + 0.3 * Math.sin(5 * a + cz) + 0.15 * Math.sin(9 * a)));
      this.p.push(cx + rr * c, y, cz + rr * s); this.n.push(0, down ? -1 : 1, 0); this.u.push(0.5 + 0.5 * c, 0.5 + 0.5 * s); }
    for (let k = 0; k < seg; k++) down ? this.i.push(o, o + 1 + k, o + 2 + k) : this.i.push(o, o + 2 + k, o + 1 + k);
  }
  cyl(cx, cz, r, y0, y1, seg = 28, sc = 1) {      // smooth vertical cylinder, world-scaled UVs
    const o = this.p.length / 3;
    for (let k = 0; k <= seg; k++) { const a = k / seg * Math.PI * 2, c = Math.cos(a), s = Math.sin(a), u = a * r * sc;
      this.p.push(cx + r * c, y0, cz + r * s, cx + r * c, y1, cz + r * s); this.n.push(c, 0, s, c, 0, s); this.u.push(-u, y0 * sc, -u, y1 * sc); }
    for (let k = 0; k < seg; k++) { const a = o + k * 2, b = a + 2; this.i.push(b, a, a + 1, b, a + 1, b + 1); }
  }
  // two parallel polylines (A[k], B[k]) with per-vertex normals; triangle winding chosen to face the normals
  strip(A, B, N, UA, UB) {
    const o = this.p.length / 3, n = A.length;
    for (let k = 0; k < n; k++) { this.p.push(...A[k], ...B[k]); this.n.push(...N[k], ...N[k]); this.u.push(...UA[k], ...UB[k]); }
    const e1 = [A[1][0] - A[0][0], A[1][1] - A[0][1], A[1][2] - A[0][2]], e2 = [B[0][0] - A[0][0], B[0][1] - A[0][1], B[0][2] - A[0][2]];
    const fn = [e1[1] * e2[2] - e1[2] * e2[1], e1[2] * e2[0] - e1[0] * e2[2], e1[0] * e2[1] - e1[1] * e2[0]];
    const flip = fn[0] * N[0][0] + fn[1] * N[0][1] + fn[2] * N[0][2] < 0;
    for (let k = 0; k < n - 1; k++) { const a = o + k * 2, b = a + 1, c = a + 2, d = a + 3;
      if (flip) this.i.push(a, b, c, c, b, d); else this.i.push(a, c, b, c, d, b); }
  }
  fan(C, P, N, UC, UP) {                            // fan from C over polyline P, winding chosen to face N
    const o = this.p.length / 3; this.p.push(...C); this.n.push(...N); this.u.push(...UC);
    for (let k = 0; k < P.length; k++) { this.p.push(...P[k]); this.n.push(...N); this.u.push(...UP[k]); }
    const e1 = [P[0][0] - C[0], P[0][1] - C[1], P[0][2] - C[2]], e2 = [P[1][0] - C[0], P[1][1] - C[1], P[1][2] - C[2]];
    const fn = [e1[1] * e2[2] - e1[2] * e2[1], e1[2] * e2[0] - e1[0] * e2[2], e1[0] * e2[1] - e1[1] * e2[0]];
    const flip = fn[0] * N[0] + fn[1] * N[1] + fn[2] * N[2] < 0;
    for (let k = 0; k < P.length - 1; k++) flip ? this.i.push(o, o + 2 + k, o + 1 + k) : this.i.push(o, o + 1 + k, o + 2 + k);
  }
  geometry() {
    if (!this.i.length) return null;
    const g = new THREE.BufferGeometry();
    g.setAttribute('position', new THREE.Float32BufferAttribute(this.p, 3));
    g.setAttribute('normal', new THREE.Float32BufferAttribute(this.n, 3));
    g.setAttribute('uv', new THREE.Float32BufferAttribute(this.u, 2));
    g.setIndex(this.i); g.computeBoundingSphere(); return g;
  }
}

// collision / geometry boxes for one cell (walls owned by the cell + its vertex post)
function cellBoxes(cx, cz, out) {
  const x = cx * S, z = cz * S;
  for (const [a, b] of intervals(wallCode(cx, cz, 0))) out.push([x - HT, x + HT, z + a, z + b]);
  for (const [a, b] of intervals(wallCode(cx, cz, 1))) out.push([x + a, x + b, z - HT, z + HT]);
  const p = postSize(cx, cz);
  if (p) out.push([x - p, x + p, z - p, z + p, 1]);
  return out;
}

function specialAt(cx, cz) { const [L, i] = cellRef(cx, cz); return L.special && L.special.i === i ? L.special : null; }
function chairPlace(cx, cz) {                        // in front of a wall if the cell has one, facing it
  if (wallCode(cx, cz, 0) === FULL) return [cx * S + 0.75, cz * S + S / 2, -Math.PI / 2];
  if (wallCode(cx, cz, 1) === FULL) return [cx * S + S / 2, cz * S + 0.75, Math.PI];
  return [cx * S + S / 2, cz * S + S / 2, (hash(cx, cz, 93) & 3) * Math.PI / 2];
}
function specialBoxes(cx, cz, out) {
  const sp = specialAt(cx, cz); if (!sp) return;
  if (sp.t === 'chair') { const [x, z] = chairPlace(cx, cz); out.push([x - 0.3, x + 0.3, z - 0.3, z + 0.3]); }
}
const exitTex = (() => { const c = document.createElement('canvas'); c.width = 256; c.height = 96; const g = c.getContext('2d');
  g.fillStyle = '#06130a'; g.fillRect(0, 0, 256, 96); g.fillStyle = '#4dff7c'; g.font = 'bold 66px Arial, sans-serif'; g.textAlign = 'center'; g.textBaseline = 'middle';
  g.fillText('EXIT', 128, 52); const t = new THREE.CanvasTexture(c); t.colorSpace = THREE.SRGBColorSpace; return t; })();
const exitMats = (() => { const dark = new THREE.MeshStandardMaterial({ color: 0x1c1c1a, roughness: 0.6 });
  const face = new THREE.MeshBasicMaterial({ map: exitTex, color: new THREE.Color(2.4, 2.4, 2.4) }); return [face, dark, dark, dark, dark, dark]; })();
function buildChair() {
  const g = new THREE.Group(), fab = M.chair, met = M.metal;
  const box = (w, h, d, x, y, z, m) => { const o = new THREE.Mesh(new THREE.BoxGeometry(w, h, d), m); o.position.set(x, y, z); o.castShadow = true; g.add(o); return o; };
  box(0.5, 0.08, 0.48, 0, 0.48, 0, fab);                                      // seat
  const back = box(0.46, 0.52, 0.06, 0, 0.84, -0.24, fab); back.rotation.x = -0.12;
  box(0.05, 0.3, 0.05, 0, 0.6, -0.22, met);
  const post = new THREE.Mesh(new THREE.CylinderGeometry(0.025, 0.03, 0.34, 10), met); post.position.y = 0.28; g.add(post);
  for (let k = 0; k < 5; k++) { const a = k / 5 * Math.PI * 2, leg = box(0.04, 0.03, 0.3, Math.sin(a) * 0.15, 0.08, Math.cos(a) * 0.15, met); leg.rotation.y = a;
    const w = new THREE.Mesh(new THREE.SphereGeometry(0.03, 8, 6), fab); w.position.set(Math.sin(a) * 0.29, 0.03, Math.cos(a) * 0.29); g.add(w); }
  return g;
}
const bottleGeo = new THREE.CylinderGeometry(0.036, 0.036, 0.2, 18);
const labelGeo = new THREE.CylinderGeometry(0.0368, 0.0368, 0.08, 18, 1, true);
const capGeo = new THREE.CylinderGeometry(0.017, 0.017, 0.03, 12);
const neckGeo = new THREE.CylinderGeometry(0.017, 0.036, 0.04, 14);

const chunks = new Map();
const collected = new Set();
function buildChunk(kx, kz) {
  const group = new THREE.Group();
  if (LEVEL === 1) return buildChunkPool(kx, kz);
  const floor = new GB(), ceil = new GB(), walls = new GB(), base = new GB(), fix = new GB(), plate = new GB(), vent = new GB(), puddle = new GB();
  const x0 = kx * CHW, z0 = kz * CHW, x1 = x0 + CHW, z1 = z0 + CHW;
  const fs = 1 / 1.2;
  floor.quad([x0, 0, z1], [x1, 0, z1], [x1, 0, z0], [x0, 0, z0], [0, 1, 0], [x0 * fs, z1 * fs], [x1 * fs, z1 * fs], [x1 * fs, z0 * fs], [x0 * fs, z0 * fs]);
  ceil.quad([x0, H, z0], [x1, H, z0], [x1, H, z1], [x0, H, z1], [0, -1, 0], [x0, -z0], [x1, -z0], [x1, -z1], [x0, -z1]);
  const bottles = [];
  for (let cz = kz * CH; cz < kz * CH + CH; cz++) for (let cx = kx * CH; cx < kx * CH + CH; cx++) {
    const boxes = cellBoxes(cx, cz, []);
    for (const b of boxes) {
      walls.box(b[0], b[1], 0, H, b[2], b[3], 2 / H);
      base.box(b[0] - 0.016, b[1] + 0.016, 0, 0.1, b[2] - 0.016, b[3] + 0.016, 1, true);
    }
    // doorways: header above the opening + painted casing
    for (const dir of [0, 1]) {
      const code = wallCode(cx, cz, dir); if (!hasHeader(code)) continue;
      const c = S * (0.3 + 0.4 * (code % 50) / 49), a = c - DOOR, b = c + DOOR, DH = 2.12, ct = HT + 0.022, li = 0.025;
      if (dir === 0) {
        const x = cx * S, z = cz * S;
        walls.box(x - HT, x + HT, DH, H, z + a, z + b, 2 / H, false);
        walls.quad([x - HT, DH, z + a], [x + HT, DH, z + a], [x + HT, DH, z + b], [x - HT, DH, z + b], [0, -1, 0], [0, 0], [0.1, 0], [0.1, 1], [0, 1]);
        base.box(x - ct, x + ct, 0, DH + 0.06, z + a - 0.07, z + a + li, 1, true); base.box(x - ct, x + ct, 0, DH + 0.06, z + b - li, z + b + 0.07, 1, true);
        base.box(x - ct, x + ct, DH - li, DH + 0.075, z + a + li, z + b - li, 1, true, true, true);
      } else {
        const x = cx * S, z = cz * S;
        walls.box(x + a, x + b, DH, H, z - HT, z + HT, 2 / H, false);
        walls.quad([x + a, DH, z - HT], [x + b, DH, z - HT], [x + b, DH, z + HT], [x + a, DH, z + HT], [0, -1, 0], [0, 0], [1, 0], [1, 0.1], [0, 0.1]);
        base.box(x + a - 0.07, x + a + li, 0, DH + 0.06, z - ct, z + ct, 1, true); base.box(x + b - li, x + b + 0.07, 0, DH + 0.06, z - ct, z + ct, 1, true);
        base.box(x + a + li, x + b - li, DH - li, DH + 0.075, z - ct, z + ct, 1, true, true, true);
      }
    }
    // wall outlets on some wall runs
    for (const b of boxes) {
      if (b[4]) continue; const len = Math.max(b[1] - b[0], b[3] - b[2]); if (len < 0.8) continue;
      const h = hash(Math.round(b[0] * 10), Math.round(b[2] * 10), 21); if ((h >>> 24) > 26) continue;
      const t = 0.25 + 0.5 * ((h >>> 8) & 255) / 255, side = (h & 1) ? 1 : -1, y0 = 0.27, y1 = 0.39, hw = 0.037, pr = 0.009;
      if (b[1] - b[0] < b[3] - b[2]) { const zc = b[2] + t * (b[3] - b[2]), xf = side > 0 ? b[1] : b[0];
        plate.box(Math.min(xf, xf + side * pr), Math.max(xf, xf + side * pr), y0, y1, zc - hw, zc + hw, 1, true);
      } else { const xc = b[0] + t * (b[1] - b[0]), zf = side > 0 ? b[3] : b[2];
        plate.box(xc - hw, xc + hw, y0, y1, Math.min(zf, zf + side * pr), Math.max(zf, zf + side * pr), 1, true); }
    }
    // return-air vents in random ceiling tiles
    { const h = hash(cx, cz, 22); if ((h >>> 24) < 14) { const tx = cx * S + [0, 2][h & 1], tz = cz * S + ((h >>> 1) % 3), y = H - 0.006;
      vent.quad([tx + 0.1, y, tz + 0.1], [tx + 0.9, y, tz + 0.1], [tx + 0.9, y, tz + 0.9], [tx + 0.1, y, tz + 0.9], [0, -1, 0], [0, 0], [1, 0], [1, 1], [0, 1]); } }
    const L = lightState(cx, cz);
    if (L.s) {
      const lx = cx * S + 1, lz = cz * S + 1, y = H - 0.004;
      fix.quad([lx, y, lz], [lx + 1, y, lz], [lx + 1, y, lz + 1], [lx, y, lz + 1], [0, -1, 0], [0, 1], [1, 1], [1, 0], [0, 0]);
    }
    { const sp = specialAt(cx, cz);
      if (sp && sp.t === 'chair') { const [px, pz, yaw] = chairPlace(cx, cz), ch = buildChair(); ch.position.set(px, 0, pz); ch.rotation.y = yaw; group.add(ch); }
      if (sp && sp.t === 'exit') { const e = new THREE.Mesh(new THREE.BoxGeometry(0.05, 0.2, 0.54), exitMats); e.position.set(cx * S + HT + 0.03, 2.28, cz * S + S / 2); group.add(e); }
    }
    { const [RL, ri] = cellRef(cx, cz); if (RL.portal === ri) puddle.disc((cx + 0.5) * S, 0.004, (cz + 0.5) * S, 0.7, 64, false, 0.28); }
    const bt = bottleAt(cx, cz);
    if (bt && !collected.has(lvKey() + ':' + cx + ',' + cz)) bottles.push({ ...bt, key: lvKey() + ':' + cx + ',' + cz });
  }
  const add = (gb, mat, cast) => { const g = gb.geometry(); if (!g) return; const m = new THREE.Mesh(g, mat); m.receiveShadow = true; m.castShadow = !!cast; m.matrixAutoUpdate = false; group.add(m); };
  add(floor, M.floor); add(ceil, M.ceil); add(walls, M.wall, true); add(base, M.base); add(fix, M.fixture); add(plate, M.plate); add(vent, M.vent); add(puddle, M.puddle);
  return finishChunk(group, bottles);
}
function finishChunk(group, bottles) {
  const items = [];
  for (const b of bottles) {
    const g = new THREE.Group();
    const body = new THREE.Mesh(bottleGeo, M.bottle); body.position.y = 0.1;
    const lab = new THREE.Mesh(labelGeo, M.label); lab.position.y = 0.09;
    const neck = new THREE.Mesh(neckGeo, M.bottle); neck.position.y = 0.22;
    const cap = new THREE.Mesh(capGeo, M.cap); cap.position.y = 0.255;
    g.add(body, lab, neck, cap); g.position.set(b.x, groundAt(b.x, b.z), b.z); g.rotation.z = 0; g.userData = b;
    for (const m of g.children) m.castShadow = true;
    group.add(g); items.push(g);
  }
  scene.add(group);
  return { group, items };
}
const COVE_R = 0.55, PT = 0.5;                     // cove radius; pool tiles: 2 m per texture repeat
// concave quarter-round cove where a wall meets the ceiling (dir 0: wall plane x = w, running along z)
function addCove(gb, dir, w, a0, a1, side, caps) {
  const seg = 7, faceW = w + side * HT, cW = faceW + side * COVE_R, cY = H - COVE_R;
  const A = [], B = [], N = [], UA = [], UB = [], prof = [];
  for (let k = 0; k <= seg; k++) {
    const th = k / seg * Math.PI / 2, pw = cW - side * COVE_R * Math.cos(th), py = cY + COVE_R * Math.sin(th);
    const nw = side * Math.cos(th), ny = -Math.sin(th), v = (cY + th * COVE_R) * PT;
    prof.push([pw, py]);
    if (dir === 0) { A.push([pw, py, a0]); B.push([pw, py, a1]); N.push([nw, ny, 0]); UA.push([-side * a0 * PT, v]); UB.push([-side * a1 * PT, v]); }
    else { A.push([a0, py, pw]); B.push([a1, py, pw]); N.push([0, ny, nw]); UA.push([side * a0 * PT, v]); UB.push([side * a1 * PT, v]); }
  }
  gb.strip(A, B, N, UA, UB);
  if (!caps) return;
  for (const [t, sg] of [[a0, -1], [a1, 1]]) {     // close the cove ends at openings
    const C = dir === 0 ? [faceW, H, t] : [t, H, faceW];
    const P = prof.map(([pw, py]) => dir === 0 ? [pw, py, t] : [t, py, pw]);
    const Nn = dir === 0 ? [0, 0, sg] : [sg, 0, 0];
    gb.fan(C, P, Nn, [0, H * PT], prof.map(([pw, py]) => [pw * PT, py * PT]));
  }
}
// panel pierced by a circular arch, built directly as quads (front, back, and the barrel of the opening)
function addArch(gb, dir, ex, ez, ybot) {
  const cx0 = S / 2, cy = ybot + 1.62, R = 1.55, seg = 64;
  const W = (u, y, d) => dir === 1 ? [ex + u, y, ez + d] : [ex + d, y, ez + u];   // u along the wall, d across it
  const nrm = (d) => dir === 1 ? [0, 0, d] : [d, 0, 0];
  const ring = [], rect = [];
  for (let k = 0; k <= seg; k++) {
    const a = k / seg * Math.PI * 2, c = Math.cos(a), sn = Math.sin(a);
    ring.push([cx0 + R * c, cy + R * sn]);
    // where the ray from the arch centre leaves the panel rectangle [0,S]x[ybot,H]
    let t = Infinity;
    if (c > 1e-6) t = Math.min(t, (S - cx0) / c); if (c < -1e-6) t = Math.min(t, -cx0 / c);
    if (sn > 1e-6) t = Math.min(t, (H - cy) / sn); if (sn < -1e-6) t = Math.min(t, (ybot - cy) / sn);
    rect.push([cx0 + t * c, cy + t * sn]);
  }
  for (const d of [-HT, HT]) {
    const A = ring.map(([u, y]) => W(u, y, d)), B = rect.map(([u, y]) => W(u, y, d)), N = ring.map(() => nrm(Math.sign(d)));
    const sgn = (dir === 1 ? 1 : -1) * Math.sign(d);
    gb.strip(A, B, N, ring.map(([u, y]) => [sgn * (ex + ez + u) * PT, y * PT]), rect.map(([u, y]) => [sgn * (ex + ez + u) * PT, y * PT]));
  }
  { const A = ring.map(([u, y]) => W(u, y, -HT)), B = ring.map(([u, y]) => W(u, y, HT));
    const N = ring.map(([u, y]) => { const nu = -(u - cx0) / R, ny = -(y - cy) / R; return dir === 1 ? [nu, ny, 0] : [0, ny, nu]; });
    gb.strip(A, B, N, ring.map((_, k) => [k / seg * 2 * Math.PI * R * PT, 0]), ring.map((_, k) => [k / seg * 2 * Math.PI * R * PT, 2 * HT * PT])); }
}
const archGeos = new Map();
function archGeometry(ybot) {
  let g = archGeos.get(ybot); if (g) return g;
  const sh = new THREE.Shape(); sh.moveTo(0, ybot); sh.lineTo(S, ybot); sh.lineTo(S, H); sh.lineTo(0, H); sh.lineTo(0, ybot);
  const hole = new THREE.Path(); hole.absarc(S / 2, ybot + 1.62, 1.55, 0, Math.PI * 2, true);   // clear of the panel's bottom edge sh.holes.push(hole);
  g = new THREE.ExtrudeGeometry(sh, { depth: 2 * HT, bevelEnabled: false, curveSegments: 48 });
  g.translate(0, 0, -HT);
  const uv = g.attributes.uv; for (let i = 0; i < uv.count; i++) uv.setXY(i, uv.getX(i) * PT, uv.getY(i) * PT);
  g.computeBoundingSphere(); archGeos.set(ybot, g); return g;
}
// visible sunbeams: real volumetric light. Each skylight gets a bounding prism; its back faces ray-march the air
// inside, testing every sample against the sun's shadow map, so beams take the exact shape of the opening and
// are cut by walls, coves and columns. Henyey-Greenstein forward scattering makes them glow toward the sun.
const beamMat = new THREE.ShaderMaterial({
  uniforms: { uTime: U.uTime, uCol: { value: new THREE.Color(1.0, 0.91, 0.76) }, uI: { value: 0.14 }, uFogD: { value: 0.03 },
    uShadowMap: { value: null }, uShadowMatrix: { value: new THREE.Matrix4() }, uHasShadow: { value: 0 }, uSunDir: { value: new THREE.Vector3() },
    uWaterY: { value: -0.14 }, uH: U.uH },
  vertexShader: /* glsl */`varying vec3 vW; varying vec3 vN;
    void main(){ vec4 w = modelMatrix * vec4(position, 1.0); vW = w.xyz; vN = normal; gl_Position = projectionMatrix * viewMatrix * w; }`,
  fragmentShader: /* glsl */`
    #include <packing>
    uniform float uTime; uniform vec3 uCol; uniform float uI; uniform float uFogD; uniform sampler2D uShadowMap; uniform mat4 uShadowMatrix;
    uniform float uHasShadow; uniform vec3 uSunDir; uniform float uWaterY; uniform float uH;
    varying vec3 vW; varying vec3 vN;
    float h3(vec3 p){ return fract(sin(dot(p, vec3(12.9898, 78.233, 37.719))) * 43758.5453); }
    float n3(vec3 p){ vec3 i = floor(p), f = fract(p); f = f * f * (3.0 - 2.0 * f);
      return mix(mix(mix(h3(i), h3(i + vec3(1,0,0)), f.x), mix(h3(i + vec3(0,1,0)), h3(i + vec3(1,1,0)), f.x), f.y),
                 mix(mix(h3(i + vec3(0,0,1)), h3(i + vec3(1,0,1)), f.x), mix(h3(i + vec3(0,1,1)), h3(i + vec3(1,1,1)), f.x), f.y), f.z); }
    float sunlit(vec3 p){
      vec4 sc = uShadowMatrix * vec4(p, 1.0);
      if (sc.x < 0.0 || sc.x > 1.0 || sc.y < 0.0 || sc.y > 1.0 || sc.z < 0.0 || sc.z > 1.0) return 0.0;
      return step(sc.z - 0.0003, unpackRGBAToDepth(texture2D(uShadowMap, sc.xy)));
    }
    void main(){
      vec3 toFrag = vW - cameraPosition; float tBack = length(toFrag); vec3 rd = toFrag / tBack;
      if (dot(vN, rd) < 0.0) discard;                                 // only the far side of the volume integrates
      if (uHasShadow < 0.5) discard;
      float t0 = max(0.05, tBack - 7.0), len = tBack - t0;
      const int N = 22;
      float dt = len / float(N);
      float jit = fract(sin(dot(gl_FragCoord.xy, vec2(12.9898, 78.233))) * 43758.5453);
      float acc = 0.0;
      for (int i = 0; i < N; i++) {
        float t = t0 + (float(i) + jit) * dt; vec3 p = cameraPosition + rd * t;
        if (p.y < uWaterY || p.y > uH - 0.12) continue;
        float lit = sunlit(p);
        if (lit <= 0.0) continue;
        float haze = 0.55 + 0.9 * n3(p * 1.3 + vec3(uTime * 0.04, -uTime * 0.02, uTime * 0.03));   // drifting, uneven dust
        float fall = 0.55 + 0.45 * smoothstep(0.0, uH, p.y);                                     // a touch denser up high
        acc += lit * haze * fall * dt;
      }
      if (acc <= 0.0) discard;
      // forward scattering: looking towards the sun through a beam makes it blaze, looking away makes it faint
      float g = 0.55, cosT = dot(-rd, -uSunDir);
      float phase = (1.0 - g * g) / pow(1.0 + g * g - 2.0 * g * cosT, 1.5);
      float fog = exp(-uFogD * uFogD * tBack * tBack * 0.5);
      gl_FragColor = vec4(uCol * (uI * acc * phase * fog), 1.0);
    }`,
  transparent: true, depthWrite: false, blending: THREE.AdditiveBlending, side: THREE.DoubleSide,
});
const beamMeshes = new Set();
const voidMat = new THREE.MeshBasicMaterial({ color: 0x000000 });
const skyTopMat = new THREE.MeshBasicMaterial({ color: new THREE.Color(7.5, 7.2, 6.4), fog: false });
function buildChunkPool(kx, kz) {
  const group = new THREE.Group();
  const floor = new GB(), basin = new GB(), ceil = new GB(), walls = new GB(), sky = new GB(), portal = new GB(), beam = new GB(), voidQ = new GB(), metal = [];
  const bottles = [];
  const sk = 0.7, WELL = 1.1;                       // skylight half-size and shaft depth
  for (let cz = kz * CH; cz < kz * CH + CH; cz++) for (let cx = kx * CH; cx < kx * CH + CH; cx++) {
    const x = cx * S, z = cz * S, pool = isPool(cx, cz), y = pool ? -PD : 0;
    (pool ? basin : floor).quad([x, y, z + S], [x + S, y, z + S], [x + S, y, z], [x, y, z], [0, 1, 0], [x * PT, (z + S) * PT], [(x + S) * PT, (z + S) * PT], [(x + S) * PT, z * PT], [x * PT, z * PT]);
    // ceiling, with a square sun shaft where this cell has a skylight
    const L = lightState(cx, cz), cq = (x0, z0, x1, z1) => ceil.quad([x0, H, z0], [x1, H, z0], [x1, H, z1], [x0, H, z1], [0, -1, 0], [x0 * PT, -z0 * PT], [x1 * PT, -z0 * PT], [x1 * PT, -z1 * PT], [x0 * PT, -z1 * PT]);
    if (L.s) {
      const mx = x + S / 2, mz = z + S / 2, h0 = mx - sk, h1 = mx + sk, j0 = mz - sk, j1 = mz + sk, Y = H + WELL;
      cq(x, z, x + S, j0); cq(x, j1, x + S, z + S); cq(x, j0, h0, j1); cq(h1, j0, x + S, j1);
      ceil.quad([h0, H, j1], [h0, H, j0], [h0, Y, j0], [h0, Y, j1], [1, 0, 0], [-j1 * PT, H * PT], [-j0 * PT, H * PT], [-j0 * PT, Y * PT], [-j1 * PT, Y * PT]);
      ceil.quad([h1, H, j0], [h1, H, j1], [h1, Y, j1], [h1, Y, j0], [-1, 0, 0], [j0 * PT, H * PT], [j1 * PT, H * PT], [j1 * PT, Y * PT], [j0 * PT, Y * PT]);
      ceil.quad([h0, H, j0], [h1, H, j0], [h1, Y, j0], [h0, Y, j0], [0, 0, 1], [h0 * PT, H * PT], [h1 * PT, H * PT], [h1 * PT, Y * PT], [h0 * PT, Y * PT]);
      ceil.quad([h1, H, j1], [h0, H, j1], [h0, Y, j1], [h1, Y, j1], [0, 0, -1], [-h1 * PT, H * PT], [-h0 * PT, H * PT], [-h0 * PT, Y * PT], [-h1 * PT, Y * PT]);
      sky.quad([h0, Y, j0], [h1, Y, j0], [h1, Y, j1], [h0, Y, j1], [0, -1, 0], [0, 0], [1, 0], [1, 1], [0, 1]);
      // bounding volume for the shaft of light falling from the opening (the shadow map gives its true shape)
      { const mg = 0.35, k = (H + 0.2) / SUN_DIR.y, dx = -SUN_DIR.x * k, dz = -SUN_DIR.z * k, yb = -0.2, yt = H + 0.02;
        const T = [[h0 - mg, j0 - mg], [h1 + mg, j0 - mg], [h1 + mg, j1 + mg], [h0 - mg, j1 + mg]];
        const top = T.map(([x2, z2]) => [x2, yt, z2]), bot = T.map(([x2, z2]) => [x2 + dx, yb, z2 + dz]);
        const C = [mx + dx / 2, (yt + yb) / 2, mz + dz / 2];
        const face = (a, b, c, d) => { const u = [b[0] - a[0], b[1] - a[1], b[2] - a[2]], v = [d[0] - a[0], d[1] - a[1], d[2] - a[2]];
          let n = [u[1] * v[2] - u[2] * v[1], u[2] * v[0] - u[0] * v[2], u[0] * v[1] - u[1] * v[0]]; const l = Math.hypot(...n) || 1; n = n.map(q => q / l);
          const fc = [(a[0] + c[0]) / 2 - C[0], (a[1] + c[1]) / 2 - C[1], (a[2] + c[2]) / 2 - C[2]];
          if (n[0] * fc[0] + n[1] * fc[1] + n[2] * fc[2] < 0) n = n.map(q => -q);
          beam.quad(a, b, c, d, n, [0, 0], [1, 0], [1, 1], [0, 1]); };
        for (let e = 0; e < 4; e++) face(top[e], top[(e + 1) % 4], bot[(e + 1) % 4], bot[e]);
        face(top[0], top[1], top[2], top[3]); face(bot[0], bot[1], bot[2], bot[3]); }
    } else cq(x, z, x + S, z + S);
    if (pool) {                                   // basin sides + a raised tiled lip on the deck side
      const cw = 0.22, ch = 0.03;
      if (!isPool(cx - 1, cz)) { basin.quad([x, -PD, z + S], [x, -PD, z], [x, 0, z], [x, 0, z + S], [1, 0, 0], [(-z - S) * PT, -PD * PT], [-z * PT, -PD * PT], [-z * PT, 0], [(-z - S) * PT, 0]); walls.box(x - cw, x, 0, ch, z, z + S, PT, true); }
      if (!isPool(cx + 1, cz)) { basin.quad([x + S, -PD, z], [x + S, -PD, z + S], [x + S, 0, z + S], [x + S, 0, z], [-1, 0, 0], [z * PT, -PD * PT], [(z + S) * PT, -PD * PT], [(z + S) * PT, 0], [z * PT, 0]); walls.box(x + S, x + S + cw, 0, ch, z, z + S, PT, true); }
      if (!isPool(cx, cz - 1)) { basin.quad([x, -PD, z], [x + S, -PD, z], [x + S, 0, z], [x, 0, z], [0, 0, 1], [x * PT, -PD * PT], [(x + S) * PT, -PD * PT], [(x + S) * PT, 0], [x * PT, 0]); walls.box(x, x + S, 0, ch, z - cw, z, PT, true); }
      if (!isPool(cx, cz + 1)) { basin.quad([x + S, -PD, z + S], [x, -PD, z + S], [x, 0, z + S], [x + S, 0, z + S], [0, 0, -1], [(-x - S) * PT, -PD * PT], [-x * PT, -PD * PT], [-x * PT, 0], [(-x - S) * PT, 0]); walls.box(x, x + S, 0, ch, z + S, z + S + cw, PT, true); }
    }
    // walls (reaching down into the water where they stand in it) with coves into the ceiling
    for (const dir of [0, 1]) {
      const code = wallCode(cx, cz, dir); if (!code) continue;
      const y0 = (dir === 0 ? (isPool(cx - 1, cz) || isPool(cx, cz)) : (isPool(cx, cz - 1) || isPool(cx, cz))) ? -PD : 0;
      if (code === ARCH_CODE) {
        addArch(walls, dir, x, z, y0);
        for (const sd of [-1, 1]) addCove(walls, dir, dir === 0 ? x : z, (dir === 0 ? z : x) + HT, (dir === 0 ? z : x) + S - HT, sd, false);
        continue;
      }
      for (const [a, b] of intervals(code)) {
        if (dir === 0) walls.box(x - HT, x + HT, y0, H, z + a, z + b, PT); else walls.box(x + a, x + b, y0, H, z - HT, z + HT, PT);
        const open0 = a > HT + 0.01, open1 = b < S - HT - 0.01;
        for (const sd of [-1, 1]) addCove(walls, dir, dir === 0 ? x : z, (dir === 0 ? z : x) + a, (dir === 0 ? z : x) + b, sd, open0 || open1);
      }
    }
    const p = postSize(cx, cz);
    if (p) {
      const y0 = (isPool(cx - 1, cz - 1) || isPool(cx, cz - 1) || isPool(cx - 1, cz) || isPool(cx, cz)) ? -PD : 0;
      if (p > 0.3) walls.cyl(x, z, 0.4, y0, H, 36, PT); else walls.box(x - p, x + p, y0, H, z - p, z + p, PT);
    }
    { const [RL, ri] = cellRef(cx, cz);
      if (RL.portal === ri) { const c0 = 0.85, c1 = 2.15, fs = 1 / 1.2;
        portal.quad([x + c0, 0.004, z + c1], [x + c1, 0.004, z + c1], [x + c1, 0.004, z + c0], [x + c0, 0.004, z + c0], [0, 1, 0], [(x + c0) * fs, (z + c1) * fs], [(x + c1) * fs, (z + c1) * fs], [(x + c1) * fs, (z + c0) * fs], [(x + c0) * fs, (z + c0) * fs]); }
      for (const ld of RL.ladders) if (ld[1] * RG + ld[0] === ri) metal.push([cx, cz, ld[2]]);
      const sp = specialAt(cx, cz);
      if (sp && sp.t === 'stairs') {                // tiled steps climbing out of the water into a dark doorway in the wall
        const g0 = isPool(cx, cz) ? -PD : 0, n = STAIR.n, top = STAIR.top, x0 = x + STAIR.x0, x1 = x + STAIR.x1;
        for (let k = 0; k < n; k++) { const zt = z + HT + (n - k) * STAIR.depth, yt = g0 + (k + 1) * (top - g0) / n;
          walls.box(x0, x1, g0, yt, z + HT, zt, PT, true); }
        voidQ.quad([x0, top, z + HT + 0.004], [x1, top, z + HT + 0.004], [x1, top + 1.9, z + HT + 0.004], [x0, top + 1.9, z + HT + 0.004], [0, 0, 1], [0, 0], [1, 0], [1, 1], [0, 1]);
      }
    }
    const bt = bottleAt(cx, cz);
    if (bt && !collected.has(lvKey() + ':' + cx + ',' + cz)) bottles.push({ ...bt, key: lvKey() + ':' + cx + ',' + cz });
  }
  const add = (gb, mat, cast) => { const g = gb.geometry(); if (!g) return; const m = new THREE.Mesh(g, mat); m.receiveShadow = true; m.castShadow = !!cast; m.matrixAutoUpdate = false; group.add(m); };
  add(floor, M.ptile); add(basin, M.ptile, true); add(ceil, M.pceil, true); add(walls, M.ptile, true); add(sky, skyTopMat); add(portal, M.portalCarpet); add(voidQ, voidMat);
  { const g = beam.geometry(); if (g) { const m = new THREE.Mesh(g, beamMat); m.renderOrder = 6; m.matrixAutoUpdate = false; m.receiveShadow = false; group.add(m); beamMeshes.add(m); } }
  for (const [cx, cz, dir] of metal) group.add(buildLadder(cx, cz, dir));
  return finishChunk(group, bottles);
}
// stainless pool ladder hooked over the basin edge
function buildLadder(cx, cz, dir) {
  const g = new THREE.Group(), e = dir === 1 ? cz * S : cx * S, mid = (dir === 1 ? cx : cz) * S + S / 2;
  const P = (u, y, along) => dir === 1 ? new THREE.Vector3(along, y, u) : new THREE.Vector3(u, y, along);
  for (const off of [-0.27, 0.27]) {
    const c = new THREE.CatmullRomCurve3([P(e - 0.42, 0, mid + off), P(e - 0.42, 0.62, mid + off), P(e - 0.33, 0.93, mid + off), P(e - 0.12, 0.98, mid + off),
      P(e + 0.06, 0.78, mid + off), P(e + 0.13, 0.3, mid + off), P(e + 0.13, -PD, mid + off)], false, 'catmullrom', 0.3);
    const m = new THREE.Mesh(new THREE.TubeGeometry(c, 48, 0.024, 12), M.metal); m.castShadow = true; g.add(m);
  }
  for (const yy of [-0.08, -0.32]) {
    const st = new THREE.Mesh(new THREE.BoxGeometry(dir === 1 ? 0.54 : 0.08, 0.025, dir === 1 ? 0.08 : 0.54), M.metal);
    st.position.copy(P(e + 0.13, yy, mid)); g.add(st);
  }
  return g;
}
function disposeChunk(c) {
  scene.remove(c.group);
  c.group.traverse(o => beamMeshes.delete(o));
  c.group.traverse(o => { if (o.isMesh && ![...archGeos.values()].includes(o.geometry) && o.geometry !== bottleGeo && o.geometry !== labelGeo && o.geometry !== capGeo && o.geometry !== neckGeo) o.geometry.dispose(); });
}
let VIEW_R = 2;
function streamChunks(px, pz, budget) {
  const kx = Math.floor(px / CHW), kz = Math.floor(pz / CHW);
  const need = [];
  for (let i = -VIEW_R; i <= VIEW_R; i++) for (let j = -VIEW_R; j <= VIEW_R; j++) {
    const key = (kx + i) + ',' + (kz + j); if (!chunks.has(key)) need.push([i * i + j * j, kx + i, kz + j, key]);
  }
  need.sort((a, b) => a[0] - b[0]);
  for (let n = 0; n < Math.min(budget, need.length); n++) { const [, x, z, key] = need[n]; chunks.set(key, buildChunk(x, z)); chunkDirty = true; }
  for (const [key, c] of chunks) {
    const [x, z] = key.split(',').map(Number);
    if (Math.abs(x - kx) > VIEW_R + 1 || Math.abs(z - kz) > VIEW_R + 1) { disposeChunk(c); chunks.delete(key); }
  }
}

// ───────────────────────────── water ───────────────────────────────────────
// One planar reflection for the whole level (all water sits at WATER_Y), sampled with wave-distorted UVs.
const WaterShader = {
  name: 'PoolWater',
  uniforms: { color: { value: null }, tDiffuse: { value: null }, textureMatrix: { value: null }, uTime: { value: 0 },
    uPlayer: { value: new THREE.Vector3() }, uFogD: { value: 0.014 }, uFogC: { value: new THREE.Color() } },
  vertexShader: /* glsl */`
    uniform mat4 textureMatrix; varying vec4 vUv4; varying vec3 vW;
    void main(){ vUv4 = textureMatrix * vec4(position, 1.0); vW = (modelMatrix * vec4(position, 1.0)).xyz;
      gl_Position = projectionMatrix * modelViewMatrix * vec4(position, 1.0); }`,
  fragmentShader: /* glsl */`
    uniform sampler2D tDiffuse; uniform float uTime; uniform vec3 uPlayer; uniform float uFogD; uniform vec3 uFogC;
    varying vec4 vUv4; varying vec3 vW;
    float h21(vec2 p){ return fract(sin(dot(p, vec2(127.1, 311.7))) * 43758.5453); }
    float vn(vec2 p){ vec2 i = floor(p), f = fract(p); f = f * f * (3.0 - 2.0 * f);
      return mix(mix(h21(i), h21(i + vec2(1, 0)), f.x), mix(h21(i + vec2(0, 1)), h21(i + vec2(1, 1)), f.x), f.y); }
    vec2 wave(vec2 p, vec2 d, float k, float a, float sp){ return d * (a * k * cos(dot(p, d) * k + uTime * sp)); }
    void main(){
      vec2 p = vW.xz;
      // slope of the surface: long swells + dense fine ripples (these break reflections into wavy slivers)
      vec2 g = wave(p, normalize(vec2(1.0, 0.31)), 2.6, 0.006, 1.1) + wave(p, normalize(vec2(-0.42, 1.0)), 4.3, 0.004, 1.6)
             + wave(p, normalize(vec2(0.7, -0.8)), 9.0, 0.0026, 2.6) + wave(p, normalize(vec2(-0.9, -0.25)), 14.0, 0.0016, 3.3)
             + wave(p, normalize(vec2(0.15, 1.0)), 21.0, 0.0011, 4.1) + wave(p, normalize(vec2(-1.0, 0.6)), 29.0, 0.0007, 5.0);
      float e = 0.03, t = uTime * 0.3;
      float n0 = vn(p * 5.0 + t), nx = vn((p + vec2(e, 0.0)) * 5.0 + t), nz = vn((p + vec2(0.0, e)) * 5.0 + t);
      g += vec2(nx - n0, nz - n0) / e * 0.005;
      if (uPlayer.z > 0.01) {                         // rings spreading from the player while wading
        vec2 dp = p - uPlayer.xy; float d = length(dp) + 1e-3;
        g += dp / d * cos(d * 13.0 - uTime * 7.5) * 13.0 * exp(-d * 1.3) * 0.0022 * uPlayer.z;
      }
      vec3 n = normalize(vec3(-g.x, 1.0, -g.y));
      vec3 V = normalize(cameraPosition - vW);
      float cosT = max(dot(V, n), 0.0);
      float F = 0.02 + 0.98 * pow(1.0 - cosT, 5.0);
      float Fa = mix(0.55, 1.0, F);                   // calm indoor water reads as a strong mirror
      // screen-space displacement from the tilted normal: reflections stretch vertically on a wavy surface
      vec3 vn3 = (viewMatrix * vec4(n.x, 0.0, n.z, 0.0)).xyz;
      float dist = length(cameraPosition - vW);
      float k = clamp(1.6 / (0.6 + dist * 0.25), 0.25, 1.6);
      vec2 off = vec2(vn3.x * 0.035, vn3.z * 0.16 + vn3.y * 0.05) * k;
      vec4 uv = vUv4; uv.xy += off * uv.w;
      // vertical smear: a few taps along the screen's up axis turn bright shapes into streaks
      vec3 refl = vec3(0.0); float ws = 0.0;
      for (int i = 0; i < 6; i++) {
        float fi = float(i) / 5.0 - 0.3, w = 1.0 - abs(fi) * 1.1;
        vec4 u2 = uv; u2.y += fi * 0.022 * k * uv.w;
        refl += texture2DProj(tDiffuse, u2).rgb * w; ws += w;
      }
      refl /= ws;
      float lum = dot(refl, vec3(0.3, 0.5, 0.2));
      vec3 body = vec3(0.06, 0.2, 0.16) * (0.35 + 0.65 * clamp(lum, 0.0, 2.0));
      float a = clamp(Fa + 0.08, 0.0, 1.0);
      vec3 col = (refl * Fa + body * 0.08) / a;
      float fog = 1.0 - exp(-uFogD * uFogD * dist * dist);
      gl_FragColor = vec4(mix(col, uFogC, fog), a);
    }`,
};
const water = new Reflector(new THREE.PlaneGeometry(280, 280), { shader: WaterShader, clipBias: 0.002, multisample: 0, textureWidth: 512, textureHeight: 512 });
water.rotation.x = -Math.PI / 2; water.position.y = WATER_Y;
water.material.transparent = true; water.material.depthWrite = false;
water.visible = false; water.renderOrder = 5;
{ const ob = water.onBeforeRender; water.onBeforeRender = function (r, sc, cam, ...rest) { if (sc.overrideMaterial) return; ob.call(this, r, sc, cam, ...rest); }; }
scene.add(water);
function sizeWater() {
  const sc = perf.scale * (IS_TOUCH ? 0.4 : 0.5);
  water.getRenderTarget().setSize(Math.max(64, Math.round(innerWidth * sc)), Math.max(64, Math.round(innerHeight * sc)));
}

// ───────────────────────────── levels ──────────────────────────────────────
const LV = [
  { H: 2.7, lightI: 11.0, cool: 0, ambient: 0.012, envScale: 0.55, emissive: 4.2, fog: [0, 0, 0], fogD: 0.014, sun: 0, envFloor: 0 },
  { H: 3.6, lightI: 9.0, cool: 0.5, ambient: 0.05, envScale: 1.05, emissive: 0, fog: [0.42, 0.46, 0.41], fogD: 0.03, sun: 5.5, envFloor: 0.42 },
];
function setLevel(n) {
  LEVEL = n; FLOOR = 0; pregions.clear(); const P = LV[n]; H = P.H;
  U.uH.value = H; U.uLightI.value = P.lightI; U.uCool.value = P.cool; U.uAmbient.value = P.ambient; U.uEnvScale.value = P.envScale; U.uEmissive.value = P.emissive; U.uEnvFloor.value = P.envFloor;
  scene.environment = ENVS[n] || (ENVS[n] = buildEnv(n));
  scene.fog.color.setRGB(...P.fog); scene.fog.density = P.fogD; scene.background.setRGB(...P.fog);
  water.material.uniforms.uFogD.value = P.fogD; water.material.uniforms.uFogC.value.setRGB(...P.fog);
  sun.visible = P.sun > 0; sun.castShadow = P.sun > 0; sun.intensity = P.sun; sunKey = '';
  for (const [, c] of chunks) disposeChunk(c); chunks.clear(); worldCenter = null;
  player.x = 0.5 * S + 0.2; player.z = 0.5 * S + 0.4; player.y = 0; player.vy = 0; player.ground = 0;
  entity.visible = false;
  updateWorldTex(0, 0);
  streamChunks(player.x, player.z, 99);
  water.visible = false;
  if (n === 1) trackSun();
  if (typeof syncLevelButton === 'function') syncLevelButton();
}
let switching = false;
function changeFloor(cx, cz) {                       // walk into the dark doorway at the top of a staircase
  const here = FLOOR + ':' + cx + ',' + cz;
  const to = stairLinks.has(here) ? stairLinks.get(here) : FLOOR + 1;
  if (to < 0 || to > TOP_FLOOR || switching) return;
  switching = true; fadeTarget = 1;
  playSample('land', 0.35, { verb: true }); sfxNoise(1.2, 220, 0.25, 'lowpass', 1.2);
  setTimeout(() => {
    stairLinks.set(here, to); stairLinks.set(to + ':' + cx + ',' + cz, FLOOR);   // linked both ways
    FLOOR = to; pregions.clear();
    for (const [, c] of chunks) disposeChunk(c); chunks.clear(); worldCenter = null; sunKey = '';
    player.x = cx * S + S / 2; player.z = cz * S + HT + 0.42; player.vy = 0;          // top step, back to the doorway
    player.y = player.ground = groundAt(player.x, player.z);
    player.yaw = Math.PI; mb.yaw = player.yaw;
    updateWorldTex(Math.floor(player.x / S), Math.floor(player.z / S)); streamChunks(player.x, player.z, 99); trackSun();
    entity.visible = false; entityTimer = 20;
    fadeTarget = 0; setTimeout(() => { switching = false; }, 900);
  }, 900);
}
function switchLevel(n) {
  if (switching) return; switching = true; fadeTarget = 1;
  playSample('scareT', 0.6, { verb: true, fallback: () => { sfxNoise(1.6, 300, 0.5, 'lowpass', 1.5); sfxTone(180, 60, 1.6, 0.12, 'sine'); } });
  setTimeout(() => { setLevel(n); fadeTarget = 0; switching = false; }, 1500);
}

// ───────────────────────────── entity ──────────────────────────────────────
const entity = new THREE.Group();
{ // flat cut-out silhouette that always turns to face the player
  const t = new THREE.TextureLoader(manager).load('tex/entity.png');
  t.colorSpace = THREE.SRGBColorSpace; t.anisotropy = 4;
  const hgt = 2.05, wid = hgt * 152 / 478;
  const m = new THREE.Mesh(new THREE.PlaneGeometry(wid, hgt), new THREE.MeshBasicMaterial({ map: t, alphaTest: 0.4, side: THREE.DoubleSide }));
  m.position.y = hgt / 2;
  entity.add(m);
  entity.visible = false; scene.add(entity);
}
let entityTimer = 20;   // a short grace period after you arrive

// ───────────────────────────── flashlight ──────────────────────────────────
// the Poolrooms' sun: a directional light whose shadow map is only re-rendered when the player moves on
const SUN_DIR = new THREE.Vector3(0.5, 1.0, 0.33).normalize();
const sun = new THREE.DirectionalLight(new THREE.Color(1.0, 0.93, 0.8), 0);
{ const big = !('ontouchstart' in window || navigator.maxTouchPoints > 0);
  sun.shadow.mapSize.set(big ? 2048 : 1024, big ? 2048 : 1024);
  const c = sun.shadow.camera; c.left = -30; c.right = 30; c.top = 30; c.bottom = -30; c.near = 1; c.far = 100;
  sun.shadow.bias = -0.0004; sun.shadow.normalBias = 0.035; }
sun.visible = false; scene.add(sun, sun.target);
let sunKey = '', chunkDirty = false;
function trackSun() {
  const sx = Math.round(player.x / 6) * 6, sz = Math.round(player.z / 6) * 6, key = sx + ',' + sz;
  if (key === sunKey && !chunkDirty) return;
  sunKey = key; chunkDirty = false;
  sun.target.position.set(sx, 0, sz); sun.position.set(sx + SUN_DIR.x * 50, SUN_DIR.y * 50, sz + SUN_DIR.z * 50);
  sun.target.updateMatrixWorld(); sun.updateMatrixWorld();
  renderer.shadowMap.needsUpdate = true;
}
const flash = new THREE.SpotLight(new THREE.Color(1.0, 0.92, 0.78), 0, 30, 0.42, 0.55, 2);
flash.position.set(0.18, -0.15, 0.1);
flash.target.position.set(0, -0.2, -5);
flash.shadow.mapSize.set(1024, 1024); flash.shadow.bias = -0.0005; flash.shadow.camera.near = 0.1; flash.shadow.camera.far = 30;
camera.add(flash, flash.target);
let flashOn = false;

// ───────────────────────────── post-processing ─────────────────────────────
// Clean full-resolution render with a photographic lens response: lateral chromatic
// aberration on bright edges (blue/purple above, yellow-green below) and light detail sharpening.
const CamShader = {
  uniforms: { tDiffuse: { value: null }, uRes: { value: new THREE.Vector2(1, 1) }, uFade: { value: 0 }, uBlur: { value: new THREE.Vector2() },
    uTime: { value: 0 }, uInsane: { value: 0 }, uMode: { value: 0 }, uFlash: { value: 0 } },
  vertexShader: `varying vec2 vUv; void main(){ vUv = uv; gl_Position = projectionMatrix * modelViewMatrix * vec4(position, 1.0); }`,
  fragmentShader: /* glsl */`
    uniform sampler2D tDiffuse; uniform vec2 uRes; uniform float uFade; uniform vec2 uBlur;
    varying vec2 vUv;
    vec3 tap(vec2 o){ vec3 t = texture2D(tDiffuse, vUv + o / uRes).rgb; return all(equal(t, t)) ? clamp(t, 0.0, 64.0) : vec3(0.0); }  // NaN/Inf-safe
    void main(){
      float px = uRes.y / 540.0;                         // fringe width scales with resolution
      vec3 c = tap(vec2(0.0));
      // channel misregistration, strongest where the image is bright (lamps, highlights)
      vec3 ca = vec3(tap(vec2(0.0, -0.8 * px)).r, tap(vec2(0.0, 0.9 * px)).g, tap(vec2(0.0, -1.9 * px)).b);
      float hl = smoothstep(0.55, 0.95, max(max(ca.r, ca.g), max(ca.b, dot(c, vec3(0.333)))));
      vec3 col = mix(c, ca, 0.35 + 0.65 * hl);
      // subtle unsharp mask for crisp texture detail
      vec3 t1 = tap(vec2(1, 0)), t2 = tap(vec2(-1, 0)), t3 = tap(vec2(0, 1)), t4 = tap(vec2(0, -1));
      vec3 b = (t1 + t2 + t3 + t4) * 0.25;
      vec3 lo = min(min(min(t1, t2), min(t3, t4)), c), hi = max(max(max(t1, t2), max(t3, t4)), c);
      col = clamp(col + (c - b) * 0.3, lo, hi);           // halo-free sharpening (no dark rings)
      // rotational motion blur: only on fast camera turns (uBlur = image motion during the shutter, in uv)
      float bl = length(uBlur);
      if (bl > 0.0005) {
        vec3 acc = vec3(0.0); float wsum = 0.0;
        float jit = fract(sin(dot(gl_FragCoord.xy, vec2(12.9898, 78.233))) * 43758.5453) / 13.0;
        for (int i = 0; i < 14; i++) {
          float t = (float(i) + jit * 13.0 - 0.5) / 13.0 - 0.5;
          float w = 1.0 - abs(t);                           // tent filter: smoother streaks
          acc += texture2D(tDiffuse, vUv + uBlur * t).rgb * w; wsum += w;
        }
        acc /= wsum;
        col = mix(col, acc, smoothstep(0.0005, 0.005, bl));
      }
      float L = dot(col, vec3(0.299, 0.587, 0.114));
      col = mix(vec3(L), col, 1.1);
      gl_FragColor = vec4(clamp(col, 0.0, 1.0) * (1.0 - uFade), 1.0);
    }`,
};

let composer, gtao, liminal, quality = 1;
// Dynamic resolution: the render scale floats between perf.min and perf.max to hold 60 fps.
const IS_TOUCH = 'ontouchstart' in window || navigator.maxTouchPoints > 0;
const perf = { max: Math.min(devicePixelRatio, IS_TOUCH ? 1.5 : 2), min: 1, scale: 1, cap: 9, capT: 0, acc: 0, n: 0, good: 0, warm: 2.0, last: performance.now() };
perf.min = Math.max(0.8, perf.max * 0.66);          // never drop to chunky-pixel territory
perf.scale = perf.max;
function buildComposer() {
  if (composer) composer.dispose?.();
  renderer.setPixelRatio(perf.scale);
  renderer.setSize(innerWidth, innerHeight);
  const w = Math.round(innerWidth * perf.scale), h = Math.round(innerHeight * perf.scale);
  composer = new EffectComposer(renderer, new THREE.WebGLRenderTarget(w, h, { type: THREE.HalfFloatType, samples: 4 }));
  composer.addPass(new RenderPass(scene, camera));
  gtao = null;
  if (!IS_TOUCH) {
    gtao = new GTAOPass(scene, camera, Math.ceil(w / 2), Math.ceil(h / 2));
    const half = gtao.setSize.bind(gtao); gtao.setSize = (ww, hh) => half(Math.ceil(ww / 2), Math.ceil(hh / 2)); // AO at half res
    gtao.updateGtaoMaterial({ radius: 0.5, distanceExponent: 1.5, thickness: 1.2, scale: 1.1, samples: 8, distanceFallOff: 1, screenSpaceRadius: false });
    gtao.updatePdMaterial({ lumaPhi: 10, depthPhi: 2, normalPhi: 3, radius: 5, rings: 2, samples: 8 });
    gtao.blendIntensity = 0.4;
    { const r0 = gtao.render.bind(gtao); gtao.render = (...a) => { for (const m of beamMeshes) m.visible = false; r0(...a); for (const m of beamMeshes) m.visible = true; }; }
    composer.addPass(gtao);
  }
  composer.addPass(new OutputPass());
  liminal = new ShaderPass(CamShader);
  composer.addPass(liminal);
  applyScale(perf.scale);
}
function applyScale(sc) {
  perf.scale = sc;
  renderer.setPixelRatio(sc);
  composer.setPixelRatio(sc); composer.setSize(innerWidth, innerHeight);
  liminal.uniforms.uRes.value.set(Math.round(innerWidth * sc), Math.round(innerHeight * sc));
  if (typeof water !== 'undefined') sizeWater();
}
function perfTick(now) {
  const ft = now - perf.last; perf.last = now;
  if (ft > 250 || document.hidden) return;            // tab switch / hitch: ignore
  if (perf.warm > 0) { perf.warm -= ft / 1000; return; }
  if (perf.capT > 0 && (perf.capT -= ft / 1000) <= 0) perf.cap = 9;
  perf.acc += ft; perf.n++;
  if (perf.acc < 800) return;
  const avg = perf.acc / perf.n; perf.acc = 0; perf.n = 0;
  if (avg > 18.2) {                                    // below ~55 fps: shed cost, cheapest-looking first
    perf.good = 0; perf.capT = 25;
    if (gtao && gtao.enabled) { gtao.enabled = false; perf.cap = perf.scale; return; }
    if (perf.scale > perf.min + 0.01) { perf.cap = perf.scale * 0.99; applyScale(Math.max(perf.min, perf.scale * 0.93)); }
  } else if (avg < 17.3) {                             // holding 60: give quality back
    if (++perf.good < 3) return; perf.good = 0;
    const lim = Math.min(perf.max, perf.cap);
    if (perf.scale < lim - 0.01) applyScale(Math.min(lim, perf.scale * 1.05));
    else if (gtao && !gtao.enabled && perf.cap > 8) gtao.enabled = true;
  } else perf.good = 0;
}
function setQuality(q) {
  quality = q;
  QUALITY.n = 2; QUALITY.r = 7.2; VIEW_R = 2;
  flash.castShadow = true;
  for (const m of patched) m.needsUpdate = true;
  buildComposer();
}

// ───────────────────────────── audio ───────────────────────────────────────
const A = { ctx: null };
function noiseBuffer(ctx, sec, brown) {
  const b = ctx.createBuffer(1, ctx.sampleRate * sec, ctx.sampleRate); const d = b.getChannelData(0); let last = 0;
  for (let i = 0; i < d.length; i++) { const w = Math.random() * 2 - 1; if (brown) { last = (last + 0.02 * w) / 1.02; d[i] = last * 3.5; } else d[i] = w; }
  return b;
}
function initAudio() {
  if (A.ctx) { A.ctx.resume?.(); return; }
  try {
    const ctx = new (window.AudioContext || window.webkitAudioContext)(); A.ctx = ctx;
    const master = ctx.createGain(); master.gain.value = 0.8; master.connect(ctx.destination); A.master = master;
    // fluorescent hum (mains 60Hz + harmonics)
    const humG = ctx.createGain(); humG.gain.value = 0.0; humG.connect(master); A.humG = humG;
    const lp = ctx.createBiquadFilter(); lp.type = 'lowpass'; lp.frequency.value = 900; lp.connect(humG);
    [[60, 'sawtooth', 0.35], [120, 'sine', 0.6], [180, 'sine', 0.18], [240, 'triangle', 0.1]].forEach(([f, t, g]) => {
      const o = ctx.createOscillator(); o.type = t; o.frequency.value = f; const og = ctx.createGain(); og.gain.value = g; o.connect(og); og.connect(lp); o.start();
    });
    // high ballast whine
    const wh = ctx.createOscillator(); wh.frequency.value = 7350; const whg = ctx.createGain(); whg.gain.value = 0.004; wh.connect(whg); whg.connect(humG); wh.start();
    // room tone
    const rt = ctx.createBufferSource(); rt.buffer = noiseBuffer(ctx, 4, true); rt.loop = true;
    const rtf = ctx.createBiquadFilter(); rtf.type = 'lowpass'; rtf.frequency.value = 220; const rtg = ctx.createGain(); rtg.gain.value = 0.09;
    rt.connect(rtf); rtf.connect(rtg); rtg.connect(master); rt.start(); A.rtg = rtg;
    // flicker buzz, spatialised at the nearest flickering tube
    A.white = noiseBuffer(ctx, 2, false);
    const bz = ctx.createBufferSource(); bz.buffer = A.white; bz.loop = true;
    const bzf = ctx.createBiquadFilter(); bzf.type = 'bandpass'; bzf.frequency.value = 2400; bzf.Q.value = 1.2;
    const bzo = ctx.createOscillator(); bzo.type = 'square'; bzo.frequency.value = 120; const bzog = ctx.createGain(); bzog.gain.value = 0.25;
    const buzzG = ctx.createGain(); buzzG.gain.value = 0;
    const pan = ctx.createPanner(); pan.panningModel = 'HRTF'; pan.distanceModel = 'inverse'; pan.refDistance = 1.5; pan.rolloffFactor = 1.4;
    bz.connect(bzf); bzf.connect(buzzG); bzo.connect(bzog); bzog.connect(buzzG); buzzG.connect(pan); pan.connect(master); bz.start(); bzo.start();
    A.buzzG = buzzG; A.pan = pan;
    // tiled-room reverb (synthetic impulse) and distant water lapping
    const ir = ctx.createBuffer(2, ctx.sampleRate * 3, ctx.sampleRate);
    for (let c = 0; c < 2; c++) { const d = ir.getChannelData(c); for (let i = 0; i < d.length; i++) d[i] = (Math.random() * 2 - 1) * Math.pow(1 - i / d.length, 3.2); }
    const rev = ctx.createConvolver(); rev.buffer = ir; const revG = ctx.createGain(); revG.gain.value = 0.12; rev.connect(revG); revG.connect(master);
    A.rev = rev; A.revG = revG;
    const wl = ctx.createBufferSource(); wl.buffer = noiseBuffer(ctx, 4, true); wl.loop = true;
    const wlf = ctx.createBiquadFilter(); wlf.type = 'bandpass'; wlf.frequency.value = 520; wlf.Q.value = 0.6;
    const waterG = ctx.createGain(); waterG.gain.value = 0; wl.connect(wlf); wlf.connect(waterG); waterG.connect(master); waterG.connect(rev); wl.start();
    A.waterG = waterG;
    // recorded audio: Level 0 ambience bed + footstep samples
    A.buf = {}; const ambG = ctx.createGain(); ambG.gain.value = 0; ambG.connect(master); A.ambG = ambG;
    const pend = [];
    const load = (k, url) => { LOAD.aud[1]++; const pr = fetch(url).then(r => { if (!r.ok) throw new Error(r.status); return r.arrayBuffer(); })
      .then(b => new Promise((res, rej) => ctx.decodeAudioData(b, res, rej)))
      .then(buf => { A.buf[k] = buf; LOAD.aud[0]++; if (k === 'amb') { const src = ctx.createBufferSource(); src.buffer = buf; src.loop = true; src.connect(ambG); src.start(); } })
      .catch(err => { LOAD.fails.push({ kind: 'aud', url }); console.warn('audio failed', url, err); })
      .finally(loaderUI); pend.push(pr); };
    load('amb', 'sfx/ambience-level0.mp3');
    for (const k of ['carpet', 'tile', 'wade']) for (const n of [1, 2]) load(k + n, `sfx/step-${k}-${n}.mp3`);
    load('scare1', 'sfx/scare-1.mp3'); load('scare2', 'sfx/scare-2.mp3'); load('scareT', 'sfx/scare-transition.mp3'); load('land', 'sfx/land-bodyfall.mp3');
    Promise.all(pend).then(() => { LOAD.audDone = true; loaderCheck(); });
    // dread drone
    const dG = ctx.createGain(); dG.gain.value = 0; dG.connect(master); A.droneG = dG;
    [43.6, 46.2, 87.9].forEach(f => { const o = ctx.createOscillator(); o.frequency.value = f; o.type = 'sine'; o.connect(dG); o.start(); });
  } catch (e) { A.ctx = null; LOAD.fails.push({ kind: 'aud', url: 'WebAudio unavailable' }); LOAD.audDone = true; loaderCheck(); }
}
function sfxNoise(dur, freq, gain, type = 'lowpass', q = 0.8, x, z) {
  if (!A.ctx) return; const ctx = A.ctx, t = ctx.currentTime;
  const s = ctx.createBufferSource(); s.buffer = A.white; const f = ctx.createBiquadFilter(); f.type = type; f.frequency.value = freq; f.Q.value = q;
  const g = ctx.createGain(); g.gain.setValueAtTime(0, t); g.gain.linearRampToValueAtTime(gain, t + 0.012); g.gain.exponentialRampToValueAtTime(0.0001, t + dur);
  s.connect(f); f.connect(g);
  if (x !== undefined) { const p = ctx.createPanner(); p.panningModel = 'HRTF'; p.refDistance = 2; p.positionX.value = x; p.positionY.value = 1; p.positionZ.value = z; g.connect(p); p.connect(A.master); }
  else g.connect(A.master);
  if (A.rev) g.connect(A.rev);
  s.start(t, Math.random()); s.stop(t + dur + 0.05);
}
// one-shot sample, optionally placed in the world (HRTF) and muffled by distance
function playSample(key, gain, opt = {}) {
  if (!A.ctx || !A.buf || !A.buf[key]) { opt.fallback && opt.fallback(); return false; }
  const ctx = A.ctx, src = ctx.createBufferSource(); src.buffer = A.buf[key];
  if (opt.rate) src.playbackRate.value = opt.rate;
  const g = ctx.createGain(); g.gain.value = gain; let node = src;
  if (opt.lowpass) { const f = ctx.createBiquadFilter(); f.type = 'lowpass'; f.frequency.value = opt.lowpass; src.connect(f); node = f; }
  node.connect(g);
  if (opt.x !== undefined) { const p = ctx.createPanner(); p.panningModel = 'HRTF'; p.distanceModel = 'inverse'; p.refDistance = 4; p.rolloffFactor = 0.6;
    p.positionX.value = opt.x; p.positionY.value = 1.6; p.positionZ.value = opt.z; g.connect(p); p.connect(A.master); if (A.rev) p.connect(A.rev); }
  else { g.connect(A.master); if (A.rev && opt.verb) g.connect(A.rev); }
  src.start(); return true;
}
const scareKey = () => Math.random() < 0.5 ? 'scare1' : 'scare2';
function playStep(kind, loud, fallback) {
  if (!A.ctx) return;
  const buf = A.buf && (A.buf[kind + (Math.random() < 0.5 ? 1 : 2)] || A.buf[kind + 1]);
  if (!buf) { fallback && fallback(); return; }
  const ctx = A.ctx, src = ctx.createBufferSource(); src.buffer = buf;
  src.playbackRate.value = 0.9 + Math.random() * 0.18;                    // no two steps quite alike
  const g = ctx.createGain(); g.gain.value = loud * (0.85 + Math.random() * 0.3);
  let node = src;
  if (kind === 'carpet') { const f = ctx.createBiquadFilter(); f.type = 'lowpass'; f.frequency.value = 1300; f.Q.value = 0.5; src.connect(f); node = f; }  // concrete, muffled by carpet
  node.connect(g); g.connect(A.master); if (A.rev) g.connect(A.rev);
  src.start();
}
function sfxTone(f0, f1, dur, gain, type = 'sine') {
  if (!A.ctx) return; const ctx = A.ctx, t = ctx.currentTime;
  const o = ctx.createOscillator(); o.type = type; o.frequency.setValueAtTime(f0, t); o.frequency.exponentialRampToValueAtTime(f1, t + dur);
  const g = ctx.createGain(); g.gain.setValueAtTime(0, t); g.gain.linearRampToValueAtTime(gain, t + 0.02); g.gain.exponentialRampToValueAtTime(0.0001, t + dur);
  o.connect(g); g.connect(A.master); o.start(t); o.stop(t + dur + 0.05);
}

// ───────────────────────────── player / input ──────────────────────────────
const player = { x: 0.5 * S + 0.2, z: 0.5 * S + 0.4, y: 0, vy: 0, yaw: 0, pitch: 0, vx: 0, vz: 0, stamina: 1, sanity: 1, bob: 0, water: 0, dist: 0, lost: 0, noclip: false };
const keys = {};
let running = false, started = false, locked = false, filterMode = 0, sens = 1, showFps = false;
let fade = 0, fadeTarget = 0, flashFx = 0, respawning = false, startTime = 0, msgTimer = 0;
const touch = { on: 'ontouchstart' in window || navigator.maxTouchPoints > 0, mx: 0, my: 0, stickId: null, lookId: null, lx: 0, ly: 0, run: false };

const $ = id => document.getElementById(id);
function showMsg() {}
function setFilter(m) { filterMode = m; if (liminal) liminal.uniforms.uMode.value = m; }
function startAudio() { initAudio(); A.ctx?.resume?.(); }
addEventListener('pointerdown', startAudio);
addEventListener('touchstart', startAudio, { passive: true });
function jump() { if (running && player.y <= (player.ground || 0) + 0.001) { player.vy = 3.9; sfxNoise(0.1, 500, 0.15, 'lowpass', 0.7); } }
document.addEventListener('pointerlockchange', () => { locked = document.pointerLockElement === renderer.domElement; });
addEventListener('keydown', e => {
  keys[e.code] = true;
  if (e.code === 'Space') { e.preventDefault(); jump(); }
  if (e.code === 'KeyF' && running) toggleFlash();
  if (e.code === 'KeyV') setFilter((filterMode + 1) % 3);
  if (e.code === 'KeyN' && running) player.noclip = !player.noclip;
  if (e.code === 'Digit1' && LEVEL !== 0) switchLevel(0);
  if (e.code === 'Digit2' && LEVEL !== 1) switchLevel(1);
});
addEventListener('keyup', e => keys[e.code] = false);
addEventListener('blur', () => { for (const k in keys) keys[k] = false; });
function look(dx, dy) {
  player.yaw -= dx * 0.0022 * sens; player.pitch -= dy * 0.0022 * sens;
  player.pitch = Math.max(-1.45, Math.min(1.45, player.pitch));
}
let dragging = false;
renderer.domElement.addEventListener('mousedown', () => { dragging = true; if (running && !locked && !touch.on) { try { renderer.domElement.requestPointerLock?.()?.catch?.(() => {}); } catch (e) {} } });
addEventListener('mouseup', () => dragging = false);
addEventListener('mousemove', e => { if (running && (locked || dragging) && !stickMouse) look(e.movementX, e.movementY); });
function toggleFlash() { flashOn = !flashOn; flash.intensity = flashOn ? 38 : 0; renderer.shadowMap.autoUpdate = flashOn; renderer.shadowMap.needsUpdate = true; sfxNoise(0.05, 3000, 0.25, 'highpass'); }

// joystick + jump (mouse and touch)
const stick = $('stick'), knob = stick.querySelector('i');
let stickMouse = false;
function stickMove(cx, cy) {
  const r = stick.getBoundingClientRect(); let dx = (cx - (r.left + r.width / 2)) / 50, dy = (cy - (r.top + r.height / 2)) / 50;
  const l = Math.hypot(dx, dy); if (l > 1) { dx /= l; dy /= l; }
  touch.mx = dx; touch.my = dy; knob.style.transform = `translate(${dx * 38}px,${dy * 38}px)`;
}
function stickEnd() { touch.mx = touch.my = 0; knob.style.transform = ''; }
stick.addEventListener('mousedown', e => { e.stopPropagation(); stickMouse = true; stickMove(e.clientX, e.clientY); });
addEventListener('mousemove', e => { if (stickMouse) stickMove(e.clientX, e.clientY); });
addEventListener('mouseup', () => { if (stickMouse) { stickMouse = false; stickEnd(); } });
$('tJump').addEventListener('mousedown', e => { e.stopPropagation(); jump(); });
$('tJump').addEventListener('touchstart', e => { e.preventDefault(); jump(); }, { passive: false });
// SHIFT: tap to toggle running on/off (lit while on)
{ const b = $('tRun'), toggle = e => { e.preventDefault(); e.stopPropagation(); touch.run = !touch.run; b.classList.toggle('on', touch.run); };
  b.addEventListener('mousedown', toggle);
  b.addEventListener('touchstart', toggle, { passive: false }); }
// level button: go to the Poolrooms / back to Level 0
{ const b = $('tLevel'); const go = e => { e.preventDefault(); e.stopPropagation(); switchLevel(1 - LEVEL); };
  b.addEventListener('mousedown', go); b.addEventListener('touchstart', go, { passive: false }); }
// credits panel
{ const pnl = $('credits'), open = e => { e.preventDefault(); e.stopPropagation(); if (document.pointerLockElement) document.exitPointerLock?.(); pnl.hidden = false; };
  $('tInfo').addEventListener('mousedown', open); $('tInfo').addEventListener('touchstart', open, { passive: false });
  const close = e => { e.stopPropagation(); pnl.hidden = true; };
  $('cClose').addEventListener('click', close);
  pnl.addEventListener('click', e => { if (e.target === pnl) close(e); });
  for (const ev of ['mousedown', 'touchstart']) pnl.addEventListener(ev, e => e.stopPropagation(), { passive: true }); }
function syncLevelButton() { const b = $('tLevel'); if (b) b.textContent = LEVEL === 1 ? 'LEVEL 0' : 'POOLROOMS'; }
if (touch.on) {
  addEventListener('touchstart', e => {
    for (const t of e.changedTouches) {
      if (t.target.closest?.('.tbtn')) continue;
      if (t.target.closest?.('#stick') && touch.stickId === null) { touch.stickId = t.identifier; stickMove(t.clientX, t.clientY); }
      else if (touch.lookId === null && !t.target.closest?.('#stick')) { touch.lookId = t.identifier; touch.lx = t.clientX; touch.ly = t.clientY; }
    }
  }, { passive: true });
  addEventListener('touchmove', e => {
    for (const t of e.changedTouches) {
      if (t.identifier === touch.stickId) stickMove(t.clientX, t.clientY);
      else if (t.identifier === touch.lookId) { look((t.clientX - touch.lx) * 1.6, (t.clientY - touch.ly) * 1.6); touch.lx = t.clientX; touch.ly = t.clientY; }
    }
  }, { passive: true });
  const end = e => { for (const t of e.changedTouches) {
    if (t.identifier === touch.stickId) { touch.stickId = null; stickEnd(); }
    if (t.identifier === touch.lookId) touch.lookId = null; } };
  addEventListener('touchend', end); addEventListener('touchcancel', end);
}

function collide(px, pz) {
  if (player.noclip) return [px, pz];
  const cx = Math.floor(px / S), cz = Math.floor(pz / S); const boxes = [];
  for (let i = -1; i <= 1; i++) for (let j = -1; j <= 1; j++) { cellBoxes(cx + i, cz + j, boxes); specialBoxes(cx + i, cz + j, boxes); }
  for (let it = 0; it < 3; it++) {
    for (const b of boxes) {
      const qx = Math.max(b[0], Math.min(px, b[1])), qz = Math.max(b[2], Math.min(pz, b[3]));
      const dx = px - qx, dz = pz - qz, d2 = dx * dx + dz * dz;
      if (d2 < RADIUS * RADIUS) {
        if (d2 > 1e-8) { const d = Math.sqrt(d2), push = (RADIUS - d) / d; px += dx * push; pz += dz * push; }
        else { // centre inside box: push out along the shallowest axis
          const l = px - b[0], r = b[1] - px, t = pz - b[2], u = b[3] - pz, m = Math.min(l, r, t, u);
          if (m === l) px = b[0] - RADIUS; else if (m === r) px = b[1] + RADIUS; else if (m === t) pz = b[2] - RADIUS; else pz = b[3] + RADIUS;
        }
      }
    }
  }
  return [px, pz];
}

function respawn() {
  respawning = true; fadeTarget = 1;
  sfxTone(220, 30, 2.5, 0.4, 'sawtooth');
  setTimeout(() => {
    const a = Math.random() * Math.PI * 2, r = 300 + Math.random() * 600;
    let x = Math.cos(a) * r, z = Math.sin(a) * r;
    x = (Math.floor(x / S) + 0.5) * S; z = (Math.floor(z / S) + 0.5) * S;
    player.x = x; player.z = z; player.sanity = 0.85; player.lost++;
    for (const [, c] of chunks) disposeChunk(c); chunks.clear(); worldCenter = null;
    streamChunks(player.x, player.z, 99);
    entity.visible = false; fadeTarget = 0; respawning = false;
    showMsg('You woke up somewhere else. It looks the same.', 5);
  }, 2600);
}

// ───────────────────────────── main loop ───────────────────────────────────
const clock = new THREE.Clock();
const mb = { yaw: 0, pitch: 0, v: new THREE.Vector2() };
let waterScanT = 0, scareT = 100 + Math.random() * 80;
let fpsAcc = 0, fpsN = 0, stepSide = 0, lastBuzz = 0, knockT = 6;
const fwd = new THREE.Vector3();
function tick() {
  requestAnimationFrame(tick);
  const dt = Math.min(clock.getDelta(), 0.05);
  const t = clock.elapsedTime;
  U.uTime.value = t;
  if (liminal) { liminal.uniforms.uTime.value = t; }

  if (running) {
    // movement
    let mx = 0, mz = 0;
    if (keys.KeyW || keys.ArrowUp) mz -= 1; if (keys.KeyS || keys.ArrowDown) mz += 1;
    if (keys.KeyA || keys.ArrowLeft) mx -= 1; if (keys.KeyD || keys.ArrowRight) mx += 1;
    if (TEST && !TP.get('still')) mz = -1;
    mx += touch.mx; mz += touch.my;
    const ml = Math.hypot(mx, mz); if (ml > 1) { mx /= ml; mz /= ml; }
    const wantRun = (keys.ShiftLeft || keys.ShiftRight || touch.run) && ml > 0.1;   // no hidden stamina cap
    player.stamina = Math.max(0, Math.min(1, player.stamina + (wantRun ? -0.16 : 0.09) * dt));
    const wading = LEVEL === 1 && player.ground < -0.1;
    const speed = (wantRun ? 4.6 : 2.3) * (player.noclip ? 2.2 : 1) * (wading ? 0.6 : 1);
    const sy = Math.sin(player.yaw), cy = Math.cos(player.yaw);
    const tx = (mx * cy + mz * sy) * speed, tz = (-mx * sy + mz * cy) * speed;
    const acc = 1 - Math.exp(-dt * 10);
    player.vx += (tx - player.vx) * acc; player.vz += (tz - player.vz) * acc;
    const ox = player.x, oz = player.z;
    [player.x, player.z] = collide(player.x + player.vx * dt, player.z + player.vz * dt);
    let gnd = player.noclip ? 0 : groundAt(player.x, player.z);
    if (!player.noclip && gnd - player.y > 0.62) { player.x = ox; player.z = oz; player.vx *= 0.2; player.vz *= 0.2; gnd = groundAt(ox, oz); }
    player.ground = gnd;
    const prevY = player.y;
    player.vy -= 12 * dt; player.y += player.vy * dt;
    if (player.y <= gnd) {
      // walked into higher ground (out of a pool): step up; a landing from a jump falls through to the else-branch
      if (prevY < gnd - 0.03 && player.vy <= 0.5 && prevY > gnd - PD - 0.05) { player.y = Math.min(gnd, player.y + dt * 3.2); player.vy = 0; } // climb the pool step
      else { if (player.vy < -2.5) { if (gnd < -0.1) playStep('wade', 1.5, () => sfxNoise(0.5, 1400, 0.45, 'bandpass', 0.5)); else { const hard = Math.min(1, (-player.vy - 2.5) / 3); playSample('land', 0.45 + 0.4 * hard, { rate: 0.95 + Math.random() * 0.1, verb: LEVEL === 1, lowpass: LEVEL === 0 ? 2600 : undefined, fallback: () => playStep(LEVEL === 1 ? 'tile' : 'carpet', 1.2) }); } } player.y = gnd; player.vy = 0; }
    }
    const moved = Math.hypot(player.x - ox, player.z - oz) * (player.y > gnd + 0.01 ? 0 : 1); player.dist += moved;
    const sp = moved / Math.max(dt, 1e-4);
    const prevBob = player.bob; player.bob += sp * dt * 2.15;
    if (Math.floor(prevBob / Math.PI) !== Math.floor(player.bob / Math.PI) && sp > 0.5) {
      stepSide ^= 1;
      const lv = wantRun ? 1.0 : 0.7;
      if (wading) playStep('wade', lv * 1.1, () => { sfxNoise(0.35, 900 + Math.random() * 900, 0.3, 'bandpass', 0.7); });
      else if (LEVEL === 1) playStep('tile', lv * 0.75, () => sfxNoise(0.09, 1600 + Math.random() * 900, 0.16, 'bandpass', 1.2));
      else playStep('carpet', lv * 0.9, () => sfxNoise(0.16, 380 + Math.random() * 260, 0.22 + (wantRun ? 0.12 : 0), 'lowpass', 0.7));
    }
    if (TEST && !TP.get('still') && !TP.get('norot')) player.yaw += dt * 0.25;
    if (TEST && TP.get('spin')) player.yaw += dt * +TP.get('spin');

    // the dark doorway at the top of Poolrooms stairs: up (or back down) a floor
    if (LEVEL === 1 && !switching) {
      const pcx = Math.floor(player.x / S), pcz = Math.floor(player.z / S), sp = specialAt(pcx, pcz);
      if (sp && sp.t === 'stairs' && player.y > STAIR.top - 0.4) {
        const lx = player.x - pcx * S, d = player.z - (pcz * S + HT);
        if (lx > STAIR.x0 + 0.25 && lx < STAIR.x1 - 0.25 && d < 0.36) changeFloor(pcx, pcz);
      }
    }
    // portals between levels
    if (!switching) {
      const pcx = Math.floor(player.x / S), pcz = Math.floor(player.z / S), [RL, ri] = cellRef(pcx, pcz);
      if (RL.portal === ri && Math.hypot(player.x - (pcx + 0.5) * S, player.z - (pcz + 0.5) * S) < 0.6) switchLevel(1 - LEVEL);
    }
    // water: follow the player; skip the reflection render when no pool is near
    if (LEVEL === 1) {
      water.position.x = Math.round(player.x); water.position.z = Math.round(player.z);
      water.material.uniforms.uTime.value = t;
      water.material.uniforms.uPlayer.value.set(player.x, player.z, wading ? Math.min(1, Math.hypot(player.vx, player.vz) / 1.4) : 0);
      if ((waterScanT -= dt) <= 0) {
        waterScanT = 0.3; let near = false; const pcx = Math.floor(player.x / S), pcz = Math.floor(player.z / S);
        for (let i = -9; i <= 9 && !near; i++) for (let j = -9; j <= 9; j++) if (isPool(pcx + i, pcz + j)) { near = true; break; }
        water.visible = near;
      }
    }
    if (LEVEL === 1) {
      trackSun();
      const sm = sun.shadow.map;
      beamMat.uniforms.uHasShadow.value = sm ? 1 : 0; beamMat.uniforms.uSunDir.value.copy(SUN_DIR);
      if (sm) { beamMat.uniforms.uShadowMap.value = sm.texture; beamMat.uniforms.uShadowMatrix.value = sun.shadow.matrix; }
    }
    // local lighting → sanity / audio
    const ll = localLight(player.x, player.z, t);
    const lit = Math.min(1, ll * 0.35);
    let drain = 0.0035 + (1 - lit) * 0.022 - (flashOn ? 0.006 : 0);
    if (player.noclip) drain = -0.01;
    player.sanity = Math.max(0, Math.min(1, player.sanity - drain * dt));
    // sanity bottoming out no longer teleports you; it only makes things stranger

    // pickups
    for (const [, c] of chunks) for (let i = c.items.length - 1; i >= 0; i--) {
      const g = c.items[i]; const d = Math.hypot(g.position.x - player.x, g.position.z - player.z);
      g.rotation.y += dt * 0.4;
      if (d < 0.85) {
        collected.add(g.userData.key); c.group.remove(g); c.items.splice(i, 1);
        player.water++; player.sanity = Math.min(1, player.sanity + 0.45); flashFx = 0.25;
        sfxTone(660, 1320, 0.6, 0.18); sfxTone(990, 1980, 0.8, 0.08);
        showMsg(['Almond water. It tastes like vanilla and childhood.', 'Almond water. Your head clears a little.', 'Almond water. Someone left this here for you.'][player.water % 3], 3.5);
      }
    }

    // entity
    const insane = 1 - player.sanity;
    entityTimer -= dt;
    if (!entity.visible && entityTimer <= 0 && Math.random() < dt * (0.02 + 0.05 * insane)) {   // can show up at any sanity
      camera.getWorldDirection(fwd); fwd.y = 0; fwd.normalize();
      let best = null;
      for (let d = 10; d <= 34; d += 1.5) {
        const ex = player.x + fwd.x * d, ez = player.z + fwd.z * d;
        const cx = (Math.floor(ex / S) + 0.5) * S, cz = (Math.floor(ez / S) + 0.5) * S;
        if (visJS(player.x, player.z, cx, cz) > 0.5) best = [cx, cz]; else break;
      }
      if (best && Math.hypot(best[0] - player.x, best[1] - player.z) < 18) best = null;   // only ever far away
      if (best) { entity.position.set(best[0], groundAt(best[0], best[1]), best[1]); entity.visible = true; entity.userData.seen = false; entity.userData.unseenT = 0; }
    }
    if (entity.visible) {
      entity.rotation.set(0, player.yaw, 0);           // sprite: always square-on to the camera
      const ex = entity.position.x, ez = entity.position.z, d = Math.hypot(ex - player.x, ez - player.z);
      // is it actually on screen, with nothing in the way?
      camera.getWorldDirection(fwd);
      const tx = (ex - player.x) / d, tz = (ez - player.z) / d, fl = Math.hypot(fwd.x, fwd.z) || 1;
      const ang = Math.acos(Math.max(-1, Math.min(1, (fwd.x * tx + fwd.z * tz) / fl)));
      const halfH = Math.atan(Math.tan(THREE.MathUtils.degToRad(camera.fov / 2)) * camera.aspect);
      const onScreen = ang < halfH * 0.92 && Math.abs(player.pitch) < 1.1 && visJS(player.x, player.z, ex, ez) > 0.5;
      const U2 = entity.userData;
      if (!U2.seen) {
        if (onScreen) {                                 // first sighting: start its clock from here
          U2.seen = true; U2.d0 = d; entityTimer = 8 + Math.random() * 7;
          playSample(scareKey(), 0.9, { x: ex, z: ez, fallback: () => sfxTone(80, 50, 3.0, 0.12, 'sawtooth') });
        } else if ((U2.unseenT += dt) > 30 || d < 8) {  // never noticed: leave quietly
          entity.visible = false; entityTimer = 10 + Math.random() * 15;
        }
      } else {
        const close = d < U2.d0 - 3;                    // a few steps towards it and it's gone
        if (close || entityTimer <= 0) {
          entity.visible = false; entityTimer = 12 + Math.random() * 20;
          if (close) playSample('scareT', 0.75, { verb: true, fallback: () => { sfxNoise(0.9, 160, 0.6, 'lowpass', 3); sfxTone(900, 60, 0.7, 0.15, 'square'); } });
        }
      }
    }
    if ((scareT -= dt) < 0) {                        // now and then, something far away in the halls
      scareT = 120 + Math.random() * 120;
      const a = Math.random() * Math.PI * 2, r = 14 + Math.random() * 10;
      playSample(scareKey(), 0.35, { x: player.x + Math.cos(a) * r, z: player.z + Math.sin(a) * r, lowpass: 1500, rate: 0.85 + Math.random() * 0.2 });
    }
    knockT -= dt;
    if (knockT < 0) { // distant knocks and footsteps that aren't yours
      knockT = 8 + Math.random() * 25 * (0.4 + player.sanity);
      const a = Math.random() * 6.28, r = 8 + Math.random() * 14;
      const n = 1 + Math.floor(Math.random() * 3);
      for (let i = 0; i < n; i++) setTimeout(() => sfxNoise(0.35, 140, 0.45 * insane + 0.08, 'lowpass', 4, player.x + Math.cos(a) * r, player.z + Math.sin(a) * r), i * 380);
    }

    // audio levels
    if (A.ctx) {
      const at = A.ctx.currentTime;
      const bed = !!(A.buf && A.buf.amb);
      A.humG.gain.setTargetAtTime((0.012 + 0.05 * lit) * (LEVEL === 0 ? (bed ? 0.25 : 1) : 0.1), at, 0.2);
      if (A.ambG) A.ambG.gain.setTargetAtTime(LEVEL === 0 ? 3.6 : 0, at, 0.6);
      if (A.rtg) A.rtg.gain.setTargetAtTime(LEVEL === 0 && bed ? 0.03 : 0.09, at, 0.6);
      if (A.waterG) { A.waterG.gain.setTargetAtTime(LEVEL === 1 ? 0.05 + 0.04 * Math.sin(t * 0.7) * Math.sin(t * 0.23) : 0, at, 0.4); A.revG.gain.setTargetAtTime(LEVEL === 1 ? 0.55 : 0.12, at, 0.5); }
      A.droneG.gain.setTargetAtTime(Math.max(0, insane - 0.3) * 0.25, at, 0.5);
      const L = A.ctx.listener; const sy2 = Math.sin(player.yaw), cy2 = Math.cos(player.yaw);
      if (L.positionX) { L.positionX.value = player.x; L.positionY.value = EYE; L.positionZ.value = player.z;
        L.forwardX.value = -sy2; L.forwardY.value = 0; L.forwardZ.value = -cy2; L.upX.value = 0; L.upY.value = 1; L.upZ.value = 0; }
      if (t - lastBuzz > 0.25) { // find nearest flickering tube
        lastBuzz = t; let best = null, bd = 1e9; const pcx = Math.floor(player.x / S), pcz = Math.floor(player.z / S);
        for (let i = -3; i <= 3; i++) for (let j = -3; j <= 3; j++) { const L2 = lightState(pcx + i, pcz + j); if (L2.s !== 2) continue;
          const d = i * i + j * j; if (d < bd) { bd = d; best = [pcx + i, pcz + j, L2.ph]; } }
        A.buzz = best;
        if (best) { A.pan.positionX.value = (best[0] + 0.5) * S; A.pan.positionY.value = H; A.pan.positionZ.value = (best[1] + 0.5) * S; }
      }
      const fv = A.buzz ? flicker(t, A.buzz[2] / 255 * 6.2831853) : 0;
      A.buzzG.gain.setTargetAtTime(A.buzz ? (fv < 0.9 ? 0.35 : 0.04) : 0, at, 0.01);
    }

  }

  // camera
  const moveAmt = Math.min(1, Math.hypot(player.vx, player.vz) / 2.3);
  camera.position.set(player.x + Math.cos(player.bob) * 0.025 * moveAmt * Math.cos(player.yaw), EYE + player.y + Math.abs(Math.sin(player.bob)) * 0.045 * moveAmt - 0.02, player.z - Math.cos(player.bob) * 0.025 * moveAmt * Math.sin(player.yaw));
  camera.rotation.set(player.pitch, player.yaw, Math.sin(player.bob) * 0.006 * moveAmt, 'YXZ');

  updateWorldTex(Math.floor(player.x / S), Math.floor(player.z / S));
  streamChunks(player.x, player.z, 1);

  fade += (fadeTarget - fade) * (1 - Math.exp(-dt * 2.5)); flashFx *= Math.exp(-dt * 3);
  if (liminal) { liminal.uniforms.uFade.value = fade; }
  // motion blur vector from camera angular velocity (shutter ≈ 1/50 s, dead-zone for normal looking)
  {
    let dy = player.yaw - mb.yaw; dy = Math.atan2(Math.sin(dy), Math.cos(dy));
    const dp = player.pitch - mb.pitch; mb.yaw = player.yaw; mb.pitch = player.pitch;
    const vf = THREE.MathUtils.degToRad(camera.fov), hf = 2 * Math.atan(Math.tan(vf / 2) * camera.aspect);
    const k = (1 / 50) / Math.max(dt, 1 / 240);
    let bx = dy * k / hf, by = -dp * k / vf;
    const m = Math.hypot(bx, by), dead = 0.012, maxL = 0.07;
    if (m > dead) { const sc = Math.min(m - dead, maxL) / m; bx *= sc; by *= sc; } else { bx = 0; by = 0; }
    const a = 1 - Math.exp(-dt * 30);
    mb.v.x += (bx - mb.v.x) * a; mb.v.y += (by - mb.v.y) * a;
    if (Math.hypot(mb.v.x, mb.v.y) < 0.0004) mb.v.set(0, 0);
    liminal.uniforms.uBlur.value.copy(mb.v);
  }
  composer.render(dt);
  perfTick(performance.now());

  fpsAcc += dt; fpsN++;
}

addEventListener('resize', () => {
  camera.aspect = innerWidth / innerHeight; camera.updateProjectionMatrix();
  buildComposer();
});

// ───────────────────────────── boot ────────────────────────────────────────
setQuality(quality);
if (location.hash === '#poolrooms' || (TEST && TP.get('lvl') === '1')) setLevel(1);
updateWorldTex(0, 0);
streamChunks(player.x, player.z, 99);
player.yaw = Math.PI * 0.25;
if (TEST && TP.get('x')) { player.x = +TP.get('x'); player.z = +TP.get('z'); player.yaw = +(TP.get('yaw') ?? 0); for (const [, c] of chunks) disposeChunk(c); chunks.clear(); streamChunks(player.x, player.z, 99); }
mb.yaw = player.yaw; mb.pitch = player.pitch;
LOAD.world = true; loaderUI();
initAudio();                                      // decodes sounds now; playback starts on the ENTER tap
(renderer.compileAsync ? renderer.compileAsync(scene, camera) : Promise.resolve(renderer.compile(scene, camera)))
  .catch(() => {}).then(() => { LOAD.shaders = true; loaderCheck(); });
setTimeout(() => {                                // never hang forever: after 25 s, let the player in regardless
  if (LOAD.finished) return;
  if (!LOAD.texDone) { LOAD.texDone = true; LOAD.fails.push({ kind: 'tex', url: 'timeout' }); }
  if (!LOAD.audDone) { LOAD.audDone = true; LOAD.fails.push({ kind: 'aud', url: 'timeout' }); }
  LOAD.shaders = true; loaderCheck();
}, 25000);
function enterGame() {
  const L = document.getElementById('loader');
  initAudio(); A.ctx?.resume?.();
  if (A.ambG && A.ctx) { const at = A.ctx.currentTime; A.ambG.gain.cancelScheduledValues(at); A.ambG.gain.setValueAtTime(0, at); A.ambG.gain.linearRampToValueAtTime(3.6, at + 1.8); }
  L.classList.add('finishing');                   // "FINISHED" while the ambience swells in
  setTimeout(() => {
    running = true; started = true; startTime = performance.now(); clock.getDelta();
    L.classList.add('out'); setTimeout(() => L.remove(), 1300);
  }, 2200);
}
if (TEST) { running = true; started = true; startTime = performance.now(); document.getElementById('loader')?.remove(); }
if (TEST) { const sp = new URLSearchParams(location.search); setQuality(+(sp.get('q') ?? 1)); setFilter(+(sp.get('f') ?? 0)); player.pitch = +(sp.get('p') ?? 0); if (sp.get('flash')) toggleFlash(); if (sp.get('s')) player.sanity = +sp.get('s'); if (sp.get('noao') && gtao) gtao.enabled = false; if (sp.get('ent')) setTimeout(() => { const d = +sp.get('ent'); entity.position.set(player.x - Math.sin(player.yaw) * d, 0, player.z - Math.cos(player.yaw) * d); entity.position.y = groundAt(entity.position.x, entity.position.z); entity.userData.d0 = d; entity.userData.seen = false; entity.userData.unseenT = -999; entity.visible = true; }, 400); }
tick();
