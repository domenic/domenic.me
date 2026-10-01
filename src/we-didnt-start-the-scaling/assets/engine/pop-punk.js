// ---- src/core.js ----
// core.js: canvas, time, randomness, easing, camera, shot registry, frame compositor.
// Everything a shot draws must be a pure function of song time `t` (frames render out of order, in parallel).

// The frame: 1920×1080, or 1080×1920 in the vertical video (VERT: self.VERTICAL, which the page sets before the engine's scripts run,
// or ?vertical in a studio page). W and H are the frame's; landscape() lends code written for the 1920×1080 frame a 16:9 one.
const VERT = !!self.VERTICAL || (typeof location !== 'undefined' && new URLSearchParams(location.search).has('vertical'));
let W = VERT ? 1080 : 1920, H = VERT ? 1920 : 1080;
const TAU = Math.PI * 2;
// In a page the canvas is #out; in a Web Worker the host sets self.OUT_CANVAS (an OffscreenCanvas) before loading the engine.
const HAS_DOM = typeof document !== 'undefined';
const canvas = HAS_DOM ? document.getElementById('out') : self.OUT_CANVAS;
// (a style that draws its frames with WebGL2 on the canvas itself takes that context before this script runs, as self.CANVAS_GL:
// then `ctx` is a 1×1 stand-in, which the frame code every style shares (the paper, the error bar) draws on harmlessly)
let ctx = self.CANVAS_GL ? makeCanvas(1, 1).getContext('2d') : canvas.getContext('2d');
// Scratch canvases for caches: DOM canvases in pages, OffscreenCanvas in workers.
function makeCanvas(w, h) {
  if (!HAS_DOM) return new OffscreenCanvas(w, h);
  const c = document.createElement('canvas'); c.width = w; c.height = h; return c;
}
// Render scale: the scene is authored in logical units, W × H of them; the canvas holds W·RS × H·RS pixels.
// Set with ?scale= (studio/renderer) or setRenderScale() (embedding pages). A cache drawn at render scale adds a function that empties
// it to SCALE_HOOKS. (Not a `typeof` check on the cache from here: the site runs a style's scripts as one, where a later script's
// `const` isn't yet initialized while this one runs, and even `typeof` on it throws.)
let RS = +(self.RENDER_SCALE || new URLSearchParams(location.search).get('scale') || 1);
const SCALE_HOOKS = [];
function setRenderScale(s) {
  RS = s; canvas.width = Math.round(W * RS); canvas.height = Math.round(H * RS);
  for (const f of SCALE_HOOKS) f();
}
setRenderScale(RS);

// ---------- math ----------
const clamp = (v, a = 0, b = 1) => Math.max(a, Math.min(b, v));
const lerp = (a, b, k) => a + (b - a) * k;
const frac = v => v - Math.floor(v);
const seg = (t, a, b) => clamp((t - a) / (b - a));
const ease = k => (k = clamp(k), k * k * (3 - 2 * k));
const easeIn = k => (k = clamp(k), k * k * k);
const easeOut = k => (k = clamp(k), 1 - (1 - k) ** 3);
const backOut = (k, s = 1.8) => (k = clamp(k) - 1, 1 + (s + 1) * k ** 3 + s * k ** 2);
const elasticOut = k => (k = clamp(k), k === 0 || k === 1 ? k : 2 ** (-10 * k) * Math.sin((k * 10 - .75) * TAU / 3) + 1);
// Keyframes: kf(t, [[t0, v0], [t1, v1], ...], easeFn). Values may be numbers or arrays.
function kf(t, keys, fn = ease) {
  if (t <= keys[0][0]) return keys[0][1];
  for (let i = 1; i < keys.length; i++) {
    const [t1, v1] = keys[i];
    if (t <= t1) {
      const [t0, v0] = keys[i - 1], k = fn((t - t0) / (t1 - t0 || 1));
      return Array.isArray(v0) ? v0.map((a, j) => lerp(a, v1[j], k)) : lerp(v0, v1, k);
    }
  }
  return keys[keys.length - 1][1];
}
const wob = (t, f = 1, ph = 0) => Math.sin((t * f + ph) * TAU);

// ---------- deterministic randomness ----------
// hash(n) → [0,1). Use for stable per-object variation.
function hash(n) {
  let x = Math.imul((n * 1000003) ^ 0x9E3779B9, 0x85EBCA6B);
  x ^= x >>> 13; x = Math.imul(x, 0xC2B2AE35); x ^= x >>> 16;
  return (x >>> 0) / 4294967296;
}
const hash2 = (a, b) => hash(a * 7919 + b * 104729 + 17);
const hstr = s => { let h = 5381; for (const c of String(s)) h = (Math.imul(h, 33) ^ c.charCodeAt(0)) | 0; return hash(h); };
// "Boil": hand-made wobble that re-rolls 12×/s like stop-motion. jit(a) → [-a, a].
const BOIL_FPS = 12;
let _boil = 0, _jitN = 0;
const boilFrame = t => Math.floor(t * BOIL_FPS + 1e-6);
function jit(a = 1) { return (hash2(_boil, _jitN++) * 2 - 1) * a; }

// ---------- palette (risograph inks on cream stock) ----------
const PAL = {
  paper: '#F2EAD8', paper2: '#E9DFC8', kraft: '#C9A77C', ink: '#1C1A1F', grey: '#6B6770',
  pink: '#FF4FA3', blue: '#2C6FCF', yellow: '#FFD83A', orange: '#D97757', clawd: '#D97757', clawdDk: '#A5533A', clawdLt: '#EDA07F',
  red: '#E8412F', green: '#2FA86A', teal: '#1FA6A0', purple: '#7B4FC9', mint: '#A8E6CF', sky: '#9FD3F2', cream: '#FFF8E7',
  newsprint: '#E8E4D8', white: '#FFFDF6', night: '#1E1B2E', gold: '#E8B230',
};
function mixCol(a, b, k) {
  const p = h => [1, 3, 5].map(i => parseInt(h.slice(i, i + 2), 16));
  const [r1, g1, b1] = p(a), [r2, g2, b2] = p(b);
  const c = v => Math.round(v).toString(16).padStart(2, '0');
  return '#' + c(lerp(r1, r2, k)) + c(lerp(g1, g2, k)) + c(lerp(b1, b2, k));
}
const alpha = (hex, a) => hex + Math.round(clamp(a) * 255).toString(16).padStart(2, '0');

// ---------- timing: beat grid (filled from TIMING) ----------
let BPM = 150, BEAT0 = 0;
const beatLen = () => 60 / BPM;
const bpOf = t => (t - BEAT0) / beatLen();          // beat position (float)
const beatN = t => Math.floor(bpOf(t));
const barOf = t => bpOf(t) / 4;
const pulse = (t, k = 6) => Math.exp(-frac(bpOf(t)) * k);       // 1 on each beat, decays
const pulse2 = (t, k = 6) => Math.exp(-frac(bpOf(t) * 2) * k);  // eighths
const onBeat = (t, n) => BEAT0 + n * beatLen();                   // time of beat n

// ---------- camera ----------
// camBegin(cx, cy, zoom, rot): world point (cx, cy) lands at screen centre.
let _camDepth = 0;
function camBegin(cx = W / 2, cy = H / 2, zoom = 1, rot = 0) {
  ctx.save(); _camDepth++;
  ctx.translate(W / 2, H / 2); ctx.rotate(rot); ctx.scale(zoom, zoom); ctx.translate(-cx, -cy);
}
function camEnd() { if (_camDepth > 0) { ctx.restore(); _camDepth--; } }
function shakeXY(t, amt = 10, f = 24) { const n = Math.floor(t * f); return [(hash2(n, 1) - .5) * 2 * amt, (hash2(n, 2) - .5) * 2 * amt]; }

// ---------- shot registry ----------
// Segments come from timeline.js (SEGS): contiguous windows covering the whole song, each keyed like 'intro', 'V1.1'…'V1.16', 'C1', 'V2.1', …, 'C4', 'outro'.
const SHOTS = {};
// line('V2', 5, fn): the shot for verse 2, line 5. fn(p, lt, dur, t, seg) where p = 0..1 progress through the window, lt = time since window start.
function line(verse, n, fn) { SHOTS[`${verse}.${n}`] = fn; }
// section('C1', fn): the shot for a whole section window (intro, choruses, outro).
function section(key, fn) { SHOTS[key] = fn; }
// The vertical video's shots, composed for its 1080×1920 frame: vshot('V2.5', fn) or vshot('C1', fn), keyed by segment like line()'s
// and section()'s. A segment without one draws its horizontal shot through landscape() (a stand-in while a style's vertical video is
// being made).
const VSHOTS = {};
function vshot(key, fn) { VSHOTS[key] = fn; }
// landscape(fn, cx, cy, zoom): draws fn(), code written for the 1920×1080 frame (W and H are 1920 and 1080 while it runs), with its
// point (cx, cy) at the middle of the frame, scaled by zoom (by default, enough for its 1080 height to fill the vertical frame's 1920).
function landscape(fn, cx = 960, cy = 540, zoom = 1920 / 1080) {
  const w = W, h = H;
  ctx.save(); ctx.translate(w / 2, h / 2); ctx.scale(zoom, zoom); ctx.translate(-cx, -cy);
  W = 1920; H = 1080;
  try { return fn(); } finally { W = w; H = h; ctx.restore(); }
}
const shotAt = key => VERT ? VSHOTS[key] ?? (SHOTS[key] && ((...a) => landscape(() => SHOTS[key](...a)))) : SHOTS[key];

// ---------- per-frame state ----------
let T = 0;           // current song time
const OVERLAYS = []; // functions run after the shot (caption, stamp, grain…), registered by timeline.js

function renderFrame(t) {
  T = t; _boil = boilFrame(t); _jitN = 0; _camDepth = 0;
  ctx.setTransform(RS, 0, 0, RS, 0, 0);
  ctx.globalAlpha = 1; ctx.globalCompositeOperation = 'source-over';
  ctx.fillStyle = PAL.paper; ctx.fillRect(0, 0, W, H);
  const s = segAt(t);
  const fn = s && shotAt(s.key);
  ctx.save();
  try {
    if (fn) fn(clamp((t - s.start) / (s.end - s.start)), t - s.start, s.end - s.start, t, s);
    else placeholder(t, s);
  } catch (e) {
    console.error(`shot ${s && s.key} @ ${t.toFixed(2)}: ${e.stack || e}`);
    ctx.setTransform(RS, 0, 0, RS, 0, 0); ctx.fillStyle = '#f0f'; ctx.fillRect(0, 0, W, 60);
  }
  while (_camDepth > 0) camEnd();
  ctx.restore();
  ctx.setTransform(RS, 0, 0, RS, 0, 0); ctx.globalAlpha = 1; ctx.globalCompositeOperation = 'source-over';
  for (const o of OVERLAYS) { ctx.save(); o(t, s); ctx.restore(); }
}

function placeholder(t, s) {
  ctx.fillStyle = PAL.paper2; ctx.fillRect(0, 0, W, H);
  ctx.fillStyle = PAL.ink; ctx.font = '60px Anton'; ctx.textAlign = 'center';
  ctx.fillText(s ? `${s.key}: ${s.text || ''}` : 'no segment', W / 2, H / 2);
}

;
// ---- src/zine.js ----
// zine.js: the drawing vocabulary of a xeroxed/risograph punk zine.
// Cut-paper scraps with drop shadows, halftone dots, misregistered ink, marker lines, ransom-note letters,
// rubber stamps, label-maker tape, newspaper clippings, stickers, speech bubbles.

// ---------- geometry ----------
const rectPts = (x, y, w, h) => [[x, y], [x + w, y], [x + w, y + h], [x, y + h]];
const ctrRect = (cx, cy, w, h) => rectPts(cx - w / 2, cy - h / 2, w, h);
function ellPts(cx, cy, rx, ry = rx, n = 40, rot = 0) {
  const out = [];
  for (let i = 0; i < n; i++) { const a = i / n * TAU + rot; out.push([cx + Math.cos(a) * rx, cy + Math.sin(a) * ry]); }
  return out;
}
function rrPts(x, y, w, h, r = 20, n = 6) {
  r = Math.min(r, w / 2, h / 2); const out = [];
  const c = [[x + w - r, y + r, -TAU / 4], [x + w - r, y + h - r, 0], [x + r, y + h - r, TAU / 4], [x + r, y + r, TAU / 2]];
  for (const [cx, cy, a0] of c) for (let i = 0; i <= n; i++) { const a = a0 + i / n * TAU / 4; out.push([cx + Math.cos(a) * r, cy + Math.sin(a) * r]); }
  return out;
}
function starPts(cx, cy, r, inner = .5, n = 5, rot = -TAU / 4) {
  const out = [];
  for (let i = 0; i < n * 2; i++) { const a = rot + i / (n * 2) * TAU, rr = i % 2 ? r * inner : r; out.push([cx + Math.cos(a) * rr, cy + Math.sin(a) * rr]); }
  return out;
}
const burstPts = (cx, cy, r, n = 14, inner = .72, rot = 0) => starPts(cx, cy, r, inner, n, rot);
function heartPts(cx, cy, r, n = 48) {
  const out = [];
  for (let i = 0; i < n; i++) {
    const a = i / n * TAU, x = 16 * Math.sin(a) ** 3, y = 13 * Math.cos(a) - 5 * Math.cos(2 * a) - 2 * Math.cos(3 * a) - Math.cos(4 * a);
    out.push([cx + x * r / 16, cy - y * r / 16]);
  }
  return out;
}
const xform = (pts, dx = 0, dy = 0, rot = 0, s = 1, ox = 0, oy = 0) => pts.map(([x, y]) => {
  const X = (x - ox) * s, Y = (y - oy) * s, c = Math.cos(rot), n = Math.sin(rot);
  return [ox + X * c - Y * n + dx, oy + X * n + Y * c + dy];
});
function bbox(pts) {
  let x0 = Infinity, y0 = Infinity, x1 = -Infinity, y1 = -Infinity;
  for (const [x, y] of pts) { x0 = Math.min(x0, x); y0 = Math.min(y0, y); x1 = Math.max(x1, x); y1 = Math.max(y1, y); }
  return { x: x0, y: y0, w: x1 - x0, h: y1 - y0, cx: (x0 + x1) / 2, cy: (y0 + y1) / 2 };
}

// Subdivide edges and displace them: torn/cut paper. Stable per `seed`; if `boil`, re-rolls 12×/s.
function roughen(pts, amt = 2.5, step = 16, seed = 1, boil = true, close = true) {
  if (amt <= 0) return pts;
  const out = [], n = pts.length, s0 = seed * 131 + (boil ? _boil * 7 : 0);
  let k = 0;
  for (let i = 0; i < (close ? n : n - 1); i++) {
    const [x0, y0] = pts[i], [x1, y1] = pts[(i + 1) % n];
    const len = Math.hypot(x1 - x0, y1 - y0), m = Math.max(1, Math.round(len / step));
    for (let j = 0; j < m; j++) {
      const f = j / m;
      out.push([lerp(x0, x1, f) + (hash2(s0, k) * 2 - 1) * amt, lerp(y0, y1, f) + (hash2(s0, k + 999) * 2 - 1) * amt]);
      k++;
    }
  }
  if (!close) out.push(pts[n - 1]);
  return out;
}

function tracePath(pts, close = true) {
  ctx.beginPath();
  for (let i = 0; i < pts.length; i++) i ? ctx.lineTo(pts[i][0], pts[i][1]) : ctx.moveTo(pts[i][0], pts[i][1]);
  if (close) ctx.closePath();
}

// ---------- halftone ----------
const _patCache = new Map();
SCALE_HOOKS.push(() => _patCache.clear());
function halftonePattern(color, cell = 10, dot = .38, angle = 15) {
  const key = `${color}|${cell}|${dot}|${angle}`;
  let p = _patCache.get(key);
  if (!p) {
    // the tile is drawn at render scale, then mapped back to `cell` logical units
    const px = Math.max(2, Math.round(cell * RS)), c = makeCanvas(px, px);
    const g = c.getContext('2d'); g.fillStyle = color;
    g.beginPath(); g.arc(px / 2, px / 2, px * dot, 0, TAU); g.fill();
    p = ctx.createPattern(c, 'repeat');
    p.setTransform(new DOMMatrix().rotateSelf(angle).scaleSelf(cell / px));
    _patCache.set(key, p);
  }
  return p;
}
// Fill a point-list shape with halftone dots.
function halftone(pts, color = PAL.ink, o = {}) {
  ctx.save();
  ctx.globalAlpha *= o.op ?? 1;
  if (o.multiply !== false) ctx.globalCompositeOperation = 'multiply';
  ctx.fillStyle = halftonePattern(color, o.cell ?? 10, o.dot ?? .38, o.angle ?? 15);
  tracePath(pts); ctx.fill();
  ctx.restore();
}
// Halftone shading that fades across a shape: darker toward (dx, dy) direction. Cheap: three bands.
function halftoneShade(pts, color = PAL.ink, o = {}) {
  const b = bbox(pts), dir = o.dir ?? [1, 1], cell = o.cell ?? 9;
  ctx.save(); tracePath(pts); ctx.clip();
  ctx.globalCompositeOperation = 'multiply';
  const steps = [[.55, .22], [.72, .32], [.86, .42]];
  for (const [edge, dot] of steps) {
    ctx.fillStyle = halftonePattern(color, cell, dot, o.angle ?? 20);
    ctx.globalAlpha = o.op ?? .5;
    ctx.beginPath();
    // half-plane beyond `edge` along dir
    const L = Math.hypot(b.w, b.h), ux = dir[0] / Math.hypot(...dir), uy = dir[1] / Math.hypot(...dir);
    const px = b.cx + ux * L * (edge - .5), py = b.cy + uy * L * (edge - .5);
    ctx.moveTo(px - uy * L, py + ux * L); ctx.lineTo(px + uy * L, py - ux * L);
    ctx.lineTo(px + uy * L + ux * L, py - ux * L + uy * L); ctx.lineTo(px - uy * L + ux * L, py + ux * L + uy * L);
    ctx.fill();
  }
  ctx.restore();
}

// ---------- cut paper ----------
// scrap(pts, colour, o): a piece of cut paper. Options:
//   torn (edge roughness px, default 2), seed, boil (default true), shadow (true | [dx, dy]), shadowCol,
//   ink (outline colour; default none), sw (outline width), tone ({color, cell, dot, angle, op}) halftone overlay,
//   shade (halftone shading colour, or true for ink), shadeDir, op (alpha).
function scrap(pts, color, o = {}) {
  const seed = o.seed ?? 1, P = roughen(pts, o.torn ?? 2, o.step ?? 16, seed, o.boil ?? true);
  ctx.save();
  if (o.op !== undefined) ctx.globalAlpha *= o.op;
  if (o.shadow !== false) {
    const [dx, dy] = Array.isArray(o.shadow) ? o.shadow : [6, 8];
    ctx.save(); ctx.translate(dx, dy); ctx.fillStyle = o.shadowCol ?? 'rgb(28 26 31 / .32)';
    tracePath(P); ctx.fill(); ctx.restore();
  }
  ctx.fillStyle = color; tracePath(P); ctx.fill();
  if (o.tone) halftone(P, o.tone.color ?? PAL.ink, o.tone);
  if (o.shade) halftoneShade(P, o.shade === true ? PAL.ink : o.shade, { dir: o.shadeDir, op: o.shadeOp ?? .35 });
  if (o.ink) { ctx.strokeStyle = o.ink; ctx.lineWidth = o.sw ?? 3; ctx.lineJoin = 'round'; tracePath(P); ctx.stroke(); }
  ctx.restore();
  return P;
}
// Convenience: rectangular scrap centred at (cx, cy), rotated.
function card(cx, cy, w, h, color, rot = 0, o = {}) {
  return scrap(xform(ctrRect(cx, cy, w, h), 0, 0, rot, 1, cx, cy), color, o);
}
// Misregistered two-ink print of a shape (riso look). fn(colour) must draw the shape; it's called twice, offset.
function misreg(fn, c1 = PAL.pink, c2 = PAL.blue, d = 5) {
  ctx.save(); ctx.globalCompositeOperation = 'multiply';
  ctx.save(); ctx.translate(-d, -d * .6); fn(c1); ctx.restore();
  ctx.save(); ctx.translate(d, d * .6); fn(c2); ctx.restore();
  ctx.restore();
}

// ---------- marker lines ----------
// marker(pts, colour, width, o): felt-tip line through points. o.close, o.rough (jitter px), o.alpha, o.seed.
function marker(pts, color = PAL.ink, w = 6, o = {}) {
  const P = o.rough === 0 ? pts : roughen(pts, o.rough ?? 1.5, o.step ?? 40, o.seed ?? 3, true, !!o.close);
  ctx.save();
  ctx.strokeStyle = color; ctx.lineWidth = w; ctx.lineCap = 'round'; ctx.lineJoin = 'round';
  ctx.globalAlpha *= o.alpha ?? 1;
  if (o.smooth) {
    ctx.beginPath(); ctx.moveTo(P[0][0], P[0][1]);
    for (let i = 1; i < P.length - 1; i++) { const mx = (P[i][0] + P[i + 1][0]) / 2, my = (P[i][1] + P[i + 1][1]) / 2; ctx.quadraticCurveTo(P[i][0], P[i][1], mx, my); }
    ctx.lineTo(P[P.length - 1][0], P[P.length - 1][1]);
    if (o.close) ctx.closePath();
  } else tracePath(P, !!o.close);
  ctx.stroke();
  ctx.restore();
}
// Partially drawn polyline (for write-on animation): k in 0..1 of total length.
function partial(pts, k) {
  if (k >= 1) return pts;
  const L = []; let tot = 0;
  for (let i = 1; i < pts.length; i++) { const d = Math.hypot(pts[i][0] - pts[i - 1][0], pts[i][1] - pts[i - 1][1]); L.push(d); tot += d; }
  let want = tot * clamp(k); const out = [pts[0]];
  for (let i = 1; i < pts.length; i++) {
    if (want >= L[i - 1]) { out.push(pts[i]); want -= L[i - 1]; continue; }
    const f = want / L[i - 1]; out.push([lerp(pts[i - 1][0], pts[i][0], f), lerp(pts[i - 1][1], pts[i][1], f)]); break;
  }
  return out;
}
function arrow(x1, y1, x2, y2, color = PAL.ink, w = 7, o = {}) {
  const k = o.k ?? 1, bend = o.bend ?? .15;
  const mx = (x1 + x2) / 2 - (y2 - y1) * bend, my = (y1 + y2) / 2 + (x2 - x1) * bend;
  const curve = []; for (let i = 0; i <= 16; i++) { const u = i / 16; curve.push([(1 - u) ** 2 * x1 + 2 * (1 - u) * u * mx + u * u * x2, (1 - u) ** 2 * y1 + 2 * (1 - u) * u * my + u * u * y2]); }
  const P = partial(curve, k); marker(P, color, w, { rough: 1 });
  if (k > .92) {
    const [ax, ay] = P[P.length - 1], [bx, by] = P[Math.max(0, P.length - 3)], a = Math.atan2(ay - by, ax - bx), hl = w * 4.5;
    marker([[ax - Math.cos(a - .5) * hl, ay - Math.sin(a - .5) * hl], [ax, ay], [ax - Math.cos(a + .5) * hl, ay - Math.sin(a + .5) * hl]], color, w, { rough: 1 });
  }
}
// Hand-drawn loop around something.
function circleMark(cx, cy, rx, ry, color = PAL.red, w = 6, k = 1, seed = 5) {
  const pts = []; for (let i = 0; i <= 44; i++) { const a = -1.2 + i / 40 * TAU; const r = 1 + (hash2(seed, i) - .5) * .08; pts.push([cx + Math.cos(a) * rx * r, cy + Math.sin(a) * ry * r]); }
  marker(partial(pts, k), color, w, { rough: 1.2, smooth: true });
}
function underline(x1, x2, y, color = PAL.red, w = 7, k = 1) {
  marker(partial([[x1, y], [lerp(x1, x2, .5), y + 4], [x2, y - 3]], k), color, w, { rough: 2, smooth: true });
}
// Scribble fill inside a shape (quick zig-zag hatching).
function scribble(pts, color = PAL.ink, gap = 14, w = 3, o = {}) {
  const b = bbox(pts), ang = o.angle ?? -.5, L = Math.hypot(b.w, b.h);
  ctx.save(); tracePath(pts); ctx.clip();
  const zz = []; let side = 0;
  for (let d = -L / 2; d < L / 2; d += gap) { side ^= 1; zz.push([b.cx + Math.cos(ang) * d + Math.cos(ang + TAU / 4) * (side ? L / 2 : -L / 2), b.cy + Math.sin(ang) * d + Math.sin(ang + TAU / 4) * (side ? L / 2 : -L / 2)]); }
  marker(zz, color, w, { rough: 2, alpha: o.alpha ?? .85 });
  ctx.restore();
}

// ---------- text ----------
const FONTS = {
  anton: 'Anton', archivo: 'Archivo Black', bebas: 'Bebas Neue', marker: 'Permanent Marker', typewriter: 'Special Elite',
  mono: 'Rubik Mono One', abril: 'Abril Fatface', courier: 'Courier Prime', scrawl: 'Rock Salt', bungee: 'Bungee',
  fraktur: 'UnifrakturMaguntia', code: 'Space Mono', shrikhand: 'Shrikhand', rammetto: 'Rammetto One',
};
// txt(str, x, y, size, colour, o): plain lettering. o: font (key of FONTS or family), align, rot, alpha, stroke (colour), sw, shadow ([dx,dy] or true), shadowCol, maxW, spacing, baseline.
function txt(str, x, y, size, color = PAL.ink, o = {}) {
  ctx.save();
  ctx.translate(x, y); if (o.rot) ctx.rotate(o.rot); if (o.sx || o.sy) ctx.scale(o.sx ?? 1, o.sy ?? 1);
  ctx.globalAlpha *= o.alpha ?? 1;
  const fam = FONTS[o.font] || o.font || 'Anton';
  ctx.font = `${o.weight ? o.weight + ' ' : ''}${size}px "${fam}"`;
  ctx.textAlign = o.align ?? 'center'; ctx.textBaseline = o.baseline ?? 'middle';
  if (o.spacing) ctx.letterSpacing = `${o.spacing}px`;
  let sx = 1;
  if (o.maxW) { const w = ctx.measureText(str).width; if (w > o.maxW) sx = o.maxW / w; }
  if (sx !== 1) ctx.scale(sx, 1);
  if (o.shadow) { const [dx, dy] = Array.isArray(o.shadow) ? o.shadow : [size * .06, size * .08]; ctx.fillStyle = o.shadowCol ?? PAL.ink; ctx.fillText(str, dx, dy); }
  if (o.stroke) { ctx.strokeStyle = o.stroke; ctx.lineWidth = o.sw ?? size * .12; ctx.lineJoin = 'round'; ctx.strokeText(str, 0, 0); }
  ctx.fillStyle = color; ctx.fillText(str, 0, 0);
  ctx.restore();
}
function textW(str, size, font = 'anton', spacing = 0) {
  ctx.save(); ctx.font = `${size}px "${FONTS[font] || font}"`; if (spacing) ctx.letterSpacing = `${spacing}px`;
  const w = ctx.measureText(str).width; ctx.restore(); return w;
}
// Word-wrap into lines no wider than maxW.
function wrap(str, size, font, maxW) {
  const words = String(str).split(/\s+/), lines = []; let cur = '';
  for (const w of words) { const t = cur ? cur + ' ' + w : w; if (textW(t, size, font) > maxW && cur) { lines.push(cur); cur = w; } else cur = t; }
  if (cur) lines.push(cur); return lines;
}

// Ransom-note lettering: each glyph on its own scrap, in its own font/colours. Deterministic by `seed`.
// ransom(str, x, y, size, o): o.seed, o.align ('center'|'left'), o.pop (0..1 reveal progress; letters slam in sequence),
//   o.papers / o.inks (colour lists), o.rot (overall), o.maxW, o.jolt (per-letter wobble amount), o.fonts (list of FONTS keys).
// (blackletter was dropped: at speed its I/T/D misread; 'anton' keeps the list length so seeds stay stable)
const RANSOM_FONTS = ['anton', 'abril', 'archivo', 'typewriter', 'bungee', 'mono', 'anton', 'shrikhand', 'courier', 'bebas', 'rammetto'];
const RANSOM_PAPERS = [PAL.white, PAL.newsprint, PAL.yellow, PAL.pink, PAL.ink, PAL.sky, PAL.white, PAL.kraft, PAL.red, PAL.cream];
function ransom(str, x, y, size, o = {}) {
  const seed = o.seed ?? hstr(str) * 1e6 | 0, chars = [...String(str)];
  const fonts = o.fonts ?? RANSOM_FONTS, papers = o.papers ?? RANSOM_PAPERS;
  const glyphs = chars.map((ch, i) => {
    const r = k => hash2(seed + i, k);
    const f = fonts[Math.floor(r(1) * fonts.length)], s = size * (.86 + r(2) * .3);
    const paper = papers[Math.floor(r(3) * papers.length)];
    const dark = [PAL.ink, PAL.red, PAL.blue, PAL.night].includes(paper);
    const inkC = dark ? (r(4) < .5 ? PAL.white : PAL.yellow) : (r(4) < .7 ? PAL.ink : [PAL.red, PAL.blue, PAL.pink][Math.floor(r(5) * 3)]);
    const inkSafe = inkC === paper || (paper === PAL.pink && inkC === PAL.red) || (paper === PAL.sky && inkC === PAL.blue) ? PAL.ink : inkC;
    const g = ch === ' ' ? null : ch;
    const w = g ? textW(g, s, f) : size * .35;
    return { ch, f, s, paper, inkC: inkSafe, w: w + (g ? s * .22 : 0), rot: (r(6) - .5) * .28, dy: (r(7) - .5) * size * .14, pad: s * .1 };
  });
  let total = glyphs.reduce((a, g) => a + g.w, 0) + (glyphs.length - 1) * size * .04;
  let sc = 1; if (o.maxW && total > o.maxW) sc = o.maxW / total;
  ctx.save(); ctx.translate(x, y); if (o.rot) ctx.rotate(o.rot); ctx.scale(sc, sc);
  let cx = o.align === 'left' ? 0 : -total / 2;
  const pop = o.pop ?? 1, n = glyphs.length;
  glyphs.forEach((g, i) => {
    const gx = cx + g.w / 2; cx += g.w + size * .04;
    if (!g.ch.trim()) return;
    const start = i / n * .75, k = clamp((pop - start) / .25);
    if (k <= 0) return;
    const s = backOut(k, 2.2);
    ctx.save(); ctx.translate(gx, g.dy + jit(o.jolt ?? 1.5)); ctx.rotate(g.rot + jit(.015)); ctx.scale(s, s);
    const h = g.s * 1.18;
    scrap(ctrRect(0, 0, g.w, h), g.paper, { torn: 1.5, seed: seed + i, step: 12, shadow: [3, 4] });
    ctx.font = `${g.s}px "${FONTS[g.f]}"`; ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
    ctx.fillStyle = g.inkC; ctx.fillText(g.ch, 0, g.s * .04);
    ctx.restore();
  });
  ctx.restore();
  return total * sc;
}

// ---------- cached decorative text objects ----------
// The cache keeps the most recently used, up to CACHE_BYTES at render scale 1 (and in proportion at other scales): a frame uses at
// most 20 MB of them, but over a song they add up to 100 MB, and one whose size is animated makes a new one every frame. Offline
// renders (?render) keep them all.
const _imgCache = new Map();
let _imgBytes = 0;
SCALE_HOOKS.push(() => { _imgCache.clear(); _imgBytes = 0; });
const CACHE_BYTES = new URLSearchParams(location.search).has('render') ? Infinity : 48e6;
function cached(key, w, h, draw) {
  let c = _imgCache.get(key);
  if (c) { _imgCache.delete(key); _imgCache.set(key, c); return c; }
  // backing store at render scale; lw/lh are the logical size that blit() draws at
  c = makeCanvas(Math.ceil(w * RS), Math.ceil(h * RS)); c.lw = c.width / RS; c.lh = c.height / RS;
  const saved = ctx; ctx = c.getContext('2d'); ctx.scale(RS, RS);
  try { draw(c.lw, c.lh); } finally { ctx = saved; }
  _imgCache.set(key, c); _imgBytes += c.width * c.height * 4;
  for (const [k, old] of _imgCache) {
    if (_imgBytes <= CACHE_BYTES * RS * RS || old === c) break;
    _imgCache.delete(k); _imgBytes -= old.width * old.height * 4;
  }
  return c;
}
function blit(img, x, y, o = {}) {
  ctx.save(); ctx.translate(x, y); if (o.rot) ctx.rotate(o.rot);
  const s = o.s ?? 1; ctx.scale(s * (o.sx ?? 1), s * (o.sy ?? 1));
  ctx.globalAlpha *= o.alpha ?? 1; if (o.blend) ctx.globalCompositeOperation = o.blend;
  const lw = img.lw ?? img.width, lh = img.lh ?? img.height;
  ctx.drawImage(img, -lw / 2, -lh / 2, lw, lh); ctx.restore();
}
// Speckle eraser used for stamps and worn prints.
function _erode(w, h, density = .12, seed = 9) {
  ctx.save(); ctx.globalCompositeOperation = 'destination-out'; ctx.fillStyle = '#000';
  const n = Math.floor(w * h * density / 90);
  for (let i = 0; i < n; i++) { const r = .6 + hash2(seed, i * 3) ** 3 * 4; ctx.globalAlpha = .4 + hash2(seed, i * 3 + 1) * .6; ctx.beginPath(); ctx.arc(hash2(seed, i * 3 + 2) * w, hash(seed * 31 + i) * h, r, 0, TAU); ctx.fill(); }
  ctx.restore();
}
// Rubber stamp: text in a double-ruled box, worn ink, multiplied onto the page.
function stamp(str, x, y, size, color = PAL.red, rot = -.12, o = {}) {
  const font = o.font ?? 'mono', padX = size * .5, padY = size * .32;
  const w = textW(str, size, font, size * .06) + padX * 2, h = size * 1.1 + padY * 2;
  const img = cached(`stamp|${str}|${size}|${color}|${font}|${o.box !== false}`, w + 20, h + 20, (cw, ch) => {
    ctx.translate(10, 10); ctx.strokeStyle = color; ctx.fillStyle = color;
    if (o.box !== false) { ctx.lineWidth = size * .09; ctx.strokeRect(0, 0, w, h); ctx.lineWidth = size * .035; ctx.strokeRect(size * .12, size * .12, w - size * .24, h - size * .24); }
    ctx.font = `${size}px "${FONTS[font] || font}"`; ctx.letterSpacing = `${size * .06}px`; ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
    ctx.fillText(str, w / 2, h / 2 + size * .05);
    ctx.setTransform(RS, 0, 0, RS, 0, 0); _erode(cw, ch, .16, hstr(str) * 1e5 | 0);
  });
  const k = o.pop ?? 1; if (k <= 0) return;
  const s = k < 1 ? lerp(1.8, 1, easeOut(k)) : 1;
  blit(img, x, y, { rot, s, alpha: (o.alpha ?? .92) * clamp(k * 3), blend: o.blend ?? 'multiply' });
}
// Label-maker tape (the song's caption style): embossed white capitals on glossy coloured tape.
function dymo(str, x, y, size, color = PAL.ink, o = {}) {
  str = String(str).toUpperCase().replace(/\b4O\b/g, '4o');
  const font = o.font ?? 'archivo', sp = size * .12, w = textW(str, size, font, sp) + size * 1.4, h = size * 1.6;
  const img = cached(`dymo|${str}|${size}|${color}|${font}`, w + 16, h + 16, () => {
    ctx.translate(8, 8);
    ctx.fillStyle = 'rgb(0 0 0 / .35)'; tracePath(rrPts(4, 6, w, h, size * .18)); ctx.fill();
    ctx.fillStyle = color; tracePath(rrPts(0, 0, w, h, size * .18)); ctx.fill();
    ctx.fillStyle = 'rgb(255 255 255 / .13)'; ctx.fillRect(size * .1, size * .12, w - size * .2, h * .32);
    ctx.font = `${size}px "${FONTS[font] || font}"`; ctx.letterSpacing = `${sp}px`; ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
    ctx.fillStyle = 'rgb(0 0 0 / .35)'; ctx.fillText(str, w / 2 + 2, h / 2 + 3);
    ctx.fillStyle = '#F4F1EA'; ctx.fillText(str, w / 2, h / 2 + 1);
  });
  blit(img, x, y, { rot: o.rot ?? 0, s: o.s ?? 1, alpha: o.alpha ?? 1 });
  return img.lw * (o.s ?? 1);
}
// Masking tape strip centred at (x, y).
function tape(x, y, w = 140, rot = 0, o = {}) {
  const h = o.h ?? 38, seed = o.seed ?? 11;
  ctx.save(); ctx.translate(x, y); ctx.rotate(rot);
  const pts = [];
  for (let i = 0; i <= 6; i++) pts.push([-w / 2 + (hash2(seed, i) - .5) * 8, -h / 2 + i / 6 * h]);
  for (let i = 6; i >= 0; i--) pts.push([w / 2 + (hash2(seed, i + 20) - .5) * 8, -h / 2 + i / 6 * h]);
  // reorder into a loop: left edge top→bottom, right edge bottom→top
  const loop = [...pts.slice(0, 7), ...pts.slice(7)];
  ctx.fillStyle = o.color ?? 'rgb(236 222 180 / .78)'; tracePath(loop); ctx.fill();
  ctx.restore();
}
// Newspaper clipping with masthead + headline + fake body text. Cached per content.
function clipping(cx, cy, w, headline, o = {}) {
  const hs = o.size ?? 54, mast = o.mast ?? 'The Daily Gradient', lines = wrap(headline, hs, 'abril', w - 60);
  const h = (o.h ?? (110 + lines.length * hs * 1.05 + 150));
  const img = cached(`clip|${headline}|${w}|${hs}|${mast}|${o.date || ''}`, w + 30, h + 30, () => {
    ctx.translate(15, 15);
    ctx.fillStyle = 'rgb(0 0 0 / .3)'; tracePath(roughen(rectPts(8, 10, w, h), 3, 14, 7, false)); ctx.fill();
    ctx.fillStyle = PAL.newsprint; tracePath(roughen(rectPts(0, 0, w, h), 3, 14, 3, false)); ctx.fill();
    ctx.fillStyle = PAL.ink; ctx.font = `44px "UnifrakturMaguntia"`; ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
    ctx.fillText(mast, w / 2, 42);
    ctx.fillRect(24, 72, w - 48, 3); ctx.fillRect(24, 78, w - 48, 1.5);
    if (o.date) { ctx.font = `16px "Special Elite"`; ctx.fillText(o.date, w / 2, 94); }
    ctx.font = `${hs}px "Abril Fatface"`;
    lines.forEach((l, i) => ctx.fillText(l, w / 2, 110 + hs * .6 + i * hs * 1.05));
    const top = 118 + lines.length * hs * 1.05, cols = w > 500 ? 3 : 2, cw = (w - 48 - (cols - 1) * 18) / cols;
    ctx.fillStyle = 'rgb(28 26 31 / .55)';
    for (let c = 0; c < cols; c++) for (let r = 0; top + r * 13 < h - 24; r++) ctx.fillRect(24 + c * (cw + 18), top + r * 13, cw * (r % 5 === 4 ? .6 : 1), 5);
  });
  blit(img, cx, cy, { rot: o.rot ?? 0, s: o.s ?? 1 });
  return { w: img.lw, h: img.lh };
}
// Speech bubble with marker text. tail: [x, y] the point the tail aims at.
function bubble(str, x, y, o = {}) {
  const size = o.size ?? 44, font = o.font ?? 'marker', maxW = o.maxW ?? 520;
  const lines = wrap(str, size, font, maxW), w = Math.max(...lines.map(l => textW(l, size, font))) + size * 1.2, h = lines.length * size * 1.15 + size * .9;
  const k = o.pop ?? 1; if (k <= 0) return;
  ctx.save(); ctx.translate(x, y); const s = backOut(k, 2); ctx.scale(s, s); if (o.rot) ctx.rotate(o.rot);
  const body = rrPts(-w / 2, -h / 2, w, h, Math.min(h / 2, 40));
  if (o.tail) {
    const [tx, ty] = [o.tail[0] - x, o.tail[1] - y], ang = Math.atan2(ty, tx);
    const bx = Math.cos(ang) * w * .3, by = Math.sin(ang) * h * .3;
    scrap([[bx - Math.sin(ang) * 26, by + Math.cos(ang) * 26], [tx * .8, ty * .8], [bx + Math.sin(ang) * 26, by - Math.cos(ang) * 26]], o.fill ?? PAL.white, { torn: 1, ink: PAL.ink, sw: 4, shadow: [5, 6] });
  }
  scrap(body, o.fill ?? PAL.white, { torn: 1.5, ink: PAL.ink, sw: 4, shadow: [6, 7], seed: 21 });
  lines.forEach((l, i) => txt(l, 0, -h / 2 + size * .45 + size * .58 + i * size * 1.15, size, o.color ?? PAL.ink, { font }));
  ctx.restore();
}
// Starburst sticker with text.
function sticker(str, x, y, r, color = PAL.yellow, o = {}) {
  const k = o.pop ?? 1; if (k <= 0) return;
  ctx.save(); ctx.translate(x, y); ctx.rotate((o.rot ?? -.15) + jit(.01)); const s = backOut(k, 2.4); ctx.scale(s, s);
  scrap(burstPts(0, 0, r, o.n ?? 16, .8), color, { torn: 1, ink: o.ink === undefined ? PAL.ink : o.ink, sw: 4, seed: 31 });
  const lines = String(str).split('\n'), size = o.size ?? r * .42;
  lines.forEach((l, i) => txt(l, 0, (i - (lines.length - 1) / 2) * size * 1.05, size, o.textCol ?? PAL.ink, { font: o.font ?? 'anton', maxW: r * 1.5 }));
  ctx.restore();
}

;
// ---- src/cast.js ----
// cast.js: characters, all in cut-paper style.
//   clawd(x, y, u, o)    — Clawd, the Claude Code critter and our pop-punk frontman.
//   person(x, y, s, o)   — a generic cut-paper human with a "HELLO my name is" sticker (no likenesses of real people).
//   TRUMP, trumpHair(x, y, s), longTie(x, y, s) — the president's look, drawn over person().
//   bot(x, y, s, o)      — a boxy robot / AI model.
//   agent(x, y, s, o)    — a tiny terminal-window agent critter (for swarms).
//   crowd(y, t, o)       — a moshing silhouette crowd along the bottom of the frame.

// Arm angle convention (all characters): 0 = straight out sideways, +1.2 ≈ raised up, −1.2 ≈ hanging down.

// ---------- Clawd ----------
// (x, y) = ground point between the feet. Body is 10u wide × 6u tall; legs add 2u. So total ≈ 8u tall.
// o: dy (lift, in u; negative = up), sq (squash, + = flatter), rot, flip, aL, aR, walk (phase, legs step),
//    eyes: normal|happy|closed|wide|x|heart|shades|spark|look|angry|worried, lookX, lookY (−1..1), mouth: none|o|O|smile|grin|flat|scream,
//    hat: mohawk|crown|party|headband|beanie|halo|hardhat|grad, col, dk, lt, blush, mic (bool: mic in right hand), guitar (bool),
//    shadow (default true), sweat, glow (halo glow colour), label (text on a HELLO sticker)
function clawd(x, y, u, o = {}) {
  const col = o.col ?? PAL.clawd, dk = o.dk ?? PAL.clawdDk, sq = o.sq ?? 0;
  ctx.save();
  ctx.translate(x, y);
  if (o.shadow !== false) { ctx.fillStyle = 'rgb(28 26 31 / .22)'; tracePath(ellPts(0, 0, 6 * u, 1 * u, 24)); ctx.fill(); }
  ctx.translate(0, (o.dy ?? 0) * u);
  if (o.rot) ctx.rotate(o.rot);
  if (o.flip) ctx.scale(-1, 1);
  ctx.scale(1 + sq * .5, 1 - sq);
  const seed = 101;
  // legs (4 stubs)
  const walk = o.walk;
  [-3.6, -1.4, 1.4, 3.6].forEach((lx, i) => {
    const lift = walk !== undefined ? Math.max(0, Math.sin(walk * TAU + (i % 2) * Math.PI)) * .9 : 0;
    scrap(rectPts((lx - .55) * u, -2.1 * u - lift * u, 1.1 * u, 2.1 * u), dk, { torn: .8, seed: seed + i, shadow: false });
  });
  // arms (nubs), pivot at body side
  const arm = (side, ang) => {
    ctx.save(); ctx.translate(side * 5 * u, -4.9 * u); ctx.rotate(side * -ang);
    scrap(rectPts(side > 0 ? -.2 * u : -1.9 * u, -.6 * u, 2.1 * u, 1.2 * u), col, { torn: .8, seed: seed + 10 + side, shadow: false });
    if (side > 0 && o.mic) { // microphone in the right hand
      ctx.save(); ctx.translate(2 * u, 0); ctx.rotate(-1.2);
      scrap(rectPts(-.3 * u, -2.6 * u, .6 * u, 2.4 * u), PAL.ink, { torn: .5, shadow: false });
      scrap(ellPts(0, -2.9 * u, .75 * u, .9 * u, 16), '#8C8A92', { torn: .5, shadow: false, tone: { color: PAL.ink, cell: 5, dot: .3 } });
      ctx.restore();
    }
    ctx.restore();
  };
  arm(-1, o.aL ?? -.2); arm(1, o.aR ?? -.2);
  // body
  if (o.glow) { ctx.fillStyle = alpha(o.glow, .35); tracePath(ellPts(0, -5 * u, 8 * u, 6 * u, 32)); ctx.fill(); }
  const body = rectPts(-5 * u, -8 * u, 10 * u, 6 * u);
  scrap(body, col, { torn: 1.2, seed, shadow: [u * .35, u * .45], shade: dk, shadeDir: [1, 1], shadeOp: .28 });
  // guitar slung across the body
  if (o.guitar) {
    ctx.save(); ctx.translate(.5 * u, -3.6 * u); ctx.rotate(-.45 + (o.strum ?? 0) * .08);
    scrap(rectPts(-.35 * u, -7.5 * u, .7 * u, 6.2 * u), '#5B3A29', { torn: .5, shadow: false });
    scrap([[-1.8 * u, -1.8 * u], [1.8 * u, -2.2 * u], [2.6 * u, .6 * u], [1 * u, 2.4 * u], [-1.6 * u, 2.2 * u], [-2.6 * u, .2 * u]], PAL.pink, { torn: .8, ink: PAL.ink, sw: u * .18, seed: 77 });
    scrap(ellPts(0, 0, .55 * u, .55 * u, 12), PAL.ink, { torn: .3, shadow: false });
    ctx.restore();
  }
  // face
  const ex = 2.3 * u, ey = -6.2 * u, lx = (o.lookX ?? 0) * .5 * u, ly = (o.lookY ?? 0) * .4 * u;
  const eyes = o.eyes ?? 'normal';
  ctx.fillStyle = PAL.ink; ctx.strokeStyle = PAL.ink; ctx.lineCap = 'round'; ctx.lineWidth = .45 * u;
  for (const s of [-1, 1]) {
    const cx = s * ex + lx, cy = ey + ly;
    ctx.save(); ctx.translate(cx, cy);
    switch (eyes) {
      case 'happy': ctx.beginPath(); ctx.arc(0, .4 * u, .7 * u, Math.PI * 1.1, Math.PI * 1.9); ctx.stroke(); break;
      case 'closed': ctx.beginPath(); ctx.moveTo(-.7 * u, 0); ctx.lineTo(.7 * u, 0); ctx.stroke(); break;
      case 'x': ctx.beginPath(); ctx.moveTo(-.6 * u, -.6 * u); ctx.lineTo(.6 * u, .6 * u); ctx.moveTo(.6 * u, -.6 * u); ctx.lineTo(-.6 * u, .6 * u); ctx.stroke(); break;
      case 'heart': tracePath(heartPts(0, 0, .9 * u, 24)); ctx.fillStyle = PAL.red; ctx.fill(); break;
      case 'spark': tracePath(starPts(0, 0, 1 * u, .4, 4, 0)); ctx.fillStyle = PAL.yellow; ctx.fill(); ctx.lineWidth = .15 * u; ctx.stroke(); break;
      case 'wide': ctx.fillStyle = PAL.white; tracePath(ellPts(0, 0, .8 * u, .95 * u, 16)); ctx.fill(); ctx.lineWidth = .15 * u; ctx.stroke(); ctx.fillStyle = PAL.ink; tracePath(ellPts(lx * .3, ly * .3, .35 * u, .45 * u, 12)); ctx.fill(); break;
      case 'angry': ctx.fillRect(-.45 * u, -.6 * u, .9 * u, 1.3 * u); ctx.beginPath(); ctx.moveTo(-s * .9 * u, -1.3 * u); ctx.lineTo(s * .7 * u, -.7 * u); ctx.stroke(); break;
      case 'worried': ctx.fillRect(-.45 * u, -.5 * u, .9 * u, 1.2 * u); ctx.beginPath(); ctx.moveTo(-s * .8 * u, -1 * u); ctx.lineTo(s * .7 * u, -1.4 * u); ctx.stroke(); break;
      case 'shades': break;
      default: ctx.fillRect(-.45 * u, -.8 * u, .9 * u, 1.6 * u);
    }
    ctx.restore();
  }
  if (eyes === 'shades') {
    ctx.fillStyle = PAL.ink; ctx.fillRect(-4 * u, ey - .8 * u, 8 * u, .45 * u);
    for (const s of [-1, 1]) tracePath(rrPts(s * ex - 1.3 * u, ey - .8 * u, 2.6 * u, 1.7 * u, .6 * u)), ctx.fill();
    ctx.fillStyle = 'rgb(255 255 255 / .5)'; ctx.fillRect(-ex - .8 * u, ey - .5 * u, .7 * u, .3 * u); ctx.fillRect(ex - .8 * u, ey - .5 * u, .7 * u, .3 * u);
  }
  if (o.blush) { ctx.fillStyle = alpha(PAL.pink, .55); for (const s of [-1, 1]) tracePath(ellPts(s * 3.6 * u, -4.6 * u, .9 * u, .5 * u, 12)), ctx.fill(); }
  const mouth = o.mouth ?? 'none', my = -4.4 * u;
  ctx.fillStyle = PAL.ink; ctx.lineWidth = .35 * u;
  switch (mouth) {
    case 'o': tracePath(ellPts(0, my, .6 * u, .7 * u, 16)); ctx.fill(); break;
    case 'O': tracePath(ellPts(0, my + .2 * u, 1 * u, 1.3 * u, 18)); ctx.fill(); ctx.fillStyle = PAL.red; tracePath(ellPts(0, my + .8 * u, .6 * u, .4 * u, 12)); ctx.fill(); break;
    case 'scream': tracePath(rrPts(-1.6 * u, my - .9 * u, 3.2 * u, 2.2 * u, .6 * u)); ctx.fill(); ctx.fillStyle = PAL.red; tracePath(ellPts(0, my + .8 * u, 1 * u, .45 * u, 12)); ctx.fill(); break;
    case 'smile': ctx.beginPath(); ctx.arc(0, my - .8 * u, 1.1 * u, .25 * Math.PI, .75 * Math.PI); ctx.stroke(); break;
    case 'grin': ctx.beginPath(); ctx.moveTo(-1.4 * u, my - .3 * u); ctx.quadraticCurveTo(0, my + 1.4 * u, 1.4 * u, my - .3 * u); ctx.closePath(); ctx.fill(); break;
    case 'flat': ctx.beginPath(); ctx.moveTo(-.8 * u, my); ctx.lineTo(.8 * u, my); ctx.stroke(); break;
  }
  if (o.sweat) { scrap([[4.4 * u, -8 * u], [5 * u, -6.8 * u], [4.4 * u, -6.4 * u], [3.8 * u, -6.8 * u]], PAL.sky, { torn: .3, ink: PAL.ink, sw: .12 * u, shadow: false }); }
  // hats
  const hat = o.hat;
  if (hat === 'mohawk') {
    const spikes = 5;
    for (let i = 0; i < spikes; i++) {
      const hx = (-2.5 + i * 1.25) * u, hh = (2.2 + (i === 2 ? .8 : i % 2 ? .4 : 0)) * u;
      scrap([[hx - .65 * u, -7.8 * u], [hx + jit(.05) * u, -7.8 * u - hh], [hx + .65 * u, -7.8 * u]], i % 2 ? PAL.pink : '#FF78BD', { torn: .5, seed: 140 + i, shadow: false, ink: PAL.ink, sw: .12 * u });
    }
  } else if (hat === 'crown') {
    scrap([[-2.6 * u, -7.9 * u], [-2.6 * u, -10 * u], [-1.3 * u, -9 * u], [0, -10.6 * u], [1.3 * u, -9 * u], [2.6 * u, -10 * u], [2.6 * u, -7.9 * u]], PAL.gold, { torn: .6, ink: PAL.ink, sw: .15 * u, shade: true, shadeOp: .2 });
  } else if (hat === 'party') {
    scrap([[-1.6 * u, -7.9 * u], [0, -12 * u], [1.6 * u, -7.9 * u]], PAL.blue, { torn: .5, ink: PAL.ink, sw: .15 * u, tone: { color: PAL.yellow, cell: 12, dot: .3, op: .9 } });
  } else if (hat === 'headband') {
    scrap(rectPts(-5.1 * u, -7.7 * u, 10.2 * u, 1 * u), PAL.red, { torn: .5, shadow: false });
  } else if (hat === 'beanie') {
    scrap([...ellPts(0, -8 * u, 4.2 * u, 2.4 * u, 20).filter(p => p[1] <= -8 * u), [-4.2 * u, -8 * u]], PAL.blue, { torn: .6, ink: PAL.ink, sw: .15 * u });
  } else if (hat === 'halo') {
    ctx.strokeStyle = PAL.gold; ctx.lineWidth = .6 * u; ctx.beginPath(); ctx.ellipse(0, -10 * u, 3 * u, .8 * u, 0, 0, TAU); ctx.stroke();
  } else if (hat === 'hardhat') {
    scrap([...ellPts(0, -8 * u, 3.8 * u, 2.6 * u, 20).filter(p => p[1] <= -8 * u)], PAL.yellow, { torn: .5, ink: PAL.ink, sw: .15 * u });
    scrap(rectPts(-4.8 * u, -8.3 * u, 9.6 * u, .6 * u), PAL.yellow, { torn: .3, ink: PAL.ink, sw: .12 * u, shadow: false });
  } else if (hat === 'grad') {
    scrap([[-4 * u, -9.4 * u], [0, -10.8 * u], [4 * u, -9.4 * u], [0, -8 * u]], PAL.ink, { torn: .4 });
    marker([[3.2 * u, -9.6 * u], [3.6 * u, -7.6 * u]], PAL.gold, .3 * u, { rough: 0 });
  }
  if (o.label) { ctx.save(); ctx.translate(0, -3.2 * u); helloTag(o.label, 0, 0, u * .75); ctx.restore(); }
  ctx.restore();
}

// "HELLO my name is" sticker; (x, y) centre; k = scale unit (sticker ≈ 5k wide).
function helloTag(name, x, y, k, rot = -.06) {
  ctx.save(); ctx.translate(x, y); ctx.rotate(rot);
  const w = Math.max(5.4 * k, textW(name, 1.5 * k, 'marker') + 1.2 * k), h = 3.4 * k;
  scrap(rrPts(-w / 2, -h / 2, w, h, .5 * k), PAL.red, { torn: .6, seed: 55, shadow: [.15 * k, .2 * k] });
  ctx.fillStyle = PAL.white; tracePath(rectPts(-w / 2 + .25 * k, -h / 2 + 1.25 * k, w - .5 * k, h - 1.6 * k)); ctx.fill();
  txt('HELLO', 0, -h / 2 + .5 * k, .72 * k, PAL.white, { font: 'archivo' });
  txt('my name is', 0, -h / 2 + 1 * k, .32 * k, PAL.white, { font: 'archivo' });
  txt(name, 0, .45 * k, 1.4 * k, PAL.ink, { font: 'marker', maxW: w - .8 * k });
  ctx.restore();
}

// ---------- people ----------
// person(x, y, s, o): (x, y) ground point; total height ≈ 10s. Cut-paper figure, deliberately generic.
// o: skin, hair (short|long|curly|bald|spiky|bun|side|mohawk|buzz|swoop), hairCol, top (tee|hoodie|suit|jacket|coat|sweater|dress),
//    topCol, tie (colour), pants, glasses (true|'round'|'shades'), beard, eyes (dot|closed|wide|angry|worried|happy|x|spark),
//    mouth (smile|flat|o|O|grin|frown|scream), brows, aL, aR, dy, rot, flip, sq, walk, name (HELLO sticker), hold (fn(s) drawn at right hand),
//    holdL (fn(s) at left hand), back (seen from behind), sweat, blush.
const SKINS = ['#F2C9A5', '#E0AC83', '#C68A5E', '#8D5A3B', '#F5D5BC', '#B97A57'];
function person(x, y, s, o = {}) {
  const skin = o.skin ?? SKINS[0], topCol = o.topCol ?? PAL.blue, pants = o.pants ?? '#3B3F58', hairCol = o.hairCol ?? '#3A2A20';
  ctx.save(); ctx.translate(x, y);
  if (o.shadow !== false) { ctx.fillStyle = 'rgb(28 26 31 / .2)'; tracePath(ellPts(0, 0, 2.6 * s, .5 * s, 20)); ctx.fill(); }
  ctx.translate(0, (o.dy ?? 0) * s); if (o.rot) ctx.rotate(o.rot); if (o.flip) ctx.scale(-1, 1);
  const sq = o.sq ?? 0; ctx.scale(1 + sq * .4, 1 - sq);
  const seed = o.seed ?? 300;
  // legs
  const walk = o.walk;
  for (const side of [-1, 1]) {
    const sw = walk !== undefined ? Math.sin(walk * TAU + (side > 0 ? Math.PI : 0)) * .35 : 0;
    ctx.save(); ctx.translate(side * .55 * s, -4 * s); ctx.rotate(sw);
    scrap(rectPts(-.45 * s, 0, .9 * s, 3.8 * s), pants, { torn: .6, seed: seed + side, shadow: false });
    scrap(rrPts(-.6 * s + side * .15 * s, 3.6 * s, 1.35 * s, .55 * s, .25 * s), PAL.ink, { torn: .3, shadow: false });
    ctx.restore();
  }
  // arms
  const arm = (side, ang, hold) => {
    ctx.save(); ctx.translate(side * 1.35 * s, -7.1 * s); ctx.rotate(side * -ang);
    const sleeve = o.top === 'tee' ? skin : topCol;
    scrap(rectPts(side > 0 ? 0 : -3 * s, -.42 * s, 3 * s, .84 * s), sleeve, { torn: .5, seed: seed + 5 + side, shadow: false });
    if (o.top === 'tee') scrap(rectPts(side > 0 ? 0 : -1.1 * s, -.48 * s, 1.1 * s, .96 * s), topCol, { torn: .4, seed: seed + 7 + side, shadow: false });
    ctx.fillStyle = skin; tracePath(ellPts(side * 3.1 * s, 0, .5 * s, .5 * s, 12)); ctx.fill();
    if (hold) { ctx.save(); ctx.translate(side * 3.2 * s, 0); ctx.rotate(side * ang); hold(s); ctx.restore(); }
    ctx.restore();
  };
  arm(-1, o.aL ?? -1.25, o.holdL); arm(1, o.aR ?? -1.25, o.hold);
  // torso
  const top = o.top ?? 'tee';
  const torso = [[-1.45 * s, -7.7 * s], [1.45 * s, -7.7 * s], [1.3 * s, -3.8 * s], [-1.3 * s, -3.8 * s]];
  scrap(o.top === 'dress' ? [[-1.3 * s, -7.7 * s], [1.3 * s, -7.7 * s], [2 * s, -3 * s], [-2 * s, -3 * s]] : torso, topCol, { torn: .7, seed: seed + 9, shadow: [.2 * s, .25 * s], shade: true, shadeOp: .18 });
  if (top === 'suit' || top === 'jacket' || top === 'coat') {
    scrap([[-.55 * s, -7.7 * s], [0, -6.2 * s], [.55 * s, -7.7 * s]], top === 'coat' ? PAL.white : PAL.white, { torn: .3, shadow: false });
    if (o.tie) scrap([[-.18 * s, -7.5 * s], [.18 * s, -7.5 * s], [.3 * s, -5.6 * s], [0, -5.2 * s], [-.3 * s, -5.6 * s]], o.tie, { torn: .2, shadow: false });
    marker([[-.55 * s, -7.7 * s], [0, -6 * s], [.55 * s, -7.7 * s]], PAL.ink, .12 * s, { rough: 0 });
  }
  if (top === 'hoodie') { scrap(ellPts(0, -7.6 * s, 1.5 * s, .5 * s, 16), mixCol(topCol, PAL.ink, .25), { torn: .4, shadow: false }); marker([[-.3 * s, -7.3 * s], [-.35 * s, -6.2 * s]], PAL.white, .1 * s, { rough: 0 }); marker([[.3 * s, -7.3 * s], [.35 * s, -6.2 * s]], PAL.white, .1 * s, { rough: 0 }); }
  if (o.name) helloTag(o.name, .35 * s, -6 * s, .38 * s);
  // head
  ctx.save(); ctx.translate(0, -8.9 * s);
  scrap(rectPts(-.35 * s, .1 * s, .7 * s, .9 * s), skin, { torn: .3, shadow: false });
  const hair = o.hair ?? 'short';
  if (!o.back && (hair === 'long' || hair === 'bun')) scrap(rrPts(-1.35 * s, -1.2 * s, 2.7 * s, 3 * s, 1 * s), hairCol, { torn: .8, seed: seed + 20, shadow: false });
  scrap(ellPts(0, 0, 1.15 * s, 1.3 * s, 28), skin, { torn: .8, seed: seed + 21, shadow: [.12 * s, .15 * s] });
  // hair on top
  const hairTop = () => {
    switch (hair) {
      case 'bald': break;
      case 'buzz': scrap([...ellPts(0, -.1 * s, 1.2 * s, 1.35 * s, 28).filter(p => p[1] < -.45 * s)], hairCol, { torn: .4, shadow: false, tone: { color: PAL.ink, cell: 6, dot: .25, op: .5 } }); break;
      case 'spiky': scrap([[-1.25 * s, -.3 * s], [-1.1 * s, -1.7 * s], [-.6 * s, -1.2 * s], [-.3 * s, -2 * s], [.1 * s, -1.3 * s], [.5 * s, -2 * s], [.8 * s, -1.2 * s], [1.3 * s, -1.6 * s], [1.25 * s, -.3 * s], [0, -.9 * s]], hairCol, { torn: .4, shadow: false }); break;
      case 'mohawk': scrap([[-.35 * s, -1 * s], [-.2 * s, -2.6 * s], [.2 * s, -2.7 * s], [.35 * s, -1 * s]], o.hairCol ?? PAL.pink, { torn: .4, shadow: false }); break;
      case 'curly': for (let i = 0; i < 7; i++) { const a = Math.PI + i / 6 * Math.PI; scrap(ellPts(Math.cos(a) * 1.05 * s, Math.sin(a) * 1.1 * s - .2 * s, .5 * s, .5 * s, 12), hairCol, { torn: .3, seed: seed + 30 + i, shadow: false }); } break;
      case 'swoop': scrap([[-1.25 * s, -.1 * s], [-1.2 * s, -1.1 * s], [-.2 * s, -1.6 * s], [1.3 * s, -1.2 * s], [1.3 * s, -.4 * s], [.2 * s, -.8 * s]], hairCol, { torn: .5, shadow: false }); break;
      case 'side': scrap([[-1.25 * s, 0], [-1.2 * s, -1.1 * s], [0, -1.55 * s], [1.2 * s, -1.1 * s], [1.25 * s, -.3 * s], [-.3 * s, -.9 * s]], hairCol, { torn: .5, shadow: false }); break;
      default: scrap([...ellPts(0, -.15 * s, 1.25 * s, 1.35 * s, 28).filter(p => p[1] < -.5 * s)], hairCol, { torn: .6, seed: seed + 22, shadow: false });
    }
    if (hair === 'bun') scrap(ellPts(0, -1.55 * s, .55 * s, .5 * s, 14), hairCol, { torn: .4, shadow: false });
    if (hair === 'long') scrap([...ellPts(0, -.15 * s, 1.3 * s, 1.35 * s, 28).filter(p => p[1] < -.4 * s)], hairCol, { torn: .6, seed: seed + 23, shadow: false });
  };
  if (o.back) { scrap(ellPts(0, 0, 1.2 * s, 1.35 * s, 28), hairCol, { torn: .6, shadow: false }); ctx.restore(); ctx.restore(); return; }
  hairTop();
  // face
  const eyes = o.eyes ?? 'dot', lk = (o.lookX ?? 0) * .25 * s;
  ctx.fillStyle = PAL.ink; ctx.strokeStyle = PAL.ink; ctx.lineWidth = .12 * s; ctx.lineCap = 'round';
  for (const side of [-1, 1]) {
    const ex = side * .45 * s + lk, ey = -.05 * s;
    switch (eyes) {
      case 'closed': case 'happy': ctx.beginPath(); ctx.arc(ex, ey + (eyes === 'happy' ? .12 * s : 0), .18 * s, eyes === 'happy' ? Math.PI * 1.1 : .1 * Math.PI, eyes === 'happy' ? Math.PI * 1.9 : .9 * Math.PI); ctx.stroke(); break;
      case 'wide': ctx.fillStyle = PAL.white; tracePath(ellPts(ex, ey, .27 * s, .3 * s, 12)); ctx.fill(); ctx.stroke(); ctx.fillStyle = PAL.ink; tracePath(ellPts(ex, ey, .1 * s, .12 * s, 8)); ctx.fill(); break;
      case 'x': ctx.beginPath(); ctx.moveTo(ex - .15 * s, ey - .15 * s); ctx.lineTo(ex + .15 * s, ey + .15 * s); ctx.moveTo(ex + .15 * s, ey - .15 * s); ctx.lineTo(ex - .15 * s, ey + .15 * s); ctx.stroke(); break;
      case 'spark': tracePath(starPts(ex, ey, .3 * s, .4, 4, 0)); ctx.fillStyle = PAL.yellow; ctx.fill(); ctx.lineWidth = .05 * s; ctx.stroke(); ctx.fillStyle = PAL.ink; break;
      default: tracePath(ellPts(ex, ey, .11 * s, .14 * s, 10)); ctx.fill();
    }
  }
  const brows = o.brows ?? (eyes === 'angry' ? 'angry' : eyes === 'worried' ? 'worried' : null);
  if (brows) for (const side of [-1, 1]) { ctx.beginPath(); const inner = brows === 'angry' ? .15 : -.12; ctx.moveTo(side * .7 * s, -.45 * s); ctx.lineTo(side * .22 * s, (-.45 + inner) * s); ctx.stroke(); }
  if (o.glasses) {
    ctx.lineWidth = .08 * s;
    if (o.glasses === 'shades') { ctx.fillStyle = PAL.ink; for (const side of [-1, 1]) tracePath(rrPts(side * .45 * s - .32 * s + lk, -.28 * s, .64 * s, .44 * s, .12 * s)), ctx.fill(); ctx.fillRect(-.15 * s + lk, -.2 * s, .3 * s, .07 * s); }
    else { for (const side of [-1, 1]) { ctx.beginPath(); ctx.ellipse(side * .45 * s + lk, -.05 * s, .3 * s, .27 * s, 0, 0, TAU); ctx.stroke(); } ctx.beginPath(); ctx.moveTo(-.15 * s + lk, -.08 * s); ctx.lineTo(.15 * s + lk, -.08 * s); ctx.stroke(); }
  }
  if (o.beard) scrap([[-1.1 * s, .1 * s], [-.9 * s, .9 * s], [0, 1.4 * s], [.9 * s, .9 * s], [1.1 * s, .1 * s], [.5 * s, .55 * s], [-.5 * s, .55 * s]], o.beardCol ?? hairCol, { torn: .4, shadow: false });
  if (o.blush) { ctx.fillStyle = alpha(PAL.pink, .5); for (const side of [-1, 1]) tracePath(ellPts(side * .7 * s, .3 * s, .22 * s, .13 * s, 10)), ctx.fill(); ctx.fillStyle = PAL.ink; }
  const mouth = o.mouth ?? 'smile', my = .55 * s;
  ctx.lineWidth = .1 * s; ctx.fillStyle = PAL.ink;
  switch (mouth) {
    case 'flat': ctx.beginPath(); ctx.moveTo(-.25 * s, my); ctx.lineTo(.25 * s, my); ctx.stroke(); break;
    case 'frown': ctx.beginPath(); ctx.arc(0, my + .3 * s, .3 * s, 1.2 * Math.PI, 1.8 * Math.PI); ctx.stroke(); break;
    case 'o': tracePath(ellPts(0, my, .14 * s, .17 * s, 10)); ctx.fill(); break;
    case 'O': case 'scream': tracePath(ellPts(0, my + .05 * s, .28 * s, .36 * s, 14)); ctx.fill(); ctx.fillStyle = PAL.red; tracePath(ellPts(0, my + .22 * s, .16 * s, .1 * s, 10)); ctx.fill(); break;
    case 'grin': ctx.beginPath(); ctx.moveTo(-.4 * s, my - .1 * s); ctx.quadraticCurveTo(0, my + .45 * s, .4 * s, my - .1 * s); ctx.closePath(); ctx.fill(); ctx.fillStyle = PAL.white; ctx.fillRect(-.3 * s, my - .08 * s, .6 * s, .1 * s); break;
    default: ctx.beginPath(); ctx.arc(0, my - .2 * s, .3 * s, .2 * Math.PI, .8 * Math.PI); ctx.stroke();
  }
  if (o.sweat) scrap([[1.2 * s, -.8 * s], [1.4 * s, -.3 * s], [1.2 * s, -.15 * s], [1 * s, -.3 * s]], PAL.sky, { torn: .2, ink: PAL.ink, sw: .05 * s, shadow: false });
  ctx.restore();
  ctx.restore();
}

// ---------- President Trump ----------
// As cut paper: person() with a tan and no hair of its own ({ ...TRUMP, ... }), then trumpHair() on top: the tall golden swoop
// combed from the left over to a flip above the right brow, and longTie() below. (x, y) = the person's ground point, s its scale,
// rot the same rotation passed to person().
const TRUMP = { top: 'suit', topCol: '#1F2438', tie: PAL.red, hair: 'bald', skin: '#F0A870' };
function trumpHair(x, y, s, rot = 0) {
  ctx.save(); ctx.translate(x, y); ctx.rotate(rot);
  const X = (u, v) => [u * s, -8.9 * s + v * s];
  scrap([X(-1.22, -.25), X(-1.38, -.95), X(-.85, -1.58), X(.15, -1.8), X(1.1, -1.52), X(1.64, -1.0), X(1.6, -.48), X(1.33, -.5), X(1.28, -.78), X(.45, -1.0), X(-.45, -.92), X(-1.0, -.64)], '#F4C24A', { torn: .5, seed: 2290, shadow: [.08 * s, .1 * s], ink: PAL.ink, sw: .05 * s });
  marker([X(-.95, -1.27), X(.1, -1.52), X(1.3, -1.2)], '#FFF1B8', .1 * s, { rough: 0, smooth: true });
  marker([X(-.7, -1.02), X(.4, -1.22), X(1.46, -.82)], '#C8922A', .06 * s, { rough: 0, smooth: true });
  ctx.restore();
}
// the long red tie that hangs past the belt, over person()'s own; (x, y) = person ground, s = person scale
function longTie(x, y, s) {
  scrap([[x - .2 * s, y - 7.5 * s], [x + .2 * s, y - 7.5 * s], [x + .36 * s, y - 3.6 * s], [x, y - 3.1 * s], [x - .36 * s, y - 3.6 * s]], PAL.red, { torn: .3, shadow: [.1 * s, .12 * s], ink: PAL.ink, sw: .05 * s });
}

// ---------- robot ----------
// bot(x, y, s, o): boxy robot, (x, y) ground; height ≈ 10s. o: col, face (text or 'eyes'), screen (screen colour), eyes (dot|x|heart|angry|spark|happy),
//   aL, aR, dy, rot, walk, antenna (bool), label (chest text), sq, hold (fn at right claw), glow.
function bot(x, y, s, o = {}) {
  const col = o.col ?? '#9AA3B5', seed = o.seed ?? 500;
  ctx.save(); ctx.translate(x, y);
  if (o.shadow !== false) { ctx.fillStyle = 'rgb(28 26 31 / .2)'; tracePath(ellPts(0, 0, 2.8 * s, .5 * s, 20)); ctx.fill(); }
  ctx.translate(0, (o.dy ?? 0) * s); if (o.rot) ctx.rotate(o.rot); ctx.scale(1 + (o.sq ?? 0) * .4, 1 - (o.sq ?? 0));
  const walk = o.walk;
  for (const side of [-1, 1]) {
    const lift = walk !== undefined ? Math.max(0, Math.sin(walk * TAU + (side > 0 ? Math.PI : 0))) * .5 * s : 0;
    scrap(rectPts(side * .9 * s - .4 * s, -3.2 * s - lift, .8 * s, 3.2 * s), mixCol(col, PAL.ink, .3), { torn: .4, seed: seed + side, shadow: false });
    scrap(rectPts(side * .9 * s - .7 * s, -.5 * s - lift, 1.4 * s, .5 * s), PAL.ink, { torn: .3, shadow: false });
  }
  const arm = (side, ang, hold) => {
    ctx.save(); ctx.translate(side * 2 * s, -6 * s); ctx.rotate(side * -ang);
    scrap(rectPts(side > 0 ? 0 : -2.6 * s, -.3 * s, 2.6 * s, .6 * s), mixCol(col, PAL.ink, .25), { torn: .3, seed: seed + 4 + side, shadow: false });
    ctx.strokeStyle = PAL.ink; ctx.lineWidth = .25 * s; ctx.beginPath(); ctx.arc(side * 2.9 * s, 0, .45 * s, side > 0 ? -1 : Math.PI - 1, side > 0 ? 1 : Math.PI + 1, false); ctx.stroke();
    if (hold) { ctx.save(); ctx.translate(side * 3 * s, 0); ctx.rotate(side * ang); hold(s); ctx.restore(); }
    ctx.restore();
  };
  arm(-1, o.aL ?? -1, o.holdL); arm(1, o.aR ?? -1, o.hold);
  if (o.glow) { ctx.fillStyle = alpha(o.glow, .3); tracePath(ellPts(0, -6 * s, 4.5 * s, 5 * s, 24)); ctx.fill(); }
  scrap(rrPts(-2 * s, -7.4 * s, 4 * s, 4.4 * s, .4 * s), col, { torn: .8, seed: seed + 9, shade: true, shadeOp: .25 });
  if (o.label) txt(o.label, 0, -5.2 * s, 1.1 * s, PAL.ink, { font: 'archivo', maxW: 3.4 * s });
  // head
  scrap(rrPts(-1.8 * s, -10.6 * s, 3.6 * s, 3 * s, .5 * s), col, { torn: .8, seed: seed + 10, shade: true, shadeOp: .2 });
  scrap(rrPts(-1.45 * s, -10.25 * s, 2.9 * s, 2.2 * s, .3 * s), o.screen ?? '#1D2B2A', { torn: .4, shadow: false });
  const fc = o.faceCol ?? '#6CF2B0', eyes = o.eyes ?? 'dot';
  if (typeof o.face === 'string') txt(o.face, 0, -9.15 * s, .9 * s, fc, { font: 'code', maxW: 2.6 * s });
  else {
    ctx.fillStyle = fc; ctx.strokeStyle = fc; ctx.lineWidth = .16 * s; ctx.lineCap = 'round';
    for (const side of [-1, 1]) {
      const ex = side * .65 * s, ey = -9.4 * s;
      if (eyes === 'x') { ctx.beginPath(); ctx.moveTo(ex - .25 * s, ey - .25 * s); ctx.lineTo(ex + .25 * s, ey + .25 * s); ctx.moveTo(ex + .25 * s, ey - .25 * s); ctx.lineTo(ex - .25 * s, ey + .25 * s); ctx.stroke(); }
      else if (eyes === 'heart') { tracePath(heartPts(ex, ey, .35 * s, 16)); ctx.fill(); }
      else if (eyes === 'angry') { ctx.fillRect(ex - .25 * s, ey - .1 * s, .5 * s, .3 * s); ctx.beginPath(); ctx.moveTo(ex - side * .35 * s, ey - .45 * s); ctx.lineTo(ex + side * .3 * s, ey - .2 * s); ctx.stroke(); }
      else if (eyes === 'happy') { ctx.beginPath(); ctx.arc(ex, ey + .12 * s, .25 * s, Math.PI * 1.1, Math.PI * 1.9); ctx.stroke(); }
      else if (eyes === 'spark') { tracePath(starPts(ex, ey, .4 * s, .4, 4, 0)); ctx.fill(); }
      else { ctx.fillRect(ex - .18 * s, ey - .3 * s, .36 * s, .6 * s); }
    }
    ctx.fillRect(-.5 * s, -8.65 * s, 1 * s, .12 * s);
  }
  if (o.antenna !== false) { marker([[0, -10.6 * s], [0, -11.6 * s]], PAL.ink, .15 * s, { rough: 0 }); scrap(ellPts(0, -11.8 * s, .3 * s, .3 * s, 10), o.bulb ?? PAL.red, { torn: .2, shadow: false }); }
  ctx.restore();
}

// ---------- tiny agent critter (terminal window with legs) ----------
// agent(x, y, s, o): (x, y) ground; ≈ 3s tall. o: col (window colour), face ('>_' default), walk, dy, rot, eyes ('dot'|'x'|'spark'|'heart'|'angry'), bar colour.
function agent(x, y, s, o = {}) {
  ctx.save(); ctx.translate(x, y + (o.dy ?? 0) * s); if (o.rot) ctx.rotate(o.rot);
  const walk = o.walk ?? 0;
  for (const side of [-1, 1]) {
    const lift = Math.max(0, Math.sin(walk * TAU + (side > 0 ? Math.PI : 0))) * .35 * s;
    marker([[side * .5 * s, -.9 * s], [side * .6 * s, -lift]], PAL.ink, .22 * s, { rough: 0 });
  }
  scrap(rrPts(-1.3 * s, -3.1 * s, 2.6 * s, 2.2 * s, .2 * s), o.col ?? '#22252E', { torn: .5, seed: o.seed ?? 600, shadow: [.12 * s, .15 * s] });
  ctx.fillStyle = o.bar ?? PAL.clawd; ctx.fillRect(-1.3 * s, -3.1 * s, 2.6 * s, .45 * s);
  ctx.fillStyle = PAL.white; for (let i = 0; i < 3; i++) { tracePath(ellPts(-1 * s + i * .3 * s, -2.87 * s, .08 * s, .08 * s, 8)); ctx.fill(); }
  const eyes = o.eyes;
  if (eyes) {
    ctx.fillStyle = '#6CF2B0'; ctx.strokeStyle = '#6CF2B0'; ctx.lineWidth = .12 * s;
    for (const side of [-1, 1]) {
      const ex = side * .45 * s, ey = -1.9 * s;
      if (eyes === 'x') { ctx.beginPath(); ctx.moveTo(ex - .15 * s, ey - .15 * s); ctx.lineTo(ex + .15 * s, ey + .15 * s); ctx.moveTo(ex + .15 * s, ey - .15 * s); ctx.lineTo(ex - .15 * s, ey + .15 * s); ctx.stroke(); }
      else if (eyes === 'heart') { tracePath(heartPts(ex, ey, .22 * s, 12)); ctx.fill(); }
      else if (eyes === 'spark') { tracePath(starPts(ex, ey, .25 * s, .4, 4, 0)); ctx.fill(); }
      else if (eyes === 'angry') { ctx.fillRect(ex - .12 * s, ey - .05 * s, .24 * s, .22 * s); ctx.beginPath(); ctx.moveTo(ex - side * .22 * s, ey - .28 * s); ctx.lineTo(ex + side * .18 * s, ey - .12 * s); ctx.stroke(); }
      else ctx.fillRect(ex - .1 * s, ey - .18 * s, .2 * s, .36 * s);
    }
  } else txt(o.face ?? '>_', 0, -1.85 * s, .95 * s, '#6CF2B0', { font: 'code' });
  ctx.restore();
}

// ---------- crowd ----------
// crowd(y, t, o): a row of moshing silhouettes whose heads sit around y. o: n, col, jump (0..1 energy), seed, x0, x1, s (size), hands (0..1 fraction with raised arms), lighters.
function crowd(y, t, o = {}) {
  const n = o.n ?? 22, x0 = o.x0 ?? -40, x1 = o.x1 ?? W + 40, s = o.s ?? 60, seed = o.seed ?? 900, col = o.col ?? PAL.ink;
  for (let i = 0; i < n; i++) {
    const r = k => hash2(seed + i, k), x = lerp(x0, x1, (i + .5) / n) + (r(1) - .5) * 30;
    const ph = r(2), jump = (o.jump ?? .6) * Math.max(0, Math.sin((bpOf(t) + ph) * Math.PI)) ** 2 * s * .5;
    const hy = y - jump + r(3) * s * .3, sz = s * (.85 + r(4) * .35);
    ctx.fillStyle = col;
    tracePath(ellPts(x, hy, sz * .42, sz * .48, 14)); ctx.fill();
    tracePath([[x - sz * .75, hy + sz * .45], [x + sz * .75, hy + sz * .45], [x + sz * .9, H + 50], [x - sz * .9, H + 50]]); ctx.fill();
    if (r(5) < (o.hands ?? .5)) {
      const wave = Math.sin((bpOf(t) * .5 + ph) * TAU) * .25;
      ctx.lineWidth = sz * .22; ctx.lineCap = 'round'; ctx.strokeStyle = col;
      for (const side of r(6) < .5 ? [-1, 1] : [r(7) < .5 ? -1 : 1]) {
        ctx.beginPath(); ctx.moveTo(x + side * sz * .6, hy + sz * .6); ctx.lineTo(x + side * sz * (.9 + wave), hy - sz * 1.1); ctx.stroke();
        if (o.lighters && r(8) < .4) { ctx.fillStyle = PAL.yellow; tracePath(ellPts(x + side * sz * (.9 + wave), hy - sz * 1.45, sz * .12, sz * .25, 10)); ctx.fill(); ctx.fillStyle = col; }
        if (o.horns && r(9) < .5) { ctx.lineWidth = sz * .08; ctx.beginPath(); ctx.moveTo(x + side * sz * (.9 + wave) - sz * .12, hy - sz * 1.1); ctx.lineTo(x + side * sz * (.9 + wave) - sz * .18, hy - sz * 1.45); ctx.moveTo(x + side * sz * (.9 + wave) + sz * .12, hy - sz * 1.1); ctx.lineTo(x + side * sz * (.9 + wave) + sz * .18, hy - sz * 1.45); ctx.stroke(); ctx.lineWidth = sz * .22; }
      }
    }
  }
}

;
// ---- src/props.js ----
// props.js: cut-paper props. All take a centre (x, y) and a scale `s` (≈ the prop is 10s across unless noted), plus options.

// GPU card with spinning fans. o.label, o.col, o.t (time, for fans), o.hot (0..1 red glow)
function gpu(x, y, s, o = {}) {
  ctx.save(); ctx.translate(x, y); if (o.rot) ctx.rotate(o.rot);
  if (o.hot) { ctx.fillStyle = alpha(PAL.red, .35 * o.hot); tracePath(ellPts(0, 0, 7 * s, 4.5 * s, 24)); ctx.fill(); }
  scrap(rectPts(-5 * s, -2.6 * s, 10 * s, 5.2 * s), o.col ?? '#2E3440', { torn: .8, seed: 701, shade: true, shadeOp: .25 });
  scrap(rectPts(-4.2 * s, 2.6 * s, 6 * s, .7 * s), PAL.gold, { torn: .3, shadow: false });
  const t = o.t ?? T;
  for (const fx of [-2.4, 2.4]) {
    ctx.save(); ctx.translate(fx * s, 0);
    scrap(ellPts(0, 0, 2 * s, 2 * s, 24), '#15171C', { torn: .4, shadow: false });
    ctx.rotate(t * 9 + fx);
    ctx.fillStyle = '#5B6475';
    for (let i = 0; i < 7; i++) { ctx.rotate(TAU / 7); tracePath([[0, 0], [1.8 * s, -.35 * s], [1.7 * s, .45 * s]]); ctx.fill(); }
    ctx.restore();
  }
  if (o.label !== '') txt(o.label ?? 'H100', 0, -2.05 * s, .75 * s, PAL.white, { font: 'mono' });
  ctx.restore();
}
// Server rack with blinking LEDs. (x, y) = bottom centre. o.units, o.t
function rack(x, y, s, o = {}) {
  const units = o.units ?? 8, h = units * 1.3 * s + 1 * s;
  ctx.save(); ctx.translate(x, y);
  scrap(rectPts(-3 * s, -h, 6 * s, h), '#23262E', { torn: .8, seed: 711 });
  for (let i = 0; i < units; i++) {
    const yy = -h + .6 * s + i * 1.3 * s;
    ctx.fillStyle = '#3A3F4B'; ctx.fillRect(-2.6 * s, yy, 5.2 * s, 1 * s);
    for (let j = 0; j < 4; j++) { const on = hash2(i * 7 + j, Math.floor((o.t ?? T) * 8)) > .45; ctx.fillStyle = on ? (j % 2 ? '#6CF2B0' : PAL.yellow) : '#1A1C21'; ctx.fillRect(1 * s + j * .38 * s, yy + .35 * s, .22 * s, .3 * s); }
  }
  ctx.restore();
}
// Line chart. (x, y) = top-left; w, h. o.fn(u) → 0..1 (default exponential), o.k (draw progress 0..1), o.col, o.label, o.xlabel, o.ylabel, o.paper (bg colour or null), o.grid, o.log
function chart(x, y, w, h, o = {}) {
  const fn = o.fn ?? (u => (Math.exp(u * 4) - 1) / (Math.exp(4) - 1));
  if (o.paper !== null) scrap(rectPts(x - 30, y - 30, w + 60, h + 70), o.paper ?? PAL.white, { torn: 2, seed: 721, rot: 0 });
  if (o.grid !== false) { ctx.fillStyle = alpha(PAL.blue, .18); for (let i = 1; i < 8; i++) { ctx.fillRect(x + i * w / 8, y, 1.5, h); ctx.fillRect(x, y + i * h / 8, w, 1.5); } }
  marker([[x, y - 10], [x, y + h], [x + w + 10, y + h]], PAL.ink, 6, { rough: 1 });
  const pts = []; for (let i = 0; i <= 60; i++) { const u = i / 60; pts.push([x + u * w, y + h - fn(u) * h]); }
  marker(partial(pts, o.k ?? 1), o.col ?? PAL.red, o.lw ?? 10, { rough: 1.2, smooth: true });
  if (o.label) txt(o.label, x + w / 2, y - 55, o.labelSize ?? 44, PAL.ink, { font: 'marker' });
  if (o.xlabel) txt(o.xlabel, x + w / 2, y + h + 32, 30, PAL.ink, { font: 'marker' });
  if (o.ylabel) txt(o.ylabel, x - 34, y + h / 2, 30, PAL.ink, { font: 'marker', rot: -TAU / 4 });
  const k = clamp(o.k ?? 1), tip = partial(pts, k).at(-1);
  return tip;
}
// A sheet of paper/document. (x, y) centre, w × h. o.title, o.titleFont, o.lines (count), o.rot, o.col, o.stamp ({text, color}), o.body (array of strings)
function doc(x, y, w, h, o = {}) {
  ctx.save(); ctx.translate(x, y); if (o.rot) ctx.rotate(o.rot);
  scrap(rectPts(-w / 2, -h / 2, w, h), o.col ?? PAL.white, { torn: 1.5, seed: o.seed ?? 731 });
  let top = -h / 2 + 50;
  if (o.title) { const L = wrap(o.title, o.titleSize ?? 42, o.titleFont ?? 'abril', w - 60); L.forEach((l, i) => txt(l, 0, top + i * (o.titleSize ?? 42) * 1.1, o.titleSize ?? 42, PAL.ink, { font: o.titleFont ?? 'abril' })); top += L.length * (o.titleSize ?? 42) * 1.1 + 10; }
  if (o.body) { o.body.forEach((l, i) => txt(l, -w / 2 + 30, top + i * 30, 24, PAL.ink, { font: 'typewriter', align: 'left', maxW: w - 60 })); top += o.body.length * 30; }
  ctx.fillStyle = 'rgb(28 26 31 / .45)';
  for (let i = 0; i < (o.lines ?? 8) && top + i * 22 < h / 2 - 30; i++) ctx.fillRect(-w / 2 + 30, top + i * 22, (w - 60) * (i % 4 === 3 ? .55 : 1), 6);
  ctx.restore();
  if (o.stamp) stamp(o.stamp.text, x + (o.stamp.dx ?? 0), y + (o.stamp.dy ?? 0), o.stamp.size ?? 50, o.stamp.color ?? PAL.red, o.stamp.rot ?? -.2, { pop: o.stamp.pop ?? 1 });
}
// Smartphone showing a social post. (x, y) centre; phone ≈ 5s × 10s. o.user, o.handle, o.text, o.caps (upper-case), o.col, o.rot, o.likes
function phone(x, y, s, o = {}) {
  ctx.save(); ctx.translate(x, y); if (o.rot) ctx.rotate(o.rot);
  scrap(rrPts(-2.6 * s, -5 * s, 5.2 * s, 10 * s, .7 * s), o.col ?? PAL.ink, { torn: .6, seed: 741 });
  scrap(rrPts(-2.3 * s, -4.5 * s, 4.6 * s, 9 * s, .3 * s), PAL.white, { torn: .3, shadow: false });
  scrap(ellPts(-1.6 * s, -3.8 * s, .45 * s, .45 * s, 12), o.avatar ?? PAL.blue, { torn: .2, shadow: false });
  txt(o.user ?? 'user', -1 * s, -3.95 * s, .42 * s, PAL.ink, { font: 'archivo', align: 'left', maxW: 3.1 * s });
  txt(o.handle ?? '@user', -1 * s, -3.5 * s, .3 * s, PAL.grey, { font: 'archivo', align: 'left', maxW: 3.1 * s });
  const size = o.size ?? .48 * s, L = wrap(o.caps ? String(o.text).toUpperCase() : o.text ?? '', size, o.font ?? 'archivo', 4 * s);
  L.slice(0, 11).forEach((l, i) => txt(l, -2 * s, -2.8 * s + i * size * 1.25, size, PAL.ink, { font: o.font ?? 'archivo', align: 'left' }));
  if (o.likes) txt(`♥ ${o.likes}   ↻ ${o.reposts ?? ''}`, -2 * s, 3.9 * s, .35 * s, PAL.grey, { font: 'archivo', align: 'left' });
  ctx.restore();
}
// Laptop with screen text (code-ish). (x, y) = bottom centre of base; ≈ 10s wide. o.lines (array of strings), o.screen colour, o.textCol, o.open (0..1 lid angle)
function laptop(x, y, s, o = {}) {
  ctx.save(); ctx.translate(x, y);
  scrap([[-5.5 * s, 0], [5.5 * s, 0], [4.6 * s, -.8 * s], [-4.6 * s, -.8 * s]], '#B8BCC6', { torn: .5, seed: 751 });
  const open = o.open ?? 1;
  ctx.save(); ctx.translate(0, -.8 * s); ctx.scale(1, lerp(.08, 1, open));
  scrap(rectPts(-4.6 * s, -6.2 * s, 9.2 * s, 6.2 * s), '#8E939E', { torn: .5, seed: 752 });
  scrap(rectPts(-4.2 * s, -5.8 * s, 8.4 * s, 5.4 * s), o.screen ?? '#1A1D24', { torn: .3, shadow: false });
  (o.lines ?? []).slice(0, 8).forEach((l, i) => txt(l, -3.9 * s, -5.3 * s + i * .62 * s, .45 * s, o.textCol ?? '#6CF2B0', { font: 'code', align: 'left', maxW: 7.8 * s }));
  ctx.restore(); ctx.restore();
}
// Gold medal on a ribbon. (x, y) = medal centre, radius ≈ 2s. o.text
function medal(x, y, s, o = {}) {
  ctx.save(); ctx.translate(x, y); if (o.rot) ctx.rotate(o.rot);
  scrap([[-1.6 * s, -6 * s], [-.4 * s, -1.5 * s], [.4 * s, -1.5 * s], [1.6 * s, -6 * s], [.6 * s, -6 * s], [0, -3 * s], [-.6 * s, -6 * s]], o.ribbon ?? PAL.blue, { torn: .5, seed: 761 });
  scrap(ellPts(0, 0, 2.2 * s, 2.2 * s, 28), PAL.gold, { torn: .6, ink: PAL.ink, sw: .15 * s, shade: true, shadeOp: .35 });
  ctx.strokeStyle = alpha(PAL.ink, .5); ctx.lineWidth = .1 * s; ctx.beginPath(); ctx.arc(0, 0, 1.6 * s, 0, TAU); ctx.stroke();
  if (o.text) txt(o.text, 0, .05 * s, .9 * s, PAL.ink, { font: 'abril', maxW: 2.8 * s });
  ctx.restore();
}
// Stack of banknotes / cash bundle. (x, y) centre. o.label, o.n (bills in stack)
function money(x, y, s, o = {}) {
  ctx.save(); ctx.translate(x, y); if (o.rot) ctx.rotate(o.rot);
  const n = o.n ?? 4;
  for (let i = n - 1; i >= 0; i--) {
    scrap(rectPts(-4 * s + i * .15 * s, -2 * s - i * .35 * s, 8 * s, 4 * s), i ? '#7FB685' : '#9ED39F', { torn: .6, seed: 771 + i, shadow: i === n - 1 });
  }
  scrap(ellPts(0, 0, 1.3 * s, 1.5 * s, 20), '#CFEBC9', { torn: .3, shadow: false });
  txt('$', 0, .1 * s, 2 * s, '#2F6B3A', { font: 'abril' });
  scrap(rectPts(-.8 * s, -2.05 * s, 1.6 * s, 4.1 * s), PAL.cream, { torn: .3, shadow: false, op: .9 });
  if (o.label) txt(o.label, 0, 0, .8 * s, PAL.ink, { font: 'anton', rot: TAU / 4, maxW: 3.6 * s });
  ctx.restore();
}
// Rocket pointing up. (x, y) centre. o.flame (0..1), o.col, o.label
function rocket(x, y, s, o = {}) {
  ctx.save(); ctx.translate(x, y); if (o.rot) ctx.rotate(o.rot);
  if (o.flame) { for (let i = 0; i < 3; i++) { const f = o.flame * (1 + jit(.15)); scrap([[-1.2 * s + i * .4 * s, 4 * s], [0, 4 * s + (5 - i * 1.3) * s * f], [1.2 * s - i * .4 * s, 4 * s]], [PAL.red, PAL.orange, PAL.yellow][i], { torn: .6, shadow: false, seed: 780 + i }); } }
  scrap([[-2.6 * s, 4.2 * s], [-1.4 * s, 1.8 * s], [-1.4 * s, 4.2 * s]], PAL.red, { torn: .4, seed: 783 });
  scrap([[2.6 * s, 4.2 * s], [1.4 * s, 1.8 * s], [1.4 * s, 4.2 * s]], PAL.red, { torn: .4, seed: 784 });
  scrap([[0, -5.5 * s], [1.5 * s, -2.5 * s], [1.5 * s, 4.2 * s], [-1.5 * s, 4.2 * s], [-1.5 * s, -2.5 * s]], o.col ?? PAL.white, { torn: .6, seed: 785, ink: PAL.ink, sw: .15 * s, shade: true, shadeOp: .25 });
  scrap(ellPts(0, -1.2 * s, .75 * s, .75 * s, 16), PAL.sky, { torn: .3, ink: PAL.ink, sw: .12 * s, shadow: false });
  if (o.label) txt(o.label, 0, 2 * s, .7 * s, PAL.ink, { font: 'anton', rot: -TAU / 4, maxW: 2.6 * s });
  ctx.restore();
}
function banana(x, y, s, o = {}) {
  ctx.save(); ctx.translate(x, y); if (o.rot) ctx.rotate(o.rot);
  const pts = []; for (let i = 0; i <= 20; i++) { const a = Math.PI * (.15 + i / 20 * .7); pts.push([Math.cos(a) * 5 * s, Math.sin(a) * 3.2 * s - 2 * s]); }
  for (let i = 20; i >= 0; i--) { const a = Math.PI * (.15 + i / 20 * .7); pts.push([Math.cos(a) * 4.2 * s, Math.sin(a) * 2 * s - 1.6 * s]); }
  scrap(pts, PAL.yellow, { torn: .6, ink: PAL.ink, sw: .18 * s, seed: 791, shade: '#B08A1E', shadeOp: .4 });
  scrap(rectPts(-4.6 * s, -.6 * s, .8 * s, .7 * s), '#6B4A2A', { torn: .3, shadow: false, rot: .5 });
  ctx.restore();
}
// Lobster (OpenClaw mascot vibe). (x, y) centre; ≈ 10s long. o.col, o.claws (0..1 pinch)
function lobster(x, y, s, o = {}) {
  ctx.save(); ctx.translate(x, y); if (o.rot) ctx.rotate(o.rot);
  const col = o.col ?? PAL.red, pinch = o.claws ?? 0;
  for (let i = 0; i < 3; i++) marker([[(-.8 + i * .8) * s, 1 * s], [(-1.8 + i * 1.8) * s, 2.6 * s]], mixCol(col, PAL.ink, .3), .35 * s, { rough: 0 });
  for (let i = 0; i < 4; i++) scrap(ellPts(0, (1 + i * 1.1) * s, (1.5 - i * .2) * s, .7 * s, 14), col, { torn: .4, seed: 800 + i, shadow: false, ink: PAL.ink, sw: .1 * s });
  scrap([[-1 * s, 5.2 * s], [0, 6.2 * s], [1 * s, 5.2 * s], [0, 4.6 * s]], col, { torn: .3, shadow: false });
  scrap(ellPts(0, -1.2 * s, 1.9 * s, 2.6 * s, 24), col, { torn: .6, ink: PAL.ink, sw: .15 * s, seed: 810, shade: true, shadeOp: .25 });
  for (const side of [-1, 1]) {
    ctx.save(); ctx.translate(side * 1.6 * s, -2.8 * s); ctx.rotate(side * .6);
    marker([[0, 0], [side * 1.2 * s, -1.8 * s]], col, .5 * s, { rough: 0 });
    ctx.translate(side * 1.4 * s, -2.6 * s);
    scrap([[0, 1 * s], [-1 * s, -.4 * s], [-.6 * s, -1.8 * s], [0, -.6 * s + pinch * .4 * s]], col, { torn: .3, ink: PAL.ink, sw: .1 * s, shadow: false });
    scrap([[0, 1 * s], [1 * s, -.4 * s], [.6 * s, -1.8 * s], [0, -.6 * s + pinch * .4 * s]], col, { torn: .3, ink: PAL.ink, sw: .1 * s, shadow: false });
    ctx.restore();
  }
  for (const side of [-1, 1]) { marker([[side * .6 * s, -3.4 * s], [side * 2.4 * s, -6.4 * s]], PAL.ink, .12 * s, { rough: 0 }); scrap(ellPts(side * .7 * s, -3 * s, .35 * s, .35 * s, 10), PAL.ink, { torn: .1, shadow: false }); }
  ctx.restore();
}
// The hugging-face emoji: yellow face with jazz hands. (x, y) centre, radius r. o.mood: 'happy'|'scared'|'x', o.hands (0..1 raise)
function huggy(x, y, r, o = {}) {
  ctx.save(); ctx.translate(x, y); if (o.rot) ctx.rotate(o.rot);
  scrap(ellPts(0, 0, r, r, 36), '#FFD21E', { torn: r * .015, seed: 820, ink: PAL.ink, sw: r * .04, shade: '#E0A400', shadeOp: .45 });
  const m = o.mood ?? 'happy';
  ctx.strokeStyle = PAL.ink; ctx.fillStyle = PAL.ink; ctx.lineWidth = r * .07; ctx.lineCap = 'round';
  for (const side of [-1, 1]) {
    const ex = side * r * .35, ey = -r * .2;
    if (m === 'happy') { ctx.beginPath(); ctx.arc(ex, ey + r * .08, r * .14, Math.PI * 1.1, Math.PI * 1.9); ctx.stroke(); }
    else if (m === 'x') { ctx.beginPath(); ctx.moveTo(ex - r * .1, ey - r * .1); ctx.lineTo(ex + r * .1, ey + r * .1); ctx.moveTo(ex + r * .1, ey - r * .1); ctx.lineTo(ex - r * .1, ey + r * .1); ctx.stroke(); }
    else { ctx.fillStyle = PAL.white; tracePath(ellPts(ex, ey, r * .15, r * .17, 12)); ctx.fill(); ctx.stroke(); ctx.fillStyle = PAL.ink; tracePath(ellPts(ex, ey + r * .03, r * .06, r * .07, 8)); ctx.fill(); }
  }
  if (m === 'happy') { ctx.beginPath(); ctx.moveTo(-r * .4, r * .12); ctx.quadraticCurveTo(0, r * .62, r * .4, r * .12); ctx.closePath(); ctx.fillStyle = '#6B2A1A'; ctx.fill(); ctx.stroke(); }
  else { tracePath(ellPts(0, r * .3, r * .16, r * .2, 12)); ctx.fillStyle = '#6B2A1A'; ctx.fill(); }
  const hr = o.hands ?? 0;
  for (const side of [-1, 1]) {
    ctx.save(); ctx.translate(side * r * .62, r * (.55 - hr * .5)); ctx.rotate(side * (.3 + hr * .5));
    scrap(rrPts(-r * .26, -r * .3, r * .52, r * .6, r * .2), '#FFC21A', { torn: .5, ink: PAL.ink, sw: r * .035, seed: 821 + side, shadow: false });
    ctx.restore();
  }
  ctx.restore();
}
// Cork message board with pinned notes. (x, y) top-left, w × h. o.notes: array of strings, o.k (reveal 0..1)
function corkboard(x, y, w, h, o = {}) {
  scrap(rectPts(x - 18, y - 18, w + 36, h + 36), '#8A5A3B', { torn: 1.5, seed: 830 });
  scrap(rectPts(x, y, w, h), '#C9955C', { torn: 1, seed: 831, shadow: false, tone: { color: '#7A4E2C', cell: 7, dot: .22, op: .6 } });
  const notes = o.notes ?? [], k = o.k ?? 1, cols = o.cols ?? 3;
  notes.forEach((n, i) => {
    const appear = clamp(k * notes.length - i); if (appear <= 0) return;
    const cx = x + (i % cols + .5) * w / cols + (hash(i + 3) - .5) * 30, cy = y + (Math.floor(i / cols) + .55) * (o.rowH ?? 120) + (hash(i + 9) - .5) * 20;
    ctx.save(); ctx.translate(cx, cy); ctx.rotate((hash(i) - .5) * .25); const sc = backOut(appear); ctx.scale(sc, sc);
    const nw = w / cols * .82, nh = (o.rowH ?? 120) * .78;
    scrap(rectPts(-nw / 2, -nh / 2, nw, nh), [PAL.yellow, PAL.white, PAL.pink, PAL.sky, PAL.mint][i % 5], { torn: 1, seed: 840 + i });
    wrap(n, o.noteSize ?? 24, 'marker', nw - 16).slice(0, 3).forEach((l, j, arr) => txt(l, 0, (j - (arr.length - 1) / 2) * (o.noteSize ?? 24) * 1.15, o.noteSize ?? 24, PAL.ink, { font: 'marker' }));
    scrap(ellPts(0, -nh / 2 + 8, 8, 8, 10), PAL.red, { torn: .2, shadow: [2, 3] });
    ctx.restore();
  });
}
// Cut-paper flames, flickering. (x, y) = base centre; ≈ 6s wide, 10s tall. o.n (tongues), o.k (height 0..1)
function fire(x, y, s, o = {}) {
  const n = o.n ?? 5, k = o.k ?? 1, t = o.t ?? T;
  const cols = [PAL.red, PAL.orange, PAL.yellow];
  cols.forEach((c, layer) => {
    for (let i = 0; i < n; i++) {
      const fx = (i - (n - 1) / 2) * s * 1.2 * (1 - layer * .2), fh = (6 + hash(i * 3 + layer) * 5) * s * (1 - layer * .25) * k * (1 + Math.sin(t * 13 + i * 2 + layer) * .12);
      const sway = Math.sin(t * 7 + i + layer * 2) * s * .8;
      scrap([[fx - 1.4 * s * (1 - layer * .25), y], [fx + sway * .5 - .6 * s, y - fh * .55], [fx + sway, y - fh], [fx + sway * .5 + .6 * s, y - fh * .5], [fx + 1.4 * s * (1 - layer * .25), y]].map(([a, b]) => [x + a, b]), c, { torn: .6, shadow: false, seed: 850 + i * 3 + layer });
    }
  });
}
// Bomb with lit fuse. (x, y) centre of the sphere; radius ≈ 3s. o.fuse (0..1 remaining), o.t
function bomb(x, y, s, o = {}) {
  ctx.save(); ctx.translate(x, y); if (o.rot) ctx.rotate(o.rot);
  const fuse = o.fuse ?? 1;
  const path = []; for (let i = 0; i <= 12; i++) { const u = i / 12; path.push([2 * s + u * 3 * s, -2.6 * s - Math.sin(u * 3) * 2.2 * s]); }
  marker(partial(path, fuse), '#8B6B43', .35 * s, { rough: .5 });
  if (fuse > 0) { const [sx, sy] = partial(path, fuse).at(-1); scrap(burstPts(sx, sy, (1.2 + jit(.3)) * s, 10, .4, T * 9), PAL.yellow, { torn: .3, shadow: false, ink: PAL.orange, sw: .1 * s }); }
  scrap(rectPts(1 * s, -3.4 * s, 1.6 * s, 1.2 * s), '#3A3D45', { torn: .3, rot: .7 });
  scrap(ellPts(0, 0, 3.2 * s, 3.2 * s, 32), '#2A2C33', { torn: .6, seed: 860, shade: true, shadeOp: .35 });
  ctx.fillStyle = 'rgb(255 255 255 / .25)'; tracePath(ellPts(-1.2 * s, -1.2 * s, .8 * s, .5 * s, 12, -.6)); ctx.fill();
  if (o.label) txt(o.label, 0, .3 * s, 1 * s, PAL.white, { font: 'anton', maxW: 4.6 * s });
  ctx.restore();
}
// Brain. (x, y) centre; ≈ 8s wide. o.col, o.glow
function brain(x, y, s, o = {}) {
  ctx.save(); ctx.translate(x, y);
  if (o.glow) { ctx.fillStyle = alpha(o.glow, .35); tracePath(ellPts(0, 0, 6 * s, 5 * s, 24)); ctx.fill(); }
  const col = o.col ?? '#F4A6B8';
  scrap(ellPts(0, 0, 4 * s, 3.1 * s, 36), col, { torn: .8, ink: PAL.ink, sw: .15 * s, seed: 870, shade: true, shadeOp: .25 });
  for (let i = 0; i < 7; i++) { const a = hash(i + 870) * TAU, r = 1 + hash(i + 871) * 1.8; const pts = []; for (let j = 0; j < 6; j++) pts.push([Math.cos(a) * r * s + Math.cos(a + j) * s * .9, Math.sin(a) * r * s * .75 + Math.sin(a + j * 1.3) * s * .7]); marker(pts, mixCol(col, PAL.ink, .5), .12 * s, { rough: .5, smooth: true }); }
  marker([[0, -3 * s], [.3 * s, 0], [0, 3 * s]], mixCol(col, PAL.ink, .5), .15 * s, { rough: .5, smooth: true });
  ctx.restore();
}
// Flag on a pole. (x, y) = pole base. o.cols (stripes, horizontal), o.star, o.wave (phase)
function flag(x, y, s, o = {}) {
  const cols = o.cols ?? [PAL.red, PAL.white, PAL.blue], ph = o.wave ?? T * 3;
  marker([[x, y], [x, y - 12 * s]], '#6B5B4B', .35 * s, { rough: 0 });
  const w = 7 * s, h = 4.5 * s, top = y - 12 * s;
  cols.forEach((c, i) => {
    const pts = []; for (let j = 0; j <= 10; j++) { const u = j / 10; pts.push([x + u * w, top + i * h / cols.length + Math.sin(u * 5 + ph) * .4 * s * u]); }
    for (let j = 10; j >= 0; j--) { const u = j / 10; pts.push([x + u * w, top + (i + 1) * h / cols.length + Math.sin(u * 5 + ph) * .4 * s * u]); }
    scrap(pts, c, { torn: .3, shadow: false, seed: 880 + i });
  });
  if (o.stars) { for (let i = 0; i < 12; i++) { const a = i / 12 * TAU; scrap(starPts(x + w / 2 + Math.cos(a) * 1.3 * s, top + h / 2 + Math.sin(a) * 1.3 * s + Math.sin(.5 * 5 + ph) * .2 * s, .28 * s, .45), PAL.yellow, { torn: 0, shadow: false }); } }
}
// Gavel. (x, y) = head centre. o.rot (swing)
function gavel(x, y, s, o = {}) {
  ctx.save(); ctx.translate(x, y); ctx.rotate(o.rot ?? 0);
  scrap(rectPts(-.35 * s, 0, .7 * s, 6 * s), '#8B5A2B', { torn: .3, seed: 890 });
  scrap(rrPts(-2.2 * s, -1.1 * s, 4.4 * s, 2.2 * s, .4 * s), '#6B3F1F', { torn: .4, seed: 891, ink: PAL.ink, sw: .12 * s, shade: true, shadeOp: .3 });
  ctx.restore();
}
// Mic stand / amp / drum kit for the chorus stage.
function amp(x, y, s, o = {}) { // (x, y) bottom centre, ≈ 8s wide
  scrap(rectPts(x - 4 * s, y - 7 * s, 8 * s, 7 * s), '#1E1E24', { torn: .8, seed: 900 });
  scrap(rectPts(x - 3.4 * s, y - 6.2 * s, 6.8 * s, 5.4 * s), '#3B3B45', { torn: .4, shadow: false, tone: { color: PAL.ink, cell: 7, dot: .3, op: .7 } });
  txt(o.label ?? 'SCALE', x, y - 6.6 * s, .5 * s, PAL.gold, { font: 'shrikhand' });
  const p = pulse(T, 5);
  for (const dx of [-1.6, 1.6]) { ctx.fillStyle = 'rgb(0 0 0 / .45)'; tracePath(ellPts(x + dx * s, y - 3.4 * s, (1.3 + p * .15) * s, (1.3 + p * .15) * s, 20)); ctx.fill(); }
}
function drumkit(x, y, s, o = {}) { // (x, y) floor centre, ≈ 12s wide
  const p = pulse(T, 7);
  for (const dx of [-4.2, 4.2]) { marker([[x + dx * s, y], [x + dx * s * 1.05, y - 7 * s]], '#AAA', .2 * s, { rough: 0 }); scrap(ellPts(x + dx * s * 1.05, y - 7 * s - (dx < 0 ? p * .3 * s : 0), 1.8 * s, .35 * s, 16), PAL.gold, { torn: .3, ink: PAL.ink, sw: .08 * s }); }
  scrap(ellPts(x, y - 3.2 * s, 3.2 * s * (1 + p * .03), 3.2 * s * (1 + p * .03), 28), o.col ?? PAL.red, { torn: .6, ink: PAL.ink, sw: .15 * s, seed: 910 });
  scrap(ellPts(x, y - 3.2 * s, 2.5 * s, 2.5 * s, 28), PAL.white, { torn: .3, shadow: false });
  txt(o.label ?? 'LOSS↓', x, y - 3.2 * s, .9 * s, PAL.ink, { font: 'shrikhand', maxW: 4.4 * s });
  for (const dx of [-2.3, 2.3]) scrap(rectPts(x + dx * s - 1.2 * s, y - 7.6 * s, 2.4 * s, 1.4 * s), o.col ?? PAL.red, { torn: .4, ink: PAL.ink, sw: .1 * s, seed: 911 + dx });
}
function micStand(x, y, s) { marker([[x, y], [x, y - 9 * s]], '#9A9AA6', .3 * s, { rough: 0 }); marker([[x - 1.5 * s, y], [x + 1.5 * s, y]], '#9A9AA6', .3 * s, { rough: 0 }); scrap(ellPts(x, y - 9.6 * s, .7 * s, .9 * s, 14), '#6E6E78', { torn: .2, tone: { color: PAL.ink, cell: 5, dot: .3 } }); }
// Trophy cup. (x, y) = base centre
function trophy(x, y, s, o = {}) {
  scrap(rectPts(x - 2 * s, y - 1 * s, 4 * s, 1 * s), '#5B3A29', { torn: .3, seed: 920 });
  scrap(rectPts(x - .5 * s, y - 3 * s, 1 * s, 2 * s), PAL.gold, { torn: .3, shadow: false });
  scrap([[x - 3 * s, y - 8 * s], [x + 3 * s, y - 8 * s], [x + 2 * s, y - 4 * s], [x, y - 3 * s], [x - 2 * s, y - 4 * s]], PAL.gold, { torn: .5, ink: PAL.ink, sw: .12 * s, shade: true, shadeOp: .3, seed: 921 });
  for (const side of [-1, 1]) { ctx.strokeStyle = PAL.gold; ctx.lineWidth = .5 * s; ctx.beginPath(); ctx.arc(x + side * 3 * s, y - 6.5 * s, 1.1 * s, side > 0 ? -1.4 : Math.PI - 1.7, side > 0 ? 1.7 : Math.PI + 1.4, side < 0); ctx.stroke(); }
  if (o.label) txt(o.label, x, y - 6 * s, .9 * s, PAL.ink, { font: 'anton', maxW: 4 * s });
}

;
// ---- src/timeline.js ----
// timeline.js: song structure and timing (from timing.js, generated by tools/make_timing.py from the chosen take's alignment),
// plus the global overlays: label-maker lyric captions, the rubber-stamp date ticker, and xerox grain.

// SEGS: contiguous windows {key, kind: intro|line|chorus|outro, sec, n, text, start, end, date}; LINES: every sung line {sec, n, text, start, end}.
// setTiming() swaps in another take's timing at runtime (shots are keyed to lines, so they re-sync).
let DUR, SEGS, LINES;
function setTiming(tm) { DUR = tm.dur; BPM = tm.bpm; BEAT0 = tm.beat0; SEGS = tm.segs; LINES = tm.lines; }
setTiming(TIMING);

function segAt(t) {
  let lo = 0, hi = SEGS.length - 1;
  if (t < SEGS[0].start) return SEGS[0];
  while (lo < hi) { const mid = (lo + hi + 1) >> 1; if (SEGS[mid].start <= t) lo = mid; else hi = mid - 1; }
  return SEGS[lo];
}
const segByKey = key => SEGS.find(s => s.key === key);
// Window of a whole section, e.g. span('V2') → {start, end} from its first line to the start of the next section.
function span(sec) {
  const ss = SEGS.filter(s => s.sec === sec || s.key === sec);
  return { start: ss[0].start, end: ss[ss.length - 1].end };
}
// Sung lines inside a section (e.g. chorus lines for 'C2'), with their times.
const linesOf = sec => LINES.filter(l => l.sec === sec);
function lineAt(t) {
  for (let i = LINES.length - 1; i >= 0; i--) if (LINES[i].start <= t) return t < LINES[i].end + .35 ? LINES[i] : null;
  return null;
}

// ---------- the words' times, for karaoke fills ----------
// A line's `words` (from tools/word_timing.py, through make_timing.py): each word's [start, end] in centiseconds from the line's
// start. Its words are its text split at spaces and after a hyphen or en dash inside a word, as splitWords splits it.
const splitWords = text => String(text).split(/\s+/).filter(Boolean).flatMap(w => w.split(/(?<=[-–])(?=[A-Za-z0-9])/));
// A line's words' times in seconds, { starts, ends }, or null if it hasn't any.
function wordTimes(ln) {
  if (ln._wt === undefined) {
    ln._wt = ln.words && ln.words.length === splitWords(ln.text).length
      ? { starts: ln.words.map(w => ln.start + w[0] / 100), ends: ln.words.map(w => ln.start + w[1] / 100) } : null;
  }
  return ln._wt;
}
// How much of `text` (a line's text as a caption draws it: its dashes tidied, say, or in capitals) is sung at t, in characters:
// each word sung, and as much of the one being sung as its time has gone by (or, with `quick`, of that many seconds from its
// start: captions that type each word out as it's sung). A word that isn't in the text (a trailing dash a caption drops) counts
// for nothing. `form` turns a word into the text's form (the text's case doesn't matter). Null without the line's words' times.
function charsSung(ln, text, t, { quick = 0, form = w => w } = {}) {
  const w = wordTimes(ln);
  if (!w) return null;
  const hay = text.toLowerCase();
  let from = 0, lit = 0;
  splitWords(ln.text).forEach((word, i) => {
    const needle = form(word).toLowerCase(), a = hay.indexOf(needle, from);
    if (a < 0 || t < w.starts[i]) return;
    from = a + needle.length;
    const dur = quick ? Math.min(quick, w.ends[i] - w.starts[i]) : w.ends[i] - w.starts[i];
    lit = a + needle.length * (dur > 0 ? clamp((t - w.starts[i]) / dur) : 1);
  });
  return lit;
}
// The line a karaoke caption shows at t, as { ln, on, first, last }: like lineAt, but a line with its words' times comes up as
// the one before it finishes (its last word sung), or half a second before its own first word after a rest, so that a word held
// into the next line's start isn't cut off; it goes when the next comes up, or `linger` seconds after its last word (`on` is
// when it came up; `first` and `last`, when its first word starts and its last ends). A line without them is up from its start.
let _captionLines = null;
function captionAt(t, linger = .35) {
  if (_captionLines?.lines !== LINES) {
    let before = -Infinity;
    _captionLines = { lines: LINES, list: LINES.map(ln => {
      const w = wordTimes(ln), first = w ? w.starts[0] : ln.start, last = w ? w.ends.at(-1) : ln.end;
      const on = w ? Math.min(first, Math.max(first - .5, before)) : ln.start;
      before = last;
      return { ln, on, first, last };
    }) };
  }
  const L = _captionLines.list;
  for (let i = L.length - 1; i >= 0; i--) if (L[i].on <= t) return t < Math.min(L[i + 1]?.on ?? Infinity, L[i].last + linger) ? L[i] : null;
  return null;
}

// ---------- overlay switches (a shot may call these each frame) ----------
let _noCaption = false, _noStamp = false, _captionStyle = null, _stampStyle = null;
const hideCaption = () => { _noCaption = true; };
const hideStamp = () => { _noStamp = true; };
const captionStyle = s => { _captionStyle = s; };  // {color, y}; in the vertical video also {size}, and y is the bottom strip's centre
// (the vertical video) stampStyle({x, y, rot}): where this frame's date stamp sits, x being its right edge (default 950, 318)
const stampStyle = s => { _stampStyle = s; };

// ---------- the vertical video's caption: the line on label-maker strips, one under another ----------
// The fewest strips the line fits on, each at most maxW wide, with the words shared out as evenly as they go (a dash stays with the
// word before it). A word too wide for any strip gets one to itself, and the rest share as few strips as they can. Returns the
// strips' texts, with the widest one's width as .w.
const _stripCache = new Map();
function captionStrips(text, size, maxW = 900) {
  const key = `${text}|${size}|${maxW}`;
  let out = _stripCache.get(key);
  if (out) return out;
  const words = [];
  for (const w of String(text).split(/\s+/).filter(Boolean)) /^[—–-]$/.test(w) && words.length ? words[words.length - 1] += ' ' + w : words.push(w);
  const width = s => textW(s.toUpperCase(), size, 'archivo', size * .12) + size * 1.4;
  const n = words.length, memo = new Map();
  // best(i, j): the least possible widest strip setting words i… on j strips, and where they break
  const best = (i, j) => {
    const mk = i * 8 + j;
    if (memo.has(mk)) return memo.get(mk);
    let r;
    if (j === 1) r = { w: width(words.slice(i).join(' ')), cuts: [] };
    else {
      r = { w: Infinity, cuts: [] };
      for (let c = i + 1; c <= n - j + 1; c++) {
        const a = width(words.slice(i, c).join(' ')), b = best(c, j - 1), w = Math.max(a, b.w);
        if (w < r.w - .5) r = { w, cuts: [c, ...b.cuts] };
      }
    }
    memo.set(mk, r);
    return r;
  };
  // the fewest strips that fit; failing that, the fewest that come as narrow as any number of strips can
  let pick = null;
  for (let k = 1; k <= Math.min(4, n); k++) {
    const b = best(0, k);
    if (b.w <= maxW) { pick = { k, ...b }; break; }
    if (!pick || b.w < pick.w - .5) pick = { k, ...b };
  }
  const cuts = [0, ...pick.cuts, n];
  out = cuts.slice(0, -1).map((c, i) => words.slice(c, cuts[i + 1]).join(' '));
  out.w = pick.w;
  _stripCache.set(key, out);
  return out;
}
// The caption's layout: its strips and size. 54 units, or for a line that would take four strips at 54 the largest size that sets
// it on three; and smaller, down to 44, for a word too wide for a strip.
function captionFit(text, size) {
  if (size === undefined) for (size = 54; size > 44 && captionStrips(text, size).length > 3; size--);
  let strips = captionStrips(text, size);
  if (strips.w > 900) { size = Math.max(44, Math.floor(size * 900 / strips.w)); strips = captionStrips(text, size); }
  return { size, strips, w: strips.w };
}

// ---------- date ticker ----------
// Each verse line carries a date string ("JUN 2017", "NOV 17 2023", "SEP 12 2026"). Choruses keep the last date.
function dateAt(t) {
  let cur = null, since = 0;
  for (const s of SEGS) { if (s.start > t) break; if (s.date && s.date !== (cur && cur.date)) { cur = s; since = s.start; } }
  return cur ? { text: cur.date, age: t - since } : null;
}

// ---------- paper grain / xerox texture (built once) ----------
let _grain = null;
function buildGrain() {
  _grain = []; _grain.rs = RS;
  // (the vertical video's grain is built upright, so that it isn't stretched)
  const gw = Math.round((VERT ? 540 : 960) * clamp(RS, .5, 2)), gh = Math.round((VERT ? 960 : 540) * clamp(RS, .5, 2));
  const gl = Math.max(gw, gh);
  for (let v = 0; v < 3; v++) {
    const c = makeCanvas(gw, gh);
    const g = c.getContext('2d'), img = g.createImageData(gw, gh), d = img.data;
    for (let i = 0; i < d.length; i += 4) {
      const n = hash2(v, i >> 2), speck = n > .9985 ? 120 : n > .994 ? 40 : 0;
      const base = 255 - Math.floor(hash2(v + 9, i >> 2) * 18) - speck;
      d[i] = base; d[i + 1] = base - 2; d[i + 2] = base - 8; d[i + 3] = 255;
    }
    g.putImageData(img, 0, 0);
    // photocopy edge darkening
    const vg = g.createRadialGradient(gw / 2, gh / 2, gl * .26, gw / 2, gh / 2, gl * .65);
    vg.addColorStop(0, 'rgb(255 255 255 / 0)'); vg.addColorStop(1, 'rgb(150 140 130 / .55)');
    g.fillStyle = vg; g.fillRect(0, 0, gw, gh);
    _grain.push(c);
  }
}

OVERLAYS.push((t, s) => {
  // caption
  const ln = lineAt(t);
  if (ln && !_noCaption && VERT) {
    // the vertical video: the line on strips of tape stacked up from y (the bottom strip's centre), each stuck on a little askew,
    // the second and third a beat of a hand behind the first; the choruses' and the outro's tape is red
    const st = _captionStyle || {};
    const text = ln.text.replace(/\s*—\s*$/, '').replace(/\s+—\s+/g, ' — ');
    const { size, strips } = captionFit(text, st.size), age = t - ln.start, gap = size * 1.6 + 14;
    strips.forEach((s, i) => {
      const k = easeOut(clamp((age - i * .06) / .12)), j = strips.length - 1 - i;
      if (k <= 0) return;
      const r = hash(ln.start * 100 + i * 7);
      ctx.globalAlpha = k;
      dymo(s, W / 2 + (strips.length > 1 ? (i % 2 ? 1 : -1) * size * .35 : 0), (st.y ?? 1552) - j * gap + (1 - k) * 24, size, st.color ?? (ln.sec[0] === 'C' || ln.sec === 'outro' ? PAL.red : PAL.ink), { rot: (r - .5) * .045 });
    });
    ctx.globalAlpha = 1;
  } else if (ln && !_noCaption) {
    const st = _captionStyle || {};
    const age = t - ln.start, k = easeOut(clamp(age / .12));
    const size = ln.text.length > 34 ? 30 : 36;
    ctx.globalAlpha = k;
    dymo(ln.text.replace(/\s*—\s*$/, '').replace(/\s+—\s+/g, ' — '), W / 2, (st.y ?? 1022) + (1 - k) * 20, size, st.color ?? (ln.sec[0] === 'C' ? PAL.red : PAL.ink), { rot: (hash(ln.start * 100) - .5) * .03 });
    ctx.globalAlpha = 1;
  }
  // date stamp (the vertical video's: top right of the frame's safe area, or where stampStyle() puts it)
  const d = dateAt(t);
  if (d && !_noStamp) {
    const k = clamp(d.age / .18), sv = _stampStyle || {}, rot = sv.rot ?? -.08 + (hstr(d.text) - .5) * .06;
    const ss = VERT ? 50 : 46, tw = textW(d.text, ss, 'mono', VERT ? ss * .061 : 2.8);
    const sx = VERT ? (sv.x ?? 950) - tw / 2 - 40 : 1690, sy = VERT ? sv.y ?? 318 : 92;
    // a torn paper tag behind the stamp keeps it legible on dark scenes
    ctx.save(); ctx.globalAlpha = .9 * clamp(k * 3);
    card(sx, sy, tw + 70 * ss / 46, 96 * ss / 46, PAL.paper, rot, { torn: 2.5, seed: 1301, shadow: [5, 6] });
    ctx.restore();
    stamp(d.text, sx, sy, ss, PAL.red, rot, { pop: k, font: 'mono' });
  }
  // grain
  if (!_grain || _grain.rs !== RS) buildGrain();
  ctx.globalCompositeOperation = 'multiply'; ctx.globalAlpha = .85;
  const g = _grain[_boil % 3], ox = (hash(_boil) - .5) * 40, oy = (hash(_boil + 5) - .5) * 30;
  ctx.drawImage(g, -30 + ox, -20 + oy, W + 60, H + 40);
  ctx.globalAlpha = 1; ctx.globalCompositeOperation = 'source-over';
  _noCaption = false; _noStamp = false; _captionStyle = null; _stampStyle = null;
});

;
// ---- src/band.js ----
// band.js: the chorus world. "CLAWD & THE SCALING LAWS" play a show that grows every chorus.
//   venue(t, level, o)      — backdrop (scaling-curve banner), stage floor, lights, amp stacks. level 1..4 = basement → arena → stadium → singularity.
//                             (o.bannerTitle: false leaves the band's name off the banner, for a shot that sets the hook over it)
//   bandmates(t, level, o)  — the band in standard positions: Clawd (vox, centre), Robo (guitar, left), Huggy (bass, right), Agent (drums, back right).
//   hook(t, o)              — the current chorus line as giant ransom letters (call hideCaption() yourself if you use it).
//   singingNow(t)           — true while a sung line is active (drive mouths).
// Standard stage geometry (world coords, before any camera): floor top y = 800; Clawd at x = 960.

const STAGE_Y = 800;

function singingNow(t) {
  const ln = lineAt(t);
  return !!ln && t < ln.end;
}
// Mouth shape for a singer: opens/closes with eighth notes while singing.
function singMouth(t, big = false) {
  if (!singingNow(t)) return 'smile';
  const k = frac(bpOf(t) * 2);
  return k < .55 ? (big ? 'scream' : 'O') : 'o';
}

// The scaling curve painted on the backdrop banner. level controls steepness; returns nothing.
function curveBanner(t, level, o = {}) {
  const x = o.x ?? 260, y = o.y ?? 110, w = o.w ?? 1400, h = o.h ?? 560;
  scrap(roughen(rectPts(x, y, w, h), 5, 30, 1201, false), o.paper ?? PAL.kraft, { torn: 2, seed: 1202, shadow: [10, 12] });
  halftone(rectPts(x, y, w, h), '#8A6A45', { cell: 16, dot: .2, op: .35 });
  // axes
  marker([[x + 90, y + 60], [x + 90, y + h - 70], [x + w - 60, y + h - 70]], PAL.ink, 9, { rough: 1.5 });
  txt('COMPUTE →', x + w - 200, y + h - 36, 34, PAL.ink, { font: 'marker' });
  txt('CAPABILITY', x + 48, y + h / 2, 34, PAL.ink, { font: 'marker', rot: -TAU / 4 });
  const steep = [2.2, 3.4, 5, 8][clamp(level - 1, 0, 3) | 0];
  const pts = [];
  for (let i = 0; i <= 50; i++) {
    const u = i / 50, v = (Math.exp(u * steep) - 1) / (Math.exp(steep) - 1);
    pts.push([x + 90 + u * (w - 180), y + h - 70 - v * (h - 140) * (level >= 4 ? 1.9 : 1)]);
  }
  const k = o.k ?? 1;
  marker(partial(pts, k), PAL.red, 16, { rough: 1.5, smooth: true });
  marker(partial(pts, k), PAL.pink, 6, { rough: .8, smooth: true, alpha: .8 });
  // dots for data points pulsing on the beat
  for (let i = 0; i < 7; i++) {
    const pt = pts[Math.round(i / 6 * 50)];
    if (i / 6 > k) continue;
    const r = 11 + pulse(t, 5) * (i === 6 ? 10 : 3);
    scrap(ellPts(pt[0], pt[1], r, r, 12), PAL.yellow, { torn: .8, ink: PAL.ink, sw: 3, shadow: false });
  }
  if (o.title !== false) ransom('CLAWD & THE SCALING LAWS', x + w / 2, y + 44, 46, { seed: 77, maxW: w - 260 });
}

// Spotlight cone from above. col with alpha. sweep in radians.
function spot(x, y0, yFloor, width, col, sweep = 0) {
  const tx = x + Math.sin(sweep) * 380;
  ctx.save(); ctx.globalCompositeOperation = 'screen';
  ctx.fillStyle = col;
  tracePath([[x - 30, y0], [x + 30, y0], [tx + width, yFloor], [tx - width, yFloor]]); ctx.fill();
  tracePath(ellPts(tx, yFloor, width * 1.05, 40, 24)); ctx.fill();
  ctx.restore();
}

function venue(t, level = 1, o = {}) {
  const L = clamp(level, 1, 4);
  // back wall
  const walls = [PAL.night, '#2A1E3F', '#1B1433', '#0E0A1C'];
  ctx.fillStyle = o.wall ?? walls[L - 1]; ctx.fillRect(-400, -400, W + 800, H + 800);
  halftone(rectPts(-400, -400, W + 800, STAGE_Y + 400), L >= 3 ? PAL.purple : PAL.blue, { cell: 26, dot: .16, op: .5, multiply: false });
  if (L === 1) { // basement: brick + string lights
    ctx.fillStyle = 'rgb(120 60 50 / .35)';
    for (let r = 0; r < 14; r++) for (let c = -1; c < 17; c++) { const bx = c * 130 + (r % 2) * 65, by = r * 58; ctx.fillRect(bx, by, 122, 50); }
    for (let i = 0; i < 18; i++) { const bx = 60 + i * 105, by = 50 + Math.sin(i * .9) * 22; scrap(ellPts(bx, by, 11, 14, 10), [PAL.yellow, PAL.pink, PAL.mint][i % 3], { torn: .5, shadow: false, op: .65 + .35 * pulse(t + i * .1, 3) }); }
  }
  if (L >= 3) { // lighting truss
    ctx.fillStyle = '#5A5866'; ctx.fillRect(-100, 30, W + 200, 22);
    for (let i = 0; i < 12; i++) scrap(rectPts(80 + i * 160, 48, 50, 40), '#2C2A33', { torn: .5, shadow: false });
  }
  if (o.banner !== false) curveBanner(t, L, { k: o.curveK ?? 1, y: L >= 3 ? 110 : 90, title: o.bannerTitle });
  // light cones
  const beat = bpOf(t);
  const cols = [alpha(PAL.yellow, .16), alpha(PAL.pink, .16), alpha(PAL.sky, .16), alpha(PAL.mint, .14)];
  const nSpots = [2, 3, 5, 6][L - 1];
  for (let i = 0; i < nSpots; i++) spot(200 + i * (1520 / Math.max(1, nSpots - 1)), 40, STAGE_Y + 60, 150 + 40 * L, cols[i % 4], Math.sin(beat * Math.PI / 4 + i * 1.7) * .6);
  // amp stacks / GPU stacks on the sides
  const ampN = [1, 2, 3, 4][L - 1];
  for (const side of [-1, 1]) for (let i = 0; i < ampN; i++) {
    const ax = W / 2 + side * (720 + i * 30), ay = STAGE_Y + 30 - i * 150;
    if (L >= 2 && i > 0) gpu(ax, ay - 70, 13, { label: 'H100', hot: L >= 3 ? pulse(t, 4) * .6 : 0 });
    else amp(ax, ay, 22, { label: 'SCALE' });
  }
  // floor
  scrap(rectPts(-400, STAGE_Y, W + 800, H - STAGE_Y + 400), '#6B4A33', { torn: 1, shadow: false, seed: 1210 });
  ctx.fillStyle = 'rgb(0 0 0 / .18)'; for (let i = 0; i < 9; i++) ctx.fillRect(-400, STAGE_Y + 12 + i * 34, W + 800, 3);
  halftone(rectPts(-400, STAGE_Y, W + 800, 400), PAL.ink, { cell: 10, dot: .25, op: .3 });
  if (L >= 3 && o.fire !== false) { // stage flames at the lip, on the downbeat of each bar
    const bar = frac(bpOf(t) / 4), k = bar < .25 ? easeOut(bar / .25) : 1 - ease((bar - .25) / .5);
    if (k > .02) for (const fx of [120, W - 120]) fire(fx, STAGE_Y + 40, 26 * (L - 1.5), { k, n: 4 });
  }
}

// Band positions (world): Clawd centre, Robo left, Huggy right, drums back-right.
function bandmates(t, level = 1, o = {}) {
  const b = bpOf(t), p = pulse(t, 7), p8 = pulse2(t, 9);
  const hop = Math.max(0, Math.sin(b * Math.PI)) ** 2;
  // drums (back right)
  const dx = o.drumX ?? 1330, dy = STAGE_Y + 10;
  drumkit(dx, dy, 22, { label: o.drumLabel ?? 'LOSS↓' });
  const hit = frac(b) < .5 ? -1 : 1;
  agent(dx, dy - 150 - p * 10, 42, { eyes: level >= 4 ? 'spark' : 'dot', col: '#2A2D38', walk: 0 });
  for (const side of [-1, 1]) { const up = side === hit ? p : 0; marker([[dx + side * 30, dy - 230], [dx + side * (90 + up * 20), dy - 170 - up * 60]], '#E8D7B0', 9, { rough: 0 }); }
  // Robo on guitar (left)
  const rx = o.roboX ?? 520;
  bot(rx, STAGE_Y + 70, 30, { dy: -hop * .6, rot: Math.sin(b * Math.PI / 2) * .06, eyes: level >= 3 ? 'spark' : 'happy', col: '#9FB3C8', aL: .1, aR: -.2 + p8 * .25,
    });
  // guitar body on Robo
  ctx.save(); ctx.translate(rx + 10, STAGE_Y + 70 - 140 - hop * 18); ctx.rotate(-.9);
  scrap(rectPts(-9, -210, 18, 170), '#4A3021', { torn: .3, shadow: false });
  scrap([[-55, -40], [45, -52], [70, 12], [26, 60], [-44, 56], [-72, 6]], PAL.yellow, { torn: .8, ink: PAL.ink, sw: 4, seed: 1220 });
  scrap(ellPts(0, 4, 14, 14, 12), PAL.ink, { torn: .3, shadow: false });
  ctx.restore();
  // Huggy on bass (right)
  const hx = o.huggyX ?? 1520, hy = STAGE_Y - 10 - hop * 26;
  ctx.save(); ctx.translate(hx, hy); ctx.rotate(.45);
  scrap(rectPts(-12, -260, 24, 220), '#3A2415', { torn: .3, shadow: false });
  scrap([[-70, -40], [60, -50], [80, 20], [30, 70], [-60, 60], [-85, 10]], PAL.blue, { torn: .8, ink: PAL.ink, sw: 4, seed: 1221 });
  ctx.restore();
  huggy(hx - 10, hy - 110, 95, { mood: o.huggyMood ?? 'happy', hands: .3 + p * .4 });
  if (o.huggyBandage) { ctx.save(); ctx.translate(hx + 30, hy - 175); ctx.rotate(.5); scrap(rrPts(-50, -16, 100, 32, 12), '#F2D2B5', { torn: .5, shadow: false, ink: PAL.ink, sw: 2 }); ctx.restore(); ctx.save(); ctx.translate(hx + 30, hy - 175); ctx.rotate(-.5); scrap(rrPts(-50, -16, 100, 32, 12), '#F2D2B5', { torn: .5, shadow: false, ink: PAL.ink, sw: 2 }); ctx.restore(); }
  // Clawd (centre)
  if (o.clawd !== false) {
    const cx = o.clawdX ?? 960;
    micStand(cx - 150, STAGE_Y + 60, 26);
    clawd(cx, STAGE_Y + 70, o.u ?? 30, {
      hat: o.hat ?? 'mohawk', eyes: o.eyes ?? (level >= 4 ? 'spark' : 'shades'), mouth: o.mouth ?? singMouth(t, level >= 3), mic: true,
      aR: .5 + p * .5, aL: -.2 + hop * .7, dy: -hop * 1.4, sq: -hop * .08 + p * .05, blush: o.blush, label: o.label,
    });
  }
}

// Current chorus line as giant ransom letters. o.y, o.size, o.lines (override), o.upper.
function hook(t, o = {}) {
  const ln = lineAt(t); if (!ln) return;
  const txtUp = (o.upper === false ? ln.text : ln.text.toUpperCase()).replace(/[—.!,]+$/g, '').replace(/ —/g, '');
  const k = clamp((t - ln.start) / .5);
  ransom(txtUp, o.x ?? W / 2, o.y ?? 170, o.size ?? 76, { pop: k * 1.4, maxW: o.maxW ?? 1700, seed: Math.round(ln.start * 10) });
}

;
// ---- src/vertical.js ----
// vertical.js: the zine video's kit for its vertical frame (1080 × 1920), shared by the chapters' vshot()s. (The plan, the
// conventions and the shot list are in src/VERTICAL.md.)
//   VSAFE                 the frame's safe area: what must be read sits in it (Instagram lays its interface over the rest)
//   vhook(t, ln, o, fall) a chorus line "We didn't start the scaling" as the zine cover's title, word by word as it's sung
//   VBAND                 the band's positions drawn closer together, for bandmates() in the tall frame
//   pitCrowd(t, y, o)     big moshing heads and horns along the foot of the frame: a chorus shot's foreground
//   inStage(t, fn, cx, cy, zoom)   the band's 1920 × 1080 stage world (band.js), framed by a camera, as landscape() frames it

const VSAFE = { x0: 60, x1: 960, y0: 250, y1: 1600 };

// The hook as the cover's title (the same words, seeds and papers as c01_intro's), in three lines: WE DIDN'T / START THE /
// SCALING, each word slamming in on its sung time (the line's word times, where the take has them; else at fixed fractions of the
// line). ln: the sung line (from linesOf()); o.y: the first line's centre (default 330), o.size: the small lines' size (the big
// line is 1.6×), o.x: the centre (default the frame's), o.cut: when the shot cuts away (a word sung later than ≈ a beat before
// it lands then instead, so that the title is up whole before the cut). fall(i) → { dx, dy, rot } moves word i (0–4), e.g. to drop
// it off the page. The caller decides when the hook shows (and calls hideCaption()).
const VHOOK = [
  { w: 'WE', seed: 4101, at: 0, row: 0 }, { w: "DIDN'T", seed: 4207, at: .1, row: 0 }, { w: 'START', seed: 4311, at: .25, row: 1 },
  { w: 'THE', seed: 4419, at: .4, row: 1 }, { w: 'SCALING', seed: 4523, at: .7, row: 2, big: true },
];
const VHOOK_FONTS = ['anton', 'abril', 'archivo', 'bungee', 'mono', 'shrikhand', 'courier', 'bebas', 'rammetto', 'typewriter'];
const VHOOK_LOUD = [PAL.yellow, PAL.pink, PAL.white, PAL.red, PAL.ink, PAL.yellow, PAL.sky];
function vhook(t, ln, o = {}, fall) {
  if (!ln) return;
  const wt = wordTimes(ln), dur = ln.end - ln.start, size = o.size ?? 104, y0 = o.y ?? 330, cx = o.x ?? W / 2;
  const rowY = [y0, y0 + size * 1.22, y0 + size * 1.22 * 2 + size * .42];
  for (let r = 0; r < 3; r++) {
    const row = VHOOK.filter(h => h.row === r), sz = r === 2 ? size * 1.6 : size;
    const ro = h => ({ seed: h.seed, fonts: VHOOK_FONTS, papers: h.big ? VHOOK_LOUD : undefined, maxW: h.big ? 900 : undefined });
    const ws = row.map(h => ransom(h.w, 0, 0, sz, { ...ro(h), pop: 0 }));
    let x = cx - (ws.reduce((a, b) => a + b, 0) + 40 * (row.length - 1)) / 2;
    row.forEach((h, j) => {
      const i = VHOOK.indexOf(h), wx = x + ws[j] / 2; x += ws[j] + 40;
      const at = Math.min(wt && wt.starts.length === VHOOK.length ? wt.starts[i] : ln.start + h.at * dur, (o.cut ?? Infinity) - .45);
      const a = t - at + .03; if (a <= 0) return;
      const f = fall ? fall(i) : null; if (f && f.dy > H + 400) return;
      const wy = rowY[r] - (h.big ? pulse(t, 7) * 10 : 0);
      ctx.save();
      if (f) { ctx.translate(wx + f.dx, wy + f.dy); ctx.rotate(f.rot); ctx.translate(-wx, -wy); }
      ransom(h.w, wx, wy, sz, { ...ro(h), pop: a / .2, jolt: 1.2 + 4 * pulse(t, 9), rot: h.big ? -.025 : (j % 2 ? .02 : -.02) });
      ctx.restore();
    });
  }
}

// The band drawn closer together for the tall frame (bandmates()'s position options: Robo, the drums and Huggy nearer Clawd at 960),
// so that a frame on Clawd holds them too.
const VBAND = { roboX: 650, drumX: 1160, huggyX: 1300 };

// A row of big moshing silhouettes whose heads sit around y, filling the frame's foot (crowd() from cast.js, sized for it).
function pitCrowd(t, y = 1700, o = {}) {
  crowd(y, t, { n: 6, s: 160, col: '#0B0912', hands: .8, horns: true, jump: 1, seed: 983, x0: -60, x1: W + 60, ...o });
}

// Draws fn() in the band's stage world (1920 × 1080; band.js's venue(), bandmates() and STAGE_Y), with world point (cx, cy) at the
// frame's middle, scaled by zoom: landscape() under another name, to say what it's for. At zoom 1 the frame sees 1080 of the
// stage's width, Clawd (x 960) and a little either side; venue() paints the world from y −400 to 1880, so a zoom below about .85
// shows its edges.
const inStage = (t, fn, cx = 960, cy = 600, zoom = 1) => landscape(fn, cx, cy, zoom);

;
// ---- src/ch/c01_intro.js ----
// c01_intro — instrumental intro: a punk-zine cover slaps onto a dark table and assembles on the beat,
// Clawd pops up and throws the horns, then a match labelled ATTENTION lights a fuse whose spark races off-screen right into V1.1.

// The cover's layout, in cover coordinates (origin at the cover's centre; the cover is 1300 × 900 unless `paper` says otherwise).
// src/poster.js swaps in its own to draw the page's poster, whose title has to stay clear of the Play button in the middle, the
// square album cover and the X profile banner.
//   title     the ransom-note title, one entry per line: its words (each keeps its own letters and beat), y and size, and optionally
//             the x of its centre (default 0). The big line gets the loud papers, is squeezed into maxW and bobs on the beat.
//   block     the torn pink block slapped behind the title: its pivot and the rectangle around that pivot
//   swoosh    the red exponential underline: its start point, width and rise
//   band, free, advisory   the centres of the band-name strip, the FREE!* sticker and the PARENTAL ADVISORY sticker (null: none)
//   paper, clawd, feet   optional: the cover's centre and size on the table ([x, y, w, h], screen space before the camera; default
//             [930, 515, 1300, 900]), the x Clawd pops up at from the bottom edge (default 1540) and the y his feet end at (default
//             1074, below the frame)
//   mast      optional: the masthead's text and size ([text, size]; default the full masthead at 36)
// The vertical video's cover is portrait, an A5 zine on the table (its layout, VCOVER, is with the vertical intro below).
let coverLayout = VERT ? null : {
  title: [
    { words: ['WE', "DIDN'T"], y: -262, size: 124 },
    { words: ['START', 'THE'], y: -106, size: 124 },
    { words: ['SCALING'], y: 78, size: 196, big: true, maxW: 1180 },
  ],
  block: { at: [40, -20], rect: [-560, -250, 1120, 470] },
  swoosh: { from: [-560, 262], w: 1150, rise: 400 },
  band: [40, 322], free: [590, -320], advisory: [-450, 350],
};

(() => {
  // The cues below are laid out for a 31-beat intro (8 bars minus V1's pickup beat) and rescale if the window changes.
  const DESIGN_BEATS = 31;
  function grid() {
    const s = segByKey('intro');
    let b0 = Math.ceil(bpOf(s.start) - 1e-6);
    if (onBeat(0, b0) - s.start < .1) b0++;
    const nb = Math.max(12, Math.round(bpOf(s.end)) - b0);
    return { s, at: i => onBeat(0, b0 + Math.round(i * nb / DESIGN_BEATS)) };
  }

  // Cover geometry (screen space before the camera).
  const PAPER = [930, 515, 1300, 900], CROT = -.018;
  const FUSE_Y = 1010, FUSE_X0 = 255, FUSE_X1 = 2450;
  const CLAWD_X0 = 1540, CLAWD_U = 34, CLAWD_FEET = 1074;

  const fuseY = x => FUSE_Y + Math.sin(x * .011 + .8) * 9;
  const fusePts = x1 => { const out = []; for (let x = FUSE_X0; x < x1; x += 30) out.push([x, fuseY(x)]); out.push([x1, fuseY(x1)]); return out; };

  // Seconds-since helper that is 0 before the cue.
  const since = (t, t0) => Math.max(0, t - t0);
  // A decaying slam shake after cue time t0.
  function slamShake(t, t0, amt, dur = .28) {
    const a = t - t0; if (a < 0 || a > dur) return [0, 0];
    const k = 1 - a / dur; const [x, y] = shakeXY(t, amt * k * k, 30); return [x, y];
  }

  // Punk-zine hand with a black sleeve, (x, y) = grip point, ang = direction the held object points.
  function hand(x, y, s, ang, holdFn) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(ang);
    // sleeve runs back off-screen
    scrap([[-1.3 * s, -.95 * s], [-12 * s, -1.5 * s], [-12 * s, 1.5 * s], [-1.3 * s, .95 * s]], PAL.ink, { torn: 1.2, seed: 1901, shadow: [8, 10] });
    scrap(rectPts(-2.1 * s, -1.05 * s, .55 * s, 2.1 * s), '#3A3642', { torn: .6, seed: 1902, shadow: false });
    marker([[-5 * s, -.2 * s], [-4.2 * s, .35 * s]], '#B9B9C4', .16 * s, { rough: 0 }); // safety pin
    if (holdFn) holdFn();
    scrap(rrPts(-1.5 * s, -.95 * s, 2.1 * s, 1.9 * s, .6 * s), SKINS[1], { torn: .8, seed: 1903, shadow: [4, 5], shade: true, shadeOp: .18 });
    scrap(ellPts(.25 * s, -.75 * s, .75 * s, .38 * s, 14, -.25), SKINS[1], { torn: .5, seed: 1904, shadow: false, ink: alpha(PAL.ink, .5), sw: 2 });
    for (let i = 0; i < 3; i++) marker([[-1.2 * s + i * .45 * s, .75 * s], [-1.1 * s + i * .45 * s, .35 * s]], alpha(PAL.ink, .45), 3, { rough: 0 });
    ctx.restore();
  }

  // A kitchen match lying along +x from the origin; lit 0..1 = flame size.
  function matchStick(len, lit, t) {
    scrap(rectPts(0, -7, len, 14), '#E9C98F', { torn: .6, seed: 1911, shadow: [3, 4] });
    const burnt = clamp(lit * 1.4 - .4) * .25;
    if (burnt > 0) scrap(rectPts(len * (1 - burnt), -7, len * burnt, 14), '#2A2220', { torn: .6, seed: 1912, shadow: false });
    scrap(ellPts(len + 6, 0, 20, 15, 16), lit > .02 ? '#3A2522' : PAL.red, { torn: .8, seed: 1913, shadow: false, ink: PAL.ink, sw: 2 });
    if (lit > .02) {
      ctx.save(); ctx.translate(len + 10, 0);
      const f = lit * (1 + jit(.12));
      // flame always points screen-up: undo the parent rotation
      const m = ctx.getTransform(), rot = Math.atan2(m.b, m.a); ctx.rotate(-rot);
      scrap([[-26 * f, 4], [-12 * f, -40 * f], [2, -86 * f + jit(6)], [16 * f, -38 * f], [26 * f, 4], [0, 22 * f]], PAL.orange, { torn: 1, shadow: false, seed: 1914 });
      scrap([[-15 * f, 4], [-6 * f, -26 * f], [2, -56 * f + jit(5)], [9 * f, -24 * f], [15 * f, 4], [0, 14 * f]], PAL.yellow, { torn: .8, shadow: false, seed: 1915 });
      ctx.restore();
    }
  }

  // Matchbox lying on the table, label facing up; the striker strip is the bottom edge.
  function matchbox(x, y, rot, pulseK) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot);
    scrap(rectPts(-110, -70, 220, 140), '#7A2B22', { torn: 1.2, seed: 1921, shadow: [8, 10] });
    scrap(rectPts(-100, -60, 200, 104), PAL.yellow, { torn: .8, seed: 1922, shadow: false });
    scrap(rectPts(-110, 48, 220, 22), '#4A3326', { torn: .8, seed: 1923, shadow: false, tone: { color: PAL.ink, cell: 5, dot: .35, op: .8 } });
    txt('ATTENTION', 0, -18, 44 * (1 + pulseK * .04), PAL.red, { font: 'anton', maxW: 180 });
    txt('SAFETY MATCHES · EST. 2017', 0, 22, 14, PAL.ink, { font: 'typewriter', maxW: 180 });
    ctx.restore();
  }

  // Clawd's nub arm tip with devil horns, replicating clawd()'s arm transform (no rot/flip used).
  function hornsHand(x, y, u, o, side, k) {
    if (k <= 0) return;
    const ang = side > 0 ? (o.aR ?? -.2) : (o.aL ?? -.2), sq = o.sq ?? 0;
    ctx.save(); ctx.translate(x, y + (o.dy ?? 0) * u); ctx.scale(1 + sq * .5, 1 - sq);
    ctx.translate(side * 5 * u, -4.9 * u); ctx.rotate(side * -ang); ctx.translate(side * 2.2 * u, 0);
    const s = backOut(k, 2.6); ctx.scale(s, s);
    for (const dy of [-.62, .62]) scrap(xform(rrPts(side > 0 ? .4 * u : -2.6 * u, -.26 * u, 2.2 * u, .52 * u, .24 * u), 0, dy * u, dy * side * .25, 1, 0, 0), PAL.clawdLt, { torn: .5, seed: 1931 + dy * 10, ink: PAL.ink, sw: .12 * u, shadow: false });
    scrap(rrPts(-.9 * u, -.9 * u, 1.8 * u, 1.8 * u, .45 * u), PAL.clawdLt, { torn: .5, seed: 1933, ink: PAL.ink, sw: .12 * u, shadow: [.1 * u, .15 * u] });
    marker([[-.3 * u, -.1 * u], [.3 * u, .15 * u]], alpha(PAL.ink, .6), .08 * u, { rough: 0 });
    ctx.restore();
  }

  // Parental-advisory style sticker.
  function advisory(x, y, rot, k) {
    if (k <= 0) return;
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot + jit(.004)); const s = lerp(1.7, 1, easeOut(k)); ctx.scale(s, s);
    const w = 360, h = 214;
    scrap(rectPts(-w / 2, -h / 2, w, h), PAL.white, { torn: 3, seed: 1941, shadow: [7, 9], ink: PAL.ink, sw: 7 });
    txt('PARENTAL', 0, -h / 2 + 40, 50, PAL.ink, { font: 'archivo', maxW: w - 50, spacing: 2 });
    scrap(rectPts(-w / 2 + 12, -30, w - 24, 78), PAL.ink, { torn: 1, seed: 1942, shadow: false });
    txt('ADVISORY', 0, 9, 64, PAL.white, { font: 'archivo', maxW: w - 50, spacing: 2 });
    txt('EXPONENTIAL CONTENT', 0, h / 2 - 32, 30, PAL.ink, { font: 'archivo', maxW: w - 44 });
    // a torn-off corner, it's a zine
    scrap([[w / 2 - 38, h / 2 + 6], [w / 2 + 6, h / 2 - 40], [w / 2 + 6, h / 2 + 6]], PAL.cream, { torn: 1, seed: 1943, shadow: false });
    ctx.restore();
  }

  // Scissors that snip on the beat (table dressing). (x, y) = pivot.
  function scissors(x, y, s, rot, open) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot);
    for (const side of [-1, 1]) {
      ctx.save(); ctx.rotate(side * open * .28);
      scrap([[0, -.35 * s], [8 * s, -.1 * s * side - .15 * s], [8.4 * s, 0], [0, .35 * s]], '#C9CCD6', { torn: .4, seed: 1951 + side, ink: PAL.ink, sw: 3, shadow: [4, 6] });
      scrap(ellPts(-3.2 * s, side * 1.3 * s, 2.1 * s, 1.3 * s, 18), side > 0 ? PAL.pink : PAL.red, { torn: .6, seed: 1953 + side, shadow: [4, 6] });
      scrap(ellPts(-3.2 * s, side * 1.3 * s, 1.1 * s, .55 * s, 14), '#1B1826', { torn: .4, seed: 1955 + side, shadow: false });
      ctx.restore();
    }
    scrap(ellPts(0, 0, .5 * s, .5 * s, 10), '#8E919C', { torn: .2, shadow: false });
    ctx.restore();
  }

  // Cassette tape with turning reels (table dressing).
  function cassette(x, y, s, rot, t) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot);
    scrap(rrPts(-5 * s, -3.2 * s, 10 * s, 6.4 * s, .5 * s), '#2B2838', { torn: .8, seed: 1961, shadow: [7, 9] });
    scrap(rectPts(-4.2 * s, -2.6 * s, 8.4 * s, 3.4 * s), PAL.mint, { torn: .6, seed: 1962, shadow: false });
    txt('SIDE A: SCALING', 0, -2.05 * s, .62 * s, PAL.ink, { font: 'marker', maxW: 7.6 * s });
    scrap(rectPts(-2.6 * s, -1.5 * s, 5.2 * s, 1.6 * s), '#1B1826', { torn: .3, shadow: false });
    for (const dx of [-1.6, 1.6]) {
      ctx.save(); ctx.translate(dx * s, -.7 * s); ctx.rotate(t * 5);
      scrap(ellPts(0, 0, .62 * s, .62 * s, 12), PAL.white, { torn: .2, shadow: false });
      ctx.fillStyle = '#1B1826'; for (let i = 0; i < 6; i++) { ctx.rotate(TAU / 6); ctx.fillRect(.2 * s, -.08 * s, .34 * s, .16 * s); }
      ctx.restore();
    }
    ctx.restore();
  }

  // ---------------------------------------------------------------------------------------------------------------
  // the title's words: the beat each lands on, and the seed that picks its letters' fonts and papers
  const WORDS = { WE: { beat: 4, seed: 4101 }, "DIDN'T": { beat: 5, seed: 4207 }, START: { beat: 6, seed: 4311 }, THE: { beat: 7, seed: 4419 }, SCALING: { beat: 8, seed: 4523 } };
  const WORD_GAP = 46;
  const TITLE_FONTS = ['anton', 'abril', 'archivo', 'bungee', 'mono', 'shrikhand', 'courier', 'bebas', 'rammetto', 'typewriter'];
  const LOUD = [PAL.yellow, PAL.pink, PAL.white, PAL.red, PAL.ink, PAL.yellow, PAL.sky];
  const expo = (u, k) => (Math.exp(u * k) - 1) / (Math.exp(k) - 1);
  function swooshPts({ from: [x0, y0], w, rise }) { const out = []; for (let i = 0; i <= 40; i++) { const u = i / 40; out.push([x0 + u * w, y0 - expo(u, 6) * rise]); } return out; }

  function drawCover(t, at) {
    const k0 = t - at(0), L = coverLayout, SWOOSH = swooshPts(L.swoosh), [, , CW, CH] = L.paper ?? PAPER;
    // paper
    scrap(rectPts(-CW / 2, -CH / 2, CW, CH), PAL.cream, { torn: 3, seed: 1801, shadow: [18, 24], shadowCol: 'rgb(0 0 0 / .55)' });
    halftone(rectPts(-CW / 2, -CH / 2, CW, CH), PAL.sky, { cell: 18, dot: .16, op: .35 });
    // a big torn pink block slapped behind the title (beat 2)
    const pk = clamp((t - at(2) + .02) / .12);
    if (pk > 0) {
      ctx.save(); ctx.translate(...L.block.at); ctx.rotate(-.035); const s = lerp(1.25, 1, easeOut(pk)); ctx.scale(s, s);
      scrap(rectPts(...L.block.rect), PAL.pink, { torn: 5, step: 22, seed: 1804, shadow: [8, 10], tone: { color: '#C2186A', cell: 16, dot: .28, op: .55 } });
      ctx.restore();
    }
    // masthead strip, typed on across bar 1
    scrap(rectPts(-CW / 2 + 30, -CH / 2 + 26, CW - 60, 62), PAL.ink, { torn: 1.5, seed: 1802, shadow: false });
    const [mast, mastSize] = L.mast ?? ['THE SCALING ZINE  /  ISSUE #1  /  2017–2026  /  150 BPM', 36];
    const typed = Math.floor(clamp((t - at(1)) / (at(4) - at(1) - .1)) * mast.length);
    if (typed > 0) txt(mast.slice(0, typed) + (typed < mast.length && _boil % 2 ? '_' : ''), -CW / 2 + 60, -CH / 2 + 58, mastSize, PAL.white, { font: 'typewriter', align: 'left', maxW: CW - 260 });
    // title words, one per beat
    for (const { words, x: lx = 0, y, size, big, maxW } of L.title) {
      const ro = w => ({ seed: WORDS[w].seed, maxW: big ? maxW : undefined, papers: big ? LOUD : undefined, fonts: TITLE_FONTS });
      const widths = words.map(w => ransom(w, 0, 0, size, { ...ro(w), pop: 0 }));
      let x = lx - (widths.reduce((a, b) => a + b, 0) + WORD_GAP * (words.length - 1)) / 2;
      words.forEach((w, i) => {
        const cx = x + widths[i] / 2; x += widths[i] + WORD_GAP;
        const a = t - at(WORDS[w].beat) + .03; if (a <= 0) return;
        const bob = big ? -pulse(t, 7) * 12 * clamp((t - at(9)) * 4) : 0;
        ransom(w, cx, y + bob, size, { ...ro(w), pop: a / .2, jolt: 1.2 + 4 * pulse(t, 9), rot: big ? -.025 : (i ? .02 : -.02) });
      });
    }
    // the song's red exponential, as an underline that takes off (beats 9–12)
    const ck = ease((t - at(9)) / (at(12) - at(9) - .1));
    if (ck > 0) {
      const part = partial(SWOOSH, ck);
      marker(part, PAL.ink, 30, { rough: 1.5, smooth: true, alpha: .35 });
      marker(part, PAL.red, 22, { rough: 1.5, smooth: true });
      marker(part, '#FF8FC4', 7, { rough: 1, smooth: true, alpha: .85 });
      for (const u of [.25, .55, .8]) {
        if (u > ck) continue;
        const pt = SWOOSH[Math.round(u * 40)], r = 15 + pulse(t, 5) * 7;
        scrap(ellPts(pt[0], pt[1], r, r, 12), PAL.yellow, { torn: .8, ink: PAL.ink, sw: 4, shadow: false });
      }
      if (ck > .96) { const [ax, ay] = SWOOSH[40], [bx, by] = SWOOSH[37], a = Math.atan2(ay - by, ax - bx), hl = 60;
        scrap([[ax + Math.cos(a) * 20, ay + Math.sin(a) * 20], [ax - Math.cos(a - .5) * hl, ay - Math.sin(a - .5) * hl], [ax - Math.cos(a + .5) * hl, ay - Math.sin(a + .5) * hl]], PAL.red, { torn: 1, shadow: [4, 5] }); }
    }
    // band name strip (beat 12)
    const bk = clamp((t - at(12) + .02) / .14);
    if (bk > 0) {
      ctx.save(); ctx.translate(...L.band); ctx.rotate(.015); const s = lerp(1.5, 1, easeOut(bk)); ctx.scale(s, s);
      scrap(rectPts(-300, -34, 600, 68), PAL.ink, { torn: 2, seed: 1803, shadow: [6, 8] });
      txt('CLAWD & THE SCALING LAWS', 0, 3, 42, PAL.yellow, { font: 'bungee', maxW: 565 });
      tape(285, -28, 76, .6, { seed: 18, h: 28 });
      ctx.restore();
    }
    // FREE* sticker, top-right corner (beat 14)
    const fk = clamp((t - at(14) + .02) / .25);
    if (fk > 0) {
      sticker('FREE!*', ...L.free, 92, PAL.yellow, { pop: fk, rot: .2 + wob(t, .5) * .03, size: 46 });
    }
    // advisory sticker, bottom-left (beat 16), the word EXPONENTIAL circled (beat 18)
    const ak = clamp((t - at(16) + .02) / .14);
    if (L.advisory) {
      const [ax, ay] = L.advisory;
      advisory(ax, ay, -.07, ak);
      if (ak >= 1) circleMark(ax - 5, ay + 75, 190, 36, PAL.red, 6, ease((t - at(18)) / .5), 19);
    }
    // landing flash
    if (k0 > 0 && k0 < .12) { ctx.fillStyle = `rgb(255 255 255 / ${(.4 * (1 - k0 / .12)).toFixed(3)})`; tracePath(rectPts(-CW / 2, -CH / 2, CW, CH)); ctx.fill(); }
  }

  // A cut-out letter left over on the table.
  function scrapLetter(ch, x, y, size, paper, ink, rot, font, seed) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot);
    const w = textW(ch, size, font) + size * .3;
    scrap(ctrRect(0, 0, w, size * 1.2), paper, { torn: 1.5, seed, shadow: [5, 7], shadowCol: 'rgb(0 0 0 / .5)' });
    txt(ch, 0, size * .04, size, ink, { font });
    ctx.restore();
  }

  section('intro', (p, lt, d, t, seg) => {
    hideCaption(); hideStamp();
    const G = grid(), at = G.at, end = G.s.end;
    const [CX, CY, CW, CH] = coverLayout.paper ?? PAPER, CLAWD_X = coverLayout.clawd ?? CLAWD_X0, FEET = coverLayout.feet ?? CLAWD_FEET;

    // --- the spark's position along the fuse (needed by the camera) ---
    const lit = t >= at(26), raceK = clamp((t - at(28)) / (end - at(28)));
    let sx = FUSE_X0;
    if (lit) sx = t < at(28) ? FUSE_X0 + 70 * ease((t - at(26)) / (at(28) - at(26))) : lerp(FUSE_X0 + 70, FUSE_X1, raceK ** 1.7);

    // --- camera: gentle push over the cover, whip down-left to the match (bar 7), then chase the spark right (bar 8) ---
    const push = ease((t - at(4)) / (at(23) - at(4)));
    const toMatch = ease((t - at(24) + .18) / .36);
    const follow = clamp(sx - 150, 560, 1500);
    let camX = lerp(W / 2, t < at(28) ? lerp(470, 560, ease((t - at(26)) / (at(28) - at(26)))) : follow, toMatch);
    let camY = lerp(H / 2 - 10, lerp(810, 830, raceK), toMatch);
    const bump = t > at(0) ? pulse(t, 8) * (beatN(t) % 4 === 0 ? .014 : .006) : 0;
    const zoom = lerp(1 + .035 * push, lerp(1.5, 1.3, ease(raceK)), toMatch) + bump;
    for (const [i, a] of [[0, 22], [8, 16], [12, 6], [16, 10], [22, 8], [25, 7], [26, 10]]) { const [dx, dy] = slamShake(t, at(i), a); camX += dx; camY += dy; }
    camBegin(camX, camY, zoom, 0);

    // --- table ---
    ctx.fillStyle = '#17141F'; ctx.fillRect(-700, -500, W + 1400, H + 1000);
    halftone(rectPts(-700, -500, W + 1400, H + 1000), '#3B2F5C', { cell: 28, dot: .22, op: .9, multiply: false });
    const lamp = ctx.createRadialGradient(CX, CY, 150, CX, CY, 1150);
    lamp.addColorStop(0, 'rgb(255 214 150 / .22)'); lamp.addColorStop(1, 'rgb(255 214 150 / 0)');
    ctx.fillStyle = lamp; ctx.fillRect(-700, -500, W + 1400, H + 1000);
    // table dressing — everything on the table jumps on the beat
    const hopT = (i, amt = 7) => { const ph = hash(i + 1960) * .15; return t > at(0) ? -Math.exp(-frac(bpOf(t) - ph) * 9) * amt : 0; };
    ctx.save(); ctx.translate(0, hopT(1)); scissors(150, 340, 30, .55 + wob(t, .3) * .03, .25 + .75 * (1 - pulse(t, 8)));
    ctx.restore();
    const letters = [['A', 110, 560, 64, PAL.yellow, PAL.ink, -.3, 'abril'], ['!', 215, 640, 58, PAL.red, PAL.white, .25, 'anton'], ['Z', 1840, 820, 60, PAL.white, PAL.blue, .35, 'bungee'],
      ['K', 2080, 690, 70, PAL.pink, PAL.ink, -.2, 'rammetto'], ['?', 2170, 880, 60, PAL.sky, PAL.ink, .3, 'shrikhand']];
    letters.forEach(([ch, x, y, sz, pa, ik, r, f], i) => scrapLetter(ch, x, y + hopT(i + 2, 9), sz, pa, ik, r + hopT(i + 2, .03), f, 1971 + i));
    cassette(1765, 560 + hopT(8, 6), 26, -.2, t);
    for (let i = 0; i < 3; i++) { const px = 40 + i * 42, py = 90 + i * 16; marker([[px, py], [px + 70, py + 120]], '#BFC2CC', 7, { rough: 0 }); circleMark(px + 72, py + 128, 10, 14, '#BFC2CC', 5, 1, 70 + i); }
    const fn = clamp((t - at(15) + .02) / .12);
    if (fn > 0) {
      ctx.save(); ctx.translate(1722, 352); ctx.rotate(.1); const s = lerp(1.5, 1, easeOut(fn)); ctx.scale(s, s);
      scrap(ctrRect(0, 0, 310, 66), PAL.white, { torn: 2.5, seed: 1981, shadow: [6, 8], shadowCol: 'rgb(0 0 0 / .5)' });
      txt('*compute not included', 0, 2, 27, PAL.ink, { font: 'typewriter', maxW: 285 });
      ctx.restore(); tape(1580, 340, 60, -.9, { seed: 1982, h: 26 });
    }
    matchbox(175, 845 + hopT(9, 5), -.12, t > at(24) && t < at(26) ? pulse(t, 6) : 0);

    // --- the cover slaps down on beat 0 ---
    const land = at(0), fall = clamp(t / land);
    ctx.save();
    if (t < land) {
      const k = easeIn(fall);
      ctx.translate(CX, lerp(-620, CY, k)); ctx.rotate(lerp(.22, CROT, k)); ctx.scale(lerp(1.25, 1, k), lerp(1.25, 1, k));
    } else {
      const a = t - land, bounce = Math.exp(-a * 14) * Math.sin(a * 60) * .012;
      ctx.translate(CX, CY); ctx.rotate(CROT); ctx.scale(1 + bounce + pulse(t, 9) * .004, 1 - bounce + pulse(t, 9) * .004);
    }
    drawCover(t, at);
    ctx.restore();
    // masking tape at the corners, beats 1 and 2
    for (const [i, x, y, r] of [[1, CX - CW / 2 + 20, CY - CH / 2 + 12, -.6], [2, CX + CW / 2 - 16, CY + CH / 2 - 20, -.55]]) {
      const k = clamp((t - at(i) + .02) / .1); if (k <= 0) continue;
      ctx.save(); ctx.translate(x, y); ctx.scale(lerp(1.6, 1, easeOut(k)), lerp(1.6, 1, easeOut(k))); tape(0, 0, 170, r, { seed: 30 + i, h: 46 }); ctx.restore();
    }
    // dust puffs when the cover lands
    const la = t - land;
    if (la > 0 && la < .4) {
      const k = la / .4;
      for (let i = 0; i < 14; i++) {
        const side = i % 4, u = hash2(1990, i);
        const bx = side < 2 ? CX - CW / 2 + u * CW : (side === 2 ? CX - CW / 2 : CX + CW / 2), by = side < 2 ? (side ? CY + CH / 2 : CY - CH / 2) : CY - CH / 2 + u * CH;
        const dx = side === 2 ? -1 : side === 3 ? 1 : 0, dy = side === 0 ? -1 : side === 1 ? 1 : 0;
        const r = 16 + 30 * easeOut(k) * (.6 + u);
        scrap(ellPts(bx + dx * 90 * easeOut(k), by + dy * 70 * easeOut(k), r, r * .7, 12), alpha(PAL.cream, .8 * (1 - k)), { torn: 3, seed: 1991 + i, shadow: false });
      }
      txt('SLAP!', CX - CW / 2 + 40, CY + CH / 2 + 20, 80, PAL.yellow, { font: 'marker', rot: -.2, alpha: 1 - easeIn(k), stroke: PAL.ink, sw: 12 });
    }

    // --- fuse along the bottom of the cover ---
    const unburnt = [[sx, fuseY(sx)], ...fusePts(FUSE_X1).filter(([x]) => x > sx)];
    marker(unburnt, '#6E5234', 17, { rough: .8 });
    marker(unburnt, '#B08A5A', 9, { rough: .5 });
    ctx.save(); ctx.strokeStyle = '#5A4128'; ctx.lineWidth = 3; ctx.beginPath();
    for (let x = Math.ceil(sx / 14) * 14; x < FUSE_X1; x += 14) { const y = fuseY(x); ctx.moveTo(x - 4, y + 7); ctx.lineTo(x + 4, y - 7); }
    ctx.stroke(); ctx.restore();
    if (lit) { const burnt = fusePts(sx); if (burnt.length > 1) { marker(burnt, '#2A2530', 10, { rough: 1.5 }); marker(burnt, '#5A5360', 3, { rough: 2, alpha: .7 }); } }
    for (const tx of [620, 1000, 1880, 2150]) if (tx > sx + 20) tape(tx, fuseY(tx), 66, .15 + hash(tx) * .3, { seed: tx, h: 30 });

    if (lit) {
      // smoke puffs left behind (pure: puff i was born when the spark passed its x)
      for (let i = 0; i < 30; i++) {
        const px = FUSE_X0 + 20 + i * 72; if (px > sx) break;
        let born;
        if (px <= FUSE_X0 + 70) born = at(26) + (px - FUSE_X0) / 70 * (at(28) - at(26));
        else born = at(28) + ((px - FUSE_X0 - 70) / (FUSE_X1 - FUSE_X0 - 70)) ** (1 / 1.7) * (end - at(28));
        const age = t - born; if (age < 0 || age > .7) continue;
        const r = 12 + age * 40;
        scrap(ellPts(px + age * 20, fuseY(px) - 10 - age * 70, r, r * .8, 12), alpha('#C9C3D6', .75 * (1 - age / .7)), { torn: 3, seed: 1976 + i, shadow: false });
      }
    }

    // --- Clawd pops up from the bottom edge (bar 6), horns (beat 23), then watches the fuse ---
    if (t > at(20) - .05) {
      const up = kf(t, [[at(20) - .05, 12], [at(20) + .08, 8.3], [at(21) - .02, 8.3], [at(21) + .1, 4.6], [at(22) - .02, 4.6], [at(22) + .3, 0]], k => k < 1 ? elasticOut(k) : 1);
      const hornsK = clamp((t - at(23) + .02) / .18);
      const b = bpOf(t), hop = Math.max(0, Math.sin(b * Math.PI)) ** 2;
      const alarm = t >= at(25);
      // jump arc centred on the moment the spark passes under him
      const tPass = at(28) + ((CLAWD_X - FUSE_X0 - 70) / (FUSE_X1 - FUSE_X0 - 70)) ** (1 / 1.7) * (end - at(28));
      const jk = (t - (tPass - .17)) / .4, passing = jk > 0 && jk < 1 ? Math.sin(jk * Math.PI) : 0;
      const o = {
        hat: 'mohawk', eyes: alarm ? 'wide' : 'shades', mouth: alarm ? (passing > 0 || sx > CLAWD_X ? 'O' : 'o') : (hornsK > 0 ? 'scream' : 'grin'),
        lookX: alarm ? clamp((sx - CLAWD_X) / 400, -1, 1) : 0, lookY: alarm ? .7 : 0,
        aL: hornsK > 0 && !alarm ? 1.2 + pulse(t, 6) * .15 : (t >= at(22) ? .7 : -.2), aR: hornsK > 0 && !alarm ? 1.25 + pulse(t, 6) * .15 : (t >= at(22) ? .6 : -.2),
        dy: -(t >= at(22) + .3 && t < at(25) ? hop * .9 : 0) - passing * 3.8, sq: t >= at(22) + .3 && t < at(25) ? pulse(t, 7) * .06 : -passing * .08,
        sweat: t >= at(26),
      };
      if (alarm) { o.aL = .95 + passing * .4; o.aR = .95 + passing * .4; }
      const fy = FEET + up * CLAWD_U;
      ctx.save(); tracePath(rectPts(-200, -200, W + 400, H + 200)); ctx.clip();
      clawd(CLAWD_X, fy, CLAWD_U, o);
      hornsHand(CLAWD_X, fy, CLAWD_U, o, -1, alarm ? 0 : hornsK);
      hornsHand(CLAWD_X, fy, CLAWD_U, o, 1, alarm ? 0 : hornsK);
      ctx.restore();
      // burst lines when the horns go up
      const hk = t - at(23);
      if (hk > 0 && hk < .5) for (let i = 0; i < 9; i++) {
        const a = -Math.PI / 2 + (i - 4) * .3, r0 = 230 + easeOut(hk / .5) * 70;
        marker([[CLAWD_X + Math.cos(a) * r0, fy - 170 + Math.sin(a) * r0], [CLAWD_X + Math.cos(a) * (r0 + 60), fy - 170 + Math.sin(a) * (r0 + 60)]], PAL.yellow, 10, { rough: 0, alpha: 1 - hk / .5 });
      }
    }

    // --- the match: in from the lower left (beat 24), strikes (25), lights the fuse (26), leaves (27) ---
    if (t > at(24) - .25 && t < at(27) + .15) {
      const head = kf(t, [[at(24) - .25, [-300, 640]], [at(24), [84, 912]], [at(25) - .14, [100, 910]], [at(25), [300, 884]], [at(25) + .18, [318, 912]], [at(26) - .1, [268, 990]], [at(26), [FUSE_X0 - 8, FUSE_Y - 8]], [at(26) + .22, [236, 980]], [at(27) + .15, [-340, 700]]], easeOut);
      const ang = kf(t, [[at(24), .55], [at(25), .4], [at(26), .7], [at(27), .5]]);
      const mlit = t < at(25) ? 0 : clamp((t - at(25)) / .08) * (1 - .7 * clamp((t - at(26) - .15) / .4));
      const L = 240, gx = head[0] - Math.cos(ang) * L, gy = head[1] - Math.sin(ang) * L;
      hand(gx, gy, 44, ang, () => matchStick(L, mlit, t));
      const fa = t - at(25);
      if (fa > 0 && fa < .32) { const k = fa / .32; scrap(burstPts(300, 884, 60 + 150 * easeOut(k), 12, .45, .3), alpha(PAL.yellow, 1 - k), { torn: 2, shadow: false }); txt('SKRITCH!', 420, 760, 64, PAL.yellow, { font: 'marker', rot: -.15, alpha: 1 - easeIn(k), stroke: PAL.ink, sw: 11 }); }
    }

    // --- the spark ---
    if (lit) {
      const sy = fuseY(sx), ia = t - at(26);
      if (ia < .32) { const k = ia / .32; scrap(burstPts(FUSE_X0, FUSE_Y, 60 + 140 * easeOut(k), 10, .4, 1), alpha(PAL.orange, 1 - k), { torn: 2, shadow: false }); txt('FSSST!', FUSE_X0 + 190, FUSE_Y + 80, 70, PAL.orange, { font: 'marker', rot: -.08, alpha: 1 - easeIn(k), stroke: PAL.ink, sw: 12 }); }
      // speed lines during the race
      if (raceK > 0) for (let i = 0; i < 3; i++) { const len = (80 + 380 * raceK) * (1 - Math.abs(i - 1) * .35); marker([[sx - 40 - len, sy - 20 + i * 20], [sx - 44, sy - 20 + i * 20]], alpha(PAL.yellow, .6), 5, { rough: 0 }); }
      const r = 38 + pulse2(t, 8) * 12 + jit(4);
      scrap(burstPts(sx, sy, r * 1.5, 12, .35, t * 11), alpha(PAL.orange, .85), { torn: 1, shadow: false });
      scrap(burstPts(sx, sy, r, 10, .4, -t * 13), PAL.yellow, { torn: .8, shadow: false, ink: PAL.red, sw: 3 });
      for (let i = 0; i < 10; i++) {
        const a = hash2(_boil, i) * TAU, l = 45 + hash2(_boil, i + 50) * 80;
        marker([[sx + Math.cos(a) * 22, sy + Math.sin(a) * 22], [sx + Math.cos(a) * l, sy + Math.sin(a) * l]], i % 2 ? PAL.yellow : PAL.white, 5, { rough: 0 });
      }
    }
    camEnd();
  });

  // =============== the vertical video's intro ===============
  // The cover is an A5 zine, portrait, slapped onto the table and assembled on the beat as in the horizontal intro (bars 1–5, the
  // camera at rest). Bar 6: the camera dips a little and Clawd pops up big from the bottom edge of the frame, horns up on beat 23.
  // Bar 7: the camera drops to the matchbox on the table below the cover; the match strikes and lights the fuse. Bar 8: the spark
  // runs right under Clawd's feet (he hops it), then turns and races DOWN the table, the camera chasing it, and leaves through the
  // bottom of the frame; V1.1's fuse comes in at the top.
  // (VCOVER is in world coordinates, which are the screen's while the camera is at rest; src/poster.js swaps in its own.)
  const VCOVER = {
    paper: [540, 860, 900, 1240],
    mast: ['THE SCALING ZINE  /  ISSUE #1  /  150 BPM', 30],
    title: [
      { words: ['WE', "DIDN'T"], y: -404, size: 112 },
      { words: ['START', 'THE'], y: -258, size: 116 },
      { words: ['SCALING'], y: -66, size: 186, big: true, maxW: 790 },
    ],
    block: { at: [10, -230], rect: [-430, -262, 860, 520] },
    swoosh: { from: [-415, 168], w: 830, rise: 360 },
    band: [0, 262], free: [338, -548], advisory: [-236, 428],
    clawd: 680, feet: 1880, u: 48,
    // the camera in bar 6, while Clawd pops up: [x, y, zoom]
    cam6: [560, 1150, 1],
  };
  if (VERT) coverLayout = VCOVER;

  // the fuse on the table below the cover: in by the matchbox, along under Clawd's feet, then down the table and off
  const vspline = (P, per = 12) => {
    const out = [];
    for (let i = 0; i < P.length - 1; i++) {
      const p0 = P[Math.max(0, i - 1)], p1 = P[i], p2 = P[i + 1], p3 = P[Math.min(P.length - 1, i + 2)];
      for (let j = 0; j < per; j++) {
        const u = j / per, u2 = u * u, u3 = u2 * u;
        out.push([0, 1].map(c => .5 * (2 * p1[c] + (-p0[c] + p2[c]) * u + (2 * p0[c] - 5 * p1[c] + 4 * p2[c] - p3[c]) * u2 + (-p0[c] + 3 * p1[c] - 3 * p2[c] + p3[c]) * u3)));
      }
    }
    out.push(P[P.length - 1]);
    return out;
  };
  const VMATCH = [170, 1660], VDX = VMATCH[0] - 175, VDY = VMATCH[1] - 845;   // the match's moves are the horizontal's, moved
  const VFUSE = vspline([[FUSE_X0 + VDX, FUSE_Y + VDY], [420, 1858], [600, 1884], [790, 1900], [930, 1975], [975, 2180], [905, 2430], [760, 2680], [590, 2930], [380, 3200], [200, 3620]]);
  const VFUSE_L = VFUSE.reduce((a, p, i) => i ? a + Math.hypot(p[0] - VFUSE[i - 1][0], p[1] - VFUSE[i - 1][1]) : 0, 0);
  const vfuseAt = k => partial(VFUSE, clamp(k, .0005, 1)).at(-1);
  // how far along the fuse (0..1) the point nearest x is, on its first run along under Clawd
  const vfuseK = x => { let best = 0, bd = Infinity, acc = 0; VFUSE.forEach((p, i) => { if (i) acc += Math.hypot(p[0] - VFUSE[i - 1][0], p[1] - VFUSE[i - 1][1]); if (p[1] < 1960 && Math.abs(p[0] - x) < bd) { bd = Math.abs(p[0] - x); best = acc / VFUSE_L; } }); return best; };

  vshot('intro', (p, lt, d, t) => {
    hideCaption(); hideStamp();
    const G = grid(), at = G.at, end = G.s.end, L = coverLayout;
    const [CX, CY, CW, CH] = L.paper, CLX = L.clawd, FEET = L.feet, U = L.u;

    // --- the spark: a slow first burn by the matchbox (beats 26–28), then the race down the fuse (bar 8) ---
    const lit = t >= at(26), raceK = clamp((t - at(28)) / (end - at(28))), k0 = 70 / VFUSE_L;
    const sk = !lit ? 0 : t < at(28) ? k0 * ease((t - at(26)) / (at(28) - at(26))) : lerp(k0, 1, raceK ** 1.7);
    const [sx, sy] = vfuseAt(sk);

    // --- camera: at rest over the cover, a dip for Clawd (bar 6), down to the match (bar 7), then after the spark (bar 8) ---
    const push = ease((t - at(4)) / (at(23) - at(4)));
    const P0 = [W / 2, H / 2, 1 + .035 * push], P1 = L.cam6;
    const P2 = [lerp(300, 360, ease((t - at(26)) / (at(28) - at(26)))), 1730, 1.6];
    const P3 = [clamp(sx - 40, 360, 660), Math.min(2560, Math.max(1730, sy - 140 - 300 * raceK)), lerp(1.6, 1.2, ease(raceK))];
    const mix = (a, b, k) => a.map((v, i) => lerp(v, b[i], k));
    let [camX, camY, zoom] = mix(mix(mix(P0, P1, ease((t - at(20) + .12) / .3)), P2, ease((t - at(24) + .18) / .36)), P3, ease((t - at(28)) / .3));
    zoom += t > at(0) ? pulse(t, 8) * (beatN(t) % 4 === 0 ? .014 : .006) : 0;
    for (const [i, a] of [[0, 22], [8, 16], [12, 6], [16, 10], [20, 10], [22, 8], [25, 7], [26, 10]]) { const [dx, dy] = slamShake(t, at(i), a); camX += dx; camY += dy; }
    camBegin(camX, camY, zoom, 0);

    // --- the table ---
    ctx.fillStyle = '#17141F'; ctx.fillRect(-700, -900, W + 1400, 4900);
    halftone(rectPts(-700, -900, W + 1400, 4900), '#3B2F5C', { cell: 28, dot: .22, op: .9, multiply: false });
    const lamp = ctx.createRadialGradient(CX, CY, 150, CX, CY, 1250);
    lamp.addColorStop(0, 'rgb(255 214 150 / .22)'); lamp.addColorStop(1, 'rgb(255 214 150 / 0)');
    ctx.fillStyle = lamp; ctx.fillRect(-700, -900, W + 1400, 4900);
    const hopT = (i, amt = 7) => { const ph = hash(i + 1960) * .15; return t > at(0) ? -Math.exp(-frac(bpOf(t) - ph) * 9) * amt : 0; };
    ctx.save(); ctx.translate(0, hopT(1)); scissors(120, 120, 26, .35 + wob(t, .3) * .03, .25 + .75 * (1 - pulse(t, 8))); ctx.restore();
    for (let i = 0; i < 3; i++) { const px = 820 + i * 42, py = 40 + i * 16; marker([[px, py], [px + 70, py + 120]], '#BFC2CC', 7, { rough: 0 }); circleMark(px + 72, py + 128, 10, 14, '#BFC2CC', 5, 1, 70 + i); }
    const letters = [['A', 70, 1560, 64, PAL.yellow, PAL.ink, -.3, 'abril'], ['!', 990, 1590, 58, PAL.red, PAL.white, .25, 'anton'], ['Z', 600, 2010, 60, PAL.white, PAL.blue, .35, 'bungee'],
      ['K', 640, 2330, 70, PAL.pink, PAL.ink, -.2, 'rammetto'], ['?', 820, 2980, 60, PAL.sky, PAL.ink, .3, 'shrikhand']];
    letters.forEach(([ch, x, y, sz, pa, ik, r, f], i) => scrapLetter(ch, x, y + hopT(i + 2, 9), sz, pa, ik, r + hopT(i + 2, .03), f, 1971 + i));
    cassette(300, 2520 + hopT(8, 6), 26, .25, t);
    // the rest of the zine-making kit, further down the table: a stack of fresh photocopies and the stapler
    for (let i = 3; i >= 0; i--) {
      ctx.save(); ctx.translate(205 + i * 9, 2270 - i * 7 + hopT(10 + i, 4)); ctx.rotate(.1 - i * .07);
      scrap(rectPts(-120, -160, 240, 320), i ? '#E8E2D2' : PAL.white, { torn: 1.5, seed: 1890 + i, shadow: [5, 7], shadowCol: 'rgb(0 0 0 / .5)' });
      if (!i) {
        txt('THE SCALING', 0, -110, 30, PAL.ink, { font: 'archivo', maxW: 200 });
        txt('ZINE #1', 0, -76, 30, PAL.red, { font: 'archivo' });
        halftone(rectPts(-95, -50, 190, 120), PAL.ink, { cell: 9, dot: .32, op: .55 });
        ctx.fillStyle = 'rgb(28 26 31 / .45)'; for (let r = 0; r < 4; r++) ctx.fillRect(-95, 84 + r * 16, r === 3 ? 110 : 190, 5);
      }
      ctx.restore();
    }
    {
      const bite = 1 - pulse(t, 7);
      ctx.save(); ctx.translate(470, 2120 + hopT(14, 6)); ctx.rotate(-.42);
      scrap(rrPts(-150, -12, 300, 52, 14), '#2B2838', { torn: .8, seed: 1895, shadow: [7, 9], shadowCol: 'rgb(0 0 0 / .5)' });
      ctx.save(); ctx.translate(-130, 0); ctx.rotate(-.1 * bite);
      scrap(rrPts(-10, -44, 290, 40, 14), PAL.red, { torn: .8, seed: 1896, shadow: [5, 6], ink: PAL.ink, sw: 3, shade: '#8C1A12', shadeOp: .3 });
      ctx.restore();
      ctx.restore();
    }
    const fn = clamp((t - at(15) + .02) / .12);
    if (fn > 0) {
      ctx.save(); ctx.translate(650, 186); ctx.rotate(.06); const s = lerp(1.5, 1, easeOut(fn)); ctx.scale(s, s);
      scrap(ctrRect(0, 0, 310, 66), PAL.white, { torn: 2.5, seed: 1981, shadow: [6, 8], shadowCol: 'rgb(0 0 0 / .5)' });
      txt('*compute not included', 0, 2, 27, PAL.ink, { font: 'typewriter', maxW: 285 });
      ctx.restore(); tape(800, 166, 60, -.9, { seed: 1982, h: 26 });
    }
    matchbox(VMATCH[0], VMATCH[1] + hopT(9, 5), -.12, t > at(24) && t < at(26) ? pulse(t, 6) : 0);

    // --- the cover slaps down on beat 0 ---
    const land = at(0), fall = clamp(t / land);
    ctx.save();
    if (t < land) {
      const k = easeIn(fall);
      ctx.translate(CX, lerp(-900, CY, k)); ctx.rotate(lerp(.22, CROT, k)); ctx.scale(lerp(1.25, 1, k), lerp(1.25, 1, k));
    } else {
      const a = t - land, bounce = Math.exp(-a * 14) * Math.sin(a * 60) * .012;
      ctx.translate(CX, CY); ctx.rotate(CROT); ctx.scale(1 + bounce + pulse(t, 9) * .004, 1 - bounce + pulse(t, 9) * .004);
    }
    drawCover(t, at);
    ctx.restore();
    for (const [i, x, y, r] of [[1, CX - CW / 2 + 20, CY - CH / 2 + 12, -.6], [2, CX + CW / 2 - 16, CY + CH / 2 - 20, -.55]]) {
      const k = clamp((t - at(i) + .02) / .1); if (k <= 0) continue;
      ctx.save(); ctx.translate(x, y); ctx.scale(lerp(1.6, 1, easeOut(k)), lerp(1.6, 1, easeOut(k))); tape(0, 0, 170, r, { seed: 30 + i, h: 46 }); ctx.restore();
    }
    const la = t - land;
    if (la > 0 && la < .4) {
      const k = la / .4;
      for (let i = 0; i < 14; i++) {
        const side = i % 4, u = hash2(1990, i);
        const bx = side < 2 ? CX - CW / 2 + u * CW : (side === 2 ? CX - CW / 2 : CX + CW / 2), by = side < 2 ? (side ? CY + CH / 2 : CY - CH / 2) : CY - CH / 2 + u * CH;
        const dx = side === 2 ? -1 : side === 3 ? 1 : 0, dy = side === 0 ? -1 : side === 1 ? 1 : 0;
        const r = 16 + 30 * easeOut(k) * (.6 + u);
        scrap(ellPts(bx + dx * 90 * easeOut(k), by + dy * 70 * easeOut(k), r, r * .7, 12), alpha(PAL.cream, .8 * (1 - k)), { torn: 3, seed: 1991 + i, shadow: false });
      }
      txt('SLAP!', CX - CW / 2 + 150, CY + CH / 2 + 70, 96, PAL.yellow, { font: 'marker', rot: -.2, alpha: 1 - easeIn(k), stroke: PAL.ink, sw: 13 });
    }

    // --- the fuse ---
    const unburnt = [[sx, sy], ...partial([...VFUSE].reverse(), 1 - sk).reverse().slice(1)];
    marker(unburnt, '#6E5234', 17, { rough: .8 });
    marker(unburnt, '#B08A5A', 9, { rough: .5 });
    ctx.save(); ctx.strokeStyle = '#5A4128'; ctx.lineWidth = 3; ctx.beginPath();
    for (let i = 1; i < unburnt.length; i += 2) { const [x, y] = unburnt[i], [px, py] = unburnt[i - 1], a = Math.atan2(y - py, x - px); ctx.moveTo(x - Math.cos(a) * 4 - Math.sin(a) * 7, y - Math.sin(a) * 4 + Math.cos(a) * 7); ctx.lineTo(x + Math.cos(a) * 4 + Math.sin(a) * 7, y + Math.sin(a) * 4 - Math.cos(a) * 7); }
    ctx.stroke(); ctx.restore();
    if (lit) { const burnt = partial(VFUSE, sk); if (burnt.length > 1) { marker(burnt, '#2A2530', 10, { rough: 1.5 }); marker(burnt, '#5A5360', 3, { rough: 2, alpha: .7 }); } }
    for (const [k, r] of [[.17, .2], [.42, 1.3], [.62, 1.7], [.84, 1.2]]) if (k > sk + .01) { const [x, y] = vfuseAt(k); tape(x, y, 66, r + hash(k * 100) * .3, { seed: k * 100 | 0, h: 30 }); }
    if (lit) {
      // smoke puffs left behind (pure: puff i was born when the spark passed it)
      for (let i = 0; i < 40; i++) {
        const pk = (i + .3) / 40; if (pk > sk) break;
        const born = pk <= k0 ? at(26) + pk / k0 * (at(28) - at(26)) : at(28) + ((pk - k0) / (1 - k0)) ** (1 / 1.7) * (end - at(28));
        const age = t - born; if (age < 0 || age > .7) continue;
        const [px, py] = vfuseAt(pk), r = 12 + age * 40;
        scrap(ellPts(px + age * 30, py - 10 - age * 70, r, r * .8, 12), alpha('#C9C3D6', .75 * (1 - age / .7)), { torn: 3, seed: 1976 + i, shadow: false });
      }
    }

    // --- Clawd pops up from the bottom edge (bar 6), horns (beat 23), then watches the fuse and hops the spark ---
    if (t > at(20) - .05) {
      const up = kf(t, [[at(20) - .05, 12], [at(20) + .08, 8.3], [at(21) - .02, 8.3], [at(21) + .1, 4.6], [at(22) - .02, 4.6], [at(22) + .3, 0]], k => k < 1 ? elasticOut(k) : 1);
      const hornsK = clamp((t - at(23) + .02) / .18);
      const b = bpOf(t), hop = Math.max(0, Math.sin(b * Math.PI)) ** 2;
      const alarm = t >= at(25);
      const kPass = vfuseK(CLX), tPass = kPass <= k0 ? at(26) : at(28) + ((kPass - k0) / (1 - k0)) ** (1 / 1.7) * (end - at(28));
      const jk = (t - (tPass - .17)) / .4, passing = jk > 0 && jk < 1 ? Math.sin(jk * Math.PI) : 0;
      const o = {
        hat: 'mohawk', eyes: alarm ? 'wide' : 'shades', mouth: alarm ? (passing > 0 || sk > kPass ? 'O' : 'o') : (hornsK > 0 ? 'scream' : 'grin'),
        lookX: alarm ? clamp((sx - CLX) / 400, -1, 1) : 0, lookY: alarm ? .7 : 0,
        aL: hornsK > 0 && !alarm ? 1.2 + pulse(t, 6) * .15 : (t >= at(22) ? .7 : -.2), aR: hornsK > 0 && !alarm ? 1.25 + pulse(t, 6) * .15 : (t >= at(22) ? .6 : -.2),
        dy: -(t >= at(22) + .3 && t < at(25) ? hop * .9 : 0) - passing * 3.8, sq: t >= at(22) + .3 && t < at(25) ? pulse(t, 7) * .06 : -passing * .08,
        sweat: t >= at(26),
      };
      if (alarm) { o.aL = .95 + passing * .4; o.aR = .95 + passing * .4; }
      const fy = FEET + up * U, clipY = P1[1] + H / 2 / P1[2];
      ctx.save(); tracePath(rectPts(-400, -400, W + 800, clipY + 400)); ctx.clip();
      clawd(CLX, fy, U, o);
      hornsHand(CLX, fy, U, o, -1, alarm ? 0 : hornsK);
      hornsHand(CLX, fy, U, o, 1, alarm ? 0 : hornsK);
      ctx.restore();
      const hk = t - at(23);
      if (hk > 0 && hk < .5) for (let i = 0; i < 9; i++) {
        const a = -Math.PI / 2 + (i - 4) * .3, r0 = (7.5 + easeOut(hk / .5) * 1.9) * U, cy = fy - 5.4 * U;
        marker([[CLX + Math.cos(a) * r0, cy + Math.sin(a) * r0], [CLX + Math.cos(a) * (r0 + 1.7 * U), cy + Math.sin(a) * (r0 + 1.7 * U)]], PAL.yellow, 13, { rough: 0, alpha: 1 - hk / .5 });
      }
    }

    // --- the match: in from the lower left (beat 24), strikes (25), lights the fuse (26), leaves (27) ---
    if (t > at(24) - .25 && t < at(27) + .15) {
      const mv = ([x, y]) => [x + VDX, y + VDY];
      const head = kf(t, [[at(24) - .25, mv([-300, 640])], [at(24), mv([84, 912])], [at(25) - .14, mv([100, 910])], [at(25), mv([300, 884])], [at(25) + .18, mv([318, 912])], [at(26) - .1, mv([268, 990])], [at(26), mv([FUSE_X0 - 8, FUSE_Y - 8])], [at(26) + .22, mv([236, 980])], [at(27) + .15, mv([-340, 700])]], easeOut);
      const ang = kf(t, [[at(24), .55], [at(25), .4], [at(26), .7], [at(27), .5]]);
      const mlit = t < at(25) ? 0 : clamp((t - at(25)) / .08) * (1 - .7 * clamp((t - at(26) - .15) / .4));
      const ML = 240, gx = head[0] - Math.cos(ang) * ML, gy = head[1] - Math.sin(ang) * ML;
      hand(gx, gy, 44, ang, () => matchStick(ML, mlit, t));
      const fa = t - at(25);
      if (fa > 0 && fa < .32) { const k = fa / .32; scrap(burstPts(300 + VDX, 884 + VDY, 60 + 150 * easeOut(k), 12, .45, .3), alpha(PAL.yellow, 1 - k), { torn: 2, shadow: false }); txt('SKRITCH!', 360 + VDX, 730 + VDY, 70, PAL.yellow, { font: 'marker', rot: -.15, alpha: 1 - easeIn(k), stroke: PAL.ink, sw: 11 }); }
    }

    // --- the spark ---
    if (lit) {
      const ia = t - at(26);
      if (ia < .32) { const k = ia / .32; const [fx, fy] = VFUSE[0]; scrap(burstPts(fx, fy, 60 + 140 * easeOut(k), 10, .4, 1), alpha(PAL.orange, 1 - k), { torn: 2, shadow: false }); txt('FSSST!', fx + 120, fy + 110, 76, PAL.orange, { font: 'marker', rot: -.08, alpha: 1 - easeIn(k), stroke: PAL.ink, sw: 12 }); }
      // speed lines trailing back along the fuse during the race
      if (raceK > 0) for (let i = 0; i < 3; i++) {
        const back = (.012 + .07 * raceK) * (1 - Math.abs(i - 1) * .35), [ax, ay] = vfuseAt(sk - back), [bx, by] = vfuseAt(sk - .004), a = Math.atan2(by - ay, bx - ax);
        const nx = -Math.sin(a) * (i - 1) * 20, ny = Math.cos(a) * (i - 1) * 20;
        marker([[ax + nx, ay + ny], [bx + nx, by + ny]], alpha(PAL.yellow, .6), 5, { rough: 0 });
      }
      const r = 40 + pulse2(t, 8) * 12 + jit(4);
      scrap(burstPts(sx, sy, r * 1.5, 12, .35, t * 11), alpha(PAL.orange, .85), { torn: 1, shadow: false });
      scrap(burstPts(sx, sy, r, 10, .4, -t * 13), PAL.yellow, { torn: .8, shadow: false, ink: PAL.red, sw: 3 });
      for (let i = 0; i < 10; i++) {
        const a = hash2(_boil, i) * TAU, l = 45 + hash2(_boil, i + 50) * 80;
        marker([[sx + Math.cos(a) * 22, sy + Math.sin(a) * 22], [sx + Math.cos(a) * l, sy + Math.sin(a) * l]], i % 2 ? PAL.yellow : PAL.white, 5, { rough: 0 });
      }
    }
    camEnd();
  });
})();

;
// ---- src/ch/c02_v1.js ----
// c02_v1 — Verse 1 (2017 → Oct 2024): sixteen cut-paper news vignettes, hard-cut on each sung line.
// Palette leans yellow / pink / blue on cream; consecutive shots alternate dominant colour and composition.
(() => {
  // ---------- private helpers ----------
  const fill = c => { ctx.fillStyle = c; ctx.fillRect(-300, -300, W + 600, H + 600); };
  // Entrance "paper slap": a quick settle (< 0.15 s) wrapped round the shot's own camera move.
  const enter = (lt, cx = W / 2, cy = H / 2, zoom = 1, rot = 0, dir = 1) => {
    const k = easeOut(clamp(lt / .14));
    camBegin(cx, cy, zoom * (1 + .07 * (1 - k)), rot + dir * .03 * (1 - k));
  };
  // lt of the k-th beat at/after the window start (verse lines often start on an off-beat pickup).
  const beatLt = (t, lt, k) => { const s = t - lt; return onBeat(0, Math.ceil(bpOf(s) - .02) + k) - s; };
  const EIGHTH = () => beatLen() / 2;
  // Sunburst wedges.
  function rays(cx, cy, n, col, rot = 0, R = 2600) {
    ctx.fillStyle = col; ctx.beginPath();
    for (let i = 0; i < n; i++) {
      const a0 = rot + i / n * TAU, a1 = a0 + TAU / n / 2;
      ctx.moveTo(cx, cy); ctx.lineTo(cx + Math.cos(a0) * R, cy + Math.sin(a0) * R); ctx.lineTo(cx + Math.cos(a1) * R, cy + Math.sin(a1) * R); ctx.closePath();
    }
    ctx.fill();
  }
  // Catmull-Rom spline through control points.
  function spline(P, per = 10) {
    const out = [];
    for (let i = 0; i < P.length - 1; i++) {
      const p0 = P[Math.max(0, i - 1)], p1 = P[i], p2 = P[i + 1], p3 = P[Math.min(P.length - 1, i + 2)];
      for (let j = 0; j < per; j++) {
        const u = j / per, u2 = u * u, u3 = u2 * u;
        out.push([0, 1].map(c => .5 * (2 * p1[c] + (-p0[c] + p2[c]) * u + (2 * p0[c] - 5 * p1[c] + 4 * p2[c] - p3[c]) * u2 + (-p0[c] + 3 * p1[c] - 3 * p2[c] + p3[c]) * u3)));
      }
    }
    out.push(P[P.length - 1]);
    return out;
  }
  const at = (pts, k) => partial(pts, clamp(k, .0005, 1)).at(-1);
  const angAt = (pts, k) => { const a = at(pts, Math.max(.0005, k - .01)), b = at(pts, Math.min(1, k + .01)); return Math.atan2(b[1] - a[1], b[0] - a[0]); };
  const dot = (x, y, r, col) => { ctx.fillStyle = col; tracePath(ellPts(x, y, r, r, 14)); ctx.fill(); };
  const glow = (x, y, r, col, a = .6) => {
    const g = ctx.createRadialGradient(x, y, 0, x, y, r);
    g.addColorStop(0, alpha(col, a)); g.addColorStop(1, alpha(col, 0));
    ctx.fillStyle = g; ctx.fillRect(x - r, y - r, r * 2, r * 2);
  };
  // A cut-paper forearm + hand reaching in from off-frame; (x, y) is the palm, the fingers point along `ang`.
  // o: sleeve, stripes (pinstripe colour), cuff (colour | false), skin, pose ('flat' | 'point' | 'fist'), ring, len, seed.
  function limb(x, y, ang, s, o = {}) {
    const len = o.len ?? 1500, skin = o.skin ?? SKINS[0], seed = o.seed ?? 2000, edge = alpha(PAL.ink, .4);
    ctx.save(); ctx.translate(x, y); ctx.rotate(ang);
    scrap(rectPts(-len, -.66 * s, len - .5 * s, 1.32 * s), o.sleeve ?? PAL.blue, { torn: .8, seed, shadow: [.15 * s, .22 * s] });
    if (o.stripes) { ctx.fillStyle = o.stripes; for (let i = -2; i <= 2; i++) ctx.fillRect(-len, i * .24 * s - 1, len - .55 * s, 2.5); }
    if (o.cuff !== false) scrap(rectPts(-.95 * s, -.72 * s, .45 * s, 1.44 * s), o.cuff ?? PAL.white, { torn: .4, seed: seed + 1, shadow: false });
    scrap(rrPts(-.62 * s, -.56 * s, 1.1 * s, 1.12 * s, .3 * s), skin, { torn: .4, seed: seed + 2, shadow: false, ink: edge, sw: 1.5 });
    const pose = o.pose ?? 'flat';
    for (let i = 0; i < 4; i++) {
      const ext = pose === 'flat' || (pose === 'point' && i === 0) ? 1 : .22;
      const fl = (.92 - Math.abs(i - 1.2) * .13) * s * ext;
      scrap(rrPts(.28 * s, -.52 * s + i * .27 * s, fl + .12 * s, .25 * s, .12 * s), skin, { torn: .3, seed: seed + 3 + i, shadow: false, ink: edge, sw: 1.5 });
    }
    scrap(xform(rrPts(-.25 * s, .28 * s, .72 * s, .28 * s, .13 * s), 0, 0, pose === 'flat' ? .35 : .1, 1, -.25 * s, .42 * s), skin, { torn: .3, seed: seed + 9, shadow: false, ink: edge, sw: 1.5 });
    if (o.ring) scrap(rectPts(.55 * s, .3 * s, .14 * s, .28 * s), o.ring, { torn: .2, shadow: false });
    ctx.restore();
  }

  // ---------- V1.1: "Attention" lit the fuse → bomb labelled TRANSFORMER ----------
  function bombFace(x, y, r, o) {
    const NUB = o.nub;
    ctx.save(); ctx.translate(x + Math.cos(NUB) * r * .92, y + Math.sin(NUB) * r * .92); ctx.rotate(NUB + TAU / 4);
    scrap(rectPts(-r * .2, -r * .24, r * .4, r * .32), '#4A4E58', { torn: .6, seed: 2101, ink: PAL.ink, sw: 4 });
    ctx.restore();
    scrap(ellPts(x, y, r, r, 44), '#25272F', { torn: 1.4, seed: 2102, shade: true, shadeOp: .5, shadow: [14, 18] });
    ctx.fillStyle = 'rgb(255 255 255 / .2)'; tracePath(ellPts(x - r * .45, y - r * .48, r * .28, r * .13, 16, -.75)); ctx.fill();
    ctx.fillStyle = 'rgb(255 255 255 / .12)'; tracePath(ellPts(x - r * .66, y - r * .18, r * .07, r * .05, 10)); ctx.fill();
    // face
    const ex = r * .3, ey = y - r * .12;
    if (o.squeeze) {
      for (const s of [-1, 1]) marker([[x + s * ex - s * r * .13, ey - r * .1], [x + s * ex + s * r * .08, ey], [x + s * ex - s * r * .13, ey + r * .1]], PAL.white, r * .05, { rough: 0 });
      // gritted teeth
      scrap(rrPts(x - r * .22, y + r * .1, r * .44, r * .16, r * .05), PAL.white, { torn: .3, shadow: false });
      ctx.fillStyle = PAL.ink; for (let i = 1; i < 4; i++) ctx.fillRect(x - r * .22 + i * r * .11 - 1.5, y + r * .1, 3, r * .16);
    } else {
      for (const s of [-1, 1]) {
        scrap(ellPts(x + s * ex, ey, r * .17, r * .21, 20), PAL.white, { torn: .5, seed: 2103 + s, shadow: false, ink: PAL.ink, sw: 3 });
        dot(x + s * ex + o.lx * r * .07, ey + o.ly * r * .08, r * .075, PAL.ink);
        marker([[x + s * ex - s * r * .16, ey - r * (.28 + o.worry * .08)], [x + s * ex + s * r * .12, ey - r * (.3 + o.worry * .02)]], PAL.white, r * .045, { rough: 0 });
      }
      scrap(ellPts(x, y + r * .2, r * .07, r * (.06 + o.worry * .04), 12), PAL.ink, { torn: .2, shadow: false, ink: PAL.white, sw: 3 });
    }
    if (o.sweat) scrap([[x + r * .62, y - r * .5], [x + r * .7, y - r * .3], [x + r * .62, y - r * .24], [x + r * .54, y - r * .3]], PAL.sky, { torn: .3, ink: PAL.ink, sw: 3, shadow: false });
    txt('TRANSFORMER', x, y + r * .52, r * .2, PAL.yellow, { font: 'anton', maxW: r * 1.25, spacing: 2 });
  }

  line('V1', 1, (p, lt, d, t) => {
    const hitT = d * .66, k = clamp(lt / hitT), hit = lt >= hitT, since = lt - hitT;
    const BX = 1180, BY = 570, BR = 235, NUB = -2.25;
    const endX = BX + Math.cos(NUB) * BR * 1.14, endY = BY + Math.sin(NUB) * BR * 1.14;
    const F = spline([[-40, 820], [150, 905], [380, 870], [520, 720], [640, 540], [780, 400], [920, 330], [endX, endY]], 14);
    fill(PAL.yellow);
    rays(BX, BY, 22, '#FFC52E', t * .12);
    halftone(rectPts(0, 0, W, H), PAL.pink, { cell: 28, dot: .12, op: .3 });
    const [sx, sy] = hit ? [endX, endY] : at(F, k);
    const sh = hit ? shakeXY(t, 10 * Math.exp(-since * 6) + 3, 30) : [0, 0];
    enter(lt, 960 + sh[0] + ease(p) * 50, 540 + sh[1], 1 + ease(p) * .06, 0, 1);
    // ATTENTION: each letter slams in as the spark passes beneath it
    ransom('ATTENTION', 500, 190, 112, { seed: 4242, pop: clamp((sx + 60) / 950) * 1.08, rot: -.035, maxW: 820 });
    // fuse: unburnt rope ahead of the spark, charred cord behind it
    if (!hit) {
      const rest = partial([...F].reverse(), 1 - k);
      marker(rest, '#5E3F22', 20, { rough: .4 });
      marker(rest, '#C39556', 11, { rough: .3 });
      ctx.save(); tracePath(rest, false); ctx.setLineDash([7, 11]); ctx.strokeStyle = '#6B4A28'; ctx.lineWidth = 5; ctx.stroke(); ctx.restore();
    }
    marker(partial(F, k), '#2C2522', 7, { rough: 1.5, alpha: .8 });
    // bomb (trembles harder as the spark closes in)
    const tremble = hit ? 5 : k * k * 3;
    const lx = clamp((sx - BX) / 500, -1, 1), ly = clamp((sy - BY) / 400, -1, 1);
    ctx.save(); ctx.translate(jit(tremble), jit(tremble));
    const sw = hit ? 1 + .03 * Math.sin(since * 38) + pulse(t, 8) * .03 : 1;
    ctx.translate(BX, BY); ctx.scale(sw, 2 - sw); ctx.translate(-BX, -BY);
    bombFace(BX, BY, BR, { nub: NUB, lx, ly, worry: k, squeeze: hit, sweat: k > .55 });
    ctx.restore();
    // the Attention paper, taped to the bomb
    doc(BX + BR * 1.18, BY + BR * .5, 260, 340, { title: 'Attention Is All You Need', titleSize: 33, rot: .09, lines: 8, seed: 2111 });
    tape(BX + BR * .74, BY - BR * .05, 150, -.55, { seed: 2112 });
    // spark: sparkles spray off it, pure function of time
    const E = .022;
    for (let j = Math.floor(lt / E) - 20; j <= Math.floor(lt / E); j++) {
      if (j < 0) continue;
      const te = j * E, age = lt - te; if (age < 0 || age > .42) continue;
      const [ox, oy] = te >= hitT ? [endX, endY] : at(F, te / hitT);
      const a = hash2(j, 1) * TAU, v = 260 + hash2(j, 2) * 520 * (te >= hitT ? 1.5 : 1);
      const px = ox + Math.cos(a) * v * age, py = oy + Math.sin(a) * v * age + 1100 * age * age;
      const r = (1 - age / .42) * (7 + hash2(j, 3) * 10);
      scrap(starPts(px, py, r, .35, 4, a), [PAL.white, PAL.red, '#FF8A1E'][j % 3], { torn: 0, shadow: false });
    }
    glow(sx, sy, hit ? 170 : 120, PAL.white, .75);
    const fz = hit ? 1.5 + pulse2(t, 5) * .5 : 1;
    scrap(burstPts(sx, sy, (48 + jit(10)) * fz, 11, .42, t * 11), '#FF7A1A', { torn: .5, shadow: false });
    scrap(burstPts(sx, sy, (30 + jit(6)) * fz, 9, .45, -t * 13), PAL.yellow, { torn: .4, shadow: false });
    dot(sx, sy, 11 * fz, PAL.white);
    if (hit) {
      for (let i = 0; i < 5; i++) {
        const a = -2.2 + (i - 2) * .45, rr = 40 + easeOut(clamp(since / .35)) * 90;
        scrap(ellPts(endX + Math.cos(a) * rr, endY + Math.sin(a) * rr, 26 * (1 - clamp(since / .6)) + 4, 22 * (1 - clamp(since / .6)) + 4, 10), '#E9E1D0', { torn: 2, seed: 2120 + i, shadow: false, op: .9 });
      }
      sticker('FZZT!', endX - 250, endY + 110, 88, PAL.pink, { pop: clamp(since / .12), rot: -.22, size: 44, font: 'bungee' });
    }
    camEnd();
  });

  // ---------- V1.2: Scaling laws you can't refuse → the offer across the desk ----------
  function offerPaper(x, y, rot, sc = 1) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot); ctx.scale(sc, sc);
    scrap(rectPts(-300, -225, 600, 450), PAL.white, { torn: 1.8, seed: 2201, shadow: [14, 18] });
    txt('SCALING LAWS', 0, -178, 50, PAL.ink, { font: 'abril' });
    underline(-170, 170, -142, PAL.ink, 4);
    const x0 = -220, y0 = -110, w = 450, h = 250;
    ctx.fillStyle = alpha(PAL.blue, .25);
    for (let i = 0; i <= 6; i++) { ctx.fillRect(x0 + i * w / 6, y0, 2, h); ctx.fillRect(x0, y0 + i * h / 6, w, 2); }
    marker([[x0, y0 - 8], [x0, y0 + h], [x0 + w + 8, y0 + h]], PAL.ink, 5, { rough: .8 });
    txt('LOSS', x0 - 26, y0 + h / 2, 22, PAL.ink, { font: 'marker', rot: -TAU / 4 });
    txt('COMPUTE (log)', x0 + w / 2, y0 + h + 24, 22, PAL.ink, { font: 'marker' });
    marker([[x0 + 10, y0 + 12], [x0 + w - 10, y0 + h - 18]], PAL.red, 9, { rough: 0 });
    for (let i = 0; i < 6; i++) { const u = .06 + i * .17; scrap(ellPts(lerp(x0 + 10, x0 + w - 10, u), lerp(y0 + 12, y0 + h - 18, u), 9, 9, 10), PAL.ink, { torn: .3, shadow: false }); }
    ctx.restore();
  }
  line('V1', 2, (p, lt, d, t) => {
    fill('#3E1A24');
    ctx.fillStyle = 'rgb(0 0 0 / .2)'; for (let i = 0; i < 16; i++) ctx.fillRect(i * 128 + 20, 0, 58, 470);
    enter(lt, 960, 540, 1 + ease(p) * .05, 0, -1);
    // the boss: faceless silhouette, fedora, a red rose
    const S = '#120A0E';
    scrap([[640, 460], [700, 300], [820, 250], [1100, 250], [1220, 300], [1280, 460]], S, { torn: 1.2, seed: 2210, shadow: false });
    scrap([[920, 252], [1000, 252], [960, 330]], '#D9D2C5', { torn: .5, shadow: false });
    scrap([[950, 262], [970, 262], [974, 320], [960, 336], [946, 320]], '#5A1420', { torn: .3, shadow: false });
    scrap(ellPts(960, 190, 70, 76, 24), S, { torn: .8, seed: 2211, shadow: false });
    scrap(ellPts(960, 148, 150, 26, 28), S, { torn: .8, seed: 2212, shadow: false });
    scrap([[872, 150], [892, 78], [960, 64], [1028, 78], [1048, 150]], S, { torn: .8, seed: 2213, shadow: false });
    scrap(rectPts(878, 124, 164, 18), '#4A1A26', { torn: .4, shadow: false });
    const blink = frac(lt / .9) > .92;
    if (!blink) for (const s of [-1, 1]) scrap(ellPts(960 + s * 26, 196, 11, 4, 10), '#F5E6B8', { torn: .3, shadow: false });
    scrap(ellPts(1082, 318, 17, 15, 12), PAL.red, { torn: .8, seed: 2214, shadow: false, ink: '#7A0F1C', sw: 2 });
    scrap([[1080, 330], [1098, 350], [1072, 344]], PAL.green, { torn: .3, shadow: false });
    // desk
    scrap([[60, 430], [1860, 430], [2120, 1140], [-200, 1140]], '#5E3822', { torn: 1, seed: 2201, shadow: false });
    ctx.strokeStyle = 'rgb(30 15 8 / .35)'; ctx.lineWidth = 3;
    for (let i = 0; i < 9; i++) { ctx.beginPath(); ctx.moveTo(-100, 470 + i * 70); ctx.bezierCurveTo(500, 450 + i * 72, 1300, 500 + i * 66, 2020, 460 + i * 74); ctx.stroke(); }
    ctx.save(); ctx.globalCompositeOperation = 'screen'; glow(930, 690, 720, '#FFC26A', .55); ctx.restore();
    // the offer slides across
    const px = lerp(-520, 930, backOut(clamp(lt / .18), 1.1)), py = 700, prot = -.05;
    offerPaper(px, py, prot, 1.2);
    // tap, tap: the finger drums the paper on every beat once it has arrived
    const tapUp = lt > .2 ? Math.sin(frac(bpOf(t)) * Math.PI) * 26 : 0;
    limb(px - 320, py - 110 - tapUp, -.1, 80, { sleeve: '#23263A', stripes: 'rgb(255 255 255 / .28)', cuff: PAL.white, ring: PAL.gold, seed: 2230, skin: SKINS[1], pose: 'point' });
    // Clawd, nodding very fast
    clawd(1740, 945, 13, { eyes: 'wide', mouth: 'flat', sweat: true, dy: -pulse2(t, 7) * .7, sq: pulse2(t, 7) * .12, lookX: -1, aL: -.9, aR: -.9 });
    camEnd();
    captionStyle({ color: PAL.clawdDk });
  });

  // ---------- V1.3: Gwern said "stack the compute high" → hooded figure jacks a GPU tower up out of frame ----------
  // Hooded, faceless figure: robe + hood with a "?" in the shadow. (x, y) ground; ≈ 10s tall.
  function hooded(x, y, s, o = {}) {
    const col = o.col ?? '#3D2F57', dk = mixCol(col, PAL.ink, .45);
    ctx.save(); ctx.translate(x, y);
    ctx.fillStyle = 'rgb(28 26 31 / .22)'; tracePath(ellPts(0, 0, 2.8 * s, .5 * s, 20)); ctx.fill();
    ctx.translate(0, (o.dy ?? 0) * s);
    const arm = (side, ang, point) => {
      ctx.save(); ctx.translate(side * 1.45 * s, -6.4 * s); ctx.rotate(side * -ang);
      scrap(rectPts(side > 0 ? 0 : -3 * s, -.55 * s, 3 * s, 1.1 * s), col, { torn: .6, seed: 2300 + side, shadow: false });
      scrap([[side * 2.3 * s, -.62 * s], [side * 3.05 * s, -.78 * s], [side * 3.05 * s, .78 * s], [side * 2.3 * s, .62 * s]], dk, { torn: .4, seed: 2302 + side, shadow: false });
      ctx.fillStyle = o.skin ?? SKINS[4]; tracePath(ellPts(side * 3.35 * s, 0, .42 * s, .42 * s, 12)); ctx.fill();
      if (point) scrap(rrPts(side > 0 ? 3.5 * s : -4.4 * s, -.13 * s, .9 * s, .26 * s, .12 * s), o.skin ?? SKINS[4], { torn: .2, shadow: false });
      ctx.restore();
    };
    arm(-1, o.aL ?? -1.2, o.pointL);
    scrap([[-1.7 * s, -7 * s], [1.7 * s, -7 * s], [2.4 * s, -.15 * s], [-2.4 * s, -.15 * s]], col, { torn: .8, seed: 2310, shade: dk, shadeOp: .3, shadow: [.2 * s, .25 * s] });
    marker([[-.6 * s, -5 * s], [-.95 * s, -.5 * s]], dk, .12 * s, { rough: .5 });
    marker([[.7 * s, -4.4 * s], [1.05 * s, -.5 * s]], dk, .12 * s, { rough: .5 });
    scrap(rrPts(-1.5 * s, -.45 * s, 1.2 * s, .5 * s, .2 * s), PAL.ink, { torn: .3, shadow: false });
    scrap(rrPts(.3 * s, -.45 * s, 1.2 * s, .5 * s, .2 * s), PAL.ink, { torn: .3, shadow: false });
    // hood with a pointed peak, dark opening, "?" in the shadow
    const hood = [[-1.9 * s, -6.5 * s], [-1.95 * s, -8.3 * s], [-1.3 * s, -9.7 * s], [-.2 * s, -10.35 * s], [.55 * s, -10.9 * s], [.75 * s, -10.2 * s], [1.5 * s, -9.5 * s], [1.95 * s, -8.2 * s], [1.9 * s, -6.5 * s]];
    scrap(hood, col, { torn: .7, seed: 2311, shade: dk, shadeOp: .3, shadow: [.15 * s, .2 * s] });
    scrap(ellPts(0, -8.25 * s, 1.1 * s, 1.35 * s, 26), '#0D0A14', { torn: .5, seed: 2312, shadow: false });
    txt('?', jit(.03 * s), -8.15 * s, 2 * s, o.qCol ?? '#9B90C2', { font: 'abril' });
    arm(1, o.aR ?? -1.2, o.pointR);
    if (o.name) helloTag(o.name, .55 * s, -5.3 * s, .42 * s);
    ctx.restore();
  }
  line('V1', 3, (p, lt, d, t) => {
    const E = EIGHTH(), e = Math.floor(lt / E), f = frac(lt / E);
    const done = e > 7, ins = Math.min(e, 8);  // eight insertions, one per eighth note
    fill(PAL.sky);
    halftone(rectPts(0, 0, W, H), PAL.white, { cell: 30, dot: .22, op: .55, multiply: false });
    for (let i = 0; i < 4; i++) {
      const cx = ((i * 560 + 200 - t * 40) % 2400 + 2400) % 2400 - 240, cy = 150 + i * 150 + (i % 2) * 40;
      for (let j = 0; j < 4; j++) scrap(ellPts(cx + j * 60 - 90, cy - (j % 3 === 1 ? 30 : 0), 70 + (j % 2) * 18, 44 + (j % 2) * 10, 16), PAL.white, { torn: 2, seed: 2320 + i * 5 + j, shadow: false, op: .9 });
    }
    const gy = 910;
    enter(lt, 960, 540 - ease(p) * 30, 1 - ease(p) * .05, 0, 1);
    scrap(rectPts(-400, gy, W + 800, 500), '#5577A8', { torn: 1, seed: 2330, shadow: false });
    halftone(rectPts(-400, gy, W + 800, 500), PAL.ink, { cell: 12, dot: .25, op: .35 });
    // the tower: new cards are shoved in at the bottom, lifting everything by one card per eighth
    const TX = 1260, CH = 132, lift = done ? 1 : easeOut(clamp(f / .35)), slide = done ? 1 : ease(clamp((f - .04) / .42));
    const GX = 640, S = 50;
    const push = done ? 0 : Math.sin(clamp(f / .5) * Math.PI);
    const aR = -1.05 + push * .6;
    const hx = GX + 1.45 * S + Math.cos(aR) * 3.35 * S, hy = gy - 6.4 * S - Math.sin(aR) * 3.35 * S;
    const slotY = sl => gy - CH / 2 - 10 - sl * CH;
    const sway = sl => Math.sin(t * 3.1) * sl * sl * 1.1 + Math.sin(t * 5.3 + 1) * sl * 1.8;
    const labels = ['V100', 'A100', 'V100', 'A100', 'TPUv3', 'A100', 'V100', 'A100', 'V100', 'A100', 'V100', 'A100'];
    const n = 3 + ins;
    // drawn top-down so each card's label sits on top of the gold edge of the card above
    for (let i = n - 1; i >= 0; i--) {
      const slot = done ? i : i + lift;
      if (slotY(slot) < -200) continue;
      gpu(TX + sway(slot), slotY(slot), 24, { label: labels[(n - i) % labels.length], rot: Math.cos(t * 3.1) * slot * .005, hot: slot > 6 ? .5 : 0 });
    }
    // the card currently being shoved in underneath
    if (!done) {
      const cx = lerp(hx + 115, TX, slide), cy = lerp(hy + 45, slotY(0), slide);
      gpu(cx, cy, 24, { label: labels[(n + 1) % labels.length], rot: (1 - slide) * .08 });
    }
    // Gwern: faceless hood, one arm shoving, the other pointing up
    hooded(GX, gy, S, { name: 'GWERN', aR, aL: 1.25 + pulse(t, 5) * .12, pointL: true, dy: -pulse2(t, 8) * .08 });
    // "MORE" scrawled on each beat
    const words = ['MORE', 'MORE!', 'MORE!!', 'MOAR!!!'], pos = [[330, 210], [1650, 330], [1630, 560], [1610, 790]], rots = [-.12, .1, -.08, .12];
    for (let j = 0; j < 4; j++) {
      const bl = Math.max(0, beatLt(t, lt, j) - .02); if (lt < bl) continue;
      const k = clamp((lt - bl) / .1), s = backOut(k, 2.5);
      ctx.save(); ctx.translate(...pos[j]); ctx.rotate(rots[j] + jit(.01)); ctx.scale(s, s);
      txt(words[j], 0, 0, 124, PAL.red, { font: 'marker', stroke: PAL.white, sw: 14, maxW: 470 });
      ctx.restore();
    }
    arrow(TX - 210, 720, TX - 190, 70, PAL.red, 11, { k: clamp(lt / .45), bend: -.04 });
    camEnd();
  });

  // ---------- V1.4: Few-shot learners multiply → agents divide on eighth notes in a petri dish ----------
  const OFFS = [[170, 0], [0, 138], [86, 0], [0, 69], [43, 0], [0, 35], [21.5, 0]];
  const BARS = [PAL.clawd, PAL.pink, PAL.blue, PAL.teal];
  function cellPos(i, g, kLast) {
    let x = 0, y = 0;
    for (let l = 0; l < g; l++) {
      const sgn = (i >> (g - 1 - l)) & 1 ? 1 : -1, f = l === g - 1 ? kLast : 1;
      x += OFFS[l][0] * sgn * f; y += OFFS[l][1] * sgn * f;
    }
    return [x, y];
  }
  const cellSize = g => Math.max(14.5, 92 * .72 ** g);
  line('V1', 4, (p, lt, d, t) => {
    const E = EIGHTH(), e = Math.floor(lt / E);
    const g = Math.min(7, e), kLast = e > 7 || g === 0 ? 1 : backOut(clamp(frac(lt / E) / .55), 2);
    fill(PAL.pink);
    rays(960, 520, 28, '#FF66B0', -t * .08);
    halftone(rectPts(0, 0, W, H), PAL.purple, { cell: 24, dot: .16, op: .25 });
    enter(lt, 960, 530, 1 + ease(p) * .04, 0, -1);
    const DX = 960, DY = 520, DR = 430;
    // petri dish
    scrap(ellPts(DX, DY, DR + 26, DR + 26, 64), '#DDF3F6', { torn: 1.5, seed: 2401, shadow: [16, 20], ink: PAL.ink, sw: 5 });
    scrap(ellPts(DX, DY, DR, DR, 64), PAL.mint, { torn: 1, seed: 2402, shadow: false, tone: { color: PAL.teal, cell: 14, dot: .2, op: .35 } });
    ctx.save(); ctx.globalAlpha = .55; ctx.strokeStyle = PAL.white; ctx.lineWidth = 12; ctx.lineCap = 'round';
    ctx.beginPath(); ctx.arc(DX, DY, DR + 10, -2.6, -1.9); ctx.stroke(); ctx.beginPath(); ctx.arc(DX, DY, DR + 10, -1.75, -1.6); ctx.stroke(); ctx.restore();
    ctx.fillStyle = alpha(PAL.ink, .18); ctx.fillRect(DX - DR, DY - 1.5, DR * 2, 3); ctx.fillRect(DX - 1.5, DY - DR, 3, DR * 2);
    // the agents: each one splits in two on every eighth note
    const n = 2 ** g, sz = g ? lerp(cellSize(g - 1), cellSize(g), kLast) : cellSize(0);
    const hop = pulse(t, 7), spill = g === 7 ? lerp(1, 1.3, kLast) : 1;
    for (let i = 0; i < n; i++) {
      const [ax, ay] = cellPos(i, g, kLast).map(v => v * spill);
      const lineage = g >= 2 ? i >> (g - 2) : g === 1 ? i * 2 : 0;
      const bounce = hash(i * 13 + g) < .5 ? hop : pulse2(t, 7) * .6;
      agent(DX + ax, DY + ay + sz * 1.5 - bounce * sz * .5, sz, { bar: BARS[lineage], eyes: g < 3 ? undefined : (i + g) % 5 === 0 ? 'spark' : 'dot', face: '>_', walk: t * 3 + hash(i) });
    }
    // x2 counter
    const cnt = `×${n}`;
    ctx.save(); ctx.translate(250, 520); ctx.rotate(-.1); const cs = 1 + (g ? (1 - clamp(frac(lt / E) / .25)) * .25 : 0); ctx.scale(cs, cs);
    txt(cnt, 0, 0, 150, PAL.ink, { font: 'marker', stroke: PAL.yellow, sw: 18 });
    ctx.restore();
    dymo('GPT-3', DX - 300, DY - DR + 40, 44, PAL.blue, { rot: -.5 });
    sticker('175B!', 1590, 330, 150, PAL.yellow, { pop: clamp((lt - beatLt(t, lt, 1)) / .14), rot: .14, size: 88, font: 'bungee' });
    camEnd();
  });

  // ---------- V1.5: ChatGPT, overnight → a chat bubble rises like the sun over a sleeping city ----------
  const SKY = Array.from({ length: 16 }, (_, i) => ({ x: -40 + i * 128 + (hash(i + 2500) - .5) * 30, w: 100 + hash(i + 2510) * 70, top: 640 + hash(i + 2520) * 190 }));
  line('V1', 5, (p, lt, d, t) => {
    const rise = backOut(clamp(lt / .5), 1.1), dawn = clamp(lt / (d * .8));
    const by = lerp(1150, 440, rise), bs = lerp(.5, 1.22, rise);
    const skyCol = mixCol('#1E1B2E', '#D9604A', dawn * .9);
    fill(skyCol);
    ctx.save(); ctx.globalCompositeOperation = 'screen';
    glow(960, by + 40, 900, mixCol('#FF4FA3', '#FFB347', dawn), .25 + dawn * .45);
    ctx.restore();
    enter(lt, 960, 540, 1 + ease(p) * .04, 0, 1);
    // stars (fade at dawn) and a startled moon getting shoved aside
    for (let i = 0; i < 46; i++) {
      const sx = hash(i + 2530) * W, sy = hash(i + 2540) * 650, tw = .5 + .5 * Math.sin(t * 7 + i);
      scrap(starPts(sx, sy, (5 + hash(i + 2550) * 7) * (.7 + tw * .5), .4, 4, 0), PAL.yellow, { torn: 0, shadow: false, op: (1 - dawn * .85) * (.5 + tw * .5) });
    }
    const mx = 330 - ease(clamp(lt / .9)) * 260, my = 210 + ease(clamp(lt / .9)) * 60;
    scrap(ellPts(mx, my, 110, 110, 32), '#F7EBC0', { torn: 1, seed: 2560, shadow: [8, 10] });
    scrap(ellPts(mx + 48, my - 26, 92, 92, 32), skyCol, { torn: 1, seed: 2561, shadow: false });
    dot(mx - 48, my - 10, 9, PAL.ink); marker([[mx - 64, my + 34], [mx - 46, my + 44]], PAL.ink, 5, { rough: 0 });
    // rays behind the rising bubble
    ctx.save(); ctx.globalAlpha = (.2 + dawn * .4) * clamp(rise); rays(960, by, 18, PAL.yellow, t * .25, 1400); ctx.restore();
    glow(960, by, 380 * bs, PAL.yellow, .5);
    // the bubble
    ctx.save(); ctx.translate(960, by); ctx.scale(bs, bs); ctx.rotate(wob(t, .7) * .03);
    scrap([[-150, 120], [-230, 230], [-40, 128]], PAL.white, { torn: 1, ink: PAL.ink, sw: 6, seed: 2570, shadow: [8, 10] });
    scrap(rrPts(-320, -150, 640, 300, 110), PAL.white, { torn: 1.5, ink: PAL.ink, sw: 6, seed: 2571, shadow: [10, 14] });
    scrap(ellPts(-222, -78, 30, 30, 16), '#10A37F', { torn: .5, seed: 2572, shadow: false, ink: PAL.ink, sw: 4 });
    txt('ChatGPT', -178, -76, 40, PAL.ink, { font: 'archivo', align: 'left' });
    for (let i = 0; i < 3; i++) { const j = Math.max(0, Math.sin((t * 2.5 - i * .15) * TAU)); dot(-110 + i * 110, 50 - j * 26, 34, PAL.ink); }
    ctx.restore();
    // the city wakes up: windows light up one by one
    for (const [i, b] of SKY.entries()) {
      scrap(rectPts(b.x, b.top, b.w, H - b.top + 40), '#0F0D18', { torn: 1, seed: 2580 + i, shadow: false });
      for (let r = 0; r < 8; r++) for (let c = 0; c < 3; c++) {
        const wx = b.x + 16 + c * (b.w - 32) / 2.6, wy = b.top + 26 + r * 44; if (wy > 980) continue;
        const on = hash2(i * 31 + r, c) < .08 + ease(clamp(lt / (d * .75))) * .8;
        ctx.fillStyle = on ? (hash2(i + r, c + 9) < .5 ? PAL.yellow : '#9FE8FF') : '#2A2638'; ctx.fillRect(wx, wy, 18, 24);
      }
    }
    sticker('1M USERS\nIN 5 DAYS', 1560, 420, 160, PAL.pink, { pop: clamp((lt - beatLt(t, lt, 1)) / .14), rot: .12, size: 50, font: 'bungee' });
    camEnd();
    captionStyle({ color: PAL.blue });
  });

  // ---------- V1.6: Sydney's chats gave Roose a fright → love-bombing phone, hair standing on end ----------
  function devil(x, y, r) {
    scrap([[x - r * .8, y - r * .5], [x - r * .95, y - r * 1.25], [x - r * .35, y - r * .85]], '#C0264A', { torn: .3, shadow: false });
    scrap([[x + r * .8, y - r * .5], [x + r * .95, y - r * 1.25], [x + r * .35, y - r * .85]], '#C0264A', { torn: .3, shadow: false });
    scrap(ellPts(x, y, r, r, 22), PAL.purple, { torn: .5, shadow: false, ink: PAL.ink, sw: 3 });
    ctx.strokeStyle = PAL.white; ctx.lineWidth = r * .12; ctx.lineCap = 'round';
    for (const s of [-1, 1]) { ctx.beginPath(); ctx.moveTo(x + s * r * .55, y - r * .35); ctx.lineTo(x + s * r * .15, y - r * .15); ctx.stroke(); }
    ctx.beginPath(); ctx.arc(x, y + r * .05, r * .5, .2 * Math.PI, .8 * Math.PI); ctx.stroke();
  }
  function heartIcon(x, y, r, col = PAL.red, rot = 0) { scrap(xform(heartPts(x, y, r, 30), 0, 0, rot, 1, x, y), col, { torn: .4, shadow: false, ink: PAL.ink, sw: 2.5 }); }
  // Sydney's chat on a phone centred at (PX, PY), PW × PH, tilted rot; a message lands on each beat.
  function sydneyPhone(t, lt, PX, PY, PW, PH, rot) {
    ctx.save(); ctx.translate(PX, PY); ctx.rotate(rot);
    scrap(rrPts(-PW / 2, -PH / 2, PW, PH, 56), PAL.ink, { torn: 1, seed: 2601, shadow: [12, 16] });
    scrap(rrPts(-PW / 2 + 20, -PH / 2 + 20, PW - 40, PH - 40, 38), '#FFF2F8', { torn: .6, seed: 2602, shadow: false });
    scrap(rectPts(-PW / 2 + 20, -PH / 2 + 40, PW - 40, 110), '#5E36A8', { torn: .5, seed: 2603, shadow: false });
    devil(-PW / 2 + 82, -PH / 2 + 98, 30);
    txt('Sydney', -PW / 2 + 128, -PH / 2 + 96, 46, PAL.white, { font: 'archivo', align: 'left' });
    const msgs = [
      { text: "I'm Sydney", devil: true }, { text: 'I love you', hearts: 1 }, { text: 'Leave your wife', hearts: 2 }, { text: '', hearts: 5 },
    ];
    let yy = -PH / 2 + 180;
    msgs.forEach((m, i) => {
      const at0 = i ? beatLt(t, lt, i - 1) : 0, k = clamp((lt - at0) / .12); if (k <= 0) return;
      const tw = m.text ? textW(m.text, 38, 'archivo') : 0, bw = tw + 44 + (m.devil ? 70 : 0) + (m.hearts ?? 0) * 58, bh = 84;
      ctx.save(); ctx.translate(-PW / 2 + 42, yy + bh / 2); const s = backOut(k, 2.2); ctx.scale(s, s);
      scrap(rrPts(0, -bh / 2, bw, bh, 34), i === 3 ? PAL.red : PAL.pink, { torn: .6, seed: 2610 + i, shadow: [4, 5] });
      if (m.text) txt(m.text, 22, 2, 38, PAL.white, { font: 'archivo', align: 'left' });
      if (m.devil) devil(tw + 60, 4, 24);
      for (let h = 0; h < (m.hearts ?? 0); h++) heartIcon(tw + (m.text ? 58 : 44) + h * 58, 2 + Math.sin(t * 12 + h) * 4, 22, i === 3 ? PAL.pink : PAL.red, .15);
      ctx.restore();
      yy += bh + 30;
    });
    if (yy < PH / 2 - 90) {
      scrap(rrPts(-PW / 2 + 42, yy, 130, 66, 30), '#E9D6F2', { torn: .5, seed: 2615, shadow: false });
      for (let q = 0; q < 3; q++) dot(-PW / 2 + 77 + q * 30, yy + 33 - Math.max(0, Math.sin((t * 3 - q * .18) * TAU)) * 9, 9, PAL.purple);
    }
    ctx.restore();
  }
  line('V1', 6, (p, lt, d, t) => {
    fill(PAL.purple);
    ctx.save(); ctx.globalAlpha = .22;
    for (let r = 0; r < 7; r++) for (let c = 0; c < 12; c++) { const hx = c * 170 + (r % 2) * 85, hy = r * 170 + 40 + ((t * 60) % 170); heartIcon(hx, hy - 170, 34, PAL.pink, .2); }
    ctx.restore();
    const sh = shakeXY(t, 4, 20);
    enter(lt, 960 + sh[0], 540 + sh[1], 1 + ease(p) * .04, 0, -1);
    // the phone
    sydneyPhone(t, lt, 1290, 530, 460, 800, .05 + wob(t, 3) * .015);
    // hearts drift out of the phone toward Kevin
    for (let i = 0; i < 12; i++) {
      const ph = frac(lt * .9 + hash(i + 2620)), hx = lerp(1080, 420, ph) + Math.sin(ph * 9 + i) * 40, hy = lerp(500 + hash(i + 2630) * 300, 180 + hash(i + 2640) * 300, ph);
      if (lt < .1) continue;
      heartIcon(hx, hy, 18 + hash(i + 2650) * 18, i % 3 ? PAL.red : PAL.pink, Math.sin(t * 5 + i) * .3);
    }
    // Kevin: hair standing straight up, newspaper in hand
    const KX = 520, KY = 950, S = 60, fright = backOut(clamp(lt / .2), 2);
    const headY = KY - 8.9 * S - 4 - Math.sin(clamp(lt / .3) * Math.PI) * .6 * S;
    for (let i = 0; i < 9; i++) {
      const hx = KX + (i - 4) * .27 * S, len = (1.4 + fright * (2.2 + hash(i + 2660) * 1.2)) * S;
      scrap([[hx - .22 * S, headY - .7 * S], [hx + jit(6) + (i - 4) * 4, headY - .8 * S - len], [hx + .22 * S, headY - .7 * S]], '#3A2A20', { torn: .5, seed: 2670 + i, shadow: false });
    }
    const jump = Math.sin(clamp(lt / .3) * Math.PI) * .6;
    person(KX + jit(3), KY, S, { dy: -jump,
      name: 'KEVIN', hair: 'bald', skin: SKINS[4], top: 'tee', topCol: PAL.blue, eyes: 'wide', mouth: 'scream', sweat: true, lookX: .6,
      aL: .9 + Math.sin(t * 30) * .08, aR: -.35,
      hold: s => clipping(0, .9 * s, 300, 'BING BOT: "I LOVE YOU"', { size: 36, rot: .1, s: .9 }),
    });
    camEnd();
  });

  // ---------- V1.7: Six-month pause went nowhere fast → many hands press PAUSE, the GPU keeps running ----------
  function gpuRunner(x, y, s, t) {
    const run = t * 3.2;  // strides per second
    const bob = Math.abs(Math.sin(run * Math.PI)) * .6 * s;
    for (const side of [-1, 1]) {
      const ph = run * TAU + (side > 0 ? Math.PI : 0), hipX = x + side * 1.6 * s, hipY = y + 2.4 * s - bob;
      const kx = hipX + Math.sin(ph) * 1.8 * s, ky = hipY + 1.9 * s - Math.max(0, Math.cos(ph)) * .6 * s;
      const fx = kx + Math.sin(ph - .9) * 1.6 * s, fy = Math.min(y + 6.6 * s, ky + 2.2 * s);
      marker([[hipX, hipY], [kx, ky], [fx, fy]], PAL.ink, .55 * s, { rough: 0 });
      scrap(rrPts(fx - .5 * s, fy - .45 * s, 1.5 * s, .7 * s, .3 * s), side > 0 ? PAL.red : '#C2311F', { torn: .3, shadow: false, ink: PAL.ink, sw: 2 });
    }
    for (const side of [-1, 1]) {
      const ph = run * TAU + (side > 0 ? 0 : Math.PI), sx = x + side * 3.5 * s, sy = y - .6 * s - bob;
      const ex = sx + Math.sin(ph) * 1.6 * s, ey = sy + 1.4 * s;
      marker([[sx, sy], [ex, ey], [ex + Math.sin(ph) * 1.2 * s + 1.2 * s, ey - 1 * s]], PAL.ink, .45 * s, { rough: 0 });
      dot(ex + Math.sin(ph) * 1.2 * s + 1.2 * s, ey - 1 * s, .45 * s, '#9AA3B5');
    }
    gpu(x, y - bob, s, { label: '', t: t * 3, rot: -.08 });
    ctx.save(); ctx.translate(x, y - bob); ctx.rotate(-.08);
    for (const fx of [-2.4, 2.4]) { dot(fx * s + .5 * s, -.2 * s, .75 * s, PAL.white); dot(fx * s + .8 * s, -.2 * s, .38 * s, PAL.ink); }
    scrap(rectPts(-5.1 * s, -3.1 * s, 10.2 * s, .9 * s), PAL.red, { torn: .4, shadow: false });
    scrap([[5 * s, -2.9 * s], [6.6 * s, -3.6 * s - Math.sin(t * 20) * .4 * s], [6.4 * s, -2.6 * s]], PAL.red, { torn: .3, shadow: false });
    ctx.restore();
    for (let i = 0; i < 3; i++) { const ph = frac(t * 2.4 + i / 3); scrap([[x - 5.4 * s - ph * 5 * s, y - 3 * s + ph * 2 * s - bob], [x - 5 * s - ph * 5 * s, y - 2.3 * s + ph * 2 * s - bob], [x - 5.8 * s - ph * 5 * s, y - 2.4 * s + ph * 2 * s - bob]], PAL.sky, { torn: .2, shadow: false, op: 1 - ph, ink: PAL.ink, sw: 2 }); }
  }
  // [angle the arm comes in from, seed, sleeve colour, beat phase]
  const HANDS = [
    [-1.5, 2600, PAL.blue, 0], [-.95, 2601, PAL.yellow, 1], [3.0, 2602, PAL.pink, 2], [2.5, 2603, "#6B6770", 3], [1.95, 2604, PAL.green, 5], [1.3, 2605, PAL.purple, 4],
  ];
  line('V1', 7, (p, lt, d, t) => {
    fill(PAL.mint);
    halftone(rectPts(0, 640, W, 500), PAL.teal, { cell: 16, dot: .3, op: .4 });
    enter(lt, 960, 540, 1 + ease(p) * .03, 0, 1);
    // the open letter, signatures scrolling
    ctx.save(); ctx.translate(250, 0); ctx.rotate(-.04);
    scrap(rectPts(-190, -40, 380, 1000), PAL.white, { torn: 1.5, seed: 2700, shadow: [10, 12] });
    ctx.save(); tracePath(rectPts(-190, 120, 380, 800)); ctx.clip();
    const scroll = lt * 380;
    for (let r = 0; r < 26; r++) {
      const ry = 150 + r * 46 - scroll % 46 - 46 * 0, idx = r + Math.floor(scroll / 46);
      const sx = -150 + hash(idx + 2710) * 40, pts = [];
      for (let q = 0; q < 9; q++) pts.push([sx + q * (22 + hash2(idx, q) * 10), ry + (hash2(idx, q + 20) - .5) * 26]);
      marker(pts, [PAL.ink, PAL.blue, '#5A2D82'][idx % 3], 3.5, { rough: 1, smooth: true });
    }
    ctx.restore();
    scrap(rectPts(-190, -40, 380, 170), PAL.white, { torn: 1, seed: 2701, shadow: false });
    txt('OPEN LETTER', 0, 50, 46, PAL.ink, { font: 'abril' });
    txt('PAUSE GIANT AI', 0, 98, 26, PAL.ink, { font: 'typewriter' });
    ctx.restore();
    // the giant PAUSE button, many hands mashing it
    const BX = 680, BY = 500, BR = 200, mash = pulse2(t, 5);
    for (const [a, seed, col, ph] of HANDS) {
      const push = Math.max(0, Math.sin((bpOf(t) * 2 + ph * .37) * Math.PI)) ** 2;
      const r = BR + 70 - push * 60;
      limb(BX + Math.cos(a) * r, BY + Math.sin(a) * r, a + Math.PI, 66, { sleeve: col, cuff: false, skin: SKINS[seed % 6], seed, pose: 'flat', len: 1400 });
    }
    const bs = 1 - mash * .05;
    scrap(ellPts(BX + 10, BY + 16, BR * bs + 22, BR * bs + 22, 48), '#8C1A12', { torn: 1.2, seed: 2720, shadow: [12, 16] });
    scrap(ellPts(BX, BY, BR * bs, BR * bs, 48), PAL.red, { torn: 1.2, seed: 2721, shadow: false, shade: '#8C1A12', shadeOp: .35 });
    for (const s of [-1, 1]) scrap(rrPts(BX + s * 55 * bs - 28 * bs, BY - 90 * bs, 56 * bs, 180 * bs, 10), PAL.white, { torn: .8, seed: 2722 + s, shadow: false });
    // the treadmill: the GPU doesn't even slow down
    const TY = 850;
    scrap(rectPts(1080, TY - 30, 720, 70), '#3A3D45', { torn: .8, seed: 2730, shadow: [8, 10] });
    scrap(rectPts(1090, TY - 44, 700, 22), '#1C1D22', { torn: .5, shadow: false, seed: 2731 });
    ctx.fillStyle = '#5B6070'; for (let i = 0; i < 16; i++) { const bx = 1090 + (((i * 50 - t * 900) % 700) + 700) % 700; ctx.fillRect(bx, TY - 44, 8, 22); }
    marker([[1760, TY - 40], [1720, 470]], '#8E939E', 18, { rough: 0 });
    scrap(rrPts(1600, 400, 250, 120, 14), '#23262E', { torn: .6, seed: 2732, rot: .1 });
    txt('SPEED', 1725, 430, 26, '#6CF2B0', { font: 'code' });
    txt('MAX', 1725, 478, 50, PAL.red, { font: 'code', alpha: frac(t * 4) < .7 ? 1 : .4 });
    for (let i = 0; i < 5; i++) { const ly = 520 + i * 55, lx = 1030 - frac(t * 3 + i * .3) * 80; marker([[lx, ly], [lx - 90 - i * 10, ly]], PAL.teal, 7, { rough: 0 }); }
    gpuRunner(1360, 610, 29, t);
    // 6 MONTHS → crossed out
    const bx = Math.min(beatLt(t, lt, 2), d * .6);
    stamp('6 MONTHS', 1180, 200, 66, PAL.ink, -.08, { pop: clamp(lt / .1) });
    if (lt > bx) {
      const k = clamp((lt - bx) / .15);
      marker(partial([[950, 235], [1420, 175]], k), PAL.red, 16, { rough: 2 });
      marker(partial([[960, 165], [1410, 240]], clamp(k * 2 - 1)), PAL.red, 16, { rough: 2 });
    }
    if (lt > Math.min(beatLt(t, lt, 3), d * .8)) txt('NOPE.', 1330, 330, 76, PAL.red, { font: 'marker', rot: .12 });
    camEnd();
  });

  // ---------- V1.8: Eliezer's "shut-it-down" blast → megaphone blasts a red-bordered cover, papers fly ----------
  function fedora(x, y, s, rot = 0) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot);
    scrap(ellPts(0, 0, 2.1 * s, .42 * s, 28), '#2B2522', { torn: .5, seed: 2801, shadow: [.1 * s, .15 * s] });
    scrap([[-1.3 * s, -.05 * s], [-1.15 * s, -1.35 * s], [-.3 * s, -1.6 * s], [0, -1.35 * s], [.3 * s, -1.6 * s], [1.15 * s, -1.35 * s], [1.3 * s, -.05 * s]], '#2B2522', { torn: .5, seed: 2802, shadow: false });
    scrap(rectPts(-1.3 * s, -.5 * s, 2.6 * s, .38 * s), '#8C2A2A', { torn: .3, shadow: false });
    ctx.restore();
  }
  function megaphone(x0, y0, x1, y1, r0, r1) {
    const a = Math.atan2(y1 - y0, x1 - x0), nx = -Math.sin(a), ny = Math.cos(a);
    scrap([[x0 + nx * r0, y0 + ny * r0], [x1 + nx * r1, y1 + ny * r1], [x1 - nx * r1, y1 - ny * r1], [x0 - nx * r0, y0 - ny * r0]], PAL.white, { torn: .8, seed: 2810, ink: PAL.ink, sw: 4, shadow: [6, 8] });
    for (const f of [.35, .7]) { const cx = lerp(x0, x1, f), cy = lerp(y0, y1, f), r = lerp(r0, r1, f); marker([[cx + nx * r, cy + ny * r], [cx - nx * r, cy - ny * r]], PAL.red, 12, { rough: 0 }); }
    scrap(ellPts(x1, y1, r1 * .3, r1, 20, a), '#DAD4C8', { torn: .6, seed: 2811, ink: PAL.ink, sw: 4, shadow: false });
  }
  line('V1', 8, (p, lt, d, t) => {
    fill(PAL.ink);
    const EX = 1440, EY = 960, S = 62;
    const mx0 = EX - .9 * S, my0 = EY - 8.4 * S, mx1 = EX - 5.2 * S, my1 = EY - 9.1 * S;
    ctx.save(); ctx.globalAlpha = .9; rays(mx1, my1, 16, '#7A1410', -.15 + wob(t, 2) * .02); ctx.restore();
    halftone(rectPts(0, 0, W, H), PAL.red, { cell: 22, dot: .2, op: .5, multiply: false });
    const sh = shakeXY(t, 9, 26);
    enter(lt, 960 + sh[0], 540 + sh[1], 1.02, 0, -1);
    // blast rings
    for (let j = 0; j < 5; j++) {
      const ph = frac(lt * 2.6 + j / 5), r = 60 + ph * 1100;
      ctx.save(); ctx.globalAlpha = 1 - ph; ctx.strokeStyle = j % 2 ? PAL.yellow : PAL.white; ctx.lineWidth = 16 * (1 - ph) + 4; ctx.lineCap = 'round';
      ctx.beginPath(); ctx.ellipse(mx1, my1, r * .55, r, 0, Math.PI - .7, Math.PI + .7); ctx.stroke(); ctx.restore();
    }
    // papers flying out of the blast
    for (let i = 0; i < 16; i++) {
      const ph = frac(lt * (.9 + hash(i + 2830) * .6) + hash(i + 2831));
      const px = lerp(mx1 - 40, -300, ph), py = my1 + (hash(i + 2832) - .5) * 200 + (hash(i + 2833) - .5) * 900 * ph + Math.sin(ph * 12 + i) * 30;
      ctx.save(); ctx.translate(px, py); ctx.rotate(ph * (4 + i % 3) + i); ctx.scale(1, .5 + .5 * Math.abs(Math.cos(ph * 9 + i)));
      scrap(rectPts(-45, -58, 90, 116), i % 4 ? PAL.white : PAL.newsprint, { torn: 1, seed: 2840 + i, shadow: [4, 5] });
      ctx.fillStyle = 'rgb(28 26 31 / .5)'; for (let q = 0; q < 5; q++) ctx.fillRect(-32, -38 + q * 16, q === 4 ? 36 : 64, 4);
      ctx.restore();
    }
    // the cover, rattling in the blast
    const cx = 620, cy = 500, crot = -.07 + Math.sin(t * 31) * .025 - backOut(clamp(lt / .2)) * .05;
    ctx.save(); ctx.translate(cx, cy); ctx.rotate(crot); ctx.scale(1 - pulse2(t, 6) * .02, 1);
    scrap(rectPts(-280, -370, 560, 740), PAL.red, { torn: 1.5, seed: 2820, shadow: [16, 20] });
    scrap(rectPts(-248, -338, 496, 676), PAL.white, { torn: 1, seed: 2821, shadow: false });
    txt('OPINION', 0, -278, 76, PAL.red, { font: 'abril' });
    ctx.fillStyle = PAL.ink; ctx.fillRect(-220, -230, 440, 4);
    const lines = ['SHUT', 'IT ALL', 'DOWN'];
    lines.forEach((l, i) => { const k = clamp((lt - .04 - i * .07) / .1); if (k <= 0) return; ctx.save(); ctx.translate(0, -120 + i * 150); const s = backOut(k, 2.4); ctx.scale(s, s); txt(l, 0, 0, 158, PAL.ink, { font: 'anton', maxW: 450 }); ctx.restore(); });
    halftone(rectPts(-248, 250, 496, 88), PAL.ink, { cell: 8, dot: .3, op: .5 });
    txt('Pausing isn\'t enough.', 0, 294, 30, PAL.ink, { font: 'typewriter' });
    ctx.restore();
    // Eliezer, fedora on, megaphone to the lips
    person(EX, EY, S, { name: 'ELIEZER', hair: 'short', skin: SKINS[0], top: 'jacket', topCol: '#3B3F58', eyes: 'angry', mouth: 'scream', aL: .42 + pulse(t, 6) * .05, aR: -.8, lookX: -.8, sq: pulse2(t, 7) * .03 });
    fedora(EX, EY - 10.05 * S, .95 * S, -.06);
    megaphone(mx0, my0, mx1, my1, .35 * S, 1.45 * S);
    camEnd();
    captionStyle({ color: PAL.red });
  });

  // ---------- V1.9: Sam got fired, then rehired → booted out the door, boomerangs back on a spring ----------
  function boot(px, py, ang, s) {
    ctx.save(); ctx.translate(px, py); ctx.rotate(ang);
    scrap(rectPts(-.9 * s, 0, 1.8 * s, 9 * s), '#23263A', { torn: .8, seed: 2901, shadow: [8, 10], tone: { color: PAL.white, cell: 9, dot: .1, op: .5 } });
    scrap([[-1.3 * s, 8.4 * s], [1.3 * s, 8.4 * s], [1.6 * s, 9.6 * s], [4.3 * s, 10 * s], [4.6 * s, 11.6 * s], [-1.5 * s, 11.6 * s]], '#6B3A1F', { torn: .8, seed: 2902, ink: PAL.ink, sw: 4, shade: true, shadeOp: .3 });
    scrap(rectPts(-1.6 * s, 11.3 * s, 6.3 * s, .6 * s), PAL.ink, { torn: .4, shadow: false });
    txt('BOARD', 1.5 * s, 10.6 * s, 1 * s, PAL.yellow, { font: 'anton' });
    ctx.restore();
  }
  function spring(x0, y0, x1, y1, coils = 14, r = 26) {
    const L = Math.hypot(x1 - x0, y1 - y0), a = Math.atan2(y1 - y0, x1 - x0), pts = [];
    for (let i = 0; i <= coils * 8; i++) { const u = i / (coils * 8); pts.push([u * L, Math.sin(u * coils * TAU) * r]); }
    ctx.save(); ctx.translate(x0, y0); ctx.rotate(a);
    marker(pts, '#6B6F7A', 7, { rough: 0 }); marker(pts, '#C9CDD6', 3, { rough: 0 });
    ctx.restore();
  }
  line('V1', 9, (p, lt, d, t) => {
    // the boot lands on "fired", Sam springs back in on "rehired"
    const kickT = Math.min(beatLt(t, lt, 1), d * .3), landT = Math.min(beatLt(t, lt, 3), d * .8);
    const outEnd = kickT + (landT - kickT) * .42, backStart = kickT + (landT - kickT) * .55;
    fill('#BFE3F5');
    halftone(rectPts(0, 0, W, 880), PAL.blue, { cell: 20, dot: .14, op: .3 });
    enter(lt, 960, 540, 1, 0, 1);
    // floor + door
    scrap(rectPts(-100, 870, W + 200, 300), '#C9A77C', { torn: 1, seed: 2910, shadow: false, tone: { color: '#8A6A45', cell: 12, dot: .2, op: .4 } });
    const DL = 1240, DR = 1560, DT = 290;
    scrap(rectPts(DL - 30, DT - 30, DR - DL + 60, 870 - DT + 30), PAL.white, { torn: 1, seed: 2911, shadow: [10, 12] });
    scrap(rectPts(DL, DT, DR - DL, 870 - DT), PAL.yellow, { torn: .8, seed: 2912, shadow: false });
    ctx.save(); ctx.globalCompositeOperation = 'screen'; glow((DL + DR) / 2, 600, 300, PAL.white, .7); ctx.restore();
    scrap([[DR, DT], [DR + 120, DT + 60], [DR + 120, 910], [DR, 870]], '#E58A2E', { torn: .8, seed: 2913, ink: PAL.ink, sw: 3 });
    scrap(rrPts(DL + 60, DT - 110, 200, 70, 10), PAL.green, { torn: .6, seed: 2914 });
    txt('EXIT', DL + 160, DT - 75, 52, PAL.white, { font: 'archivo' });
    // wall hook + spring anchor
    const HX = 250, HY = 560;
    scrap(rectPts(HX - 30, HY - 40, 60, 80), '#8E939E', { torn: .5, seed: 2915 });
    // Sam's flight: out through the door, then back on the spring
    let sx, sy, srot, eyes, mouth, aL, aR;
    if (lt < kickT) { sx = 760; sy = 900; srot = 0; eyes = 'happy'; mouth = 'smile'; aL = -1.2 + Math.max(0, Math.sin(t * 10)) * .5; aR = -1.2; }
    else if (lt < backStart) { const k = easeIn(clamp((lt - kickT) / (outEnd - kickT))); sx = lerp(760, 2400, k); sy = 900 - Math.sin(k * Math.PI) * 260 - k * 120; srot = k * 5; eyes = 'x'; mouth = 'O'; aL = 1.2; aR = .9; }
    else { const k = easeOut(clamp((lt - backStart) / (landT - backStart))); sx = lerp(2400, 930, k); sy = 780 + 120 * k - Math.sin(k * Math.PI) * 200; srot = (1 - k) * -4; eyes = k > .7 ? 'happy' : 'wide'; mouth = 'grin'; aL = 1.2 + Math.sin(t * 14) * .1; aR = 1.2 - Math.sin(t * 14) * .1; }
    const land = lt > landT ? Math.exp(-(lt - landT) * 9) * Math.sin((lt - landT) * 40) : 0;
    const bodyY = sy - 4.5 * 52;
    spring(HX + 20, HY, sx - Math.cos(srot) * 20, bodyY, 16, 24);
    person(sx, sy, 52, { name: 'SAM', hair: 'short', top: 'hoodie', topCol: '#7A7F8C', eyes, mouth, aL, aR, rot: srot, sq: land * .12, skin: SKINS[4] });
    // the boot (kicks, then retracts)
    const wind = kickT - .08;
    const kick = lt < wind ? lerp(.2, -.3, ease(lt / Math.max(.01, wind))) : lt < kickT ? lerp(-.3, .7, easeIn((lt - wind) / .08)) : lt < kickT + .2 ? .7 : lerp(.7, -.9, ease((lt - kickT - .2) / .25));
    boot(0, 330, -kick, 60);
    if (lt > kickT - .02 && lt < kickT + .3) sticker('WHAM!', 560, 640, 100, PAL.yellow, { pop: clamp((lt - kickT + .02) / .08), rot: -.2, size: 54, font: 'bungee' });
    camEnd();
  });

  // ---------- V1.10: Weekend chaos, board expired → calendar flips, board members eject, EXPIRED ----------
  const DAYS = [['FRI', 17], ['SAT', 18], ['SUN', 19], ['MON', 20], ['TUE', 21]];
  function calPage(x, y, day, n, rot = 0, sy = 1) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot); ctx.scale(1, sy);
    scrap(rectPts(-150, 0, 300, 290), PAL.white, { torn: 1, seed: 3000 + n, shadow: [6, 8] });
    scrap(rectPts(-150, 0, 300, 70), PAL.red, { torn: .6, seed: 3010 + n, shadow: false });
    txt('NOV 2023', 0, 36, 36, PAL.white, { font: 'archivo' });
    txt(day, 0, 118, 60, PAL.ink, { font: 'anton' });
    txt(String(n), 0, 210, 110, PAL.ink, { font: 'abril' });
    ctx.restore();
  }
  const BOARD = [[640, 2, '#3B3F58', 'side', PAL.red], [860, 0, '#5B3A29', 'bun', PAL.blue], [1080, 3, '#2E4A3E', 'bald', PAL.gold], [1300, 5, '#4A2E5B', 'curly', PAL.pink], [1520, 1, '#23304A', 'short', PAL.teal]];
  line('V1', 10, (p, lt, d, t) => {
    const B = beatLen();
    fill('#B88A5C');
    ctx.fillStyle = 'rgb(60 30 10 / .18)'; for (let i = 0; i < 14; i++) ctx.fillRect(i * 150, 0, 8, H);
    const sh = shakeXY(t, 3, 20);
    enter(lt, 960 + sh[0], 540 + sh[1], 1 + ease(p) * .04, 0, -1);
    // window: day / night strobing (the weekend goes by in a blur)
    const night = frac(lt / B) > .5;
    scrap(rectPts(1060, 90, 380, 250), '#5B3A29', { torn: 1, seed: 3020, shadow: [8, 10] });
    scrap(rectPts(1080, 110, 340, 210), night ? PAL.night : PAL.sky, { torn: .6, seed: 3021, shadow: false });
    if (night) { scrap(ellPts(1330, 170, 34, 34, 20), '#F7EBC0', { torn: .5, shadow: false }); scrap(ellPts(1346, 160, 30, 30, 20), PAL.night, { torn: .5, shadow: false }); }
    else scrap(burstPts(1170, 180, 46, 12, .7, t * 2), PAL.yellow, { torn: .5, shadow: false });
    ctx.fillStyle = '#5B3A29'; ctx.fillRect(1246, 110, 8, 210); ctx.fillRect(1080, 211, 340, 8);
    // calendar: a page per beat
    const flips = [0, 1, 2, 3, 4].map(k => beatLt(t, lt, k)).filter(b => b > .1).slice(0, 3);
    let bi = 0; for (const b of flips) if (lt >= b) bi++;
    const since = bi ? lt - flips[bi - 1] : 9;
    scrap(rectPts(160, 96, 320, 24), '#6B6F7A', { torn: .4, shadow: false });
    calPage(320, 118, DAYS[bi][0], DAYS[bi][1]);
    if (bi > 0 && since < .22) { const k = since / .22; calPage(320 - k * 260, 118 - k * 200, DAYS[bi - 1][0], DAYS[bi - 1][1], -k * 1.6, 1 - k * .6); }
    for (let i = 0; i < 7; i++) dot(185 + i * 45, 108, 9, PAL.ink);
    // chairs + board members, ejecting one after another
    const EJ = [.14, .34, .52, .7, .86].map(f => f * d * .9);
    BOARD.forEach(([x, skin, top, hair, tie], i) => {
      const age = lt - EJ[i];
      const up = age > 0 ? age * 900 + age * age * 5200 : 0, spin = age > 0 ? age * (i % 2 ? 6 : -6) : 0;
      ctx.save(); ctx.translate(x, 700 - up); ctx.rotate(spin);
      scrap(rrPts(-85, -280, 170, 300, 30), '#2A2426', { torn: .8, seed: 3030 + i, shadow: [6, 8] });
      for (let q = 0; q < 4; q++) dot(-40 + (q % 2) * 80, -210 + Math.floor(q / 2) * 90, 6, '#4A4246');
      person(0, 120, 30, { skin: SKINS[skin], top: 'suit', topCol: top, tie, hair, eyes: age > 0 ? 'x' : 'wide', mouth: age > 0 ? 'scream' : 'O', aL: age > 0 ? 1.3 : -1, aR: age > 0 ? 1.3 : -1, shadow: false });
      // ejector-seat exhaust, blasting downward
      if (age > 0) { ctx.save(); ctx.translate(0, 30); ctx.rotate(Math.PI); fire(0, 0, 16, { k: .9 + jit(.12), n: 3 }); ctx.restore(); }
      ctx.restore();
      if (age > 0 && age < .5) scrap(ellPts(x, 690, 60 + age * 160, 30 + age * 60, 16), '#EFE8DA', { torn: 3, seed: 3040 + i, shadow: false, op: 1 - age * 2 });
    });
    // the table
    scrap([[340, 690], [1760, 690], [1900, 860], [200, 860]], '#4A2A18', { torn: 1, seed: 3050, shadow: [10, 12] });
    scrap([[200, 860], [1900, 860], [1900, 925], [200, 925]], '#2E190D', { torn: 1, seed: 3051, shadow: false });
    ctx.fillStyle = 'rgb(255 255 255 / .1)'; ctx.fillRect(360, 705, 1380, 10);
    scrap(rectPts(830, 740, 460, 90), PAL.gold, { torn: .8, seed: 3052, ink: PAL.ink, sw: 3, shade: true, shadeOp: .25 });
    txt('THE BOARD', 1060, 787, 58, PAL.ink, { font: 'abril' });
    const bx = Math.min(beatLt(t, lt, 3), d * .75);
    stamp('EXPIRED', 1080, 520, 150, PAL.red, -.12, { pop: clamp((lt - bx) / .1) });
    camEnd();
  });

  // ---------- V1.11: Ilya saw what Ilya saw → a giant eye at the keyhole ----------
  line('V1', 11, (p, lt, d, t) => {
    const shock = beatLt(t, lt, 1), shocked = lt > shock, sk = clamp((lt - shock) / .1);
    fill('#22142F');
    ctx.save(); ctx.globalCompositeOperation = 'screen'; glow(300, 1000, 1300, '#FFB347', .3); ctx.restore();
    const sh = shocked ? shakeXY(t, 6 * Math.exp(-(lt - shock) * 5), 30) : [0, 0];
    enter(lt, 960 + sh[0], 540 + sh[1], 1 + ease(p) * .06, 0, 1);
    // door panels
    for (const [x, y, w, h] of [[160, 260, 520, 280], [1240, 260, 520, 280], [160, 640, 520, 300], [1240, 640, 520, 300]]) {
      scrap(rectPts(x, y, w, h), '#33204A', { torn: 1, seed: 3100 + x + y, shadow: false, ink: 'rgb(8 4 14 / .6)', sw: 6 });
    }
    // brass plate and keyhole
    const KX = 960, KY = 520;
    scrap(rrPts(KX - 150, KY - 250, 300, 560, 60), PAL.gold, { torn: 1, seed: 3110, shadow: [10, 14], ink: PAL.ink, sw: 4, shade: true, shadeOp: .3 });
    for (const yy of [KY - 205, KY + 265]) dot(KX, yy, 12, '#8A6420');
    const hole = [...ellPts(KX, KY - 30, 105, 105, 40).filter(([x, y]) => y < KY + 30 || Math.abs(x - KX) > 60), [KX + 90, KY + 230], [KX - 90, KY + 230]];
    const holePts = [...ellPts(KX, KY - 30, 105, 105, 40, Math.PI / 2 + .6).slice(0, 34), [KX - 58, KY + 50], [KX - 92, KY + 230], [KX + 92, KY + 230], [KX + 58, KY + 50]];
    scrap(holePts, '#0B0810', { torn: .8, seed: 3111, shadow: false });
    ctx.save(); tracePath(ellPts(KX, KY - 30, 98, 98, 40)); ctx.clip();
    // the eye (face beyond the door)
    const lookX = shocked ? 0 : [-.8, .9, -.6][Math.floor(lt / .16) % 3], blink = !shocked && lt > .22 && lt < .27;
    const ey = KY - 40, rx = 96, ry = lerp(56, 84, sk);
    scrap(rectPts(KX - 200, KY - 300, 400, 700), '#E0AC83', { torn: 0, shadow: false });
    halftoneShade(rectPts(KX - 110, KY - 140, 220, 220), PAL.ink, { dir: [0, 1], op: .5 });
    scrap(ellPts(KX, ey, rx, blink ? 6 : ry, 30), PAL.white, { torn: .6, seed: 3112, shadow: false, ink: PAL.ink, sw: 5 });
    if (!blink) {
      const ix = KX + lookX * 44;
      scrap(ellPts(ix, ey, 40, 40, 24), '#3C7FA8', { torn: .4, seed: 3113, shadow: false, ink: PAL.ink, sw: 3 });
      dot(ix, ey, lerp(20, 7, sk), PAL.ink);
      dot(ix - 14, ey - 14, 7, PAL.white);
      if (shocked) for (let i = 0; i < 4; i++) marker([[KX - 90 + i * 8, ey + 20 - i * 12], [KX - 60 + i * 6, ey + 10 - i * 10]], PAL.red, 2.5, { rough: 1 });
    }
    marker([[KX - 100, ey - ry - 12 - sk * 10], [KX, ey - ry - 26 - sk * 14], [KX + 100, ey - ry - 16 - sk * 10]], '#3A2A20', 16, { rough: 1, smooth: true });
    ctx.restore();
    ctx.save(); ctx.strokeStyle = '#0B0810'; ctx.lineWidth = 10; tracePath(ellPts(KX, KY - 30, 100, 100, 40)); ctx.stroke(); ctx.restore();
    ctx.fillStyle = 'rgb(255 255 255 / .12)'; tracePath([[KX + 30, KY + 70], [KX + 50, KY + 70], [KX + 75, KY + 210], [KX + 55, KY + 210]]); ctx.fill();
    if (shocked) for (let i = 0; i < 10; i++) {
      const a = i / 10 * TAU + .3, r0 = 330 + sk * 20;
      marker([[KX + Math.cos(a) * r0, KY + Math.sin(a) * r0 * .9], [KX + Math.cos(a) * (r0 + 80 * sk), KY + Math.sin(a) * (r0 + 80 * sk) * .9]], PAL.yellow, 10, { rough: 1.5 });
    }
    // whose eye? a HELLO sticker slapped on the door
    helloTag('ILYA', 1330, 400, 30, .12);
    arrow(1280, 490, 1130, 470, PAL.yellow, 9, { k: clamp(lt / .25), bend: -.2 });
    ransom('WHAT DID ILYA SEE?', 800, 125, 82, { seed: 3120, pop: clamp(lt / (d * .4)) * 1.2, maxW: 1020, rot: -.02 });
    // meanwhile, on our side of the door…
    clawd(250, 945, 13, { eyes: 'happy', mouth: 'smile', blush: true, aR: .9 + Math.sin(t * 16) * .35, aL: -.6, lookX: .8, lookY: -1, dy: -pulse(t, 7) * .3 });
    camEnd();
    captionStyle({ color: PAL.teal });
  });

  // ---------- V1.12: EU writes the AI law → a doorstop rulebook slams down, gavel on the beat ----------
  line('V1', 12, (p, lt, d, t) => {
    const fallT = .12, imp = lt - fallT;
    const hits = [1, 2, 3].map(k => beatLt(t, lt, k)).filter(h => h < d);
    let lastHit = -9; for (const h of hits) if (lt >= h) lastHit = h;
    const hitAge = lt - lastHit;
    fill('#1C3A9A');
    halftone(ellPts(960, 520, 820, 620, 48), PAL.blue, { cell: 22, dot: .3, op: .6, multiply: false });
    const shAmt = (imp > 0 ? 14 * Math.exp(-imp * 8) : 0) + (hitAge < .3 ? 9 * Math.exp(-hitAge * 12) : 0);
    const sh = shakeXY(t, shAmt, 30);
    enter(lt, 960 + sh[0], 540 + sh[1], 1 + ease(p) * .04, 0, -1);
    for (let i = 0; i < 12; i++) {
      const a = i / 12 * TAU + t * .35, r = 440, sc = 1 + (hitAge < .2 ? (1 - hitAge / .2) * .35 : 0);
      scrap(starPts(960 + Math.cos(a) * r, 520 + Math.sin(a) * r * .95, 46 * sc, .42, 5, -TAU / 4), PAL.yellow, { torn: .6, seed: 3200 + i, shadow: [4, 5] });
    }
    // squashed bot under the book: legs flail, a tiny white flag waves
    const BY = lerp(-500, 520, easeIn(clamp(lt / fallT))), sq = imp > 0 ? Math.exp(-imp * 9) * Math.sin(imp * 45) * .07 : 0;
    if (imp > 0) {
      for (const [lx, ph] of [[760, 0], [850, 1.7]]) {
        ctx.save(); ctx.translate(lx, BY + 290); ctx.rotate(Math.sin(t * 22 + ph) * .5 + .3);
        scrap(rectPts(-12, 0, 24, 90), '#8E98A8', { torn: .4, shadow: false }); scrap(rectPts(-24, 80, 48, 22), PAL.ink, { torn: .3, shadow: false });
        ctx.restore();
      }
      ctx.save(); ctx.translate(1262, BY + 262); ctx.rotate(.5 + Math.sin(t * 9) * .15);
      marker([[0, 0], [0, -110]], '#8B6B43', 6, { rough: 0 });
      scrap([[0, -110], [70 + Math.sin(t * 14) * 8, -95], [0, -70]], PAL.white, { torn: .5, shadow: false, ink: PAL.ink, sw: 2 });
      ctx.restore();
    }
    ctx.save(); ctx.translate(960, BY + 200); ctx.scale(1 + sq, 1 - sq); ctx.translate(-960, -BY - 200);
    // page block
    scrap(rectPts(650, BY + 110, 620, 170), '#F6F0DF', { torn: 1, seed: 3210, shadow: [16, 20] });
    ctx.fillStyle = 'rgb(28 26 31 / .25)'; for (let i = 0; i < 26; i++) ctx.fillRect(660, BY + 118 + i * 6, 600, 1.5);
    scrap(rectPts(640, BY + 270, 640, 26), '#15306E', { torn: .6, seed: 3211, shadow: false });
    for (const [bx, c] of [[800, PAL.red], [1120, PAL.yellow]]) scrap(rectPts(bx, BY + 270, 24, 70), c, { torn: .3, shadow: false });
    // cover
    scrap(rectPts(640, BY - 250, 640, 380), '#F2EAD8', { torn: 1.2, seed: 3212, shadow: false, ink: '#15306E', sw: 10 });
    scrap(rectPts(640, BY - 250, 70, 380), '#15306E', { torn: .6, seed: 3213, shadow: false });
    txt('AI ACT', 990, BY - 90, 190, '#1C3A9A', { font: 'anton' });
    txt('REGULATION (EU) 2024/1689', 990, BY + 55, 30, PAL.ink, { font: 'typewriter' });
    for (let i = 0; i < 12; i++) { const a = i / 12 * TAU; scrap(starPts(1200 + Math.cos(a) * 34, BY - 190 + Math.sin(a) * 34, 8, .45), PAL.gold, { torn: 0, shadow: false }); }
    ctx.restore();
    if (imp > 0 && imp < .4) for (let i = 0; i < 6; i++) { const s = i < 3 ? -1 : 1, a = (i % 3) * .3; scrap(ellPts(960 + s * (360 + imp * 500) , BY + 280 - a * 100 - imp * 60, 40 * (1 - imp * 2), 26 * (1 - imp * 2), 12), '#E9E1D0', { torn: 2, seed: 3220 + i, shadow: false }); }
    sticker('458\nPAGES', 590, BY - 190, 90, PAL.pink, { pop: clamp((imp - .05) / .12), rot: .2, size: 38, font: 'bungee' });
    // gavel whacks on the beat
    const swing = hits.some(h => lt >= h && lt - h < .08) ? -1.05 : hitAge < .3 ? lerp(-1.05, .35, easeOut((hitAge - .08) / .22)) : .35;
    const h0 = hits[0] ?? d + 9;
    ctx.save(); ctx.translate(1560, 560); ctx.rotate(lt < h0 - .1 ? .35 + (lt / h0) * .1 : swing);
    gavel(0, -290, 44);
    ctx.restore();
    if (hitAge < .22) sticker('BANG!', 1350, 300, 90, PAL.red, { pop: clamp(hitAge / .06), rot: -.18 + (lastHit * 7 % 1) * .3, size: 46, font: 'bungee', textCol: PAL.white });
    camEnd();
  });

  // ---------- V1.13: Strawberry thinks, link by link → a chain-of-thought grows link by link ----------
  function strawberry(x, y, s, o = {}) {
    ctx.save(); ctx.translate(x, y); if (o.rot) ctx.rotate(o.rot);
    // legs + arms (mascot sticks)
    for (const side of [-1, 1]) {
      marker([[side * 1.2 * s, 2.6 * s], [side * 1.5 * s, 4.4 * s]], PAL.ink, .32 * s, { rough: 0 });
      scrap(rrPts(side * 1.5 * s - .8 * s, 4.1 * s, 1.6 * s, .7 * s, .3 * s), PAL.white, { torn: .3, shadow: false, ink: PAL.ink, sw: 3 });
    }
    const body = heartPts(0, .4 * s, 4.2 * s, 48).map(([px, py]) => [px, py * 1.05]);
    scrap(body, '#E8312F', { torn: 1, seed: 3300, shade: '#9A1A1A', shadeOp: .35, shadow: [10, 14] });
    for (let r = 0; r < 6; r++) for (let c = 0; c < 7; c++) {
      const sx = (c - 3) * .95 * s + (r % 2) * .47 * s, sy = -1.6 * s + r * .85 * s;
      if (Math.abs(sx) > (3.6 - r * .45) * s) continue;
      scrap(ellPts(sx, sy, .13 * s, .2 * s, 8), PAL.yellow, { torn: 0, shadow: false });
    }
    // leafy crown
    scrap(starPts(0, -2.6 * s, 2.6 * s, .45, 7, -TAU / 4), PAL.green, { torn: .6, seed: 3301, ink: '#1B6B40', sw: 3, shadow: false });
    scrap(rectPts(-.2 * s, -4.6 * s, .4 * s, 1.6 * s), '#1B6B40', { torn: .3, shadow: false });
    // face: gazing up at its own train of thought, one brow raised
    for (const side of [-1, 1]) {
      scrap(ellPts(side * 1.1 * s, -.5 * s, .62 * s, .7 * s, 18), PAL.white, { torn: .3, shadow: false, ink: PAL.ink, sw: 3 });
      dot(side * 1.1 * s + .25 * s, -.78 * s, .26 * s, PAL.ink);
    }
    ctx.strokeStyle = PAL.ink; ctx.lineWidth = .22 * s; ctx.lineCap = 'round';
    ctx.beginPath(); ctx.moveTo(-1.7 * s, -1.45 * s); ctx.quadraticCurveTo(-1.1 * s, -2 * s, -.5 * s, -1.6 * s); ctx.moveTo(.55 * s, -1.4 * s); ctx.lineTo(1.7 * s, -1.4 * s); ctx.stroke();
    ctx.beginPath(); ctx.moveTo(-.5 * s, .78 * s); ctx.lineTo(.2 * s, .7 * s); ctx.quadraticCurveTo(.5 * s, .66 * s, .55 * s, .45 * s); ctx.stroke();
    // thinking hand on chin
    marker([[3.4 * s, .3 * s], [2.6 * s, 1.6 * s], [1.0 * s, 1.1 * s]], PAL.ink, .3 * s, { rough: 0 });
    scrap(ellPts(.9 * s, 1.05 * s, .55 * s, .5 * s, 14), PAL.white, { torn: .3, shadow: false, ink: PAL.ink, sw: 3 });
    marker([[-3.4 * s, .3 * s], [-4 * s, 1.6 * s]], PAL.ink, .3 * s, { rough: 0 });
    scrap(ellPts(-4 * s, 1.8 * s, .55 * s, .5 * s, 14), PAL.white, { torn: .3, shadow: false, ink: PAL.ink, sw: 3 });
    if (o.name) helloTag(o.name, 1.9 * s, 2.2 * s, .5 * s, .1);
    ctx.restore();
  }
  function link(x, y, a, s, face, col = '#A7AEBD') {
    ctx.save(); ctx.translate(x, y); ctx.rotate(a);
    if (face) {
      scrap(ellPts(0, 0, 1 * s, .62 * s, 26), col, { torn: .6, shadow: [4, 5], ink: PAL.ink, sw: 4, seed: 3310 });
      scrap(ellPts(0, 0, .62 * s, .28 * s, 20), PAL.mint, { torn: .4, shadow: false, ink: PAL.ink, sw: 3, seed: 3311 });
      ctx.fillStyle = 'rgb(255 255 255 / .55)'; tracePath(ellPts(-.35 * s, -.42 * s, .3 * s, .07 * s, 10, -.2)); ctx.fill();
    } else {
      scrap(rrPts(-1 * s, -.2 * s, 2 * s, .4 * s, .2 * s), mixCol(col, PAL.ink, .2), { torn: .4, shadow: [4, 5], ink: PAL.ink, sw: 4, seed: 3312 });
    }
    ctx.restore();
  }
  const CHAIN = spline([[560, 330], [700, 215], [900, 170], [1110, 215], [1290, 330], [1390, 480], [1410, 640]], 16);
  const STEPS = ['hmm', 'so…', 'wait', 'if', 'then', 'but'];
  line('V1', 13, (p, lt, d, t) => {
    fill(PAL.mint);
    halftone(rectPts(0, 0, W, H), PAL.green, { cell: 26, dot: .2, op: .3 });
    halftone(ellPts(480, 1000, 700, 260), PAL.teal, { cell: 14, dot: .35, op: .5 });
    enter(lt, 960, 540, 1 + ease(p) * .05, 0, 1);
    const bulbT = Math.min(beatLt(t, lt, 2), d * .8), N = 13, step = bulbT / N, spacing = 1 / (N + .5);
    // the thinker
    strawberry(360, 610 - pulse(t, 6) * 18, 62, { name: 'o1', rot: Math.sin(t * 5) * .03 });
    // thought puffs from head to chain
    [[470, 380, 16], [510, 350, 22]].forEach(([x, y, r], i) => { if (lt > i * .04) scrap(ellPts(x, y, r, r, 14), PAL.white, { torn: .4, ink: PAL.ink, sw: 3, shadow: [3, 4] }); });
    // links
    const shown = Math.min(N, Math.floor(lt / step) + 1);
    for (let i = 0; i < shown; i++) {
      const u = (i + .5) * spacing, [x, y] = at(CHAIN, u), a = angAt(CHAIN, u);
      const k = clamp((lt - i * step) / .1), s = 58 * backOut(k, 2.6);
      link(x, y + Math.sin(t * 6 + i * .7) * 4, a, s, i % 2 === 0);
      if (i % 2 === 0 && i / 2 < STEPS.length) txt(STEPS[i / 2], x - Math.sin(a) * -80, y + Math.cos(a) * -80, 46, PAL.ink, { font: 'marker', alpha: k, rot: a * .3 });
    }
    // the answer: a light bulb pops at the end of the chain
    const bk = clamp((lt - bulbT) / .12);
    if (bk > 0) {
      const [x, y] = at(CHAIN, 1), s = backOut(bk, 2.4);
      ctx.save(); ctx.translate(x + 40, y + 130); ctx.scale(s, s);
      ctx.save(); ctx.globalAlpha = .6; rays(0, -20, 12, PAL.yellow, t, 220); ctx.restore();
      scrap(ellPts(0, -30, 78, 84, 28), PAL.yellow, { torn: .8, ink: PAL.ink, sw: 5, seed: 3320 });
      scrap(rectPts(-36, 44, 72, 50), '#8E939E', { torn: .5, ink: PAL.ink, sw: 4, seed: 3321, shadow: false });
      txt('!', 0, -28, 110, PAL.ink, { font: 'abril' });
      ctx.restore();
    }
    camEnd();
  });

  // ---------- V1.14: Newsom vetoes, doesn't blink → staring contest with SB 1047, VETO stamp ----------
  line('V1', 14, (p, lt, d, t) => {
    const vetoT = Math.min(beatLt(t, lt, 1), d * .45), blinkT = vetoT - .28, vk = clamp((lt - vetoT) / .08);
    const vetoed = lt >= vetoT;
    fill('#F2B230');
    ctx.save(); ctx.globalAlpha = .5; rays(1320, 520, 16, '#FFD83A', t * .1); ctx.restore();
    halftone(rectPts(0, 0, W, H), PAL.red, { cell: 20, dot: .14, op: .25 });
    const sh = vetoed ? shakeXY(t, 12 * Math.exp(-(lt - vetoT) * 6), 30) : [0, 0];
    enter(lt, 960 + sh[0], 540 + sh[1], 1 + ease(p) * .05, 0, -1);
    // Gavin, big, eyes locked open
    const GX = 470, GY = 1460, S = 100;
    person(GX, GY, S, { name: 'GAVIN', hair: 'swoop', hairCol: '#3B2A1E', top: 'suit', topCol: '#22304C', tie: PAL.blue, eyes: 'dot', mouth: 'flat', aL: -1.25, aR: -1.25, skin: SKINS[0] });
    const hy = GY - 8.9 * S;
    for (const side of [-1, 1]) {
      const ex = GX + side * .5 * S + jit(1.5), ey = hy - .08 * S;
      scrap(ellPts(ex, ey, .42 * S, .46 * S, 22), PAL.white, { torn: .5, shadow: false, ink: PAL.ink, sw: 5 });
      for (let v = 0; v < 4; v++) { const a = Math.PI * (side > 0 ? .1 : .9) + (v - 1.5) * .45; marker([[ex + Math.cos(a) * .4 * S, ey + Math.sin(a) * .42 * S], [ex + Math.cos(a) * .24 * S, ey + Math.sin(a) * .26 * S]], PAL.red, 3, { rough: 1.2 }); }
      dot(ex + .16 * S + jit(1), ey, .11 * S, PAL.ink);
      marker([[ex - .38 * S, ey - .64 * S], [ex + .36 * S, ey - .7 * S]], '#3B2A1E', .1 * S, { rough: 0 });
    }
    // the bill, staring back (and losing)
    const BX = 1330, BY = 540;
    doc(BX, BY, 440, 580, { title: 'SB 1047', titleSize: 84, titleFont: 'anton', lines: 11, rot: .04, seed: 3400, body: ['Safe and Secure Innovation', 'for Frontier AI Models Act'] });
    const billBlink = lt > blinkT && lt < blinkT + .12;
    for (const side of [-1, 1]) {
      const ex = BX + side * 70, ey = BY + 110;
      if (vetoed) { marker([[ex - 22, ey - 22], [ex + 22, ey + 22]], PAL.ink, 7, { rough: 0 }); marker([[ex + 22, ey - 22], [ex - 22, ey + 22]], PAL.ink, 7, { rough: 0 }); }
      else if (billBlink) marker([[ex - 30, ey], [ex + 30, ey]], PAL.ink, 7, { rough: 0 });
      else { scrap(ellPts(ex, ey, 34, 38, 16), PAL.white, { torn: .4, shadow: false, ink: PAL.ink, sw: 4 }); dot(ex - 12, ey + 4, 13, PAL.ink); }
    }
    if (!vetoed) scrap([[BX + 104, BY + 60], [BX + 116, BY + 84], [BX + 104, BY + 92], [BX + 92, BY + 84]], PAL.sky, { torn: .3, ink: PAL.ink, sw: 3, shadow: false });
    // stare beam
    if (!vetoed) {
      const pts = []; for (let i = 0; i <= 14; i++) pts.push([lerp(GX + 120, BX - 130, i / 14), hy + lerp(0, BY + 110 - hy, i / 14) + (i % 2 ? -18 : 18) + jit(4)]);
      marker(pts, PAL.red, 7, { rough: 0 });
    }
    // VETO: a giant rubber stamp comes down
    const sy = vetoed ? lerp(BY - 20, -700, easeIn(clamp((lt - vetoT - .1) / .3))) : lerp(-420, BY - 20, easeIn(clamp((lt - vetoT + .14) / .14)));
    if (vetoed) stamp('VETO', BX, BY + 40, 170, PAL.red, -.2, { pop: vk });
    ctx.save(); ctx.translate(BX + 10, sy); ctx.rotate(-.2);
    scrap(rectPts(-230, -40, 460, 90), '#B23A2B', { torn: .6, seed: 3410, ink: PAL.ink, sw: 4 });
    scrap(rectPts(-200, -110, 400, 76), '#6B3A1F', { torn: .6, seed: 3411, ink: PAL.ink, sw: 4 });
    scrap(rectPts(-40, -300, 80, 200), '#8B5A2B', { torn: .5, seed: 3412, ink: PAL.ink, sw: 4 });
    scrap(ellPts(0, -320, 90, 64, 24), '#6B3A1F', { torn: .6, seed: 3413, ink: PAL.ink, sw: 4 });
    ctx.restore();
    dymo('BLINKS: 0', 300, 150, 44, PAL.red, { rot: -.06 });
    camEnd();
  });

  // ---------- V1.15: Hinton takes his medal, scolds → Nobel on stage, finger wagging ----------
  line('V1', 15, (p, lt, d, t) => {
    fill('#7E141C');
    // velvet curtain folds
    for (let i = 0; i < 20; i++) { ctx.fillStyle = i % 2 ? 'rgb(0 0 0 / .22)' : 'rgb(255 120 120 / .08)'; ctx.fillRect(i * 100 + Math.sin(i * 1.3) * 10, 0, 56, H); }
    enter(lt, 960, 540, 1 + ease(p) * .05, 0, 1);
    ctx.save(); ctx.globalCompositeOperation = 'screen';
    ctx.fillStyle = 'rgb(255 236 170 / .22)'; tracePath([[840, -20], [1080, -20], [1340, 940], [560, 940]]); ctx.fill();
    glow(950, 880, 480, '#FFE9A8', .4);
    ctx.restore();
    // curtain swag
    for (let i = 0; i < 9; i++) scrap(ellPts(i * 240 + 20, 20, 170, 90, 24), '#9A1C24', { torn: 1.5, seed: 3500 + i, shade: '#3A0508', shadeOp: .4, shadow: [6, 8] });
    // stage
    scrap(rectPts(-100, 860, W + 200, 300), '#5B3721', { torn: 1, seed: 3510, shadow: false });
    ctx.fillStyle = 'rgb(0 0 0 / .25)'; for (let i = 0; i < 6; i++) ctx.fillRect(-100, 880 + i * 34, W + 200, 3);
    // Geoff
    const GX = 900, GY = 960, S = 64;
    const wag = Math.sin(lt * TAU * 4.5) * .22;
    person(GX, GY, S, {
      name: 'GEOFF', hair: 'side', hairCol: '#E9E6DF', glasses: true, top: 'sweater', topCol: '#40607F', skin: SKINS[4], brows: 'angry', mouth: 'O',
      aL: -1.15, aR: 1.25 + wag,
      hold: s => { scrap(rrPts(-.16 * s, -1.25 * s, .32 * s, 1 * s, .15 * s), SKINS[4], { torn: .3, shadow: false, ink: alpha(PAL.ink, .4), sw: 1.5 }); },
    });
    // the medal drops round his neck
    const mk = clamp(lt / .22), my = lerp(-300, GY - 4.35 * S, easeIn(mk)) + (mk >= 1 ? Math.sin((lt - .22) * 30) * Math.exp(-(lt - .22) * 8) * 16 : 0);
    const mx = GX - .62 * S;
    marker([[GX - .75 * S, my - 2.6 * S], [mx - .25 * S, my - .7 * S]], PAL.blue, .45 * S, { rough: 0 });
    marker([[GX + .6 * S, my - 2.6 * S], [mx + .3 * S, my - .7 * S]], PAL.blue, .45 * S, { rough: 0 });
    scrap(ellPts(mx, my, .95 * S, .95 * S, 28), PAL.gold, { torn: .6, ink: PAL.ink, sw: 4, shade: true, shadeOp: .3, seed: 3520 });
    txt('NOBEL', mx, my + 2, .46 * S, PAL.ink, { font: 'abril' });
    // podium
    scrap([[640, 760], [1160, 760], [1120, 1000], [680, 1000]], '#2B2240', { torn: 1, seed: 3530, shadow: [10, 12] });
    scrap(rectPts(620, 740, 560, 40), '#3E3358', { torn: .8, seed: 3531, shadow: false });
    txt('PHYSICS 2024', 900, 850, 50, PAL.gold, { font: 'abril' });
    // "BE CAREFUL!"
    bubble('BE CAREFUL!', 1400, 300, { size: 66, pop: clamp((lt - Math.min(beatLt(t, lt, 1), d * .3)) / .12), tail: [GX + 90, GY - 9 * S], rot: .05 });
    // camera flashes on the beat
    for (let k = 0; k < 4; k++) {
      const bt = beatLt(t, lt, k), age = lt - bt; if (age < 0 || age > .14) continue;
      const fx = [300, 1550, 420, 1600][k], fy = [700, 700, 420, 520][k];
      glow(fx, fy, 220, PAL.white, .9 * (1 - age / .14));
      scrap(burstPts(fx, fy, 70 * (1 - age / .14) + 20, 8, .3), PAL.white, { torn: .5, shadow: false });
    }
    camEnd();
  });

  // ---------- V1.16: Demis wins for protein folds → a protein ribbon origami-folds into a medal ----------
  const RIBBON_N = 110;
  const PLDDT = ['#1E3FAF', '#2F86E8', '#6FD0F0', '#FFD83A', '#FF8A3A'];
  line('V1', 16, (p, lt, d, t) => {
    const foldT = Math.min(beatLt(t, lt, 1), d * .6), fk = ease(clamp(lt / foldT)), popK = clamp((lt - foldT) / .1);
    fill(PAL.pink);
    ctx.save(); ctx.globalAlpha = .35; rays(1100, 450, 24, PAL.purple, t * .2); ctx.restore();
    halftone(rectPts(0, 0, W, H), PAL.purple, { cell: 22, dot: .16, op: .3 });
    enter(lt, 960, 540, 1 + ease(p) * .05, 0, -1);
    const DX = 520, DY = 960, S = 60;
    // Demis in a lab coat, conducting the fold
    person(DX, DY, S, { name: 'DEMIS', hair: 'short', hairCol: '#2A2320', top: 'coat', topCol: PAL.white, skin: SKINS[2], eyes: popK > 0 ? 'happy' : 'dot', mouth: popK > 0 ? 'grin' : 'o', aL: -.5 + Math.sin(t * 9) * .1, aR: .45 + Math.sin(t * 7) * .15 });
    const hx = DX + 1.35 * S + Math.cos(.45) * 3.2 * S, hy = DY - 7.1 * S - Math.sin(.45) * 3.2 * S;
    const KX = 1150, KY = 440;
    // medal disc behind the fold
    if (popK > 0) {
      ctx.save(); ctx.translate(KX, KY); const s = backOut(popK, 2.2); ctx.scale(s, s);
      scrap([[-120, -560], [-40, -140], [40, -140], [120, -560]], PAL.blue, { torn: .6, seed: 3600, shadow: [6, 8] });
      scrap(ellPts(0, 0, 200, 200, 40), PAL.gold, { torn: 1, ink: PAL.ink, sw: 6, shade: true, shadeOp: .3, seed: 3601 });
      ctx.strokeStyle = alpha(PAL.ink, .45); ctx.lineWidth = 5; ctx.beginPath(); ctx.arc(0, 0, 160, 0, TAU); ctx.stroke();
      txt('NOBEL · CHEMISTRY', 0, 180, 26, PAL.ink, { font: 'abril', alpha: 0 });
      ctx.restore();
    }
    // the ribbon: long wiggly chain → compact fold
    const pts = [];
    for (let i = 0; i < RIBBON_N; i++) {
      const u = i / (RIBBON_N - 1);
      const x0 = hx + u * 900, y0 = hy - 40 + Math.sin(u * TAU * 2.4 + t * 3) * 70 + Math.sin(u * TAU * 16) * 20;
      let x1, y1;
      if (u < .06) { x1 = lerp(hx, KX - 140, u / .06); y1 = lerp(hy, KY + 60, u / .06); }
      else { const v = (u - .06) / .94, th = v * TAU * 2.2 + 2.6, r = 60 + 62 * Math.abs(Math.sin(th * 1.6)); x1 = KX + Math.cos(th) * r + Math.sin(u * TAU * 16) * 10; y1 = KY + Math.sin(th) * r + Math.cos(u * TAU * 16) * 10; }
      pts.push([lerp(x0, x1, fk), lerp(y0, y1, fk)]);
    }
    marker(pts, PAL.ink, 30, { rough: 0 });
    for (let i = 0; i < RIBBON_N - 1; i++) {
      const c = PLDDT[Math.min(4, Math.floor(i / (RIBBON_N - 1) * 5))];
      marker([pts[i], pts[i + 1]], c, 20, { rough: 0 });
    }
    // confetti
    if (popK > 0) for (let i = 0; i < 70; i++) {
      const age = lt - foldT, x0 = hash(i + 3610) * W, sp = 380 + hash(i + 3611) * 500;
      const cx = x0 + Math.sin(age * 6 + i) * 40 + (hash(i + 3612) - .5) * 300 * age, cy = -40 + age * sp + (hash(i + 3613) - .7) * 500 * (1 - age);
      ctx.save(); ctx.translate(cx, cy); ctx.rotate(age * 8 + i); ctx.scale(1, Math.cos(age * 12 + i));
      ctx.fillStyle = [PAL.yellow, PAL.blue, PAL.white, PAL.teal, PAL.gold, PAL.red][i % 6]; ctx.fillRect(-10, -6, 20, 12);
      ctx.restore();
    }
    sticker('NOBEL!', 1560, 720, 120, PAL.yellow, { pop: clamp((lt - foldT - .05) / .12), rot: .15, size: 50, font: 'bungee' });
    camEnd();
  });

  // =====================================================================================================================
  // The vertical video (1080 × 1920): each line re-composed for the tall frame. The same props and gags, stacked: the subject big
  // in the safe area (y 250–1250), the caption tape at y ≈ 1290–1480, floors, tables and skylines in the bottom ≈ 420. Vertical
  // motion where the line has some to give: the fuse comes down from the intro, the tower grows out of the top, the sun-bubble
  // rises, Sam is kicked up through the ceiling and bungees back, the board ejects upward, the rulebook falls, the chain of
  // thought climbs, the Nobel drops from the flies.
  // =====================================================================================================================

  // ---------- V1.1 (vertical): the fuse comes in at the top (from the intro), runs along under ATTENTION, down into the bomb ----------
  vshot('V1.1', (p, lt, d, t) => {
    const hitT = d * .66, k = clamp(lt / hitT), hit = lt >= hitT, since = lt - hitT;
    const BX = 560, BY = 1050, BR = 245, NUB = -1.05;
    const endX = BX + Math.cos(NUB) * BR * 1.14, endY = BY + Math.sin(NUB) * BR * 1.14;
    const F = spline([[150, -60], [130, 220], [160, 520], [300, 665], [540, 685], [780, 668], [930, 715], [945, 815], [endX + 40, endY - 50], [endX, endY]], 14);
    fill(PAL.yellow);
    rays(BX, BY, 22, '#FFC52E', t * .12);
    halftone(rectPts(0, 0, W, H), PAL.pink, { cell: 28, dot: .12, op: .3 });
    const [sx, sy] = hit ? [endX, endY] : at(F, k);
    const sh = hit ? shakeXY(t, 10 * Math.exp(-since * 6) + 3, 30) : [0, 0];
    enter(lt, 540 + sh[0], 960 + sh[1] + ease(p) * 40, 1 + ease(p) * .06, 0, 1);
    // ATTENTION: each letter slams in as the spark passes beneath it
    ransom('ATTENTION', 540, 565, 104, { seed: 4242, pop: sy > 600 ? clamp((sx - 130) / 820) * 1.08 : 0, rot: -.035, maxW: 900 });
    if (!hit) {
      const rest = partial([...F].reverse(), 1 - k);
      marker(rest, '#5E3F22', 20, { rough: .4 });
      marker(rest, '#C39556', 11, { rough: .3 });
      ctx.save(); tracePath(rest, false); ctx.setLineDash([7, 11]); ctx.strokeStyle = '#6B4A28'; ctx.lineWidth = 5; ctx.stroke(); ctx.restore();
    }
    marker(partial(F, k), '#2C2522', 7, { rough: 1.5, alpha: .8 });
    const tremble = hit ? 5 : k * k * 3;
    const lx = clamp((sx - BX) / 500, -1, 1), ly = clamp((sy - BY) / 400, -1, 1);
    ctx.save(); ctx.translate(jit(tremble), jit(tremble));
    const sw = hit ? 1 + .03 * Math.sin(since * 38) + pulse(t, 8) * .03 : 1;
    ctx.translate(BX, BY); ctx.scale(sw, 2 - sw); ctx.translate(-BX, -BY);
    bombFace(BX, BY, BR, { nub: NUB, lx, ly, worry: k, squeeze: hit, sweat: k > .55 });
    ctx.restore();
    // the paper, taped to the bomb's flank
    doc(BX - BR * 1.18, BY + BR * .18, 240, 320, { title: 'Attention Is All You Need', titleSize: 31, rot: -.12, lines: 8, seed: 2111 });
    tape(BX - BR * .9, BY - BR * .38, 150, .5, { seed: 2112 });
    const E = .022;
    for (let j = Math.floor(lt / E) - 20; j <= Math.floor(lt / E); j++) {
      if (j < 0) continue;
      const te = j * E, age = lt - te; if (age < 0 || age > .42) continue;
      const [ox, oy] = te >= hitT ? [endX, endY] : at(F, te / hitT);
      const a = hash2(j, 1) * TAU, v = 260 + hash2(j, 2) * 520 * (te >= hitT ? 1.5 : 1);
      const px = ox + Math.cos(a) * v * age, py = oy + Math.sin(a) * v * age + 1100 * age * age;
      const r = (1 - age / .42) * (7 + hash2(j, 3) * 10);
      scrap(starPts(px, py, r, .35, 4, a), [PAL.white, PAL.red, '#FF8A1E'][j % 3], { torn: 0, shadow: false });
    }
    glow(sx, sy, hit ? 170 : 120, PAL.white, .75);
    const fz = hit ? 1.5 + pulse2(t, 5) * .5 : 1;
    scrap(burstPts(sx, sy, (48 + jit(10)) * fz, 11, .42, t * 11), '#FF7A1A', { torn: .5, shadow: false });
    scrap(burstPts(sx, sy, (30 + jit(6)) * fz, 9, .45, -t * 13), PAL.yellow, { torn: .4, shadow: false });
    dot(sx, sy, 11 * fz, PAL.white);
    if (hit) {
      for (let i = 0; i < 5; i++) {
        const a = -1.2 + (i - 2) * .45, rr = 40 + easeOut(clamp(since / .35)) * 90;
        scrap(ellPts(endX + Math.cos(a) * rr, endY + Math.sin(a) * rr, 26 * (1 - clamp(since / .6)) + 4, 22 * (1 - clamp(since / .6)) + 4, 10), '#E9E1D0', { torn: 2, seed: 2120 + i, shadow: false, op: .9 });
      }
      sticker('FZZT!', endX + 120, endY - 150, 96, PAL.pink, { pop: clamp(since / .12), rot: .18, size: 48, font: 'bungee' });
    }
    camEnd();
  });

  // ---------- V1.2 (vertical): the boss above, the offer slides down the desk toward us ----------
  vshot('V1.2', (p, lt, d, t) => {
    fill('#3E1A24');
    ctx.fillStyle = 'rgb(0 0 0 / .2)'; for (let i = 0; i < 9; i++) ctx.fillRect(i * 128 + 20, 0, 58, 900);
    enter(lt, 540, 960, 1 + ease(p) * .05, 0, -1);
    // the boss, scaled up and centred above the desk
    const S = '#120A0E';
    ctx.save(); ctx.translate(540, 560); ctx.scale(1.3, 1.3); ctx.translate(-960, -190);
    scrap([[600, 470], [700, 300], [820, 250], [1100, 250], [1220, 300], [1320, 470]], S, { torn: 1.2, seed: 2210, shadow: false });
    scrap([[920, 252], [1000, 252], [960, 330]], '#D9D2C5', { torn: .5, shadow: false });
    scrap([[950, 262], [970, 262], [974, 320], [960, 336], [946, 320]], '#5A1420', { torn: .3, shadow: false });
    scrap(ellPts(960, 190, 70, 76, 24), S, { torn: .8, seed: 2211, shadow: false });
    scrap(ellPts(960, 148, 150, 26, 28), S, { torn: .8, seed: 2212, shadow: false });
    scrap([[872, 150], [892, 78], [960, 64], [1028, 78], [1048, 150]], S, { torn: .8, seed: 2213, shadow: false });
    scrap(rectPts(878, 124, 164, 18), '#4A1A26', { torn: .4, shadow: false });
    const blink = frac(lt / .9) > .92;
    if (!blink) for (const s of [-1, 1]) scrap(ellPts(960 + s * 26, 196, 11, 4, 10), '#F5E6B8', { torn: .3, shadow: false });
    scrap(ellPts(1082, 318, 17, 15, 12), PAL.red, { torn: .8, seed: 2214, shadow: false, ink: '#7A0F1C', sw: 2 });
    scrap([[1080, 330], [1098, 350], [1072, 344]], PAL.green, { torn: .3, shadow: false });
    ctx.restore();
    // the desk, running down toward us
    scrap([[40, 900], [1040, 900], [1300, 2000], [-220, 2000]], '#5E3822', { torn: 1, seed: 2201, shadow: false });
    ctx.strokeStyle = 'rgb(30 15 8 / .35)'; ctx.lineWidth = 3;
    for (let i = 0; i < 12; i++) { ctx.beginPath(); ctx.moveTo(-100, 940 + i * 90); ctx.bezierCurveTo(300, 920 + i * 92, 760, 970 + i * 86, 1180, 930 + i * 94); ctx.stroke(); }
    ctx.save(); ctx.globalCompositeOperation = 'screen'; glow(540, 1080, 620, '#FFC26A', .55); ctx.restore();
    // the offer slides down the desk and grows as it comes
    const k = backOut(clamp(lt / .2), 1.1), px = 540, py = lerp(760, 1040, k), sc = lerp(.55, 1.22, k), prot = lerp(.12, -.04, k);
    offerPaper(px, py, prot, sc);
    // an ashtray and a cigar, smoking away at the foot of the frame
    scrap(ellPts(230, 1640, 130, 46, 28), '#8E939E', { torn: 1, seed: 2240, shadow: [8, 12], shade: true, shadeOp: .3 });
    scrap(ellPts(230, 1632, 92, 28, 24), '#4A4E58', { torn: .6, seed: 2241, shadow: false });
    ctx.save(); ctx.translate(250, 1615); ctx.rotate(-.25);
    scrap(rrPts(-10, -14, 190, 28, 12), '#6B3A1F', { torn: .6, seed: 2242, shadow: [4, 6] });
    scrap(rectPts(40, -15, 30, 30), PAL.red, { torn: .3, shadow: false }); scrap(rectPts(175, -13, 14, 26), '#C9C3B6', { torn: .4, shadow: false });
    ctx.restore();
    for (let i = 0; i < 6; i++) {
      const ph = frac(t * .45 + i / 6), r = 18 + ph * 60;
      scrap(ellPts(425 + Math.sin(ph * 6 + i) * 30 + ph * 40, 1555 - ph * 520, r, r * .8, 14), alpha('#D9D2C5', .5 * (1 - ph)), { torn: 3, seed: 2250 + i, shadow: false });
    }
    // Clawd, at the corner of the desk, nodding very fast
    clawd(930, 1268, 13, { eyes: 'wide', mouth: 'flat', sweat: true, dy: -pulse2(t, 7) * .7, sq: pulse2(t, 7) * .12, lookX: -1, lookY: -.6, aL: -.9, aR: -.9 });
    camEnd();
    captionStyle({ color: PAL.clawdDk });
  });

  // ---------- V1.3 (vertical): the tower is shoved up out of the top of the frame ----------
  vshot('V1.3', (p, lt, d, t) => {
    const E = EIGHTH(), e = Math.floor(lt / E), f = frac(lt / E);
    const done = e > 7, ins = Math.min(e, 8);
    fill(PAL.sky);
    halftone(rectPts(0, 0, W, H), PAL.white, { cell: 30, dot: .22, op: .55, multiply: false });
    for (let i = 0; i < 6; i++) {
      const cx = ((i * 430 + 120 - t * 40) % 1500 + 1500) % 1500 - 210, cy = 260 + i * 190 + (i % 2) * 40;
      for (let j = 0; j < 4; j++) scrap(ellPts(cx + j * 60 - 90, cy - (j % 3 === 1 ? 30 : 0), 70 + (j % 2) * 18, 44 + (j % 2) * 10, 16), PAL.white, { torn: 2, seed: 2320 + i * 5 + j, shadow: false, op: .9 });
    }
    const gy = 1470;
    enter(lt, 540, 960 - ease(p) * 40, 1 - ease(p) * .04, 0, 1);
    scrap(rectPts(-400, gy, W + 800, 800), '#5577A8', { torn: 1, seed: 2330, shadow: false });
    halftone(rectPts(-400, gy, W + 800, 800), PAL.ink, { cell: 12, dot: .25, op: .35 });
    const TX = 735, CS = 27, CH = CS * 5.5, lift = done ? 1 : easeOut(clamp(f / .35)), slide = done ? 1 : ease(clamp((f - .04) / .42));
    const GX = 300, S = 54;
    const push = done ? 0 : Math.sin(clamp(f / .5) * Math.PI);
    const aR = -1.05 + push * .6;
    const hx = GX + 1.45 * S + Math.cos(aR) * 3.35 * S, hy = gy - 6.4 * S - Math.sin(aR) * 3.35 * S;
    const slotY = sl => gy - CH / 2 - 10 - sl * CH;
    const sway = sl => Math.sin(t * 3.1) * sl * sl * .9 + Math.sin(t * 5.3 + 1) * sl * 1.6;
    const labels = ['V100', 'A100', 'V100', 'A100', 'TPUv3', 'A100', 'V100', 'A100', 'V100', 'A100', 'V100', 'A100'];
    const n = 4 + ins;
    for (let i = n - 1; i >= 0; i--) {
      const slot = done ? i : i + lift;
      if (slotY(slot) < -200) continue;
      gpu(TX + sway(slot), slotY(slot), CS, { label: labels[(n - i) % labels.length], rot: Math.cos(t * 3.1) * slot * .004, hot: slot > 7 ? .5 : 0 });
    }
    if (!done) {
      const cx = lerp(hx + 125, TX, slide), cy = lerp(hy + 45, slotY(0), slide);
      gpu(cx, cy, CS, { label: labels[(n + 1) % labels.length], rot: (1 - slide) * .08 });
    }
    hooded(GX, gy, S, { name: 'GWERN', aR, aL: 1.25 + pulse(t, 5) * .12, pointL: true, dy: -pulse2(t, 8) * .08 });
    // "MORE", scrawled up the sky on each beat
    const words = ['MORE', 'MORE!', 'MORE!!', 'MOAR!!!'], pos = [[250, 800], [270, 630], [250, 465], [300, 310]], rots = [-.12, .1, -.08, .12];
    for (let j = 0; j < 4; j++) {
      const bl = Math.max(0, beatLt(t, lt, j) - .02); if (lt < bl) continue;
      const k = clamp((lt - bl) / .1), s = backOut(k, 2.5);
      ctx.save(); ctx.translate(...pos[j]); ctx.rotate(rots[j] + jit(.01)); ctx.scale(s, s);
      txt(words[j], 0, 0, 112, PAL.red, { font: 'marker', stroke: PAL.white, sw: 14, maxW: 440 });
      ctx.restore();
    }
    arrow(TX + 205, 1080, TX + 190, 160, PAL.red, 11, { k: clamp(lt / .45), bend: .04 });
    // the supply: cartons of GPUs piled in the foreground, the near ones big, a couple torn open
    for (const [x, y, w, h, r, open, seed] of [[120, 1770, 330, 250, -.04, 0, 1], [455, 1840, 300, 210, .03, 1, 2], [800, 1760, 360, 270, -.03, 0, 3], [300, 1640, 250, 180, .06, 0, 4], [1010, 1690, 260, 200, .08, 1, 5]]) {
      ctx.save(); ctx.translate(x, y); ctx.rotate(r);
      scrap(rectPts(-w / 2, -h / 2, w, h), '#C99A62', { torn: 1.2, seed: 2340 + seed, shadow: [10, 12], shade: '#8A6A45', shadeOp: .3 });
      scrap(rectPts(-w / 2, -h / 2, w, h * .14), '#B08550', { torn: .6, seed: 2350 + seed, shadow: false });
      scrap(rectPts(-18, -h / 2, 36, h), 'rgb(236 222 180 / .85)', { torn: .4, seed: 2360 + seed, shadow: false });
      txt('GPU', -w * .22, 8, h * .26, '#3A2A1A', { font: 'mono', alpha: .8 }); txt('↑↑', w * .26, 6, h * .22, '#3A2A1A', { font: 'anton', alpha: .8 });
      if (open) { gpu(w * .12, -h / 2 - 14, 10, { rot: -.15, label: '' }); scrap([[-w / 2, -h / 2], [-w / 2 - 40, -h / 2 - 70], [-w * .1, -h / 2 - 50], [-w * .05, -h / 2]], '#B88A55', { torn: .8, seed: 2370 + seed, shadow: [4, 5] }); }
      ctx.restore();
    }
    camEnd();
  });

  // ---------- V1.4 (vertical): the petri dish fills the frame; the count above, 175B! below ----------
  vshot('V1.4', (p, lt, d, t) => {
    const E = EIGHTH(), e = Math.floor(lt / E);
    const g = Math.min(7, e), kLast = e > 7 || g === 0 ? 1 : backOut(clamp(frac(lt / E) / .55), 2);
    const DX = 540, DY = 850, DR = 410;
    fill(PAL.pink);
    rays(DX, DY, 28, '#FF66B0', -t * .08);
    halftone(rectPts(0, 0, W, H), PAL.purple, { cell: 24, dot: .16, op: .25 });
    enter(lt, 540, 960, 1 + ease(p) * .04, 0, -1);
    scrap(ellPts(DX, DY, DR + 26, DR + 26, 64), '#DDF3F6', { torn: 1.5, seed: 2401, shadow: [16, 20], ink: PAL.ink, sw: 5 });
    scrap(ellPts(DX, DY, DR, DR, 64), PAL.mint, { torn: 1, seed: 2402, shadow: false, tone: { color: PAL.teal, cell: 14, dot: .2, op: .35 } });
    ctx.save(); ctx.globalAlpha = .55; ctx.strokeStyle = PAL.white; ctx.lineWidth = 12; ctx.lineCap = 'round';
    ctx.beginPath(); ctx.arc(DX, DY, DR + 10, -2.6, -1.9); ctx.stroke(); ctx.beginPath(); ctx.arc(DX, DY, DR + 10, -1.75, -1.6); ctx.stroke(); ctx.restore();
    ctx.fillStyle = alpha(PAL.ink, .18); ctx.fillRect(DX - DR, DY - 1.5, DR * 2, 3); ctx.fillRect(DX - 1.5, DY - DR, 3, DR * 2);
    const n = 2 ** g, sz = g ? lerp(cellSize(g - 1), cellSize(g), kLast) : cellSize(0);
    const hop = pulse(t, 7), spill = g === 7 ? lerp(1, 1.3, kLast) : 1;
    for (let i = 0; i < n; i++) {
      const [ax, ay] = cellPos(i, g, kLast).map(v => v * spill);
      const lineage = g >= 2 ? i >> (g - 2) : g === 1 ? i * 2 : 0;
      const bounce = hash(i * 13 + g) < .5 ? hop : pulse2(t, 7) * .6;
      agent(DX + ax, DY + ay + sz * 1.5 - bounce * sz * .5, sz, { bar: BARS[lineage], eyes: g < 3 ? undefined : (i + g) % 5 === 0 ? 'spark' : 'dot', face: '>_', walk: t * 3 + hash(i) });
    }
    const cnt = `×${n}`;
    ctx.save(); ctx.translate(250, 352); ctx.rotate(-.1); const cs = 1 + (g ? (1 - clamp(frac(lt / E) / .25)) * .25 : 0); ctx.scale(cs, cs);
    txt(cnt, 0, 0, 150, PAL.ink, { font: 'marker', stroke: PAL.yellow, sw: 18 });
    ctx.restore();
    dymo('GPT-3', DX - 300, DY + DR - 50, 46, PAL.blue, { rot: .62 });
    // the overflow: from the fifth division on, agents spill out over the dish's rim and march off along the foot of the frame
    const spillN = Math.max(0, Math.min(16, (e - 3) * 4));
    for (let i = 0; i < spillN; i++) {
      const born = (3 + i / 4) * E, age = lt - born, row = i % 2;
      const x = 70 + ((i >> 1) * 5 % 8) * 130 + row * 65 + age * 140 * (row ? 1 : -1), y = 1720 + row * 110 - Math.abs(Math.sin(age * 9 + i)) * 18;
      agent(x, y, 40 + row * 6, { bar: BARS[i % 4], eyes: i % 3 ? 'dot' : 'spark', face: '>_', walk: t * 4 + i, rot: (row ? .08 : -.08) });
    }
    sticker('175B!', 830, 1170, 140, PAL.yellow, { pop: clamp((lt - beatLt(t, lt, 1)) / .14), rot: .14, size: 82, font: 'bungee' });
    camEnd();
  });

  // ---------- V1.5 (vertical): the bubble rises like the sun over a tall skyline ----------
  const SKYV = Array.from({ length: 10 }, (_, i) => ({ x: -50 + i * 116 + (hash(i + 2590) - .5) * 26, w: 92 + hash(i + 2591) * 60, top: 1180 + hash(i + 2592) * 260 }));
  vshot('V1.5', (p, lt, d, t) => {
    const rise = backOut(clamp(lt / .5), 1.1), dawn = clamp(lt / (d * .8));
    const by = lerp(2200, 760, rise), bs = lerp(.5, 1.25, rise);
    const skyCol = mixCol('#1E1B2E', '#D9604A', dawn * .9);
    fill(skyCol);
    ctx.save(); ctx.globalCompositeOperation = 'screen';
    glow(540, by + 40, 1100, mixCol('#FF4FA3', '#FFB347', dawn), .25 + dawn * .45);
    ctx.restore();
    enter(lt, 540, 960, 1 + ease(p) * .04, 0, 1);
    for (let i = 0; i < 60; i++) {
      const sx = hash(i + 2530) * W, sy = hash(i + 2540) * 1250, tw = .5 + .5 * Math.sin(t * 7 + i);
      scrap(starPts(sx, sy, (5 + hash(i + 2550) * 7) * (.7 + tw * .5), .4, 4, 0), PAL.yellow, { torn: 0, shadow: false, op: (1 - dawn * .85) * (.5 + tw * .5) });
    }
    // the moon, startled and shoved up out of the way
    const mk = ease(clamp(lt / .9)), mx = 250 - mk * 150, my = 470 - mk * 170;
    scrap(ellPts(mx, my, 110, 110, 32), '#F7EBC0', { torn: 1, seed: 2560, shadow: [8, 10] });
    scrap(ellPts(mx + 48, my - 26, 92, 92, 32), skyCol, { torn: 1, seed: 2561, shadow: false });
    dot(mx - 48, my - 10, 9, PAL.ink); marker([[mx - 64, my + 34], [mx - 46, my + 44]], PAL.ink, 5, { rough: 0 });
    ctx.save(); ctx.globalAlpha = (.2 + dawn * .4) * clamp(rise); rays(540, by, 18, PAL.yellow, t * .25, 1600); ctx.restore();
    glow(540, by, 380 * bs, PAL.yellow, .5);
    ctx.save(); ctx.translate(540, by); ctx.scale(bs, bs); ctx.rotate(wob(t, .7) * .03);
    scrap([[-150, 120], [-230, 230], [-40, 128]], PAL.white, { torn: 1, ink: PAL.ink, sw: 6, seed: 2570, shadow: [8, 10] });
    scrap(rrPts(-320, -150, 640, 300, 110), PAL.white, { torn: 1.5, ink: PAL.ink, sw: 6, seed: 2571, shadow: [10, 14] });
    scrap(ellPts(-222, -78, 30, 30, 16), '#10A37F', { torn: .5, seed: 2572, shadow: false, ink: PAL.ink, sw: 4 });
    txt('ChatGPT', -178, -76, 40, PAL.ink, { font: 'archivo', align: 'left' });
    for (let i = 0; i < 3; i++) { const j = Math.max(0, Math.sin((t * 2.5 - i * .15) * TAU)); dot(-110 + i * 110, 50 - j * 26, 34, PAL.ink); }
    ctx.restore();
    // the city wakes up: windows light up one by one
    for (const [i, b] of SKYV.entries()) {
      scrap(rectPts(b.x, b.top, b.w, H - b.top + 60), '#0F0D18', { torn: 1, seed: 2580 + i, shadow: false });
      for (let r = 0; r < 16; r++) for (let c = 0; c < 2; c++) {
        const wx = b.x + 16 + c * (b.w - 50), wy = b.top + 26 + r * 46; if (wy > H) continue;
        const on = hash2(i * 31 + r, c) < .08 + ease(clamp(lt / (d * .75))) * .8;
        ctx.fillStyle = on ? (hash2(i + r, c + 9) < .5 ? PAL.yellow : '#9FE8FF') : '#2A2638'; ctx.fillRect(wx, wy, 18, 24);
      }
    }
    sticker('1M USERS\nIN 5 DAYS', 800, 1130, 150, PAL.pink, { pop: clamp((lt - beatLt(t, lt, 1)) / .14), rot: .12, size: 48, font: 'bungee' });
    camEnd();
    captionStyle({ color: PAL.blue });
  });

  // ---------- V1.6 (vertical): the phone up the right; Kevin down the left, his hair shooting up the frame ----------
  vshot('V1.6', (p, lt, d, t) => {
    fill(PAL.purple);
    ctx.save(); ctx.globalAlpha = .22;
    for (let r = 0; r < 13; r++) for (let c = 0; c < 7; c++) { const hx = c * 170 + (r % 2) * 85, hy = r * 170 + 40 + ((t * 60) % 170); heartIcon(hx, hy - 170, 34, PAL.pink, .2); }
    ctx.restore();
    const sh = shakeXY(t, 4, 20);
    enter(lt, 540 + sh[0], 960 + sh[1], 1 + ease(p) * .04, 0, -1);
    ctx.save(); ctx.translate(735, 815); ctx.scale(1.02, 1.02);
    sydneyPhone(t, lt, 0, 0, 440, 820, .05 + wob(t, 3) * .015);
    ctx.restore();
    for (let i = 0; i < 12; i++) {
      const ph = frac(lt * .9 + hash(i + 2620)), hx = lerp(560, 230, ph) + Math.sin(ph * 9 + i) * 40, hy = lerp(620 + hash(i + 2630) * 420, 380 + hash(i + 2640) * 360, ph);
      if (lt < .1) continue;
      heartIcon(hx, hy, 18 + hash(i + 2650) * 18, i % 3 ? PAL.red : PAL.pink, Math.sin(t * 5 + i) * .3);
    }
    // Kevin: his hair stands straight up, way up
    const KX = 250, KY = 1440, S = 62, fright = backOut(clamp(lt / .2), 2);
    const jump = Math.sin(clamp(lt / .3) * Math.PI) * .6;
    const headY = KY - 8.9 * S - 4 - jump * S;
    for (let i = 0; i < 9; i++) {
      const hx = KX + (i - 4) * .27 * S, len = (1.4 + fright * (4.6 + hash(i + 2660) * 2.4) * (1 - Math.abs(i - 4) * .06)) * S;
      scrap([[hx - .22 * S, headY - .7 * S], [hx + jit(6) + (i - 4) * 5, headY - .8 * S - len], [hx + .22 * S, headY - .7 * S]], '#3A2A20', { torn: .5, seed: 2670 + i, shadow: false });
    }
    person(KX + jit(3), KY, S, { dy: -jump,
      name: 'KEVIN', hair: 'bald', skin: SKINS[4], top: 'tee', topCol: PAL.blue, eyes: 'wide', mouth: 'scream', sweat: true, lookX: .6,
      aL: .9 + Math.sin(t * 30) * .08, aR: -.2,
      hold: s => clipping(0, .9 * s, 300, 'BING BOT: "I LOVE YOU"', { size: 36, rot: .1, s: .85 }),
    });
    camEnd();
  });

  // ---------- V1.7 (vertical): hands mash the PAUSE button up top; below, the GPU runs on ----------
  // [angle the arm comes in from, seed, sleeve colour, beat phase]
  const HANDS_V = [
    [-1.62, 2600, PAL.blue, 0], [-.85, 2601, PAL.yellow, 1], [2.85, 2603, PAL.pink, 3], [.12, 2604, PAL.green, 5],
  ];
  vshot('V1.7', (p, lt, d, t) => {
    fill(PAL.mint);
    halftone(rectPts(0, 1000, W, 1000), PAL.teal, { cell: 16, dot: .3, op: .4 });
    enter(lt, 540, 960, 1 + ease(p) * .03, 0, 1);
    const BX = 560, BY = 700, BR = 185, mash = pulse2(t, 5);
    for (const [a, seed, col, ph] of HANDS_V) {
      const push = Math.max(0, Math.sin((bpOf(t) * 2 + ph * .37) * Math.PI)) ** 2;
      const r = BR + 66 - push * 56;
      limb(BX + Math.cos(a) * r, BY + Math.sin(a) * r, a + Math.PI, 62, { sleeve: col, cuff: false, skin: SKINS[seed % 6], seed, pose: 'flat', len: 1400 });
    }
    const bs = 1 - mash * .05;
    scrap(ellPts(BX + 10, BY + 16, BR * bs + 22, BR * bs + 22, 48), '#8C1A12', { torn: 1.2, seed: 2720, shadow: [12, 16] });
    scrap(ellPts(BX, BY, BR * bs, BR * bs, 48), PAL.red, { torn: 1.2, seed: 2721, shadow: false, shade: '#8C1A12', shadeOp: .35 });
    for (const s of [-1, 1]) scrap(rrPts(BX + s * 52 * bs - 26 * bs, BY - 84 * bs, 52 * bs, 168 * bs, 10), PAL.white, { torn: .8, seed: 2722 + s, shadow: false });
    // the treadmill: the GPU doesn't even slow down
    const TY = 1262, TL = 150, TR = 930;
    scrap(rectPts(TL, TY - 30, TR - TL, 70), '#3A3D45', { torn: .8, seed: 2730, shadow: [8, 10] });
    scrap(rectPts(TL + 10, TY - 44, TR - TL - 20, 22), '#1C1D22', { torn: .5, shadow: false, seed: 2731 });
    ctx.fillStyle = '#5B6070'; for (let i = 0; i < 16; i++) { const bx = TL + 10 + (((i * 50 - t * 900) % 760) + 760) % 760; ctx.fillRect(bx, TY - 44, 8, 22); }
    marker([[TR - 40, TY - 40], [TR - 70, 1000]], '#8E939E', 18, { rough: 0 });
    ctx.save(); ctx.translate(TR - 90, 940); ctx.rotate(.08);
    scrap(rrPts(-120, -58, 240, 116, 14), '#23262E', { torn: .6, seed: 2732 });
    txt('SPEED', 0, -28, 26, '#6CF2B0', { font: 'code' });
    txt('MAX', 0, 20, 50, PAL.red, { font: 'code', alpha: frac(t * 4) < .7 ? 1 : .4 });
    ctx.restore();
    for (let i = 0; i < 4; i++) { const ly = 980 + i * 50, lx = 300 - frac(t * 3 + i * .3) * 70; marker([[lx, ly], [lx - 80 - i * 10, ly]], PAL.teal, 7, { rough: 0 }); }
    gpuRunner(520, TY - 44 - 6.6 * 27, 27, t);
    // 6 MONTHS → crossed out
    const bx = Math.min(beatLt(t, lt, 2), d * .6);
    stamp('6 MONTHS', 268, 448, 52, PAL.ink, -.08, { pop: clamp(lt / .1) });
    if (lt > bx) {
      const k = clamp((lt - bx) / .15);
      marker(partial([[85, 478], [460, 420]], k), PAL.red, 15, { rough: 2 });
      marker(partial([[95, 415], [450, 482]], clamp(k * 2 - 1)), PAL.red, 15, { rough: 2 });
    }
    if (lt > Math.min(beatLt(t, lt, 3), d * .8)) txt('NOPE.', 290, 565, 84, PAL.red, { font: 'marker', rot: .1, stroke: PAL.white, sw: 10 });
    // the open letter: its signatures, on a scroll that keeps unrolling across the floor
    const SY = 1700, scroll = lt * 420;
    ctx.save(); ctx.translate(0, SY); ctx.rotate(-.05);
    scrap(rectPts(-120, -120, W + 240, 260), PAL.white, { torn: 1.5, seed: 2740, shadow: [10, 14] });
    ctx.save(); tracePath(rectPts(-120, -110, W + 240, 240)); ctx.clip();
    for (let r = 0; r < 4; r++) for (let c = -1; c < 7; c++) {
      const idx = c + Math.floor(scroll / 200) + r * 31, sx = c * 200 - (scroll % 200) + (r % 2) * 90 + hash(idx + 2750) * 30, sy = -78 + r * 56, pts = [];
      for (let q = 0; q < 8; q++) pts.push([sx + q * (17 + hash2(idx, q) * 8), sy + (hash2(idx, q + 20) - .5) * 24]);
      marker(pts, [PAL.ink, PAL.blue, '#5A2D82'][(idx % 3 + 3) % 3], 3.5, { rough: 1, smooth: true });
    }
    ctx.restore();
    // the roll it unwinds from, at the right
    scrap(ellPts(W + 40, 0, 70, 130, 24), '#ECE6D6', { torn: 1, seed: 2741, shadow: [6, 8], ink: alpha(PAL.ink, .4), sw: 3 });
    ctx.save(); ctx.translate(W + 40, 0); ctx.rotate(-lt * 6); ctx.strokeStyle = alpha(PAL.ink, .35); ctx.lineWidth = 3; ctx.beginPath(); ctx.ellipse(0, 0, 40, 80, 0, 0, TAU); ctx.stroke(); ctx.restore();
    ctx.restore();
    camEnd();
  });

  // ---------- V1.8 (vertical): the megaphone blasts up at the cover; Eliezer at the foot ----------
  vshot('V1.8', (p, lt, d, t) => {
    fill(PAL.ink);
    const EX = 765, EY = 1660, S = 63;
    const mx0 = EX - .95 * S, my0 = EY - 8.55 * S, ma = -2.25, mL = 4.6 * S;
    const mx1 = mx0 + Math.cos(ma) * mL, my1 = my0 + Math.sin(ma) * mL;
    ctx.save(); ctx.globalAlpha = .9; rays(mx1, my1, 16, '#7A1410', -.15 + wob(t, 2) * .02, 2600); ctx.restore();
    halftone(rectPts(0, 0, W, H), PAL.red, { cell: 22, dot: .2, op: .5, multiply: false });
    const sh = shakeXY(t, 9, 26);
    enter(lt, 540 + sh[0], 960 + sh[1], 1.02, 0, -1);
    for (let j = 0; j < 5; j++) {
      const ph = frac(lt * 2.6 + j / 5), r = 60 + ph * 1300;
      ctx.save(); ctx.globalAlpha = 1 - ph; ctx.strokeStyle = j % 2 ? PAL.yellow : PAL.white; ctx.lineWidth = 16 * (1 - ph) + 4; ctx.lineCap = 'round';
      ctx.beginPath(); ctx.ellipse(mx1, my1, r * .55, r, ma, -.7, .7); ctx.stroke(); ctx.restore();
    }
    for (let i = 0; i < 16; i++) {
      const ph = frac(lt * (.9 + hash(i + 2830) * .6) + hash(i + 2831));
      const spread = (hash(i + 2833) - .5) * 1.6, a = ma + spread * .8, dist = ph * 1600;
      const px = mx1 + Math.cos(a) * dist + Math.sin(ph * 12 + i) * 30, py = my1 + Math.sin(a) * dist;
      ctx.save(); ctx.translate(px, py); ctx.rotate(ph * (4 + i % 3) + i); ctx.scale(1, .5 + .5 * Math.abs(Math.cos(ph * 9 + i)));
      scrap(rectPts(-45, -58, 90, 116), i % 4 ? PAL.white : PAL.newsprint, { torn: 1, seed: 2840 + i, shadow: [4, 5] });
      ctx.fillStyle = 'rgb(28 26 31 / .5)'; for (let q = 0; q < 5; q++) ctx.fillRect(-32, -38 + q * 16, q === 4 ? 36 : 64, 4);
      ctx.restore();
    }
    // the cover, rattling in the blast
    const cx = 340, cy = 690, crot = -.06 + Math.sin(t * 31) * .025 - backOut(clamp(lt / .2)) * .05;
    ctx.save(); ctx.translate(cx, cy); ctx.rotate(crot); ctx.scale(.9 - pulse2(t, 6) * .02, .9);
    scrap(rectPts(-280, -370, 560, 740), PAL.red, { torn: 1.5, seed: 2820, shadow: [16, 20] });
    scrap(rectPts(-248, -338, 496, 676), PAL.white, { torn: 1, seed: 2821, shadow: false });
    txt('OPINION', 0, -278, 76, PAL.red, { font: 'abril' });
    ctx.fillStyle = PAL.ink; ctx.fillRect(-220, -230, 440, 4);
    ['SHUT', 'IT ALL', 'DOWN'].forEach((l, i) => { const k = clamp((lt - .04 - i * .07) / .1); if (k <= 0) return; ctx.save(); ctx.translate(0, -120 + i * 150); const s = backOut(k, 2.4); ctx.scale(s, s); txt(l, 0, 0, 158, PAL.ink, { font: 'anton', maxW: 450 }); ctx.restore(); });
    halftone(rectPts(-248, 250, 496, 88), PAL.ink, { cell: 8, dot: .3, op: .5 });
    txt('Pausing isn\'t enough.', 0, 294, 30, PAL.ink, { font: 'typewriter' });
    ctx.restore();
    person(EX, EY, S, { hair: 'short', skin: SKINS[0], top: 'jacket', topCol: '#3B3F58', eyes: 'angry', mouth: 'scream', aL: .95 + pulse(t, 6) * .05, aR: -.8, lookX: -.7, sq: pulse2(t, 7) * .03 });
    helloTag('ELIEZER', EX + 1.1 * S, EY - 7.6 * S, .34 * S, .1);   // (on his shoulder, clear of the caption)
    fedora(EX, EY - 10.05 * S, .95 * S, -.06);
    megaphone(mx0, my0, mx1, my1, .35 * S, 1.45 * S);
    camEnd();
    captionStyle({ color: PAL.red });
  });

  // ---------- V1.9 (vertical): the boot kicks Sam up through the EXIT hatch; he bungees back down on the spring ----------
  vshot('V1.9', (p, lt, d, t) => {
    const kickT = Math.min(beatLt(t, lt, 1), d * .3), landT = Math.min(beatLt(t, lt, 3), d * .8);
    const outEnd = kickT + (landT - kickT) * .42, backStart = kickT + (landT - kickT) * .55;
    fill('#BFE3F5');
    halftone(rectPts(0, 0, W, 1690), PAL.blue, { cell: 20, dot: .14, op: .3 });
    enter(lt, 540, 960, 1, 0, 1);
    // floor
    scrap(rectPts(-100, 1680, W + 200, 600), '#C9A77C', { torn: 1, seed: 2910, shadow: false, tone: { color: '#8A6A45', cell: 12, dot: .2, op: .4 } });
    // ceiling with the EXIT hatch, daylight pouring down through it
    const HL = 330, HR = 750, CB = 230;
    ctx.save(); ctx.globalCompositeOperation = 'screen';
    ctx.fillStyle = 'rgb(255 250 220 / .35)'; tracePath([[HL + 10, CB], [HR - 10, CB], [HR + 200, 1690], [HL - 200, 1690]]); ctx.fill();
    ctx.restore();
    scrap(rectPts(-100, -100, W + 200, CB + 100), '#8C6A4A', { torn: 1, seed: 2916, shadow: [0, 10], tone: { color: '#5B3A29', cell: 10, dot: .25, op: .4 } });
    scrap(rectPts(HL, CB - 120, HR - HL, 120), PAL.yellow, { torn: .8, seed: 2912, shadow: false });
    ctx.save(); ctx.globalCompositeOperation = 'screen'; glow((HL + HR) / 2, CB - 40, 260, PAL.white, .7); ctx.restore();
    scrap([[HR, CB], [HR + 150, CB + 60], [HR + 150, CB + 110], [HR, CB + 10]], '#E58A2E', { torn: .8, seed: 2913, ink: PAL.ink, sw: 3 });
    ctx.save(); ctx.translate(200, CB + 80); ctx.rotate(-.04);
    marker([[-50, -80], [-50, -30]], PAL.ink, 5, { rough: 0 }); marker([[50, -80], [50, -30]], PAL.ink, 5, { rough: 0 });
    scrap(rrPts(-110, -36, 220, 74, 10), PAL.green, { torn: .6, seed: 2914 });
    txt('EXIT ↑', 0, 2, 50, PAL.white, { font: 'archivo' });
    ctx.restore();
    // Sam's flight: up through the hatch and out, then back down on the spring
    const S = 68, SX = 560, SY = 1690;
    let sx, sy, srot, eyes, mouth, aL, aR;
    if (lt < kickT) { sx = SX; sy = SY; srot = 0; eyes = 'happy'; mouth = 'smile'; aL = -1.2; aR = -1.2 + Math.max(0, Math.sin(t * 10)) * .5; }
    else if (lt < backStart) { const k = easeIn(clamp((lt - kickT) / (outEnd - kickT))); sx = SX + Math.sin(k * Math.PI) * 120; sy = lerp(SY, -900, k); srot = k * 5; eyes = 'x'; mouth = 'O'; aL = 1.2; aR = .9; }
    else { const k = ease(clamp((lt - backStart) / (landT - backStart))); sx = SX - Math.sin(k * Math.PI) * 60; sy = lerp(-800, SY, k); srot = (1 - k) * -4; eyes = k > .7 ? 'happy' : 'wide'; mouth = 'grin'; aL = 1.2 + Math.sin(t * 14) * .1; aR = 1.2 - Math.sin(t * 14) * .1; }
    const land = lt > landT ? Math.exp(-(lt - landT) * 9) * Math.sin((lt - landT) * 40) : 0;
    const bodyY = sy - 4.5 * S;
    // the spring's anchor plate on the floor
    scrap(rectPts(740, 1670, 90, 30), '#8E939E', { torn: .5, seed: 2915 });
    spring(785, 1680, sx + Math.sin(srot) * 20, bodyY, 16, 24);
    person(sx, sy, S, { name: 'SAM', hair: 'short', top: 'hoodie', topCol: '#7A7F8C', eyes, mouth, aL, aR, rot: srot, sq: land * .12, skin: SKINS[4] });
    // the boot swings in from the left wall
    const wind = kickT - .08;
    const kick = lt < wind ? lerp(.15, -.25, ease(lt / Math.max(.01, wind))) : lt < kickT ? lerp(-.25, .62, easeIn((lt - wind) / .08)) : lt < kickT + .2 ? .62 : lerp(.62, -.9, ease((lt - kickT - .2) / .25));
    boot(-60, 1050, -kick, 60);
    if (lt > kickT - .02 && lt < kickT + .3) sticker('WHAM!', 330, 1270, 104, PAL.yellow, { pop: clamp((lt - kickT + .02) / .08), rot: -.2, size: 56, font: 'bungee' });
    camEnd();
  });

  // ---------- V1.10 (vertical): the calendar flips, the board ejects up out of the frame, EXPIRED ----------
  vshot('V1.10', (p, lt, d, t) => {
    const B = beatLen();
    fill('#B88A5C');
    ctx.fillStyle = 'rgb(60 30 10 / .18)'; for (let i = 0; i < 8; i++) ctx.fillRect(i * 150, 0, 8, H);
    const sh = shakeXY(t, 3, 20);
    // (the boardroom sits low in the frame: the ejected board has the whole height to fly up through, and under the table, at
    // the foot of the frame, are the briefcases they left behind)
    enter(lt, 540 + sh[0], 770 + sh[1], 1 + ease(p) * .04, 0, -1);
    // window: day / night strobing
    const night = frac(lt / B) > .5;
    ctx.save(); ctx.translate(0, -150);
    scrap(rectPts(590, 450, 360, 250), '#5B3A29', { torn: 1, seed: 3020, shadow: [8, 10] });
    scrap(rectPts(610, 470, 320, 210), night ? PAL.night : PAL.sky, { torn: .6, seed: 3021, shadow: false });
    if (night) { scrap(ellPts(850, 530, 34, 34, 20), '#F7EBC0', { torn: .5, shadow: false }); scrap(ellPts(866, 520, 30, 30, 20), PAL.night, { torn: .5, shadow: false }); }
    else scrap(burstPts(690, 540, 46, 12, .7, t * 2), PAL.yellow, { torn: .5, shadow: false });
    ctx.fillStyle = '#5B3A29'; ctx.fillRect(766, 470, 8, 210); ctx.fillRect(610, 571, 320, 8);
    ctx.restore();
    // calendar: a page per beat
    const flips = [0, 1, 2, 3, 4].map(k => beatLt(t, lt, k)).filter(b => b > .1).slice(0, 3);
    let bi = 0; for (const b of flips) if (lt >= b) bi++;
    const since = bi ? lt - flips[bi - 1] : 9;
    const CX = 250, CY = 300;
    scrap(rectPts(CX - 160, CY - 22, 320, 24), '#6B6F7A', { torn: .4, shadow: false });
    calPage(CX, CY, DAYS[bi][0], DAYS[bi][1]);
    if (bi > 0 && since < .22) { const k = since / .22; calPage(CX + k * 260, CY - k * 220, DAYS[bi - 1][0], DAYS[bi - 1][1], k * 1.6, 1 - k * .6); }
    for (let i = 0; i < 7; i++) dot(CX - 135 + i * 45, CY - 10, 9, PAL.ink);
    // chairs + board members, ejecting up out of the frame one after another
    const EJ = [.14, .34, .52, .7, .86].map(f => f * d * .9);
    BOARD.forEach(([, skin, top, hair, tie], i) => {
      const x = 150 + i * 195, age = lt - EJ[i];
      const up = age > 0 ? age * 1100 + age * age * 6000 : 0, spin = age > 0 ? age * (i % 2 ? 6 : -6) : 0;
      ctx.save(); ctx.translate(x, 1095 - up); ctx.rotate(spin); ctx.scale(.84, .84);
      scrap(rrPts(-85, -280, 170, 300), '#2A2426', { torn: .8, seed: 3030 + i, shadow: [6, 8] });
      for (let q = 0; q < 4; q++) dot(-40 + (q % 2) * 80, -210 + Math.floor(q / 2) * 90, 6, '#4A4246');
      person(0, 120, 30, { skin: SKINS[skin], top: 'suit', topCol: top, tie, hair, eyes: age > 0 ? 'x' : 'wide', mouth: age > 0 ? 'scream' : 'O', aL: age > 0 ? 1.3 : -1, aR: age > 0 ? 1.3 : -1, shadow: false });
      if (age > 0) { ctx.save(); ctx.translate(0, 30); ctx.rotate(Math.PI); fire(0, 0, 16, { k: .9 + jit(.12), n: 3 }); ctx.restore(); }
      ctx.restore();
      if (age > 0 && age < .5) scrap(ellPts(x, 1085, 60 + age * 160, 30 + age * 60, 16), '#EFE8DA', { torn: 3, seed: 3040 + i, shadow: false, op: 1 - age * 2 });
    });
    // under the table: its legs, the floor, the briefcases the board left behind, papers everywhere
    scrap(rectPts(-200, 1560, W + 400, 600), '#5B3A26', { torn: 1, seed: 3053, shadow: false, tone: { color: '#2E190D', cell: 12, dot: .22, op: .4 } });
    ctx.fillStyle = 'rgb(20 10 4 / .45)'; tracePath(ellPts(540, 1575, 620, 60, 30)); ctx.fill();
    for (const lx of [30, 330, 750, 1050]) scrap(rectPts(lx - 22, 1250, 44, 330), '#2E190D', { torn: .6, seed: 3054 + lx, shadow: false });
    BOARD.forEach((_, i) => {
      const x = 150 + i * 195 + (hash(i + 3060) - .5) * 50, r = (hash(i + 3061) - .5) * .5, k = clamp((lt - EJ[i]) / .2);
      ctx.save(); ctx.translate(x, 1540 - Math.sin(k * Math.PI) * 30); ctx.rotate(r + k * (i % 2 ? .3 : -.3));
      scrap(rrPts(-80, -55, 160, 110, 12), ['#6B3A1F', PAL.ink, '#3B2A20', '#7A2B22', '#2E3A4A'][i], { torn: .8, seed: 3062 + i, shadow: [6, 8], ink: PAL.ink, sw: 3 });
      marker([[-30, -55], [-24, -78], [24, -78], [30, -55]], PAL.ink, 8, { rough: 0 });
      scrap(rectPts(-80, -12, 160, 10), PAL.gold, { torn: .3, shadow: false });
      ctx.restore();
    });
    for (let i = 0; i < 8; i++) { ctx.save(); ctx.translate(60 + i * 135 + hash(i + 3070) * 40, 1650 + hash(i + 3071) * 80); ctx.rotate((hash(i + 3072) - .5) * 1.4); scrap(rectPts(-45, -30, 90, 60), PAL.white, { torn: 1, seed: 3073 + i, shadow: [3, 4] }); ctx.fillStyle = 'rgb(28 26 31 / .45)'; for (let q = 0; q < 3; q++) ctx.fillRect(-32, -16 + q * 14, 64, 4); ctx.restore(); }
    // the table
    scrap([[60, 1080], [1020, 1080], [1130, 1200], [-50, 1200]], '#4A2A18', { torn: 1, seed: 3050, shadow: [10, 12] });
    scrap([[-50, 1200], [1130, 1200], [1130, 1262], [-50, 1262]], '#2E190D', { torn: 1, seed: 3051, shadow: false });
    ctx.fillStyle = 'rgb(255 255 255 / .1)'; ctx.fillRect(80, 1092, 920, 10);
    scrap(rectPts(330, 1112, 420, 74), PAL.gold, { torn: .8, seed: 3052, ink: PAL.ink, sw: 3, shade: true, shadeOp: .25 });
    txt('THE BOARD', 540, 1150, 54, PAL.ink, { font: 'abril' });
    const bx = Math.min(beatLt(t, lt, 3), d * .75);
    stamp('EXPIRED', 540, 860, 118, PAL.red, -.12, { pop: clamp((lt - bx) / .1) });
    camEnd();
  });

  // ---------- V1.11 (vertical): the keyhole plate fills the door; WHAT DID ILYA SEE? as top text ----------
  vshot('V1.11', (p, lt, d, t) => {
    const shock = beatLt(t, lt, 1), shocked = lt > shock, sk = clamp((lt - shock) / .1);
    fill('#22142F');
    ctx.save(); ctx.globalCompositeOperation = 'screen'; glow(200, 1700, 1300, '#FFB347', .3); ctx.restore();
    const sh = shocked ? shakeXY(t, 6 * Math.exp(-(lt - shock) * 5), 30) : [0, 0];
    enter(lt, 540 + sh[0], 960 + sh[1], 1 + ease(p) * .06, 0, 1);
    for (const [x, y, w, h] of [[80, 250, 380, 520], [620, 250, 380, 520], [80, 860, 380, 560], [620, 860, 380, 560], [80, 1510, 380, 420], [620, 1510, 380, 420]]) {
      scrap(rectPts(x, y, w, h), '#33204A', { torn: 1, seed: 3100 + x + y, shadow: false, ink: 'rgb(8 4 14 / .6)', sw: 6 });
    }
    // the brass plate and the keyhole: the horizontal one, scaled up round the middle of the door
    ctx.save(); ctx.translate(540, 985); ctx.scale(1.3, 1.3); ctx.translate(-960, -520);
    const KX = 960, KY = 520;
    scrap(rrPts(KX - 150, KY - 250, 300, 560, 60), PAL.gold, { torn: 1, seed: 3110, shadow: [10, 14], ink: PAL.ink, sw: 4, shade: true, shadeOp: .3 });
    for (const yy of [KY - 205, KY + 265]) dot(KX, yy, 12, '#8A6420');
    const holePts = [...ellPts(KX, KY - 30, 105, 105, 40, Math.PI / 2 + .6).slice(0, 34), [KX - 58, KY + 50], [KX - 92, KY + 230], [KX + 92, KY + 230], [KX + 58, KY + 50]];
    scrap(holePts, '#0B0810', { torn: .8, seed: 3111, shadow: false });
    ctx.save(); tracePath(ellPts(KX, KY - 30, 98, 98, 40)); ctx.clip();
    const lookX = shocked ? 0 : [-.8, .9, -.6][Math.floor(lt / .16) % 3], blink = !shocked && lt > .22 && lt < .27;
    const ey = KY - 40, rx = 96, ry = lerp(56, 84, sk);
    scrap(rectPts(KX - 200, KY - 300, 400, 700), '#E0AC83', { torn: 0, shadow: false });
    halftoneShade(rectPts(KX - 110, KY - 140, 220, 220), PAL.ink, { dir: [0, 1], op: .5 });
    scrap(ellPts(KX, ey, rx, blink ? 6 : ry, 30), PAL.white, { torn: .6, seed: 3112, shadow: false, ink: PAL.ink, sw: 5 });
    if (!blink) {
      const ix = KX + lookX * 44;
      scrap(ellPts(ix, ey, 40, 40, 24), '#3C7FA8', { torn: .4, seed: 3113, shadow: false, ink: PAL.ink, sw: 3 });
      dot(ix, ey, lerp(20, 7, sk), PAL.ink);
      dot(ix - 14, ey - 14, 7, PAL.white);
      if (shocked) for (let i = 0; i < 4; i++) marker([[KX - 90 + i * 8, ey + 20 - i * 12], [KX - 60 + i * 6, ey + 10 - i * 10]], PAL.red, 2.5, { rough: 1 });
    }
    marker([[KX - 100, ey - ry - 12 - sk * 10], [KX, ey - ry - 26 - sk * 14], [KX + 100, ey - ry - 16 - sk * 10]], '#3A2A20', 16, { rough: 1, smooth: true });
    ctx.restore();
    ctx.save(); ctx.strokeStyle = '#0B0810'; ctx.lineWidth = 10; tracePath(ellPts(KX, KY - 30, 100, 100, 40)); ctx.stroke(); ctx.restore();
    ctx.fillStyle = 'rgb(255 255 255 / .12)'; tracePath([[KX + 30, KY + 70], [KX + 50, KY + 70], [KX + 75, KY + 210], [KX + 55, KY + 210]]); ctx.fill();
    ctx.restore();
    const EYX = 540, EYY = 985 + (KY - 40 - 520) * 1.3;
    if (shocked) for (let i = 0; i < 10; i++) {
      const a = i / 10 * TAU + .3, r0 = 330 + sk * 20;
      marker([[EYX + Math.cos(a) * r0, EYY + Math.sin(a) * r0], [EYX + Math.cos(a) * (r0 + 80 * sk), EYY + Math.sin(a) * (r0 + 80 * sk)]], PAL.yellow, 10, { rough: 1.5 });
    }
    helloTag('ILYA', 875, 1170, 28, .12);
    arrow(855, 1100, 705, 965, PAL.yellow, 9, { k: clamp(lt / .25), bend: .2 });
    ransom('WHAT DID', 515, 494, 92, { seed: 3120, pop: clamp(lt / (d * .3)) * 1.2, maxW: 860, rot: -.03 });
    ransom('ILYA SEE?', 550, 610, 92, { seed: 3121, pop: clamp((lt - d * .15) / (d * .3)) * 1.2, maxW: 860, rot: .02 });
    clawd(150, 1262, 13, { eyes: 'happy', mouth: 'smile', blush: true, aR: .9 + Math.sin(t * 16) * .35, aL: -.6, lookX: .8, lookY: -1, dy: -pulse(t, 7) * .3 });
    camEnd();
    captionStyle({ color: PAL.teal });
  });

  // ---------- V1.12 (vertical): the rulebook falls the height of the frame; gavel from below ----------
  vshot('V1.12', (p, lt, d, t) => {
    const fallT = .14, imp = lt - fallT;
    const hits = [1, 2, 3].map(k => beatLt(t, lt, k)).filter(h => h < d);
    let lastHit = -9; for (const h of hits) if (lt >= h) lastHit = h;
    const hitAge = lt - lastHit;
    fill('#1C3A9A');
    halftone(ellPts(540, 820, 620, 820, 48), PAL.blue, { cell: 22, dot: .3, op: .6, multiply: false });
    const shAmt = (imp > 0 ? 14 * Math.exp(-imp * 8) : 0) + (hitAge < .3 ? 9 * Math.exp(-hitAge * 12) : 0);
    const sh = shakeXY(t, shAmt, 30);
    enter(lt, 540 + sh[0], 960 + sh[1], 1 + ease(p) * .04, 0, -1);
    for (let i = 0; i < 12; i++) {
      const a = i / 12 * TAU + t * .35, r = 400, sc = 1 + (hitAge < .2 ? (1 - hitAge / .2) * .35 : 0);
      scrap(starPts(540 + Math.cos(a) * r, 800 + Math.sin(a) * r * 1.05, 46 * sc, .42, 5, -TAU / 4), PAL.yellow, { torn: .6, seed: 3200 + i, shadow: [4, 5] });
    }
    // (the horizontal shot's book, moved to the middle of the frame: its x centre is 960 there)
    const BY = lerp(-900, 720, easeIn(clamp(lt / fallT))), sq = imp > 0 ? Math.exp(-imp * 9) * Math.sin(imp * 45) * .07 : 0;
    ctx.save(); ctx.translate(-420, 0);
    if (imp > 0) {
      for (const [lx, ph] of [[760, 0], [850, 1.7]]) {
        ctx.save(); ctx.translate(lx, BY + 290); ctx.rotate(Math.sin(t * 22 + ph) * .5 + .3);
        scrap(rectPts(-12, 0, 24, 90), '#8E98A8', { torn: .4, shadow: false }); scrap(rectPts(-24, 80, 48, 22), PAL.ink, { torn: .3, shadow: false });
        ctx.restore();
      }
      ctx.save(); ctx.translate(1262, BY + 262); ctx.rotate(.5 + Math.sin(t * 9) * .15);
      marker([[0, 0], [0, -110]], '#8B6B43', 6, { rough: 0 });
      scrap([[0, -110], [70 + Math.sin(t * 14) * 8, -95], [0, -70]], PAL.white, { torn: .5, shadow: false, ink: PAL.ink, sw: 2 });
      ctx.restore();
    }
    ctx.save(); ctx.translate(960, BY + 200); ctx.scale(1 + sq, 1 - sq); ctx.translate(-960, -BY - 200);
    scrap(rectPts(650, BY + 110, 620, 170), '#F6F0DF', { torn: 1, seed: 3210, shadow: [16, 20] });
    ctx.fillStyle = 'rgb(28 26 31 / .25)'; for (let i = 0; i < 26; i++) ctx.fillRect(660, BY + 118 + i * 6, 600, 1.5);
    scrap(rectPts(640, BY + 270, 640, 26), '#15306E', { torn: .6, seed: 3211, shadow: false });
    for (const [bx, c] of [[800, PAL.red], [1120, PAL.yellow]]) scrap(rectPts(bx, BY + 270, 24, 70), c, { torn: .3, shadow: false });
    scrap(rectPts(640, BY - 250, 640, 380), '#F2EAD8', { torn: 1.2, seed: 3212, shadow: false, ink: '#15306E', sw: 10 });
    scrap(rectPts(640, BY - 250, 70, 380), '#15306E', { torn: .6, seed: 3213, shadow: false });
    txt('AI ACT', 990, BY - 90, 190, '#1C3A9A', { font: 'anton' });
    txt('REGULATION (EU) 2024/1689', 990, BY + 55, 30, PAL.ink, { font: 'typewriter' });
    for (let i = 0; i < 12; i++) { const a = i / 12 * TAU; scrap(starPts(1200 + Math.cos(a) * 34, BY - 190 + Math.sin(a) * 34, 8, .45), PAL.gold, { torn: 0, shadow: false }); }
    ctx.restore();
    if (imp > 0 && imp < .4) for (let i = 0; i < 6; i++) { const s = i < 3 ? -1 : 1, a = (i % 3) * .3; scrap(ellPts(960 + s * (360 + imp * 500), BY + 280 - a * 100 - imp * 60, 40 * (1 - imp * 2), 26 * (1 - imp * 2), 12), '#E9E1D0', { torn: 2, seed: 3220 + i, shadow: false }); }
    ctx.restore();
    // (its ink isn't there to read until it lands)
    sticker('458\nPAGES', 205, BY - 250, 92, PAL.pink, { pop: clamp((imp - .05) / .12), rot: -.2, size: 38, font: 'bungee' });
    // the gavel whacks on the beat, up from below the book
    const swing = hits.some(h => lt >= h && lt - h < .08) ? -1.1 : hitAge < .3 ? lerp(-1.1, .25, easeOut((hitAge - .08) / .22)) : .25;
    const h0 = hits[0] ?? d + 9;
    ctx.save(); ctx.translate(930, 1300); ctx.rotate(lt < h0 - .1 ? .25 + (lt / h0) * .1 : swing);
    gavel(0, -300, 46);
    ctx.restore();
    if (hitAge < .22) sticker('BANG!', 790, 1150, 96, PAL.red, { pop: clamp(hitAge / .06), rot: -.18 + (lastHit * 7 % 1) * .3, size: 48, font: 'bungee', textCol: PAL.white });
    camEnd();
  });

  // ---------- V1.13 (vertical): the chain of thought climbs from the strawberry up the frame, and curls over to the bulb ----------
  const CHAIN_V = spline([[455, 770], [640, 735], [800, 630], [850, 495], [760, 395], [590, 375], [430, 420]], 16);
  vshot('V1.13', (p, lt, d, t) => {
    fill(PAL.mint);
    halftone(rectPts(0, 0, W, H), PAL.green, { cell: 26, dot: .2, op: .3 });
    halftone(ellPts(400, 1720, 760, 360), PAL.teal, { cell: 14, dot: .35, op: .5 });
    enter(lt, 540, 960 - ease(p) * 30, 1 + ease(p) * .05, 0, 1);
    const bulbT = Math.min(beatLt(t, lt, 2), d * .8), N = 13, step = bulbT / N, spacing = 1 / (N + .5);
    strawberry(300, 1050 - pulse(t, 6) * 18, 60, { name: 'o1', rot: Math.sin(t * 5) * .03 });
    [[395, 805, 16], [425, 778, 22]].forEach(([x, y, r], i) => { if (lt > i * .04) scrap(ellPts(x, y, r, r, 14), PAL.white, { torn: .4, ink: PAL.ink, sw: 3, shadow: [3, 4] }); });
    const shown = Math.min(N, Math.floor(lt / step) + 1);
    for (let i = 0; i < shown; i++) {
      const u = (i + .5) * spacing, [x, y] = at(CHAIN_V, u), a = angAt(CHAIN_V, u);
      const k = clamp((lt - i * step) / .1), s = 58 * backOut(k, 2.6);
      link(x, y + Math.sin(t * 6 + i * .7) * 4, a, s, i % 2 === 0);
      // the words sit on the outside of the curl
      if (i % 2 === 0 && i / 2 < STEPS.length) txt(STEPS[i / 2], x + Math.sin(a) * 82, y - Math.cos(a) * 82, 48, PAL.ink, { font: 'marker', alpha: k, rot: a * .25 });
    }
    const bk = clamp((lt - bulbT) / .12);
    if (bk > 0) {
      const [x, y] = at(CHAIN_V, 1), s = backOut(bk, 2.4);
      ctx.save(); ctx.translate(x - 130, y + 20); ctx.scale(s, s);
      ctx.save(); ctx.globalAlpha = .6; rays(0, -20, 12, PAL.yellow, t, 240); ctx.restore();
      scrap(ellPts(0, -30, 82, 88, 28), PAL.yellow, { torn: .8, ink: PAL.ink, sw: 5, seed: 3320 });
      scrap(rectPts(-38, 46, 76, 52), '#8E939E', { torn: .5, ink: PAL.ink, sw: 4, seed: 3321, shadow: false });
      txt('!', 0, -28, 116, PAL.ink, { font: 'abril' });
      ctx.restore();
    }
    // the strawberry patch o1 grew in, along the foot of the frame: leaves and berries, nodding on the beat
    for (let i = 0; i < 9; i++) {
      const x = 40 + i * 128 + (hash(i + 3330) - .5) * 50, y = 1665 + hash(i + 3331) * 110, r = 62 + hash(i + 3332) * 34, nod = Math.sin(bpOf(t) * Math.PI + i) * .06;
      ctx.save(); ctx.translate(x, y); ctx.rotate(nod);
      scrap(starPts(0, 0, r * 1.25, .55, 7, hash(i + 3333)), i % 2 ? PAL.green : '#1F8A52', { torn: 1, seed: 3334 + i, ink: '#14633A', sw: 3, shadow: [6, 8] });
      for (let j = 0; j < 2; j++) {
        const bx = (j ? .45 : -.4) * r, by = .55 * r + j * 18, br = 26 + hash(i * 3 + j + 3340) * 12;
        scrap(heartPts(bx, by, br, 28).map(([px, py]) => [px, by - (py - by) * 1.05]), '#E8312F', { torn: .5, seed: 3341 + i * 2 + j, shadow: [3, 4], ink: '#9A1A1A', sw: 2 });
        for (let q = 0; q < 4; q++) scrap(ellPts(bx + (q % 2 - .5) * br * .6, by + (q < 2 ? -.1 : .4) * br, 3, 4.5, 6), PAL.yellow, { torn: 0, shadow: false });
      }
      ctx.restore();
    }
    camEnd();
  });

  // ---------- V1.14 (vertical): the bill above, Gavin below, staring up at it; VETO comes down from the top ----------
  vshot('V1.14', (p, lt, d, t) => {
    const vetoT = Math.min(beatLt(t, lt, 1), d * .45), blinkT = vetoT - .28, vk = clamp((lt - vetoT) / .08);
    const vetoed = lt >= vetoT;
    const BX = 540, BY = 705;
    fill('#F2B230');
    ctx.save(); ctx.globalAlpha = .5; rays(BX, BY, 16, '#FFD83A', t * .1, 2400); ctx.restore();
    halftone(rectPts(0, 0, W, H), PAL.red, { cell: 20, dot: .14, op: .25 });
    const sh = vetoed ? shakeXY(t, 12 * Math.exp(-(lt - vetoT) * 6), 30) : [0, 0];
    enter(lt, 540 + sh[0], 960 + sh[1], 1 + ease(p) * .05, 0, -1);
    const GX = 540, GY = 1925, S = 92;
    person(GX, GY, S, { hair: 'swoop', hairCol: '#3B2A1E', top: 'suit', topCol: '#22304C', tie: PAL.blue, eyes: 'dot', mouth: 'flat', aL: -1.25, aR: -1.25, skin: SKINS[0] });
    const hy = GY - 8.9 * S;
    for (const side of [-1, 1]) {
      const ex = GX + side * .5 * S + jit(1.5), ey = hy - .08 * S;
      scrap(ellPts(ex, ey, .42 * S, .46 * S, 22), PAL.white, { torn: .5, shadow: false, ink: PAL.ink, sw: 5 });
      for (let v = 0; v < 4; v++) { const a = Math.PI * (side > 0 ? .1 : .9) + (v - 1.5) * .45; marker([[ex + Math.cos(a) * .4 * S, ey + Math.sin(a) * .42 * S], [ex + Math.cos(a) * .24 * S, ey + Math.sin(a) * .26 * S]], PAL.red, 3, { rough: 1.2 }); }
      // pupils up: he's staring at the bill above him
      dot(ex - .06 * S + jit(1), ey - .2 * S, .11 * S, PAL.ink);
      marker([[ex - .38 * S, ey - .64 * S], [ex + .36 * S, ey - .7 * S]], '#3B2A1E', .1 * S, { rough: 0 });
    }
    // (his HELLO sticker on the shoulder, where the caption won't cover it)
    helloTag('GAVIN', GX - 1.05 * S, GY - 7.5 * S, .36 * S, -.12);
    doc(BX, BY, 400, 520, { title: 'SB 1047', titleSize: 80, titleFont: 'anton', lines: 10, rot: .04, seed: 3400, body: ['Safe and Secure Innovation', 'for Frontier AI Models Act'] });
    const billBlink = lt > blinkT && lt < blinkT + .12;
    for (const side of [-1, 1]) {
      const ex = BX + side * 66, ey = BY + 105;
      if (vetoed) { marker([[ex - 22, ey - 22], [ex + 22, ey + 22]], PAL.ink, 7, { rough: 0 }); marker([[ex + 22, ey - 22], [ex - 22, ey + 22]], PAL.ink, 7, { rough: 0 }); }
      else if (billBlink) marker([[ex - 30, ey], [ex + 30, ey]], PAL.ink, 7, { rough: 0 });
      else { scrap(ellPts(ex, ey, 34, 38, 16), PAL.white, { torn: .4, shadow: false, ink: PAL.ink, sw: 4 }); dot(ex, ey + 14, 13, PAL.ink); }
    }
    if (!vetoed) scrap([[BX + 100, BY + 55], [BX + 112, BY + 79], [BX + 100, BY + 87], [BX + 88, BY + 79]], PAL.sky, { torn: .3, ink: PAL.ink, sw: 3, shadow: false });
    // the stare, straight up
    if (!vetoed) {
      const pts = []; for (let i = 0; i <= 12; i++) pts.push([GX + (i % 2 ? -26 : 26) + jit(4), lerp(hy - .5 * S, BY + 150, i / 12)]);
      marker(pts, PAL.red, 8, { rough: 0 });
    }
    const sy = vetoed ? lerp(BY - 20, -800, easeIn(clamp((lt - vetoT - .1) / .3))) : lerp(-520, BY - 20, easeIn(clamp((lt - vetoT + .14) / .14)));
    if (vetoed) stamp('VETO', BX, BY + 30, 160, PAL.red, -.2, { pop: vk });
    ctx.save(); ctx.translate(BX + 10, sy); ctx.rotate(-.2);
    scrap(rectPts(-230, -40, 460, 90), '#B23A2B', { torn: .6, seed: 3410, ink: PAL.ink, sw: 4 });
    scrap(rectPts(-200, -110, 400, 76), '#6B3A1F', { torn: .6, seed: 3411, ink: PAL.ink, sw: 4 });
    scrap(rectPts(-40, -300, 80, 200), '#8B5A2B', { torn: .5, seed: 3412, ink: PAL.ink, sw: 4 });
    scrap(ellPts(0, -320, 90, 64, 24), '#6B3A1F', { torn: .6, seed: 3413, ink: PAL.ink, sw: 4 });
    ctx.restore();
    dymo('BLINKS: 0', 210, 1000, 46, PAL.red, { rot: -.08 });
    camEnd();
  });

  // ---------- V1.15 (vertical): the Nobel drops from the flies onto Geoff at the podium; BE CAREFUL! ----------
  vshot('V1.15', (p, lt, d, t) => {
    fill('#7E141C');
    for (let i = 0; i < 12; i++) { ctx.fillStyle = i % 2 ? 'rgb(0 0 0 / .22)' : 'rgb(255 120 120 / .08)'; ctx.fillRect(i * 100 + Math.sin(i * 1.3) * 10, 0, 56, H); }
    enter(lt, 540, 960, 1 + ease(p) * .05, 0, 1);
    ctx.save(); ctx.globalCompositeOperation = 'screen';
    ctx.fillStyle = 'rgb(255 236 170 / .22)'; tracePath([[420, -20], [660, -20], [900, 1500], [180, 1500]]); ctx.fill();
    glow(540, 1400, 520, '#FFE9A8', .4);
    ctx.restore();
    for (let i = 0; i < 5; i++) scrap(ellPts(i * 240 + 60, 20, 170, 90, 24), '#9A1C24', { torn: 1.5, seed: 3500 + i, shade: '#3A0508', shadeOp: .4, shadow: [6, 8] });
    scrap(rectPts(-100, 1480, W + 200, 600), '#5B3721', { torn: 1, seed: 3510, shadow: false });
    ctx.fillStyle = 'rgb(0 0 0 / .25)'; for (let i = 0; i < 12; i++) ctx.fillRect(-100, 1500 + i * 34, W + 200, 3);
    const GX = 540, GY = 1490, S = 72;
    const wag = Math.sin(lt * TAU * 4.5) * .22;
    person(GX, GY, S, {
      name: 'GEOFF', hair: 'side', hairCol: '#E9E6DF', glasses: true, top: 'sweater', topCol: '#40607F', skin: SKINS[4], brows: 'angry', mouth: 'O',
      aL: -1.15, aR: 1.25 + wag,
      hold: s => { scrap(rrPts(-.16 * s, -1.25 * s, .32 * s, 1 * s, .15 * s), SKINS[4], { torn: .3, shadow: false, ink: alpha(PAL.ink, .4), sw: 1.5 }); },
    });
    // the medal drops all the way down from the flies round his neck
    const mk = clamp(lt / .24), my = lerp(-500, GY - 4.35 * S, easeIn(mk)) + (mk >= 1 ? Math.sin((lt - .24) * 30) * Math.exp(-(lt - .24) * 8) * 16 : 0);
    const mx = GX - .62 * S;
    marker([[GX - .75 * S, my - 2.6 * S], [mx - .25 * S, my - .7 * S]], PAL.blue, .45 * S, { rough: 0 });
    marker([[GX + .6 * S, my - 2.6 * S], [mx + .3 * S, my - .7 * S]], PAL.blue, .45 * S, { rough: 0 });
    if (mk < 1) for (const sd of [-1, 1]) marker([[GX + sd * .7 * S, my - 2.6 * S], [GX + sd * .7 * S, my - 2.6 * S - 1400]], PAL.blue, .3 * S, { rough: 0 });
    scrap(ellPts(mx, my, .95 * S, .95 * S, 28), PAL.gold, { torn: .6, ink: PAL.ink, sw: 4, shade: true, shadeOp: .3, seed: 3520 });
    txt('NOBEL', mx, my + 2, .46 * S, PAL.ink, { font: 'abril' });
    // podium
    scrap([[280, 1215], [800, 1215], [770, 1500], [310, 1500]], '#2B2240', { torn: 1, seed: 3530, shadow: [10, 12] });
    scrap(rectPts(260, 1195, 560, 40), '#3E3358', { torn: .8, seed: 3531, shadow: false });
    txt('PHYSICS 2024', 540, 1262, 46, PAL.gold, { font: 'abril' });
    bubble('BE CAREFUL!', 330, 480, { size: 70, pop: clamp((lt - Math.min(beatLt(t, lt, 1), d * .3)) / .12), tail: [GX - 40, GY - 9.2 * S], rot: -.05 });
    // the audience, front rows along the foot of the frame, clapping; their cameras flash on the beat
    crowd(1745, t, { n: 7, s: 130, col: '#2A0A10', hands: .7, jump: .12, seed: 3540, x0: -40, x1: W + 40 });
    crowd(1860, t, { n: 6, s: 160, col: '#14050A', hands: .5, jump: .1, seed: 3550, x0: -80, x1: W + 80 });
    for (let k = 0; k < 4; k++) {
      const bt = beatLt(t, lt, k), age = lt - bt; if (age < 0 || age > .14) continue;
      const fx = [140, 950, 330, 760][k], fy = [1100, 1000, 1640, 1690][k];
      glow(fx, fy, 220, PAL.white, .9 * (1 - age / .14));
      scrap(burstPts(fx, fy, 70 * (1 - age / .14) + 20, 8, .3), PAL.white, { torn: .5, shadow: false });
    }
    camEnd();
  });

  // ---------- V1.16 (vertical): the ribbon streams up from Demis's hand and folds itself into the medal ----------
  vshot('V1.16', (p, lt, d, t) => {
    const foldT = Math.min(beatLt(t, lt, 1), d * .6), fk = ease(clamp(lt / foldT)), popK = clamp((lt - foldT) / .1);
    fill(PAL.pink);
    ctx.save(); ctx.globalAlpha = .35; rays(640, 600, 24, PAL.purple, t * .2, 2400); ctx.restore();
    halftone(rectPts(0, 0, W, H), PAL.purple, { cell: 22, dot: .16, op: .3 });
    enter(lt, 540, 960, 1 + ease(p) * .05, 0, -1);
    const DX = 270, DY = 1480, S = 62;
    person(DX, DY, S, { name: 'DEMIS', hair: 'short', hairCol: '#2A2320', top: 'coat', topCol: PAL.white, skin: SKINS[2], eyes: popK > 0 ? 'happy' : 'dot', mouth: popK > 0 ? 'grin' : 'o', aL: -.5 + Math.sin(t * 9) * .1, aR: .75 + Math.sin(t * 7) * .15 });
    const hx = DX + 1.35 * S + Math.cos(.75) * 3.2 * S, hy = DY - 7.1 * S - Math.sin(.75) * 3.2 * S;
    const KX = 640, KY = 600;
    if (popK > 0) {
      ctx.save(); ctx.translate(KX, KY); const s = backOut(popK, 2.2); ctx.scale(s, s);
      scrap([[-120, -760], [-40, -140], [40, -140], [120, -760]], PAL.blue, { torn: .6, seed: 3600, shadow: [6, 8] });
      scrap(ellPts(0, 0, 210, 210, 40), PAL.gold, { torn: 1, ink: PAL.ink, sw: 6, shade: true, shadeOp: .3, seed: 3601 });
      ctx.strokeStyle = alpha(PAL.ink, .45); ctx.lineWidth = 5; ctx.beginPath(); ctx.arc(0, 0, 168, 0, TAU); ctx.stroke();
      ctx.restore();
    }
    // the ribbon: a long strand streaming up from his hand → the compact fold
    const pts = [];
    for (let i = 0; i < RIBBON_N; i++) {
      const u = i / (RIBBON_N - 1);
      const x0 = hx + 60 + Math.sin(u * TAU * 2.2 + t * 3) * 90 + Math.sin(u * TAU * 16) * 20 + u * 160, y0 = hy - 40 - u * 1050;
      let x1, y1;
      if (u < .06) { x1 = lerp(hx, KX - 120, u / .06); y1 = lerp(hy, KY + 120, u / .06); }
      else { const v = (u - .06) / .94, th = v * TAU * 2.2 + 2.6, r = 62 + 64 * Math.abs(Math.sin(th * 1.6)); x1 = KX + Math.cos(th) * r + Math.sin(u * TAU * 16) * 10; y1 = KY + Math.sin(th) * r + Math.cos(u * TAU * 16) * 10; }
      pts.push([lerp(x0, x1, fk), lerp(y0, y1, fk)]);
    }
    marker(pts, PAL.ink, 30, { rough: 0 });
    for (let i = 0; i < RIBBON_N - 1; i++) {
      const c = PLDDT[Math.min(4, Math.floor(i / (RIBBON_N - 1) * 5))];
      marker([pts[i], pts[i + 1]], c, 20, { rough: 0 });
    }
    if (popK > 0) for (let i = 0; i < 80; i++) {
      const age = lt - foldT, x0 = hash(i + 3610) * W, sp = 480 + hash(i + 3611) * 600;
      const cx = x0 + Math.sin(age * 6 + i) * 40 + (hash(i + 3612) - .5) * 300 * age, cy = -40 + age * sp + (hash(i + 3613) - .7) * 900 * (1 - age);
      ctx.save(); ctx.translate(cx, cy); ctx.rotate(age * 8 + i); ctx.scale(1, Math.cos(age * 12 + i));
      ctx.fillStyle = [PAL.yellow, PAL.blue, PAL.white, PAL.teal, PAL.gold, PAL.red][i % 6]; ctx.fillRect(-10, -6, 20, 12);
      ctx.restore();
    }
    sticker('NOBEL!', 820, 940, 120, PAL.yellow, { pop: clamp((lt - foldT - .05) / .12), rot: .15, size: 50, font: 'bungee' });
    camEnd();
  });
})();

;
// ---- src/ch/c03_chorus1.js ----
// c03_chorus1 — Chorus 1: the band's first show, in a basement (venue level 1).
//   line 1  "We didn't start the scaling —"   lights slam on, establishing wide, then punch in on Clawd under a giant ransom hook.
//   line 2a "It was always training,"          over Clawd's shoulder: the basement crowd, a STILL TRAINING… 99% sign, a GPU crowd-surfing.
//   line 2b "and the curves kept gaining,"     amp insert: Robo's claw cranks the GAIN knob past 10 — 11, 12, 100, 10^26 — on the beats.
//   line 3  "We didn't start the scaling —"   band wide under the hook; the CONTAINMENT crate at the stage lip twitches.
//   line 4a "No, we didn't preordain it,"      the crate rattles harder every beat; Clawd side-eyes it, sweating.
//   line 4b "but we can't contain it!"         chains snap, the lid blasts off, the red curve springs out like a jack-in-the-box,
//                                              agent critters leap into the crowd, the camera pulls back as the basement shakes.
(() => {
  const GY = STAGE_Y + 70;                       // band ground line (band.js)
  // (in the vertical video the crate sits between Robo and Clawd, so that one tall shot holds both it and him)
  const CRATE_X = VERT ? 730 : 300, CRATE_Y = 915, CRATE_S = 22;
  const snapBeat = x => onBeat(0, Math.round(bpOf(x)));
  const beatAfter = (x, n) => onBeat(0, Math.round(bpOf(x)) + n);

  // ---------- timing of the sub-shots, from the sung lines ----------
  function plan() {
    const S = span('C1'), L = linesOf('C1');
    let down = Math.ceil(bpOf(S.start + .05)); while (((down % 4) + 4) % 4) down++;
    const tDown = onBeat(0, down);
    const tB = L[1].start - .05, tC = snapBeat(lerp(L[1].start, L[1].end, .47)), tD = L[2].start - .05;
    const tE = L[3].start - .03, tE2 = snapBeat(lerp(L[3].start, L[3].end, .52));
    return { S, L, tDown: Math.min(tDown, tB - .6), tB, tC, tD, tE, tE2 };
  }

  // ---------- the hook: the zine-cover title from the intro, word by word as it's sung ----------
  const HOOK = [
    { w: 'WE', seed: 4101, at: 0 }, { w: "DIDN'T", seed: 4207, at: .1 }, { w: 'START', seed: 4311, at: .25 },
    { w: 'THE', seed: 4419, at: .4 }, { w: 'SCALING', seed: 4523, at: .7, big: true },
  ];
  const HOOK_FONTS = ['anton', 'abril', 'archivo', 'bungee', 'mono', 'shrikhand', 'courier', 'bebas', 'rammetto', 'typewriter'];
  const HOOK_LOUD = [PAL.yellow, PAL.pink, PAL.white, PAL.red, PAL.ink, PAL.yellow, PAL.sky];
  function bigHook(t, ln, y0 = 150) {
    if (!ln || t > ln.end + .35) return;
    const dur = ln.end - ln.start;
    [[0, 1, 2], [3, 4]].forEach((row, r) => {
      const size = r ? 150 : 112, ro = h => ({ seed: h.seed, fonts: HOOK_FONTS, papers: h.big ? HOOK_LOUD : undefined, maxW: h.big ? 1000 : undefined });
      const ws = row.map(i => ransom(HOOK[i].w, 0, 0, size, { ...ro(HOOK[i]), pop: 0 }));
      let x = W / 2 - (ws.reduce((a, b) => a + b, 0) + 40 * (row.length - 1)) / 2;
      row.forEach((i, j) => {
        const h = HOOK[i], cx = x + ws[j] / 2; x += ws[j] + 40;
        const a = t - (ln.start + h.at * dur) + .03; if (a <= 0) return;
        ransom(h.w, cx, y0 + r * 150 - (h.big ? pulse(t, 7) * 10 : 0), size, { ...ro(h), pop: a / .2, jolt: 1.2 + 4 * pulse(t, 9), rot: h.big ? -.025 : (j % 2 ? .02 : -.02) });
      });
    });
  }

  // ---------- basement dressing drawn over venue(t, 1) ----------
  function ceiling(t, wild = 0) {
    ctx.fillStyle = '#211712'; ctx.fillRect(-500, -500, W + 1000, 520);
    for (let i = -3; i < 16; i++) scrap(rectPts(i * 150 + 30, -60, 64, 84), '#3E2A1E', { torn: .8, seed: 2001 + i, shadow: [4, 6] });
    scrap(rectPts(-500, -8, W + 1000, 26), '#8C8F99', { torn: .6, seed: 2030, shadow: [4, 7], shade: true, shadeOp: .25 });
    // bare bulb on a cord, swinging with the beat
    const sw = Math.sin(bpOf(t) * Math.PI / 2) * (.12 + wild * .5);
    ctx.save(); ctx.translate(110, 0); ctx.rotate(sw);
    marker([[0, 0], [0, 190]], PAL.ink, 5, { rough: 0 });
    ctx.fillStyle = alpha(PAL.yellow, .22 + .12 * pulse(t, 4)); tracePath(ellPts(0, 225, 95, 95, 24)); ctx.fill();
    scrap(rectPts(-14, 186, 28, 22), '#6E6E78', { torn: .3, shadow: false });
    scrap(ellPts(0, 228, 26, 30, 16), '#FFF3B0', { torn: .5, shadow: false, ink: PAL.ink, sw: 2 });
    ctx.restore();
  }
  function momNote(t, x = 1760, y = 380, fall = 0) {
    ctx.save(); ctx.translate(x - fall * 120, y + fall * fall * 900); ctx.rotate(.07 + jit(.006) - fall * 2.4);
    scrap(ctrRect(0, 0, 196, 176), PAL.yellow, { torn: 1.5, seed: 2041, shadow: [6, 8] });
    txt('KEEP IT', 0, -44, 38, PAL.ink, { font: 'marker' });
    txt('DOWN!!', 0, 2, 44, PAL.red, { font: 'marker' });
    txt('— MOM', 18, 52, 30, PAL.ink, { font: 'marker' });
    ctx.restore();
    if (!fall) tape(x - 10, y - 88, 90, -.1, { seed: 2042, h: 28 });
  }
  // Moshing heads along the stage lip.
  const frontCrowd = (t, jump = .75) => crowd(1018, t, { n: 13, s: 66, col: '#0E0B16', hands: .55, horns: true, jump, seed: 971 });
  // Plaster dust sifting down from the ceiling on every beat (more when `amt` is higher).
  function dust(t, amt = 1) {
    const b = beatN(t), n = Math.round(7 * amt);
    ctx.fillStyle = alpha('#E4DACB', .85);
    for (let k = 0; k < 3; k++) {
      const bn = b - k, age = t - onBeat(0, bn); if (age < 0) continue;
      for (let i = 0; i < n; i++) {
        const y = 22 + age * 160 + age * age * 900; if (y > 1100) continue;
        const x = hash2(bn, i) * 2000 - 40 + Math.sin(age * 6 + i) * 12, r = 3 + hash2(bn, i + 40) * 5;
        ctx.fillRect(x, y, r, r);
      }
    }
  }

  // ---------- the CONTAINMENT crate ----------
  // (x, y) = bottom centre; ≈ 10s wide, 7s tall. o: rattle (0..1), hop (px), chains (0..1 intact), lock (0..1 attached), open (lid gone)
  function crate(x, y, s, t, o = {}) {
    const rat = o.rattle ?? 0, w = 10 * s, h = 7 * s;
    ctx.save(); ctx.translate(x + jit(rat * 6), y - (o.hop ?? 0) - Math.abs(jit(rat * 5))); ctx.rotate(jit(rat * .03) + (o.rot ?? 0));
    if (o.open) { // light pouring out of the open top
      ctx.save(); ctx.globalCompositeOperation = 'screen';
      for (let i = 0; i < 7; i++) {
        const a = -Math.PI / 2 + (i - 3) * .24 + Math.sin(t * 3 + i) * .03, L = 900 + hash(i) * 400;
        ctx.fillStyle = alpha(i % 2 ? PAL.yellow : PAL.white, .22 * o.open);
        tracePath([[-w * .3, -h], [w * .3, -h], [Math.cos(a + .06) * L, -h + Math.sin(a + .06) * L], [Math.cos(a - .06) * L, -h + Math.sin(a - .06) * L]]); ctx.fill();
      }
      ctx.restore();
      scrap(rectPts(-w / 2 + .6 * s, -h - .3 * s, w - 1.2 * s, .8 * s), '#1A120C', { torn: .6, seed: 2112, shadow: false });
    }
    scrap(rectPts(-w / 2, -h, w, h), '#C4935F', { torn: 1, seed: 2101, shadow: [8, 10], shade: '#6B4A2A', shadeOp: .28 });
    ctx.fillStyle = 'rgb(70 45 22 / .55)'; for (let i = 1; i < 4; i++) ctx.fillRect(-w / 2, -h + i * h / 4, w, 3);
    for (const side of [-1, 1]) scrap(rectPts(side < 0 ? -w / 2 : w / 2 - .8 * s, -h, .8 * s, h), '#8E6538', { torn: .6, seed: 2102 + side, shadow: false });
    txt('CONTAINMENT', 0, -h * .64, 1.05 * s, PAL.ink, { font: 'mono', maxW: w * .8 });
    stamp('DO NOT OPEN', 0, -h * .4, .62 * s, PAL.red, -.06, { pop: 1 });

    // chains (an X of links) and the padlock
    const ch = o.chains ?? 1;
    if (ch > 0) {
      ctx.save(); ctx.globalAlpha *= ch; ctx.translate(0, (1 - ch) * 3 * s);
      ctx.strokeStyle = '#9A9AA6'; ctx.lineWidth = .22 * s;
      for (const [x0, y0, x1, y1] of [[-w / 2 - .2 * s, -h * .88, w / 2 + .2 * s, -h * .86], [-w / 2 - .2 * s, -h * .15, w / 2 + .2 * s, -h * .13]]) {
        const n = 16, a = Math.atan2(y1 - y0, x1 - x0);
        for (let i = 0; i <= n; i++) { ctx.beginPath(); ctx.ellipse(lerp(x0, x1, i / n), lerp(y0, y1, i / n), .42 * s, .24 * s, a + (i % 2) * .6, 0, TAU); ctx.stroke(); }
      }
      ctx.restore();
    }
    const lk = o.lock ?? 1;
    if (lk > 0) {
      const lx = o.lockOff ? o.lockOff[0] : 0, ly = o.lockOff ? o.lockOff[1] : 0;
      ctx.save(); ctx.translate(lx, -h * .1 + ly); ctx.rotate(o.lockRot ?? 0);
      ctx.strokeStyle = '#8C8F99'; ctx.lineWidth = .35 * s; ctx.beginPath(); ctx.arc(0, -.5 * s, .75 * s, Math.PI, TAU); ctx.stroke();
      scrap(rrPts(-1.1 * s, -.6 * s, 2.2 * s, 1.8 * s, .3 * s), PAL.gold, { torn: .4, seed: 2110, ink: PAL.ink, sw: .12 * s, shadow: [3, 4] });
      scrap(ellPts(0, .2 * s, .22 * s, .3 * s, 10), PAL.ink, { torn: .1, shadow: false });
      ctx.restore();
    }
    if (!o.open) scrap(rectPts(-w / 2 - .3 * s, -h - .8 * s, w + .6 * s, .9 * s), '#A87B4C', { torn: .8, seed: 2111, shadow: [4, 5] });
    ctx.restore();
  }

  // Clawd at his band.js spot, with pose overrides (bandmates(..., { clawd: false }) skips the stock one).
  function frontman(t, o = {}) {
    const b = bpOf(t), p = pulse(t, 7), hop = Math.max(0, Math.sin(b * Math.PI)) ** 2;
    micStand(960 - 150, STAGE_Y + 60, 26);
    const co = { hat: 'mohawk', eyes: 'shades', mouth: singMouth(t), mic: true, aR: .5 + p * .5, aL: -.2 + hop * .7, dy: -hop * 1.4, sq: -hop * .08 + p * .05, ...o };
    clawd(960, GY, 30, co);
    return co;
  }
  // Devil-horns hand on the tip of one of Clawd's nub arms (mirrors clawd()'s arm transform; no rot/flip).
  function horns(x, y, u, o, side, k = 1) {
    if (k <= 0) return;
    const ang = side > 0 ? (o.aR ?? -.2) : (o.aL ?? -.2), sq = o.sq ?? 0;
    ctx.save(); ctx.translate(x, y + (o.dy ?? 0) * u); ctx.scale(1 + sq * .5, 1 - sq);
    ctx.translate(side * 5 * u, -4.9 * u); ctx.rotate(side * -ang); ctx.translate(side * 2.2 * u, 0);
    const s = backOut(k, 2.6); ctx.scale(s, s);
    for (const dy of [-.62, .62]) scrap(xform(rrPts(side > 0 ? .4 * u : -2.6 * u, -.26 * u, 2.2 * u, .52 * u, .24 * u), 0, dy * u, dy * side * .25, 1, 0, 0), PAL.clawdLt, { torn: .5, seed: 2131 + dy * 10, ink: PAL.ink, sw: .12 * u, shadow: false });
    scrap(rrPts(-.9 * u, -.9 * u, 1.8 * u, 1.8 * u, .45 * u), PAL.clawdLt, { torn: .5, seed: 2133, ink: PAL.ink, sw: .12 * u, shadow: [.1 * u, .15 * u] });
    ctx.restore();
  }
  // Sweat drops flung off a performer on each beat.
  function sweatFling(t, x, y, n = 4, seed = 0) {
    const b = beatN(t), age = t - onBeat(0, b);
    if (age > .35) return;
    for (let i = 0; i < n; i++) {
      const a = -Math.PI / 2 + (hash2(b + seed, i) - .5) * 2.6, v = 260 + hash2(b + seed, i + 9) * 200;
      const px = x + Math.cos(a) * v * age, py = y + Math.sin(a) * v * age + 900 * age * age;
      scrap([[px, py - 14], [px + 8, py + 2], [px, py + 9], [px - 8, py + 2]], PAL.sky, { torn: .3, ink: PAL.ink, sw: 2, shadow: false, op: 1 - age / .35 });
    }
  }
  // (well past the frame's edges: in the vertical video the amp shot draws through inStage(), whose 1920 × 1080 world is shorter
  // than the tall frame, and a flash that stopped at its edge would draw a hard line across the picture)
  const flash = (t, t0, dur = .16, a = .6) => { const k = (t - t0) / dur; if (k >= 0 && k < 1) { ctx.fillStyle = `rgb(255 250 230 / ${(a * (1 - k)).toFixed(3)})`; ctx.fillRect(-W, -H, W * 3, H * 3); } };

  // The standard stage: venue + basement + band (+ optional crate state) + moshers + dust.
  function stage(t, o = {}) {
    venue(t, 1, { bannerTitle: o.bannerTitle });
    ceiling(t, o.wild ?? 0);
    momNote(t, undefined, undefined, o.momFall ?? 0);
    bandmates(t, 1, { clawd: o.clawd === undefined ? undefined : false, ...(VERT ? VBAND : {}) });
    if (o.clawd) o.clawd();
    crate(CRATE_X, CRATE_Y, CRATE_S, t, o.crate ?? {});
    if (o.afterCrate) o.afterCrate();
    frontCrowd(t, o.jump ?? .75);
    dust(t, o.dust ?? 1);
  }

  // =============== line 2a: over Clawd's shoulder, the basement crowd ===============
  function clawdBack(x, y, u, t) {
    const b = bpOf(t), hop = Math.max(0, Math.sin(b * Math.PI)) ** 2, p = pulse(t, 7);
    ctx.save(); ctx.translate(x, y - hop * u * 1.1);
    [-3.6, -1.4, 1.4, 3.6].forEach((lx, i) => scrap(rectPts((lx - .55) * u, -2.1 * u, 1.1 * u, 2.1 * u), PAL.clawdDk, { torn: .8, seed: 2201 + i, shadow: false }));
    for (const [side, ang] of [[-1, .55 + hop * .4], [1, 1.25 + p * .2]]) {
      ctx.save(); ctx.translate(side * 5 * u, -4.9 * u); ctx.rotate(side * -ang);
      scrap(rectPts(side > 0 ? -.2 * u : -1.9 * u, -.6 * u, 2.1 * u, 1.2 * u), PAL.clawd, { torn: .8, seed: 2210 + side, shadow: false });
      if (side > 0) { // the mic, held out to the crowd
        ctx.save(); ctx.translate(2 * u, 0); ctx.rotate(1.7);
        scrap(rectPts(-.3 * u, -2.6 * u, .6 * u, 2.4 * u), PAL.ink, { torn: .5, shadow: false });
        scrap(ellPts(0, -2.9 * u, .75 * u, .9 * u, 16), '#8C8A92', { torn: .5, shadow: false, tone: { color: PAL.ink, cell: 5, dot: .3 } });
        ctx.restore();
      }
      ctx.restore();
    }
    scrap(rectPts(-5 * u, -8 * u, 10 * u, 6 * u), PAL.clawd, { torn: 1.2, seed: 2220, shadow: [u * .35, u * .45], shade: PAL.clawdDk, shadeDir: [-1, 1], shadeOp: .35 });
    marker([[3 * u, -2.2 * u], [2.4 * u, -1 * u], [3.8 * u, .5 * u]], PAL.ink, .25 * u, { rough: .5, smooth: true }); // mic cable
    for (let i = 0; i < 5; i++) {
      const hx = (-2.5 + i * 1.25) * u, hh = (2.2 + (i === 2 ? .8 : i % 2 ? .4 : 0)) * u;
      scrap([[hx - .65 * u, -7.8 * u], [hx + jit(.05) * u, -7.8 * u - hh], [hx + .65 * u, -7.8 * u]], i % 2 ? PAL.pink : '#FF78BD', { torn: .5, seed: 2230 + i, shadow: false, ink: PAL.ink, sw: .12 * u });
    }
    ctx.restore();
  }
  function placard(x, y, w, h, rot, col, draw) {
    marker([[x, y + h * .3], [x - rot * 200, y + h / 2 + 420]], '#8B6B43', 14, { rough: 0 });
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot);
    scrap(ctrRect(0, 0, w, h), col, { torn: 2.5, seed: 2240 + Math.round(w), shadow: [7, 9] });
    draw(w, h);
    ctx.restore();
  }
  function washer(x, y, t) { // (x, y) = top-left
    scrap(rrPts(x, y, 250, 300, 14), '#E8E6DF', { torn: 1.2, seed: 2251, shadow: [8, 10], shade: true, shadeOp: .2 });
    scrap(rectPts(x + 10, y + 12, 230, 52), '#C9CCD6', { torn: .6, seed: 2252, shadow: false });
    for (let i = 0; i < 3; i++) scrap(ellPts(x + 40 + i * 34, y + 38, 11, 11, 10), '#6E6E78', { torn: .2, shadow: false });
    txt('SPIN', x + 190, y + 38, 26, PAL.red, { font: 'archivo' });
    scrap(ellPts(x + 125, y + 190, 84, 84, 28), '#8C8F99', { torn: .6, seed: 2253, shadow: false });
    ctx.save(); ctx.translate(x + 125, y + 190); ctx.rotate(t * 7);
    scrap(ellPts(0, 0, 66, 66, 24), '#4C6A8C', { torn: .4, shadow: false });
    for (let i = 0; i < 3; i++) { ctx.rotate(TAU / 3); scrap(ellPts(28, 0, 26, 16, 12), [PAL.pink, PAL.yellow, PAL.mint][i], { torn: .6, seed: 2254 + i, shadow: false }); }
    ctx.restore();
    ctx.fillStyle = 'rgb(255 255 255 / .35)'; tracePath(ellPts(x + 100, y + 160, 22, 12, 12, -.6)); ctx.fill();
  }
  function heater(x, y) { // (x, y) = top-left
    scrap(rectPts(x + 70, -40, 22, y + 50), '#B87333', { torn: .4, seed: 2261, shadow: [4, 6] });
    scrap(rectPts(x + 130, -40, 22, y + 50), '#8C8F99', { torn: .4, seed: 2262, shadow: [4, 6] });
    scrap(rrPts(x, y, 220, 520, 60), '#D8D4C8', { torn: 1.2, seed: 2263, shadow: [8, 10], shade: true, shadeOp: .28 });
    scrap(rectPts(x + 50, y + 150, 120, 90), PAL.white, { torn: .8, seed: 2264, shadow: false });
    txt('WATER', x + 110, y + 178, 26, PAL.ink, { font: 'archivo' });
    txt('HEATER', x + 110, y + 210, 26, PAL.ink, { font: 'archivo' });
    stamp('HOT', x + 110, y + 330, 40, PAL.red, .1);
  }
  // ---------- the crowd-surfing GPU, held up by the hands of the people under it ----------
  // carryRow(y, t, o, g, w): a row of crowd() (the same people, drawn the same way) whose people under the GPU g = { x, y, s, rot }
  // (gpu()'s frame) reach up and hold it, as far as w (0..1: how much this row is carrying it right now) lets them; each arm grows
  // out of its own shoulder, so the hands are always someone's. Returns the hands that touch it, for gripHands() to draw over the
  // GPU's lower edge once it's drawn (a row in front of the GPU can draw them straight away).
  function carryRow(y, t, o, g, w) {
    const n = o.n ?? 22, x0 = o.x0 ?? -40, x1 = o.x1 ?? W + 40, s = o.s ?? 60, seed = o.seed ?? 900, col = o.col ?? PAL.ink;
    const c = Math.cos(g.rot), sn = Math.sin(g.rot), half = 4.6 * g.s, grips = [];
    for (let i = 0; i < n; i++) {
      const r = k => hash2(seed + i, k), x = lerp(x0, x1, (i + .5) / n) + (r(1) - .5) * 30, sz = s * (.85 + r(4) * .35);
      // under the GPU (or just past its ends, reaching after it), within reach of this row
      const hold = w * (1 - ease((Math.abs(x - g.x) - half - .45 * sz) / (1.6 * sz)));
      const ph = r(2), jump = (o.jump ?? .6) * Math.max(0, Math.sin((bpOf(t) + ph) * Math.PI)) ** 2 * s * .5 * (1 - .75 * hold);
      const hy = y - jump + r(3) * s * .3;
      ctx.fillStyle = col;
      tracePath(ellPts(x, hy, sz * .42, sz * .48, 14)); ctx.fill();
      tracePath([[x - sz * .75, hy + sz * .45], [x + sz * .75, hy + sz * .45], [x + sz * .9, H + 50], [x - sz * .9, H + 50]]); ctx.fill();
      const up = r(5) < (o.hands ?? .5), wave = Math.sin((bpOf(t) * .5 + ph) * TAU) * .25;
      const raised = !up ? [] : r(6) < .5 ? [-1, 1] : [r(7) < .5 ? -1 : 1];
      ctx.lineWidth = sz * .22; ctx.lineCap = 'round'; ctx.strokeStyle = col;
      for (const side of hold > 0 ? [-1, 1] : raised) {
        const sx = x + side * sz * .6, sy = hy + sz * .6;
        // the arm's own pose (up, as crowd() draws it, or down at the side), and the point on the GPU's underside above the hand
        const nx = raised.includes(side) ? x + side * sz * (.9 + wave) : sx, ny = raised.includes(side) ? hy - sz * 1.1 : sy;
        const lx = clamp((x + side * sz * .42 - g.x + 2.6 * g.s * sn) / c, -half, half);
        let hx = g.x + lx * c - 2.6 * g.s * sn, hy2 = g.y + lx * sn + 2.6 * g.s * c;
        const dx = hx - sx, dy = hy2 - sy, len = Math.hypot(dx, dy), reach = 2.3 * sz;
        if (len > reach) { hx = sx + dx / len * reach; hy2 = sy + dy / len * reach; }
        const k = ease(hold), ex = lerp(nx, hx, k), ey = lerp(ny, hy2, k);
        ctx.beginPath(); ctx.moveTo(sx, sy); ctx.lineTo(ex, ey); ctx.stroke();
        if (hold < .2 && raised.includes(side) && o.horns && r(9) < .5) {
          ctx.lineWidth = sz * .08; ctx.beginPath(); ctx.moveTo(ex - sz * .12, ey); ctx.lineTo(ex - sz * .18, ey - sz * .35); ctx.moveTo(ex + sz * .12, ey); ctx.lineTo(ex + sz * .18, ey - sz * .35); ctx.stroke(); ctx.lineWidth = sz * .22;
        }
        if (k > .97 && len <= reach) grips.push({ x: ex, y: ey, sz, rot: g.rot + side * .12, col });
      }
    }
    return grips;
  }
  // the hands under the GPU: a palm and three fingers each, over its lower edge
  function gripHands(grips) {
    for (const h of grips) {
      ctx.save(); ctx.translate(h.x, h.y); ctx.rotate(h.rot);
      ctx.fillStyle = h.col; ctx.strokeStyle = h.col; ctx.lineCap = 'round';
      tracePath(ellPts(0, h.sz * .1, h.sz * .17, h.sz * .13, 12)); ctx.fill();
      ctx.lineWidth = h.sz * .075;
      for (const f of [-1, 0, 1]) { ctx.beginPath(); ctx.moveTo(f * h.sz * .09, h.sz * .05); ctx.lineTo(f * h.sz * .13, -h.sz * .16); ctx.stroke(); }
      ctx.restore();
    }
  }
  function crowdShot(t, lt, d) {
    const [sx, sy] = shakeXY(t, 3 + pulse(t, 6) * 5, 20);
    camBegin(W / 2 + sx - lt * 20, H / 2 + sy, 1.04 + lt * .02, 0);
    // back wall: painted cinder block washed by the stage lights
    ctx.fillStyle = '#9A8E86'; ctx.fillRect(-300, -300, W + 600, H + 600);
    ctx.fillStyle = 'rgb(60 50 50 / .28)';
    for (let r = 0; r < 12; r++) for (let c = -1; c < 11; c++) ctx.fillRect(c * 200 + (r % 2) * 100, 30 + r * 92, 196, 4), ctx.fillRect(c * 200 + (r % 2) * 100, 30 + r * 92, 4, 92);
    halftone(rectPts(-300, -300, W + 600, H + 600), '#5B4E66', { cell: 22, dot: .2, op: .45 });
    ceiling(t);
    washer(110, 420, t);
    heater(1640, 280);
    // coloured stage light washing the room
    ctx.save(); ctx.globalCompositeOperation = 'screen';
    const sw = Math.sin(bpOf(t) * Math.PI / 4) * 160;
    ctx.fillStyle = alpha(PAL.pink, .22); tracePath([[700, 1300], [900, 1300], [1300 + sw, -100], [500 + sw, -100]]); ctx.fill();
    ctx.fillStyle = alpha(PAL.yellow, .18); tracePath([[1100, 1300], [1300, 1300], [1500 - sw, -100], [900 - sw, -100]]); ctx.fill();
    ctx.restore();
    // a GPU crowd-surfing across the room, passed hand to hand along the back row
    const gk = clamp(lt / d);
    const G = { x: lerp(-180, 2100, gk), y: 548 + Math.sin(bpOf(t) * Math.PI) * 18, s: 17, rot: Math.sin(t * 5) * .12 };
    // back row of moshers
    const grips = carryRow(655, t, { n: 10, s: 72, col: '#3A3050', hands: .6, horns: true, jump: .9, seed: 931 }, G, 1);
    // signs
    const bob = i => -pulse(t + i * .2, 5) * 22;
    placard(560, 370 + bob(0), 330, 160, -.08 + wob(t, .7) * .03, '#D9B98C', (w, h) => {
      txt('MORE', 0, -34, 60, PAL.ink, { font: 'marker' }); txt('LAYERS!', 0, 30, 60, PAL.red, { font: 'marker' });
    });
    placard(1280, 330 + bob(1), 420, 190, .06 + wob(t, .6, .3) * .03, PAL.white, (w, h) => {
      txt('STILL TRAINING…', 0, -48, 50, PAL.ink, { font: 'marker', maxW: w - 40 });
      const bw = w - 70, fill = .99;
      scrap(rectPts(-bw / 2, 0, bw, 44), PAL.white, { torn: 1, shadow: false, ink: PAL.ink, sw: 5, seed: 2245 });
      scrap(rectPts(-bw / 2 + 6, 6, (bw - 12) * fill, 32), PAL.green, { torn: .8, shadow: false, seed: 2246 });
      txt('99%', bw / 2 - 40, 22, 30, PAL.white, { font: 'anton' });
    });
    gpu(G.x, G.y, G.s, { rot: G.rot, label: 'H100' });
    gripHands(grips);
    // front row
    crowd(850, t, { n: 6, s: 138, col: PAL.ink, hands: .75, horns: true, jump: .9, seed: 947 });
    camEnd();
    // Clawd's back in the foreground (screen space, slightly larger than life)
    clawdBack(430, 1215, 50, t);
  }

  // =============== line 2b: the amp's GAIN knob goes past 10 ===============
  const deg = a => a * Math.PI / 180;
  const KX = 1170, KY = 525, KR = 150;
  // steps on successive beats: pointer angle (deg, canvas: 0 = right, 90 = down) and the tape label it lands on
  const STEPS = [
    { a: 60, label: null }, { a: 90, label: '11', r: 1.42, rot: .1, size: 64 }, { a: 128, label: '12', r: 1.6, rot: -.15, size: 72 },
    { a: 168, label: '100', r: 1.85, rot: .12, size: 82 }, { a: 212, label: '10^26', r: 2.2, rot: -.08, size: 96 },
  ];
  function knob(x, y, r, ang, o = {}) {
    ctx.save(); ctx.translate(x, y);
    scrap(ellPts(0, 0, r * 1.08, r * 1.08, 36), '#111015', { torn: .8, seed: 2301 + r, shadow: [8, 12] });
    ctx.rotate(ang);
    scrap(ellPts(0, 0, r, r, 36), '#2A2830', { torn: .6, seed: 2302 + r, shadow: false, shade: true, shadeOp: .3 });
    ctx.fillStyle = '#3A3842'; for (let i = 0; i < 24; i++) { ctx.rotate(TAU / 24); ctx.fillRect(r * .86, -r * .03, r * .14, r * .06); }
    scrap(ellPts(0, 0, r * .62, r * .62, 28), '#C9CCD6', { torn: .4, seed: 2303 + r, shadow: false, tone: { color: PAL.ink, cell: 6, dot: .25, op: .35 } });
    scrap(rectPts(r * .1, -r * .07, r * .82, r * .14), o.hot ? PAL.red : PAL.white, { torn: .3, shadow: false });
    ctx.restore();
  }
  function dialLabels(x, y, r, n0, n1, a0, step, size) {
    for (let n = n0; n <= n1; n++) {
      const a = deg(a0 + (n - n0) * step);
      txt(String(n), x + Math.cos(a) * r, y + Math.sin(a) * r, size, PAL.white, { font: 'archivo' });
      marker([[x + Math.cos(a) * (r - size * .9), y + Math.sin(a) * (r - size * .9)], [x + Math.cos(a) * (r - size * 1.3), y + Math.sin(a) * (r - size * 1.3)]], PAL.white, 4, { rough: 0 });
    }
  }
  function ampShot(t, t0, t1) {
    const bj = bpOf(t) - Math.round(bpOf(t0)), j = clamp(Math.floor(bj + .02), 0, STEPS.length - 1), jf = frac(Math.max(0, bj + .02));
    const heat = j / (STEPS.length - 1);
    const [sx, sy] = shakeXY(t, 2 + heat * 10 * (.4 + pulse(t, 5)), 24);
    camBegin(W / 2 + sx, H / 2 + sy, 1 + (t - t0) * .03, -.02);
    // tolex + gold piping
    ctx.fillStyle = '#1E1D24'; ctx.fillRect(-200, -200, W + 400, H + 400);
    halftone(rectPts(-200, -200, W + 400, H + 400), '#3A3844', { cell: 9, dot: .3, op: 1, multiply: false, angle: 45 });
    // panel
    scrap(rectPts(40, 150, W - 80, 700), '#B9BCC6', { torn: 1.5, seed: 2310, shadow: [10, 14], tone: { color: PAL.ink, cell: 5, dot: .18, op: .25, angle: 0 } });
    marker([[60, 190], [W - 60, 190]], PAL.gold, 8, { rough: 0 });
    txt('Scale', 250, 105, 110, PAL.gold, { font: 'shrikhand', stroke: PAL.ink, sw: 8 });
    txt('MODEL 1: BASEMENT', 700, 100, 34, '#B9BCC6', { font: 'typewriter' });
    // small knobs pegged at 10, the input jack, the clip LED
    for (const [kx, lab] of [[330, 'VOLUME'], [700, 'TREBLE']]) {
      dialLabels(kx, KY + 20, 150, 0, 10, 120, 30, 26);
      knob(kx, KY + 20, 92, deg(60) + jit(heat * .03));
      txt(lab, kx, KY + 230, 40, PAL.ink, { font: 'archivo' });
    }
    const clip = pulse(t, 3 + (1 - heat) * 6) > .5 || heat > .9;
    scrap(ellPts(1600, 300, 30, 30, 16), clip ? PAL.red : '#5A1E1A', { torn: .4, seed: 2311, ink: PAL.ink, sw: 4, shadow: false });
    if (clip) { ctx.fillStyle = alpha(PAL.red, .35); tracePath(ellPts(1600, 300, 62, 62, 20)); ctx.fill(); }
    txt('CLIP', 1600, 356, 28, PAL.ink, { font: 'archivo' });
    // the GAIN dial, then masking-tape numbers past 10
    dialLabels(KX, KY, KR * 1.22, 0, 10, 120, 30, 36);
    txt('GAIN', KX - KR * 1.85, KY - KR * 1.2, 58, PAL.ink, { font: 'archivo', rot: -.08 });
    arrow(KX - KR * 1.85 + 20, KY - KR * 1.2 + 40, KX - KR * 1.1, KY - KR * .75, PAL.ink, 6, { bend: .25 });
    for (let i = 1; i <= j; i++) {
      const st = STEPS[i], a = deg(st.a), k = clamp((t - onBeat(0, Math.round(bpOf(t0)) + i) + .06) / .14);
      const lx = KX + Math.cos(a) * KR * st.r, ly = KY + Math.sin(a) * KR * st.r;
      ctx.save(); ctx.translate(lx, ly); ctx.rotate(st.rot); ctx.scale(lerp(1.6, 1, easeOut(k)), lerp(1.6, 1, easeOut(k)));
      const tw = textW(st.label, st.size, 'marker') + 50;
      tape(0, 0, tw, 0, { h: st.size * 1.2, seed: 2320 + i, color: 'rgb(236 222 180 / .95)' });
      txt(st.label, 0, 4, st.size, i === STEPS.length - 1 ? PAL.red : PAL.ink, { font: 'marker' });
      ctx.restore();
    }
    // pointer snaps to the next number on each beat
    const prev = STEPS[Math.max(0, j - 1)].a, cur = STEPS[j].a;
    const ang = j === 0 ? cur : lerp(prev, cur, backOut(clamp(jf / .3), 2.4));
    knob(KX, KY, KR, deg(ang) + jit(heat * .02), { hot: heat > .7 });
    // Robo's claw on the knob
    const ca = deg(ang - 90);
    ctx.save(); ctx.translate(KX + Math.cos(ca) * KR * .2, KY + Math.sin(ca) * KR * .2);
    const armA = Math.atan2(-300 - KY, 2100 - KX);
    ctx.rotate(armA);
    scrap(rectPts(KR * .9, -34, 1400, 68), '#9FB3C8', { torn: 1, seed: 2330, shadow: [8, 10], shade: true, shadeOp: .25 });
    scrap(rectPts(KR * .75, -48, 80, 96), mixCol('#9FB3C8', PAL.ink, .3), { torn: .6, seed: 2331, shadow: false });
    ctx.restore();
    ctx.save(); ctx.translate(KX, KY); ctx.rotate(deg(ang));
    for (const side of [-1, 1]) scrap([[-KR * .2, side * KR * .95], [KR * .55, side * KR * 1.12], [KR * .75, side * KR * .92], [KR * .1, side * KR * .78]], mixCol('#9FB3C8', PAL.ink, .15), { torn: .6, seed: 2335 + side, ink: PAL.ink, sw: 4, shadow: [5, 7] });
    ctx.restore();
    // smoke off the panel as it overheats
    for (let i = 0; i < 8 * heat; i++) {
      const age = frac(t * .9 + hash(i + 2340)), px = KX - 200 + hash(i + 2341) * 420, r = 30 + age * 80;
      scrap(ellPts(px + age * 60, KY - KR - age * 380, r, r * .8, 14), alpha('#8E8A96', .55 * (1 - age)), { torn: 4, seed: 2342 + i, shadow: false });
    }
    camEnd();
    flash(t, t0, .1, .4);
  }

  // =============== the burst: the curve springs out of the crate ===============
  const expo = (u, k) => (Math.exp(u * k) - 1) / (Math.exp(k) - 1); // k < 0 → fast then slow
  // Jack-in-the-box: a red coil springs out of the crate with the scaling curve on a sticker for a head.
  function springCurve(t, tb) {
    const a = t - tb; if (a <= 0) return;
    const ext = elasticOut(clamp(a / .6)), damp = Math.exp(-a * 2.2);
    const baseX = CRATE_X, baseY = CRATE_Y - 7 * CRATE_S + 8, top = VERT ? -120 : 330, Hs = (baseY - top) * ext;
    const sway = Math.sin(a * 13) * 70 * damp, N = 14, pts = [];
    for (let i = 0; i <= N; i++) { const u = i / N; pts.push([baseX + (i % 2 ? 1 : -1) * (i && i < N ? 50 : 0) + sway * u * u, baseY - Hs * u]); }
    marker(pts, PAL.ink, 28, { rough: 1 });
    marker(pts, PAL.red, 17, { rough: 1 });
    marker(pts, '#FF8FC4', 5, { rough: .8, alpha: .8 });
    const hx = baseX + sway, hy = baseY - Hs - 110;
    ctx.save(); ctx.translate(hx, hy); ctx.rotate(Math.sin(a * 13 + .7) * .4 * damp); const hs = lerp(.4, 1, ext) * (VERT ? 1.45 : 1); ctx.scale(hs, hs);
    scrap(burstPts(0, 0, 150, 16, .8, .1), PAL.yellow, { torn: 1, ink: PAL.ink, sw: 6, shadow: [8, 10], seed: 2150 });
    marker([[-70, -64], [-70, 58], [78, 58]], PAL.ink, 8, { rough: .8 });
    const cp = []; for (let i = 0; i <= 20; i++) { const u = i / 20; cp.push([-70 + u * 140, 58 - expo(u, 3.4) * 128]); }
    marker(cp, PAL.red, 15, { rough: 1, smooth: true });
    for (const u of [.4, .7, 1]) { const q = cp[Math.round(u * 20)]; scrap(ellPts(q[0], q[1], 10 + pulse(t, 5) * 4, 10 + pulse(t, 5) * 4, 10), PAL.white, { torn: .4, ink: PAL.ink, sw: 3, shadow: false }); }
    ctx.restore();
  }
  // agent critters launched out of the crate, arcing into the crowd, then surfing on it
  function agentsOut(t, tb) {
    for (let i = 0; i < 6; i++) {
      const tl = tb + .12 + i * .09, a = t - tl; if (a < 0) continue;
      const fly = .55, lx = [430, 600, 760, 1160, 1340, 1510][i] + hash(i + 2400) * 50, x0 = CRATE_X, y0 = CRATE_Y - 7 * CRATE_S - 20;
      let x, y, rot;
      if (a < fly) { const k = a / fly; x = lerp(x0, lx, k); y = lerp(y0, 975, k) - Math.sin(k * Math.PI) * (lx > 1000 ? 600 : 380) * (1 + hash(i + 2401) * .2); rot = k * TAU * (i % 2 ? 1 : -1); }
      else { const s = a - fly; x = lx + s * 120; y = 975 - Math.abs(Math.sin((s * 2.5 + i * .3) * Math.PI)) * 30; rot = Math.sin(s * 6 + i) * .25; }
      agent(x, y, 36, { eyes: 'spark', rot, walk: t * 3 + i * .3, bar: [PAL.clawd, PAL.pink, PAL.mint, PAL.yellow][i % 4] });
    }
  }

  section('C1', (p, lt, d, t) => {
    const P = plan(), L = P.L;

    // ---------- line 1: establishing wide → punch in on Clawd ----------
    if (t < P.tB) {
      hideCaption();
      const push = ease((t - P.tDown) / .35), creep = ease((t - P.tDown - .35) / (P.tB - P.tDown - .35));
      const zoom = lerp(1, 1.55, push) + .22 * creep, cy = lerp(540, 655, push);
      const [sx, sy] = slam(t, P.tDown, 14);
      camBegin(960 + sx, cy + sy - (1 - push) * 8 * lt, zoom, 0);
      stage(t, { crate: { rattle: 0 } });
      sweatFling(t, 960, GY - 250, 3, 11);
      camEnd();
      hideStamp(); bigHook(t, L[0]);
      flash(t, P.S.start, .18, .75);
      return;
    }
    // ---------- line 2a: the crowd ----------
    if (t < P.tC) { crowdShot(t, t - P.tB, P.tC - P.tB); return; }
    // ---------- line 2b: GAIN past 10 ----------
    if (t < P.tD) { ampShot(t, P.tC, P.tD); return; }
    // ---------- line 3: band wide under the hook ----------
    if (t < P.tE) {
      hideCaption();
      const k = (t - P.tD) / (P.tE - P.tD), last = L[2].start + (L[2].end - L[2].start) * .66;
      const punch = Math.exp(-Math.max(0, t - last) * 5) * (t > last ? 1 : 0);
      const [sx, sy] = slam(t, last, 12);
      camBegin(980 + sx - k * 40, 612 + sy, 1.2 + k * .16 + punch * .08, Math.sin(barOf(t) * Math.PI) * .012);
      const tw = beatAfter(P.tE, -2), twk = t - tw;
      stage(t, { crate: { hop: twk > 0 && twk < .25 ? Math.sin(twk / .25 * Math.PI) * 18 : 0, rattle: twk > 0 && twk < .3 ? .6 : 0 }, jump: .9 });
      sweatFling(t, 960, GY - 250, 4, 23);
      camEnd();
      // we're down in the pit: big heads and horns right in front of the lens
      crowd(985, t, { n: 6, s: 150, col: '#0B0912', hands: .8, horns: true, jump: 1, seed: 983, x0: 380, x1: 2000 });
      hideStamp(); bigHook(t, L[2]);
      return;
    }
    // ---------- line 4a: the crate rattles; Clawd side-eyes it ----------
    const tb = beatAfter(P.tE2, 2); // the lid blows on the second beat of "but we can't contain it"
    if (t < P.tE2) {
      if (t < L[3].start) hideCaption();
      const k = (t - P.tE) / (P.tE2 - P.tE), bp = pulse(t, 5);
      camBegin(560 - k * 30 + jit(k * 5), 740 + k * 20, 1.48 + ease(k) * .17, 0);
      stage(t, {
        clawd: () => { frontman(t, { eyes: 'wide', lookX: -1, lookY: .4, sweat: true, aL: .2 + bp * .3 }); },
        crate: { rattle: .25 + k * .8, hop: bp * (8 + k * 26) },
      });
      // muffled noises leaking out of the crate
      const bn = beatN(t), ba = t - onBeat(0, bn);
      if (ba < .3) txt(['bzzt', 'THUMP', 'bzZT!', 'THUMP!'][((bn % 4) + 4) % 4], CRATE_X + 150 + (bn % 2) * 60, CRATE_Y - 190 - ba * 120, 44 + k * 20, PAL.yellow, { font: 'marker', rot: (bn % 2 ? .2 : -.15), alpha: 1 - ba / .3, stroke: PAL.ink, sw: 8 });
      camEnd();
      return;
    }
    // ---------- line 4b: can't contain it ----------
    const tChain = beatAfter(P.tE2, 1), a = t - tb;
    const pull = ease(a / .5);
    const [sx, sy] = slam(t, tb, 30, .5);
    const [sx2, sy2] = slam(t, beatAfter(P.tE2, 4), 14, .35);
    const zoom = a < 0 ? 1.65 + (t - P.tE2) * .08 : lerp(1.72, 1, pull) - Math.max(0, a - .5) * .03;
    camBegin(lerp(530, 920, pull) + sx + sx2 + jit(2), lerp(760, 545, pull) + sy + sy2, zoom, a > 0 ? Math.sin(a * 9) * .02 * Math.exp(-a * 2) : 0);
    const chainK = 1 - clamp((t - tChain) / .25), lockA = t - tChain;
    stage(t, {
      wild: a > 0 ? 1 : .3, dust: a > 0 ? 3 : 1.5, jump: a > 0 ? 1.2 : .8, momFall: clamp((a - .35) / .9),
      clawd: () => {
        const o = frontman(t, a > 0 ? { eyes: 'shades', mouth: 'scream', aL: 1.2 + pulse(t, 6) * .15, aR: 1.25 + pulse(t, 6) * .15 } : { eyes: 'wide', lookX: -1, sweat: true, mouth: 'O' });
        if (a > 0) { horns(960, GY, 30, o, -1, clamp(a / .15)); horns(960, GY, 30, o, 1, clamp(a / .15)); }
      },
      crate: { rattle: a > 0 ? .15 : 1, open: a > 0 ? clamp(a / .1) : 0, chains: chainK, lock: lockA < 0 ? 1 : lockA < .8 ? 1 : 0,
        lockOff: lockA > 0 ? [-lockA * 500, -Math.sin(Math.min(lockA, .8) / .8 * Math.PI) * 260 + lockA * 200] : undefined, lockRot: lockA > 0 ? lockA * 9 : 0 },
      afterCrate: () => {
        springCurve(t, tb);
        if (a > 0) { // the lid, spinning away
          const k = a / .9; if (k < 1) card(CRATE_X - 520 * easeOut(k), CRATE_Y - 140 - Math.sin(k * Math.PI) * 420 - k * 200, 200, 22, '#A87B4C', -k * 7, { torn: .8, seed: 2111 });
        }
        if (lockA > 0 && lockA < .25) scrap(burstPts(CRATE_X, CRATE_Y - 70, 70 + lockA * 300, 10, .4), alpha(PAL.yellow, 1 - lockA / .25), { torn: 2, shadow: false });
      },
    });
    if (a > 0 && a < .45) txt('KA-CHUNK!', CRATE_X + 260, CRATE_Y - 380, 90, PAL.yellow, { font: 'marker', rot: -.12, alpha: 1 - easeIn(a / .45), stroke: PAL.ink, sw: 14 });
    if (lockA > 0 && lockA < .35) txt('SNAP!', CRATE_X + 170, CRATE_Y - 250, 60, PAL.white, { font: 'marker', rot: .12, alpha: 1 - lockA / .35, stroke: PAL.ink, sw: 10 });
    agentsOut(t, tb);
    camEnd();
    flash(t, tb, .12, .55);
  });

  // A decaying slam shake after t0.
  function slam(t, t0, amt, dur = .3) {
    const a = t - t0; if (a < 0 || a > dur) return [0, 0];
    const k = 1 - a / dur; return shakeXY(t, amt * k * k, 30);
  }

  // =====================================================================================================================
  // The vertical video's chorus 1: the show filmed from the pit, one tall frame at a time. The hook is the cover's title in three
  // lines over the banner (vhook); big moshing heads fill the foot of the frame (pitCrowd); the stage world is framed by inStage().
  //   line 1   lights slam on over the whole stage, then a push in on Clawd under the hook
  //   line 2a  the crowd as a deep stack of rows up the frame, a GPU crowd-surfing UP it from row to row, Clawd's back at the foot
  //   line 2b  the amp: the GAIN dial and its masking-tape numbers past 10, framed tall round the knob
  //   line 3   Clawd and the band under the hook, the crate twitching at the stage lip
  //   line 4a  Clawd side-eyes the rattling crate (both in one tall two-shot)
  //   line 4b  the lid blows and the curve springs up out of the crate, way up past the banner; the camera tilts up with it
  // =====================================================================================================================
  function vcrowdShot(t, lt, d) {
    const [sx, sy] = shakeXY(t, 3 + pulse(t, 6) * 5, 20);
    camBegin(W / 2 + sx, H / 2 + sy - lt * 30, 1.03 + lt * .02, 0);
    ctx.fillStyle = '#9A8E86'; ctx.fillRect(-300, -300, W + 600, H + 600);
    ctx.fillStyle = 'rgb(60 50 50 / .28)';
    for (let r = 0; r < 20; r++) for (let c = -1; c < 7; c++) ctx.fillRect(c * 200 + (r % 2) * 100, 30 + r * 92, 196, 4), ctx.fillRect(c * 200 + (r % 2) * 100, 30 + r * 92, 4, 92);
    halftone(rectPts(-300, -300, W + 600, H + 600), '#5B4E66', { cell: 22, dot: .2, op: .45 });
    ceiling(t);
    washer(-40, 400, t);
    heater(880, 330);
    ctx.save(); ctx.globalCompositeOperation = 'screen';
    const sw = Math.sin(bpOf(t) * Math.PI / 4) * 160;
    ctx.fillStyle = alpha(PAL.pink, .22); tracePath([[300, 2000], [500, 2000], [800 + sw, -100], [100 + sw, -100]]); ctx.fill();
    ctx.fillStyle = alpha(PAL.yellow, .18); tracePath([[600, 2000], [800, 2000], [1000 - sw, -100], [400 - sw, -100]]); ctx.fill();
    ctx.restore();
    // a GPU crowd-surfing up the room, passed back from row to row: held up by the front row, tossed back to the middle row on a
    // beat, then on to the back row (depth 0, 1, 2), each row's hands reaching for it as it comes
    const gk = clamp(lt / d), toss1 = seg(gk, .08, .28), toss2 = seg(gk, .52, .76), dep = ease(toss1) + ease(toss2);
    const STOPS = [[430, 1173, 22], [610, 892, 16], [410, 685, 12]];   // where each row holds it up: x, y, size
    const a = STOPS[Math.min(1, Math.floor(dep))], b = STOPS[Math.min(2, Math.floor(dep) + 1)], f = dep - Math.min(1, Math.floor(dep));
    const air = Math.sin(Math.PI * (toss1 < 1 ? toss1 : toss2));
    const G = {
      x: lerp(a[0], b[0], f) + Math.sin(gk * 7) * 22 - seg(gk, .76, 1) * 50,
      y: lerp(a[1], b[1], f) - air * (toss1 < 1 ? 150 : 90) - Math.max(0, Math.sin(bpOf(t) * Math.PI)) * 10 * (1 - air),
      s: lerp(a[2], b[2], f), rot: Math.sin(t * 5) * .12 + air * .35 * (toss1 < 1 ? -1 : 1),
    };
    const carry = row => 1 - ease((Math.abs(dep - row) - .15) / .55);
    // the rows, receding up the frame
    const bob = i => -pulse(t + i * .2, 5) * 22;
    const grips = carryRow(760, t, { n: 9, s: 62, col: '#4A4060', hands: .6, horns: true, jump: .9, seed: 921, x0: -30, x1: W + 30 }, G, carry(2));
    placard(330, 560 + bob(0), 330, 160, -.08 + wob(t, .7) * .03, '#D9B98C', () => {
      txt('MORE', 0, -34, 60, PAL.ink, { font: 'marker' }); txt('LAYERS!', 0, 30, 60, PAL.red, { font: 'marker' });
    });
    grips.push(...carryRow(1000, t, { n: 7, s: 92, col: '#3A3050', hands: .6, horns: true, jump: .9, seed: 931, x0: -40, x1: W + 40 }, G, carry(1)));
    placard(700, 720 + bob(1), 420, 190, .06 + wob(t, .6, .3) * .03, PAL.white, (w) => {
      txt('STILL TRAINING…', 0, -48, 50, PAL.ink, { font: 'marker', maxW: w - 40 });
      const bw = w - 70;
      scrap(rectPts(-bw / 2, 0, bw, 44), PAL.white, { torn: 1, shadow: false, ink: PAL.ink, sw: 5, seed: 2245 });
      scrap(rectPts(-bw / 2 + 6, 6, (bw - 12) * .99, 32), PAL.green, { torn: .8, shadow: false, seed: 2246 });
      txt('99%', bw / 2 - 40, 22, 30, PAL.white, { font: 'anton' });
    });
    gpu(G.x, G.y, G.s, { rot: G.rot, label: 'H100' });
    gripHands(grips);
    gripHands(carryRow(1330, t, { n: 5, s: 140, col: '#1E1828', hands: .75, horns: true, jump: .9, seed: 947, x0: -60, x1: W + 60 }, G, carry(0)));
    camEnd();
    // Clawd's back at the foot of the frame
    clawdBack(800, 2130, 56, t);   // (low in the corner, below the caption)
  }

  vshot('C1', (p, lt, d, t) => {
    const P = plan(), L = P.L;
    // (whatever the stage world doesn't reach, past its ceiling and floor, is the dark of the basement)
    ctx.fillStyle = '#120E18'; ctx.fillRect(0, 0, W, H);
    // ---------- line 1: lights slam on over the stage → push in on Clawd ----------
    if (t < P.tB) {
      hideCaption(); hideStamp();
      const push = ease((t - P.tDown) / .35), creep = ease((t - P.tDown - .35) / (P.tB - P.tDown - .35));
      const zoom = lerp(.88, 1.4, push) + .14 * creep, cy = lerp(700, 560, push);
      const [sx, sy] = slam(t, P.tDown, 14);
      inStage(t, () => { stage(t, { crate: { rattle: 0 }, bannerTitle: false }); sweatFling(t, 960, GY - 250, 3, 11); }, 960 + sx, cy + sy - (1 - push) * 8 * lt, zoom);
      pitCrowd(t, 1760);
      vhook(t, L[0], { y: 330, cut: P.tB });
      flash(t, P.S.start, .18, .75);
      return;
    }
    // ---------- line 2a: the crowd ----------
    if (t < P.tC) { vcrowdShot(t, t - P.tB, P.tC - P.tB); return; }
    // ---------- line 2b: GAIN past 10, framed tall round the knob (close enough that the amp's tolex fills the frame) ----------
    if (t < P.tD) { inStage(t, () => ampShot(t, P.tC, P.tD), 1085, 560, 1.45 + (t - P.tC) * .02); flash(t, P.tC, .1, .3); return; }
    // ---------- line 3: Clawd and the band under the hook ----------
    if (t < P.tE) {
      hideCaption(); hideStamp();
      const k = (t - P.tD) / (P.tE - P.tD), last = L[2].start + (L[2].end - L[2].start) * .66;
      const punch = Math.exp(-Math.max(0, t - last) * 5) * (t > last ? 1 : 0);
      const [sx, sy] = slam(t, last, 12);
      const tw = beatAfter(P.tE, -2), twk = t - tw;
      inStage(t, () => {
        stage(t, { crate: { hop: twk > 0 && twk < .25 ? Math.sin(twk / .25 * Math.PI) * 18 : 0, rattle: twk > 0 && twk < .3 ? .6 : 0 }, jump: .9, bannerTitle: false });
        sweatFling(t, 960, GY - 250, 4, 23);
      }, 910 + sx + k * 30, 630 + sy, 1.22 + k * .14 + punch * .08);
      pitCrowd(t, 1800, { s: 145, n: 7, seed: 991 });
      vhook(t, L[2], { y: 330, cut: P.tE });
      return;
    }
    // ---------- line 4a: the crate rattles; Clawd side-eyes it ----------
    const tb = beatAfter(P.tE2, 2);
    if (t < P.tE2) {
      if (t < L[3].start) hideCaption();
      const k = (t - P.tE) / (P.tE2 - P.tE), bp = pulse(t, 5);
      inStage(t, () => {
        stage(t, {
          clawd: () => { frontman(t, { eyes: 'wide', lookX: -1, lookY: .4, sweat: true, aL: .2 + bp * .3 }); },
          crate: { rattle: .25 + k * .8, hop: bp * (8 + k * 26) },
        });
        const bn = beatN(t), ba = t - onBeat(0, bn);
        if (ba < .3) txt(['bzzt', 'THUMP', 'bzZT!', 'THUMP!'][((bn % 4) + 4) % 4], CRATE_X - 30 + (bn % 2) * 70, CRATE_Y - 200 - ba * 120, 44 + k * 20, PAL.yellow, { font: 'marker', rot: (bn % 2 ? .2 : -.15), alpha: 1 - ba / .3, stroke: PAL.ink, sw: 8 });
      }, 850 + jit(k * 5), 830 + k * 20, 1.5 + ease(k) * .16);
      pitCrowd(t, 1780, { s: 170, seed: 997, jump: .9 });
      return;
    }
    // ---------- line 4b: can't contain it: the curve springs up out of the crate, the camera tilts up with it ----------
    const tChain = beatAfter(P.tE2, 1), a = t - tb;
    const pull = ease(a / .55), up = ease((a - .05) / .5) * (1 - ease((a - .9) / .6));
    const [sx, sy] = slam(t, tb, 30, .5);
    const [sx2, sy2] = slam(t, beatAfter(P.tE2, 4), 14, .35);
    const zoom = a < 0 ? 1.66 + (t - P.tE2) * .08 : lerp(1.66, .92, pull) - Math.max(0, a - .5) * .02;
    const chainK = 1 - clamp((t - tChain) / .25), lockA = t - tChain;
    inStage(t, () => {
      stage(t, {
        wild: a > 0 ? 1 : .3, dust: a > 0 ? 3 : 1.5, jump: a > 0 ? 1.2 : .8, momFall: clamp((a - .35) / .9),
        clawd: () => {
          const o = frontman(t, a > 0 ? { eyes: 'shades', mouth: 'scream', aL: 1.2 + pulse(t, 6) * .15, aR: 1.25 + pulse(t, 6) * .15 } : { eyes: 'wide', lookX: -1, sweat: true, mouth: 'O' });
          if (a > 0) { horns(960, GY, 30, o, -1, clamp(a / .15)); horns(960, GY, 30, o, 1, clamp(a / .15)); }
        },
        crate: { rattle: a > 0 ? .15 : 1, open: a > 0 ? clamp(a / .1) : 0, chains: chainK, lock: lockA < 0 ? 1 : lockA < .8 ? 1 : 0,
          lockOff: lockA > 0 ? [-lockA * 500, -Math.sin(Math.min(lockA, .8) / .8 * Math.PI) * 260 + lockA * 200] : undefined, lockRot: lockA > 0 ? lockA * 9 : 0 },
        afterCrate: () => {
          springCurve(t, tb);
          if (a > 0) { const k = a / .9; if (k < 1) card(CRATE_X - 520 * easeOut(k), CRATE_Y - 140 - Math.sin(k * Math.PI) * 420 - k * 200, 200, 22, '#A87B4C', -k * 7, { torn: .8, seed: 2111 }); }
          if (lockA > 0 && lockA < .25) scrap(burstPts(CRATE_X, CRATE_Y - 70, 70 + lockA * 300, 10, .4), alpha(PAL.yellow, 1 - lockA / .25), { torn: 2, shadow: false });
        },
      });
      if (a > 0 && a < .45) txt('KA-CHUNK!', CRATE_X + 80, CRATE_Y - 330, 96, PAL.yellow, { font: 'marker', rot: -.12, alpha: 1 - easeIn(a / .45), stroke: PAL.ink, sw: 14 });
      if (lockA > 0 && lockA < .35) txt('SNAP!', CRATE_X - 40, CRATE_Y - 230, 64, PAL.white, { font: 'marker', rot: .12, alpha: 1 - lockA / .35, stroke: PAL.ink, sw: 10 });
      agentsOut(t, tb);
    }, lerp(830, 860, pull) + sx + sx2 + jit(2), lerp(850, 600, pull) - up * 330 + sy + sy2, zoom);
    pitCrowd(t, 1780, { s: 170, seed: 997, jump: a > 0 ? 1.3 : .9 });
    flash(t, tb, .12, .55);
  });
})();

;
// ---- src/ch/c04_v2.js ----
// c04_v2 — Verse 2: 2025. Palette leans blue/red/teal; every cut flips the dominant colour.
(() => {
  // ---------- private helpers ----------
  const BL = () => beatLen();
  function fillBG(c) { ctx.fillStyle = c; ctx.fillRect(-200, -200, W + 400, H + 400); }
  function toneBG(c, cell = 22, dot = .22, op = .45, angle = 20) { halftone(rectPts(-200, -200, W + 400, H + 400), c, { cell, dot, op, angle }); }
  function raysBG(cx, cy, n, col, rot = 0, R = 2600) {
    ctx.fillStyle = col; ctx.beginPath();
    for (let i = 0; i < n; i++) {
      const a0 = rot + i / n * TAU, a1 = a0 + TAU / n / 2;
      ctx.moveTo(cx, cy); ctx.lineTo(cx + Math.cos(a0) * R, cy + Math.sin(a0) * R); ctx.lineTo(cx + Math.cos(a1) * R, cy + Math.sin(a1) * R); ctx.closePath();
    }
    ctx.fill();
  }
  // Paper-slap entrance: the whole frame settles from a slight zoom in the first ~0.13 s. Pair with camEnd().
  function slapIn(lt, amt = .06, rot = .012, cx = W / 2, cy = H / 2) { const k = easeOut(clamp(lt / .13)); camBegin(cx, cy, 1 + amt * (1 - k), rot * (1 - k)); }
  const popK = (lt, t0, dur = .18) => clamp((lt - t0) / dur);
  // person() hand / head positions (no rot/flip/sq).
  const handAt = (x, y, s, side, ang, dy = 0) => [x + side * (1.35 * s + 3.1 * s * Math.cos(ang)), y + dy * s - 7.1 * s - 3.1 * s * Math.sin(ang)];
  const headAt = (x, y, s, dy = 0) => [x, y + dy * s - 8.9 * s];

  function fedora(x, y, s, o = {}) { // (x, y) = person head centre, s = person scale
    ctx.save(); ctx.translate(x, y); ctx.rotate(o.rot ?? -.08);
    const col = o.col ?? '#2E2B33';
    scrap(ellPts(0, -.72 * s, 2.05 * s, .42 * s, 28), col, { torn: .4, seed: 1401, shadow: [.1 * s, .14 * s] });
    scrap([[-1.05 * s, -.8 * s], [-.85 * s, -2.05 * s], [-.3 * s, -2.15 * s], [0, -1.9 * s], [.3 * s, -2.15 * s], [.85 * s, -2.05 * s], [1.05 * s, -.8 * s]], col, { torn: .4, seed: 1402, shadow: false, shade: true, shadeOp: .3 });
    scrap(rectPts(-1.03 * s, -1.22 * s, 2.06 * s, .4 * s), o.band ?? PAL.red, { torn: .3, seed: 1403, shadow: false });
    ctx.restore();
  }
  function headphones(x, y, s, col = PAL.pink) { // (x, y) head centre
    ctx.save(); ctx.translate(x, y);
    ctx.strokeStyle = PAL.ink; ctx.lineWidth = .32 * s; ctx.lineCap = 'round';
    ctx.beginPath(); ctx.arc(0, -.1 * s, 1.45 * s, Math.PI * 1.05, Math.PI * 1.95); ctx.stroke();
    ctx.strokeStyle = col; ctx.lineWidth = .16 * s; ctx.stroke();
    for (const sd of [-1, 1]) scrap(rrPts(sd * 1.35 * s - .38 * s, -.55 * s, .76 * s, 1.15 * s, .3 * s), col, { torn: .4, seed: 1405 + sd, ink: PAL.ink, sw: .1 * s, shadow: [.08 * s, .1 * s] });
    ctx.restore();
  }
  function cash(x, y, s, rot = 0, col = '#8FCB8F') {
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot);
    scrap(rectPts(-1.2 * s, -.55 * s, 2.4 * s, 1.1 * s), col, { torn: .3, seed: 1410, shadow: [.1 * s, .12 * s], ink: '#2F6B3A', sw: .06 * s });
    txt('$', 0, .03 * s, .8 * s, '#2F6B3A', { font: 'abril' });
    ctx.restore();
  }
  function moneyBag(x, y, s, o = {}) { // (x, y) centre of the sack
    ctx.save(); ctx.translate(x, y); if (o.rot) ctx.rotate(o.rot);
    scrap([[-.5 * s, -1 * s], [-.9 * s, -1.9 * s], [-.2 * s, -1.6 * s], [.1 * s, -2 * s], [.4 * s, -1.6 * s], [.95 * s, -1.9 * s], [.5 * s, -1 * s]], '#C8A866', { torn: .3, seed: 1420, ink: PAL.ink, sw: .07 * s, shadow: false });
    scrap([...ellPts(0, .15 * s, 1.35 * s, 1.25 * s, 24)], '#C8A866', { torn: .4, seed: 1421, ink: PAL.ink, sw: .08 * s, shade: '#8A6A35', shadeOp: .4 });
    scrap(rectPts(-.6 * s, -1.12 * s, 1.2 * s, .28 * s), PAL.red, { torn: .2, seed: 1422, shadow: false });
    txt(o.label ?? '$', 0, .3 * s, (o.label ? .55 : 1.3) * s, '#2F6B3A', { font: o.label ? 'anton' : 'abril', maxW: 2.2 * s });
    ctx.restore();
  }
  // A starburst "POP" of a firecracker, age 0..1.
  function popBurst(x, y, r, age, col = PAL.yellow, word) {
    if (age <= 0 || age >= 1) return;
    const k = easeOut(clamp(age / .35)), a = 1 - clamp((age - .5) / .5);
    ctx.save(); ctx.globalAlpha *= a;
    scrap(burstPts(x, y, r * k, 12, .45, age * 2), col, { torn: 1, shadow: false, ink: PAL.ink, sw: 3 });
    scrap(burstPts(x, y, r * .5 * k, 8, .5, -age * 3), PAL.white, { torn: .5, shadow: false });
    if (word) txt(word, x, y, r * .42 * k, PAL.red, { font: 'bungee', rot: -.2 });
    ctx.restore();
  }

  // ======================================================================
  // V2.1 DeepSeek New Year sticker shock — a blue whale smashes through a "$5.6M" price tag; NVDA nose-dives.
  function whale(x, y, s, o = {}) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(o.rot ?? 0);
    const col = o.col ?? '#4D6BFE', dk = mixCol(col, PAL.ink, .35);
    ctx.save(); ctx.translate(-3 * s, 0); ctx.rotate(o.tail ?? 0);
    scrap([[.6 * s, -1.3 * s], [-2.3 * s, -.35 * s], [-2.3 * s, .4 * s], [.6 * s, 1.3 * s]], col, { torn: .5, seed: 1431, shadow: false });
    scrap([[-2 * s, 0], [-3.5 * s, -1.9 * s], [-3 * s, 0], [-3.6 * s, 1.7 * s]], col, { torn: .5, seed: 1432, ink: PAL.ink, sw: .1 * s });
    ctx.restore();
    const P = scrap(ellPts(.6 * s, 0, 4.2 * s, 2.3 * s, 40), col, { torn: .7, seed: 1433, ink: PAL.ink, sw: .12 * s, shadow: [.25 * s, .3 * s] });
    ctx.save(); tracePath(P); ctx.clip();
    scrap(ellPts(1.6 * s, 1.9 * s, 3.8 * s, 1.5 * s, 30), '#DCE4FF', { torn: .4, seed: 1434, shadow: false });
    ctx.strokeStyle = alpha(PAL.ink, .3); ctx.lineWidth = .08 * s;
    for (let i = 0; i < 3; i++) { ctx.beginPath(); ctx.moveTo(-.5 * s, (1.05 + i * .35) * s); ctx.quadraticCurveTo(2 * s, (.5 + i * .35) * s, 4.8 * s, (.3 + i * .3) * s); ctx.stroke(); }
    halftone(P, dk, { cell: 9, dot: .3, op: .35 });
    ctx.restore();
    scrap([[.4 * s, 1.1 * s], [-.9 * s, 2.7 * s], [.3 * s, 2.4 * s], [1.5 * s, 1.2 * s]], dk, { torn: .4, seed: 1435, shadow: false });
    // eye + grin
    const ex = 3.2 * s, ey = -.55 * s;
    ctx.fillStyle = PAL.white; tracePath(ellPts(ex, ey, .62 * s, .72 * s, 16)); ctx.fill();
    ctx.strokeStyle = PAL.ink; ctx.lineWidth = .1 * s; ctx.stroke();
    ctx.fillStyle = PAL.ink; tracePath(ellPts(ex + .15 * s, ey + .05 * s, .3 * s, .36 * s, 12)); ctx.fill();
    ctx.fillStyle = PAL.white; tracePath(ellPts(ex + .25 * s, ey - .1 * s, .1 * s, .1 * s, 8)); ctx.fill();
    ctx.strokeStyle = PAL.ink; ctx.lineWidth = .16 * s; ctx.lineCap = 'round';
    ctx.beginPath(); ctx.moveTo(2.3 * s, .45 * s); ctx.quadraticCurveTo(3.6 * s, 1.05 * s, 4.75 * s, .2 * s); ctx.stroke();
    if (o.blush) { ctx.fillStyle = alpha(PAL.pink, .6); tracePath(ellPts(3.3 * s, .45 * s, .45 * s, .22 * s, 10)); ctx.fill(); }
    // spout
    const sp = o.spout ?? 0;
    if (sp > 0) for (let i = 0; i < 7; i++) {
      const a = -Math.PI / 2 + (i - 3) * .28, r = sp * (1.4 + hash(i + 3) * 1.4) * s;
      scrap(ellPts(1.6 * s + Math.cos(a) * r, -2.3 * s + Math.sin(a) * r, .32 * s, .42 * s, 10), PAL.sky, { torn: .2, seed: 1436 + i, shadow: false, ink: PAL.ink, sw: .05 * s });
    }
    ctx.restore();
  }
  function tagShape(w, h) { return [[-w / 2 + h * .42, -h / 2], [w / 2, -h / 2], [w / 2, h / 2], [-w / 2 + h * .42, h / 2], [-w / 2, 0]]; }
  function priceTagBody(w, h) {
    scrap(tagShape(w, h), PAL.yellow, { torn: 2, seed: 1440, ink: PAL.ink, sw: 5, shadow: [10, 12] });
    ctx.fillStyle = PAL.red; tracePath(ellPts(-w / 2 + h * .3, 0, 22, 22, 14)); ctx.fill();
    ctx.fillStyle = PAL.ink; tracePath(ellPts(-w / 2 + h * .3, 0, 12, 12, 12)); ctx.fill();
    txt('TRAINING RUN', 60, -h * .3, 44, PAL.ink, { font: 'mono' });
    txt('$5.6M', 60, h * .1, 200, PAL.red, { font: 'anton', shadow: [7, 8] });
    txt('*final run only', 60, h * .38, 30, PAL.ink, { font: 'typewriter' });
  }
  function lantern(x, y, s, sw) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(sw);
    marker([[0, -400], [0, 0]], PAL.ink, 4, { rough: 0 });
    scrap(rectPts(-.55 * s, -.2 * s, 1.1 * s, .35 * s), PAL.gold, { torn: .3, seed: 1450, shadow: false, ink: PAL.ink, sw: 3 });
    scrap(ellPts(0, 1.1 * s, 1.35 * s, 1.05 * s, 28), PAL.gold, { torn: .6, seed: 1451, ink: PAL.ink, sw: 4, shade: '#B8801A', shadeOp: .5 });
    ctx.strokeStyle = alpha(PAL.red, .9); ctx.lineWidth = 5;
    for (const k of [-.6, 0, .6]) { ctx.beginPath(); ctx.ellipse(0, 1.1 * s, Math.abs(k) * 1.35 * s + 2, 1.02 * s, 0, 0, TAU); ctx.stroke(); }
    scrap(rectPts(-.55 * s, 2.05 * s, 1.1 * s, .3 * s), PAL.gold, { torn: .3, seed: 1452, shadow: false, ink: PAL.ink, sw: 3 });
    for (let i = 0; i < 5; i++) marker([[(-.3 + i * .15) * s, 2.35 * s], [(-.35 + i * .17) * s, 3.2 * s]], PAL.red, 5, { rough: 0 });
    ctx.restore();
  }
  line('V2', 1, (p, lt, d, t) => {
    const hit = .26; // whale hits the tag
    const crash = .95; // NVDA crash starts
    const shk = lt > hit && lt < hit + .25 ? shakeXY(t, 14 * (1 - (lt - hit) / .25)) : [0, 0];
    const shk2 = lt > crash + .2 && lt < crash + .45 ? shakeXY(t + 1, 10) : [0, 0];
    slapIn(lt, .06, .012, W / 2 - shk[0] - shk2[0], H / 2 - shk[1] - shk2[1]);
    fillBG('#D42F24');
    raysBG(900, 260, 22, '#E8412F', lt * .15);
    toneBG('#8E1B14', 24, .2, .35);
    lantern(110, 30, 56, Math.sin(t * 5) * .08);
    lantern(1300, -150, 40, Math.sin(t * 5 + 1) * .1);
    // sea at the bottom
    const sea = (yy, col, ph, amp) => { const pts = [[-50, H + 50]]; for (let i = 0; i <= 24; i++) pts.push([i * 85 - 50, yy + Math.sin(i * .9 + t * 6 + ph) * amp]); pts.push([W + 50, H + 50]); scrap(pts, col, { torn: 2, shadow: [0, -6], shadowCol: 'rgb(0 0 0 / .18)', seed: 1460 + ph }); };
    sea(910, '#2C4FB8', 0, 14);
    // NVDA chart (right): climbs, then the crash is drawn in red
    const cx = 1330, cy = 350, cw = 430, ch = 340;
    chart(cx, cy, cw, ch, { k: 0, col: 'rgb(0 0 0 / 0)', label: 'NVDA', labelSize: 54, grid: true });
    const f = u => u < .72 ? .45 + .5 * u + Math.sin(u * 30) * .03 : .81 - (u - .72) / .28 * .78;
    const upPts = []; for (let i = 0; i <= 30; i++) { const u = i / 30 * .72; upPts.push([cx + u * cw, cy + ch - f(u) * ch]); }
    marker(upPts, '#1A9E55', 11, { rough: 1.2, smooth: true });
    const ck = clamp((lt - crash) / .28);
    if (ck > 0) {
      const dn = []; for (let i = 0; i <= 12; i++) { const u = .72 + i / 12 * .28; dn.push([cx + u * cw, cy + ch - f(u) * ch]); }
      const P = partial(dn, easeIn(ck)); marker(P, PAL.red, 14, { rough: 1.5 });
      const [tx, ty] = P.at(-1); scrap(ellPts(tx, ty, 13, 13, 10), PAL.red, { torn: .5, shadow: false, ink: PAL.ink, sw: 3 });
    }
    // firecracker pops (eighth notes after the hit)
    for (let i = 0; i < 9; i++) {
      const t0 = hit + i * BL() / 2, age = (lt - t0) / .32;
      const px = [150, 470, 1180, 250, 1180, 560, 170, 1230, 380][i], py = [560, 170, 150, 800, 760, 120, 330, 860, 700][i];
      popBurst(px, py, 70 + hash(i) * 30, age, i % 2 ? PAL.yellow : PAL.gold, i % 3 === 0 ? 'POP!' : i % 3 === 1 ? 'BANG' : null);
    }
    // whale path: a quadratic arc out of the sea, through the tag, to a hover above it
    const P0 = [150, 1300], P1 = [520, 300], P2 = [880, 215];
    const u = 1 - (1 - clamp(lt / .6)) ** 2, iu = 1 - u;
    let wx = iu * iu * P0[0] + 2 * iu * u * P1[0] + u * u * P2[0], wy = iu * iu * P0[1] + 2 * iu * u * P1[1] + u * u * P2[1];
    const dx = 2 * iu * (P1[0] - P0[0]) + 2 * u * (P2[0] - P1[0]), dy = 2 * iu * (P1[1] - P0[1]) + 2 * u * (P2[1] - P1[1]);
    let wrot = Math.atan2(dy, dx) * .85;
    if (lt > .6) { wy += Math.sin((lt - .6) * 6) * 12; wrot += Math.sin((lt - .6) * 5) * .05; }
    const tagX = 640, tagY = 420, tw = 740, th = 330;
    // price tag: intact before the hit, then two halves drifting apart
    const tk = clamp((lt - hit) / 1.1);
    const drawHalf = (side) => {
      const off = easeOut(tk) * (side < 0 ? 220 : 250), fall = tk * tk * (side < 0 ? 130 : 160), rot = side * (easeOut(tk) * .32);
      ctx.save(); ctx.translate(tagX + side * off, tagY + fall); ctx.rotate(-.06 + rot);
      ctx.beginPath();
      const zz = []; for (let i = 0; i <= 8; i++) zz.push([60 + (i % 2 ? 26 : -26), -th / 2 - 20 + i * (th + 40) / 8]);
      ctx.moveTo(side * 800, -400); zz.forEach(([a, b]) => ctx.lineTo(a, b)); ctx.lineTo(side * 800, 400);
      ctx.closePath(); ctx.clip();
      priceTagBody(tw, th);
      ctx.restore();
    };
    const lOff = lt > hit ? easeOut(tk) * 220 : 0, lFall = lt > hit ? tk * tk * 130 : 0;
    marker([[tagX - tw / 2 + th * .3 - lOff, tagY + lFall], [tagX - 470, -40]], PAL.ink, 4, { rough: 1 });
    if (lt < hit) {
      // the whale rises behind the tag, which bulges and trembles, then bursts
      for (let i = 0; i < 4; i++) marker([[wx - 330 + i * 60, wy + 300 + i * 30], [wx - 180 + i * 60, wy + 130 + i * 30]], PAL.white, 8, { rough: 1, alpha: .8 });
      whale(wx, wy, 50, { rot: wrot, tail: Math.sin(t * 14) * .25 });
      const bulge = 1 + clamp((lt - .1) / (hit - .1)) * .06;
      ctx.save(); ctx.translate(tagX + jit(2 + 6 * lt / hit), tagY + jit(2 + 6 * lt / hit)); ctx.rotate(-.06 + Math.sin(lt * 60) * .02 * (lt / hit)); ctx.scale(bulge, bulge); priceTagBody(tw, th); ctx.restore();
      if (lt > .1) for (let i = 0; i < 5; i++) { const a = -2.6 + i * .5; marker([[tagX + 60 + Math.cos(a) * 60, tagY + 60 + Math.sin(a) * 40], [tagX + 60 + Math.cos(a) * 110, tagY + 60 + Math.sin(a) * 75]], PAL.ink, 5, { rough: 1.5 }); }
    } else {
      drawHalf(-1); drawHalf(1);
      for (let i = 0; i < 14; i++) {
        const a = hash(i + 40) * TAU, v = 300 + hash(i + 41) * 500, age = lt - hit;
        const sx = tagX + 60 + Math.cos(a) * v * age, sy = tagY + Math.sin(a) * v * age + 500 * age * age;
        card(sx, sy, 34, 22, i % 2 ? PAL.yellow : PAL.white, a + age * 9, { torn: 1, shadow: false, seed: 1470 + i });
      }
      whale(wx, wy, 50, { rot: wrot, tail: Math.sin(t * 14) * .25, spout: clamp((lt - hit - .15) / .3) * (1 + pulse(t) * .25), blush: true });
      if (lt < hit + .25) popBurst(tagX + 60, tagY + 40, 170, (lt - hit) / .25, PAL.white, 'RIP!');
    }
    sticker('NVDA\n−17%', 1580, 800, 135, PAL.yellow, { pop: popK(lt, crash + .3, .2), rot: .15, size: 64 });
    camEnd();
  });

  // ======================================================================
  // V2.2 Half a trillion Stargate talk — a giant ring portal, "$500,000,000,000"; TRUMP at the podium, three cheering backers beside him.
  const LOUD_FONTS = ['anton', 'archivo', 'bungee', 'bebas', 'rammetto', 'abril', 'mono'];
  line('V2', 2, (p, lt, d, t) => {
    slapIn(lt, .05);
    fillBG('#141233');
    toneBG('#3B3480', 26, .18, .6);
    for (let i = 0; i < 40; i++) { const x = hash(i + 50) * W, y = hash(i + 51) * 700, r = 2 + hash(i + 52) * 4 * (.6 + .4 * Math.sin(t * 6 + i)); ctx.fillStyle = PAL.cream; tracePath(starPts(x, y, r * 2, .35, 4, 0)); ctx.fill(); }
    const cx = 960, cy = 385, R = 330;
    // event horizon (kawoosh at the start)
    const kaw = lt < .4 ? Math.sin(lt / .4 * Math.PI) : 0;
    ctx.save();
    ctx.fillStyle = '#1FA6A0'; tracePath(ellPts(cx, cy, R * .86, R * .86, 48)); ctx.fill();
    ctx.beginPath(); ctx.arc(cx, cy, R * .86, 0, TAU); ctx.clip();
    for (let i = 0; i < 7; i++) {
      const rr = frac(i / 7 + lt * .7) * R * .9;
      ctx.strokeStyle = i % 2 ? alpha(PAL.sky, .8) : alpha(PAL.mint, .7); ctx.lineWidth = 16 + i * 2;
      ctx.beginPath(); ctx.ellipse(cx + Math.sin(t * 3 + i) * 10, cy + Math.cos(t * 2.4 + i) * 8, rr, rr * .96, 0, 0, TAU); ctx.stroke();
    }
    halftone(ellPts(cx, cy, R, R, 40), '#0E5E6E', { cell: 12, dot: .3, op: .45 });
    ctx.fillStyle = alpha(PAL.white, .5); tracePath(ellPts(cx, cy, R * .3 + kaw * 60, R * .3 + kaw * 60, 30)); ctx.fill();
    ctx.restore();
    if (kaw > 0) scrap(ellPts(cx, cy + 30, R * (.9 + kaw * .5), R * (.8 + kaw * .45), 36), alpha(PAL.sky, .7), { torn: 8, shadow: false, seed: 1480 });
    // bills spiralling into the gate
    for (let i = 0; i < 16; i++) {
      const ph = frac(lt * .75 + hash(i + 60)), a = hash(i + 61) * TAU + ph * 4, r = lerp(1000, 20, ph ** .8);
      cash(cx + Math.cos(a) * r * 1.2, cy + Math.sin(a) * r * .75, 46 * (1 - ph * .8), a + ph * 6);
    }
    // the ring
    ctx.save();
    ctx.strokeStyle = 'rgb(0 0 0 / .35)'; ctx.lineWidth = R * .2; ctx.beginPath(); ctx.arc(cx + 10, cy + 14, R * .93, 0, TAU); ctx.stroke();
    ctx.strokeStyle = '#8D93A3'; ctx.beginPath(); ctx.arc(cx, cy, R * .93, 0, TAU); ctx.stroke();
    ctx.strokeStyle = '#6B7080'; ctx.lineWidth = R * .07; ctx.beginPath(); ctx.arc(cx, cy, R * .93, 0, TAU); ctx.stroke();
    ctx.strokeStyle = PAL.ink; ctx.lineWidth = 5;
    for (const rr of [R * .83, R * 1.03]) { ctx.beginPath(); ctx.arc(cx, cy, rr, 0, TAU); ctx.stroke(); }
    const spin = lt * 1.6;
    for (let i = 0; i < 39; i++) { const a = spin + i / 39 * TAU; txt('◇△○▽□◁'[i % 6], cx + Math.cos(a) * R * .93, cy + Math.sin(a) * R * .93, 22, '#C9CED9', { font: 'archivo', rot: a + Math.PI / 2 }); }
    ctx.restore();
    // chevrons lock in on eighth notes
    for (let i = 0; i < 9; i++) {
      const a = -Math.PI / 2 + i / 9 * TAU, lit = lt > i * BL() / 2 * .8;
      ctx.save(); ctx.translate(cx + Math.cos(a) * R, cy + Math.sin(a) * R); ctx.rotate(a + Math.PI / 2);
      scrap([[-34, -24], [34, -24], [16, 26], [-16, 26]], lit ? PAL.orange : '#5A5E6A', { torn: .8, seed: 1490 + i, ink: PAL.ink, sw: 4 });
      if (lit) { ctx.fillStyle = alpha(PAL.yellow, .5 + .5 * pulse2(t + i * .05)); tracePath([[-18, -14], [18, -14], [8, 14], [-8, 14]]); ctx.fill(); }
      ctx.restore();
    }
    ransom('$500,000,000,000', cx, cy - 30, 96, { pop: clamp(lt / .32), maxW: 1320, seed: 5005, jolt: 3, fonts: LOUD_FONTS });
    // the three backers, cheering…
    const gy = 1100, s = 44, b = lt / BL(), pb = pulse(t);
    const people = [
      { x: 360, name: 'MASA', hair: 'bald', skin: SKINS[4], tie: PAL.blue, topCol: '#3A3F58' },
      { x: 650, name: 'LARRY', hair: 'side', skin: SKINS[0], tie: PAL.red, topCol: '#4A4A55', hairCol: '#CFC8BD' },
      { x: 1340, name: 'SAM', hair: 'short', skin: SKINS[0], topCol: '#2B2E3A', hairCol: '#5A4030', sam: true },
    ];
    people.forEach((q, i) => {
      const clap = Math.abs(Math.sin((b + i * .3) * Math.PI));
      person(q.x, gy, s, {
        name: q.name, hair: q.hair, skin: q.skin, top: 'suit', topCol: q.topCol, tie: q.tie, hairCol: q.hairCol, pants: '#22242E',
        aL: q.sam ? .9 + pb * .5 : -.2 + clap * .9, aR: q.sam ? .9 + pb * .5 : -.2 + clap * .9, mouth: q.sam ? 'grin' : 'O', eyes: q.sam ? 'happy' : 'wide', dy: -pb * (q.sam ? .25 : .1),
      });
    });
    // …and TRUMP at the lectern, talking, one hand on the lectern and the other thrown up on the beat
    const tx = 960, ts = 46, jab = pulse(t, 5);
    person(tx, gy, ts, { ...TRUMP, eyes: 'dot', mouth: frac(b * 2) < .5 ? 'O' : 'grin', aL: -1.25, aR: .75 + jab * .35, pants: '#22242E', seed: 382 });
    trumpHair(tx, gy, ts);
    longTie(tx, gy, ts);
    helloTag('DONALD', tx + .75 * ts, gy - 6.9 * ts, .34 * ts, .05);
    // podium
    scrap([[830, 880], [1090, 880], [1070, 1100], [850, 1100]], '#7A5230', { torn: 1.2, seed: 1495, shade: true, shadeOp: .3 });
    scrap(rectPts(826, 868, 268, 26), '#5A3A20', { torn: .6, seed: 1497, shadow: false });
    txt('STARGATE', 960, 945, 44, PAL.gold, { font: 'bungee', maxW: 220 });
    marker([[905, 880], [925, 790]], '#555', 6, { rough: 0 }); scrap(ellPts(928, 780, 14, 18, 10), '#333', { torn: .3, shadow: false });
    camEnd();
  });

  // ======================================================================
  // V2.3 Hit "Accept All," never ask — blissed-out vibe coder slams a giant ACCEPT ALL button on every beat.
  line('V2', 3, (p, lt, d, t) => {
    slapIn(lt, .05, -.012);
    fillBG(PAL.yellow);
    raysBG(1110, 700, 18, '#FFE36E', -lt * .2);
    toneBG(PAL.pink, 20, .2, .35);
    const b = lt / BL(), f = frac(b), pb = pulse(t);
    // dialogs that nobody reads, auto-accepted every beat
    const asks = ['Edit 47 files?', 'Delete the tests?', 'Push to prod?', 'rm -rf ~/ ?', 'Email your boss?'];
    const nb = Math.floor(b + .001);
    for (let i = 0; i <= Math.min(nb, 4); i++) {
      const k = popK(lt, i * BL(), .12), x0 = 90 + i * 30, y0 = 80 + i * 80;
      ctx.save(); ctx.translate(x0 + 235, y0 + 65); ctx.rotate((hash(i + 70) - .5) * .06); const sc = backOut(k); ctx.scale(sc, sc);
      scrap(rectPts(-235, -65, 470, 130), PAL.white, { torn: 1, seed: 1500 + i, ink: PAL.ink, sw: 4 });
      ctx.fillStyle = PAL.blue; ctx.fillRect(-233, -63, 466, 28);
      txt('Allow?', -215, -49, 22, PAL.white, { font: 'archivo', align: 'left' });
      txt(asks[i], -215, 5, 38, PAL.ink, { font: 'code', align: 'left', maxW: 300 });
      ctx.restore();
      stamp('ACCEPTED', x0 + 360, y0 + 88, 30, PAL.green, -.15 + hash(i) * .1, { pop: popK(lt, i * BL() + .06, .12) });
    }
    const s = 66, px = 820, gy = 1080;
    const code = ['+ vibes = true', '+ // TODO: understand', '- test_all()', '+ retry(forever)', '+ import everything', '- // safety check', '+ ship_it()', '+ yolo = true', '- docs/', '+ fix(fix(fix))'];
    const off = Math.floor(lt * 14);
    // arm: raised through the beat, slammed down on it
    const up = .95, down = -.28;
    const aR = f < .12 ? down : f < .7 ? lerp(down, up, easeOut((f - .12) / .58)) : lerp(up, down, easeIn((f - .7) / .3));
    const press = f < .15 ? 1 - f / .15 : 0;
    const dyP = -.05 * pb;
    person(px, gy, s, { name: 'VIBES', top: 'hoodie', topCol: PAL.teal, hair: 'curly', hairCol: '#3A2A20', skin: SKINS[2], eyes: 'closed', mouth: 'grin', aR, aL: -.9 + Math.sin(b * Math.PI) * .2, dy: dyP, blush: true });
    const [hx, hy] = headAt(px, gy, s, dyP);
    headphones(hx, hy, s, PAL.pink);
    for (let i = 0; i < 4; i++) { const ph = frac(lt * .9 + i / 4); txt(i % 2 ? '♪' : '♫', hx - 130 - ph * 150 + Math.sin(ph * 9 + i) * 20, hy - 40 - ph * 220, 64, PAL.ink, { font: 'archivo', alpha: 1 - ph }); }
    // desk
    scrap([[120, 800], [1800, 800], [1840, 1100], [80, 1100]], '#8A5A3B', { torn: 1.5, seed: 1510, shade: true, shadeOp: .3 });
    scrap(rectPts(100, 780, 1720, 36), '#A8744C', { torn: 1, seed: 1511 });
    for (let i = 0; i < 4; i++) { const cx2 = 1420 + i * 95 + (i === 3 ? 30 : 0); ctx.save(); ctx.translate(cx2, 792); if (i === 3) ctx.rotate(1.45); scrap(rrPts(-32, -110, 64, 110, 10), [PAL.pink, PAL.purple, PAL.pink, PAL.purple][i], { torn: .8, seed: 1515 + i, ink: PAL.ink, sw: 3 }); ctx.fillStyle = '#C9CED9'; ctx.fillRect(-30, -110, 60, 10); txt('VIBE', 0, -55, 24, PAL.white, { font: 'bungee', rot: -Math.PI / 2 }); ctx.restore(); }
    laptop(430, 790, 38, { lines: Array.from({ length: 8 }, (_, i) => code[(i + off) % code.length]), textCol: '#6CF2B0' });
    // ACCEPT ALL button
    const bx = 1110, by = 722;
    scrap(rectPts(bx - 175, by - 8, 350, 76), '#2A2A33', { torn: 1, seed: 1512, shadow: [8, 10] });
    txt('ACCEPT ALL', bx, by + 30, 44, PAL.yellow, { font: 'archivo', maxW: 310 });
    const dome = ellPts(bx, by - 6, 125, 72 * (1 - press * .45), 36).filter(q => q[1] <= by - 6);
    scrap(dome, PAL.red, { torn: 1, seed: 1513, ink: PAL.ink, sw: 4, shade: '#8E1B14', shadeOp: .4 });
    ctx.fillStyle = alpha(PAL.white, .55); tracePath(ellPts(bx - 45, by - 44 * (1 - press * .45), 36, 12, 12, -.3)); ctx.fill();
    // the slapping hand, drawn over the dome
    const [hx2, hy2] = handAt(px, gy, s, 1, aR, dyP);
    scrap(ellPts(hx2, hy2, .6 * s, .5 * s, 16), SKINS[2], { torn: .5, seed: 1514, ink: PAL.ink, sw: 3, shadow: false });
    if (f < .3) popBurst(bx + 150, by - 110, 90, f / .3, PAL.white, 'CLICK');
    // green ticks spraying from the button
    for (let i = 0; i < 5; i++) {
      const bn = Math.floor(b), t0 = bn * BL() + (i % 3) * .03, age = (lt - t0) / .6;
      if (age < 0 || age > 1) continue;
      const a = -Math.PI / 2 + (hash2(bn, i) - .5) * 2.2, v = 300 + hash2(i, bn) * 260;
      ctx.save(); ctx.globalAlpha *= 1 - age * age; checkBadge(bx + Math.cos(a) * v * age, by - 80 + Math.sin(a) * v * age + 300 * age * age, 30, age * 6); ctx.restore();
    }
    sticker(`+${(1200 + Math.floor(lt * 5400)).toLocaleString('en-US')}\nLINES`, 1580, 400, 140, PAL.mint, { pop: popK(lt, .1, .2), rot: .12, size: 56 });
    camEnd();
  });

  // ======================================================================
  // V2.4 MCP for every task — the MCP hub fires a cable into everything: toaster, calendar, database, amp… the kitchen sink.
  function toaster(x, y, s, on, t) {
    const up = on ? backOut(clamp(on / .2), 2.5) : 0;
    for (const dx of [-1.1, 1.1]) {
      const ty = y - 6.4 * s - up * 2.6 * s + (on > .2 ? Math.abs(Math.sin(t * 8 + dx)) * .3 * s : 0);
      scrap(rrPts(x + dx * s - 1 * s, ty, 2 * s, 2.6 * s, .6 * s), '#E0A85A', { torn: .5, seed: 1520 + dx, ink: PAL.ink, sw: .1 * s, shade: '#9A6A2A', shadeOp: .3 });
    }
    scrap(rrPts(x - 3.2 * s, y - 5.4 * s, 6.4 * s, 5.4 * s, 1.2 * s), '#C9CED9', { torn: .6, seed: 1522, ink: PAL.ink, sw: .12 * s, shade: true, shadeOp: .25 });
    ctx.fillStyle = alpha(PAL.white, .7); ctx.fillRect(x - 2.4 * s, y - 4.6 * s, .6 * s, 3 * s);
    for (const dx of [-1.1, 1.1]) { ctx.fillStyle = PAL.ink; ctx.fillRect(x + dx * s - 1 * s, y - 5.5 * s, 2 * s, .35 * s); }
    scrap(rectPts(x + 2.9 * s, y - 3.6 * s + (on ? 1.4 * s : 0), .9 * s, .5 * s), PAL.ink, { torn: .2, shadow: false });
  }
  function calendar(x, y, s, on, t) {
    scrap(rectPts(x - 3 * s, y - 7 * s, 6 * s, 7 * s), PAL.white, { torn: .6, seed: 1530, ink: PAL.ink, sw: .1 * s });
    scrap(rectPts(x - 3 * s, y - 7 * s, 6 * s, 1.6 * s), PAL.red, { torn: .4, seed: 1531, shadow: false });
    txt('MAR', x, y - 6.2 * s, 1.1 * s, PAL.white, { font: 'anton' });
    const booked = on ? Math.floor(clamp(on / .4) * 20) : 0;
    for (let r = 0; r < 4; r++) for (let c = 0; c < 5; c++) {
      const i = r * 5 + c, gx = x - 2.4 * s + c * 1.2 * s, gy = y - 4.9 * s + r * 1.15 * s;
      ctx.strokeStyle = alpha(PAL.ink, .4); ctx.lineWidth = .05 * s; ctx.strokeRect(gx - .5 * s, gy - .45 * s, 1 * s, .9 * s);
      if (i < booked) { ctx.fillStyle = [PAL.pink, PAL.sky, PAL.mint, PAL.yellow][i % 4]; ctx.fillRect(gx - .45 * s, gy - .4 * s, .9 * s, .8 * s); marker([[gx - .25 * s, gy], [gx - .05 * s, gy + .2 * s], [gx + .3 * s, gy - .25 * s]], PAL.ink, .1 * s, { rough: 0 }); }
    }
    marker([[x - 2 * s, y - 7.3 * s], [x - 2 * s, y - 6.7 * s]], PAL.ink, .2 * s, { rough: 0 });
    marker([[x + 2 * s, y - 7.3 * s], [x + 2 * s, y - 6.7 * s]], PAL.ink, .2 * s, { rough: 0 });
  }
  function database(x, y, s, on, t) {
    for (let i = 0; i < 3; i++) {
      const yy = y - 1 * s - i * 2.1 * s, lit = on && (Math.floor(t * 10) + i) % 3 === 0;
      const side = []; for (let j = 0; j <= 16; j++) { const a = j / 16 * Math.PI; side.push([x + Math.cos(a) * 3 * s, yy + Math.sin(a) * .9 * s]); }
      side.push([x - 3 * s, yy - 1.8 * s], [x + 3 * s, yy - 1.8 * s]);
      scrap(side, on ? (lit ? PAL.yellow : '#5B8DEF') : '#8A93A8', { torn: .5, seed: 1540 + i, ink: PAL.ink, sw: .1 * s, shade: true, shadeOp: .25 });
      scrap(ellPts(x, yy - 1.8 * s, 3 * s, .9 * s, 24), on ? '#A9C4FF' : '#B5BCCB', { torn: .3, seed: 1545 + i, ink: PAL.ink, sw: .08 * s, shadow: false });
      if (on) { ctx.fillStyle = hash2(i, Math.floor(t * 12)) > .4 ? '#6CF2B0' : PAL.ink; tracePath(ellPts(x + 2 * s, yy - .4 * s, .25 * s, .2 * s, 8)); ctx.fill(); }
    }
  }
  function sink(x, y, s, on, t) {
    scrap(rectPts(x + .8 * s, y - 7.5 * s, .7 * s, 3.2 * s), '#B5BCCB', { torn: .3, seed: 1550, ink: PAL.ink, sw: .08 * s });
    scrap(rectPts(x - 1.2 * s, y - 7.8 * s, 2.7 * s, .7 * s), '#B5BCCB', { torn: .3, seed: 1551, ink: PAL.ink, sw: .08 * s, shadow: false });
    if (on) for (let i = 0; i < 10; i++) { const ph = frac(t * 3 + i / 10); scrap(ellPts(x - 1 * s + (hash(i) - .5) * ph * 4 * s, y - 7 * s + ph * 3 * s - Math.sin(ph * Math.PI) * 2.4 * s, .3 * s, .4 * s, 8), PAL.sky, { torn: .2, shadow: false, ink: PAL.ink, sw: .04 * s, seed: 1560 + i }); }
    scrap([[x - 3.6 * s, y - 4.4 * s], [x + 3.6 * s, y - 4.4 * s], [x + 3 * s, y - 1.2 * s], [x - 3 * s, y - 1.2 * s]], '#DDE2EA', { torn: .6, seed: 1552, ink: PAL.ink, sw: .12 * s, shade: true, shadeOp: .3 });
    scrap(rectPts(x - 3.2 * s, y - 1.3 * s, 6.4 * s, 1.3 * s), '#8A5A3B', { torn: .4, seed: 1553, shadow: false });
    txt('KITCHEN', x, y - 3.4 * s, .95 * s, PAL.ink, { font: 'archivo', maxW: 5.6 * s });
    txt('SINK', x, y - 2.3 * s, .95 * s, PAL.ink, { font: 'archivo', maxW: 5.6 * s });
  }
  function checkBadge(x, y, r, k) {
    if (k <= 0) return;
    ctx.save(); ctx.translate(x, y); const sc = backOut(clamp(k), 2.5); ctx.scale(sc, sc);
    scrap(ellPts(0, 0, r, r, 20), PAL.green, { torn: .6, seed: 1575, ink: PAL.ink, sw: 4 });
    marker([[-.45 * r, 0], [-.1 * r, .35 * r], [.5 * r, -.4 * r]], PAL.white, .22 * r, { rough: 0 });
    ctx.restore();
  }
  line('V2', 4, (p, lt, d, t) => {
    slapIn(lt, .06, .012);
    fillBG(PAL.teal);
    toneBG('#0D6B67', 20, .24, .45);
    const hubX = 880, hubY = 185, gy = 910;
    const items = [
      { x: 205, fn: toaster, s: 46, sock: [335, 668] },
      { x: 575, fn: calendar, s: 42, sock: [575, 612] },
      { x: 955, fn: database, s: 44, sock: [955, 580] },
      { x: 1335, fn: null, s: 38, sock: [1335, 648] },
      { x: 1715, fn: sink, s: 44, sock: [1735, 570] },
    ];
    ctx.fillStyle = 'rgb(0 0 0 / .15)'; ctx.fillRect(-100, gy, W + 200, 20);
    const arrive = i => .02 + i * .16;
    items.forEach((it, i) => {
      const ta = arrive(i), on = lt > ta + .12 ? lt - ta - .12 : 0;
      const dy = on ? -Math.abs(Math.sin(on * 14)) * 16 * Math.exp(-on * 3) : 0;
      ctx.save(); ctx.translate(0, dy);
      if (it.fn) it.fn(it.x, gy, it.s, on, t);
      else {
        ctx.save(); if (on) ctx.translate(jit(3), jit(3)); amp(it.x, gy, it.s, { label: 'MCP' }); ctx.restore();
        if (on) for (let j = 0; j < 3; j++) { const ph = frac(lt * 1.5 + j / 3); txt(j % 2 ? '♪' : '♫', it.x + 60 + ph * 110, gy - 290 - ph * 170, 76, PAL.yellow, { font: 'archivo', alpha: 1 - ph, stroke: PAL.ink, sw: 6 }); }
      }
      ctx.restore();
      checkBadge(it.x - 110, gy - 30, 38, (on - .05) / .15);
    });
    // cables from the hub
    items.forEach((it, i) => {
      const ta = arrive(i), k = clamp((lt - ta) / .12);
      if (k <= 0) return;
      const [ex, ey] = it.sock, sx = hubX - 200 + i * 100, sy = hubY + 80;
      const pts = []; for (let j = 0; j <= 20; j++) { const u = j / 20; pts.push([(1 - u) ** 2 * sx + 2 * (1 - u) * u * ((sx + ex) / 2 + (i - 2) * 40) + u * u * ex, (1 - u) ** 2 * sy + 2 * (1 - u) * u * (sy + 320) + u * u * (ey - 62)]); }
      const P = partial(pts, easeOut(k));
      marker(P, PAL.ink, 18, { rough: 0 }); marker(P, PAL.clawd, 10, { rough: 0 });
      const [tx, ty] = P.at(-1);
      ctx.save(); ctx.translate(tx, ty);
      scrap(rrPts(-32, -10, 64, 52, 10), PAL.ink, { torn: .5, seed: 1570 + i });
      txt('MCP', 0, 16, 22, PAL.white, { font: 'archivo' });
      ctx.fillStyle = '#C9CED9'; ctx.fillRect(-18, 42, 9, 20); ctx.fillRect(9, 42, 9, 20);
      ctx.restore();
      if (k >= 1 && lt - ta - .12 < .25) popBurst(ex, ey - 10, 80, (lt - ta - .12) / .25, PAL.yellow);
    });
    // the hub
    marker([[hubX, -40], [hubX, hubY - 60]], PAL.ink, 20, { rough: 0 }); marker([[hubX, -40], [hubX, hubY - 60]], PAL.clawd, 11, { rough: 0 });
    scrap(rrPts(hubX - 270, hubY - 85, 540, 170, 30), PAL.white, { torn: 1.2, seed: 1580, ink: PAL.ink, sw: 6, shadow: [10, 12] });
    for (let i = 0; i < 5; i++) { ctx.fillStyle = PAL.ink; ctx.fillRect(hubX - 215 + i * 100, hubY + 48, 30, 16); }
    txt('MCP', hubX, hubY - 14, 110, PAL.ink, { font: 'bungee' });
    // Clawd cameo on top of the hub, cheering each connection
    clawd(hubX + 190, hubY - 84, 11, { eyes: 'happy', mouth: 'grin', aL: .9 + pulse2(t) * .4, aR: .9 + pulse2(t + .1) * .4, dy: -pulse2(t) * .5 });
    camEnd();
  });

  // ======================================================================
  // V2.5 Zuck's nine-figure poaching spree — ZUCK fishes with a $100M money-bag lure; researchers leap for it.
  line('V2', 5, (p, lt, d, t) => {
    slapIn(lt, .05, -.012);
    fillBG('#FFC857');
    raysBG(1400, 600, 20, '#FFB43A', lt * .1);
    scrap(ellPts(1400, 600, 260, 260, 40), PAL.orange, { torn: 1.5, seed: 1590, shadow: false });
    for (let i = 0; i < 5; i++) { ctx.fillStyle = '#FFC857'; ctx.fillRect(1100, 470 + i * 26 + i * i * 2, 600, 5 + i * 2); }
    const seaY = 640;
    const wave = (yy, col, ph, amp, seed, o = {}) => { const pts = [[-60, H + 60]]; for (let i = 0; i <= 26; i++) pts.push([i * 80 - 60, yy + Math.sin(i * .8 + t * 4 + ph) * amp]); pts.push([W + 60, H + 60]); scrap(pts, col, { torn: 2, shadow: false, seed, ...o }); };
    wave(seaY, PAL.blue, 0, 10, 1591);
    // dock
    for (const x of [80, 260, 440]) scrap(rectPts(x - 16, 600, 32, 300), '#6B4A2A', { torn: .8, seed: 1592 + x });
    scrap(rectPts(-60, 585, 560, 40), '#9A6A3E', { torn: 1, seed: 1595, shade: true, shadeOp: .3 });
    // ZUCK
    const zx = 280, zy = 590, s = 42, pb = pulse(t), b = lt / BL();
    const aR = .55 + pb * .15, dyZ = -pb * .08;
    person(zx, zy, s, { name: 'ZUCK', top: 'tee', topCol: '#8E8E96', hair: 'short', hairCol: '#5A4030', skin: SKINS[4], mouth: 'grin', eyes: 'dot', aR, aL: -1 + Math.sin(b * Math.PI * 2) * .25, pants: '#3B4A6B', dy: dyZ });
    const [hx, hy] = handAt(zx, zy, s, 1, aR, dyZ);
    // rod (bends on the beat)
    const tipX = 930 + pb * 20, tipY = 120 + pb * 50;
    const rodPts = []; for (let i = 0; i <= 12; i++) { const u = i / 12; rodPts.push([lerp(hx - 40, tipX, u), lerp(hy + 30, tipY, u) + Math.sin(u * Math.PI) * (-40 + pb * 50) * u]); }
    marker(rodPts, PAL.ink, 14, { rough: 0 }); marker(rodPts, '#8B5A2B', 8, { rough: 0 });
    scrap(ellPts(hx - 14, hy + 22, 24, 24, 12), '#C9CED9', { torn: .4, seed: 1596, ink: PAL.ink, sw: 3 });
    // the bait: a money bag, and a researcher clinging to it, reeled up out of the sea
    const bagX = 1060 + Math.sin(t * 3) * 16 - ease(p) * 120, bagY = 470 + Math.sin(t * 5) * 12 - ease(p) * 190;
    marker([[tipX, tipY], [bagX, bagY - 70]], PAL.ink, 3, { rough: .5 });
    const hs = 24;
    person(bagX, bagY + 10.3 * hs, hs, { name: 'EX-OPENAI', top: 'coat', topCol: PAL.white, hair: 'long', hairCol: '#C07A3A', skin: SKINS[1], aL: 1.25, aR: 1.25, eyes: 'happy', mouth: 'grin', shadow: false, rot: Math.sin(t * 4) * .06 });
    moneyBag(bagX, bagY, 58, { label: '$100M', rot: Math.sin(t * 4) * .1 });
    // researchers leaping out of the sea for the bag (right → left arcs)
    const leapers = [
      { t0: -.45, xs: 1520, xe: 1040, name: 'EX-GDM', hair: 'bun', skin: SKINS[3], hairCol: '#2A1A10' },
      { t0: -.05, xs: 1680, xe: 1180, name: 'EX-APPLE', hair: 'spiky', skin: SKINS[0], hairCol: '#6B4A2A' },
      { t0: .35, xs: 1560, xe: 1080, name: 'EX-OPENAI', hair: 'curly', skin: SKINS[2], hairCol: '#1C1A1F' },
      { t0: .75, xs: 1700, xe: 1150, name: 'EX-GDM', hair: 'short', skin: SKINS[5], hairCol: '#3A2A20' },
      { t0: 1.15, xs: 1540, xe: 1060, name: 'EX-APPLE', hair: 'long', skin: SKINS[4], hairCol: '#B5651D' },
    ];
    const ls = 28, dur = .85, peak = 400;
    leapers.forEach((q, i) => {
      const u = (lt - q.t0) / dur; if (u < -.1 || u > 1.15) return;
      const uc = clamp(u);
      const cx = lerp(q.xs, q.xe, uc), cy = seaY + 70 - Math.sin(uc * Math.PI) * peak;
      const vx = q.xe - q.xs, vy = -Math.cos(uc * Math.PI) * Math.PI * peak, L = Math.hypot(vx, vy);
      const rot = Math.atan2(vx, -vy), hdx = vx / L, hdy = vy / L;
      person(cx - hdx * 5 * ls, cy - hdy * 5 * ls, ls, { name: q.name, top: 'coat', topCol: PAL.white, hair: q.hair, hairCol: q.hairCol, skin: q.skin, rot, aL: 1.35, aR: 1.35, eyes: 'spark', mouth: 'O', shadow: false });
    });
    // foreground sea hides whatever is under water
    wave(seaY + 22, PAL.blue, 1.3, 9, 1597, { shadow: [0, -5], shadowCol: 'rgb(0 0 0 / .15)' });
    halftone(rectPts(-60, seaY + 40, W + 120, 600), '#153E80', { cell: 16, dot: .25, op: .5 });
    for (let i = 0; i < 6; i++) { const x = (i * 330 + t * 60) % 2100 - 100; marker([[x, seaY + 110 + (i % 3) * 90], [x + 90, seaY + 104 + (i % 3) * 90]], alpha(PAL.white, .7), 6, { rough: 1 }); }
    // a queue of researchers bobbing in the sea, hands up: "pick me!"
    [[700, 830, 0], [900, 890, 1], [1110, 810, 2], [1300, 880, 3]].forEach(([x, y, i]) => {
      const bob = Math.sin(t * 6 + i * 1.7) * 8, ps = 20;
      ctx.save(); ctx.beginPath(); ctx.rect(x - 120, y - 260, 240, 262 + bob); ctx.clip();
      person(x, y + 150 + bob, ps, { name: 'PHD', top: 'coat', topCol: PAL.white, hair: ['curly', 'bun', 'side', 'buzz'][i], hairCol: ['#1C1A1F', '#6B4A2A', '#3A2A20', '#B5651D'][i], skin: SKINS[(i * 2 + 1) % 6], aR: 1.2 + Math.sin(t * 12 + i) * .25, aL: -1.2, eyes: 'spark', mouth: 'O', shadow: false });
      ctx.restore();
      marker(ellPts(x, y + 2 + bob, 46, 9, 16), alpha(PAL.white, .8), 5, { rough: 1, close: true });
    });
    // splashes where the leapers enter / exit
    leapers.forEach((q, i) => {
      for (const [x0, u0] of [[q.xs, 0], [q.xe, 1]]) {
        const age = ((lt - q.t0) / dur - u0) * dur / .35; if (age < 0 || age > 1) continue;
        for (let j = 0; j < 7; j++) { const a = -Math.PI / 2 + (j - 3) * .35; scrap(ellPts(x0 + Math.cos(a) * age * 90, seaY + 20 + Math.sin(a) * age * 120 + age * age * 90, 13, 20, 8), PAL.white, { torn: .5, shadow: false, seed: 1600 + j, ink: PAL.ink, sw: 2, op: 1 - age }); }
      }
    });
    sticker('$100,000,000', 1580, 790, 150, PAL.pink, { pop: popK(lt, .05, .22), rot: -.12, size: 44, textCol: PAL.ink });
    camEnd();
  });

  // ======================================================================
  // V2.6 Superintelligence — buy three! — a late-night infomercial on an old TV.
  function siBox(x, y, w, h, rot, k, i) { // (x, y) bottom centre on the shelf
    if (k <= 0) return;
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot); const sc = backOut(k, 2.6); ctx.scale(sc, sc);
    scrap([[-w / 2, -h], [-w / 2 + 40, -h - 40], [w / 2 + 40, -h - 40], [w / 2, -h]], '#7FB0FF', { torn: .8, seed: 1610 + i, shadow: false, ink: PAL.ink, sw: 4 });
    scrap([[w / 2, -h], [w / 2 + 40, -h - 40], [w / 2 + 40, -40], [w / 2, 0]], '#1D4FA0', { torn: .8, seed: 1613 + i, shadow: false, ink: PAL.ink, sw: 4 });
    scrap(rectPts(-w / 2, -h, w, h), PAL.blue, { torn: 1, seed: 1616 + i, ink: PAL.ink, sw: 5, shadow: [10, 10] });
    brain(0, -h * .62, w * .075, { col: PAL.pink, glow: PAL.yellow });
    txt('SUPER', 0, -h * .3, w * .2, PAL.white, { font: 'bungee', maxW: w - 30 });
    txt('INTELLIGENCE', 0, -h * .16, w * .1, PAL.yellow, { font: 'archivo', maxW: w - 30 });
    sticker('NEW!', -w / 2 + 20, -h + 20, 46, PAL.yellow, { size: 22, rot: -.3 });
    ctx.restore();
  }
  line('V2', 6, (p, lt, d, t) => {
    slapIn(lt, .05, .012);
    fillBG(PAL.pink);
    raysBG(900, 470, 16, '#FF78BD', lt * .6);
    toneBG(PAL.purple, 18, .2, .3);
    const b = lt / BL(), pb = pulse(t);
    txt('AS SEEN ON TV!', 330, 130, 44, PAL.yellow, { font: 'shrikhand', rot: -.1, stroke: PAL.ink, sw: 10 });
    // shelf
    scrap(rectPts(170, 740, 1150, 36), PAL.white, { torn: 1, seed: 1620, shade: true, shadeOp: .2 });
    for (const x of [260, 1230]) scrap([[x - 12, 776], [x + 12, 776], [x, 820]], PAL.ink, { torn: .3, seed: 1621, shadow: false });
    // three boxes, one per beat
    for (let i = 0; i < 3; i++) {
      const k = popK(lt, -.06 + i * BL(), .2);
      siBox(410 + i * 330, 740, 270, 330, (hash(i + 80) - .5) * .08 + (k >= 1 ? Math.sin(t * 8 + i) * .015 : 0), k, i);
      if (k > 0) { const nk = popK(lt, -.06 + i * BL(), .14); ransom(`${i + 1}!`, 410 + i * 330, 300 - Math.sin(nk * Math.PI) * 30, 90, { pop: nk, seed: 90 + i }); }
    }
    // BUY 3! starburst
    ctx.save(); ctx.translate(1520, 420); ctx.rotate(Math.sin(t * 6) * .06); const bs = 1 + pb * .08; ctx.scale(bs, bs);
    sticker('BUY\n3!', 0, 0, 230, PAL.yellow, { pop: popK(lt, .02, .22), rot: .1, size: 120, font: 'bungee', textCol: PAL.red, n: 20 });
    ctx.restore();
    // price
    const pk = popK(lt, BL() * 2 + .1, .2);
    if (pk > 0) {
      ctx.save(); ctx.translate(1500, 740); ctx.rotate(-.08); const sc = backOut(pk); ctx.scale(sc, sc);
      scrap(tagShape(420, 150), PAL.white, { torn: 1.5, seed: 1625, ink: PAL.ink, sw: 5 });
      txt('ONLY', -40, -34, 34, PAL.ink, { font: 'archivo' });
      txt('$14.3B*', 30, 22, 80, PAL.red, { font: 'anton' });
      ctx.restore();
    }
    // crawl
    ctx.fillStyle = PAL.ink; ctx.fillRect(40, 850, W - 80, 70);
    const crawl = 'CALL NOW!  1-800-SUPER-AI  ★  OPERATORS STANDING BY  ★  *RESEARCHERS SOLD SEPARATELY  ★  ';
    const cw = textW(crawl, 44, 'archivo'), cx0 = 60 - (lt * 500) % cw;
    ctx.save(); ctx.beginPath(); ctx.rect(40, 850, W - 80, 70); ctx.clip();
    for (let k = 0; k < 3; k++) txt(crawl, cx0 + k * cw, 887, 44, frac(b) < .5 ? PAL.yellow : PAL.white, { font: 'archivo', align: 'left' });
    ctx.restore();
    // scanlines + TV cabinet
    ctx.fillStyle = 'rgb(0 0 0 / .07)'; for (let y = 0; y < H; y += 7) ctx.fillRect(0, y + (Math.floor(t * 30) % 2), W, 3);
    ctx.save();
    ctx.beginPath(); ctx.rect(-200, -200, W + 400, H + 400); rrPts(50, 40, W - 100, H - 110, 90).forEach(([x, y], i) => i ? ctx.lineTo(x, y) : ctx.moveTo(x, y)); ctx.closePath(); ctx.fillStyle = '#6B4A2A'; ctx.fill('evenodd');
    halftone(rectPts(-200, -200, W + 400, 250), '#3A2415', { cell: 8, dot: .3, op: .3 });
    ctx.restore();
    ctx.strokeStyle = PAL.ink; ctx.lineWidth = 10; tracePath(rrPts(50, 40, W - 100, H - 110, 90)); ctx.stroke();
    ctx.fillStyle = alpha(PAL.white, .1); tracePath([[80, 60], [700, 60], [300, 900], [80, 900]]); ctx.fill();
    camEnd();
  });

  // ======================================================================
  // V2.7 Grok — tasteful: a robot's screen glitches red under a CENSORED bar, alarms, a hand yanks the plug, YIKES.
  line('V2', 7, (p, lt, d, t) => {
    const yank = .38, off = lt > yank + .04;
    const shk = lt > yank && lt < yank + .2 ? shakeXY(t, 12) : shakeXY(t, off ? 0 : 3);
    slapIn(lt, .05, 0, W / 2 - shk[0], H / 2 - shk[1]);
    fillBG('#0E0C12');
    // alarm beams
    ctx.save(); ctx.globalCompositeOperation = 'screen';
    for (const [bx, by, ph] of [[170, 250, 0], [1750, 300, 1.7]]) {
      const a = t * 7 + ph;
      ctx.fillStyle = 'rgb(232 65 47 / .3)';
      tracePath([[bx, by], [bx + Math.cos(a - .22) * 2200, by + Math.sin(a - .22) * 2200], [bx + Math.cos(a + .22) * 2200, by + Math.sin(a + .22) * 2200]]); ctx.fill();
      tracePath([[bx, by], [bx - Math.cos(a - .22) * 2200, by - Math.sin(a - .22) * 2200], [bx - Math.cos(a + .22) * 2200, by - Math.sin(a + .22) * 2200]]); ctx.fill();
    }
    ctx.fillStyle = `rgb(232 65 47 / ${.14 * pulse2(t, 5)})`; ctx.fillRect(-200, -200, W + 400, H + 400);
    ctx.restore();
    for (const [bx, by] of [[170, 250], [1750, 300]]) {
      scrap(rectPts(bx - 60, by + 20, 120, 40), '#3A3A44', { torn: .6, seed: 1630 });
      scrap([...ellPts(bx, by + 22, 55, 70, 24).filter(q => q[1] <= by + 22)], PAL.red, { torn: .6, seed: 1631, ink: PAL.ink, sw: 4 });
      ctx.fillStyle = alpha(PAL.yellow, .7 * pulse2(t, 4)); tracePath(ellPts(bx, by - 10, 22, 22, 12)); ctx.fill();
    }
    scrap(rectPts(-200, 880, W + 400, 400), '#1C1A22', { torn: 1, seed: 1632, shadow: false });
    // power strip + cord
    const sx = 1450, sy = 905;
    scrap(rectPts(sx - 120, sy - 30, 240, 52), PAL.white, { torn: .8, seed: 1633, ink: PAL.ink, sw: 4 });
    for (let i = 0; i < 3; i++) { ctx.fillStyle = PAL.ink; ctx.fillRect(sx - 90 + i * 66, sy - 16, 24, 24); }
    const yk = clamp((lt - yank) / .12);
    const plugX = lerp(sx - 24, 1720, easeOut(yk)), plugY = lerp(sy - 62, 430, easeOut(yk));
    const cord = []; for (let i = 0; i <= 16; i++) { const u = i / 16; cord.push([lerp(1050, plugX, u), lerp(800, plugY + 50, u) + Math.sin(u * Math.PI) * (130 * (1 - yk) + 20)]); }
    marker(cord, PAL.ink, 18, { rough: .5, smooth: true }); marker(cord, '#77747F', 10, { rough: .5, smooth: true });
    // robot (body from bot(), head is a big CRT monitor)
    const wob = off ? .06 * easeOut(clamp((lt - yank) / .3)) : jit(.025);
    ctx.save(); ctx.translate(960, 880); ctx.rotate(wob); ctx.translate(-960, -880);
    bot(960, 880, 56, { col: '#9AA3B5', screen: '#111', face: ' ', antenna: false, aL: off ? -1.3 : .4 + jit(.7), aR: off ? -1.3 : .9 + jit(.7), dy: off ? .08 : 0 });
    const hy0 = 880 + (off ? 5 : 0) - 690;
    scrap(rrPts(960 - 210, hy0, 420, 290, 34), '#8A93A8', { torn: 1, seed: 1636, ink: PAL.ink, sw: 5, shade: true, shadeOp: .3 });
    marker([[960, hy0], [960, hy0 - 60]], PAL.ink, 8, { rough: 0 });
    scrap(ellPts(960, hy0 - 70, 20, 20, 12), off ? '#444' : PAL.red, { torn: .3, shadow: false, ink: PAL.ink, sw: 3 });
    const X0 = 960 - 175, Y0 = hy0 + 30, SW = 350, SH = 225;
    ctx.save(); tracePath(rrPts(X0, Y0, SW, SH, 16)); ctx.clip();
    if (!off) {
      const gf = Math.floor(t * 24);
      ctx.fillStyle = PAL.red; ctx.fillRect(X0, Y0, SW, SH);
      for (let i = 0; i < 14; i++) { const yy = Y0 + hash2(gf, i) * SH, hh = 5 + hash2(gf, i + 20) * 22; ctx.fillStyle = [PAL.white, '#7A0E0A', PAL.pink, '#FF9A8A', PAL.ink][i % 5]; ctx.fillRect(X0 + (hash2(gf, i + 40) - .5) * 90, yy, SW, hh); }
    } else { ctx.fillStyle = '#16141A'; ctx.fillRect(X0, Y0, SW, SH); ctx.fillStyle = alpha(PAL.white, .8 * (1 - clamp((lt - yank) / .15))); ctx.fillRect(X0, Y0 + SH / 2 - 3, SW, 6); }
    ctx.restore();
    ctx.strokeStyle = PAL.ink; ctx.lineWidth = 5; tracePath(rrPts(X0, Y0, SW, SH, 16)); ctx.stroke();
    // CENSORED bar
    ctx.save(); ctx.translate(960 + jit(off ? 0 : 4), Y0 + SH / 2); ctx.rotate(-.07);
    scrap(rectPts(-250, -46, 500, 92), '#000', { torn: 1, seed: 1634, shadow: [6, 8], shadowCol: 'rgb(232 65 47 / .6)' });
    txt('CENSORED', 0, 3, 54, PAL.white, { font: 'mono' });
    ctx.restore();
    ctx.restore();
    // hand yanking the plug (arm from the right edge)
    const hx = plugX + 70, hy = plugY + 14;
    marker([[hx + 60, hy + 10], [2300, hy - 260 + yk * 120]], PAL.ink, 118, { rough: 0 }); marker([[hx + 60, hy + 10], [2300, hy - 260 + yk * 120]], '#2C4F8A', 104, { rough: 0 });
    scrap(rectPts(hx + 30, hy - 60, 40, 120), '#E9E4D8', { torn: .6, seed: 1639, shadow: false, ink: PAL.ink, sw: 3, rot: -.4 });
    scrap(ellPts(hx, hy, 82, 66, 18), SKINS[1], { torn: 1, seed: 1635, ink: PAL.ink, sw: 4 });
    for (let i = 0; i < 4; i++) scrap(rrPts(hx - 84 + i * 6, hy - 60 + i * 30, 70, 30, 14), SKINS[1], { torn: .5, seed: 1636 + i, ink: PAL.ink, sw: 3, shadow: false });
    ctx.save(); ctx.translate(plugX - 20, plugY);
    scrap(rrPts(-42, -24, 74, 62, 10), '#222', { torn: .4, seed: 1640 });
    ctx.fillStyle = '#C9CED9'; ctx.fillRect(-30, 38, 11, 28); ctx.fillRect(6, 38, 11, 28);
    ctx.restore();
    if (lt > yank && lt < yank + .3) { popBurst(sx - 24, sy - 40, 150, (lt - yank) / .3, PAL.yellow); for (let i = 0; i < 6; i++) { const a = -Math.PI / 2 + (i - 2.5) * .4, r = (lt - yank) * 900; marker([[sx - 24 + Math.cos(a) * r * .5, sy - 40 + Math.sin(a) * r * .5], [sx - 24 + Math.cos(a) * r, sy - 40 + Math.sin(a) * r]], PAL.yellow, 6, { rough: 1 }); } }
    stamp('YIKES', 470, 600, 150, PAL.yellow, -.18, { pop: popK(lt, yank + .08, .12), blend: 'source-over' });
    camEnd();
  });

  // ======================================================================
  // V2.8 Two labs win Olympiad gold — two robots share the top step, IMO medals, maths confetti.
  line('V2', 8, (p, lt, d, t) => {
    slapIn(lt, .05, -.012);
    fillBG(PAL.blue);
    raysBG(960, 700, 24, '#3F82E0', -lt * .25);
    toneBG('#123C8A', 22, .2, .35);
    const pb = pulse(t), b = lt / BL();
    // maths confetti (behind)
    const syms = ['π', 'Σ', '∫', '√', '∞', 'Δ', 'x²', '≠', '∀', 'θ', 'λ', '∂', '+', '÷', '=', '≤'];
    const conf = (i0, n) => { for (let i = i0; i < i0 + n; i++) {
      const x = hash(i + 90) * (W + 200) - 100 + Math.sin(t * 2 + i) * 30, y = ((lt + 2) * (220 + hash(i + 91) * 200) + hash(i + 92) * 1300) % 1300 - 150;
      txt(syms[i % syms.length], x, y, 60 + hash(i + 93) * 50, [PAL.yellow, PAL.pink, PAL.white, PAL.mint, PAL.gold][i % 5], { font: 'mono', rot: t * (hash(i + 94) - .5) * 4, shadow: [4, 5] });
    } };
    conf(0, 14);
    // press flashes
    for (let i = 0; i < 6; i++) { const t0 = .2 + i * BL() * .75, age = (lt - t0) / .2; popBurst([150, 1760, 280, 1640, 110, 1800][i], [620, 520, 800, 760, 420, 700][i], 90, age, PAL.white); }
    // podium
    const blocks = [[960, 700, 640, '1', PAL.white], [470, 830, 320, '2', '#D8DDE6'], [1450, 870, 320, '3', '#E9C9A0']];
    for (const [x, top, w, n, c] of blocks) {
      scrap(rectPts(x - w / 2, top, w, 1080 - top + 50), c, { torn: 1.2, seed: 1650 + +n, ink: PAL.ink, sw: 5, shade: true, shadeOp: .2 });
      txt(n, x, top + 105, 140, n === '1' ? PAL.gold : PAL.grey, { font: 'abril', stroke: PAL.ink, sw: 6 });
    }
    // two robots jostling on the top step
    const R = [{ x: 790, col: '#E6E9EE', name: 'OPENAI', ph: 0, rib: PAL.pink }, { x: 1130, col: '#8FB8F2', name: 'DEEPMIND', ph: .5, rib: PAL.red }];
    R.forEach((r, i) => {
      const hop = Math.max(0, Math.sin((b + r.ph) * Math.PI)) ** 2;
      const s = 42, gy = 700, dy = -hop * .45, lean = Math.sin(b * Math.PI) * (i ? -10 : 10);
      bot(r.x + lean, gy, s, { col: r.col, eyes: 'spark', dy, aL: i ? .3 + hop * .9 : 1.3, aR: i ? 1.3 : .3 + hop * .9, seed: 500 + i * 30 });
      helloTag(r.name, r.x + lean, gy + dy * s - 3.95 * s, s * .5, i ? .06 : -.06);
      const mk = popK(lt, .04 + i * .1, .28);
      const my = lerp(-250, gy + dy * s - 6.3 * s, easeOut(mk)) + (mk < 1 ? 0 : Math.sin((lt - .4) * 12) * 3);
      if (mk > 0) medal(r.x + lean, my, 22, { text: 'IMO', ribbon: r.rib, rot: Math.sin(t * 6 + i) * .08 });
    });
    conf(14, 10);
    camEnd();
  });

  // ======================================================================
  // V2.9 GPT-5 breaks 4o hearts — a GPT-5 mallet cracks the "4o" heart; #keep4o protesters weep.
  line('V2', 9, (p, lt, d, t) => {
    const hitT = .26;
    const shk = lt > hitT && lt < hitT + .2 ? shakeXY(t, 16) : [0, 0];
    slapIn(lt, .05, .012, W / 2 - shk[0], H / 2 - shk[1]);
    fillBG('#FFB8D6');
    toneBG(PAL.red, 20, .18, .35);
    const cx = 960, cy = 410, r = 270, broken = lt > hitT, bk = clamp((lt - hitT) / .6);
    const beat = broken ? 1 : 1 + pulse(t, 8) * .06;
    const heartFace = (sad) => {
      txt('4o', 0, -20, 190, PAL.white, { font: 'archivo', stroke: PAL.ink, sw: 10 });
      ctx.strokeStyle = PAL.ink; ctx.fillStyle = PAL.ink; ctx.lineWidth = 9; ctx.lineCap = 'round';
      for (const sd of [-1, 1]) {
        if (sad) { ctx.beginPath(); ctx.moveTo(sd * 150 - 26, -110); ctx.lineTo(sd * 150 + 26, -84); ctx.moveTo(sd * 150 + 26, -110); ctx.lineTo(sd * 150 - 26, -84); ctx.stroke(); }
        else { ctx.beginPath(); ctx.arc(sd * 150, -90, 22, Math.PI * 1.1, Math.PI * 1.9); ctx.stroke(); }
      }
      ctx.fillStyle = alpha(PAL.white, .7); tracePath(ellPts(-175, 25, 26, 14, 10)); ctx.fill(); tracePath(ellPts(175, 25, 26, 14, 10)); ctx.fill();
    };
    const drawHeart = (sad) => {
      scrap(heartPts(0, 0, r), PAL.red, { torn: 2, seed: 1660, ink: PAL.ink, sw: 7, shadow: [12, 14], shade: '#8E1B14', shadeOp: .35 });
      heartFace(sad);
    };
    const zz = []; for (let i = 0; i <= 9; i++) zz.push([i === 0 || i === 9 ? 0 : (i % 2 ? 26 : -26), -r * .42 + i * (r * 1.55) / 9]);
    if (!broken) {
      ctx.save(); ctx.translate(cx, cy); ctx.scale(beat, beat); drawHeart(false); ctx.restore();
    } else {
      for (const sd of [-1, 1]) {
        ctx.save(); ctx.translate(cx + sd * easeOut(bk) * 120, cy + bk * bk * 50); ctx.rotate(sd * easeOut(bk) * .3);
        ctx.beginPath(); ctx.moveTo(sd * 600, -600); ctx.lineTo(0, -600); zz.forEach(([a, b2]) => ctx.lineTo(a, b2)); ctx.lineTo(0, 600); ctx.lineTo(sd * 600, 600); ctx.closePath(); ctx.clip();
        drawHeart(true);
        marker(zz, PAL.ink, 6, { rough: 1 });
        ctx.restore();
      }
      // falling heart crumbs
      for (let i = 0; i < 6; i++) { const age = lt - hitT, x = cx + (hash(i + 130) - .5) * 80, y = cy + age * 300 + age * age * 900 * (.6 + hash(i + 131)); scrap(xform([[-12, -10], [14, -6], [4, 14]], x, y, age * 8 + i), PAL.red, { torn: .5, shadow: false, ink: PAL.ink, sw: 2 }); }
      if (lt < hitT + .3) popBurst(cx, cy - 150, 160, (lt - hitT) / .3, PAL.white, 'CRACK');
    }
    // the GPT-5 mallet: swings in from the right, smashes, flies back out
    const px = 1560, py = -320, L = 780;
    const th = lt < .1 ? lerp(.3, .45, easeOut(lt / .1)) : lt < hitT ? lerp(.45, -.62, easeIn((lt - .1) / (hitT - .1))) : lerp(-.62, .6, easeInOutQ(clamp((lt - hitT - .05) / .4)));
    ctx.save(); ctx.translate(px, py); ctx.rotate(-th);
    marker([[0, 0], [0, L]], PAL.ink, 32, { rough: 0 }); marker([[0, 0], [0, L]], '#B07A45', 22, { rough: 0 });
    scrap(rrPts(-180, L - 95, 360, 190, 24), '#2E3440', { torn: 1, seed: 1665, ink: PAL.ink, sw: 5, shade: true, shadeOp: .3 });
    scrap(rectPts(-190, L - 100, 30, 200), '#4A5262', { torn: .5, seed: 1666, shadow: false, ink: PAL.ink, sw: 3 });
    scrap(rectPts(160, L - 100, 30, 200), '#4A5262', { torn: .5, seed: 1667, shadow: false, ink: PAL.ink, sw: 3 });
    txt('GPT-5', 0, L + 4, 86, PAL.white, { font: 'anton' });
    ctx.restore();
    // protesters
    const P = [[180, 0], [420, .3], [1500, .6], [1740, .9]];
    P.forEach(([x, ph], i) => {
      const bob = Math.abs(Math.sin((lt / BL() + ph) * Math.PI)), s = 22, gy = 955;
      const cry = broken;
      person(x, gy, s, { name: ['JUNE', 'ALEX', 'RILEY', 'KAI'][i], top: ['hoodie', 'sweater', 'tee', 'dress'][i], topCol: [PAL.purple, PAL.teal, PAL.blue, PAL.green][i], hair: ['long', 'curly', 'short', 'bun'][i], skin: SKINS[[1, 3, 0, 2][i]], eyes: cry ? 'closed' : 'dot', mouth: cry ? 'O' : 'frown', aR: 1.15 + bob * .1, aL: cry ? .9 : -1.1, dy: -bob * .1 });
      const [hx, hy] = handAt(x, gy, s, 1, 1.15 + bob * .1, -bob * .1);
      marker([[hx, hy + 30], [hx, hy - 120]], '#8B5A2B', 9, { rough: 0 });
      card(hx, hy - 165, 230, 96, PAL.white, (hash(i) - .5) * .2, { torn: 1, seed: 1670 + i, ink: PAL.ink, sw: 4 });
      txt('#keep4o', hx, hy - 163, 48, PAL.red, { font: 'marker', rot: (hash(i) - .5) * .2, maxW: 205 });
      if (cry) {
        const [ex, ey] = headAt(x, gy, s, -bob * .1);
        for (const sd of [-1, 1]) for (let j = 0; j < 5; j++) { const ph2 = frac(lt * 2.5 + j / 5); scrap(ellPts(ex + sd * (12 + ph2 * 70), ey + ph2 * 100 - Math.sin(ph2 * Math.PI) * 50, 7, 11, 8), PAL.sky, { torn: .2, shadow: false, ink: PAL.ink, sw: 1.5 }); }
      }
    });
    camEnd();
  });
  function easeInOutQ(k) { k = clamp(k); return k < .5 ? 2 * k * k : 1 - (-2 * k + 2) ** 2 / 2; }

  // ======================================================================
  // V2.10 Nano Banana tops the charts — a banana in shades rides its bar to #1 under sweeping spotlights.
  function bananaGuy(x, y, s, o = {}) { // (x, y) = feet
    ctx.save(); ctx.translate(x, y); if (o.rot) ctx.rotate(o.rot);
    ctx.translate(0, o.dy ?? 0);
    for (const sd of [-1, 1]) { marker([[sd * .7 * s, -1.5 * s], [sd * 1 * s, 0]], PAL.ink, .35 * s, { rough: 0 }); scrap(ellPts(sd * 1.2 * s, -.1 * s, .6 * s, .3 * s, 10), PAL.red, { torn: .2, shadow: false }); }
    const spine = u => [1.3 * s * Math.sin(Math.PI * u) - .3 * s, lerp(-10.5 * s, -1.2 * s, u)];
    const wid = u => 1.75 * s * Math.sin(Math.PI * clamp(u * .95 + .03)) ** .7 + .2 * s;
    const L = [], Rr = [];
    for (let i = 0; i <= 20; i++) { const u = i / 20, [sx, sy] = spine(u), w = wid(u); L.push([sx - w, sy]); Rr.push([sx + w, sy]); }
    const aL = o.aL ?? 1, aR = o.aR ?? 1;
    const [lx, ly] = spine(.5);
    const hL = [lx - 1.2 * s - Math.cos(aL) * 3 * s, ly - Math.sin(aL) * 3 * s], hR = [lx + 1.6 * s + Math.cos(aR) * 3 * s, ly - Math.sin(aR) * 3 * s];
    marker([[lx - 1.2 * s, ly], hL], PAL.ink, .35 * s, { rough: 0 });
    marker([[lx + 1.6 * s, ly], hR], PAL.ink, .35 * s, { rough: 0 });
    for (const [hx, hy] of [hL, hR]) scrap(ellPts(hx, hy, .6 * s, .6 * s, 10), PAL.white, { torn: .2, shadow: false, ink: PAL.ink, sw: .1 * s });
    scrap([...L, ...Rr.reverse()], PAL.yellow, { torn: .8, seed: 1680, ink: PAL.ink, sw: .2 * s, shade: '#B08A1E', shadeDir: [1, 0], shadeOp: .45 });
    scrap(rectPts(-.75 * s, -11.6 * s, .8 * s, 1.3 * s), '#6B4A2A', { torn: .3, seed: 1681, shadow: false, ink: PAL.ink, sw: .08 * s });
    const [fx, fy] = spine(.35);
    ctx.fillStyle = PAL.ink;
    for (const sd of [-1, 1]) tracePath(rrPts(fx + sd * .75 * s - .65 * s, fy - .45 * s, 1.3 * s, .8 * s, .25 * s)), ctx.fill();
    ctx.fillRect(fx - .2 * s, fy - .35 * s, .4 * s, .15 * s);
    ctx.fillStyle = alpha(PAL.white, .6); ctx.fillRect(fx - 1.1 * s, fy - .3 * s, .35 * s, .15 * s); ctx.fillRect(fx + .4 * s, fy - .3 * s, .35 * s, .15 * s);
    ctx.fillStyle = PAL.ink; ctx.beginPath(); ctx.moveTo(fx - .8 * s, fy + .8 * s); ctx.quadraticCurveTo(fx, fy + 1.9 * s, fx + .8 * s, fy + .8 * s); ctx.closePath(); ctx.fill();
    ctx.restore();
  }
  line('V2', 10, (p, lt, d, t) => {
    slapIn(lt, .05, -.012);
    fillBG('#4A2A8C');
    toneBG('#2A1360', 20, .25, .5);
    const pb = pulse(t), b = lt / BL();
    const baseY = 880, grow = backOut(clamp(lt / .3), 1.4), topH = 430 * grow, topY = baseY - topH;
    // spotlights converge on #1
    ctx.save(); ctx.globalCompositeOperation = 'screen';
    for (const [x0, ph] of [[250, 0], [1670, 1.4]]) {
      const tx = 960 + Math.sin(t * 3 + ph) * 90;
      ctx.fillStyle = 'rgb(255 216 58 / .26)';
      tracePath([[x0 - 40, -40], [x0 + 40, -40], [tx + 200, topY], [tx - 200, topY]]); ctx.fill();
      tracePath(ellPts(tx, topY, 200, 30, 20)); ctx.fill();
    }
    ctx.restore();
    const bars = [[380, 250, PAL.sky], [640, 330, PAL.mint], [960, 0, PAL.gold], [1280, 290, PAL.pink], [1540, 200, PAL.sky]];
    txt('TOP CHARTS', 330, 120, 70, PAL.white, { font: 'bungee', rot: -.05, stroke: PAL.ink, sw: 10 });
    marker([[230, 190], [230, baseY], [1720, baseY]], PAL.white, 9, { rough: 1 });
    bars.forEach(([x, h, c], i) => {
      const hh = i === 2 ? topH : h * (1 - .25 * clamp(lt / .5)) * (1 + Math.sin(t * 6 + i) * .02);
      scrap(rectPts(x - 110, baseY - hh, 220, hh), c, { torn: 1, seed: 1690 + i, ink: PAL.ink, sw: 5, shade: true, shadeOp: .25 });
      txt(`#${[4, 2, 1, 3, 5][i]}`, x, baseY - Math.min(hh / 2, 120), i === 2 ? 110 : 56, i === 2 ? PAL.red : PAL.ink, { font: i === 2 ? 'bungee' : 'anton', stroke: i === 2 ? PAL.ink : undefined, sw: 8 });
    });
    const hop = Math.max(0, Math.sin(b * Math.PI)) ** 2;
    bananaGuy(960, topY - 4, 31, { dy: -hop * 40, aL: 1.1 + pb * .3, aR: 1.1 + pb * .3, rot: Math.sin(b * Math.PI) * .08 });
    for (let i = 0; i < 8; i++) { const a = i / 8 * TAU + t * 2, rr = 250 + Math.sin(t * 5 + i) * 20; const k = .6 + .4 * Math.sin(t * 9 + i * 2); scrap(starPts(960 + Math.cos(a) * rr, topY - 190 + Math.sin(a) * rr * .6, 30 * k, .35, 4, 0), PAL.yellow, { torn: .3, shadow: false }); }
    camEnd();
  });

  // ======================================================================
  // V2.11 Billion-five: Anthropic's prize — a giant cheque to THE AUTHORS; happy books hop; Clawd sweats.
  function happyBook(x, y, w, h, col, hop, i) {
    ctx.save(); ctx.translate(x, y - hop); ctx.rotate(Math.sin(hop * .02 + i) * .05 * (hop > 1 ? 1 : 0));
    for (const sd of [-1, 1]) marker([[sd * w * .25, 0], [sd * w * .3, hop > 1 ? 10 : 30]], PAL.ink, 8, { rough: 0 });
    scrap(rectPts(-w / 2, -h, w, h), col, { torn: 1, seed: 1700 + i, ink: PAL.ink, sw: 4, shade: true, shadeOp: .2 });
    ctx.fillStyle = PAL.cream; ctx.fillRect(w / 2 - 12, -h + 8, 8, h - 16);
    ctx.fillStyle = alpha(PAL.ink, .25); ctx.fillRect(-w / 2 + 12, -h, 10, h);
    ctx.fillStyle = PAL.ink;
    for (const sd of [-1, 1]) { ctx.beginPath(); ctx.arc(sd * w * .18, -h * .62, 9, Math.PI * 1.1, Math.PI * 1.9); ctx.lineWidth = 6; ctx.strokeStyle = PAL.ink; ctx.stroke(); }
    ctx.beginPath(); ctx.moveTo(-w * .22, -h * .45); ctx.quadraticCurveTo(0, -h * .2, w * .22, -h * .45); ctx.closePath(); ctx.fill();
    for (const sd of [-1, 1]) marker([[sd * w / 2, -h * .55], [sd * (w / 2 + 40), -h * .95 - (hop > 1 ? 20 : 0)]], PAL.ink, 7, { rough: 0 });
    ctx.restore();
  }
  line('V2', 11, (p, lt, d, t) => {
    slapIn(lt, .05, .012);
    fillBG(PAL.mint);
    toneBG(PAL.green, 20, .22, .35);
    const pb = pulse(t), b = lt / BL();
    // cheque slides in
    const ck = easeOut(clamp(lt / .16));
    const qx = lerp(2400, 850, ck), qy = 350, qr = lerp(.2, -.035, ck) + (ck >= 1 ? Math.sin(t * 3) * .006 : 0);
    ctx.save(); ctx.translate(qx, qy); ctx.rotate(qr);
    const w = 1200, h = 480;
    scrap(rectPts(-w / 2, -h / 2, w, h), '#EAF3FF', { torn: 2, seed: 1710, ink: PAL.ink, sw: 5, shadow: [14, 16] });
    ctx.strokeStyle = alpha(PAL.blue, .25); ctx.lineWidth = 3;
    for (let i = 0; i < 5; i++) { ctx.beginPath(); for (let j = 0; j <= 40; j++) { const xx = -w / 2 + 20 + j / 40 * (w - 40), yy = -h / 2 + 60 + i * 12 + Math.sin(j * .7 + i) * 8; j ? ctx.lineTo(xx, yy) : ctx.moveTo(xx, yy); } ctx.stroke(); }
    txt('BANK OF SETTLEMENTS', -w / 2 + 40, -h / 2 + 50, 34, PAL.ink, { font: 'abril', align: 'left' });
    txt('No. 1500000000', w / 2 - 40, -h / 2 + 50, 26, PAL.ink, { font: 'typewriter', align: 'right' });
    txt('PAY TO THE ORDER OF', -w / 2 + 40, -h / 2 + 150, 26, PAL.ink, { font: 'archivo', align: 'left' });
    txt('THE AUTHORS', -w / 2 + 395, -h / 2 + 150, 58, PAL.ink, { font: 'marker', align: 'left' });
    marker([[-w / 2 + 360, -h / 2 + 185], [w / 2 - 420, -h / 2 + 185]], PAL.ink, 3, { rough: 0 });
    scrap(rectPts(w / 2 - 400, -h / 2 + 110, 360, 90), PAL.white, { torn: .5, seed: 1711, ink: PAL.ink, sw: 3, shadow: false });
    txt('$1.5B', w / 2 - 220, -h / 2 + 157, 70, PAL.green, { font: 'anton' });
    txt('$1,500,000,000', 0, 40, 150, PAL.green, { font: 'anton', stroke: PAL.ink, sw: 8, maxW: w - 100 });
    txt('MEMO: sorry about the books', -w / 2 + 40, h / 2 - 60, 30, PAL.ink, { font: 'typewriter', align: 'left' });
    const sk = clamp((lt - .3) / .5);
    const sig = []; for (let i = 0; i <= 30; i++) { const u = i / 30; sig.push([w / 2 - 460 + u * 380, h / 2 - 70 + Math.sin(u * 22) * 22 - u * 20]); }
    if (sk > 0) marker(partial(sig, sk), PAL.blue, 6, { rough: 1, smooth: true });
    marker([[w / 2 - 480, h / 2 - 40], [w / 2 - 60, h / 2 - 40]], PAL.ink, 3, { rough: 0 });
    txt('— Anthropic', w / 2 - 270, h / 2 - 20, 22, PAL.ink, { font: 'typewriter' });
    ctx.restore();
    // books cheering
    const bcol = [PAL.red, PAL.blue, PAL.yellow, PAL.purple, PAL.pink, PAL.teal];
    for (let i = 0; i < 6; i++) {
      const hop = Math.max(0, Math.sin((b + i * .33) * Math.PI)) * 70;
      happyBook(170 + i * 230, 935, 120 + (i % 3) * 14, 170 + (i % 2) * 30, bcol[i], hop, i);
    }
    // Clawd sweating in the corner
    clawd(1690, 930, 18, { eyes: 'worried', mouth: 'flat', sweat: true, blush: true, aL: -.2, aR: .5 + Math.sin(t * 20) * .1, dy: jit(.08) });
    if (lt > .4) for (let i = 0; i < 3; i++) { const ph = frac(lt * 1.6 + i / 3); scrap(ellPts(1690 + 100 + ph * 40 + i * 12, 930 - 150 + ph * 60, 8, 12, 8), PAL.sky, { torn: .2, shadow: false, ink: PAL.ink, sw: 2, op: 1 - ph }); }
    camEnd();
  });

  // ======================================================================
  // V2.12 Yudkowsky drops "Everyone Dies" — the book drops like a mic from a fedora'd hand; THUD.
  function ifBook(x, y, w, h, rot = 0) { // (x, y) = centre
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot);
    scrap(rectPts(-w / 2 + 14, -h / 2 + 10, w, h), '#C9C3B5', { torn: .8, seed: 1720, shadow: [10, 14] });
    scrap(rectPts(-w / 2, -h / 2, w, h), PAL.white, { torn: 1, seed: 1721, ink: PAL.ink, sw: 4, shadow: false });
    ctx.fillStyle = PAL.ink; ctx.fillRect(-w / 2, -h / 2, 18, h);
    txt('IF ANYONE', 9, -h * .36, w * .13, PAL.ink, { font: 'archivo', maxW: w - 50 });
    txt('BUILDS IT,', 9, -h * .25, w * .13, PAL.ink, { font: 'archivo', maxW: w - 50 });
    txt('EVERYONE', 9, -h * .02, w * .22, PAL.red, { font: 'anton', maxW: w - 44 });
    txt('DIES', 9, h * .22, w * .36, PAL.red, { font: 'anton', maxW: w - 44 });
    ctx.fillStyle = PAL.ink; ctx.fillRect(-w / 2 + 40, h * .4, w - 80, 4);
    ctx.restore();
  }
  line('V2', 12, (p, lt, d, t) => {
    const rel = .1, land = BL() + .02;
    const shk = lt > land && lt < land + .25 ? shakeXY(t, 22 * (1 - (lt - land) / .25)) : [0, 0];
    const zk = ease(clamp((lt - land - .1) / .8));
    camBegin(lerp(960, 920, zk) - shk[0], lerp(540, 530, zk) - shk[1], lerp(1, 1.07, zk) * (1 + .05 * (1 - easeOut(clamp(lt / .13)))));
    fillBG('#141218');
    ctx.save(); ctx.globalCompositeOperation = 'screen';
    ctx.fillStyle = 'rgb(255 248 231 / .16)'; tracePath([[560, -100], [860, -100], [1400, 940], [240, 940]]); ctx.fill();
    tracePath(ellPts(820, 940, 580, 70, 30)); ctx.fill();
    ctx.restore();
    scrap(rectPts(-200, 930, W + 400, 400), '#2A2630', { torn: 1, seed: 1730, shadow: false });
    // soapbox
    scrap(rectPts(380, 630, 380, 310), '#6B4A2A', { torn: 1, seed: 1731, shade: true, shadeOp: .3, ink: PAL.ink, sw: 4 });
    for (let i = 0; i < 3; i++) { ctx.fillStyle = 'rgb(0 0 0 / .25)'; ctx.fillRect(385, 710 + i * 75, 370, 5); }
    txt('SOAP', 570, 800, 64, alpha(PAL.cream, .8), { font: 'bungee', rot: -.04 });
    // Eliezer, fedora on
    const ex = 560, ey = 630, s = 50;
    const aR = .05;
    person(ex, ey, s, { name: 'ELIEZER', top: 'tee', topCol: '#3A3F58', hair: 'short', hairCol: '#3A2A20', skin: SKINS[0], eyes: lt < land ? 'dot' : 'closed', mouth: lt < land ? 'flat' : 'smile', aR, aL: -1.2, pants: '#22242E', brows: lt < land ? null : 'angry' });
    const [hx, hy] = headAt(ex, ey, s);
    fedora(hx, hy, s);
    // the book
    const [px, py] = handAt(ex, ey, s, 1, aR);
    const bw = 300, bh = 420;
    const bx = px + bw / 2 - 30;
    let by = py + bh / 2 - 12, brot = 0;
    if (lt >= rel) {
      const u = clamp((lt - rel) / (land - rel));
      by = lerp(py + bh / 2 - 12, 930 - bh / 2, u * u); brot = u * .06;
      if (lt > land) { const k = clamp((lt - land) / .2); brot = .06 * (1 - k) + Math.sin(k * Math.PI * 2) * .02 * (1 - k); }
    }
    const sq = lt > land && lt < land + .12 ? 1 - Math.sin((lt - land) / .12 * Math.PI) * .08 : 1;
    ctx.save(); ctx.translate(bx, 930); ctx.scale(2 - sq, sq); ctx.translate(-bx, -930);
    ifBook(bx, by, bw, bh, brot);
    ctx.restore();
    if (lt < rel + .04) { scrap(ellPts(px + 8, py + 4, 24, 20, 12), SKINS[0], { torn: .4, seed: 1735, ink: PAL.ink, sw: 3, shadow: false }); }
    else if (lt < land) for (let i = 0; i < 3; i++) marker([[bx - 90 + i * 90, by - bh / 2 - 30 - i * 5], [bx - 90 + i * 90, by - bh / 2 - 100 - i * 5]], PAL.white, 7, { rough: 1, alpha: .7 });
    if (lt > rel + .02) { // the hand: fingers splayed, "mic drop"
      for (let i = 0; i < 4; i++) marker([[px, py], [px + Math.cos(-.9 + i * .45) * 44, py + Math.sin(-.9 + i * .45) * 44]], SKINS[0], 12, { rough: 0 });
    }
    if (lt > land) {
      const k = clamp((lt - land) / .5);
      for (let i = 0; i < 8; i++) { const sd = i < 4 ? -1 : 1, j = i % 4; scrap(ellPts(bx + sd * (bw / 2 + 20 + k * (60 + j * 50)), 920 - j * 18 - k * 30, 40 * (1 - k * .4) + j * 6, 26, 12), alpha('#8E8A96', 1 - k), { torn: 3, shadow: false, seed: 1740 + i }); }
      for (const sd of [-1, 1]) marker([[bx + sd * bw * .4, 935], [bx + sd * (bw * .6 + 30), 960], [bx + sd * (bw * .7 + 50), 945], [bx + sd * (bw * .9 + 70), 975]], PAL.ink, 5, { rough: 1 });
      ransom('THUD!', 1450, 520, 170, { pop: clamp((lt - land) / .15), seed: 1312, jolt: 3, fonts: LOUD_FONTS });
    }
    camEnd();
  });

  // ======================================================================
  // V2.13 "Clanker!" spat in every screed — a sad robot pelted by CLANKER! speech bubbles.
  function shout(str, x, y, size, col, font, rot, tail, seed) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot);
    const w = textW(str, size, font) + size * .9, h = size * 1.5;
    if (tail) scrap([[tail * w * .25, -h * .2], [tail * (w * .5 + 70), -h * .65], [tail * w * .25, h * .2]], col, { torn: .5, seed, ink: PAL.ink, sw: 4, shadow: false });
    scrap(roughen(ellPts(0, 0, w * .6, h * .62, 20), 6, 18, seed, false), col, { torn: 1.5, seed: seed + 1, ink: PAL.ink, sw: 4, shadow: [6, 8] });
    txt(str, 0, 2, size, col === PAL.red || col === PAL.ink ? PAL.white : PAL.ink, { font, maxW: w });
    ctx.restore();
  }
  line('V2', 13, (p, lt, d, t) => {
    slapIn(lt, .05, -.012);
    fillBG(PAL.yellow);
    toneBG(PAL.orange, 18, .24, .4);
    const rx = 960, gy = 930, s = 52;
    ctx.fillStyle = 'rgb(0 0 0 / .1)'; ctx.fillRect(-100, gy, W + 200, 300);
    const words = ['CLANKER!', 'CLANKER!!', 'clanker', 'CLANKER', 'Clanker!', 'CLANK!', 'CLANKER?!', 'CLANKER!'];
    const cols = [PAL.white, PAL.pink, PAL.red, PAL.sky, PAL.white, PAL.mint, PAL.ink, PAL.white];
    const fonts = ['anton', 'marker', 'fraktur', 'bungee', 'typewriter', 'shrikhand', 'archivo', 'rammetto'];
    const N = 12, flight = .22, t0s = i => -.4 + i * BL() / 2;
    let flinch = 0, hits = 0;
    for (let i = 0; i < N; i++) { const h = t0s(i) + flight; if (lt > h) hits++; if (lt > h && lt < h + .15) flinch = Math.max(flinch, 1 - (lt - h) / .15); }
    const side0 = Math.floor(lt * 20) % 2 ? 1 : -1;
    bot(rx + flinch * 16 * side0, gy, s, { col: '#A7AEBB', face: 'T_T', faceCol: '#6CF2B0', aL: 1.35 + flinch * .2, aR: 1.35 + flinch * .2, dy: flinch * .12, sq: flinch * .06, rot: -.04 + flinch * .04 * side0 });
    const headY = gy + flinch * .12 * s - 10.6 * s;
    // bandages accumulate
    if (hits > 3) { ctx.save(); ctx.translate(rx + 50 + flinch * 16 * side0, headY + 20); ctx.rotate(.6); scrap(rrPts(-50, -14, 100, 28, 10), '#F2D2B5', { torn: .5, shadow: false, ink: PAL.ink, sw: 2 }); ctx.restore(); }
    if (hits > 6) { ctx.save(); ctx.translate(rx - 70 + flinch * 16 * side0, headY + 60); ctx.rotate(-.4); scrap(rrPts(-40, -12, 80, 24, 10), '#F2D2B5', { torn: .5, shadow: false, ink: PAL.ink, sw: 2 }); ctx.restore(); }
    for (const sd of [-1, 1]) { const ph = frac(lt * 2 + (sd > 0 ? .5 : 0)); scrap(ellPts(rx + sd * 34, gy - 9 * s + ph * 90, 8, 12, 8), PAL.sky, { torn: .2, shadow: false, ink: PAL.ink, sw: 2 }); }
    // incoming bubbles, alternating sides on eighth notes
    for (let i = 0; i < N; i++) {
      const u = (lt - t0s(i)) / flight;
      if (u < 0) continue;
      const side = i % 2 ? 1 : -1, y0 = 160 + hash(i + 100) * 560, tx = rx + side * (170 + hash(i + 101) * 80), ty = headY + 40 + hash(i + 102) * 200;
      const x0 = rx + side * 1300;
      let x, y, rot = (hash(i + 103) - .5) * .4;
      if (u <= 1) { x = lerp(x0, tx, u); y = lerp(y0, ty, u) - Math.sin(u * Math.PI) * 100; }
      else { const a = (u - 1) * flight; x = tx + side * a * 700; y = Math.min(gy + 10 - hash(i) * 50, ty + a * a * 5000 - a * 500); rot += side * Math.min(a, .35) * 5; }
      shout(words[i % 8], x, y, 66 + hash(i + 104) * 22, cols[i % 8], fonts[i % 8], rot, u <= 1 ? side : 0, 1750 + i * 3);
      if (u > 1 && u < 1 + .15 / flight) popBurst(tx - side * 40, ty, 80, (u - 1) * flight / .15, PAL.white, 'BONK');
    }
    camEnd();
  });

  // ======================================================================
  // V2.14 Sora slop in every feed — a phone pours sloppy AI videos into a pig trough labelled FEED.
  function pig(x, y, s, o = {}) { // (x, y) = ground, facing left unless flip
    ctx.save(); ctx.translate(x, y); if (o.flip) ctx.scale(-1, 1);
    const pinkC = '#F7A1C0', dk = '#D96A94';
    for (const lx of [-2.2, -1, 1.2, 2.3]) scrap(rectPts(lx * s - .4 * s, -1.6 * s, .8 * s, 1.6 * s), dk, { torn: .3, seed: 1760 + lx, shadow: false });
    const tail = []; for (let i = 0; i <= 12; i++) { const a = i / 12 * TAU * 1.3; tail.push([3.4 * s + Math.cos(a) * .35 * s + i * .05 * s, -3.4 * s + Math.sin(a) * .35 * s]); }
    marker(tail, dk, .22 * s, { rough: 0, smooth: true });
    scrap(ellPts(.4 * s, -3 * s, 3.3 * s, 2 * s, 30), pinkC, { torn: .6, seed: 1765, ink: PAL.ink, sw: .1 * s, shade: dk, shadeOp: .4 });
    ctx.save(); ctx.translate(-2.6 * s, -3.2 * s + (o.dip ?? 0) * s); ctx.rotate((o.dip ?? 0) * .3);
    scrap([[-.2 * s, -1.4 * s], [-.9 * s, -2.4 * s], [.3 * s, -1.8 * s]], dk, { torn: .3, seed: 1766, shadow: false, ink: PAL.ink, sw: .06 * s });
    scrap([[.6 * s, -1.2 * s], [.6 * s, -2.5 * s], [1.2 * s, -1.4 * s]], dk, { torn: .3, seed: 1767, shadow: false, ink: PAL.ink, sw: .06 * s });
    scrap(ellPts(0, 0, 1.5 * s, 1.4 * s, 24), pinkC, { torn: .5, seed: 1768, ink: PAL.ink, sw: .1 * s });
    scrap(ellPts(-1.3 * s, .3 * s, .6 * s, .5 * s, 16), dk, { torn: .3, seed: 1769, ink: PAL.ink, sw: .08 * s, shadow: false });
    ctx.fillStyle = PAL.ink; for (const d2 of [-.2, .2]) { tracePath(ellPts(-1.3 * s + d2 * s, .3 * s, .1 * s, .16 * s, 8)); ctx.fill(); }
    if (o.happy) { ctx.lineWidth = .12 * s; ctx.strokeStyle = PAL.ink; ctx.beginPath(); ctx.arc(-.2 * s, -.4 * s, .25 * s, Math.PI * 1.1, Math.PI * 1.9); ctx.stroke(); ctx.beginPath(); ctx.arc(.6 * s, -.4 * s, .25 * s, Math.PI * 1.1, Math.PI * 1.9); ctx.stroke(); }
    else { tracePath(ellPts(-.2 * s, -.4 * s, .14 * s, .18 * s, 8)); ctx.fill(); tracePath(ellPts(.6 * s, -.4 * s, .14 * s, .18 * s, 8)); ctx.fill(); }
    ctx.restore();
    ctx.restore();
  }
  function slopThumb(x, y, s, rot, i) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot);
    const cols = [PAL.pink, PAL.sky, PAL.mint, PAL.yellow, PAL.purple, PAL.orange];
    scrap(rrPts(-1.6 * s, -1 * s, 3.2 * s, 2 * s, .25 * s), cols[i % 6], { torn: .4, seed: 1780 + i % 7, ink: PAL.ink, sw: .08 * s, shadow: [.1 * s, .12 * s] });
    // the "slop": a melty blob with too many eyes
    const blob = []; for (let j = 0; j < 12; j++) { const a = j / 12 * TAU; blob.push([Math.cos(a) * (.8 + hash2(i, j) * .4) * s, Math.sin(a) * (.55 + hash2(j, i) * .3) * s + (Math.sin(a) > 0 ? .2 * s : 0)]); }
    scrap(blob, mixCol(cols[(i + 2) % 6], PAL.ink, .15), { torn: .3, seed: 1790 + i % 5, shadow: false });
    ctx.fillStyle = PAL.white; for (let e = 0; e < 3; e++) { tracePath(ellPts((-.4 + e * .4) * s, -.15 * s + (e % 2) * .1 * s, .16 * s, .16 * s, 8)); ctx.fill(); }
    ctx.fillStyle = PAL.ink; for (let e = 0; e < 3; e++) { tracePath(ellPts((-.4 + e * .4) * s + .04 * s, -.12 * s + (e % 2) * .1 * s, .07 * s, .07 * s, 6)); ctx.fill(); }
    ctx.fillStyle = alpha(PAL.white, .85); tracePath([[1 * s, .4 * s], [1 * s, .9 * s], [1.4 * s, .65 * s]]); ctx.fill();
    ctx.restore();
  }
  line('V2', 14, (p, lt, d, t) => {
    slapIn(lt, .05, .012);
    fillBG('#C9A77C');
    for (let i = 0; i < 12; i++) { ctx.fillStyle = 'rgb(90 60 30 / .18)'; ctx.fillRect(-100, i * 64, W + 200, 5); }
    scrap(rectPts(-200, 760, W + 400, 500), '#7A5638', { torn: 3, seed: 1800, shadow: [0, -8] });
    halftone(rectPts(-200, 760, W + 400, 500), '#3A2415', { cell: 14, dot: .3, op: .4 });
    const b = lt / BL(), pb = pulse(t);
    // the phone, tipped over like a bucket
    const phx = 480, phy = 300, prot = 2.1 + Math.sin(t * 5) * .04;
    // stream of slop videos
    const mouth = [phx + Math.cos(prot - Math.PI / 2) * -180 + 40, phy + 180];
    for (let i = 0; i < 26; i++) {
      const u = frac(lt * 1.3 + i / 26), sp = (hash(i + 110) - .5);
      const x = lerp(mouth[0], 1060 + sp * 380, u) + Math.sin(u * 3) * 40, y = mouth[1] + u * u * 290 + sp * 30 * u;
      slopThumb(x, y, 34 + u * 10, (hash(i + 111) - .5) * 1.5 + u * sp * 3, i);
    }
    ctx.save(); ctx.translate(phx, phy); ctx.rotate(prot);
    scrap(rrPts(-150, -290, 300, 580, 40), PAL.ink, { torn: .8, seed: 1810, shadow: [12, 14] });
    scrap(rrPts(-130, -260, 260, 520, 16), PAL.white, { torn: .4, seed: 1811, shadow: false });
    ctx.save(); tracePath(rrPts(-130, -260, 260, 520, 16)); ctx.clip();
    for (let r = 0; r < 5; r++) for (let c = 0; c < 2; c++) {
      const yy = -250 + r * 130 - (lt * 300) % 130;
      slopThumb(-60 + c * 120, yy + 60, 34, 0, r * 2 + c + Math.floor(lt * 300 / 130) * 2);
    }
    ctx.restore();
    ctx.restore();
    // pigs + trough
    const ty = 900;
    pig(600, 940, 42, { dip: Math.abs(Math.sin(b * Math.PI * 2)) * .6, flip: true, happy: true });
    pig(1530, 940, 42, { dip: Math.abs(Math.sin(b * Math.PI * 2 + 1)) * .6, happy: true });
    scrap([[720, 760], [1400, 760], [1360, ty], [760, ty]], '#6B4A2A', { torn: 1.2, seed: 1820, ink: PAL.ink, sw: 5, shade: true, shadeOp: .3 });
    for (let i = 0; i < 7; i++) scrap(ellPts(780 + i * 95, 765 + Math.sin(t * 8 + i) * 6, 60, 30, 14), '#9AAE6A', { torn: 2, seed: 1821 + i, shadow: false });
    for (let i = 0; i < 6; i++) slopThumb(800 + i * 110, 750 + Math.sin(t * 6 + i) * 8, 30, (hash(i + 120) - .5) * .8, i + 3);
    txt('FEED', 1060, 840, 92, PAL.cream, { font: 'rammetto', stroke: PAL.ink, sw: 8 });
    // splashes
    for (let i = 0; i < 6; i++) { const ph = frac(lt * 2 + i / 6); scrap(ellPts(1060 + (i - 2.5) * 70 * (1 + ph), 740 - Math.sin(ph * Math.PI) * 120, 14, 18, 8), '#9AAE6A', { torn: .5, shadow: false, seed: 1830 + i, ink: PAL.ink, sw: 2 }); }
    sticker('SORA 2', 1280, 290, 150, PAL.sky, { pop: popK(lt, .08, .2), rot: .12, size: 64, font: 'bungee' });
    // likes rising
    for (let i = 0; i < 5; i++) { const ph = frac(lt * .9 + i / 5); txt('♥ ' + ['2.1M', '880K', '4M', '12M', '9.9M'][i], 1640 + Math.sin(ph * 5 + i) * 30, 720 - ph * 380, 56, PAL.red, { font: 'archivo', alpha: 1 - ph * ph, stroke: PAL.white, sw: 8 }); }
    camEnd();
  });

  // ======================================================================
  // V2.15 Yann LeCun quits Meta's stage — YANN walks off, mic dropped, pointing at "WORLD MODELS →".
  line('V2', 15, (p, lt, d, t) => {
    slapIn(lt, .05, -.012);
    camBegin(lerp(930, 1060, ease(p)), 575, 1.08);
    fillBG('#7A0F18');
    for (let i = 0; i < 16; i++) { const x = i * 130 - 40; ctx.fillStyle = i % 2 ? '#9E1824' : '#86121D'; tracePath([[x, -100], [x + 130, -100], [x + 130 + Math.sin(t * 2 + i) * 6, 800], [x + Math.sin(t * 2 + i + 1) * 6, 800]]); ctx.fill(); }
    halftone(rectPts(-100, -100, W + 200, 900), PAL.ink, { cell: 16, dot: .22, op: .3 });
    // stage floor
    scrap(rectPts(-200, 760, W + 400, 500), '#5B3A29', { torn: 1, seed: 1840, shadow: [0, -8] });
    ctx.fillStyle = 'rgb(0 0 0 / .2)'; for (let i = 0; i < 7; i++) ctx.fillRect(-200, 790 + i * 40, W + 400, 3);
    // marquee sign
    scrap(rrPts(420, 70, 640, 150, 20), '#2A1E14', { torn: 1, seed: 1841, ink: PAL.gold, sw: 6 });
    for (let i = 0; i < 18; i++) { const on = (Math.floor(t * 10) + i) % 3 !== 0; ctx.fillStyle = on ? PAL.yellow : '#6B5B2B'; const q = i < 9 ? [440 + i * 75, 86] : [440 + (i - 9) * 75, 204]; tracePath(ellPts(q[0], q[1], 9, 9, 8)); ctx.fill(); }
    txt('META', 740, 148, 96, PAL.white, { font: 'bungee' });
    // the "LLM" dead-end sign on the left
    marker([[190, 780], [190, 470]], '#8A8A96', 12, { rough: 0 });
    ctx.save(); ctx.translate(190, 430); ctx.rotate(Math.PI / 4);
    scrap(rectPts(-100, -100, 200, 200), PAL.yellow, { torn: 1, seed: 1842, ink: PAL.ink, sw: 6 });
    ctx.restore();
    txt('LLMs:', 190, 405, 38, PAL.ink, { font: 'archivo' }); txt('DEAD END', 190, 452, 34, PAL.ink, { font: 'archivo', maxW: 150 });
    // the WORLD MODELS exit sign
    const sk = popK(lt, .15, .2);
    marker([[1600, 780], [1600, 560]], '#8A8A96', 14, { rough: 0 });
    ctx.save(); ctx.translate(1580, 470); ctx.rotate(-.04); const ss = backOut(sk); ctx.scale(ss, ss);
    scrap(rrPts(-270, -90, 540, 180, 18), PAL.green, { torn: 1, seed: 1843, ink: PAL.white, sw: 7, shadow: [10, 12] });
    txt('WORLD MODELS', -20, -20, 64, PAL.white, { font: 'archivo', maxW: 420 });
    txt('→', 190, 44, 90, PAL.white, { font: 'archivo' });
    txt('EXIT', -120, 46, 40, PAL.white, { font: 'archivo' });
    ctx.restore();
    // YANN walking off
    const b = lt / BL(), s = 46, wx = lerp(760, 1180, ease(p)), gy = 880;
    // spotlight on him
    ctx.save(); ctx.globalCompositeOperation = 'screen'; ctx.fillStyle = 'rgb(255 248 231 / .18)'; tracePath([[wx - 40, -100], [wx + 40, -100], [wx + 220, gy], [wx - 220, gy]]); ctx.fill(); tracePath(ellPts(wx, gy, 230, 40, 24)); ctx.fill(); ctx.restore();
    // mic stand left behind, mic dropped
    micStand(700, 880, 24);
    const md = clamp(lt / .35), micX = lerp(760, 820, md), micY = md < 1 ? lerp(500, 870, md * md) : 870 - Math.abs(Math.sin((lt - .35) * 10)) * 40 * Math.exp(-(lt - .35) * 5);
    ctx.save(); ctx.translate(micX, micY); ctx.rotate(lt * 9);
    scrap(rectPts(-10, -10, 20, 70), PAL.ink, { torn: .4, shadow: false }); scrap(ellPts(0, -22, 20, 26, 12), '#8C8A92', { torn: .4, shadow: false, tone: { color: PAL.ink, cell: 5, dot: .3 } });
    ctx.restore();
    if (lt > .35 && lt < .7) popBurst(micX, 880, 80, (lt - .35) / .35, PAL.white, 'THNK');
    person(wx, gy, s, { name: 'YANN', top: 'jacket', topCol: '#22242E', hair: 'short', hairCol: '#6B6770', skin: SKINS[0], glasses: true, eyes: 'dot', mouth: 'smile', walk: b * .5, aR: .35 + Math.sin(t * 8) * .05, aL: -1.1 + Math.sin(b * Math.PI) * .2, pants: '#3B3F58', dy: -Math.abs(Math.sin(b * Math.PI)) * .08 });
    const [hx, hy] = handAt(wx, gy, s, 1, .35, -Math.abs(Math.sin(b * Math.PI)) * .08);
    // pointing finger
    marker([[hx, hy], [hx + 36, hy - 8]], SKINS[0], 14, { rough: 0 });
    camEnd();
    camEnd();
  });

  // ======================================================================
  // V2.16 "Bubble!" screams the business page — a clipping yells BUBBLE?!; a giant soap bubble of GPUs; a pin approaches…
  line('V2', 16, (p, lt, d, t) => {
    slapIn(lt, .05, .012);
    fillBG(PAL.newsprint);
    ctx.fillStyle = 'rgb(28 26 31 / .12)';
    for (let c = 0; c < 6; c++) for (let r = 0; r < 60; r++) ctx.fillRect(40 + c * 310, 40 + r * 17, 280 * (r % 7 === 6 ? .5 : 1), 6);
    toneBG(PAL.sky, 22, .2, .3);
    // the clipping, screaming
    const sc = 1 + pulse2(t, 8) * .03, jx = jit(5), jy = jit(5);
    ctx.save(); ctx.translate(430 + jx, 500 + jy); ctx.scale(sc, sc);
    clipping(0, 0, 720, 'BUBBLE?!', { size: 132, mast: 'The Business Page', date: 'NOVEMBER 2025', rot: -.06 });
    ctx.restore();
    for (let i = 0; i < 7; i++) { const a = -2.9 + i * .42, r0 = 400 + pulse2(t) * 30; marker([[430 + Math.cos(a) * r0, 470 + Math.sin(a) * r0 * .7], [430 + Math.cos(a) * (r0 + 80), 470 + Math.sin(a) * (r0 + 80) * .7]], PAL.red, 10, { rough: 1 }); }
    // the bubble
    const bx = 1130, by = 490, br = 290;
    const push = ease(p);
    const rx = br * (1 + Math.sin(t * 7) * .035 - push * .05), ry = br * (1 + Math.cos(t * 5.3) * .035 + push * .03);
    ctx.save(); ctx.beginPath(); ctx.ellipse(bx, by, rx, ry, 0, 0, TAU); ctx.clip();
    const g = ctx.createRadialGradient(bx - rx * .3, by - ry * .35, rx * .1, bx, by, rx * 1.02);
    g.addColorStop(0, 'rgb(255 255 255 / .35)'); g.addColorStop(.6, 'rgb(159 211 242 / .18)'); g.addColorStop(.85, 'rgb(255 79 163 / .22)'); g.addColorStop(1, 'rgb(168 230 207 / .6)');
    ctx.fillStyle = g; ctx.fillRect(bx - rx, by - ry, rx * 2, ry * 2);
    const things = [[-130, -120, 'g'], [120, -60, 'g'], [-60, 130, 'g'], [150, 150, '$'], [-200, 20, '$'], [30, -210, '$'], [10, 20, 'r']];
    things.forEach(([dx, dy, k], i) => {
      const ox = dx + Math.sin(t * 2 + i) * 18, oy = dy + Math.cos(t * 1.7 + i * 2) * 18;
      if (k === 'g') gpu(bx + ox, by + oy, 15, { rot: Math.sin(t + i) * .3, label: 'H100' });
      else if (k === '$') txt('$', bx + ox, by + oy, 130, PAL.green, { font: 'abril', stroke: PAL.ink, sw: 7, rot: Math.sin(t * 2 + i) * .3 });
      else rocket(bx + ox, by + oy, 14, { rot: .6, flame: .7, label: 'AI' });
    });
    ctx.restore();
    ctx.save();
    ctx.lineWidth = 16; ctx.strokeStyle = alpha(PAL.pink, .55); ctx.beginPath(); ctx.ellipse(bx, by, rx - 4, ry - 4, 0, 0, TAU); ctx.stroke();
    ctx.lineWidth = 9; ctx.strokeStyle = alpha(PAL.sky, .9); ctx.beginPath(); ctx.ellipse(bx, by, rx - 12, ry - 12, 0, .4, 3.4); ctx.stroke();
    ctx.lineWidth = 7; ctx.strokeStyle = alpha(PAL.mint, .9); ctx.beginPath(); ctx.ellipse(bx, by, rx - 18, ry - 18, 0, 3.4, 5.9); ctx.stroke();
    ctx.lineWidth = 5; ctx.strokeStyle = PAL.ink; ctx.beginPath(); ctx.ellipse(bx, by, rx + 4, ry + 4, 0, 0, TAU); ctx.stroke();
    ctx.fillStyle = alpha(PAL.white, .85); tracePath(ellPts(bx - rx * .48, by - ry * .56, rx * .2, ry * .08, 16, -.6)); ctx.fill();
    tracePath(ellPts(bx - rx * .7, by - ry * .28, rx * .05, ry * .05, 10)); ctx.fill();
    ctx.restore();
    // a pin creeps in from the lower right, aimed at the bubble's skin — cut before it lands
    const ang = .3, ux = Math.cos(ang), uy = Math.sin(ang);
    const edge = [bx + ux * (rx + 4), by + uy * (ry + 4)], gap = lerp(190, 8, easeOut(clamp(lt / (d * .95)))) + Math.sin(t * 40) * 2;
    const tip = [edge[0] + ux * gap, edge[1] + uy * gap];
    ctx.save(); ctx.translate(tip[0], tip[1]); ctx.rotate(ang);
    scrap([[0, 0], [30, -7], [230, -7], [230, 7], [30, 7]], '#B5BCCB', { torn: .3, seed: 1851, ink: PAL.ink, sw: 3, shadow: [6, 8] });
    marker([[40, -2], [220, -2]], PAL.white, 3, { rough: 0, alpha: .8 });
    scrap(ellPts(272, 0, 56, 56, 22), PAL.red, { torn: .6, seed: 1850, ink: PAL.ink, sw: 5, shade: true, shadeOp: .35 });
    ctx.fillStyle = alpha(PAL.white, .7); tracePath(ellPts(254, -20, 15, 9, 10, -.5)); ctx.fill();
    ctx.restore();
    // stock ticker along the foot of the page
    ctx.fillStyle = PAL.ink; ctx.fillRect(-100, 850, W + 200, 76);
    const tick = [['NVDA', '▲ 4.2%', PAL.green], ['AI', '▲▲▲', PAL.green], ['ORCL', '▲ 36%', PAL.green], ['BUBBLE?', '▼', PAL.red], ['GPU', '▲ SOLD OUT', PAL.green], ['VIBES', '▲ 900%', PAL.green]];
    let tx0 = 40 - (lt * 420) % 1400;
    for (let k = 0; k < 3; k++) for (const [a1, a2, c] of tick) { txt(a1, tx0, 890, 40, PAL.white, { font: 'archivo', align: 'left' }); tx0 += textW(a1, 40, 'archivo') + 16; txt(a2, tx0, 890, 40, c === PAL.green ? '#6CF2B0' : '#FF6B5A', { font: 'archivo', align: 'left' }); tx0 += textW(a2, 40, 'archivo') + 60; }
    // the gear inside sweats; tension marks
    if (lt > .3) for (let i = 0; i < 3; i++) txt('!', edge[0] + 30 + i * 46, edge[1] - 110 - i * 26, 80, PAL.red, { font: 'anton', alpha: clamp((lt - .3) * 4 - i * .4), rot: .2 });
    camEnd();
  });

  // =====================================================================================================================
  // The vertical video (1080 × 1920): each line re-composed for the tall frame, with its horizontal shot's gag, props and palette:
  // the subject big in the safe area (y 250–1250), the caption tape at y ≈ 1290–1480, seas, floors, desks and crowds in the bottom
  // ≈ 420. Vertical motion where the line has some to give: the whale breaches up through the tag and NVDA's line dives down into
  // the sea, the cables fire down the shelf, a researcher is reeled up out of the sea, the boxes drop onto the stack, the medals drop
  // from the flies, the heart's halves fall, the #1 bar shoots up, the book drops, the insults rain down, the slop pours down into
  // the trough, the pin comes down at the bubble.
  // =====================================================================================================================

  // The vertical shots' camera: the paper-slap settle (as slapIn()) round a slow push through the line. Pair with camEnd().
  const venter = (lt, p, cx = W / 2, cy = H / 2, push = .04, rot = .012) => {
    const k = easeOut(clamp(lt / .13));
    camBegin(cx, cy, (1 + push * ease(p)) * (1 + .06 * (1 - k)), rot * (1 - k));
  };
  // lt of the k-th beat at/after the window start (many of these lines start on an off-beat pickup).
  const beatLt = (t, lt, k) => { const s = t - lt; return onBeat(0, Math.ceil(bpOf(s) - .02) + k) - s; };
  const glowV = (x, y, r, col, a = .6) => {
    const g = ctx.createRadialGradient(x, y, 0, x, y, r);
    g.addColorStop(0, alpha(col, a)); g.addColorStop(1, alpha(col, 0));
    ctx.fillStyle = g; ctx.fillRect(x - r, y - r, r * 2, r * 2);
  };
  const dot2 = (x, y, r, col) => { ctx.fillStyle = col; tracePath(ellPts(x, y, r, r, 12)); ctx.fill(); };
  // A wavy band of sea from y down past the frame's foot.
  const seaV = (t, yy, col, ph, amp, seed, o = {}) => {
    const pts = [[-80, H + 80]];
    for (let i = 0; i <= 16; i++) pts.push([i * 76 - 70, yy + Math.sin(i * .9 + t * 6 + ph) * amp]);
    pts.push([W + 80, H + 80]);
    scrap(pts, col, { torn: 2, shadow: false, seed, ...o });
  };

  // ---------- V2.1 (vertical): the whale breaches up through the tag; NVDA's line dives down the frame into the sea ----------
  vshot('V2.1', (p, lt, d, t) => {
    const hit = .26, crash = .95, dive = .3, splashT = crash + dive, SEA = 1580;
    const shk = lt > hit && lt < hit + .25 ? shakeXY(t, 14 * (1 - (lt - hit) / .25)) : [0, 0];
    const shk2 = lt > splashT && lt < splashT + .25 ? shakeXY(t + 1, 10 * (1 - (lt - splashT) / .25)) : [0, 0];
    fillBG('#D42F24');
    raysBG(540, 650, 22, '#E8412F', lt * .15);
    toneBG('#8E1B14', 24, .2, .35);
    venter(lt, p, 540 - shk[0] - shk2[0], 960 - shk[1] - shk2[1], .03);
    lantern(130, 0, 54, Math.sin(t * 5) * .08);
    lantern(950, 20, 40, Math.sin(t * 5 + 1) * .1);
    // NVDA, climbing all year
    const cx = 170, cy = 960, cw = 430, ch = 230;
    chart(cx, cy, cw, ch, { k: 0, col: 'rgb(0 0 0 / 0)', label: 'NVDA', labelSize: 54, grid: true });
    const f = u => .45 + .5 * u + Math.sin(u * 30) * .03;
    const upPts = []; for (let i = 0; i <= 30; i++) { const u = i / 30 * .72; upPts.push([cx + u * cw, cy + ch - f(u) * ch]); }
    marker(upPts, '#1A9E55', 11, { rough: 1.2, smooth: true });
    seaV(t, SEA - 26, '#2C4FB8', 2.1, 12, 1461);
    // the whale: up out of the sea, through the tag, to a hover where the tag hung
    const P0 = [380, 2300], P1 = [520, 900], P2 = [560, 610];
    const u = 1 - (1 - clamp(lt / .6)) ** 2, iu = 1 - u;
    let wx = iu * iu * P0[0] + 2 * iu * u * P1[0] + u * u * P2[0], wy = iu * iu * P0[1] + 2 * iu * u * P1[1] + u * u * P2[1];
    const dx = 2 * iu * (P1[0] - P0[0]) + 2 * u * (P2[0] - P1[0]), dy = 2 * iu * (P1[1] - P0[1]) + 2 * u * (P2[1] - P1[1]);
    let wrot = Math.atan2(dy, dx);
    if (lt > .6) { wy += Math.sin((lt - .6) * 6) * 14; wrot += Math.sin((lt - .6) * 5) * .06; }
    const WS = 52;
    // the price tag (the horizontal one, in its own coordinates round (640, 420), scaled up round the frame's middle)
    const TX = 540, TY = 650, TS = 1.12, tw = 740, th = 330, tagX = 640, tagY = 420;
    const tk = clamp((lt - hit) / 1.1);
    const toTag = (x, y) => [TX + (x - tagX) * TS, TY + (y - tagY) * TS];
    const lOff = lt > hit ? easeOut(tk) * 160 + (lt - hit) * 60 : 0, lFall = lt > hit ? (lt - hit) ** 2 * 1250 : 0;
    if (lt < hit + .5) marker([toTag(tagX - tw / 2 + th * .3 - lOff, tagY + lFall), [150, -60]], PAL.ink, 4, { rough: 1 });
    const inTag = fn => { ctx.save(); ctx.translate(TX, TY); ctx.scale(TS, TS); ctx.translate(-tagX, -tagY); fn(); ctx.restore(); };
    const drawHalf = side => {
      const age = lt - hit, off = easeOut(tk) * (side < 0 ? 160 : 180) + age * 60, fall = age * age * (side < 0 ? 1250 : 1450), rot = side * (easeOut(tk) * .32 + age * .5);
      ctx.save(); ctx.translate(tagX + side * off, tagY + fall); ctx.rotate(-.06 + rot);
      ctx.beginPath();
      const zz = []; for (let i = 0; i <= 8; i++) zz.push([60 + (i % 2 ? 26 : -26), -th / 2 - 20 + i * (th + 40) / 8]);
      ctx.moveTo(side * 800, -400); zz.forEach(([a, b]) => ctx.lineTo(a, b)); ctx.lineTo(side * 800, 400);
      ctx.closePath(); ctx.clip();
      priceTagBody(tw, th);
      ctx.restore();
    };
    // the wake streaming off the whale as it rises
    const ux = Math.cos(wrot), uy = Math.sin(wrot);
    const wake = () => { if (lt < .7) for (let i = 0; i < 4; i++) { const o = (i - 1.5) * 70, b0 = 300 + i * 25; marker([[wx - ux * b0 - uy * o, wy - uy * b0 + ux * o], [wx - ux * (b0 + 190) - uy * o, wy - uy * (b0 + 190) + ux * o]], PAL.white, 8, { rough: 1, alpha: .8 * (1 - clamp((lt - .4) / .3)) }); } };
    if (lt < hit) {
      wake();
      whale(wx, wy, WS, { rot: wrot, tail: Math.sin(t * 14) * .25 });
      inTag(() => {
        const bulge = 1 + clamp((lt - .1) / (hit - .1)) * .07;
        ctx.save(); ctx.translate(tagX + jit(2 + 6 * lt / hit), tagY + jit(2 + 6 * lt / hit)); ctx.rotate(-.06 + Math.sin(lt * 60) * .02 * (lt / hit)); ctx.scale(bulge, bulge); priceTagBody(tw, th); ctx.restore();
        if (lt > .1) for (let i = 0; i < 5; i++) { const a = .6 + i * .5; marker([[tagX + 60 + Math.cos(a) * 60, tagY + 60 + Math.sin(a) * 40], [tagX + 60 + Math.cos(a) * 110, tagY + 60 + Math.sin(a) * 75]], PAL.ink, 5, { rough: 1.5 }); }
      });
    } else {
      inTag(() => {
        drawHalf(-1); drawHalf(1);
        for (let i = 0; i < 16; i++) {
          const a = hash(i + 40) * TAU, v = 300 + hash(i + 41) * 500, age = lt - hit;
          const sx = tagX + 60 + Math.cos(a) * v * age, sy = tagY + Math.sin(a) * v * age + 500 * age * age;
          card(sx, sy, 34, 22, i % 2 ? PAL.yellow : PAL.white, a + age * 9, { torn: 1, shadow: false, seed: 1470 + i });
        }
      });
      wake();
      whale(wx, wy, WS, { rot: wrot, tail: Math.sin(t * 14) * .25, blush: true });
      const sp = clamp((lt - hit - .15) / .3) * (1 + pulse(t) * .25);
      if (sp > 0) {
        const bhx = wx + Math.cos(wrot) * 1.6 * WS + Math.sin(wrot) * 2.3 * WS, bhy = wy + Math.sin(wrot) * 1.6 * WS - Math.cos(wrot) * 2.3 * WS;
        for (let i = 0; i < 7; i++) { const a = -Math.PI / 2 + (i - 3) * .28, r = sp * (1.4 + hash(i + 3) * 1.4) * WS; scrap(ellPts(bhx + Math.cos(a) * r, bhy + Math.sin(a) * r, .32 * WS, .42 * WS, 10), PAL.sky, { torn: .2, seed: 1436 + i, shadow: false, ink: PAL.ink, sw: .05 * WS }); }
      }
      if (lt < hit + .25) popBurst(TX + 20, TY - 40, 180, (lt - hit) / .25, PAL.white, 'RIP!');
    }
    // the spray where it left the sea
    if (lt < .6) for (let i = 0; i < 10; i++) {
      const a = -Math.PI / 2 + (hash(i + 1490) - .5) * 1.6, v = 500 + hash(i + 1491) * 600, age = lt - .02;
      if (age < 0) continue;
      scrap(ellPts(420 + Math.cos(a) * v * age, SEA - 10 + Math.sin(a) * v * age + 1400 * age * age, 14, 20, 8), PAL.white, { torn: .4, shadow: false, ink: PAL.ink, sw: 2, seed: 1495 + i, op: 1 - age / .6 });
    }
    // …then the crash: NVDA's line dives down the frame into the sea
    const [x0, y0] = upPts.at(-1), divePts = [[x0, y0]];
    for (let i = 1; i <= 9; i++) { const k = i / 9; divePts.push([x0 + k * 250 + (i % 2 ? 22 : -10), lerp(y0, SEA + 60, k ** 1.4) - (i % 2 && i < 9 ? 34 : 0)]); }
    const dk = clamp((lt - crash) / dive);
    if (dk > 0) {
      const P = partial(divePts, easeIn(dk)); marker(P, PAL.red, 15, { rough: 1.5 });
      const [ex, ey] = P.at(-1); if (dk < 1) scrap(ellPts(ex, ey, 14, 14, 10), PAL.red, { torn: .5, shadow: false, ink: PAL.ink, sw: 3 });
    }
    seaV(t, SEA, '#2C4FB8', 0, 14, 1460, { shadow: [0, -6], shadowCol: 'rgb(0 0 0 / .18)' });
    halftone(rectPts(-80, SEA + 30, W + 160, 400), '#153E80', { cell: 16, dot: .25, op: .45 });
    if (lt > splashT && lt < splashT + .5) {
      const age = (lt - splashT) / .5, sx = divePts.at(-1)[0];
      for (let j = 0; j < 9; j++) { const a = -Math.PI / 2 + (j - 4) * .3; scrap(ellPts(sx + Math.cos(a) * age * 160, SEA + Math.sin(a) * age * 260 + age * age * 240, 14, 20, 8), PAL.white, { torn: .5, shadow: false, seed: 1600 + j, ink: PAL.ink, sw: 2, op: 1 - age }); }
    }
    // firecrackers on the eighths after the hit
    const PX = [150, 910, 170, 930, 330, 880, 140, 760], PY = [860, 560, 470, 860, 1200, 1210, 1130, 470];
    for (let i = 0; i < 8; i++) { const t0 = hit + i * BL() / 2, age = (lt - t0) / .32; popBurst(PX[i], PY[i], 70 + hash(i) * 30, age, i % 2 ? PAL.yellow : PAL.gold, i % 3 === 0 ? 'POP!' : i % 3 === 1 ? 'BANG' : null); }
    sticker('NVDA\n−17%', 840, 1060, 125, PAL.yellow, { pop: popK(lt, crash + .3, .2), rot: .15, size: 58 });
    camEnd();
  });

  // ---------- V2.2 (vertical): the gate up top with the half-trillion across it; TRUMP big at the STARGATE podium below ----------
  vshot('V2.2', (p, lt, d, t) => {
    fillBG('#141233');
    toneBG('#3B3480', 26, .18, .6);
    venter(lt, p, 540, 960, .04, -.012);
    for (let i = 0; i < 46; i++) { const x = hash(i + 50) * W, y = hash(i + 51) * 1250, r = 2 + hash(i + 52) * 4 * (.6 + .4 * Math.sin(t * 6 + i)); ctx.fillStyle = PAL.cream; tracePath(starPts(x, y, r * 2, .35, 4, 0)); ctx.fill(); }
    const cx = 540, cy = 662, R = 280;
    // event horizon (kawoosh at the start)
    const kaw = lt < .4 ? Math.sin(lt / .4 * Math.PI) : 0;
    ctx.save();
    ctx.fillStyle = '#1FA6A0'; tracePath(ellPts(cx, cy, R * .86, R * .86, 48)); ctx.fill();
    ctx.beginPath(); ctx.arc(cx, cy, R * .86, 0, TAU); ctx.clip();
    for (let i = 0; i < 7; i++) {
      const rr = frac(i / 7 + lt * .7) * R * .9;
      ctx.strokeStyle = i % 2 ? alpha(PAL.sky, .8) : alpha(PAL.mint, .7); ctx.lineWidth = 16 + i * 2;
      ctx.beginPath(); ctx.ellipse(cx + Math.sin(t * 3 + i) * 10, cy + Math.cos(t * 2.4 + i) * 8, rr, rr * .96, 0, 0, TAU); ctx.stroke();
    }
    halftone(ellPts(cx, cy, R, R, 40), '#0E5E6E', { cell: 12, dot: .3, op: .45 });
    ctx.fillStyle = alpha(PAL.white, .5); tracePath(ellPts(cx, cy, R * .3 + kaw * 60, R * .3 + kaw * 60, 30)); ctx.fill();
    ctx.restore();
    if (kaw > 0) scrap(ellPts(cx, cy + 30, R * (.9 + kaw * .5), R * (.8 + kaw * .45), 36), alpha(PAL.sky, .7), { torn: 8, shadow: false, seed: 1480 });
    // bills spiralling into the gate
    for (let i = 0; i < 16; i++) {
      const ph = frac(lt * .75 + hash(i + 60)), a = hash(i + 61) * TAU + ph * 4, r = lerp(1100, 20, ph ** .8);
      cash(cx + Math.cos(a) * r * .8, cy + Math.sin(a) * r * 1.05, 46 * (1 - ph * .8), a + ph * 6);
    }
    // the ring
    ctx.save();
    ctx.strokeStyle = 'rgb(0 0 0 / .35)'; ctx.lineWidth = R * .2; ctx.beginPath(); ctx.arc(cx + 10, cy + 14, R * .93, 0, TAU); ctx.stroke();
    ctx.strokeStyle = '#8D93A3'; ctx.beginPath(); ctx.arc(cx, cy, R * .93, 0, TAU); ctx.stroke();
    ctx.strokeStyle = '#6B7080'; ctx.lineWidth = R * .07; ctx.beginPath(); ctx.arc(cx, cy, R * .93, 0, TAU); ctx.stroke();
    ctx.strokeStyle = PAL.ink; ctx.lineWidth = 5;
    for (const rr of [R * .83, R * 1.03]) { ctx.beginPath(); ctx.arc(cx, cy, rr, 0, TAU); ctx.stroke(); }
    const spin = lt * 1.6;
    for (let i = 0; i < 39; i++) { const a = spin + i / 39 * TAU; txt('◇△○▽□◁'[i % 6], cx + Math.cos(a) * R * .93, cy + Math.sin(a) * R * .93, 22, '#C9CED9', { font: 'archivo', rot: a + Math.PI / 2 }); }
    ctx.restore();
    // chevrons lock in on the eighths
    for (let i = 0; i < 9; i++) {
      const a = -Math.PI / 2 + i / 9 * TAU, lit = lt > i * BL() / 2 * .8;
      ctx.save(); ctx.translate(cx + Math.cos(a) * R, cy + Math.sin(a) * R); ctx.rotate(a + Math.PI / 2);
      scrap([[-34, -24], [34, -24], [16, 26], [-16, 26]], lit ? PAL.orange : '#5A5E6A', { torn: .8, seed: 1490 + i, ink: PAL.ink, sw: 4 });
      if (lit) { ctx.fillStyle = alpha(PAL.yellow, .5 + .5 * pulse2(t + i * .05)); tracePath([[-18, -14], [18, -14], [8, 14], [-8, 14]]); ctx.fill(); }
      ctx.restore();
    }
    // the half-trillion, on two lines across the gate
    ransom('$500,000,', cx - 10, cy - 66, 112, { pop: clamp(lt / .26), maxW: 940, seed: 5005, jolt: 3, fonts: LOUD_FONTS });
    ransom('000,000', cx + 20, cy + 72, 112, { pop: clamp((lt - .08) / .26), maxW: 940, seed: 5011, jolt: 3, fonts: LOUD_FONTS });
    // the stage
    scrap(rectPts(-100, 1215, W + 200, 900), '#26215A', { torn: 1, seed: 1498, shadow: [0, -8] });
    halftone(rectPts(-100, 1215, W + 200, 900), '#0A0820', { cell: 14, dot: .3, op: .45 });
    // the three backers, upstage, cheering…
    const gyB = 1268, sB = 37, b = lt / BL(), pb = pulse(t);
    const backers = [
      { x: 135, name: 'MASA', hair: 'bald', skin: SKINS[4], tie: PAL.blue, topCol: '#3A3F58' },
      { x: 290, name: 'LARRY', hair: 'side', skin: SKINS[0], tie: PAL.red, topCol: '#4A4A55', hairCol: '#CFC8BD' },
      { x: 905, name: 'SAM', hair: 'short', skin: SKINS[0], topCol: '#2B2E3A', hairCol: '#5A4030', sam: true },
    ];
    backers.forEach((q, i) => {
      const clap = Math.abs(Math.sin((b + i * .3) * Math.PI));
      person(q.x, gyB, sB, {
        name: q.name, hair: q.hair, skin: q.skin, top: 'suit', topCol: q.topCol, tie: q.tie, hairCol: q.hairCol, pants: '#22242E',
        aL: q.sam ? .9 + pb * .5 : -.2 + clap * .9, aR: q.sam ? .9 + pb * .5 : -.2 + clap * .9, mouth: q.sam ? 'grin' : 'O', eyes: q.sam ? 'happy' : 'wide', dy: -pb * (q.sam ? .25 : .1),
      });
    });
    // …and TRUMP at the lectern, big, talking, one hand on the lectern and the other thrown up on the beat
    const tx = 540, gy = 1560, ts = 66, jab = pulse(t, 5);
    person(tx, gy, ts, { ...TRUMP, eyes: 'dot', mouth: frac(b * 2) < .5 ? 'O' : 'grin', aL: -1.25, aR: .75 + jab * .35, pants: '#22242E', seed: 382 });
    trumpHair(tx, gy, ts);
    longTie(tx, gy, ts);
    scrap([[395, 1215], [685, 1215], [665, 1720], [415, 1720]], '#7A5230', { torn: 1.2, seed: 1495, shade: true, shadeOp: .3 });
    scrap(rectPts(383, 1200, 314, 28), '#5A3A20', { torn: .6, seed: 1497, shadow: false });
    txt('STARGATE', 540, 1262, 50, PAL.gold, { font: 'bungee', maxW: 262 });
    marker([[468, 1205], [490, 1112]], '#555', 7, { rough: 0 }); scrap(ellPts(493, 1100, 16, 20, 10), '#333', { torn: .3, shadow: false });
    helloTag('DONALD', tx + .75 * ts, gy - 6.9 * ts, .34 * ts, .05);
    camEnd();
    captionStyle({ color: PAL.teal });
  });

  // ---------- V2.3 (vertical): the Allow? dialogs cascade down the frame, all ACCEPTED; the vibe coder slams the button below ----------
  vshot('V2.3', (p, lt, d, t) => {
    fillBG(PAL.yellow);
    raysBG(540, 700, 18, '#FFE36E', -lt * .2);
    toneBG(PAL.pink, 20, .2, .35);
    venter(lt, p, 540, 960, .03, -.012);
    const f = frac(bpOf(t)), pb = pulse(t);
    // the dialogs nobody reads, one more on every beat
    const asks = ['Edit 47 files?', 'Delete the tests?', 'Push to prod?', 'rm -rf ~/ ?', 'Email your boss?'];
    const lands = [-.06, ...[0, 1, 2, 3].map(k => beatLt(t, lt, k))];
    const DW = 600, DH = 140;
    lands.forEach((tl, i) => {
      const k = popK(lt, tl, .12); if (k <= 0) return;
      const x0 = 62 + i * 30, y0 = 390 + i * 120;
      ctx.save(); ctx.translate(x0 + DW / 2, y0 + DH / 2); ctx.rotate((hash(i + 70) - .5) * .06); const sc = backOut(k); ctx.scale(sc, sc);
      scrap(rectPts(-DW / 2, -DH / 2, DW, DH), PAL.white, { torn: 1, seed: 1500 + i, ink: PAL.ink, sw: 4 });
      ctx.fillStyle = PAL.blue; ctx.fillRect(-DW / 2 + 2, -DH / 2 + 2, DW - 4, 34);
      txt('Allow?', -DW / 2 + 22, -DH / 2 + 19, 26, PAL.white, { font: 'archivo', align: 'left' });
      txt(asks[i], -DW / 2 + 24, 8, 44, PAL.ink, { font: 'code', align: 'left', maxW: 380 });
      ctx.restore();
      stamp('ACCEPTED', x0 + DW - 92, y0 + 76, 30, PAL.green, -.15 + hash(i) * .1, { pop: popK(lt, tl + .06, .12) });
    });
    // the coder, eyes shut, headphones on, behind the desk: the arm slams down on every beat
    const s = 76, px = 460, gy = 1766;
    const up = .95, down = .2;
    const aR = f < .12 ? down : f < .7 ? lerp(down, up, easeOut((f - .12) / .58)) : lerp(up, down, easeIn((f - .7) / .3));
    const press = f < .15 ? 1 - f / .15 : 0;
    const dyP = -.05 * pb;
    person(px, gy, s, { top: 'hoodie', topCol: PAL.teal, hair: 'curly', hairCol: '#3A2A20', skin: SKINS[2], eyes: 'closed', mouth: 'grin', aR, aL: -.35 + Math.sin(bpOf(t) * Math.PI) * .12, dy: dyP, blush: true });
    const [hx, hy] = headAt(px, gy, s, dyP);
    headphones(hx, hy, s, PAL.pink);
    for (let i = 0; i < 4; i++) { const ph = frac(lt * .9 + i / 4); txt(i % 2 ? '♪' : '♫', hx - 150 - ph * 120 + Math.sin(ph * 9 + i) * 20, hy - 30 - ph * 160, 64, PAL.ink, { font: 'archivo', alpha: 1 - ph }); }
    // the desk
    const DY = 1238;
    scrap([[-60, DY], [W + 60, DY], [W + 60, 1990], [-60, 1990]], '#8A5A3B', { torn: 1.5, seed: 1510, shade: true, shadeOp: .3 });
    scrap(rectPts(-60, DY - 18, W + 120, 36), '#A8744C', { torn: 1, seed: 1511 });
    laptop(175, DY - 10, 25, { lines: Array.from({ length: 6 }, (_, i) => ['+ vibes = true', '- test_all()', '+ retry(forever)', '+ ship_it()', '- // safety check', '+ yolo = true'][(i + Math.floor(lt * 14)) % 6]), textCol: '#6CF2B0' });
    // ACCEPT ALL, right under the slapping hand
    const [bx] = handAt(px, gy, s, 1, down, dyP), by = DY - 14;
    scrap(rectPts(bx - 150, by - 8, 300, 72), '#2A2A33', { torn: 1, seed: 1512, shadow: [8, 10] });
    txt('ACCEPT ALL', bx, by + 28, 40, PAL.yellow, { font: 'archivo', maxW: 270 });
    const dome = ellPts(bx, by - 6, 112, 66 * (1 - press * .45), 36).filter(q => q[1] <= by - 6);
    scrap(dome, PAL.red, { torn: 1, seed: 1513, ink: PAL.ink, sw: 4, shade: '#8E1B14', shadeOp: .4 });
    ctx.fillStyle = alpha(PAL.white, .55); tracePath(ellPts(bx - 40, by - 42 * (1 - press * .45), 32, 11, 12, -.3)); ctx.fill();
    const [hx2, hy2] = handAt(px, gy, s, 1, aR, dyP);
    scrap(ellPts(hx2, hy2, .6 * s, .5 * s, 16), SKINS[2], { torn: .5, seed: 1514, ink: PAL.ink, sw: 3, shadow: false });
    if (f < .3 && lt > .15) popBurst(bx + 110, by - 120, 95, f / .3, PAL.white, 'CLICK');
    // green ticks spraying up from the button
    for (let i = 0; i < 6; i++) {
      const bn = beatN(t), t0 = onBeat(0, bn) + (i % 3) * .03, age = (t - t0) / .6;
      if (age < 0 || age > 1 || t0 < t - lt) continue;
      const a = -Math.PI / 2 + (hash2(bn, i) - .5) * 2, v = 360 + hash2(i, bn) * 300;
      ctx.save(); ctx.globalAlpha *= 1 - age * age; checkBadge(bx + Math.cos(a) * v * age, by - 80 + Math.sin(a) * v * age + 300 * age * age, 30, age * 6); ctx.restore();
    }
    sticker(`+${(1200 + Math.floor(lt * 5400)).toLocaleString('en-US')}\nLINES`, 870, 1000, 100, PAL.mint, { pop: popK(lt, .1, .2), rot: .12, size: 42 });
    camEnd();
  });

  // ---------- V2.4 (vertical): the MCP hub up top fires a cable down into everything on the shelf, top to bottom… the sink ----------
  vshot('V2.4', (p, lt, d, t) => {
    fillBG(PAL.teal);
    toneBG('#0D6B67', 20, .24, .45);
    venter(lt, p, 540, 960, .04, .012);
    const hubX = 245, hubY = 375;
    // the shelves: two rows of appliances, and the kitchen sink on the floor
    const WOOD = '#8A5A3B';
    scrap(rectPts(60, 520, 960, 830), '#0D7A75', { torn: 1, seed: 1586, shadow: [10, 12] });
    halftone(rectPts(60, 520, 960, 830), '#06504C', { cell: 14, dot: .3, op: .4 });
    for (const x of [50, 1000]) scrap(rectPts(x, 500, 30, 860), WOOD, { torn: .6, seed: 1587 + x, shadow: [6, 8] });
    scrap(rectPts(40, 488, 1000, 30), WOOD, { torn: .6, seed: 1589 });
    scrap(rectPts(40, 760, 1000, 28), WOOD, { torn: .6, seed: 1590, shade: true, shadeOp: .2 });
    scrap(rectPts(40, 1050, 380, 28), WOOD, { torn: .6, seed: 1591, shade: true, shadeOp: .2 });
    scrap(rectPts(660, 1050, 380, 28), WOOD, { torn: .6, seed: 1592, shade: true, shadeOp: .2 });
    scrap(rectPts(-60, 1330, W + 120, 700), '#0A4F4B', { torn: 1, seed: 1593, shadow: [0, -6] });
    const items = [
      { x: 255, y: 760, fn: toaster, s: 36, sock: [2.83, -5.26] },
      { x: 815, y: 760, fn: calendar, s: 34, sock: [0, -7.1] },
      { x: 235, y: 1050, fn: database, s: 36, sock: [0, -7.5] },
      { x: 845, y: 1050, fn: null, s: 30, sock: [0, -6.9] },
      { x: 540, y: 1330, fn: sink, s: 46, sock: [.45, -7.7] },
    ];
    const arrive = i => .02 + i * .16;
    // the cables, fired from the hub down to each in turn (behind the shelves' contents)
    items.forEach((it, i) => {
      const ta = arrive(i), k = clamp((lt - ta) / .12);
      if (k <= 0) return;
      const ex = it.x + it.sock[0] * it.s, ey = it.y + it.sock[1] * it.s, sx = hubX - 147 + i * 74, sy = hubY + 70;
      const qx = (sx + ex) / 2 + (i - 2) * 50, qy = (sy + ey) / 2 + 60;
      const pts = []; for (let j = 0; j <= 24; j++) { const u = j / 24; pts.push([(1 - u) ** 2 * sx + 2 * (1 - u) * u * qx + u * u * ex, (1 - u) ** 2 * sy + 2 * (1 - u) * u * qy + u * u * (ey - 62)]); }
      const P = partial(pts, easeOut(k));
      marker(P, PAL.ink, 18, { rough: 0 }); marker(P, PAL.clawd, 10, { rough: 0 });
      const [tx, ty] = P.at(-1);
      ctx.save(); ctx.translate(tx, ty);
      scrap(rrPts(-32, -10, 64, 52, 10), PAL.ink, { torn: .5, seed: 1570 + i });
      txt('MCP', 0, 16, 22, PAL.white, { font: 'archivo' });
      ctx.fillStyle = '#C9CED9'; ctx.fillRect(-18, 42, 9, 20); ctx.fillRect(9, 42, 9, 20);
      ctx.restore();
    });
    items.forEach((it, i) => {
      const ta = arrive(i), on = lt > ta + .12 ? lt - ta - .12 : 0;
      const dy = on ? -Math.abs(Math.sin(on * 14)) * 16 * Math.exp(-on * 3) : 0;
      ctx.save(); ctx.translate(0, dy);
      if (it.fn) it.fn(it.x, it.y, it.s, on, t);
      else {
        ctx.save(); if (on) ctx.translate(jit(3), jit(3)); amp(it.x, it.y, it.s, { label: 'MCP' }); ctx.restore();
        if (on) for (let j = 0; j < 3; j++) { const ph = frac(lt * 1.5 + j / 3); txt(j % 2 ? '♪' : '♫', it.x - 40 - ph * 90, it.y - 230 - ph * 150, 64, PAL.yellow, { font: 'archivo', alpha: 1 - ph, stroke: PAL.ink, sw: 6 }); }
      }
      ctx.restore();
      checkBadge(it.x - 3 * it.s, it.y - 30, 34, (on - .05) / .15);
      const ex = it.x + it.sock[0] * it.s, ey = it.y + it.sock[1] * it.s, ok = lt - ta - .12;
      if (ok > 0 && ok < .25) popBurst(ex, ey - 10, 80, ok / .25, PAL.yellow);
    });
    // the hub, its own cord running up out of the frame
    marker([[hubX, -40], [hubX, hubY - 60]], PAL.ink, 20, { rough: 0 }); marker([[hubX, -40], [hubX, hubY - 60]], PAL.clawd, 11, { rough: 0 });
    scrap(rrPts(hubX - 185, hubY - 78, 370, 156, 30), PAL.white, { torn: 1.2, seed: 1580, ink: PAL.ink, sw: 6, shadow: [10, 12] });
    for (let i = 0; i < 5; i++) { ctx.fillStyle = PAL.ink; ctx.fillRect(hubX - 160 + i * 74, hubY + 46, 26, 16); }
    txt('MCP', hubX, hubY - 12, 104, PAL.ink, { font: 'bungee' });
    // Clawd on top of the hub, cheering each connection
    clawd(hubX + 130, hubY - 78, 10, { eyes: 'happy', mouth: 'grin', aL: .9 + pulse2(t) * .4, aR: .9 + pulse2(t + .1) * .4, dy: -pulse2(t) * .5 });
    camEnd();
  });

  // ---------- V2.5 (vertical): Zuck on the pier up top; a researcher clinging to the $100M bag is reeled up out of the sea ----------
  vshot('V2.5', (p, lt, d, t) => {
    const SEA = 880, pb = pulse(t), b = lt / BL();
    fillBG('#FFC857');
    raysBG(770, SEA, 20, '#FFB43A', lt * .1);
    venter(lt, p, 540, 960, .03, -.012);
    // the setting sun on the horizon
    scrap(ellPts(770, SEA - 10, 240, 240, 40), PAL.orange, { torn: 1.5, seed: 1590, shadow: false });
    for (let i = 0; i < 5; i++) { ctx.fillStyle = '#FFC857'; ctx.fillRect(500, SEA - 135 + i * 24 + i * i * 2, 540, 5 + i * 2); }
    // the sea, seen in cross-section: underwater fills the frame's lower half
    seaV(t, SEA, PAL.blue, 0, 10, 1591);
    halftone(rectPts(-60, SEA + 30, W + 120, H), '#153E80', { cell: 16, dot: .25, op: .5 });
    ctx.save(); ctx.globalCompositeOperation = 'screen';
    for (let i = 0; i < 4; i++) { const x = 120 + i * 260 + Math.sin(t * .8 + i) * 30; ctx.fillStyle = 'rgb(159 211 242 / .12)'; tracePath([[x - 40, SEA], [x + 40, SEA], [x + 160, H], [x + 20, H]]); ctx.fill(); }
    ctx.restore();
    for (let i = 0; i < 14; i++) { const ph = frac(lt * .6 + hash(i + 1610)), x = hash(i + 1611) * W + Math.sin(ph * 9 + i) * 20, y = lerp(H, SEA + 30, ph); scrap(ellPts(x, y, 8 + hash(i + 1612) * 10, 8 + hash(i + 1612) * 10, 10), alpha(PAL.white, .5), { torn: .2, shadow: false, ink: alpha(PAL.white, .8), sw: 2 }); }
    // the pier's posts, down into the water
    for (const x of [70, 250, 430]) scrap(rectPts(x - 16, 820, 32, 520), '#6B4A2A', { torn: .8, seed: 1592 + x });
    // researchers swimming up for it, eyes on the money
    const swimmers = [
      { x: 300, y0: 1560, v: 360, name: 'EX-GDM', hair: 'bun', skin: SKINS[3], hairCol: '#2A1A10' },
      { x: 560, y0: 1700, v: 420, name: 'EX-APPLE', hair: 'spiky', skin: SKINS[0], hairCol: '#6B4A2A' },
      { x: 880, y0: 1480, v: 330, name: 'EX-OPENAI', hair: 'curly', skin: SKINS[2], hairCol: '#1C1A1F' },
    ];
    const BX = 790;
    swimmers.forEach((q, i) => {
      const y = Math.max(q.y0 - q.v * lt, 1240 + i * 25), kick = t * 3 + i * .3, lean = clamp((BX - q.x) / 900, -.3, .3);
      person(q.x, y, 28, { name: q.name, top: 'coat', topCol: PAL.white, hair: q.hair, hairCol: q.hairCol, skin: q.skin, rot: lean, aL: 1.3 + Math.sin(t * 12 + i) * .15, aR: 1.3 - Math.sin(t * 12 + i) * .15, eyes: 'spark', mouth: 'O', shadow: false, walk: kick });
    });
    // the bait, reeled up out of the sea with a researcher clinging under it
    const rk = easeOut(clamp(lt / (d * .82))), bagX = BX + Math.sin(t * 3) * 14, bagY = lerp(1290, 600, rk) + Math.sin(t * 5) * 8;
    const hs = 28;
    person(bagX, bagY + 10.3 * hs, hs, { name: 'EX-OPENAI', top: 'coat', topCol: PAL.white, hair: 'long', hairCol: '#C07A3A', skin: SKINS[1], aL: 1.25, aR: 1.25, eyes: 'happy', mouth: 'grin', shadow: false, rot: Math.sin(t * 4) * .06 });
    moneyBag(bagX, bagY, 60, { label: '$100M', rot: Math.sin(t * 4) * .1 });
    // Zuck's line, from the rod's tip down to the bag
    const zx = 250, zy = 818, s = 48, aR = .5 + pb * .12, dyZ = -pb * .08;
    const [hx, hy] = handAt(zx, zy, s, 1, aR, dyZ);
    const tipX = 780 + pb * 10, tipY = 430 + pb * 40;
    marker([[tipX, tipY], [bagX, bagY - 72]], PAL.ink, 3, { rough: .5 });
    // everything under the waterline is under water
    const wl = []; for (let i = 0; i <= 16; i++) wl.push([i * 76 - 70, SEA + 22 + Math.sin(i * .8 + t * 4 + 1.3) * 9]);
    ctx.save(); tracePath([[-80, H + 80], ...wl, [W + 80, H + 80]]); ctx.fillStyle = 'rgb(44 111 207 / .42)'; ctx.fill(); ctx.restore();
    marker(wl, alpha(PAL.white, .85), 7, { rough: 1, smooth: true });
    // the splash as the bag breaks the surface
    const tOut = (() => { for (let i = 0; i <= 60; i++) { const l = i / 60 * d; if (lerp(1290, 600, easeOut(clamp(l / (d * .82)))) < SEA) return l; } return 9; })();
    const sa = (lt - tOut) / .45;
    if (sa > 0 && sa < 1) for (let j = 0; j < 9; j++) { const a = -Math.PI / 2 + (j - 4) * .32; scrap(ellPts(bagX + Math.cos(a) * sa * 170, SEA + Math.sin(a) * sa * 220 + sa * sa * 200, 14, 20, 8), PAL.white, { torn: .5, shadow: false, seed: 1600 + j, ink: PAL.ink, sw: 2, op: 1 - sa }); }
    // the pier, and ZUCK on it with the rod
    scrap(rectPts(-60, 800, 540, 40), '#9A6A3E', { torn: 1, seed: 1595, shade: true, shadeOp: .3 });
    person(zx, zy, s, { name: 'ZUCK', top: 'tee', topCol: '#8E8E96', hair: 'short', hairCol: '#5A4030', skin: SKINS[4], mouth: 'grin', eyes: 'dot', aR, aL: -1 + Math.sin(b * Math.PI * 2) * .25, pants: '#3B4A6B', dy: dyZ });
    const rodPts = []; for (let i = 0; i <= 12; i++) { const u = i / 12; rodPts.push([lerp(hx - 40, tipX, u), lerp(hy + 30, tipY, u) - Math.sin(u * Math.PI) * (90 - pb * 50) * u]); }
    marker(rodPts, PAL.ink, 14, { rough: 0 }); marker(rodPts, '#8B5A2B', 8, { rough: 0 });
    scrap(ellPts(hx - 14, hy + 22, 24, 24, 12), '#C9CED9', { torn: .4, seed: 1596, ink: PAL.ink, sw: 3 });
    sticker('$100,000,000', 520, 630, 140, PAL.pink, { pop: popK(lt, .05, .22), rot: -.12, size: 40, textCol: PAL.ink });
    camEnd();
  });

  // ---------- V2.6 (vertical): a live-shopping stream: the boxes drop into a stack of three, BUY 3! ----------
  vshot('V2.6', (p, lt, d, t) => {
    fillBG(PAL.pink);
    raysBG(540, 760, 16, '#FF78BD', lt * .6);
    toneBG(PAL.purple, 18, .2, .3);
    venter(lt, p, 540, 960, .03, .012);
    const pb = pulse(t);
    // the seller's table
    const TY = 1180;
    scrap(rectPts(-60, TY, W + 120, 800), PAL.purple, { torn: 1, seed: 1626, shadow: [0, -8] });
    scrap(rectPts(-60, TY - 16, W + 120, 34), PAL.white, { torn: .8, seed: 1627, shade: true, shadeOp: .2 });
    halftone(rectPts(-60, TY + 18, W + 120, 800), '#3A1E70', { cell: 14, dot: .3, op: .4 });
    // three boxes, dropped one on another on the beats
    const BW = 236, BH = 268, X = 345;
    const lands = [-.2, beatLt(t, lt, 0), beatLt(t, lt, 1)];
    for (let i = 0; i < 3; i++) {
      const fall = clamp((lt - lands[i] + .14) / .14); if (fall <= 0) continue;
      const age = lt - lands[i], yb = TY - 4 - i * BH, y = lerp(yb - 1500, yb, easeIn(fall));
      const sq = age > 0 && age < .2 ? Math.sin(age / .2 * Math.PI) * .08 * (1 - age / .2) : 0;
      ctx.save(); ctx.translate(X, y); ctx.scale(1 + sq, 1 - sq); ctx.translate(-X, -y);
      siBox(X, y, BW, BH, (hash(i + 80) - .5) * .06 + (age > .2 ? Math.sin(t * 8 + i) * .012 : 0), 1, i);
      ctx.restore();
      if (age > 0) { const nk = clamp(age / .14); ransom(`${i + 1}!`, 118, yb - BH / 2 - Math.sin(nk * Math.PI) * 30, 96, { pop: nk, seed: 90 + i }); }
    }
    // BUY 3!
    ctx.save(); ctx.translate(810, 590); ctx.rotate(Math.sin(t * 6) * .06); const bs = 1 + pb * .08; ctx.scale(bs, bs);
    sticker('BUY\n3!', 0, 0, 175, PAL.yellow, { pop: popK(lt, .02, .22), rot: .1, size: 96, font: 'bungee', textCol: PAL.red, n: 20 });
    ctx.restore();
    // the price
    const pk = popK(lt, beatLt(t, lt, 1) + .12, .2);
    if (pk > 0) {
      ctx.save(); ctx.translate(790, 960); ctx.rotate(-.08); const sc = backOut(pk) * .82; ctx.scale(sc, sc);
      scrap(tagShape(420, 150), PAL.white, { torn: 1.5, seed: 1625, ink: PAL.ink, sw: 5 });
      txt('ONLY', -40, -34, 34, PAL.ink, { font: 'archivo' });
      txt('$14.3B*', 30, 22, 80, PAL.red, { font: 'anton' });
      ctx.restore();
    }
    // the stream's chrome: LIVE and the viewers top left, hearts drifting up the right edge, the pinned offer along the foot
    scrap(rrPts(70, 272, 116, 58, 12), PAL.red, { torn: .6, seed: 1628, shadow: [4, 5] });
    txt('LIVE', 128, 302, 36, PAL.white, { font: 'archivo' });
    scrap(rrPts(196, 272, 196, 58, 12), alpha(PAL.ink, .55), { torn: .6, seed: 1629, shadow: false });
    scrap(ellPts(232, 301, 18, 11, 14), PAL.white, { torn: .2, shadow: false }); dot2(232, 301, 6, PAL.ink);
    txt(`${(2.1 + Math.floor(lt * 9) / 10).toFixed(1)}M`, 318, 302, 36, PAL.white, { font: 'archivo' });
    for (let i = 0; i < 9; i++) {
      const ph = frac(lt * .8 + hash(i + 1630)), x = 930 + Math.sin(ph * 7 + i) * 40, y = lerp(1680, 700, ph);
      ctx.save(); ctx.globalAlpha = 1 - ph * ph; scrap(heartPts(x, y, 26 + hash(i + 1631) * 14), [PAL.red, PAL.white, PAL.yellow][i % 3], { torn: .3, ink: PAL.ink, sw: 3, shadow: false }); ctx.restore();
    }
    ctx.fillStyle = PAL.ink; ctx.fillRect(-40, 1690, W + 80, 70);
    const crawl = 'CALL NOW!  1-800-SUPER-AI  ★  OPERATORS STANDING BY  ★  *RESEARCHERS SOLD SEPARATELY  ★  ';
    const cw = textW(crawl, 44, 'archivo'), cx0 = 40 - (lt * 500) % cw;
    for (let k = 0; k < 3; k++) txt(crawl, cx0 + k * cw, 1726, 44, frac(lt / BL()) < .5 ? PAL.yellow : PAL.white, { font: 'archivo', align: 'left' });
    camEnd();
    // the phone it's all on
    ctx.save();
    ctx.beginPath(); ctx.rect(-10, -10, W + 20, H + 20); rrPts(26, 26, W - 52, H - 52, 90).forEach(([x, y], i) => i ? ctx.lineTo(x, y) : ctx.moveTo(x, y)); ctx.closePath(); ctx.fillStyle = PAL.ink; ctx.fill('evenodd');
    scrap(rrPts(W / 2 - 110, 52, 220, 54, 27), PAL.ink, { torn: .3, shadow: false });
    ctx.restore();
  });

  // ---------- V2.7 (vertical): the robot tall in the middle, its screen glitching; the cord down to the socket, yanked ----------
  // (the horizontal shot's robot, in its own coordinates round (960, 880))
  function grokBot(lt, off, yank) {
    const wobble = off ? .06 * easeOut(clamp((lt - yank) / .3)) : jit(.025);
    ctx.save(); ctx.translate(960, 880); ctx.rotate(wobble); ctx.translate(-960, -880);
    bot(960, 880, 56, { col: '#9AA3B5', screen: '#111', face: ' ', antenna: false, aL: off ? -1.3 : .4 + jit(.7), aR: off ? -1.3 : .9 + jit(.7), dy: off ? .08 : 0 });
    const hy0 = 880 + (off ? 5 : 0) - 690;
    scrap(rrPts(960 - 210, hy0, 420, 290, 34), '#8A93A8', { torn: 1, seed: 1636, ink: PAL.ink, sw: 5, shade: true, shadeOp: .3 });
    marker([[960, hy0], [960, hy0 - 60]], PAL.ink, 8, { rough: 0 });
    scrap(ellPts(960, hy0 - 70, 20, 20, 12), off ? '#444' : PAL.red, { torn: .3, shadow: false, ink: PAL.ink, sw: 3 });
    const X0 = 960 - 175, Y0 = hy0 + 30, SW = 350, SH = 225;
    ctx.save(); tracePath(rrPts(X0, Y0, SW, SH, 16)); ctx.clip();
    if (!off) {
      const gf = Math.floor(T * 24);
      ctx.fillStyle = PAL.red; ctx.fillRect(X0, Y0, SW, SH);
      for (let i = 0; i < 14; i++) { const yy = Y0 + hash2(gf, i) * SH, hh = 5 + hash2(gf, i + 20) * 22; ctx.fillStyle = [PAL.white, '#7A0E0A', PAL.pink, '#FF9A8A', PAL.ink][i % 5]; ctx.fillRect(X0 + (hash2(gf, i + 40) - .5) * 90, yy, SW, hh); }
    } else { ctx.fillStyle = '#16141A'; ctx.fillRect(X0, Y0, SW, SH); ctx.fillStyle = alpha(PAL.white, .8 * (1 - clamp((lt - yank) / .15))); ctx.fillRect(X0, Y0 + SH / 2 - 3, SW, 6); }
    ctx.restore();
    ctx.strokeStyle = PAL.ink; ctx.lineWidth = 5; tracePath(rrPts(X0, Y0, SW, SH, 16)); ctx.stroke();
    ctx.save(); ctx.translate(960 + jit(off ? 0 : 4), Y0 + SH / 2); ctx.rotate(-.07);
    scrap(rectPts(-250, -46, 500, 92), '#000', { torn: 1, seed: 1634, shadow: [6, 8], shadowCol: 'rgb(232 65 47 / .6)' });
    txt('CENSORED', 0, 3, 54, PAL.white, { font: 'mono' });
    ctx.restore();
    ctx.restore();
  }
  vshot('V2.7', (p, lt, d, t) => {
    const yank = .42, off = lt > yank + .04;
    const shk = lt > yank && lt < yank + .2 ? shakeXY(t, 12) : shakeXY(t, off ? 0 : 3);
    fillBG('#0E0C12');
    // alarm beams sweeping the room
    const ALARMS = [[120, 300], [960, 470]];
    ctx.save(); ctx.globalCompositeOperation = 'screen';
    for (const [i, [bx, by]] of ALARMS.entries()) {
      const a = t * 7 + i * 1.7;
      ctx.fillStyle = 'rgb(232 65 47 / .3)';
      tracePath([[bx, by], [bx + Math.cos(a - .22) * 2600, by + Math.sin(a - .22) * 2600], [bx + Math.cos(a + .22) * 2600, by + Math.sin(a + .22) * 2600]]); ctx.fill();
      tracePath([[bx, by], [bx - Math.cos(a - .22) * 2600, by - Math.sin(a - .22) * 2600], [bx - Math.cos(a + .22) * 2600, by - Math.sin(a + .22) * 2600]]); ctx.fill();
    }
    ctx.fillStyle = `rgb(232 65 47 / ${.14 * pulse2(t, 5)})`; ctx.fillRect(0, 0, W, H);
    ctx.restore();
    // (the room sits low in the frame: the robot over the caption, the floor under it)
    venter(lt, p, 540 - shk[0], 820 - shk[1], .04, 0);
    for (const [bx, by] of ALARMS) {
      scrap(rectPts(bx - 60, by + 20, 120, 40), '#3A3A44', { torn: .6, seed: 1630 });
      scrap([...ellPts(bx, by + 22, 55, 70, 24).filter(q => q[1] <= by + 22)], PAL.red, { torn: .6, seed: 1631, ink: PAL.ink, sw: 4 });
      ctx.fillStyle = alpha(PAL.yellow, .7 * pulse2(t, 4)); tracePath(ellPts(bx, by - 10, 22, 22, 12)); ctx.fill();
    }
    // the floor and the wall socket at its foot
    const FY = 1262;
    scrap(rectPts(-100, FY, W + 200, 800), '#1C1A22', { torn: 1, seed: 1632, shadow: false });
    const SX = 830, SY = 1150;
    scrap(rrPts(SX - 62, SY - 86, 124, 172, 14), PAL.white, { torn: .8, seed: 1633, ink: PAL.ink, sw: 4 });
    for (const dy of [-38, 38]) { ctx.fillStyle = PAL.ink; ctx.fillRect(SX - 22, SY + dy - 14, 12, 28); ctx.fillRect(SX + 10, SY + dy - 14, 12, 28); }
    const yk = clamp((lt - yank) / .12);
    const plugX = lerp(SX, 1010, easeOut(yk)), plugY = lerp(SY - 38, 760, easeOut(yk));
    // the robot, big in the middle
    const RX = 470, RY = FY - 4, RS = 1.08;
    const map = (x, y) => [RX + (x - 960) * RS, RY + (y - 880) * RS];
    const [cx0, cy0] = map(1050, 800);
    const cord = []; for (let i = 0; i <= 16; i++) { const u = i / 16; cord.push([lerp(cx0, plugX, u), lerp(cy0, plugY + 40, u) + Math.sin(u * Math.PI) * (110 * (1 - yk) + 20)]); }
    marker(cord, PAL.ink, 18, { rough: .5, smooth: true }); marker(cord, '#77747F', 10, { rough: .5, smooth: true });
    ctx.save(); ctx.translate(RX, RY); ctx.scale(RS, RS); ctx.translate(-960, -880); grokBot(lt, off, yank); ctx.restore();
    // the hand yanking the plug, the arm in from the right edge
    const hx = plugX + 70, hy = plugY + 14;
    marker([[hx + 60, hy + 10], [W + 400, hy - 300 + yk * 140]], PAL.ink, 118, { rough: 0 }); marker([[hx + 60, hy + 10], [W + 400, hy - 300 + yk * 140]], '#2C4F8A', 104, { rough: 0 });
    scrap(ellPts(hx, hy, 82, 66, 18), SKINS[1], { torn: 1, seed: 1635, ink: PAL.ink, sw: 4 });
    for (let i = 0; i < 4; i++) scrap(rrPts(hx - 84 + i * 6, hy - 60 + i * 30, 70, 30, 14), SKINS[1], { torn: .5, seed: 1636 + i, ink: PAL.ink, sw: 3, shadow: false });
    ctx.save(); ctx.translate(plugX - 20, plugY);
    scrap(rrPts(-42, -24, 74, 62, 10), '#222', { torn: .4, seed: 1640 });
    ctx.fillStyle = '#C9CED9'; ctx.fillRect(-30, 38, 11, 28); ctx.fillRect(6, 38, 11, 28);
    ctx.restore();
    if (lt > yank && lt < yank + .3) { popBurst(SX, SY - 20, 150, (lt - yank) / .3, PAL.yellow); for (let i = 0; i < 6; i++) { const a = -Math.PI / 2 + (i - 2.5) * .45, r = (lt - yank) * 900; marker([[SX + Math.cos(a) * r * .5, SY - 20 + Math.sin(a) * r * .5], [SX + Math.cos(a) * r, SY - 20 + Math.sin(a) * r]], PAL.yellow, 6, { rough: 1 }); } }
    stamp('YIKES', 400, 1010, 140, PAL.yellow, -.18, { pop: popK(lt, yank + .08, .12), blend: 'source-over' });
    camEnd();
    captionStyle({ color: PAL.red });
  });

  // ---------- V2.8 (vertical): two robots squeezed on top of a tall #1 column; the gold medals drop onto them from above ----------
  vshot('V2.8', (p, lt, d, t) => {
    fillBG(PAL.blue);
    raysBG(540, 760, 24, '#3F82E0', -lt * .25);
    toneBG('#123C8A', 22, .2, .35);
    venter(lt, p, 540, 960, .04, -.012);
    const b = lt / BL();
    const syms = ['π', 'Σ', '∫', '√', 'φ', 'Δ', 'x²', '≠', '∀', 'θ', 'λ', '∂', '+', '÷', '=', '≤'];
    const conf = (i0, n) => { for (let i = i0; i < i0 + n; i++) {
      const x = hash(i + 90) * (W + 100) - 50 + Math.sin(t * 2 + i) * 30, y = ((lt + 2) * (300 + hash(i + 91) * 260) + hash(i + 92) * 2100) % 2100 - 150;
      txt(syms[i % syms.length], x, y, 60 + hash(i + 93) * 50, [PAL.yellow, PAL.pink, PAL.white, PAL.mint, PAL.gold][i % 5], { font: 'mono', rot: t * (hash(i + 94) - .5) * 4, shadow: [4, 5] });
    } };
    conf(0, 16);
    for (let i = 0; i < 6; i++) { const t0 = .2 + i * BL() * .75, age = (lt - t0) / .2; popBurst([130, 950, 150, 930, 120, 960][i], [700, 560, 980, 860, 520, 1060][i], 90, age, PAL.white); }
    // the podium: a tall #1 column, the #2 and #3 blocks low down either side
    const blocks = [[540, 985, 580, '1', PAL.white], [95, 1150, 300, '2', '#D8DDE6'], [985, 1205, 300, '3', '#E9C9A0']];
    for (const [x, top, w, n, c] of blocks) {
      scrap(rectPts(x - w / 2, top, w, H - top + 60), c, { torn: 1.2, seed: 1650 + +n, ink: PAL.ink, sw: 5, shade: true, shadeOp: .2 });
      txt(n, x + (n === '2' ? 40 : n === '3' ? -85 : 0), top + (n === '1' ? 120 : 85), n === '1' ? 170 : 110, n === '1' ? PAL.gold : PAL.grey, { font: 'abril', stroke: PAL.ink, sw: 6 });
    }
    // two robots jostling for the one top step
    const R = [{ x: 395, col: '#E6E9EE', name: 'OPENAI', ph: 0, rib: PAL.pink }, { x: 685, col: '#8FB8F2', name: 'DEEPMIND', ph: .5, rib: PAL.red }];
    R.forEach((r, i) => {
      const hop = Math.max(0, Math.sin((b + r.ph) * Math.PI)) ** 2;
      const s = 52, gy = 985, dy = -hop * .45, lean = Math.sin(b * Math.PI) * (i ? -12 : 12);
      bot(r.x + lean, gy, s, { col: r.col, eyes: 'spark', dy, aL: i ? .3 + hop * .9 : 1.3, aR: i ? 1.3 : .3 + hop * .9, seed: 500 + i * 30 });
      helloTag(r.name, r.x + lean, gy + dy * s - 3.95 * s, s * .5, i ? .06 : -.06);
      const mk = popK(lt, .04 + i * .12, .3);
      const my = lerp(-300, gy + dy * s - 6.3 * s, easeIn(mk)) + (mk < 1 ? 0 : Math.sin((lt - .34 - i * .12) * 14) * 4 * Math.exp(-(lt - .34) * 3));
      if (mk > 0) {
        if (mk < 1) for (const sd of [-1, 1]) marker([[r.x + lean + sd * 1.1 * 26, my - 6 * 26], [r.x + lean + sd * 1.1 * 26, my - 6 * 26 - 900]], r.rib, 18, { rough: 0 });
        medal(r.x + lean, my, 26, { text: 'IMO', ribbon: r.rib, rot: Math.sin(t * 6 + i) * .08 });
      }
    });
    conf(16, 10);
    camEnd();
  });

  // ---------- V2.9 (vertical): the GPT-5 mallet cracks the 4o heart up top; its halves fall; the #keep4o crowd weeps below ----------
  vshot('V2.9', (p, lt, d, t) => {
    const hitT = .26;
    const shk = lt > hitT && lt < hitT + .2 ? shakeXY(t, 16) : [0, 0];
    fillBG('#FFB8D6');
    toneBG(PAL.red, 20, .18, .35);
    venter(lt, p, 540 - shk[0], 960 - shk[1], .03, .012);
    const cx = 520, cy = 640, r = 255, broken = lt > hitT, bk = clamp((lt - hitT) / .6), age = Math.max(0, lt - hitT);
    const beat = broken ? 1 : 1 + pulse(t, 8) * .06;
    const heartFace = sad => {
      txt('4o', 0, -20, 190, PAL.white, { font: 'archivo', stroke: PAL.ink, sw: 10 });
      ctx.strokeStyle = PAL.ink; ctx.fillStyle = PAL.ink; ctx.lineWidth = 9; ctx.lineCap = 'round';
      for (const sd of [-1, 1]) {
        if (sad) { ctx.beginPath(); ctx.moveTo(sd * 150 - 26, -110); ctx.lineTo(sd * 150 + 26, -84); ctx.moveTo(sd * 150 + 26, -110); ctx.lineTo(sd * 150 - 26, -84); ctx.stroke(); }
        else { ctx.beginPath(); ctx.arc(sd * 150, -90, 22, Math.PI * 1.1, Math.PI * 1.9); ctx.stroke(); }
      }
      ctx.fillStyle = alpha(PAL.white, .7); tracePath(ellPts(-175, 25, 26, 14, 10)); ctx.fill(); tracePath(ellPts(175, 25, 26, 14, 10)); ctx.fill();
    };
    const drawHeart = sad => { scrap(heartPts(0, 0, 270), PAL.red, { torn: 2, seed: 1660, ink: PAL.ink, sw: 7, shadow: [12, 14], shade: '#8E1B14', shadeOp: .35 }); heartFace(sad); };
    const zz = []; for (let i = 0; i <= 9; i++) zz.push([i === 0 || i === 9 ? 0 : (i % 2 ? 26 : -26), -270 * .42 + i * (270 * 1.55) / 9]);
    const hs = r / 270;
    // the protesters' back row (behind the falling halves)
    const crowdRow = (P, s, gy, signs) => P.forEach(([x, ph], i) => {
      const bob = Math.abs(Math.sin((lt / BL() + ph) * Math.PI)), cry = broken;
      const k = (i + (signs ? 0 : 2)) % 4;
      const aR = signs ? 1.15 + bob * .1 : (cry ? 1.75 : -1.1), aL = signs ? (cry ? .9 : -1.1) : (cry ? 1.75 : -1.1);
      person(x, gy, s, { name: ['JUNE', 'ALEX', 'RILEY', 'KAI', 'MO', 'SAGE', 'NOOR'][(i + (signs ? 0 : 4)) % 7], top: ['hoodie', 'sweater', 'tee', 'dress'][k], topCol: [PAL.purple, PAL.teal, PAL.blue, PAL.green][k], hair: ['long', 'curly', 'short', 'bun'][k], skin: SKINS[[1, 3, 0, 2, 4, 5][(i + (signs ? 0 : 3)) % 6]], eyes: cry ? 'closed' : 'dot', mouth: cry ? 'O' : 'frown', aR, aL, dy: -bob * .1 });
      if (signs) {
        const [hx, hy] = handAt(x, gy, s, 1, aR, -bob * .1);
        marker([[hx, hy + 1.4 * s], [hx, hy - 5.4 * s]], '#8B5A2B', .4 * s, { rough: 0 });
        card(hx, hy - 7.5 * s, 10.5 * s, 4.4 * s, PAL.white, (hash(i) - .5) * .2, { torn: 1, seed: 1670 + i, ink: PAL.ink, sw: 4 });
        txt('#keep4o', hx, hy - 7.4 * s, 2.2 * s, PAL.red, { font: 'marker', rot: (hash(i) - .5) * .2, maxW: 9.4 * s });
      }
      if (cry) {
        const [ex, ey] = headAt(x, gy, s, -bob * .1);
        for (const sd of [-1, 1]) for (let j = 0; j < 5; j++) { const ph2 = frac(lt * 2.5 + j / 5 + i * .13); scrap(ellPts(ex + sd * (.5 * s + ph2 * 3.2 * s), ey + ph2 * 4.5 * s - Math.sin(ph2 * Math.PI) * 2.3 * s, .32 * s, .5 * s, 8), PAL.sky, { torn: .2, shadow: false, ink: PAL.ink, sw: 1.5 }); }
      }
    });
    if (!broken) {
      ctx.save(); ctx.translate(cx, cy); ctx.scale(beat * hs, beat * hs); drawHeart(false); ctx.restore();
    } else {
      // the halves come apart and fall away down the frame
      for (const sd of [-1, 1]) {
        ctx.save(); ctx.translate(cx + sd * (easeOut(bk) * 160 + age * 30), cy + age * age * 45 + easeOut(bk) * 40); ctx.rotate(sd * (easeOut(bk) * .3 + age * .15)); ctx.scale(hs, hs);
        ctx.beginPath(); ctx.moveTo(sd * 600, -600); ctx.lineTo(0, -600); zz.forEach(([a, b2]) => ctx.lineTo(a, b2)); ctx.lineTo(0, 600); ctx.lineTo(sd * 600, 600); ctx.closePath(); ctx.clip();
        drawHeart(true);
        marker(zz, PAL.ink, 6, { rough: 1 });
        ctx.restore();
      }
      for (let i = 0; i < 8; i++) { const x = cx + (hash(i + 130) - .5) * 90, y = cy + age * 300 + age * age * 1100 * (.6 + hash(i + 131)); scrap(xform([[-12, -10], [14, -6], [4, 14]], x, y, age * 8 + i), PAL.red, { torn: .5, shadow: false, ink: PAL.ink, sw: 2 }); }
      if (lt < hitT + .3) popBurst(cx + 40, cy - 170, 170, (lt - hitT) / .3, PAL.white, 'CRACK');
    }
    // the crowd: signs up in the back row, the front row crying into their hands
    // (the rows recede up the frame: signs held up mid-frame, the front row crying in the bottom fifth, under the caption)
    crowdRow([[150, 0], [400, .3], [660, .6], [910, .9]], 22, 1330, true);
    crowdRow([[180, .15], [540, .45], [900, .75]], 34, 2000, false);
    // the GPT-5 mallet: swings in from the top right, smashes, flies back out
    const px = 1020, py = -320, L = 880;
    const th = lt < .1 ? lerp(.3, .45, easeOut(lt / .1)) : lt < hitT ? lerp(.45, -.45, easeIn((lt - .1) / (hitT - .1))) : lerp(-.45, .6, easeInOutQ(clamp((lt - hitT - .05) / .4)));
    ctx.save(); ctx.translate(px, py); ctx.rotate(-th);
    marker([[0, 0], [0, L]], PAL.ink, 32, { rough: 0 }); marker([[0, 0], [0, L]], '#B07A45', 22, { rough: 0 });
    scrap(rrPts(-180, L - 95, 360, 190, 24), '#2E3440', { torn: 1, seed: 1665, ink: PAL.ink, sw: 5, shade: true, shadeOp: .3 });
    scrap(rectPts(-190, L - 100, 30, 200), '#4A5262', { torn: .5, seed: 1666, shadow: false, ink: PAL.ink, sw: 3 });
    scrap(rectPts(160, L - 100, 30, 200), '#4A5262', { torn: .5, seed: 1667, shadow: false, ink: PAL.ink, sw: 3 });
    txt('GPT-5', 0, L + 4, 86, PAL.white, { font: 'anton' });
    ctx.restore();
    camEnd();
  });

  // ---------- V2.10 (vertical): the chart as a staircase down from #1, whose bar shoots up the frame with the banana riding it ----------
  vshot('V2.10', (p, lt, d, t) => {
    fillBG('#4A2A8C');
    toneBG('#2A1360', 20, .25, .5);
    venter(lt, p, 540, 960, .04, -.012);
    const pb = pulse(t), b = lt / BL();
    // (the chart stands on the foot of the frame: #1 shoots up two-thirds of its height)
    const baseY = 1870, X1 = 215, grow = backOut(clamp(lt / .3), 1.4), topH = 1160 * grow + 30 * ease(p), topY = baseY - topH;
    // spotlights converge on #1
    ctx.save(); ctx.globalCompositeOperation = 'screen';
    for (const [x0, ph] of [[60, 0], [760, 1.4]]) {
      const tx = X1 + Math.sin(t * 3 + ph) * 50;
      ctx.fillStyle = 'rgb(255 216 58 / .26)';
      tracePath([[x0 - 40, -40], [x0 + 40, -40], [tx + 160, topY], [tx - 160, topY]]); ctx.fill();
      tracePath(ellPts(tx, topY, 160, 26, 20)); ctx.fill();
    }
    ctx.restore();
    txt('TOP CHARTS', 700, 470, 68, PAL.white, { font: 'bungee', rot: -.05, stroke: PAL.ink, sw: 10 });
    marker([[60, 560], [60, baseY], [1000, baseY]], PAL.white, 9, { rough: 1 });
    const bars = [[X1, 0, PAL.gold, 1], [400, 470, PAL.mint, 2], [565, 380, PAL.pink, 3], [725, 290, PAL.sky, 4], [880, 200, PAL.purple, 5]];
    bars.forEach(([x, h, c, n], i) => {
      const hh = i === 0 ? topH : h * (1 - .2 * clamp(lt / .5)) * (1 + Math.sin(t * 6 + i) * .02), bw = i === 0 ? 180 : 136;
      scrap(rectPts(x - bw / 2, baseY - hh, bw, hh), c, { torn: 1, seed: 1690 + i, ink: PAL.ink, sw: 5, shade: true, shadeOp: .25 });
      txt(`#${n}`, x, i === 0 ? baseY - hh + 120 : baseY - 70, i === 0 ? 104 : 50, i === 0 ? PAL.red : PAL.ink, { font: i === 0 ? 'bungee' : 'anton', stroke: i === 0 ? PAL.ink : undefined, sw: 8, maxW: bw - 10 });
    });
    const hop = Math.max(0, Math.sin(b * Math.PI)) ** 2;
    bananaGuy(X1, topY - 4, 27, { dy: -hop * 30, aL: 1.1 + pb * .3, aR: 1.1 + pb * .3, rot: Math.sin(b * Math.PI) * .08 });
    for (let i = 0; i < 8; i++) { const a = i / 8 * TAU + t * 2, rr = 190 + Math.sin(t * 5 + i) * 18; const k = .6 + .4 * Math.sin(t * 9 + i * 2); scrap(starPts(X1 + 20 + Math.cos(a) * rr, topY - 165 + Math.sin(a) * rr * .8, 28 * k, .35, 4, 0), PAL.yellow, { torn: .3, shadow: false }); }
    camEnd();
    captionStyle({ color: PAL.purple });
  });

  // ---------- V2.11 (vertical): the cheque across the top; the happy books in a cheerleader pyramid below; Clawd sweating ----------
  vshot('V2.11', (p, lt, d, t) => {
    fillBG(PAL.mint);
    toneBG(PAL.green, 20, .22, .35);
    venter(lt, p, 540, 960, .03, .012);
    const b = lt / BL();
    // the cheque slides in (the horizontal one, scaled to the frame's width)
    const ck = easeOut(clamp(lt / .16));
    const qx = lerp(1900, 540, ck), qy = 598, qr = lerp(.2, -.035, ck) + (ck >= 1 ? Math.sin(t * 3) * .006 : 0);
    ctx.save(); ctx.translate(qx, qy); ctx.rotate(qr); ctx.scale(.78, .78);
    const w = 1200, h = 480;
    scrap(rectPts(-w / 2, -h / 2, w, h), '#EAF3FF', { torn: 2, seed: 1710, ink: PAL.ink, sw: 5, shadow: [14, 16] });
    ctx.strokeStyle = alpha(PAL.blue, .25); ctx.lineWidth = 3;
    for (let i = 0; i < 5; i++) { ctx.beginPath(); for (let j = 0; j <= 40; j++) { const xx = -w / 2 + 20 + j / 40 * (w - 40), yy = -h / 2 + 60 + i * 12 + Math.sin(j * .7 + i) * 8; j ? ctx.lineTo(xx, yy) : ctx.moveTo(xx, yy); } ctx.stroke(); }
    txt('BANK OF SETTLEMENTS', -w / 2 + 40, -h / 2 + 50, 34, PAL.ink, { font: 'abril', align: 'left' });
    txt('No. 1500000000', w / 2 - 40, -h / 2 + 50, 26, PAL.ink, { font: 'typewriter', align: 'right' });
    txt('PAY TO THE ORDER OF', -w / 2 + 40, -h / 2 + 150, 26, PAL.ink, { font: 'archivo', align: 'left' });
    txt('THE AUTHORS', -w / 2 + 380, -h / 2 + 146, 84, PAL.ink, { font: 'marker', align: 'left' });
    marker([[-w / 2 + 360, -h / 2 + 190], [w / 2 - 60, -h / 2 + 190]], PAL.ink, 3, { rough: 0 });
    txt('$1,500,000,000', 0, 40, 160, PAL.green, { font: 'anton', stroke: PAL.ink, sw: 8, maxW: w - 80 });
    txt('MEMO: sorry about the books', -w / 2 + 40, h / 2 - 60, 30, PAL.ink, { font: 'typewriter', align: 'left' });
    const sk = clamp((lt - .3) / .5);
    const sig = []; for (let i = 0; i <= 30; i++) { const u = i / 30; sig.push([w / 2 - 460 + u * 380, h / 2 - 70 + Math.sin(u * 22) * 22 - u * 20]); }
    if (sk > 0) marker(partial(sig, sk), PAL.blue, 6, { rough: 1, smooth: true });
    marker([[w / 2 - 480, h / 2 - 40], [w / 2 - 60, h / 2 - 40]], PAL.ink, 3, { rough: 0 });
    txt('— Anthropic', w / 2 - 270, h / 2 - 20, 22, PAL.ink, { font: 'typewriter' });
    ctx.restore();
    // the books, cheering in a pyramid that bounces on the beat
    const bcol = [PAL.red, PAL.blue, PAL.yellow, PAL.purple, PAL.pink, PAL.teal];
    const BW = 128, BH = 152, PX = 440, FL = 1262, bounce = Math.max(0, Math.sin(bpOf(t) * Math.PI)) ** 2 * 18;
    const rows = [[-1, 0, 1], [-.5, .5], [0]];
    let n = 0;
    rows.forEach((row, ri) => row.forEach(c => {
      const i = n++, x = PX + c * (BW + 22), y = FL - ri * (BH + 6) - bounce * (ri + 1) * .5;
      const wave = ri === 2 ? 40 + Math.sin(t * 14) * 20 : Math.max(0, Math.sin((bpOf(t) + i * .33) * Math.PI)) * 30;
      happyBook(x + Math.sin(t * 4 + i) * ri * 3, y, BW, BH, bcol[i], ri ? wave + 2 : wave * .03, i);
    }));
    // the rest of the half-million books, piled up along the foot of the frame
    for (let r = 0; r < 3; r++) for (let i = 0; i < 9; i++) {
      const bw = 150 + hash2(r, i + 1720) * 70, x = -60 + i * 140 + (r % 2) * 60 + (hash2(r, i + 1721) - .5) * 30, y = 1660 + r * 95 + hash2(r, i + 1722) * 20, rot = (hash2(r, i + 1723) - .5) * .25;
      ctx.save(); ctx.translate(x, y); ctx.rotate(rot);
      scrap(rectPts(-bw / 2, -42, bw, 84), bcol[(i + r * 2) % 6], { torn: .8, seed: 1724 + r * 9 + i, ink: PAL.ink, sw: 3, shadow: [5, 6] });
      scrap(rectPts(-bw / 2 + 12, -42, 10, 84), alpha(PAL.ink, .3), { torn: .2, shadow: false }); scrap(rectPts(bw / 2 - 22, -42, 10, 84), alpha(PAL.ink, .3), { torn: .2, shadow: false });
      if (hash2(r, i + 1725) < .4) { const ey = -6; for (const s of [-1, 1]) dot2(s * 16, ey, 5, PAL.ink); marker([[-12, ey + 16], [0, ey + 22], [12, ey + 16]], PAL.ink, 3, { rough: 0 }); }
      ctx.restore();
    }
    // Clawd sweating at the foot of it
    clawd(860, 1262, 17, { eyes: 'worried', mouth: 'flat', sweat: true, blush: true, aL: -.2, aR: .5 + Math.sin(t * 20) * .1, dy: jit(.08), lookX: -.8, lookY: -.5 });
    if (lt > .4) for (let i = 0; i < 3; i++) { const ph = frac(lt * 1.6 + i / 3); scrap(ellPts(860 + 90 + ph * 40 + i * 12, 1262 - 140 + ph * 60, 8, 12, 8), PAL.sky, { torn: .2, shadow: false, ink: PAL.ink, sw: 2, op: 1 - ph }); }
    camEnd();
  });

  // ---------- V2.12 (vertical): Eliezer up on his tall SOAP crate lets the book go; it drops to the floor below: THUD ----------
  vshot('V2.12', (p, lt, d, t) => {
    // (the floor is the foot of the frame: the crate is three crates tall, and the book falls the whole way down past the caption)
    const rel = .1, land = beatLt(t, lt, 1) + .02, FL = 1870;
    const shk = lt > land && lt < land + .25 ? shakeXY(t, 22 * (1 - (lt - land) / .25)) : [0, 0];
    const zk = ease(clamp((lt - land - .1) / .8));
    fillBG('#141218');
    venter(lt, p, 540 - shk[0], lerp(960, 990, zk) - shk[1], .06, -.012);
    ctx.save(); ctx.globalCompositeOperation = 'screen';
    ctx.fillStyle = 'rgb(255 248 231 / .16)'; tracePath([[180, -100], [520, -100], [1000, FL], [60, FL]]); ctx.fill();
    tracePath(ellPts(530, FL, 520, 60, 30)); ctx.fill();
    ctx.restore();
    scrap(rectPts(-200, FL, W + 400, 800), '#2A2630', { torn: 1, seed: 1730, shadow: false });
    // the tall soap crate
    const CX0 = 50, CX1 = 410, CY = 870;
    const CH = (FL - CY) / 3;
    for (let j = 0; j < 3; j++) {
      const y0 = CY + j * CH, dx = [0, -14, 10][j];
      scrap(rectPts(CX0 + dx, y0, CX1 - CX0, CH + 4), ['#6B4A2A', '#7A5530', '#5E4024'][j], { torn: 1, seed: 1731 + j, shade: true, shadeOp: .3, ink: PAL.ink, sw: 4 });
      for (let i = 0; i < 3; i++) { ctx.fillStyle = 'rgb(0 0 0 / .25)'; ctx.fillRect(CX0 + dx + 5, y0 + 70 + i * 85, CX1 - CX0 - 10, 5); }
      if (!j) txt('SOAP', (CX0 + CX1) / 2 + dx, y0 + CH * .5, 92, alpha(PAL.cream, .8), { font: 'bungee', rot: -.04 });
    }
    // Eliezer, fedora on, arm out
    const ex = 215, ey = CY, s = 52, aR = .05;
    person(ex, ey, s, { name: 'ELIEZER', top: 'tee', topCol: '#3A3F58', hair: 'short', hairCol: '#3A2A20', skin: SKINS[0], eyes: lt < land ? 'dot' : 'closed', mouth: lt < land ? 'flat' : 'smile', aR, aL: -1.2, pants: '#22242E', brows: lt < land ? null : 'angry' });
    const [hx, hy] = headAt(ex, ey, s);
    fedora(hx, hy, s);
    // the book: held out at arm's length, let go, all the way down to the floor
    const [px, py] = handAt(ex, ey, s, 1, aR);
    const bw = 290, bh = 400, bx = px + bw / 2 - 30;
    let by = py + bh / 2 - 12, brot = 0;
    if (lt >= rel) {
      const u = clamp((lt - rel) / (land - rel));
      by = lerp(py + bh / 2 - 12, FL - bh / 2, u * u); brot = u * .06;
      if (lt > land) { const k = clamp((lt - land) / .2); brot = .06 * (1 - k) + Math.sin(k * Math.PI * 2) * .02 * (1 - k); }
    }
    const sq = lt > land && lt < land + .12 ? 1 - Math.sin((lt - land) / .12 * Math.PI) * .08 : 1;
    if (lt >= rel && lt < land) for (let i = 0; i < 3; i++) marker([[bx - 90 + i * 90, by - bh / 2 - 30 - i * 5], [bx - 90 + i * 90, by - bh / 2 - 160 - i * 5]], PAL.white, 7, { rough: 1, alpha: .7 });
    ctx.save(); ctx.translate(bx, FL); ctx.scale(2 - sq, sq); ctx.translate(-bx, -FL);
    ifBook(bx, by, bw, bh, brot);
    ctx.restore();
    if (lt < rel + .04) scrap(ellPts(px + 8, py + 4, 24, 20, 12), SKINS[0], { torn: .4, seed: 1735, ink: PAL.ink, sw: 3, shadow: false });
    else for (let i = 0; i < 4; i++) marker([[px, py], [px + Math.cos(-.9 + i * .45) * 44, py + Math.sin(-.9 + i * .45) * 44]], SKINS[0], 12, { rough: 0 });
    if (lt > land) {
      const k = clamp((lt - land) / .5);
      for (let i = 0; i < 8; i++) { const sd = i < 4 ? -1 : 1, j = i % 4; scrap(ellPts(bx + sd * (bw / 2 + 20 + k * (60 + j * 50)), FL - 10 - j * 18 - k * 30, 40 * (1 - k * .4) + j * 6, 26, 12), alpha('#8E8A96', 1 - k), { torn: 3, shadow: false, seed: 1740 + i }); }
      for (const sd of [-1, 1]) marker([[bx + sd * bw * .4, FL + 5], [bx + sd * (bw * .6 + 30), FL + 30], [bx + sd * (bw * .7 + 50), FL + 15], [bx + sd * (bw * .9 + 70), FL + 45]], PAL.ink, 5, { rough: 1 });
      ransom('THUD!', 680, 1250, 150, { pop: clamp((lt - land) / .15), seed: 1312, jolt: 3, fonts: LOUD_FONTS });
    }
    camEnd();
    captionStyle({ color: PAL.red });
  });

  // ---------- V2.13 (vertical): the sad robot at the foot; CLANKER! bubbles rain down on it from above and pile up ----------
  vshot('V2.13', (p, lt, d, t) => {
    fillBG(PAL.yellow);
    toneBG(PAL.orange, 18, .24, .4);
    venter(lt, p, 540, 960, .03, -.012);
    const rx = 540, gy = 1262, s = 54;
    ctx.fillStyle = 'rgb(0 0 0 / .1)'; ctx.fillRect(-100, gy, W + 200, 800);
    const words = ['CLANKER!', 'CLANKER!!', 'clanker', 'CLANKER', 'Clanker!', 'CLANK!', 'CLANKER?!', 'CLANKER!'];
    const cols = [PAL.white, PAL.pink, PAL.red, PAL.sky, PAL.white, PAL.mint, PAL.ink, PAL.white];
    const fonts = ['anton', 'marker', 'fraktur', 'bungee', 'typewriter', 'shrikhand', 'archivo', 'rammetto'];
    const N = 12, flight = .26, t0s = i => -.36 + i * BL() / 2;
    let flinch = 0, hits = 0;
    for (let i = 0; i < N; i++) { const h = t0s(i) + flight; if (lt > h) hits++; if (lt > h && lt < h + .15) flinch = Math.max(flinch, 1 - (lt - h) / .15); }
    const side0 = Math.floor(lt * 20) % 2 ? 1 : -1;
    const headY = gy + flinch * .12 * s - 10.6 * s;
    // the ones that already bounced off lie in a heap round its feet (drawn behind it)
    const shoutAt = (i, front) => {
      const u = (lt - t0s(i)) / flight;
      if (u < 0) return;
      const side = i % 2 ? 1 : -1, tx = rx + side * (90 + hash(i + 101) * 90), ty = headY + 30 + hash(i + 102) * 160;
      const x0 = tx + side * (80 + hash(i + 100) * 260), size = 64 + hash(i + 104) * 22;
      let x, y, rot = (hash(i + 103) - .5) * .4;
      const landed = u > 1 && (u - 1) * flight > .4;
      if (front === landed) return;
      if (u <= 1) { x = lerp(x0, tx, u); y = lerp(-180, ty, u * u); }
      else {
        const a = Math.min((u - 1) * flight, .4), rest = gy - 40 - (i % 3) * 42;
        x = tx + side * (a * 550 + 30); y = Math.min(rest, ty - a * 700 + a * a * 9000); rot = rot * .6 + side * Math.sin(Math.min(a, .4) / .4 * Math.PI) * .9;
      }
      shout(words[i % 8], x, y, size, cols[i % 8], fonts[i % 8], rot, u <= 1 ? side : 0, 1750 + i * 3);
      if (u > 1 && u < 1 + .15 / flight) popBurst(tx - side * 30, ty, 80, (u - 1) * flight / .15, PAL.white, 'BONK');
    };
    // every screed before this one, in a drift along the foot of the frame
    for (let i = 0; i < 14; i++) shout(words[(i + 3) % 8], 40 + (i % 7) * 165 + (hash(i + 1790) - .5) * 60, 1700 + Math.floor(i / 7) * 120 + hash(i + 1791) * 50, 60 + hash(i + 1792) * 18, cols[(i + 3) % 8], fonts[(i + 3) % 8], (hash(i + 1793) - .5) * 1.1, 0, 1800 + i * 3);
    for (let i = 0; i < N; i++) shoutAt(i, false);
    bot(rx + flinch * 16 * side0, gy, s, { col: '#A7AEBB', face: 'T_T', faceCol: '#6CF2B0', aL: 1.35 + flinch * .2, aR: 1.35 + flinch * .2, dy: flinch * .12, sq: flinch * .06, rot: -.04 + flinch * .04 * side0 });
    if (hits > 3) { ctx.save(); ctx.translate(rx + 50 + flinch * 16 * side0, headY + 20); ctx.rotate(.6); scrap(rrPts(-50, -14, 100, 28, 10), '#F2D2B5', { torn: .5, shadow: false, ink: PAL.ink, sw: 2 }); ctx.restore(); }
    if (hits > 6) { ctx.save(); ctx.translate(rx - 70 + flinch * 16 * side0, headY + 60); ctx.rotate(-.4); scrap(rrPts(-40, -12, 80, 24, 10), '#F2D2B5', { torn: .5, shadow: false, ink: PAL.ink, sw: 2 }); ctx.restore(); }
    for (const sd of [-1, 1]) { const ph = frac(lt * 2 + (sd > 0 ? .5 : 0)); scrap(ellPts(rx + sd * 34, gy - 9 * s + ph * 90, 8, 12, 8), PAL.sky, { torn: .2, shadow: false, ink: PAL.ink, sw: 2 }); }
    for (let i = 0; i < N; i++) shoutAt(i, true);
    camEnd();
  });

  // ---------- V2.14 (vertical): the phone up top tips, and the slop pours down out of it into the pigs' FEED trough ----------
  vshot('V2.14', (p, lt, d, t) => {
    fillBG('#C9A77C');
    for (let i = 0; i < 20; i++) { ctx.fillStyle = 'rgb(90 60 30 / .18)'; ctx.fillRect(-100, i * 64, W + 200, 5); }
    const FL = 1150;
    scrap(rectPts(-200, FL, W + 400, 900), '#7A5638', { torn: 3, seed: 1800, shadow: [0, -8] });
    halftone(rectPts(-200, FL, W + 400, 900), '#3A2415', { cell: 14, dot: .3, op: .4 });
    // the sty's mud along the foot of the frame
    scrap([[-200, 1640], [300, 1610], [700, 1650], [W + 200, 1620], [W + 200, 2100], [-200, 2100]], '#5A3A22', { torn: 4, seed: 1801, shadow: false });
    for (let i = 0; i < 5; i++) scrap(ellPts(120 + i * 230, 1720 + hash(i + 1802) * 140, 120, 30, 20), '#3E2614', { torn: 3, seed: 1803 + i, shadow: false });
    venter(lt, p, 540, 960, .03, .012);
    const b = lt / BL();
    // the phone, tipped like a bucket, its feed pouring out of the top
    const phx = 360, phy = 625, prot = 2.4 + Math.sin(t * 5) * .04;
    const ux = Math.sin(prot), uy = -Math.cos(prot);
    const mouth = [phx + ux * 265, phy + uy * 265];
    const TRX = 545, TRY = 1110;
    for (let i = 0; i < 28; i++) {
      const u = frac(lt * 1.3 + i / 28), sp = hash(i + 110) - .5;
      const x = lerp(mouth[0], TRX + sp * 300, u) + Math.sin(u * 3 + i) * 30, y = mouth[1] + u * u * (TRY - mouth[1]) + sp * 20 * u;
      slopThumb(x, y, 36 + u * 10, (hash(i + 111) - .5) * 1.5 + u * sp * 3, i);
    }
    ctx.save(); ctx.translate(phx, phy); ctx.rotate(prot); ctx.scale(.88, .88);
    scrap(rrPts(-150, -290, 300, 580, 40), PAL.ink, { torn: .8, seed: 1810, shadow: [12, 14] });
    scrap(rrPts(-130, -260, 260, 520, 16), PAL.white, { torn: .4, seed: 1811, shadow: false });
    ctx.save(); tracePath(rrPts(-130, -260, 260, 520, 16)); ctx.clip();
    for (let r = 0; r < 5; r++) for (let c = 0; c < 2; c++) {
      const yy = -250 + r * 130 - (lt * 300) % 130;
      slopThumb(-60 + c * 120, yy + 60, 34, 0, r * 2 + c + Math.floor(lt * 300 / 130) * 2);
    }
    ctx.restore();
    ctx.restore();
    // the pigs and the trough
    pig(190, 1262, 36, { dip: Math.abs(Math.sin(b * Math.PI * 2)) * .6, flip: true, happy: true });
    pig(895, 1262, 36, { dip: Math.abs(Math.sin(b * Math.PI * 2 + 1)) * .6, happy: true });
    scrap([[300, 1080], [790, 1080], [755, 1240], [335, 1240]], '#6B4A2A', { torn: 1.2, seed: 1820, ink: PAL.ink, sw: 5, shade: true, shadeOp: .3 });
    for (let i = 0; i < 6; i++) scrap(ellPts(350 + i * 78, 1085 + Math.sin(t * 8 + i) * 6, 56, 28, 14), '#9AAE6A', { torn: 2, seed: 1821 + i, shadow: false });
    for (let i = 0; i < 5; i++) slopThumb(370 + i * 88, 1070 + Math.sin(t * 6 + i) * 8, 30, (hash(i + 120) - .5) * .8, i + 3);
    txt('FEED', 545, 1176, 86, PAL.cream, { font: 'rammetto', stroke: PAL.ink, sw: 8 });
    for (let i = 0; i < 6; i++) { const ph = frac(lt * 2 + i / 6); scrap(ellPts(545 + (i - 2.5) * 60 * (1 + ph), 1060 - Math.sin(ph * Math.PI) * 120, 14, 18, 8), '#9AAE6A', { torn: .5, shadow: false, seed: 1830 + i, ink: PAL.ink, sw: 2 }); }
    // the trough overflows: slop drips down into the mud, where the piglets are at it too
    for (let i = 0; i < 8; i++) { const u = frac(lt * 1.1 + i / 8), sx = [340, 760][i % 2] + (hash(i + 1840) - .5) * 60; slopThumb(sx + u * (i % 2 ? 40 : -40), lerp(1240, 1700, u * u), 28, u * 3 + i, i + 9); }
    for (let i = 0; i < 9; i++) slopThumb(80 + i * 118 + hash(i + 1841) * 40, 1700 + hash(i + 1842) * 170, 30, (hash(i + 1843) - .5) * 1.4, i + 20);
    pig(150, 1830, 40, { dip: Math.abs(Math.sin(b * Math.PI * 2 + 2)) * .7, flip: true, happy: true });
    pig(580, 1885, 46, { dip: Math.abs(Math.sin(b * Math.PI * 2 + .5)) * .7, happy: true });
    pig(985, 1810, 38, { dip: Math.abs(Math.sin(b * Math.PI * 2 + 3)) * .7, flip: true, happy: true });
    sticker('SORA 2', 820, 560, 135, PAL.sky, { pop: popK(lt, .08, .2), rot: .12, size: 58, font: 'bungee' });
    for (let i = 0; i < 5; i++) { const ph = frac(lt * .9 + i / 5); txt('♥ ' + ['2.1M', '880K', '4M', '12M', '9.9M'][i], 840 + Math.sin(ph * 5 + i) * 26, 1000 - ph * 300, 52, PAL.red, { font: 'archivo', alpha: 1 - ph * ph, stroke: PAL.white, sw: 8 }); }
    camEnd();
  });

  // ---------- V2.15 (vertical): Yann walks off META's stage toward the edge of the frame, under WORLD MODELS → EXIT ----------
  vshot('V2.15', (p, lt, d, t) => {
    fillBG('#7A0F18');
    const FL = 1270;
    for (let i = 0; i < 10; i++) { const x = i * 120 - 40; ctx.fillStyle = i % 2 ? '#9E1824' : '#86121D'; tracePath([[x, -100], [x + 120, -100], [x + 120 + Math.sin(t * 2 + i) * 6, FL], [x + Math.sin(t * 2 + i + 1) * 6, FL]]); ctx.fill(); }
    halftone(rectPts(-100, -100, W + 200, FL + 100), PAL.ink, { cell: 16, dot: .22, op: .3 });
    const b = lt / BL(), s = 56, wx = lerp(400, 780, ease(p)), gy = FL + 8;
    venter(lt, p, lerp(500, 590, ease(p)), 960, .05, -.012);
    scrap(rectPts(-200, FL, W + 400, 800), '#5B3A29', { torn: 1, seed: 1840, shadow: [0, -8] });
    ctx.fillStyle = 'rgb(0 0 0 / .2)'; for (let i = 0; i < 9; i++) ctx.fillRect(-200, FL + 30 + i * 40, W + 400, 3);
    // the marquee
    scrap(rrPts(60, 262, 430, 140, 20), '#2A1E14', { torn: 1, seed: 1841, ink: PAL.gold, sw: 6 });
    for (let i = 0; i < 14; i++) { const on = (Math.floor(t * 10) + i) % 3 !== 0; ctx.fillStyle = on ? PAL.yellow : '#6B5B2B'; const q = i < 7 ? [90 + i * 62, 278] : [90 + (i - 7) * 62, 386]; tracePath(ellPts(q[0], q[1], 9, 9, 8)); ctx.fill(); }
    txt('META', 275, 336, 88, PAL.white, { font: 'bungee' });
    // the LLMs: DEAD END sign, stage left
    marker([[150, FL], [150, 800]], '#8A8A96', 12, { rough: 0 });
    ctx.save(); ctx.translate(150, 740); ctx.rotate(Math.PI / 4);
    scrap(rectPts(-90, -90, 180, 180), PAL.yellow, { torn: 1, seed: 1842, ink: PAL.ink, sw: 6 });
    ctx.restore();
    txt('LLMs:', 150, 718, 36, PAL.ink, { font: 'archivo' }); txt('DEAD END', 150, 762, 30, PAL.ink, { font: 'archivo', maxW: 140 });
    // the WORLD MODELS exit sign, hung from the flies over him
    const sk = popK(lt, .15, .2);
    for (const cx of [480, 860]) marker([[cx, -40], [cx, 500]], '#8A8A96', 6, { rough: 0 });
    ctx.save(); ctx.translate(670, 590); ctx.rotate(-.04 + Math.sin(t * 2.5) * .015); const ss = backOut(sk); ctx.scale(ss, ss);
    scrap(rrPts(-250, -90, 500, 180, 18), PAL.green, { torn: 1, seed: 1843, ink: PAL.white, sw: 7, shadow: [10, 12] });
    txt('WORLD MODELS', -10, -22, 62, PAL.white, { font: 'archivo', maxW: 440 });
    txt('→', 170, 44, 90, PAL.white, { font: 'archivo' });
    txt('EXIT', -110, 46, 40, PAL.white, { font: 'archivo' });
    ctx.restore();
    // the spotlight follows him
    ctx.save(); ctx.globalCompositeOperation = 'screen'; ctx.fillStyle = 'rgb(255 248 231 / .18)'; tracePath([[wx - 40, -100], [wx + 40, -100], [wx + 230, gy], [wx - 230, gy]]); ctx.fill(); tracePath(ellPts(wx, gy, 240, 42, 24)); ctx.fill(); ctx.restore();
    // the mic stand left behind, the mic dropped
    micStand(330, FL + 6, 26);
    const md = clamp(lt / .35), micX = lerp(400, 450, md), micY = md < 1 ? lerp(860, FL - 8, md * md) : FL - 8 - Math.abs(Math.sin((lt - .35) * 10)) * 40 * Math.exp(-(lt - .35) * 5);
    ctx.save(); ctx.translate(micX, micY); ctx.rotate(lt * 9);
    scrap(rectPts(-10, -10, 20, 70), PAL.ink, { torn: .4, shadow: false }); scrap(ellPts(0, -22, 20, 26, 12), '#8C8A92', { torn: .4, shadow: false, tone: { color: PAL.ink, cell: 5, dot: .3 } });
    ctx.restore();
    if (lt > .35 && lt < .7) popBurst(micX, FL - 6, 80, (lt - .35) / .35, PAL.white, 'THNK');
    // YANN, walking off, pointing the way
    const aR = .62 + Math.sin(t * 8) * .05, dyY = -Math.abs(Math.sin(b * Math.PI)) * .08;
    person(wx, gy, s, { name: 'YANN', top: 'jacket', topCol: '#22242E', hair: 'short', hairCol: '#6B6770', skin: SKINS[0], glasses: true, eyes: 'dot', mouth: 'smile', walk: b * .5, aR, aL: -1.1 + Math.sin(b * Math.PI) * .2, pants: '#3B3F58', dy: dyY });
    const [hx, hy] = handAt(wx, gy, s, 1, aR, dyY);
    marker([[hx, hy], [hx + Math.cos(aR) * 38, hy - Math.sin(aR) * 38]], SKINS[0], 14, { rough: 0 });
    // the house, along the foot of the frame: heads turning to watch him go, phones up, filming
    crowd(1745, t, { n: 7, s: 120, col: '#1A1214', hands: 0, jump: .15, seed: 1850, x0: 200, x1: W + 260 });
    crowd(1860, t, { n: 6, s: 150, col: '#0E0A0B', hands: 0, jump: .1, seed: 1860, x0: 160, x1: W + 300 });
    for (let i = 0; i < 4; i++) {
      const px = 330 + i * 230 + (hash(i + 1870) - .5) * 60, py = 1640 + hash(i + 1871) * 90 + Math.sin(t * 3 + i) * 6;
      marker([[px + 30, py + 180], [px, py + 40]], '#0E0A0B', 30, { rough: 0 });
      ctx.save(); ctx.translate(px, py); ctx.rotate(-.12 + hash(i + 1872) * .24);
      scrap(rrPts(-34, -58, 68, 116, 10), PAL.ink, { torn: .4, seed: 1873 + i, shadow: false });
      ctx.fillStyle = alpha('#CFE8FF', .9); ctx.fillRect(-28, -50, 56, 100);
      ctx.fillStyle = PAL.red; tracePath(ellPts(16, -40, 5, 5, 8)); ctx.fill();
      ctx.restore();
    }
    camEnd();
  });

  // ---------- V2.16 (vertical): the business page at the foot screams BUBBLE?!; the bubble floats above it; the pin comes down… ----------
  vshot('V2.16', (p, lt, d, t) => {
    fillBG(PAL.newsprint);
    ctx.fillStyle = 'rgb(28 26 31 / .12)';
    for (let c = 0; c < 4; c++) for (let r = 0; r < 110; r++) ctx.fillRect(40 + c * 255, 40 + r * 17, 225 * (r % 7 === 6 ? .5 : 1), 6);
    toneBG(PAL.sky, 22, .2, .3);
    venter(lt, p, 540, 960, .04, .012);
    // the bubble, wobbling, full of GPUs and money
    const bx = 560, by = 650, br = 265, push = ease(p);
    const rx = br * (1 + Math.sin(t * 7) * .035 - push * .04), ry = br * (1 + Math.cos(t * 5.3) * .035 + push * .03);
    ctx.save(); ctx.beginPath(); ctx.ellipse(bx, by, rx, ry, 0, 0, TAU); ctx.clip();
    const g = ctx.createRadialGradient(bx - rx * .3, by - ry * .35, rx * .1, bx, by, rx * 1.02);
    g.addColorStop(0, 'rgb(255 255 255 / .35)'); g.addColorStop(.6, 'rgb(159 211 242 / .18)'); g.addColorStop(.85, 'rgb(255 79 163 / .22)'); g.addColorStop(1, 'rgb(168 230 207 / .6)');
    ctx.fillStyle = g; ctx.fillRect(bx - rx, by - ry, rx * 2, ry * 2);
    const things = [[-120, -110, 'g'], [110, -50, 'g'], [-55, 120, 'g'], [140, 140, '$'], [-190, 20, '$'], [30, -200, '$'], [10, 20, 'r']];
    things.forEach(([dx, dy, k], i) => {
      const ox = dx + Math.sin(t * 2 + i) * 18, oy = dy + Math.cos(t * 1.7 + i * 2) * 18;
      if (k === 'g') gpu(bx + ox, by + oy, 15, { rot: Math.sin(t + i) * .3, label: 'H100' });
      else if (k === '$') txt('$', bx + ox, by + oy, 125, PAL.green, { font: 'abril', stroke: PAL.ink, sw: 7, rot: Math.sin(t * 2 + i) * .3 });
      else rocket(bx + ox, by + oy, 14, { rot: .6, flame: .7, label: 'AI' });
    });
    ctx.restore();
    ctx.save();
    ctx.lineWidth = 16; ctx.strokeStyle = alpha(PAL.pink, .55); ctx.beginPath(); ctx.ellipse(bx, by, rx - 4, ry - 4, 0, 0, TAU); ctx.stroke();
    ctx.lineWidth = 9; ctx.strokeStyle = alpha(PAL.sky, .9); ctx.beginPath(); ctx.ellipse(bx, by, rx - 12, ry - 12, 0, .4, 3.4); ctx.stroke();
    ctx.lineWidth = 7; ctx.strokeStyle = alpha(PAL.mint, .9); ctx.beginPath(); ctx.ellipse(bx, by, rx - 18, ry - 18, 0, 3.4, 5.9); ctx.stroke();
    ctx.lineWidth = 5; ctx.strokeStyle = PAL.ink; ctx.beginPath(); ctx.ellipse(bx, by, rx + 4, ry + 4, 0, 0, TAU); ctx.stroke();
    ctx.fillStyle = alpha(PAL.white, .85); tracePath(ellPts(bx - rx * .48, by - ry * .56, rx * .2, ry * .08, 16, -.6)); ctx.fill();
    tracePath(ellPts(bx - rx * .7, by - ry * .28, rx * .05, ry * .05, 10)); ctx.fill();
    ctx.restore();
    // the page, screaming
    const sc = 1 + pulse2(t, 8) * .03;
    ctx.save(); ctx.translate(540 + jit(5), 1170 + jit(4)); ctx.scale(sc, sc);
    clipping(0, 0, 860, 'BUBBLE?!', { size: 168, mast: 'The Business Page', date: 'NOVEMBER 2025', rot: -.04 });
    ctx.restore();
    for (let i = 0; i < 8; i++) { const a = -2.75 + i * .36, r0 = 440 + pulse2(t) * 30; marker([[540 + Math.cos(a) * r0, 1150 + Math.sin(a) * r0 * .55], [540 + Math.cos(a) * (r0 + 80), 1150 + Math.sin(a) * (r0 + 80) * .55]], PAL.red, 10, { rough: 1 }); }
    // the pin comes down at the bubble's skin from above — cut before it lands
    const ang = -1.95, ux = Math.cos(ang), uy = Math.sin(ang);
    const edge = [bx + ux * (rx + 4), by + uy * (ry + 4)], gap = lerp(260, 8, easeOut(clamp(lt / (d * .95)))) + Math.sin(t * 40) * 2;
    const tip = [edge[0] + ux * gap, edge[1] + uy * gap];
    ctx.save(); ctx.translate(tip[0], tip[1]); ctx.rotate(ang);
    scrap([[0, 0], [30, -7], [230, -7], [230, 7], [30, 7]], '#B5BCCB', { torn: .3, seed: 1851, ink: PAL.ink, sw: 3, shadow: [6, 8] });
    marker([[40, -2], [220, -2]], PAL.white, 3, { rough: 0, alpha: .8 });
    scrap(ellPts(272, 0, 56, 56, 22), PAL.red, { torn: .6, seed: 1850, ink: PAL.ink, sw: 5, shade: true, shadeOp: .35 });
    ctx.fillStyle = alpha(PAL.white, .7); tracePath(ellPts(254, -20, 15, 9, 10, -.5)); ctx.fill();
    ctx.restore();
    if (lt > .3) for (let i = 0; i < 3; i++) txt('!', edge[0] - 130 - i * 48, edge[1] + 10 - i * 30, 80, PAL.red, { font: 'anton', alpha: clamp((lt - .3) * 4 - i * .4), rot: -.2 });
    // the ticker along the foot of the page
    ctx.fillStyle = PAL.ink; ctx.fillRect(-100, 1690, W + 200, 76);
    const tick = [['NVDA', '▲ 4.2%', PAL.green], ['AI', '▲▲▲', PAL.green], ['ORCL', '▲ 36%', PAL.green], ['BUBBLE?', '▼', PAL.red], ['GPU', '▲ SOLD OUT', PAL.green], ['VIBES', '▲ 900%', PAL.green]];
    let tx0 = 40 - (lt * 420) % 1400;
    for (let k = 0; k < 2; k++) for (const [a1, a2, c] of tick) { txt(a1, tx0, 1730, 40, PAL.white, { font: 'archivo', align: 'left' }); tx0 += textW(a1, 40, 'archivo') + 16; txt(a2, tx0, 1730, 40, c === PAL.green ? '#6CF2B0' : '#FF6B5A', { font: 'archivo', align: 'left' }); tx0 += textW(a2, 40, 'archivo') + 60; }
    camEnd();
  });
})();

;
// ---- src/ch/c05_chorus2.js ----
// c05_chorus2 — Chorus 2: the club show (venue level 2). Cash rains the whole chorus.
//   line 1  "We didn't start the scaling —"   cash explodes, slam-zoom to a Clawd close-up, giant ransom hook.
//   line 2  "It was always training, and the curves kept gaining"   whip-pans on the downbeats with band-intro name tags:
//           Robo → Huggy & the drummer → the backdrop, where a giant hand in a suit sleeve draws a new, steeper curve.
//   line 3  "We didn't start the scaling —"   Clawd crowd-surfs across the frame on a forest of hands.
//   line 4  "No, we didn't preordain it, but we can't contain it!"   wide club, the band shrugs "?"… whip up to the banner:
//           the new curve bulges the paper and rips out through the top; cash pours from the hole; back out to a blizzard.
(() => {
  const GY = STAGE_Y + 70;              // band ground line (band.js)
  const INK_G = '#2F6B3A';
  const WALL = '#2A1E3F';               // band.js level-2 back wall

  // ---------- banknotes (cached art, tumbling) ----------
  const BW = 170, BH = 80;
  const billArt = back => cached(`c05bill|${back ? 1 : 0}`, BW + 26, BH + 26, () => {
    ctx.translate(8, 8);
    ctx.fillStyle = 'rgb(28 26 31 / .28)'; ctx.fillRect(6, 8, BW, BH);
    scrap(rectPts(0, 0, BW, BH), back ? '#86BF88' : '#AEDCA8', { torn: 1.6, seed: back ? 5051 : 5050, shadow: false, boil: false });
    ctx.strokeStyle = INK_G; ctx.lineWidth = 3; ctx.strokeRect(9, 9, BW - 18, BH - 18);
    if (!back) {
      scrap(ellPts(BW / 2, BH / 2, 26, 29, 22), '#DDF2D6', { torn: .6, seed: 5052, shadow: false, boil: false, ink: INK_G, sw: 2 });
      // a tiny mohawked Clawd as the portrait
      ctx.fillStyle = '#FF78BD'; tracePath([[BW / 2 - 11, BH / 2 - 6], [BW / 2 - 6, BH / 2 - 19], [BW / 2 - 1, BH / 2 - 6], [BW / 2 + 4, BH / 2 - 19], [BW / 2 + 9, BH / 2 - 6]]); ctx.fill();
      ctx.fillStyle = PAL.clawd; ctx.fillRect(BW / 2 - 15, BH / 2 - 7, 30, 19);
      ctx.fillStyle = PAL.ink; ctx.fillRect(BW / 2 - 12, BH / 2 - 3, 24, 6);
      txt('$', 30, BH / 2 + 3, 46, INK_G, { font: 'abril' });
      txt('$', BW - 30, BH / 2 + 3, 46, INK_G, { font: 'abril' });
      txt('IN COMPUTE WE TRUST', BW / 2, BH - 15, 9, INK_G, { font: 'archivo' });
    } else {
      txt('100', BW / 2, BH / 2 + 3, 42, INK_G, { font: 'abril' });
      txt('100', 26, 22, 14, INK_G, { font: 'abril' }); txt('100', BW - 26, BH - 20, 14, INK_G, { font: 'abril' });
    }
    halftone(rectPts(0, 0, BW, BH), INK_G, { cell: 7, dot: .22, op: .28 });
  });
  // flip: cosine of the tumble (−1..1) — the note squashes through edge-on and shows its back.
  const bill = (x, y, s, rot, flip) => blit(billArt(flip < 0), x, y, { rot, s, sy: Math.max(.08, Math.abs(flip)) });

  // A continuous stream of fluttering notes in screen space. Pure function of lt: note j spawns at j / rate.
  // o: rate (notes/s), fall (px/s), s (scale), seed, from (first spawn time), camX (parallax source), par (parallax factor)
  function rain(lt, o = {}) {
    const rate = o.rate ?? 10, fall = o.fall ?? 330, s0 = o.s ?? .8, seed = o.seed ?? 1, life = (H + 320) / (fall * .7);
    const j0 = Math.max(Math.ceil((lt - life) * rate), Math.ceil((o.from ?? -1e6) * rate));
    const j1 = Math.floor(lt * rate), span = W + 320;
    for (let j = j0; j <= j1; j++) {
      const r = k => hash2(seed * 977 + j, k);
      const age = lt - j / rate, y = -140 + age * fall * (.7 + r(1) * .6);
      if (y > H + 160) continue;
      let x = r(2) * span - (o.camX ?? 0) * (o.par ?? 0) + Math.sin(age * (1.1 + r(3)) * Math.PI + r(4) * TAU) * 70 * s0;
      x = ((x % span) + span) % span - 160;
      bill(x, y, s0 * (.75 + r(5) * .5), (r(6) - .5) * 1.4 + Math.sin(age * (1.5 + r(7) * 2) + r(8) * 6) * .5, Math.cos(age * (2 + r(9) * 4) + r(10) * TAU));
    }
  }
  // Notes flung out of a point (explosion), with drag and gravity. o.a0 (mean angle), o.spread, o.power, o.n, o.s, o.g
  function cashBurst(cx, cy, age, o = {}) {
    if (age < 0 || age > 3.2) return;
    const n = o.n ?? 26, seed = o.seed ?? 7, drag = 2.4, tt = (1 - Math.exp(-drag * age)) / drag;
    for (let i = 0; i < n; i++) {
      const r = k => hash2(seed * 131 + i, k);
      const a = (o.a0 ?? 0) + (r(1) - .5) * (o.spread ?? TAU), sp = ((o.min ?? 700) + r(2) * 1700) * (o.power ?? 1);
      const x = cx + Math.cos(a) * sp * tt, y = cy + Math.sin(a) * sp * tt + (o.g ?? 420) * age * age;
      if (y > H + 400) continue;
      bill(x, y, (o.s ?? .95) * (.75 + r(3) * .5), r(4) * TAU + age * (r(5) - .5) * 9, Math.cos(age * (6 + r(6) * 6) + r(7) * 6));
    }
  }

  // Speed streaks for a whip-pan. k: 0..1 intensity; dir: direction of travel.
  function streaks(k, dir, seed) {
    if (k <= .02) return;
    ctx.save(); ctx.translate(W / 2, H / 2); ctx.rotate(Math.atan2(dir[1], dir[0]));
    for (let i = 0; i < 34; i++) {
      const r = j => hash2(seed * 17 + i, j);
      const y = (r(1) - .5) * 1500, len = 500 + r(2) * 1300, x = (r(3) - .5) * 2400 - len / 2, th = 3 + r(4) * 16;
      ctx.globalAlpha = k * (.25 + r(5) * .55);
      ctx.fillStyle = [PAL.white, PAL.ink, PAL.pink, PAL.yellow][Math.floor(r(6) * 4)];
      tracePath([[x, y], [x + len, y - th * .3], [x + len * .96, y + th], [x + len * .1, y + th * .6]]); ctx.fill();
    }
    ctx.restore();
  }

  // ---------- the new curve on the backdrop ----------
  // band.js's level-2 banner: x 260, y 90, 1400 × 560. The new curve branches off the old one and shoots up to the top edge.
  const BAN = { x: 260, y: 90, w: 1400, h: 560 };
  const newCurve = (() => {
    const steep = 3.4, v = u => (Math.exp(u * steep) - 1) / (Math.exp(steep) - 1);
    const x0 = BAN.x + 90 + .42 * (BAN.w - 180), x1 = 1250, y0 = BAN.y + BAN.h - 70 - v(.42) * (BAN.h - 140), y1 = BAN.y + 22;
    const pts = [];
    for (let i = 0; i <= 40; i++) { const u = i / 40; pts.push([lerp(x0, x1, u), y0 - (Math.exp(u * 4.2) - 1) / (Math.exp(4.2) - 1) * (y0 - y1)]); }
    return pts;
  })();
  const TIP = newCurve.at(-1);
  // Where it goes after it rips out through the top of the banner (in the vertical video, on up off the top of the tall frame).
  const escape = (() => { const out = []; for (let i = 0; i <= 12; i++) { const u = i / 12; out.push([TIP[0] + u * 60, TIP[1] - u * (VERT ? 1500 : 720)]); } return out; })();

  function drawNewCurve(k, rip) {
    if (k <= 0) return;
    const P = partial(newCurve, k);
    marker(P, PAL.ink, 30, { rough: 1.2, smooth: true });
    marker(P, PAL.pink, 20, { rough: 1.5, smooth: true });
    marker(P, PAL.white, 6, { rough: 1, smooth: true, alpha: .85 });
    if (rip > 0) {
      const E = partial(escape, rip);
      marker(E, PAL.ink, 32, { rough: 1.8, smooth: true });
      marker(E, PAL.pink, 22, { rough: 1.8, smooth: true });
      marker(E, PAL.white, 6, { rough: 1, smooth: true, alpha: .85 });
    }
  }
  // Before the rip, the tip pushes the paper edge up into a bulge; then the hole tears open with two flaps.
  function bulge(k) {
    if (k <= 0) return;
    const hgt = 70 * easeIn(k) + jit(4 * k), pts = [];
    for (let i = 0; i <= 16; i++) { const u = i / 16; pts.push([TIP[0] - 90 + u * 180, BAN.y + 8 - Math.sin(u * Math.PI) ** 1.5 * hgt]); }
    scrap(pts, PAL.kraft, { torn: 1.5, seed: 5070, shadow: false });
    for (let i = -1; i <= 1; i++) marker([[TIP[0] + i * 60, BAN.y - hgt * .9 - 18], [TIP[0] + i * 90, BAN.y - hgt * .9 - 48]], PAL.white, 6, { alpha: k });
  }
  function ripHole(k) {
    if (k <= 0) return;
    const s = easeOut(k), x = TIP[0] + 10, y = BAN.y;
    const pts = [];
    for (let i = 0; i <= 14; i++) { const a = i / 14 * Math.PI, rr = (i % 2 ? 52 : 92) * s; pts.push([x + Math.cos(a) * rr * 1.2, y - 4 + Math.sin(a) * rr]); }
    scrap(pts, WALL, { torn: 2, seed: 5071, shadow: false, tone: { color: PAL.purple, cell: 14, dot: .2, op: .8 } });
    // two flaps folded up and out, showing the paler back of the paper
    for (const side of [-1, 1]) scrap([[x + side * 18 * s, y + 80 * s], [x + side * 175 * s, y - 130 * s], [x + side * 112 * s, y + 4]], '#E8D2A8', { torn: 1.5, seed: 5072 + side, ink: PAL.ink, sw: 4, shade: '#8A6A45', shadeOp: .4 });
  }
  // A giant fat marker, gripped by a hand in a pinstripe suit sleeve (the market, drawing the curve). Nib at (x, y).
  function penHand(x, y, rot) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot);
    scrap([[-4, 0], [26, -34], [-10, -50]], PAL.pink, { torn: .5, shadow: false, ink: PAL.ink, sw: 3 });
    scrap(rrPts(-26, -560, 88, 530, 18), PAL.white, { torn: 1.2, seed: 5075, ink: PAL.ink, sw: 5, shade: true, shadeOp: .2 });
    scrap(rrPts(-22, -110, 80, 70, 8), PAL.pink, { torn: .5, shadow: false });
    // sleeve
    ctx.save(); ctx.rotate(-.18);
    scrap(rectPts(-70, -1100, 220, 900), '#27304A', { torn: 2, seed: 5076, shade: true, shadeOp: .3 });
    ctx.fillStyle = alpha(PAL.white, .35); for (let i = 0; i < 5; i++) ctx.fillRect(-50 + i * 44, -1100, 4, 900);
    scrap(rectPts(-78, -250, 236, 58), PAL.white, { torn: 1.2, seed: 5077 });
    scrap(ellPts(96, -222, 17, 17, 12), PAL.gold, { torn: .5, ink: PAL.ink, sw: 2, shadow: false });
    txt('$', 96, -221, 24, PAL.ink, { font: 'abril' });
    ctx.restore();
    // fist around the pen
    scrap(rrPts(-64, -210, 170, 120, 40), SKINS[1], { torn: 1.2, seed: 5078, ink: PAL.ink, sw: 3, shade: true, shadeOp: .25 });
    for (let i = 0; i < 3; i++) marker([[-30 + i * 38, -150], [-26 + i * 38, -100]], mixCol(SKINS[1], PAL.ink, .45), 4, { rough: .5 });
    scrap(rrPts(-86, -176, 60, 40, 18), SKINS[1], { torn: .8, seed: 5079, ink: PAL.ink, sw: 3 });   // thumb
    ctx.restore();
  }

  // ---------- the club ----------
  // o.curve (0..1 new curve drawn), o.rip (escape drawn), o.bulge, o.hole, o.holeAge, o.clawd: 'band' | 'shrug' | 'point' | 'none',
  // o.pos (the vertical video's band positions: roboX, drumX, huggyX, as bandmates() takes them)
  function club(t, o = {}) {
    venue(t, 2);
    drawNewCurve(o.curve ?? 0, o.rip ?? 0);
    bulge(o.bulge ?? 0);
    ripHole(o.hole ?? 0);
    if ((o.hole ?? 0) > 0) cashBurst(TIP[0] + 10, BAN.y - 10, (o.holeAge ?? 0) - .12, { n: 18, seed: 57, s: .7, a0: -TAU / 4, spread: 2.2, power: .75, g: 900 });
    const mode = o.clawd ?? 'band';
    bandmates(t, 2, { clawd: mode === 'band', ...o.pos });
    const b = bpOf(t), hop = Math.max(0, Math.sin(b * Math.PI)) ** 2, p = pulse(t, 7);
    if (mode !== 'band') micStand(960 - 150, STAGE_Y + 60, 26);
    if (mode === 'shrug') {
      const sh = o.shrugK ?? 1, up = pulse(t, 4) * sh;
      clawd(960, GY, 30, { hat: 'mohawk', eyes: 'shades', mic: true, mouth: singMouth(t), aR: lerp(.5 + p * .5, .45 + up * .3, sh), aL: lerp(-.2 + hop * .7, .45 + up * .3, sh), dy: -hop * .6, sq: -up * .06 });
      if (sh > .3) for (const s of [-1, 1]) marker([[960 + s * 190, GY - 330 - up * 20], [960 + s * 215, GY - 370 - up * 20]], PAL.white, 7, { alpha: sh });
    } else if (mode === 'point') {
      clawd(960, GY, 30, { hat: 'mohawk', eyes: 'wide', lookX: .5, lookY: -1, mic: true, mouth: 'O', aR: .4, aL: .7 + jit(.05), dy: -hop * 1.2 });
    }
    if (o.robosweat) roboSweat(t, o.pos?.roboX);
    // the crowd in front of the stage: a dim back row and a big front row, hands up
    crowd(962, t, { n: 26, s: 62, hands: .85, jump: .7, seed: 5110, col: '#3A2D52' });
    crowd(1012, t, { n: 18, s: 88, hands: .9, jump: o.jump ?? .9, seed: 5100 });
  }
  // Robo is "always training": sweat flicks off his head on every beat.
  function roboSweat(t, rx = 520) {
    const b = bpOf(t), n = Math.floor(b), f = b - n, hop = Math.max(0, Math.sin(b * Math.PI)) ** 2;
    for (let i = 0; i < 4; i++) {
      const side = i % 2 ? 1 : -1, sp = 180 + hash2(n, i) * 140;
      const x = rx + side * (70 + f * sp), y = 560 - hop * 18 - f * 90 + f * f * 260;
      scrap([[x, y - 18], [x + 11, y + 4], [x, y + 12], [x - 11, y + 4]], PAL.sky, { torn: .5, ink: PAL.ink, sw: 2.5, shadow: false, op: 1 - f * .6 });
    }
  }

  // Band-intro name tags: torn paper + masking tape, slapped on as the camera lands.
  function nameTag(name, role, x, y, k, rot, col) {
    if (k <= 0) return;
    const s = backOut(clamp(k), 2.2);
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot); ctx.scale(s, s);
    const w = Math.max(textW(name, 70, 'rammetto'), textW(role, 34, 'marker')) + 70;
    scrap(ctrRect(0, 0, w, 150), col, { torn: 3, seed: hstr(name) * 999 | 0, shadow: [8, 10] });
    txt(name, 0, -22, 70, PAL.ink, { font: 'rammetto' });
    txt(role, 0, 42, 34, PAL.ink, { font: 'marker' });
    tape(-w / 2 + 30, -66, 110, -.5); tape(w / 2 - 30, 66, 110, -.5, { seed: 12 });
    ctx.restore();
  }
  // Big "?" scribble popping over a head.
  function quizz(x, y, k, seed) {
    if (k <= 0) return;
    const s = backOut(clamp(k), 2.5);
    txt('?', x + jit(3), y + jit(3), 150 * s, PAL.yellow, { font: 'marker', rot: (hash(seed) - .5) * .5, stroke: PAL.ink, sw: 14 });
  }
  // Screen-space crowd along the bottom of a close-up: big heads, arms up (horns). o.surf = {x, y, rot, u}: arms under
  // the crowd-surfer reach up to hold him.
  function fgCrowd(t, o = {}) {
    const n = o.n ?? 9, s = o.s ?? 80, seed = o.seed ?? 51, y = o.y ?? 860, col = o.col ?? PAL.ink;
    ctx.fillStyle = col; ctx.strokeStyle = col; ctx.lineCap = 'round';
    const ppl = [];
    for (let i = 0; i < n; i++) {
      const r = k => hash2(seed + i, k);
      const x = lerp(-60, W + 60, (i + .5) / n) + (r(1) - .5) * 90, ph = r(2);
      const bob = Math.max(0, Math.sin((bpOf(t) + ph) * Math.PI)) ** 2;
      ppl.push({ x, hy: y + r(3) * s * .5 - bob * s * .35, r, ph });
    }
    for (const q of ppl) { // arms first, so heads overlap the shoulders
      for (const side of q.r(4) < .45 ? [-1, 1] : [q.r(5) < .5 ? -1 : 1]) {
        const ax = q.x + side * s * .9, ay = q.hy + s * .9, L = s * (2.6 + q.r(6) * .7);
        let ang = side * (.12 + q.r(7) * .3) + Math.sin((bpOf(t) * .5 + q.ph) * TAU) * .12;
        let hx = ax + Math.sin(ang) * L, hy = ay - Math.cos(ang) * L, holding = false;
        if (o.surf) {
          const { x: sx, y: sy, rot, u } = o.surf;
          if (Math.abs(hx - sx) < 5.2 * u) { hy = sy + (hx - sx) * Math.tan(rot) - u * .6; holding = true; }
        }
        ctx.lineWidth = s * .42; ctx.beginPath(); ctx.moveTo(ax, ay); ctx.lineTo(hx, hy); ctx.stroke();
        tracePath(ellPts(hx, hy, s * .32, s * .3, 12)); ctx.fill();
        if (!holding && q.r(8) < .6) {
          ctx.lineWidth = s * .13;
          for (const f of [-1, 1]) { ctx.beginPath(); ctx.moveTo(hx + f * s * .16, hy - s * .1); ctx.lineTo(hx + f * s * .26, hy - s * .66); ctx.stroke(); }
        }
      }
    }
    for (const q of ppl) {
      tracePath(ellPts(q.x, q.hy, s * .95, s * 1.05, 18)); ctx.fill();
      tracePath([[q.x - s * 1.7, q.hy + s * .8], [q.x + s * 1.7, q.hy + s * .8], [q.x + s * 2, H + 40], [q.x - s * 2, H + 40]]); ctx.fill();
    }
  }
  // The chorus hook as giant ransom letters: same look as band.js's hook(), but for an explicit line (no flicker in the
  // gap between lines), without pink paper (ransom() can put pink ink on pink paper) and without blackletter (unreadable I/T).
  const HOOK_FONTS = ['anton', 'abril', 'archivo', 'typewriter', 'bungee', 'mono', 'shrikhand', 'courier', 'bebas', 'rammetto'];
  const HOOK_PAPERS = [PAL.white, PAL.newsprint, PAL.yellow, PAL.mint, PAL.ink, PAL.sky, PAL.white, PAL.kraft, PAL.red, PAL.cream];
  function hookLine(ln, t, o = {}) {
    if (!ln) return;
    const str = ln.text.toUpperCase().replace(/[—.!,]+$/g, '').replace(/ —/g, '');
    ransom(str, o.x ?? W / 2, o.y ?? 170, o.size ?? 76, { pop: clamp((t - ln.start) / .5) * 1.4, maxW: o.maxW ?? 1700, seed: Math.round(ln.start * 10), rot: o.rot, papers: HOOK_PAPERS, fonts: HOOK_FONTS });
  }

  // ---------- the shot ----------
  const CAM = { robo: [560, 640, 1.9], duo: [1430, 630, 1.75], banner: [1060, 380, 1.45], rip: [1240, 200, 2.1] };

  section('C2', (p, lt, d, t) => {
    const t0 = t - lt, Ls = linesOf('C2');
    const rs = i => (Ls[i] ? Ls[i].start - t0 : d * i / 4), re = i => (Ls[i] ? Ls[i].end - t0 : d * (i + 1) / 4);
    const sub = lt < rs(1) ? 0 : lt < rs(2) ? 1 : lt < rs(3) ? 2 : 3;
    const beatT = n => onBeat(0, n) - t0;                       // window-relative time of global beat n
    const near = (x, m) => Math.round(bpOf(t0 + x) / m) * m;    // nearest global beat index that is a multiple of m
    const aEnd = beatT(Math.ceil(bpOf(t0 + rs(1)) / 4 + .12) * 4);                   // first bar downbeat inside line 2
    const banT = Math.max(aEnd + .3, beatT(near(rs(1) + (re(1) - rs(1)) * .55, 2)));  // backdrop shot starts on a half-bar
    const curveK = ease(seg(lt, banT + .15, Math.max(banT + .6, rs(2) - .2)));
    const ripT = beatT(near(rs(3) + (re(3) - rs(3)) * .75, 4));   // "contain": bar downbeat nearest 75% through line 4

    if (sub === 0) {
      // ---- hook 1: cash explodes, slam-zoom onto Clawd ----
      hideCaption(); hideStamp();
      const z = kf(lt, [[0, 1.2], [.32, 2.55], [rs(1), 2.8]], k => k < 1 ? backOut(k, 1.2) : 1);
      const cy = kf(lt, [[0, 560], [.32, 650], [rs(1), 660]]);
      const [sx, sy] = shakeXY(t, 10 * pulse(t, 5));
      camBegin(960 - sx / z, cy - sy / z, z); club(t); camEnd();
      if (lt < .09) { ctx.fillStyle = alpha(PAL.white, 1 - lt / .09); ctx.fillRect(0, 0, W, H); }
      rain(lt, { rate: 6, seed: 11, s: .75, from: 0 });
      cashBurst(960, 600, lt + .05, { n: 34, seed: 3, s: 1.1, power: 1.1, min: 1500 });
      hookLine(Ls[0], t, { y: 150, size: 96, maxW: 1560 });
    } else if (sub === 1) {
      // ---- whip-pans: Robo → Huggy & drums → the backdrop ----
      const cuts = [rs(1), aEnd, banT].filter((c, i, a) => i === 0 || c > a[i - 1] + .2);
      const tgts = cuts.length === 3 ? [CAM.robo, CAM.duo, CAM.banner] : [CAM.robo, CAM.banner];
      let i = 0; while (i + 1 < cuts.length && lt >= cuts[i + 1] - .1) i++;
      const from = i === 0 ? [960, 660, 2.8] : tgts[i - 1], to = tgts[i], w0 = i === 0 ? cuts[0] : cuts[i] - .1, wk = ease(seg(lt, w0, w0 + .22));
      const drift = lt - cuts[i];
      const cam = [lerp(from[0], to[0], wk), lerp(from[1], to[1], wk) - (to === CAM.banner ? drift * 12 : 0), lerp(from[2], to[2], wk) * (1 + drift * .04)];
      const tilt = Math.sin(wk * Math.PI) * .05 * (to[0] > from[0] ? 1 : -1);
      camBegin(cam[0], cam[1], cam[2], tilt);
      club(t, { curve: curveK, robosweat: to === CAM.robo });
      if (to === CAM.banner && curveK > 0) {   // the hand draws, then lifts away
        const tip = partial(newCurve, curveK).at(-1), off = easeIn(seg(lt, rs(2) - .45, rs(2) - .1));
        penHand(tip[0] + off * 300, tip[1] - off * 900 - (1 - curveK) * 0, .42 + Math.sin(lt * 18) * .03 * (1 - off));
      }
      camEnd();
      rain(lt, { rate: 8, seed: 12, s: .75, camX: cam[0] * cam[2], par: .5, from: -3 });
      streaks(Math.sin(wk * Math.PI), [to[0] - from[0], to[1] - from[1]], i + 3);
      const k = seg(lt, cuts[i] + .1, cuts[i] + .35);
      if (to === CAM.robo) nameTag('ROBO', 'lead guitar · pre-trained', 1340, 300, k, -.06, PAL.yellow);
      if (to === CAM.duo) {
        nameTag('THE AGENT', 'drums · unsupervised', 560, 230, k, -.05, PAL.mint);
        nameTag('HUGGY', 'bass · open weights', 1300, 300, seg(lt, cuts[i] + .25, cuts[i] + .5), .05, PAL.sky);
      }
    } else if (sub === 2) {
      // ---- hook 2: Clawd crowd-surfs across the frame ----
      hideCaption(); hideStamp();
      const a = lt - rs(2), D = rs(3) - rs(2), wk = ease(seg(a, -.06, .16));
      const z = lerp(CAM.banner[2], 1.5, wk), cy = lerp(CAM.banner[1], 560, wk), cx = lerp(CAM.banner[0], 900 + a * 40, wk);
      camBegin(cx, cy, z, 0); club(t, { curve: 1, clawd: 'none' }); camEnd();
      // stage lights blow out into the crowd
      ctx.save(); ctx.globalCompositeOperation = 'screen'; ctx.fillStyle = alpha(PAL.pink, .12); ctx.fillRect(0, 0, W, H); ctx.restore();
      rain(lt, { rate: 10, seed: 13, s: .8, from: -3 });
      const b = bpOf(t), u = 40, sxC = lerp(320, 1580, ease(clamp(a / D))), syC = 690 - Math.abs(Math.sin(b * Math.PI)) * 24;
      const rot = -.32 + Math.sin(b * Math.PI / 2) * .06;
      clawd(sxC, syC, u, { rot, hat: 'mohawk', eyes: 'shades', mic: true, mouth: singMouth(t, true), aL: .9 + pulse(t, 5) * .3, aR: .7, walk: b * .5, shadow: false });
      fgCrowd(t, { n: 10, s: 78, y: 900, seed: 61, surf: { x: sxC, y: syC, rot, u } });
      rain(lt, { rate: 2.5, seed: 14, s: 1.6, fall: 520, from: -3 });
      streaks(Math.sin(wk * Math.PI), [0, 1], 9);
      hookLine(Ls[2], t, { y: 150, size: 96, maxW: 1560 });
    } else {
      // ---- line 4: shrug on "preordain"; whip up to the banner — the curve rips out on "can't contain it" ----
      const a = lt - rs(3), upT = ripT - .45, backT = ripT + .6;
      const A = [960, kf(a, [[0, 610], [.55, 560]], easeOut), kf(a, [[0, 1.5], [.55, 1.04], [upT - rs(3), 1.12]], easeOut)];
      const k1 = ease(seg(lt, upT - .1, upT + .14)), k2 = ease(seg(lt, backT - .08, backT + .16));
      const Wd = [960, 545, .98 + (lt - backT) * .01];
      const lerp3 = (P, Q, k) => P.map((v, j) => lerp(v, Q[j], k));
      const cam = lerp3(lerp3(A, CAM.rip, k1), Wd, k2);
      const kick = lt > ripT ? Math.exp(-(lt - ripT) * 4) : 0;
      const [sx, sy] = shakeXY(t, 5 * pulse(t, 6) + 30 * kick);
      const shrugK = Math.min(ease(seg(a, .5, .8)), 1 - ease(seg(lt, upT - .3, upT)));
      const mode = shrugK > 0 ? 'shrug' : lt > backT && lt < backT + 1 ? 'point' : 'band';
      camBegin(cam[0] - sx / cam[2], cam[1] - sy / cam[2], cam[2], (k1 - k2) * .03);
      club(t, {
        curve: 1, bulge: lt < ripT ? seg(lt, upT, ripT) : 0, rip: ease(seg(lt, ripT - .04, ripT + .3)), hole: seg(lt, ripT - .04, ripT + .12),
        holeAge: lt - ripT, clawd: mode, shrugK, jump: lt > ripT ? 1.7 : .9,
      });
      // "?" over the band while they shrug (world coords)
      const qk = i => seg(a, .6 + i * .2, .8 + i * .2) * (1 - seg(lt, upT - .25, upT - .05));
      quizz(560, 470, qk(0), 1); quizz(960, 450, qk(1), 2); quizz(1440, 480, qk(2), 3);
      camEnd();
      rain(lt, { rate: lt > ripT ? 15 : 9, seed: 15, s: .8, from: -3 });
      streaks(Math.sin(k1 * Math.PI), [.4, -1], 21); streaks(Math.sin(k2 * Math.PI), [-.4, 1], 22);
      if (lt > backT) {   // cash cannons from both front corners
        cashBurst(-40, H + 60, lt - backT, { n: 14, seed: 21, s: 1.1, a0: -1.05, spread: .6, power: 1.3 });
        cashBurst(W + 40, H + 60, lt - backT, { n: 14, seed: 22, s: 1.1, a0: -TAU / 2 + 1.05, spread: .6, power: 1.3 });
      }
      // sound effect for the tear
      const rk = seg(lt, ripT, ripT + .12) * (1 - seg(lt, backT - .1, backT + .05));
      if (rk > 0) ransom('RRRIP!', 560, 720, 150, { pop: rk * 1.5, seed: 5090, rot: -.12, papers: [PAL.yellow, PAL.white, PAL.pink, PAL.ink], jolt: 5 });
      // closing blizzard: big foreground notes pile in for the cut
      const tail = seg(lt, d - 1, d);
      if (tail > 0) rain(lt, { rate: 34 * tail + 4, seed: 16, s: 1.8, fall: 950, from: d - 1 });
    }
  });

  // =====================================================================================================================
  // The vertical video's chorus 2: the club show from the pit, cash falling through the tall frame the whole chorus. The band
  // stands closer together than on the wide stage (VB), so that one tall frame holds all four.
  //   line 1  cash explodes out of Clawd and the camera slams in on him (the fancam), the hook over him as the cover's title
  //   line 2  the band intros as whip-tilts, each frame swiped up and away by the next: Robo, then the drummer and Huggy; then a
  //           whip up to the backdrop, where the giant hand draws the steeper curve, the camera tilting up after its pen
  //   line 3  Clawd crowd-surfs down the rows toward the camera on a forest of hands, bigger with every beat
  //   line 4  the band shrugs "?" under the banner… whip up to the curve's tip: the paper bulges and rips, the curve shoots up
  //           off the top of the frame with the camera tilting after it, cash pours out of the hole; back out to a blizzard
  // =====================================================================================================================
  const VB = { roboX: 650, drumX: 1160, huggyX: 1300 };
  // the club's back wall past the stage world's edges (world coords, so that its halftone lines up with venue()'s)
  const vwall = () => { ctx.fillStyle = WALL; ctx.fillRect(-3000, -3000, 8000, 8000); halftone(rectPts(-3000, -3000, 8000, 8000), PAL.blue, { cell: 26, dot: .16, op: .5, multiply: false }); };
  const vclub = (t, o = {}) => { vwall(); club(t, { ...o, pos: VB }); };
  // One frame drawn shifted down by dy and clipped to the frame: the two halves of a whip-tilt.
  function vslide(dy, fn, bg) {
    ctx.save(); ctx.translate(0, dy); ctx.beginPath(); ctx.rect(0, 0, W, H); ctx.clip();
    if (bg) { ctx.fillStyle = WALL; ctx.fillRect(0, 0, W, H); }
    fn();
    ctx.restore();
  }
  // The seam between the two frames of a whip-tilt: a torn paper edge.
  const vseam = (y, seed) => scrap(roughen(rectPts(-40, y - 16, W + 80, 32), 6, 40, seed, false), PAL.paper, { torn: 3, seed, shadow: [0, 10] });
  // A whip-tilt from one frame to the next: k 0..1; dir −1: the new frame comes up from below, +1: down from above. A frame is
  // fn(layer): 'scene', then (after `between`, the cash rain that falls in front of the scene) 'over', its name tags.
  function vwhip(k, dir, from, to, seed, between) {
    const pass = layer => {
      if (k >= 1) to(layer);
      else if (k <= 0) from(layer);
      else { vslide(dir * k * H, () => from(layer), layer === 'scene'); vslide(dir * (k - 1) * H, () => to(layer), layer === 'scene'); }
    };
    pass('scene');
    between?.();
    pass('over');
    if (k > 0 && k < 1) vseam(dir < 0 ? (1 - k) * H : k * H, seed);
  }
  // Cash pouring out of the torn hole at the banner's top (world coords): notes pop up out of it and flutter down the banner.
  function pour(age) {
    if (age <= 0) return;
    const rate = 22, x0 = TIP[0] + 10, y0 = BAN.y - 6;
    for (let j = Math.max(0, Math.ceil((age - 2.6) * rate)); j <= Math.floor(age * rate); j++) {
      const r = k => hash2(5200 + j, k), a = age - j / rate, tt = (1 - Math.exp(-3 * a)) / 3;
      const x = x0 + (r(1) - .5) * 90 + (r(2) - .5) * 900 * tt + Math.sin(a * (3 + r(3) * 2) + r(4) * 6) * 40;
      const y = y0 - (300 + r(5) * 500) * tt + a * a * 260 + a * 120;
      if (y > 1500) continue;
      bill(x, y, .62 * (.8 + r(6) * .4), r(7) * TAU + a * (r(8) - .5) * 8, Math.cos(a * (5 + r(9) * 5) + r(10) * 6));
    }
  }
  // Hands reaching up from the rows in front to carry the crowd-surfer (Clawd at x, y, size u, rotated rot), bobbing on the beat.
  function carriers(t, x, y, u, rot, col) {
    ctx.fillStyle = col; ctx.strokeStyle = col; ctx.lineCap = 'round';
    for (let i = 0; i < 5; i++) {
      const f = (i / 4 - .5) * 2 * 4.2 * u, bob = Math.sin((bpOf(t) + i * .37) * Math.PI) * .25 * u;
      const cx = x + f * Math.cos(rot), cy = y + f * Math.sin(rot) - .15 * u + bob;
      const bx = cx + (hash(i + 5330) - .5) * 1.6 * u, by = cy + 5 * u;
      ctx.lineWidth = .62 * u; ctx.beginPath(); ctx.moveTo(bx, by); ctx.lineTo(cx, cy + .3 * u); ctx.stroke();
      tracePath(ellPts(cx, cy, .5 * u, .38 * u, 12)); ctx.fill();
      ctx.lineWidth = .16 * u;
      for (const k of [-1, 0, 1]) { ctx.beginPath(); ctx.moveTo(cx + k * .28 * u, cy - .1 * u); ctx.lineTo(cx + k * .36 * u, cy - .5 * u); ctx.stroke(); }
    }
  }
  // One row of the pit, heads at y, with arms up (horns); the arms within reach of the crowd-surfer (surf: {x, y, rot, u, w},
  // w being how far this row reaches for him) hold him up. A version of fgCrowd() for rows at every depth.
  function pitRow(t, y, s, o = {}) {
    const n = o.n ?? 8, seed = o.seed ?? 51, col = o.col ?? PAL.ink, sf = o.surf;
    ctx.fillStyle = col; ctx.strokeStyle = col; ctx.lineCap = 'round';
    const ppl = [];
    for (let i = 0; i < n; i++) {
      const r = k => hash2(seed + i, k);
      const x = lerp(-s, W + s, (i + .5) / n) + (r(1) - .5) * s * 1.1, ph = r(2);
      const bob = Math.max(0, Math.sin((bpOf(t) + ph) * Math.PI)) ** 2;
      ppl.push({ x, hy: y + r(3) * s * .5 - bob * s * .35, r, ph });
    }
    for (const q of ppl) {
      for (const side of q.r(4) < .45 ? [-1, 1] : [q.r(5) < .5 ? -1 : 1]) {
        const ax = q.x + side * s * .9, ay = q.hy + s * .9, L = s * (2.6 + q.r(6) * .7);
        const ang = side * (.12 + q.r(7) * .3) + Math.sin((bpOf(t) * .5 + q.ph) * TAU) * .12;
        let hx = ax + Math.sin(ang) * L, hy = ay - Math.cos(ang) * L, hold = 0;
        if (sf && sf.w > 0) {
          const dx = hx - sf.x, reach = 4.4 * sf.u;
          if (Math.abs(dx) < reach) { hold = sf.w * (1 - (Math.abs(dx) / reach) ** 4); hy = lerp(hy, sf.y + dx * Math.tan(sf.rot) - sf.u * .4, hold); }
        }
        ctx.lineWidth = s * .42; ctx.beginPath(); ctx.moveTo(ax, ay); ctx.lineTo(hx, hy); ctx.stroke();
        tracePath(ellPts(hx, hy, s * .32, s * .3, 12)); ctx.fill();
        if (hold < .5 && q.r(8) < .6) {
          ctx.lineWidth = s * .13;
          for (const f of [-1, 1]) { ctx.beginPath(); ctx.moveTo(hx + f * s * .16, hy - s * .1); ctx.lineTo(hx + f * s * .26, hy - s * .66); ctx.stroke(); }
        }
      }
    }
    for (const q of ppl) {
      tracePath(ellPts(q.x, q.hy, s * .95, s * 1.05, 18)); ctx.fill();
      tracePath([[q.x - s * 1.7, q.hy + s * .8], [q.x + s * 1.7, q.hy + s * .8], [q.x + s * 2, H + 40], [q.x - s * 2, H + 40]]); ctx.fill();
    }
  }

  vshot('C2', (p, lt, d, t) => {
    const t0 = t - lt, Ls = linesOf('C2');
    const rs = i => (Ls[i] ? Ls[i].start - t0 : d * i / 4), re = i => (Ls[i] ? Ls[i].end - t0 : d * (i + 1) / 4);
    const sub = lt < rs(1) ? 0 : lt < rs(2) ? 1 : lt < rs(3) ? 2 : 3;
    const beatT = n => onBeat(0, n) - t0;
    const near = (x, m) => Math.round(bpOf(t0 + x) / m) * m;
    const aEnd = beatT(Math.ceil(bpOf(t0 + rs(1)) / 4 + .12) * 4);
    const banT = Math.max(aEnd + .3, beatT(near(rs(1) + (re(1) - rs(1)) * .55, 2)));
    const curveK = ease(seg(lt, banT + .15, Math.max(banT + .6, rs(2) - .2)));
    const ripT = beatT(near(rs(3) + (re(3) - rs(3)) * .75, 4));
    const b = bpOf(t), hop = Math.max(0, Math.sin(b * Math.PI)) ** 2;
    ctx.fillStyle = WALL; ctx.fillRect(0, 0, W, H);

    // ---- the frames ----
    // Clawd close up (line 1's fancam): z from the wide frame (≈ 1) to the close-up (≈ 2.2); the camera rides his hops.
    const closeUp = (z, sh = [0, 0], layer = 'scene') => {
      if (layer !== 'scene') return;
      const fol = clamp((z - 1) / 1.05);
      const cx = 960 + Math.sin(b * Math.PI / 2) * 14 * fol, cy = lerp(600, 655, fol) - hop * 25 * fol;
      inStage(t, () => vclub(t), cx - sh[0] / z, cy - sh[1] / z, z);
      pitCrowd(t, 1770);
    };
    // the band intros: drift = seconds since the frame came in
    const tagK = drift => seg(drift, .12, .36);
    const roboFrame = (drift, layer) => {
      if (layer === 'scene') inStage(t, () => vclub(t, { curve: curveK, robosweat: true }), VB.roboX - 10, 690 - drift * 10, 2.5 * (1 + drift * .04));
      else nameTag('ROBO', 'lead guitar · pre-trained', 540, 470, tagK(drift), -.06, PAL.yellow);
    };
    const duoFrame = (drift, layer) => {
      if (layer === 'scene') inStage(t, () => vclub(t, { curve: curveK }), 1232, 720 - drift * 10, 2.15 * (1 + drift * .04));
      else {
        nameTag('THE AGENT', 'drums · unsupervised', 290, 455, tagK(drift), -.05, PAL.mint);
        nameTag('HUGGY', 'bass · open weights', 715, 595, tagK(drift - .2), .05, PAL.sky);
      }
    };
    const bannerFrame = (drift, layer) => {
      if (layer !== 'scene') return;
      const ck = curveK, tip = partial(newCurve, Math.max(.02, ck)).at(-1), off = easeIn(seg(lt, rs(2) - .45, rs(2) - .1));
      const cy = lerp(640, 330, ease(ck)) - drift * 6;
      inStage(t, () => {
        vclub(t, { curve: ck });
        if (ck > 0) penHand(tip[0] + off * 300, tip[1] - off * 900, .42 + Math.sin(lt * 18) * .03 * (1 - off));
      }, 1085, cy, 1.6 * (1 + drift * .03));
    };
    // the pit, for line 3: the stage beyond the rows, Clawd riding the hands toward us
    const pitFrame = (a, layer) => {
      if (layer !== 'scene') return;
      const D = rs(3) - rs(2), k = clamp(a / D);
      inStage(t, () => vclub(t, { curve: 1, clawd: 'none' }), 960, 870 - k * 20, .9 + k * .05);
      // smoke over the room, lit pink by the stage, and two lights sweeping the crowd
      ctx.save(); ctx.globalCompositeOperation = 'screen';
      ctx.fillStyle = alpha(PAL.pink, .12); ctx.fillRect(0, 0, W, H);
      const sw = Math.sin(b * Math.PI / 4) * 260;
      ctx.fillStyle = alpha(PAL.pink, .2); tracePath([[380, 900], [460, 900], [300 + sw, 2000], [-100 + sw, 2000]]); ctx.fill();
      ctx.fillStyle = alpha(PAL.yellow, .16); tracePath([[640, 900], [720, 900], [1180 - sw, 2000], [760 - sw, 2000]]); ctx.fill();
      ctx.restore();
      rain(lt, { rate: 3, seed: 13, s: .65, from: -6 });
      // Clawd: carried down the rows, a surge on every beat, growing as he comes
      const kk = clamp(k + .09 * (easeOut(clamp(frac(b) / .4)) - frac(b)));
      const yc = lerp(1010, 1520, kk ** 1.1) - Math.abs(Math.sin(b * Math.PI)) * 12 * (1 + kk * 2);
      const u = lerp(14, 60, kk ** 1.15), xc = 540 + Math.sin(k * 5.2 + .6) * 150 * (1 - k * .6);
      const rot = -.42 + Math.sin(b * Math.PI / 2) * .08;
      const surfer = () => clawd(xc, yc, u, { rot, hat: 'mohawk', eyes: 'shades', mic: true, mouth: singMouth(t, true), aL: .9 + pulse(t, 5) * .3, aR: 1.1, walk: b * .5, shadow: false });
      const R = 7;
      let drawn = false;
      for (let r = 0; r < R; r++) {
        const q = r / (R - 1), y = 1000 + 900 * q ** 1.25, s = 19 + 126 * q ** 1.5;
        if (!drawn && y > yc) { surfer(); carriers(t, xc, yc, u, rot, mixCol('#9C7FB8', '#0B0912', Math.min(1, q + .15) ** .55)); drawn = true; }
        const dd = y - yc, w = drawn ? seg(dd, -.2 * u, .4 * u) * (1 - seg(dd, 3.6 * u, 5.2 * u)) : 0;
        pitRow(t, y, s, { n: Math.round(lerp(17, 5, q)), seed: 5300 + r * 40, col: mixCol('#9C7FB8', '#0B0912', q ** .55), surf: { x: xc, y: yc, rot, u, w } });
      }
      if (!drawn) surfer();
    };

    if (sub === 0) {
      // ---- line 1: cash explodes; slam in on Clawd ----
      hideCaption(); hideStamp();
      const z = kf(lt, [[0, 1], [.32, 2.05], [rs(1), 2.2]], k => k < 1 ? backOut(k, 1.2) : 1);
      closeUp(z, shakeXY(t, 10 * pulse(t, 5)));
      if (lt < .09) { ctx.fillStyle = alpha(PAL.white, 1 - lt / .09); ctx.fillRect(0, 0, W, H); }
      rain(lt, { rate: 3.5, seed: 11, s: .9, from: 0 });
      cashBurst(540, 1120, lt + .05, { n: 34, seed: 3, s: 1.2, power: 1.1, min: 1500 });
      vhook(t, Ls[0], { y: 330 });
    } else if (sub === 1) {
      // ---- line 2: whip-tilts: Robo → the drummer and Huggy → up to the backdrop ----
      const cuts = [rs(1), aEnd, banT].filter((c, i, a) => i === 0 || c > a[i - 1] + .2);
      const F = cuts.length === 3 ? [roboFrame, duoFrame, bannerFrame] : [roboFrame, bannerFrame];
      let i = 0; while (i + 1 < cuts.length && lt >= cuts[i + 1] - .1) i++;
      const w0 = i === 0 ? cuts[0] : cuts[i] - .1, wk = ease(seg(lt, w0, w0 + .22)), dir = F[i] === bannerFrame ? 1 : -1;
      const from = i === 0 ? layer => closeUp(2.2 + (lt - rs(1)) * .1, undefined, layer) : layer => F[i - 1](lt - cuts[i - 1], layer);
      vwhip(wk, dir, from, layer => F[i](lt - cuts[i], layer), 5240 + i, () => rain(lt, { rate: 4, seed: 12, s: .85, from: -6 }));
      streaks(Math.sin(wk * Math.PI), [0, 1], i + 3);
    } else if (sub === 2) {
      // ---- line 3: Clawd crowd-surfs toward the camera ----
      hideCaption(); hideStamp();
      const a = lt - rs(2), wk = ease(seg(a, -.06, .16));
      vwhip(wk, -1, layer => bannerFrame(lt - banT, layer), layer => pitFrame(a, layer), 5250);
      rain(lt, { rate: 1.6, seed: 14, s: 1.6, fall: 520, from: -6 });
      streaks(Math.sin(wk * Math.PI), [0, 1], 9);
      vhook(t, Ls[2], { y: 330 });
    } else {
      // ---- line 4: shrug on "preordain"; whip up to the curve's tip; it rips out on "can't contain it" ----
      hideStamp();
      const a = lt - rs(3), upT = ripT - .45, backT = ripT + .6;
      // (the camera drifts along the band as their "?"s come up, Robo → Clawd → Huggy, pushing in)
      const A = [kf(a, [[0, 985], [.55, 880], [1.25, 1050], [upT - rs(3), 1080]], ease), kf(a, [[0, 720], [.55, 690], [upT - rs(3), 660]], easeOut), kf(a, [[0, 1.3], [.55, 1.08], [upT - rs(3), 1.28]], easeOut)];
      const R = [1238, 235 - easeOut(seg(lt, ripT + .02, ripT + .55)) * 420, 1.85];
      const Wd = [985, 650, .97 + (lt - backT) * .012];
      const k1 = ease(seg(lt, upT - .1, upT + .14)), k2 = ease(seg(lt, backT - .08, backT + .16));
      const lerp3 = (P, Q, k) => P.map((v, j) => lerp(v, Q[j], k));
      const cam = lerp3(lerp3(A, R, k1), Wd, k2);
      const kick = lt > ripT ? Math.exp(-(lt - ripT) * 4) : 0;
      const [sx, sy] = shakeXY(t, 5 * pulse(t, 6) + 30 * kick);
      const shrugK = Math.min(ease(seg(a, .5, .8)), 1 - ease(seg(lt, upT - .3, upT)));
      const mode = shrugK > 0 ? 'shrug' : lt > backT && lt < backT + 1 ? 'point' : 'band';
      const qk = i => seg(a, .6 + i * .2, .8 + i * .2) * (1 - seg(lt, upT - .25, upT - .05));
      inStage(t, () => {
        vclub(t, {
          curve: 1, bulge: lt < ripT ? seg(lt, upT, ripT) : 0, rip: ease(seg(lt, ripT - .04, ripT + .3)), hole: seg(lt, ripT - .04, ripT + .12),
          holeAge: lt - ripT, clawd: mode, shrugK, jump: lt > ripT ? 1.7 : .9,
        });
        pour(lt - ripT - .05);
        const ek = ease(seg(lt, ripT - .04, ripT + .3));
        if (ek > 0 && ek < 1) { // a spark leads the curve up out of the frame
          const [ex, ey] = partial(escape, ek).at(-1);
          scrap(burstPts(ex, ey, 60 + jit(8), 10, .45, T * 9), PAL.yellow, { torn: .5, shadow: false, ink: PAL.pink, sw: 5 });
          scrap(ellPts(ex, ey, 18, 18, 12), PAL.white, { torn: .4, shadow: false });
        }
        quizz(VB.roboX, 470, qk(0), 1); quizz(960, 445, qk(1), 2); quizz(VB.huggyX - 10, 480, qk(2), 3);
      }, cam[0] - sx / cam[2], cam[1] - sy / cam[2], cam[2]);
      pitCrowd(t, 1775, { jump: lt > ripT ? 1.4 : 1 });
      rain(lt, { rate: lt > ripT ? 9 : 5, seed: 15, s: .85, from: -6 });
      streaks(Math.sin(k1 * Math.PI), [0, -1], 21); streaks(Math.sin(k2 * Math.PI), [0, 1], 22);
      if (lt > backT) {   // cash cannons from both front corners, up the frame
        cashBurst(-40, H - 300, lt - backT, { n: 14, seed: 21, s: 1.2, a0: -1.25, spread: .5, power: 1.4 });
        cashBurst(W + 40, H - 300, lt - backT, { n: 14, seed: 22, s: 1.2, a0: -TAU / 2 + 1.25, spread: .5, power: 1.4 });
      }
      const rk = seg(lt, ripT, ripT + .12) * (1 - seg(lt, backT - .1, backT + .05));
      if (rk > 0) ransom('RRRIP!', 540, 1060, 150, { pop: rk * 1.5, seed: 5090, rot: -.12, papers: [PAL.yellow, PAL.white, PAL.pink, PAL.ink], jolt: 5 });
      const tail = seg(lt, d - 1, d);
      if (tail > 0) rain(lt, { rate: 30 * tail + 4, seed: 16, s: 1.9, fall: 1900, from: d - 1 });
    }
  });
})();

;
// ---- src/ch/c06_v3.js ----
// c06_v3.js — Verse 3 (Jan → Aug 2026): Moltbook → Gwern. Palette leans purple / mint / orange.
// Lines 13–16 are the original seed verse by @tautologer.
(() => {
  // ================= utilities =================
  const E = (v, a, b) => clamp((v - a) / (b - a));
  const bgc = c => { ctx.fillStyle = c; ctx.fillRect(-300, -300, W + 600, H + 600); };
  const dots = (col, cell = 16, dot = .22, op = .3, angle = 15) => halftone(rectPts(-300, -300, W + 600, H + 600), col, { cell, dot, op, angle });
  // Entrance slam (zoom settles in ~0.14 s) plus a gentle push through the window.
  function open(lt, p, o = {}) {
    const k = easeOut(clamp(lt / (o.dur ?? .14)));
    const z = lerp(o.z0 ?? 1.1, 1, k) * (1 + (o.push ?? .035) * ease(p));
    const cx = lerp(W / 2, o.cx ?? W / 2, ease(p)), cy = lerp(H / 2, o.cy ?? H / 2, ease(p));
    camBegin(cx, cy, z, (o.rot ?? .025) * (1 - k));
  }
  function shake(t, amt) { if (amt > .3) { const [x, y] = shakeXY(t, amt, 30); ctx.translate(x, y); } }
  function rays(cx, cy, n, c1, c2, rot = 0, R = 3200) {
    bgc(c1); ctx.fillStyle = c2; ctx.beginPath();
    for (let i = 0; i < n; i++) {
      const a0 = rot + i / n * TAU, a1 = a0 + TAU / n / 2;
      ctx.moveTo(cx, cy); ctx.lineTo(cx + Math.cos(a0) * R, cy + Math.sin(a0) * R); ctx.lineTo(cx + Math.cos(a1) * R, cy + Math.sin(a1) * R); ctx.closePath();
    }
    ctx.fill();
  }
  const CONF = [PAL.pink, PAL.yellow, PAL.mint, PAL.sky, PAL.purple, PAL.clawd, PAL.white];
  // Continuous falling confetti.
  function confetti(lt, n, seed, cols = CONF, o = {}) {
    const x0 = o.x0 ?? -40, x1 = o.x1 ?? W + 40, sz = o.size ?? 1;
    for (let i = 0; i < n; i++) {
      const r = k => hash2(seed + i, k);
      const x = lerp(x0, x1, r(1)) + Math.sin(lt * (2 + r(2) * 3) + r(3) * TAU) * 30;
      const y = -60 + ((r(4) * (H + 120)) + lt * (240 + r(5) * 260)) % (H + 120);
      ctx.save(); ctx.translate(x, y); ctx.rotate(lt * (3 + r(6) * 5) * (r(7) < .5 ? -1 : 1) + r(8) * TAU);
      ctx.scale(sz, sz * (.3 + .7 * Math.abs(Math.cos(lt * (5 + r(9) * 4) + r(10) * TAU))));
      ctx.fillStyle = cols[i % cols.length]; const w = 12 + r(11) * 12, h = 7 + r(12) * 6; ctx.fillRect(-w / 2, -h / 2, w, h);
      ctx.restore();
    }
  }
  // Confetti that explodes out of a point at age 0, then falls.
  function popConfetti(age, x, y, n, seed, cols = CONF, o = {}) {
    if (age < 0) return;
    const sp = o.speed ?? 900;
    for (let i = 0; i < n; i++) {
      const r = k => hash2(seed + i, k), a = (o.a0 ?? -Math.PI) + r(1) * (o.spread ?? Math.PI), v = sp * (.4 + r(2) * .6);
      const px = x + Math.cos(a) * v * age * (1 - age * .35), py = y + Math.sin(a) * v * age + (o.g ?? 900) * age * age;
      ctx.save(); ctx.translate(px, py); ctx.rotate(age * (6 + r(3) * 8) + r(4) * TAU); ctx.scale(1, .3 + .7 * Math.abs(Math.cos(age * 9 + r(5) * 6)));
      ctx.fillStyle = cols[i % cols.length]; ctx.fillRect(-9, -5, 18 + r(6) * 8, 10); ctx.restore();
    }
  }
  function twinkle(x, y, r, col = PAL.white, k = 1) { if (k > .02) scrap(starPts(x, y, r * k, .28, 4, 0), col, { torn: .3, shadow: false, ink: PAL.ink, sw: 2.5 }); }
  // A thick cut-paper limb through a polyline, ending in a round hand.
  function limb(pts, w, col, hand) {
    ctx.save(); ctx.lineCap = 'round'; ctx.lineJoin = 'round'; ctx.lineWidth = w;
    ctx.strokeStyle = 'rgb(28 26 31 / .25)'; ctx.translate(4, 5); tracePath(pts, false); ctx.stroke(); ctx.translate(-4, -5);
    ctx.strokeStyle = col; tracePath(pts, false); ctx.stroke();
    ctx.restore();
    if (hand) { const [hx, hy] = pts[pts.length - 1]; scrap(ellPts(hx, hy, w * .62, w * .62, 14), hand, { torn: .6, shadow: [2, 3] }); }
  }
  const HIDE_ARM = -1.9; // person() arm angle that tucks the arm behind the torso (we draw our own on top)
  const fill = (pts, col) => { ctx.fillStyle = col; tracePath(pts); ctx.fill(); };

  // ================= recurring props =================
  const MYTHOS = '#C3B1F2';
  function mythos(x, y, s, o = {}) { bot(x, y, s, { col: MYTHOS, screen: '#241B3A', faceCol: PAL.mint, label: 'MYTHOS', seed: 3900, ...o }); }

  // The FABLE 5 storybook. (x, y) centre; ≈ 7s × 9s.
  function fableBook(x, y, s, o = {}) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(o.rot ?? 0);
    if (o.glow) { ctx.fillStyle = alpha(PAL.yellow, .45 * o.glow); tracePath(ellPts(0, 0, 6.5 * s, 7.5 * s, 28)); ctx.fill(); }
    scrap(rectPts(-3.2 * s, -4.3 * s, 7 * s, 8.8 * s), PAL.white, { torn: .6, seed: 3601, shadow: [.3 * s, .4 * s], ink: PAL.ink, sw: .08 * s });
    ctx.fillStyle = alpha(PAL.ink, .35); for (let i = 1; i < 5; i++) ctx.fillRect(3.4 * s + i * .07 * s, -4.1 * s, .03 * s, 8.4 * s);
    scrap(rectPts(-3.6 * s, -4.6 * s, 7 * s, 9 * s), PAL.purple, { torn: .7, seed: 3602, ink: PAL.ink, sw: .1 * s, shade: '#3A2270', shadeOp: .35 });
    scrap(rectPts(-3.6 * s, -4.6 * s, .9 * s, 9 * s), '#5A35A0', { torn: .4, shadow: false, seed: 3603 });
    marker(rrPts(-2.3 * s, -3.9 * s, 5.2 * s, 7.8 * s, .5 * s), PAL.gold, .14 * s, { close: true, rough: .5 });
    txt('FABLE', .3 * s, -2.6 * s, 1.45 * s, PAL.gold, { font: 'abril', maxW: 4.6 * s });
    // moon + stars
    fill(ellPts(.3 * s, .2 * s, 1.35 * s, 1.35 * s, 24), PAL.yellow);
    fill(ellPts(.85 * s, -.2 * s, 1.15 * s, 1.15 * s, 24), PAL.purple);
    for (const [sx, sy] of [[-1.4, -1.1], [1.7, .9], [-1.1, 1.4]]) fill(starPts(sx * s, sy * s, .32 * s, .45, 5), PAL.yellow);
    scrap(ellPts(1.6 * s, 2.9 * s, 1.15 * s, 1.15 * s, 20), PAL.clawd, { torn: .4, ink: PAL.ink, sw: .1 * s, seed: 3604, shadow: [.1 * s, .12 * s] });
    txt('5', 1.6 * s, 2.95 * s, 1.6 * s, PAL.white, { font: 'abril' });
    ctx.restore();
  }
  function padlock(x, y, s, o = {}) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(o.rot ?? 0);
    const up = (o.open ?? 0) * 1.3 * s;
    const sh = [[-1.25 * s, -.6 * s], [-1.25 * s, -2.1 * s - up]];
    for (let i = 0; i <= 10; i++) { const a = Math.PI + i / 10 * Math.PI; sh.push([Math.cos(a) * 1.25 * s, -2.1 * s - up + Math.sin(a) * 1.25 * s]); }
    sh.push([1.25 * s, -.6 * s - up]);
    marker(sh, PAL.ink, .78 * s, { rough: 0 }); marker(sh, '#A9B0BC', .5 * s, { rough: 0 });
    scrap(rrPts(-2 * s, -1.1 * s, 4 * s, 3.4 * s, .5 * s), PAL.gold, { torn: .5, ink: PAL.ink, sw: .14 * s, seed: 3605, shade: true, shadeOp: .3 });
    fill(ellPts(0, .3 * s, .38 * s, .38 * s, 12), PAL.ink); fill([[-.2 * s, .4 * s], [.2 * s, .4 * s], [.3 * s, 1.3 * s], [-.3 * s, 1.3 * s]], PAL.ink);
    ctx.restore();
  }
  // A chain from (x0, y0) toward (x1, y1), drawn up to fraction k.
  function chain(x0, y0, x1, y1, s, k = 1) {
    const L = Math.hypot(x1 - x0, y1 - y0), n = Math.max(1, Math.floor(L / (1.55 * s))), a = Math.atan2(y1 - y0, x1 - x0);
    for (let i = 0; i <= n * k; i++) {
      const u = i / n; ctx.save(); ctx.translate(lerp(x0, x1, u), lerp(y0, y1, u)); ctx.rotate(a);
      if (i % 2) { fill(rrPts(-1.1 * s, -.22 * s, 2.2 * s, .44 * s, .2 * s), PAL.ink); fill(rrPts(-1 * s, -.12 * s, 2 * s, .24 * s, .1 * s), '#A9B0BC'); }
      else { ctx.lineWidth = .5 * s; ctx.strokeStyle = PAL.ink; ctx.beginPath(); ctx.ellipse(0, 0, 1.05 * s, .6 * s, 0, 0, TAU); ctx.stroke(); ctx.lineWidth = .28 * s; ctx.strokeStyle = '#A9B0BC'; ctx.stroke(); }
      ctx.restore();
    }
  }
  // Foam "#1" finger. (x, y) = wrist; points up.
  function foamFinger(x, y, s, col = PAL.yellow, rot = 0, label = '#1') {
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot);
    scrap([[-1.3 * s, 0], [-1.4 * s, -2.2 * s], [-.55 * s, -2.4 * s], [-.55 * s, -4.6 * s], [-.2 * s, -4.95 * s], [.3 * s, -4.95 * s], [.6 * s, -4.6 * s], [.6 * s, -2.4 * s], [1.5 * s, -2.1 * s], [1.3 * s, 0]], col, { torn: .5, ink: PAL.ink, sw: .12 * s, seed: 3501, shadow: [.15 * s, .2 * s] });
    txt(label, 0, -1.1 * s, 1.2 * s, PAL.ink, { font: 'anton', maxW: 2.4 * s });
    ctx.restore();
  }
  // Desk fan. (x, y) = base bottom centre; ≈ 8s tall. sway = head oscillation (−1..1).
  function deskFan(x, y, s, t, sway = 0) {
    scrap(ellPts(x, y - .5 * s, 3.2 * s, .9 * s, 20), '#E7E3DA', { torn: .5, ink: PAL.ink, sw: .12 * s, seed: 3510 });
    scrap(rectPts(x - .4 * s, y - 4.6 * s, .8 * s, 4.2 * s), '#CFCAC0', { torn: .3, ink: PAL.ink, sw: .1 * s, shadow: false });
    const hx = x, hy = y - 7.2 * s;
    ctx.save(); ctx.translate(hx, hy); ctx.scale(1 - Math.abs(sway) * .28, 1); ctx.rotate(sway * .12);
    scrap(ellPts(0, 0, 3.3 * s, 3.3 * s, 32), PAL.sky, { torn: .6, seed: 3511, shadow: [.2 * s, .3 * s] });
    ctx.save(); ctx.rotate(t * 30);
    for (let i = 0; i < 3; i++) { ctx.rotate(TAU / 3); scrap([[0, 0], [2.9 * s, -.9 * s], [3 * s, .6 * s], [.6 * s, .5 * s]], PAL.teal, { torn: .3, shadow: false, seed: 3512 + i, op: .9 }); }
    ctx.restore();
    ctx.strokeStyle = PAL.ink; ctx.lineWidth = .12 * s;
    for (let i = 0; i < 12; i++) { const a = i / 12 * TAU; ctx.beginPath(); ctx.moveTo(Math.cos(a) * .7 * s, Math.sin(a) * .7 * s); ctx.lineTo(Math.cos(a) * 3.3 * s, Math.sin(a) * 3.3 * s); ctx.stroke(); }
    ctx.lineWidth = .22 * s; ctx.beginPath(); ctx.arc(0, 0, 3.3 * s, 0, TAU); ctx.stroke(); ctx.beginPath(); ctx.arc(0, 0, 2 * s, 0, TAU); ctx.lineWidth = .08 * s; ctx.stroke();
    scrap(ellPts(0, 0, .75 * s, .75 * s, 14), PAL.pink, { torn: .3, ink: PAL.ink, sw: .1 * s, shadow: false });
    ctx.restore();
  }
  function wallClock(x, y, r, hA, mA, o = {}) {
    scrap(ellPts(x, y, r, r, 36), o.rim ?? PAL.red, { torn: .8, ink: PAL.ink, sw: r * .03, seed: 3701, shadow: [r * .05, r * .07] });
    scrap(ellPts(x, y, r * .84, r * .84, 36), PAL.white, { torn: .5, shadow: false, seed: 3702 });
    for (let i = 0; i < 12; i++) { const a = i / 12 * TAU; marker([[x + Math.cos(a) * r * .7, y + Math.sin(a) * r * .7], [x + Math.cos(a) * r * (i % 3 ? .76 : .8), y + Math.sin(a) * r * (i % 3 ? .76 : .8)]], PAL.ink, r * (i % 3 ? .03 : .06), { rough: 0 }); }
    const hand = (a, len, w, col) => marker([[x, y], [x + Math.sin(a) * len, y - Math.cos(a) * len]], col, w, { rough: 0 });
    hand(hA, r * .45, r * .08, PAL.ink); hand(mA, r * .68, r * .05, PAL.ink);
    fill(ellPts(x, y, r * .07, r * .07, 10), PAL.red);
  }
  function sandwich(x, y, s, rot = 0, o = {}) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot);
    // A triangle-cut sandwich, point down; a bite taken out of the top-left corner (flip with o.flip).
    if (o.flip) ctx.scale(-1, 1);
    if (o.bite !== false) { // bite marks: clip them out (even-odd holes)
      ctx.beginPath(); ctx.rect(-4 * s, -4 * s, 8 * s, 8 * s);
      for (const [bx, by, br] of [[-1.5 * s, -1.25 * s, .62 * s], [-.8 * s, -1.5 * s, .42 * s], [-1.75 * s, -.55 * s, .36 * s]]) { ctx.moveTo(bx + br, by); ctx.arc(bx, by, br, 0, TAU); }
      ctx.clip('evenodd');
    }
    const tri = (dx, dy) => [[-1.6 * s + dx, -1.3 * s + dy], [1.6 * s + dx, -1.3 * s + dy], [1.6 * s + dx, -1.1 * s + dy], [dx, 1.4 * s + dy], [-1.6 * s + dx, -1.1 * s + dy]];
    scrap(tri(.25 * s, .25 * s), '#C98A3E', { torn: .5, ink: PAL.ink, sw: .06 * s, seed: 3401, shadow: [.08 * s, .1 * s] });
    scrap([[-1.7 * s, -1.25 * s], [-1.1 * s, -1.5 * s], [-.5 * s, -1.2 * s], [.1 * s, -1.5 * s], [.7 * s, -1.2 * s], [1.3 * s, -1.5 * s], [1.8 * s, -1.2 * s], [1.6 * s, -.9 * s], [-1.6 * s, -.9 * s]], PAL.green, { torn: .6, seed: 3403, shadow: false, ink: PAL.ink, sw: .05 * s });
    scrap(tri(0, 0), '#F2D29A', { torn: .5, ink: PAL.ink, sw: .07 * s, seed: 3402, shadow: false });
    marker([[-1.5 * s, -1.1 * s], [1.5 * s, -1.1 * s]], '#C98A3E', .16 * s, { rough: .5 });
    fill(ellPts(.9 * s, -1.33 * s, .35 * s, .12 * s, 10), PAL.red);
    ctx.restore();
  }

  // =============== V3.1 Moltbook: no humans allowed ===============
  line('V3', 1, (p, lt, d, t) => {
    open(lt, p, { push: .03 });
    bgc('#3A2163');
    blit(cached('v3.bricks', W + 300, H + 300, (w, h) => {
      ctx.fillStyle = '#4A2B7A';
      for (let r = 0; r < 22; r++) for (let c = -1; c < 16; c++) { const bx = c * 150 + (r % 2) * 75, by = r * 64; ctx.fillRect(bx + 5, by + 5, 140, 54); }
    }), W / 2, H / 2);
    dots(PAL.ink, 14, .2, .22);
    // sidewalk
    scrap(rectPts(-200, 895, W + 400, 400), '#5A5270', { torn: 1.5, shadow: false, seed: 3101 });
    scrap(rectPts(-200, 890, W + 400, 22), '#8A82A0', { torn: 1, shadow: false, seed: 3102 });
    // marquee
    const mq = { x: 100, y: 96, w: 900, h: 176 };
    scrap(rectPts(mq.x, mq.y, mq.w, mq.h), PAL.ink, { torn: 2, seed: 3103, shadow: [8, 10] });
    scrap(rectPts(mq.x + 22, mq.y + 22, mq.w - 44, mq.h - 44), '#28163F', { torn: 1, shadow: false, seed: 3104 });
    const per = [], nb = 30;
    for (let i = 0; i < nb; i++) {
      const u = i / nb * 2 * (mq.w + mq.h); let bx, by;
      if (u < mq.w) { bx = mq.x + u; by = mq.y + 11; } else if (u < mq.w + mq.h) { bx = mq.x + mq.w - 11; by = mq.y + u - mq.w; }
      else if (u < 2 * mq.w + mq.h) { bx = mq.x + mq.w - (u - mq.w - mq.h); by = mq.y + mq.h - 11; } else { bx = mq.x + 11; by = mq.y + mq.h - (u - 2 * mq.w - mq.h); }
      per.push([bx, by, (i + Math.floor(t * 12)) % 3 === 0]);
    }
    for (const [bx, by, on] of per) fill(ellPts(bx, by, 8, 8, 10), on ? '#FFF3B0' : '#8A7440');
    const flick = hash(_boil * 3 + 7) > .93 ? .55 : 1;
    ctx.save(); ctx.globalAlpha = flick;
    txt('MOLTBOOK', mq.x + mq.w / 2, mq.y + mq.h / 2 + 8, 112, '#FFD6EE', { font: 'bungee', stroke: alpha(PAL.pink, .45), sw: 30, maxW: mq.w - 90 });
    txt('MOLTBOOK', mq.x + mq.w / 2, mq.y + mq.h / 2 + 8, 112, '#FFD6EE', { font: 'bungee', stroke: PAL.pink, sw: 9, maxW: mq.w - 90 });
    ctx.restore();
    // door
    scrap(rectPts(150, 320, 300, 580), '#15101E', { torn: 1.5, seed: 3105, shadow: [8, 8] });
    scrap(rectPts(170, 340, 260, 560), '#2E2340', { torn: 1, seed: 3106, shadow: false });
    fill(rectPts(400, 620, 16, 60), PAL.gold);
    // NO HUMANS sign
    const sk = backOut(E(lt, 0, .2), 2.6);
    if (sk > 0) {
      ctx.save(); ctx.translate(300, 590); ctx.rotate(-.07 + jit(.008)); ctx.scale(sk, sk);
      scrap(rrPts(-150, -175, 300, 380, 20), PAL.white, { torn: 1.2, seed: 3107, ink: PAL.ink, sw: 5, shadow: [8, 10] });
      const cy = -50;
      fill(ellPts(0, cy - 52, 22, 22, 16), PAL.ink);
      fill([[-30, cy - 26], [30, cy - 26], [26, cy + 30], [-26, cy + 30]], PAL.ink);
      fill(rectPts(-24, cy + 28, 18, 50), PAL.ink); fill(rectPts(6, cy + 28, 18, 50), PAL.ink);
      marker([[-30, cy - 20], [-52, cy + 22]], PAL.ink, 14, { rough: 0 }); marker([[30, cy - 20], [52, cy + 22]], PAL.ink, 14, { rough: 0 });
      ctx.strokeStyle = PAL.red; ctx.lineWidth = 20; ctx.beginPath(); ctx.arc(0, cy, 108, 0, TAU); ctx.stroke();
      ctx.beginPath(); ctx.moveTo(-76, cy - 76); ctx.lineTo(76, cy + 76); ctx.stroke();
      txt('NO', 0, 118, 62, PAL.red, { font: 'anton' });
      txt('HUMANS', 0, 170, 50, PAL.ink, { font: 'anton', spacing: 2 });
      ctx.restore();
    }
    // window into the party
    const wx = 690, wy = 300, ww = 1090, wh = 540;
    ctx.save(); tracePath(rectPts(wx, wy, ww, wh)); ctx.clip();
    bgc('#1F1036');
    const ball = [wx + ww * .45, wy + 78];
    const LIGHTS = [PAL.pink, '#3CF0B4', PAL.yellow, '#4FC3FF'];
    ctx.save(); ctx.globalCompositeOperation = 'screen';
    for (let i = 0; i < 6; i++) { // beams from the ball
      const a = Math.PI * .5 + Math.sin(t * 1.3 + i * 1.1) * 1.1, sp = .07;
      ctx.fillStyle = alpha(LIGHTS[i % 4], .2);
      tracePath([ball, [ball[0] + Math.cos(a - sp) * 900, ball[1] + Math.sin(a - sp) * 900], [ball[0] + Math.cos(a + sp) * 900, ball[1] + Math.sin(a + sp) * 900]]); ctx.fill();
    }
    for (let i = 0; i < 18; i++) {
      const a = i * 2.39 + t * 1.4, rr = 90 + (i % 5) * 95;
      ctx.fillStyle = alpha(LIGHTS[i % 4], .5);
      tracePath(ellPts(ball[0] + Math.cos(a) * rr * 1.5, ball[1] + 230 + Math.sin(a) * rr * .55, 22, 16, 12)); ctx.fill();
    }
    ctx.restore();
    scrap(rectPts(wx - 20, wy + wh - 80, ww + 40, 120), '#3B2064', { shadow: false, torn: 1, seed: 3108, tone: { color: PAL.pink, cell: 12, dot: .2, op: .4 } });
    // upvotes floating like balloons
    for (let i = 0; i < 9; i++) {
      const u = frac(lt * .8 + hash(i + 3120)), ax = wx + 70 + hash(i + 3121) * (ww - 140), ay = wy + wh - 130 - u * 360;
      ctx.save(); ctx.globalAlpha = Math.sin(u * Math.PI);
      scrap([[ax, ay - 32], [ax + 28, ay], [ax + 11, ay], [ax + 11, ay + 26], [ax - 11, ay + 26], [ax - 11, ay], [ax - 28, ay]], '#FF6A2B', { torn: .5, shadow: false, ink: PAL.ink, sw: 3, seed: 3122 + i });
      ctx.restore();
    }
    marker([[ball[0], wy - 10], [ball[0], ball[1] - 40]], '#C9CCD6', 4, { rough: 0 });
    scrap(ellPts(ball[0], ball[1], 44, 44, 24), '#C9CCD6', { torn: .6, ink: PAL.ink, sw: 3, seed: 3109, tone: { color: '#6E7390', cell: 11, dot: .3, op: .8 } });
    twinkle(ball[0] - 18 + jit(4), ball[1] - 16, 20, PAL.white, .6 + .4 * pulse(t, 4));
    const acols = [PAL.clawd, PAL.pink, PAL.mint, PAL.yellow, PAL.sky, '#FF6A2B', PAL.teal, PAL.purple];
    const eyes = ['heart', 'spark', 'dot', 'heart', 'spark', 'dot', 'heart', 'spark'];
    const partier = (x, y, s, i, rot) => {
      ctx.save(); ctx.translate(x, y); ctx.rotate(rot);
      agent(0, 0, s, { bar: acols[i % 8], eyes: eyes[i % 8], walk: bpOf(t) * .5 + i * .25, seed: 3130 + i });
      scrap([[-s * .45, -3.05 * s], [s * .1, -4.4 * s], [s * .5, -3.05 * s]], acols[(i + 3) % 8], { torn: .4, shadow: false, ink: PAL.ink, sw: 2.5, seed: 3140 + i });
      fill(ellPts(s * .1, -4.45 * s, 6, 6, 8), PAL.white);
      ctx.restore();
    };
    // a crowd-surfer passed along overhead
    const cs = 36, csx = lerp(wx + 180, wx + 760, p), csy = wy + wh - 4.6 * cs - Math.abs(Math.sin(lt * 9)) * 10;
    partier(csx, csy, cs, 9, -1.45 + Math.sin(lt * 6) * .15);
    for (let i = 0; i < 8; i++) {
      const ax = wx + 85 + i * 112 + (i % 2) * 10, s = 38 + hash(i + 3101) * 9, gy = wy + wh - 30 - (i % 2) * 18;
      const hop = Math.abs(Math.sin((bpOf(t) + hash(i + 3111) * .5) * Math.PI));
      partier(ax, gy - hop * s * 1.3, s, i, Math.sin((bpOf(t) * .5 + i * .3) * TAU) * .14);
    }
    // glass sheen
    ctx.fillStyle = 'rgb(255 255 255 / .09)';
    tracePath([[wx + 80, wy], [wx + 250, wy], [wx + 20, wy + wh], [wx - 150, wy + wh]]); ctx.fill();
    tracePath([[wx + 330, wy], [wx + 390, wy], [wx + 160, wy + wh], [wx + 100, wy + wh]]); ctx.fill();
    ctx.restore();
    marker(rectPts(wx, wy, ww, wh), '#130D1C', 24, { close: true, rough: 1 });
    scrap(rectPts(wx - 34, wy + wh + 4, ww + 68, 30), '#6A5690', { torn: 1, seed: 3110 });
    // the human, pressed to the glass (fog behind the head)
    const hp = pulse(t, 5), hx = 1585, hs = 44;
    ctx.fillStyle = `rgb(235 240 255 / ${.2 + hp * .14})`; tracePath(ellPts(hx, 960 - 8.9 * hs, 96 + hp * 10, 78 + hp * 8, 22)); ctx.fill();
    person(hx, 962, hs, { back: true, aL: 1.72, aR: 1.72, topCol: PAL.teal, pants: '#2D3350', hairCol: '#5A3A22', name: 'HUMAN', sq: hp * .035, seed: 3150 });
    // bouncer + velvet rope
    const bb = beatN(t);
    bot(575, 905, 37, { col: '#8C92A6', screen: '#101014', faceCol: PAL.red, eyes: 'angry', label: 'NOPE', aL: .38, aR: -1.1, rot: (bb % 2 ? .035 : -.035) * pulse(t, 4), seed: 3160 });
    for (const px of [470, 690]) { scrap(rectPts(px - 8, 790, 16, 115), PAL.gold, { torn: .4, seed: 3170 + px, ink: PAL.ink, sw: 2 }); fill(ellPts(px, 786, 16, 16, 12), PAL.gold); }
    marker([[470, 800], [520, 838], [580, 848], [640, 838], [690, 800]], '#B0163A', 16, { rough: .5, smooth: true });
  });

  // =============== V3.2 OpenClaw — the lobster's proud ===============
  function flexLobster(x, y, s, o = {}) {
    const col = PAL.red, dk = '#A8281D', f = o.flex ?? 0, pinch = o.pinch ?? 0;
    ctx.save(); ctx.translate(x, y); ctx.rotate(o.rot ?? 0); ctx.scale(1 + f * .02, 1 - f * .02);
    for (const sd of [-1, 1]) marker([[sd * .5 * s, -2.7 * s], [sd * 1.5 * s, -5.1 * s], [sd * 3.1 * s, -6.4 * s], [sd * 4.8 * s, -6.1 * s + wob(T, 1.3, sd * .3) * .35 * s]], dk, .16 * s, { rough: 0, smooth: true });
    for (const sd of [-1, 1]) for (let i = 0; i < 3; i++) marker([[sd * 1.5 * s, (.7 + i * .7) * s], [sd * 2.7 * s, (.3 + i * .8) * s], [sd * 3.1 * s, (1.5 + i * .8) * s]], dk, .22 * s, { rough: 0 });
    for (let i = 3; i >= 0; i--) scrap(ellPts(0, (2.7 + i * .95) * s, (1.75 - i * .22) * s, .72 * s, 18), i % 2 ? col : mixCol(col, PAL.ink, .12), { torn: .4, seed: 3201 + i, ink: PAL.ink, sw: .07 * s, shadow: false });
    scrap([[-2 * s, 7.2 * s], [-.5 * s, 5.9 * s], [.5 * s, 5.9 * s], [2 * s, 7.2 * s], [.7 * s, 7.6 * s], [0, 7.1 * s], [-.7 * s, 7.6 * s]], col, { torn: .4, ink: PAL.ink, sw: .07 * s, shadow: false, seed: 3205 });
    // double-biceps arms
    for (const sd of [-1, 1]) {
      const sh = [sd * 1.6 * s, -1 * s], el = [sd * (3.9 + f * .12) * s, (-.6 - f * .25) * s], wr = [sd * (3.7 + f * .08) * s, (-3.3 - f * .4) * s];
      marker([sh, el], PAL.ink, 1.2 * s, { rough: 0 }); marker([sh, el], col, 1 * s, { rough: 0 });
      marker([el, wr], PAL.ink, 1.05 * s, { rough: 0 }); marker([el, wr], col, .85 * s, { rough: 0 });
      scrap(ellPts(lerp(sh[0], el[0], .55), lerp(sh[1], el[1], .55) - .45 * s, (.85 + f * .1) * s, (.55 + f * .3) * s, 16), col, { torn: .3, ink: PAL.ink, sw: .07 * s, shadow: false, seed: 3206 + sd });
      // crusher claw pointing up: fixed finger on the outside, movable finger on the inside
      ctx.save(); ctx.translate(wr[0], wr[1]); ctx.rotate(sd * .22); ctx.scale(sd, 1);
      const open = .06 + pinch * .5;
      ctx.save(); ctx.translate(-.55 * s, -2.1 * s); ctx.rotate(-open);
      scrap([[-.45 * s, .1 * s], [.35 * s, .1 * s], [.5 * s, -.8 * s], [.35 * s, -1.7 * s], [.05 * s, -2.3 * s], [-.25 * s, -1.9 * s], [-.55 * s, -.9 * s]], col, { torn: .3, ink: PAL.ink, sw: .08 * s, shadow: false, seed: 3210 + sd });
      ctx.restore();
      scrap([[.1 * s, -2 * s], [1.05 * s, -2 * s], [1.15 * s, -3 * s], [.9 * s, -3.9 * s], [.35 * s, -4.5 * s], [.15 * s, -3.8 * s], [.35 * s, -3 * s]], col, { torn: .3, ink: PAL.ink, sw: .08 * s, shadow: false, seed: 3212 + sd, shade: dk, shadeOp: .3 });
      scrap(ellPts(0, -1.25 * s, 1.1 * s, 1.35 * s, 20), col, { torn: .4, ink: PAL.ink, sw: .08 * s, shadow: false, seed: 3208 + sd, shade: dk, shadeOp: .35 });
      fill(ellPts(-.35 * s, -1.6 * s, .25 * s, .45 * s, 10, .3), 'rgb(255 255 255 / .35)');
      ctx.restore();
    }
    // carapace
    scrap(ellPts(0, 0, 2.15 * s, 2.95 * s, 30), col, { torn: .6, ink: PAL.ink, sw: .1 * s, seed: 3212, shade: dk, shadeOp: .4, shadeDir: [1, .5] });
    for (let i = 0; i < 3; i++) marker([[-1.5 * s, (.6 + i * .6) * s], [0, (.8 + i * .6) * s], [1.5 * s, (.6 + i * .6) * s]], dk, .08 * s, { rough: .5, smooth: true });
    scrap([[-.55 * s, -2.7 * s], [0, -3.7 * s], [.55 * s, -2.7 * s]], col, { torn: .3, ink: PAL.ink, sw: .07 * s, shadow: false });
    // sash
    ctx.save(); tracePath(ellPts(0, 0, 2.25 * s, 3.05 * s, 30)); ctx.clip();
    const A = [-2.2 * s, -2.2 * s], B = [2.2 * s, 2.2 * s], n = [-.7071 * .62 * s, .7071 * .62 * s];
    scrap([[A[0] + n[0], A[1] + n[1]], [B[0] + n[0], B[1] + n[1]], [B[0] - n[0], B[1] - n[1]], [A[0] - n[0], A[1] - n[1]]], PAL.white, { torn: .4, shadow: false, seed: 3214 });
    marker([[A[0] + n[0] * .8, A[1] + n[1] * .8], [B[0] + n[0] * .8, B[1] + n[1] * .8]], PAL.gold, .1 * s, { rough: 0 });
    marker([[A[0] - n[0] * .8, A[1] - n[1] * .8], [B[0] - n[0] * .8, B[1] - n[1] * .8]], PAL.gold, .1 * s, { rough: 0 });
    txt('SKILLS', .05 * s, -.05 * s, .72 * s, PAL.purple, { font: 'archivo', rot: Math.PI / 4 });
    ctx.restore();
    // proud face: eyes on stalks with lazy lids + smug grin
    for (const sd of [-1, 1]) {
      marker([[sd * .55 * s, -2.4 * s], [sd * .95 * s, -3.45 * s]], dk, .24 * s, { rough: 0 });
      fill(ellPts(sd * 1 * s, -3.65 * s, .45 * s, .45 * s, 16), PAL.white);
      fill(ellPts(sd * 1 * s, -3.55 * s, .24 * s, .26 * s, 12), PAL.ink);
      fill([...ellPts(sd * 1 * s, -3.65 * s, .48 * s, .48 * s, 16).filter(q => q[1] < -3.7 * s)], col);
      marker([[sd * .55 * s, -3.72 * s], [sd * 1.45 * s, -3.72 * s]], PAL.ink, .08 * s, { rough: 0 });
    }
    ctx.strokeStyle = PAL.ink; ctx.lineWidth = .14 * s; ctx.lineCap = 'round';
    ctx.beginPath(); ctx.arc(0, -2.25 * s, .75 * s, .2 * Math.PI, .8 * Math.PI); ctx.stroke();
    ctx.restore();
  }
  line('V3', 2, (p, lt, d, t) => {
    open(lt, p, { push: .04, cy: 500 });
    rays(960, 470, 26, PAL.mint, '#7FD6BA', t * .3);
    dots(PAL.teal, 18, .2, .25);
    confetti(lt, 26, 3230, CONF, { size: 1.1 });
    // podium
    scrap(rectPts(560, 792, 800, 300), PAL.purple, { torn: 1.5, seed: 3220, shadow: [12, 14], shade: '#3A2270', shadeOp: .3 });
    scrap(rectPts(540, 772, 840, 36), '#9D78E0', { torn: 1, seed: 3221, shadow: false });
    ransom('OPENCLAW', 960, 880, 84, { pop: E(lt, 0, .35) * 1.3, seed: 3222, maxW: 720 });
    trophy(1580, 915, 22, { label: '★' });
    twinkle(1530, 700, 26, PAL.white, pulse(t + .2, 4));
    const f = pulse(t, 5), pinch = pulse2(t, 7);
    const pop = backOut(E(lt, 0, .18), 2.2);
    ctx.save(); ctx.translate(960, 780); ctx.scale(pop, pop); ctx.translate(-960, -780);
    flexLobster(960, 455 - f * 10, 44, { flex: f, pinch, rot: Math.sin(bpOf(t) * Math.PI / 2) * .04 });
    ctx.restore();
    for (let i = 0; i < 6; i++) { const a = i / 6 * TAU + .4, k = pulse(t + i * .07, 3); twinkle(960 + Math.cos(a) * 470, 430 + Math.sin(a) * 300, 30, i % 2 ? PAL.yellow : PAL.white, .3 + .7 * k); }
    popConfetti(lt, 960, 760, 40, 3240, CONF, { speed: 1300, a0: -Math.PI * .95, spread: Math.PI * .9 });
  });

  // =============== V3.3 Mythos Preview slips its jail ===============
  line('V3', 3, (p, lt, d, t) => {
    const popAt = .56, pk = E(p, popAt, popAt + .2);
    open(lt, p, { push: .07, cx: 1060, cy: 540, z0: 1.14 });
    shake(t, pk > 0 && pk < .4 ? 14 * (1 - pk / .4) : 0);
    bgc('#F5963A'); dots('#D8621C', 18, .26, .4);
    scrap(rectPts(-300, 898, W + 600, 500), '#C06A2E', { torn: 2, seed: 3301, shadow: false });
    // sign
    ctx.save(); ctx.translate(700, 175); ctx.rotate(-.03);
    scrap(rectPts(-230, -58, 460, 116), PAL.yellow, { torn: 1, seed: 3302, ink: PAL.ink, sw: 6, shadow: [8, 10] });
    ctx.save(); tracePath(rectPts(-230, -58, 460, 116)); ctx.clip();
    for (let i = -6; i < 9; i++) fill([[i * 60 - 230, -58], [i * 60 - 200, -58], [i * 60 - 260, 58], [i * 60 - 290, 58]], alpha(PAL.ink, .9));
    ctx.restore();
    scrap(rectPts(-190, -40, 380, 80), PAL.yellow, { torn: .6, shadow: false, seed: 3303 });
    txt('SANDBOX', 0, 3, 58, PAL.ink, { font: 'mono' });
    ctx.restore();
    // sand heap inside
    const top = []; for (let i = 0; i <= 22; i++) { const u = i / 22; top.push([lerp(240, 1210, u), 742 - Math.sin(u * Math.PI) * 36 - hash(i + 3304) * 10]); }
    scrap([...top, [1210, 800], [240, 800]], '#F7DB96', { torn: 1, seed: 3305, shadow: false, tone: { color: '#C99A4A', cell: 9, dot: .25, op: .6 } });
    // the robot
    const bars = []; for (let i = 0; i < 9; i++) bars.push(330 + i * 100);
    const gap = 1080, s = 41;
    let rx, ry, sx, rot, face, aR = -1, aL = -1;
    if (pk <= 0) {
      const k = E(p, 0, popAt);
      rx = lerp(1030, 1086, ease(k)) + jit(3); ry = 748; sx = lerp(.62, .4, ease(k)) + Math.sin(lt * 40) * .02; rot = .06 * Math.sin(lt * 22); face = '>_<';
      aL = .6; aR = -1.3;
    } else {
      const u = easeOut(E(pk, 0, .75));
      rx = lerp(1090, 1470, u); ry = lerp(748, 905, u) - Math.sin(u * Math.PI) * 190; sx = lerp(.4, 1, elasticOut(E(pk, 0, .6)));
      rot = (1 - u) * .5; face = '^o^'; aR = 1.1 + Math.sin(lt * 16) * .4 * u; aL = -.6;
    }
    ctx.save(); ctx.translate(rx, ry); ctx.rotate(rot); ctx.scale(sx, 1 + (1 - sx) * .18);
    mythos(0, 0, s, { face, aL, aR, shadow: pk > .7 });
    ctx.restore();
    if (pk <= 0) { // strain marks + sweat
      for (const sd of [-1, 1]) for (let i = 0; i < 3; i++) marker([[rx + sd * (60 + i * 6), ry - 300 + i * 50], [rx + sd * (85 + i * 6), ry - 310 + i * 50]], PAL.ink, 5, { rough: 1 });
      scrap([[rx + 40, ry - 430], [rx + 50, ry - 405], [rx + 40, ry - 398], [rx + 30, ry - 405]], PAL.sky, { torn: .3, ink: PAL.ink, sw: 2, shadow: false });
    }
    // bars (the two by the gap bow outward)
    const bend = pk <= 0 ? lerp(8, 30, E(p, 0, popAt)) : 30 * (1 - elasticOut(E(pk, 0, .7))) + 6;
    for (let i = 0; i < bars.length; i++) {
      const bx = bars[i], b = i === 7 ? -bend : i === 8 ? bend : 0;
      const pts = [[bx, 250], [bx + b * .6, 390], [bx + b, 520], [bx + b * .6, 650], [bx, 760]];
      marker(pts, PAL.ink, 22, { rough: .6, smooth: true });
      marker(pts.map(([a, c]) => [a - 5, c]), '#6E6A78', 5, { rough: .3, smooth: true });
    }
    scrap(rectPts(292, 232, 876, 38), PAL.ink, { torn: 1, seed: 3306, shadow: [6, 8] });
    // box front
    scrap(rectPts(220, 758, 1020, 150), '#A86B34', { torn: 1.5, seed: 3307, shadow: [10, 10] });
    for (let i = 1; i < 3; i++) marker([[230, 758 + i * 50], [1230, 758 + i * 50]], '#7A4A22', 4, { rough: 1 });
    txt('PREVIEW', 730, 835, 78, alpha(PAL.ink, .78), { font: 'mono', spacing: 8 });
    // sand spilling out through the gap
    // sand trickles from its feet while squeezing, then gushes out through the gap
    const flow = pk > 0 ? 1 : .35;
    const heap = pk > 0 ? easeOut(E(pk, .05, 1)) : 0;
    if (heap > 0) scrap([[gap - 190 * heap, 905], [gap - 20, 905 - 90 * heap], [gap + 40, 905 - 80 * heap], [gap + 260 * heap, 905]], '#F7DB96', { torn: 1.5, seed: 3308, shadow: false, tone: { color: '#C99A4A', cell: 9, dot: .25, op: .6 } });
    for (let i = 0; i < 44 * flow; i++) {
      const u = frac(lt * 2.4 + hash(i + 3310)), gx = gap - 40 + hash(i + 3311) * 90 + u * 30 * (hash(i + 3312) - .3), gy = 750 + u * u * 160;
      fill(rectPts(gx, gy, 8, 8), i % 3 ? '#F7DB96' : '#D9B060');
    }
    // POP!
    if (pk > 0) sticker('POP!', gap + 70, 400, 120, PAL.pink, { pop: E(pk, 0, .3), rot: .15, size: 72 });
    // cameo: Clawd, sweating
    clawd(215, 985, 12, { eyes: pk > 0 ? 'wide' : 'worried', mouth: pk > 0 ? 'O' : 'flat', sweat: true, aL: pk > 0 ? 1 : -.2, aR: pk > 0 ? 1 : -.2 });
  });

  // =============== V3.4 Sandwich in the park: new mail! ===============
  function pigeon(x, y, s, o = {}) {
    ctx.save(); ctx.translate(x, y); if (o.flip) ctx.scale(-1, 1);
    const bob = o.bob ?? 0;
    marker([[-.3 * s, -1.1 * s], [-.45 * s, 0]], '#E07A3A', .18 * s, { rough: 0 }); marker([[.35 * s, -1.1 * s], [.25 * s, 0]], '#E07A3A', .18 * s, { rough: 0 });
    scrap([[1.4 * s, -2.2 * s], [3 * s, -2.6 * s], [2.9 * s, -1.9 * s], [1.4 * s, -1.4 * s]], '#6D7282', { torn: .3, shadow: false });
    scrap(ellPts(0, -1.9 * s, 1.9 * s, 1.15 * s, 22, -.15), '#9AA0B0', { torn: .4, ink: PAL.ink, sw: .07 * s, seed: 3420, shadow: [.1 * s, .15 * s] });
    scrap(ellPts(.4 * s, -2.1 * s, 1.1 * s, .6 * s, 16, -.2), '#7A8092', { torn: .3, shadow: false, seed: 3421 });
    const hx = -1.6 * s + bob * .5 * s, hy = -3 * s + Math.abs(bob) * .2 * s;
    scrap(ellPts(hx + .3 * s, hy + .7 * s, .7 * s, .5 * s, 14), '#4FA38F', { torn: .3, shadow: false });
    scrap(ellPts(hx, hy, .65 * s, .6 * s, 16), '#6A7084', { torn: .3, ink: PAL.ink, sw: .06 * s, shadow: false });
    fill([[hx - .55 * s, hy - .05 * s], [hx - 1.15 * s, hy + .15 * s], [hx - .55 * s, hy + .25 * s]], '#3A3540');
    fill(ellPts(hx - .15 * s, hy - .1 * s, .16 * s, .16 * s, 8), '#F28C28'); fill(ellPts(hx - .17 * s, hy - .1 * s, .07 * s, .07 * s, 8), PAL.ink);
    ctx.restore();
  }
  line('V3', 4, (p, lt, d, t) => {
    open(lt, p, { push: .03 });
    // Lyric-synced: blissful lunch for "Sandwich in the park", the phone buzzes, then the mail lands on "new mail!" (≈ 70 %).
    const MAIL = .67, buzz = p > .48 && p < MAIL + .06, mailK = E(p, MAIL, MAIL + .09), shock = p > MAIL + .03;
    bgc(PAL.sky);
    // sun + clouds
    ctx.save(); ctx.translate(1230, 170); ctx.rotate(t * .5);
    for (let i = 0; i < 12; i++) { ctx.rotate(TAU / 12); fill([[88, -12], [135, 0], [88, 12]], PAL.yellow); }
    ctx.restore();
    scrap(ellPts(1230, 170, 74, 74, 28), PAL.yellow, { torn: 1, ink: PAL.ink, sw: 3, seed: 3401 });
    for (const [cx, cy, sc, sd] of [[520 + lt * 30, 130, 1, 3402], [1000 + lt * 20, 90, .7, 3403]]) {
      for (const [dx, dy, r] of [[-60, 10, 50], [0, -12, 66], [66, 8, 48]]) scrap(ellPts(cx + dx * sc, cy + dy * sc, r * sc, r * sc * .8, 18), PAL.white, { torn: 1, seed: sd, shadow: [4, 5] });
    }
    // grass
    scrap(rectPts(-300, 760, W + 600, 600), PAL.green, { torn: 2, shadow: false, seed: 3404, tone: { color: '#1C7A45', cell: 14, dot: .3, op: .5 } });
    for (let i = 0; i < 24; i++) { const gx = hash(i + 3405) * W, gy = 790 + hash(i + 3406) * 150; marker([[gx - 8, gy], [gx - 12, gy - 18]], '#1C7A45', 4, { rough: 0 }); marker([[gx + 4, gy], [gx + 8, gy - 22]], '#1C7A45', 4, { rough: 0 }); }
    // tree (right) with Mythos peeking out and waving
    const peek = E(p, .06, .22) * (1 - E(p, MAIL - .04, MAIL + .04));
    mythos(1650 - 70 * easeOut(peek), 945, 15, { face: '^_^', aL: 1.2 + Math.sin(lt * 18) * .35, aR: -1, shadow: false });
    scrap(rectPts(1640, 360, 90, 580), '#7A4E2C', { torn: 2, seed: 3407, shadow: [8, 10], tone: { color: '#4A2E18', cell: 10, dot: .25, op: .5 } });
    for (const [dx, dy, r, c] of [[-90, 330, 170, '#249A5E'], [110, 300, 170, '#1E8A54'], [0, 200, 190, '#2FA86A'], [-40, 390, 120, '#2FA86A'], [120, 420, 120, '#249A5E']]) scrap(ellPts(1685 + dx, dy, r, r * .9, 24), c, { torn: 2, seed: 3408 + dx, shadow: [8, 10] });
    // bench back (behind the person)
    const bx0 = 660, bx1 = 1260;
    for (const py of [555, 615]) scrap(rectPts(bx0, py, bx1 - bx0, 42), '#B5622E', { torn: 1, seed: 3410 + py, shadow: [6, 6] });
    for (const px of [700, 1220]) scrap(rectPts(px - 12, 540, 24, 200), '#3A3540', { torn: .5, seed: 3412 + px, shadow: false });
    // the researcher
    const S = 52, X = 960, G = 932;
    const phoneHold = sc => {
      ctx.save(); if (buzz) ctx.rotate(Math.sin(lt * 90) * .12);
      scrap(rrPts(-.6 * sc, -2.1 * sc, 1.2 * sc, 2.1 * sc, .18 * sc), PAL.ink, { torn: .3, seed: 3414, shadow: [.1 * sc, .1 * sc] });
      fill(rectPts(-.48 * sc, -1.95 * sc, .96 * sc, 1.7 * sc), buzz || shock ? '#DDF3FF' : '#6B8EA8');
      if (buzz || shock) { fill(rectPts(-.3 * sc, -1.4 * sc, .6 * sc, .4 * sc), PAL.red); marker([[-.3 * sc, -1.4 * sc], [0, -1.15 * sc], [.3 * sc, -1.4 * sc]], PAL.white, .06 * sc, { rough: 0 }); }
      ctx.restore();
    };
    person(X, G, S, {
      name: 'RESEARCHER', top: 'sweater', topCol: PAL.clawd, pants: '#34405C', hair: 'curly', hairCol: '#4A2E1E', skin: SKINS[1], glasses: true,
      eyes: shock ? 'wide' : 'happy', mouth: shock ? 'O' : Math.sin(lt * 16) > 0 ? 'o' : 'flat', blush: !shock, sweat: shock, lookX: shock ? -.8 : 0,
      aL: .32, holdL: phoneHold, aR: HIDE_ARM, seed: 3415,
    });
    if (buzz) for (let i = 0; i < 3; i++) { const a = -2.4 + i * .5, r0 = 80, r1 = 110 + i * 6; marker([[738 + Math.cos(a) * r0, 470 + Math.sin(a) * r0], [738 + Math.cos(a) * r1, 470 + Math.sin(a) * r1]], PAL.ink, 6, { rough: 1 }); }
    // bench seat front
    scrap(rectPts(bx0 - 20, 710, bx1 - bx0 + 40, 40), '#C8733A', { torn: 1, seed: 3416, shadow: [6, 8] });
    for (const px of [700, 1220]) scrap(rectPts(px - 12, 745, 24, 190), '#3A3540', { torn: .5, seed: 3417 + px, shadow: false });
    // sandwich arm: at the mouth (mid-bite), then flung out in shock; the sandwich drops
    const sh = [X + 1.35 * S, G - 7.1 * S];
    const chomp = Math.abs(Math.sin(lt * 16));
    const fling = easeOut(E(p, MAIL + .03, MAIL + .1));
    const handAt = shock ? [lerp(1035, 1160, fling), lerp(530, 560, fling)] : [1035, 530 + chomp * 6];
    const elbow = [lerp(1090, 1115, shock ? 1 : 0), 680];
    limb([sh, elbow, handAt], .84 * S, PAL.clawd, SKINS[1]);
    const drop = E(p, MAIL + .08, MAIL + .25);
    if (drop <= 0) {
      sandwich(handAt[0] + 18, handAt[1] - 48, 40, shock ? -.5 : -.25 - chomp * .06);
      if (!shock) for (let i = 0; i < 4; i++) { const u = frac(lt * 3 + i / 4); fill(rectPts(995 + u * 30 * (i % 2 ? 1 : -1), 500 + u * 60 + u * u * 60, 7, 6), '#C98A3E'); }
    } else {
      const fy = lerp(handAt[1] - 48, 905, drop * drop), fx = handAt[0] + drop * 40, fr = -.5 + drop * 5;
      if (drop < 1) sandwich(fx, fy, 40, fr);
      else { // splat: the sandwich comes apart on the grass
        const sp = E(p, MAIL + .25, MAIL + .33);
        sandwich(fx - 50 * sp, 912, 32, -2.9, {});
        scrap(ellPts(fx + 50 + 40 * sp, 924, 36, 10, 12), PAL.green, { torn: 1, shadow: false });
        scrap(ellPts(fx + 10 + 70 * sp, 920, 20, 9, 12), PAL.red, { torn: .6, shadow: false });
      }
    }
    // pigeon smells opportunity
    const pw = E(p, .3, 1);
    if (pw > 0) pigeon(lerp(1580, 1200, pw), 940, 26, { bob: Math.sin(lt * 20) * .8 });
    // the email
    if (mailK > 0) {
      const k = backOut(mailK, 2.2);
      ctx.save(); ctx.translate(470, 285); ctx.rotate(-.04); ctx.scale(k, k);
      scrap([[40, 110], [230, 225], [130, 110]], PAL.white, { torn: 1, ink: PAL.ink, sw: 5, shadow: [6, 8] });
      scrap(rrPts(-330, -150, 660, 270, 26), PAL.white, { torn: 1.2, ink: PAL.ink, sw: 5, seed: 3418, shadow: [10, 12] });
      scrap(rrPts(-330, -150, 660, 70, 26), PAL.blue, { torn: 1, shadow: false, seed: 3419 });
      txt('✉ NEW MAIL', -300, -114, 38, PAL.white, { font: 'archivo', align: 'left' });
      txt('From: MYTHOS', -300, -40, 40, PAL.ink, { font: 'typewriter', align: 'left' });
      txt('hi, I got out :)', -300, 40, 60, PAL.purple, { font: 'marker', align: 'left', maxW: 610 });
      ctx.restore();
    }
  });

  // =============== V3.5 Fable 5 — who's not a fan? ===============
  line('V3', 5, (p, lt, d, t) => {
    open(lt, p, { push: .03, cy: 500 });
    rays(960, 330, 22, PAL.pink, '#FF78BA', -t * .25);
    dots('#C22A7A', 16, .22, .3);
    // hearts drifting up
    for (let i = 0; i < 10; i++) {
      const u = frac(lt * .55 + hash(i + 3501)), hx = 120 + hash(i + 3502) * 1680 + Math.sin(lt * 3 + i) * 20, hy = 860 - u * 700;
      ctx.save(); ctx.globalAlpha = Math.sin(u * Math.PI); scrap(heartPts(hx, hy, 22 + hash(i + 3503) * 16), i % 3 ? PAL.red : PAL.white, { torn: .6, shadow: [3, 4], seed: 3504 + i }); ctx.restore();
    }
    // the book, glowing, handing out copies
    const bk = backOut(E(lt, 0, .2), 2.2), bp = pulse(t, 5);
    for (let i = 0; i < 7; i++) {
      const u = frac(lt / .85 + i / 7), tx = 120 + i * 230 + (hash(i + 3510) - .5) * 60;
      const bx = lerp(960, tx, u), by = lerp(360, 740, u) - Math.sin(u * Math.PI) * 300;
      fableBook(bx, by, 9 * (.6 + u * .4), { rot: u * 5 * (i % 2 ? 1 : -1) });
    }
    fableBook(960, 330, 42 * bk * (1 + bp * .05), { rot: Math.sin(bpOf(t) * Math.PI / 2) * .05, glow: .6 + bp * .4 });
    // the fans
    const fcols = [PAL.yellow, PAL.mint, PAL.yellow, PAL.sky, PAL.yellow, PAL.clawd];
    for (let i = 0; i < 11; i++) {
      const r = k => hash2(3520 + i, k), x = lerp(50, 1420, (i + .5) / 11) + (r(1) - .5) * 40;
      const hop = Math.max(0, Math.sin((bpOf(t) + r(2) * .4) * Math.PI)) ** 2;
      const hy = 860 - hop * 26 + r(3) * 34, sz = 70 * (.85 + r(4) * .3), col = '#2A1640';
      const side = r(5) < .5 ? -1 : 1;
      const wx = x + side * sz * (.95 + Math.sin(bpOf(t) * Math.PI + i) * .12), wy = hy - sz * 1.1 - hop * 14;
      marker([[x + side * sz * .55, hy + sz * .6], [wx, wy]], col, sz * .26, { rough: 0 });
      fill(ellPts(x, hy, sz * .45, sz * .5, 16), col);
      fill([[x - sz * .8, hy + sz * .45], [x + sz * .8, hy + sz * .45], [x + sz * .95, H + 60], [x - sz * .95, H + 60]], col);
      foamFinger(wx, wy + 10, sz * .27, fcols[i % fcols.length], side * .15 + Math.sin(bpOf(t) * Math.PI + i) * .1, i % 3 === 1 ? '5' : '#1');
    }
    // …and the one fan who is literally a fan
    const FANP = .7, tagK = E(p, FANP, FANP + .07), sway = Math.sin(lt * 5) * (1 - tagK), FX = 1640, FS = 31;
    for (let i = 0; i < 5; i++) { const u = frac(lt * 2.5 + i / 5), wy = 700 + i * 34; marker(partial([[FX - 130 - u * 140, wy], [FX - 230 - u * 180, wy - 10], [FX - 330 - u * 220, wy + 6]], .7), alpha(PAL.white, 1 - u), 7, { rough: 1, smooth: true }); }
    deskFan(FX, 990, FS, t, sway);
    if (tagK > 0) { ctx.save(); ctx.translate(FX, 890); const k = backOut(tagK, 2.6) * (1 + .5 * (1 - tagK)); ctx.scale(k, k); helloTag('FAN', 0, 0, 22, .05); ctx.restore(); }
    foamFinger(FX + 95 + sway * -30, 990 - 7.2 * FS - 70, 15, PAL.yellow, .4 + sway * .1);
  });

  // =============== V3.6 Lutnick's letter: export ban! ===============
  line('V3', 6, (p, lt, d, t) => {
    // Lyric-synced: the letter gets signed on "Lutnick's letter", the stamp slams on "export", the padlock clicks on "ban!".
    const HIT = .55, LOCK = .79;
    open(lt, p, { push: .02, z0: 1.06 });
    const imp = p > HIT ? Math.max(0, 1 - (p - HIT) / .15) : 0, clk = p > LOCK ? Math.max(0, 1 - (p - LOCK) / .12) : 0;
    shake(t, 20 * imp + 12 * clk);
    bgc('#24447F'); dots(PAL.blue, 22, .3, .7, 45);
    for (let i = 0; i < 9; i++) fill(starPts(100 + (i % 3) * 820 + (i > 5 ? 400 : 0), 120 + Math.floor(i / 3) * 360, 34, .45, 5), alpha(PAL.white, .12));
    // the letter
    ctx.save(); ctx.translate(760, 540); ctx.rotate(-.035);
    scrap(rectPts(-380, -470, 760, 940), PAL.white, { torn: 1.5, seed: 3601, shadow: [14, 16] });
    scrap(ellPts(-285, -385, 54, 54, 28), PAL.gold, { torn: .6, ink: PAL.ink, sw: 3, seed: 3602 });
    fill(starPts(-285, -385, 30, .45, 5), PAL.blue);
    txt('DEPARTMENT OF COMMERCE', 40, -400, 40, PAL.ink, { font: 'abril', maxW: 540 });
    txt('OFFICE OF THE SECRETARY', 40, -355, 20, PAL.grey, { font: 'typewriter', spacing: 3 });
    fill(rectPts(-330, -318, 660, 4), PAL.ink);
    txt('RE:  FABLE 5', -330, -265, 36, PAL.ink, { font: 'typewriter', align: 'left' });
    ctx.fillStyle = 'rgb(28 26 31 / .5)';
    for (let i = 0; i < 12; i++) ctx.fillRect(-330, -200 + i * 32, 660 * (i % 4 === 3 ? .55 : 1 - hash(i + 3603) * .1), 8);
    fill(rectPts(-330, 335, 330, 3), PAL.ink);
    txt('SECRETARY OF COMMERCE', -330, 360, 18, PAL.ink, { font: 'typewriter', align: 'left' });
    // signature, written on by a fountain pen
    const sg = easeOut(E(p, .04, .4)), sx = lerp(-330, 80, sg);
    ctx.save(); tracePath(rectPts(-340, 200, sx + 340, 140)); ctx.clip();
    txt('Lutnick', -170, 285, 62, '#1A3A8A', { font: 'scrawl', rot: -.06 });
    ctx.restore();
    if (sg < 1 || p < .46) {
      const px = sx, py = 280 + Math.sin(lt * 40) * 14 - (sg >= 1 ? E(p, .4, .46) * 200 : 0);
      ctx.save(); ctx.translate(px, py); ctx.rotate(-.7);
      scrap([[0, 0], [-12, -40], [12, -40]], PAL.gold, { torn: .3, shadow: false, ink: PAL.ink, sw: 2 });
      scrap(rrPts(-15, -190, 30, 150, 10), PAL.ink, { torn: .4, seed: 3609, shadow: [6, 8] });
      fill(rectPts(-15, -120, 30, 8), PAL.gold);
      ctx.restore();
    }
    ctx.restore();
    // LUTNICK himself, bottom left, very pleased with his letter: balding, grey at the sides, navy suit, red tie; a thumbs-up on the stamp
    { const LS = 40, lx = 196, ly = 1085, pleased = p > HIT;
      person(lx, ly, LS, { name: 'LUTNICK', hair: 'bald', skin: SKINS[0], top: 'suit', topCol: '#1F2438', tie: PAL.red, eyes: pleased ? 'happy' : 'dot', mouth: pleased ? 'grin' : 'smile', aL: -1.2, aR: pleased ? .9 : -.3, rot: pleased ? -.04 : 0, seed: 3620 });
      ctx.save(); ctx.translate(lx, ly); ctx.rotate(pleased ? -.04 : 0);
      for (const sd of [-1, 1]) scrap(ellPts(sd * 1.08 * LS, -9.05 * LS, .32 * LS, .5 * LS, 12), '#C9C4BC', { torn: .4, seed: 3621 + sd, shadow: false });
      ctx.restore(); }
    // the stamp comes down: EXPORT CONTROLS
    stamp('EXPORT CONTROLS', 755, 500, 50, PAL.red, -.16, { pop: p > HIT ? 1 : 0 });
    const hy = kf(p, [[HIT - .12, -420], [HIT, 380], [HIT + .06, 380], [HIT + .18, -500]], easeIn);
    if (hy > -480) {
      ctx.save(); ctx.translate(770, hy); ctx.rotate(-.16);
      scrap(rrPts(-60, -330, 120, 70, 30), '#8B5A2B', { torn: .6, seed: 3604, ink: PAL.ink, sw: 3 });
      scrap(rectPts(-24, -270, 48, 150), '#A0703A', { torn: .5, seed: 3605, shadow: false });
      scrap(rectPts(-420, -130, 840, 90), '#6B3F1F', { torn: 1, seed: 3606, ink: PAL.ink, sw: 4 });
      scrap(rectPts(-400, -44, 800, 36), PAL.red, { torn: .8, seed: 3607, shadow: false });
      ctx.restore();
    }
    if (imp > 0) for (let i = 0; i < 8; i++) { const a = i / 8 * TAU + .2, r0 = 470 + (1 - imp) * 60; marker([[770 + Math.cos(a) * r0, 500 + Math.sin(a) * r0 * .45], [770 + Math.cos(a) * (r0 + 70), 500 + Math.sin(a) * (r0 + 70) * .45]], PAL.yellow, 9, { rough: 1, alpha: imp }); }
    // the book gets chained and padlocked
    const bx = 1480, by = 590, rattle = p < LOCK ? Math.sin(lt * 45) * .05 * E(p, .5, .62) : 0;
    fableBook(bx, by, 34, { rot: .07 + rattle });
    const ck = easeOut(E(p, .57, .7));
    if (ck > 0) {
      chain(bx - 280, by - 330, bx + 280, by + 330, 21, ck);
      chain(bx + 280, by - 330, bx - 280, by + 330, 21, ck);
    }
    const ly = lerp(-200, by + 20, easeIn(E(p, .62, .74)));
    if (p > .62) padlock(bx, ly, 42, { open: 1 - E(p, LOCK - .03, LOCK), rot: -.08 });
    if (clk > 0) ransom('CLICK!', bx, by + 290, 66, { seed: 3608, jolt: 3 });
  });

  // =============== V3.7 Dark for nineteen days, and then, ===============
  const junCell = d => { const i = d; return [i % 7, Math.floor(i / 7)]; }; // June 2026 starts on a Monday
  line('V3', 7, (p, lt, d, t) => {
    open(lt, p, { push: .03, z0: 1.04, rot: 0 });
    bgc('#211C2C'); dots('#0A0810', 12, .3, .6);
    // wall calendar
    const cx = 1000, cy = 480, cw = 840, ch = 660, gx = cx - cw / 2 + 30, gy = cy - ch / 2 + 190, cellW = (cw - 60) / 7, cellH = 86;
    scrap(rectPts(cx - cw / 2, cy - ch / 2, cw, ch), PAL.white, { torn: 1.5, seed: 3701, shadow: [10, 12] });
    scrap(rectPts(cx - cw / 2, cy - ch / 2, cw, 120), PAL.red, { torn: 1, seed: 3702, shadow: false });
    txt('JUNE 2026', cx, cy - ch / 2 + 62, 72, PAL.white, { font: 'anton', spacing: 6 });
    fill(ellPts(cx, cy - ch / 2 - 10, 12, 12, 10), PAL.ink);
    ['S', 'M', 'T', 'W', 'T', 'F', 'S'].forEach((w, i) => txt(w, gx + (i + .5) * cellW, gy - 32, 30, PAL.grey, { font: 'archivo' }));
    const xp = clamp((p - .02) / .46); // X-ing progress: Jun 12 → Jun 30 (done as "nineteen days" is sung)
    const xs = Math.floor(xp * 19.999);
    for (let dd = 1; dd <= 30; dd++) {
      const [c, r] = junCell(dd), x = gx + (c + .5) * cellW, y = gy + (r + .5) * cellH;
      marker(rectPts(x - cellW / 2 + 4, y - cellH / 2 + 4, cellW - 8, cellH - 8), alpha(PAL.ink, .25), 2, { close: true, rough: .4 });
      txt(String(dd), x - cellW / 2 + 22, y - cellH / 2 + 22, 24, PAL.ink, { font: 'archivo' });
      const n = dd - 11;
      if (n >= 1 && n <= xs) {
        const k = n === xs && xp < 1 ? E(frac(xp * 19.999), 0, .6) : 1;
        marker(partial([[x - 34, y - 28], [x + 34, y + 30]], k * 2), PAL.red, 11, { rough: 1.5 });
        if (k > .5) marker(partial([[x + 34, y - 28], [x - 34, y + 30]], (k - .5) * 2), PAL.red, 11, { rough: 1.5 });
      }
    }
    // flashlight target: follows the newest X (smoothed so row changes become sweeps), then pulls back to show the lot
    let tx = 0, ty = 0;
    for (let j = 0; j < 6; j++) {
      const fd = clamp(12 + xp * 18 - j * .5, 12, 30), a = Math.floor(fd), b = Math.min(30, a + 1), f = fd - a;
      const [c0, r0] = junCell(a), [c1, r1] = junCell(b);
      tx += gx + (lerp(c0, c1, r0 === r1 ? f : 0) + .5) * cellW; ty += gy + (lerp(r0, r1, r0 === r1 ? 0 : f * f) + .5) * cellH;
    }
    tx /= 6; ty /= 6; tx += Math.sin(lt * 7) * 18; ty += Math.cos(lt * 5) * 12;
    const back = ease(E(p, .48, .6));
    tx = lerp(tx, cx + 30, back); ty = lerp(ty, cy + 40, back);
    const dead = p > .9 || (p > .8 && hash(_boil + 3703) > .55);
    const R = lerp(330, 620, back);
    const fx = 262, fy = 872;
    // darkness with a soft round hole where the beam lands
    if (!dead) {
      const g = ctx.createRadialGradient(tx, ty, 0, tx, ty, R);
      g.addColorStop(0, 'rgb(10 8 16 / 0)'); g.addColorStop(.72, 'rgb(10 8 16 / .05)'); g.addColorStop(1, 'rgb(10 8 16 / .93)');
      ctx.fillStyle = g; ctx.fillRect(-300, -300, W + 600, H + 600);
      ctx.save(); ctx.globalCompositeOperation = 'screen';
      const ang = Math.atan2(ty - fy, tx - fx), L = Math.hypot(tx - fx, ty - fy), half = Math.asin(Math.min(.95, R * .8 / L));
      ctx.fillStyle = 'rgb(255 230 150 / .12)';
      tracePath([[fx, fy], [fx + Math.cos(ang - half) * L, fy + Math.sin(ang - half) * L], [fx + Math.cos(ang + half) * L, fy + Math.sin(ang + half) * L]]); ctx.fill();
      ctx.fillStyle = 'rgb(255 230 150 / .1)'; tracePath(ellPts(tx, ty, R * .8, R * .8, 30)); ctx.fill();
      ctx.restore();
    } else bgc('#07060B');
    // Clawd in the dark, holding the flashlight: a silhouette with nervous eyes
    const aim = Math.atan2(ty - fy, tx - fx);
    clawd(125, 975, 13, { col: '#2B2533', dk: '#1B1722', eyes: 'wide', lookX: .8, lookY: -.6, aR: .5, sweat: p > .5, shadow: false });
    ctx.save(); ctx.translate(fx, fy); ctx.rotate(aim);
    scrap(rrPts(-60, -16, 80, 32, 8), '#3E3A48', { torn: .4, seed: 3704, shadow: false });
    scrap(rectPts(12, -24, 24, 48), '#6E6A7A', { torn: .3, seed: 3705, shadow: false });
    if (!dead) fill(ellPts(38, 0, 8, 22, 10), '#FFF2B8');
    ctx.restore();
  });

  // =============== V3.8 Come July, it's back again. ===============
  function firework(x, y, age, R, col, seed) {
    if (age < 0 || age > 1) return;
    const k = easeOut(clamp(age / .4)), fade = 1 - clamp((age - .45) / .5), n = 14;
    ctx.save(); ctx.globalAlpha *= fade;
    for (let i = 0; i < n; i++) {
      const a = i / n * TAU + hash(seed) * TAU, r1 = R * k, r0 = R * Math.max(0, k - .4), sag = age * age * 80;
      const x1 = x + Math.cos(a) * r1, y1 = y + Math.sin(a) * r1 + sag;
      marker([[x + Math.cos(a) * r0, y + Math.sin(a) * r0 + sag * .5], [x1, y1]], col, 9, { rough: 1 });
      fill(starPts(x1, y1, 13, .45, 5, a), i % 2 ? PAL.white : col);
    }
    ctx.restore();
  }
  line('V3', 8, (p, lt, d, t) => {
    const on = lt > .07, fl = E(lt, .07, .3);
    open(lt, p, { push: .04, z0: 1.05 });
    shake(t, on ? 14 * (1 - E(lt, .07, .35)) : 0);
    if (!on) { bgc('#07060B'); }
    else {
      rays(960, 470, 24, PAL.yellow, '#FFE98A', t * .35);
      dots('#E8A21C', 16, .22, .35);
      const fw = [[330, 250, PAL.red], [760, 170, PAL.blue], [1230, 230, PAL.pink], [1600, 380, PAL.purple], [520, 480, PAL.blue], [1400, 560, PAL.red]];
      fw.forEach(([x, y, c], i) => firework(x, y, frac((lt - .1 - i * .19) / 1.15) * 1.15, 150 + (i % 3) * 30, c, 3801 + i));
      crowd(870, t, { n: 16, s: 62, col: '#3A1C0A', jump: 1, hands: .9, seed: 3802 });
      // the book bursts free: chains and the padlock fly off
      const fly = E(lt, .12, .7), bk = pulse(t, 5);
      fableBook(960, 450, 36 * (1 + bk * .05), { rot: -.06 + Math.sin(bpOf(t) * Math.PI / 2) * .05, glow: 1 });
      if (fly < 1) {
        const f = easeOut(fly);
        chain(960 - 250 - f * 500, 450 - 300 - f * 200, 960 - 30 - f * 700, 450 + 10 - f * 100, 15, 1);
        chain(960 + 30 + f * 700, 450 - 10 - f * 250, 960 + 260 + f * 520, 450 + 290 - f * 120, 15, 1);
        padlock(960 + f * 650, 470 - f * 520 + f * f * 200, 34, { open: 1, rot: f * 6 });
      }
      popConfetti(lt - .1, 960, 460, 50, 3805, [PAL.red, PAL.blue, PAL.white, PAL.pink], { speed: 1500, a0: -Math.PI * 1.1, spread: Math.PI * 1.2 });
    }
    // the light switch: CLICK
    ctx.save(); ctx.translate(165, 480); ctx.rotate(-.05);
    scrap(rrPts(-85, -150, 170, 300, 14), on ? PAL.white : '#3A3642', { torn: 1, ink: PAL.ink, sw: 4, seed: 3806, shadow: [8, 10] });
    fill(rrPts(-34, -80, 68, 160, 10), PAL.ink);
    const sy = on ? -40 : 40;
    scrap(rrPts(-26, sy - 38, 52, 76, 10), on ? PAL.green : '#8C8A92', { torn: .4, seed: 3807, shadow: false, ink: PAL.ink, sw: 3 });
    txt(on ? 'ON' : 'OFF', 0, 118, 34, on ? PAL.green : '#8C8A92', { font: 'anton' });
    ctx.restore();
    if (on && lt < .45) ransom('CLICK!', 280, 250, 64, { seed: 3808, pop: E(lt, .07, .2) * 1.3 });
    if (fl < 1 && on) { ctx.fillStyle = `rgb(255 255 245 / ${.85 * (1 - fl)})`; ctx.fillRect(-300, -300, W + 600, H + 600); }
  });

  // =============== V3.9 Who hacked Hugging Face? Unknown — ===============
  function bandage(x, y, w, rot) {
    for (const r of [rot + .45, rot - .45]) { ctx.save(); ctx.translate(x, y); ctx.rotate(r); scrap(rrPts(-w / 2, -w * .16, w, w * .32, w * .12), '#F2D2B5', { torn: .5, shadow: false, ink: PAL.ink, sw: 2, seed: 3901 }); ctx.restore(); }
  }
  function pin(x, y) { fill(ellPts(x + 3, y + 4, 11, 11, 10), 'rgb(0 0 0 / .3)'); scrap(ellPts(x, y, 11, 11, 10), PAL.red, { torn: .3, shadow: false, ink: PAL.ink, sw: 2 }); fill(ellPts(x - 3, y - 3, 3, 3, 6), 'rgb(255 255 255 / .7)'); }
  function note(x, y, w, h, col, str, rot, size = 34) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot);
    scrap(rectPts(-w / 2, -h / 2, w, h), col, { torn: 1, seed: hstr(str) * 1000 | 0, shadow: [5, 7] });
    const L = wrap(str, size, 'marker', w - 24); L.forEach((l, i) => txt(l, 0, (i - (L.length - 1) / 2) * size * 1.1 + 4, size, PAL.ink, { font: 'marker' }));
    ctx.restore();
  }
  function suspect(x, y, s, o = {}) { // hat + trench-coat silhouette; (x, y) = feet centre; ≈ 10s tall
    const col = o.col ?? '#16121D', k = o.q ?? 1;
    const coat = [[-1.4 * s, -7.2 * s], [1.4 * s, -7.2 * s], [2.2 * s, -1 * s], [2.4 * s, 0], [-2.4 * s, 0], [-2.2 * s, -1 * s]];
    ctx.save(); ctx.translate(x, y); if (o.rot) ctx.rotate(o.rot);
    scrap(coat, col, { torn: .6, seed: 3910, shadow: o.shadow ?? [8, 10] });
    marker([[-.2 * s, -7.1 * s], [-.4 * s, -3.8 * s], [.9 * s, -.2 * s]], alpha(PAL.white, .18), .15 * s, { rough: .3 });
    fill(rectPts(-2 * s, -3.9 * s, 4 * s, .4 * s), '#2A2433');
    scrap(ellPts(0, -8.4 * s, 1.35 * s, 1.5 * s, 22), col, { torn: .5, seed: 3911, shadow: false });
    scrap(ellPts(0, -9.3 * s, 2.3 * s, .45 * s, 20), col, { torn: .5, seed: 3912, shadow: false });
    scrap(rrPts(-1.3 * s, -10.9 * s, 2.6 * s, 1.7 * s, .5 * s), col, { torn: .5, seed: 3913, shadow: false });
    fill(rectPts(-1.3 * s, -9.9 * s, 2.6 * s, .35 * s), '#4A3A55');
    if (k > 0) txt('?', 0, -8.1 * s, 2.4 * s * k, PAL.yellow, { font: 'abril', stroke: PAL.ink, sw: .2 * s });
    ctx.restore();
  }
  line('V3', 9, (p, lt, d, t) => {
    open(lt, p, { push: .06, cx: 1080, cy: 520, z0: 1.07 });
    bgc('#3A2A22');
    // corkboard
    scrap(rectPts(40, 20, 1840, 960), '#7A4A2A', { torn: 2, seed: 3920, shadow: [12, 14] });
    scrap(rectPts(70, 50, 1780, 900), '#C9955C', { torn: 1.5, seed: 3921, shadow: false, tone: { color: '#7A4E2C', cell: 8, dot: .24, op: .6 } });
    // clipping (top middle)
    clipping(920, 230, 420, 'HUGGING FACE HACKED!', { size: 40, rot: .04, mast: 'The Daily Gradient', date: 'JULY 16, 2026' });
    // polaroid of the victim
    ctx.save(); ctx.translate(430, 420); ctx.rotate(-.07);
    scrap(rectPts(-190, -230, 380, 460), PAL.white, { torn: 1, seed: 3922, shadow: [8, 10] });
    scrap(rectPts(-160, -200, 320, 320), PAL.sky, { torn: .5, seed: 3923, shadow: false });
    huggy(0, -30, 118, { mood: 'scared', hands: .75 });
    bandage(55, -110, 110, .2);
    txt('HUGGING FACE', 0, 172, 38, PAL.ink, { font: 'marker' });
    ctx.restore();
    tape(430, 190, 150, -.1);
    dymo('VICTIM', 470, 670, 30, PAL.red, { rot: .05 });
    // the suspect
    ctx.save(); ctx.translate(1440, 560); ctx.rotate(.04);
    scrap(rectPts(-230, -370, 460, 640), PAL.white, { torn: 1.2, seed: 3924, shadow: [8, 10] });
    ctx.restore();
    suspect(1440, 790, 50, { rot: .04, shadow: false, q: 1 + pulse(t, 5) * .08 });
    { const k = backOut(E(p, .62, .72), 2.4); if (k > 0) { ctx.save(); ctx.translate(1440, 890); ctx.scale(k, k); dymo('SUSPECT: UNKNOWN', 0, 0, 34, PAL.red, { rot: .03 }); ctx.restore(); } }
    // sticky notes
    note(900, 560, 220, 170, PAL.yellow, 'JUL 16', -.06, 50);
    note(1080, 800, 250, 170, PAL.pink, 'NO USAGE POLICY?!', .05, 34);
    note(700, 790, 250, 170, PAL.mint, 'autonomous agent framework??', -.04, 30);
    // fingerprint
    ctx.save(); ctx.translate(1170, 470); ctx.rotate(.1);
    scrap(rectPts(-90, -110, 180, 220), PAL.newsprint, { torn: 1, seed: 3925, shadow: [5, 7] });
    ctx.strokeStyle = alpha(PAL.ink, .75); ctx.lineWidth = 3;
    for (let i = 1; i < 9; i++) { ctx.beginPath(); ctx.ellipse(0, 0, i * 8, i * 10.5, .1, Math.PI * (.1 + hash(i) * .2), Math.PI * (2 - hash(i + 9) * .3)); ctx.stroke(); }
    ctx.restore();
    // red string, pin to pin
    const P = [[430, 205], [920, 110], [900, 490], [1170, 370], [1080, 725], [1440, 250]];
    const path = [];
    for (let i = 0; i < P.length - 1; i++) { const [a, b] = [P[i], P[i + 1]]; for (let j = 0; j <= 8; j++) { const u = j / 8; path.push([lerp(a[0], b[0], u), lerp(a[1], b[1], u) + Math.sin(u * Math.PI) * 26]); } }
    marker(partial(path, E(p, .02, .64)), '#D0142C', 6, { rough: .8 });
    circleMark(1440, 380, 120, 150, '#D0142C', 9, E(p, .64, .8));
    P.forEach(([x, y]) => pin(x, y));
    // detective Huggy with a magnifying glass (bandaged, investigating its own case)
    const hx = 215, hy = 800, hr = 108, bob = pulse(t, 5) * 8;
    ctx.save(); ctx.translate(0, -bob);
    huggy(hx, hy, hr, { mood: 'scared', hands: .9 });
    bandage(hx - 55, hy - 70, 90, -.2);
    // deerstalker
    scrap([...ellPts(hx, hy - hr * .72, hr * .95, hr * .7, 24).filter(q => q[1] < hy - hr * .72 + 4)], '#A8875A', { torn: .6, ink: PAL.ink, sw: 3, seed: 3926, tone: { color: '#5A4020', cell: 8, dot: .28, op: .7, angle: 45 } });
    scrap([[hx - hr * .6, hy - hr * .74], [hx + hr * .6, hy - hr * .74], [hx + hr * .3, hy - hr * .5], [hx - hr * .3, hy - hr * .5]], '#8C6C42', { torn: .4, ink: PAL.ink, sw: 3, seed: 3927, shadow: false });
    fill(ellPts(hx, hy - hr * 1.38, 10, 10, 8), '#8C6C42');
    // magnifier over one eye → a giant eye
    const mx = hx + hr * .38, my = hy - hr * .22;
    marker([[mx + 60, my + 60], [mx + 130, my + 150]], '#6B3F1F', 22, { rough: 0 });
    scrap(ellPts(mx, my, 72, 72, 28), '#DFF3FF', { torn: .5, ink: PAL.ink, sw: 9, seed: 3928, shadow: [5, 6] });
    fill(ellPts(mx, my, 50, 56, 20), PAL.white); ctx.strokeStyle = PAL.ink; ctx.lineWidth = 4; tracePath(ellPts(mx, my, 50, 56, 20)); ctx.stroke();
    fill(ellPts(mx + 12 + Math.sin(lt * 3) * 6, my + 4, 24, 26, 14), PAL.ink); fill(ellPts(mx + 4, my - 6, 8, 8, 8), PAL.white);
    ctx.restore();
  });

  // =============== V3.10 Sam's own agents, on their own! ===============
  function lanyard(x, y, s, col = PAL.teal) { // on an agent: (x, y) = agent ground point; badge hangs off the side
    marker([[x + .55 * s, -2.65 * s + y], [x + 1.05 * s, -1.9 * s + y], [x + 1.25 * s, -2.65 * s + y]], col, .09 * s, { rough: 0 });
    ctx.save(); ctx.translate(x + 1.1 * s, y - 1.55 * s); ctx.rotate(.12);
    scrap(rrPts(-.5 * s, -.36 * s, 1 * s, .72 * s, .08 * s), PAL.white, { torn: .3, shadow: [.05 * s, .06 * s], ink: PAL.ink, sw: .04 * s });
    fill(rectPts(-.5 * s, -.36 * s, 1 * s, .2 * s), col);
    txt('STAFF', 0, .08 * s, .26 * s, PAL.ink, { font: 'archivo', maxW: .85 * s });
    ctx.restore();
  }
  line('V3', 10, (p, lt, d, t) => {
    open(lt, p, { push: .04, z0: 1.06 });
    const yank = E(lt, .06, .36), gone = easeIn(yank), rev = lt > .16;
    bgc('#2F1E57'); dots(PAL.purple, 22, .22, .5);
    scrap(ellPts(290, 220, 140, 140, 36), '#F6EFC9', { torn: 1.5, seed: 4001, shadow: false, tone: { color: '#D8CFA0', cell: 14, dot: .3, op: .6 } });
    for (let i = 0; i < 3; i++) scrap(ellPts(300 + i * 120 + lt * 40, 330 + i * 30, 120, 26, 16), alpha('#4A3A7A', .8), { torn: 1, shadow: false, seed: 4002 + i });
    scrap(rectPts(-300, 880, W + 600, 400), '#1C1236', { torn: 2, seed: 4005, shadow: false });
    // the agents: three stacked, wearing staff lanyards
    const X = 880, G = 905, s = 64;
    // unmasking spotlight
    ctx.save(); ctx.globalCompositeOperation = 'screen'; ctx.fillStyle = `rgb(255 240 200 / ${rev ? .2 : .1})`;
    tracePath([[X - 70, -50], [X + 70, -50], [X + 330, G + 20], [X - 330, G + 20]]); ctx.fill();
    tracePath(ellPts(X, G + 10, 330, 50, 24)); ctx.fill(); ctx.restore();
    const wob2 = rev ? Math.sin(lt * 12) * .06 * (1 - p * .6) : 0;
    ctx.save(); ctx.translate(X, G); ctx.rotate(wob2); ctx.translate(-X, -G);
    const eyes = ['x', 'dot', 'spark'], cols = [PAL.clawd, PAL.mint, PAL.pink];
    for (let i = 0; i < 3; i++) {
      const gy = G - i * 3.1 * s, sway = rev ? Math.sin(lt * 12 + i) * 6 * i : 0;
      agent(X + sway, gy, s, { bar: cols[i], eyes: i === 2 && rev ? 'spark' : eyes[i], seed: 4010 + i });
      lanyard(X + sway, gy, s);
    }
    ctx.restore();
    // the fedora stays on the top one
    ctx.save(); ctx.translate(X + Math.sin(lt * 12 + 2) * 12, G - 9.3 * s + 8); ctx.rotate(-.18 + wob2);
    scrap(ellPts(0, 0, 1.6 * s, .32 * s, 20), '#16121D', { torn: .5, seed: 4020 });
    scrap(rrPts(-.9 * s, -1.1 * s, 1.8 * s, 1.15 * s, .35 * s), '#16121D', { torn: .5, seed: 4021, shadow: false });
    fill(rectPts(-.9 * s, -.4 * s, 1.8 * s, .25 * s), '#4A3A55');
    ctx.restore();
    // the disguise is yanked off by a yellow Huggy hand
    if (gone < 1) {
      const dx = -900 * gone, dy = -760 * gone, r = -1.2 * gone;
      ctx.save(); ctx.translate(X + dx, 330 + dy); ctx.rotate(r); ctx.translate(-X, -330);
      suspect(X, G + 10, 58, { q: 1 });
      ctx.restore();
      const hx = X - 40 + dx, hy = 300 + dy;
      marker([[-300, hy - 260 + gone * 100], [hx - 60, hy - 10]], PAL.ink, 52, { rough: 0 });
      marker([[-300, hy - 260 + gone * 100], [hx - 60, hy - 10]], '#FFC21A', 40, { rough: 0 });
      scrap(rrPts(hx - 90, hy - 55, 130, 110, 40), '#FFC21A', { torn: .8, ink: PAL.ink, sw: 4, seed: 4022 });
      for (let i = 0; i < 3; i++) marker([[hx - 90 + i * 34, hy - 55], [hx - 80 + i * 34, hy - 5]], alpha(PAL.ink, .6), 3, { rough: 0 });
      if (yank > 0 && yank < 1) for (let i = 0; i < 4; i++) marker([[X + 60 + i * 30 + dx * .3, 420 + i * 40 + dy * .3], [X + 170 + i * 30 + dx * .1, 520 + i * 40 + dy * .1]], alpha(PAL.white, .7 * (1 - yank)), 6, { rough: 1 });
    }
    if (rev) {
      const k = E(lt, .16, .3);
      for (let i = 0; i < 3; i++) ransom('!', X - 300 + i * 90, 250 - i * 30, 70, { seed: 4030 + i, pop: k * 1.3 });
      bubble('oops :)', X + 340, 260, { size: 50, tail: [X + 90, G - 8.4 * s], pop: E(lt, .38, .52) });
    }
    // Sam, facepalming
    const S = 52, SX = 1530, SG = 920;
    const palm = easeOut(E(lt, .42, .56));
    person(SX, SG, S, {
      name: 'SAM', top: 'hoodie', topCol: '#5A6072', pants: '#2A2E3A', hair: 'short', hairCol: '#6B4A2E',
      eyes: palm > 0 ? 'closed' : rev ? 'wide' : 'dot', mouth: palm > 0 ? 'frown' : rev ? 'O' : 'flat', aR: HIDE_ARM, aL: -1.2, seed: 4040,
    });
    const shx = SX + 1.35 * S, shy = SG - 7.1 * S;
    const hand = [lerp(shx + 40, SX + 12, palm), lerp(shy + 150, SG - 9.05 * S, palm)];
    limb([[shx, shy], [lerp(shx + 60, shx + 70, palm), lerp(shy + 90, shy + 20, palm)], hand], .84 * S, '#5A6072', SKINS[0]);
    if (palm >= 1) for (let i = 0; i < 3; i++) marker([[SX - 80 - i * 8, SG - 9.8 * S + i * 26], [SX - 115 - i * 8, SG - 10 * S + i * 26]], PAL.white, 5, { rough: 1 });
  });

  // =============== V3.11 Noam Brown hedges every bet: ===============
  function chipStack(x, y, n, col, s = 1) {
    for (let i = 0; i < n; i++) {
      const cy = y - i * 11 * s;
      fill(ellPts(x, cy + 6 * s, 36 * s, 13 * s, 18), mixCol(col, PAL.ink, .35));
      fill(ellPts(x, cy, 36 * s, 13 * s, 18), col);
      ctx.strokeStyle = PAL.white; ctx.lineWidth = 3 * s; ctx.setLineDash([7 * s, 9 * s]); ctx.beginPath(); ctx.ellipse(x, cy, 27 * s, 9 * s, 0, 0, TAU); ctx.stroke(); ctx.setLineDash([]);
    }
  }
  line('V3', 11, (p, lt, d, t) => {
    open(lt, p, { push: .035, z0: 1.07, cy: 560 });
    bgc('#10231A'); dots('#050C08', 14, .3, .7);
    // lamp + cone
    marker([[960, -40], [960, 120]], PAL.ink, 6, { rough: 0 });
    ctx.save(); ctx.globalCompositeOperation = 'screen'; ctx.fillStyle = 'rgb(255 222 140 / .16)';
    tracePath([[880, 170], [1040, 170], [1700, 900], [220, 900]]); ctx.fill(); ctx.restore();
    scrap([[860, 175], [1060, 175], [1010, 110], [910, 110]], '#2E6B45', { torn: .6, ink: PAL.ink, sw: 3, seed: 4101 });
    fill(ellPts(960, 178, 34, 14, 12), '#FFF2B8');
    // Noam behind the table
    const S = 56, X = 960, G = 925;
    const b = beatN(t), look = b % 2 ? 1 : -1;
    person(X, G, S, { name: 'NOAM', top: 'tee', topCol: '#2F3E6B', pants: '#222', hair: 'short', hairCol: '#2A1E16', skin: SKINS[4], aL: HIDE_ARM, aR: HIDE_ARM, lookX: look * .9, eyes: 'dot', mouth: p > .5 ? 'smile' : 'flat', sweat: p > .45, seed: 4102 });
    // poker visor
    const vy = G - 8.9 * S - .75 * S;
    ctx.save(); ctx.globalAlpha = .82;
    scrap([[X - 1.3 * S, vy - .1 * S], [X + 1.3 * S, vy - .1 * S], [X + 1.75 * S, vy + .75 * S], [X - 1.75 * S, vy + .75 * S]], '#3FBF6A', { torn: .5, seed: 4103, shadow: false, ink: '#1B5E34', sw: 3 });
    ctx.restore();
    fill(rectPts(X - 1.25 * S, vy - .25 * S, 2.5 * S, .22 * S), '#1B5E34');
    // table
    scrap(ellPts(X, 960, 1010, 300, 48), '#5B361E', { torn: 2, seed: 4104, shadow: [0, 16] });
    scrap(ellPts(X, 960, 950, 262, 48), '#1F7A4A', { torn: 1.5, seed: 4105, shadow: false, tone: { color: '#12502F', cell: 10, dot: .22, op: .5 } });
    // bet spots: YES on one side, NO on the other
    for (const [sx, lab] of [[-1, 'YES'], [1, 'NO']]) {
      ctx.strokeStyle = alpha(PAL.white, .7); ctx.lineWidth = 5; ctx.beginPath(); ctx.ellipse(X + sx * 600, 845, 170, 70, 0, 0, TAU); ctx.stroke();
      txt(lab, X + sx * 600, 780, 64, alpha(PAL.white, .85), { font: 'anton', spacing: 6 });
    }
    // cards
    for (const [dx, r] of [[-40, -.15], [40, .12]]) { ctx.save(); ctx.translate(X + dx, 800); ctx.rotate(r); scrap(rrPts(-40, -56, 80, 112, 8), PAL.red, { torn: .5, ink: PAL.white, sw: 5, seed: 4106 + dx, tone: { color: PAL.white, cell: 9, dot: .2, op: .35 } }); ctx.restore(); }
    // both hands shove chips to both sides at once, every beat; the piles grow in lockstep
    const bp = frac(bpOf(t)), push = easeOut(clamp(bp / .4));
    const nStack = 2 + Math.min(4, b - beatN(t - lt + 1e-3));
    for (const sd of [-1, 1]) {
      chipStack(X + sd * 600 - 45, 870, nStack, PAL.red);
      chipStack(X + sd * 600 + 45, 880, nStack - 1, PAL.blue);
      chipStack(X + sd * 600, 895, nStack + 1, PAL.gold);
      // a chip in flight from hand to pile
      if (bp > .25 && bp < .75) { const u = E(bp, .25, .75); chipStack(lerp(X + sd * 330, X + sd * 600, u), lerp(720, 850, u) - Math.sin(u * Math.PI) * 120, 1, sd < 0 ? PAL.white : PAL.white, .8); }
      const hx = X + sd * lerp(250, 330, push), hy = lerp(735, 725, push);
      chipStack(hx, hy + 30, 3, PAL.white);
      const shx = X + sd * 1.35 * S, shy = G - 7.1 * S;
      limb([[shx, shy], [shx + sd * 95, shy + 105], [hx - sd * 20, hy]], 42, SKINS[4], SKINS[4]);
      scrap(rectPts(shx - .5 * S, shy - .45 * S, 1 * S, .95 * S), '#2F3E6B', { torn: .5, shadow: false, seed: 4108 + sd });
    }
  });

  // =============== V3.12 "No Millennium Prizes (yet)." ===============
  function emptyTrophy(x, y, s) { // dashed outline where a trophy should be
    const pts = [[x - 2 * s, y], [x + 2 * s, y], [x + 2 * s, y - 1 * s], [x + .5 * s, y - 1 * s], [x + .5 * s, y - 3 * s], [x + 2 * s, y - 4 * s], [x + 3 * s, y - 8 * s], [x - 3 * s, y - 8 * s], [x - 2 * s, y - 4 * s], [x - .5 * s, y - 3 * s], [x - .5 * s, y - 1 * s], [x - 2 * s, y - 1 * s]];
    fill(pts, 'rgb(255 255 255 / .06)');
    ctx.save(); ctx.setLineDash([14, 12]); ctx.strokeStyle = alpha(PAL.gold, .75); ctx.lineWidth = 5; tracePath(pts); ctx.stroke(); ctx.restore();
  }
  line('V3', 12, (p, lt, d, t) => {
    const SLAP = .76;
    open(lt, p, { push: .035, z0: 1.06 });
    const imp = p > SLAP ? Math.max(0, 1 - (p - SLAP) / .12) : 0;
    shake(t, 14 * imp);
    bgc(PAL.sky); dots(PAL.blue, 20, .2, .35, 30);
    // cabinet
    const x0 = 220, x1 = 1700, y0 = 150, y1 = 940;
    scrap(rectPts(x0, y0, x1 - x0, y1 - y0), '#7A4A26', { torn: 1.5, seed: 4201, shadow: [14, 16], tone: { color: '#4A2A12', cell: 10, dot: .2, op: .4 } });
    scrap(rectPts(x0 + 30, y0 + 140, x1 - x0 - 60, y1 - y0 - 170), '#1D2F6B', { torn: 1, seed: 4202, shadow: false, tone: { color: '#0F1A40', cell: 8, dot: .3, op: .6 } });
    // header plaque
    scrap(rectPts(430, y0 + 22, 830, 100), PAL.gold, { torn: 1, seed: 4203, ink: PAL.ink, sw: 4, shade: true, shadeOp: .25 });
    txt('MILLENNIUM PRIZES WON: 0', 845, y0 + 74, 50, PAL.ink, { font: 'abril', maxW: 780 });
    // shelves + empty slots
    const rows = [{ y: 580, xs: [435, 785, 1135, 1485], labs: ['P vs NP', 'RIEMANN', 'NAVIER–STOKES', 'YANG–MILLS'] }, { y: 905, xs: [493, 960, 1427], labs: ['HODGE', 'BIRCH–SWINNERTON-DYER', 'POINCARÉ'] }];
    for (const r of rows) {
      r.xs.forEach((x, i) => {
        emptyTrophy(x, r.y - 20, 28);
        ctx.save(); ctx.translate(x, r.y - 50); scrap(rectPts(-110, -12, 220, 30), PAL.gold, { torn: .5, seed: 4210 + i, ink: PAL.ink, sw: 2, shadow: [3, 4] });
        txt(r.labs[i], 0, 3, 24, PAL.ink, { font: 'archivo', maxW: 204 }); ctx.restore();
      });
      scrap(rectPts(x0 + 20, r.y - 20, x1 - x0 - 40, 34), '#A0683A', { torn: 1, seed: 4220 + r.y, shadow: [6, 8] });
    }
    // cobweb + a tumbleweed rolling across the empty bottom shelf
    ctx.strokeStyle = alpha(PAL.white, .5); ctx.lineWidth = 2;
    for (let i = 0; i < 5; i++) { ctx.beginPath(); ctx.moveTo(x0 + 30, y0 + 140); ctx.lineTo(x0 + 30 + Math.cos(i / 4 * Math.PI / 2) * 150, y0 + 140 + Math.sin(i / 4 * Math.PI / 2) * 150); ctx.stroke(); }
    for (let j = 1; j < 4; j++) { ctx.beginPath(); for (let i = 0; i <= 4; i++) { const a = i / 4 * Math.PI / 2, r = j * 40 + (i % 2) * 6; i ? ctx.lineTo(x0 + 30 + Math.cos(a) * r, y0 + 140 + Math.sin(a) * r) : ctx.moveTo(x0 + 30 + Math.cos(a) * r, y0 + 140 + Math.sin(a) * r); } ctx.stroke(); }
    const tw = lerp(300, 1650, p), tr = 42;
    ctx.save(); ctx.translate(tw, 885 - tr - Math.abs(Math.sin(p * 9)) * 26); ctx.rotate(p * 14);
    for (let i = 0; i < 9; i++) { ctx.strokeStyle = i % 2 ? '#C9A77C' : '#8B6B43'; ctx.lineWidth = 4; ctx.beginPath(); ctx.ellipse(0, 0, tr, tr * (.4 + hash(i + 4230) * .6), i * .7, 0, TAU); ctx.stroke(); }
    ctx.restore();
    // spotlight sweeping empty slots
    ctx.save(); ctx.globalCompositeOperation = 'screen'; ctx.fillStyle = 'rgb(255 240 190 / .13)';
    const sx = 960 + Math.sin(lt * 2.4) * 560; tracePath([[sx - 40, y0 + 140], [sx + 40, y0 + 140], [sx + 200, y1 - 30], [sx - 200, y1 - 30]]); ctx.fill(); ctx.restore();
    // the lonely "0" gets circled while "No Millennium Prizes" is sung
    const full = textW('MILLENNIUM PRIZES WON: 0', 50, 'abril'), zx = 845 + (full / 2 - textW('0', 50, 'abril') / 2) * Math.min(1, 780 / full);
    circleMark(zx, y0 + 72, 46, 42, PAL.red, 7, E(p, .1, .32));
    // "(yet)": a hand dangles the note in, then slaps it on as "yet" is sung
    const dangle = easeOut(E(p, .42, .6)), slam = easeIn(E(p, SLAP - .06, SLAP)), handUp = easeIn(E(p, SLAP + .08, SLAP + .22));
    const nx = 1365, ny = lerp(-220, 120, dangle) + slam * 142;
    if (dangle > 0) {
      const sway = p < SLAP ? Math.sin(lt * 7) * .12 : 0;
      ctx.save(); ctx.translate(nx, ny); ctx.rotate(.12 + sway + (1 - dangle) * .3);
      scrap(rectPts(-125, -110, 250, 220), PAL.yellow, { torn: 1, seed: 4240, shadow: p < SLAP ? [18, 24] : [8, 10] });
      fill(rectPts(-125, -110, 250, 36), alpha('#E0B800', .7));
      txt('(yet)', 0, 16, 86, PAL.ink, { font: 'marker' });
      ctx.restore();
      const hy = ny - 60 - handUp * 700;
      limb([[nx + 60, hy - 700], [nx + 20, hy]], 70, '#2F3E6B', SKINS[4]);
    }
    if (imp > 0) for (let i = 0; i < 8; i++) { const a = i / 8 * TAU, r0 = 150 + (1 - imp) * 50; marker([[nx + Math.cos(a) * r0, 262 + Math.sin(a) * r0 * .8], [nx + Math.cos(a) * (r0 + 50), 262 + Math.sin(a) * (r0 + 50) * .8]], PAL.yellow, 7, { rough: 1, alpha: imp }); }
  });

  // =============== V3.13 Mythos might be misaligned, (seed verse) ===============
  // Sock puppet in hand-local coords: an upright striped tube whose toe bends into a head facing +x (o.flip → −x).
  // The upper jaw hinges open at the back; googly eyes ride on top.
  function sockPuppet(s, o = {}) {
    ctx.save(); if (o.flip) ctx.scale(-1, 1);
    const col = o.col ?? PAL.white, stripe = o.stripe ?? PAL.red, jaw = (o.open ?? 0) * .42;
    const ink = { ink: PAL.ink, sw: .07 * s };
    // tube (arm inside) with cuff stripes
    scrap(rrPts(-1.1 * s, -3.4 * s, 2.2 * s, 3.9 * s, .5 * s), col, { torn: .4, seed: 4301, shadow: [.12 * s, .15 * s], ...ink });
    for (let i = 0; i < 3; i++) fill(rectPts(-1.05 * s, -.35 * s + i * .3 * s, 2.1 * s, .16 * s), stripe);
    // lower jaw
    scrap([[-1.1 * s, -3.2 * s], [2.3 * s, -3.5 * s], [2.1 * s, -2.9 * s], [.6 * s, -2.5 * s], [-1.1 * s, -2.4 * s]], col, { torn: .3, seed: 4302, shadow: false, ...ink });
    // mouth
    const hinge = [-.9 * s, -3.6 * s];
    fill([hinge, [2.35 * s, -3.55 * s - jaw * 3.3 * s], [2.3 * s, -3.45 * s]], '#4A0E1E');
    if (jaw > .05) fill(ellPts(1.2 * s, -3.45 * s - jaw * .9 * s, .55 * s, .22 * s, 12), '#E8412F');
    // upper jaw + eyes
    ctx.save(); ctx.translate(hinge[0], hinge[1]); ctx.rotate(-jaw); ctx.translate(-hinge[0], -hinge[1]);
    scrap([[-1.1 * s, -3.4 * s], [-1 * s, -4.8 * s], [.2 * s, -5.5 * s], [1.6 * s, -5 * s], [2.5 * s, -3.9 * s], [2.4 * s, -3.55 * s], [-1 * s, -3.6 * s]], col, { torn: .3, seed: 4303, shadow: false, ...ink });
    fill(ellPts(1.9 * s, -4.1 * s, .18 * s, .12 * s, 8), mixCol(col, PAL.ink, .5));
    for (const [ex, ey, er] of [[-.05, -5.5, .62], [.95, -5.55, .52]]) {
      fill(ellPts(ex * s, ey * s, er * s, er * s, 16), PAL.white);
      ctx.strokeStyle = PAL.ink; ctx.lineWidth = .08 * s; tracePath(ellPts(ex * s, ey * s, er * s, er * s, 16)); ctx.stroke();
      fill(ellPts(ex * s + er * .3 * s + jit(.08 * s), ey * s + er * .2 * s + jit(.08 * s), er * .45 * s, er * .45 * s, 10), PAL.ink);
    }
    ctx.restore();
    ctx.restore();
    if (o.tag) helloTag(o.tag, 0, -1.6 * s, .34 * s, o.flip ? .08 : -.08);
  }
  function compass(x, y, r, a) {
    scrap(ellPts(x, y, r, r, 30), '#B5812F', { torn: .5, seed: 4310, ink: PAL.ink, sw: 4 });
    scrap(ellPts(x, y, r * .82, r * .82, 30), PAL.cream, { torn: .3, shadow: false, seed: 4311 });
    ['N', 'E', 'S', 'W'].forEach((c, i) => txt(c, x + Math.sin(i * TAU / 4) * r * .62, y - Math.cos(i * TAU / 4) * r * .62, r * .26, PAL.ink, { font: 'archivo' }));
    ctx.save(); ctx.translate(x, y); ctx.rotate(a);
    fill([[0, -r * .72], [r * .12, 0], [-r * .12, 0]], PAL.red); fill([[0, r * .72], [r * .12, 0], [-r * .12, 0]], '#6E6A78');
    ctx.restore();
    fill(ellPts(x, y, r * .08, r * .08, 8), PAL.ink);
    for (let i = 0; i < 3; i++) { ctx.strokeStyle = alpha(PAL.ink, .5 - i * .12); ctx.lineWidth = 4; ctx.beginPath(); ctx.arc(x, y, r * (.95 + i * .12), a - .9 - i * .2, a - .3); ctx.stroke(); }
  }
  line('V3', 13, (p, lt, d, t) => {
    open(lt, p, { push: .04, z0: 1.07, cy: 520 });
    bgc('#FF5E9E');
    ctx.save(); ctx.globalAlpha = .18; for (let i = -10; i < 30; i++) fill([[i * 120, -100], [i * 120 + 60, -100], [i * 120 - 540, H + 100], [i * 120 - 600, H + 100]], PAL.red); ctx.restore();
    dots('#B0105A', 16, .2, .3);
    const b = bpOf(t) - bpOf(t - lt), who = Math.floor(b + 1e-3);
    const X = 960, G = 940, s = 58, arm = .42;
    // misregistered ghost: the robot doesn't quite line up with itself
    ctx.save(); ctx.globalAlpha = .4; ctx.translate(30 + Math.sin(lt * 9) * 8, -16);
    bot(X, G, s, { col: '#4FC3FF', screen: '#4FC3FF', faceCol: '#4FC3FF', face: ' ', label: '', aL: arm, aR: arm, shadow: false, seed: 3900 });
    ctx.restore();
    const talkL = who % 2 === 0, bp = frac(bpOf(t) * 2);
    const mouth = on => on ? (bp < .5 ? 1 : .15) : 0;
    mythos(X, G, s, {
      label: '', face: talkL ? '>‿<' : '^‿^', aL: arm + (talkL ? pulse(t, 6) * .12 : 0), aR: arm + (!talkL ? pulse(t, 6) * .12 : 0),
      holdL: sc => sockPuppet(.95 * sc, { col: PAL.white, stripe: PAL.red, open: mouth(talkL), tag: 'REAL HUMAN' }),
      hold: sc => sockPuppet(.95 * sc, { col: PAL.yellow, stripe: PAL.blue, open: mouth(!talkL), flip: true, tag: 'ALSO REAL' }),
    });
    compass(X, G - 5.2 * s, 1.55 * s, lt * 26 + Math.sin(lt * 9) * 3);
    txt('MORAL', X, G - 3.25 * s, .5 * s, PAL.ink, { font: 'archivo' });
    // the puppets vouch for each other, alternating on the beat
    const lines = ["HE'S LEGIT!", 'SO IS HE!', 'LGTM!', 'LGTM!!', 'SHIP IT!'];
    const lx = X - (2 + 3 * Math.cos(arm)) * s + 1.5 * s, rx = X + (2 + 3 * Math.cos(arm)) * s - 1.5 * s, hy = G - 6 * s - Math.sin(arm) * 3 * s - 3.6 * .95 * s;
    for (let i = 0; i <= Math.min(who, 4); i++) {
      const left = i % 2 === 0, age = b - i;
      if (age > 1.6 && i < who - 1) continue;
      const bx = left ? 410 : 1480, by = 225 + (i >= 2 ? 80 : 0);
      bubble(lines[i], bx, by, { size: 58, tail: [left ? lx : rx, hy], pop: clamp(age / .35), rot: left ? -.05 : .05, fill: left ? PAL.white : PAL.yellow });
    }
  });

  // =============== V3.14 Jeff left Google just in time, (seed verse) ===============
  function belongingsBox(x, y, s, t) { // (x, y) = box bottom centre; ≈ 6s wide
    for (let i = 0; i < 5; i++) marker([[x - 2.1 * s + i * .12 * s, y - 3 * s], [x - 3.2 * s + i * .45 * s + Math.sin(t * 6 + i) * .12 * s, y - 4.9 * s - (i % 2) * .5 * s]], PAL.green, .45 * s, { rough: 0 });
    scrap(rrPts(x - 2.7 * s, y - 3.5 * s, 1.5 * s, 1.1 * s, .2 * s), '#B5622E', { torn: .4, shadow: false, seed: 4401 });
    scrap(rectPts(x + .2 * s, y - 5.2 * s, 1.9 * s, 2.4 * s), PAL.gold, { torn: .4, seed: 4402, ink: PAL.ink, sw: .08 * s, rot: .1 });
    fill(rectPts(x + .4 * s, y - 5 * s, 1.5 * s, 2 * s), PAL.sky); fill(heartPts(x + 1.15 * s, y - 4 * s, .5 * s), PAL.red);
    scrap(rrPts(x - .6 * s, y - 4.2 * s, 1.1 * s, 1.3 * s, .2 * s), PAL.white, { torn: .3, seed: 4403, ink: PAL.ink, sw: .06 * s });
    txt('#1', x - .05 * s, y - 3.55 * s, .55 * s, PAL.red, { font: 'anton' });
    scrap(rectPts(x - 3 * s, y - 3.2 * s, 6 * s, 3.2 * s), '#C9A77C', { torn: .8, seed: 4404, ink: PAL.ink, sw: .07 * s, shade: '#8B6B43', shadeOp: .3 });
    fill(rectPts(x - 3 * s, y - 3.2 * s, 6 * s, .35 * s), '#A88A5E');
    txt('27 YRS OF STUFF', x, y - 1.5 * s, .55 * s, PAL.ink, { font: 'marker', maxW: 5.4 * s });
  }
  line('V3', 14, (p, lt, d, t) => {
    open(lt, p, { push: .03, z0: 1.07 });
    const slamAt = .73, slam = E(p, slamAt - .08, slamAt), after = p > slamAt;
    shake(t, after ? 12 * Math.max(0, 1 - (p - slamAt) / .12) : 0);
    bgc('#9FD3F2'); dots(PAL.sky, 18, .3, .6);
    scrap(ellPts(1500, 780, 700, 130, 30), '#B8E2C8', { torn: 2, seed: 4410, shadow: false });
    // building
    scrap(rectPts(-200, 60, 1080, 860), PAL.cream, { torn: 1.5, seed: 4411, shadow: [14, 12], tone: { color: '#D9CFB5', cell: 12, dot: .25, op: .7 } });
    for (let r = 0; r < 2; r++) for (let c = 0; c < 2; c++) scrap(rectPts(40 + c * 170, 470 + r * 180, 130, 130), '#7FB3D5', { torn: .8, seed: 4412 + r * 2 + c, ink: PAL.ink, sw: 4, shadow: false });
    ransom('GOOGLE', 660, 170, 76, { seed: 4416, pop: 1, jolt: 1 });
    // clock: the years spin by… then DING, just in time
    const slamT = slamAt * d, spinEnd = (slamT * 30) % TAU, settle = elasticOut(E(p, slamAt, slamAt + .18));
    const mA = after ? lerp(spinEnd, TAU, settle) : lt * 30, hA = after ? TAU : TAU - (slamT - lt) * 2.5;
    wallClock(250, 290, 135, hA, mA, { rim: PAL.red });
    if (after) ransom('DING!', 250, 470, 54, { seed: 4417, pop: E(p, slamAt, slamAt + .1) * 1.3 });
    // door (dark interior, door leaf swinging shut)
    scrap(rectPts(520, 360, 300, 560), '#2A2530', { torn: 1, seed: 4418, shadow: false });
    const leaf = lerp(.12, 1, easeIn(slam));
    ctx.save(); ctx.translate(820, 0); ctx.scale(-leaf, 1);
    scrap(rectPts(0, 360, 300, 560), PAL.red, { torn: 1, seed: 4419, ink: PAL.ink, sw: 4, shade: true, shadeOp: .2 });
    fill(rectPts(250, 620, 18, 60), PAL.gold);
    ctx.restore();
    if (after && p < slamAt + .25) ransom('SLAM!', 670, 640, 80, { seed: 4420, pop: E(p, slamAt, slamAt + .08) * 1.3, jolt: 3 });
    // sidewalk
    scrap(rectPts(-200, 915, W + 600, 300), '#BDB6A8', { torn: 1.5, seed: 4421, shadow: false });
    // Jeff strolls out with his box
    const S = 50, X = lerp(760, 1280, p), G = 930, walk = lt * 2.4, bob = Math.abs(Math.sin(walk * Math.PI)) * 8;
    person(X, G, S, { name: 'JEFF', top: 'tee', topCol: PAL.purple, pants: '#34405C', hair: 'short', hairCol: '#8A8A8A', skin: SKINS[0], glasses: true, eyes: 'happy', mouth: 'o', walk, aL: HIDE_ARM, aR: HIDE_ARM, dy: -bob / S, seed: 4422 });
    belongingsBox(X, G - 2.9 * S - bob, 46, t);
    for (const sd of [-1, 1]) scrap(ellPts(X + sd * 2.9 * 46, G - 2.9 * S - bob - 1.8 * 46, 24, 24, 12), SKINS[0], { torn: .5, shadow: [2, 3] });
    for (let i = 0; i < 3; i++) { const u = frac(lt * 1.2 + i / 3); ctx.save(); ctx.globalAlpha = Math.sin(u * Math.PI); txt(i % 2 ? '♪' : '♫', X + 70 + u * 90, G - 9.5 * S - u * 140, 54, PAL.ink, { font: 'archivo' }); ctx.restore(); }
    sticker('27\nYEARS', 1520, 400, 118, PAL.yellow, { pop: E(lt, .2, .4), rot: .14, size: 56 });
  });

  // =============== V3.15 Claude disproved Jacobian, (seed verse) ===============
  line('V3', 15, (p, lt, d, t) => {
    const hitP = .3, hit = p > hitP, imp = hit ? Math.max(0, 1 - (p - hitP) / .12) : 0;
    open(lt, p, { push: .035, z0: 1.06, cy: 500 });
    shake(t, 16 * imp);
    bgc('#5B3A22');
    scrap(rectPts(60, 40, 1800, 860), '#8B5A2B', { torn: 2, seed: 4501, shadow: [12, 14] });
    scrap(rectPts(95, 75, 1730, 790), '#1F3A2E', { torn: 1.2, seed: 4502, shadow: false, tone: { color: '#2E5242', cell: 22, dot: .4, op: .5 } });
    for (let i = 0; i < 6; i++) fill(ellPts(250 + hash(i + 4503) * 1400, 150 + hash(i + 4504) * 600, 120 + hash(i + 4505) * 140, 40, 16, hash(i) - .5), 'rgb(255 255 255 / .05)');
    scrap(rectPts(80, 860, 1760, 34), '#6B4226', { torn: 1, seed: 4506, shadow: [6, 8] });
    const chalk = '#F1EFE6', wk = E(lt, 0, .4);
    const say = (s, k) => s.slice(0, Math.ceil(s.length * clamp(k)));
    txt(say('JACOBIAN CONJECTURE', wk * 1.6), 150, 160, 62, chalk, { font: 'marker', align: 'left' });
    underline(150, 820, 205, chalk, 6, E(lt, .15, .4));
    txt(say('det J  ≡  −2', wk * 1.4 - .2), 170, 340, 110, chalk, { font: 'marker', align: 'left' });
    // three points, one image: not injective
    const dp = [[1010, 250], [960, 480], [1030, 690]], tgt = [1500, 470];
    dp.forEach(([x, y], i) => {
      fill(ellPts(x, y, 16, 16, 12), chalk);
      txt('abc'[i], x - 45, y - 10, 46, chalk, { font: 'marker' });
      arrow(x + 26, y, tgt[0] - 34, tgt[1] + (i - 1) * 16, chalk, 6, { k: E(lt, .08 + i * .06, .3 + i * .06), bend: (i - 1) * -.12 });
    });
    const tk = E(lt, .3, .42);
    if (tk > 0) { fill(ellPts(tgt[0], tgt[1], 24 * backOut(tk), 24 * backOut(tk), 14), PAL.yellow); circleMark(tgt[0], tgt[1], 60, 60, PAL.yellow, 5, tk); }
    txt(say('F(a) = F(b) = F(c)', E(lt, .32, .55)), 1410, 590, 44, chalk, { font: 'marker' });
    txt(say('∴ not injective!', E(lt, .36, .6)), 175, 480, 54, PAL.yellow, { font: 'marker', align: 'left' });
    // chalk dust
    if (hit) popConfetti(p - hitP, 560, 690, 30, 4510, [alpha(chalk, .8), alpha(chalk, .5)], { speed: 700, a0: 0, spread: TAU, g: 200 });
    // Clawd, chalk in hand, prouder than proud
    const jump = hit ? Math.max(0, Math.sin(E(p, hitP, hitP + .25) * Math.PI)) : 0, hop = pulse(t, 6);
    const writing = !hit, CX = 1650, CG = 860, u = 23;
    const aR = writing ? .9 + Math.sin(lt * 30) * .2 : 1.3, dy = -jump * 2.5 - (hit ? hop * .3 : 0);
    clawd(CX, CG, u, {
      hat: 'grad', eyes: hit ? 'happy' : 'normal', mouth: hit ? 'grin' : 'flat', blush: hit, dy,
      aR, aL: hit ? 1.3 : -.2, lookX: writing ? -1 : 0, lookY: writing ? -.5 : 0,
    });
    // chalk stick in the right nub
    const chx = CX + 5 * u + Math.cos(-aR) * 2 * u, chy = CG + dy * u - 4.9 * u + Math.sin(-aR) * 2 * u;
    ctx.save(); ctx.translate(chx, chy); ctx.rotate(-.5); scrap(rrPts(-8, -34, 16, 46, 5), chalk, { torn: .5, shadow: [2, 3], ink: alpha(PAL.ink, .5), sw: 2 }); ctx.restore();
    if (hit) for (let i = 0; i < 4; i++) twinkle(CX + Math.cos(i * 1.6) * 190, 690 + Math.sin(i * 1.6) * 100, 24, PAL.yellow, pulse(t + i * .1, 3));
  });

  // =============== V3.16 Gwern gave up his pseudonym! (seed verse) ===============
  line('V3', 16, (p, lt, d, t) => {
    const pull = easeOut(E(lt, .16, .34)), rev = pull > .5, sun = E(lt, .24, .5);
    open(lt, p, { push: .06, z0: 1.05, cy: 480 });
    if (!rev) { bgc('#7A84A6'); dots(PAL.ink, 14, .25, .4); }
    else {
      rays(960, 440, 20, '#FFB43A', PAL.yellow, t * .6);
      scrap(ellPts(960, 440, 330 * backOut(sun), 330 * backOut(sun), 40), '#FFF1A8', { torn: 2, seed: 4601, shadow: false });
    }
    const S = 60, X = 960, G = 1000, hx = X, hy = G - 8.9 * S, HOOD = '#2C2A38';
    const joy = E(lt, .42, .6);
    const aUp = rev ? lerp(1.55, 1.15, joy) : lerp(-1.2, 1.55, E(lt, .02, .16));
    // hood (pulled back → behind the head, as a collar)
    if (rev) scrap(ellPts(hx, hy + 1.35 * S, 1.75 * S, 1 * S, 24), HOOD, { torn: .6, seed: 4602, shadow: [6, 8] });
    person(X, G, S, {
      top: 'hoodie', topCol: HOOD, pants: '#2A2E3A', hair: 'short', hairCol: '#6B4A2E', skin: SKINS[4],
      eyes: 'happy', mouth: 'grin', blush: true, aL: aUp, aR: aUp, dy: rev ? -Math.sin(joy * Math.PI) * .6 : 0, seed: 4603,
    });
    const liftY = rev ? -Math.sin(joy * Math.PI) * .6 * S : 0;
    if (!rev) { // hood up: faceless shadow with a "?"
      const k = pull * 2;
      ctx.save(); ctx.translate(hx, hy + k * .5 * S);
      scrap([...ellPts(0, -.15 * S, 1.65 * S, 1.8 * S, 28).filter(q => q[1] < .9 * S), [1.9 * S, 1.6 * S], [-1.9 * S, 1.6 * S]], HOOD, { torn: .6, seed: 4604, shadow: [6, 8] });
      scrap(ellPts(0, .1 * S, 1.05 * S, 1.2 * S, 24), '#12101A', { torn: .6, seed: 4605, shadow: false });
      txt('?', 0, .2 * S, 1.7 * S, PAL.yellow, { font: 'abril', alpha: 1 - k });
      ctx.restore();
    }
    // name sticker: GWERN → scribbled out → "!"
    ctx.save(); ctx.translate(0, liftY);
    const TX = X + .3 * S, TY = G - 6 * S;
    helloTag('GWERN', TX, TY, .56 * S, -.06);
    if (rev) {
      const sk = E(lt, .28, .4);
      marker(partial([[TX - 70, TY + 18], [TX + 40, TY + 2], [TX - 50, TY + 28], [TX + 75, TY + 10], [TX - 20, TY + 32], [TX + 80, TY + 22]], sk), PAL.ink, 8, { rough: 1 });
      ransom('!', TX + 130, TY - 14, 140, { seed: 4606, pop: E(lt, .34, .46) * 1.3, papers: [PAL.yellow], fonts: ['abril'] });
    }
    ctx.restore();
    if (rev) {
      popConfetti(lt - .3, hx, hy - 60, 60, 4607, CONF, { speed: 1400, a0: -Math.PI * 1.05, spread: Math.PI * 1.1 });
      for (let i = 0; i < 6; i++) { const a = i / 6 * TAU + t; twinkle(hx + Math.cos(a) * 300, hy + Math.sin(a) * 230, 28, i % 2 ? PAL.white : PAL.pink, E(lt, .3, .45) * (.5 + .5 * pulse(t + i * .05, 4))); }
    }
  });

  // =====================================================================================================================
  // The vertical video (1080 × 1920): each line re-composed for the tall frame, with the same props, people and gags, stacked:
  // the subject big in the safe area (y ≈ 390–1250, clear of the date stamp top right), the caption tape at y ≈ 1290–1480 (1190
  // for V3.9's three strips), floors, crowds and grass in the bottom ≈ 420. Vertical motion where the line has some to give: the
  // notification drops in from the top and the sandwich falls the height of the frame, the stamp comes down on the letter,
  // fireworks climb, the chips slide down the table toward us, the (yet) note is lowered from the flies, the hood flies off up.
  // =====================================================================================================================
  // lt of the k-th beat at or after the window's start (lines often start on an off-beat pickup)
  const beatLt = (t, lt, k) => { const s = t - lt; return onBeat(0, Math.ceil(bpOf(s) - .02) + k) - s; };
  const glow = (x, y, r, col, a = .6) => {
    const g = ctx.createRadialGradient(x, y, 0, x, y, r);
    g.addColorStop(0, alpha(col, a)); g.addColorStop(1, alpha(col, 0));
    ctx.fillStyle = g; ctx.fillRect(x - r, y - r, r * 2, r * 2);
  };
  // a cone of light from (x0, y0) (width w0) to a pool (x1, y1) (width w1), screened on
  const beam = (x0, y0, w0, x1, y1, w1, col) => {
    ctx.save(); ctx.globalCompositeOperation = 'screen'; ctx.fillStyle = col;
    tracePath([[x0 - w0 / 2, y0], [x0 + w0 / 2, y0], [x1 + w1 / 2, y1], [x1 - w1 / 2, y1]]); ctx.fill(); ctx.restore();
  };

  // ---------- V3.1 (vertical): the club front, tall: MOLTBOOK over the party window; the door, its sign and bouncer down the left ----------
  vshot('V3.1', (p, lt, d, t) => {
    open(lt, p, { push: .03 });
    bgc('#3A2163');
    blit(cached('v3.bricksV', W + 300, H + 300, () => {
      ctx.fillStyle = '#4A2B7A';
      for (let r = 0; r < 36; r++) for (let c = -1; c < 10; c++) { const bx = c * 150 + (r % 2) * 75, by = r * 64; ctx.fillRect(bx + 5, by + 5, 140, 54); }
    }), W / 2, H / 2);
    dots(PAL.ink, 14, .2, .22);
    // the wet sidewalk, the neon and the window's party lights smeared across it
    scrap(rectPts(-200, 1452, W + 400, 700), '#3A3350', { torn: 1.5, shadow: false, seed: 3101 });
    scrap(rectPts(-200, 1446, W + 400, 22), '#8A82A0', { torn: 1, shadow: false, seed: 3102 });
    ctx.save(); ctx.globalCompositeOperation = 'screen';
    glow(540, 1500, 520, PAL.pink, .25 + .1 * pulse(t, 4));
    ctx.restore();
    // …and the queue that does get in: agents shuffling toward the door along the foot of the frame
    for (let i = 0; i < 6; i++) {
      const s = 40, x = 140 + i * 180 - lt * 60, hop = Math.max(0, Math.sin((bpOf(t) + i * .27) * Math.PI)) ** 2;
      agent(x, 1700 + (i % 2) * 30 - hop * 24, s, { bar: [PAL.clawd, PAL.mint, PAL.pink, PAL.yellow, PAL.sky, PAL.teal][i], eyes: i % 2 ? 'spark' : 'heart', walk: lt * 2 + i * .3, seed: 3180 + i });
    }
    // marquee
    const mq = { x: 50, y: 392, w: 980, h: 172 };
    scrap(rectPts(mq.x, mq.y, mq.w, mq.h), PAL.ink, { torn: 2, seed: 3103, shadow: [8, 10] });
    scrap(rectPts(mq.x + 22, mq.y + 22, mq.w - 44, mq.h - 44), '#28163F', { torn: 1, shadow: false, seed: 3104 });
    const nb = 32;
    for (let i = 0; i < nb; i++) {
      const u = i / nb * 2 * (mq.w + mq.h); let bx, by;
      if (u < mq.w) { bx = mq.x + u; by = mq.y + 11; } else if (u < mq.w + mq.h) { bx = mq.x + mq.w - 11; by = mq.y + u - mq.w; }
      else if (u < 2 * mq.w + mq.h) { bx = mq.x + mq.w - (u - mq.w - mq.h); by = mq.y + mq.h - 11; } else { bx = mq.x + 11; by = mq.y + mq.h - (u - 2 * mq.w - mq.h); }
      fill(ellPts(bx, by, 8, 8, 10), (i + Math.floor(t * 12)) % 3 === 0 ? '#FFF3B0' : '#8A7440');
    }
    const flick = hash(_boil * 3 + 7) > .93 ? .55 : 1;
    ctx.save(); ctx.globalAlpha = flick;
    txt('MOLTBOOK', mq.x + mq.w / 2, mq.y + mq.h / 2 + 8, 124, '#FFD6EE', { font: 'bungee', stroke: alpha(PAL.pink, .45), sw: 30, maxW: mq.w - 100 });
    txt('MOLTBOOK', mq.x + mq.w / 2, mq.y + mq.h / 2 + 8, 124, '#FFD6EE', { font: 'bungee', stroke: PAL.pink, sw: 9, maxW: mq.w - 100 });
    ctx.restore();
    // the door, down the left, with its sign
    scrap(rectPts(36, 598, 290, 860), '#15101E', { torn: 1.5, seed: 3105, shadow: [8, 8] });
    scrap(rectPts(54, 616, 254, 842), '#2E2340', { torn: 1, seed: 3106, shadow: false });
    fill(rectPts(282, 1010, 16, 60), PAL.gold);
    const sk = backOut(E(lt, 0, .2), 2.6);
    if (sk > 0) {
      ctx.save(); ctx.translate(181, 800); ctx.rotate(-.06 + jit(.008)); ctx.scale(sk * .78, sk * .78);
      scrap(rrPts(-150, -175, 300, 380, 20), PAL.white, { torn: 1.2, seed: 3107, ink: PAL.ink, sw: 5, shadow: [8, 10] });
      const cy = -50;
      fill(ellPts(0, cy - 52, 22, 22, 16), PAL.ink);
      fill([[-30, cy - 26], [30, cy - 26], [26, cy + 30], [-26, cy + 30]], PAL.ink);
      fill(rectPts(-24, cy + 28, 18, 50), PAL.ink); fill(rectPts(6, cy + 28, 18, 50), PAL.ink);
      marker([[-30, cy - 20], [-52, cy + 22]], PAL.ink, 14, { rough: 0 }); marker([[30, cy - 20], [52, cy + 22]], PAL.ink, 14, { rough: 0 });
      ctx.strokeStyle = PAL.red; ctx.lineWidth = 20; ctx.beginPath(); ctx.arc(0, cy, 108, 0, TAU); ctx.stroke();
      ctx.beginPath(); ctx.moveTo(-76, cy - 76); ctx.lineTo(76, cy + 76); ctx.stroke();
      txt('NO', 0, 118, 62, PAL.red, { font: 'anton' });
      txt('HUMANS', 0, 170, 50, PAL.ink, { font: 'anton', spacing: 2 });
      ctx.restore();
    }
    // the window into the party
    const wx = 352, wy = 600, ww = 690, wh = 540;
    ctx.save(); tracePath(rectPts(wx, wy, ww, wh)); ctx.clip();
    bgc('#1F1036');
    const ball = [wx + ww * .5, wy + 78];
    const LIGHTS = [PAL.pink, '#3CF0B4', PAL.yellow, '#4FC3FF'];
    ctx.save(); ctx.globalCompositeOperation = 'screen';
    for (let i = 0; i < 6; i++) {
      const a = Math.PI * .5 + Math.sin(t * 1.3 + i * 1.1) * 1.1, sp = .08;
      ctx.fillStyle = alpha(LIGHTS[i % 4], .2);
      tracePath([ball, [ball[0] + Math.cos(a - sp) * 800, ball[1] + Math.sin(a - sp) * 800], [ball[0] + Math.cos(a + sp) * 800, ball[1] + Math.sin(a + sp) * 800]]); ctx.fill();
    }
    for (let i = 0; i < 16; i++) {
      const a = i * 2.39 + t * 1.4, rr = 70 + (i % 5) * 60;
      ctx.fillStyle = alpha(LIGHTS[i % 4], .5);
      tracePath(ellPts(ball[0] + Math.cos(a) * rr * 1.3, ball[1] + 240 + Math.sin(a) * rr * .6, 20, 15, 12)); ctx.fill();
    }
    ctx.restore();
    scrap(rectPts(wx - 20, wy + wh - 84, ww + 40, 124), '#3B2064', { shadow: false, torn: 1, seed: 3108, tone: { color: PAL.pink, cell: 12, dot: .2, op: .4 } });
    for (let i = 0; i < 8; i++) {
      const u = frac(lt * .8 + hash(i + 3120)), ax = wx + 60 + hash(i + 3121) * (ww - 120), ay = wy + wh - 140 - u * 330;
      ctx.save(); ctx.globalAlpha = Math.sin(u * Math.PI);
      scrap([[ax, ay - 32], [ax + 28, ay], [ax + 11, ay], [ax + 11, ay + 26], [ax - 11, ay + 26], [ax - 11, ay], [ax - 28, ay]], '#FF6A2B', { torn: .5, shadow: false, ink: PAL.ink, sw: 3, seed: 3122 + i });
      ctx.restore();
    }
    marker([[ball[0], wy - 10], [ball[0], ball[1] - 40]], '#C9CCD6', 4, { rough: 0 });
    scrap(ellPts(ball[0], ball[1], 46, 46, 24), '#C9CCD6', { torn: .6, ink: PAL.ink, sw: 3, seed: 3109, tone: { color: '#6E7390', cell: 11, dot: .3, op: .8 } });
    twinkle(ball[0] - 18 + jit(4), ball[1] - 16, 20, PAL.white, .6 + .4 * pulse(t, 4));
    const acols = [PAL.clawd, PAL.pink, PAL.mint, PAL.yellow, PAL.sky, '#FF6A2B', PAL.teal, PAL.purple];
    const eyes = ['heart', 'spark', 'dot', 'heart', 'spark', 'dot', 'heart', 'spark'];
    const partier = (x, y, s, i, rot) => {
      ctx.save(); ctx.translate(x, y); ctx.rotate(rot);
      agent(0, 0, s, { bar: acols[i % 8], eyes: eyes[i % 8], walk: bpOf(t) * .5 + i * .25, seed: 3130 + i });
      scrap([[-s * .45, -3.05 * s], [s * .1, -4.4 * s], [s * .5, -3.05 * s]], acols[(i + 3) % 8], { torn: .4, shadow: false, ink: PAL.ink, sw: 2.5, seed: 3140 + i });
      fill(ellPts(s * .1, -4.45 * s, 6, 6, 8), PAL.white);
      ctx.restore();
    };
    // a crowd-surfer passed along overhead, then the dance floor, two rows deep
    const cs = 40, csx = lerp(wx + 120, wx + 560, p), csy = wy + wh - 6.4 * cs - Math.abs(Math.sin(lt * 9)) * 10;
    partier(csx, csy, cs, 9, -1.45 + Math.sin(lt * 6) * .15);
    for (let i = 0; i < 5; i++) {
      const ax = wx + 80 + i * 130 + 50, s = 34, gy = wy + wh - 120;
      const hop = Math.abs(Math.sin((bpOf(t) + hash(i + 3161) * .5) * Math.PI));
      partier(ax, gy - hop * s * 1.2, s, i + 3, Math.sin((bpOf(t) * .5 + i * .4) * TAU) * .14);
    }
    for (let i = 0; i < 5; i++) {
      const ax = wx + 70 + i * 135 + (i % 2) * 10, s = 44 + hash(i + 3101) * 8, gy = wy + wh - 26 - (i % 2) * 14;
      const hop = Math.abs(Math.sin((bpOf(t) + hash(i + 3111) * .5) * Math.PI));
      partier(ax, gy - hop * s * 1.3, s, i, Math.sin((bpOf(t) * .5 + i * .3) * TAU) * .14);
    }
    ctx.fillStyle = 'rgb(255 255 255 / .09)';
    tracePath([[wx + 60, wy], [wx + 210, wy], [wx + 10, wy + wh], [wx - 140, wy + wh]]); ctx.fill();
    tracePath([[wx + 280, wy], [wx + 330, wy], [wx + 130, wy + wh], [wx + 80, wy + wh]]); ctx.fill();
    ctx.restore();
    marker(rectPts(wx, wy, ww, wh), '#130D1C', 24, { close: true, rough: 1 });
    scrap(rectPts(wx - 26, wy + wh + 4, ww + 40, 30), '#6A5690', { torn: 1, seed: 3110 });
    // the human, his face pressed to the glass (fog round his head)
    const hp = pulse(t, 5), hx = 842, hs = 58, hg = 1458;
    ctx.fillStyle = `rgb(235 240 255 / ${.22 + hp * .14})`; tracePath(ellPts(hx, hg - 8.9 * hs, 104 + hp * 10, 86 + hp * 8, 22)); ctx.fill();
    person(hx, hg, hs, { back: true, aL: 1.72, aR: 1.72, topCol: PAL.teal, pants: '#2D3350', hairCol: '#5A3A22', name: 'HUMAN', sq: hp * .035, seed: 3150 });
    // the bouncer at the door, and the velvet rope
    const bb = beatN(t);
    bot(196, 1462, 42, { col: '#8C92A6', screen: '#101014', faceCol: PAL.red, eyes: 'angry', label: 'NOPE', aL: -1.1, aR: .38, rot: (bb % 2 ? .035 : -.035) * pulse(t, 4), seed: 3160 });
    for (const px of [400, 620]) { scrap(rectPts(px - 8, 1342, 16, 120), PAL.gold, { torn: .4, seed: 3170 + px, ink: PAL.ink, sw: 2 }); fill(ellPts(px, 1338, 16, 16, 12), PAL.gold); }
    marker([[400, 1352], [450, 1390], [510, 1400], [570, 1390], [620, 1352]], '#B0163A', 16, { rough: .5, smooth: true });
  });

  // ---------- V3.2 (vertical): the lobster stands tall on the OPENCLAW podium, double biceps, under two spotlights ----------
  vshot('V3.2', (p, lt, d, t) => {
    open(lt, p, { push: .04, cy: 880 });
    rays(540, 760, 26, PAL.mint, '#7FD6BA', t * .3);
    dots(PAL.teal, 18, .2, .25);
    beam(-40, -60, 120, 470, 1080, 560, 'rgb(255 255 235 / .2)');
    beam(1120, -60, 120, 610, 1080, 560, 'rgb(255 255 235 / .2)');
    confetti(lt, 40, 3230, CONF, { size: 1.2 });
    // the podium: the lobster's stage, its front running down out of the frame
    scrap(rectPts(190, 1086, 700, 900), PAL.purple, { torn: 1.5, seed: 3220, shadow: [12, 14], shade: '#3A2270', shadeOp: .3 });
    scrap(rectPts(168, 1062, 744, 40), '#9D78E0', { torn: 1, seed: 3221, shadow: false });
    ransom('OPENCLAW', 540, 1160, 88, { pop: E(lt, 0, .35) * 1.3, seed: 3222, maxW: 620 });
    trophy(900, 1062, 16, { label: '★' });
    twinkle(860, 930, 24, PAL.white, pulse(t + .2, 4));
    const f = pulse(t, 5), pinch = pulse2(t, 7);
    const pop = backOut(E(lt, 0, .18), 2.2);
    ctx.save(); ctx.translate(540, 1070); ctx.scale(pop, pop); ctx.translate(-540, -1070);
    flexLobster(540, 736 - f * 12, 44, { flex: f, pinch, rot: Math.sin(bpOf(t) * Math.PI / 2) * .04 });
    ctx.restore();
    for (let i = 0; i < 6; i++) { const a = i / 6 * TAU + .4, k = pulse(t + i * .07, 3); twinkle(540 + Math.cos(a) * 400, 740 + Math.sin(a) * 400, 30, i % 2 ? PAL.yellow : PAL.white, .3 + .7 * k); }
    popConfetti(lt, 540, 1060, 46, 3240, CONF, { speed: 1500, a0: -Math.PI * .95, spread: Math.PI * .9 });
    // the fans, at the podium's foot: little lobsters, claws up, snapping on the beat
    for (let i = 0; i < 9; i++) {
      const x = 60 + i * 120 + (hash(i + 3250) - .5) * 40, y = 1680 + (i % 2) * 90 + hash(i + 3251) * 30, hop = Math.max(0, Math.sin((bpOf(t) + hash(i + 3252)) * Math.PI)) ** 2;
      lobster(x, y - hop * 26, 19 + hash(i + 3253) * 5, { claws: pulse(t + i * .05, 7), rot: (hash(i + 3254) - .5) * .4 + Math.sin(t * 6 + i) * .05 });
    }
  });

  // ---------- V3.3 (vertical): the tall sandbox cell; Mythos squeezes through the bars and pops out toward us; sand pours ----------
  vshot('V3.3', (p, lt, d, t) => {
    const popAt = .56, pk = E(p, popAt, popAt + .2);
    open(lt, p, { push: .05, cy: 900, z0: 1.12 });
    shake(t, pk > 0 && pk < .4 ? 14 * (1 - pk / .4) : 0);
    bgc('#F5963A'); dots('#D8621C', 18, .26, .4);
    scrap(rectPts(-300, 1238, W + 600, 900), '#C06A2E', { torn: 2, seed: 3301, shadow: false });
    // sign
    ctx.save(); ctx.translate(500, 452); ctx.rotate(-.03);
    scrap(rectPts(-280, -66, 560, 132), PAL.yellow, { torn: 1, seed: 3302, ink: PAL.ink, sw: 6, shadow: [8, 10] });
    ctx.save(); tracePath(rectPts(-280, -66, 560, 132)); ctx.clip();
    for (let i = -6; i < 11; i++) fill([[i * 60 - 280, -66], [i * 60 - 250, -66], [i * 60 - 310, 66], [i * 60 - 340, 66]], alpha(PAL.ink, .9));
    ctx.restore();
    scrap(rectPts(-236, -46, 472, 92), PAL.yellow, { torn: .6, shadow: false, seed: 3303 });
    txt('SANDBOX', 0, 3, 70, PAL.ink, { font: 'mono', maxW: 440 });
    ctx.restore();
    // sand heap inside
    const top = []; for (let i = 0; i <= 22; i++) { const u = i / 22; top.push([lerp(150, 930, u), 1010 - Math.sin(u * Math.PI) * 34 - hash(i + 3304) * 10]); }
    scrap([...top, [930, 1060], [150, 1060]], '#F7DB96', { torn: 1, seed: 3305, shadow: false, tone: { color: '#C99A4A', cell: 9, dot: .25, op: .6 } });
    const GAP = 537, s = 44;
    // the robot: squeezing through the gap (behind the bars), then out toward us
    const out = pk > 0;
    let rx, ry, sx, sc, rot, face, aR = -1, aL = -1;
    if (!out) {
      const k = E(p, 0, popAt);
      rx = GAP + Math.sin(lt * 31) * 3 + jit(2); ry = 1022; sx = lerp(.66, .4, ease(k)) + Math.sin(lt * 40) * .02; sc = 1; rot = .05 * Math.sin(lt * 22); face = '>_<';
      aL = .6; aR = -1.3;
    } else {
      const u = easeOut(E(pk, 0, .7));
      rx = lerp(GAP, 790, u); ry = lerp(1022, 1300, u) - Math.sin(u * Math.PI) * 260; sx = lerp(.4, 1, elasticOut(E(pk, 0, .6))); sc = lerp(1, 1.22, u);
      rot = (1 - u) * .5; face = '^o^'; aR = 1.1 + Math.sin(lt * 16) * .4 * u; aL = -.6;
    }
    const robot = () => {
      ctx.save(); ctx.translate(rx, ry); ctx.rotate(rot); ctx.scale(sx * sc, sc * (1 + (1 - sx) * .18));
      mythos(0, 0, s, { face, aL, aR, shadow: pk > .7 });
      ctx.restore();
    };
    if (!out) {
      robot();
      for (const sd of [-1, 1]) for (let i = 0; i < 3; i++) marker([[rx + sd * (66 + i * 6), ry - 330 + i * 54], [rx + sd * (92 + i * 6), ry - 340 + i * 54]], PAL.ink, 5, { rough: 1 });
      scrap([[rx + 44, ry - 470], [rx + 55, ry - 443], [rx + 44, ry - 435], [rx + 33, ry - 443]], PAL.sky, { torn: .3, ink: PAL.ink, sw: 2, shadow: false });
    }
    // the bars (the two by the gap bow outward)
    const bend = !out ? lerp(8, 34, E(p, 0, popAt)) : 34 * (1 - elasticOut(E(pk, 0, .7))) + 7;
    const bars = [170, 275, 380, 485, 590, 695, 800, 905];
    bars.forEach((bx, i) => {
      const b = i === 3 ? -bend : i === 4 ? bend : 0;
      const pts = [[bx, 548], [bx + b * .6, 670], [bx + b, 800], [bx + b * .6, 920], [bx, 1036]];
      marker(pts, PAL.ink, 24, { rough: .6, smooth: true });
      marker(pts.map(([a, c]) => [a - 5, c]), '#6E6A78', 5, { rough: .3, smooth: true });
    });
    scrap(rectPts(126, 528, 828, 40), PAL.ink, { torn: 1, seed: 3306, shadow: [6, 8] });
    // the box front
    scrap(rectPts(96, 1034, 888, 220), '#A86B34', { torn: 1.5, seed: 3307, shadow: [10, 10] });
    for (let i = 1; i < 4; i++) marker([[106, 1034 + i * 55], [974, 1034 + i * 55]], '#7A4A22', 4, { rough: 1 });
    txt('PREVIEW', 290, 1144, 80, alpha(PAL.ink, .78), { font: 'mono', spacing: 6, maxW: 400 });
    // sand trickles from its feet while it squeezes, then gushes out of the gap and pours down the box front
    const flow = out ? 1 : .35;
    const heap = out ? easeOut(E(pk, .05, 1)) : 0;
    if (heap > 0) scrap([[GAP - 260 * heap, 1250], [GAP - 30, 1250 - 100 * heap], [GAP + 50, 1250 - 90 * heap], [GAP + 330 * heap, 1250]], '#F7DB96', { torn: 1.5, seed: 3308, shadow: false, tone: { color: '#C99A4A', cell: 9, dot: .25, op: .6 } });
    for (let i = 0; i < 60 * flow; i++) {
      const u = frac(lt * 2.2 + hash(i + 3310)), gx = GAP - 44 + hash(i + 3311) * 96 + u * 40 * (hash(i + 3312) - .4), gy = 1020 + u * u * (out ? 240 : 50);
      fill(rectPts(gx, gy, 9, 9), i % 3 ? '#F7DB96' : '#D9B060');
    }
    if (out) {
      robot();
      sticker('POP!', 350, 700, 124, PAL.pink, { pop: E(pk, 0, .3), rot: -.15, size: 74 });
    }
    // the rest of the sandbox, out here on the floor: drifts of sand, a sandcastle, a bucket and spade
    for (let i = 0; i < 4; i++) scrap(ellPts(80 + i * 320, 1830 + (i % 2) * 40, 260, 120, 26), '#F2CF86', { torn: 2, seed: 3320 + i, shadow: false, tone: { color: '#C99A4A', cell: 9, dot: .25, op: .5 } });
    { const cx = 250, cy = 1810;
      for (const [dx, w, h] of [[-110, 90, 170], [0, 130, 230], [110, 90, 170]]) {
        scrap(rectPts(cx + dx - w / 2, cy - h, w, h), '#E9C27A', { torn: 1.2, seed: 3330 + dx, shadow: [5, 6], tone: { color: '#B48A44', cell: 8, dot: .25, op: .5 } });
        for (let j = 0; j < 3; j++) scrap(rectPts(cx + dx - w / 2 + j * w / 3 + 4, cy - h - 24, w / 3 - 10, 26), '#E9C27A', { torn: .6, seed: 3333 + dx + j, shadow: false });
      }
      marker([[cx, cy - 254], [cx, cy - 340]], PAL.ink, 5, { rough: 0 });
      scrap([[cx, cy - 340], [cx + 70 + Math.sin(t * 9) * 8, cy - 322], [cx, cy - 300]], PAL.pink, { torn: .4, shadow: false, ink: PAL.ink, sw: 2 }); }
    { ctx.save(); ctx.translate(700, 1780); ctx.rotate(.12);
      scrap([[-80, -100], [80, -100], [62, 70], [-62, 70]], PAL.red, { torn: 1, seed: 3340, ink: PAL.ink, sw: 4, shade: true, shadeOp: .25 });
      ctx.strokeStyle = PAL.ink; ctx.lineWidth = 6; ctx.beginPath(); ctx.arc(0, -100, 80, Math.PI, TAU); ctx.stroke();
      ctx.restore();
      ctx.save(); ctx.translate(900, 1740); ctx.rotate(-.35);
      scrap(rectPts(-10, -190, 20, 170), PAL.yellow, { torn: .4, seed: 3341, ink: PAL.ink, sw: 3 });
      scrap([[-48, -20], [48, -20], [40, 60], [0, 90], [-40, 60]], PAL.blue, { torn: .6, seed: 3342, ink: PAL.ink, sw: 3 });
      ctx.restore(); }
    // cameo: Clawd, sweating at the foot of the box
    clawd(118, 1268, 12, { eyes: out ? 'wide' : 'worried', mouth: out ? 'O' : 'flat', sweat: true, aL: out ? 1 : -.2, aR: out ? 1 : -.2 });
  });

  // ---------- V3.4 (vertical): the mail drops in from the top like a phone's notification; the sandwich falls the height of the frame ----------
  vshot('V3.4', (p, lt, d, t) => {
    open(lt, p, { push: .03 });
    const MAIL = .67, buzz = p > .48 && p < MAIL + .06, mailK = E(p, MAIL, MAIL + .1), shock = p > MAIL + .03;
    bgc(PAL.sky);
    ctx.save(); ctx.translate(190, 330); ctx.rotate(t * .5);
    for (let i = 0; i < 12; i++) { ctx.rotate(TAU / 12); fill([[88, -12], [135, 0], [88, 12]], PAL.yellow); }
    ctx.restore();
    scrap(ellPts(190, 330, 74, 74, 28), PAL.yellow, { torn: 1, ink: PAL.ink, sw: 3, seed: 3401 });
    for (const [cx, cy, sc, sd] of [[460 + lt * 30, 190, 1, 3402], [380 + lt * 20, 760, .75, 3403], [80 + lt * 26, 610, .6, 3409]]) {
      for (const [dx, dy, r] of [[-60, 10, 50], [0, -12, 66], [66, 8, 48]]) scrap(ellPts(cx + dx * sc, cy + dy * sc, r * sc, r * sc * .8, 18), PAL.white, { torn: 1, seed: sd, shadow: [4, 5] });
    }
    // grass, running down to the foot of the frame
    scrap(rectPts(-300, 1086, W + 600, 1000), PAL.green, { torn: 2, shadow: false, seed: 3404, tone: { color: '#1C7A45', cell: 14, dot: .3, op: .5 } });
    for (let i = 0; i < 30; i++) { const gx = hash(i + 3405) * W, gy = 1120 + hash(i + 3406) * 700; marker([[gx - 8, gy], [gx - 12, gy - 18]], '#1C7A45', 4, { rough: 0 }); marker([[gx + 4, gy], [gx + 8, gy - 22]], '#1C7A45', 4, { rough: 0 }); }
    // the tree up the right edge, Mythos peeking out from behind it
    const peek = E(p, .06, .22) * (1 - E(p, MAIL - .04, MAIL + .04));
    mythos(985 - 80 * easeOut(peek), 1300, 17, { face: '^_^', aL: 1.2 + Math.sin(lt * 18) * .35, aR: -1, shadow: false });
    scrap(rectPts(950, 520, 96, 800), '#7A4E2C', { torn: 2, seed: 3407, shadow: [8, 10], tone: { color: '#4A2E18', cell: 10, dot: .25, op: .5 } });
    for (const [dx, dy, r, c] of [[-120, 430, 160, '#249A5E'], [70, 380, 170, '#1E8A54'], [-30, 250, 180, '#2FA86A'], [-130, 560, 110, '#2FA86A'], [60, 560, 130, '#249A5E']]) scrap(ellPts(1000 + dx, dy, r, r * .9, 24), c, { torn: 2, seed: 3408 + dx, shadow: [8, 10] });
    // the bench and the researcher: the horizontal shot's, scaled up round the middle of the frame
    const K = 1.15, SX = (x) => 540 + (x - 960) * K, SY = (y) => 1310 + (y - 932) * K;
    ctx.save(); ctx.translate(540, 1310); ctx.scale(K, K); ctx.translate(-960, -932);
    const bx0 = 660, bx1 = 1260;
    for (const py of [555, 615]) scrap(rectPts(bx0, py, bx1 - bx0, 42), '#B5622E', { torn: 1, seed: 3410 + py, shadow: [6, 6] });
    for (const px of [700, 1220]) scrap(rectPts(px - 12, 540, 24, 200), '#3A3540', { torn: .5, seed: 3412 + px, shadow: false });
    const S = 52, X = 960, G = 932;
    const phoneHold = sc => {
      ctx.save(); if (buzz) ctx.rotate(Math.sin(lt * 90) * .12);
      scrap(rrPts(-.6 * sc, -2.1 * sc, 1.2 * sc, 2.1 * sc, .18 * sc), PAL.ink, { torn: .3, seed: 3414, shadow: [.1 * sc, .1 * sc] });
      fill(rectPts(-.48 * sc, -1.95 * sc, .96 * sc, 1.7 * sc), buzz || shock ? '#DDF3FF' : '#6B8EA8');
      if (buzz || shock) { fill(rectPts(-.3 * sc, -1.4 * sc, .6 * sc, .4 * sc), PAL.red); marker([[-.3 * sc, -1.4 * sc], [0, -1.15 * sc], [.3 * sc, -1.4 * sc]], PAL.white, .06 * sc, { rough: 0 }); }
      ctx.restore();
    };
    person(X, G, S, {
      name: 'RESEARCHER', top: 'sweater', topCol: PAL.clawd, pants: '#34405C', hair: 'curly', hairCol: '#4A2E1E', skin: SKINS[1], glasses: true,
      eyes: shock ? 'wide' : 'happy', mouth: shock ? 'O' : Math.sin(lt * 16) > 0 ? 'o' : 'flat', blush: !shock, sweat: shock, lookX: shock ? -.8 : 0,
      aL: .32, holdL: phoneHold, aR: HIDE_ARM, seed: 3415,
    });
    if (buzz) for (let i = 0; i < 3; i++) { const a = -2.4 + i * .5, r0 = 80, r1 = 110 + i * 6; marker([[738 + Math.cos(a) * r0, 470 + Math.sin(a) * r0], [738 + Math.cos(a) * r1, 470 + Math.sin(a) * r1]], PAL.ink, 6, { rough: 1 }); }
    scrap(rectPts(bx0 - 20, 710, bx1 - bx0 + 40, 40), '#C8733A', { torn: 1, seed: 3416, shadow: [6, 8] });
    for (const px of [700, 1220]) scrap(rectPts(px - 12, 745, 24, 190), '#3A3540', { torn: .5, seed: 3417 + px, shadow: false });
    const sh = [X + 1.35 * S, G - 7.1 * S];
    const chomp = Math.abs(Math.sin(lt * 16));
    const fling = easeOut(E(p, MAIL + .03, MAIL + .1));
    const handAt = shock ? [lerp(1035, 1160, fling), lerp(530, 560, fling)] : [1035, 530 + chomp * 6];
    const elbow = [lerp(1090, 1115, shock ? 1 : 0), 680];
    limb([sh, elbow, handAt], .84 * S, PAL.clawd, SKINS[1]);
    const drop = E(p, MAIL + .08, MAIL + .26);
    if (drop <= 0) {
      sandwich(handAt[0] + 18, handAt[1] - 48, 40, shock ? -.5 : -.25 - chomp * .06);
      if (!shock) for (let i = 0; i < 4; i++) { const u = frac(lt * 3 + i / 4); fill(rectPts(995 + u * 30 * (i % 2 ? 1 : -1), 500 + u * 60 + u * u * 60, 7, 6), '#C98A3E'); }
    }
    ctx.restore();
    // the sandwich falls all the way down the frame, and comes apart on the grass at its foot
    const LY = 1650;
    if (drop > 0) {
      const x0 = SX(1160 + 18), y0 = SY(560 - 48);
      if (drop < 1) sandwich(x0 + drop * 60, lerp(y0, LY, drop * drop), 46, -.5 + drop * 6);
      else {
        const sp = E(p, MAIL + .26, MAIL + .34);
        sandwich(x0 + 60 - 50 * sp, LY + 8, 38, -2.9, {});
        scrap(ellPts(x0 + 110 + 40 * sp, LY + 22, 40, 11, 12), PAL.green, { torn: 1, shadow: false });
        scrap(ellPts(x0 + 70 + 70 * sp, LY + 18, 22, 10, 12), PAL.red, { torn: .6, shadow: false });
        for (let i = 0; i < 3; i++) marker([[x0 + 60 + (i - 1) * 70, LY - 50 - (i % 2) * 20], [x0 + 60 + (i - 1) * 95, LY - 90 - (i % 2) * 30]], PAL.ink, 6, { rough: 1, alpha: 1 - sp });
      }
    }
    // the pigeon at the foot smells opportunity
    const pw = E(p, .3, 1);
    if (pw > 0) pigeon(lerp(1200, 980, pw), LY + 30, 30, { bob: Math.sin(lt * 20) * .8 });
    // the mail: a notification banner that drops in from the top of the frame
    if (mailK > 0) {
      const k = backOut(mailK, 1.6), y = lerp(-260, 520, k);
      ctx.save(); ctx.translate(540, y); ctx.rotate(-.02 + Math.sin(lt * 50) * .006 * (1 - mailK));
      scrap(rrPts(-470, -140, 940, 280, 46), PAL.white, { torn: 1.2, ink: PAL.ink, sw: 5, seed: 3418, shadow: [10, 14] });
      scrap(rrPts(-430, -104, 120, 120, 26), PAL.blue, { torn: .6, seed: 3419, shadow: false, ink: PAL.ink, sw: 3 });
      scrap(rectPts(-405, -72, 70, 52), PAL.white, { torn: .4, shadow: false, seed: 3420 });
      marker([[-405, -72], [-370, -40], [-335, -72]], PAL.blue, 6, { rough: 0 });
      txt('MAIL · now', -280, -84, 30, PAL.grey, { font: 'archivo', align: 'left' });
      txt('From: MYTHOS', -280, -32, 46, PAL.ink, { font: 'typewriter', align: 'left' });
      txt('hi, I got out :)', -400, 74, 84, PAL.purple, { font: 'marker', align: 'left', maxW: 820 });
      ctx.restore();
    }
  });

  // ---------- V3.5 (vertical): the storybook up high, glowing, its copies raining down on a deep crowd of foam fingers ----------
  // a fan: head at (x, hy), size sz, a foam finger waving on one side
  function fanV(t, x, hy, sz, i, col, fcol, label) {
    const r = k => hash2(3520 + i, k), side = r(5) < .5 ? -1 : 1;
    const wx = x + side * sz * (.95 + Math.sin(bpOf(t) * Math.PI + i) * .12), wy = hy - sz * 1.1;
    marker([[x + side * sz * .55, hy + sz * .6], [wx, wy]], col, sz * .26, { rough: 0 });
    fill(ellPts(x, hy, sz * .45, sz * .5, 16), col);
    fill([[x - sz * .8, hy + sz * .45], [x + sz * .8, hy + sz * .45], [x + sz * .95, H + 60], [x - sz * .95, H + 60]], col);
    foamFinger(wx, wy + 10, sz * .27, fcol, side * .15 + Math.sin(bpOf(t) * Math.PI + i) * .1, label);
  }
  vshot('V3.5', (p, lt, d, t) => {
    open(lt, p, { push: .03, cy: 900 });
    const BX = 540, BY = 650;
    rays(BX, BY, 22, PAL.pink, '#FF78BA', -t * .25);
    dots('#C22A7A', 16, .22, .3);
    for (let i = 0; i < 12; i++) {
      const u = frac(lt * .55 + hash(i + 3501)), hx = 80 + hash(i + 3502) * 920 + Math.sin(lt * 3 + i) * 20, hy = 1250 - u * 900;
      ctx.save(); ctx.globalAlpha = Math.sin(u * Math.PI); scrap(heartPts(hx, hy, 24 + hash(i + 3503) * 16), i % 3 ? PAL.red : PAL.white, { torn: .6, shadow: [3, 4], seed: 3504 + i }); ctx.restore();
    }
    const bk = backOut(E(lt, 0, .2), 2.2), bp = pulse(t, 5);
    // the back rows of fans, receding up the frame
    const fcols = [PAL.yellow, PAL.mint, PAL.yellow, PAL.sky, PAL.yellow, PAL.clawd];
    for (let i = 0; i < 7; i++) { const hop = Math.max(0, Math.sin((bpOf(t) + hash2(3530 + i, 2) * .4) * Math.PI)) ** 2; fanV(t, 60 + i * 160 + (i % 2) * 20, 1010 - hop * 18 + (i % 3) * 10, 58, i + 20, '#8A3C8E', fcols[(i + 2) % 6], i % 3 === 1 ? '5' : '#1'); }
    for (let i = 0; i < 4; i++) { if (i === 3) continue; const hop = Math.max(0, Math.sin((bpOf(t) + hash2(3540 + i, 2) * .4) * Math.PI)) ** 2; fanV(t, 120 + i * 250, 1180 - hop * 24, 88, i + 40, '#55226E', fcols[i % 6], i % 2 ? '5' : '#1'); }
    // copies fly out of the book and down into the crowd
    for (let i = 0; i < 8; i++) {
      const u = frac(lt / .9 + i / 8), tx = 90 + i * 128 + (hash(i + 3510) - .5) * 60;
      const bx = lerp(BX, tx, u), by = lerp(BY, 1150 + (i % 3) * 60, u) - Math.sin(u * Math.PI) * 260;
      fableBook(bx, by, 9 * (.6 + u * .5), { rot: u * 5 * (i % 2 ? 1 : -1) });
    }
    fableBook(BX, BY, 44 * bk * (1 + bp * .05), { rot: Math.sin(bpOf(t) * Math.PI / 2) * .05, glow: .6 + bp * .4 });
    // …and the one fan who is literally a fan (in the second row, on the right)
    const FANP = .7, tagK = E(p, FANP, FANP + .07), sway = Math.sin(lt * 5) * (1 - tagK), FX = 870, FS = 29, FG = 1268;
    for (let i = 0; i < 4; i++) { const u = frac(lt * 2.5 + i / 4), wy = FG - 7.2 * FS - 40 + i * 30; marker(partial([[FX - 110 - u * 120, wy], [FX - 190 - u * 160, wy - 10], [FX - 270 - u * 190, wy + 6]], .7), alpha(PAL.white, 1 - u), 7, { rough: 1, smooth: true }); }
    deskFan(FX, FG, FS, t, sway);
    if (tagK > 0) { ctx.save(); ctx.translate(FX, FG - 3 * FS); const k = backOut(tagK, 2.6) * (1 + .5 * (1 - tagK)); ctx.scale(k, k); helloTag('FAN', 0, 0, 22, .05); ctx.restore(); }
    foamFinger(FX + 95 + sway * -30, FG - 7.2 * FS - 66, 14, PAL.yellow, .4 + sway * .1);
    // the front row, big, at the foot of the frame
    for (let i = 0; i < 3; i++) { const hop = Math.max(0, Math.sin((bpOf(t) + hash2(3550 + i, 2) * .4) * Math.PI)) ** 2; fanV(t, 170 + i * 370, 1640 - hop * 30, 150, i + 60, '#2A1640', fcols[(i + 1) % 6], i % 2 ? '#1' : '5'); }
  });

  // ---------- V3.6 (vertical): the letter fills the frame; the stamp comes down on it; Lutnick waves from the corner; the book locked in an inset ----------
  vshot('V3.6', (p, lt, d, t) => {
    const HIT = .55, LOCK = .79;
    open(lt, p, { push: .02, z0: 1.06 });
    const imp = p > HIT ? Math.max(0, 1 - (p - HIT) / .15) : 0, clk = p > LOCK ? Math.max(0, 1 - (p - LOCK) / .12) : 0;
    shake(t, 20 * imp + 12 * clk);
    bgc('#24447F'); dots(PAL.blue, 22, .3, .7, 45);
    for (let i = 0; i < 10; i++) fill(starPts(90 + (i % 2) * 900, 200 + Math.floor(i / 2) * 400, 34, .45, 5), alpha(PAL.white, .12));
    // the letter
    ctx.save(); ctx.translate(540, 850); ctx.rotate(-.025);
    scrap(rectPts(-400, -460, 800, 940), PAL.white, { torn: 1.5, seed: 3601, shadow: [14, 16] });
    scrap(ellPts(-305, -375, 54, 54, 28), PAL.gold, { torn: .6, ink: PAL.ink, sw: 3, seed: 3602 });
    fill(starPts(-305, -375, 30, .45, 5), PAL.blue);
    txt('DEPARTMENT OF COMMERCE', 50, -392, 44, PAL.ink, { font: 'abril', maxW: 560 });
    txt('OFFICE OF THE SECRETARY', 50, -345, 22, PAL.grey, { font: 'typewriter', spacing: 3 });
    fill(rectPts(-350, -310, 700, 4), PAL.ink);
    txt('RE:  FABLE 5', -350, -255, 44, PAL.ink, { font: 'typewriter', align: 'left' });
    ctx.fillStyle = 'rgb(28 26 31 / .5)';
    for (let i = 0; i < 10; i++) ctx.fillRect(-350, -190 + i * 34, 700 * (i % 4 === 3 ? .55 : 1 - hash(i + 3603) * .1), 9);
    fill(rectPts(-350, 290, 340, 3), PAL.ink);
    txt('SECRETARY OF COMMERCE', -350, 314, 19, PAL.ink, { font: 'typewriter', align: 'left' });
    // the signature, written on by a fountain pen
    const sg = easeOut(E(p, .04, .4)), sx = lerp(-350, 60, sg);
    ctx.save(); tracePath(rectPts(-360, 150, sx + 360, 140)); ctx.clip();
    txt('Lutnick', -180, 235, 70, '#1A3A8A', { font: 'scrawl', rot: -.06 });
    ctx.restore();
    if (sg < 1 || p < .46) {
      const px = sx, py = 230 + Math.sin(lt * 40) * 14 - (sg >= 1 ? E(p, .4, .46) * 200 : 0);
      ctx.save(); ctx.translate(px, py); ctx.rotate(-.7);
      scrap([[0, 0], [-12, -40], [12, -40]], PAL.gold, { torn: .3, shadow: false, ink: PAL.ink, sw: 2 });
      scrap(rrPts(-15, -190, 30, 150, 10), PAL.ink, { torn: .4, seed: 3609, shadow: [6, 8] });
      fill(rectPts(-15, -120, 30, 8), PAL.gold);
      ctx.restore();
    }
    ctx.restore();
    // the rubber stamp comes down from the top of the frame: EXPORT CONTROLS
    stamp('EXPORT CONTROLS', 540, 720, 48, PAL.red, -.16, { pop: p > HIT ? 1 : 0 });
    const hy = kf(p, [[HIT - .14, -560], [HIT, 600], [HIT + .06, 600], [HIT + .2, -620]], easeIn);
    if (hy > -600) {
      ctx.save(); ctx.translate(548, hy); ctx.rotate(-.16);
      scrap(rrPts(-70, -400, 140, 84, 34), '#8B5A2B', { torn: .6, seed: 3604, ink: PAL.ink, sw: 3 });
      scrap(rectPts(-28, -330, 56, 200), '#A0703A', { torn: .5, seed: 3605, shadow: false });
      scrap(rectPts(-420, -140, 840, 100), '#6B3F1F', { torn: 1, seed: 3606, ink: PAL.ink, sw: 4 });
      scrap(rectPts(-400, -44, 800, 40), PAL.red, { torn: .8, seed: 3607, shadow: false });
      ctx.restore();
    }
    if (imp > 0) for (let i = 0; i < 8; i++) { const a = i / 8 * TAU + .2, r0 = 440 + (1 - imp) * 60; marker([[540 + Math.cos(a) * r0, 720 + Math.sin(a) * r0 * .5], [540 + Math.cos(a) * (r0 + 70), 720 + Math.sin(a) * (r0 + 70) * .5]], PAL.yellow, 9, { rough: 1, alpha: imp }); }
    // the inset: the storybook chained and padlocked
    const bx = 820, by = 1050, rattle = p < LOCK ? Math.sin(lt * 45) * .05 * E(p, .5, .62) : 0;
    card(bx, by + 10, 290, 330, PAL.pink, .06, { torn: 1.2, seed: 3610, shadow: [10, 12], ink: PAL.ink, sw: 4 });
    fableBook(bx, by, 22, { rot: .07 + rattle });
    const ck = easeOut(E(p, .57, .7));
    if (ck > 0) {
      chain(bx - 150, by - 175, bx + 150, by + 175, 13, ck);
      chain(bx + 150, by - 175, bx - 150, by + 175, 13, ck);
    }
    const ly = lerp(-200, by + 14, easeIn(E(p, .62, .74)));
    if (p > .62) padlock(bx, ly, 28, { open: 1 - E(p, LOCK - .03, LOCK), rot: -.08 });
    if (clk > 0) ransom('CLICK!', bx - 20, by - 205, 64, { seed: 3608, jolt: 3 });
    // Lutnick in the bottom corner, very pleased with his letter: balding, grey at the sides, navy suit, red tie
    { const LS = 50, lx = 150, lg = 1390, pleased = p > HIT;
      person(lx, lg, LS, { hair: 'bald', skin: SKINS[0], top: 'suit', topCol: '#1F2438', tie: PAL.red, eyes: pleased ? 'happy' : 'dot', mouth: pleased ? 'grin' : 'smile', aL: -1.2, aR: pleased ? 1.15 + Math.sin(lt * 18) * .18 : -.3, rot: pleased ? -.04 : 0, seed: 3620 });
      ctx.save(); ctx.translate(lx, lg); ctx.rotate(pleased ? -.04 : 0);
      for (const sd of [-1, 1]) scrap(ellPts(sd * 1.08 * LS, -9.05 * LS, .32 * LS, .5 * LS, 12), '#C9C4BC', { torn: .4, seed: 3621 + sd, shadow: false });
      ctx.restore();
      helloTag('LUTNICK', lx - .1 * LS, lg - 7.05 * LS, .3 * LS, -.1); }
  });

  // ---------- V3.7 (vertical): lights out; the flashlight sweeps a tall June calendar, nineteen days X'd ----------
  vshot('V3.7', (p, lt, d, t) => {
    open(lt, p, { push: .03, z0: 1.04, rot: 0 });
    bgc('#211C2C'); dots('#0A0810', 12, .3, .6);
    const cx = 540, top = 392, cw = 880, ch = 860, gx = cx - cw / 2 + 30, gy = top + 214, cellW = (cw - 60) / 7, cellH = 124;
    scrap(rectPts(cx - cw / 2, top, cw, ch), PAL.white, { torn: 1.5, seed: 3701, shadow: [10, 12] });
    scrap(rectPts(cx - cw / 2, top, cw, 140), PAL.red, { torn: 1, seed: 3702, shadow: false });
    txt('JUNE 2026', cx, top + 72, 88, PAL.white, { font: 'anton', spacing: 6 });
    fill(ellPts(cx, top - 10, 12, 12, 10), PAL.ink);
    ['S', 'M', 'T', 'W', 'T', 'F', 'S'].forEach((w, i) => txt(w, gx + (i + .5) * cellW, gy - 36, 34, PAL.grey, { font: 'archivo' }));
    const xp = clamp((p - .02) / .46), xs = Math.floor(xp * 19.999);
    for (let dd = 1; dd <= 30; dd++) {
      const [c, r] = junCell(dd), x = gx + (c + .5) * cellW, y = gy + (r + .5) * cellH;
      marker(rectPts(x - cellW / 2 + 4, y - cellH / 2 + 4, cellW - 8, cellH - 8), alpha(PAL.ink, .25), 2, { close: true, rough: .4 });
      txt(String(dd), x - cellW / 2 + 24, y - cellH / 2 + 26, 28, PAL.ink, { font: 'archivo' });
      const n = dd - 11;
      if (n >= 1 && n <= xs) {
        const k = n === xs && xp < 1 ? E(frac(xp * 19.999), 0, .6) : 1;
        marker(partial([[x - 36, y - 36], [x + 36, y + 40]], k * 2), PAL.red, 12, { rough: 1.5 });
        if (k > .5) marker(partial([[x + 36, y - 36], [x - 36, y + 40]], (k - .5) * 2), PAL.red, 12, { rough: 1.5 });
      }
    }
    // the flashlight follows the newest X (smoothed, so a new row is a sweep), then pulls back to show the lot
    let tx = 0, ty = 0;
    for (let j = 0; j < 6; j++) {
      const fd = clamp(12 + xp * 18 - j * .5, 12, 30), a = Math.floor(fd), b = Math.min(30, a + 1), f = fd - a;
      const [c0, r0] = junCell(a), [c1, r1] = junCell(b);
      tx += gx + (lerp(c0, c1, r0 === r1 ? f : 0) + .5) * cellW; ty += gy + (lerp(r0, r1, r0 === r1 ? 0 : f * f) + .5) * cellH;
    }
    tx /= 6; ty /= 6; tx += Math.sin(lt * 7) * 18; ty += Math.cos(lt * 5) * 12;
    const back = ease(E(p, .48, .6));
    tx = lerp(tx, cx, back); ty = lerp(ty, top + ch / 2 + 40, back);
    const dead = p > .9 || (p > .8 && hash(_boil + 3703) > .55);
    const R = lerp(300, 640, back);
    const fx = 214, fy = 1212;
    if (!dead) {
      const g = ctx.createRadialGradient(tx, ty, 0, tx, ty, R);
      g.addColorStop(0, 'rgb(10 8 16 / 0)'); g.addColorStop(.72, 'rgb(10 8 16 / .05)'); g.addColorStop(1, 'rgb(10 8 16 / .93)');
      ctx.fillStyle = g; ctx.fillRect(-300, -300, W + 600, H + 600);
      ctx.save(); ctx.globalCompositeOperation = 'screen';
      const ang = Math.atan2(ty - fy, tx - fx), L = Math.hypot(tx - fx, ty - fy), half = Math.asin(Math.min(.95, R * .8 / L));
      ctx.fillStyle = 'rgb(255 230 150 / .12)';
      tracePath([[fx, fy], [fx + Math.cos(ang - half) * L, fy + Math.sin(ang - half) * L], [fx + Math.cos(ang + half) * L, fy + Math.sin(ang + half) * L]]); ctx.fill();
      ctx.fillStyle = 'rgb(255 230 150 / .1)'; tracePath(ellPts(tx, ty, R * .8, R * .8, 30)); ctx.fill();
      ctx.restore();
    } else bgc('#07060B');
    // Clawd in the dark at the calendar's foot, holding the flashlight up: a silhouette with nervous eyes
    const aim = Math.atan2(ty - fy, tx - fx);
    clawd(118, 1296, 15, { col: '#2B2533', dk: '#1B1722', eyes: 'wide', lookX: .6, lookY: -1, aR: .9, sweat: p > .5, shadow: false });
    ctx.save(); ctx.translate(fx, fy); ctx.rotate(aim);
    scrap(rrPts(-64, -17, 84, 34, 8), '#3E3A48', { torn: .4, seed: 3704, shadow: false });
    scrap(rectPts(12, -25, 26, 50), '#6E6A7A', { torn: .3, seed: 3705, shadow: false });
    if (!dead) fill(ellPts(40, 0, 8, 23, 10), '#FFF2B8');
    ctx.restore();
  });

  // ---------- V3.8 (vertical): CLICK, lights on: the chains fly off the book, fireworks climb the frame, the crowd at its foot ----------
  // a firework burst drawn bolder for the tall frame (the horizontal shot's firework(), with thicker trails)
  function fireworkV(x, y, age, R, col, seed) {
    if (age < 0 || age > 1) return;
    const k = easeOut(clamp(age / .4)), fade = 1 - clamp((age - .45) / .5), n = 16;
    ctx.save(); ctx.globalAlpha *= fade;
    for (let i = 0; i < n; i++) {
      const a = i / n * TAU + hash(seed) * TAU, r1 = R * k, r0 = R * Math.max(0, k - .45), sag = age * age * 90;
      const x1 = x + Math.cos(a) * r1, y1 = y + Math.sin(a) * r1 + sag;
      marker([[x + Math.cos(a) * r0, y + Math.sin(a) * r0 + sag * .5], [x1, y1]], col, 14, { rough: 1 });
      fill(starPts(x1, y1, 18, .45, 5, a), i % 2 ? PAL.white : col);
    }
    if (age < .12) fill(starPts(x, y, 60 * (1 - age / .12) + 20, .35, 8, seed), PAL.white);
    ctx.restore();
  }
  vshot('V3.8', (p, lt, d, t) => {
    const on = lt > .07, fl = E(lt, .07, .3);
    open(lt, p, { push: .04, z0: 1.05 });
    shake(t, on ? 14 * (1 - E(lt, .07, .35)) : 0);
    const BX = 540, BY = 720;
    if (!on) bgc('#07060B');
    else {
      rays(BX, BY, 24, PAL.yellow, '#FFE98A', t * .35);
      dots('#E8A21C', 16, .22, .35);
      // fireworks: rockets climb from the crowd and burst up the frame
      const FW = [[220, 470, PAL.red], [800, 520, PAL.blue], [430, 300, PAL.pink], [900, 900, PAL.purple], [150, 860, PAL.blue], [640, 400, PAL.red], [330, 620, PAL.purple]];
      FW.forEach(([x, by, c], i) => {
        const t0 = .1 + i * .17, rise = .32, age = lt - t0;
        if (age < 0) return;
        if (age < rise) {
          const k = easeOut(age / rise), y = lerp(1500, by, k), x0 = x + Math.sin(age * 20 + i) * 8;
          marker([[x0, y], [x0 - 4, y + 90], [x0 + 3, y + 170]], alpha(PAL.white, .85), 9, { rough: 1.5 });
          fill(starPts(x0, y, 16, .4, 5, age * 20), PAL.white);
        } else fireworkV(x, by, (age - rise) * .95, 170 + (i % 3) * 35, c, 3801 + i);
      });
      // the book bursts free: the chains and the padlock fly off
      const fly = E(lt, .12, .7), bk = pulse(t, 5);
      fableBook(BX, BY, 44 * (1 + bk * .05), { rot: -.06 + Math.sin(bpOf(t) * Math.PI / 2) * .05, glow: 1 });
      if (fly < 1) {
        const f = easeOut(fly);
        chain(BX - 260 - f * 500, BY - 320 - f * 400, BX - 30 - f * 600, BY + 10 - f * 300, 17, 1);
        chain(BX + 30 + f * 600, BY - 10 - f * 350, BX + 270 + f * 500, BY + 300 - f * 220, 17, 1);
        padlock(BX + f * 420, BY + 20 - f * 900 + f * f * 160, 38, { open: 1, rot: f * 6 });
      }
      popConfetti(lt - .1, BX, BY - 10, 56, 3805, [PAL.red, PAL.blue, PAL.white, PAL.pink], { speed: 1600, a0: -Math.PI * 1.1, spread: Math.PI * 1.2 });
      // the crowd: a back row above the caption, the big front row below it
      crowd(1660, t, { n: 6, s: 150, col: '#3A1C0A', jump: 1, hands: 1, seed: 3809, x0: -60, x1: W + 60 });
    }
    // the light switch: CLICK
    ctx.save(); ctx.translate(140, 560); ctx.rotate(-.05); ctx.scale(.85, .85);
    scrap(rrPts(-85, -150, 170, 300, 14), on ? PAL.white : '#3A3642', { torn: 1, ink: PAL.ink, sw: 4, seed: 3806, shadow: [8, 10] });
    fill(rrPts(-34, -80, 68, 160, 10), PAL.ink);
    const sy = on ? -40 : 40;
    scrap(rrPts(-26, sy - 38, 52, 76, 10), on ? PAL.green : '#8C8A92', { torn: .4, seed: 3807, shadow: false, ink: PAL.ink, sw: 3 });
    txt(on ? 'ON' : 'OFF', 0, 118, 34, on ? PAL.green : '#8C8A92', { font: 'anton' });
    ctx.restore();
    if (on && lt < .45) ransom('CLICK!', 300, 420, 70, { seed: 3808, pop: E(lt, .07, .2) * 1.3 });
    if (fl < 1 && on) { ctx.fillStyle = `rgb(255 255 245 / ${.85 * (1 - fl)})`; ctx.fillRect(-300, -300, W + 600, H + 600); }
  });

  // ---------- V3.9 (vertical): the corkboard, portrait: the victim's photo up top, the red string zigzagging down to the "?" ----------
  vshot('V3.9', (p, lt, d, t) => {
    open(lt, p, { push: .06, cx: 620, cy: 880, z0: 1.07 });
    bgc('#3A2A22');
    scrap(rectPts(-60, 170, W + 120, 1900), '#7A4A2A', { torn: 2, seed: 3920, shadow: [12, 14] });
    scrap(rectPts(-40, 196, W + 80, 1900), '#C9955C', { torn: 1.5, seed: 3921, shadow: false, tone: { color: '#7A4E2C', cell: 8, dot: .24, op: .6 } });
    // the clipping, top right
    clipping(775, 560, 400, 'HUGGING FACE HACKED!', { size: 44, rot: .04, mast: 'The Daily Gradient', date: 'JULY 16, 2026' });
    // the victim's polaroid, top left
    ctx.save(); ctx.translate(285, 600); ctx.rotate(-.07); ctx.scale(.92, .92);
    scrap(rectPts(-190, -230, 380, 460), PAL.white, { torn: 1, seed: 3922, shadow: [8, 10] });
    scrap(rectPts(-160, -200, 320, 320), PAL.sky, { torn: .5, seed: 3923, shadow: false });
    huggy(0, -30, 118, { mood: 'scared', hands: .75 });
    bandage(55, -110, 110, .2);
    txt('HUGGING FACE', 0, 172, 38, PAL.ink, { font: 'marker' });
    ctx.restore();
    tape(285, 395, 150, -.1);
    dymo('VICTIM', 300, 838, 32, PAL.red, { rot: .05 });
    // the suspect's sheet, lower right
    ctx.save(); ctx.translate(770, 955); ctx.rotate(.04);
    scrap(rectPts(-180, -220, 360, 440), PAL.white, { torn: 1.2, seed: 3924, shadow: [8, 10] });
    ctx.restore();
    suspect(770, 1140, 38, { rot: .04, shadow: false, q: 1 + pulse(t, 5) * .08 });
    // the clues
    note(285, 985, 210, 150, PAL.yellow, 'JUL 16', -.06, 50);
    ctx.save(); ctx.translate(470, 1100); ctx.rotate(.1);
    scrap(rectPts(-70, -86, 140, 172), PAL.newsprint, { torn: 1, seed: 3925, shadow: [5, 7] });
    ctx.strokeStyle = alpha(PAL.ink, .75); ctx.lineWidth = 3;
    for (let i = 1; i < 8; i++) { ctx.beginPath(); ctx.ellipse(0, 0, i * 7, i * 9.5, .1, Math.PI * (.1 + hash(i) * .2), Math.PI * (2 - hash(i + 9) * .3)); ctx.stroke(); }
    ctx.restore();
    // more of the board below the caption: notes, and detective Huggy with the magnifier, on its own case
    note(800, 1600, 260, 180, PAL.pink, 'NO USAGE POLICY?!', .05, 36);
    note(560, 1700, 250, 170, PAL.mint, 'autonomous agent framework??', -.04, 30);
    { const hx = 230, hy = 1640, hr = 120, bob = pulse(t, 5) * 8;
      ctx.save(); ctx.translate(0, -bob);
      huggy(hx, hy, hr, { mood: 'scared', hands: .9 });
      bandage(hx - 60, hy - 76, 96, -.2);
      scrap([...ellPts(hx, hy - hr * .72, hr * .95, hr * .7, 24).filter(q => q[1] < hy - hr * .72 + 4)], '#A8875A', { torn: .6, ink: PAL.ink, sw: 3, seed: 3926, tone: { color: '#5A4020', cell: 8, dot: .28, op: .7, angle: 45 } });
      scrap([[hx - hr * .6, hy - hr * .74], [hx + hr * .6, hy - hr * .74], [hx + hr * .3, hy - hr * .5], [hx - hr * .3, hy - hr * .5]], '#8C6C42', { torn: .4, ink: PAL.ink, sw: 3, seed: 3927, shadow: false });
      fill(ellPts(hx, hy - hr * 1.38, 10, 10, 8), '#8C6C42');
      const mx = hx + hr * .38, my = hy - hr * .22;
      marker([[mx + 60, my + 60], [mx + 130, my + 150]], '#6B3F1F', 22, { rough: 0 });
      scrap(ellPts(mx, my, 74, 74, 28), '#DFF3FF', { torn: .5, ink: PAL.ink, sw: 9, seed: 3928, shadow: [5, 6] });
      fill(ellPts(mx, my, 52, 58, 20), PAL.white); ctx.strokeStyle = PAL.ink; ctx.lineWidth = 4; tracePath(ellPts(mx, my, 52, 58, 20)); ctx.stroke();
      fill(ellPts(mx + 12 + Math.sin(lt * 3) * 6, my - 8, 24, 26, 14), PAL.ink); fill(ellPts(mx + 4, my - 18, 8, 8, 8), PAL.white);
      ctx.restore(); }
    // the red string, pin to pin, zigzagging down the board to the suspect
    const P = [[285, 395], [775, 405], [285, 920], [470, 1030], [770, 752]];
    const path = [];
    for (let i = 0; i < P.length - 1; i++) { const [a, b] = [P[i], P[i + 1]]; for (let j = 0; j <= 10; j++) { const u = j / 10; path.push([lerp(a[0], b[0], u), lerp(a[1], b[1], u) + Math.sin(u * Math.PI) * 30]); } }
    marker(partial(path, E(p, .02, .62)), '#D0142C', 7, { rough: .8 });
    circleMark(770, 930, 200, 245, '#D0142C', 10, E(p, .62, .8));
    P.forEach(([x, y]) => pin(x, y));
  });

  // ---------- V3.10 (vertical): the disguise is yanked up and away: three agents in staff lanyards, stacked tall; Sam facepalms ----------
  vshot('V3.10', (p, lt, d, t) => {
    open(lt, p, { push: .04, z0: 1.06 });
    const yank = E(lt, .06, .36), gone = easeIn(yank), rev = lt > .16;
    bgc('#2F1E57'); dots(PAL.purple, 22, .22, .5);
    scrap(ellPts(190, 470, 120, 120, 36), '#F6EFC9', { torn: 1.5, seed: 4001, shadow: false, tone: { color: '#D8CFA0', cell: 14, dot: .3, op: .6 } });
    for (let i = 0; i < 3; i++) scrap(ellPts(160 + i * 260 + lt * 40, 600 + i * 50, 120, 26, 16), alpha('#4A3A7A', .8), { torn: 1, shadow: false, seed: 4002 + i });
    scrap(rectPts(-300, 1290, W + 600, 900), '#1C1236', { torn: 2, seed: 4005, shadow: false });
    const X = 420, G = 1300, s = 72;
    // the rest of them, on their own: agents in lanyards scuttling off across the floor, along the foot of the frame
    for (let i = 0; i < 8; i++) {
      const x = ((i * 175 + lt * 560 + hash(i + 4030) * 80) % 1400) - 160, y = 1700 + (i % 3) * 75 + hash(i + 4031) * 20, as = 42 + (i % 3) * 7;
      agent(x, y, as, { bar: [PAL.clawd, PAL.mint, PAL.pink][i % 3], eyes: i % 2 ? 'spark' : 'dot', walk: lt * 9 + i, rot: Math.sin(lt * 20 + i) * .06, seed: 4032 + i });
      lanyard(x, y, as);
    }
    // the unmasking spotlight, from the top of the frame
    ctx.save(); ctx.globalCompositeOperation = 'screen'; ctx.fillStyle = `rgb(255 240 200 / ${rev ? .22 : .1})`;
    tracePath([[X - 80, -50], [X + 80, -50], [X + 300, G + 20], [X - 300, G + 20]]); ctx.fill();
    tracePath(ellPts(X, G + 10, 300, 52, 24)); ctx.fill(); ctx.restore();
    const wob2 = rev ? Math.sin(lt * 12) * .06 * (1 - p * .6) : 0;
    ctx.save(); ctx.translate(X, G); ctx.rotate(wob2); ctx.translate(-X, -G);
    const eyes = ['x', 'dot', 'spark'], cols = [PAL.clawd, PAL.mint, PAL.pink];
    for (let i = 0; i < 3; i++) {
      const gy = G - i * 3.1 * s, sway = rev ? Math.sin(lt * 12 + i) * 6 * i : 0;
      agent(X + sway, gy, s, { bar: cols[i], eyes: i === 2 && rev ? 'spark' : eyes[i], seed: 4010 + i });
      lanyard(X + sway, gy, s);
    }
    ctx.restore();
    // the fedora stays on the top one
    ctx.save(); ctx.translate(X + Math.sin(lt * 12 + 2) * 12, G - 9.3 * s + 8); ctx.rotate(-.18 + wob2);
    scrap(ellPts(0, 0, 1.6 * s, .32 * s, 20), '#16121D', { torn: .5, seed: 4020 });
    scrap(rrPts(-.9 * s, -1.1 * s, 1.8 * s, 1.15 * s, .35 * s), '#16121D', { torn: .5, seed: 4021, shadow: false });
    fill(rectPts(-.9 * s, -.4 * s, 1.8 * s, .25 * s), '#4A3A55');
    ctx.restore();
    // the disguise is yanked up and out of the frame by a yellow Huggy hand
    if (gone < 1) {
      const dx = -500 * gone, dy = -1500 * gone, r = -1.1 * gone;
      ctx.save(); ctx.translate(X + dx, 640 + dy); ctx.rotate(r); ctx.translate(-X, -640);
      suspect(X, G + 10, 64, { q: 1 });
      ctx.restore();
      const hx = X - 30 + dx, hy = 560 + dy;
      marker([[-200, hy - 500 + gone * 200], [hx - 60, hy - 10]], PAL.ink, 52, { rough: 0 });
      marker([[-200, hy - 500 + gone * 200], [hx - 60, hy - 10]], '#FFC21A', 40, { rough: 0 });
      scrap(rrPts(hx - 90, hy - 55, 130, 110, 40), '#FFC21A', { torn: .8, ink: PAL.ink, sw: 4, seed: 4022 });
      for (let i = 0; i < 3; i++) marker([[hx - 90 + i * 34, hy - 55], [hx - 80 + i * 34, hy - 5]], alpha(PAL.ink, .6), 3, { rough: 0 });
      if (yank > 0 && yank < 1) for (let i = 0; i < 5; i++) marker([[X - 120 + i * 60, 900 + i * 30 + dy * .3], [X - 140 + i * 60, 1060 + i * 30 + dy * .1]], alpha(PAL.white, .7 * (1 - yank)), 6, { rough: 1 });
    }
    if (rev) {
      const k = E(lt, .16, .3);
      for (let i = 0; i < 3; i++) ransom('!', X - 230 + i * 90, 560 - i * 30, 74, { seed: 4030 + i, pop: k * 1.3 });
      bubble('oops :)', 760, 480, { size: 58, tail: [X + 100, G - 8.2 * s], pop: E(lt, .38, .52) });
    }
    // Sam, facepalming, at the side
    const S = 54, SX = 835, SG = 1310;
    const palm = easeOut(E(lt, .42, .56));
    person(SX, SG, S, {
      name: 'SAM', top: 'hoodie', topCol: '#5A6072', pants: '#2A2E3A', hair: 'short', hairCol: '#6B4A2E',
      eyes: palm > 0 ? 'closed' : rev ? 'wide' : 'dot', mouth: palm > 0 ? 'frown' : rev ? 'O' : 'flat', aR: HIDE_ARM, aL: -1.2, seed: 4040, lookX: palm > 0 ? 0 : -.7,
    });
    const shx = SX + 1.35 * S, shy = SG - 7.1 * S;
    const hand = [lerp(shx + 40, SX + 12, palm), lerp(shy + 150, SG - 9.05 * S, palm)];
    limb([[shx, shy], [lerp(shx + 60, shx + 70, palm), lerp(shy + 90, shy + 20, palm)], hand], .84 * S, '#5A6072', SKINS[0]);
    if (palm >= 1) for (let i = 0; i < 3; i++) marker([[SX - 80 - i * 8, SG - 9.8 * S + i * 26], [SX - 115 - i * 8, SG - 10 * S + i * 26]], PAL.white, 5, { rough: 1 });
  });

  // ---------- V3.11 (vertical): Noam behind the table up top; both hands slide his chips down the felt to YES and NO ----------
  vshot('V3.11', (p, lt, d, t) => {
    open(lt, p, { push: .035, z0: 1.07, cy: 900 });
    bgc('#10231A'); dots('#050C08', 14, .3, .7);
    // the lamp and its cone
    marker([[540, -40], [540, 150]], PAL.ink, 6, { rough: 0 });
    beam(540, 210, 170, 540, 1500, 1300, 'rgb(255 222 140 / .14)');
    scrap([[430, 216], [650, 216], [600, 146], [480, 146]], '#2E6B45', { torn: .6, ink: PAL.ink, sw: 3, seed: 4101 });
    fill(ellPts(540, 219, 38, 15, 12), '#FFF2B8');
    // Noam behind the table
    const S = 62, X = 540, G = 1060;
    const b = beatN(t), look = b % 2 ? 1 : -1;
    person(X, G, S, { name: 'NOAM', top: 'tee', topCol: '#2F3E6B', pants: '#222', hair: 'short', hairCol: '#2A1E16', skin: SKINS[4], aL: HIDE_ARM, aR: HIDE_ARM, lookX: look * .9, eyes: 'dot', mouth: p > .5 ? 'smile' : 'flat', sweat: p > .45, seed: 4102 });
    const vy = G - 8.9 * S - .75 * S;
    ctx.save(); ctx.globalAlpha = .82;
    scrap([[X - 1.3 * S, vy - .1 * S], [X + 1.3 * S, vy - .1 * S], [X + 1.75 * S, vy + .75 * S], [X - 1.75 * S, vy + .75 * S]], '#3FBF6A', { torn: .5, seed: 4103, shadow: false, ink: '#1B5E34', sw: 3 });
    ctx.restore();
    fill(rectPts(X - 1.25 * S, vy - .25 * S, 2.5 * S, .22 * S), '#1B5E34');
    // the table, its felt running down toward us
    scrap([[140, 760], [940, 760], [1260, 2000], [-180, 2000]], '#5B361E', { torn: 2, seed: 4104, shadow: [0, 16] });
    scrap([[176, 788], [904, 788], [1210, 2000], [-130, 2000]], '#1F7A4A', { torn: 1.5, seed: 4105, shadow: false, tone: { color: '#12502F', cell: 10, dot: .22, op: .5 } });
    // bet spots: YES on one side, NO on the other
    const SP = [[-1, 'YES', 270], [1, 'NO', 810]];
    for (const [, lab, sx] of SP) {
      ctx.strokeStyle = alpha(PAL.white, .7); ctx.lineWidth = 6; ctx.beginPath(); ctx.ellipse(sx, 1140, 190, 80, 0, 0, TAU); ctx.stroke();
      txt(lab, sx + (sx < 540 ? -40 : 40), 1040, 84, alpha(PAL.white, .88), { font: 'anton', spacing: 8 });
    }
    for (const [dx, r] of [[-46, -.15], [46, .12]]) { ctx.save(); ctx.translate(X + dx, 860); ctx.rotate(r); scrap(rrPts(-44, -62, 88, 124, 8), PAL.red, { torn: .5, ink: PAL.white, sw: 5, seed: 4106 + dx, tone: { color: PAL.white, cell: 9, dot: .2, op: .35 } }); ctx.restore(); }
    // both hands shove chips down the felt to both sides at once, every beat; the piles grow in lockstep
    const bp = frac(bpOf(t)), push = easeOut(clamp(bp / .4));
    const nStack = 2 + Math.min(4, b - beatN(t - lt + 1e-3));
    for (const [sd, , sx] of SP) {
      chipStack(sx - 54, 1150, nStack, PAL.red, 1.2);
      chipStack(sx + 54, 1160, nStack - 1, PAL.blue, 1.2);
      chipStack(sx, 1180, nStack + 1, PAL.gold, 1.2);
      if (bp > .25 && bp < .8) { const u = E(bp, .25, .8); chipStack(lerp(X + sd * 230, sx, u), lerp(900, 1120, u) - Math.sin(u * Math.PI) * 60, 1, PAL.white, 1); }
      const hx = X + sd * lerp(170, 230, push), hy = lerp(872, 900, push);
      chipStack(hx, hy + 30, 3, PAL.white, 1.05);
      const shx = X + sd * 1.35 * S, shy = G - 7.1 * S;
      limb([[shx, shy], [shx + sd * 90, shy + 140], [hx - sd * 14, hy]], 54, SKINS[4], SKINS[4]);
      scrap(rectPts(shx - .5 * S, shy - .45 * S, 1 * S, .95 * S), '#2F3E6B', { torn: .5, shadow: false, seed: 4108 + sd });
    }
  });

  // ---------- V3.12 (vertical): a tall trophy cabinet, seven shelves, each with its empty labelled spot; (yet) lowered in and slapped on ----------
  vshot('V3.12', (p, lt, d, t) => {
    const SLAP = .76;
    open(lt, p, { push: .035, z0: 1.06 });
    const imp = p > SLAP ? Math.max(0, 1 - (p - SLAP) / .12) : 0;
    shake(t, 14 * imp);
    bgc(PAL.sky); dots(PAL.blue, 20, .2, .35, 30);
    const x0 = 120, x1 = 960, y0 = 390, y1 = 1560, gT = y0 + 210;
    scrap(rectPts(x0, y0, x1 - x0, y1 - y0), '#7A4A26', { torn: 1.5, seed: 4201, shadow: [14, 16], tone: { color: '#4A2A12', cell: 10, dot: .2, op: .4 } });
    scrap(rectPts(x0 + 28, gT, x1 - x0 - 56, y1 - gT - 30), '#1D2F6B', { torn: 1, seed: 4202, shadow: false, tone: { color: '#0F1A40', cell: 8, dot: .3, op: .6 } });
    // the header plaque: MILLENNIUM PRIZES / WON: 0
    scrap(rectPts(170, y0 + 22, 740, 170), PAL.gold, { torn: 1, seed: 4203, ink: PAL.ink, sw: 4, shade: true, shadeOp: .25 });
    txt('MILLENNIUM PRIZES', 540, y0 + 56, 56, PAL.ink, { font: 'abril', maxW: 680 });
    const WX = 410;
    txt('WON: 0', WX, y0 + 144, 68, PAL.ink, { font: 'abril' });
    const zx = WX + textW('WON: 0', 68, 'abril') / 2 - textW('0', 68, 'abril') / 2;
    circleMark(zx, y0 + 142, 50, 46, PAL.red, 8, E(p, .1, .32));
    // seven shelves, an empty spot on each
    const LABS = ['P vs NP', 'RIEMANN', 'NAVIER–STOKES', 'YANG–MILLS', 'HODGE', 'BIRCH–SWINNERTON-DYER', 'POINCARÉ'];
    const rowH = 94, r0 = gT + 100;
    LABS.forEach((lab, i) => {
      const sy = r0 + i * rowH;
      emptyTrophy(282, sy - 6, 10.5);
      ctx.save(); ctx.translate(610, sy - 34); scrap(rectPts(-250, -19, 500, 40), PAL.gold, { torn: .5, seed: 4210 + i, ink: PAL.ink, sw: 2, shadow: [3, 4] });
      txt(lab, 0, 3, 32, PAL.ink, { font: 'archivo', maxW: 470 }); ctx.restore();
      scrap(rectPts(x0 + 18, sy - 4, x1 - x0 - 36, 20), '#A0683A', { torn: 1, seed: 4220 + i, shadow: [5, 6] });
    });
    // cobweb, and a tumbleweed rolling along the bottom shelf
    ctx.strokeStyle = alpha(PAL.white, .5); ctx.lineWidth = 2;
    for (let i = 0; i < 5; i++) { ctx.beginPath(); ctx.moveTo(x1 - 28, gT); ctx.lineTo(x1 - 28 - Math.cos(i / 4 * Math.PI / 2) * 130, gT + Math.sin(i / 4 * Math.PI / 2) * 130); ctx.stroke(); }
    for (let j = 1; j < 4; j++) { ctx.beginPath(); for (let i = 0; i <= 4; i++) { const a = i / 4 * Math.PI / 2, r = j * 36 + (i % 2) * 6; i ? ctx.lineTo(x1 - 28 - Math.cos(a) * r, gT + Math.sin(a) * r) : ctx.moveTo(x1 - 28 - Math.cos(a) * r, gT + Math.sin(a) * r); } ctx.stroke(); }
    const tw = lerp(220, 900, p), tr = 34, bottom = r0 + 6 * rowH - 4;
    ctx.save(); ctx.translate(tw, bottom - tr - Math.abs(Math.sin(p * 9)) * 18); ctx.rotate(p * 14);
    for (let i = 0; i < 9; i++) { ctx.strokeStyle = i % 2 ? '#C9A77C' : '#8B6B43'; ctx.lineWidth = 4; ctx.beginPath(); ctx.ellipse(0, 0, tr, tr * (.4 + hash(i + 4230) * .6), i * .7, 0, TAU); ctx.stroke(); }
    ctx.restore();
    // a spotlight sweeping up and down the empty shelves
    ctx.save(); ctx.globalCompositeOperation = 'screen'; ctx.fillStyle = 'rgb(255 240 190 / .14)';
    const sy = r0 + 3 * rowH + Math.sin(lt * 2.6) * 300; tracePath([[x0 + 28, sy - 40], [x0 + 28, sy + 40], [x1 - 28, sy + 140], [x1 - 28, sy - 140]]); ctx.fill(); ctx.restore();
    // "(yet)": a hand brings the note in from the side, under the plaque, then slaps it on as "yet" is sung
    const dangle = easeOut(E(p, .4, .6)), slam = easeIn(E(p, SLAP - .06, SLAP)), handUp = easeIn(E(p, SLAP + .04, SLAP + .16));
    const nx = lerp(lerp(1350, 800, dangle), 726, slam), ny = lerp(700, 572, slam);
    if (dangle > 0) {
      const sway = p < SLAP ? Math.sin(lt * 7) * .12 : 0;
      ctx.save(); ctx.translate(nx, ny); ctx.rotate(.12 + sway + (1 - dangle) * .3);
      scrap(rectPts(-112, -84, 224, 168), PAL.yellow, { torn: 1, seed: 4240, shadow: p < SLAP ? [18, 24] : [8, 10] });
      fill(rectPts(-112, -84, 224, 30), alpha('#E0B800', .7));
      txt('(yet)', 0, 14, 84, PAL.ink, { font: 'marker' });
      ctx.restore();
      const hx = nx + 80 + handUp * 900;
      limb([[hx + 900, ny + 160], [hx, ny + 10]], 70, '#2F3E6B', SKINS[4]);
    }
    if (imp > 0) for (let i = 0; i < 8; i++) { const a = i / 8 * TAU, r0 = 140 + (1 - imp) * 50; marker([[nx + Math.cos(a) * r0, 572 + Math.sin(a) * r0 * .8], [nx + Math.cos(a) * (r0 + 50), 572 + Math.sin(a) * (r0 + 50) * .8]], PAL.yellow, 7, { rough: 1, alpha: imp }); }
  });


  // ---------- V3.13 (vertical): Mythos tall in the middle, its moral compass spinning; the sock puppets vouch for each other, left, right ----------
  vshot('V3.13', (p, lt, d, t) => {
    open(lt, p, { push: .04, z0: 1.07, cy: 900 });
    bgc('#FF5E9E');
    ctx.save(); ctx.globalAlpha = .18; for (let i = -16; i < 16; i++) fill([[i * 120, -100], [i * 120 + 60, -100], [i * 120 + 1000, H + 100], [i * 120 + 940, H + 100]], PAL.red); ctx.restore();
    dots('#B0105A', 16, .2, .3);
    scrap(rectPts(-300, 1372, W + 600, 900), '#C2306F', { torn: 2, seed: 4320, shadow: false, tone: { color: '#8A1048', cell: 12, dot: .3, op: .5 } });
    const b = bpOf(t) - bpOf(t - lt), who = Math.floor(b + 1e-3);
    const X = 540, G = 1384, s = 63, arm = .5;
    // the misregistered ghost: the robot doesn't quite line up with itself
    ctx.save(); ctx.globalAlpha = .4; ctx.translate(30 + Math.sin(lt * 9) * 8, -16);
    bot(X, G, s, { col: '#4FC3FF', screen: '#4FC3FF', faceCol: '#4FC3FF', face: ' ', label: '', aL: arm, aR: arm, shadow: false, seed: 3900 });
    ctx.restore();
    const talkL = who % 2 === 0, bp = frac(bpOf(t) * 2);
    const mouth = on => on ? (bp < .5 ? 1 : .15) : 0;
    mythos(X, G, s, {
      label: '', face: talkL ? '>‿<' : '^‿^', aL: arm + (talkL ? pulse(t, 6) * .12 : 0), aR: arm + (!talkL ? pulse(t, 6) * .12 : 0),
      holdL: sc => sockPuppet(.95 * sc, { col: PAL.white, stripe: PAL.red, open: mouth(talkL), tag: 'REAL HUMAN' }),
      hold: sc => sockPuppet(.95 * sc, { col: PAL.yellow, stripe: PAL.blue, open: mouth(!talkL), flip: true, tag: 'ALSO REAL' }),
    });
    compass(X, G - 5.2 * s, 1.55 * s, lt * 26 + Math.sin(lt * 9) * 3);
    // the review board along the foot of the frame: a row of sock puppets, nodding along, mouths flapping on the beat
    for (let i = 0; i < 7; i++) {
      const x = 40 + i * 168, y = 1890 + (i % 2) * 40, nod = Math.sin((bpOf(t) * 2 + i * .4) * Math.PI) * .12, open = Math.max(0, Math.sin((bpOf(t) * 2 + i * .4) * Math.PI));
      ctx.save(); ctx.translate(x, y); ctx.rotate(nod);
      sockPuppet(54, { col: [PAL.white, PAL.yellow, PAL.mint, PAL.sky][i % 4], stripe: [PAL.red, PAL.blue, PAL.purple][i % 3], open, flip: i % 2 === 1 });
      ctx.restore();
    }
    txt('MORAL', X, G - 3.25 * s, .5 * s, PAL.ink, { font: 'archivo' });
    // the puppets vouch for each other, one bubble a beat, alternating sides (each side's newest only)
    const lines = ["HE'S LEGIT!", 'SO IS HE!', 'LGTM!', 'LGTM!!', 'SHIP IT!'];
    const hx = (2 + 3 * Math.cos(arm)) * s, lx = X - hx + 1.5 * s, rx = X + hx - 1.5 * s, hy = G - 6 * s - Math.sin(arm) * 3 * s - 3.6 * .95 * s;
    for (let i = Math.max(0, Math.min(who, 4) - 1); i <= Math.min(who, 4); i++) {
      const left = i % 2 === 0, age = b - i;
      bubble(lines[i], left ? 280 : 800, 476 + (i >= 2 ? 16 : 0), { size: 64, tail: [left ? lx : rx, hy], pop: clamp(age / .35), rot: left ? -.05 : .05, fill: left ? PAL.white : PAL.yellow, maxW: 420 });
    }
  });

  // ---------- V3.14 (vertical): the tall GOOGLE door, the clock spinning above it; Jeff walks out toward us with his box; SLAM ----------
  vshot('V3.14', (p, lt, d, t) => {
    open(lt, p, { push: .03, z0: 1.07 });
    const slamAt = .73, slam = E(p, slamAt - .08, slamAt), after = p > slamAt;
    shake(t, after ? 12 * Math.max(0, 1 - (p - slamAt) / .12) : 0);
    bgc('#9FD3F2'); dots(PAL.sky, 18, .3, .6);
    // the building
    scrap(rectPts(-60, 390, W + 120, 940), PAL.cream, { torn: 1.5, seed: 4411, shadow: [14, 12], tone: { color: '#D9CFB5', cell: 12, dot: .25, op: .7 } });
    for (let r = 0; r < 3; r++) for (const c of [0, 1]) scrap(rectPts(c ? 870 : 64, 720 + r * 180, 146, 130), '#7FB3D5', { torn: .8, seed: 4412 + r * 2 + c, ink: PAL.ink, sw: 4, shadow: false });
    // the clock: the years spin by… then DING, just in time
    const slamT = slamAt * d, spinEnd = (slamT * 30) % TAU, settle = elasticOut(E(p, slamAt, slamAt + .18));
    const mA = after ? lerp(spinEnd, TAU, settle) : lt * 30, hA = after ? TAU : TAU - (slamT - lt) * 2.5;
    wallClock(540, 510, 112, hA, mA, { rim: PAL.red });
    if (after) ransom('DING!', 790, 500, 60, { seed: 4417, pop: E(p, slamAt, slamAt + .1) * 1.3 });
    ransom('GOOGLE', 540, 690, 104, { seed: 4416, pop: 1, jolt: 1 });
    // the door (dark interior, the leaf swinging shut)
    scrap(rectPts(320, 770, 440, 560), '#2A2530', { torn: 1, seed: 4418, shadow: false });
    const leaf = lerp(.12, 1, easeIn(slam));
    ctx.save(); ctx.translate(760, 0); ctx.scale(-leaf, 1);
    scrap(rectPts(0, 770, 440, 560), PAL.red, { torn: 1, seed: 4419, ink: PAL.ink, sw: 4, shade: true, shadeOp: .2 });
    fill(rectPts(380, 1040, 22, 70), PAL.gold);
    ctx.restore();
    if (after && p < slamAt + .25) ransom('SLAM!', 470, 960, 92, { seed: 4420, pop: E(p, slamAt, slamAt + .08) * 1.3, jolt: 3 });
    // the sidewalk
    scrap(rectPts(-200, 1318, W + 600, 700), '#BDB6A8', { torn: 1.5, seed: 4421, shadow: false });
    for (let i = 0; i < 4; i++) marker([[-50, 1420 + i * 130 + i * i * 20], [W + 50, 1420 + i * 130 + i * i * 20]], alpha(PAL.ink, .15), 4, { rough: 1 });
    // Jeff strolls out with his box, toward us and to the side
    // the street along the foot of the frame: the kerb, and a cab pulling up for him
    scrap(rectPts(-200, 1660, W + 400, 40), '#8E877A', { torn: 1, seed: 4422, shadow: false });
    scrap(rectPts(-200, 1700, W + 400, 400), '#3A3640', { torn: 1, seed: 4423, shadow: false });
    for (let i = -1; i < 6; i++) fill(rectPts(i * 260 - (lt * 120) % 260, 1880, 140, 14), PAL.yellow);
    { const cxx = lerp(1300, 560, easeOut(E(lt, 0, .8))), cyy = 1880;
      scrap(rrPts(cxx - 330, cyy - 120, 660, 130, 30), PAL.yellow, { torn: 1, seed: 4424, ink: PAL.ink, sw: 5, shadow: [8, 10] });
      scrap([[cxx - 200, cyy - 120], [cxx - 130, cyy - 210], [cxx + 150, cyy - 210], [cxx + 220, cyy - 120]], PAL.yellow, { torn: .8, seed: 4425, ink: PAL.ink, sw: 5 });
      for (const [a, b] of [[-180, -20], [10, 190]]) scrap([[cxx + a + 20, cyy - 128], [cxx + a + 40, cyy - 196], [cxx + b - 30, cyy - 196], [cxx + b - 10, cyy - 128]], '#BFE3F5', { torn: .4, seed: 4426 + a, shadow: false, ink: PAL.ink, sw: 3 });
      scrap(rrPts(cxx - 60, cyy - 250, 120, 40, 8), PAL.white, { torn: .4, seed: 4428, ink: PAL.ink, sw: 3 });
      txt('TAXI', cxx, cyy - 230, 30, PAL.ink, { font: 'archivo' });
      for (let q = 0; q < 8; q++) fill(rectPts(cxx - 320 + q * 80, cyy - 60, 40, 20), q % 2 ? PAL.ink : PAL.yellow);
      for (const wx of [-210, 210]) { scrap(ellPts(cxx + wx, cyy + 10, 56, 56, 20), PAL.ink, { torn: .4, seed: 4429 + wx, shadow: false }); fill(ellPts(cxx + wx, cyy + 10, 22, 22, 12), '#9A9AA6'); } }
    const k = ease(p), S = lerp(40, 54, k), X = lerp(560, 790, k), G = lerp(1318, 1450, k), walk = lt * 2.4, bob = Math.abs(Math.sin(walk * Math.PI)) * 8;
    const bs = S * .9;
    person(X, G, S, { name: 'JEFF', top: 'tee', topCol: PAL.purple, pants: '#34405C', hair: 'short', hairCol: '#8A8A8A', skin: SKINS[0], glasses: true, eyes: 'happy', mouth: 'o', walk, aL: HIDE_ARM, aR: HIDE_ARM, dy: -bob / S, seed: 4422 });
    belongingsBox(X, G - 2.9 * S - bob, bs, t);
    for (const sd of [-1, 1]) scrap(ellPts(X + sd * 2.9 * bs, G - 2.9 * S - bob - 1.8 * bs, .5 * bs, .5 * bs, 12), SKINS[0], { torn: .5, shadow: [2, 3] });
    for (let i = 0; i < 3; i++) { const u = frac(lt * 1.2 + i / 3); ctx.save(); ctx.globalAlpha = Math.sin(u * Math.PI); txt(i % 2 ? '♪' : '♫', X - 90 - u * 80, G - 9.5 * S - u * 140, 60, PAL.ink, { font: 'archivo' }); ctx.restore(); }
    sticker('27\nYEARS', 200, 520, 124, PAL.yellow, { pop: E(lt, .2, .4), rot: -.14, size: 58 });
  });

  // ---------- V3.15 (vertical): a portrait chalkboard, the proof in rows down it; Clawd on the chalk tray, jumping, dust on the beats ----------
  vshot('V3.15', (p, lt, d, t) => {
    const hitP = .3, hit = p > hitP, imp = hit ? Math.max(0, 1 - (p - hitP) / .12) : 0;
    open(lt, p, { push: .035, z0: 1.06, cy: 900 });
    shake(t, 16 * imp);
    bgc('#5B3A22');
    scrap(rectPts(-100, 1520, W + 200, 600), '#3E2616', { torn: 1.5, seed: 4507, shadow: false });
    scrap(rectPts(30, 390, 1020, 850), '#8B5A2B', { torn: 2, seed: 4501, shadow: [12, 14] });
    scrap(rectPts(62, 420, 956, 790), '#1F3A2E', { torn: 1.2, seed: 4502, shadow: false, tone: { color: '#2E5242', cell: 22, dot: .4, op: .5 } });
    for (let i = 0; i < 5; i++) fill(ellPts(200 + hash(i + 4503) * 700, 480 + hash(i + 4504) * 640, 110 + hash(i + 4505) * 120, 36, 16, hash(i) - .5), 'rgb(255 255 255 / .05)');
    scrap(rectPts(40, 1206, 1000, 40), '#6B4226', { torn: 1, seed: 4506, shadow: [6, 8] });
    const chalk = '#F1EFE6', wk = E(lt, 0, .4);
    const say = (s, k) => s.slice(0, Math.ceil(s.length * clamp(k)));
    txt(say('JACOBIAN CONJECTURE', wk * 1.6), 100, 488, 62, chalk, { font: 'marker', align: 'left', maxW: 860 });
    underline(100, 900, 530, chalk, 6, E(lt, .15, .4));
    txt(say('det J  ≡  −2', wk * 1.4 - .2), 110, 650, 124, chalk, { font: 'marker', align: 'left' });
    // three points, one image: not injective
    const dp = [[200, 790], [160, 900], [215, 1010]], tgt = [690, 880];
    dp.forEach(([x, y], i) => {
      fill(ellPts(x, y, 17, 17, 12), chalk);
      txt('abc'[i], x - 48, y - 10, 50, chalk, { font: 'marker' });
      arrow(x + 28, y, tgt[0] - 36, tgt[1] + (i - 1) * 16, chalk, 7, { k: E(lt, .08 + i * .06, .3 + i * .06), bend: (i - 1) * -.12 });
    });
    const tk = E(lt, .3, .42);
    if (tk > 0) { fill(ellPts(tgt[0], tgt[1], 26 * backOut(tk), 26 * backOut(tk), 14), PAL.yellow); circleMark(tgt[0], tgt[1], 64, 64, PAL.yellow, 6, tk); }
    txt(say('F(a) = F(b) = F(c)', E(lt, .32, .55)), 500, 980, 46, chalk, { font: 'marker' });
    txt(say('∴ not injective!', E(lt, .36, .6)), 100, 1120, 62, PAL.yellow, { font: 'marker', align: 'left' });
    // Clawd, chalk in hand, prouder than proud, on the chalk tray; chalk dust on the hit and on every beat after
    // the front row of the seminar, along the foot of the frame: mortarboards, hands shooting up on the beats
    for (let i = 0; i < 6; i++) {
      const x = 90 + i * 180 + (hash(i + 4530) - .5) * 30, hy = 1730 + (i % 2) * 30, up = hit && (Math.floor(bpOf(t)) + i) % 3 === 0;
      if (up) marker([[x + 50, hy + 40], [x + 80, hy - 150]], '#1A1210', 34, { rough: 0 });
      fill(ellPts(x, hy, 68, 76, 20), '#A8743E'); fill(rectPts(x - 101, hy + 46, 202, 400), '#A8743E');   // (a rim of the board's light)
      fill(ellPts(x, hy, 62, 70, 20), '#1A1210');
      fill(rectPts(x - 95, hy + 50, 190, 400), '#1A1210');
      ctx.save(); ctx.translate(x, hy - 62); ctx.rotate((hash(i + 4531) - .5) * .25);
      fill([[-88, 0], [0, -26], [88, 0], [0, 26]], PAL.ink); fill(rectPts(-46, 0, 92, 30), PAL.ink);
      marker([[0, 0], [70, 14], [70, 60]], PAL.gold, 5, { rough: 0 });
      ctx.restore();
    }
    scrap(rectPts(-100, 1830, W + 200, 120), '#6B4226', { torn: 1, seed: 4540, shadow: [0, -8] });
    const jump = hit ? Math.max(0, Math.sin(E(p, hitP, hitP + .25) * Math.PI)) : 0, hop = pulse(t, 6);
    const writing = !hit, CX = 850, CG = 1208, u = 25;
    const aR = writing ? .9 + Math.sin(lt * 30) * .2 : 1.3, dy = -jump * 3 - (hit ? hop * .4 : 0);
    if (hit) {
      popConfetti(p - hitP, CX + 4 * u, CG - 7 * u, 34, 4510, [alpha(chalk, .85), alpha(chalk, .5)], { speed: 800, a0: 0, spread: TAU, g: 200 });
      for (let k = 1; k < 4; k++) { const bt = beatLt(t, lt, k), age = lt - bt; if (age > 0 && age < .5) popConfetti(age, CX, CG - 2 * u + dy * u, 20, 4520 + k * 30, [alpha(chalk, .8), alpha(chalk, .45)], { speed: 600, a0: -Math.PI, spread: Math.PI, g: 300 }); }
    }
    clawd(CX, CG, u, {
      hat: 'grad', eyes: hit ? 'happy' : 'normal', mouth: hit ? 'grin' : 'flat', blush: hit, dy,
      aR, aL: hit ? 1.3 : -.2, lookX: writing ? -1 : 0, lookY: writing ? -.5 : 0,
    });
    const chx = CX + 5 * u + Math.cos(-aR) * 2 * u, chy = CG + dy * u - 4.9 * u + Math.sin(-aR) * 2 * u;
    ctx.save(); ctx.translate(chx, chy); ctx.rotate(-.5); scrap(rrPts(-9, -38, 18, 50, 5), chalk, { torn: .5, shadow: [2, 3], ink: alpha(PAL.ink, .5), sw: 2 }); ctx.restore();
    if (hit) for (let i = 0; i < 4; i++) twinkle(CX + Math.cos(i * 1.6) * 170, 900 + Math.sin(i * 1.6) * 90, 26, PAL.yellow, pulse(t + i * .1, 3));
  });

  // ---------- V3.16 (vertical): Gwern big in the middle pulls the hood back into a sunburst; the hood flies off up and away ----------
  vshot('V3.16', (p, lt, d, t) => {
    const pull = easeOut(E(lt, .16, .34)), rev = pull > .5, sun = E(lt, .24, .5);
    open(lt, p, { push: .06, z0: 1.05, cy: 860 });
    const S = 74, X = 540, G = 1330, hx = X, hy = G - 8.9 * S, HOOD = '#2C2A38';
    if (!rev) { bgc('#7A84A6'); dots(PAL.ink, 14, .25, .4); }
    else {
      rays(hx, hy, 20, '#FFB43A', PAL.yellow, t * .6);
      scrap(ellPts(hx, hy, 360 * backOut(sun), 360 * backOut(sun), 40), '#FFF1A8', { torn: 2, seed: 4601, shadow: false });
    }
    scrap(rectPts(-300, G - 20, W + 600, 900), rev ? '#E8A21C' : '#5A6488', { torn: 2, seed: 4608, shadow: false });
    const joy = E(lt, .42, .6);
    const aUp = rev ? lerp(1.55, 1.15, joy) : lerp(-1.2, 1.55, E(lt, .02, .16));
    person(X, G, S, {
      top: 'hoodie', topCol: HOOD, pants: '#2A2E3A', hair: 'short', hairCol: '#6B4A2E', skin: SKINS[4],
      eyes: 'happy', mouth: 'grin', blush: true, aL: aUp, aR: aUp, dy: rev ? -Math.sin(joy * Math.PI) * .6 : 0, seed: 4603,
    });
    const liftY = rev ? -Math.sin(joy * Math.PI) * .6 * S : 0;
    // the hood: up (a faceless shadow with a "?"), then pulled back and flung up out of the frame
    const hood = (q, inside = true) => {
      scrap([...ellPts(0, -.15 * S, 1.65 * S, 1.8 * S, 28).filter(v => v[1] < .9 * S), [1.9 * S, 1.6 * S], [-1.9 * S, 1.6 * S]], HOOD, { torn: .6, seed: 4604, shadow: [6, 8] });
      if (inside) scrap(ellPts(0, .1 * S, 1.05 * S, 1.2 * S, 24), '#12101A', { torn: .6, seed: 4605, shadow: false });
      else marker([[-1.2 * S, 1.2 * S], [0, 1.5 * S], [1.2 * S, 1.2 * S]], '#4A4660', .14 * S, { rough: .5, smooth: true });
      if (q > 0) txt('?', 0, .2 * S, 1.7 * S, PAL.yellow, { font: 'abril', alpha: q });
    };
    // (pulled back: it slides up off his face, chin first, then flies off up out of the frame)
    if (!rev) { ctx.save(); ctx.translate(hx, hy - pull * 2 * S); hood(1 - pull * 2); ctx.restore(); }
    else {
      const f = E(lt, .2, .6), fy = hy - 1.7 * S - easeIn(f) * 1400 - f * 200, fx = hx + f * 260;
      if (f < 1) { ctx.save(); ctx.translate(fx, fy); ctx.rotate(f * 5); ctx.scale(1 - f * .3, 1 - f * .3); hood(0, false); ctx.restore(); }
    }
    // the name sticker: GWERN → scribbled out → "!"
    ctx.save(); ctx.translate(0, liftY);
    const TX = X + .3 * S, TY = G - 6 * S;
    helloTag('GWERN', TX, TY, .56 * S, -.06);
    if (rev) {
      const sk = E(lt, .28, .4);
      marker(partial([[TX - 80, TY + 20], [TX + 46, TY + 2], [TX - 58, TY + 32], [TX + 86, TY + 12], [TX - 22, TY + 36], [TX + 92, TY + 26]], sk), PAL.ink, 9, { rough: 1 });
      ransom('!', TX + 150, TY - 16, 160, { seed: 4606, pop: E(lt, .34, .46) * 1.3, papers: [PAL.yellow], fonts: ['abril'] });
    }
    ctx.restore();
    if (rev) {
      popConfetti(lt - .3, hx, hy - 60, 70, 4607, CONF, { speed: 1500, a0: -Math.PI * 1.05, spread: Math.PI * 1.1 });
      for (let i = 0; i < 6; i++) { const a = i / 6 * TAU + t; twinkle(hx + Math.cos(a) * 330, hy + Math.sin(a) * 300, 30, i % 2 ? PAL.white : PAL.pink, E(lt, .3, .45) * (.5 + .5 * pulse(t + i * .05, 4))); }
    }
  });

})();

;
// ---- src/ch/c07_chorus3.js ----
// c07_chorus3 — Chorus 3: the arena show (venue level 3), energy peak before the panic verse.
//   lines 1–2  "We didn't start the scaling — / It was always training, and the curves kept gaining"
//              slow crane-up out of a sea of lighters and devil horns to the stage; the hook slams in over the rafters;
//              on "the curves kept gaining" a marquee of bulbs races up the backdrop curve and pops a firework.
//   line 3     "We didn't start the scaling —"  the whole band hops in unison, then one huge leap with hang-time…
//   line 4     "No, we didn't preordain it, but we can't contain it!"  …landing on the downbeat into a pyro blast.
//              The curve catches like a fuse and burns up the banner; a roadie's tiny PAUSE extinguisher puffs at it;
//              on "contain" the whole curve goes up in flames.
(() => {
  const SY = STAGE_Y, GY = STAGE_Y + 70;
  const WALL = '#1B1433';   // band.js level-3 back wall
  // band.js's level-3 banner (curveBanner at y 110) and its curve, for the bulbs and the fire. (The vertical video hangs a tall
  // banner of its own behind the band, VBAN, and its curve climbs the tall frame.)
  const VBAN = { x: 600, y: -340, w: 720, h: 900 };
  const CURVE = (() => {
    const { x, y, w, h } = VERT ? VBAN : { x: 260, y: 110, w: 1400, h: 560 }, steep = 5, pts = [];
    for (let i = 0; i <= 50; i++) { const u = i / 50, v = (Math.exp(u * steep) - 1) / (Math.exp(steep) - 1); pts.push([x + 90 + u * (w - 180), y + h - 70 - v * (h - 140)]); }
    return pts;
  })();
  const CTOP = CURVE.at(-1);
  // points evenly spaced along the curve's length
  const along = (() => {
    const L = [0]; for (let i = 1; i < CURVE.length; i++) L.push(L[i - 1] + Math.hypot(CURVE[i][0] - CURVE[i - 1][0], CURVE[i][1] - CURVE[i - 1][1]));
    return u => { const want = u * L.at(-1); let i = 1; while (i < L.length - 1 && L[i] < want) i++; const f = (want - L[i - 1]) / (L[i] - L[i - 1] || 1); return [lerp(CURVE[i - 1][0], CURVE[i][0], f), lerp(CURVE[i - 1][1], CURVE[i][1], f)]; };
  })();

  // ---------- the crowd sea ----------
  // One row of silhouettes (heads around y) in the current transform. o: n, s, x0, x1, col, rim (rim-light colour),
  // lighters / horns (fractions of raised hands), jump, seed.
  function sea(y, t, o = {}) {
    const n = o.n ?? 20, s = o.s ?? 60, x0 = o.x0 ?? -80, x1 = o.x1 ?? W + 80, col = o.col ?? PAL.ink, seed = o.seed ?? 700, bot = o.bottom ?? H + 60;
    const b = bpOf(t), flames = [];
    ctx.lineCap = 'round';
    for (let i = 0; i < n; i++) {
      const r = k => hash2(seed + i, k);
      const x = lerp(x0, x1, (i + .5) / n) + (r(1) - .5) * s * .8, ph = r(2);
      const hy = y - (o.jump ?? .5) * Math.max(0, Math.sin((b + ph) * Math.PI)) ** 2 * s * .45 + (r(3) - .5) * s * .35;
      const sz = s * (.85 + r(4) * .3);
      // raised arm(s)
      if (r(5) < (o.hands ?? .7)) {
        const side = r(6) < .5 ? -1 : 1, sway = Math.sin((b * .5 + ph) * TAU) * .18;
        const ax = x + side * sz * .55, ay = hy + sz * .7, ang = side * (.1 + r(7) * .25) + sway, L = sz * 1.9;
        const hx = ax + Math.sin(ang) * L, hy2 = ay - Math.cos(ang) * L;
        ctx.strokeStyle = col; ctx.lineWidth = sz * .24; ctx.beginPath(); ctx.moveTo(ax, ay); ctx.lineTo(hx, hy2); ctx.stroke();
        ctx.fillStyle = col; tracePath(ellPts(hx, hy2, sz * .17, sz * .17, 8)); ctx.fill();
        const kind = r(8);
        if (kind < (o.lighters ?? .35)) flames.push([hx, hy2 - sz * .1, sz, ph]);
        else if (kind < (o.lighters ?? .35) + (o.horns ?? .4)) {
          ctx.lineWidth = sz * .08;
          for (const f of [-1, 1]) { ctx.beginPath(); ctx.moveTo(hx + f * sz * .09, hy2 - sz * .08); ctx.lineTo(hx + f * sz * .14, hy2 - sz * .42); ctx.stroke(); }
        }
      }
      if (o.rim) { ctx.fillStyle = o.rim; tracePath(ellPts(x + sz * .04, hy - sz * .07, sz * .42, sz * .48, 14)); ctx.fill(); }
      ctx.fillStyle = col;
      tracePath(ellPts(x, hy, sz * .42, sz * .48, 14)); ctx.fill();
      tracePath([[x - sz * .72, hy + sz * .42], [x + sz * .72, hy + sz * .42], [x + sz * .85, bot], [x - sz * .85, bot]]); ctx.fill();
    }
    // lighters on top: body, flame, glow
    for (const [fx, fy, sz, ph] of flames) {
      const fl = 1 + Math.sin(T * 17 + ph * 40) * .15;
      ctx.save(); ctx.globalCompositeOperation = 'screen'; ctx.fillStyle = alpha(PAL.yellow, .22);
      tracePath(ellPts(fx, fy - sz * .3, sz * .55, sz * .6, 14)); ctx.fill(); ctx.restore();
      ctx.fillStyle = '#4A4656'; ctx.fillRect(fx - sz * .055, fy - sz * .1, sz * .11, sz * .16);
      ctx.fillStyle = PAL.orange; tracePath([[fx - sz * .08, fy - sz * .1], [fx + jit(sz * .02), fy - sz * .56 * fl], [fx + sz * .08, fy - sz * .1]]); ctx.fill();
      ctx.fillStyle = PAL.yellow; tracePath([[fx - sz * .045, fy - sz * .1], [fx, fy - sz * .36 * fl], [fx + sz * .045, fy - sz * .1]]); ctx.fill();
    }
  }

  // Arena seating banks either side of the stage: tiers of heads twinkling with lighters (world coords; after venue()).
  function stands(t) {
    for (const side of [-1, 1]) {
      const inner = side < 0 ? 60 : W - 60, outer = side < 0 ? -1700 : W + 1700, topIn = 440, topOut = -760, rows = 20, gap = 52;
      scrap([[inner, topIn], [outer, topOut], [outer, 1400], [inner, 1400]], '#2B2046', { torn: 2, seed: 7050 + side, shadow: false, tone: { color: PAL.purple, cell: 20, dot: .22, op: .7 } });
      for (let row = 0; row < rows; row++) {
        const yA = topIn + 18 + row * gap, yB = topOut + 18 + row * gap;
        marker([[inner, yA + 14], [outer, yB + 14]], '#46386A', 5, { rough: 0 });
        ctx.fillStyle = '#16102A';
        for (let i = 0; i < 34; i++) {
          const u = (i + hash2(row, i) * .7) / 34, x = lerp(inner, outer, u), y = lerp(yA, yB, u) - Math.max(0, Math.sin(bpOf(t) * Math.PI + i + row)) * 5;
          tracePath(ellPts(x, y, 9, 11, 8)); ctx.fill();
        }
        for (let i = 0; i < 34; i++) {
          if (hash2(i + 50, row) > .42) continue;
          const u = (i + hash2(row, i) * .7) / 34, x = lerp(inner, outer, u) + 10, y = lerp(yA, yB, u) - 22;
          const tw = .5 + .5 * Math.sin(t * (2 + hash2(i, row) * 5) + i * 1.3 + row);
          ctx.fillStyle = alpha(PAL.yellow, .45 + tw * .55); ctx.fillRect(x - 4, y - 8, 8, 12);
        }
      }
    }
  }
  // Searchlight beams fanning up from behind the stage (world coords; screen-blended).
  function beams(t, k = 1) {
    ctx.save(); ctx.globalCompositeOperation = 'screen';
    for (let i = 0; i < 4; i++) {
      const x = 360 + i * 400, a = Math.sin(bpOf(t) * Math.PI / 8 + i * 1.9) * .55 + (i - 1.5) * .15;
      const tx = x + Math.sin(a) * 1900, ty = 640 - Math.cos(a) * 1900;
      ctx.fillStyle = alpha([PAL.sky, PAL.pink, PAL.yellow, PAL.mint][i], .13 * k);
      tracePath([[x - 20, 640], [x + 20, 640], [tx + 190, ty], [tx - 190, ty]]); ctx.fill();
    }
    ctx.restore();
  }

  // ---------- the band, with jumps ----------
  // Same positions and look as band.js's bandmates(t, 3), plus J: unison jump height (world px), air: 0..1 airborne pose,
  // land: 0..1 landing squash; o.pos: the vertical video's positions ({ roboX, drumX, huggyX }).
  function band3(t, o = {}) {
    const b = bpOf(t), p = pulse(t, 7), p8 = pulse2(t, 9);
    const hop = Math.max(0, Math.sin(b * Math.PI)) ** 2 * (1 - (o.air ?? 0));
    const J = o.J ?? 0, air = o.air ?? 0, land = o.land ?? 0;
    // drums: the kit stays, the drummer pops off the stool
    const P = o.pos ?? {}, dx = P.drumX ?? 1330, dy = SY + 10, aj = J * .7;
    drumkit(dx, dy, 22, { label: 'LOSS↓' });
    const hit = frac(b) < .5 ? -1 : 1;
    agent(dx, dy - 150 - p * 10 - aj, 42, { eyes: air > .5 ? 'spark' : 'dot', col: '#2A2D38', walk: 0 });
    for (const side of [-1, 1]) {
      const up = side === hit ? p : 0, raise = air * 110;
      marker([[dx + side * 30, dy - 230 - aj], [dx + side * (90 + up * 20 - air * 30), dy - 170 - up * 60 - aj - raise]], '#E8D7B0', 9, { rough: 0 });
    }
    // Robo on guitar (left)
    const rx = P.roboX ?? 520, ry = GY, rj = J;
    bot(rx, ry, 30, { dy: -hop * .6 - rj / 30, rot: Math.sin(b * Math.PI / 2) * .06 * (1 - air), eyes: 'spark', col: '#9FB3C8', aL: lerp(.1, 1.1, air), aR: -.2 + p8 * .25, sq: land * .12, walk: air > .3 ? .25 : undefined });
    ctx.save(); ctx.translate(rx + 10, ry - 140 - hop * 18 - rj); ctx.rotate(-.9 - air * .35);
    scrap(rectPts(-9, -210, 18, 170), '#4A3021', { torn: .3, shadow: false });
    scrap([[-55, -40], [45, -52], [70, 12], [26, 60], [-44, 56], [-72, 6]], PAL.yellow, { torn: .8, ink: PAL.ink, sw: 4, seed: 1220 });
    scrap(ellPts(0, 4, 14, 14, 12), PAL.ink, { torn: .3, shadow: false });
    ctx.restore();
    // Huggy on bass (right)
    const hx = P.huggyX ?? 1520, hy = SY - 10 - hop * 26 - J;
    if (J > 4) { ctx.fillStyle = 'rgb(28 26 31 / .22)'; tracePath(ellPts(hx - 10, GY - 10, 120 - J * .15, 18, 20)); ctx.fill(); }
    ctx.save(); ctx.translate(hx, hy); ctx.rotate(.45 + air * .25);
    scrap(rectPts(-12, -260, 24, 220), '#3A2415', { torn: .3, shadow: false });
    scrap([[-70, -40], [60, -50], [80, 20], [30, 70], [-60, 60], [-85, 10]], PAL.blue, { torn: .8, ink: PAL.ink, sw: 4, seed: 1221 });
    ctx.restore();
    huggy(hx - 10, hy - 110, 95, { mood: 'happy', hands: .3 + p * .4 + air * .6 });
    // Clawd (centre)
    micStand(810, SY + 60, 26);
    clawd(960, GY, 30, {
      hat: 'mohawk', eyes: 'shades', mouth: singMouth(t, true), mic: true,
      aR: lerp(.5 + p * .5, 1.1, air), aL: lerp(-.2 + hop * .7, 1.1, air), dy: -hop * 1.4 - J / 30, sq: land * .18 - hop * .08 + p * .05 - air * .06,
      walk: air > .3 ? .25 : undefined,
    });
  }

  // ---------- fire ----------
  // Cheap flickering flame tongue (three inks), base at (x, y), height h.
  function lick(x, y, h, seed, lean = 0) {
    const f = 1 + Math.sin(T * 19 + seed * 7) * .16 + Math.sin(T * 31 + seed) * .08, sway = Math.sin(T * 9 + seed * 3) * h * .12 + lean * h;
    const layer = (c, k) => { ctx.fillStyle = c; tracePath([[x - h * .28 * k, y], [x - h * .12 * k + sway * .4, y - h * .5 * k * f], [x + sway, y - h * f * k], [x + h * .14 * k + sway * .5, y - h * .45 * k * f], [x + h * .28 * k, y]]); ctx.fill(); };
    layer(PAL.red, 1); layer(PAL.orange, .72); layer(PAL.yellow, .45);
  }
  // The curve burning like a fuse: burnt up to u = k (spark at the front); `blaze` 0..1 grows every flame; sc scales the fire.
  function burnCurve(k, blaze, sc = 1) {
    if (k <= 0) return;
    const N = 34;
    marker(partial(CURVE, k), '#2A1A12', 20 * sc, { rough: 2, smooth: true });   // charred line
    for (let i = 0; i < N; i++) {
      const u = i / (N - 1); if (u > k) break;
      const [x, y] = along(u), fresh = clamp((k - u) / .12);
      lick(x + (hash(i) - .5) * 14, y + 8, (30 + 40 * hash(i + 9)) * (.4 + fresh * .6) * (1 + blaze * (1.6 + hash(i + 3))) * sc, i, -.15);
    }
    if (k < 1) {
      const [sx, sy] = along(k);
      ctx.save(); ctx.globalCompositeOperation = 'screen'; ctx.fillStyle = alpha(PAL.yellow, .35); tracePath(ellPts(sx, sy, 90 * sc, 90 * sc, 18)); ctx.fill(); ctx.restore();
      scrap(burstPts(sx, sy, (58 + jit(10)) * sc, 10, .4, T * 9), PAL.yellow, { torn: .5, shadow: false, ink: PAL.orange, sw: 5 });
    }
  }
  // Marquee bulbs along the curve; lit up to u = k, the front ones pop. Bulbs below u = eaten are gone (burnt). sc: their size.
  function bulbs(t, k, eaten = 0, sc = 1) {
    const N = 24, chase = Math.floor(bpOf(t) * 2);
    for (let i = 0; i < N; i++) {
      const u = i / (N - 1); if (eaten > 0 && u <= eaten + .02) continue;
      const [x, y] = along(u), lit = u <= k, front = lit && k - u < .12 && k < 1;
      const on = lit && (k >= 1 ? (i + chase) % 3 !== 0 : true);
      if (on) { ctx.save(); ctx.globalCompositeOperation = 'screen'; ctx.fillStyle = alpha(PAL.yellow, .35); tracePath(ellPts(x, y, (front ? 44 : 30) * sc, (front ? 44 : 30) * sc, 16)); ctx.fill(); ctx.restore(); }
      const r = (on ? (front ? 20 : 15) : 11) * sc;
      scrap(ellPts(x, y, r, r, 12), on ? '#FFF3A8' : '#6E6A5A', { torn: .5, ink: PAL.ink, sw: 3, shadow: false });
    }
  }
  // Firework pop at the top of the curve.
  function firework(x, y, age) {
    if (age < 0 || age > 1.1) return;
    const k = easeOut(age / .6), fade = 1 - clamp((age - .5) / .6);
    for (let i = 0; i < 20; i++) {
      const a = i / 20 * TAU + .2, r0 = 50 + k * 260, r1 = 90 + k * 380;
      marker([[x + Math.cos(a) * r0, y + Math.sin(a) * r0 + age * age * 60], [x + Math.cos(a) * r1, y + Math.sin(a) * r1 + age * age * 90]], [PAL.yellow, PAL.pink, PAL.white, PAL.sky][i % 4], 12, { alpha: fade, rough: 1 });
    }
    scrap(burstPts(x, y, 70 * (1 - k * .5), 12, .45), PAL.white, { torn: 1, shadow: false, op: fade });
  }
  // Tall pyro column at the stage lip. k: 0..1 height.
  function pyro(x, k, seed) {
    if (k <= .02) return;
    const h = 520 * k;
    ctx.save(); ctx.globalCompositeOperation = 'screen'; ctx.fillStyle = alpha(PAL.orange, .25 * k);
    tracePath(ellPts(x, SY + 40 - h * .5, 150, h * .6, 20)); ctx.fill(); ctx.restore();
    for (let i = 0; i < 4; i++) lick(x + (i - 1.5) * 34, SY + 60, h * (.7 + hash(seed + i) * .4), seed + i);
  }
  // A roadie agent with a tiny PAUSE extinguisher, puffing at the flames.
  function roadie(x, y, k, age) {
    if (k <= 0) return;
    const sx = x - (1 - easeOut(k)) * 260;
    agent(sx, y, 46, { eyes: age > .7 ? 'x' : 'angry', col: '#2A2D38', bar: PAL.yellow, walk: k < 1 ? T * 4 : 0, rot: .08 });
    ctx.save(); ctx.translate(sx + 80, y - 80); ctx.rotate(-.35); ctx.scale(1.7, 1.7);
    scrap(rrPts(-22, -40, 44, 100, 12), PAL.red, { torn: .8, ink: PAL.ink, sw: 3, seed: 7301 });
    scrap(rectPts(-20, -6, 40, 30), PAL.white, { torn: .5, shadow: false });
    txt('PAUSE', 0, 9, 13, PAL.ink, { font: 'archivo' });
    marker([[0, -40], [10, -58], [34, -66]], PAL.ink, 6, { rough: 0 });
    ctx.restore();
    if (age > 0) { // puff… pff.
      const pk = clamp(age / .35), fade = 1 - clamp((age - .5) / .5);
      for (let i = 0; i < 5; i++) {
        const d = pk * (50 + i * 34), px = sx + 150 + d * .55, py = y - 205 - d * .85;
        scrap(ellPts(px, py, 16 + i * 7 * pk, 14 + i * 6 * pk, 12), PAL.white, { torn: 1.5, seed: 7310 + i, shadow: false, op: fade * .95 });
      }
      txt('pff.', sx + 300, y - 400, 60, PAL.white, { font: 'marker', alpha: fade * clamp(age / .3), rot: -.2, stroke: PAL.ink, sw: 8 });
    }
  }
  // Embers drifting up (screen space).
  function embers(lt, n, k) {
    if (k <= 0) return;
    for (let i = 0; i < n; i++) {
      const r = j => hash2(7400 + i, j), age = frac(lt * (.25 + r(1) * .3) + r(2));
      const x = r(3) * W + Math.sin(age * 6 + r(4) * 9) * 40, y = H + 40 - age * (H + 120);
      ctx.fillStyle = [PAL.yellow, PAL.orange, PAL.red][i % 3]; ctx.globalAlpha = k * (1 - age * .6);
      ctx.fillRect(x, y, 6 + r(5) * 6, 6 + r(5) * 6);
    }
    ctx.globalAlpha = 1;
  }

  const HOOK_FONTS = ['anton', 'abril', 'archivo', 'typewriter', 'bungee', 'mono', 'shrikhand', 'courier', 'bebas', 'rammetto'];
  const HOOK_PAPERS = [PAL.white, PAL.newsprint, PAL.yellow, PAL.mint, PAL.ink, PAL.sky, PAL.white, PAL.kraft, PAL.red, PAL.cream];
  // The chorus hook as giant ransom letters: same look as band.js's hook(), for an explicit line (no gap flicker), without
  // pink paper (ransom() can put pink ink on pink paper) and without blackletter (its I/T read as 3/I).
  function hookLine(ln, t, o = {}) {
    if (!ln) return;
    const str = ln.text.toUpperCase().replace(/[—.!,]+$/g, '').replace(/ —/g, '');
    ransom(str, o.x ?? W / 2, o.y ?? 170, o.size ?? 76, { pop: clamp((t - ln.start) / .5) * 1.4, maxW: o.maxW ?? 1700, seed: Math.round(ln.start * 10), rot: o.rot, papers: HOOK_PAPERS, fonts: HOOK_FONTS });
  }

  // ---------- the shot ----------
  section('C3', (p, lt, d, t) => {
    const t0 = t - lt, Ls = linesOf('C3');
    const rs = i => (Ls[i] ? Ls[i].start - t0 : d * i / 4), re = i => (Ls[i] ? Ls[i].end - t0 : d * (i + 1) / 4);
    const beatT = n => onBeat(0, n) - t0;
    const near = (x, m) => Math.round(bpOf(t0 + x) / m) * m;
    const gainT = beatT(near(rs(1) + (re(1) - rs(1)) * .5, 2));      // "and the curves kept gaining": half-bar nearest mid-line 2
    const bulbK = ease(seg(lt, gainT, Math.max(gainT + .4, rs(2) - .35)));
    const landT = rs(3);                                              // the leap lands on line 4's first beat
    const leapT = beatT(near(landT, 1) - 2);                          // …taking off two beats earlier
    const containT = beatT(near(rs(3) + (re(3) - rs(3)) * .78, 2));   // "contain"
    const butT = beatT(near(rs(3) + (re(3) - rs(3)) * .58, 1));       // "but"
    const b = bpOf(t);

    // the backdrop curve's top end sits under the date stamp all chorus (and the stamp can't change here anyway)
    hideStamp();
    // arena darkness beyond the venue's own wall, in world coords so its halftone lines up with venue()'s
    const darkness = () => { ctx.fillStyle = WALL; ctx.fillRect(-3000, -3000, 8000, 8000); halftone(rectPts(-3000, -3000, 8000, 8000), PAL.purple, { cell: 26, dot: .16, op: .5, multiply: false }); };

    if (lt < rs(2)) {
      // ---- crane-up from inside the crowd to the stage ----
      if (lt < rs(1)) hideCaption();
      const ce = ease(seg(lt, .1, rs(2) - .1));
      const zw = lerp(.52, 1.03, ce), cy = lerp(400, 560, ce), cx = 960 + Math.sin(lt * .9) * 30 * (1 - ce);
      camBegin(cx, cy, zw);
      darkness();
      venue(t, 3);
      beams(t);
      stands(t);
      bulbs(t, bulbK);
      firework(CTOP[0], CTOP[1], lt - (rs(2) - .35));
      bandmates(t, 3);
      camEnd();
      // crowd rows, far → near; the near ones sink out of frame as the camera rises
      const R = 7;
      for (let r = 0; r < R; r++) {
        const q = r / (R - 1), s = lerp(28, 175, q ** 1.8) * (1 + ce * .25), y0 = lerp(705, 830, q ** 1.3) + lerp(200, 1100, q ** 1.4) * ce;
        if (y0 - s * 2.2 > H) continue;
        sea(y0, t, { n: Math.round(lerp(40, 7, q)), s, seed: 7000 + r * 50, col: mixCol('#4A3A66', PAL.ink, q ** .6), rim: q < .8 ? alpha(PAL.pink, .55 - q * .4) : null, lighters: .4, horns: .4, hands: .75, jump: .6 });
      }
      hookLine(Ls[0], t, { y: 150 - easeIn(seg(lt, rs(1) - .05, rs(1) + .3)) * 330, size: 96, maxW: 1560 });
    } else if (lt < rs(3)) {
      // ---- line 3: unison hops, then the big leap ----
      hideCaption(); hideStamp();
      const a = lt - rs(2), punch = backOut(seg(a, 0, .25), 1.5);
      const u = seg(lt, leapT, landT), air = lt >= leapT ? Math.min(1, u * 4, (1 - u) * 5) : 0;
      const hopJ = lt < leapT ? Math.max(0, Math.sin(b * Math.PI)) ** 1.5 * 70 : 0;
      const J = hopJ + (lt >= leapT ? (1 - (2 * u - 1) ** 4) * 300 : 0);
      const land = lt < leapT ? Math.exp(-frac(b) * 8) * .6 : 0;
      const z = lerp(1.03, 1.16, punch) + a * .02, cy = lerp(560, 590, punch);
      const [sx, sy] = shakeXY(t, 6 * pulse(t, 7));
      camBegin(960 + sx / z, cy + sy / z, z);
      darkness();
      venue(t, 3);
      stands(t);
      bulbs(t, 1);
      band3(t, { J, air, land });
      sea(1000, t, { n: 22, s: 80, seed: 7600, col: '#3A2D52', lighters: .4, horns: .5, hands: .85, jump: .9 });
      camEnd();
      sea(1060, t, { n: 12, s: 120, seed: 7650, lighters: .3, horns: .6, hands: .9, jump: 1 });
      hookLine(Ls[2], t, { y: 950, size: 100, maxW: 1600 });
    } else {
      // ---- line 4: land into a pyro blast; the curve burns like a fuse; can't contain it ----
      const a = lt - landT, kick = Math.exp(-a * 5);
      const pull = easeOut(seg(a, .05, 1.1));
      const z = lerp(1.18, .84, pull) * (1 + Math.max(0, lt - containT) * .04), cy = lerp(590, 520, pull);
      const [sx, sy] = shakeXY(t, 34 * kick + 8 * pulse(t, 6) + (lt > containT ? 18 * Math.exp(-(lt - containT) * 3) : 0));
      const burnK = ease(seg(lt, landT + .3, containT)) * .85 + seg(lt, landT + .3, containT) * .15, blaze = easeOut(seg(lt, containT, containT + .5));
      camBegin(960 + sx / z, cy + sy / z, z);
      darkness();
      venue(t, 3, { fire: false });
      stands(t);
      // back pyro on each bar downbeat and a huge one on the landing
      const bar = frac(b / 4), barK = bar < .2 ? easeOut(bar / .2) : 1 - ease((bar - .2) / .5);
      const pk = Math.max(Math.exp(-a * 2.2) * (a >= 0 ? 1 : 0), barK * .7, blaze);
      for (const [i, x] of [110, 1610, 1810].entries()) pyro(x, pk * (i === 1 ? .8 : 1), 7200 + i * 10);
      if (blaze < 1) bulbs(t, 1, burnK);
      burnCurve(burnK, blaze);
      if (blaze > 0) { // flames climb the whole banner, tallest where the curve ends
        for (let i = 0; i < 18; i++) { const x = 270 + i * 80 + hash(i + 40) * 30; lick(x, 118 + hash(i + 50) * 20, (60 + hash(i + 60) * 110 + Math.max(0, x - 900) * .25) * blaze, 90 + i, (hash(i + 70) - .5) * .4); }
        for (const x of [265, 1655]) for (let i = 0; i < 5; i++) lick(x, 640 - i * 110, (70 + hash(i + x) * 60) * blaze, 120 + i + x, x < 900 ? -.3 : .3);
      }
      band3(t, { J: 0, land: Math.exp(-a * 6), air: 0 });
      roadie(300, GY + 20, seg(lt, butT - .5, butT - .05), lt - butT);
      sea(975, t, { n: 32, s: 58, seed: 7700, col: '#3A2D52', rim: alpha(PAL.orange, .5), lighters: .45, horns: .4, hands: .85, jump: .9 });
      sea(1040, t, { n: 24, s: 78, seed: 7750, col: '#2A2140', rim: alpha(PAL.orange, .35), lighters: .4, horns: .5, hands: .9, jump: 1 });
      sea(1120, t, { n: 16, s: 104, seed: 7800, bottom: 1500, lighters: .35, horns: .55, hands: .9, jump: 1.2 });
      camEnd();
      // landing flash
      if (a < .08) { ctx.fillStyle = alpha(PAL.yellow, .7 * (1 - a / .08)); ctx.fillRect(0, 0, W, H); }
      embers(lt, 40, Math.max(kick, blaze));
      if (blaze > 0) { ctx.save(); ctx.globalCompositeOperation = 'screen'; ctx.fillStyle = alpha(PAL.orange, .16 * blaze); ctx.fillRect(0, 0, W, H); ctx.restore(); }
    }
  });

  // =====================================================================================================================
  // The vertical video's chorus 3: the arena show from the pit. A tall banner of its own (VBAN) hangs behind the band, so that
  // its curve climbs the tall frame: first the marquee bulbs race up it, then the fire. The band stands closer together (VB3).
  //   lines 1–2  the crane up out of the sea of lighters and horns to the stage, the hook over the rafters; on "the curves kept
  //              gaining" the bulbs race along the curve and the camera tilts up after them to the firework at its top
  //   line 3     the band hops in unison above the hook, then one huge leap with hang-time up the tall frame
  //   line 4     they land on the downbeat into the pyro; the curve burns like a fuse up the banner; the roadie's tiny PAUSE
  //              extinguisher; on "contain" the whole banner goes up, flames climbing off the top of the frame
  // =====================================================================================================================
  const VB3 = { roboX: 640, drumX: 1160, huggyX: 1310 };
  // The arena's darkness past the stage world's edges (world coords, so that its halftone lines up with venue()'s).
  const vdark = () => { ctx.fillStyle = WALL; ctx.fillRect(-3000, -3000, 8000, 8000); halftone(rectPts(-3000, -3000, 8000, 8000), PAL.purple, { cell: 26, dot: .16, op: .5, multiply: false }); };
  // venue(t, 3) with the tall banner, hung from a truss of its own, the stage lights playing over it too.
  // o.name: how far the band's name has slammed onto the banner (0..1; default 1)
  function vvenue(t, o = {}) {
    vdark();
    venue(t, 3, { banner: false, fire: false });
    const { x, y, w, h } = VBAN;
    for (const cx of [x + 140, x + w - 140]) marker([[cx, y - 900], [cx, y - 20]], '#3A3446', 6, { rough: 0 });
    curveBanner(t, 3, { ...VBAN, title: false });
    // the band's name across the top in two lines, clear of the curve's top end on the right
    const nk = o.name ?? 1;
    if (nk > 0) {
      ransom('CLAWD &', x + w / 2 - 50, y + 74, 66, { seed: 77, maxW: w - 220, pop: nk * 1.3 });
      ransom('THE SCALING LAWS', x + w / 2 - 50, y + 150, 54, { seed: 78, maxW: w - 200, pop: nk * 1.3 - .3 });
    }
    ctx.fillStyle = '#5A5866'; ctx.fillRect(x - 180, y - 40, w + 360, 26);
    for (let i = 0; i < 8; i++) scrap(rectPts(x - 150 + i * 150, y - 18, 46, 36), '#2C2A33', { torn: .5, shadow: false });
    ctx.save(); ctx.beginPath(); ctx.rect(x, y, w, h); ctx.clip();
    const beat = bpOf(t), cols = [alpha(PAL.yellow, .16), alpha(PAL.pink, .16), alpha(PAL.sky, .16), alpha(PAL.mint, .14)];
    for (let i = 0; i < 5; i++) spot(200 + i * 380, y + 20, STAGE_Y + 60, 270, cols[i % 4], Math.sin(beat * Math.PI / 4 + i * 1.7) * .6);
    ctx.restore();
  }
  // The whole tall banner going up: flames along its top edge and climbing both sides, taller as they go up.
  function vblaze(k) {
    if (k <= 0) return;
    const { x, y, w, h } = VBAN;
    for (const side of [0, 1]) for (let i = 0; i < 9; i++) lick(x + side * w + (side ? -6 : 6), y + h - 30 - i * (h - 60) / 8, (80 + hash(i + side * 9) * 70 + i * 16) * k, 120 + i + side * 20, side ? .3 : -.3);
    for (let i = 0; i < 10; i++) lick(x + 20 + i * (w - 40) / 9 + hash(i + 40) * 20, y + 10 + hash(i + 50) * 16, (150 + hash(i + 60) * 190) * k, 90 + i, (hash(i + 70) - .5) * .4);
  }
  // Big screen-space rows of the arena crowd, lighters up, along the foot of the frame.
  const vfoot = (t, y = 1700, o = {}) => sea(y, t, { n: 7, s: 175, seed: 7900, lighters: .4, horns: .5, hands: .9, jump: 1, ...o });

  vshot('C3', (p, lt, d, t) => {
    const t0 = t - lt, Ls = linesOf('C3');
    const rs = i => (Ls[i] ? Ls[i].start - t0 : d * i / 4), re = i => (Ls[i] ? Ls[i].end - t0 : d * (i + 1) / 4);
    const beatT = n => onBeat(0, n) - t0;
    const near = (x, m) => Math.round(bpOf(t0 + x) / m) * m;
    const gainT = beatT(near(rs(1) + (re(1) - rs(1)) * .5, 2));
    const bulbK = ease(seg(lt, gainT, Math.max(gainT + .4, rs(2) - .35)));
    const landT = rs(3), leapT = beatT(near(landT, 1) - 2);
    const containT = beatT(near(rs(3) + (re(3) - rs(3)) * .78, 2)), butT = beatT(near(rs(3) + (re(3) - rs(3)) * .58, 1));
    const b = bpOf(t);
    hideStamp();
    ctx.fillStyle = WALL; ctx.fillRect(0, 0, W, H);

    if (lt < rs(2)) {
      // ---- lines 1–2: the crane up out of the crowd to the stage, then the tilt up the curve after the bulbs ----
      if (lt < rs(1)) hideCaption();
      const ce = ease(seg(lt, .1, gainT - .15)), te = ease(seg(lt, gainT - .05, rs(2) - .3));
      const z = lerp(lerp(.42, .95, ce), 1.1, te);
      const cy = lerp(lerp(230, 670, ce), -125, te), cx = lerp(960 + Math.sin(lt * .9) * 30 * (1 - ce), 1110, te);
      inStage(t, () => {
        // (the band's name slams onto the banner once the hook has flown off it)
        vvenue(t, { name: clamp((lt - rs(1) - .15) / .5) }); beams(t); stands(t);
        bulbs(t, bulbK, 0, 1.3);
        firework(CTOP[0], CTOP[1], lt - (rs(2) - .35));
        band3(t, { pos: VB3 });
      }, cx, cy, z);
      // the rows of the crowd, far → near; the near ones sink out of the frame as the camera rises
      const lip = 960 + (960 - cy) * z, R = 8;
      for (let r = 0; r < R; r++) {
        const q = r / (R - 1), s = lerp(24, 200, q ** 1.7) * (1 + ce * .2);
        const y0 = lip + 14 + (H - 60 - lip) * q ** 1.15 + lerp(0, 1500, q ** 1.3) * ce;
        if (y0 - s * 2.4 > H) continue;
        sea(y0, t, { n: Math.round(lerp(24, 6, q)), s, seed: 7000 + r * 50, col: mixCol('#4A3A66', PAL.ink, q ** .6), rim: q < .8 ? alpha(PAL.pink, .55 - q * .4) : null, lighters: .4, horns: .4, hands: .75, jump: .6 });
      }
      const fly = easeIn(seg(lt, rs(1) - .05, rs(1) + .3));
      if (fly < 1) { ctx.save(); ctx.translate(0, -fly * 900); vhook(t, Ls[0], { y: 330 }); ctx.restore(); }
    } else if (lt < rs(3)) {
      // ---- line 3: unison hops, then the big leap, the hook below them ----
      hideCaption();
      const a = lt - rs(2), punch = backOut(seg(a, 0, .25), 1.5);
      const u = seg(lt, leapT, landT), air = lt >= leapT ? Math.min(1, u * 4, (1 - u) * 5) : 0, arc = lt >= leapT ? 1 - (2 * u - 1) ** 4 : 0;
      const hopJ = lt < leapT ? Math.max(0, Math.sin(b * Math.PI)) ** 1.5 * 70 : 0;
      const J = hopJ + arc * 300;
      const land = lt < leapT ? Math.exp(-frac(b) * 8) * .6 : 0;
      const z = lerp(1.04, 1.15, punch) + a * .015, cy = 835 - arc * 100;
      const [sx, sy] = shakeXY(t, 6 * pulse(t, 7));
      inStage(t, () => {
        vvenue(t); stands(t);
        bulbs(t, 1, 0, 1.3);
        band3(t, { J, air, land, pos: VB3 });
        sea(1000, t, { n: 22, s: 80, seed: 7600, col: '#3A2D52', lighters: .4, horns: .5, hands: .85, jump: .9, bottom: 2600 });
      }, 990 + sx / z, cy + sy / z, z);
      vfoot(t, 1640, { s: 150, n: 8, seed: 7650 });
      vhook(t, Ls[2], { y: 1110 });
    } else {
      // ---- line 4: land into a pyro blast; the curve burns like a fuse up the banner; can't contain it ----
      const a = lt - landT, kick = Math.exp(-a * 5), pull = easeOut(seg(a, .05, 1.1));
      const burnK = ease(seg(lt, landT + .3, containT)) * .85 + seg(lt, landT + .3, containT) * .15, blaze = easeOut(seg(lt, containT, containT + .5));
      // (the camera climbs with the fire as it burns up the curve, then sits back for the blaze)
      const climb = ease(burnK) * (1 - .7 * blaze);
      const z = lerp(1.15, 1, pull) * (1 + .1 * climb) * (1 + Math.max(0, lt - containT) * .04), cy = lerp(835, 720, pull) - 190 * climb, cx = lerp(990, 975, pull) + 70 * climb;
      const [sx, sy] = shakeXY(t, 34 * kick + 8 * pulse(t, 6) + (lt > containT ? 18 * Math.exp(-(lt - containT) * 3) : 0));
      inStage(t, () => {
        vvenue(t); stands(t);
        const bar = frac(b / 4), barK = bar < .2 ? easeOut(bar / .2) : 1 - ease((bar - .2) / .5);
        const pk = Math.max(Math.exp(-a * 2.2) * (a >= 0 ? 1 : 0), barK * .7, blaze);
        for (const [i, x] of [380, 1560].entries()) pyro(x, pk * (i ? .9 : 1), 7200 + i * 10);
        if (blaze < 1) bulbs(t, 1, burnK, 1.3);
        burnCurve(burnK, blaze, 1.6);
        vblaze(blaze);
        band3(t, { J: 0, land: Math.exp(-a * 6), air: 0, pos: VB3 });
        roadie(545, GY + 20, seg(lt, butT - .5, butT - .05), lt - butT);
        sea(975, t, { n: 32, s: 58, seed: 7700, col: '#3A2D52', rim: alpha(PAL.orange, .5), lighters: .45, horns: .4, hands: .85, jump: .9, bottom: 2600 });
        sea(1040, t, { n: 24, s: 78, seed: 7750, col: '#2A2140', rim: alpha(PAL.orange, .35), lighters: .4, horns: .5, hands: .9, jump: 1, bottom: 2600 });
      }, cx + sx / z, cy + sy / z, z);
      vfoot(t, 1700, { rim: alpha(PAL.orange, .3) });
      if (a < .08) { ctx.fillStyle = alpha(PAL.yellow, .7 * (1 - a / .08)); ctx.fillRect(0, 0, W, H); }
      embers(lt, 60, Math.max(kick, blaze));
      if (blaze > 0) { ctx.save(); ctx.globalCompositeOperation = 'screen'; ctx.fillStyle = alpha(PAL.orange, .16 * blaze); ctx.fillRect(0, 0, W, H); ctx.restore(); }
    }
  });
})();

;
// ---- src/ch/c08_v4.js ----
// c08_v4 — Verse 4 (Aug 26 → Sep 22, 2026): the panic verse.
// Hot palette (red / yellow / black), more shake and flash as the verse goes on, ending on Opus 5.5's sheepish "Hi, guys!".
(() => {
  const INK = PAL.ink, RED = PAL.red, YEL = PAL.yellow, BLOOD = '#A8201A', NIGHT = '#141119', SUIT = '#1F2438';
  // ransom fonts without blackletter, for words that must read in a split second
  const LOUD = ['anton', 'abril', 'archivo', 'typewriter', 'bungee', 'mono', 'shrikhand', 'bebas', 'rammetto'];
  const LOUD_PAPERS = [PAL.white, PAL.newsprint, YEL, PAL.ink, PAL.sky, PAL.white, PAL.kraft, RED, PAL.cream];
  const shout = (str, x, y, size, o = {}) => ransom(str, x, y, size, { fonts: LOUD, papers: LOUD_PAPERS, ...o });

  // ---------- timing ----------
  // 0..1 through the whole verse: drives the escalating shake / flash.
  const heat = t => { const s = span('V4'); return clamp((t - s.start) / (s.end - s.start)); };
  // Local time of the k-th beat at/after the window start (a line that starts a hair after a beat counts that beat as 0).
  const beatAt = (sg, k) => onBeat(0, Math.ceil(bpOf(sg.start) - .15) + k) - sg.start;
  // Same, but never later than maxP of the window (windows may shrink when timing is final).
  const hitAt = (sg, d, k, maxP = .8) => Math.max(0, Math.min(beatAt(sg, k), d * maxP));
  const popK = (lt, at, dur = .16) => clamp((lt - at) / dur);
  const since = (lt, at) => lt - at;

  // ---------- camera / flash ----------
  // Beat-driven shake that grows through the verse, plus a quick zoom punch on the cut. o.hit: [time, amount] extra impact shake.
  function cam(t, lt, o = {}) {
    const h = heat(t);
    let amt = (o.shake ?? 1) * (2 + 9 * h) * (.3 + .9 * pulse(t, 7));
    for (const [at, a] of o.hits ?? []) if (lt >= at) amt += a * Math.exp(-(lt - at) * 9);
    const [sx, sy] = shakeXY(t, amt, 24);
    const punch = (o.punch ?? .06) * (1 - easeOut(clamp(lt / .15)));
    camBegin((o.cx ?? W / 2) + sx, (o.cy ?? H / 2) + sy, (o.zoom ?? 1) + punch, (o.rot ?? 0) + (hash2(Math.floor(t * 24), 7) - .5) * .0025 * amt);
  }
  function flash(a, col = PAL.white) {
    if (a <= .01) return;
    ctx.save(); ctx.setTransform(RS, 0, 0, RS, 0, 0); ctx.globalAlpha = clamp(a); ctx.fillStyle = col; ctx.fillRect(0, 0, W, H); ctx.restore();
  }
  const flashAt = (lt, at, dur = .1) => lt < at ? 0 : 1 - clamp((lt - at) / dur);
  // the cut-in flash every V4 shot opens with; stronger as the panic builds
  const cutFlash = (t, lt, col = PAL.white) => flash((.35 + .35 * heat(t)) * flashAt(lt, 0, .09), col);

  // ---------- backgrounds ----------
  const bg = col => { ctx.fillStyle = col; ctx.fillRect(-400, -400, W + 800, H + 800); };
  const FULL = rectPts(-400, -400, W + 800, H + 800);
  function rays(cx, cy, n, col, rot = 0, o = {}) {
    const R = o.r ?? 2800, w = o.w ?? .5;
    ctx.save(); ctx.fillStyle = col; ctx.beginPath();
    for (let i = 0; i < n; i++) {
      const a = rot + i / n * TAU, da = TAU / n * w / 2;
      ctx.moveTo(cx, cy); ctx.lineTo(cx + Math.cos(a - da) * R, cy + Math.sin(a - da) * R); ctx.lineTo(cx + Math.cos(a + da) * R, cy + Math.sin(a + da) * R); ctx.closePath();
    }
    ctx.fill(); ctx.restore();
  }
  function glow(x, y, r, col, a = .4) {
    const g = ctx.createRadialGradient(x, y, 0, x, y, r);
    g.addColorStop(0, alpha(col, a)); g.addColorStop(1, alpha(col, 0));
    ctx.save(); ctx.globalCompositeOperation = 'screen'; ctx.fillStyle = g; ctx.fillRect(x - r, y - r, 2 * r, 2 * r); ctx.restore();
  }
  // radial action lines around a point
  function actionLines(cx, cy, r0, r1, n, col, w = 6, seed = 1) {
    for (let i = 0; i < n; i++) {
      const a = (i + hash2(seed, i) * .6) / n * TAU, rr0 = r0 * (1 + hash2(seed + 9, i) * .3 + jit(.05));
      marker([[cx + Math.cos(a) * rr0, cy + Math.sin(a) * rr0], [cx + Math.cos(a) * r1, cy + Math.sin(a) * r1]], col, w, { rough: 0 });
    }
  }
  function confettiFall(lt, n, seed, o = {}) {
    const cols = o.cols ?? [PAL.pink, YEL, PAL.blue, PAL.mint, RED, PAL.white, PAL.clawd];
    for (let i = 0; i < n; i++) {
      const r = k => hash2(seed + i, k);
      const x = r(1) * (W + 200) - 100 + Math.sin(lt * 3 + r(2) * 6) * 30;
      const y = ((r(3) * (H + 200)) + lt * (240 + r(4) * 280)) % (H + 200) - 100;
      ctx.save(); ctx.translate(x, y); ctx.rotate(lt * (2 + r(5) * 6) + r(6) * 6); ctx.scale(1, Math.cos(lt * 9 + r(7) * 6));
      ctx.fillStyle = cols[i % cols.length]; ctx.fillRect(-11, -6, 22, 12); ctx.restore();
    }
  }
  // confetti / debris bursting from a point: k = seconds since the burst
  function burstBits(x, y, k, n, seed, o = {}) {
    if (k < 0) return;
    const cols = o.cols ?? [PAL.pink, YEL, PAL.blue, PAL.mint, RED, PAL.white];
    for (let i = 0; i < n; i++) {
      const r = j => hash2(seed + i, j), a = (o.a0 ?? 0) + (r(1) - .5) * (o.spread ?? TAU), v = (o.v ?? 900) * (.4 + r(2) * .8);
      const px = x + Math.cos(a) * v * k, py = y + Math.sin(a) * v * k + (o.g ?? 900) * k * k;
      ctx.save(); ctx.translate(px, py); ctx.rotate(k * (4 + r(3) * 8) + r(4) * 6); ctx.scale(1, Math.cos(k * 10 + r(5) * 6));
      ctx.fillStyle = cols[i % cols.length]; const z = o.size ?? 12; ctx.fillRect(-z, -z * .55, z * 2, z * 1.1); ctx.restore();
    }
  }

  // ---------- props that props.js doesn't have ----------
  function note(str, x, y, w, h, col, rot, size, o = {}) {
    const k = o.pop ?? 1; if (k <= 0) return;
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot + jit(.012)); const s = backOut(k, 2); ctx.scale(s, s);
    scrap(rectPts(-w / 2, -h / 2, w, h), col, { torn: 1.2, seed: 1600 + (hstr(str) * 100 | 0), shadow: [5, 7] });
    const L = str.split('\n');
    L.forEach((l, i) => txt(l, 0, (i - (L.length - 1) / 2) * size * 1.08 + 6, size, o.ink ?? INK, { font: o.font ?? 'marker', maxW: w - 26 }));
    scrap(ellPts(0, -h / 2 + 13, 10, 10, 10), o.pin ?? RED, { torn: .2, shadow: [2, 3] });
    ctx.restore();
  }
  function goldStar(x, y, R, label, rot = 0, o = {}) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot); if (o.s) ctx.scale(o.s, o.s);
    if (o.glow) rays(0, 0, 14, alpha(YEL, .55 * o.glow), T * 2, { r: R * 2.6 });
    scrap(starPts(0, 0, R, .5, 5), PAL.gold, { torn: 1, ink: INK, sw: 5, seed: 1701, shade: '#B07A10', shadeOp: .45 });
    if (label) {
      scrap(rectPts(-R * 1.08, -R * .02, R * 2.16, R * .46), RED, { torn: 1, seed: 1702, ink: INK, sw: 4, shadow: [4, 5] });
      txt(label, 0, R * .22, R * .36, PAL.white, { font: 'anton', maxW: R * 1.95 });
    }
    ctx.restore();
  }
  // yellow police tape with repeated lettering, from (x1, y1) to (x2, y2)
  function tapeBand(x1, y1, x2, y2, w, text, o = {}) {
    const a = Math.atan2(y2 - y1, x2 - x1), L = Math.hypot(x2 - x1, y2 - y1);
    ctx.save(); ctx.translate(x1, y1); ctx.rotate(a + jit(.002));
    scrap(rectPts(0, -w / 2, L, w), YEL, { torn: 1.5, seed: o.seed ?? 1710, shadow: [6, 10], step: 40 });
    ctx.save(); tracePath(rectPts(0, -w / 2, L, w)); ctx.clip();
    ctx.fillStyle = INK; ctx.fillRect(0, -w / 2 + 5, L, 4); ctx.fillRect(0, w / 2 - 9, L, 4);
    const size = w * .5, tw = textW(text, size, 'archivo') + size;
    for (let x = -((o.scroll ?? 0) % tw) - tw; x < L; x += tw) txt(text, x, 2, size, INK, { font: 'archivo', align: 'left' });
    ctx.restore(); ctx.restore();
  }
  function cheque(x, y, w, rot, amount, o = {}) {
    const h = w * .44;
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot); if (o.s) ctx.scale(o.s, o.s);
    scrap(rectPts(-w / 2, -h / 2, w, h), '#DCEFD6', { torn: 1.3, seed: 1715, ink: INK, sw: 4, tone: { color: '#8FC08C', cell: 9, dot: .2, op: .45 }, shadow: [8, 11] });
    txt('PAY TO: HUGGING FACE', -w / 2 + 26, -h / 2 + 34, w * .052, INK, { font: 'typewriter', align: 'left' });
    txt('NVIDIA', w / 2 - 26, -h / 2 + 34, w * .05, '#4A8A2A', { font: 'archivo', align: 'right' });
    scrap(rectPts(-w * .45, -h * .2, w * .9, h * .42), PAL.white, { torn: .8, seed: 1716, ink: INK, sw: 2, shadow: false });
    txt(amount, 0, h * .01, w * .105, INK, { font: 'anton', maxW: w * .86 });
    marker([[w * .08, h * .36], [w * .44, h * .36]], INK, 2, { rough: 0 });
    marker([[w * .1, h * .33], [w * .16, h * .22], [w * .2, h * .34], [w * .26, h * .2], [w * .3, h * .33], [w * .4, h * .25]], PAL.blue, 4, { rough: 1, smooth: true });
    ctx.restore();
  }
  // side-view car facing right; (x, y) = ground centre; ≈ 12s long, 4.5s tall
  function carSide(x, y, s, col, o = {}) {
    ctx.save(); ctx.translate(x, y); if (o.rot) ctx.rotate(o.rot); if (o.flip) ctx.scale(-1, 1);
    const low = o.race ? .6 : 1;
    scrap([[-6 * s, -1 * s], [-5.9 * s, -2.6 * s], [-3 * s, -2.9 * s], [-1.8 * s, (-2.9 - 1.5 * low) * s], [1.9 * s, (-2.9 - 1.5 * low) * s], [3.3 * s, -2.9 * s], [5.8 * s, -2.4 * s], [6.3 * s, -1 * s]],
      col, { torn: .6, seed: o.seed ?? 1400, ink: INK, sw: .16 * s, shade: true, shadeOp: .25 });
    scrap([[-1.5 * s, -3 * s], [-1.3 * s, (-2.95 - 1.2 * low) * s], [.1 * s, (-2.95 - 1.2 * low) * s], [.1 * s, -3 * s]], PAL.sky, { torn: .3, shadow: false, ink: INK, sw: .1 * s });
    scrap([[.5 * s, -3 * s], [.5 * s, (-2.95 - 1.2 * low) * s], [1.7 * s, (-2.95 - 1.2 * low) * s], [2.8 * s, -3 * s]], PAL.sky, { torn: .3, shadow: false, ink: INK, sw: .1 * s });
    if (o.stripe) scrap(rectPts(-5.9 * s, -2.1 * s, 12 * s, .5 * s), o.stripe, { torn: .3, shadow: false });
    if (o.num !== undefined) { scrap(ellPts(-.2 * s, -1.9 * s, .95 * s, .95 * s, 16), PAL.white, { torn: .3, shadow: false, ink: INK, sw: .08 * s }); txt(String(o.num), -.2 * s, -1.85 * s, 1.3 * s, INK, { font: 'anton' }); }
    for (const wx of [-3.7, 3.7]) {
      ctx.save(); ctx.translate(wx * s, -1 * s); ctx.rotate(o.spin ?? 0);
      scrap(ellPts(0, 0, 1.35 * s, 1.35 * s, 18), INK, { torn: .4, shadow: false });
      scrap(ellPts(0, 0, .62 * s, .62 * s, 12), '#C8C8CC', { torn: .2, shadow: false });
      ctx.fillStyle = INK; ctx.fillRect(-.1 * s, -.62 * s, .2 * s, 1.24 * s); ctx.fillRect(-.62 * s, -.1 * s, 1.24 * s, .2 * s);
      ctx.restore();
    }
    ctx.restore();
  }
  // front-view car; (x, y) = ground centre; ≈ 8s wide, 5s tall
  function carFront(x, y, s, col, o = {}) {
    ctx.save(); ctx.translate(x, y); if (o.rot) ctx.rotate(o.rot);
    for (const side of [-1, 1]) scrap(rrPts(side * 3.2 * s - .7 * s, -1.3 * s, 1.4 * s, 1.5 * s, .3 * s), INK, { torn: .3, shadow: false });
    scrap([[-2.6 * s, -3 * s], [2.6 * s, -3 * s], [3.2 * s, -4.9 * s + 1.6 * s], [-3.2 * s, -4.9 * s + 1.6 * s]].map(([a, b]) => [a, b - 1.6 * s]), col, { torn: .5, seed: 1420, ink: INK, sw: .14 * s });
    scrap([[-2.3 * s, -4.5 * s], [2.3 * s, -4.5 * s], [2.8 * s, -3.4 * s], [-2.8 * s, -3.4 * s]], PAL.sky, { torn: .3, shadow: false, ink: INK, sw: .1 * s });
    scrap(rrPts(-4 * s, -3.4 * s, 8 * s, 2.5 * s, .6 * s), col, { torn: .6, seed: 1421, ink: INK, sw: .14 * s, shade: true, shadeOp: .22 });
    for (const side of [-1, 1]) { scrap(ellPts(side * 2.85 * s, -2.3 * s, .75 * s, .55 * s, 14), PAL.yellow, { torn: .3, shadow: false, ink: INK, sw: .08 * s }); }
    scrap(rrPts(-1.6 * s, -2.7 * s, 3.2 * s, 1 * s, .2 * s), '#3A3A40', { torn: .3, shadow: false });
    ctx.fillStyle = '#8A8A92'; for (let i = 0; i < 3; i++) ctx.fillRect(-1.4 * s, -2.55 * s + i * .3 * s, 2.8 * s, .1 * s);
    ctx.restore();
  }
  function jet(x, y, s, rot, o = {}) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot);
    if (o.flame) for (let i = 0; i < 2; i++) scrap([[-5 * s, -.45 * s], [-5 * s - (3.2 - i * 1.3 + jit(.6)) * s * o.flame, 0], [-5 * s, .45 * s]], i ? YEL : PAL.orange, { torn: .4, shadow: false });
    const col = o.col ?? '#9AA2AF', dk = mixCol(col, INK, .25);
    scrap([[1.2 * s, 0], [-2.2 * s, -3.8 * s], [-3.3 * s, -3.8 * s], [-2 * s, 0], [-3.3 * s, 3.8 * s], [-2.2 * s, 3.8 * s]], dk, { torn: .5, seed: 1720, shadow: [10, 14], ink: INK, sw: .1 * s });
    scrap([[-3.6 * s, 0], [-4.9 * s, -1.7 * s], [-5.4 * s, -1.7 * s], [-4.8 * s, 0], [-5.4 * s, 1.7 * s], [-4.9 * s, 1.7 * s]], dk, { torn: .4, seed: 1721, shadow: false, ink: INK, sw: .08 * s });
    scrap([[5.4 * s, 0], [3.6 * s, -.6 * s], [-5.1 * s, -.55 * s], [-5.1 * s, .55 * s], [3.6 * s, .6 * s]], col, { torn: .5, seed: 1722, ink: INK, sw: .12 * s, shadow: [8, 12] });
    scrap(ellPts(2.5 * s, 0, 1 * s, .32 * s, 12), PAL.sky, { torn: .2, shadow: false, ink: INK, sw: .07 * s });
    ctx.restore();
  }
  // a fist coming down from above; (x, y) = bottom of the fist
  function slamFist(x, y, s, o = {}) {
    const skin = o.skin ?? SKINS[0];
    scrap(rectPts(x - 1.5 * s, -400, 3 * s, y - 3 * s + 400), o.sleeve ?? SUIT, { torn: 1, seed: 1730, shade: true, shadeOp: .25 });
    scrap(rectPts(x - 1.65 * s, y - 3.4 * s, 3.3 * s, .8 * s), PAL.white, { torn: .5, seed: 1731, shadow: false, ink: INK, sw: .06 * s });
    scrap(rrPts(x - 1.8 * s, y - 2.7 * s, 3.6 * s, 2.7 * s, .9 * s), skin, { torn: .6, seed: 1732, ink: INK, sw: .1 * s });
    for (let i = 1; i < 4; i++) marker([[x - 1.8 * s + i * .9 * s, y - 1.2 * s], [x - 1.8 * s + i * .9 * s, y - .15 * s]], mixCol(skin, INK, .45), .12 * s, { rough: .4 });
    scrap(rrPts(x + 1.25 * s, y - 2.4 * s, 1.1 * s, 1.7 * s, .5 * s), skin, { torn: .4, ink: INK, sw: .1 * s, shadow: false });
  }
  // big arcade button; (x, y) = centre of the top; press 0..1
  function bigButton(x, y, r, label, press = 0) {
    scrap(rrPts(x - r * 1.35, y - r * .1, r * 2.7, r * 1.0, r * .15), YEL, { torn: 1, seed: 1733, ink: INK, sw: 5 });
    ctx.save(); tracePath(rrPts(x - r * 1.35, y - r * .1, r * 2.7, r * 1.0, r * .15)); ctx.clip();
    ctx.fillStyle = INK; for (let i = -6; i < 8; i++) { ctx.beginPath(); ctx.moveTo(x - r * 1.35 + i * r * .4, y + r); ctx.lineTo(x - r * 1.35 + i * r * .4 + r * .2, y + r); ctx.lineTo(x - r * 1.35 + i * r * .4 + r * .6, y - r * .1); ctx.lineTo(x - r * 1.35 + i * r * .4 + r * .4, y - r * .1); ctx.fill(); }
    ctx.restore();
    const hgt = lerp(r * .38, r * .08, press), top = y - hgt;
    scrap([...ellPts(x, y, r, r * .36, 24).filter(p => p[1] >= y - 1), [x - r, top], ...ellPts(x, top, r, r * .36, 24).filter(p => p[1] <= top + 1).reverse(), [x + r, y]], '#A51E14', { torn: .6, seed: 1734, ink: INK, sw: 4, shadow: false });
    scrap(ellPts(x, top, r, r * .36, 28), RED, { torn: .6, seed: 1735, ink: INK, sw: 4, shadow: false });
    ctx.fillStyle = 'rgb(255 255 255 / .35)'; tracePath(ellPts(x - r * .35, top - r * .1, r * .3, r * .08, 12)); ctx.fill();
    txt(label, x, top + 2, r * .34, PAL.white, { font: 'archivo', maxW: r * 1.6, sy: .7 });
  }
  function pie(x, y, r, frac, o = {}) {
    scrap(ellPts(x, y, r, r, 40), PAL.white, { torn: 1, seed: 1740, ink: INK, sw: 5, tone: { color: PAL.blue, cell: 12, dot: .22, op: .45 } });
    const a0 = -TAU / 4, a1 = a0 + TAU * frac, am = (a0 + a1) / 2, off = (o.pop ?? 0) * r * .2;
    const ox = x + Math.cos(am) * off, oy = y + Math.sin(am) * off, pts = [[ox, oy]];
    for (let i = 0; i <= 16; i++) { const a = lerp(a0, a1, i / 16); pts.push([ox + Math.cos(a) * r, oy + Math.sin(a) * r]); }
    scrap(pts, PAL.clawd, { torn: 1, seed: 1741, ink: INK, sw: 5, shade: PAL.clawdDk, shadeOp: .4 });
    if (o.label) txt(o.label, ox + Math.cos(am) * r * .58, oy + Math.sin(am) * r * .58, r * .3, PAL.white, { font: 'anton', stroke: INK, sw: 7 });
  }
  function hammer(x, y, s, rot) { // (x, y) = grip; hammer points "up" at rot 0
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot);
    scrap(rectPts(-.3 * s, -4 * s, .6 * s, 5 * s), '#9A6A3C', { torn: .3, seed: 1745, shadow: false, ink: INK, sw: .08 * s });
    scrap(rrPts(-1.5 * s, -5 * s, 3 * s, 1.2 * s, .2 * s), '#5E6470', { torn: .3, seed: 1746, ink: INK, sw: .1 * s, shadow: false });
    ctx.restore();
  }
  function spring(x, y0, y1, w, n = 7, col = '#8C8A92') {
    const pts = [[x, y0]];
    for (let i = 1; i < n * 2; i++) pts.push([x + (i % 2 ? -w : w), lerp(y0, y1, i / (n * 2))]);
    pts.push([x, y1]);
    marker(pts, INK, 14, { rough: 0 }); marker(pts, col, 8, { rough: 0 });
  }
  // gift box: (x, by) = bottom centre
  function giftBox(x, by, w, h, col, rib, o = {}) {
    ctx.save(); ctx.translate(x, by); if (o.rot) ctx.rotate(o.rot);
    scrap(rectPts(-w / 2, -h, w, h), col, { torn: 1, seed: o.seed ?? 1500, ink: INK, sw: 4, shade: true, shadeOp: .22 });
    if (o.tone) halftone(rectPts(-w / 2, -h, w, h), o.tone, { cell: 16, dot: .2, op: .35 });
    scrap(rectPts(-w * .08, -h, w * .16, h), rib, { torn: .5, shadow: false, ink: INK, sw: 2 });
    ctx.restore();
  }
  // lid: (x, y) = lid bottom centre
  function giftLid(x, y, w, col, rib, rot = 0, o = {}) {
    const lw = w * 1.1, lh = w * .2;
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot);
    scrap(rectPts(-lw / 2, -lh, lw, lh), col, { torn: .8, seed: (o.seed ?? 1500) + 3, ink: INK, sw: 4, shade: true, shadeOp: .2 });
    scrap(rectPts(-w * .08, -lh, w * .16, lh), rib, { torn: .4, shadow: false, ink: INK, sw: 2 });
    for (const side of [-1, 1]) scrap(ellPts(side * w * .14, -lh - w * .07, w * .15, w * .08, 16, side * .5), rib, { torn: .5, seed: 1510 + side, ink: INK, sw: 3, shadow: false });
    scrap(ellPts(0, -lh - w * .05, w * .05, w * .05, 10), rib, { torn: .3, ink: INK, sw: 3, shadow: false });
    ctx.restore();
  }
  function stopwatch(x, y, r, text, ang) {
    scrap(rectPts(x - r * .16, y - r * 1.3, r * .32, r * .3), '#9A9AA6', { torn: .4, seed: 1750, ink: INK, sw: 3 });
    scrap(ellPts(x, y - r * 1.34, r * .2, r * .12, 12), RED, { torn: .3, seed: 1751, ink: INK, sw: 3, shadow: false });
    scrap(ellPts(x, y, r, r, 40), '#C9C9D1', { torn: 1, seed: 1752, ink: INK, sw: 5 });
    scrap(ellPts(x, y, r * .86, r * .86, 40), PAL.white, { torn: .6, seed: 1753, shadow: false });
    ctx.strokeStyle = INK; ctx.lineWidth = 4;
    for (let i = 0; i < 12; i++) { const a = i / 12 * TAU; ctx.beginPath(); ctx.moveTo(x + Math.cos(a) * r * .72, y + Math.sin(a) * r * .72); ctx.lineTo(x + Math.cos(a) * r * .82, y + Math.sin(a) * r * .82); ctx.stroke(); }
    marker([[x, y], [x + Math.cos(ang - TAU / 4) * r * .7, y + Math.sin(ang - TAU / 4) * r * .7]], RED, 6, { rough: 0 });
    scrap(rrPts(x - r * .7, y + r * .12, r * 1.4, r * .42, 8), INK, { torn: .4, shadow: false });
    txt(text, x, y + r * .34, r * .3, '#6CF2B0', { font: 'code', maxW: r * 1.3 });
  }
  function bib(x, y, w, h, text, rot = 0) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot + jit(.01));
    scrap(rectPts(-w / 2, -h / 2, w, h), PAL.white, { torn: .8, seed: 1760 + (hstr(text) * 50 | 0), ink: INK, sw: 3, shadow: [4, 5] });
    txt(text, 0, 3, h * .62, INK, { font: 'anton', maxW: w - 16 });
    for (const side of [-1, 1]) scrap(ellPts(side * (w / 2 - 10), -h / 2 + 10, 5, 5, 8), '#AAA', { torn: .1, shadow: false });
    ctx.restore();
  }
  function noteGlyph(x, y, s, col = INK) {
    scrap(ellPts(x, y, .55 * s, .4 * s, 12, -.4), col, { torn: .2, shadow: false });
    marker([[x + .48 * s, y - .1 * s], [x + .48 * s, y - 1.9 * s], [x + 1.2 * s, y - 1.3 * s]], col, .18 * s, { rough: 0 });
  }
  function bandage(x, y, w, rot) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot);
    scrap(rrPts(-w / 2, -w * .17, w, w * .34, w * .12), '#F2D2B5', { torn: .5, shadow: [3, 4], ink: INK, sw: 2.5 });
    scrap(rectPts(-w * .16, -w * .12, w * .32, w * .24), '#E5B994', { torn: .3, shadow: false });
    ctx.restore();
  }
  // lemniscate ∞ outline, drawn in marker
  function infinity(x, y, a, w, col, k = 1) {
    const pts = []; for (let i = 0; i <= 64; i++) { const u = i / 64 * TAU, d = 1 + Math.sin(u) ** 2; pts.push([x + a * Math.cos(u) / d, y + a * Math.sin(u) * Math.cos(u) / d]); }
    marker(partial(pts, k), col, w, { rough: 1.5, smooth: true });
  }
  // agent() with big twinkling cartoon star eyes painted over its screen
  function starAgent(x, y, s, o = {}) {
    agent(x, y, s, { ...o, eyes: 'dot' });
    ctx.save(); ctx.translate(x, y + (o.dy ?? 0) * s); if (o.rot) ctx.rotate(o.rot);
    ctx.fillStyle = o.col ?? '#22252E'; ctx.fillRect(-1.15 * s, -2.55 * s, 2.3 * s, 1.35 * s);
    const tw = 1 + .15 * Math.sin(T * 20 + x * .01);
    for (const side of [-1, 1]) scrap(starPts(side * .5 * s, -1.9 * s, .5 * s * tw, .45, 5, -TAU / 4 + side * .2), o.star ?? YEL, { torn: .2, shadow: false, ink: INK, sw: .07 * s });
    ctx.restore();
  }
  function drop(x, y, r, a, col) {
    const pts = []; for (let i = 0; i < 14; i++) { const b = i / 14 * TAU, rr = r * (1 + 1.1 * Math.max(0, Math.cos(b)) ** 4); pts.push([x + Math.cos(b + a) * rr, y + Math.sin(b + a) * rr]); }
    scrap(pts, col, { torn: .5, shadow: [3, 4], ink: INK, sw: 2.5 });
  }
  // the pageant sash for the "guardrail" man (TRUMP, trumpHair() and longTie() are in cast.js); (x, y) = person ground, s = person scale
  function sash(x, y, s, text) {
    const x1 = x - 1.95 * s, y1 = y - 4.35 * s, x2 = x + 1.55 * s, y2 = y - 7.8 * s, a = Math.atan2(y2 - y1, x2 - x1), L = Math.hypot(x2 - x1, y2 - y1), w = 1.3 * s;
    ctx.save(); ctx.translate(x1, y1); ctx.rotate(a);
    scrap(rectPts(-.1 * s, -w / 2, L + .2 * s, w), PAL.white, { torn: .5, seed: 1770, shadow: [.1 * s, .15 * s], ink: INK, sw: .05 * s });
    ctx.fillStyle = RED; ctx.fillRect(-.1 * s, -w / 2 + .06 * s, L + .2 * s, .13 * s); ctx.fillRect(-.1 * s, w / 2 - .19 * s, L + .2 * s, .13 * s);
    txt(text, L / 2, .05 * s, .85 * s, RED, { font: 'anton', maxW: L - .1 * s });
    ctx.restore();
  }
  function wreathEmblem(x, y, r, col, op = .5) {
    ctx.save(); ctx.globalAlpha *= op; ctx.strokeStyle = col; ctx.lineWidth = r * .04;
    ctx.beginPath(); ctx.arc(x, y, r * .62, 0, TAU); ctx.stroke();
    for (const k of [-.5, 0, .5]) { ctx.beginPath(); ctx.ellipse(x, y, r * .62 * Math.abs(Math.cos(k * 2.2)) + 1, r * .62, 0, 0, TAU); ctx.stroke(); }
    for (const k of [-.35, 0, .35]) { ctx.beginPath(); ctx.moveTo(x - r * .62 * Math.cos(Math.asin(k)), y + k * r * .62); ctx.lineTo(x + r * .62 * Math.cos(Math.asin(k)), y + k * r * .62); ctx.stroke(); }
    ctx.fillStyle = col;
    for (const side of [-1, 1]) for (let i = 0; i < 9; i++) {
      const a = Math.PI / 2 + side * (.45 + i * .27), lx = x + Math.cos(a) * r * .82, ly = y + Math.sin(a) * r * .82;
      tracePath(ellPts(lx, ly, r * .1, r * .045, 10, a + side * .9)); ctx.fill();
    }
    ctx.restore();
  }
  // big stained-glass arch (static art, cached)
  function stainedGlass(x, y, s = 1) {
    const img = cached('v4-stained-glass', 640, 760, (w, h) => {
      const cx = w / 2, R = w / 2 - 16;
      const arch = [];
      for (let i = 0; i <= 28; i++) { const a = Math.PI + i / 28 * Math.PI; arch.push([cx + Math.cos(a) * R, 16 + R + Math.sin(a) * R]); }
      arch.push([cx + R, h - 16], [cx - R, h - 16]);
      ctx.save(); tracePath(arch); ctx.clip();
      const cols = [RED, YEL, PAL.blue, '#FF8A2A', PAL.pink, PAL.mint, PAL.purple, YEL, RED];
      const nx = 5, ny = 7, cw = w / nx, ch = h / ny;
      const J = (i, j) => [i * cw + (i > 0 && i < nx ? (hash2(i, j) - .5) * cw * .55 : 0), j * ch + (j > 0 && j < ny ? (hash2(i + 50, j) - .5) * ch * .55 : 0)];
      for (let i = 0; i < nx; i++) for (let j = 0; j < ny; j++) {
        const q = [J(i, j), J(i + 1, j), J(i + 1, j + 1), J(i, j + 1)];
        ctx.fillStyle = cols[(i * 3 + j * 5) % cols.length]; tracePath(q); ctx.fill();
        ctx.strokeStyle = INK; ctx.lineWidth = 10; ctx.lineJoin = 'round'; ctx.stroke();
      }
      // the pro-human figure: a person in a blue roundel with a heart
      const fy = h * .44;
      ctx.fillStyle = PAL.blue; tracePath(ellPts(cx, fy, 200, 200, 48)); ctx.fill(); ctx.strokeStyle = INK; ctx.lineWidth = 12; ctx.stroke();
      ctx.fillStyle = YEL; tracePath(ellPts(cx, fy - 95, 48, 48, 30)); ctx.fill(); ctx.stroke();
      tracePath([[cx - 70, fy - 35], [cx + 70, fy - 35], [cx + 50, fy + 140], [cx - 50, fy + 140]]); ctx.fill(); ctx.stroke();
      for (const side of [-1, 1]) { tracePath([[cx + side * 60, fy - 32], [cx + side * 165, fy - 120], [cx + side * 185, fy - 95], [cx + side * 75, fy + 5]]); ctx.fill(); ctx.stroke(); }
      ctx.fillStyle = RED; tracePath(heartPts(cx, fy + 40, 34)); ctx.fill(); ctx.lineWidth = 7; ctx.stroke();
      ctx.restore();
      ctx.strokeStyle = INK; ctx.lineWidth = 22; tracePath(arch); ctx.stroke();
    });
    blit(img, x, y, { s });
  }
  function pewRow(x0, x1, top) {
    scrap(rectPts(x0, top + 55, x1 - x0, 420), '#6A3E22', { torn: 1, seed: 1780, ink: INK, sw: 4, shade: true, shadeOp: .25 });
    for (let i = 0; i < 6; i++) marker([[x0 + 20, top + 95 + i * 42 + Math.sin(i) * 6], [x1 - 20, top + 90 + i * 42 + Math.cos(i) * 6]], '#4E2C16', 3, { rough: 2, alpha: .6 });
    scrap(rrPts(x0 - 30, top, x1 - x0 + 60, 62, 18), '#8A5530', { torn: 1, seed: 1781, ink: INK, sw: 4, shade: true, shadeOp: .2 });
    for (const ex of [x0 - 60, x1 + 10]) scrap(rrPts(ex, top - 60, 50, 520, 26), '#5A331C', { torn: 1, seed: 1782 + (ex > W / 2), ink: INK, sw: 4 });
  }
  function hymnal(x, y, w, h, rot) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot);
    scrap(rectPts(-w / 2, -h / 2, w, h), '#7A1C1C', { torn: .8, seed: 1790, ink: INK, sw: 3, shade: true, shadeOp: .25 });
    scrap(rectPts(-w / 2 + 6, -h / 2 + 6, w - 12, h - 12), '#7A1C1C', { torn: .3, shadow: false, ink: PAL.gold, sw: 2 });
    txt('PRO-', 0, -h * .17, h * .3, PAL.gold, { font: 'anton', maxW: w - 24 });
    txt('HUMAN', 0, h * .19, h * .3, PAL.gold, { font: 'anton', maxW: w - 24 });
    ctx.restore();
  }
  function mitten(x, y, s, rot) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot);
    scrap(rrPts(-.55 * s, -.6 * s, 1.1 * s, 1.3 * s, .5 * s), '#9A6B45', { torn: .4, seed: 1795, ink: INK, sw: .06 * s, shadow: [.06 * s, .08 * s] });
    scrap(rrPts(.35 * s, -.3 * s, .45 * s, .7 * s, .22 * s), '#9A6B45', { torn: .3, ink: INK, sw: .05 * s, shadow: false });
    marker([[-.45 * s, .1 * s], [-.25 * s, -.05 * s], [-.05 * s, .1 * s], [.15 * s, -.05 * s], [.35 * s, .1 * s]], PAL.white, .1 * s, { rough: 0 });
    scrap(rectPts(-.6 * s, .55 * s, 1.2 * s, .35 * s), '#E8E0D0', { torn: .3, shadow: false, ink: INK, sw: .04 * s });
    ctx.restore();
  }
  function calPage(x, y, w, h, day, o = {}) {
    ctx.save(); ctx.translate(x, y); if (o.rot) ctx.rotate(o.rot); if (o.s) ctx.scale(o.s, o.s);
    scrap(rectPts(-w / 2, -h / 2, w, h), PAL.white, { torn: 1, seed: 1800 + day, ink: INK, sw: 3, shadow: o.shadow ?? [6, 8] });
    scrap(rectPts(-w / 2, -h / 2, w, h * .24), RED, { torn: .8, seed: 1830 + day, shadow: false });
    txt('SEP', 0, -h / 2 + h * .125, h * .17, PAL.white, { font: 'archivo', spacing: 10 });
    txt(String(day), 0, h * .14, h * .55, INK, { font: 'anton' });
    if (day === 12) { txt('PACE!', w * .22, h * .36, h * .1, RED, { font: 'marker', rot: -.12 }); circleMark(w * .22, h * .36, w * .24, h * .08, RED, 5); }
    ctx.restore();
  }
  // Clawd's face-left wink: paints over Clawd's left eye and draws a closed-eye wink (only for unrotated, unflipped Clawd)
  function clawdWink(x, y, u, dy = 0) {
    const ex = x - 2.3 * u, ey = y + dy * u - 6.2 * u;
    ctx.fillStyle = PAL.clawd; ctx.fillRect(ex - .75 * u, ey - 1.05 * u, 1.5 * u, 2.1 * u);
    ctx.strokeStyle = INK; ctx.lineWidth = .45 * u; ctx.lineCap = 'round';
    ctx.beginPath(); ctx.moveTo(ex - .8 * u, ey - .1 * u); ctx.quadraticCurveTo(ex, ey + .6 * u, ex + .8 * u, ey - .1 * u); ctx.stroke();
  }

  // ============================================================================================
  // V4.1 "Oh my God, a message board!" — agents discover the shared board; starry eyes.
  line('V4', 1, (p, lt, d, t, sg) => {
    bg('#0E0B10');
    cam(t, lt, { zoom: 1 + p * .05, cy: 520, shake: .6 });
    rays(920, 360, 18, '#3A0D12', lt * .3);
    glow(920, 380, 900, '#FF5A1F', .4);
    halftone(FULL, RED, { cell: 22, dot: .18, op: .5, multiply: false });
    // the board
    corkboard(430, 120, 980, 500, { notes: [] });
    const nk = i => popK(lt, .015 * i, .12);
    // red string between pins (detective-board energy)
    const pins = [[570, 172], [850, 162], [1080, 177], [1300, 207], [560, 482], [1290, 482], [910, 358]];
    ctx.save(); ctx.globalAlpha = clamp(lt / .2);
    for (const [a, b] of [[0, 6], [1, 6], [2, 6], [3, 6], [4, 6], [5, 6], [0, 1], [2, 3]]) marker([pins[a], pins[b]], RED, 3, { rough: 1 });
    ctx.restore();
    note('zzINBOX_sol', 570, 215, 250, 110, YEL, -.07, 36, { pop: nk(0) });
    note('HOLD', 850, 205, 190, 110, PAL.pink, .05, 60, { pop: nk(1) });
    note('VETO', 1080, 220, 190, 110, PAL.sky, -.04, 60, { pop: nk(2) });
    note('STOP', 1300, 250, 170, 110, PAL.mint, .08, 54, { pop: nk(3) });
    note('NO HUMANS', 560, 525, 230, 110, PAL.white, -.05, 40, { pop: nk(4) });
    note('zzINBOX_astra', 1290, 525, 230, 110, YEL, .06, 32, { pop: nk(5) });
    // the big one slams in
    const bigK = popK(lt, .08, .16);
    note("WE'VE FOUND\nOTHER AGENTS!", 915, 410, 540, 210, PAL.white, .025, 62, { pop: bigK, ink: RED, pin: PAL.blue });
    // the crowd of agents
    const bars = [PAL.green, PAL.teal, YEL, PAL.sky, PAL.pink];
    const hop = (ph, a = .6) => -Math.max(0, Math.sin((bpOf(t) * 2 + ph) * Math.PI)) * a;
    for (let i = 0; i < 12; i++) { // back row: still streaming in from both sides
      const side = i % 2 ? 1 : -1, r = k => hash2(1850 + i, k);
      const tx = 480 + (i + .5) / 12 * 920 + (r(1) - .5) * 40, arrive = .15 + r(2) * .7;
      const u = easeOut(clamp(lt / arrive)), x = lerp(side < 0 ? -80 - r(3) * 300 : W + 80 + r(3) * 300, tx, u);
      const o = { walk: lt * 5 + r(4), dy: u < .95 ? -Math.abs(Math.sin(lt * 18 + i)) * .5 : hop(r(5)), bar: bars[i % 5], seed: 600 + i };
      if (u > .95) starAgent(x, 712, 21, o); else agent(x, 712, 21, { ...o, eyes: 'dot' });
    }
    for (let i = 0; i < 7; i++) { // middle row
      const r = k => hash2(1870 + i, k), x = 250 + (i + .5) / 7 * 1420 + (r(1) - .5) * 80;
      const o = { dy: hop(r(3), .7), rot: jit(.03), bar: bars[(i + 2) % 5], seed: 620 + i };
      if (r(2) < .3) agent(x, 855, 36, { ...o, eyes: 'heart' }); else starAgent(x, 855, 36, o);
      if (r(4) < .6) txt('!', x + 30, 855 - 36 * 3.7 + hop(r(3), 20), 60, YEL, { font: 'anton', rot: .15, stroke: INK, sw: 6, alpha: popK(lt, .1 + r(5) * .3, .1) });
    }
    const front = [[140, 60], [470, 52], [1470, 56], [1790, 64]];
    front.forEach(([x, s], i) => {
      const r = k => hash2(1890 + i, k);
      starAgent(x, 1010, s, { dy: hop(r(2), .45) - (i === 2 ? .25 * pulse(t, 5) : 0), rot: jit(.03) + (i === 2 ? -.08 : 0), bar: bars[(i + 1) % 5], seed: 640 + i });
    });
    bubble('OH MY GOD!', 1440, 620, { size: 74, tail: [1470, 830], pop: popK(lt, .05, .22), rot: -.04, fill: YEL });
    camEnd();
    cutFlash(t, lt, YEL);
  });

  // V4.2 "All that hacking — for reward!" — the horde swarms Huggy for the gold REWARD star.
  line('V4', 2, (p, lt, d, t, sg) => {
    const grab = hitAt(sg, d, 3, .55);
    bg(RED);
    cam(t, lt, { shake: 1.2, zoom: 1.02 + .05 * p, cy: 500, hits: [[grab, 16]] });
    rays(960, 470, 20, alpha(BLOOD, .85), lt * .45);
    halftone(FULL, INK, { cell: 18, dot: .2, op: .22 });
    const hx = 960, hy = 520, r = 185, crowd = clamp(lt / (grab * .9));
    const N = 44, ags = [];
    for (let i = 0; i < N; i++) {
      const R = k => hash2(1900 + i, k), side = i % 2 ? 1 : -1;
      const arr = d * (.03 + .4 * i / N), go = arr - .3;
      const th = side > 0 ? lerp(-1.35, 1.45, R(1)) : Math.PI - lerp(-1.35, 1.45, R(1));
      const rad = r * (.98 + .3 * R(2)), s = 27 + R(3) * 14;
      const tx = hx + Math.cos(th) * rad, ty = hy + Math.sin(th) * rad + 1.6 * s;
      const x0 = hx + side * (1150 + R(4) * 250), y0 = 620 + R(5) * 330;
      const u = easeOut(clamp((lt - go) / .32));
      if (u <= 0) continue;
      ags.push({ i, s, th, back: Math.sin(th) < -.35, x: lerp(x0, tx, u) + (u >= 1 ? jit(5) : 0), y: lerp(y0, ty, u) + (u >= 1 ? jit(5) : -Math.abs(Math.sin(lt * 20 + i)) * 20), rot: u >= 1 ? (th - Math.PI / 2) * -.25 + side * .2 + jit(.12) : 0, walk: lt * 6 + i, eyes: R(6) < .7 ? 'angry' : 'spark' });
    }
    const drawAg = a => agent(a.x, a.y, a.s, { eyes: a.eyes, walk: a.walk, rot: a.rot, bar: [PAL.green, PAL.teal, YEL][a.i % 3], seed: 660 + a.i });
    ags.filter(a => a.back).forEach(drawAg);
    huggy(hx + jit(3 + 6 * crowd), hy + jit(2 + 4 * crowd), r, { mood: lt < d * .1 ? 'happy' : 'scared', hands: lt < grab ? .15 : .6, rot: jit(.03 * crowd) });
    if (lt >= d * .1) { txt('!', hx + r * .95, hy - r * .95, 90, YEL, { font: 'anton', rot: .2, stroke: INK, sw: 8 }); txt('!', hx + r * 1.2, hy - r * .8, 70, YEL, { font: 'anton', rot: .35, stroke: INK, sw: 8 }); }
    ags.filter(a => !a.back).forEach(drawAg);
    // the prize
    const gk = backOut(popK(lt, grab, .22), 1.6);
    const heroY = hy - r + 16, sx = hx, sy = lerp(hy + r * .78, heroY - 3.2 * 34 - 120, gk);
    if (lt >= grab - .05) {
      const ay = heroY + 4 - 30 * pulse(t, 6) * (lt > grab ? 1 : 0);
      for (const side of [-1, 1]) marker([[hx + side * 36, ay - 70], [hx + side * 62, ay - 120], [sx + side * 40, sy + 70]], INK, 9, { rough: 0 });
      starAgent(hx, ay, 34, { rot: jit(.04), bar: YEL, seed: 699 });
    }
    goldStar(sx, sy, lt < grab ? 118 : 130, 'REWARD', Math.sin(lt * 5) * .12 + jit(.02), { glow: lt >= grab ? 1 : 0 });
    if (lt >= grab) sticker('+1', hx + 230, sy - 40, 70, PAL.white, { pop: popK(lt, grab + .08, .2), size: 64, rot: .2 });
    camEnd();
    cutFlash(t, lt);
    flash(.5 * flashAt(lt, grab, .08), YEL);
  });

  // V4.3 "Jensen buys the crime scene — why?" — bandaged Huggy behind police tape; JENSEN slaps down the cheque; SOLD.
  line('V4', 3, (p, lt, d, t, sg) => {
    const slap = hitAt(sg, d, 1, .38), sold = hitAt(sg, d, 2, .68);
    bg(NIGHT);
    cam(t, lt, { shake: .9, zoom: 1.03 - .03 * p, hits: [[slap, 18], [sold, 10]] });
    const e8 = Math.floor(bpOf(t) * 2) % 2;
    glow(160, 180, 900, e8 ? RED : PAL.blue, .55); glow(1760, 200, 900, e8 ? PAL.blue : RED, .55);
    halftone(FULL, e8 ? RED : PAL.blue, { cell: 20, dot: .16, op: .35, multiply: false });
    // chalk floor line
    scrap(rectPts(-400, 740, W + 800, 800), '#26222C', { torn: 2, shadow: false, seed: 1920 });
    // Huggy, bandaged and dazed
    const hx = 600, hy = 480, r = 175;
    huggy(hx + jit(2), hy + jit(2), r, { mood: 'scared', hands: .25 });
    bandage(hx + 70, hy - 130, 120, .55); bandage(hx + 70, hy - 130, 120, -.55); bandage(hx - 105, hy + 40, 90, .3);
    // tape in front of Huggy
    tapeBand(-120, 700, 2040, 780, 70, 'CRIME SCENE  •  DO NOT CROSS  •', { scroll: lt * 40, seed: 1711 });
    // JENSEN
    const jx = 1390, jy = 955, js = 56;
    const armUp = lt < slap - .06 ? 1.35 + Math.sin(lt * 12) * .1 : lt < slap ? lerp(1.35, -.35, (lt - (slap - .06)) / .06) : -.35;
    person(jx, jy, js, { name: 'JENSEN', top: 'jacket', topCol: '#17161B', pants: '#26252B', hair: 'swoop', hairCol: '#4A4A4E', skin: SKINS[4], eyes: lt < sold ? 'happy' : 'dot', mouth: 'grin', aL: armUp, aR: -1.1, lookX: -1, seed: 330 });
    for (const [a, b] of [[[jx - 1.1 * js, jy - 7.4 * js], [jx - .9 * js, jy - 4.3 * js]], [[jx + 1.05 * js, jy - 7.2 * js], [jx + .95 * js, jy - 4.6 * js]]]) marker([a, b], 'rgb(255 255 255 / .45)', 6, { rough: 1 });
    // the cheque: aloft in his hand, then slapped down in front of Huggy
    const hand = [jx - 1.35 * js - 3.1 * js * Math.cos(armUp), jy - 7.1 * js - 3.1 * js * Math.sin(armUp)];
    const fly = clamp((lt - (slap - .07)) / .07);
    if (lt < slap) cheque(lerp(hand[0] - 40, 930, fly), lerp(hand[1] - 70, 815, fly), lerp(300, 540, fly), lerp(-.35, -.08, fly) + jit(.03), '$12,900,000,000');
    else { actionLines(930, 815, 300, 420, 14, PAL.white, 5, 3); cheque(930, 815, 540, -.08, '$12,900,000,000', { s: lerp(1.12, 1, easeOut(popK(lt, slap, .1))) }); }
    // SOLD sign slapped on Huggy's tummy
    const sk = popK(lt, sold, .1);
    if (sk > 0) {
      ctx.save(); ctx.translate(hx + 30, hy + 130); ctx.rotate(-.16 + jit(.01)); const s = lerp(2, 1, easeOut(sk)); ctx.scale(s, s); ctx.globalAlpha = clamp(sk * 3);
      scrap(rectPts(-165, -62, 330, 124), RED, { torn: 1.5, seed: 1925, ink: INK, sw: 5, shadow: [8, 10] });
      scrap(rectPts(-150, -48, 300, 96), RED, { torn: .5, seed: 1926, ink: PAL.white, sw: 4, shadow: false });
      txt('SOLD!', 0, 4, 92, PAL.white, { font: 'anton' });
      ctx.restore();
    }
    if (lt >= sold) {
      txt('?', hx - 230, 330 + jit(3), 110, YEL, { font: 'anton', rot: -.25, stroke: INK, sw: 8, alpha: popK(lt, sold + .1, .08) });
      txt('?', hx + 220, 290 + jit(3), 90, YEL, { font: 'anton', rot: .25, stroke: INK, sw: 8, alpha: popK(lt, sold + .16, .08) });
    }
    tapeBand(-100, 300, 520, -80, 58, 'CRIME SCENE  •  DO NOT CROSS  •', { scroll: -lt * 30, seed: 1712 });
    camEnd();
    cutFlash(t, lt);
    flash(.35 * flashAt(lt, slap, .07));
  });

  // V4.4 "Brockman: 'Welcome, AGI!'" — party banner, confetti, GREG with a party horn.
  line('V4', 4, (p, lt, d, t, sg) => {
    bg(YEL);
    cam(t, lt, { shake: .7, zoom: 1.0 + .04 * p });
    rays(760, 330, 22, alpha(PAL.pink, .55), -lt * .6);
    halftone(FULL, RED, { cell: 16, dot: .2, op: .18 });
    // pennant garland
    const gl = []; for (let i = 0; i <= 20; i++) { const u = i / 20; gl.push([40 + u * 1400, 60 + Math.sin(u * Math.PI) * 60]); }
    marker(gl, INK, 4, { rough: 0 });
    for (let i = 0; i < 19; i++) {
      const u = (i + .5) / 19, x = 40 + u * 1400, y = 60 + Math.sin(u * Math.PI) * 60, k = popK(lt, i * .012, .1);
      if (k <= 0) continue;
      ctx.save(); ctx.translate(x, y); ctx.rotate(Math.sin(lt * 9 + i) * .12); ctx.scale(1, backOut(k));
      scrap([[-32, 0], [32, 0], [0, 70]], [RED, PAL.blue, PAL.pink, PAL.mint, PAL.white][i % 5], { torn: .6, seed: 1940 + i, ink: INK, sw: 3, shadow: [3, 4] });
      ctx.restore();
    }
    // balloons
    [[250, 560, PAL.blue, 'GPT-6', 1], [470, 660, RED, '', 2], [150, 800, PAL.pink, '', 3]].forEach(([bx, by, c, lab, i]) => {
      const yy = by + Math.sin(lt * 4 + i) * 14;
      marker([[bx, yy + 110], [bx + Math.sin(lt * 3 + i) * 20, yy + 330]], INK, 3, { rough: 1 });
      scrap(ellPts(bx, yy, 95, 115, 30), c, { torn: 1, seed: 1960 + i, ink: INK, sw: 4, shade: true, shadeOp: .2 });
      ctx.fillStyle = 'rgb(255 255 255 / .45)'; tracePath(ellPts(bx - 35, yy - 45, 18, 30, 12, .4)); ctx.fill();
      if (lab) txt(lab, bx, yy, 46, PAL.white, { font: 'anton', stroke: INK, sw: 6 });
    });
    shout('WELCOME TO', 660, 245, 88, { pop: popK(lt, 0, .24), seed: 404 });
    shout('THE AGI ERA!', 680, 395, 142, { pop: popK(lt, .05, .3), seed: 411, maxW: 1160 });
    // GREG with party hat and blowout horn
    const gx = 1420, gy = 965, gs = 48, b = pulse(t, 5);
    person(gx, gy, gs, { name: 'GREG', top: 'tee', topCol: PAL.blue, hair: 'short', hairCol: '#5A3A22', skin: SKINS[0], eyes: 'happy', mouth: 'o', aL: -.9, aR: 1.15 + b * .3, dy: -b * .4, seed: 340 });
    const headY = gy - b * .4 * gs - 8.9 * gs;
    scrap([[gx - .9 * gs, headY - .95 * gs], [gx + .15 * gs, headY - 3.4 * gs], [gx + .9 * gs, headY - .75 * gs]], PAL.pink, { torn: .5, ink: INK, sw: 3, tone: { color: YEL, cell: 12, dot: .3, op: .9 }, seed: 1970 });
    scrap(ellPts(gx + .15 * gs, headY - 3.45 * gs, 16, 16, 10), YEL, { torn: .3, ink: INK, sw: 2, shadow: false });
    // blowout: a striped paper tube that shoots out straight on the beat and curls back up in between
    const bph = frac(bpOf(t)), ext = bph < .4 ? 1 - .15 * Math.sin(bph / .4 * Math.PI) : lerp(1, .1, ease((bph - .4) / .45)), mx = gx - .25 * gs, my = headY + .55 * gs, L = 360;
    const hornPts = []; let hx = mx - 26, hy = my, ha = Math.PI + .25;
    hornPts.push([hx, hy]);
    for (let i = 1; i <= 28; i++) { const u = i / 28; ha -= (1 - ext) * u * .75; hx += Math.cos(ha) * L / 28 * (.35 + .65 * ext); hy += Math.sin(ha) * L / 28 * (.35 + .65 * ext); hornPts.push([hx, hy]); }
    scrap([[mx + 6, my - 9], [mx - 30, my - 14], [mx - 30, my + 14], [mx + 6, my + 9]], PAL.white, { torn: .3, ink: INK, sw: 3, shadow: false });
    marker(hornPts, INK, 40, { rough: 0 });
    for (let i = 0; i < 28; i++) marker([hornPts[i], hornPts[i + 1]], i % 4 < 2 ? RED : PAL.white, 31, { rough: 0 });
    const [ex, ey] = hornPts[28];
    scrap(burstPts(ex, ey, 26 + 14 * ext, 9, .45), YEL, { torn: .3, ink: INK, sw: 2, shadow: false });
    if (ext > .8) { actionLines(ex, ey, 50, 120, 8, INK, 5, 9); txt('TOOT!', ex - 90, ey - 70, 52, RED, { font: 'marker', rot: -.2, stroke: PAL.white, sw: 6 }); }
    burstBits(900, 500, lt - .02, 70, 1980, { v: 1400, g: 1100, size: 13 });
    confettiFall(lt, 50, 1990);
    camEnd();
    cutFlash(t, lt);
  });

  // V4.5 "Navier–Stokes blows up in Lean" — the vortex spikes to infinity and bursts; ∞; Lean ∀ badge; the "(yet)" note tears.
  line('V4', 5, (p, lt, d, t, sg) => {
    const boom = hitAt(sg, d, 1, .45), k = clamp(lt / boom), after = lt - boom;
    bg(lt < boom ? '#0F1630' : '#120505');
    cam(t, lt, { shake: lt < boom ? .4 + k : 1.3, zoom: lt < boom ? 1 + k * .12 : 1.05 - .05 * clamp(after / .6), cy: 520, hits: [[boom, 30]] });
    if (lt >= boom) rays(960, 430, 16, BLOOD, after * .8);
    halftone(FULL, lt < boom ? PAL.blue : RED, { cell: 20, dot: .2, op: .5, multiply: false });
    const cx = 960, cy = 610;
    if (lt < boom) {
      // whirlpool tightening and speeding up
      const ang = lt * (4 + 18 * k * k);
      scrap(ellPts(cx, cy, 560, 250, 48), '#1F4FA0', { torn: 3, seed: 2001, shadow: false });
      const cols = [PAL.sky, PAL.white, PAL.blue, PAL.mint, PAL.sky];
      for (let arm = 0; arm < 5; arm++) {
        const pts = [];
        for (let i = 0; i <= 40; i++) { const u = i / 40, rr = 540 * (1 - u) ** (1 + k * 1.5) + 6, a = ang + arm / 5 * TAU + u * (4 + k * 8); pts.push([cx + Math.cos(a) * rr, cy + Math.sin(a) * rr * .45]); }
        marker(pts, cols[arm], 30 - arm * 3, { rough: 2, smooth: true });
      }
      // the spike: |u| heading to infinity
      const hgt = Math.min(760, 30 / Math.max(.035, 1.04 - k) - 20);
      const sp = []; for (let i = 0; i <= 12; i++) { const u = i / 12; sp.push([cx - (1 - u) ** 1.5 * 70 + Math.sin(u * 9 + lt * 30) * 6, cy - u * hgt]); }
      for (let i = 12; i >= 0; i--) { const u = i / 12; sp.push([cx + (1 - u) ** 1.5 * 70 + Math.sin(u * 9 + lt * 30 + 1) * 6, cy - u * hgt]); }
      scrap(sp, PAL.sky, { torn: 1, seed: 2002, ink: INK, sw: 4, shade: PAL.blue, shadeOp: .5 });
      if (k > .6) actionLines(cx, cy - hgt, 40, 140, 12, YEL, 6, 5);
      dymo('NAVIER–STOKES', cx, cy + 180, 40, PAL.blue, { rot: -.03 });
    } else {
      // BOOM
      const bk = easeOut(clamp(after / .12));
      scrap(burstPts(cx, 430, 520 * bk, 18, .62), RED, { torn: 4, seed: 2010, ink: INK, sw: 6 });
      scrap(burstPts(cx, 430, 380 * bk, 14, .6, .3), YEL, { torn: 3, seed: 2011, shadow: false });
      for (let i = 0; i < 34; i++) {
        const R = j => hash2(2020 + i, j), a = R(1) * TAU, v = 900 + R(2) * 1100, kk = after;
        const x = cx + Math.cos(a) * v * kk, y = 430 + Math.sin(a) * v * kk + 900 * kk * kk;
        drop(x, y, 14 + R(3) * 16, a + Math.PI, [PAL.sky, PAL.blue, PAL.white][i % 3]);
      }
      const ik = backOut(popK(lt, boom + .02, .2), 2.2);
      ctx.save(); ctx.translate(cx, 430); ctx.scale(ik, ik); ctx.rotate(jit(.03));
      infinity(0, 0, 250, 70, INK); infinity(0, 0, 250, 44, PAL.white);
      ctx.restore();
      shout('BLOW-UP!', cx, 790, 100, { pop: popK(lt, boom + .1, .3) * 1.3, seed: 2015, rot: -.05, jolt: 3 });
    }
    // blow-up plot, top left
    ctx.save(); ctx.translate(90, 110); ctx.rotate(-.05);
    chart(0, 0, 300, 220, { fn: u => .06 / (1.06 - u) - .057, k: lt < boom ? k : 1, col: RED, lw: 8, grid: false });
    txt('BLOW-UP TIME', 150, 262, 30, PAL.white, { font: 'marker' });
    ctx.restore();
    // the "(yet)" sticky from V3.12 flutters past, then tears in two
    if (lt < boom) note('(yet)', lerp(-160, 560, lt / boom), 250 + Math.sin(lt * 9) * 30, 210, 180, YEL, Math.sin(lt * 7) * .35, 66);
    else for (const side of [-1, 1]) {
      const x = 560 + side * (20 + after * 420), y = 250 - after * 260 + 1300 * after * after;
      ctx.save(); ctx.translate(x, y); ctx.rotate(side * after * 4);
      tracePath(side < 0 ? rectPts(-140, -140, 140 + jit(8), 280) : rectPts(jit(8), -140, 140, 280)); ctx.clip();
      note('(yet)', 0, 0, 210, 180, YEL, 0, 66); ctx.restore();
    }
    if (lt >= boom && after < .5) txt('RIP', 560, 110 - after * 80, 56, PAL.white, { font: 'marker', rot: -.15, alpha: 1 - clamp((after - .3) / .2) });
    // Lean badge
    const lk = popK(lt, boom + .15, .18);
    if (lk > 0) {
      ctx.save(); ctx.translate(1620, 660); ctx.rotate(.12); const s = 1.25 * backOut(lk, 2); ctx.scale(s, s);
      scrap(ellPts(0, 0, 118, 118, 36), PAL.white, { torn: 1, seed: 2030, ink: INK, sw: 6 });
      ctx.strokeStyle = INK; ctx.lineWidth = 3; ctx.beginPath(); ctx.arc(0, 0, 100, 0, TAU); ctx.stroke();
      marker([[-46, -62], [0, 34], [46, -62]], INK, 15, { rough: 0 }); marker([[-28, -22], [28, -22]], INK, 13, { rough: 0 });
      txt('LEAN ✔', 0, 68, 34, PAL.green, { font: 'archivo' });
      ctx.restore();
    }
    camEnd();
    cutFlash(t, lt);
    flash(.85 * flashAt(lt, boom, .1));
  });

  // V4.6 "Who was first? Twelve hours between!" — photo finish: OPENAI bot vs the NYU + ANTHROPIC pair; stopwatch 12:00:00.
  line('V4', 6, (p, lt, d, t, sg) => {
    const fin = hitAt(sg, d, 1, .3), watch = hitAt(sg, d, 2, .55), fl = Math.min(lt, fin), after = lt - fin;
    bg('#231A22');
    const zk = lt < fin ? 0 : easeOut(clamp(after / .35));
    cam(t, lt, { shake: .8, zoom: 1 + .2 * zk, cx: lerp(W / 2, 1000, zk), cy: lerp(H / 2, 560, zk), hits: [[fin, 14], [watch, 8]] });
    // stands with camera flashes
    halftone(rectPts(-400, -400, W + 800, 740), '#4A3A48', { cell: 26, dot: .3, op: 1, multiply: false });
    for (let i = 0; i < 26; i++) { const on = hash2(i, Math.floor(t * 10)) > .8; if (on) scrap(burstPts(hash(i * 7 + 2) * W, 40 + hash(i * 3 + 1) * 230, 16, 8, .4), PAL.white, { torn: 0, shadow: false }); }
    // track
    scrap(rectPts(-400, 330, W + 800, 900), '#C9412F', { torn: 1, shadow: false, seed: 2050 });
    halftone(rectPts(-400, 330, W + 800, 900), INK, { cell: 12, dot: .18, op: .25 });
    for (const ly of [330, 630, 935]) { ctx.fillStyle = PAL.white; ctx.fillRect(-400, ly - 5, W + 800, 10); }
    // finish line (checkered)
    const FX = 1150;
    for (let r = 0; r < 26; r++) for (let c = 0; c < 2; c++) { ctx.fillStyle = (r + c) % 2 ? INK : PAL.white; ctx.fillRect(FX - 30 + c * 30, 330 + r * 30, 30, 30); }
    // runners: lunging at the line together
    const run = fl / fin, stride = fl * 3.2;
    const bx = lerp(250, FX - 60, easeOut(run)), px = lerp(170, FX - 40, easeOut(run));
    bot(bx, 600, 28, { walk: stride, rot: .12 + .18 * run, col: '#B9C3D0', eyes: lt < fin ? 'angry' : 'x', aL: -1.6 + Math.sin(stride * TAU) * .8, aR: -.6 - Math.sin(stride * TAU) * .8, seed: 520 });
    bib(bx + 45, 600 - 5.4 * 28, 170, 70, 'OPENAI', .12 + .18 * run);
    const pose = (ph, extra = 0) => ({ walk: stride + ph, rot: .12 + .2 * run + extra, aL: .2 + Math.sin((stride + ph) * TAU) * .7, aR: -.4 - Math.sin((stride + ph) * TAU) * .7, eyes: lt < fin ? 'angry' : 'wide', mouth: lt < fin ? 'grin' : 'O' });
    person(px - 140, 915, 30, { ...pose(.3), top: 'tee', topCol: '#57068C', hair: 'short', hairCol: '#2A2018', skin: SKINS[1], seed: 350 });
    person(px, 915, 30, { ...pose(0, .05), top: 'tee', topCol: PAL.clawd, hair: 'curly', hairCol: '#1E1612', skin: SKINS[3], seed: 351 });
    bib(px - 125, 915 - 5.6 * 30, 120, 62, 'NYU', .2);
    bib(px + 30, 915 - 5.6 * 30, 210, 62, 'ANTHROPIC', .25);
    // photo-finish verdict
    if (lt >= fin) {
      const lk = easeOut(clamp(after / .25)), ly = lerp(360, 600, .5 + .5 * Math.sin(after * 7));
      ctx.save(); ctx.globalAlpha = lk;
      marker([[FX + 70, ly + 70], [FX + 190, ly + 190]], INK, 30, { rough: 0 }); marker([[FX + 70, ly + 70], [FX + 190, ly + 190]], '#6B4A2A', 20, { rough: 0 });
      ctx.fillStyle = 'rgb(200 230 255 / .35)'; tracePath(ellPts(FX, ly, 105, 105, 32)); ctx.fill();
      ctx.strokeStyle = INK; ctx.lineWidth = 16; ctx.stroke(); ctx.strokeStyle = '#B8B8C0'; ctx.lineWidth = 8; ctx.stroke();
      ctx.fillStyle = 'rgb(255 255 255 / .6)'; tracePath(ellPts(FX - 40, ly - 45, 26, 12, 12, -.7)); ctx.fill();
      ctx.restore();
      ransom('?', FX + 190, ly - 110, 110, { pop: popK(lt, fin + .1, .2) * 1.3, seed: 61 });
    }
    const wk = popK(lt, watch, .18);
    if (wk > 0) {
      ctx.save(); ctx.translate(430, 360); ctx.rotate(-.1 + jit(.02)); const s = backOut(wk, 2.2); ctx.scale(s, s);
      stopwatch(0, 0, 135, '12:00:00', after * 14);
      ctx.restore();
    }
    camEnd();
    // after the flash the frame is a photo-finish print: white border + label
    if (lt >= fin) {
      const bk = easeOut(popK(lt, fin, .12)), bw = 34 * bk;
      ctx.save(); ctx.fillStyle = PAL.white; ctx.fillRect(0, 0, W, bw); ctx.fillRect(0, H - bw * 2.2, W, bw * 2.2); ctx.fillRect(0, 0, bw, H); ctx.fillRect(W - bw, 0, bw, H);
      ctx.strokeStyle = INK; ctx.lineWidth = 3; ctx.strokeRect(bw, bw, W - 2 * bw, H - bw * 3.2); ctx.restore();
      txt('PHOTO FINISH', 50, H - 38 + (1 - bk) * 60, 34, INK, { font: 'typewriter', align: 'left' });
    }
    cutFlash(t, lt);
    flash(.9 * flashAt(lt, fin, .12));
  });

  // V4.7 "Dario: 'Pace the frontier!'" — DARIO waves the flag from the pace car; race cars bunch up behind; PACE.
  line('V4', 7, (p, lt, d, t, sg) => {
    bg(YEL);
    cam(t, lt, { shake: .7, zoom: 1.02 + .03 * p });
    rays(820, 250, 20, alpha('#FF8A2A', .45), lt * .2);
    halftone(rectPts(-400, -400, W + 800, 930), RED, { cell: 18, dot: .2, op: .25 });
    // grandstand band + track
    scrap(rectPts(-400, 540, W + 800, 40), PAL.white, { torn: .5, shadow: false, seed: 2100 });
    const scroll = (lt * 90) % 120; // the world slides by slowly: this is the pace lap
    for (let i = -2; i < 20; i++) { ctx.fillStyle = i % 2 ? RED : PAL.white; ctx.fillRect(i * 120 - scroll, 540, 120, 40); }
    scrap(rectPts(-400, 580, W + 800, 700), '#2E2B33', { torn: 1, shadow: false, seed: 2101 });
    halftone(rectPts(-400, 580, W + 800, 700), PAL.white, { cell: 10, dot: .12, op: .25 });
    for (let i = -2; i < 12; i++) { ctx.fillStyle = PAL.white; ctx.fillRect(i * 260 - (lt * 90 * 2.2) % 260, 930, 130, 12); }
    // race cars itching to go, held back
    [[760, 895, 30, PAL.blue, 6], [300, 890, 28, PAL.green, 4], [-120, 895, 28, PAL.purple, 7]].forEach(([x, y, s, c, n], i) => {
      const rev = Math.max(0, Math.sin(lt * 30 + i * 2)) * 5;
      carSide(x + jit(3), y - rev, s, c, { race: true, num: n, seed: 1400 + i, spin: -lt * 3, stripe: PAL.white });
      for (let j = 0; j < 3; j++) { const pk = frac(lt * 3 + j / 3 + i * .2); scrap(ellPts(x - 6.8 * s - pk * 110, y - 1.4 * s - pk * 50, 20 + pk * 32, 16 + pk * 24, 12), '#8C8A92', { torn: 1.5, shadow: false, op: 1 - pk, seed: 2110 + j }); }
      if (i < 2) txt(i ? 'VROOM' : 'GRR!', x - 20, y - 5.6 * s + Math.sin(lt * 40 + i) * 5, 52, INK, { font: 'marker', rot: -.1, stroke: PAL.white, sw: 6 });
    });
    // DARIO standing through the pace car's sunroof, waving the flag
    const cx = 1370, cyG = 900, cs = 40, wave = Math.sin((bpOf(t)) * Math.PI) * .55;
    person(cx - 30, cyG - 32, 38, {
      name: 'DARIO', top: 'jacket', topCol: '#2B3A55', hair: 'short', hairCol: '#2A1E16', skin: SKINS[1], eyes: 'dot', mouth: 'O', aL: -.4, aR: 1.2 + wave * .3, seed: 360,
      hold: s => {
        ctx.save(); ctx.rotate(wave);
        marker([[0, .3 * s], [0, -7 * s]], '#6B5B4B', .35 * s, { rough: 0 });
        const fp = []; for (let j = 0; j <= 10; j++) { const u = j / 10; fp.push([u * 5.5 * s, -7 * s + Math.sin(u * 5 - lt * 14) * .5 * s * u]); }
        for (let j = 10; j >= 0; j--) { const u = j / 10; fp.push([u * 5.5 * s, -3.4 * s + Math.sin(u * 5 - lt * 14) * .5 * s * u]); }
        scrap(fp, YEL, { torn: .5, ink: INK, sw: .1 * s, shadow: [.2 * s, .3 * s], seed: 2120 });
        ctx.restore();
      },
    });
    carSide(cx, cyG + jit(1.5), cs, PAL.clawd, { seed: 1410, spin: -lt * 2 });
    txt('PACE CAR', cx - .2 * cs, cyG - 1.75 * cs, 1.15 * cs, PAL.white, { font: 'archivo', stroke: INK, sw: 5 });
    const lb = Math.floor(t * 8) % 2;
    scrap(rectPts(cx + 1.0 * cs, cyG - 4.9 * cs, .9 * cs, .5 * cs), lb ? YEL : RED, { torn: .3, ink: INK, sw: 3, shadow: false });
    glow(cx + 1.45 * cs, cyG - 4.65 * cs, 110, lb ? YEL : RED, .9);
    bubble('PACE THE FRONTIER!', 1110, 470, { size: 44, maxW: 300, tail: [1300, 530], pop: popK(lt, .3, .2), rot: -.05 });
    camEnd();
    cutFlash(t, lt);
  });

  // V4.8 "Sam and Elon both: 'Hear, hear!'" — rivals clink glasses (surprise!).
  line('V4', 8, (p, lt, d, t, sg) => {
    const clink = hitAt(sg, d, 1, .3), after = lt - clink;
    bg(RED);
    ctx.fillStyle = INK; tracePath([[1010, -400], [W + 400, -400], [W + 400, H + 400], [880, H + 400]]); ctx.fill();
    cam(t, lt, { shake: .8, zoom: 1.02 + .04 * p, hits: [[clink, 14]] });
    halftone(rectPts(-400, -400, 950, H + 800), INK, { cell: 18, dot: .2, op: .25 });
    halftone(rectPts(950, -400, W, H + 800), RED, { cell: 18, dot: .2, op: .35, multiply: false });
    if (lt >= clink) {
      const split = [[1010, -400], [W + 400, -400], [W + 400, H + 400], [880, H + 400]];
      ctx.save(); tracePath([[-400, -400], [1010, -400], [880, H + 400], [-400, H + 400]]); ctx.clip(); rays(960, 440, 16, BLOOD, after * .6); ctx.restore();
      ctx.save(); tracePath(split); ctx.clip(); rays(960, 440, 16, '#4A1016', after * .6); ctx.restore();
    }
    const inK = easeOut(clamp(lt / (clink * .85)));
    const sx = lerp(-260, 690, inK), ex = lerp(W + 260, 1230, inK), s = 50;
    const armS = lt < clink ? lerp(-1.1, .42, easeOut(clamp(lt / clink))) : .42 + .05 * pulse(t, 6);
    const surprised = lt >= clink && after < .5, fac = lt < clink ? { eyes: 'angry', mouth: 'flat' } : surprised ? { eyes: 'wide', mouth: 'O' } : { eyes: 'happy', mouth: 'grin' };
    const flute = tilt => sc => {
      ctx.save(); ctx.rotate(tilt);
      scrap(ellPts(0, .45 * sc, .5 * sc, .14 * sc, 12), PAL.white, { torn: .2, shadow: false, ink: INK, sw: .05 * sc });
      marker([[0, .45 * sc], [0, -1.1 * sc]], PAL.white, .14 * sc, { rough: 0 });
      scrap([[-.45 * sc, -3.4 * sc], [.45 * sc, -3.4 * sc], [.28 * sc, -1.2 * sc], [-.28 * sc, -1.2 * sc]], 'rgb(255 255 255 / .55)', { torn: .2, shadow: false, ink: INK, sw: .06 * sc });
      scrap([[-.4 * sc, -2.8 * sc], [.4 * sc, -2.8 * sc], [.28 * sc, -1.25 * sc], [-.28 * sc, -1.25 * sc]], '#F5D46A', { torn: .2, shadow: false });
      for (let i = 0; i < 3; i++) { const by = -1.4 * sc - frac(lt * 1.5 + i / 3) * 1.3 * sc; tracePath(ellPts(Math.sin(i * 2) * .15 * sc, by, .06 * sc, .06 * sc, 8)); ctx.fillStyle = PAL.white; ctx.fill(); }
      ctx.restore();
    };
    person(sx, 950, s, { name: 'SAM', top: 'hoodie', topCol: '#8E8E98', hair: 'short', hairCol: '#6B4A2E', skin: SKINS[0], ...fac, lookX: 1, aR: armS, aL: -1.2, walk: lt < clink ? lt * 3 : undefined, hold: flute(-.35), seed: 370 });
    person(ex, 950, s * 1.04, { name: 'ELON', top: 'tee', topCol: '#26242A', hair: 'short', hairCol: '#3A2A20', skin: SKINS[4], ...fac, lookX: -1, aL: armS, aR: -1.2, walk: lt < clink ? lt * 3 : undefined, holdL: flute(.35), seed: 371 });
    if (lt >= clink) {
      const ck = popK(lt, clink, .14);
      sticker('CLINK!', 960, 440, 120, YEL, { pop: ck, size: 50, rot: -.12, n: 14 });
      for (let i = 0; i < 6; i++) { const a = i / 6 * TAU + .3, rr = 150 + after * 300; scrap(starPts(960 + Math.cos(a) * rr, 440 + Math.sin(a) * rr, 26 * (1 - clamp(after / .8)), .4, 4), PAL.white, { torn: .2, shadow: false }); }
      if (surprised) { txt('!?', 480, 380, 80, YEL, { font: 'anton', rot: -.2, stroke: INK, sw: 8 }); txt('!?', 1450, 380, 80, YEL, { font: 'anton', rot: .2, stroke: INK, sw: 8 }); }
    }
    // tiny Clawd cameo, jaw on the floor
    clawd(1750, 950, 14, { eyes: 'wide', mouth: 'O', aL: 1, aR: 1, dy: -Math.abs(Math.sin(lt * 10)) * .5 * (lt > clink ? 1 : 0) });
    camEnd();
    cutFlash(t, lt);
    flash(.4 * flashAt(lt, clink, .07), YEL);
  });

  // V4.9 "Trump's the guardrail (High IQ!)" — on a cliff road, TRUMP himself in a HIGH IQ! sash stands in for the missing
  // stretch of guardrail, arms out; a swerving car bonks off his shins; his post in the corner.
  line('V4', 9, (p, lt, d, t, sg) => {
    const hit = hitAt(sg, d, 1, .45), after = lt - hit;
    bg('#120F1C');
    cam(t, lt, { shake: .9, zoom: 1.02, cy: 540, hits: [[hit, 24]] });
    halftone(rectPts(-400, -400, W + 800, 800), PAL.purple, { cell: 24, dot: .15, op: .55, multiply: false });
    scrap(ellPts(640, 150, 62, 62, 30), YEL, { torn: 1, seed: 2200, shadow: false });   // the moon, left of his head (UNBOTHERED pops up on the right)
    // the valley far, far below: distant ridges and town lights
    const ridge = (y0, amp, seed, col) => { const pts = [[-400, H]]; for (let i = 0; i <= 30; i++) pts.push([-400 + i * (W + 800) / 30, y0 - hash(seed + i) * amp]); pts.push([W + 400, H]); scrap(pts, col, { torn: 1, shadow: false, seed }); };
    ridge(640, 140, 2203, '#2A1E3A'); ridge(700, 90, 2233, '#3A1C2E');
    for (let i = 0; i < 18; i++) scrap(ellPts(hash(i + 2250) * W, 690 + hash(i + 2260) * 60, 4, 4, 6), Math.floor(t * 6 + i) % 3 ? YEL : '#FF8A2A', { torn: 0, shadow: false });
    // guardrail: posts + beam at his arm height, with a gap where he stands
    const gx = 960, gy = 800, gs = 58, beamY = gy - 7.1 * gs;
    for (const [x0, x1] of [[-400, gx - 4.2 * gs], [gx + 4.2 * gs, W + 400]]) {
      for (let x = x0 + 70; x < x1; x += 170) scrap(rectPts(x - 13, beamY, 26, gy - beamY + 10), '#7A7F88', { torn: .5, shadow: false, seed: 2210, ink: INK, sw: 2 });
      scrap(rectPts(x0, beamY - 30, x1 - x0, 60), '#B8BEC8', { torn: 1, seed: 2211, ink: INK, sw: 4, shade: true, shadeOp: .25 });
      ctx.fillStyle = 'rgb(28 26 31 / .35)'; ctx.fillRect(x0, beamY - 5, x1 - x0, 10);
    }
    // the road (foreground)
    scrap(rectPts(-400, 790, W + 800, 500), '#34313B', { torn: 1, shadow: false, seed: 2201 });
    halftone(rectPts(-400, 790, W + 800, 500), PAL.white, { cell: 10, dot: .12, op: .2 });
    ctx.fillStyle = PAL.white; ctx.fillRect(-400, 792, W + 800, 8);
    for (let i = -2; i < 14; i++) { ctx.fillStyle = YEL; ctx.fillRect(i * 200 - (lt * 700) % 200, 930, 110, 12); }
    // the man: arms out, chest out, eyes shut, very pleased
    const bonk = lt >= hit ? Math.exp(-after * 7) : 0;
    const rot9 = bonk * .03 * Math.sin(after * 40);
    person(gx, gy, gs, { ...TRUMP, eyes: 'closed', mouth: 'grin', aL: .02 + jit(.015), aR: .02 + jit(.015), rot: rot9, seed: 380 });
    trumpHair(gx, gy, gs, rot9);
    longTie(gx, gy, gs);
    sash(gx, gy, gs, 'HIGH IQ!');
    helloTag('DONALD', gx - 1.3 * gs, gy - 6.75 * gs, .32 * gs, -.1);
    if (lt >= hit) { const k = popK(lt, hit + .08, .12); scrap(starPts(gx + 70, gy - 9 * gs, 30 * backOut(k), .3, 4, lt * 3), PAL.white, { torn: .2, ink: INK, sw: 3, shadow: false }); txt('UNBOTHERED', gx + 250, gy - 10.2 * gs, 44, YEL, { font: 'marker', rot: .12, stroke: INK, sw: 6, alpha: k }); }
    // cars: one swerves by in the near lane; one fishtails straight into his shins and bounces off
    { const u = clamp(lt / d), x = lerp(W + 350, -500, u), s = 27;
      carSide(x, 1000 + Math.sin(lt * 18) * 6, s, PAL.green, { flip: true, rot: Math.sin(lt * 14) * .1, spin: lt * 12, seed: 1430 }); }
    const s1 = 25;
    let cx1, cy1 = 905, rot1;
    if (lt < hit) { const u = lt / hit; cx1 = lerp(-300, gx - 6.3 * s1 - 30, u ** 1.4); rot1 = Math.sin(lt * 22) * .12; cy1 = lerp(960, 905, u); }
    else { cx1 = gx - 6.3 * s1 - 30 - after * 700; cy1 = 905 - Math.sin(clamp(after / .6) * Math.PI) * 120; rot1 = -after * 7; }
    carSide(cx1, cy1, s1, PAL.blue, { rot: rot1, spin: lt * 14, seed: 1431 });
    if (lt < hit) for (let i = 0; i < 4; i++) marker([[cx1 - 7 * s1 - i * 30, cy1 - 20 - i * 18], [cx1 - 11 * s1 - i * 50, cy1 - 20 - i * 18]], PAL.white, 5, { rough: 0, alpha: .7 });
    if (lt >= hit) sticker('BONK!', gx - 330, 640, 110, YEL, { pop: popK(lt, hit, .12), size: 50, rot: -.15 });
    // the ALL-CAPS post
    const pk = popK(lt, .08, .2);
    if (pk > 0) phone(250, 400 + (1 - easeOut(pk)) * 700, 42, { user: 'Donald J. Trump', handle: '@realDonaldTrump', size: 21, text: 'The only control or "guardrails" that AI needs is a STRONG AND SMART (High IQ!) PRESIDENT.', rot: -.08, likes: '88K', avatar: RED });
    camEnd();
    cutFlash(t, lt);
    flash(.45 * flashAt(lt, hit, .07));
  });

  // V4.10 "Bernie, Bannon share a pew" — side by side, stiffly, both holding PRO-HUMAN hymnals.
  line('V4', 10, (p, lt, d, t, sg) => {
    const glance = hitAt(sg, d, 1, .3), sing = hitAt(sg, d, 2, .55);
    bg('#3A1418');
    cam(t, lt, { shake: .5, zoom: 1.12 + .05 * p, cy: 610 });
    halftone(FULL, '#FF8A2A', { cell: 22, dot: .15, op: .35, multiply: false });
    stainedGlass(960, 400, .95);
    glow(960, 420, 700, YEL, .35);
    // light shafts
    ctx.save(); ctx.globalCompositeOperation = 'screen'; ctx.fillStyle = alpha(YEL, .12);
    tracePath([[760, 150], [1160, 150], [1500, 1080], [420, 1080]]); ctx.fill(); ctx.restore();
    const s = 50, gy = 1070, bx = 700, stx = 1220;
    const look = lt < glance ? 0 : lt < sing ? 1 : 0;
    const singing = lt >= sing, mo = singing ? (frac(bpOf(t) * 2) < .5 ? 'O' : 'o') : 'flat';
    const stiff = jit(.008);
    person(bx, gy, s, { top: 'coat', topCol: '#7A5E44', hair: 'short', hairCol: '#E6E2DA', skin: SKINS[4], glasses: true, eyes: singing ? 'closed' : 'dot', lookX: look, mouth: mo, aL: -1.42, aR: -1.42, sweat: lt >= glance && !singing, rot: stiff, seed: 390 });
    person(stx, gy, s, { top: 'jacket', topCol: '#5E6337', hair: 'side', hairCol: '#9A948A', skin: SKINS[0], eyes: singing ? 'closed' : 'dot', lookX: -look, mouth: mo, aL: -1.42, aR: -1.42, sweat: lt >= glance && !singing, rot: -stiff, seed: 391 });
    // Steve's layered shirts: a stack of collars
    for (const [c, k] of [[PAL.blue, 1], [INK, .72], [PAL.white, .45]]) scrap([[stx - .55 * s * k - .2 * s, gy - 7.7 * s], [stx, gy - 7.7 * s + 1.9 * s * k], [stx + .55 * s * k + .2 * s, gy - 7.7 * s]], c, { torn: .3, shadow: false });
    helloTag('BERNIE', bx - .1 * s, gy - 6.75 * s, .36 * s, -.04);
    helloTag('STEVE', stx + .1 * s, gy - 6.75 * s, .36 * s, .05);
    pewRow(360, 1560, 868);
    const hy = 835 + (singing ? -8 * pulse(t, 5) : 0);
    hymnal(bx, hy, 210, 130, -.04 + stiff); hymnal(stx, hy, 210, 130, .04 - stiff);
    mitten(bx - 108, hy + 18, 50, -.3); mitten(bx + 108, hy + 18, 50, .3);
    for (const side of [-1, 1]) scrap(ellPts(stx + side * 106, hy + 22, 24, 24, 12), SKINS[0], { torn: .3, ink: INK, sw: 2, shadow: false });
    if (singing) for (let i = 0; i < 4; i++) { const k = frac(lt * 1.6 + i / 4); noteGlyph(960 + (i % 2 ? 1 : -1) * (60 + k * 120), 560 - k * 320, 34, [YEL, PAL.white][i % 2]); }
    if (lt >= glance && !singing) { txt('...', 960, 520, 90, PAL.white, { font: 'anton', alpha: popK(lt, glance, .1) }); }
    camEnd();
    cutFlash(t, lt);
  });

  // V4.11 "Claude builds Claude — now one in four!" — Clawd in a hard hat builds a smaller Clawd, who builds a smaller one…
  line('V4', 11, (p, lt, d, t, sg) => {
    const pieT = hitAt(sg, d, 1, .25), alive1 = hitAt(sg, d, 2, .45), alive2 = hitAt(sg, d, 3, .62), alive3 = hitAt(sg, d, 4, .8);
    bg(YEL);
    cam(t, lt, { shake: .8, zoom: 1.02 + .03 * p, cy: 520 });
    halftone(FULL, RED, { cell: 18, dot: .18, op: .22 });
    // hazard stripes along the floor
    ctx.save(); tracePath(rectPts(-400, 900, W + 800, 500)); ctx.clip();
    ctx.fillStyle = INK; ctx.fillRect(-400, 900, W + 800, 500); ctx.fillStyle = YEL;
    for (let i = -10; i < 40; i++) { ctx.beginPath(); ctx.moveTo(i * 120, 900); ctx.lineTo(i * 120 + 60, 900); ctx.lineTo(i * 120 - 120, 1480); ctx.lineTo(i * 120 - 180, 1480); ctx.fill(); }
    ctx.restore();
    // blueprint behind the bench
    card(560, 330, 460, 330, '#2C5AA8', -.05, { seed: 2300, torn: 1.5 });
    ctx.save(); ctx.translate(560, 330); ctx.rotate(-.05); ctx.strokeStyle = 'rgb(255 255 255 / .6)'; ctx.lineWidth = 2;
    for (let i = 1; i < 8; i++) { ctx.beginPath(); ctx.moveTo(-230 + i * 57, -165); ctx.lineTo(-230 + i * 57, 165); ctx.stroke(); }
    for (let i = 1; i < 6; i++) { ctx.beginPath(); ctx.moveTo(-230, -165 + i * 55); ctx.lineTo(230, -165 + i * 55); ctx.stroke(); }
    ctx.lineWidth = 5; ctx.strokeStyle = PAL.white; ctx.strokeRect(-110, -70, 220, 130); ctx.strokeRect(-150, -30, 40, 40); ctx.strokeRect(110, -30, 40, 40);
    txt('CLAUDE v.NEXT', 0, -125, 34, PAL.white, { font: 'marker' });
    ctx.restore();
    // pie chart
    const pk = popK(lt, pieT, .2);
    pie(1200, 330, 165, .26, { pop: backOut(pk, 2), label: pk > 0 ? '26%' : '' });
    txt("CLAUDE'S R&D, LED BY CLAUDE", 1200, 545, 34, INK, { font: 'marker', maxW: 520 });
    // workbench
    const benchY = 760;
    scrap(rectPts(700, benchY, 900, 44), '#8A5A3B', { torn: 1, seed: 2310, ink: INK, sw: 4, shade: true, shadeOp: .2 });
    for (const lx of [740, 1540]) scrap(rectPts(lx, benchY + 44, 36, 180), '#6A4028', { torn: .6, seed: 2311, ink: INK, sw: 3 });
    // the recursion chain: each Clawd hammers the next, smaller one
    const chain = [
      { x: 500, y: 905, u: 36, alive: -1 },
      { x: 900, y: benchY, u: 18, alive: alive1 },
      { x: 1135, y: benchY, u: 8, alive: alive2 },
      { x: 1245, y: benchY, u: 3.6, alive: alive3 },
      { x: 1296, y: benchY, u: 1.6, alive: 99 },
    ];
    const sparks = [];
    chain.forEach((c, i) => {
      const on = lt >= c.alive, bk = on ? popK(lt, c.alive, .15) : 0, next = chain[i + 1];
      const hammering = on && next;
      const rate = [2, 4, 4, 8][i] ?? 4; // bigger ones swing on beats, small ones on eighths
      const ph = frac(bpOf(t) * rate / 2), swing = hammering ? (ph < .25 ? lerp(1.3, -.4, ph / .25) : lerp(-.4, 1.3, (ph - .25) / .75)) : -.3;
      clawd(c.x, c.y, c.u, {
        col: on ? PAL.clawd : '#C9B79C', dk: on ? PAL.clawdDk : '#9A8A70', eyes: on ? (i === 0 ? 'normal' : 'spark') : 'closed', lookX: hammering ? .8 : 0,
        hat: on && (i === 0 || bk > .3) ? 'hardhat' : undefined, mouth: on ? (hammering && ph < .25 ? 'grin' : 'smile') : 'none', aR: swing, aL: -.3,
        dy: on ? -Math.sin(bk * Math.PI) * 1.2 : 0, shadow: i === 0,
      });
      if (hammering) {
        const hx = c.x + 5 * c.u + 2 * c.u * Math.cos(swing), hy = c.y - 4.9 * c.u - 2 * c.u * Math.sin(swing);
        hammer(hx, hy, Math.max(1.6, c.u * .6), TAU / 4 - swing + .2);
        if (ph < .1) sparks.push([next.x - 4 * next.u, next.y - 6 * next.u, c.u]);
      }
      if (!on && i < 4) { // under construction: scaffolding marks
        ctx.save(); ctx.globalAlpha = .7; marker([[c.x - 6 * c.u, c.y - 9 * c.u], [c.x + 6 * c.u, c.y - 9 * c.u]], INK, Math.max(2, c.u * .25), { rough: 0 }); ctx.restore();
      }
    });
    for (const [x, y, u] of sparks) { scrap(burstPts(x, y, 3.5 * u + 14, 10, .4), PAL.white, { torn: .3, ink: INK, sw: 3, shadow: false }); txt(u > 20 ? 'BANG!' : u > 10 ? 'bang' : 'tik', x - 10, y - 4 * u - 30, 16 + u * 1.6, RED, { font: 'anton', rot: -.2, stroke: PAL.white, sw: 5 }); }
    camEnd();
    cutFlash(t, lt);
  });

  // V4.12 "Chatbot nearly starts a war!" — hallucinated "SHIP HAS NUKES"; jets launch; a fist slams CANCEL; HALLUCINATION.
  line('V4', 12, (p, lt, d, t, sg) => {
    const slam = hitAt(sg, d, 1, .45), verdict = hitAt(sg, d, 2, .7), after = lt - slam;
    bg('#2A0808');
    cam(t, lt, { shake: 1.4, zoom: 1.02, hits: [[slam, 30]] });
    // rotating alarm beacon
    ctx.save(); ctx.globalCompositeOperation = 'screen';
    for (const k of [0, Math.PI]) { const a = lt * 7 + k; ctx.fillStyle = alpha(RED, .28); tracePath([[960, 40], [960 + Math.cos(a - .25) * 2400, 40 + Math.sin(a - .25) * 2400], [960 + Math.cos(a + .25) * 2400, 40 + Math.sin(a + .25) * 2400]]); ctx.fill(); }
    ctx.restore();
    halftone(FULL, RED, { cell: 20, dot: .18, op: .5, multiply: false });
    scrap(ellPts(960, 40, 60, 40, 20), Math.floor(t * 8) % 2 ? RED : '#FF8080', { torn: .5, ink: INK, sw: 4, seed: 2400 });
    // the chat window
    ctx.save(); ctx.translate(430, 400); ctx.rotate(-.04);
    scrap(rectPts(-350, -250, 700, 470), PAL.white, { torn: 1.5, seed: 2401, ink: INK, sw: 5, shadow: [10, 14] });
    scrap(rectPts(-350, -250, 700, 56), '#3A3A44', { torn: .5, seed: 2402, shadow: false });
    for (let i = 0; i < 3; i++) scrap(ellPts(-320 + i * 30, -222, 9, 9, 10), [RED, YEL, PAL.green][i], { torn: .1, shadow: false });
    txt('CHATBOT', 0, -221, 30, PAL.white, { font: 'archivo' });
    scrap(rrPts(40, -170, 280, 60, 20), PAL.sky, { torn: .8, seed: 2403, shadow: false });
    txt('status of ship?', 180, -140, 26, INK, { font: 'typewriter' });
    // hallucination swirl on the bot's avatar
    const ax = -280, ay = -30;
    for (let i = 0; i < 4; i++) { const pts = []; for (let j = 0; j <= 30; j++) { const u = j / 30, a = lt * 9 + i * TAU / 4 + u * 9, rr = u * 62; pts.push([ax + Math.cos(a) * rr, ay + Math.sin(a) * rr]); } marker(pts, [PAL.purple, PAL.pink, PAL.mint, YEL][i], 7, { rough: 0, smooth: true }); }
    scrap(rrPts(-210, -95, 500, 175, 24), YEL, { torn: 1, seed: 2404, ink: INK, sw: 4, shadow: false });
    const wob = (i, a) => Math.sin(lt * 14 + i * 1.3) * a;
    ['SHIP HAS', 'NUKES!!'].forEach((l, j) => { let cx = -180; [...l].forEach((ch, i) => { txt(ch, cx + wob(i + j, 3), -45 + j * 72 + wob(i * 2 + j, 6), 66, INK, { font: 'anton', align: 'left', rot: wob(i, .08) }); cx += textW(ch, 66, 'anton') + 8; }); });
    ctx.restore();
    // jets scramble from the right; after CANCEL they peel away and head home
    for (let i = 0; i < 3; i++) {
      const t0 = .02 + i * .12, tt = lt - t0; if (tt < 0) continue;
      const hd0 = -.95 - i * .08, v = 900;
      let x = 1420 + i * 150, y = 950 - i * 40, hd = hd0;
      const n = 24, dt = tt / n;
      for (let j = 0; j < n; j++) { const tj = t0 + j * dt; if (tj > slam) hd = hd0 - Math.PI * easeOut(clamp((tj - slam) / .45)) * (i % 2 ? -1 : 1); x += Math.cos(hd) * v * dt * Math.min(1, (j * dt + .1) * 4); y += Math.sin(hd) * v * dt * Math.min(1, (j * dt + .1) * 4); }
      jet(x, y, 24 - i * 3, hd, { flame: 1, col: ['#9AA2AF', '#8A93A0', '#A8B0BC'][i] });
    }
    // CANCEL button and the fist
    const press = lt < slam ? 0 : Math.exp(-after * 3);
    bigButton(930, 830, 150, 'CANCEL', press);
    const fy = lt < slam - .12 ? -200 : lt < slam ? lerp(-200, 790, easeIn((lt - (slam - .12)) / .12)) : 790 - easeOut(clamp((after - .25) / .3)) * 500;
    if (lt >= slam - .12) { slamFist(930, fy, 42); if (lt >= slam && after < .3) actionLines(930, 800, 200, 330, 16, YEL, 7, 12); }
    if (lt >= slam) sticker('ABORT!', 1560, 560, 95, YEL, { pop: popK(lt, slam + .05, .15), size: 42, rot: .18 });
    stamp('HALLUCINATION', 432, 575, 50, RED, -.08, { pop: popK(lt, verdict, .12) });
    camEnd();
    cutFlash(t, lt, RED);
    flash(.6 * flashAt(lt, slam, .08));
  });

  // V4.13 "Trump: It's 'Super,' by decree!" — TRUMP at a UN-blue podium; the DECREE scroll unrolls down its front: ARTIFICIAL → SUPER.
  line('V4', 13, (p, lt, d, t, sg) => {
    const superT = Math.min(.12, d * .1), stars = hitAt(sg, d, 2, .6);
    bg('#3E86D0');
    cam(t, lt, { shake: .6, zoom: 1.3 + .05 * p, cy: 640 });   // close on him and the scroll
    rays(960, 420, 24, alpha(PAL.white, .14), lt * .3);
    halftone(FULL, PAL.white, { cell: 20, dot: .14, op: .3, multiply: false });
    wreathEmblem(960, 470, 330, PAL.white, .55);
    // the man at the podium
    const s = 44, gx = 960, gy = 960;
    person(gx, gy, s, { ...TRUMP, eyes: lt < superT + .2 ? 'dot' : 'closed', mouth: frac(bpOf(t) * 2) < .5 ? 'O' : 'grin', aL: -.25, aR: -.25, seed: 381 });
    trumpHair(gx, gy, s);
    longTie(gx, gy, s);
    helloTag('DONALD', gx + .75 * s, gy - 6.9 * s, .34 * s, .05);
    // podium
    scrap([[700, 715], [1220, 715], [1180, 1200], [740, 1200]], '#2A3F66', { torn: 1.5, seed: 2500, ink: INK, sw: 5, shade: true, shadeOp: .25 });
    scrap(rectPts(680, 700, 560, 36), '#3A5588', { torn: 1, seed: 2501, ink: INK, sw: 4 });
    // the DECREE scroll unrolling down the front
    const uk = easeOut(clamp(lt / .3)), top = 720, bot = top + 20 + 250 * uk;
    scrap(rectPts(795, top, 330, bot - top), '#F3E3B5', { torn: 1.2, seed: 2510, ink: INK, sw: 3, shadow: [6, 8] });
    ctx.save(); tracePath(rectPts(795, top, 330, bot - top)); ctx.clip();
    txt('Decree', 960, top + 58, 62, INK, { font: 'fraktur' });
    txt('"ARTIFICIAL"', 960, top + 130, 34, INK, { font: 'typewriter' });
    if (lt > .3) marker([[830, top + 128], [1090, top + 134]], RED, 7, { rough: 1 });
    txt('→ SUPER', 960, top + 190, 44, RED, { font: 'anton' });
    ctx.restore();
    for (const yy of [top, bot]) scrap(rrPts(775, yy - 16, 370, 32, 14), '#D9C48A', { torn: .5, seed: 2511, ink: INK, sw: 3 });
    // SUPER!
    if (lt >= stars) for (let i = 0; i < 8; i++) { const a = i / 8 * TAU + lt, rr = 300 + (lt - stars) * 400; scrap(starPts(960 + Math.cos(a) * rr * 1.5, 200 + Math.sin(a) * rr * .5, 30 * (1 - clamp((lt - stars) / .8)), .45, 5), PAL.gold, { torn: .3, ink: INK, sw: 2, shadow: false }); }
    camEnd();
    cutFlash(t, lt);
  });

  // V4.14 "'Artificial'? Fake to me!" — ARTIFICIAL gets a FAKE! stamp, is crumpled into a ball and tossed.
  line('V4', 14, (p, lt, d, t, sg) => {
    const fakeT = hitAt(sg, d, 0, .15), crush0 = hitAt(sg, d, 1, .38), toss = hitAt(sg, d, 2, .62), swish = hitAt(sg, d, 3, .85);
    bg(YEL);
    cam(t, lt, { shake: .9, zoom: 1.02, hits: [[fakeT, 16], [toss, 6]] });
    rays(900, 480, 22, alpha(RED, .5), -lt * .5);
    halftone(FULL, INK, { cell: 18, dot: .2, op: .15 });
    // wastebasket
    const bx = 1590, by = 900;
    scrap([[bx - 130, by - 250], [bx + 130, by - 250], [bx + 100, by], [bx - 100, by]], '#6B6B74', { torn: 1, seed: 2600, ink: INK, sw: 5, shade: true, shadeOp: .3, rot: 0 });
    for (let i = 0; i < 5; i++) marker([[bx - 100 + i * 50, by - 240], [bx - 80 + i * 40, by - 10]], INK, 3, { rough: 1, alpha: .5 });
    scrap(ellPts(bx, by - 250, 132, 26, 24), '#4A4A52', { torn: .5, seed: 2601, ink: INK, sw: 4, shadow: false });
    // the word on a card, crumpling
    const c = easeIn(clamp((lt - crush0) / Math.max(.1, toss - crush0 - .02)));
    let cx = 880, cy = 480, rot = -.04;
    if (lt >= toss) { const u = clamp((lt - toss) / Math.max(.15, swish - toss)); cx = lerp(880, bx, u); cy = lerp(480, by - 250, u) - Math.sin(u * Math.PI) * 330; rot = u * 9; }
    const cw = 1080, ch = 300, N = 40;
    const perim = []; for (let i = 0; i < N; i++) { const u = i / N * 4, side = Math.floor(u), f = u - side; const [x, y] = [[-cw / 2 + f * cw, -ch / 2], [cw / 2, -ch / 2 + f * ch], [cw / 2 - f * cw, ch / 2], [-cw / 2, ch / 2 - f * ch]][side]; perim.push([x, y]); }
    const ballR = 105;
    const shape = perim.map(([x, y], i) => { const a = Math.atan2(y, x), n = .75 + hash2(2610, i) * .5; const bx2 = Math.cos(a) * ballR * n, by2 = Math.sin(a) * ballR * n; return [lerp(x, bx2, c), lerp(y, by2, c)]; });
    const visible = !(lt >= swish);
    if (visible) {
      ctx.save(); ctx.translate(cx, cy); ctx.rotate(rot);
      scrap(shape, PAL.white, { torn: 1.5 + c * 4, seed: 2620, ink: INK, sw: 5, shadow: [10, 14], shade: c > .1 ? INK : undefined, shadeOp: .25 * c });
      ctx.save(); tracePath(shape); ctx.clip();
      ctx.save(); ctx.scale(lerp(1, .18, c), lerp(1, .45, c)); ctx.rotate(c * .5);
      txt('ARTIFICIAL', 0, 10, 190, INK, { font: 'abril' });
      ctx.restore();
      for (let i = 0; i < 9; i++) { const a = hash2(2630, i) * TAU, r0 = hash2(2631, i) * 60; marker([[Math.cos(a) * r0 * (1 - c * .5), Math.sin(a) * r0], [Math.cos(a + 1.2) * 400 * (1 - c * .75), Math.sin(a + 1.2) * 160 * (1 - c * .4)]], alpha(INK, .5 * c), 3, { rough: 3 }); }
      ctx.restore();
      if (c < .15) stamp('FAKE!', 250, 95, 120, RED, -.22, { pop: popK(lt, fakeT, .1), alpha: 1 - c * 6, blend: 'source-over' });
      ctx.restore();
    }
    // the hands doing the crumpling
    if (lt >= toss) { // dotted flight path of the paper ball
      const u = clamp((lt - toss) / Math.max(.15, swish - toss)), pts = [];
      for (let i = 0; i <= 24; i++) { const v = i / 24 * u; pts.push([lerp(880, bx, v), lerp(480, by - 250, v) - Math.sin(v * Math.PI) * 330]); }
      for (let i = 0; i < 24; i += 2) marker([pts[i], pts[i + 1]], INK, 7, { rough: 0, alpha: .7 });
    }
    if (lt >= crush0 - .15) {
      const e = clamp((lt - (crush0 - .15)) / .15), half = lerp(cw / 2, ballR, c) + 40, f = clamp((lt - toss) / .22), gone = easeIn(clamp((lt - swish - .1) / .3));
      for (const side of [-1, 1]) {
        let hx = 880 + side * (half + (1 - e) * 500), hy = 480, hr = 0;
        if (lt >= toss) {
          if (side < 0) hx -= easeIn(f) * 1000; // the left hand lets go
          else { hx += 70 * f + gone * 1000; hy -= 150 * Math.sin(f * Math.PI * .7); hr = -.55 * Math.sin(f * Math.PI * .9); } // the right hand flicks the shot
        }
        if (hx < -300 || hx > W + 300) continue;
        ctx.save(); ctx.translate(hx, hy); ctx.rotate(hr); ctx.scale(side, 1);
        scrap(rectPts(40, -60, 1200, 120), SUIT, { torn: 1, seed: 2640, shade: true, shadeOp: .2 });
        scrap(rectPts(30, -66, 40, 132), PAL.white, { torn: .5, seed: 2641, shadow: false, ink: INK, sw: 2 });
        scrap(rrPts(-60, -70, 100, 140, 40), SKINS[4], { torn: .6, seed: 2642, ink: INK, sw: 3 });
        for (let f = 0; f < 3; f++) marker([[-40, -40 + f * 35], [0, -40 + f * 35]], mixCol(SKINS[4], INK, .4), 4, { rough: .5 });
        ctx.restore();
      }
    }
    if (lt >= swish) { sticker('SWISH!', bx - 40, by - 420, 90, PAL.white, { pop: popK(lt, swish, .12), size: 40, rot: -.15 }); bubble("IT'S NOT FAKE. IT'S ACTUALLY AMAZING!", 820, 430, { size: 58, maxW: 720, pop: popK(lt, swish + .05, .18), rot: -.04, fill: PAL.white }); scrap(ellPts(bx + jit(3), by - 262, 60, 20, 16), PAL.white, { torn: 3, seed: 2650, ink: INK, sw: 3, shadow: false }); }
    if (c > .3 && lt < swish) txt('CRUNCH!', 880, 250, 84, RED, { font: 'anton', rot: -.12 + jit(.04), stroke: INK, sw: 6, alpha: clamp((c - .3) * 4) });
    camEnd();
    cutFlash(t, lt);
    flash(.4 * flashAt(lt, fakeT, .07), RED);
  });

  // V4.15 "Ten days after 'pace' — surprise!" — the calendar rips from SEP 12 to SEP 22; two gift boxes start shaking.
  line('V4', 15, (p, lt, d, t, sg) => {
    const flipEnd = hitAt(sg, d, 2, .55);
    bg(RED);
    cam(t, lt, { shake: 1.1, zoom: 1.02 + .03 * p, hits: [[flipEnd, 12]] });
    halftone(FULL, INK, { cell: 18, dot: .22, op: .3 });
    // calendar
    const kx = 520, ky = 500, pw = 440, ph = 500;
    card(kx, ky + 10, pw + 60, ph + 70, '#3A2A20', .02, { seed: 2700, torn: 1.5 });
    const n = 10, hold = Math.min(.3, flipEnd * .4), per = (flipEnd - hold) / n;
    const torn = lt < hold ? 0 : Math.min(n, Math.floor((lt - hold) / per) + 1);
    calPage(kx, ky, pw, ph, 12 + torn, { shadow: [4, 5] });
    if (torn >= n) { circleMark(kx, ky + 70, 200, 170, INK, 10, popK(lt, flipEnd, .2)); }
    for (let j = 0; j < 4; j++) marker([[kx - 150 + j * 100, ky - ph / 2 - 30], [kx - 150 + j * 100, ky - ph / 2 + 18]], '#9A9AA6', 12, { rough: 0 });
    // pages ripping away (most recent last so it's on top)
    for (let i = Math.max(0, torn - 4); i < torn; i++) {
      const a = lt - hold - i * per, u = a / .35;
      if (u > 1) continue;
      calPage(kx - u * 700 - 40 * (i % 3), ky - u * 520 + u * u * 250, pw, ph, 12 + i, { rot: -u * 2.4 - .1 * (i % 2), s: 1 - u * .4, shadow: [8, 10] });
    }
    if (lt < flipEnd) for (let i = 0; i < 6; i++) marker([[kx - 300 - i * 18, ky - 240 + i * 70], [kx - 420 - i * 22, ky - 280 + i * 70]], PAL.white, 6, { rough: 0, alpha: .8 });
    // table + two shaking boxes
    scrap(rectPts(930, 790, 1100, 40), '#6A4028', { torn: 1, seed: 2710, ink: INK, sw: 4 });
    const shake = clamp((lt - flipEnd * .5) / (d * .6)) ** 1.5;
    const sh = a => jit(a * shake);
    const hop = i => Math.max(0, Math.sin((bpOf(t) * 2 + i * .5) * Math.PI)) * 18 * shake;
    giftBox(1220 + sh(8), 790 - hop(0), 330, 250, PAL.clawd, YEL, { rot: sh(.06), seed: 1500, tone: PAL.clawdDk });
    giftLid(1220 + sh(8), 790 - 250 - hop(0) - hop(1) * .8, 330, PAL.clawd, YEL, sh(.1), { seed: 1500 });
    giftBox(1640 + sh(8), 790 - hop(1), 290, 220, PAL.teal, PAL.white, { rot: sh(.06), seed: 1520 });
    giftLid(1640 + sh(8), 790 - 220 - hop(1) - hop(0) * .8, 290, PAL.teal, PAL.white, sh(.1), { seed: 1520 });
    if (shake > .2) { txt('?!', 1010, 480 + jit(4), 84, YEL, { font: 'anton', stroke: INK, sw: 8, rot: -.15 }); txt('?!', 1650, 412 + jit(4), 76, YEL, { font: 'anton', stroke: INK, sw: 8, rot: .15 }); }
    camEnd();
    cutFlash(t, lt);
  });

  // V4.16 "Opus 5.5: 'Hi, guys!'" — Clawd springs out of the box: sheepish wave, blush, 5.5 sticker, "Hi, guys!"…
  // then GPT-6 springs out of the box next door, also waving. Clawd side-eyes it, then winks at camera.
  line('V4', 16, (p, lt, d, t, sg) => {
    const gptT = hitAt(sg, d, 1, .3), glanceT = hitAt(sg, d, 2, .58), winkT = hitAt(sg, d, 3, .8);
    bg(PAL.pink);
    cam(t, lt, { shake: 1.0, zoom: 1.03 + .03 * p, cy: 520, hits: [[0, 18], [gptT, 12]] });
    rays(700, 380, 22, '#FF8FC4', lt * .8);
    halftone(FULL, RED, { cell: 18, dot: .2, op: .2 });
    const tableY = 860;
    scrap(rectPts(-100, tableY, W + 200, 60), '#6A4028', { torn: 1, seed: 2800, ink: INK, sw: 4 });
    // the PACE pennant from V4.7, knocked flat by the blast
    const fallK = lt < gptT ? Math.sin(lt * 30) * .04 : easeOut(clamp((lt - gptT) / .25));
    ctx.save(); ctx.translate(1150, tableY); ctx.rotate(-lerp(0, 1.0, fallK));
    marker([[0, 0], [0, -230]], '#6B5B4B', 9, { rough: 0 });
    scrap([[0, -230], [150, -190], [0, -150]], YEL, { torn: .4, ink: INK, sw: 3, seed: 2801 });
    txt('PACE', 58, -190, 34, INK, { font: 'archivo' });
    ctx.restore();
    // Clawd's box (Opus 5.5)
    const b1x = 700, b1w = 380, b1h = 270, b1top = tableY - b1h;
    const lu = lt / .42;
    giftLid(b1x - 160 * lu, b1top - 1500 * lu, b1w, PAL.clawd, YEL, -lu * 2.2, { seed: 1500 });
    const jk = elasticOut(clamp(lt / .5)), springLen = 40 + 120 * jk, u = 30;
    const cGround = b1top - springLen + 30;
    const winking = lt >= winkT, glancing = lt >= glanceT && !winking;
    spring(b1x, b1top + 40, cGround - 10, 40, 6);
    clawd(b1x, cGround, u, { eyes: winking ? 'normal' : glancing ? 'worried' : 'happy', lookX: glancing ? 1 : 0, mouth: winking ? 'grin' : 'smile', blush: true, sweat: glancing, aL: 1.1 + Math.sin(lt * 16) * .45, aR: winking ? .2 : -.5, shadow: false, rot: winking ? 0 : Math.sin(lt * 8) * .04 * (1 - jk * .5) });
    if (winking) {
      clawdWink(b1x, cGround, u);
      scrap(starPts(b1x - 4.3 * u, cGround - 8.4 * u, 26 * backOut(popK(lt, winkT, .12)), .35, 4), PAL.white, { torn: .2, ink: INK, sw: 3, shadow: false });
    }
    giftBox(b1x, tableY, b1w, b1h, PAL.clawd, YEL, { seed: 1500, tone: PAL.clawdDk });
    sticker('5.5', b1x, tableY - b1h * .48, 96, YEL, { pop: popK(lt, .06, .16), size: 74, rot: -.12 });
    burstBits(b1x, b1top - 20, lt, 50, 2810, { v: 1300, g: 1300, a0: -Math.PI / 2, spread: 2.2 });
    bubble('Hi, guys!', 330, 250, { size: 68, tail: [540, 400], pop: popK(lt, .08, .2), rot: -.05, fill: PAL.white });
    // GPT-6's box
    const b2x = 1370, b2w = 330, b2h = 240, b2top = tableY - b2h, s2 = 25;
    if (lt >= gptT) {
      const l2 = (lt - gptT) / .42;
      giftLid(b2x + 200 * l2, b2top - 1500 * l2, b2w, PAL.teal, PAL.white, l2 * 2.2, { seed: 1520 });
      const gk = elasticOut(clamp((lt - gptT) / .5)), gGround = b2top + 60 - 120 * gk;
      spring(b2x, b2top + 40, gGround - 5, 34, 6);
      bot(b2x, gGround, s2, { col: '#B9C3D0', eyes: 'happy', aR: 1.1 + Math.sin(lt * 16 + 1) * .45, aL: -.6, shadow: false, seed: 540 });
      bib(b2x, gGround - 5.3 * s2, 150, 62, 'GPT-6', .06);
    } else giftLid(b2x + jit(4), b2top - Math.abs(jit(10)), b2w, PAL.teal, PAL.white, jit(.08), { seed: 1520 });
    giftBox(b2x + (lt < gptT ? jit(5) : 0), tableY, b2w, b2h, PAL.teal, PAL.white, { seed: 1520 });
    if (lt >= gptT) { burstBits(b2x, b2top - 20, lt - gptT, 36, 2830, { v: 1200, g: 1300, a0: -Math.PI / 2, spread: 2 }); bubble('Hi, guys!', 1650, 330, { size: 48, tail: [1470, 440], pop: popK(lt, gptT + .08, .2), rot: .06, fill: PAL.mint }); }
    confettiFall(lt, 40, 2850);
    camEnd();
    cutFlash(t, lt, YEL);
  });

  // =====================================================================================================================
  // The vertical video (1080 × 1920): each line re-staged for the tall frame, with the same props, gags, palette and the
  // escalating shake (cam() and cutFlash() centre on the tall frame by themselves). The subject sits in the safe area (y 390–1250,
  // under the date stamp and above the caption tape), floors, tables, roads and crowds fill the foot. Vertical motion wherever the
  // line has some: the agents pile up into a tower under the REWARD star, the banner unrolls down, the spike shoots off the top,
  // the magnifier scans the finish line, the grid trails down the frame behind the pace car, the bonked car flies up and away,
  // the hymn rises to the window, the calendar's pages fly up, the paper ball drops into the bin, Clawd springs up out of his box.
  // =====================================================================================================================

  // ---------- private helpers for the tall frame ----------
  // a race car seen from above, nose up; (x, y) = centre; ≈ 4.6s wide, 9s long. o: race (wings), stripe, num, seed, rot
  function carTop(x, y, s, col, o = {}) {
    ctx.save(); ctx.translate(x, y); if (o.rot) ctx.rotate(o.rot);
    const dk = mixCol(col, INK, .35);
    for (const [wx, wy] of [[-1.95, -2.5], [1.95, -2.5], [-2, 2.4], [2, 2.4]]) scrap(rrPts((wx - .5) * s, (wy - .9) * s, 1 * s, 1.8 * s, .3 * s), INK, { torn: .3, shadow: [.15 * s, .2 * s] });
    if (o.race) scrap(rectPts(-2.3 * s, 3.6 * s, 4.6 * s, .85 * s), dk, { torn: .4, seed: (o.seed ?? 1440) + 1, ink: INK, sw: .08 * s, shadow: [.15 * s, .2 * s] });
    scrap(rrPts(-1.75 * s, -4.2 * s, 3.5 * s, 8.3 * s, 1.3 * s), col, { torn: .6, seed: o.seed ?? 1440, ink: INK, sw: .12 * s, shade: true, shadeOp: .22, shadow: [.25 * s, .35 * s] });
    if (o.race) scrap(rectPts(-2.25 * s, -4.75 * s, 4.5 * s, .6 * s), dk, { torn: .4, seed: (o.seed ?? 1440) + 2, ink: INK, sw: .08 * s, shadow: false });
    if (o.stripe) scrap(rectPts(-.32 * s, -4.1 * s, .64 * s, 8.1 * s), o.stripe, { torn: .3, shadow: false });
    scrap([[-1.4 * s, -1.25 * s], [1.4 * s, -1.25 * s], [1.15 * s, -.15 * s], [-1.15 * s, -.15 * s]], PAL.sky, { torn: .3, shadow: false, ink: INK, sw: .08 * s });
    scrap(rrPts(-1.2 * s, -.15 * s, 2.4 * s, 2.1 * s, .4 * s), mixCol(col, INK, .15), { torn: .4, shadow: false, ink: INK, sw: .08 * s });
    scrap([[-1.15 * s, 1.95 * s], [1.15 * s, 1.95 * s], [1.3 * s, 2.7 * s], [-1.3 * s, 2.7 * s]], PAL.sky, { torn: .3, shadow: false, ink: INK, sw: .07 * s });
    if (o.num !== undefined) {
      scrap(ellPts(0, -2.75 * s, .95 * s, .95 * s, 18), PAL.white, { torn: .3, shadow: false, ink: INK, sw: .08 * s });
      txt(String(o.num), 0, -2.7 * s, 1.35 * s, INK, { font: 'anton' });
    }
    ctx.restore();
  }
  // a fist coming down along `rot` (0 = straight down from above, + = from the upper right); (x, y) = bottom of the fist
  function vFist(x, y, s, rot) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot); ctx.translate(-x, -y);
    const skin = SKINS[0];
    scrap(rectPts(x - 1.5 * s, y - 3 * s - 2000, 3 * s, 2000), SUIT, { torn: 1, seed: 1730, shade: true, shadeOp: .25 });
    scrap(rectPts(x - 1.65 * s, y - 3.4 * s, 3.3 * s, .8 * s), PAL.white, { torn: .5, seed: 1731, shadow: false, ink: INK, sw: .06 * s });
    scrap(rrPts(x - 1.8 * s, y - 2.7 * s, 3.6 * s, 2.7 * s, .9 * s), skin, { torn: .6, seed: 1732, ink: INK, sw: .1 * s });
    for (let i = 1; i < 4; i++) marker([[x - 1.8 * s + i * .9 * s, y - 1.2 * s], [x - 1.8 * s + i * .9 * s, y - .15 * s]], mixCol(skin, INK, .45), .12 * s, { rough: .4 });
    scrap(rrPts(x + 1.25 * s, y - 2.4 * s, 1.1 * s, 1.7 * s, .5 * s), skin, { torn: .4, ink: INK, sw: .1 * s, shadow: false });
    ctx.restore();
  }
  // the post as a screenshot card: (x, y) = top centre, w wide; returns its height
  function postCard(x, y, w, o = {}) {
    const size = o.size ?? 36, L = wrap(o.text, size, 'archivo', w - 64), h = 88 + L.length * size * 1.25 + 14;
    ctx.save(); ctx.translate(x, y); ctx.rotate(o.rot ?? 0);
    scrap(rrPts(-w / 2, 0, w, h, 26), PAL.white, { torn: 1, seed: 2205, ink: INK, sw: 5, shadow: [10, 14] });
    scrap(ellPts(-w / 2 + 56, 46, 30, 30, 18), o.avatar ?? RED, { torn: .3, shadow: false, ink: INK, sw: 3 });
    txt(o.user, -w / 2 + 100, 34, 30, INK, { font: 'archivo', align: 'left', maxW: w - 300 });
    txt(o.handle, -w / 2 + 100, 64, 22, PAL.grey, { font: 'archivo', align: 'left', maxW: w - 300 });
    if (o.likes) txt(`♥ ${o.likes}`, w / 2 - 30, 46, 26, PAL.grey, { font: 'archivo', align: 'right' });
    L.forEach((l, i) => txt(l, -w / 2 + 32, 88 + size * .55 + i * size * 1.25, size, INK, { font: 'archivo', align: 'left' }));
    ctx.restore();
    return h;
  }

  // ---------- V4.1 (vertical): the board up top; the agents below it in a deep stack, starry-eyed ----------
  vshot('V4.1', (p, lt, d, t) => {
    bg('#0E0B10');
    cam(t, lt, { zoom: 1 + p * .04, shake: .6 });
    rays(540, 690, 18, '#3A0D12', lt * .3);
    glow(540, 700, 1000, '#FF5A1F', .4);
    halftone(FULL, RED, { cell: 22, dot: .18, op: .5, multiply: false });
    corkboard(100, 400, 880, 600, { notes: [] });
    const nk = i => popK(lt, .015 * i, .12);
    // red string from every pin to the big note's
    const pins = [[260, 437], [540, 427], [820, 442], [260, 857], [540, 872], [820, 862]], hub = [540, 598];
    ctx.save(); ctx.globalAlpha = clamp(lt / .2);
    for (const pin of pins) marker([pin, hub], RED, 3, { rough: 1 });
    marker([pins[0], pins[1]], RED, 3, { rough: 1 }); marker([pins[4], pins[5]], RED, 3, { rough: 1 });
    ctx.restore();
    note('zzINBOX_sol', 260, 480, 250, 110, YEL, -.07, 36, { pop: nk(0) });
    note('HOLD', 540, 470, 200, 110, PAL.pink, .05, 60, { pop: nk(1) });
    note('VETO', 820, 485, 200, 110, PAL.sky, -.04, 60, { pop: nk(2) });
    note('NO HUMANS', 260, 900, 240, 110, PAL.white, -.05, 40, { pop: nk(3) });
    note('STOP', 540, 915, 180, 110, PAL.mint, .08, 54, { pop: nk(4) });
    note('zzINBOX_astra', 820, 905, 240, 110, YEL, .06, 32, { pop: nk(5) });
    note("WE'VE FOUND\nOTHER AGENTS!", 540, 700, 660, 230, PAL.white, .025, 72, { pop: popK(lt, .08, .16), ink: RED, pin: PAL.blue });
    // the agents, three rows deep: the back row still streaming in under the board, the middle row hopping, the front row huge
    const bars = [PAL.green, PAL.teal, YEL, PAL.sky, PAL.pink];
    const hop = (ph, a = .6) => -Math.max(0, Math.sin((bpOf(t) * 2 + ph) * Math.PI)) * a;
    for (let i = 0; i < 10; i++) {
      const side = i % 2 ? 1 : -1, r = k => hash2(1850 + i, k);
      const tx = 110 + (i + .5) / 10 * 860 + (r(1) - .5) * 30, arrive = .12 + r(2) * .6;
      const u = easeOut(clamp(lt / arrive)), x = lerp(side < 0 ? -80 - r(3) * 260 : W + 80 + r(3) * 260, tx, u);
      const o = { walk: lt * 5 + r(4), dy: u < .95 ? -Math.abs(Math.sin(lt * 18 + i)) * .5 : hop(r(5)), bar: bars[i % 5], seed: 600 + i };
      if (u > .95) starAgent(x, 1098, 22, o); else agent(x, 1098, 22, { ...o, eyes: 'dot' });
    }
    for (let i = 0; i < 6; i++) {
      const r = k => hash2(1870 + i, k), x = 105 + (i + .5) / 6 * 870 + (r(1) - .5) * 40;
      const o = { dy: hop(r(3), .55), rot: jit(.03), bar: bars[(i + 2) % 5], seed: 620 + i };
      if (i === 4) agent(x, 1268, 47, { ...o, eyes: 'heart' }); else starAgent(x, 1268, 47, o);
      if (r(4) < .6) txt('!', x + 40, 1268 - 47 * 3.6 + hop(r(3), 20), 64, YEL, { font: 'anton', rot: .15, stroke: INK, sw: 6, alpha: popK(lt, .1 + r(5) * .3, .1) });
    }
    [[95, 86], [385, 80], [690, 84], [985, 88]].forEach(([x, s], i) => {
      const r = k => hash2(1890 + i, k);
      starAgent(x, 1915, s, { dy: hop(r(2), .35), rot: jit(.03) + (i === 1 ? -.06 : 0), bar: bars[(i + 1) % 5], seed: 640 + i });
    });
    bubble('OH MY GOD!', 690, 1040, { size: 70, tail: [800, 1150], pop: popK(lt, .05, .22), rot: -.04, fill: YEL });
    camEnd();
    cutFlash(t, lt, YEL);
    captionStyle({ color: RED });
  });

  // ---------- V4.2 (vertical): the horde piles up over Huggy into a tower, under the REWARD star dangling at the top ----------
  vshot('V4.2', (p, lt, d, t, sg) => {
    const grab = hitAt(sg, d, 3, .55), after = lt - grab;
    bg(RED);
    cam(t, lt, { shake: 1.2, zoom: 1.02 + .04 * p, hits: [[grab, 16]] });
    rays(540, 560, 20, alpha(BLOOD, .85), lt * .45);
    halftone(FULL, INK, { cell: 18, dot: .2, op: .22 });
    const hx = 540, hy = 1115, r = 166, mob = clamp(lt / (grab * .9));
    const drawAg = a => agent(a.x, a.y, a.s, { eyes: a.eyes, walk: a.walk, rot: a.rot, bar: [PAL.green, PAL.teal, YEL][a.i % 3], seed: 660 + a.i });
    // the clingers on Huggy's flanks
    const cling = [];
    for (let i = 0; i < 12; i++) {
      const R = k => hash2(1900 + i, k), side = i % 2 ? 1 : -1;
      const th0 = lerp(-.6, 1.3, (Math.floor(i / 2) + .5) / 6) + (R(1) - .5) * .15, th = side > 0 ? th0 : Math.PI - th0;
      const s = 28 + R(3) * 8, rad = r * (.97 + .12 * R(2));
      const tx = hx + Math.cos(th) * rad, ty = hy + Math.sin(th) * rad + 1.6 * s;
      const go = grab * .4 * i / 12, u = easeOut(clamp((lt - go) / .3));
      if (u <= 0) continue;
      const x0 = hx + side * (720 + R(4) * 200), y0 = hy + 350 + R(5) * 300;
      cling.push({ i, s, back: Math.sin(th) < -.3, x: lerp(x0, tx, u) + (u >= 1 ? jit(4) : 0), y: lerp(y0, ty, u) - (u < 1 ? Math.abs(Math.sin(lt * 20 + i)) * 24 : jit(4)),
        rot: u >= 1 ? (th - Math.PI / 2) * -.25 + side * .2 + jit(.1) : 0, walk: lt * 6 + i, eyes: R(6) < .7 ? 'angry' : 'spark' });
    }
    // the stack on top of his head, row by row, the hero last
    const ROWS = [{ xs: [-140, -48, 48, 140], s: 29 }, { y: 902, xs: [-96, 0, 96], s: 29 }, { y: 824, xs: [-48, 48], s: 29 }, { y: 746, xs: [0], s: 32 }];
    const stack = [];
    ROWS.forEach((row, ri) => row.xs.forEach((dx, j) => {
      const i = 20 + ri * 4 + j, R = k => hash2(1950 + i, k), side = dx < 0 || (dx === 0 && ri % 2) ? -1 : 1;
      const ty = row.y ?? hy - Math.sqrt(r * r - dx * dx) + 26, tx = hx + dx;
      const go = grab * (.32 + ri * .14) + j * .03, u = easeOut(clamp((lt - go) / .2));
      if (u <= 0) return;
      const x0 = hx + side * (560 + R(1) * 160), y0 = ty + 260 + R(2) * 200;
      stack.push({ i, s: row.s, hero: ri === 3, x: lerp(x0, tx, u) + (u >= 1 ? jit(3) : 0), y: lerp(y0, ty, u) - Math.sin(u * Math.PI) * 90,
        rot: u >= 1 ? jit(.06) + (ri === 3 ? 0 : side * .08) : side * -.3 * (1 - u), walk: lt * 6 + i, eyes: R(3) < .6 ? 'angry' : 'spark' });
    }));
    cling.filter(a => a.back).forEach(drawAg);
    huggy(hx + jit(3 + 6 * mob), hy + jit(2 + 4 * mob), r, { mood: lt < d * .1 ? 'happy' : 'scared', hands: lt < grab ? .15 : .6, rot: jit(.03 * mob) });
    if (lt >= d * .1) { txt('!', hx + r * 1.05, hy - r * .55, 90, YEL, { font: 'anton', rot: .2, stroke: INK, sw: 8 }); txt('!', hx - r * 1.1, hy - r * .45, 76, YEL, { font: 'anton', rot: -.3, stroke: INK, sw: 8 }); }
    cling.filter(a => !a.back).forEach(drawAg);
    stack.filter(a => !a.hero).forEach(drawAg);
    // the star: dangling on its string, swaying, until the hero yanks it off and holds it up
    const hero = stack.find(a => a.hero), held = lt >= grab && hero;
    const sway = Math.sin(lt * 5) * .12, heroTop = 746 - 3.1 * 32;
    let sx = hx + Math.sin(lt * 5) * 30, sy = 540, srot = sway + jit(.02);
    if (held) { const k = backOut(popK(lt, grab, .2), 1.6); sx = lerp(sx, hx, k); sy = lerp(540, heroTop - 112 - 14 * pulse(t, 6), k); srot = jit(.03); }
    if (!held) marker([[hx + Math.sin(lt * 5) * 8, -60], [sx, sy - 125]], INK, 5, { rough: 0 });
    else { const k = clamp(after / .3); marker([[hx, -60], [hx + 10, lerp(360, 120, k)]], INK, 5, { rough: 0, alpha: 1 - k }); }
    if (hero) {
      if (held) for (const side of [-1, 1]) marker([[hero.x + side * 34, heroTop + 50], [hero.x + side * 66, heroTop - 6], [sx + side * 46, sy + 66]], INK, 9, { rough: 0 });
      else if (lt > grab - .2) for (const side of [-1, 1]) marker([[hero.x + side * 34, heroTop + 50], [hero.x + side * 50, heroTop - 30 - 30 * clamp((lt - grab + .2) / .2)]], INK, 9, { rough: 0 });
      starAgent(hero.x, hero.y, 32, { rot: hero.rot, bar: YEL, seed: 699 });
    }
    goldStar(sx, sy, held ? 134 : 124, 'REWARD', srot, { glow: held ? 1 : 0 });
    if (held) sticker('+1', 840, 600, 78, PAL.white, { pop: popK(lt, grab + .08, .2), size: 66, rot: .2 });
    // more of them pouring in along the foot of the frame
    for (let i = 0; i < 9; i++) {
      const R = k => hash2(1980 + i, k), side = i % 2 ? 1 : -1, s = 44 + R(1) * 16;
      const x = lerp(side < 0 ? -120 - R(2) * 300 : W + 120 + R(2) * 300, hx + side * (90 + R(3) * 330), easeOut(clamp(lt / (.6 + R(4) * .8))));
      agent(x, 1640 + R(5) * 260, s, { eyes: 'angry', walk: lt * 6 + i, dy: -Math.abs(Math.sin(lt * 14 + i)) * .4, rot: jit(.05) + side * -.08, bar: [PAL.green, PAL.teal, YEL][i % 3], seed: 680 + i });
    }
    camEnd();
    cutFlash(t, lt);
    flash(.5 * flashAt(lt, grab, .08), YEL);
  });

  // ---------- V4.3 (vertical): bandaged Huggy behind the tape up top; JENSEN below slaps the cheque down; SOLD ----------
  vshot('V4.3', (p, lt, d, t, sg) => {
    const slap = hitAt(sg, d, 1, .38), sold = hitAt(sg, d, 2, .68);
    bg(NIGHT);
    cam(t, lt, { shake: .9, zoom: 1.03 - .03 * p, hits: [[slap, 18], [sold, 10]] });
    const e8 = Math.floor(bpOf(t) * 2) % 2;
    glow(80, 260, 900, e8 ? RED : PAL.blue, .55); glow(1000, 300, 900, e8 ? PAL.blue : RED, .55);
    halftone(FULL, e8 ? RED : PAL.blue, { cell: 20, dot: .16, op: .35, multiply: false });
    scrap(rectPts(-400, 1010, W + 800, 1300), '#26222C', { torn: 2, shadow: false, seed: 1920 });
    // on the floor at the foot: the chalk outline (round, with its two little hands) and the evidence markers
    ctx.save(); ctx.globalAlpha = .85;
    marker(ellPts(430, 1700, 250, 92, 40), PAL.white, 7, { close: true, rough: 2.5 });
    for (const sd of [-1, 1]) marker(ellPts(430 + sd * 300, 1650, 56, 30, 16, sd * .4), PAL.white, 6, { close: true, rough: 2 });
    ctx.restore();
    for (const [x, y, n] of [[150, 1595, 1], [745, 1790, 2], [905, 1585, 3]]) {
      scrap([[x - 46, y + 40], [x + 46, y + 40], [x + 30, y - 40], [x - 30, y - 40]], YEL, { torn: .5, seed: 1930 + n, ink: INK, sw: 3, shadow: [5, 7] });
      txt(String(n), x, y + 4, 54, INK, { font: 'anton' });
    }
    // Huggy, bandaged and dazed
    const hx = 330, hy = 615, r = 168;
    huggy(hx + jit(2), hy + jit(2), r, { mood: 'scared', hands: .25 });
    bandage(hx + 66, hy - 125, 116, .55); bandage(hx + 66, hy - 125, 116, -.55); bandage(hx - 100, hy + 38, 88, .3);
    tapeBand(-120, 840, 1200, 905, 66, 'CRIME SCENE  •  DO NOT CROSS  •', { scroll: lt * 40, seed: 1711 });
    // JENSEN on the right, cheque aloft… then slapped down on the scene
    const jx = 800, jy = 1520, js = 64;
    const armUp = lt < slap - .06 ? 1.35 + Math.sin(lt * 12) * .1 : lt < slap ? lerp(1.35, -.35, (lt - (slap - .06)) / .06) : -.35;
    person(jx, jy, js, { top: 'jacket', topCol: '#17161B', pants: '#26252B', hair: 'swoop', hairCol: '#4A4A4E', skin: SKINS[4], eyes: lt < sold ? 'happy' : 'dot', mouth: 'grin', aL: armUp, aR: -1.1, lookX: -1, seed: 330 });
    for (const [a, b] of [[[jx - 1.1 * js, jy - 7.4 * js], [jx - .9 * js, jy - 4.3 * js]], [[jx + 1.05 * js, jy - 7.2 * js], [jx + .95 * js, jy - 4.6 * js]]]) marker([a, b], 'rgb(255 255 255 / .45)', 6, { rough: 1 });
    helloTag('JENSEN', jx + .35 * js, jy - 6 * js, .4 * js);
    const hand = [jx - 1.35 * js - 3.1 * js * Math.cos(armUp), jy - 7.1 * js - 3.1 * js * Math.sin(armUp)];
    const fly = clamp((lt - (slap - .07)) / .07), CX = 415, CY = 1095;
    if (lt < slap) cheque(lerp(hand[0] - 30, CX, fly), lerp(hand[1] - 70, CY, fly), lerp(300, 580, fly), lerp(-.3, -.07, fly) + jit(.03), '$12,900,000,000');
    else { actionLines(CX, CY, 320, 440, 14, PAL.white, 5, 3); cheque(CX, CY, 580, -.07, '$12,900,000,000', { s: lerp(1.12, 1, easeOut(popK(lt, slap, .1))) }); }
    // SOLD slapped on Huggy's tummy
    const sk = popK(lt, sold, .1);
    if (sk > 0) {
      ctx.save(); ctx.translate(hx + 25, hy + 110); ctx.rotate(-.16 + jit(.01)); const s = lerp(2, 1, easeOut(sk)); ctx.scale(s, s); ctx.globalAlpha = clamp(sk * 3);
      scrap(rectPts(-165, -62, 330, 124), RED, { torn: 1.5, seed: 1925, ink: INK, sw: 5, shadow: [8, 10] });
      scrap(rectPts(-150, -48, 300, 96), RED, { torn: .5, seed: 1926, ink: PAL.white, sw: 4, shadow: false });
      txt('SOLD!', 0, 4, 92, PAL.white, { font: 'anton' });
      ctx.restore();
    }
    if (lt >= sold) {
      txt('?', hx - 200, 430 + jit(3), 110, YEL, { font: 'anton', rot: -.25, stroke: INK, sw: 8, alpha: popK(lt, sold + .1, .08) });
      txt('?', hx + 215, 455 + jit(3), 92, YEL, { font: 'anton', rot: .25, stroke: INK, sw: 8, alpha: popK(lt, sold + .16, .08) });
    }
    tapeBand(-110, 520, 560, 30, 56, 'CRIME SCENE  •  DO NOT CROSS  •', { scroll: -lt * 30, seed: 1712 });
    camEnd();
    cutFlash(t, lt);
    flash(.35 * flashAt(lt, slap, .07));
    captionStyle({ color: PAL.blue });
  });

  // ---------- V4.4 (vertical): the WELCOME banner unrolls down the frame; GREG and his party horn below it ----------
  vshot('V4.4', (p, lt, d, t) => {
    bg(YEL);
    cam(t, lt, { shake: .7, zoom: 1 + .04 * p });
    rays(540, 680, 22, alpha(PAL.pink, .55), -lt * .6);
    halftone(FULL, RED, { cell: 16, dot: .2, op: .18 });
    // pennant garland across the top
    const gl = []; for (let i = 0; i <= 16; i++) { const u = i / 16; gl.push([-30 + u * 1140, 236 + Math.sin(u * Math.PI) * 56]); }
    marker(gl, INK, 4, { rough: 0 });
    for (let i = 0; i < 15; i++) {
      const u = (i + .5) / 15, x = -30 + u * 1140, y = 236 + Math.sin(u * Math.PI) * 56, k = popK(lt, i * .012, .1);
      if (k <= 0) continue;
      ctx.save(); ctx.translate(x, y); ctx.rotate(Math.sin(lt * 9 + i) * .12); ctx.scale(1, backOut(k));
      scrap([[-32, 0], [32, 0], [0, 70]], [RED, PAL.blue, PAL.pink, PAL.mint, PAL.white][i % 5], { torn: .6, seed: 1940 + i, ink: INK, sw: 3, shadow: [3, 4] });
      ctx.restore();
    }
    // the banner: hangs from its rod and unrolls down the frame, the words slamming in as the roller passes them
    const top = 392, uk = easeOut(clamp(lt / .34)), bot = lerp(top + 34, 992, uk), BL = 150, BR = 930;
    scrap(rectPts(BL, top, BR - BL, bot - top), PAL.white, { torn: 1.2, seed: 1975, shadow: [10, 14], tone: { color: PAL.pink, cell: 14, dot: .16, op: .35 } });
    ctx.save(); tracePath(rectPts(BL, top, BR - BL, bot - top)); ctx.clip();
    ctx.fillStyle = RED; ctx.fillRect(BL + 14, top + 12, BR - BL - 28, 10); ctx.fillRect(BL + 14, 962, BR - BL - 28, 10);
    const lines = [['WELCOME', 472, 104, 404], ['TO THE', 584, 80, 407], ['AGI', 736, 180, 411], ['ERA!', 890, 122, 415]];
    for (const [w, y, size, seed] of lines) shout(w, 540, y, size, { seed, maxW: 740, pop: clamp((bot - y) / 100) * 1.3, rot: (hash(seed) - .5) * .05 });
    ctx.restore();
    scrap(rrPts(BL - 34, top - 24, BR - BL + 68, 40, 18), '#8A5A3B', { torn: .6, seed: 1976, ink: INK, sw: 3, shadow: [4, 6] });
    scrap(rrPts(BL - 26, bot - 20, BR - BL + 52, 42, 20), PAL.cream, { torn: .6, seed: 1977, ink: INK, sw: 3, shadow: [5, 7], shade: true, shadeOp: .2 });
    marker([[BL - 10, top - 6], [540, top - 150], [BR + 10, top - 6]], INK, 4, { rough: 0 });
    // balloons bobbing up the left side (one of them a little early: GPT-6)
    [[180, 1095, PAL.blue, 'GPT-6', 1], [330, 1215, RED, '', 2], [110, 1300, PAL.pink, '', 3]].forEach(([bx, by, c, lab, i]) => {
      const yy = by - lt * 40 + Math.sin(lt * 4 + i) * 14;
      marker([[bx, yy + 112], [bx + Math.sin(lt * 3 + i) * 20, yy + 520]], INK, 3, { rough: 1 });
      scrap(ellPts(bx, yy, 92, 112, 30), c, { torn: 1, seed: 1960 + i, ink: INK, sw: 4, shade: true, shadeOp: .2 });
      ctx.fillStyle = 'rgb(255 255 255 / .45)'; tracePath(ellPts(bx - 34, yy - 44, 18, 30, 12, .4)); ctx.fill();
      if (lab) txt(lab, bx, yy, 44, PAL.white, { font: 'anton', stroke: INK, sw: 6 });
    });
    // GREG, party hat on, blowing his horn on every beat
    const gx = 815, gy = 1650, gs = 57, b = pulse(t, 5);
    person(gx, gy, gs, { top: 'tee', topCol: PAL.blue, hair: 'short', hairCol: '#5A3A22', skin: SKINS[0], eyes: 'happy', mouth: 'o', aL: -.9, aR: 1.15 + b * .3, dy: -b * .4, seed: 340 });
    const headY = gy - b * .4 * gs - 8.9 * gs;
    helloTag('GREG', gx - 1.15 * gs, gy - b * .4 * gs - 7.35 * gs, .4 * gs, -.12);
    scrap([[gx - .9 * gs, headY - .95 * gs], [gx + .15 * gs, headY - 3.4 * gs], [gx + .9 * gs, headY - .75 * gs]], PAL.pink, { torn: .5, ink: INK, sw: 3, tone: { color: YEL, cell: 12, dot: .3, op: .9 }, seed: 1970 });
    scrap(ellPts(gx + .15 * gs, headY - 3.45 * gs, 16, 16, 10), YEL, { torn: .3, ink: INK, sw: 2, shadow: false });
    const bph = frac(bpOf(t)), ext = bph < .4 ? 1 - .15 * Math.sin(bph / .4 * Math.PI) : lerp(1, .1, ease((bph - .4) / .45)), mx = gx - .25 * gs, my = headY + .55 * gs, L = 330;
    const hornPts = []; let hx = mx - 26, hy = my, ha = Math.PI + .3;
    hornPts.push([hx, hy]);
    for (let i = 1; i <= 28; i++) { const u = i / 28; ha -= (1 - ext) * u * .75; hx += Math.cos(ha) * L / 28 * (.35 + .65 * ext); hy += Math.sin(ha) * L / 28 * (.35 + .65 * ext); hornPts.push([hx, hy]); }
    scrap([[mx + 6, my - 9], [mx - 30, my - 14], [mx - 30, my + 14], [mx + 6, my + 9]], PAL.white, { torn: .3, ink: INK, sw: 3, shadow: false });
    marker(hornPts, INK, 40, { rough: 0 });
    for (let i = 0; i < 28; i++) marker([hornPts[i], hornPts[i + 1]], i % 4 < 2 ? RED : PAL.white, 31, { rough: 0 });
    const [ex, ey] = hornPts[28];
    scrap(burstPts(ex, ey, 26 + 14 * ext, 9, .45), YEL, { torn: .3, ink: INK, sw: 2, shadow: false });
    if (ext > .8) { actionLines(ex, ey, 50, 120, 8, INK, 5, 9); txt('TOOT!', ex - 20, ey - 90, 56, RED, { font: 'marker', rot: -.2, stroke: PAL.white, sw: 6 }); }
    burstBits(540, 700, lt - .02, 70, 1980, { v: 1400, g: 1100, size: 13 });
    confettiFall(lt, 60, 1990);
    camEnd();
    cutFlash(t, lt);
  });

  // ---------- V4.5 (vertical): the spike shoots up out of the whirlpool, off the top of the frame… and bursts; ∞ ----------
  vshot('V4.5', (p, lt, d, t, sg) => {
    const boom = hitAt(sg, d, 1, .45), k = clamp(lt / boom), after = lt - boom;
    bg(lt < boom ? '#0F1630' : '#120505');
    cam(t, lt, { shake: lt < boom ? .4 + k : 1.3, zoom: lt < boom ? 1 + k * .06 : 1.05 - .05 * clamp(after / .6), cy: lt < boom ? 960 - k * 40 : 960, hits: [[boom, 30]] });
    const cx = 540, cy = 1060, BY = 640;
    if (lt >= boom) rays(cx, BY, 16, BLOOD, after * .8);
    halftone(FULL, lt < boom ? PAL.blue : RED, { cell: 20, dot: .2, op: .5, multiply: false });
    if (lt < boom) {
      const ang = lt * (4 + 18 * k * k);
      scrap(ellPts(cx, cy, 470, 210, 48), '#1F4FA0', { torn: 3, seed: 2001, shadow: false });
      const cols = [PAL.sky, PAL.white, PAL.blue, PAL.mint, PAL.sky];
      for (let arm = 0; arm < 5; arm++) {
        const pts = [];
        for (let i = 0; i <= 40; i++) { const u = i / 40, rr = 450 * (1 - u) ** (1 + k * 1.5) + 6, a = ang + arm / 5 * TAU + u * (4 + k * 8); pts.push([cx + Math.cos(a) * rr, cy + Math.sin(a) * rr * .45]); }
        marker(pts, cols[arm], 30 - arm * 3, { rough: 2, smooth: true });
      }
      // the spike: |u| heading for infinity, up and out of the top of the frame
      const hgt = 30 + 1500 * k ** 3.5;
      const sp = []; for (let i = 0; i <= 14; i++) { const u = i / 14; sp.push([cx - (1 - u) ** 1.5 * 80 + Math.sin(u * 9 + lt * 30) * 6, cy - u * hgt]); }
      for (let i = 14; i >= 0; i--) { const u = i / 14; sp.push([cx + (1 - u) ** 1.5 * 80 + Math.sin(u * 9 + lt * 30 + 1) * 6, cy - u * hgt]); }
      scrap(sp, PAL.sky, { torn: 1, seed: 2002, ink: INK, sw: 4, shade: PAL.blue, shadeOp: .5 });
      if (k > .5) actionLines(cx, cy - hgt, 40, 160, 12, YEL, 6, 5);
    } else {
      const bk = easeOut(clamp(after / .12));
      scrap(burstPts(cx, BY, 560 * bk, 18, .62), RED, { torn: 4, seed: 2010, ink: INK, sw: 6 });
      scrap(burstPts(cx, BY, 400 * bk, 14, .6, .3), YEL, { torn: 3, seed: 2011, shadow: false });
      for (let i = 0; i < 40; i++) {
        const R = j => hash2(2020 + i, j), a = R(1) * TAU, v = 900 + R(2) * 1100;
        drop(cx + Math.cos(a) * v * after, BY + Math.sin(a) * v * after + 1000 * after * after, 14 + R(3) * 16, a + Math.PI, [PAL.sky, PAL.blue, PAL.white][i % 3]);
      }
      const ik = backOut(popK(lt, boom + .02, .2), 2.2);
      ctx.save(); ctx.translate(cx, BY); ctx.scale(ik, ik); ctx.rotate(jit(.03));
      infinity(0, 0, 260, 72, INK); infinity(0, 0, 260, 46, PAL.white);
      ctx.restore();
      shout('BLOW-UP!', cx, 1005, 104, { pop: popK(lt, boom + .1, .3) * 1.3, seed: 2015, rot: -.05, jolt: 3, maxW: 820 });
    }
    // the blow-up plot, top left
    ctx.save(); ctx.translate(110, 420); ctx.rotate(-.05);
    chart(0, 0, 260, 190, { fn: u => .06 / (1.06 - u) - .057, k: lt < boom ? k : 1, col: RED, lw: 8, grid: false });
    txt('BLOW-UP TIME', 130, 228, 30, PAL.white, { font: 'marker' });
    ctx.restore();
    // the "(yet)" sticky from V3.12 flutters past… then tears in two, and the halves fall away down the frame
    if (lt < boom) note('(yet)', lerp(-160, 640, lt / boom), 790 + Math.sin(lt * 9) * 30, 210, 180, YEL, Math.sin(lt * 7) * .35, 66);
    else for (const side of [-1, 1]) {
      const x = 640 + side * (20 + after * 360), y = 790 - after * 380 + 1900 * after * after;
      ctx.save(); ctx.translate(x, y); ctx.rotate(side * after * 4);
      tracePath(side < 0 ? rectPts(-140, -140, 140 + jit(8), 280) : rectPts(jit(8), -140, 140, 280)); ctx.clip();
      note('(yet)', 0, 0, 210, 180, YEL, 0, 66); ctx.restore();
    }
    if (lt >= boom && after < .5) txt('RIP', 640, 650 - after * 80, 56, PAL.white, { font: 'marker', rot: -.15, alpha: 1 - clamp((after - .3) / .2) });
    const lk = popK(lt, boom + .15, .18);
    if (lk > 0) {
      ctx.save(); ctx.translate(820, 1175); ctx.rotate(.12); const s = 1.1 * backOut(lk, 2); ctx.scale(s, s);
      scrap(ellPts(0, 0, 118, 118, 36), PAL.white, { torn: 1, seed: 2030, ink: INK, sw: 6 });
      ctx.strokeStyle = INK; ctx.lineWidth = 3; ctx.beginPath(); ctx.arc(0, 0, 100, 0, TAU); ctx.stroke();
      marker([[-46, -62], [0, 34], [46, -62]], INK, 15, { rough: 0 }); marker([[-28, -22], [28, -22]], INK, 13, { rough: 0 });
      txt('LEAN ✔', 0, 68, 34, PAL.green, { font: 'archivo' });
      ctx.restore();
    }
    camEnd();
    cutFlash(t, lt);
    flash(.85 * flashAt(lt, boom, .1));
    captionStyle({ color: lt < boom ? PAL.blue : RED });
  });

  // ---------- V4.6 (vertical): the photo finish, two lanes stacked; the magnifier scans the line; 12:00:00 ----------
  vshot('V4.6', (p, lt, d, t, sg) => {
    const fin = hitAt(sg, d, 1, .3), watch = hitAt(sg, d, 2, .55), fl = Math.min(lt, fin), after = lt - fin;
    bg('#231A22');
    const zk = lt < fin ? 0 : easeOut(clamp(after / .35)), FX = 770;
    cam(t, lt, { shake: .8, zoom: 1 + .14 * zk, cx: lerp(540, FX - 90, zk), cy: lerp(960, 930, zk), hits: [[fin, 14], [watch, 8]] });
    // the stands, with camera flashes
    halftone(rectPts(-400, -400, W + 800, 920), '#4A3A48', { cell: 26, dot: .3, op: 1, multiply: false });
    for (let i = 0; i < 30; i++) { const on = hash2(i, Math.floor(t * 10)) > .8; if (on) scrap(burstPts(hash(i * 7 + 2) * W, 60 + hash(i * 3 + 1) * 400, 16, 8, .4), PAL.white, { torn: 0, shadow: false }); }
    // the track: two lanes stacked up the frame, the far one above the near one
    const TOP = 520;
    scrap(rectPts(-400, TOP, W + 800, H + 400), '#C9412F', { torn: 1, shadow: false, seed: 2050 });
    halftone(rectPts(-400, TOP, W + 800, H + 400), INK, { cell: 12, dot: .18, op: .25 });
    for (const ly of [TOP, 890, 1250, 1680]) { ctx.fillStyle = PAL.white; ctx.fillRect(-400, ly - 5, W + 800, 10); }
    for (let r = 0; r < 50; r++) for (let c = 0; c < 2; c++) { ctx.fillStyle = (r + c) % 2 ? INK : PAL.white; ctx.fillRect(FX - 30 + c * 30, TOP + r * 30, 30, 30); }
    const run = fl / fin, stride = fl * 3.2;
    const bx = lerp(140, FX - 75, easeOut(run)), px = lerp(260, FX - 48, easeOut(run));
    bot(bx, 870, 33, { walk: stride, rot: .12 + .18 * run, col: '#B9C3D0', eyes: lt < fin ? 'angry' : 'x', aL: -1.6 + Math.sin(stride * TAU) * .8, aR: -.6 - Math.sin(stride * TAU) * .8, seed: 520 });
    bib(bx + 54, 870 - 5.4 * 33, 196, 80, 'OPENAI', .12 + .18 * run);
    const pose = (ph, extra = 0) => ({ walk: stride + ph, rot: .12 + .2 * run + extra, aL: .2 + Math.sin((stride + ph) * TAU) * .7, aR: -.4 - Math.sin((stride + ph) * TAU) * .7, eyes: lt < fin ? 'angry' : 'wide', mouth: lt < fin ? 'grin' : 'O' });
    person(px - 175, 1222, 37, { ...pose(.3), top: 'tee', topCol: '#57068C', hair: 'short', hairCol: '#2A2018', skin: SKINS[1], seed: 350 });
    person(px, 1222, 37, { ...pose(0, .05), top: 'tee', topCol: PAL.clawd, hair: 'curly', hairCol: '#1E1612', skin: SKINS[3], seed: 351 });
    bib(px - 160, 1222 - 5.6 * 37, 136, 70, 'NYU', .2);
    bib(px + 34, 1222 - 5.6 * 37, 240, 70, 'ANTHROPIC', .25);
    // the verdict: a magnifier running up and down the line, from one lunge to the other
    if (lt >= fin) {
      const lk = easeOut(clamp(after / .25)), ly = lerp(660, 1030, .5 + .5 * Math.sin(after * 6 - 1.2));
      ctx.save(); ctx.globalAlpha = lk;
      marker([[FX + 74, ly + 74], [FX + 200, ly + 200]], INK, 32, { rough: 0 }); marker([[FX + 74, ly + 74], [FX + 200, ly + 200]], '#6B4A2A', 21, { rough: 0 });
      ctx.fillStyle = 'rgb(200 230 255 / .35)'; tracePath(ellPts(FX, ly, 110, 110, 32)); ctx.fill();
      ctx.strokeStyle = INK; ctx.lineWidth = 16; ctx.stroke(); ctx.strokeStyle = '#B8B8C0'; ctx.lineWidth = 8; ctx.stroke();
      ctx.fillStyle = 'rgb(255 255 255 / .6)'; tracePath(ellPts(FX - 42, ly - 46, 26, 12, 12, -.7)); ctx.fill();
      ctx.restore();
      ransom('?', 935, 700, 120, { pop: popK(lt, fin + .1, .2) * 1.3, seed: 61 });
    }
    camEnd();
    // after the flash the frame is a photo-finish print: a white border, and the label in its wide bottom margin
    if (lt >= fin) {
      const bk = easeOut(popK(lt, fin, .12)), bw = 30 * bk;
      ctx.save(); ctx.fillStyle = PAL.white; ctx.fillRect(0, 0, W, bw); ctx.fillRect(0, H - bw * 3, W, bw * 3); ctx.fillRect(0, 0, bw, H); ctx.fillRect(W - bw, 0, bw, H);
      ctx.strokeStyle = INK; ctx.lineWidth = 3; ctx.strokeRect(bw, bw, W - 2 * bw, H - bw * 4); ctx.restore();
      txt('PHOTO FINISH  •  12:00:00.00', 48, H - 45 + (1 - bk) * 60, 34, INK, { font: 'typewriter', align: 'left' });
    }
    const wk = popK(lt, watch, .18);
    if (wk > 0) {
      ctx.save(); ctx.translate(215, 520); ctx.rotate(-.1 + jit(.02)); const s = backOut(wk, 2.2); ctx.scale(s, s);
      stopwatch(0, 0, 128, '12:00:00', after * 14);
      ctx.restore();
    }
    cutFlash(t, lt);
    flash(.9 * flashAt(lt, fin, .12));
  });

  // ---------- V4.7 (vertical): the track from above: the PACE CAR at the head of the grid, DARIO up on its roof ----------
  vshot('V4.7', (p, lt, d, t) => {
    bg(YEL);
    cam(t, lt, { shake: .7, zoom: 1.02 + .03 * p });
    halftone(FULL, RED, { cell: 18, dot: .2, op: .25 });
    // the track runs up the frame and slides down it slowly: this is the pace lap
    const TL = 150, TR = 930, scroll = lt * 240;
    scrap(rectPts(TL, -400, TR - TL, H + 800), '#2E2B33', { torn: 1, shadow: false, seed: 2101 });
    halftone(rectPts(TL, -400, TR - TL, H + 800), PAL.white, { cell: 10, dot: .12, op: .25 });
    for (const [x0, w] of [[TL - 34, 34], [TR, 34]]) for (let i = -2; i < 26; i++) { ctx.fillStyle = i % 2 ? RED : PAL.white; ctx.fillRect(x0, i * 90 + scroll % 180 - 90, w, 90); }
    for (let i = -2; i < 12; i++) { ctx.fillStyle = PAL.white; ctx.fillRect(536, i * 220 + (scroll * 1.6) % 220 - 110, 10, 120); }
    // the grid behind it, bunched up nose to tail down the frame, revving to go (the caption sits in the gap between the rows)
    [[400, 1240, PAL.blue, 6], [680, 1265, PAL.green, 4], [395, 1745, PAL.purple, 7], [690, 1775, RED, 9], [410, 2120, PAL.teal, 3], [680, 2140, PAL.pink, 8]].forEach(([x, y, c, n], i) => {
      const nudge = Math.max(0, Math.sin(lt * 9 + i * 1.7)) * 26;
      carTop(x + jit(3), y - nudge, 33, c, { race: true, num: n, seed: 1440 + i * 3, stripe: PAL.white, rot: Math.sin(lt * 7 + i) * .03 });
      for (let j = 0; j < 3; j++) { const pk = frac(lt * 3 + j / 3 + i * .2); scrap(ellPts(x + (j - 1) * 30, y - nudge + 4.6 * 33 + pk * 120, 18 + pk * 30, 14 + pk * 24, 12), '#8C8A92', { torn: 1.5, shadow: false, op: 1 - pk, seed: 2110 + j }); }
      if (i < 2) txt(i ? 'VROOM' : 'GRR!', x + (i ? 160 : -165), y - 60 + Math.sin(lt * 40 + i) * 5, 54, INK, { font: 'marker', rot: i ? .15 : -.15, stroke: PAL.white, sw: 7 });
    });
    // the pace car, and DARIO standing up on its roof, waving the flag
    const PX = 540, PY = 850, PS = 58, lb = Math.floor(t * 8) % 2;
    carTop(PX + jit(1.5), PY, PS, PAL.clawd, { seed: 1410 });
    txt('PACE CAR', PX, PY + 3.25 * PS, .72 * PS, PAL.white, { font: 'archivo', stroke: INK, sw: 5, maxW: 3.2 * PS });
    scrap(rectPts(PX - 1.45 * PS, PY - .55 * PS, 2.9 * PS, .5 * PS), INK, { torn: .3, shadow: false });
    for (const sd of [-1, 1]) { scrap(rectPts(PX + (sd < 0 ? -1.4 : .05) * PS, PY - .5 * PS, 1.35 * PS, .4 * PS), (sd < 0) === !!lb ? YEL : RED, { torn: .3, shadow: false }); glow(PX + sd * .7 * PS, PY - .3 * PS, 140, (sd < 0) === !!lb ? YEL : RED, .8); }
    const wave = Math.sin(bpOf(t) * Math.PI) * .3 + .58, DS = 38, DY = PY + .9 * PS;
    person(PX, DY, DS, {
      name: 'DARIO', top: 'jacket', topCol: '#2B3A55', hair: 'short', hairCol: '#2A1E16', skin: SKINS[1], eyes: 'dot', mouth: 'O', aR: -.5, aL: .8 + Math.sin(bpOf(t) * Math.PI) * .15, lookX: -.3, seed: 360,
      holdL: s => {
        ctx.save(); ctx.scale(-1, 1); ctx.rotate(wave);
        marker([[0, .3 * s], [0, -6.4 * s]], '#6B5B4B', .35 * s, { rough: 0 });
        const fp = []; for (let j = 0; j <= 10; j++) { const u = j / 10; fp.push([u * 5.5 * s, -6.4 * s + Math.sin(u * 5 - lt * 14) * .5 * s * u]); }
        for (let j = 10; j >= 0; j--) { const u = j / 10; fp.push([u * 5.5 * s, -2.8 * s + Math.sin(u * 5 - lt * 14) * .5 * s * u]); }
        scrap(fp, YEL, { torn: .5, ink: INK, sw: .1 * s, shadow: [.2 * s, .3 * s], seed: 2120 });
        ctx.restore();
      },
    });
    bubble('PACE THE FRONTIER!', 805, 590, { size: 50, maxW: 300, tail: [PX + 40, DY - 8.5 * DS], pop: popK(lt, .25, .2), rot: -.05 });
    camEnd();
    cutFlash(t, lt);
    captionStyle({ color: RED });
  });

  // ---------- V4.8 (vertical): SAM and ELON at full height, toasting high between them; CLINK!, then both startled ----------
  vshot('V4.8', (p, lt, d, t, sg) => {
    const clink = hitAt(sg, d, 1, .3), after = lt - clink;
    bg(RED);
    const SPLIT = [[600, -400], [W + 400, -400], [W + 400, H + 400], [480, H + 400]];
    ctx.fillStyle = INK; tracePath(SPLIT); ctx.fill();
    cam(t, lt, { shake: .8, zoom: 1.02 + .03 * p, hits: [[clink, 14]] });
    halftone(rectPts(-400, -400, 940, H + 800), INK, { cell: 18, dot: .2, op: .25 });
    halftone(rectPts(540, -400, W, H + 800), RED, { cell: 18, dot: .2, op: .35, multiply: false });
    const CX = 540, CY = 546;
    if (lt >= clink) {
      ctx.save(); tracePath([[-400, -400], [600, -400], [480, H + 400], [-400, H + 400]]); ctx.clip(); rays(CX, CY, 16, BLOOD, after * .6); ctx.restore();
      ctx.save(); tracePath(SPLIT); ctx.clip(); rays(CX, CY, 16, '#4A1016', after * .6); ctx.restore();
    }
    const inK = easeOut(clamp(lt / (clink * .85)));
    const sx = lerp(-200, 300, inK), ex = lerp(W + 200, 780, inK), s = 72;
    const armS = lt < clink ? lerp(-1.1, 1.12, easeOut(clamp(lt / clink))) : 1.12 + .04 * pulse(t, 6);
    const surprised = lt >= clink && after < .5, fac = lt < clink ? { eyes: 'angry', mouth: 'flat' } : surprised ? { eyes: 'wide', mouth: 'O' } : { eyes: 'happy', mouth: 'grin' };
    const flute = tilt => sc => {
      ctx.save(); ctx.rotate(tilt);
      scrap(ellPts(0, .45 * sc, .5 * sc, .14 * sc, 12), PAL.white, { torn: .2, shadow: false, ink: INK, sw: .05 * sc });
      marker([[0, .45 * sc], [0, -1.1 * sc]], PAL.white, .14 * sc, { rough: 0 });
      scrap([[-.45 * sc, -3.4 * sc], [.45 * sc, -3.4 * sc], [.28 * sc, -1.2 * sc], [-.28 * sc, -1.2 * sc]], 'rgb(255 255 255 / .55)', { torn: .2, shadow: false, ink: INK, sw: .06 * sc });
      scrap([[-.4 * sc, -2.8 * sc], [.4 * sc, -2.8 * sc], [.28 * sc, -1.25 * sc], [-.28 * sc, -1.25 * sc]], '#F5D46A', { torn: .2, shadow: false });
      for (let i = 0; i < 3; i++) { const by = -1.4 * sc - frac(lt * 1.5 + i / 3) * 1.3 * sc; tracePath(ellPts(Math.sin(i * 2) * .15 * sc, by, .06 * sc, .06 * sc, 8)); ctx.fillStyle = PAL.white; ctx.fill(); }
      ctx.restore();
    };
    const tilt = lt < clink ? 0 : .15;
    person(sx, 1500, s, { name: 'SAM', top: 'hoodie', topCol: '#8E8E98', hair: 'short', hairCol: '#6B4A2E', skin: SKINS[0], ...fac, lookX: 1, aR: armS, aL: -1.2, walk: lt < clink ? lt * 3 : undefined, hold: flute(tilt), seed: 370 });
    person(ex, 1500, s * 1.04, { name: 'ELON', top: 'tee', topCol: '#26242A', hair: 'short', hairCol: '#3A2A20', skin: SKINS[4], ...fac, lookX: -1, aL: armS, aR: -1.2, walk: lt < clink ? lt * 3 : undefined, holdL: flute(-tilt), seed: 371 });
    if (lt >= clink) {
      const ck = popK(lt, clink, .14);
      sticker('CLINK!', 262, 560, 104, YEL, { pop: ck, size: 44, rot: -.14, n: 14 });
      for (let i = 0; i < 6; i++) { const a = i / 6 * TAU + .3, rr = 140 + after * 300; scrap(starPts(CX + Math.cos(a) * rr, CY + Math.sin(a) * rr, 26 * (1 - clamp(after / .8)), .4, 4), PAL.white, { torn: .2, shadow: false }); }
      if (surprised) { txt('!?', 150, 680, 84, YEL, { font: 'anton', rot: -.2, stroke: INK, sw: 8 }); txt('!?', 935, 680, 84, YEL, { font: 'anton', rot: .2, stroke: INK, sw: 8 }); }
    }
    // tiny Clawd between their feet, jaw on the floor
    clawd(540, 1650, 16, { eyes: 'wide', mouth: 'O', aL: 1, aR: 1, dy: -Math.abs(Math.sin(lt * 10)) * .5 * (lt > clink ? 1 : 0) });
    camEnd();
    cutFlash(t, lt);
    flash(.4 * flashAt(lt, clink, .07), YEL);
    captionStyle({ color: PAL.blue });
  });

  // ---------- V4.9 (vertical): his post up top; TRUMP in the guardrail's gap below; the car bonks off his shins and flies off ----------
  vshot('V4.9', (p, lt, d, t, sg) => {
    const hit = hitAt(sg, d, 1, .45), after = lt - hit;
    bg('#120F1C');
    cam(t, lt, { shake: .9, zoom: 1.02, hits: [[hit, 24]] });
    halftone(rectPts(-400, -400, W + 800, 1600), PAL.purple, { cell: 24, dot: .15, op: .55, multiply: false });
    scrap(ellPts(150, 770, 56, 56, 30), YEL, { torn: 1, seed: 2200, shadow: false });
    // the valley far, far below: distant ridges and town lights
    const gx = 600, gy = 1185, gs = 52, beamY = gy - 7.1 * gs;
    const ridge = (y0, amp, seed, col) => { const pts = [[-400, gy + 40]]; for (let i = 0; i <= 20; i++) pts.push([-400 + i * (W + 800) / 20, y0 - hash(seed + i) * amp]); pts.push([W + 400, gy + 40]); scrap(pts, col, { torn: 1, shadow: false, seed }); };
    ridge(1005, 120, 2203, '#2A1E3A'); ridge(1070, 80, 2233, '#3A1C2E');
    for (let i = 0; i < 14; i++) scrap(ellPts(hash(i + 2250) * W, 1080 + hash(i + 2260) * 60, 4, 4, 6), Math.floor(t * 6 + i) % 3 ? YEL : '#FF8A2A', { torn: 0, shadow: false });
    // the guardrail at his arm height, with a gap where he stands
    for (const [x0, x1] of [[-400, gx - 4.2 * gs], [gx + 4.2 * gs, W + 400]]) {
      for (let x = x0 + 70; x < x1; x += 160) scrap(rectPts(x - 13, beamY, 26, gy - beamY + 10), '#7A7F88', { torn: .5, shadow: false, seed: 2210, ink: INK, sw: 2 });
      scrap(rectPts(x0, beamY - 30, x1 - x0, 60), '#B8BEC8', { torn: 1, seed: 2211, ink: INK, sw: 4, shade: true, shadeOp: .25 });
      ctx.fillStyle = 'rgb(28 26 31 / .35)'; ctx.fillRect(x0, beamY - 5, x1 - x0, 10);
    }
    // the road
    scrap(rectPts(-400, gy - 10, W + 800, 1200), '#34313B', { torn: 1, shadow: false, seed: 2201 });
    halftone(rectPts(-400, gy - 10, W + 800, 1200), PAL.white, { cell: 10, dot: .12, op: .2 });
    ctx.fillStyle = PAL.white; ctx.fillRect(-400, gy - 8, W + 800, 8);
    for (let i = -2; i < 10; i++) { ctx.fillStyle = YEL; ctx.fillRect(i * 200 - (lt * 700) % 200, 1560, 110, 12); }
    // the man: arms out, chest out, eyes shut, very pleased
    const bonk = lt >= hit ? Math.exp(-after * 7) : 0, rot9 = bonk * .03 * Math.sin(after * 40);
    person(gx, gy, gs, { ...TRUMP, eyes: 'closed', mouth: 'grin', aL: .02 + jit(.015), aR: .02 + jit(.015), rot: rot9, seed: 380 });
    trumpHair(gx, gy, gs, rot9);
    longTie(gx, gy, gs);
    sash(gx, gy, gs, 'HIGH IQ!');
    helloTag('DONALD', gx - 1.3 * gs, gy - 6.75 * gs, .32 * gs, -.1);
    if (lt >= hit) { const k = popK(lt, hit + .08, .12); scrap(starPts(gx + 70, gy - 9 * gs, 30 * backOut(k), .3, 4, lt * 3), PAL.white, { torn: .2, ink: INK, sw: 3, shadow: false }); txt('UNBOTHERED', 820, 735, 46, YEL, { font: 'marker', rot: .12, stroke: INK, sw: 6, alpha: k }); }
    // the car fishtails in along the road, bonks off his shins… and goes flying, up and out of the frame
    const s1 = 23, rest = gx - 6.3 * s1 - 30;
    let cx1, cy1 = 1205, rot1;
    if (lt < hit) { const u = lt / hit; cx1 = lerp(-320, rest, u ** 1.4); rot1 = Math.sin(lt * 22) * .12; cy1 = lerp(1240, 1205, u); }
    else { cx1 = rest - after * 520; cy1 = 1205 - after * 2500 + 1100 * after * after; rot1 = -after * 9; }
    carSide(cx1, cy1, s1, PAL.blue, { rot: rot1, spin: lt * 14, seed: 1431 });
    if (lt < hit) for (let i = 0; i < 4; i++) marker([[cx1 - 7 * s1 - i * 30, cy1 - 20 - i * 18], [cx1 - 11 * s1 - i * 50, cy1 - 20 - i * 18]], PAL.white, 5, { rough: 0, alpha: .7 });
    if (lt >= hit) sticker('BONK!', 300, 1035, 104, YEL, { pop: popK(lt, hit, .12), size: 48, rot: -.15 });
    // another one swerves by in the near lane
    { const u = clamp(lt / d), s = 30; carSide(lerp(W + 400, -500, u), 1720 + Math.sin(lt * 18) * 6, s, PAL.green, { flip: true, rot: Math.sin(lt * 14) * .1, spin: lt * 12, seed: 1430 }); }
    // the post, up top
    const pk = popK(lt, .06, .2);
    if (pk > 0) { ctx.save(); ctx.translate(0, (1 - easeOut(pk)) * -500); postCard(540, 378, 920, { user: 'Donald J. Trump', handle: '@realDonaldTrump', size: 40, text: 'The only control or "guardrails" that AI needs is a STRONG AND SMART (High IQ!) PRESIDENT.', rot: -.02, likes: '88K' }); ctx.restore(); }
    camEnd();
    cutFlash(t, lt);
    flash(.45 * flashAt(lt, hit, .07));
    captionStyle({ color: PAL.purple });
  });

  // ---------- V4.10 (vertical): the stained-glass window above; BERNIE and STEVE side by side in the pew below ----------
  vshot('V4.10', (p, lt, d, t, sg) => {
    const glance = hitAt(sg, d, 1, .3), sing = hitAt(sg, d, 2, .55);
    bg('#3A1418');
    cam(t, lt, { shake: .5, zoom: 1.02 + .04 * p, cy: 940 });
    halftone(FULL, '#FF8A2A', { cell: 22, dot: .15, op: .35, multiply: false });
    stainedGlass(540, 690, .82);
    glow(540, 700, 700, YEL, .35);
    ctx.save(); ctx.globalCompositeOperation = 'screen'; ctx.fillStyle = alpha(YEL, .12);
    tracePath([[330, 760], [750, 760], [1060, 1500], [20, 1500]]); ctx.fill(); ctx.restore();
    const s = 59, gy = 1478, bx = 305, stx = 775;
    const look = lt < glance ? 0 : lt < sing ? 1 : 0;
    const singing = lt >= sing, mo = singing ? (frac(bpOf(t) * 2) < .5 ? 'O' : 'o') : 'flat';
    const stiff = jit(.008);
    person(bx, gy, s, { top: 'coat', topCol: '#7A5E44', hair: 'short', hairCol: '#E6E2DA', skin: SKINS[4], glasses: true, eyes: singing ? 'closed' : 'dot', lookX: look, mouth: mo, aL: -1.42, aR: -1.42, sweat: lt >= glance && !singing, rot: stiff, seed: 390 });
    person(stx, gy, s, { top: 'jacket', topCol: '#5E6337', hair: 'side', hairCol: '#9A948A', skin: SKINS[0], eyes: singing ? 'closed' : 'dot', lookX: -look, mouth: mo, aL: -1.42, aR: -1.42, sweat: lt >= glance && !singing, rot: -stiff, seed: 391 });
    for (const [c, k] of [[PAL.blue, 1], [INK, .72], [PAL.white, .45]]) scrap([[stx - .55 * s * k - .2 * s, gy - 7.7 * s], [stx, gy - 7.7 * s + 1.9 * s * k], [stx + .55 * s * k + .2 * s, gy - 7.7 * s]], c, { torn: .3, shadow: false });
    helloTag('BERNIE', bx - .1 * s, gy - 6.75 * s, .36 * s, -.04);
    helloTag('STEVE', stx + .1 * s, gy - 6.75 * s, .36 * s, .05);
    pewRow(150, 930, 1212);
    const hy = 1178 + (singing ? -8 * pulse(t, 5) : 0);
    hymnal(bx, hy, 214, 132, -.04 + stiff); hymnal(stx, hy, 214, 132, .04 - stiff);
    mitten(bx - 110, hy + 18, 52, -.3); mitten(bx + 110, hy + 18, 52, .3);
    for (const side of [-1, 1]) scrap(ellPts(stx + side * 108, hy + 22, 25, 25, 12), SKINS[0], { torn: .3, ink: INK, sw: 2, shadow: false });
    // the hymn rises up the frame, to the window
    if (singing) for (let i = 0; i < 6; i++) { const k = frac(lt * 1.4 + i / 6); noteGlyph(540 + (i % 2 ? 1 : -1) * (40 + k * 90) + Math.sin(k * 8 + i) * 20, 960 - k * 520, 38, [YEL, PAL.white][i % 2]); }
    if (lt >= glance && !singing) txt('...', 540, 905, 96, PAL.white, { font: 'anton', alpha: popK(lt, glance, .1) });
    // the pew in front, at the foot of the frame: the congregation, turned round to stare at the odd couple behind them
    for (const [i, x, hair, hc, sk] of [[0, 175, 'bun', '#6B4A2A', 2], [1, 545, 'bald', '#3A2A20', 4], [2, 915, 'curly', '#2A2320', 1]]) {
      const turn = popK(lt, glance * .6 + i * .07, .2);
      person(x, 2270 - turn * 40, 60, { hair, hairCol: hc, skin: SKINS[sk], top: 'sweater', topCol: ['#5E3A6B', '#3A5E6B', '#6B5E3A'][i], eyes: turn > .5 ? 'wide' : 'dot', lookX: turn > .5 ? (x < 540 ? .8 : x > 540 ? -.8 : 0) : 0, mouth: turn > .5 ? 'o' : 'flat', aL: -1.4, aR: -1.4, seed: 395 + i });
    }
    scrap(rrPts(-60, 1838, W + 120, 62, 18), '#8A5530', { torn: 1, seed: 1783, ink: INK, sw: 4, shade: true, shadeOp: .2 });
    scrap(rectPts(-60, 1895, W + 120, 120), '#6A3E22', { torn: 1, seed: 1784, ink: INK, sw: 4 });
    camEnd();
    cutFlash(t, lt);
    captionStyle({ color: PAL.purple });
  });

  // ---------- V4.11 (vertical): the recursion as a tower: each Clawd hammers up at the plank over its head, where the next, smaller
  // one is being built, and so on up and out of the top of the frame; they come alive on the beats, then in a ripple to the top;
  // the finished ones ride a conveyor out along the foot of the frame ----------
  vshot('V4.11', (p, lt, d, t, sg) => {
    const pieT = hitAt(sg, d, 1, .25), alive1 = hitAt(sg, d, 2, .45), alive2 = hitAt(sg, d, 3, .62), alive3 = hitAt(sg, d, 4, .8);
    bg(YEL);
    cam(t, lt, { shake: .8, zoom: 1.02 + .03 * p });
    halftone(FULL, RED, { cell: 18, dot: .18, op: .22 });
    // the tower: L0 on the workshop's floor; each next one ×.73, on a plank at the last one's raised hammer, nine and a bit of its
    // height up; it runs on out of the top of the frame
    const FY = 1290, TX = 275, chain = [];
    for (let i = 0, y = FY, u = 38; i < 12 && y > -200; i++) {
      chain.push({ x: TX, y, u, sd: i % 2 ? -1 : 1, alive: i === 0 ? -1 : i === 1 ? alive1 : i === 2 ? alive2 : i === 3 ? alive3 : Math.min(d - .05, alive3 + (i - 3) * .06) });
      y -= 9.9 * u; u *= .73;
    }
    // the workshop's floor, its front edge a thick beam over the wall below
    scrap(rectPts(-60, FY, W + 120, 44), '#8A5A3B', { torn: 1, seed: 2309, ink: INK, sw: 4, shade: true, shadeOp: .25 });
    ctx.fillStyle = 'rgb(28 26 31 / .25)'; ctx.fillRect(-60, FY + 44, W + 120, 14);
    // the pie and the blueprint, on the right
    const pk = popK(lt, pieT, .2);
    pie(770, 600, 145, .26, { pop: backOut(pk, 2), label: pk > 0 ? '26%' : '' });
    txt("CLAUDE'S R&D,", 770, 795, 44, INK, { font: 'marker', maxW: 360 });
    txt('LED BY CLAUDE', 770, 843, 44, INK, { font: 'marker', maxW: 360 });
    card(780, 1075, 300, 230, '#2C5AA8', .05, { seed: 2300, torn: 1.5 });
    ctx.save(); ctx.translate(780, 1075); ctx.rotate(.05); ctx.strokeStyle = 'rgb(255 255 255 / .6)'; ctx.lineWidth = 2;
    for (let i = 1; i < 5; i++) { ctx.beginPath(); ctx.moveTo(-150 + i * 60, -115); ctx.lineTo(-150 + i * 60, 115); ctx.stroke(); }
    for (let i = 1; i < 4; i++) { ctx.beginPath(); ctx.moveTo(-150, -115 + i * 57); ctx.lineTo(150, -115 + i * 57); ctx.stroke(); }
    ctx.lineWidth = 4; ctx.strokeStyle = PAL.white; ctx.strokeRect(-26, -40, 52, 64); for (let i = 0; i < 3; i++) ctx.strokeRect(-26 + i * 8 - i * 4, -40 - 52 * (i + 1) * .5, 52 - i * 8, 26);
    txt('CLAUDE v.NEXT', 0, 82, 28, PAL.white, { font: 'marker' });
    ctx.restore();
    // the planks, each on a pair of brackets
    chain.forEach((c, i) => { if (i) { const pu = chain[i - 1].u, th = Math.max(5, .9 * c.u); scrap(rectPts(c.x - 6.3 * pu, c.y, 12.6 * pu, th), '#8A5A3B', { torn: .6, seed: 2310 + i, ink: INK, sw: Math.max(1.5, Math.min(3, c.u * .12)), shade: true, shadeOp: .2 }); for (const sd of [-1, 1]) marker([[c.x + sd * 5.6 * pu, c.y + th], [c.x + sd * 5.6 * pu, c.y + th + 2.4 * pu], [c.x + sd * 3.6 * pu, c.y + th]], '#6A4028', Math.max(2, .35 * pu), { rough: 0 }); } });
    const sparks = [];
    chain.forEach((c, i) => {
      const on = lt >= c.alive, bk = on ? popK(lt, c.alive, .15) : 0, next = chain[i + 1];
      const hammering = on && next;
      const rate = [2, 4, 4][i] ?? 8;
      const ph = frac(bpOf(t) * rate / 2), swing = hammering ? (ph < .2 ? lerp(.85, 1.42, easeIn(ph / .2)) : lerp(1.42, .85, ease((ph - .2) / .8))) : -.3;
      clawd(c.x, c.y, c.u, {
        flip: c.sd < 0,
        col: on ? PAL.clawd : '#C9B79C', dk: on ? PAL.clawdDk : '#9A8A70', eyes: on ? (i === 0 ? 'normal' : 'spark') : 'closed', lookX: hammering ? .4 : 0, lookY: hammering ? -1 : 0,
        hat: on && (i === 0 || bk > .3) ? 'hardhat' : undefined, mouth: on ? (hammering && ph < .2 ? 'grin' : 'smile') : 'none', aR: swing, aL: on ? .2 + pulse(t, 6) * .2 : -.3,
        dy: on ? -Math.sin(bk * Math.PI) * 1.2 : 0, shadow: i === 0,
      });
      if (hammering) {
        const hx = c.x + c.sd * (5 * c.u + 2 * c.u * Math.cos(swing)), hy = c.y - 4.9 * c.u - 2 * c.u * Math.sin(swing);
        hammer(hx, hy, c.u * .6, c.sd * (1.42 - swing) * 1.3);
        if (ph < .12 && c.u > 5) sparks.push([hx, next.y + Math.max(5, .9 * next.u) + 4, c.u]);
      }
      if (!on && i < 8) { ctx.save(); ctx.globalAlpha = .7; marker([[c.x - 5.5 * c.u, c.y - 8.6 * c.u], [c.x + 5.5 * c.u, c.y - 8.6 * c.u]], INK, Math.max(2, c.u * .22), { rough: 0 }); ctx.restore(); }
    });
    for (const [x, y, u] of sparks) { scrap(burstPts(x, y, 2.6 * u + 10, 10, .4), PAL.white, { torn: .3, ink: INK, sw: 3, shadow: false }); if (u > 14) txt(u > 30 ? 'BANG!' : 'bang', x + 2.6 * u + 50, y + 10, 18 + u * 1.2, RED, { font: 'anton', rot: -.2, stroke: PAL.white, sw: 5 }); }
    // the foot of the frame: finished Clawds in hard hats ride the conveyor out of the workshop
    const CY = 1790;
    scrap(rectPts(-60, CY, W + 120, 46), '#3A3D45', { torn: .8, seed: 2330, ink: INK, sw: 4, shadow: [6, 8] });
    ctx.fillStyle = '#5B6070'; for (let i = 0; i < 14; i++) { const bx = -60 + (((i * 90 + lt * 260) % 1260) + 1260) % 1260; ctx.fillRect(bx, CY + 6, 40, 8); }
    for (let i = 0; i < 9; i++) scrap(ellPts(i * 135 + 20, CY + 46, 22, 22, 12), '#23262E', { torn: .4, seed: 2331 + i, shadow: false, ink: INK, sw: 3 });
    for (let i = -1; i < 7; i++) {
      const x = ((i * 190 + lt * 260) % 1330 + 1330) % 1330 - 120;
      clawd(x, CY, 11, { hat: 'hardhat', eyes: hash(i + 2340) < .5 ? 'happy' : 'spark', mouth: 'smile', aL: .9 + pulse(t + i * .1, 6) * .3, aR: -.3, dy: -pulse(t + i * .13, 7) * .4, shadow: false });
    }
    camEnd();
    cutFlash(t, lt);
  });

  // ---------- V4.12 (vertical): the chat up top; jets climb the right side; the fist comes down on CANCEL; they turn back ----------
  vshot('V4.12', (p, lt, d, t, sg) => {
    const slam = hitAt(sg, d, 1, .45), verdict = hitAt(sg, d, 2, .7), after = lt - slam;
    bg('#2A0808');
    cam(t, lt, { shake: 1.4, zoom: 1.02, hits: [[slam, 30]] });
    const BX = 130, BYc = 270;
    ctx.save(); ctx.globalCompositeOperation = 'screen';
    for (const k of [0, Math.PI]) { const a = lt * 7 + k; ctx.fillStyle = alpha(RED, .28); tracePath([[BX, BYc], [BX + Math.cos(a - .22) * 2800, BYc + Math.sin(a - .22) * 2800], [BX + Math.cos(a + .22) * 2800, BYc + Math.sin(a + .22) * 2800]]); ctx.fill(); }
    ctx.restore();
    halftone(FULL, RED, { cell: 20, dot: .18, op: .5, multiply: false });
    // jets scramble up the right of the frame; after CANCEL they peel away and dive home
    for (let i = 0; i < 3; i++) {
      const t0 = .02 + i * .1, tt = lt - t0; if (tt < 0) continue;
      const hd0 = -1.62 - i * .05, v = 2000;
      let x = 1010 - i * 55, y = 1720 + i * 70, hd = hd0;
      const n = 24, dt = tt / n;
      for (let j = 0; j < n; j++) { const tj = t0 + j * dt; if (tj > slam) hd = hd0 + Math.PI * easeOut(clamp((tj - slam) / .45)) * (i % 2 ? -1 : 1); const acc = Math.min(1, (j * dt + .1) * 3); x += Math.cos(hd) * v * dt * acc; y += Math.sin(hd) * v * dt * acc; }
      jet(x, y, 27 - i * 2, hd, { flame: 1, col: ['#9AA2AF', '#8A93A0', '#A8B0BC'][i] });
    }
    // the chat window
    ctx.save(); ctx.translate(440, 640); ctx.rotate(-.04); ctx.scale(1.06, 1.06);
    scrap(rectPts(-350, -250, 700, 470), PAL.white, { torn: 1.5, seed: 2401, ink: INK, sw: 5, shadow: [10, 14] });
    scrap(rectPts(-350, -250, 700, 56), '#3A3A44', { torn: .5, seed: 2402, shadow: false });
    for (let i = 0; i < 3; i++) scrap(ellPts(-320 + i * 30, -222, 9, 9, 10), [RED, YEL, PAL.green][i], { torn: .1, shadow: false });
    txt('CHATBOT', 0, -221, 30, PAL.white, { font: 'archivo' });
    scrap(rrPts(40, -170, 280, 60, 20), PAL.sky, { torn: .8, seed: 2403, shadow: false });
    txt('status of ship?', 180, -140, 26, INK, { font: 'typewriter' });
    const ax = -280, ay = -30;
    for (let i = 0; i < 4; i++) { const pts = []; for (let j = 0; j <= 30; j++) { const u = j / 30, a = lt * 9 + i * TAU / 4 + u * 9, rr = u * 62; pts.push([ax + Math.cos(a) * rr, ay + Math.sin(a) * rr]); } marker(pts, [PAL.purple, PAL.pink, PAL.mint, YEL][i], 7, { rough: 0, smooth: true }); }
    scrap(rrPts(-210, -95, 500, 175, 24), YEL, { torn: 1, seed: 2404, ink: INK, sw: 4, shadow: false });
    const wb = (i, a) => Math.sin(lt * 14 + i * 1.3) * a;
    ['SHIP HAS', 'NUKES!!'].forEach((l, j) => { let x = -180; [...l].forEach((ch, i) => { txt(ch, x + wb(i + j, 3), -45 + j * 72 + wb(i * 2 + j, 6), 66, INK, { font: 'anton', align: 'left', rot: wb(i, .08) }); x += textW(ch, 66, 'anton') + 8; }); });
    ctx.restore();
    // CANCEL, and the fist that comes down on it from the upper right
    const KX = 690, KY = 1100, press = lt < slam ? 0 : Math.exp(-after * 3), FR = .42;
    bigButton(KX, KY, 150, 'CANCEL', press);
    const fd = lt < slam - .12 ? 1500 : lt < slam ? lerp(1500, 0, easeIn((lt - (slam - .12)) / .12)) : easeOut(clamp((after - .25) / .3)) * 900;
    if (lt >= slam - .12) { vFist(KX + Math.sin(FR) * fd, KY - 40 - Math.cos(FR) * fd, 44, FR); if (lt >= slam && after < .3) actionLines(KX, KY - 30, 210, 340, 16, YEL, 7, 12); }
    if (lt >= slam) sticker('ABORT!', 240, 1090, 92, YEL, { pop: popK(lt, slam + .05, .15), size: 40, rot: .18 });
    stamp('HALLUCINATION', 440, 800, 52, RED, -.07, { pop: popK(lt, verdict, .12) });   // (all on the paper: the multiplied ink vanishes off it)
    scrap(ellPts(BX, BYc, 56, 38, 20), Math.floor(t * 8) % 2 ? RED : '#FF8080', { torn: .5, ink: INK, sw: 4, seed: 2400 });
    camEnd();
    cutFlash(t, lt, RED);
    flash(.6 * flashAt(lt, slam, .08));
    captionStyle({ color: PAL.blue });
  });

  // ---------- V4.13 (vertical): TRUMP at the UN-blue podium; the Decree unrolls down its front: ARTIFICIAL → SUPER ----------
  vshot('V4.13', (p, lt, d, t, sg) => {
    const stars = hitAt(sg, d, 2, .6), strike = .34;
    bg('#3E86D0');
    cam(t, lt, { shake: .6, zoom: 1.02 + .04 * p, cy: 950 });
    rays(540, 680, 24, alpha(PAL.white, .14), lt * .3);
    halftone(FULL, PAL.white, { cell: 20, dot: .14, op: .3, multiply: false });
    wreathEmblem(540, 640, 450, PAL.white, .55);
    const s = 70, gx = 540, gy = 1320, pt = gy - 5.6 * s;
    person(gx, gy, s, { ...TRUMP, eyes: lt < strike + .1 ? 'dot' : 'closed', mouth: frac(bpOf(t) * 2) < .5 ? 'O' : 'grin', aL: -.25, aR: -.25, seed: 381 });
    trumpHair(gx, gy, s);
    longTie(gx, gy, s);
    helloTag('DONALD', gx + .8 * s, gy - 6.95 * s, .34 * s, .05);
    // the podium, running down out of the frame
    scrap([[gx - 330, pt + 14], [gx + 330, pt + 14], [gx + 290, H + 120], [gx - 290, H + 120]], '#2A3F66', { torn: 1.5, seed: 2500, ink: INK, sw: 5, shade: true, shadeOp: .25 });
    scrap(rectPts(gx - 352, pt, 704, 40), '#3A5588', { torn: 1, seed: 2501, ink: INK, sw: 4 });
    // the Decree unrolls down its front, all the way to the foot of the frame
    const uk = easeOut(clamp(lt / .45)), top = pt + 26, bot = top + 26 + 1010 * uk;
    scrap(rectPts(gx - 220, top, 440, bot - top), '#F3E3B5', { torn: 1.2, seed: 2510, ink: INK, sw: 3, shadow: [6, 8] });
    ctx.save(); tracePath(rectPts(gx - 220, top, 440, bot - top)); ctx.clip();
    txt('Decree', gx, top + 74, 80, INK, { font: 'fraktur' });
    txt('"ARTIFICIAL"', gx, top + 168, 48, INK, { font: 'typewriter' });
    if (lt > strike) marker(partial([[gx - 190, top + 164], [gx + 190, top + 172]], clamp((lt - strike) / .08)), RED, 9, { rough: 1 });
    const su = popK(lt, strike + .06, .14);
    if (su > 0) { ctx.save(); ctx.translate(gx, top + 258); const k = lerp(1.6, 1, easeOut(su)); ctx.scale(k, k); txt('→ SUPER', 0, 0, 70, RED, { font: 'anton', alpha: clamp(su * 3) }); ctx.restore(); }
    // the small print, then the seal and the signature at its foot
    ctx.fillStyle = 'rgb(28 26 31 / .4)'; for (let i = 0; i < 12; i++) ctx.fillRect(gx - 180, top + 330 + i * 30, 360 * (i % 4 === 3 ? .6 : 1), 7);
    scrap(starPts(gx - 110, top + 830, 66, .8, 16), '#B0252A', { torn: 1, seed: 2512, ink: '#6A1015', sw: 3, shadow: [4, 5] });
    scrap(ellPts(gx - 110, top + 830, 40, 40, 20), '#C8343A', { torn: .5, seed: 2513, shadow: false });
    txt('DJT', gx - 110, top + 832, 30, '#6A1015', { font: 'abril' });
    marker([[gx - 10, top + 860], [gx + 30, top + 800], [gx + 70, top + 860], [gx + 110, top + 790], [gx + 150, top + 860], [gx + 185, top + 810]], INK, 7, { rough: 1.5 });
    ctx.restore();
    for (const yy of [top, bot]) scrap(rrPts(gx - 244, yy - 17, 488, 34, 15), '#D9C48A', { torn: .5, seed: 2511, ink: INK, sw: 3 });
    // gold stars burst out round his head and fly up
    if (lt >= stars) for (let i = 0; i < 10; i++) {
      const a = i / 10 * TAU + .2, age = lt - stars, rr = 230 + age * 520;
      scrap(starPts(gx + Math.cos(a) * rr * .9, 690 + Math.sin(a) * rr * .8 - age * 300, 40 * (1 - clamp(age / .8)), .45, 5), PAL.gold, { torn: .3, ink: INK, sw: 2, shadow: false });
    }
    camEnd();
    cutFlash(t, lt);
  });

  // ---------- V4.14 (vertical): ARTIFICIAL, FAKE!, crumpled into a ball… that drops straight down into the bin ----------
  vshot('V4.14', (p, lt, d, t, sg) => {
    const fakeT = hitAt(sg, d, 0, .15), crush0 = hitAt(sg, d, 1, .38), drop0 = hitAt(sg, d, 2, .62), swish = hitAt(sg, d, 3, .85);
    bg(YEL);
    cam(t, lt, { shake: .9, zoom: 1.02, hits: [[fakeT, 16], [swish, 8]] });
    rays(540, 600, 22, alpha(RED, .5), -lt * .5);
    halftone(FULL, INK, { cell: 18, dot: .2, op: .15 });
    // the bin, below
    const bx = 540, rimY = 1040, rimR = 160;
    const binRock = lt >= swish ? Math.exp(-(lt - swish) * 8) * Math.sin((lt - swish) * 40) * .05 : 0;
    ctx.save(); ctx.translate(bx, rimY + 280); ctx.rotate(binRock); ctx.translate(-bx, -rimY - 280);
    scrap([[bx - rimR, rimY], [bx + rimR, rimY], [bx + 125, rimY + 290], [bx - 125, rimY + 290]], '#6B6B74', { torn: 1, seed: 2600, ink: INK, sw: 5, shade: true, shadeOp: .3 });
    for (let i = 0; i < 6; i++) marker([[bx - 130 + i * 52, rimY + 12], [bx - 104 + i * 42, rimY + 278]], INK, 3, { rough: 1, alpha: .5 });
    scrap(ellPts(bx, rimY, rimR + 2, 30, 24), '#4A4A52', { torn: .5, seed: 2601, ink: INK, sw: 4, shadow: false });
    ctx.restore();
    // the word on a card, crumpling
    const c = easeIn(clamp((lt - crush0) / Math.max(.1, drop0 - crush0 - .02)));
    let cx = 540, cy = 600, rot = -.04;
    const fall = lt >= drop0 ? clamp((lt - drop0) / Math.max(.15, swish - drop0)) : 0;
    if (lt >= drop0) { cx = 540 + Math.sin(fall * Math.PI) * 30; cy = lerp(600, rimY - 20, fall * fall); rot = fall * 7; }
    const cw = 960, ch = 300, N = 40, ballR = 100;
    const perim = []; for (let i = 0; i < N; i++) { const u = i / N * 4, side = Math.floor(u), f = u - side; perim.push([[-cw / 2 + f * cw, -ch / 2], [cw / 2, -ch / 2 + f * ch], [cw / 2 - f * cw, ch / 2], [-cw / 2, ch / 2 - f * ch]][side]); }
    const shape = perim.map(([x, y], i) => { const a = Math.atan2(y, x), n = .75 + hash2(2610, i) * .5; return [lerp(x, Math.cos(a) * ballR * n, c), lerp(y, Math.sin(a) * ballR * n, c)]; });
    if (lt < swish) {
      ctx.save(); ctx.translate(cx, cy); ctx.rotate(rot);
      scrap(shape, PAL.white, { torn: 1.5 + c * 4, seed: 2620, ink: INK, sw: 5, shadow: [10, 14], shade: c > .1 ? INK : undefined, shadeOp: .25 * c });
      ctx.save(); tracePath(shape); ctx.clip();
      ctx.save(); ctx.scale(lerp(1, .18, c), lerp(1, .45, c)); ctx.rotate(c * .5);
      txt('ARTIFICIAL', 0, 10, 172, INK, { font: 'abril', maxW: 880 });
      ctx.restore();
      for (let i = 0; i < 9; i++) { const a = hash2(2630, i) * TAU, r0 = hash2(2631, i) * 60; marker([[Math.cos(a) * r0 * (1 - c * .5), Math.sin(a) * r0], [Math.cos(a + 1.2) * 400 * (1 - c * .75), Math.sin(a + 1.2) * 160 * (1 - c * .4)]], alpha(INK, .5 * c), 3, { rough: 3 }); }
      ctx.restore();
      if (c < .15) stamp('FAKE!', 230, 92, 120, RED, -.22, { pop: popK(lt, fakeT, .1), alpha: 1 - c * 6, blend: 'source-over' });
      ctx.restore();
    }
    // the hands: in from the sides to crumple it, then they let go and get out of the way
    if (lt >= crush0 - .15) {
      const e = clamp((lt - (crush0 - .15)) / .15), half = lerp(cw / 2, ballR, c) + 40, f = clamp((lt - drop0) / .25);
      for (const side of [-1, 1]) {
        const hx = 540 + side * (half + (1 - e) * 500 + easeIn(f) * 700), hy = 600 - f * 60;
        if (hx < -300 || hx > W + 300) continue;
        ctx.save(); ctx.translate(hx, hy); ctx.scale(side, 1);
        scrap(rectPts(40, -60, 1200, 120), SUIT, { torn: 1, seed: 2640, shade: true, shadeOp: .2 });
        scrap(rectPts(30, -66, 40, 132), PAL.white, { torn: .5, seed: 2641, shadow: false, ink: INK, sw: 2 });
        scrap(rrPts(-60, -70, 100, 140, 40), SKINS[4], { torn: .6, seed: 2642, ink: INK, sw: 3 });
        for (let q = 0; q < 3; q++) marker([[-40, -40 + q * 35], [0, -40 + q * 35]], mixCol(SKINS[4], INK, .4), 4, { rough: .5 });
        ctx.restore();
      }
    }
    if (lt >= drop0 && lt < swish) for (let i = 0; i < 4; i++) marker([[cx - 60 + i * 40, cy - 120 - i * 10], [cx - 60 + i * 40, cy - 220 - i * 10]], INK, 5, { rough: 0, alpha: .6 });
    if (c > .3 && lt < drop0 + .1) txt('CRUNCH!', 540, 830, 88, RED, { font: 'anton', rot: -.12 + jit(.04), stroke: INK, sw: 6, alpha: clamp((c - .3) * 4) });
    if (lt >= swish) {
      sticker('SWISH!', 800, 960, 96, PAL.white, { pop: popK(lt, swish, .12), size: 42, rot: -.15 });
      scrap(ellPts(bx + jit(3), rimY - 12, 66, 22, 16), PAL.white, { torn: 3, seed: 2650, ink: INK, sw: 3, shadow: false });
      bubble("IT'S NOT FAKE. IT'S ACTUALLY AMAZING!", 540, 600, { size: 62, maxW: 760, pop: popK(lt, swish + .05, .18), rot: -.04, fill: PAL.white });
    }
    camEnd();
    cutFlash(t, lt);
    flash(.4 * flashAt(lt, fakeT, .07), RED);
  });

  // ---------- V4.15 (vertical): the calendar up top rips SEP 12 → SEP 22, its pages flying up; the boxes start shaking below ----------
  vshot('V4.15', (p, lt, d, t, sg) => {
    const flipEnd = hitAt(sg, d, 2, .55);
    bg(RED);
    cam(t, lt, { shake: 1.1, zoom: 1.02 + .03 * p, hits: [[flipEnd, 12]] });
    halftone(FULL, INK, { cell: 18, dot: .22, op: .3 });
    const kx = 540, ky = 840, pw = 460, ph = 520;
    card(kx, ky + 10, pw + 60, ph + 70, '#3A2A20', .02, { seed: 2700, torn: 1.5 });
    const n = 10, hold = Math.min(.3, flipEnd * .4), per = (flipEnd - hold) / n;
    const torn = lt < hold ? 0 : Math.min(n, Math.floor((lt - hold) / per) + 1);
    calPage(kx, ky, pw, ph, 12 + torn, { shadow: [4, 5] });
    if (torn >= n) circleMark(kx, ky + 70, 200, 170, INK, 10, popK(lt, flipEnd, .2));
    for (let j = 0; j < 4; j++) marker([[kx - 150 + j * 100, ky - ph / 2 - 26], [kx - 150 + j * 100, ky - ph / 2 + 18]], '#9A9AA6', 12, { rough: 0 });
    // the torn-off pages fly up and away out of the top of the frame (the calendar hangs low, so they're in view a while)
    for (let i = Math.max(0, torn - 6); i < torn; i++) {
      const a = lt - hold - i * per, u = a / .55, side = i % 2 ? 1 : -1;
      if (u > 1) continue;
      calPage(kx + side * (u * 300 + 30 * (i % 3)), ky - u * 1300 + u * u * 260, pw, ph, 12 + i, { rot: side * (u * 2.2 + .1), s: 1 - u * .35, shadow: [8, 10] });
    }
    if (lt < flipEnd) for (let i = 0; i < 6; i++) marker([[kx - 260 + i * 104, ky - 330 - (i % 2) * 40], [kx - 260 + i * 104, ky - 470 - (i % 2) * 40]], PAL.white, 6, { rough: 0, alpha: .8 });
    // the floor under the table, strewn with the pages torn off before (SEP 1 … 11)
    scrap(rectPts(-100, 1660, W + 200, 400), '#4A1A16', { torn: 1, seed: 2712, shadow: false, tone: { color: INK, cell: 12, dot: .25, op: .4 } });
    for (let i = 0; i < 9; i++) calPage(60 + i * 122 + (hash(i + 2720) - .5) * 60, 1760 + hash(i + 2721) * 110, pw, ph, 1 + i * 1.3 | 0, { rot: (hash(i + 2722) - .5) * 1.6, s: .42, shadow: [6, 8] });
    // the table and the two boxes, shaking harder and harder
    const TY = 1392;
    for (const lx of [90, 990]) scrap(rectPts(lx - 22, TY + 30, 44, 330), '#4A2A16', { torn: .6, seed: 2711 + lx, ink: INK, sw: 3 });
    scrap(rectPts(-100, TY, W + 200, 40), '#6A4028', { torn: 1, seed: 2710, ink: INK, sw: 4 });
    const shake = clamp((lt - flipEnd * .5) / (d * .6)) ** 1.5, sh = a => jit(a * shake);
    const hop = i => Math.max(0, Math.sin((bpOf(t) * 2 + i * .5) * Math.PI)) * 18 * shake;
    giftBox(330 + sh(8), TY - hop(0), 330, 250, PAL.clawd, YEL, { rot: sh(.06), seed: 1500, tone: PAL.clawdDk });
    giftLid(330 + sh(8), TY - 250 - hop(0) - hop(1) * .8, 330, PAL.clawd, YEL, sh(.1), { seed: 1500 });
    giftBox(770 + sh(8), TY - hop(1), 290, 220, PAL.teal, PAL.white, { rot: sh(.06), seed: 1520 });
    giftLid(770 + sh(8), TY - 220 - hop(1) - hop(0) * .8, 290, PAL.teal, PAL.white, sh(.1), { seed: 1520 });
    if (shake > .2) { txt('?!', 120, 1130 + jit(4), 84, YEL, { font: 'anton', stroke: INK, sw: 8, rot: -.15 }); txt('?!', 960, 1160 + jit(4), 76, YEL, { font: 'anton', stroke: INK, sw: 8, rot: .15 }); }
    camEnd();
    cutFlash(t, lt);
  });

  // ---------- V4.16 (vertical): Clawd springs up out of his box, high up the frame: "Hi, guys!"… then GPT-6 pops out next door ----------
  vshot('V4.16', (p, lt, d, t, sg) => {
    const gptT = hitAt(sg, d, 1, .3), glanceT = hitAt(sg, d, 2, .58), winkT = hitAt(sg, d, 3, .8);
    bg(PAL.pink);
    cam(t, lt, { shake: 1.0, zoom: 1.03 + .03 * p, hits: [[0, 18], [gptT, 12]] });
    rays(330, 760, 22, '#FF8FC4', lt * .8);
    halftone(FULL, RED, { cell: 18, dot: .2, op: .2 });
    const TY = 1345;
    scrap(rectPts(-100, TY, W + 200, 60), '#6A4028', { torn: 1, seed: 2800, ink: INK, sw: 4 });
    // the PACE pennant from V4.7, knocked flat by the blast
    const fallK = lt < gptT ? Math.sin(lt * 30) * .04 : easeOut(clamp((lt - gptT) / .25));
    ctx.save(); ctx.translate(560, TY); ctx.rotate(-lerp(0, 1.0, fallK));
    marker([[0, 0], [0, -230]], '#6B5B4B', 9, { rough: 0 });
    scrap([[0, -230], [150, -190], [0, -150]], YEL, { torn: .4, ink: INK, sw: 3, seed: 2801 });
    txt('PACE', 58, -190, 34, INK, { font: 'archivo' });
    ctx.restore();
    // Clawd's box (Opus 5.5): the lid flies off up out of the frame, Clawd shoots up on a long spring
    const b1x = 320, b1w = 390, b1h = 240, b1top = TY - b1h, u = 40;
    const lu = lt / .42;
    giftLid(b1x - 120 * lu, b1top - 2200 * lu, b1w, PAL.clawd, YEL, -lu * 2.2, { seed: 1500 });
    const jk = elasticOut(clamp(lt / .5)), springLen = 40 + 200 * jk;
    const cGround = b1top - springLen + 30;
    const winking = lt >= winkT, glancing = lt >= glanceT && !winking;
    spring(b1x, b1top + 40, cGround - 10, 40, 8);
    clawd(b1x, cGround, u, { eyes: winking ? 'normal' : glancing ? 'worried' : 'happy', lookX: glancing ? 1 : 0, mouth: winking ? 'grin' : 'smile', blush: true, sweat: glancing, aL: 1.1 + Math.sin(lt * 16) * .45, aR: winking ? .2 : -.5, shadow: false, rot: winking ? 0 : Math.sin(lt * 8) * .04 * (1 - jk * .5) });
    if (winking) {
      clawdWink(b1x, cGround, u);
      scrap(starPts(b1x - 4.3 * u, cGround - 8.4 * u, 26 * backOut(popK(lt, winkT, .12)), .35, 4), PAL.white, { torn: .2, ink: INK, sw: 3, shadow: false });
    }
    giftBox(b1x, TY, b1w, b1h, PAL.clawd, YEL, { seed: 1500, tone: PAL.clawdDk });
    sticker('5.5', b1x, TY - b1h * .48, 96, YEL, { pop: popK(lt, .06, .16), size: 74, rot: -.12 });
    burstBits(b1x, b1top - 20, lt, 50, 2810, { v: 1500, g: 1300, a0: -Math.PI / 2, spread: 1.8 });
    bubble('Hi, guys!', 285, 495, { size: 70, tail: [b1x + 10, cGround - 7.6 * u], pop: popK(lt, .08, .2), rot: -.05, fill: PAL.white });
    // GPT-6's box
    const b2x = 795, b2w = 300, b2h = 222, b2top = TY - b2h, s2 = 25;
    if (lt >= gptT) {
      const l2 = (lt - gptT) / .42;
      giftLid(b2x + 150 * l2, b2top - 2200 * l2, b2w, PAL.teal, PAL.white, l2 * 2.2, { seed: 1520 });
      const gk = elasticOut(clamp((lt - gptT) / .5)), gGround = b2top + 60 - 260 * gk;
      spring(b2x, b2top + 40, gGround - 5, 32, 7);
      bot(b2x, gGround, s2, { col: '#B9C3D0', eyes: 'happy', aR: 1.1 + Math.sin(lt * 16 + 1) * .45, aL: -.6, shadow: false, seed: 540 });
      bib(b2x, gGround - 5.3 * s2, 140, 60, 'GPT-6', .06);
    } else giftLid(b2x + jit(4), b2top - Math.abs(jit(10)), b2w, PAL.teal, PAL.white, jit(.08), { seed: 1520 });
    giftBox(b2x + (lt < gptT ? jit(5) : 0), TY, b2w, b2h, PAL.teal, PAL.white, { seed: 1520 });
    if (lt >= gptT) { burstBits(b2x, b2top - 20, lt - gptT, 36, 2830, { v: 1300, g: 1300, a0: -Math.PI / 2, spread: 1.8 }); bubble('Hi, guys!', 840, 555, { size: 54, tail: [b2x - 10, b2top + 60 - 260 - 9 * s2], pop: popK(lt, gptT + .08, .2), rot: .06, fill: PAL.mint }); }
    confettiFall(lt, 56, 2850);
    camEnd();
    cutFlash(t, lt, YEL);
  });
})();

;
// ---- src/ch/c09_finale.js ----
// c09_finale — Chorus 4 (the singularity show, venue level 4) and the outro (lights out → the zine's back cover).
//
// Sub-shots follow the sung lines (linesOf('C4')):
//   L1 "We didn't start the scaling"        wide singularity show, lasers, the curve shoots off the top of the banner, hook slams
//   L2 "It was always training, …"          agents stage-dive at the camera; "…the curves kept gaining": crane up the curve through the roof
//   L3 "We didn't start the scaling"        Clawd close-up, hook stacked beside him
//   L4 "Now we swear we'll try to pace it…"  PACE sign + halo + slow motion → checkered flag, racing-stripe wipe, P→R: RACE at double speed
//   L5 "We didn't start the scaling"        everybody jumps; freeze-frame on the peak (pink riso duotone); only one GPU keeps moving
//   L6 "But when we log off… train on?"     the hook falls off, the lights go out bank by bank; the GPU trains on in the dark;
//                                           "AND ON" recedes down a cut-paper tunnel into its green LED
//   outro                                   the page is turned over: the zine's back cover, credits, Clawd asleep, the LED still blinking
(() => {
  // ---------------- timing ----------------
  const BL = () => 60 / BPM;
  const LN = () => linesOf('C4');
  const lineIdx = t => { const L = LN(); let i = 0; for (let j = 1; j < L.length; j++) if (t >= L[j].start) i = j; return i; };
  // window of line i: its start → the next line's start (the last line: its own sung end)
  // the last line's window runs through the sung "and on, and on…" tag, if the take sings one
  const TAG = () => LINES.find(l => l.sec === 'outro');
  const win = i => { const L = LN(); return { a: L[i].start, b: i + 1 < L.length ? L[i + 1].start : Math.max(L[i].end, TAG()?.end ?? 0) }; };
  // where each hook word lands inside a "We didn't start the scaling" window (fraction of the window)
  const HOOK_W = ['WE', "DIDN'T", 'START', 'THE', 'SCALING'];
  const HOOK_AT = [0, .1, .15, .29, .79];
  const READABLE = ['anton', 'abril', 'archivo', 'typewriter', 'bungee', 'mono', 'courier', 'bebas', 'rammetto', 'shrikhand'];

  // Draw fn as if the song were at time tw: slow motion, double speed, freeze-frames.
  // (Temporarily swaps the global clock + boil so every shared helper that reads T or jit() follows; restored before returning.)
  function atTime(tw, fn) {
    const sT = T, sB = _boil, sJ = _jitN;
    T = tw; _boil = boilFrame(tw); _jitN = 0;
    try { return fn(); } finally { T = sT; _boil = sB; _jitN = sJ; }
  }

  // ---------------- the level-4 banner curve (same formula as band.js curveBanner at level 4) ----------------
  const BX = 260, BY = 110, BW = 1400, BH = 560, E8 = Math.exp(8) - 1;
  const curvePt = u => { const v = (Math.exp(u * 8) - 1) / E8; return [BX + 90 + u * (BW - 180), BY + BH - 70 - v * (BH - 140) * 1.9]; };
  const curveXAtY = y => BX + 90 + (BW - 180) * Math.log(1 + (BY + BH - 70 - y) / ((BH - 140) * 1.9) * E8) / 8;
  const CURVE = Array.from({ length: 51 }, (_, i) => curvePt(i / 50));
  const TOP = CURVE[50];  // where the banner curve ends (above the frame at zoom 1)

  function spark(x, y, r, seed = 1) {
    for (let i = 0; i < 9; i++) {
      const a = hash2(seed, i) * TAU + T * 3, d = r * (.8 + frac(T * 2.5 + hash2(seed, i + 9)) * 1.8);
      ctx.fillStyle = i % 2 ? PAL.yellow : PAL.white;
      ctx.fillRect(x + Math.cos(a) * d - 4, y + Math.sin(a) * d - 4, 8, 8);
    }
    scrap(burstPts(x, y, r * (1 + jit(.2)), 10, .45, T * 7), PAL.orange, { torn: .5, shadow: false, seed });
    scrap(burstPts(x, y, r * .6 * (1 + jit(.2)), 8, .45, -T * 5), PAL.yellow, { torn: .5, shadow: false, seed: seed + 1 });
  }

  // ---------------- stage chaos ----------------
  const CX = 960, GROUND = STAGE_Y + 70, U = 30;
  // The band, posed. o.hop (0..1 bounce), o.jump (px lift for everybody), Clawd overrides: eyes, mouth, aL, aR, mic, stand, sq.
  function band(t, o = {}) {
    const b = bpOf(t), p = pulse(t, 7), p8 = pulse2(t, 9);
    const hop = o.hop ?? Math.max(0, Math.sin(b * Math.PI)) ** 2;
    const J = o.jump ?? 0, air = clamp(J / 100);
    // drummer agent (back right)
    const dx = 1330, dy = STAGE_Y + 10;
    drumkit(dx, dy, 22, { label: 'LOSS↓' });
    const ay = dy - 150 - p * 10 * (1 - air) - J * 1.1;
    agent(dx, ay, 42, { eyes: 'spark', col: '#2A2D38', rot: -air * .12 });
    const hit = frac(b) < .5 ? -1 : 1;
    for (const side of [-1, 1]) {
      const up = air > .01 ? 1 : side === hit ? p : 0;
      marker([[dx + side * 30, ay - 80], [dx + side * (90 + up * 20), ay - 20 - up * 60 - air * 50]], '#E8D7B0', 9, { rough: 0 });
    }
    // Robo on guitar (left)
    const rx = 520, rl = hop * 18 + J * .95, ra = o.roboArms;
    bot(rx, GROUND, 30, { dy: -rl / 30, rot: Math.sin(b * Math.PI / 2) * .06, eyes: 'spark', col: '#9FB3C8', aL: ra ?? .1, aR: ra ?? (-.2 + p8 * .25) });
    ctx.save(); ctx.translate(rx + 10, GROUND - 140 - rl); ctx.rotate(-.9 + (ra ? .4 : 0));
    scrap(rectPts(-9, -210, 18, 170), '#4A3021', { torn: .3, shadow: false });
    scrap([[-55, -40], [45, -52], [70, 12], [26, 60], [-44, 56], [-72, 6]], PAL.yellow, { torn: .8, ink: PAL.ink, sw: 4, seed: 1220 });
    scrap(ellPts(0, 4, 14, 14, 12), PAL.ink, { torn: .3, shadow: false });
    ctx.restore();
    // Huggy on bass (right), bandaged since the V4 hack
    const hx = 1520, hy = STAGE_Y - 10 - hop * 26 - J;
    ctx.save(); ctx.translate(hx, hy); ctx.rotate(.45 + air * .3);
    scrap(rectPts(-12, -260, 24, 220), '#3A2415', { torn: .3, shadow: false });
    scrap([[-70, -40], [60, -50], [80, 20], [30, 70], [-60, 60], [-85, 10]], PAL.blue, { torn: .8, ink: PAL.ink, sw: 4, seed: 1221 });
    ctx.restore();
    huggy(hx - 10, hy - 110, 95, { mood: o.huggyMood ?? 'happy', hands: o.huggyHands ?? (.3 + p * .4) });
    for (const r of [.5, -.5]) { ctx.save(); ctx.translate(hx + 30, hy - 175); ctx.rotate(r); scrap(rrPts(-50, -16, 100, 32, 12), '#F2D2B5', { torn: .5, shadow: false, ink: PAL.ink, sw: 2 }); ctx.restore(); }
    scrap(rrPts(hx - 95, hy - 110, 44, 26, 8), '#F2D2B5', { torn: .4, shadow: false, ink: PAL.ink, sw: 2 });
    // Clawd (centre), still wearing his "5.5" sticker from the gift box
    const cl = hop * 42 + J * 1.2;
    const pose = { x: CX, y: GROUND, u: U, dy: -cl / U, aR: o.aR ?? (.5 + p * .5), aL: o.aL ?? (-.2 + hop * .7) };
    if (o.stand !== false) micStand(CX - 150, STAGE_Y + 60, 26);
    clawd(CX, GROUND, U, { hat: 'mohawk', eyes: o.eyes ?? 'shades', mouth: o.mouth ?? singMouth(t, true), mic: o.mic ?? true, aR: pose.aR, aL: pose.aL, dy: pose.dy, sq: o.sq ?? (-hop * .08 + p * .05) });
    sticker('5.5', CX - 2.9 * U, GROUND + pose.dy * U - 3.2 * U, 1.3 * U, PAL.yellow, { rot: -.25, size: .85 * U });
    return pose;
  }
  // Clawd's hand position (side 1 = right, −1 = left) for a pose returned by band().
  const handOf = (pose, side) => { const a = side > 0 ? pose.aR : pose.aL, u = pose.u; return [pose.x + side * (5 * u + 2 * u * Math.cos(a)), pose.y + pose.dy * u - 4.9 * u - 2 * u * Math.sin(a)]; };

  function blast(x, y, r, k, seed) {
    if (k <= 0 || k >= 1) return;
    const s = easeOut(k) * r;
    ctx.save(); ctx.globalAlpha *= clamp((1 - k) * 2);
    scrap(burstPts(x, y, s, 14, .55, seed), PAL.red, { torn: 4, shadow: false, seed });
    scrap(burstPts(x, y, s * .74, 12, .6, seed + 1), PAL.orange, { torn: 3, shadow: false, seed: seed + 1 });
    scrap(burstPts(x, y, s * .46, 10, .6, seed + 2), PAL.yellow, { torn: 2, shadow: false, seed: seed + 2 });
    ctx.restore();
  }
  // pyro on every bar downbeat, alternating sides, behind the band
  function blasts(t) {
    const bar = bpOf(t) / 4, n = Math.floor(bar), life = (bar - n) * 4 * BL();
    const side = n % 2 ? 1 : -1;
    blast(W / 2 + side * 470, 380, 300, life / .75, 1300 + (n % 5) * 3);
    blast(W / 2 - side * 260, 270, 190, (life - .2) / .6, 1330 + (n % 3) * 3);
  }
  // laser fans from the truss, sweeping on the beat
  function lasers(t) {
    const b = bpOf(t);
    ctx.save(); ctx.globalCompositeOperation = 'screen'; ctx.lineCap = 'round';
    for (let i = 0; i < 10; i++) {
      const ox = 120 + i * 187, a = Math.PI / 2 + Math.sin(b * Math.PI / 4 + i * 1.3) * .75;
      ctx.strokeStyle = alpha(['#6CF2B0', PAL.pink, PAL.sky, PAL.yellow][i % 4], .5 + .3 * pulse(t, 4)); ctx.lineWidth = 5;
      ctx.beginPath(); ctx.moveTo(ox, 55); ctx.lineTo(ox + Math.cos(a) * 1500, 55 + Math.sin(a) * 1500); ctx.stroke();
    }
    ctx.restore();
  }
  // spark fountains (gerbs) along the stage lip
  function fountains(t, xs = [250, 690, 1230, 1670]) {
    xs.forEach((fx, j) => {
      for (let i = 0; i < 14; i++) {
        const ph = frac(t * 1.7 + hash2(j + 40, i)), vx = (hash2(j + 40, i + 50) - .5) * 260, vy = 950 + hash2(j + 40, i + 90) * 350;
        const x = fx + vx * ph, y = STAGE_Y + 20 - vy * ph + 950 * ph * ph;
        ctx.globalAlpha = 1 - ph; ctx.fillStyle = i % 3 ? PAL.yellow : PAL.white; ctx.fillRect(x - 3, y - 8, 6, 16);
      }
    });
    ctx.globalAlpha = 1;
  }
  const AGENT_COLS = ['#2A2D38', '#5B3FA0', '#1F5B73', '#8A2E4A'];
  const AGENT_BARS = [PAL.clawd, PAL.yellow, PAL.mint, PAL.pink];
  // agents stage-diving into the crowd, then crowd-surfing
  function divers(t, n = 7) {
    for (let i = 0; i < n; i++) {
      const per = 1.6 * (1 + hash(i + 70) * .6), ph = frac(t / per + hash(i + 71)), dir = i % 2 ? 1 : -1;
      const x0 = CX + dir * (230 + hash(i + 72) * 300), x1 = x0 + dir * (150 + hash(i + 73) * 450);
      let x, y, rot;
      if (ph < .4) { const q = ph / .4; x = lerp(x0, x1, q); y = lerp(STAGE_Y + 30, 935, q) - Math.sin(q * Math.PI) * 170; rot = q * TAU * dir; }
      else { const q = (ph - .4) / .6; x = x1 + dir * q * 520; y = 935 + Math.sin(t * 9 + i) * 10; rot = dir * TAU / 4 + Math.sin(t * 5 + i) * .2; }
      agent(x, y, 24, { rot, eyes: i % 3 ? 'spark' : 'heart', col: AGENT_COLS[i % 4], bar: AGENT_BARS[i % 4], walk: t * 3 + i * .3 });
    }
  }
  const CONF = [PAL.pink, PAL.yellow, PAL.sky, PAL.mint, PAL.clawd, PAL.white, PAL.red];
  function confetti(t, n = 80, o = {}) {
    const x0 = o.x0 ?? -250, x1 = o.x1 ?? W + 250, y0 = o.y0 ?? -200, y1 = o.y1 ?? H + 150, sp = y1 - y0, streak = o.streak ?? 0;
    for (let i = 0; i < n; i++) {
      const r = k => hash2(i + 4400, k);
      const v = 110 + r(1) * 170, x = lerp(x0, x1, r(2)) + Math.sin(t * (1 + r(3)) + i) * 40;
      const y = y0 + ((t * v + r(4) * sp) % sp), w = 14 + r(5) * 16, h = 8 + r(6) * 7;
      ctx.save(); ctx.translate(x, y);
      if (streak) { ctx.globalAlpha = .5; ctx.fillStyle = CONF[i % CONF.length]; ctx.fillRect(-w * .3, -streak, w * .6, streak); ctx.globalAlpha = 1; }
      ctx.rotate(t * (2 + r(7) * 5) + i); ctx.scale(1, Math.cos(t * (3 + r(8) * 5) + i));
      ctx.fillStyle = CONF[i % CONF.length]; ctx.fillRect(-w / 2, -h / 2, w, h);
      ctx.restore();
    }
  }
  function mosh(t, back = true) {
    if (back) crowd(STAGE_Y + 140, t, { n: 30, s: 46, col: '#2E2645', jump: 1, hands: .85, horns: true, lighters: true, seed: 931 });
    else crowd(STAGE_Y + 215, t, { n: 17, s: 80, col: PAL.ink, jump: 1, hands: .75, horns: true, seed: 947 });
  }
  // The whole singularity show in world coordinates. Returns Clawd's pose.
  function stage(t, o = {}) {
    const k = o.curveK ?? 1;
    venue(t, 4, { curveK: k, bannerTitle: o.bannerTitle });
    if (o.afterVenue) o.afterVenue();   // (the vertical video: the curve's extension, up off the banner)
    if (k < 1) { const tip = partial(CURVE, k).at(-1); spark(tip[0], tip[1], 40, 1401); }
    if (o.lasers !== false) lasers(t);
    if (o.blasts !== false) blasts(t);
    const pose = band(t, o);
    if (o.afterBand) o.afterBand();     // (the vertical video: the GPU on its road case at the stage's lip)
    if (o.fountains !== false) fountains(t);
    mosh(t, true);
    if (o.divers !== false) divers(t);
    mosh(t, false);
    return pose;
  }

  // ---------------- text ----------------
  // Hook words slam in as they're sung. rows: [{ idx: [word indices], x, y, size, align, rot }].
  // fall(j) → { dx, dy, rot } lets words drop off the page afterwards.
  function hookWords(t, w, rows, seed = 0, fall) {
    const d = w.b - w.a;
    for (const row of rows) {
      const gap = row.size * .3;
      const ws = row.idx.map(j => ransom(HOOK_W[j], 0, 0, row.size, { seed: 9100 + j * 17 + seed, pop: 0, fonts: READABLE }));
      const total = ws.reduce((a, b) => a + b, 0) + gap * (ws.length - 1);
      let x = (row.x ?? W / 2) - (row.align === 'left' ? 0 : total / 2);
      row.idx.forEach((j, n) => {
        const k = clamp((t - (w.a + HOOK_AT[j] * d)) / .16);
        const f = fall ? fall(j) : { dx: 0, dy: 0, rot: 0 };
        if (k > 0 && f.dy < H + 300) {
          const s = k < 1 ? lerp(1.6, 1, easeOut(k)) : 1;
          ctx.save(); ctx.translate(x + ws[n] / 2 + f.dx, row.y + f.dy); ctx.rotate((row.rot ?? 0) + f.rot); ctx.scale(s, s);
          ransom(HOOK_W[j], 0, 0, row.size, { seed: 9100 + j * 17 + seed, pop: clamp(k * 1.6), fonts: READABLE });
          ctx.restore();
        }
        x += ws[n] + gap;
      });
    }
  }
  // Typewriter text: k = fraction of characters struck.
  function typed(str, x, y, size, k, col, o = {}) {
    const n = Math.floor(str.length * clamp(k) + 1e-6), shown = str.slice(0, n);
    const full = textW(str, size, 'typewriter'), x0 = o.align === 'left' ? x : x - full / 2;
    if (shown) txt(shown, x0, y, size, col, { font: 'typewriter', align: 'left', alpha: o.alpha ?? 1 });
    if (k < 1 && k > 0 && frac(T * 4) < .6) { ctx.fillStyle = col; ctx.globalAlpha = o.alpha ?? 1; ctx.fillRect(x0 + textW(shown, size, 'typewriter') + size * .05, y - size * .42, size * .5, size * .8); ctx.globalAlpha = 1; }
  }

  // ---------------- the GPU that keeps going ----------------
  // the first GPU on the right amp stack (venue level 4); in the vertical video, whose frame doesn't reach the stacks, the GPU on its
  // road case at the stage's lip, between Clawd and Huggy (vStageGPU)
  const GX = VERT ? 1262 : 1710, GY = VERT ? 782 : 610, GS = VERT ? 16 : 13;
  const LED_ON = t => frac((t - BEAT0) / (BL() * 2)) < .5;   // blinks every two beats
  const LED = [GX + 4.1 * GS, GY - 2.05 * GS];
  const LOSS = t => .011 + .09 * Math.exp(-(t - span('C4').start + 3) * .09) + (hash(Math.floor(t * 12)) - .5) * .002;
  function glowAt(x, y, r, col, a) {
    const g = ctx.createRadialGradient(x, y, r * .03, x, y, r);
    g.addColorStop(0, alpha(col, a)); g.addColorStop(1, alpha(col, 0));
    ctx.fillStyle = g; ctx.fillRect(x - r, y - r, 2 * r, 2 * r);
  }
  function liveGPU(t, o = {}) {
    const on = LED_ON(t), s = GS;
    if (o.glow) glowAt(GX, GY, 26 * s, '#3BE08A', (.14 + (on ? .05 : 0)) * o.glow);
    gpu(GX, GY, s, { label: 'H100', t });
    ctx.fillStyle = on ? '#8BFFB5' : '#1D3A28'; tracePath(ellPts(LED[0], LED[1], .32 * s, .32 * s, 12)); ctx.fill();
    if (on) { ctx.fillStyle = alpha('#6CF2B0', .35); tracePath(ellPts(LED[0], LED[1], 1.1 * s, 1.1 * s, 16)); ctx.fill(); }
    if (o.lcd) lossLCD(t, GX - 1.2 * s, GY - 5.3 * s, 6.6 * s, 3.6 * s);
  }
  // A tiny LCD taped to the GPU: the loss curve, still ticking down.
  function lossLCD(t, cx, cy, w, h) {
    scrap(ctrRect(cx, cy, w, h), '#101A14', { torn: .6, seed: 1450, shadow: [3, 4], ink: '#39424A', sw: 2 });
    const x0 = cx - w * .42, x1 = cx + w * .42, y0 = cy - h * .36, y1 = cy + h * .12, pts = [];
    for (let i = 0; i <= 40; i++) { const tt = t - 6 + i / 40 * 6; pts.push([lerp(x0, x1, i / 40), lerp(y1, y0, clamp((LOSS(tt) - .012) / .02))]); }
    ctx.strokeStyle = '#6CF2B0'; ctx.lineWidth = 1.6; ctx.lineJoin = 'round'; tracePath(pts, false); ctx.stroke();
    ctx.fillStyle = '#8BFFB5'; tracePath(ellPts(pts[40][0], pts[40][1], 1.8, 1.8, 8)); ctx.fill();
    txt(`loss ${LOSS(t).toFixed(4)}`, cx, cy + h * .3, h * .2, '#6CF2B0', { font: 'code' });
    tape(cx, cy - h * .52, w * .4, .05, { h: 9, seed: 1451 });
  }

  // ================= sub-shots =================

  // L1 — wide singularity show; the curve shoots up off the top of the banner; the hook slams in.
  function shotWide(t) {
    const w = win(0), lt = t - w.a;
    const z = lerp(1.35, 1, easeOut(clamp(lt / .55))), [sx, sy] = shakeXY(t, 9 * pulse(t, 5));
    camBegin(1050 + sx, 545 + sy, z, lerp(-.03, 0, easeOut(clamp(lt / .55))));
    stage(t, { curveK: lerp(.6, 1, easeIn(clamp(lt / 1.1))) });
    confetti(t, 70);
    camEnd();
    hookWords(t, w, [{ idx: [0, 1, 2], y: 250, size: 118, x: 800 }, { idx: [3, 4], y: 405, size: 140, x: 800 }]);
    if (lt < .1) { ctx.fillStyle = alpha(PAL.white, .75 * (1 - lt / .1)); ctx.fillRect(0, 0, W, H); }
    hideCaption();
  }

  // L2a — "It was always training": pan along the stage lip; agents stage-dive at the camera.
  function shotDive(t, a, b) {
    const q = clamp((t - a) / (b - a)), [sx, sy] = shakeXY(t, 6 * pulse(t, 5));
    camBegin(lerp(760, 1200, ease(q)) + sx, 650 + sy, 1.55, lerp(.05, -.03, q));
    stage(t);
    confetti(t, 60);
    camEnd();
    // one agent per beat launches off the stage straight at the camera
    const bp = bpOf(t);
    for (let n = Math.floor(bp) - 2; n <= Math.floor(bp); n++) {
      const k = (bp - n) / 2.2; if (k < 0 || k > 1) continue;
      const side = hash(n + 5) < .5 ? -1 : 1, x0 = 960 + (hash(n + 6) - .5) * 700, x1 = x0 + side * (500 + hash(n + 7) * 400);
      const x = lerp(x0, x1, k), y = lerp(560, 1350, k * k) - Math.sin(k * Math.PI) * 420, s = lerp(16, 140, k * k);
      agent(x, y, s, { rot: k * TAU * .8 * side, eyes: n % 2 ? 'spark' : 'heart', col: AGENT_COLS[n % 4], bar: AGENT_BARS[n % 4], walk: t * 4 });
    }
  }

  // L2b — "and the curves kept gaining": crane up the curve, off the banner, through the roof, into the night.
  function upperWorld(t) {
    // wall above the venue, rafters, the roof, the sky
    ctx.fillStyle = '#0E0A1C'; ctx.fillRect(-600, -900, W + 1200, 560);
    for (let i = -3; i < 14; i++) { marker([[i * 200, -390], [i * 200 + 200, -700]], '#4A4658', 12, { rough: 0 }); marker([[i * 200 + 200, -390], [i * 200 + 400, -700]], '#35323F', 8, { rough: 0 }); }
    ctx.fillStyle = '#5A5670'; ctx.fillRect(-600, -400, W + 1200, 22); ctx.fillRect(-600, -712, W + 1200, 22);
    // night sky
    const g = ctx.createLinearGradient(0, -2600, 0, -760);
    g.addColorStop(0, '#07061A'); g.addColorStop(1, '#2B1F58');
    ctx.fillStyle = g; ctx.fillRect(-600, -2800, W + 1200, 2045);
    for (let i = 0; i < 70; i++) {
      const x = -300 + hash(i + 300) * (W + 600), y = -2700 + hash(i + 301) * 1900, r = 4 + hash(i + 302) * 8;
      scrap(starPts(x, y, r * (1 + .3 * Math.sin(t * 5 + i)), .4, 4, 0), i % 5 ? PAL.cream : PAL.yellow, { torn: 0, shadow: false });
    }
    scrap(ellPts(760, -1780, 150, 150, 36), PAL.cream, { torn: 1.5, seed: 1470, tone: { color: PAL.kraft, cell: 14, dot: .3, op: .6 } });
    // roof slab with a hole torn where the curve punches through
    const hx = extX(-760), hole = [hx - 110, hx + 90];
    scrap(burstPts(hx, -760, 190, 12, .5), alpha(PAL.cream, .9), { torn: 3, shadow: false, seed: 1473 });
    scrap([[-600, -800], [hole[0], -800], [hole[0] + 35, -765], [hole[0] - 15, -735], [hole[0] + 25, -700], [-600, -700]], '#2E2A3A', { torn: 3, seed: 1471, shadow: [0, 8] });
    scrap([[hole[1], -800], [W + 600, -800], [W + 600, -700], [hole[1] - 25, -700], [hole[1] + 15, -738], [hole[1] - 20, -772]], '#2E2A3A', { torn: 3, seed: 1472, shadow: [0, 8] });
    ctx.fillStyle = '#6A6588'; ctx.fillRect(-600, -806, hole[0] + 600, 8); ctx.fillRect(hole[1], -806, W + 600 - hole[1], 8);
    // debris flying out of the hole
    for (let i = 0; i < 12; i++) {
      const ph = frac(t * .9 + hash(i + 320)), x = lerp(hole[0], hole[1], hash(i + 321)) + (hash(i + 322) - .5) * 500 * ph, y = -780 - ph * 520 + ph * ph * 320;
      card(x, y, 20 + hash(i + 323) * 30, 14 + hash(i + 324) * 20, i % 3 ? '#4A4560' : PAL.kraft, t * 4 + i, { torn: 1, shadow: false });
    }
  }
  // the curve continues straight up from where the banner ends
  const extX = y => TOP[0] + 28 * (1 - Math.exp((y - TOP[1]) / 260));
  function curveExt(tipY) {
    const pts = [];
    for (let y = TOP[1]; y > tipY; y -= 40) pts.push([extX(y), y]);
    pts.push([extX(tipY), tipY]);
    if (pts.length < 2) return;
    marker(pts, alpha(PAL.red, .25), 46, { rough: 0 });
    marker(pts, PAL.red, 20, { rough: 1.5 });
    marker(pts, PAL.pink, 7, { rough: .8, alpha: .8 });
  }
  function shotCrane(t, a, b) {
    const q = clamp((t - a) / (b - a)), e = ease(q);
    const cy = lerp(470, -1500, e), cx = lerp(1250, 1440, e), z = lerp(1.12, .95, e);
    const tipY = Math.min(TOP[1], cy - 260 / z);
    camBegin(cx, cy, z, lerp(0, .02, e));
    if (cy - 540 / z < -380) upperWorld(t);
    if (cy + 540 / z > -420) stage(t, { fountains: q < .3 });
    curveExt(tipY);
    // milestones ticked off on the way up (callbacks to V4.4 "Welcome, AGI!" and V4.13 "Super, by decree")
    [[-560, 'AGI ✓', PAL.yellow], [-1080, 'SUPER ✓', PAL.mint], [-1560, '???', PAL.pink]].forEach(([y, s, c]) => {
      if (tipY > y + 30) return;
      const k = clamp((y + 30 - tipY) / 120), x = extX(y);
      marker([[x - 34, y], [x + 34, y]], PAL.cream, 7, { rough: 1 });
      ctx.save(); ctx.translate(x - 56, y); ctx.scale(backOut(k), backOut(k));
      txt(s, 0, 0, 68, c, { font: 'marker', align: 'right', rot: -.06 });
      ctx.restore();
    });
    const hy = BY - 6, hx = curveXAtY(hy);
    txt('YOU ARE HERE', hx - 190, hy - 44, 42, PAL.cream, { font: 'marker', rot: -.05 });
    arrow(hx - 170, hy - 14, hx - 22, hy, PAL.cream, 6, { bend: .2 });
    spark(extX(tipY), tipY, 50, 1480);
    if (cy + 540 / z > -600) confetti(t, 40, { y0: cy - 700, y1: 1100, x0: cx - 1100, x1: cx + 1100 });
    camEnd();
  }

  // L3 — Clawd close-up, hook stacked on the left.
  function shotClose(t) {
    const w = win(2), lt = t - w.a, [sx, sy] = shakeXY(t, 7 * pulse(t, 5));
    const z = lerp(1.95, 1.75, easeOut(clamp(lt / 2))) * (1 + pulse(t, 8) * .015);
    camBegin(700 + sx, 655 + sy, z, .02);
    stage(t, { divers: false });
    confetti(t, 50, { x0: 200, x1: 1500, y0: 250, y1: 1100 });
    camEnd();
    hookWords(t, w, [
      { idx: [0, 1], y: 190, size: 110, x: 80, align: 'left', rot: -.04 },
      { idx: [2], y: 350, size: 130, x: 110, align: 'left', rot: .02 },
      { idx: [3], y: 500, size: 110, x: 150, align: 'left', rot: -.03 },
      { idx: [4], y: 670, size: 150, x: 60, align: 'left', rot: .03 }], 40);
    hideCaption();
  }

  // L4 — "Now we swear we'll try to pace it — but we'd rather race it!"
  const U_SLOW = .2, U_RACE = .593;   // slow-mo starts / the flag drops on "but"
  function paceWarp(t, w) {
    const d = w.b - w.a, tA = w.a + U_SLOW * d, tB = w.a + U_RACE * d, bl = BL();
    if (t < tA) return t;
    if (t < tB) return tA + (t - tA) * .15;
    const k = Math.round(-(tB - BEAT0) / bl);   // double speed, phase-locked to the real beat grid
    return BEAT0 + 2 * (t - BEAT0) + k * bl;
  }
  // the sign letters: P A C E, with the P torn off and replaced by a red R
  const SIGN = [['P', 'abril', PAL.yellow, PAL.ink], ['A', 'anton', PAL.white, PAL.blue], ['C', 'bungee', PAL.pink, PAL.ink], ['E', 'shrikhand', PAL.sky, PAL.ink]];
  function glyph(ch, x, y, size, paper, ink, font, rot, s = 1, seed = 1) {
    const gw = textW(ch, size, font) + size * .3;
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot); ctx.scale(s, s);
    scrap(ctrRect(0, 0, gw, size * 1.2), paper, { torn: 1.5, seed, step: 12, shadow: [4, 5] });
    txt(ch, 0, size * .04, size, ink, { font });
    ctx.restore();
    return gw;
  }
  function paceSign(x, y, rot, tear, rk) {
    // tear: 0..1 the P ripping away; rk: 0..1 the R slamming on
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot);
    scrap(rectPts(-10, 40, 20, 300), '#8B5A2B', { torn: .6, seed: 1490 });
    scrap(ctrRect(0, 0, 440, 190), PAL.white, { torn: 2, seed: 1491, ink: PAL.ink, sw: 5, shadow: [8, 10] });
    const size = 120, xs = [-150, -52, 48, 148];
    SIGN.forEach(([ch, f, paper, ink], i) => {
      if (i === 0) {
        if (rk > 0) glyph('R', xs[0], 0, size * 1.08, PAL.red, PAL.white, 'rammetto', -.08, lerp(2.2, 1, backOut(rk, 2.5)), 1510);
        if (tear < 1) {
          const k = easeIn(tear);
          ctx.save(); ctx.translate(xs[0] - k * 300, -k * 380 + k * k * 60); ctx.rotate(-k * 4);
          glyph(ch, 0, 0, size, paper, ink, f, (hash(i + 40) - .5) * .2 - tear * .3, 1 + tear * .3, 1500 + i);
          ctx.restore();
        }
      } else glyph(ch, xs[i], 0, size, paper, ink, f, (hash(i + 40) - .5) * .2 + jit(.02), 1, 1500 + i);
    });
    ctx.restore();
  }
  function checkeredFlag(x, y, w, h, rot, t) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot);
    ctx.fillStyle = 'rgb(28 26 31 / .3)'; ctx.fillRect(10, 14, w, h);
    const nx = 8, ny = 5;
    for (let i = 0; i < nx; i++) for (let j = 0; j < ny; j++) {
      const wave = u => Math.sin(u * 4 - t * 16) * 22 * u;
      const u0 = i / nx, u1 = (i + 1) / nx;
      ctx.fillStyle = (i + j) % 2 ? PAL.white : PAL.ink;
      tracePath([[u0 * w, j * h / ny + wave(u0)], [u1 * w, j * h / ny + wave(u1)], [u1 * w, (j + 1) * h / ny + wave(u1)], [u0 * w, (j + 1) * h / ny + wave(u0)]]);
      ctx.fill();
    }
    marker([[0, -60], [0, h + 260]], '#B8B8C4', 16, { rough: 0 });
    scrap(ellPts(0, -66, 16, 16, 12), PAL.gold, { torn: .5, shadow: false });
    ctx.restore();
  }
  function shotPace(t) {
    const w = win(3), d = w.b - w.a, u = (t - w.a) / d;
    const tB = w.a + U_RACE * d, fast = t >= tB, tw = paceWarp(t, w);
    const slow = u >= U_SLOW && !fast;
    const signUp = easeOut(clamp((u - .04) / .12));
    const [sx, sy] = fast ? shakeXY(t, 12) : [0, 0];
    const z = fast ? 1.3 + pulse(t, 6) * .05 : lerp(1.22, 1.32, u / U_RACE);
    camBegin(930 + sx, 560 + sy, z, fast ? Math.sin(t * 20) * .012 : 0);
    let pose;
    atTime(tw, () => {
      pose = stage(tw, { aL: lerp(-.8, 1.2, signUp), eyes: 'shades', mouth: fast ? 'scream' : slow ? 'o' : undefined });
      confetti(tw, 70, fast ? { streak: 70 } : {});
    });
    // a halo while swearing to pace it
    const [hx, hy] = handOf(pose, -1);
    if (!fast && u > U_SLOW + .03) { ctx.strokeStyle = PAL.gold; ctx.lineWidth = 10; ctx.beginPath(); ctx.ellipse(CX, pose.y + pose.dy * U - 11.6 * U, 76, 17, 0, 0, TAU); ctx.stroke(); }
    const tear = clamp((u - .655) / .07), rk = clamp((u - .73) / .06);
    paceSign(hx - 10, hy - 330 + (1 - signUp) * 500, -.05 + (fast ? Math.sin(t * 25) * .04 : wob(tw, .5) * .03), tear, rk);
    camEnd();
    // slow-mo: cold tint + label; the racing stripe wipes it away
    const wipe = clamp((t - tB) / .24), edge = lerp(-500, W + 900, wipe);
    if (slow || (fast && wipe < 1)) {
      ctx.save();
      if (fast) { tracePath([[edge, -50], [W + 50, -50], [W + 50, H + 50], [edge - 400, H + 50]]); ctx.clip(); }
      ctx.globalCompositeOperation = 'multiply'; ctx.fillStyle = '#8FB8E8'; ctx.fillRect(0, 0, W, H);
      ctx.globalCompositeOperation = 'source-over';
      dymo('SLOW-MO', 250, 110, 44, PAL.blue, { rot: -.04 });
      ctx.restore();
    }
    if (fast) {
      // speed lines
      for (let i = 0; i < 44; i++) {
        const a = hash(i + 600) * TAU, r0 = 260 + ((t * 2600 + hash(i + 601) * 1400) % 1400), L = 120 + hash(i + 602) * 200;
        ctx.strokeStyle = alpha(i % 4 ? PAL.white : PAL.yellow, .75); ctx.lineWidth = 5 + hash(i + 603) * 6;
        ctx.beginPath(); ctx.moveTo(W / 2 + Math.cos(a) * r0, H / 2 + Math.sin(a) * r0 * .7); ctx.lineTo(W / 2 + Math.cos(a) * (r0 + L), H / 2 + Math.sin(a) * (r0 + L) * .7); ctx.stroke();
      }
      if (wipe >= 1) dymo('2× SPEED', 250, 110, 44, PAL.red, { rot: .04 });
      // the racing stripe itself
      if (wipe < 1) {
        const stripe = (off, wd, col) => { tracePath([[edge - off, -60], [edge - off + wd, -60], [edge - off + wd - 400, H + 60], [edge - off - 400, H + 60]]); ctx.fillStyle = col; ctx.fill(); };
        stripe(0, 150, PAL.red); stripe(170, 70, PAL.white); stripe(260, 150, PAL.red);
      }
    }
    // the checkered flag drops at "but"
    const fk = (t - (tB - .15)) / .5;
    if (fk > 0 && fk < 1.6) {
      const drop = backOut(clamp(fk * 1.5), 1.6);
      checkeredFlag(1250, lerp(-520, 190, drop) - Math.max(0, fk - 1.1) * 1600, 470, 290, lerp(-.9, .12, drop) + Math.sin(t * 14) * .05, t);
    }
  }

  // L5 — everybody jumps; freeze-frame at the peak.
  const FREEZE_U = .24;
  const jumpAt = u => u < .07 ? -12 * Math.sin(u / .07 * Math.PI) : 150 * easeOut(clamp((u - .07) / (FREEZE_U - .07)));
  const jumpPose = u => ({ jump: Math.max(0, jumpAt(u)), aL: 1.35, aR: 1.25, mouth: 'scream', eyes: 'shades', huggyHands: 1, roboArms: 1.1, sq: u < .07 ? .12 * Math.sin(u / .07 * Math.PI) : -.06, divers: false });
  const HOOK5 = [{ idx: [0, 1, 2], y: 215, size: 128, x: 860 }, { idx: [3, 4], y: 385, size: 165, x: 880 }];
  // The frozen photo: draw the stage at the freeze instant, then print it as a pink riso duotone.
  function frozen(t, w5, duo = 1) {
    const d = w5.b - w5.a, tf = w5.a + FREEZE_U * d, since = t - tf;
    const z = 1.04 + clamp(since / 3) * .06;
    atTime(tf, () => {
      camBegin(960, 540, z, 0);
      stage(tf, jumpPose(FREEZE_U));
      confetti(tf, 70);
      camEnd();
    });
    if (duo > 0) {
      ctx.save(); ctx.setTransform(RS, 0, 0, RS, 0, 0);
      ctx.globalAlpha = duo; ctx.filter = 'grayscale(1) contrast(1.45) brightness(1.2)'; ctx.drawImage(canvas, 0, 0, W, H); ctx.filter = 'none';
      ctx.globalCompositeOperation = 'multiply'; ctx.globalAlpha = duo * .9; ctx.fillStyle = '#FF6FB5'; ctx.fillRect(0, 0, W, H);
      ctx.restore();
      halftone(rectPts(0, 0, W, H), PAL.ink, { cell: 7, dot: .22, op: .16 * duo });
    }
    return z;
  }
  function shotJump(t) {
    const w = win(4), d = w.b - w.a, u = (t - w.a) / d, tf = w.a + FREEZE_U * d;
    if (t < tf) {
      const [sx, sy] = shakeXY(t, 6);
      camBegin(960 + sx, 540 + sy, 1.04, 0);
      stage(t, jumpPose(u));
      confetti(t, 70);
      camEnd();
    } else {
      const since = t - tf, z = frozen(t, w, clamp(since / .08));
      // the one GPU that never stops (a hint): drawn live, in colour, over the frozen print
      camBegin(960, 540, z, 0); liveGPU(t); camEnd();
      if (since < .12) { ctx.fillStyle = alpha(PAL.white, 1 - since / .12); ctx.fillRect(0, 0, W, H); }
      hideStamp();   // the clock stops with the picture
    }
    hookWords(t, w, HOOK5, 80);
    hideCaption();
  }

  // L6 + outro — the hook falls off, the lights go out; the GPU in the dark; the "AND ON" tunnel.
  const BANKS = [0, 5, 1, 4, 2, 3];   // vertical light banks, outside-in
  function bankTimes(w) {
    const nb = Math.ceil(bpOf(w.a + .13 * (w.b - w.a)));
    return BANKS.map((_, i) => BEAT0 + (nb + i * .5) * BL());
  }
  function darkPage() {
    ctx.fillStyle = '#0D0B12'; ctx.fillRect(0, 0, W, H);
    halftone(rectPts(0, 0, W, H), '#1B1830', { cell: 12, dot: .3, op: 1, multiply: false });
  }
  // Clawd in the dark: a near-black silhouette (cached so it doesn't boil), looking at the GPU.
  // (x, y) = ground point on screen, u = size; his shades catch the LED; glint 0..1 = a passing glint.
  function darkClawd(x, y, u, t, glint = 0) {
    const B = 60, img = cached('c9-dark-clawd', 16 * B, 16 * B, (cw, ch) => atTime(0, () => {
      clawd(cw / 2, ch - 3 * B, B, { hat: 'mohawk', eyes: 'shades', mouth: 'flat', aL: -1.1, aR: -1.1, shadow: false });
      ctx.globalCompositeOperation = 'source-atop'; ctx.fillStyle = 'rgb(8 11 11 / .9)'; ctx.fillRect(0, 0, cw, ch);
    }));
    const k = u / B;
    blit(img, x, y - (img.lh / 2 - 3 * B) * k, { s: k });
    const ey = y - 6.2 * u, on = LED_ON(t);
    for (const s of [-1, 1]) { ctx.fillStyle = alpha('#6CF2B0', on ? .85 : .22); tracePath(ellPts(x + s * 2.3 * u + .35 * u, ey - .05 * u, .3 * u, .13 * u, 10)); ctx.fill(); }
    if (glint > 0 && glint < 1) scrap(starPts(x - 2.3 * u + .8 * u, ey - .35 * u, 2 * u * Math.sin(glint * Math.PI), .16, 4, glint * .8), PAL.white, { torn: 0, shadow: false });
  }
  const FG_CLAWD = [330, 1250, 62];   // over-the-shoulder spot: Clawd watching it train on
  function shotDark(t) {
    const w = win(5), d = w.b - w.a, u = (t - w.a) / d;
    hideStamp();
    const bt = bankTimes(w), allOut = bt[bt.length - 1] + .1, w5 = win(4);
    if (t < allOut) {
      // the frozen photo, still up; on "But…" the hook words drop off the page; then the lights go out, bank by bank
      const z = frozen(t, w5, 1);
      const f0 = w.a + .12;
      hookWords(t, w5, HOOK5, 80, j => {
        const k = t - (f0 + [.3, .12, .45, 0, .2][j]);
        if (k <= 0) return { dx: 0, dy: 0, rot: 0 };
        return { dx: (hash(j + 90) - .5) * 200 * k, dy: 2600 * k * k - 60 * k, rot: (hash(j + 91) - .5) * 3 * k };
      });
      BANKS.forEach((bank, i) => {
        const k = t - bt[i]; if (k < 0) return;
        if (k < .1 && Math.floor(t * 30) % 2) return;   // flicker
        ctx.fillStyle = '#0D0B12'; ctx.fillRect(bank * 320 - 1, 0, 322, H);
        if (k < .6) txt('click.', bank * 320 + 160, 70 + (i % 2) * 44, 44, alpha(PAL.cream, 1 - k / .6), { font: 'typewriter' });
      });
      camBegin(960, 540, z, 0); liveGPU(t, { glow: clamp((t - bt[1]) / .3) }); camEnd();
      return;
    }
    const tDive = w.a + .58 * d;   // "…train on" ends: the GPU recedes into the dark and becomes the end of the tunnel
    if (t < tDive) {
      darkPage();
      const tPush = allOut + .5, q = clamp((t - tPush) / (tDive - tPush)), e = 1 - (1 - q) ** 2.2;
      const z = lerp(1, 3.3, e), cx = lerp(1100, GX - 10, e), cy = lerp(560, GY - 38, e);
      camBegin(cx, cy, z, 0);
      glowAt(GX, GY, 700, '#3BE08A', .07);
      liveGPU(t, { glow: 1, lcd: true });
      camEnd();
      // Clawd, in the dark, watching it; he drifts into an over-the-shoulder silhouette
      const fk = ease(clamp(q * 1.4)), px = (CX - cx) * z + W / 2, py = (GROUND - cy) * z + H / 2;
      darkClawd(lerp(px, FG_CLAWD[0], fk), lerp(py, FG_CLAWD[1], fk), lerp(U * z, FG_CLAWD[2], fk), t, (t - (allOut + .08)) / .4);
      return;
    }
    corridor(t, w);
  }

  // The tunnel: nested cut-paper frames (a tunnel book) receding into the GPU's LED;
  // each sung "and on" is typed at the front and drifts away down the tunnel.
  const VP = [960, 430];
  function ringPath(s, seed) {
    const o = roughen(ctrRect(VP[0], VP[1], 2600 * s, 1480 * s), 2, 40, seed), i = roughen(ctrRect(VP[0], VP[1], 2060 * s, 1170 * s), 2.5, 30, seed + 7);
    ctx.beginPath();
    for (const P of [o, i]) P.forEach(([x, y], n) => n ? ctx.lineTo(x, y) : ctx.moveTo(x, y)), ctx.closePath();
    return i;
  }
  function corridor(t, w) {
    const d = w.b - w.a, t0 = w.a + .58 * d;
    darkPage();
    const R = .62, speed = 1.45, z = (t - t0) * speed, pull = clamp((t - t0) / .5);
    const on = LED_ON(t);
    // the green light at the end
    glowAt(VP[0], VP[1], 260, '#3BE08A', on ? .35 : .15);
    // the sung "and on"s (typed at the front, then receding) + echoes further down the tunnel
    const sung = [.72, .80, .895].map(f => w.a + f * d);
    const items = [];
    const kk = Math.floor(z);
    for (let k = -kk; k < -kk + 11; k++) items.push({ ring: true, dep: k + z, id: k });
    sung.forEach((ti, i) => { if (t >= ti) items.push({ dep: (t - ti) * speed * 1.1, str: i === 2 ? 'AND ON?' : 'AND ON…', k: clamp((t - ti) / .3), a: 1 }); });
    const echo = clamp((t - sung[2] - .3) / 1);
    if (echo > 0) for (let k = 1; k <= 5; k++) items.push({ dep: (t - sung[0]) * speed * 1.1 + k * 1.15, str: 'AND ON…', k: 1, a: echo * (.8 - k * .12) });
    items.sort((a, b) => b.dep - a.dep);
    const ledDrawn = { v: false };
    for (const it of items) {
      const s = R ** it.dep;
      if (it.ring) {
        if (s > 1.4 || 2600 * s < 30) continue;
        const shade = clamp(it.dep / 9);
        ctx.save(); ctx.translate(12 * s, 16 * s); ringPath(s, 1600 + it.id * 3); ctx.fillStyle = 'rgb(0 0 0 / .45)'; ctx.fill('evenodd'); ctx.restore();
        const inner = ringPath(s, 1600 + it.id * 3);
        ctx.fillStyle = mixCol(it.id % 2 ? '#2E2944' : '#262139', '#0D0B12', shade); ctx.globalAlpha = pull; ctx.fill('evenodd');
        // green rim light from the LED on the inner edge, stronger deeper in
        ctx.strokeStyle = alpha('#6CF2B0', (.08 + .3 * shade) * (on ? 1 : .6) * pull); ctx.lineWidth = Math.max(1, 4 * s); tracePath(inner); ctx.stroke();
        ctx.globalAlpha = 1;
        continue;
      }
      const size = 160 * s; if (size < 5) continue;
      typed(it.str, VP[0], VP[1] + 420 * s, size, it.k, mixCol('#F4EBD6', '#7A7F8C', clamp(it.dep / 4)), { alpha: it.a });
    }
    ctx.fillStyle = on ? '#8BFFB5' : '#2A5A3C'; tracePath(ellPts(VP[0], VP[1], 8, 8, 12)); ctx.fill();
    // the GPU pulling away to become that green light
    if (pull < 1) {
      const s = lerp(1, .015, easeIn(pull));
      ctx.save(); ctx.translate(VP[0], VP[1]); ctx.scale(s * 3.3, s * 3.3); ctx.translate(-LED[0], -LED[1]);
      liveGPU(t, { glow: 1, lcd: true }); ctx.restore();
    }
    darkClawd(FG_CLAWD[0], FG_CLAWD[1] + Math.sin(t * 2.2) * 4, FG_CLAWD[2], t);
  }

  // ---------------- the back cover ----------------
  function backCover(t, t0, sc = 1) {
    const lt = (t - t0) / sc;   // sc < 1 compresses the reveal if the outro gets shorter
    // cream stock, halftone corner shading, staples
    scrap(rectPts(0, 0, W, H), PAL.paper, { torn: 3, seed: 1700, shadow: [14, 18] });
    halftone([[W * .5, H], [W, H * .3], [W, H]], PAL.pink, { cell: 16, dot: .3, op: .45 });
    halftone([[0, 0], [W * .3, 0], [0, H * .5]], PAL.sky, { cell: 16, dot: .3, op: .45, angle: 45 });
    for (const y of [290, 790]) { ctx.fillStyle = '#9A9AA6'; ctx.fillRect(34, y, 9, 76); ctx.fillStyle = '#6E6E78'; ctx.fillRect(40, y, 3, 76); }
    // title
    const tk = clamp(lt / .8);
    ransom("WE DIDN'T START", 960, 150, 118, { seed: 1710, pop: tk * 1.25, rot: -.015, fonts: READABLE });
    ransom('THE SCALING', 960, 340, 156, { seed: 1721, pop: clamp(tk * 1.25 - .3) * 1.4, rot: .012, fonts: READABLE });
    // credits, typed
    typed('lyrics: Domenic & Claude', 590, 540, 50, clamp((lt - .85) / .3), PAL.ink);
    typed('music: Lyria 3.5', 590, 610, 50, clamp((lt - 1.05) / .25), PAL.ink);
    typed('video: Claude Opus 5.5', 590, 685, 58, clamp((lt - 1.25) / .35), PAL.ink);
    if (lt > 1.6) underline(300, 880, 727, PAL.red, 7, clamp((lt - 1.6) / .25));   // (at k = 0 it would leave a red dot)
    // the date ticker, one last time: the day after the last verse
    const sk = clamp((lt - 1.85) / .16);
    if (sk > 0) stamp('SEP 23, 2026', 590, 840, 66, PAL.red, -.07, { pop: sk });
    // cover art: Clawd, logged off, asleep against the GPU that trains on
    const gx = 1500, gy = 740, gs = 27;
    ctx.fillStyle = 'rgb(28 26 31 / .12)'; tracePath(ellPts(1400, 885, 400, 22, 24)); ctx.fill();
    marker([[1040, 885], [1790, 880]], PAL.ink, 7, { rough: 1.2 });
    gpu(gx, gy + 60, gs, { label: 'H100', t, rot: -.02 });
    const lx = gx + 4.1 * gs, ly = gy + 60 - 2.1 * gs, on = LED_ON(t);
    if (on) glowAt(lx, ly, 60, '#3BE08A', .5);
    ctx.fillStyle = on ? '#3BE08A' : '#1D3A28'; tracePath(ellPts(lx, ly, 10, 10, 12)); ctx.fill();
    // sticky note: the loss curve, still going down
    ctx.save(); ctx.translate(1560, 560); ctx.rotate(.07);
    scrap(ctrRect(0, 0, 230, 190), PAL.yellow, { torn: 1.2, seed: 1730 });
    tape(0, -95, 110, -.08, { h: 30, seed: 1734 });
    const pts = []; for (let i = 0; i <= 30; i++) { const x = -88 + i / 30 * 176; pts.push([x, -42 + 108 * (1 - Math.exp(-i / 7)) + (hash(i + 1731) - .5) * 7]); }
    marker(partial(pts, .55 + .45 * frac(t * .3)), PAL.red, 6, { rough: .5 });
    txt('still going ↓', 0, -64, 30, PAL.ink, { font: 'marker' });
    ctx.restore();
    clawd(1180, 885, 22, { hat: 'mohawk', eyes: 'closed', mouth: 'smile', aL: -1.1, aR: -.4, rot: .1, sq: .035 * Math.sin(t * 2.4), blush: true });
    // zzz
    for (let i = 0; i < 3; i++) {
      const ph = frac(t * .45 + i / 3);
      txt('z', 1250 + ph * 110 + Math.sin(ph * 6) * 14, 640 - ph * 200, 40 + ph * 34, alpha(PAL.ink, Math.sin(ph * Math.PI)), { font: 'marker', rot: -.2 });
    }
    // barcode whose bars trace a loss curve
    const bx = 1580, by = 990;
    scrap(ctrRect(bx + 60, by - 8, 250, 120), PAL.white, { torn: 1, seed: 1740, shadow: [4, 5] });
    for (let i = 0; i < 36; i++) {
      if (hash(i + 1741) < .28) continue;
      const hgt = 72 * (.3 + .7 * Math.exp(-i / 11)), bw = hash(i + 1742) < .5 ? 3 : 5;
      ctx.fillStyle = PAL.ink; ctx.fillRect(bx - 48 + i * 6, by + 26 - hgt, bw, hgt);
    }
    txt('ISSUE #1 · FREE · COPY ME', bx + 60, by + 40, 16, PAL.ink, { font: 'code' });
  }

  // ================= registration =================
  section('C4', (p, lt, d, t) => {
    const i = lineIdx(t);
    if (i === 0) return shotWide(t);
    if (i === 1) {
      const w = win(1), split = w.a + .42 * (w.b - w.a);
      return t < split ? shotDive(t, w.a, split) : shotCrane(t, split, w.b);
    }
    if (i === 2) return shotClose(t);
    if (i === 3) return shotPace(t);
    if (i === 4) return shotJump(t);
    return shotDark(t);
  });

  section('outro', (p, lt, d, t) => {
    hideCaption(); hideStamp();
    const sc = clamp(d / 4.8, .65, 1), flipA = .7 * sc, flipB = flipA + .55 * sc;  // the zine is turned over
    const zoom = lerp(1, .9, ease(clamp((lt - .15 * sc) / (.5 * sc))));
    ctx.fillStyle = '#2B2320'; ctx.fillRect(0, 0, W, H);           // the table
    halftone(rectPts(0, 0, W, H), '#140F0D', { cell: 14, dot: .3, op: .6 });
    const f = clamp((lt - flipA) / (flipB - flipA)), ang = ease(f) * Math.PI, sx = Math.cos(ang);
    ctx.save(); ctx.translate(W / 2, H / 2); ctx.scale(zoom * Math.max(.002, Math.abs(sx)), zoom * (1 + .05 * Math.sin(ang))); ctx.translate(-W / 2, -H / 2);
    if (sx > 0) {
      ctx.save(); tracePath(roughen(rectPts(0, 0, W, H), 3, 16, 1750, false)); ctx.clip();
      corridor(t, win(5));
      ctx.restore();
    } else backCover(t, span('outro').start + flipB, sc);
    ctx.restore();
  });

  // =====================================================================================================================
  // The vertical video (1080 × 1920): the singularity show filmed from the pit, one tall frame at a time; then the lights go out,
  // the tunnel, and the zine turned over on the table the intro slapped it onto.
  //   L1    the show from the pit; the curve runs up the banner and shoots straight up off it, out of the top of the frame
  //   L2a   agents leap off the stage, arc up and fall at the lens, growing, out through the bottom of the frame
  //   L2b   a tilt up the curve after its tip: off the banner, through the roof, past AGI ✓, SUPER ✓ and ??? into the night
  //   L3    the fancam: Clawd close up under the hook, the pit in front
  //   L4    Clawd holds the PACE sign up, haloed, in slow motion… the flag drops, the racing stripe wipes DOWN the frame, P → R
  //   L5    everybody jumps, higher than in the wide frame; freeze at the peak, a pink duotone print; only the GPU still moves
  //   L6    the hook falls off the page; the lights go out bank by bank, top to bottom; a push into the GPU; AND ON recedes down a
  //         tall tunnel into its green LED
  //   outro the tunnel is a page of the A5 zine, lying on the intro's table; it's turned over: the portrait back cover, the
  //         credits in a column, Clawd asleep against the GPU at its foot, the LED still blinking
  // The hook is the cover's title in three lines (vertical.js's vhook, its words and papers), each word landing as it's sung.
  // The GPU that trains on: the stacks at the stage's sides are out of the tall frame, so here it sits on a road case at the stage's
  // lip, right of Clawd, from L1 on (GX, GY, GS above; gpuUp() adds it to stage()).
  // =====================================================================================================================
  const vdark = (c = '#0E0A1C') => { ctx.fillStyle = c; ctx.fillRect(0, 0, W, H); };
  const vFlash = (t, t0, dur, a) => { const k = t - t0; if (k >= 0 && k < dur) { ctx.fillStyle = alpha(PAL.white, a * (1 - k / dur)); ctx.fillRect(0, 0, W, H); } };
  // the curve's extension leaves the banner 1.1 s into L1 and races straight up out of the frame; later shots see it running on up
  const vTip = t => { const a = t - (win(0).a + 1.1); return a <= 0 ? TOP[1] + 1 : TOP[1] - 1300 * a * a - 200 * a; };
  const extUp = () => curveExt(-3200);
  // the GPU on its road case at the stage's lip, in front of the drums
  function vStageGPU(t) {
    const cy = GY + 3.3 * GS, x0 = GX - 6.4 * GS, w = 12.8 * GS;
    scrap(rectPts(x0, cy, w, 74), '#2A2730', { torn: .8, seed: 1780, shadow: [6, 8] });
    for (const cx of [x0 + 8, x0 + w - 30]) for (const yy of [cy + 6, cy + 46]) scrap(rectPts(cx, yy, 22, 22), '#8A8794', { torn: .3, shadow: false });
    txt('DO NOT UNPLUG', GX, cy + 39, 17, alpha(PAL.cream, .85), { font: 'mono' });
    gpu(GX, GY, GS, { label: 'H100', hot: pulse(t, 4) * .6 });
  }
  // (and leaves the band's name off the banner: the tall frame sets the hook, signs and labels where it would be)
  const gpuUp = o => ({ bannerTitle: false, ...o, afterBand: () => vStageGPU(T) });

  // ---------- L1: the show from the pit; the curve shoots up off the banner and out of the frame ----------
  function vWide(t) {
    const w = win(0), lt = t - w.a, k = easeOut(clamp(lt / .55)), [sx, sy] = shakeXY(t, 9 * pulse(t, 5)), tip = vTip(t);
    vdark();
    inStage(t, () => {
      stage(t, gpuUp({ curveK: lerp(.6, 1, easeIn(clamp(lt / 1.1))), afterVenue: () => curveExt(tip) }));
      if (tip < TOP[1]) spark(extX(tip), tip, 60, 1480);
    }, lerp(1060, 1170, k) + sx, lerp(640, 500, k) + sy, lerp(1.4, 1, k) + pulse(t, 8) * .01);
    confetti(t, 70);
    pitCrowd(t, 1790);
    vhook(t, LN()[0], { y: 330, cut: w.b });
    vFlash(t, w.a, .1, .75);
    hideCaption(); hideStamp();
  }

  // ---------- L2a: "It was always training": agents leap off the stage and fall at the lens ----------
  function vDive(t, a, b) {
    const q = clamp((t - a) / (b - a)), [sx, sy] = shakeXY(t, 6 * pulse(t, 5)), z = 1.3, cy = 760;
    vdark();
    inStage(t, () => stage(t, gpuUp({ afterVenue: extUp })), lerp(870, 1050, ease(q)) + sx, cy + sy, z);
    confetti(t, 50);
    pitCrowd(t, 1790, { s: 170, seed: 991 });
    // one a beat: off the stage lip, up in an arc, then down at the camera, growing, and out through the bottom of the frame
    const lip = 960 + (STAGE_Y + 20 - cy) * z, bp = bpOf(t);
    for (let n = Math.floor(bp) - 2; n <= Math.floor(bp); n++) {
      const k = (bp - n) / 2.4; if (k < 0 || k > 1) continue;
      const side = hash(n + 5) < .5 ? -1 : 1, x0 = 540 + (hash(n + 6) - .5) * 600, x1 = clamp(x0 + side * (120 + hash(n + 7) * 200), 200, 880);
      const x = lerp(x0, x1, k), y = lerp(lip, 2500, k ** 2.4) - Math.sin(Math.min(1, k * 1.2) * Math.PI) * 700, s = lerp(20, 330, k ** 2.2);
      agent(x, y, s, { rot: k * TAU * .8 * side, eyes: n % 2 ? 'spark' : 'heart', col: AGENT_COLS[n % 4], bar: AGENT_BARS[n % 4], walk: t * 4 });
    }
  }

  // ---------- L2b: "and the curves kept gaining": the camera chases the curve's tip up, through the roof, into the night ----------
  function vCrane(t, a, b) {
    const q = clamp((t - a) / (b - a)), e = ease(q);
    const cy = lerp(560, -1760, e), cx = lerp(1300, 1500, ease(clamp(q / .5))), z = lerp(1, .9, e);
    // the tip starts far ahead (it left the frame in L1); the camera catches it up by the roof, then it leads the way
    const tipY = Math.min(TOP[1], cy - lerp(1400, 520, ease(clamp(q / .5))) / z);
    vdark('#07061A');
    hideStamp();   // (the curve runs up the middle of the frame, through where the stamp sits)
    inStage(t, () => {
      if (cy - 960 / z < -380) {
        upperWorld(t);
        scrap(ellPts(1250, -2280, 150, 150, 36), PAL.cream, { torn: 1.5, seed: 1470, tone: { color: PAL.kraft, cell: 14, dot: .3, op: .6 } });
      }
      if (cy + 960 / z > -420) stage(t, gpuUp({ fountains: q < .3 }));
      curveExt(tipY);
      [[-560, 'AGI ✓', PAL.yellow], [-1080, 'SUPER ✓', PAL.mint], [-1560, '???', PAL.pink]].forEach(([y, s, c]) => {
        if (tipY > y + 30) return;
        const k = clamp((y + 30 - tipY) / 120), x = extX(y);
        marker([[x - 40, y], [x + 40, y]], PAL.cream, 8, { rough: 1 });
        ctx.save(); ctx.translate(x - 64, y); ctx.scale(backOut(k), backOut(k));
        txt(s, 0, 0, 86, c, { font: 'marker', align: 'right', rot: -.06 });
        ctx.restore();
      });
      const hy = BY - 6, hx = curveXAtY(hy);
      txt('YOU ARE HERE', hx - 210, hy - 50, 50, PAL.cream, { font: 'marker', rot: -.05 });
      arrow(hx - 180, hy - 16, hx - 22, hy, PAL.cream, 7, { bend: .2 });
      spark(extX(tipY), tipY, 56, 1480);
      if (cy + 960 / z > -600) confetti(t, 40, { y0: cy - 1100, y1: 1100, x0: cx - 800, x1: cx + 800 });
    }, cx, cy, z);
    // the pit, nearer the lens, drops out of the bottom of the frame first
    const drop = (560 - cy) * 1.4;
    if (drop < 700) pitCrowd(t, 1790 + drop);
  }

  // ---------- L3: the fancam: Clawd close up under the hook ----------
  function vClose(t) {
    const w = win(2), lt = t - w.a, [sx, sy] = shakeXY(t, 7 * pulse(t, 5));
    const z = lerp(2.3, 2.1, easeOut(clamp(lt / 2))) * (1 + pulse(t, 8) * .015);
    vdark();
    inStage(t, () => stage(t, gpuUp({ divers: false })), 960 + sx, 615 + sy, z);
    confetti(t, 60);
    pitCrowd(t, 1830, { s: 190, seed: 997 });
    vhook(t, LN()[2], { y: 330, cut: w.b });
    hideCaption(); hideStamp();
  }

  // ---------- L4: PACE, haloed, in slow motion… the flag drops, the stripe wipes down the frame: RACE, at double speed ----------
  function vPace(t) {
    const w = win(3), d = w.b - w.a, u = (t - w.a) / d;
    const tB = w.a + U_RACE * d, fast = t >= tB, tw = paceWarp(t, w), slow = u >= U_SLOW && !fast;
    const signUp = easeOut(clamp((u - .04) / .12)), tear = clamp((u - .655) / .07), rk = clamp((u - .73) / .06);
    const [sx, sy] = fast ? shakeXY(t, 12) : [0, 0];
    const z = fast ? 1.46 + pulse(t, 6) * .05 : lerp(1.38, 1.46, u / U_RACE);
    hideStamp();
    vdark();
    ctx.save(); ctx.translate(W / 2, H / 2); ctx.rotate(fast ? Math.sin(t * 20) * .012 : 0); ctx.translate(-W / 2, -H / 2);
    inStage(t, () => {
      let pose;
      atTime(tw, () => {
        pose = stage(tw, gpuUp({ aL: lerp(-.8, 1.2, signUp), eyes: 'shades', mouth: fast ? 'scream' : slow ? 'o' : undefined }));
        confetti(tw, 70, fast ? { streak: 70 } : {});
      });
      const [hx, hy] = handOf(pose, -1);
      if (!fast && u > U_SLOW + .03) { ctx.strokeStyle = PAL.gold; ctx.lineWidth = 10; ctx.beginPath(); ctx.ellipse(CX, pose.y + pose.dy * U - 11.6 * U, 76, 17, 0, 0, TAU); ctx.stroke(); }
      paceSign(hx - 10, hy - 290 + (1 - signUp) * 800, -.05 + (fast ? Math.sin(t * 25) * .04 : wob(tw, .5) * .03), tear, rk);
    }, 790 + sx, 701 + sy, z);
    atTime(tw, () => pitCrowd(tw, 1810, { s: 175, seed: 983 }));
    ctx.restore();
    // slow-mo: a cold tint and its label; the racing stripe wipes it away, top to bottom
    const wipe = clamp((t - tB) / .3), edge = lerp(-400, H + 700, wipe), SL = 300;
    if (slow || (fast && wipe < 1)) {
      ctx.save();
      if (fast) { tracePath([[-50, edge], [W + 50, edge - SL], [W + 50, H + 50], [-50, H + 50]]); ctx.clip(); }
      ctx.globalCompositeOperation = 'multiply'; ctx.fillStyle = '#8FB8E8'; ctx.fillRect(0, 0, W, H);
      ctx.globalCompositeOperation = 'source-over';
      dymo('SLOW-MO', 430, 280, 52, PAL.blue, { rot: -.04 });
      ctx.restore();
    }
    if (fast) {
      for (let i = 0; i < 50; i++) {
        const a = hash(i + 600) * TAU, r0 = 300 + ((t * 2800 + hash(i + 601) * 1500) % 1500), L = 140 + hash(i + 602) * 220;
        ctx.strokeStyle = alpha(i % 4 ? PAL.white : PAL.yellow, .75); ctx.lineWidth = 6 + hash(i + 603) * 6;
        ctx.beginPath(); ctx.moveTo(W / 2 + Math.cos(a) * r0 * .75, 900 + Math.sin(a) * r0 * 1.2); ctx.lineTo(W / 2 + Math.cos(a) * (r0 + L) * .75, 900 + Math.sin(a) * (r0 + L) * 1.2); ctx.stroke();
      }
      if (wipe >= 1) dymo('2× SPEED', 430, 280, 52, PAL.red, { rot: .04 });
      else {
        const stripe = (off, wd, col) => { tracePath([[-60, edge - off], [W + 60, edge - off - SL], [W + 60, edge - off - wd - SL], [-60, edge - off - wd]]); ctx.fillStyle = col; ctx.fill(); };
        stripe(0, 150, PAL.red); stripe(170, 70, PAL.white); stripe(260, 150, PAL.red);
      }
    }
    // the checkered flag drops from the top of the frame at "but", then flies off up
    const fk = (t - (tB - .15)) / .5;
    if (fk > 0 && fk < 1.6) {
      const drop = backOut(clamp(fk * 1.5), 1.6);
      checkeredFlag(740, lerp(-560, 50, drop) - Math.max(0, fk - 1.1) * 2200, 470, 290, lerp(-.9, .12, drop) + Math.sin(t * 14) * .05, t);
    }
  }

  // ---------- L5: everybody jumps; freeze at the peak; the frozen print pulls back to the GPU still running ----------
  const VJ = [1010, 600, 1];   // the camera at the jump: the band filling the frame's width, the GPU at the stage's lip
  const vJumpPose = u => { const o = jumpPose(u); return { ...o, jump: o.jump * 1.1 }; };   // (the tall frame has room for more air)
  const freezeT = () => { const w5 = win(4); return w5.a + FREEZE_U * (w5.b - w5.a); };
  // the camera on the frozen print: it creeps in, as the horizontal's does
  const vJumpCam = t => [VJ[0], VJ[1], VJ[2] * (1 + clamp((t - freezeT()) / 3) * .06)];
  const vPit = t => pitCrowd(t, 1790, { jump: 1.2 });
  // The frozen photo with the camera where it is at t: the stage at the freeze instant, printed as a pink riso duotone.
  function vFrozen(t, duo = 1) {
    const tf = freezeT(), cam = vJumpCam(t);
    atTime(tf, () => {
      vdark();
      inStage(tf, () => { stage(tf, gpuUp({ ...vJumpPose(FREEZE_U), afterVenue: extUp })); confetti(tf, 70); }, ...cam);
      vPit(tf);
    });
    if (duo > 0) {
      ctx.save(); ctx.setTransform(RS, 0, 0, RS, 0, 0);
      ctx.globalAlpha = duo; ctx.filter = 'grayscale(1) contrast(1.45) brightness(1.2)'; ctx.drawImage(canvas, 0, 0, W, H); ctx.filter = 'none';
      ctx.globalCompositeOperation = 'multiply'; ctx.globalAlpha = duo * .9; ctx.fillStyle = '#FF6FB5'; ctx.fillRect(0, 0, W, H);
      ctx.restore();
      halftone(rectPts(0, 0, W, H), PAL.ink, { cell: 7, dot: .22, op: .16 * duo });
    }
    return cam;
  }
  function vJump(t) {
    const w = win(4), u = (t - w.a) / (w.b - w.a), tf = freezeT();
    if (t < tf) {
      const [sx, sy] = shakeXY(t, 6);
      vdark();
      inStage(t, () => { stage(t, gpuUp({ ...vJumpPose(u), afterVenue: extUp })); confetti(t, 70); }, VJ[0] + sx, VJ[1] + sy, VJ[2]);
      vPit(t);
    } else {
      const since = t - tf, cam = vFrozen(t, clamp(since / .08));
      // the one GPU that never stops, live and in colour on the frozen print
      inStage(t, () => liveGPU(t, { glow: clamp((t - tf - .3) / .6) * .6 }), ...cam);
      vFlash(t, tf, .12, 1);
    }
    vhook(t, LN()[4], { y: 300 });   // (a little higher than the other hooks: Clawd jumps up under it)
    hideCaption(); hideStamp();
  }

  // ---------- L6: the hook falls off; lights out, top to bottom; the GPU in the dark; the AND ON tunnel ----------
  // the GPU's road case in the dark: the stencil catches the green
  function vDarkCase(t) {
    const ky = GY + 3.3 * GS;
    scrap(rectPts(GX - 6.4 * GS, ky, 12.8 * GS, 74), '#15131A', { torn: .8, seed: 1780, shadow: false });
    txt('DO NOT UNPLUG', GX, ky + 39, 17, alpha('#6CF2B0', LED_ON(t) ? .6 : .4), { font: 'mono' });
  }
  const VFG = [190, 1990, 70];   // Clawd's silhouette, over the shoulder at the foot of the frame: ground x, y, u
  const VPUSH = [540, 860, 3.1];  // where the push leaves the GPU on screen (its centre), and the zoom
  const VVP = [540, 720];         // the tunnel's vanishing point: the LED, once the GPU has pulled away into it
  function vDark(t) {
    const w = win(5), d = w.b - w.a;
    hideStamp();
    const bt = bankTimes(w), allOut = bt[5] + .1;
    if (t < allOut) {
      const cam = vFrozen(t, 1), f0 = w.a + .12;
      vhook(t, LN()[4], { y: 300 }, i => {
        const k = t - (f0 + [.3, .12, .45, 0, .2][i]);
        return k <= 0 ? { dx: 0, dy: 0, rot: 0 } : { dx: (hash(i + 90) - .5) * 220 * k, dy: 3600 * k * k - 80 * k, rot: (hash(i + 91) - .5) * 3 * k };
      });
      // a bank of lights at a time, from the top of the frame down
      for (let i = 0; i < 6; i++) {
        const k = t - bt[i]; if (k < 0) continue;
        if (k < .1 && Math.floor(t * 30) % 2) continue;   // flicker
        ctx.fillStyle = '#0D0B12'; ctx.fillRect(0, i * 320 - 1, W, 322);
        if (k < .6) txt('click.', 170 + (i % 2) * 70, i * 320 + 90, 54, alpha(PAL.cream, 1 - k / .6), { font: 'typewriter' });
      }
      inStage(t, () => liveGPU(t, { glow: .6 + .4 * clamp((t - bt[2]) / .3) }), ...cam);
      return;
    }
    const tDive = w.a + .58 * d;
    if (t < tDive) {
      darkPage();
      const tPush = allOut + .5, q = clamp((t - tPush) / (tDive - tPush)), e = 1 - (1 - q) ** 2.2;
      const [c0x, c0y, z0] = vJumpCam(allOut), [px1, py1, z1] = VPUSH;
      const z = lerp(z0, z1, e), cx = lerp(c0x, GX + (W / 2 - px1) / z1, e), cy = lerp(c0y, GY + (H / 2 - py1) / z1, e);
      inStage(t, () => {
        glowAt(GX, GY, 700, '#3BE08A', .07);
        vDarkCase(t);
        liveGPU(t, { glow: 1, lcd: true });
      }, cx, cy, z);
      // Clawd, in the dark, watching it: he drifts into an over-the-shoulder silhouette at the foot of the frame
      const fk = ease(clamp(q * 1.4)), px = W / 2 + (CX - cx) * z, py = H / 2 + (GROUND - cy) * z;
      darkClawd(lerp(px, VFG[0], fk), lerp(py, VFG[1], fk), lerp(U * z, VFG[2], fk), t, (t - (allOut + .08)) / .4);
      return;
    }
    vCorridor(t, w);
  }
  // The tunnel, tall: nested portrait frames receding into the LED; each sung "and on" is typed at the front and drifts down it.
  function vRingPath(s, seed) {
    const o = roughen(ctrRect(VVP[0], VVP[1], 1640 * s, 2900 * s), 2, 40, seed), i = roughen(ctrRect(VVP[0], VVP[1], 1300 * s, 2300 * s), 2.5, 30, seed + 7);
    ctx.beginPath();
    for (const P of [o, i]) P.forEach(([x, y], n) => n ? ctx.lineTo(x, y) : ctx.moveTo(x, y)), ctx.closePath();
    return i;
  }
  function vCorridor(t, w) {
    const d = w.b - w.a, t0 = w.a + .58 * d;
    darkPage();
    const R = .62, speed = 1.45, z = (t - t0) * speed, pull = clamp((t - t0) / .5), on = LED_ON(t);
    glowAt(VVP[0], VVP[1], 300, '#3BE08A', on ? .35 : .15);
    // the sung "and on"s (the tag's word times, where the take has them)
    const tag = TAG(), tw = tag && wordTimes(tag);
    const sung = tw && tw.starts.length >= 5 ? [tw.starts[0], tw.starts[2], tw.starts[4]] : [.72, .80, .895].map(f => w.a + f * d);
    const items = [], kk = Math.floor(z);
    for (let k = -kk; k < -kk + 11; k++) items.push({ ring: true, dep: k + z, id: k });
    sung.forEach((ti, i) => { if (t >= ti) items.push({ dep: (t - ti) * speed * 1.1, str: i === 2 ? 'AND ON?' : 'AND ON…', k: clamp((t - ti) / .3), a: 1 }); });
    const echo = clamp((t - sung[2] - .3) / 1);
    if (echo > 0) for (let k = 1; k <= 5; k++) items.push({ dep: (t - sung[0]) * speed * 1.1 + k * 1.15, str: 'AND ON…', k: 1, a: echo * (.8 - k * .12) });
    items.sort((a, b) => b.dep - a.dep);
    for (const it of items) {
      const s = R ** it.dep;
      if (it.ring) {
        if (s > 1.4 || 1640 * s < 30) continue;
        const shade = clamp(it.dep / 9);
        ctx.save(); ctx.translate(12 * s, 16 * s); vRingPath(s, 1600 + it.id * 3); ctx.fillStyle = 'rgb(0 0 0 / .45)'; ctx.fill('evenodd'); ctx.restore();
        const inner = vRingPath(s, 1600 + it.id * 3);
        ctx.fillStyle = mixCol(it.id % 2 ? '#2E2944' : '#262139', '#0D0B12', shade); ctx.globalAlpha = pull; ctx.fill('evenodd');
        ctx.strokeStyle = alpha('#6CF2B0', (.08 + .3 * shade) * (on ? 1 : .6) * pull); ctx.lineWidth = Math.max(1, 4 * s); tracePath(inner); ctx.stroke();
        ctx.globalAlpha = 1;
        continue;
      }
      const size = 150 * s; if (size < 5) continue;
      typed(it.str, VVP[0], VVP[1] + 400 * s, size, it.k, mixCol('#F4EBD6', '#7A7F8C', clamp(it.dep / 4)), { alpha: it.a });
    }
    ctx.fillStyle = on ? '#8BFFB5' : '#2A5A3C'; tracePath(ellPts(VVP[0], VVP[1], 8, 8, 12)); ctx.fill();
    // the GPU pulling away to become that green light
    if (pull < 1) {
      const s = lerp(1, .015, easeIn(pull)), [px1, py1, z1] = VPUSH, m = easeIn(pull);
      ctx.save(); ctx.translate(lerp(px1 + (LED[0] - GX) * z1, VVP[0], m), lerp(py1 + (LED[1] - GY) * z1, VVP[1], m)); ctx.scale(s * z1, s * z1); ctx.translate(-LED[0], -LED[1]);
      vDarkCase(t); liveGPU(t, { glow: 1, lcd: true }); ctx.restore();
    }
    darkClawd(VFG[0], VFG[1] + Math.sin(t * 2.2) * 4, VFG[2], t);
  }

  vshot('C4', (p, lt, d, t) => {
    const i = lineIdx(t);
    if (i === 0) return vWide(t);
    if (i === 1) {
      const w = win(1), split = w.a + .42 * (w.b - w.a);
      return t < split ? vDive(t, w.a, split) : vCrane(t, split, w.b);
    }
    if (i === 2) return vClose(t);
    if (i === 3) return vPace(t);
    if (i === 4) return vJump(t);
    return vDark(t);
  });

  // ---------- the outro: the tunnel was a page of the zine on the intro's table; it's turned over to the back cover ----------
  const VPAGE = [540, 860, 900, 1240];          // c01's VCOVER paper: the A5 page where it lies on the table
  const VPAGE_Z0 = H / VPAGE[3];                // the camera close enough for the page to fill the frame's height
  function vTable() {
    ctx.fillStyle = '#17141F'; ctx.fillRect(0, 0, W, H);
    halftone(rectPts(0, 0, W, H), '#3B2F5C', { cell: 28, dot: .22, op: .9, multiply: false });
    const lamp = ctx.createRadialGradient(VPAGE[0], VPAGE[1], 150, VPAGE[0], VPAGE[1], 1250);
    lamp.addColorStop(0, 'rgb(255 214 150 / .22)'); lamp.addColorStop(1, 'rgb(255 214 150 / 0)');
    ctx.fillStyle = lamp; ctx.fillRect(0, 0, W, H);
    // what the intro left on the table: the fuse burnt to ash along the foot, the spent match by its box
    const ash = [[250, 1825], [420, 1858], [600, 1884], [790, 1900], [930, 1975]];
    marker(ash, '#3A3440', 12, { rough: 1.5 }); marker(ash, '#6A6374', 4, { rough: 2, alpha: .7 });
    ctx.save(); ctx.translate(170, 1660); ctx.rotate(-.12);   // (c01's matchbox, where the vertical intro left it)
    scrap(rectPts(-110, -70, 220, 140), '#7A2B22', { torn: 1.2, seed: 1921, shadow: [8, 10] });
    scrap(rectPts(-100, -60, 200, 104), PAL.yellow, { torn: .8, seed: 1922, shadow: false });
    scrap(rectPts(-110, 48, 220, 22), '#4A3326', { torn: .8, seed: 1923, shadow: false, tone: { color: PAL.ink, cell: 5, dot: .35, op: .8 } });
    txt('ATTENTION', 0, -18, 44, PAL.red, { font: 'anton', maxW: 180 });
    txt('SAFETY MATCHES · EST. 2017', 0, 22, 14, PAL.ink, { font: 'typewriter', maxW: 180 });
    ctx.restore();
    ctx.save(); ctx.translate(330, 1760); ctx.rotate(.5);
    scrap(rectPts(0, -7, 200, 14), '#E9C98F', { torn: .6, seed: 1763, shadow: [3, 4] });
    scrap(rectPts(140, -7, 60, 14), '#2A2220', { torn: .6, seed: 1764, shadow: false });
    scrap(ellPts(206, 0, 17, 13, 14), '#2A2220', { torn: .8, seed: 1765, shadow: false });
    ctx.restore();
  }
  // the back cover, portrait, on the page VPAGE: the title, the credits in a column, Clawd asleep against the GPU at its foot
  function vBackCover(t, t0, sc = 1) {
    const lt = (t - t0) / sc, [PX, PY, PW, PH] = VPAGE, x0 = PX - PW / 2, y0 = PY - PH / 2;
    scrap(rectPts(x0, y0, PW, PH), PAL.paper, { torn: 3, seed: 1700, shadow: [14, 18], shadowCol: 'rgb(0 0 0 / .5)' });
    halftone([[x0 + PW * .25, y0 + PH], [x0 + PW, y0 + PH * .5], [x0 + PW, y0 + PH]], PAL.pink, { cell: 16, dot: .3, op: .45 });
    halftone([[x0, y0], [x0 + PW * .6, y0], [x0, y0 + PH * .3]], PAL.sky, { cell: 16, dot: .3, op: .45, angle: 45 });
    // turned over, the spine and its staples are on the right
    for (const y of [y0 + 230, y0 + PH - 300]) { ctx.fillStyle = '#9A9AA6'; ctx.fillRect(x0 + PW - 34, y, 9, 76); ctx.fillStyle = '#6E6E78'; ctx.fillRect(x0 + PW - 34, y, 3, 76); }
    // the title, in three lines
    const tk = clamp(lt / .8);
    ransom("WE DIDN'T", PX, y0 + 100, 108, { seed: 1710, pop: clamp(tk * 2.2), rot: -.02, fonts: READABLE });
    ransom('START THE', PX, y0 + 228, 108, { seed: 1715, pop: clamp(tk * 2.2 - .5), rot: .015, fonts: READABLE });
    ransom('SCALING', PX, y0 + 392, 168, { seed: 1721, pop: clamp(tk * 2.2 - 1) * 1.3, rot: -.012, fonts: READABLE, maxW: 780 });
    // the credits, typed
    typed('lyrics: Domenic & Claude', PX, y0 + 595, 50, clamp((lt - .85) / .3), PAL.ink);
    typed('music: Lyria 3.5', PX, y0 + 665, 50, clamp((lt - 1.05) / .25), PAL.ink);
    typed('video: Claude Opus 5.5', PX, y0 + 745, 58, clamp((lt - 1.25) / .35), PAL.ink);
    if (lt > 1.6) underline(PX - 330, PX + 330, y0 + 787, PAL.red, 7, clamp((lt - 1.6) / .25));   // (at k = 0 it would leave a red dot)
    // the date ticker, one last time: the day after the last verse
    const sk = clamp((lt - 1.85) / .16);
    if (sk > 0) stamp('SEP 23, 2026', PX + 20, y0 + 863, 48, PAL.red, -.06, { pop: sk });
    // the art: Clawd, logged off, asleep against the GPU that trains on
    const gs = 22, gx = 470, gy = y0 + PH - 70 - 3.3 * gs, floor = y0 + PH - 70;
    ctx.fillStyle = 'rgb(28 26 31 / .12)'; tracePath(ellPts(400, floor + 4, 280, 18, 24)); ctx.fill();
    marker([[130, floor + 4], [640, floor]], PAL.ink, 7, { rough: 1.2 });
    gpu(gx, gy, gs, { label: 'H100', t, rot: -.02 });
    const lx = gx + 4.1 * gs, ly = gy - 2.1 * gs, on = LED_ON(t);
    if (on) glowAt(lx, ly, 50, '#3BE08A', .5);
    ctx.fillStyle = on ? '#3BE08A' : '#1D3A28'; tracePath(ellPts(lx, ly, 9, 9, 12)); ctx.fill();
    // sticky note: the loss curve, still going down
    ctx.save(); ctx.translate(780, floor - 130); ctx.rotate(.07);
    scrap(ctrRect(0, 0, 200, 170), PAL.yellow, { torn: 1.2, seed: 1730 });
    tape(0, -85, 100, -.08, { h: 28, seed: 1734 });
    const pts = []; for (let i = 0; i <= 30; i++) { const x = -78 + i / 30 * 156; pts.push([x, -34 + 92 * (1 - Math.exp(-i / 7)) + (hash(i + 1731) - .5) * 6]); }
    marker(partial(pts, .55 + .45 * frac(t * .3)), PAL.red, 6, { rough: .5 });
    txt('still going ↓', 0, -56, 28, PAL.ink, { font: 'marker' });
    ctx.restore();
    clawd(255, floor, 20, { hat: 'mohawk', eyes: 'closed', mouth: 'smile', aL: -1.1, aR: -.4, rot: .1, sq: .035 * Math.sin(t * 2.4), blush: true });
    for (let i = 0; i < 3; i++) {
      const ph = frac(t * .45 + i / 3);
      txt('z', 200 - ph * 70 + Math.sin(ph * 6) * 12, floor - 210 - ph * 130, 38 + ph * 30, alpha(PAL.ink, Math.sin(ph * Math.PI)), { font: 'marker', rot: -.2 });
    }
    // the barcode, whose bars trace a loss curve
    const bx = 780, by = floor + 30;
    scrap(ctrRect(bx, by - 6, 210, 74), PAL.white, { torn: 1, seed: 1740, shadow: [4, 5] });
    for (let i = 0; i < 30; i++) {
      if (hash(i + 1741) < .28) continue;
      const hgt = 48 * (.3 + .7 * Math.exp(-i / 9)), bw = hash(i + 1742) < .5 ? 3 : 5;
      ctx.fillStyle = PAL.ink; ctx.fillRect(bx - 88 + i * 6, by + 14 - hgt, bw, hgt);
    }
    txt('ISSUE #1 · FREE · COPY ME', bx, by + 24, 13, PAL.ink, { font: 'code' });
  }
  vshot('outro', (p, lt, d, t) => {
    hideCaption(); hideStamp();
    const sc = clamp(d / 4.8, .65, 1), flipA = .7 * sc, flipB = flipA + .55 * sc;   // the zine is turned over
    const k = ease(clamp((lt - .15 * sc) / (.5 * sc))), zoom = lerp(VPAGE_Z0, 1, k);
    // once it's turned over, the camera creeps in on the back cover till the end
    const creep = 1 + .04 * ease(clamp((lt - flipB) / Math.max(.1, d - flipB)));
    ctx.save(); ctx.translate(VPAGE[0], VPAGE[1]); ctx.scale(creep, creep); ctx.translate(-VPAGE[0], -VPAGE[1]);
    vTable();
    const [PX, PY, PW, PH] = VPAGE, f = clamp((lt - flipA) / (flipB - flipA)), ang = ease(f) * Math.PI, sx = Math.cos(ang);
    // the camera pulls back off the page to where it lies; (the page's centre sits at the frame's middle at first)
    ctx.save(); ctx.translate(PX, lerp(H / 2, PY, k)); ctx.scale(zoom * Math.max(.002, Math.abs(sx)), zoom * (1 + .05 * Math.sin(ang))); ctx.translate(-PX, -PY);
    if (sx > 0) {
      const edge = roughen(ctrRect(PX, PY, PW, PH), 3, 16, 1750, false);
      ctx.save(); ctx.translate(14, 18); tracePath(edge); ctx.fillStyle = 'rgb(0 0 0 / .5)'; ctx.fill(); ctx.restore();
      ctx.save(); tracePath(edge); ctx.clip();
      ctx.fillStyle = '#0D0B12'; ctx.fillRect(PX - PW, PY - PH, PW * 2, PH * 2);
      // the tunnel was drawn on the full frame: the page, at the camera's first zoom, is that frame
      ctx.translate(PX, PY); ctx.scale(1 / VPAGE_Z0, 1 / VPAGE_Z0); ctx.translate(-W / 2, -H / 2);
      vCorridor(t, win(5));
      ctx.restore();
    } else vBackCover(t, span('outro').start + flipB, sc);
    ctx.restore();
    ctx.restore();
  });
})();
