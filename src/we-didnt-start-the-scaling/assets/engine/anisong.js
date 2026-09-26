// ---- src/core.js ----
// core.js: canvas, time, randomness, easing, camera, shot registry, frame compositor.
// Everything a shot draws must be a pure function of song time `t` (frames render out of order, in parallel).

const W = 1920, H = 1080, TAU = Math.PI * 2;
// In a page the canvas is #out; in a Web Worker the host sets self.OUT_CANVAS (an OffscreenCanvas) before loading the engine.
const HAS_DOM = typeof document !== 'undefined';
const canvas = HAS_DOM ? document.getElementById('out') : self.OUT_CANVAS;
let ctx = canvas.getContext('2d');
// Scratch canvases for caches: DOM canvases in pages, OffscreenCanvas in workers.
function makeCanvas(w, h) {
  if (!HAS_DOM) return new OffscreenCanvas(w, h);
  const c = document.createElement('canvas'); c.width = w; c.height = h; return c;
}
// Render scale: the scene is always authored in 1920×1080 logical units; the canvas holds W·RS × H·RS pixels.
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

// ---------- per-frame state ----------
let T = 0;           // current song time
const OVERLAYS = []; // functions run after the shot (caption, stamp, grain…), registered by timeline.js

function renderFrame(t) {
  T = t; _boil = boilFrame(t); _jitN = 0; _camDepth = 0;
  ctx.setTransform(RS, 0, 0, RS, 0, 0);
  ctx.globalAlpha = 1; ctx.globalCompositeOperation = 'source-over';
  ctx.fillStyle = PAL.paper; ctx.fillRect(0, 0, W, H);
  const s = segAt(t);
  const fn = s && SHOTS[s.key];
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

// ---------- overlay switches (a shot may call these each frame) ----------
let _noCaption = false, _noStamp = false, _captionStyle = null;
const hideCaption = () => { _noCaption = true; };
const hideStamp = () => { _noStamp = true; };
const captionStyle = s => { _captionStyle = s; };  // {color, y}

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
  const gw = Math.round(960 * clamp(RS, .5, 2)), gh = Math.round(540 * clamp(RS, .5, 2));
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
    const vg = g.createRadialGradient(gw / 2, gh / 2, gw * .26, gw / 2, gh / 2, gw * .65);
    vg.addColorStop(0, 'rgb(255 255 255 / 0)'); vg.addColorStop(1, 'rgb(150 140 130 / .55)');
    g.fillStyle = vg; g.fillRect(0, 0, gw, gh);
    _grain.push(c);
  }
}

OVERLAYS.push((t, s) => {
  // caption
  const ln = lineAt(t);
  if (ln && !_noCaption) {
    const st = _captionStyle || {};
    const age = t - ln.start, k = easeOut(clamp(age / .12));
    const size = ln.text.length > 34 ? 30 : 36;
    ctx.globalAlpha = k;
    dymo(ln.text.replace(/\s*—\s*$/, '').replace(/\s+—\s+/g, ' — '), W / 2, (st.y ?? 1022) + (1 - k) * 20, size, st.color ?? (ln.sec[0] === 'C' ? PAL.red : PAL.ink), { rot: (hash(ln.start * 100) - .5) * .03 });
    ctx.globalAlpha = 1;
  }
  // date stamp
  const d = dateAt(t);
  if (d && !_noStamp) {
    const k = clamp(d.age / .18), rot = -.08 + (hstr(d.text) - .5) * .06;
    // a torn paper tag behind the stamp keeps it legible on dark scenes
    ctx.save(); ctx.globalAlpha = .9 * clamp(k * 3);
    card(1690, 92, textW(d.text, 46, 'mono', 2.8) + 70, 96, PAL.paper, rot, { torn: 2.5, seed: 1301, shadow: [5, 6] });
    ctx.restore();
    stamp(d.text, 1690, 92, 46, PAL.red, rot, { pop: k, font: 'mono' });
  }
  // grain
  if (!_grain || _grain.rs !== RS) buildGrain();
  ctx.globalCompositeOperation = 'multiply'; ctx.globalAlpha = .85;
  const g = _grain[_boil % 3], ox = (hash(_boil) - .5) * 40, oy = (hash(_boil + 5) - .5) * 30;
  ctx.drawImage(g, -30 + ox, -20 + oy, W + 60, H + 40);
  ctx.globalAlpha = 1; ctx.globalCompositeOperation = 'source-over';
  _noCaption = false; _noStamp = false; _captionStyle = null;
});

;
// ---- styles/anime/kit.js ----
// kit.js: the anime style's shared look. The pictures are AI-generated stills (Anima, see shots.json and STYLE.md) brought to life
// the way real anime openings animate keyframes: camera moves over the still, parallax between a background plate and character
// cut-outs, swapped patches (blinks), beat-synced cuts and flashes, shakes, speed lines, light leaks, flares and petals.
// Everything here is a pure function of song time. The zine's caption, date stamp and grain overlays are replaced by this style's.
OVERLAYS.length = 0;

// =====================================================================================================
// PALETTE (for the drawn effects and text; the pictures bring their own colours)
// =====================================================================================================
const AP = {
  sky: '#BFE3FA', cream: '#FFF9EE', sakura: '#FFC3D3', sakuraDk: '#F592AE', ink: '#2A2440', navy: '#27305A', white: '#FFFFFF',
  gold: '#FFC94A', orange: '#FF9A4A', pink: '#FF6FA0', hot: '#FF3D7F', blue: '#3D7BE0', teal: '#2BB5A8', red: '#F04E4E',
  violet: '#8A6BD8', clawd: '#D97757',
};

// =====================================================================================================
// THE STILLS: the manifest (written by `tools/stills.py build`), loading, and drawing
// =====================================================================================================
// Each entry: layer 'full' (a whole frame), 'plate' (a background to composite over), 'cutout' (a character with alpha) or 'patch'
// (a small repainted piece of another still, e.g. closed eyes, placed at x, y in that still's pixels); w and h in pixels; lo, the rect
// [x, y, w, h] of its 1/16-size stand-in in img/lowres.webp.
// <stills: generated by tools/stills.py build>
const STILLS = {
  "intro_sky": {"layer": "plate", "w": 1280, "h": 1280, "lo": [0, 0, 80, 80]},
  "intro_eyes": {"layer": "full", "w": 1536, "h": 864, "lo": [928, 0, 96, 54]},
  "intro_eyes.closed": {"layer": "patch", "of": "intro_eyes", "x": 310, "y": 310, "w": 935, "h": 375, "lo": [661, 698, 58, 23]},
  "intro_eyes.half": {"layer": "patch", "of": "intro_eyes", "x": 310, "y": 310, "w": 935, "h": 375, "lo": [721, 698, 58, 23]},
  "intro_wind": {"layer": "full", "w": 1536, "h": 864, "lo": [0, 82, 96, 54]},
  "intro_wind.laugh": {"layer": "patch", "of": "intro_wind", "x": 965, "y": 202, "w": 275, "h": 140, "lo": [959, 698, 17, 9]},
  "card_akari": {"layer": "cutout", "w": 785, "h": 900, "lo": [343, 0, 49, 56]},
  "card_ren": {"layer": "cutout", "w": 579, "h": 900, "lo": [394, 0, 36, 56]},
  "card_kiri": {"layer": "cutout", "w": 632, "h": 900, "lo": [432, 0, 40, 56]},
  "clawd_jump": {"layer": "cutout", "w": 740, "h": 501, "lo": [432, 698, 46, 31]},
  "clawd_stand": {"layer": "cutout", "w": 733, "h": 513, "lo": [337, 698, 46, 32]},
  "keyvisual": {"layer": "full", "w": 1536, "h": 864, "lo": [98, 82, 96, 54]},
  "club_room": {"layer": "plate", "w": 1536, "h": 864, "lo": [196, 82, 96, 54]},
  "v1_1_paper": {"layer": "full", "w": 1536, "h": 864, "lo": [294, 82, 96, 54]},
  "v1_1_akari": {"layer": "full", "w": 1536, "h": 864, "lo": [392, 82, 96, 54]},
  "v1_2_kiri": {"layer": "full", "w": 1536, "h": 864, "lo": [490, 82, 96, 54]},
  "v1_3_gwern": {"layer": "full", "w": 1536, "h": 864, "lo": [588, 82, 96, 54]},
  "v1_3_tower": {"layer": "full", "w": 1536, "h": 864, "lo": [686, 82, 96, 54]},
  "v1_4_clawd": {"layer": "full", "w": 1536, "h": 864, "lo": [784, 82, 96, 54]},
  "v1_5_asleep": {"layer": "full", "w": 1536, "h": 864, "lo": [882, 82, 96, 54]},
  "v1_5_ren": {"layer": "full", "w": 1536, "h": 864, "lo": [0, 138, 96, 54]},
  "v1_6_sydney": {"layer": "full", "w": 1536, "h": 864, "lo": [98, 138, 96, 54]},
  "v1_7_kiri": {"layer": "full", "w": 1536, "h": 864, "lo": [196, 138, 96, 54]},
  "v1_7_city": {"layer": "plate", "w": 1536, "h": 864, "lo": [294, 138, 96, 54]},
  "v1_8_eliezer": {"layer": "full", "w": 1536, "h": 864, "lo": [392, 138, 96, 54]},
  "v1_8_blown": {"layer": "full", "w": 1536, "h": 864, "lo": [490, 138, 96, 54]},
  "v1_9_sam": {"layer": "full", "w": 1536, "h": 864, "lo": [588, 138, 96, 54]},
  "v1_9_bench": {"layer": "full", "w": 1536, "h": 864, "lo": [686, 138, 96, 54]},
  "v1_10_chaos": {"layer": "full", "w": 1536, "h": 864, "lo": [784, 138, 96, 54]},
  "v1_10_board": {"layer": "full", "w": 1536, "h": 864, "lo": [882, 138, 96, 54]},
  "v1_11_ilya": {"layer": "full", "w": 1536, "h": 864, "lo": [0, 194, 96, 54]},
  "v1_11_peek": {"layer": "full", "w": 1536, "h": 864, "lo": [98, 194, 96, 54]},
  "v1_12_book": {"layer": "full", "w": 1536, "h": 864, "lo": [196, 194, 96, 54]},
  "v1_13_strawberry": {"layer": "full", "w": 1536, "h": 864, "lo": [294, 194, 96, 54]},
  "v1_14_gavin": {"layer": "full", "w": 1536, "h": 864, "lo": [392, 194, 96, 54]},
  "v1_15_geoff": {"layer": "full", "w": 1536, "h": 864, "lo": [490, 194, 96, 54]},
  "v1_15_salute": {"layer": "full", "w": 1536, "h": 864, "lo": [588, 194, 96, 54]},
  "v1_16_demis": {"layer": "full", "w": 1536, "h": 864, "lo": [686, 194, 96, 54]},
  "v1_16_cheer": {"layer": "full", "w": 1536, "h": 864, "lo": [784, 194, 96, 54]},
  "c1_door": {"layer": "full", "w": 1536, "h": 864, "lo": [882, 194, 96, 54]},
  "run_akari": {"layer": "cutout", "w": 713, "h": 900, "lo": [474, 0, 45, 56]},
  "run_ren": {"layer": "cutout", "w": 642, "h": 900, "lo": [521, 0, 40, 56]},
  "run_kiri": {"layer": "cutout", "w": 765, "h": 900, "lo": [563, 0, 48, 56]},
  "c1_lookup": {"layer": "full", "w": 1536, "h": 864, "lo": [0, 250, 96, 54]},
  "v2_1_whale": {"layer": "full", "w": 1536, "h": 864, "lo": [98, 250, 96, 54]},
  "v2_1_ren": {"layer": "full", "w": 1536, "h": 864, "lo": [196, 250, 96, 54]},
  "v2_2_gate": {"layer": "full", "w": 1536, "h": 864, "lo": [294, 250, 96, 54]},
  "v2_2_props": {"layer": "full", "w": 1536, "h": 864, "lo": [392, 250, 96, 54]},
  "v2_3_accept": {"layer": "full", "w": 1536, "h": 864, "lo": [490, 250, 96, 54]},
  "v2_3_wait": {"layer": "full", "w": 1536, "h": 864, "lo": [588, 250, 96, 54]},
  "v2_4_kiri": {"layer": "full", "w": 1536, "h": 864, "lo": [686, 250, 96, 54]},
  "v2_4_hub": {"layer": "full", "w": 1536, "h": 864, "lo": [784, 250, 96, 54]},
  "v2_5_zuck": {"layer": "full", "w": 1536, "h": 864, "lo": [882, 250, 96, 54]},
  "v2_5_ren": {"layer": "full", "w": 1536, "h": 864, "lo": [0, 306, 96, 54]},
  "v2_6_shop": {"layer": "full", "w": 1536, "h": 864, "lo": [98, 306, 96, 54]},
  "v2_7_robot": {"layer": "full", "w": 1536, "h": 864, "lo": [196, 306, 96, 54]},
  "v2_7_akari": {"layer": "full", "w": 1536, "h": 864, "lo": [294, 306, 96, 54]},
  "v2_8_podium": {"layer": "full", "w": 1536, "h": 864, "lo": [392, 306, 96, 54]},
  "v2_9_train": {"layer": "full", "w": 1536, "h": 864, "lo": [490, 306, 96, 54]},
  "v2_9_akari": {"layer": "full", "w": 1536, "h": 864, "lo": [588, 306, 96, 54]},
  "v2_10_banana": {"layer": "cutout", "w": 464, "h": 802, "lo": [98, 698, 29, 50]},
  "v2_11_clawd": {"layer": "full", "w": 1536, "h": 864, "lo": [686, 306, 96, 54]},
  "v2_11_line": {"layer": "full", "w": 1536, "h": 864, "lo": [784, 306, 96, 54]},
  "v2_12_eliezer": {"layer": "full", "w": 1536, "h": 864, "lo": [882, 306, 96, 54]},
  "v2_12_gasp": {"layer": "full", "w": 1536, "h": 864, "lo": [0, 362, 96, 54]},
  "v2_13_robot": {"layer": "full", "w": 1536, "h": 864, "lo": [98, 362, 96, 54]},
  "v2_14_kiri": {"layer": "full", "w": 1536, "h": 864, "lo": [196, 362, 96, 54]},
  "v2_15_yann": {"layer": "full", "w": 1536, "h": 864, "lo": [294, 362, 96, 54]},
  "v2_15_cube": {"layer": "full", "w": 1536, "h": 864, "lo": [392, 362, 96, 54]},
  "v2_16_page": {"layer": "full", "w": 1280, "h": 720, "lo": [129, 698, 80, 45]},
  "v2_16_bubble": {"layer": "full", "w": 1536, "h": 864, "lo": [490, 362, 96, 54]},
  "c2_walk": {"layer": "full", "w": 1536, "h": 864, "lo": [588, 362, 96, 54]},
  "c2_goldfish": {"layer": "full", "w": 1536, "h": 864, "lo": [686, 362, 96, 54]},
  "c2_fish": {"layer": "cutout", "w": 447, "h": 360, "lo": [781, 698, 28, 22]},
  "c2_watch": {"layer": "full", "w": 1536, "h": 864, "lo": [784, 362, 96, 54]},
  "c2_jar": {"layer": "full", "w": 1536, "h": 864, "lo": [882, 362, 96, 54]},
  "v3_1_window": {"layer": "full", "w": 1536, "h": 864, "lo": [0, 418, 96, 54]},
  "v3_agent": {"layer": "cutout", "w": 457, "h": 386, "lo": [630, 698, 29, 24]},
  "v3_2_lobster": {"layer": "full", "w": 1536, "h": 864, "lo": [98, 418, 96, 54]},
  "v3_3_sandbox": {"layer": "full", "w": 1536, "h": 864, "lo": [196, 418, 96, 54]},
  "v3_3_kiri": {"layer": "full", "w": 1536, "h": 864, "lo": [294, 418, 96, 54]},
  "v3_4_bench": {"layer": "full", "w": 1536, "h": 864, "lo": [392, 418, 96, 54]},
  "v3_5_stage": {"layer": "full", "w": 1536, "h": 864, "lo": [490, 418, 96, 54]},
  "v3_5_clawd": {"layer": "cutout", "w": 659, "h": 481, "lo": [480, 698, 41, 30]},
  "v3_5_akari": {"layer": "full", "w": 1536, "h": 864, "lo": [588, 418, 96, 54]},
  "v3_club_autumn": {"layer": "plate", "w": 1536, "h": 864, "lo": [686, 418, 96, 54]},
  "v3_7_clawd": {"layer": "cutout", "w": 938, "h": 459, "lo": [569, 698, 59, 29]},
  "v3_8_cheer": {"layer": "full", "w": 1536, "h": 864, "lo": [784, 418, 96, 54]},
  "v3_9_huggy": {"layer": "full", "w": 1536, "h": 864, "lo": [882, 418, 96, 54]},
  "v3_9_kiri": {"layer": "full", "w": 1536, "h": 864, "lo": [0, 474, 96, 54]},
  "v3_9_lineup": {"layer": "full", "w": 1536, "h": 864, "lo": [98, 474, 96, 54]},
  "v3_agent_sweater": {"layer": "cutout", "w": 487, "h": 526, "lo": [257, 698, 30, 33]},
  "v3_12_trophies": {"layer": "full", "w": 1536, "h": 864, "lo": [196, 474, 96, 54]},
  "v3_13_bag": {"layer": "full", "w": 1536, "h": 864, "lo": [294, 474, 96, 54]},
  "v3_15_clawd": {"layer": "cutout", "w": 736, "h": 522, "lo": [289, 698, 46, 33]},
  "v3_15_kiri": {"layer": "full", "w": 1536, "h": 864, "lo": [392, 474, 96, 54]},
  "v3_16_hood": {"layer": "full", "w": 1536, "h": 864, "lo": [490, 474, 96, 54]},
  "v3_16_reveal": {"layer": "full", "w": 1536, "h": 864, "lo": [588, 474, 96, 54]},
  "v3_10_sam": {"layer": "full", "w": 1536, "h": 864, "lo": [686, 474, 96, 54]},
  "v3_11_noam": {"layer": "full", "w": 1536, "h": 864, "lo": [784, 474, 96, 54]},
  "v3_11_ren": {"layer": "full", "w": 1536, "h": 864, "lo": [882, 474, 96, 54]},
  "v3_14_jeff": {"layer": "full", "w": 1536, "h": 864, "lo": [0, 530, 96, 54]},
  "c3_sunset": {"layer": "plate", "w": 1280, "h": 1280, "lo": [82, 0, 80, 80]},
  "c3_hands": {"layer": "full", "w": 1536, "h": 864, "lo": [98, 530, 96, 54]},
  "v4_3_jensen": {"layer": "full", "w": 1536, "h": 864, "lo": [196, 530, 96, 54]},
  "v4_4_greg": {"layer": "full", "w": 1536, "h": 864, "lo": [294, 530, 96, 54]},
  "v4_5_kiri": {"layer": "full", "w": 1536, "h": 864, "lo": [392, 530, 96, 54]},
  "v4_5_boom": {"layer": "full", "w": 1536, "h": 864, "lo": [490, 530, 96, 54]},
  "v4_7_dario": {"layer": "full", "w": 1536, "h": 864, "lo": [588, 530, 96, 54]},
  "v4_10_pew": {"layer": "plate", "w": 1536, "h": 864, "lo": [686, 530, 96, 54]},
  "v4_10_bernie": {"layer": "cutout", "w": 643, "h": 900, "lo": [613, 0, 40, 56]},
  "v4_10_bannon": {"layer": "cutout", "w": 461, "h": 900, "lo": [655, 0, 29, 56]},
  "v4_16_door": {"layer": "full", "w": 1536, "h": 864, "lo": [784, 530, 96, 54]},
  "v4_16_turn": {"layer": "full", "w": 1536, "h": 864, "lo": [882, 530, 96, 54]},
  "v4_1_board": {"layer": "full", "w": 1536, "h": 864, "lo": [0, 586, 96, 54]},
  "v4_2_slot": {"layer": "full", "w": 1536, "h": 864, "lo": [98, 586, 96, 54]},
  "v4_2_ren": {"layer": "full", "w": 1536, "h": 864, "lo": [196, 586, 96, 54]},
  "v4_8_sam": {"layer": "full", "w": 1536, "h": 864, "lo": [294, 586, 96, 54]},
  "v4_8_elon": {"layer": "full", "w": 1536, "h": 864, "lo": [392, 586, 96, 54]},
  "v4_9_akari": {"layer": "full", "w": 1536, "h": 864, "lo": [490, 586, 96, 54]},
  "v4_9_road": {"layer": "full", "w": 1536, "h": 864, "lo": [588, 586, 96, 54]},
  "v4_9_tcut": {"layer": "cutout", "w": 904, "h": 900, "lo": [686, 0, 56, 56]},
  "v4_9_car": {"layer": "cutout", "w": 466, "h": 283, "lo": [909, 698, 29, 18]},
  "v4_6_finish": {"layer": "full", "w": 1536, "h": 864, "lo": [686, 586, 96, 54]},
  "v4_11_bench": {"layer": "plate", "w": 1536, "h": 864, "lo": [784, 586, 96, 54]},
  "v4_11_clawd": {"layer": "cutout", "w": 696, "h": 483, "lo": [523, 698, 44, 30]},
  "v4_12_map": {"layer": "full", "w": 1536, "h": 864, "lo": [882, 586, 96, 54]},
  "v4_12_phew": {"layer": "full", "w": 1536, "h": 864, "lo": [0, 642, 96, 54]},
  "v4_13_trump": {"layer": "full", "w": 1536, "h": 864, "lo": [98, 642, 96, 54]},
  "v4_14_clawd": {"layer": "cutout", "w": 715, "h": 513, "lo": [385, 698, 45, 32]},
  "v4_3_huggy": {"layer": "cutout", "w": 696, "h": 583, "lo": [211, 698, 44, 36]},
  "v4_15_gifts": {"layer": "full", "w": 1536, "h": 864, "lo": [196, 642, 96, 54]},
  "v4_15_kiri": {"layer": "full", "w": 1536, "h": 864, "lo": [294, 642, 96, 54]},
  "c4_door": {"layer": "full", "w": 1536, "h": 864, "lo": [392, 642, 96, 54]},
  "c4_sky": {"layer": "plate", "w": 1280, "h": 1280, "lo": [164, 0, 80, 80]},
  "c4_run_akari.pass2": {"layer": "cutout", "of": "run_akari", "w": 713, "h": 926, "ox": 0, "oy": 0, "lo": [296, 0, 45, 58]},
  "c4_run_akari.air2": {"layer": "cutout", "of": "run_akari", "w": 713, "h": 900, "ox": 0, "oy": 0, "lo": [744, 0, 45, 56]},
  "c4_run_ren.pass2": {"layer": "cutout", "of": "run_ren", "w": 642, "h": 900, "ox": 0, "oy": 0, "lo": [791, 0, 40, 56]},
  "c4_run_ren.air2": {"layer": "cutout", "of": "run_ren", "w": 690, "h": 900, "ox": 0, "oy": 0, "lo": [833, 0, 43, 56]},
  "c4_run_kiri.pass": {"layer": "cutout", "of": "run_kiri", "w": 769, "h": 939, "ox": -4, "oy": 0, "lo": [246, 0, 48, 59]},
  "c4_run_kiri.air": {"layer": "cutout", "of": "run_kiri", "w": 765, "h": 900, "ox": 0, "oy": 0, "lo": [878, 0, 48, 56]},
  "c4_crouch": {"layer": "full", "w": 1536, "h": 864, "lo": [490, 642, 96, 54]},
  "c4_crouch.calm3": {"layer": "patch", "of": "c4_crouch", "x": 571, "y": 231, "w": 278, "h": 239, "lo": [940, 698, 17, 15]},
  "c4_racecu": {"layer": "full", "w": 1536, "h": 864, "lo": [588, 642, 96, 54]},
  "c4_race": {"layer": "full", "w": 1536, "h": 864, "lo": [686, 642, 96, 54]},
  "c4_race.legs2": {"layer": "patch", "of": "c4_race", "x": 0, "y": 450, "w": 1536, "h": 360, "lo": [811, 698, 96, 22]},
  "c4_group": {"layer": "full", "w": 1536, "h": 864, "lo": [784, 642, 96, 54]},
  "c4_bye": {"layer": "full", "w": 1536, "h": 864, "lo": [882, 642, 96, 54]},
  "c4_night": {"layer": "full", "w": 1536, "h": 864, "lo": [0, 698, 96, 54]},
};
// </stills>
// When the song shows each still, window by window: [name, from, to] in seconds from the window's start (from a pass over every frame).
// <still-use: generated by tools/still_use.mjs>
const STILL_USE = {
  "intro": [["intro_sky",0,3.1],["clawd_jump",1.8,3.1],["intro_eyes",3,4.6],["intro_eyes.closed",3,3.5],["intro_eyes.half",3.4,3.6],["intro_wind",4.5,6],["intro_wind.laugh",4.5,5.1],["card_akari",6,7.5],["card_ren",7.4,9],["card_kiri",8.9,10.4],["clawd_jump",10.3,11.8],["keyvisual",11.7,14.6]],
  "V1.1": [["v1_1_paper",0,1.5],["v1_1_akari",1.4,3.2]],
  "V1.2": [["v1_2_kiri",0,1.5],["card_akari",1.4,3.4],["clawd_jump",1.4,3.4]],
  "V1.3": [["v1_3_gwern",0,1.5],["v1_3_tower",1.4,2.4]],
  "V1.4": [["v1_4_clawd",0,3.3]],
  "V1.5": [["v1_5_asleep",0,1.2],["v1_5_ren",1.1,3]],
  "V1.6": [["v1_6_sydney",0,3]],
  "V1.7": [["v1_7_kiri",0,1.2],["v1_7_city",1.1,3.2]],
  "V1.8": [["v1_8_eliezer",0,1.3],["v1_8_blown",1.2,2.4]],
  "V1.9": [["v1_9_sam",0,1.3],["v1_9_bench",1.2,2.8]],
  "V1.10": [["v1_10_chaos",0,1.5],["v1_10_board",1.4,3.2]],
  "V1.11": [["v1_11_ilya",0,1.7],["v1_11_peek",1.6,3.4]],
  "V1.12": [["v1_12_book",0,2.4]],
  "V1.13": [["v1_13_strawberry",0,2.8]],
  "V1.14": [["intro_eyes",0,2.6],["v1_14_gavin",0,2.6],["intro_eyes.closed",1.6,1.8],["intro_eyes.half",1.7,2.6]],
  "V1.15": [["v1_15_geoff",0,1.7],["v1_15_salute",1.6,3.5]],
  "V1.16": [["v1_16_demis",0,2.2],["v1_16_cheer",2.1,3.7]],
  "C1": [["c1_door",0,2.1],["c4_run_akari.pass2",2,5],["c4_run_kiri.pass",2,4.9],["c4_run_ren.air2",2,5],["clawd_jump",2,5],["intro_sky",2,5],["run_kiri",2,5],["c4_run_akari.air2",2.1,4.9],["c4_run_kiri.air",2.1,5],["c4_run_ren.pass2",2.1,5],["run_akari",2.1,5],["run_ren",2.1,4.9],["card_akari",4.9,7.9],["card_ren",5.6,7.9],["card_kiri",6.3,7.9],["clawd_jump",7.1,10.1],["intro_sky",7.8,10.1],["c1_lookup",10,12.6]],
  "V2.1": [["v2_1_whale",0,1.5],["v2_1_ren",1.4,3]],
  "V2.2": [["v2_2_gate",0,1.5],["v2_2_props",1.4,3]],
  "V2.3": [["v2_3_accept",0,1.5],["v2_3_wait",1.4,3.2]],
  "V2.4": [["v2_4_kiri",0,1.2],["v2_4_hub",1.1,3],["clawd_jump",2.3,3]],
  "V2.5": [["v2_5_zuck",0,1.5],["v2_5_ren",1.4,3]],
  "V2.6": [["v2_6_shop",0,3]],
  "V2.7": [["v2_7_robot",0,2.8],["v2_7_akari",1.1,1.9]],
  "V2.8": [["v2_8_podium",0,2.6]],
  "V2.9": [["v2_9_train",0,1.9],["v2_9_akari",1.8,2.8]],
  "V2.10": [["clawd_jump",0,3.2],["v2_10_banana",0,3.2]],
  "V2.11": [["v2_11_clawd",0,1.5],["v2_11_line",1.4,3.3]],
  "V2.12": [["v2_12_eliezer",0,1.4],["v2_12_gasp",1.3,2.6]],
  "V2.13": [["v2_13_robot",0,2.6]],
  "V2.14": [["v2_13_robot",0,3.2],["v2_14_kiri",1.2,3.2]],
  "V2.15": [["v2_15_yann",0,1.5],["v2_15_cube",1.4,3]],
  "V2.16": [["v2_16_bubble",0,4.1],["v2_16_page",0,1.2],["clawd_jump",1.8,3.7]],
  "C2": [["c2_walk",0,2.3],["clawd_jump",0,2.3],["c2_fish",2.2,5.2],["c2_goldfish",2.2,5.2],["c2_watch",5.1,8.1],["c2_jar",8,11.7],["c2_watch",11.6,13],["clawd_jump",11.6,13]],
  "V3.1": [["v3_1_window",0,2.6],["v3_agent",0,2.6]],
  "V3.2": [["v3_2_lobster",0,3.1],["clawd_jump",1.7,3.1]],
  "V3.3": [["v3_3_sandbox",0,1.5],["v3_3_kiri",1.4,3]],
  "V3.4": [["v3_4_bench",0,3]],
  "V3.5": [["v3_5_clawd",0,1.5],["v3_5_stage",0,1.5],["v3_5_akari",1.4,3.4]],
  "V3.6": [["v3_5_clawd",0,1.9],["v3_5_stage",0,1.9]],
  "V3.7": [["v3_7_clawd",0,3],["v3_club_autumn",0,3]],
  "V3.8": [["v3_7_clawd",0,0.2],["v3_club_autumn",0,1.5],["clawd_jump",0.1,1.5],["v3_8_cheer",1.4,3.2]],
  "V3.9": [["v3_9_huggy",0,1],["v3_9_kiri",0.9,1.7],["v3_9_lineup",1.6,3.1],["v3_agent_sweater",1.6,3.1]],
  "V3.10": [["v3_9_lineup",0,1.5],["v3_agent_sweater",0,2.6],["v3_10_sam",1.4,2.6]],
  "V3.11": [["v3_11_noam",0,1.5],["v3_11_ren",1.4,2.8]],
  "V3.12": [["v3_12_trophies",0,3.2]],
  "V3.13": [["v3_13_bag",0,3]],
  "V3.14": [["v3_14_jeff",0,3]],
  "V3.15": [["v3_15_clawd",0,1.5],["v3_club_autumn",0,1.5],["v3_15_kiri",1.4,2.8]],
  "V3.16": [["v3_16_hood",0,1.4],["v3_16_reveal",1.3,4.3]],
  "C3": [["c3_sunset",0,6.6],["card_akari",0,2.3],["card_kiri",0,2.3],["card_ren",0,2.3],["clawd_stand",0,2.3],["c4_run_kiri.air",2.2,4.9],["c4_run_ren.pass2",2.2,4.9],["clawd_jump",2.2,5.2],["run_akari",2.2,4.9],["c4_run_akari.pass2",2.3,5],["c4_run_ren.air2",2.3,5],["run_kiri",2.3,5],["c4_run_akari.air2",2.4,5.2],["c4_run_kiri.pass",2.4,5.2],["run_ren",2.4,5.2],["card_akari",5.1,6.6],["card_ren",5.4,6.6],["card_kiri",5.8,6.6],["clawd_jump",6.2,6.6],["c3_hands",6.5,8.1],["c3_sunset",8,12.6],["card_akari",8,12.6],["card_kiri",8,12.6],["card_ren",8,12.6],["clawd_jump",8,12.6]],
  "V4.1": [["v4_1_board",0,2.4],["v3_agent",0.7,2.4]],
  "V4.2": [["v4_2_slot",0,2.1],["v4_2_ren",2,3.5]],
  "V4.3": [["v4_3_jensen",0,2.6],["v4_3_huggy",1.1,2.6]],
  "V4.4": [["v4_4_greg",0,3],["card_akari",1.1,3],["card_ren",1.1,3],["card_kiri",1.2,3]],
  "V4.5": [["v4_5_kiri",0,1.2],["v4_5_boom",1.1,2.4]],
  "V4.6": [["v4_6_finish",0,2.8]],
  "V4.7": [["clawd_stand",0,3],["v4_7_dario",0,3]],
  "V4.8": [["v4_8_sam",0,3.3],["v4_8_elon",0.1,3.3],["v4_14_clawd",2.3,3.3]],
  "V4.9": [["v4_9_akari",0,1.3],["v4_9_car",1.2,3.2],["v4_9_road",1.2,3.2],["v4_9_tcut",1.2,3.2]],
  "V4.10": [["v4_10_bannon",0,2.4],["v4_10_bernie",0,2.4],["v4_10_pew",0,2.4],["card_akari",1.3,2.4],["card_ren",1.3,2.4]],
  "V4.11": [["v4_11_bench",0,3.2],["v4_11_clawd",0,3.2],["card_kiri",1.7,3.2]],
  "V4.12": [["v4_12_map",0,1.9],["v4_12_phew",1.8,3.2]],
  "V4.13": [["v4_13_trump",0,1.7],["v1_15_salute",1.6,3.5]],
  "V4.14": [["clawd_stand",0,0.4],["v4_14_clawd",0.3,1.2],["clawd_jump",1.1,2.1]],
  "V4.15": [["v4_15_gifts",0,1.7],["v4_15_kiri",1.6,3]],
  "V4.16": [["v4_16_door",0,1.7],["v4_16_turn",1.6,3.7]],
  "C4": [["c4_door",0,1.5],["clawd_jump",0,5],["c4_run_akari.pass2",1.4,4.9],["c4_run_ren.air2",1.4,4.9],["c4_sky",1.4,5],["run_kiri",1.4,4.9],["c4_run_akari.air2",1.5,5],["c4_run_kiri.pass",1.5,5],["run_ren",1.5,5],["c4_run_kiri.air",1.6,4.8],["c4_run_ren.pass2",1.6,4.8],["run_akari",1.6,4.8],["card_akari",4.9,5.3],["card_ren",5.2,7.2],["card_kiri",5.6,7.2],["clawd_jump",6,7.2],["card_akari",6.3,7.2],["c4_crouch",7.1,9.2],["c4_crouch.calm3",7.1,9.2],["c4_racecu",9.1,10.1],["c4_race",10,11.3],["clawd_jump",10,17.2],["c4_race.legs2",10.1,11.3],["c4_group",11.2,17.2],["c4_bye",17.1,19.7],["c4_night",19.6,22.1],["clawd_stand",19.6,22.1],["c4_night",25.6,30.2],["clawd_stand",25.6,30.2]],
  "outro": [["keyvisual",0,7.7]],
};
// </still-use>

// IMGS[name] is what a still draws with: its full picture, decoded, or else its low-res stand-in (LO[name], cut from img/lowres.webp,
// drawn scaled up). The full pictures load in the background a few at a time, soonest needed first: from the playhead on, in the order
// the song shows them (STILL_USE), then the ones it has already shown. A frame far from the last one (a seek, or this video starting
// mid-song) reorders the queue, and a still that a frame drew low-res goes to the front. STYLE_READY, which the studio and the site's
// worker wait for before the first frame, settles once the stand-ins and the pictures for the first few seconds from STYLE_START (the
// host's playhead, default 0) are in; STYLE_ALL once every picture is (offline renders wait for that, so they never draw a stand-in).
// When a picture the last frame drew low-res arrives, the kit calls the host's STYLE_STALE(), so that a paused player can redraw.
// Decoded, all the pictures would take 680 MB (5.3 MB for a 1536 × 864 frame), enough to get a phone's tab killed. So only the ones on
// screen from KEEP_BEHIND s before the playhead to KEEP_AHEAD s after it, and any drawn in the last KEEP_DRAWN s, stay decoded, up to
// KEEP_BYTES (soonest needed first); the others go back to their stand-ins. Their files stay (FILES, 10 MB in all), so a picture needed
// again decodes without another download. Offline renders (studio.html?render) keep every picture decoded.
const IMGS = {}, LO = {}, FULL = new Set(), FILES = {};
// (seconds of pictures STYLE_READY waits for; loads at a time; tries per picture, 2 s then 4 s apart, before it stays low-res)
const LOAD_LEAD = 5, LOAD_PARALLEL = 4, LOAD_TRIES = 3;
const KEEP_ALL = typeof location !== 'undefined' && new URLSearchParams(location.search).has('render');
const KEEP_BEHIND = 10, KEEP_AHEAD = 30, KEEP_DRAWN = 3, KEEP_BYTES = 150e6;
// A picture's file: a Blob, or on pages that can't fetch (opened from file://, like the offline renderer's), its URL
async function loadFile(rel, signal) {
  // (from the folder the host names, or else the style's own img/)
  const url = new URL(rel, self.STYLE_BASE ?? new URL('img/', location.href));
  try {
    const r = await fetch(url, { signal });
    if (!r.ok) throw new Error(`${r.status} ${url}`);
    return await r.blob();
  } catch (e) {
    if (typeof Image === 'undefined' || signal?.aborted) throw e;
    return url;
  }
}
async function decodeFile(file) {
  if (file instanceof Blob) return createImageBitmap(file);
  const im = new Image(); im.src = file.href; await im.decode();
  return createImageBitmap(im);
}
// the stills with work to do (a download, or a decode for the playhead's window), soonest needed first; the stills to keep decoded
let _queue = Object.keys(STILLS), _keep = new Set(_queue);
const _loading = new Map(), _tries = new Map(), _retryAt = new Map();   // name → its load's AbortController; failures; next try
const _drawnAt = new Map();   // name → when a frame last drew it (performance.now())
let _lowIn = false, _drawn = new Set(), _lowLast = [], _segLast = null, _tLast = -1;
const needsWork = n => !FULL.has(n) && (_keep.has(n) || !FILES[n]);
// A sort key for each still from time t: how soon it's next on screen (0 while it is); after those, the ones the song has already
// shown for the last time, in song order; last, any it never shows. A patch or a frame of a cut-out comes right after its base.
function neededFrom(t) {
  const next = new Map(), past = new Map();
  for (const s of SEGS) for (const [n, a, b] of STILL_USE[s.key] ?? []) {
    if (s.start + b >= t) next.set(n, Math.min(next.get(n) ?? Infinity, Math.max(0, s.start + a - t)));
    else if (!past.has(n)) past.set(n, s.start + a);
  }
  const own = n => next.get(n) ?? (past.has(n) ? DUR + past.get(n) : 3 * DUR);
  return n => STILLS[n].of ? Math.min(own(n), own(STILLS[n].of) + .01) : own(n);
}
// The stills to keep decoded at time t: those on screen from KEEP_BEHIND s before t to KEEP_AHEAD s after it, and any drawn in the last
// KEEP_DRAWN s, up to KEEP_BYTES: the ones on screen now or just drawn first, then the soonest needed, then the most recently shown.
function keepFrom(t) {
  const rank = new Map(), now = performance.now();
  for (const s of SEGS) for (const [n, a, b] of STILL_USE[s.key] ?? []) {
    const from = s.start + a - t, since = t - s.start - b;
    const r = since <= 0 ? (from <= KEEP_AHEAD ? Math.max(0, from) : null) : (since <= KEEP_BEHIND ? KEEP_AHEAD + since : null);
    if (r !== null) rank.set(n, Math.min(rank.get(n) ?? Infinity, r));
  }
  for (const [n, at] of _drawnAt) if (now - at <= KEEP_DRAWN * 1000) rank.set(n, -1);
  const keep = new Set();
  let bytes = 0;
  for (const [n, r] of [...rank].sort((x, y) => x[1] - y[1])) {
    const b = STILLS[n].w * STILLS[n].h * 4;
    if (r > 0 && bytes + b > KEEP_BYTES) continue;
    keep.add(n); bytes += b;
  }
  return keep;
}
// (a still going back to its stand-in)
function releaseStill(n) {
  const b = IMGS[n];
  IMGS[n] = LO[n]; FULL.delete(n);
  for (const k of [..._tints.keys()]) if (k.startsWith(`${n}|`)) dropTint(k);
  b.close();
}
function reorderStills(t) {
  const key = neededFrom(t);
  if (!KEEP_ALL) {
    _keep = keepFrom(t);
    for (const n of FULL) if (!_keep.has(n)) releaseStill(n);
  }
  _queue = Object.keys(STILLS).filter(needsWork).sort((a, b) => key(a) - key(b));
  // a load that isn't among the soonest needed any more makes way (its still stays in the queue)
  for (const [n, ac] of _loading) if (_queue.indexOf(n) >= LOAD_PARALLEL * 2) { ac.abort(); _loading.delete(n); }
  pumpStills();
}
function pumpStills() {
  const now = performance.now();
  for (const n of _queue) {
    if (_loading.size >= LOAD_PARALLEL) break;
    if (!_loading.has(n) && !(_tries.get(n) >= LOAD_TRIES) && !(_retryAt.get(n) > now)) loadStill(n);
  }
}
async function loadStill(n) {
  const ac = new AbortController();
  _loading.set(n, ac);
  try {
    const file = FILES[n] ??= await loadFile(`${n}.webp`, ac.signal);
    // (a still that isn't needed on screen soon just downloads)
    if (FULL.has(n) || !_keep.has(n)) { _firstLeft.delete(n); return; }
    const b = await decodeFile(file);
    if (FULL.has(n) || !_keep.has(n)) { b.close(); return; }
    IMGS[n] = b; FULL.add(n); _firstLeft.delete(n);
    if (_lowLast.includes(n)) self.STYLE_STALE?.();
  } catch (e) {
    if (ac.signal.aborted) return;
    const k = (_tries.get(n) ?? 0) + 1;
    _tries.set(n, k); _firstLeft.delete(n);
    console.warn(`still ${n}: ${e}`);
    if (k < LOAD_TRIES) { _retryAt.set(n, performance.now() + 2000 * k); setTimeout(pumpStills, 2000 * k + 10); }
  } finally {
    if (_loading.get(n) === ac) _loading.delete(n);
    if (!needsWork(n) && _queue.includes(n)) _queue.splice(_queue.indexOf(n), 1);
    pumpStills(); settleStills();
  }
}
let _firstLeft, _readyOK, _readyBad, _allOK, _allBad;
self.STYLE_READY = new Promise((ok, bad) => { _readyOK = ok; _readyBad = bad; });
self.STYLE_ALL = new Promise((ok, bad) => { _allOK = ok; _allBad = bad; });
self.STYLE_ALL.catch(() => {});
function settleStills() {
  if (!_lowIn) return;
  if (!_firstLeft.size) _readyOK();
  if (!_queue.length) _allOK();
  else if (_queue.every(n => _tries.get(n) >= LOAD_TRIES)) _allBad(new Error(`stills failed to load: ${_queue.join(', ')}`));
}
{
  const t0 = clamp(+(self.STYLE_START ?? 0) || 0, 0, DUR), key = neededFrom(t0);
  _firstLeft = new Set(_queue.filter(n => key(n) <= LOAD_LEAD));
  // the stand-ins first, then the pictures from t0 on
  (async () => {
    let atlas;
    for (let k = 1; !atlas; k++) {
      try { atlas = await decodeFile(await loadFile('lowres.webp')); } catch (e) {
        if (k >= LOAD_TRIES) { _readyBad(e); _allBad(e); return; }
        await new Promise(ok => setTimeout(ok, 2000 * k));
      }
    }
    await Promise.all(Object.entries(STILLS).map(async ([n, I]) => { LO[n] = await createImageBitmap(atlas, ...I.lo); if (!FULL.has(n)) IMGS[n] = LO[n]; }));
    atlas.close();
    _lowIn = true;
    settleStills();
  })();
  reorderStills(t0);
  _tLast = t0;
}
// Each frame: after a jump or into a new window, the queue is reordered from there (and the stills kept decoded change); the stills
// it drew low-res go to the front.
{
  const draw = renderFrame;
  renderFrame = t => {
    const s = segAt(t);
    if (s !== _segLast || Math.abs(t - _tLast) > 1) reorderStills(t);
    _segLast = s; _tLast = t;
    _drawn.clear();
    draw(t);
    const now = performance.now();
    for (const n of _drawn) _drawnAt.set(n, now);
    _lowLast = [..._drawn].filter(n => STILLS[n] && !FULL.has(n));
    if (_lowLast.some(n => !_loading.has(n) && !_queue.slice(0, LOAD_PARALLEL).includes(n))) {
      for (const n of _lowLast) _keep.add(n);
      _queue = [..._lowLast, ..._queue.filter(n => !_lowLast.includes(n))];
      pumpStills();
    }
  };
}
// (how many stills the last frame drew low-res, and the bytes of full pictures decoded, for the host's diagnostics)
self.STYLE_LOWRES = () => _lowLast.length;
self.STYLE_DECODED = () => [...FULL].reduce((a, n) => a + STILLS[n].w * STILLS[n].h * 4, 0);

// A framing of a still: the image point (x, y) (fractions 0..1 of its width and height) lands on the centre of the target rect,
// z zooms (1 = the still just covers the rect), r rotates (radians). Framings interpolate (kb) for Ken Burns moves.
const lerpF = (a, b, k) => ({ x: lerp(a.x ?? .5, b.x ?? .5, k), y: lerp(a.y ?? .5, b.y ?? .5, k), z: lerp(a.z ?? 1, b.z ?? 1, k), r: lerp(a.r ?? 0, b.r ?? 0, k) });

// still(name, f, o): draw a still with framing f. Returns a mapper: pt(u, v) → the screen point of image point (u, v) (fractions), and s
// (screen px per image px). o: rect [x, y, w, h] (default the frame), dx / dy (screen offset, for shakes), flip (mirror), alpha,
// patches (names of patch stills drawn on top, e.g. closed eyes), free (allow the framing to show past the still's edges),
// blend (composite op), filter (a canvas filter string, e.g. 'saturate(1.3)'; slow, use sparingly).
function still(name, f = {}, o = {}) {
  const I = STILLS[name], B = IMGS[name];
  _drawn.add(name);
  const [rx, ry, rw, rh] = o.rect ?? [0, 0, W, H];
  if (!I || !B) { ctx.fillStyle = '#E8E0F0'; ctx.fillRect(rx, ry, rw, rh); txt(`missing still: ${name}`, rx + rw / 2, ry + rh / 2, 40, '#A04060', { font: 'code' }); return { s: 1, pt: (u, v) => [rx + u * rw, ry + v * rh] }; }
  const z = f.z ?? 1, s = Math.max(rw / I.w, rh / I.h) * z;
  let cx = (f.x ?? .5) * I.w, cy = (f.y ?? .5) * I.h;
  if (!o.free) { const hw = rw / 2 / s, hh = rh / 2 / s; cx = clamp(cx, hw, Math.max(hw, I.w - hw)); cy = clamp(cy, hh, Math.max(hh, I.h - hh)); }
  const mx = rx + rw / 2, my = ry + rh / 2, ox = mx - cx * s + (o.dx ?? 0), oy = my - cy * s + (o.dy ?? 0);
  ctx.save();
  if (o.rect) { ctx.beginPath(); ctx.rect(rx, ry, rw, rh); ctx.clip(); }
  if (f.r) { ctx.translate(mx, my); ctx.rotate(f.r); ctx.translate(-mx, -my); }
  if (o.flip) { ctx.translate(mx * 2, 0); ctx.scale(-1, 1); }
  if (o.alpha !== undefined) ctx.globalAlpha *= o.alpha;
  if (o.blend) ctx.globalCompositeOperation = o.blend;
  if (o.filter) ctx.filter = o.filter;
  ctx.imageSmoothingQuality = 'high';
  ctx.drawImage(B, ox, oy, I.w * s, I.h * s);
  for (const p of o.patches ?? []) { const P = STILLS[p]; _drawn.add(p); if (P && IMGS[p]) ctx.drawImage(IMGS[p], ox + P.x * s, oy + P.y * s, P.w * s, P.h * s); }
  ctx.restore();
  const pt = (u, v) => { let x = ox + u * I.w * s, y = oy + v * I.h * s; if (o.flip) x = 2 * mx - x; if (f.r) { const c = Math.cos(f.r), sn = Math.sin(f.r), X = x - mx, Y = y - my; x = mx + X * c - Y * sn; y = my + X * sn + Y * c; } return [x, y]; };
  return { s, pt };
}
// kb(name, k, f0, f1, o): a Ken Burns move from framing f0 to f1 as k goes 0 → 1 (eased with o.ease, default ease).
const kb = (name, k, f0, f1, o = {}) => still(name, lerpF(f0, f1, (o.ease ?? ease)(clamp(k))), o);

// cut(name, x, y, h, o): draw a cut-out so its anchor (o.anchor [u, v], default the manifest's or bottom-centre [.5, 1]) lands on
// (x, y), h px tall. o: flip, rot (about the anchor), alpha, sq (squash: + wider/shorter), shadow (a soft contact shadow under it),
// tint + tintA (recolour toward tint: a silhouette at tintA = 1), rim (a white rim light offset by rim px up-left), glow.
// Returns pt(u, v) → screen point of the cut-out's (u, v).
function cut(name, x, y, h, o = {}) {
  const I = STILLS[name], B = IMGS[name];
  _drawn.add(name);
  if (!I || !B) { ctx.fillStyle = 'rgb(160 60 100 / .5)'; ctx.fillRect(x - h * .35, y - h, h * .7, h); return { pt: (u, v) => [x + (u - .5) * h * .7, y - (1 - v) * h] }; }
  const [au, av] = o.anchor ?? I.anchor ?? [.5, 1], s = h / I.h, sq = o.sq ?? 0, sx = s * (1 + sq) * (o.flip ? -1 : 1), sy = s * (1 - sq);
  if (o.shadow) { ctx.save(); ctx.globalAlpha *= (o.alpha ?? 1) * (o.shadow === true ? .28 : o.shadow); blob(x, y, I.w * s * .42, h * .045, '#2A2350', 1); ctx.restore(); }
  ctx.save(); ctx.translate(x, y); if (o.rot) ctx.rotate(o.rot); ctx.scale(sx, sy); ctx.translate(-au * I.w, -av * I.h);
  if (o.alpha !== undefined) ctx.globalAlpha *= o.alpha;
  ctx.imageSmoothingQuality = 'high';
  // (sized explicitly: a still that hasn't loaded yet draws its small stand-in, scaled up)
  if (o.glow) { ctx.save(); ctx.shadowColor = o.glow; ctx.shadowBlur = 40 * RS; ctx.drawImage(B, 0, 0, I.w, I.h); ctx.restore(); }
  if (o.rim) { const R = tintedBitmap(name, '#FFFFFF', 1); ctx.save(); ctx.globalAlpha *= .85; ctx.drawImage(R, -o.rim / s, -o.rim / s, I.w, I.h); ctx.restore(); }
  ctx.drawImage(o.tint ? tintedBitmap(name, o.tint, o.tintA ?? 1) : B, 0, 0, I.w, I.h);
  ctx.restore();
  const pt = (u, v) => { const lx = (u - au) * I.w * sx, ly = (v - av) * I.h * sy, c = Math.cos(o.rot ?? 0), sn = Math.sin(o.rot ?? 0); return [x + lx * c - ly * sn, y + lx * sn + ly * c]; };
  return { pt, s };
}
// A cached recoloured copy of a still (the same bitmap every time, so it's still a pure function of time), the size of the bitmap it
// recolours (the stand-in's, until the full picture has loaded). The cache keeps the most recently used copies, up to TINT_BYTES (the
// third chorus's silhouetted runners go through 67 MB of them in half a second, but a fading tint makes a new copy every frame), and
// a still going back to its stand-in takes its copies with it.
const _tints = new Map(), TINT_BYTES = 80e6;
let _tintBytes = 0;
function tintedBitmap(name, col, a = 1) {
  const B = IMGS[name], key = `${name}|${col}|${a}|${B.width}`;
  let c = _tints.get(key);
  if (c) { _tints.delete(key); _tints.set(key, c); return c; }
  c = makeCanvas(B.width, B.height); const g = c.getContext('2d');
  g.drawImage(B, 0, 0); g.globalCompositeOperation = 'source-atop'; g.globalAlpha = a; g.fillStyle = col; g.fillRect(0, 0, B.width, B.height);
  _tints.set(key, c); _tintBytes += c.width * c.height * 4;
  for (const [k, old] of _tints) {
    if (_tintBytes <= TINT_BYTES || old === c) break;
    dropTint(k);
  }
  return c;
}
function dropTint(key) {
  const c = _tints.get(key);
  _tints.delete(key); _tintBytes -= c.width * c.height * 4;
}

// parallax(pan, layers): one camera move shared by a background plate and cut-outs; each layer shifts by pan × its depth
// (0 = far away, 1 = the subject, >1 = in front). pan = [dx, dy] in px. Layers are drawn in order:
//   { still: name, f, depth, o }  a plate (framed with f; the pan moves its framing)  |  { cut: name, x, y, h, depth, o }  a cut-out.
function parallax(pan, layers) {
  const out = [];
  for (const L of layers) {
    const d = L.depth ?? 1, dx = pan[0] * d, dy = pan[1] * d;
    if (L.still) out.push(still(L.still, L.f ?? {}, { ...(L.o ?? {}), dx: (L.o?.dx ?? 0) + dx, dy: (L.o?.dy ?? 0) + dy, free: true }));
    else out.push(cut(L.cut, L.x + dx, L.y + dy, L.h, L.o ?? {}));
  }
  return out;
}
// panel(x, y, w, h, fn): draw a whole shot (fn paints a full 1920×1080 frame) shrunk into a rectangle: split screens, TV screens.
function panel(x, y, w, h, fn, o = {}) {
  ctx.save(); ctx.beginPath(); ctx.rect(x, y, w, h); ctx.clip();
  const s = Math.max(w / W, h / H); ctx.translate(x + w / 2, y + h / 2); ctx.scale(s, s); ctx.translate(-W / 2, -H / 2);
  fn(); ctx.restore();
  if (o.border !== false) { ctx.save(); ctx.strokeStyle = o.border ?? '#FFFFFF'; ctx.lineWidth = o.bw ?? 8; ctx.strokeRect(x, y, w, h); ctx.restore(); }
}

// =====================================================================================================
// TIME: beats, cuts, blinks
// =====================================================================================================
// beatsIn(t, seg): beats counted on the tempo grid from the beat at (or just before) the window's start. It starts between −0.2 and
// 1 (lines begin on the sung word, not always on a beat), so whole-beat cuts land on the grid. Stage every shot in these.
const beatsIn = (t, seg) => bpOf(t) - Math.floor(bpOf(seg.start) + .2);
// cuts(b, starts): which sub-shot beat b falls in, given the beats each one starts on ([0, 4] = two cuts). → [index, beats into it]
function cuts(b, starts) { let i = 0; while (i + 1 < starts.length && b >= starts[i + 1]) i++; return [i, b - starts[i]]; }
// cutFlash(bb, k, len): the short white flash that opens a cut, by beats since the cut (≈ 0.1 s at the default len).
const cutFlash = (bb, k = .7, len = .3, col = '#FFFFFF') => flash(k * (1 - clamp(bb / len)), col);
// hit(bb, len): 1 at a hit, decaying over len beats (for punches, shakes, glows).
const hit = (bb, len = .5) => bb < 0 ? 0 : Math.exp(-bb / len * 3);
// shake(t, amt): a jittery camera offset [dx, dy] (re-rolled 24×/s); scale amt by hit() for impacts.
const shake = (t, amt) => amt <= 0 ? [0, 0] : shakeXY(t, amt, 24);
// blinking(t, seed): true during a blink (≈ 0.13 s, every 2.5–4 s per seed). Draw the still's closed-eyes patch then.
function blinking(t, seed = 1) { const per = 2.6 + hash(seed) * 1.4, ph = (t + hash(seed + 7) * per) % per; return ph < .13; }
// punch(bb, amt): a quick zoom punch on a beat (1 + amt at the hit, easing back).
const punch = (bb, amt = .06) => 1 + amt * hit(bb, .4);

// =====================================================================================================
// DRAWING PRIMITIVES (for effects and text)
// =====================================================================================================
function linGrad(x0, y0, x1, y1, stops) { const g = ctx.createLinearGradient(x0, y0, x1, y1); for (const [k, c] of stops) g.addColorStop(k, c); return g; }
function blob(cx, cy, rx, ry, col, a = 1) {
  if (rx <= 0 || ry <= 0) return;
  ctx.save(); ctx.translate(cx, cy); ctx.scale(1, ry / rx);
  const g = ctx.createRadialGradient(0, 0, 0, 0, 0, rx); g.addColorStop(0, alpha(col, a)); g.addColorStop(1, alpha(col, 0));
  ctx.fillStyle = g; ctx.beginPath(); ctx.arc(0, 0, rx, 0, TAU); ctx.fill(); ctx.restore();
}
const ellPath = (cx, cy, rx, ry, rot = 0) => { const p = new Path2D(); p.ellipse(cx, cy, Math.abs(rx), Math.abs(ry), rot, 0, TAU); return p; };
function fillP(path, col) { ctx.fillStyle = col; ctx.fill(path); }
function rrPath(x, y, w, h, r) { const p = new Path2D(); p.roundRect(x, y, w, h, r); return p; }
// a tapered ray from (x0, y0) to (x1, y1), w wide at its widest
function ray(x0, y0, x1, y1, w, col) {
  const dx = x1 - x0, dy = y1 - y0, L = Math.hypot(dx, dy) || 1, nx = -dy / L * w / 2, ny = dx / L * w / 2, mx = x0 + dx * .35, my = y0 + dy * .35;
  ctx.fillStyle = col; ctx.beginPath(); ctx.moveTo(x0, y0); ctx.lineTo(mx + nx, my + ny); ctx.lineTo(x1, y1); ctx.lineTo(mx - nx, my - ny); ctx.closePath(); ctx.fill();
}
function starShape(cx, cy, r, col, inner = .45, n = 5, rot = -Math.PI / 2) {
  ctx.fillStyle = col; ctx.beginPath();
  for (let i = 0; i < n * 2; i++) { const a = rot + i * Math.PI / n, rr = i % 2 ? r * inner : r; i ? ctx.lineTo(cx + Math.cos(a) * rr, cy + Math.sin(a) * rr) : ctx.moveTo(cx + Math.cos(a) * rr, cy + Math.sin(a) * rr); }
  ctx.closePath(); ctx.fill();
}
// grade(col, a, blend): a full-frame colour grade ('multiply' for night, 'screen' for haze, 'overlay', 'color'…).
function grade(col, a = 1, blend = 'multiply') { if (a <= 0) return; ctx.save(); ctx.setTransform(RS, 0, 0, RS, 0, 0); ctx.globalCompositeOperation = blend; ctx.globalAlpha = clamp(a); ctx.fillStyle = col; ctx.fillRect(0, 0, W, H); ctx.restore(); }
// letterbox(k): cinematic black bars (k 0..1 slides them in).
function letterbox(k, hgt = 110) { if (k <= 0) return; ctx.fillStyle = '#0E0B18'; ctx.fillRect(0, 0, W, hgt * k); ctx.fillRect(0, H - hgt * k, W, hgt * k); }

// =====================================================================================================
// LIGHT & FX: flares, leaks, rays, sparkles, petals, confetti, speed lines, flashes, bursts (pure functions of time)
// =====================================================================================================
function addGlow(x, y, r, col, a = 1) { ctx.save(); ctx.globalCompositeOperation = 'lighter'; blob(x, y, r, r, col, a); ctx.restore(); }
// rays(x, y, o): soft god-rays fanning from (x, y) (usually off the top-left corner). o: n, spread, len, col, a, ang, t (slow drift).
function rays(x, y, o = {}) {
  const n = o.n ?? 7, col = o.col ?? '#FFFFFF', len = o.len ?? 2600, base = o.ang ?? .75, spread = o.spread ?? .7, t = o.t ?? 0;
  ctx.save(); ctx.globalCompositeOperation = o.blend ?? 'screen';
  for (let i = 0; i < n; i++) {
    const a = base + (i / (n - 1) - .5) * spread + Math.sin(t * .4 + i * 1.7) * .02, w = .025 + hash(i * 3 + 1) * .05, k = (o.a ?? .22) * (.5 + .5 * hash(i * 5 + 2)) * (.8 + .2 * Math.sin(t * 1.3 + i));
    const g = ctx.createLinearGradient(x, y, x + Math.cos(a) * len, y + Math.sin(a) * len); g.addColorStop(0, alpha(col, k)); g.addColorStop(1, alpha(col, 0));
    ctx.fillStyle = g; ctx.beginPath(); ctx.moveTo(x, y); ctx.lineTo(x + Math.cos(a - w) * len, y + Math.sin(a - w) * len); ctx.lineTo(x + Math.cos(a + w) * len, y + Math.sin(a + w) * len); ctx.closePath(); ctx.fill();
  }
  ctx.restore();
}
// flare(x, y, k, o): a lens flare from a light at (x, y): a bright core, a streak and a chain of coloured ghosts through the centre.
function flare(x, y, k = 1, o = {}) {
  if (k <= 0) return;
  ctx.save(); ctx.globalCompositeOperation = 'lighter';
  blob(x, y, 260 * (o.size ?? 1), 260 * (o.size ?? 1), o.col ?? '#FFF1D6', .55 * k);
  blob(x, y, 70, 70, '#FFFFFF', .9 * k);
  ctx.globalAlpha = .9 * k; ctx.fillStyle = linGrad(x - 600, y, x + 600, y, [[0, 'rgb(255 255 255 / 0)'], [.5, 'rgb(255 250 230 / .8)'], [1, 'rgb(255 255 255 / 0)']]); ctx.fillRect(x - 600, y - 2, 1200, 4);
  const dx = W / 2 - x, dy = H / 2 - y;
  [[.35, 30, '#FFD6A0', .25], [.62, 14, '#B8F0FF', .35], [.9, 60, '#FFB0D8', .12], [1.2, 22, '#C8FFD0', .25], [1.5, 90, '#A8C8FF', .08], [1.75, 36, '#FFE8A0', .18]].forEach(([f, r, c, a]) => {
    ctx.globalAlpha = k; blob(x + dx * f, y + dy * f, r, r, c, a * 1.6);
    ctx.strokeStyle = alpha(c, a * .8 * k); ctx.lineWidth = 2; ctx.beginPath(); ctx.arc(x + dx * f, y + dy * f, r * .9, 0, TAU); ctx.stroke();
  });
  ctx.restore();
}
// leak(k, o): a warm light leak washing in from a frame edge (o.side: 'left' | 'right' | 'top' | 'bottom'; o.col).
function leak(k, o = {}) {
  if (k <= 0) return;
  const side = o.side ?? 'left', col = o.col ?? '#FFB27A';
  ctx.save(); ctx.globalCompositeOperation = 'screen';
  const [x0, y0, x1, y1] = { left: [0, 0, W * .6, 0], right: [W, 0, W * .4, 0], top: [0, 0, 0, H * .7], bottom: [0, H, 0, H * .3] }[side];
  ctx.fillStyle = linGrad(x0, y0, x1, y1, [[0, alpha(col, .75 * k)], [.5, alpha(col, .25 * k)], [1, alpha(col, 0)]]); ctx.fillRect(0, 0, W, H);
  ctx.restore();
}
// sparkle(x, y, r, a, col): a four-point twinkle with a soft glow.
function sparkle(x, y, r, a = 1, col = '#FFFFFF') {
  if (r <= .5 || a <= 0) return;
  ctx.save(); ctx.globalAlpha *= a; blob(x, y, r * 1.6, r * 1.6, col, .45);
  ctx.fillStyle = col; ctx.beginPath();
  for (let i = 0; i < 8; i++) { const an = i * Math.PI / 4 - Math.PI / 2, rr = i % 2 ? r * .16 : r * (i % 4 === 0 ? 1 : .7); i ? ctx.lineTo(x + Math.cos(an) * rr, y + Math.sin(an) * rr) : ctx.moveTo(x + Math.cos(an) * rr, y + Math.sin(an) * rr); }
  ctx.closePath(); ctx.fill(); ctx.restore();
}
// sparkleField(t, o): twinkling sparkles over a region. o: n, x0, y0, x1, y1, r, seed, col, rate.
function sparkleField(t, o = {}) {
  const n = o.n ?? 24, seed = o.seed ?? 3, [x0, y0, x1, y1] = [o.x0 ?? 0, o.y0 ?? 0, o.x1 ?? W, o.y1 ?? H];
  for (let i = 0; i < n; i++) {
    const ph = frac(t * (o.rate ?? .7) * (.6 + hash2(seed, i) * .8) + hash2(seed, i + 50)), k = Math.sin(ph * Math.PI) ** 3;
    sparkle(lerp(x0, x1, hash2(seed, i + 10)), lerp(y0, y1, hash2(seed, i + 20)), (o.r ?? 16) * (.5 + hash2(seed, i + 30)) * k, k, o.col ?? '#FFFFFF');
  }
}
// glint(x, y, r, k): the anime glasses/eye "ping": a white four-point star with a flash ring.
function glint(x, y, r, k) {
  if (k <= 0) return;
  addGlow(x, y, r * 1.5, '#FFFFFF', .45 * k);
  sparkle(x, y, r * (.6 + .4 * k), 1, '#FFFFFF');
  ctx.save(); ctx.globalAlpha = k * .8; ctx.strokeStyle = '#FFFFFF'; ctx.lineWidth = 3; ctx.beginPath(); ctx.arc(x, y, r * (1.6 - k * .6), 0, TAU); ctx.stroke(); ctx.restore();
}
// lensFlash(pts, r, k): the "glasses flash": white-out ellipses over a pair of lenses (screen points from still()'s pt), plus a glint.
function lensFlash(pts, rx, ry, k) {
  if (k <= 0) return;
  ctx.save(); ctx.globalAlpha = .92 * k; ctx.fillStyle = '#FFFFFF';
  for (const [x, y] of pts) { ctx.beginPath(); ctx.ellipse(x, y, rx, ry, 0, 0, TAU); ctx.fill(); }
  ctx.restore();
  const [gx, gy] = pts[0]; glint(gx + rx * .4, gy - ry * .4, rx * 1.3, k);
}
// petal(x, y, s, rot, flip, col): one sakura petal; petals(t, o): a drifting shower (o: n, wind, fall, seed, s, col, x0, x1, alpha, depth).
function petal(x, y, s, rot, flip = 1, col = AP.sakura) {
  ctx.save(); ctx.translate(x, y); ctx.rotate(rot); ctx.scale(s, s * Math.max(.15, Math.abs(flip)));
  ctx.beginPath(); ctx.moveTo(0, -12); ctx.bezierCurveTo(9, -9, 9, 5, 2, 11); ctx.lineTo(0, 8); ctx.lineTo(-2, 11); ctx.bezierCurveTo(-9, 5, -9, -9, 0, -12); ctx.closePath();
  ctx.fillStyle = col; ctx.fill(); ctx.strokeStyle = alpha(AP.sakuraDk, .7); ctx.lineWidth = 1.2 / s; ctx.stroke();
  ctx.fillStyle = alpha('#FFFFFF', .45); ctx.beginPath(); ctx.ellipse(-1, -4, 3.5, 6, .2, 0, TAU); ctx.fill();
  ctx.restore();
}
function petals(t, o = {}) {
  const n = o.n ?? 40, seed = o.seed ?? 7, wind = o.wind ?? 120, fall = o.fall ?? 90, x0 = o.x0 ?? -200, x1 = o.x1 ?? W + 200, span = x1 - x0 + 400;
  ctx.save(); ctx.globalAlpha *= o.alpha ?? 1;
  for (let i = 0; i < n; i++) {
    const sp = .6 + hash2(seed, i) * .8, life = (H + 200) / (fall * sp), ph = frac(t / life + hash2(seed, i + 1)), y = -100 + ph * (H + 200);
    const x = lerp(x0, x1, hash2(seed, i + 2)) + wind * ph * life * .3 + Math.sin(t * 1.3 * sp + i) * 40;
    const s = (o.s ?? 1.3) * (.6 + hash2(seed, i + 3) * .8) * (o.depth ? lerp(.6, 1.8, hash2(seed, i + 4)) : 1);
    const xx = ((x - x0 + 200) % span + span) % span + x0 - 200;
    petal(xx, y, s, t * (1 + hash2(seed, i + 5)) + i, Math.sin(t * 2.2 * sp + i * 2), o.col);
  }
  ctx.restore();
}
// confetti(t, o): falling paper confetti (o: n, seed, cols, fall, s, t0 = when it started: pieces enter from the top after it).
function confetti(t, o = {}) {
  const n = o.n ?? 70, seed = o.seed ?? 5, cols = o.cols ?? ['#FFD34A', '#FF6FA0', '#6FC8FF', '#8BE0A8', '#FFFFFF', '#B89CFF'], fall = o.fall ?? 260;
  for (let i = 0; i < n; i++) {
    const age = t - (o.t0 ?? -99) - hash2(seed, i) * .4; if (age < 0) continue;
    const sp = .7 + hash2(seed, i + 1) * .6, y = -40 + (o.t0 === undefined ? frac(t * fall * sp / (H + 80) + hash2(seed, i + 2)) * (H + 80) : age * fall * sp * 1.6 - hash2(seed, i + 9) * 300);
    if (y > H + 40) continue;
    const x = hash2(seed, i + 3) * W + Math.sin(t * 2 * sp + i) * 50, s = (o.s ?? 1) * (10 + hash2(seed, i + 4) * 8), rot = t * 5 * sp + i, fl = Math.sin(t * 7 * sp + i);
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot); ctx.scale(1, fl); ctx.fillStyle = cols[i % cols.length]; ctx.fillRect(-s / 2, -s * .3, s, s * .6); ctx.restore();
  }
}
// speedLines(cx, cy, t, o): radial anime focus lines converging on (cx, cy), re-rolled 12×/s. o: n, r0 (clear radius), col, a, w.
function speedLines(cx, cy, t, o = {}) {
  const n = o.n ?? 90, r0 = o.r0 ?? 260, col = o.col ?? '#FFFFFF', f = Math.floor(t * 12);
  ctx.save(); ctx.globalAlpha *= o.a ?? .8; ctx.fillStyle = col;
  for (let i = 0; i < n; i++) {
    const a = (i + hash2(f, i) * .8) / n * TAU, w = (o.w ?? .012) * (.4 + hash2(f, i + 300) * 1.2), r1 = r0 * (1 + hash2(f, i + 600) * .5), R = 2400;
    ctx.beginPath(); ctx.moveTo(cx + Math.cos(a) * r1, cy + Math.sin(a) * r1); ctx.lineTo(cx + Math.cos(a - w) * R, cy + Math.sin(a - w) * R); ctx.lineTo(cx + Math.cos(a + w) * R, cy + Math.sin(a + w) * R); ctx.closePath(); ctx.fill();
  }
  ctx.restore();
}
// speedBars(t, o): horizontal (o.ang) streaks rushing past, for runs and whip pans. o: n, a, col, ang, speed, y0, y1.
function speedBars(t, o = {}) {
  const n = o.n ?? 40, ang = o.ang ?? 0, speed = o.speed ?? 3000, col = o.col ?? '#FFFFFF';
  ctx.save(); ctx.globalAlpha *= o.a ?? .6; ctx.translate(W / 2, H / 2); ctx.rotate(ang); ctx.fillStyle = col;
  for (let i = 0; i < n; i++) {
    const y = lerp(o.y0 ?? -H * .7, o.y1 ?? H * .7, hash2(31, i)), L = 200 + hash2(32, i) * 600, x = ((-(t * speed * (.6 + hash2(33, i))) + hash2(34, i) * 4000) % 4000 + 4000) % 4000 - 2000, th = 2 + hash2(35, i) * 5;
    ctx.fillRect(x, y, L, th);
  }
  ctx.restore();
}
// flash(k, col): a full-frame colour flash (white by default); k 0..1.
function flash(k, col = '#FFFFFF') { if (k <= 0) return; ctx.save(); ctx.setTransform(RS, 0, 0, RS, 0, 0); ctx.globalAlpha = clamp(k); ctx.fillStyle = col; ctx.fillRect(0, 0, W, H); ctx.restore(); }
// burst(x, y, r, k, cols): a firework/impact burst (radiating rays + a ring), k 0..1 through its life.
function burst(x, y, r, k, cols = ['#FFFFFF', '#FFD86A', '#FF8FB8']) {
  if (k <= 0 || k >= 1) return;
  const e = easeOut(k), n = 16;
  ctx.save(); ctx.globalAlpha *= 1 - k * k;
  for (let i = 0; i < n; i++) { const a = i / n * TAU + .2, r0 = r * e * .3, r1 = r * e; ray(x + Math.cos(a) * r0, y + Math.sin(a) * r0, x + Math.cos(a) * r1, y + Math.sin(a) * r1, r * .07 * (1 - k * .6), cols[i % cols.length]); }
  ctx.strokeStyle = cols[0]; ctx.lineWidth = r * .05 * (1 - k); ctx.beginPath(); ctx.arc(x, y, r * e * 1.1, 0, TAU); ctx.stroke();
  ctx.restore();
  addGlow(x, y, r * 1.4, '#FFE0B0', .7 * (1 - k));
}
// impactFrame(k, col): the anime "impact frame": the picture inverted to a two-tone negative for a few frames on a hit.
function impactFrame(k) { if (k <= 0) return; ctx.save(); ctx.setTransform(RS, 0, 0, RS, 0, 0); ctx.globalCompositeOperation = 'difference'; ctx.globalAlpha = clamp(k); ctx.fillStyle = '#FFFFFF'; ctx.fillRect(0, 0, W, H); ctx.restore(); }
// zoomBlur(k, cx, cy): a radial zoom burst of whatever is on the canvas (a few scaled, faded copies of the frame over itself).
function zoomBlur(k, cx = W / 2, cy = H / 2) {
  if (k <= 0) return;
  ctx.save(); ctx.setTransform(1, 0, 0, 1, 0, 0);
  for (let i = 1; i <= 3; i++) {
    const s = 1 + k * .05 * i, X = cx * RS, Y = cy * RS;
    ctx.globalAlpha = .28 * clamp(k * 2) / i; ctx.drawImage(canvas, X - X * s, Y - Y * s, canvas.width * s, canvas.height * s);
  }
  ctx.restore();
}
// sparks(x, y, t, o): a fizzing spark (a fuse tip, a sparkler): a hot core and short rays re-rolled 24×/s.
function sparks(x, y, t, o = {}) {
  const f = Math.floor(t * 24), r = o.r ?? 70;
  addGlow(x, y, r * 1.4, '#FFB050', .8); addGlow(x, y, r * .4, '#FFFFFF', 1);
  for (let j = 0; j < (o.n ?? 14); j++) { const a = hash2(f, j) * TAU, rr = r * (.3 + hash2(f, j + 40) * .9); ray(x, y, x + Math.cos(a) * rr, y + Math.sin(a) * rr, 5, j % 2 ? '#FFE680' : '#FFFFFF'); }
}

// =====================================================================================================
// TEXT: the title logo, cast name cards, name tags for real people, bubbles, stamps
// =====================================================================================================
// logoText(str, x, y, size, o): one line of logo lettering. o: font, grad ([top, mid, bottom]), rimCol, edge (navy), rot, spacing,
// k (0..1 pop-in, letter by letter), skew, align ('center' | 'left').
function logoText(str, x, y, size, o = {}) {
  const fam = FONTS[o.font ?? 'rammetto'], sp_ = o.spacing ?? size * .02;
  ctx.save(); ctx.translate(x, y); if (o.rot) ctx.rotate(o.rot); if (o.skew) ctx.transform(1, 0, o.skew, 1, 0, 0);
  ctx.font = `${size}px "${fam}"`; ctx.textBaseline = 'middle'; ctx.textAlign = 'left';
  const chars = [...str], ws = chars.map(c => ctx.measureText(c).width), tot = ws.reduce((a, b) => a + b, 0) + sp_ * (chars.length - 1);
  let cx = o.align === 'left' ? 0 : -tot / 2;
  const k = o.k ?? 1;
  chars.forEach((c, i) => {
    const kk = clamp(k * (chars.length + 3) - i), sc = kk < 1 ? backOut(kk, 2.6) : 1;
    if (kk > 0 && c !== ' ') {
      ctx.save(); ctx.translate(cx + ws[i] / 2, 0); ctx.scale(sc, sc); ctx.lineJoin = 'round';
      if (o.shadow !== false) { ctx.fillStyle = alpha(o.edge ?? '#2A2350', .35); ctx.fillText(c, -ws[i] / 2 + size * .05, size * .09); }
      ctx.strokeStyle = o.edge ?? '#2A2350'; ctx.lineWidth = size * .26; ctx.strokeText(c, -ws[i] / 2, 0);
      ctx.strokeStyle = o.rimCol ?? '#FFFFFF'; ctx.lineWidth = size * .15; ctx.strokeText(c, -ws[i] / 2, 0);
      const [g0, g1, g2] = o.grad ?? ['#FF7FB0', '#FF5A8A', '#FFB060'];
      ctx.fillStyle = linGrad(0, -size * .45, 0, size * .45, [[0, g0], [.55, g1], [1, g2]]); ctx.fillText(c, -ws[i] / 2, 0);
      ctx.save(); ctx.beginPath(); ctx.rect(-ws[i], -size, ws[i] * 2, size * .42); ctx.clip(); ctx.fillStyle = alpha('#FFFFFF', .35); ctx.fillText(c, -ws[i] / 2, 0); ctx.restore();
      ctx.restore();
    }
    cx += ws[i] + sp_;
  });
  ctx.restore();
  return tot;
}
// titleLogo(x, y, s, k, t): the title block ("WE DIDN'T / START THE / SCALING") centred on (x, y) at scale s; k 0..1 builds it.
function titleLogo(x, y, s = 1, k = 1, t = 0) {
  ctx.save(); ctx.translate(x, y); ctx.scale(s, s);
  const k1 = clamp(k / .35), k2 = clamp((k - .2) / .35), k3 = clamp((k - .4) / .45), k4 = clamp((k - .8) / .2);
  logoText("WE DIDN'T", -70, -150, 58, { font: 'archivo', k: k1, rot: -.06, grad: ['#6FD0FF', '#3D8BFF', '#6A5CFF'] });
  logoText('START THE', 10, -70, 58, { font: 'archivo', k: k2, rot: -.06, grad: ['#6FD0FF', '#3D8BFF', '#6A5CFF'] });
  logoText('SCALING', 0, 56, 124, { font: 'rammetto', k: k3, rot: -.06, grad: ['#FFB6D0', '#FF4F8B', '#FF9A4A'], spacing: 3 });
  if (k4 > 0) {
    txt('— a scaling-club opening —', 20, 158, 24, '#FFFFFF', { font: 'code', alpha: k4, rot: -.06, stroke: 'rgb(42 35 80 / .7)', sw: 6 });
    sparkle(250, -12, 40 * k4 * (1 + .15 * Math.sin(t * 6)), 1, '#FFFFFF'); sparkle(-260, 104, 24 * k4, 1, '#FFF4B0');
  }
  ctx.restore();
}
// nameCard(name, role, x, y, k, col, o): the cast-reveal caption: a big name that slides in over a colour bar, a role line.
function nameCard(name, role, x, y, k, col = '#FF5A9A', o = {}) {
  if (k <= 0) return;
  const e = easeOut(clamp(k)), size = o.size ?? 96;
  ctx.save(); ctx.translate(x + (1 - e) * -200, y);
  ctx.save(); ctx.transform(1, 0, -.25, 1, 0, 0);
  const tw = textW(name, size, 'rammetto') + 60;
  ctx.fillStyle = col; ctx.globalAlpha = .92; ctx.fillRect(-30, size * .18, tw * e, size * .5);
  ctx.restore();
  logoText(name, 0, 0, size, { font: 'rammetto', align: 'left', grad: ['#FFFFFF', '#FFFFFF', '#FFE8F2'], edge: '#2A2350', rimCol: col, k: 1, spacing: 2 });
  txt(role, 8, size * .8, size * .3, '#FFFFFF', { font: 'code', align: 'left', stroke: '#2A2350', sw: 7 });
  ctx.restore();
}
// nameTag(name, note, x, y, k, col): the caption for a real person named in the lyrics (always an anime extra or off-screen, never a
// likeness): the name big and a note under it, on a slanted white chip with a coloured edge; slides in with k.
function nameTag(name, note, x, y, k, col = '#2FA890') {
  if (k <= 0) return;
  ctx.save(); ctx.globalAlpha *= clamp(k * 2); ctx.translate(x + (1 - easeOut(k)) * -60, y);
  ctx.save(); ctx.transform(1, 0, -.2, 1, 0, 0); ctx.fillStyle = 'rgb(255 255 255 / .93)';
  const w = Math.max(textW(name, 56, 'rammetto'), textW(note, 22, 'code')) + 60; ctx.fillRect(-20, -48, w, 110); ctx.fillStyle = col; ctx.fillRect(-20, -48, 12, 110); ctx.restore();
  txt(name, 10, -10, 56, '#1E2A3A', { font: 'rammetto', align: 'left' });
  txt(note, 12, 40, 22, '#4A6070', { font: 'code', align: 'left' });
  ctx.restore();
}
// sayBubble(str, x, y, size, k, tx, ty, o): a white speech bubble centred on (x, y) with a tail to (tx, ty); it pops in and the text
// types on as k goes 0 → 1. o.font (default 'archivo'), o.col, o.fill, o.line.
function sayBubble(str, x, y, size, k, tx, ty, o = {}) {
  if (k <= 0) return;
  const f = o.font ?? 'archivo', n = Math.ceil([...str].length * clamp(k * 1.4)), shown = [...str].slice(0, n).join('');
  const tw = textW(str, size, f), w = tw / 2 + size * .8, h = size * 1.0, e = backOut(clamp(k * 3), 2);
  ctx.save(); ctx.translate(x, y); ctx.scale(e, e);
  const fill = o.fill ?? '#FFFFFF', line = o.line ?? '#3B3150';
  ctx.lineJoin = 'round'; ctx.lineWidth = 4; ctx.strokeStyle = line; ctx.fillStyle = fill;
  const tail = new Path2D(); tail.moveTo(-size * .45, h * .5); tail.lineTo(size * .25, h * .5); tail.lineTo((tx - x) / e, (ty - y) / e); tail.closePath();
  const body = rrPath(-w, -h, w * 2, h * 2, h);
  ctx.stroke(tail); ctx.stroke(body); ctx.fill(tail); ctx.fill(body);
  txt(shown, -tw / 2, 2, size, o.col ?? '#2A2350', { font: f, align: 'left' });
  ctx.restore();
}
// stampMark(str, x, y, size, k, o): an official red stamp (VETOED, ADOPTED…) that slams down from above the frame and settles.
// o: col, rot, sub (a smaller second line).
function stampMark(str, x, y, size, k, o = {}) {
  if (k <= 0) return;
  const col = o.col ?? '#E2334A', e = clamp(k / .35), sc = lerp(2.4, 1, easeIn(e)) * (e >= 1 ? 1 + .06 * Math.exp(-(k - .35) * 18) : 1);
  const tw = textW(str, size, 'archivo'), sub = o.sub, w = tw + size * .9, h = size * (sub ? 1.75 : 1.3);
  ctx.save(); ctx.translate(x, y); ctx.rotate(o.rot ?? -.12); ctx.scale(sc, sc); ctx.globalAlpha *= clamp(e * 1.5);
  ctx.strokeStyle = col; ctx.lineWidth = size * .09; ctx.fillStyle = 'rgb(255 255 255 / .18)';
  const p = rrPath(-w / 2, -h / 2, w, h, size * .18); ctx.fill(p); ctx.stroke(p);
  ctx.lineWidth = size * .03; ctx.strokeStyle = alpha(col, .8); ctx.stroke(rrPath(-w / 2 + size * .12, -h / 2 + size * .12, w - size * .24, h - size * .24, size * .1));
  txt(str, 0, sub ? -size * .22 : size * .02, size, col, { font: 'archivo' });
  if (sub) txt(sub, 0, size * .5, size * .36, col, { font: 'code' });
  ctx.restore();
}
// popLabel(str, x, y, size, k, o): a rounded pill label that pops in (numbers, captions, "OK!!"). o: fill, col, rot, font.
function popLabel(str, x, y, size, k, o = {}) {
  if (k <= 0) return;
  const f = o.font ?? 'archivo', tw = textW(str, size, f), e = backOut(clamp(k), 2.2);
  ctx.save(); ctx.translate(x, y); ctx.rotate(o.rot ?? 0); ctx.scale(e, e);
  const p = rrPath(-tw / 2 - size * .5, -size * .72, tw + size, size * 1.44, size * .72);
  ctx.fillStyle = 'rgb(40 30 80 / .25)'; ctx.translate(6, 8); ctx.fill(p); ctx.translate(-6, -8);
  ctx.fillStyle = o.fill ?? '#FFFFFF'; ctx.fill(p); ctx.strokeStyle = o.line ?? '#2A2350'; ctx.lineWidth = 4; ctx.stroke(p);
  txt(str, 0, 2, size, o.col ?? '#2A2350', { font: f });
  ctx.restore();
}
// diagSplit(c1, c2, t, o): an anime-OP colour background: two tones split on a diagonal, with drifting stripes and dots.
function diagSplit(c1, c2, t, o = {}) {
  ctx.fillStyle = c1; ctx.fillRect(0, 0, W, H);
  const a = o.a ?? .35, x = o.x ?? W * .58;
  ctx.fillStyle = c2; ctx.beginPath(); ctx.moveTo(x - H * a, H); ctx.lineTo(x + H * a, 0); ctx.lineTo(W, 0); ctx.lineTo(W, H); ctx.closePath(); ctx.fill();
  ctx.save(); ctx.globalAlpha = .18; ctx.fillStyle = '#FFFFFF';
  for (let i = -4; i < 14; i++) { const xx = ((i * 160 + t * (o.speed ?? 240)) % 2400 + 2400) % 2400 - 300; ctx.beginPath(); ctx.moveTo(xx, H); ctx.lineTo(xx + 50, H); ctx.lineTo(xx + 50 + H * .6, 0); ctx.lineTo(xx + H * .6, 0); ctx.closePath(); ctx.fill(); }
  ctx.restore();
  ctx.save(); ctx.globalAlpha = .25; ctx.fillStyle = '#FFFFFF';
  for (let i = 0; i < 60; i++) { const px_ = (i % 12) * 170 + (Math.floor(i / 12) % 2) * 85, py = Math.floor(i / 12) * 230 + 60; ctx.beginPath(); ctx.arc(((px_ + t * 30) % (W + 100) + W + 100) % (W + 100) - 50, py, 7, 0, TAU); ctx.fill(); }
  ctx.restore();
}

// =====================================================================================================
// OVERLAYS: soft bloom + a lilac vignette, the karaoke subtitle, the date card
// =====================================================================================================
// Per-frame switches a shot may call (reset after every frame): hideCaption(), hideStamp(), captionStyle({ y, col, size }),
// setBloom(k) (0 = off; default .25), noVignette().
let _bloomK = null, _noVig = false;
const setBloom = k => { _bloomK = k; };
const noVignette = () => { _noVig = true; };
let _bl = null;
function bloomPass(k) {
  if (k <= 0) return;
  if (!_bl) { _bl = { a: makeCanvas(480, 270), b: makeCanvas(240, 135), c: makeCanvas(120, 68) }; for (const c of Object.values(_bl)) c.g = c.getContext('2d', { willReadFrequently: true }); }
  const { a, b, c } = _bl;
  a.g.globalCompositeOperation = 'copy'; a.g.drawImage(canvas, 0, 0, canvas.width, canvas.height, 0, 0, 480, 270);
  b.g.globalCompositeOperation = 'copy'; b.g.drawImage(a, 0, 0, 240, 135);
  const img = b.g.getImageData(0, 0, 240, 135), d = img.data, thr = 214;
  for (let i = 0; i < d.length; i += 4) { const l = d[i] * .3 + d[i + 1] * .59 + d[i + 2] * .11, f = l > thr ? ((l - thr) / (255 - thr)) ** 1.5 : 0; d[i] *= f; d[i + 1] *= f; d[i + 2] *= f; }
  b.g.putImageData(img, 0, 0);
  c.g.globalCompositeOperation = 'copy'; c.g.drawImage(b, 0, 0, 120, 68);
  ctx.save(); ctx.setTransform(1, 0, 0, 1, 0, 0); ctx.globalCompositeOperation = 'screen'; ctx.imageSmoothingQuality = 'high';
  ctx.globalAlpha = .6 * k; ctx.drawImage(b, 0, 0, canvas.width, canvas.height);
  ctx.globalAlpha = .9 * k; ctx.drawImage(c, 0, 0, canvas.width, canvas.height);
  ctx.restore();
}
function vignette() {
  const g = ctx.createRadialGradient(W / 2, H * .45, H * .5, W / 2, H * .45, H * 1.1);
  g.addColorStop(0, 'rgb(90 60 140 / 0)'); g.addColorStop(1, 'rgb(90 60 140 / .22)');
  ctx.fillStyle = g; ctx.fillRect(0, 0, W, H);
}
// ---------- the karaoke subtitle: white lettering with a navy rim and a soft glow; the sung part fills pink (verses) / gold (choruses) ----------
function drawCaption(t) {
  const ln = lineAt(t); if (!ln || _noCaption) return;
  const st = _captionStyle || {};
  const text = ln.text.replace(/\s*—\s*$/, '').replace(/\s+—\s+/g, ' — ');
  const age = t - ln.start, kin = easeOut(clamp(age / .16)), kout = clamp((ln.end + .35 - t) / .2);
  const chorus = ln.sec[0] !== 'V', size = st.size ?? (text.length > 44 ? 40 : 46), y = st.y ?? 1004, font = 'Archivo Black';
  ctx.save(); ctx.globalAlpha = kin * kout;
  ctx.font = `${size}px "${font}"`; ctx.textBaseline = 'middle'; ctx.textAlign = 'left';
  const sp_ = size * .02, chars = [...text], ws = chars.map(c => ctx.measureText(c).width), tw0 = ws.reduce((a, b) => a + b, 0) + sp_ * chars.length;
  const sx = Math.min(1, 1640 / tw0), tw = tw0 * sx, x0 = W / 2 - tw / 2;
  ctx.translate(x0, y + (1 - kin) * 16); ctx.scale(sx, 1);
  const prog = clamp((t - ln.start) / Math.max(.4, ln.end - ln.start - .15)), lit = prog * chars.length;
  const col = st.col ?? (chorus ? ['#FFE07A', '#FF9A4A'] : ['#FFB0D0', '#FF5A9A']);
  const draw = pass => {
    let x = 0;
    chars.forEach((c, i) => {
      const k = clamp(lit - i), bounce = k > 0 && k < 1 ? -Math.sin(k * Math.PI) * size * .08 : 0;
      if (pass === 0) { ctx.lineJoin = 'round'; ctx.strokeStyle = 'rgb(30 24 70 / .9)'; ctx.lineWidth = size * .24; ctx.strokeText(c, x, bounce); }
      else if (pass === 1) { ctx.strokeStyle = k > 0 ? col[1] : '#FFFFFF'; ctx.lineWidth = size * .1; ctx.strokeText(c, x, bounce); }
      else { ctx.fillStyle = k >= 1 ? linGrad(0, -size / 2, 0, size / 2, [[0, '#FFFFFF'], [.5, col[0]], [1, col[0]]]) : '#FFFFFF'; ctx.fillText(c, x, bounce); }
      x += ws[i] + sp_;
    });
  };
  ctx.shadowColor = 'rgb(255 120 180 / .5)'; ctx.shadowBlur = 18; draw(0); ctx.shadowBlur = 0; draw(1); draw(2);
  ctx.restore();
  ctx.save(); ctx.globalAlpha = kin * kout;
  const nx = x0 - 44, ny = y + (1 - kin) * 16;
  fillP(ellPath(nx, ny, 22, 22), chorus ? '#FF9A4A' : '#FF5A9A'); ctx.strokeStyle = '#FFFFFF'; ctx.lineWidth = 3; ctx.stroke(ellPath(nx, ny, 22, 22));
  txt('♪', nx, ny + 1, 26, '#FFFFFF', { font: 'archivo' });
  ctx.restore();
}
// ---------- the date card: a slanted white tab, the month small over the year big, a coloured stripe; wipes in on change ----------
function dateInfo(t) {
  let cur = null;
  for (const s of SEGS) { if (s.start > t) break; if (s.date && s.date !== (cur && cur.date)) cur = s; }
  return cur ? { text: cur.date, seg: cur, age: t - cur.start } : null;
}
function drawDateCard(t) {
  const d = dateInfo(t); if (!d || _noStamp) return;
  const parts = d.text.split(/\s+/), yr = parts[parts.length - 1], md = parts.slice(0, -1).join(' ');
  const k = easeOut(clamp(d.age / .28)), x = W - 60, y = 58, w = 300, h = 92;
  ctx.save(); ctx.translate(x, y); ctx.transform(1, 0, -.18, 1, 0, 0);
  ctx.beginPath(); ctx.rect(-w - 40, -20, (w + 80) * k, h + 40); ctx.clip();
  ctx.fillStyle = 'rgb(40 30 90 / .25)'; ctx.fillRect(-w + 8, 8, w, h);
  ctx.fillStyle = 'rgb(255 255 255 / .94)'; ctx.fillRect(-w, 0, w, h);
  ctx.fillStyle = linGrad(-w, 0, -w, h, [[0, '#FF6FA8'], [1, '#FF9A4A']]); ctx.fillRect(-w, 0, 14, h);
  ctx.restore();
  ctx.save(); ctx.globalAlpha = clamp((d.age - .08) / .2);
  txt(md || '·', x - w + 44, y + 26, 22, '#5A4E86', { font: 'code', align: 'left' });
  txt(yr, x - w + 38, y + 64, 50, '#2A2350', { font: 'archivo', align: 'left' });
  txt('★', x - 34, y + 22, 22, '#FF6FA8', { font: 'archivo' });
  ctx.restore();
  if (d.age < .6) sparkle(x - 20, y + 4, 26 * Math.sin(clamp(d.age / .6) * Math.PI), 1, '#FFFFFF');
}
OVERLAYS.push((t, s) => {
  if (s && s.key !== undefined) {
    bloomPass(_bloomK ?? .25);
    if (!_noVig) vignette();
    drawCaption(t);
    drawDateCard(t);
  }
  _noCaption = false; _noStamp = false; _captionStyle = null; _bloomK = null; _noVig = false;
});

// =====================================================================================================
// PLACEHOLDER for windows nobody has painted yet: the club room plate, the window's key and lyric on a card, Clawd bobbing
// =====================================================================================================
function placeholder(t, s) {
  still('club_room', { x: .5, y: .5, z: 1.04 + .02 * Math.sin(t * .3) });
  grade('#F4ECFF', .35, 'screen');
  ctx.save(); ctx.translate(W / 2 - 180, 420); ctx.rotate(-.02);
  ctx.fillStyle = 'rgb(40 30 80 / .2)'; ctx.fill(rrPath(-560, -190, 1140, 400, 26));
  ctx.fillStyle = 'rgb(255 255 255 / .94)'; ctx.fill(rrPath(-570, -200, 1140, 400, 26));
  txt(s ? s.key : '—', -520, -120, 48, '#3D6FD0', { font: 'marker', align: 'left' });
  if (s && s.text) txt(s.text, -520, -10, 44, '#2A2350', { font: 'marker', align: 'left', maxW: 1060 });
  txt('(not painted yet)', -520, s && s.text ? 110 : 20, 30, '#8A8EA0', { font: 'marker', align: 'left' });
  ctx.restore();
  const hop = Math.abs(Math.sin(frac(bpOf(t) / 2) * Math.PI));
  cut('clawd_stand', 1560, 930 - hop * 40, 300, { shadow: true, sq: (1 - hop) * .04 });
}

;
// ---- styles/anime/ch/c01_intro.js ----
// c01_intro.js: the opening's intro (≈ 40 beats at 165 BPM): the sky, the eyes, the wind, the cast reveal, the title drop.
// Every picture is a generated still (shots.json); the motion is camera moves, cut-outs, patches and light. Staging is in beats
// from the window start (b), so it follows the tempo grid if the take's timing moves.
(() => {
  const CARDS = [
    { cut: 'card_akari', name: 'AKARI HINATA', role: 'freshman · keeps asking "but WHY does it work?"', c1: '#FFD1E0', c2: '#FF8FB8', col: '#FF5A9A', side: 1 },
    { cut: 'card_ren', name: 'REN KAGAMI', role: 'sophomore · has read every paper (twice)', c1: '#CFE4FA', c2: '#5E86D8', col: '#3D6FD0', side: -1 },
    { cut: 'card_kiri', name: 'KIRI SHIROMINE', role: 'grad student · club president · reads loss curves', c1: '#E6DDFA', c2: '#9F86E0', col: '#7B5CD6', side: 1, lenses: [[.438, .332], [.618, .332]] },
  ];
  // an OP credit line (thin, white, with a soft shadow), in and out
  const credit = (a, b, x, y, lines, bt) => {
    const k = clamp((bt - a) / .6) * clamp((b - bt) / .6); if (k <= 0) return;
    lines.forEach((l, i) => txt(l, x, y + i * 52, i === 0 ? 26 : 48, '#FFFFFF', { font: i === 0 ? 'code' : 'archivo', align: 'left', alpha: k, stroke: 'rgb(60 90 160 / .55)', sw: 6 }));
  };
  section('intro', (p, lt, d, t, seg) => {
    hideCaption(); hideStamp();
    const b = bpOf(t) - Math.round(bpOf(seg.start));
    // ---------- the sky: a slow tilt down from the high blue to the rooftop railing; Clawd hops up onto it ----------
    if (b < 8) {
      const k = ease(clamp(b / 7.2));
      const v = still('intro_sky', { x: .5, y: k, z: 1.1 - .1 * k });
      rays(-100, -120, { t, a: .22, n: 8 });
      petals(t, { n: 22, seed: 3, s: 1.4, depth: true });
      if (b > 4.6) {
        // up from below the frame in an arc, a squash on landing on the top rail, then a bob on every beat
        const [rx, ry] = v.pt(.56, .856), hop = clamp((b - 4.6) / .9), land = b - 5.5;
        const x = lerp(rx + 260, rx, easeOut(hop)), y = hop < 1 ? lerp(H + 300, ry, easeOut(hop)) - Math.sin(hop * Math.PI) * 220 : ry;
        const sq = hop < 1 ? -.08 : .14 * Math.exp(-land * 5) * Math.cos(land * 14) + .04 * pulse(t);
        if (land > 0 && land < 1.2) burst(rx, ry - 90, 260, land / 1.2, ['#FFFFFF', '#FFE070', '#FFB0C8']);
        cut('clawd_jump', x, y + 8, 250, { sq, rot: hop < 1 ? (1 - hop) * .5 : 0 });
        if (land > 0) sparkleField(t, { n: 6, r: 22, seed: 4, x0: rx - 200, x1: rx + 200, y0: ry - 330, y1: ry - 60 });
      }
      credit(1, 5, 110, 760, ['OPENING THEME', "We Didn't Start the Scaling"], b);
      flare(260, 110 + (1 - k) * 60, .8 + .2 * Math.sin(t * 3));
      flash(1 - clamp(b / .6));
      return;
    }
    // ---------- extreme close-up: Akari's eyes open in three drawings (closed, half, open); star glints cross them ----------
    if (b < 12) {
      const bb = b - 8;
      const patches = bb < 1 ? ['intro_eyes.closed'] : bb < 1.35 ? ['intro_eyes.half'] : [];
      const v = still('intro_eyes', { x: .5, y: .6, z: 1.02 + bb * .025 }, { patches });
      leak(.4 + .12 * Math.sin(t * 2), { side: 'left', col: '#FFC08A' });
      if (bb > 2.2) { const g = Math.sin(clamp((bb - 2.2) / 1.2) * Math.PI); for (const u of [.34, .66]) { const [x, y] = v.pt(u, .585); glint(x + 18, y - 40, 56, g); } }
      sparkleField(t, { n: 8, r: 18, seed: 12, y0: 60, y1: 500 });
      flash(1 - clamp(bb / .25));
      return;
    }
    // ---------- the wind: Akari against the sky, laughing, then beaming at us; a sakura storm and a slow push in ----------
    if (b < 16) {
      const bb = b - 12, k = ease(clamp(bb / 4));
      still('intro_wind', { x: lerp(.6, .68, k), y: lerp(.45, .34, k), z: lerp(1.02, 1.3, k) }, { patches: bb < 1.5 ? ['intro_wind.laugh'] : [] });
      rays(-100, -120, { t, a: .2, n: 7 });
      petals(t, { n: 46, seed: 9, s: 2.1, depth: true, wind: 420, fall: 70 });
      sparkleField(t, { n: 8, r: 20, seed: 5 });
      leak(.28, { side: 'right', col: '#FFD0E0' });
      cutFlash(bb, .9, .35);
      return;
    }
    // ---------- the cast reveal: one card per four beats; the character whips in, the name slams on, a push-in, a flash out ----------
    if (b < 32) {
      const i = Math.floor((b - 16) / 4), bb = (b - 16) - i * 4, slide = easeOut(clamp(bb / .5)), push = 1 + bb * .018;
      if (i < 3) {
        const C = CARDS[i];
        diagSplit(C.c1, C.c2, t, { x: C.side > 0 ? W * .6 : W * .4, a: .3 * C.side, speed: 300 * C.side });
        speedLines(C.side > 0 ? W * .68 : W * .32, H * .4, t, { n: 70, r0: 420, a: .3 });
        const x = (C.side > 0 ? W * .7 : W * .3) + (1 - slide) * 700 * C.side;
        const v = cut(C.cut, x, H + 60 + bb * 6, 1180 * push, { shadow: false });
        if (C.lenses) { const pts = C.lenses.map(([u, w]) => v.pt(u, w)), r = v.s * 632 * .042; lensFlash(pts, r, r * .8, Math.sin(clamp((bb - 1.2) / .9) * Math.PI)); }
        nameCard(C.name, C.role, C.side > 0 ? 110 : 1000, 820, clamp((bb - .4) / .5), C.col, { size: 92 });
        sparkleField(t, { n: 8, r: 20, seed: 11 + i });
      } else {
        // Clawd's card: he bounces on every beat
        diagSplit('#FFE4CC', '#FF9E6A', t, { x: W * .6, a: .3, speed: 300 });
        speedLines(W * .68, H * .45, t, { n: 70, r0: 380, a: .3 });
        const hop = Math.abs(Math.sin(frac(b) * Math.PI));
        cut('clawd_jump', W * .68 + (1 - slide) * 700, 900 - hop * 90, 560 * push, { sq: (1 - hop) * .07, shadow: .3 });
        nameCard('CLAWD', 'club mascot · helpful, harmless, orange', 110, 820, clamp((bb - .4) / .5), '#E8783E', { size: 110 });
        sparkleField(t, { n: 10, r: 24, seed: 19 });
      }
      flash(.8 * (1 - clamp(bb / .25)));
      if (bb > 3.6) flash((bb - 3.6) / .4 * .9);
      return;
    }
    // ---------- the title drop: white flash, the key visual pulls back, the logo slams in letter by letter ----------
    const bb = b - 32, k = easeOut(clamp(bb / 3.2));
    still('keyvisual', { x: lerp(.66, .5, k), y: lerp(.42, .5, k), z: lerp(1.3, 1, k) });
    petals(t, { n: 18, seed: 21, s: 1.5, depth: true });
    titleLogo(500, 400, 1.35, clamp((bb - .8) / 3), t);
    if (bb > 3.8 && bb < 5.5) flare(1640, 120, Math.sin(clamp((bb - 3.8) / 1.7) * Math.PI));
    flash(1 - clamp(bb / .5));
  });
})();

;
// ---- styles/anime/ch/c02_v1.js ----
// c02_v1.js: Verse 1 (spring, JUN 2017 → OCT 2024): sixteen lines, one gag each, painted with generated stills (shots.json).
// Each line is staged in beats from its window start (b = beatsIn(t, seg), about 0 → 8.5); most lines cut once, near beat 4.
(() => {
  const H2 = H / 2;
  // a little heart (Sydney's)
  const heart = (x, y, r, col) => {
    ctx.fillStyle = col; ctx.beginPath(); ctx.moveTo(x, y + r * .9);
    ctx.bezierCurveTo(x - r * 1.5, y - r * .1, x - r * .7, y - r * 1.2, x, y - r * .4);
    ctx.bezierCurveTo(x + r * .7, y - r * 1.2, x + r * 1.5, y - r * .1, x, y + r * .9); ctx.fill();
  };
  // hearts rising from (x, y) in a drifting stream (pure: each heart's age comes from t and its seed)
  function heartStream(t, x, y, o = {}) {
    const n = o.n ?? 26;
    for (let i = 0; i < n; i++) {
      const life = 1.4 + hash2(71, i) * .8, age = frac(t / life + hash2(72, i)) * life, k = age / life;
      const hx = x + (hash2(73, i) - .5) * (o.spread ?? 500) + Math.sin(t * 3 + i) * 30 + k * (o.dx ?? -300), hy = y - k * (o.rise ?? 700);
      ctx.save(); ctx.globalAlpha = Math.sin(k * Math.PI); heart(hx, hy, (o.r ?? 26) * (.6 + hash2(74, i) * .8) * (.6 + k), i % 3 ? '#FF6FA8' : '#FFB0D0'); ctx.restore();
    }
  }
  // a glowing, growing curve (the scaling curve, a chain of thought, a fuse's path): pts in screen px, drawn to fraction k
  function glowPath(pts, k, o = {}) {
    if (k <= 0) return null;
    const L = [0]; for (let i = 1; i < pts.length; i++) L.push(L[i - 1] + Math.hypot(pts[i][0] - pts[i - 1][0], pts[i][1] - pts[i - 1][1]));
    const at = L[L.length - 1] * clamp(k); let i = 1; while (i < pts.length - 1 && L[i] < at) i++;
    const f = (at - L[i - 1]) / Math.max(1e-6, L[i] - L[i - 1]), tip = [lerp(pts[i - 1][0], pts[i][0], f), lerp(pts[i - 1][1], pts[i][1], f)];
    const path = new Path2D(); path.moveTo(pts[0][0], pts[0][1]); for (let j = 1; j < i; j++) path.lineTo(pts[j][0], pts[j][1]); path.lineTo(tip[0], tip[1]);
    ctx.save(); ctx.lineCap = 'round'; ctx.lineJoin = 'round';
    ctx.globalCompositeOperation = 'lighter'; ctx.strokeStyle = alpha(o.col ?? '#FFB050', .35); ctx.lineWidth = (o.w ?? 10) * 4; ctx.stroke(path);
    ctx.globalCompositeOperation = 'source-over'; ctx.strokeStyle = o.col ?? '#FFB050'; ctx.lineWidth = o.w ?? 10; ctx.stroke(path);
    ctx.strokeStyle = '#FFFFFF'; ctx.lineWidth = (o.w ?? 10) * .4; ctx.stroke(path);
    ctx.restore();
    return tip;
  }

  // ---------- V1.1 "First, 'Attention' lit the fuse": the paper on the desk, its title glowing, the fuse fizzing; then Akari, starry-eyed ----------
  line('V1', 1, (p, lt, d, t, seg) => {
    const b = beatsIn(t, seg), [i, bb] = cuts(b, [0, 4.5]);
    if (i === 0) {
      hideStamp();   // the paper's title runs along the top edge, under the date card; the card comes in with the next cut
      const k = ease(clamp(bb / 4.5));
      const v = still('v1_1_paper', { x: lerp(.42, .52, k), y: lerp(.3, .52, k), z: lerp(1.35, 1.15, k) });
      // a glow sweeps along the title, then hops to the fuse
      const sw = clamp(bb / 1.6);
      if (sw < 1) { const [x, y] = v.pt(lerp(.15, .48, sw), .035); addGlow(x, y, 120, '#FFB050', .8); sparkle(x, y, 40, 1, '#FFF4C0'); }
      const [fx, fy] = v.pt(.305, .56);
      sparks(fx + Math.sin(t * 9) * 4, fy, t, { r: 90 + 20 * pulse2(t) });
      leak(.25, { side: 'top', col: '#FFD9A0' });
      cutFlash(bb, .5);
    } else {
      const k = ease(clamp(bb / 4));
      const v = still('v1_1_akari', { x: .5, y: lerp(.5, .45, k), z: lerp(1.04, 1.18, k) });
      const [sx, sy] = v.pt(.28, .88);
      sparks(sx, sy, t, { r: 110 });
      if (bb < 1.2) burst(W * .5, H * .12, 420, bb / 1.2, ['#FFFFFF', '#FFE070', '#FFB0C8']);
      for (const u of [.455, .54]) { const [x, y] = v.pt(u, .285); glint(x, y - 10, 34, Math.sin(clamp((bb - .6) / 1.4) * Math.PI)); }
      petals(t, { n: 18, seed: 2, s: 1.4, depth: true });
      cutFlash(bb, .9, .35);
    }
  });

  // ---------- V1.2 "Scaling laws you can't refuse": Kiri the mob boss strokes Clawd; then her tablet: a perfectly straight power law ----------
  line('V1', 2, (p, lt, d, t, seg) => {
    const b = beatsIn(t, seg), [i, bb] = cuts(b, [-1, 4]);
    if (i === 0) {
      const k = ease(clamp((b - .5) / 3.5));
      const v = still('v1_2_kiri', { x: .52, y: lerp(.5, .38, k), z: lerp(1.05, 1.3, k) });
      letterbox(1);
      const g = Math.sin(clamp((b - 1) / 1) * Math.PI), L = [v.pt(.605, .245), v.pt(.683, .24)];
      lensFlash(L, 42 * v.s, 34 * v.s, g);
      const [mx, my] = v.pt(.6, .33);
      sayBubble("It's a power law.", 520, 220, 50, clamp((b - 2) / 1.2), mx - 60, my);
      if (b < 1) flash(.6 * (1 - clamp((b - .5) / .2)));
    } else {
      // the tablet fills the frame: log compute (x) vs log loss (y); a point lands every half beat on one straight line
      ctx.fillStyle = '#20264A'; ctx.fillRect(0, 0, W, H);
      const bez = 70, x0 = 260, y0 = 170, x1 = 1680, y1 = 860;
      ctx.fillStyle = '#0E1330'; ctx.fillRect(bez, bez, W - bez * 2, H - bez * 2);
      ctx.strokeStyle = 'rgb(120 150 255 / .18)'; ctx.lineWidth = 2;
      for (let gx = 0; gx <= 8; gx++) { const x = lerp(x0, x1, gx / 8); ctx.beginPath(); ctx.moveTo(x, y0); ctx.lineTo(x, y1); ctx.stroke(); }
      for (let gy = 0; gy <= 5; gy++) { const y = lerp(y0, y1, gy / 5); ctx.beginPath(); ctx.moveTo(x0, y); ctx.lineTo(x1, y); ctx.stroke(); }
      txt('compute (log)', (x0 + x1) / 2, y1 + 60, 34, '#9FB4FF', { font: 'code' });
      txt('loss (log)', x0 - 70, (y0 + y1) / 2, 34, '#9FB4FF', { font: 'code', rot: -Math.PI / 2 });
      const n = clamp(Math.floor(bb * 2) + 1, 0, 8), line = u => [lerp(x0 + 60, x1 - 60, u), lerp(y0 + 60, y1 - 60, 1 - u) - 0];
      // the fitted line escapes past the bezel on the last beats
      const ext = clamp((bb - 3) / .8);
      const [ax, ay] = line(-.15), [bx_, by_] = line(1 + ext * .6);
      ctx.save(); ctx.globalCompositeOperation = 'lighter'; ctx.strokeStyle = 'rgb(255 170 80 / .35)'; ctx.lineWidth = 26; ctx.beginPath(); ctx.moveTo(ax, ay); ctx.lineTo(lerp(ax, bx_, clamp(bb / 1.5)), lerp(ay, by_, clamp(bb / 1.5))); ctx.stroke(); ctx.restore();
      ctx.strokeStyle = '#FFB050'; ctx.lineWidth = 7; ctx.beginPath(); ctx.moveTo(ax, ay); ctx.lineTo(lerp(ax, bx_, clamp(bb / 1.5)), lerp(ay, by_, clamp(bb / 1.5))); ctx.stroke();
      for (let j = 0; j < n; j++) {
        const [x, y] = line((j + .5) / 8), age = bb - j / 2, e = backOut(clamp(age / .25), 3);
        fillP(ellPath(x, y, 16 * e, 16 * e), '#FFFFFF'); addGlow(x, y, 50 * e, '#7FD8FF', .8 * (1 - clamp(age)));
      }
      txt('L ∝ C^−α', 1400, 250, 64, '#FFE3B0', { font: 'archivo', alpha: clamp((bb - 2) / .5) });
      // Akari and Clawd pop up in the corner, bobbing on the beat: "OK!!"
      const pk = easeOut(clamp((bb - 2.2) / .4)), bob = pulse(t, 5) * 16;
      cut('card_akari', 1620, H + 330 - pk * 330 + bob, 760, {});
      cut('clawd_jump', 1300, H + 20 - pk * 120 + bob * 1.4, 240, { rot: -.12 });
      popLabel('OK!!', 1330, 640 - bob, 54, clamp((bb - 2.6) / .3), { fill: '#FFE070', rot: .08 });
      cutFlash(bb, .8);
    }
  });

  // ---------- V1.3 "Gwern said 'stack the compute high'": the hooded essayist points up; then the GPU tower into the clouds ----------
  line('V1', 3, (p, lt, d, t, seg) => {
    const b = beatsIn(t, seg), [i, bb] = cuts(b, [-1, 4]);
    if (i === 0) {
      const k = ease(clamp((b - .5) / 3.5));
      still('v1_3_gwern', { x: .5, y: lerp(.5, .42, k), z: lerp(1.05, 1.2, k) });
      nameTag('GWERN', 'pseudonymous essayist', 90, 150, clamp((b - .7) / .5), '#2BB5A8');
      sayBubble('stack the compute high.', 1320, 180, 44, clamp((b - 1.4) / 1.6), 1150, 330);
      if (b < 1) flash(.6 * (1 - clamp((b - .5) / .2)));
    } else {
      // tilt up the tower; every beat the tower thumps (a punch, a shake, a flash of light at the top)
      const k = ease(clamp(bb / 4.8)), h = hit(frac(bb), .35), [sx, sy] = shake(t, 8 * h);
      still('v1_3_tower', { x: .5, y: lerp(.75, .25, k), z: lerp(1.08, 1.22, k) * punch(frac(bb), .025) }, { dx: sx, dy: sy });
      addGlow(W * .5, lerp(420, 140, k), 260, '#7FF0FF', .35 * h + .15);
      sparkleField(t, { n: 10, r: 20, seed: 33, x0: W * .3, x1: W * .7, y0: 0, y1: H * .6, col: '#C8FFFF' });
      cutFlash(bb, .8);
    }
  });

  // ---------- V1.4 "Few-shot learners multiply": Clawd at his desk doing 23×47, in panels that double on the beats ----------
  const ANSWERS = ['1081 ✓', '1071 ✗', '981 ✗', '1081 ✓', '2347 ✗', '1180 ✗', '1091 ✗', '1081 ✓', '1801 ✗', '107 ✗', '1081 ✓', '1018 ✗', '961 ✗', '1981 ✗', '1081 ✓', '1101 ✗'];
  const TINTS = ['#FFD1E0', '#CFE4FA', '#E6DDFA', '#FFE8B8', '#CFF3E3', '#FFD8C2', '#DDEBFF', '#F6D5F5'];
  line('V1', 4, (p, lt, d, t, seg) => {
    const b = beatsIn(t, seg), lvl = clamp(Math.floor(b / 2), 0, 4), n = 1 << lvl, cols = [1, 2, 2, 4, 4][lvl], rows = n / cols;
    const pw = W / cols, ph = H / rows, lb = b - lvl * 2;
    for (let j = 0; j < n; j++) {
      const x = (j % cols) * pw, y = Math.floor(j / cols) * ph;
      still('v1_4_clawd', { x: .5 + (hash2(9, j) - .5) * .1, y: .45, z: 1.05 + .03 * Math.sin(t * 2 + j) }, { rect: [x, y, pw, ph] });
      if (j) { ctx.save(); ctx.globalCompositeOperation = 'multiply'; ctx.globalAlpha = .35; ctx.fillStyle = TINTS[j % TINTS.length]; ctx.fillRect(x, y, pw, ph); ctx.restore(); }
      const ak = clamp((lb - .3 - hash2(5, j) * .8) / .3), ok = ANSWERS[j].endsWith('✓');
      popLabel(ANSWERS[j], x + pw * .72, y + ph * .22, Math.max(22, 56 / Math.sqrt(cols)), ak, { fill: ok ? '#C8F5D8' : '#FFD0D8', col: ok ? '#1E7A45' : '#B02040' });
      ctx.strokeStyle = '#FFFFFF'; ctx.lineWidth = 6; ctx.strokeRect(x, y, pw, ph);
    }
    popLabel('23 × 47 = ?', 330, 110, 44, clamp(b / .3), { fill: '#FFFFFF' });
    if (b > 7.5) {
      const k = clamp((b - 7.5) / .3);
      ctx.save(); ctx.translate(W / 2, H * .47); ctx.rotate(-.05); ctx.scale(backOut(k, 2), backOut(k, 2));
      ctx.fillStyle = 'rgb(40 30 80 / .3)'; ctx.fill(rrPath(-440 + 10, -130 + 14, 880, 260, 40));
      ctx.fillStyle = '#FFE070'; ctx.fill(rrPath(-440, -130, 880, 260, 40)); ctx.strokeStyle = '#2A2350'; ctx.lineWidth = 8; ctx.stroke(rrPath(-440, -130, 880, 260, 40));
      txt('GPT-3 · 175B', 0, -34, 96, '#2A2350', { font: 'rammetto' });
      txt('two-digit multiplication: ~29% right', 0, 70, 34, '#2A2350', { font: 'code' });
      ctx.restore();
    }
    cutFlash(lb, .6, .25);
  });

  // ---------- V1.5 "ChatGPT, overnight": Akari asleep at the chat window at night; smash cut to morning: Ren frozen mid-sip ----------
  const fmt = n => Math.round(n).toLocaleString('en-US');
  function usersCounter(x, y, n, k) {
    popLabel(`users: ${fmt(n)}`, x, y, 46, k, { fill: '#FFFFFF', font: 'archivo' });
  }
  line('V1', 5, (p, lt, d, t, seg) => {
    const b = beatsIn(t, seg), [i, bb] = cuts(b, [0, 3.5]);
    if (i === 0) {
      still('v1_5_asleep', { x: lerp(.45, .6, ease(clamp(bb / 3.5))), y: .5, z: lerp(1.04, 1.18, ease(clamp(bb / 3.5))) });
      grade('#1A2150', .62, 'multiply'); grade('#3A5AC0', .18, 'screen');
      addGlow(W * .62, H * .45, 420, '#9FD4FF', .35 + .05 * Math.sin(t * 7));
      usersCounter(1560, 170, 1, clamp(bb / .3));
      cutFlash(bb, .5);
    } else {
      // morning: a zoom punch on Ren, the counter rolls over like an odometer
      const [sx, sy] = shake(t, 10 * hit(bb, .5));
      still('v1_5_ren', { x: .5, y: .42, z: 1.1 * punch(bb, .12) }, { dx: sx, dy: sy });
      speedLines(W * .5, H * .4, t, { n: 60, r0: 460, a: .3 * hit(bb, 1.2) });
      const r = clamp(bb / 3), n = r < .4 ? lerp(1, 1e6, (r / .4) ** 3) : lerp(1e6, 1e8, ((r - .4) / .6) ** 2);
      usersCounter(1500, 170, n, 1);
      if (r > .35 && r < .5) sparkle(1700, 130, 40, 1);
      flash(1 - clamp(bb / .25), '#FFF6DE');
    }
  });

  // ---------- V1.6 "Sydney's chats gave Roose a fright": a heart-eyed chat pours hearts at the bearded columnist; 5 TURNS MAX ----------
  line('V1', 6, (p, lt, d, t, seg) => {
    const b = beatsIn(t, seg), k = ease(clamp(b / 7)), [sx, sy] = shake(t, 3);
    const v = still('v1_6_sydney', { x: lerp(.5, .56, k), y: .45, z: lerp(1.04, 1.16, k) }, { dx: sx, dy: sy });
    // the hearts rise off the chat face on the screen and drift across to his face
    const [hx, hy] = v.pt(.3, .56), [fx, fy] = v.pt(.6, .4);
    heartStream(t, hx, hy, { n: 26, spread: 160, dx: fx - hx - 40, rise: hy - fy + 60 });
    nameTag('KEVIN', 'tech columnist', 90, 150, clamp((b - .4) / .5), '#FF6FA0');
    const [lx, ly] = v.pt(.3, .36);
    sayBubble('…leave your wife? ♥', 760, 150, 42, clamp((b - 1.6) / 1.4), lx, ly, { col: '#D02070' });
    // the stamp lands on the chat face, not on him
    const [cx, cy] = v.pt(.27, .52);
    stampMark('5 TURNS MAX', Math.max(cx, 380), cy, 76, clamp((b - 4.5) / 1.2));
    cutFlash(b, .6);
  });

  // ---------- V1.7 "Six-month pause went nowhere fast": Kiri presses PAUSE; the days and months whip past anyway ----------
  const MONTHS = ['APR', 'MAY', 'JUN', 'JUL', 'AUG', 'SEP'];
  line('V1', 7, (p, lt, d, t, seg) => {
    const b = beatsIn(t, seg), [i, bb] = cuts(b, [0, 3.5]);
    if (i === 0) {
      const pr = hit(bb - 1, .5);
      still('v1_7_kiri', { x: .5, y: .45, z: 1.06 * (1 + .05 * pr) });
      speedLines(W * .45, H * .6, t, { n: 50, r0: 420, a: .35 * pr });
      popLabel('⏸ PAUSE', 420, 180, 70, clamp((bb - 1) / .3), { fill: '#FFE070' });
      cutFlash(bb, .6);
    } else {
      // a time-lapse: the sky cycles day → dusk → night on every beat, the calendar tears off a month on every half beat
      still('v1_7_city', { x: .5, y: .55, z: 1.05 });
      const ph = frac(bb), day = .5 + .5 * Math.cos(ph * TAU);
      grade('#0C1234', (1 - day) * .85, 'multiply'); grade('#FF9A6A', Math.sin(ph * TAU * 2) ** 2 * .25 * (1 - day), 'screen');
      // city lights come on at night
      if (day < .45) for (let j = 0; j < 60; j++) { ctx.fillStyle = alpha(j % 3 ? '#FFE9A0' : '#FFFFFF', (.45 - day) * 2 * hash2(81, j)); ctx.fillRect(hash2(82, j) * W, H * (.62 + hash2(83, j) * .18), 5, 4); }
      const sa = ph * TAU - Math.PI / 2, [cx_, cy_] = [W / 2 + Math.cos(sa) * 900, H * .75 + Math.sin(sa) * 700];
      addGlow(cx_, cy_, 160, day > .5 ? '#FFF2C0' : '#CFE0FF', .9); fillP(ellPath(cx_, cy_, 50, 50), day > .5 ? '#FFF8E0' : '#E8F0FF');
      speedBars(t, { n: 30, a: .25, speed: 5000 });
      const m = clamp(Math.floor(bb * 2), 0, MONTHS.length - 1), mk = frac(bb * 2);
      ctx.save(); ctx.translate(1560, 300); ctx.rotate(.04);
      ctx.fillStyle = 'rgb(30 20 60 / .3)'; ctx.fillRect(-150 + 10, -150 + 12, 300, 300);
      ctx.fillStyle = '#FFFFFF'; ctx.fillRect(-150, -150, 300, 300); ctx.fillStyle = '#F04E4E'; ctx.fillRect(-150, -150, 300, 80);
      txt('2023', 0, -110, 40, '#FFFFFF', { font: 'archivo' }); txt(MONTHS[Math.min(m + 1, MONTHS.length - 1)], 0, 40, 110, '#2A2350', { font: 'rammetto' });
      if (m < MONTHS.length - 1) { ctx.save(); ctx.globalAlpha = 1 - mk; ctx.translate(mk * 300, -mk * 200); ctx.rotate(mk * 1.2); ctx.fillStyle = '#FFFFFF'; ctx.fillRect(-150, -70, 300, 220); txt(MONTHS[m], 0, 40, 110, '#2A2350', { font: 'rammetto' }); ctx.restore(); }
      ctx.restore();
      popLabel('⏸ ???', 420, 180, 60, clamp(bb / .3), { fill: '#FFFFFF', rot: -.06 });
      cutFlash(bb, .8);
    }
  });

  // ---------- V1.8 "Eliezer's 'shut-it-down' blast": the fedora extra's shout; an impact frame blows Akari and Clawd back ----------
  line('V1', 8, (p, lt, d, t, seg) => {
    const b = beatsIn(t, seg), [i, bb] = cuts(b, [-1, 3.5]);
    if (i === 0) {
      const h = hit(b - 2, .6), [sx, sy] = shake(t, 14 * h);
      still('v1_8_eliezer', { x: .5, y: .45, z: 1.06 * punch(b - 2, .08) }, { dx: sx, dy: sy });
      speedLines(W * .5, H * .4, t, { n: 80, r0: 380, a: .5 * h });
      nameTag('ELIEZER', 'decision theorist', 90, 150, clamp((b - .7) / .5), '#F04E4E');
      if (b < 1) flash(.6 * (1 - clamp((b - .5) / .2)));
    } else {
      const [sx, sy] = shake(t, 22 * hit(bb, 1.2) + 4);
      still('v1_8_blown', { x: .5, y: .45, z: 1.1 }, { dx: sx, dy: sy });
      speedBars(t, { n: 50, a: .5, speed: 6000 });
      impactFrame(bb < .25 ? 1 : 0);
      zoomBlur(hit(bb, .8));
    }
  });

  // ---------- V1.9 "Sam got fired, then rehired": out the revolving door, back in, on the beats; the cast watches, heads turning ----------
  line('V1', 9, (p, lt, d, t, seg) => {
    const b = beatsIn(t, seg), [i, bb] = cuts(b, [0, 4]);
    if (i === 0) {
      const beat = Math.floor(bb), fb = frac(bb), out = beat % 2 === 0;
      still('v1_9_sam', { x: .5, y: .48, z: 1.08, r: (1 - easeOut(clamp(fb / .3))) * (out ? .25 : -.25) }, { flip: !out });
      nameTag('SAM', 'OpenAI CEO', 90, 150, clamp(bb / .4), '#8A6BD8');
      flash(.5 * (1 - clamp(fb / .2)), out ? '#FFD0D8' : '#D0FFE0');
    } else {
      // the bench: the still mirrors on every beat, so their heads snap left, right, left
      const beat = Math.floor(bb);
      still('v1_9_bench', { x: .5, y: .5, z: 1.06 }, { flip: beat % 2 === 1 });
      cutFlash(frac(bb), .25, .2);
    }
  });

  // ---------- V1.10 "Weekend chaos, board expired": Akari drowning in buzzing phones; then the empty boardroom: EXPIRED ----------
  line('V1', 10, (p, lt, d, t, seg) => {
    const b = beatsIn(t, seg), [i, bb] = cuts(b, [-1, 4]);
    if (i === 0) {
      const [sx, sy] = shake(t, 6);
      still('v1_10_chaos', { x: .5, y: .48, z: 1.08 }, { dx: sx, dy: sy });
      for (let j = 0; j < 4; j++) { const on = frac(b * 2 + j * .25) < .5; popLabel(['BZZT', 'bzzt!', 'BZZ', 'ping!'][j], [300, 1600, 380, 1500][j], [260, 300, 760, 720][j], 40, on ? 1 : 0, { fill: '#FFFFFF', rot: (j % 2 ? .1 : -.1) }); }
      popLabel('FRI → SAT → SUN → MON', W / 2, 110, 40, clamp((b - .5) / .3), { fill: '#FFE070' });
      if (b < 1) flash(.6 * (1 - clamp((b - .5) / .2)));
    } else {
      const k = ease(clamp(bb / 3.5));
      still('v1_10_board', { x: .5, y: .5, z: lerp(1.02, 1.14, k) });
      grade('#FFB070', .15, 'soft-light');
      stampMark('EXPIRED', W * .5, H * .45, 130, clamp((bb - 1) / 1.1), { rot: -.16 });
      cutFlash(bb, .7);
    }
  });

  // ---------- V1.11 "Ilya saw what Ilya saw": he stares into a glowing blank board, lit by it; the cast stacked in a doorway, trying to see ----------
  line('V1', 11, (p, lt, d, t, seg) => {
    const b = beatsIn(t, seg), [i, bb] = cuts(b, [-1, 5]);
    if (i === 0) {
      // a slow push in on his face; the board breathes, and what he sees glints in his eyes
      const k = ease(clamp((b - .5) / 4.5));
      const v = still('v1_11_ilya', { x: lerp(.5, .45, k), y: lerp(.45, .4, k), z: lerp(1.02, 1.22, k) });
      const [gx, gy] = v.pt(.82, .45);
      addGlow(gx, gy, 520, '#FFF4D0', .25 + .1 * Math.sin(t * 3));
      sparkleField(t, { n: 16, r: 22, seed: 44, x0: W * .45, col: '#FFF4C0' });
      const gk = Math.sin(clamp((b - 1.5) / 2) * Math.PI);
      for (const [u, w] of [[.372, .345], [.418, .355]]) { const [ex, ey] = v.pt(u, w); glint(ex, ey, 9 * v.s, gk); }
      nameTag('ILYA', 'OpenAI chief scientist', 90, 150, clamp((b - .7) / .5), '#C8A040');
      if (b < 1) flash(.6 * (1 - clamp((b - .5) / .2)));
    } else {
      // the stack fills the still top to bottom, so shrink it a little and let the wall colour run under the subtitle
      const k = ease(clamp(bb / 4.5)), z = lerp(.9, .95, k);
      ctx.fillStyle = '#F4EEEA'; ctx.fillRect(0, 0, W, H);
      still('v1_11_peek', { x: .45, y: .5, z }, { free: true, dy: -(H - 864 * 1.25 * z) / 2 });
      for (let j = 0; j < 3; j++) popLabel('?', 1500 + j * 70, 260 + j * 60, 60, clamp((bb - 1.2 - j * .35) / .25), { fill: '#FFFFFF', rot: (j - 1) * .2 });
      cutFlash(bb, .6);
    }
  });

  // ---------- V1.12 "EU writes the AI law": the rulebook slams onto the club table, dust, bounce; ADOPTED 523–46 ----------
  line('V1', 12, (p, lt, d, t, seg) => {
    const b = beatsIn(t, seg), land = b - 1, drop = clamp((b - .5) / .5);
    const h = hit(land, .7), [sx, sy] = shake(t, 20 * h);
    still('v1_12_book', { x: .5, y: .5, z: 1.06 * punch(land, .05) }, { dx: sx, dy: sy + (drop < 1 ? -(1 - easeIn(drop)) * 60 : 0) });
    if (drop < 1) flash(.35 * (1 - drop), '#FFFFFF');
    if (land > 0 && land < 1.5) {
      for (let j = 0; j < 14; j++) { const a = Math.PI + (j / 13) * Math.PI, r = 200 + easeOut(land / 1.5) * 500; ctx.save(); ctx.globalAlpha = .5 * (1 - land / 1.5); blob(W / 2 + Math.cos(a) * r, H * .7 + Math.sin(a) * r * .25, 90, 60, '#F4EEE4', 1); ctx.restore(); }
    }
    stampMark('ADOPTED', W * .5, H * .5, 120, clamp((b - 4.5) / 1.2), { sub: '523 – 46', col: '#2856C8', rot: -.1 });
    cutFlash(b, .5);
  });

  // ---------- V1.13 "Strawberry thinks, link by link": Akari and the strawberry ponder; a chain of thought grows a link a beat → o1 ----------
  const LINKS = ['think', 'check', 'think again', 'answer!'];
  line('V1', 13, (p, lt, d, t, seg) => {
    const b = beatsIn(t, seg), k = ease(clamp(b / 8));
    const v = still('v1_13_strawberry', { x: .5, y: lerp(.5, .44, k), z: lerp(1.04, 1.12, k) });
    // the chain climbs from her chin up the gap between the two thinkers, the way her eyes look
    const pts = [[.47, .56], [.5, .43], [.49, .3], [.51, .16]].map(([u, w]) => v.pt(u, w));
    for (let j = 0; j < LINKS.length; j++) {
      const lk = clamp((b - .8 - j * 1.4) / .35);
      if (j && lk > 0) glowPath([pts[j - 1], pts[j]], clamp(lk * 1.5), { col: '#FF7FA8', w: 8 });
      popLabel(LINKS[j], pts[j][0], pts[j][1], 40, lk, { fill: j === 3 ? '#FFE070' : '#FFFFFF' });
    }
    const bulb = clamp((b - 6.6) / .3);
    if (bulb > 0) { addGlow(220, 200, 300, '#FFF0A0', .8 * bulb); popLabel('o1', 220, 200, 110, bulb, { fill: '#FFF7C8', font: 'rammetto' }); }
    cutFlash(b, .6);
  });

  // ---------- V1.14 "Newsom vetoes, doesn't blink": a staring contest, his eyes over hers; she blinks first; VETO ----------
  line('V1', 14, (p, lt, d, t, seg) => {
    const b = beatsIn(t, seg), tension = clamp((b - .5) / 4.5), [sx, sy] = shake(t, 2 + 8 * tension);
    still('v1_14_gavin', { x: .5, y: .45, z: 1.15 + tension * .1 }, { rect: [0, 0, W, H2], dx: sx, dy: sy });
    const blink = b > 5 && b < 5.35, after = b >= 5.35;
    still('intro_eyes', { x: .5, y: .6, z: 1.25 + tension * .1 }, { rect: [0, H2, W, H2], dx: -sx, dy: -sy, patches: blink ? ['intro_eyes.closed'] : after ? ['intro_eyes.half'] : [] });
    ctx.fillStyle = '#FFFFFF'; ctx.fillRect(0, H2 - 5, W, 10);
    nameTag('GAVIN', 'governor', 90, 130, clamp((b - .7) / .5), '#3D7BE0');
    stampMark('VETO', W * .5, H * .5, 150, clamp((b - 5.5) / 1.1), { sub: 'SB 1047', rot: -.12 });
    cutFlash(b, .6);
  });

  // ---------- V1.15 "Hinton takes his medal, scolds": the white-haired laureate wags a finger under confetti; the cast snaps to attention ----------
  line('V1', 15, (p, lt, d, t, seg) => {
    const b = beatsIn(t, seg), [i, bb] = cuts(b, [0, 5]);
    if (i === 0) {
      const k = ease(clamp(bb / 5)), wag = Math.sin(t * 16) * .006;
      const v = still('v1_15_geoff', { x: .5, y: lerp(.5, .42, k), z: lerp(1.04, 1.16, k), r: wag });
      confetti(t, { n: 60, seed: 15 });
      nameTag('GEOFF', 'Nobel laureate, physics', 90, 150, clamp((bb - .4) / .5), '#C8A040');
      const [mx, my] = v.pt(.62, .6);
      sayBubble('be careful!', 1530, 300, 56, clamp((bb - 2.2) / .9), mx, my);
      cutFlash(bb, .6);
    } else {
      still('v1_15_salute', { x: .5, y: .45, z: 1.06 * punch(bb, .08) });
      speedLines(W * .5, H * .45, t, { n: 60, r0: 520, a: .25 * hit(bb, 1) });
      cutFlash(bb, .8);
    }
  });

  // ---------- V1.16 "Demis wins for protein folds": the grinning laureate and his glowing protein; the cast's freeze-frame cheer ----------
  line('V1', 16, (p, lt, d, t, seg) => {
    const b = beatsIn(t, seg), [i, bb] = cuts(b, [-1, 6]);
    if (i === 0) {
      const k = ease(clamp((b - .5) / 5.5));
      const v = still('v1_16_demis', { x: lerp(.5, .52, k), y: lerp(.45, .4, k), z: lerp(1.04, 1.18, k) });
      // the folded protein glows and twinkles in his hands
      const [px, py] = v.pt(.27, .4);
      addGlow(px, py, 300, '#B8E0FF', .3 + .15 * Math.sin(t * 4));
      sparkleField(t, { n: 14, r: 24, seed: 16, x0: px - 300, x1: px + 300, y0: py - 260, y1: py + 240 });
      confetti(t, { n: 50, seed: 16 });
      nameTag('DEMIS', 'Nobel laureate, chemistry', 90, 150, clamp((b - .7) / .5), '#2BB5A8');
      if (b < 1) flash(.6 * (1 - clamp((b - .5) / .2)));
    } else {
      // the cheer: a quick push, then a freeze frame with a flare, and the white-out into the chorus
      const frz = bb > 3, k = frz ? 1 : easeOut(clamp(bb / 3));
      still('v1_16_cheer', { x: .5, y: .45, z: lerp(1.0, 1.1, k) });
      const tf = frz ? t - (bb - 3) * beatLen() : t;   // the freeze stops the confetti and petals too
      confetti(tf, { n: 60, seed: 17 });
      petals(tf, { n: 20, seed: 18, s: 1.6, depth: true });
      if (frz) { flare(1500, 160, .8); grade('#FFF4E0', .12, 'screen'); }
      cutFlash(bb, .8);
      if (bb > 4.4) flash((bb - 4.4) / .6);
    }
  });
})();

;
// ---- styles/anime/ch/c03_chorus1.js ----
// c03_chorus1.js: Chorus 1, the rooftop at noon (≈ 36 beats): the door bursts open, the run along the glowing scaling curve,
// the curve launching into the sky, the four-way split of faces, and the cast looking up as it bursts out of the frame.
// b = beats from the window start (it starts at about 0); the chorus lines start near b 0, 5.5, 22 and 27, with "and the curves
// kept gaining" at about 16.5 and "can't" at 32.5.
(() => {
  // the scaling curve: a glowing power-law path in screen space, drawn up to its tip at fraction k (0..1)
  function curve(pts, k, o = {}) {
    if (k <= 0 || pts.length < 2) return pts[0];
    const n = Math.max(2, Math.ceil(pts.length * clamp(k))), P = pts.slice(0, n);
    const path = new Path2D(); path.moveTo(P[0][0], P[0][1]); for (const q of P.slice(1)) path.lineTo(q[0], q[1]);
    ctx.save(); ctx.lineCap = 'round'; ctx.lineJoin = 'round';
    ctx.globalCompositeOperation = 'lighter';
    ctx.strokeStyle = alpha(o.col ?? '#FFB050', .22); ctx.lineWidth = (o.w ?? 16) * 5; ctx.stroke(path);
    ctx.strokeStyle = alpha(o.col ?? '#FFB050', .45); ctx.lineWidth = (o.w ?? 16) * 2; ctx.stroke(path);
    ctx.globalCompositeOperation = 'source-over';
    ctx.strokeStyle = o.col ?? '#FFB050'; ctx.lineWidth = o.w ?? 16; ctx.stroke(path);
    ctx.strokeStyle = '#FFFFFF'; ctx.lineWidth = (o.w ?? 16) * .45; ctx.stroke(path);
    ctx.restore();
    const tip = P[P.length - 1];
    addGlow(tip[0], tip[1], 90, '#FFE0A0', .9); sparkle(tip[0], tip[1], 46, 1);
    return tip;
  }
  // points of y = a·x^p across the frame, as a world strip that scrolls left by `scroll` px
  const curvePts = (scroll, x0, y0, x1, y1, pw = 2.2, n = 60) => Array.from({ length: n + 1 }, (_, i) => { const u = i / n; return [lerp(x0, x1, u) - scroll, lerp(y0, y1, u ** pw)]; });
  const onCurve = (pts, x) => { for (let i = 1; i < pts.length; i++) if (pts[i][0] >= x) { const [a, b] = [pts[i - 1], pts[i]], f = (x - a[0]) / (b[0] - a[0]); return [lerp(a[1], b[1], f), Math.atan2(b[1] - a[1], b[0] - a[0])]; } return [pts[pts.length - 1][1], 0]; };

  // ---------- the run cycle (as in C3 and C4) ----------
  // each runner is its run cut-out plus two repainted drawings of it (c4_run_*: the passing position, and the flight between
  // strides), shown a third of a beat each, so one stride a beat; LIFT is how far the body rises in each drawing (fractions of h)
  const RUN = {
    akari: { base: 'run_akari', frames: ['run_akari', 'c4_run_akari.pass2', 'c4_run_akari.air2'] },
    ren: { base: 'run_ren', frames: ['run_ren', 'c4_run_ren.pass2', 'c4_run_ren.air2'], flip: true },   // Anima drew him running left
    kiri: { base: 'run_kiri', frames: ['run_kiri', 'c4_run_kiri.pass', 'c4_run_kiri.air'] },
  };
  const LIFT = [0, -.035, .05];
  // draw drawing `name` of cut-out `base` exactly where cut(base, …) would draw the base (a frame carries its crop offset);
  // pt(u, v) takes the base's fractions
  function frameCut(base, name, x, y, h, o = {}) {
    const B = STILLS[base], F = STILLS[name];
    if (name === base || !F || !IMGS[name]) return cut(base, x, y, h, o);
    const [au, av] = o.anchor ?? [.5, 1], fu = u => (u * B.w - F.ox) / F.w, fv = v => (v * B.h - F.oy) / F.h;
    const c = cut(name, x, y, h * F.h / B.h, { ...o, anchor: [fu(au), fv(av)] });
    return { s: c.s, pt: (u, v) => c.pt(fu(u), fv(v)) };
  }
  // a runner at (x, y) (the feet), h px tall, leaning by rot; bt = beats into the stride. Speed lines stream off its back.
  function runner(who, x, y, h, bt, o = {}) {
    const R = RUN[who], n = R.frames.length, f = ((Math.floor(bt * n) % n) + n) % n, rot = o.rot ?? 0;
    const up = k => [x + Math.sin(rot) * k * h, y - Math.cos(rot) * k * h];
    const opt = { rot, flip: R.flip, shadow: false, tint: o.tint, tintA: o.tintA };
    // the streaks behind: short white dashes flying off the back of the body
    if (o.lines !== false) {
      ctx.save(); ctx.translate(x, y); ctx.rotate(rot); ctx.strokeStyle = o.lineCol ?? 'rgb(255 255 255 / .75)'; ctx.lineCap = 'round';
      for (let j = 0; j < 7; j++) {
        const ph = frac(bt * 1.7 + hash2(j, 3)), ly = -h * (.18 + .7 * hash2(j, 4)), lx = -h * (.2 + ph * .9), len = h * (.18 + .2 * hash2(j, 5));
        ctx.globalAlpha = (1 - ph) * .8; ctx.lineWidth = 3 + 4 * hash2(j, 6); ctx.beginPath(); ctx.moveTo(lx, ly); ctx.lineTo(lx - len, ly); ctx.stroke();
      }
      ctx.restore();
    }
    const [px, py] = up(LIFT[f]);
    return frameCut(R.base, R.frames[f], px, py, h, opt);
  }

  const FACES = [
    { cut: 'card_akari', c1: '#FFD1E0', c2: '#FF8FB8', face: [.42, .19] },
    { cut: 'card_ren', c1: '#CFE4FA', c2: '#5E86D8', face: [.45, .14] },
    { cut: 'card_kiri', c1: '#E6DDFA', c2: '#9F86E0', face: [.5, .29] },
    { cut: 'clawd_jump', c1: '#FFE4CC', c2: '#FF9E6A', face: [.5, .45] },
  ];

  section('C1', (p, lt, d, t, seg) => {
    const b = beatsIn(t, seg);
    // ---------- "We didn't start the scaling": the rooftop door bursts open, the cast runs out into the noon sun in slow motion ----------
    if (b < 5.5) {
      const k = ease(clamp((b - .5) / 5));
      still('c1_door', { x: .5, y: lerp(.5, .42, k), z: lerp(1.02, 1.16, k) });
      rays(W * .5, H * .1, { t, a: .25, n: 9, ang: Math.PI / 2, spread: 2.2, len: 1600 });
      petals(t * .5, { n: 50, seed: 31, s: 2, depth: true, wind: 300, fall: 50 });
      flare(W * .52, H * .22, .7);
      flash(1 - clamp((b - .5) / .4));
      return;
    }
    // ---------- "It was always training": the three run along the glowing curve across the sky ----------
    if (b < 16) {
      // the curve scrolls left under them and steepens as it goes; the camera climbs with them (the sky slides down behind)
      const bb = b - 5.5, scroll = bb * 180;
      const raw = curvePts(scroll, -300, H * 1.1, W * 2.4, -H * .8, 2), lift = 660 - onCurve(raw, 1300)[0];
      const pts = raw.map(([x, y]) => [x, y + lift]);
      still('intro_sky', { x: .3 + clamp(bb / 10.5) * .4, y: clamp(.62 - lift / 2600, .05, .95), z: 1.3 });
      speedBars(t, { n: 36, a: .35, speed: 3200 });
      curve(pts, 1);
      // the three run in step with the beat (each a third of a stride apart), a new drawing every third of a beat
      const onRun = (who, x, h, ph) => { const [y, a] = onCurve(pts, x); return runner(who, x, y + 8, h, b + ph, { rot: a * .6 }); };
      onRun('kiri', 470, 480, .67);
      onRun('ren', 880, 500, .33);
      const ak = onRun('akari', 1300, 490, 0);
      const [hx, hy] = ak.pt(.78, .04);
      cut('clawd_jump', hx, hy + 40, 130, { rot: -.1 + .1 * Math.sin(b * Math.PI) });
      petals(t, { n: 24, seed: 32, s: 1.6, depth: true, wind: -900, fall: 40 });
      cutFlash(bb, .8);
      return;
    }
    // ---------- "And the curves kept gaining": the curve launches straight up the sky, Clawd riding its tip ----------
    if (b < 21.5) {
      const bb = b - 16, k = ease(clamp(bb / 5.5));
      still('intro_sky', { x: .5, y: lerp(.75, .1, k), z: 1.15 });
      const tipY = lerp(H * .7, -200, easeIn(clamp(bb / 5.5)));
      const pts = Array.from({ length: 40 }, (_, i) => { const u = i / 39; return [lerp(-100, W * .62, u ** .5), lerp(H + 150, tipY, u)]; });
      const tip = curve(pts, 1, { w: 20 });
      cut('clawd_jump', tip[0], tip[1] + 40, 200, { rot: .15 * Math.sin(t * 8) });
      speedBars(t, { n: 30, a: .3, speed: 4000, ang: -Math.PI / 2 });
      sparkleField(t, { n: 14, r: 24, seed: 34 });
      cutFlash(bb, .8);
      return;
    }
    // ---------- "We didn't start the scaling": the four-way split of faces, a panel every beat and a half, each with its colour flash ----------
    if (b < 27) {
      // the panels share the width, so the first face gets the whole frame
      hideStamp();   // the date card would sit on Kiri's hairpin
      const STEP = 1.5, bb = b - 21.5, shown = clamp(Math.floor(bb / STEP) + 1, 1, 4), pw = W / shown;
      for (let j = 0; j < shown; j++) {
        const F = FACES[j], x = j * pw, age = bb - j * STEP, slide = easeOut(clamp(age / .4));
        ctx.save(); ctx.beginPath(); ctx.rect(x, 0, pw, H); ctx.clip();
        diagSplit(F.c1, F.c2, t, { x: x + pw * .6, a: .25, speed: 200 });
        // cut-outs are ~900 px tall, so keep them under ~1.5× (h 1350) or the line art goes soft
        const h = j === 3 ? 330 : 1350, push = 1 + clamp(bb / 5.5) * .06, bobY = j === 3 ? -Math.abs(Math.sin(b * Math.PI)) * 40 : 0;
        cut(F.cut, x + pw / 2 + (1 - slide) * pw * (j % 2 ? 1 : -1), (j === 3 ? H * .52 : 400) + bobY, h * push, { anchor: F.face });
        // the new panel opens with a flash of its own colour
        ctx.globalAlpha = .8 * (1 - clamp(age / .3)); ctx.fillStyle = '#FFFFFF'; ctx.fillRect(x, 0, pw, H); ctx.globalAlpha = 1;
        ctx.restore();
      }
      ctx.fillStyle = '#FFFFFF'; for (let j = 1; j < shown; j++) ctx.fillRect(j * pw - 5, 0, 10, H);
      return;
    }
    // ---------- "No, we didn't preordain it, but we can't contain it!": the cast looks up as the curve bursts out of the top; freeze, white ----------
    // the freeze lands a beat after "can't", and the white-out fills the last beat before V2
    const FRZ = 6.5, bb = b - 27, frz = bb > FRZ, bf = frz ? FRZ : bb, k = ease(clamp(bf / FRZ));
    still('c1_lookup', { x: .5, y: lerp(.55, .42, k), z: lerp(1.02, 1.14, k) * (frz ? 1.02 : 1) });
    const sweep = clamp((bf - .5) / 2.5), pts = Array.from({ length: 30 }, (_, i) => { const u = i / 29; return [lerp(-100, W * .78, u), lerp(H * .42, -260, u ** 2.2)]; });
    curve(pts, sweep, { w: 22 });
    const tf = frz ? t - (bb - FRZ) * beatLen() : t;
    petals(tf, { n: 30, seed: 35, s: 1.8, depth: true, wind: 200 });
    if (frz) { grade('#FFF2E0', .1, 'screen'); flare(W * .78, 60, .8); }
    cutFlash(bb, .8);
    if (bb > FRZ + 1.6) flash((bb - FRZ - 1.6) / .8);
  });
})();

;
// ---- styles/anime/ch/c04_v2.js ----
// c04_v2.js: Verse 2 (summer, JAN → NOV 2025): sixteen lines, one gag each, painted with generated stills (shots/c04_v2.json).
// The dates run winter to autumn, but the art is the club's summer: saturated blue skies, cumulus, cold drinks, the beach.
// Each line is staged in beats from its window start (b = beatsIn(t, seg), about 0 → 8.5); most lines cut once, near beat 4.
(() => {
  // ---------- private helpers ----------
  // the flash that opens a line: timed from the window's actual start (the sung word), whether that falls on a beat or between
  const startFlash = (t, seg, k = .7) => flash(k * (1 - clamp((t - seg.start) / (beatLen() * .3))));
  // a smoke puff ("poof!") that blooms and fades over k 0 → 1
  function puff(x, y, r, k, label) {
    if (k <= 0 || k >= 1) return;
    const e = easeOut(k);
    ctx.save(); ctx.globalAlpha *= 1 - k * k;
    for (let i = 0; i < 9; i++) { const a = i / 9 * TAU + .3, rr = r * (.35 + .55 * e); fillP(ellPath(x + Math.cos(a) * rr, y + Math.sin(a) * rr * .7, r * (.35 + .25 * hash2(i, 7)) * (.6 + .4 * e), r * (.3 + .2 * hash2(i, 8)) * (.6 + .4 * e)), i % 2 ? '#FFFFFF' : '#EDEAF6'); }
    fillP(ellPath(x, y, r * .55 * (.6 + .4 * e), r * .45 * (.6 + .4 * e)), '#FFFFFF');
    ctx.restore();
    if (label) popLabel(label, x, y - r * .1, r * .32, clamp(k * 5) * (1 - clamp((k - .75) / .25)), { fill: '#FFFFFF', rot: -.08 });
  }
  // an anime sweat drop (a teardrop with a highlight), s = its height in px
  function sweatDrop(x, y, s, rot = .3) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot); ctx.scale(s / 100, s / 100);
    const p = new Path2D(); p.moveTo(0, -50); p.bezierCurveTo(22, -12, 36, 12, 36, 26); p.arc(0, 26, 36, 0, Math.PI); p.bezierCurveTo(-36, 12, -22, -12, 0, -50); p.closePath();
    ctx.fillStyle = '#BFE6FF'; ctx.fill(p); ctx.lineWidth = 5; ctx.strokeStyle = '#3F7FC8'; ctx.stroke(p);
    fillP(ellPath(-12, 22, 8, 14, .3), '#FFFFFF');
    ctx.restore();
  }
  // rain: slanted streaks falling fast (pure: each streak's position comes from t)
  function rain(t, o = {}) {
    const n = o.n ?? 120, a = o.a ?? .5, ang = o.ang ?? .18, sp = o.speed ?? 2600;
    ctx.save(); ctx.globalAlpha *= a; ctx.strokeStyle = o.col ?? '#E8F2FF'; ctx.lineCap = 'round';
    for (let i = 0; i < n; i++) {
      const L = 40 + hash2(91, i) * 70, y = frac(t * sp * (.8 + hash2(92, i) * .4) / (H + 200) + hash2(93, i)) * (H + 200) - 100, x = hash2(94, i) * (W + 300) - 150 - y * ang;
      ctx.lineWidth = 1.5 + hash2(95, i) * 2; ctx.beginPath(); ctx.moveTo(x, y); ctx.lineTo(x - L * ang, y + L); ctx.stroke();
    }
    ctx.restore();
  }
  // a digital glitch: horizontal slices of the frame shifted sideways, plus RGB-split bars (a few frames on each beat)
  function glitch(t, k) {
    if (k <= 0) return;
    const f = Math.floor(t * 24);
    ctx.save(); ctx.setTransform(1, 0, 0, 1, 0, 0);
    for (let i = 0; i < 9; i++) {
      const y = hash2(f, i) * canvas.height, h = (8 + hash2(f, i + 20) * 70) * RS, dx = (hash2(f, i + 40) - .5) * 160 * RS * k;
      ctx.drawImage(canvas, 0, y, canvas.width, h, dx, y, canvas.width, h);
    }
    ctx.globalCompositeOperation = 'screen';
    for (let i = 0; i < 4; i++) { ctx.fillStyle = ['rgb(255 0 60 / .35)', 'rgb(0 220 255 / .3)'][i % 2]; ctx.globalAlpha = k; ctx.fillRect(0, hash2(f, i + 60) * canvas.height, canvas.width, (4 + hash2(f, i + 70) * 18) * RS); }
    ctx.restore();
  }
  // a sticky price tag (a pentagon tag with a hole and a string), swinging from its hole at (x, y)
  function priceTag(str, x, y, size, k, rot, sub) {
    if (k <= 0) return;
    const e = backOut(clamp(k), 2.4), tw = textW(str, size, 'rammetto'), w = tw + size * 1.4, h = size * (sub ? 2.1 : 1.6);
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot); ctx.scale(e, e);
    const p = new Path2D(); p.moveTo(0, 0); p.lineTo(h * .45, -h / 2); p.lineTo(w, -h / 2); p.lineTo(w, h / 2); p.lineTo(h * .45, h / 2); p.closePath();
    ctx.fillStyle = 'rgb(40 30 80 / .28)'; ctx.translate(8, 10); ctx.fill(p); ctx.translate(-8, -10);
    ctx.fillStyle = '#FFE070'; ctx.fill(p); ctx.lineWidth = 6; ctx.strokeStyle = '#2A2350'; ctx.lineJoin = 'round'; ctx.stroke(p);
    fillP(ellPath(h * .38, 0, size * .16, size * .16), '#FFFFFF'); ctx.lineWidth = 4; ctx.stroke(ellPath(h * .38, 0, size * .16, size * .16));
    txt(str, h * .45 + (w - h * .45) / 2, sub ? -size * .25 : 2, size, '#2A2350', { font: 'rammetto' });
    if (sub) txt(sub, h * .45 + (w - h * .45) / 2, size * .55, size * .34, '#5A4E86', { font: 'code' });
    ctx.restore();
  }
  // a stock chart panel whose line climbs, then nosedives off the bottom as k goes 0 → 1
  function chartDive(x, y, w, h, k, t) {
    ctx.save(); ctx.translate(x, y);
    ctx.fillStyle = 'rgb(14 19 48 / .88)'; ctx.fill(rrPath(0, 0, w, h, 24)); ctx.strokeStyle = '#FFFFFF'; ctx.lineWidth = 5; ctx.stroke(rrPath(0, 0, w, h, 24));
    ctx.beginPath(); ctx.rect(0, 0, w, h); ctx.clip();
    ctx.strokeStyle = 'rgb(120 150 255 / .18)'; ctx.lineWidth = 2;
    for (let i = 1; i < 6; i++) { ctx.beginPath(); ctx.moveTo(0, h * i / 6); ctx.lineTo(w, h * i / 6); ctx.stroke(); }
    const pts = [];
    for (let i = 0; i <= 60; i++) {
      const u = i / 60, up = h * .72 - u * h * .45 + Math.sin(i * 1.7) * 10, dive = u > .62 ? ((u - .62) / .38) ** 1.6 * h * 1.3 : 0;
      pts.push([30 + u * (w - 60), up + dive]);
    }
    const n = Math.max(2, Math.ceil(pts.length * clamp(k)));
    const col = k > .62 ? '#FF4D6A' : '#6FF0A0';
    ctx.lineJoin = 'round'; ctx.lineCap = 'round';
    ctx.strokeStyle = alpha(col, .35); ctx.lineWidth = 22; ctx.beginPath(); pts.slice(0, n).forEach(([px, py], i) => i ? ctx.lineTo(px, py) : ctx.moveTo(px, py)); ctx.stroke();
    ctx.strokeStyle = col; ctx.lineWidth = 8; ctx.stroke();
    ctx.restore();
  }
  // a code-diff panel scrolling like a slot machine: green + lines and red − lines rushing upward
  function diffTower(x, y, w, h, scroll) {
    ctx.save(); ctx.translate(x, y);
    ctx.fillStyle = 'rgb(20 24 40 / .9)'; ctx.fill(rrPath(0, 0, w, h, 20)); ctx.strokeStyle = '#FFFFFF'; ctx.lineWidth = 5; ctx.stroke(rrPath(0, 0, w, h, 20));
    ctx.beginPath(); ctx.rect(8, 8, w - 16, h - 16); ctx.clip();
    const lh = 30, first = Math.floor(scroll / lh);
    for (let i = first; i < first + h / lh + 2; i++) {
      const yy = i * lh - scroll + 10, kind = hash2(61, i), plus = kind > .45, len = .3 + hash2(62, i) * .6, ind = Math.floor(hash2(63, i) * 3) * 22;
      ctx.fillStyle = plus ? 'rgb(60 200 120 / .22)' : 'rgb(230 70 90 / .22)'; ctx.fillRect(8, yy, w - 16, lh - 4);
      txt(plus ? '+' : '−', 26, yy + lh / 2 - 2, 22, plus ? '#7CF0A8' : '#FF8A9A', { font: 'code' });
      ctx.fillStyle = plus ? '#7CF0A8' : '#FF8A9A'; ctx.globalAlpha = .75; ctx.fillRect(50 + ind, yy + 9, (w - 90 - ind) * len, 9); ctx.globalAlpha = 1;
    }
    ctx.restore();
  }
  // a big rounded button that squishes when pressed (press 1 at the hit, decaying)
  function bigButton(str, x, y, size, k, press, o = {}) {
    if (k <= 0) return;
    const tw = textW(str, size, 'archivo'), w = tw + size * 1.2, h = size * 1.7, e = backOut(clamp(k), 2), dz = press * size * .12;
    ctx.save(); ctx.translate(x, y); ctx.rotate(o.rot ?? 0); ctx.scale(e, e);
    ctx.fillStyle = '#1C6B3A'; ctx.fill(rrPath(-w / 2, -h / 2 + size * .2, w, h, h / 2));
    ctx.fillStyle = o.fill ?? '#38C96E'; ctx.fill(rrPath(-w / 2, -h / 2 + dz, w, h - size * .05, h / 2));
    ctx.strokeStyle = '#123D22'; ctx.lineWidth = 6; ctx.stroke(rrPath(-w / 2, -h / 2 + dz, w, h - size * .05, h / 2));
    ctx.fillStyle = 'rgb(255 255 255 / .3)'; ctx.fill(rrPath(-w / 2 + size * .3, -h / 2 + dz + size * .15, w - size * .6, size * .3, size * .15));
    txt(str, 0, dz + size * .02, size, '#FFFFFF', { font: 'archivo', stroke: '#123D22', sw: size * .14 });
    ctx.restore();
    if (press > .05) { ctx.save(); ctx.globalAlpha = press; ctx.strokeStyle = '#FFFFFF'; ctx.lineWidth = 6; ctx.beginPath(); ctx.ellipse(x, y, w * .5 + (1 - press) * 120, h * .5 + (1 - press) * 80, 0, 0, TAU); ctx.stroke(); ctx.restore(); }
  }
  // a product box for the infomercial (a little 3/4 view carton with a label)
  function productBox(x, y, s, col, label, k) {
    if (k <= 0) return;
    const e = backOut(clamp(k), 2.6);
    ctx.save(); ctx.translate(x, y); ctx.scale(e * s, e * s);
    blob(0, 4, 110, 18, '#2A2350', .35);
    ctx.fillStyle = mixCol(col, '#2A2350', .25); ctx.beginPath(); ctx.moveTo(70, 0); ctx.lineTo(110, -30); ctx.lineTo(110, -210); ctx.lineTo(70, -180); ctx.closePath(); ctx.fill();
    ctx.fillStyle = mixCol(col, '#FFFFFF', .35); ctx.beginPath(); ctx.moveTo(-90, -180); ctx.lineTo(70, -180); ctx.lineTo(110, -210); ctx.lineTo(-50, -210); ctx.closePath(); ctx.fill();
    ctx.fillStyle = col; ctx.fillRect(-90, -180, 160, 180);
    ctx.strokeStyle = '#2A2350'; ctx.lineWidth = 5; ctx.lineJoin = 'round';
    ctx.strokeRect(-90, -180, 160, 180); ctx.beginPath(); ctx.moveTo(70, 0); ctx.lineTo(110, -30); ctx.lineTo(110, -210); ctx.lineTo(-50, -210); ctx.lineTo(-90, -180); ctx.moveTo(70, -180); ctx.lineTo(110, -210); ctx.stroke();
    starShape(-10, -120, 34, '#FFFFFF');
    txt(label, -10, -50, 34, '#FFFFFF', { font: 'rammetto', stroke: '#2A2350', sw: 7 });
    ctx.restore();
  }
  // a starburst sticker ("NOW 3 FOR 1!")
  function starSticker(lines, x, y, r, k, rot, col = '#FF3D7F') {
    if (k <= 0) return;
    const e = backOut(clamp(k), 2.4);
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot); ctx.scale(e, e);
    ctx.fillStyle = 'rgb(40 30 80 / .3)'; ctx.translate(8, 10); starShape(0, 0, r, 'rgb(40 30 80 / .3)', .78, 16, 0); ctx.translate(-8, -10);
    starShape(0, 0, r, '#FFE070', .78, 16, 0); starShape(0, 0, r * .86, col, .8, 16, 0);
    lines.forEach((l, i) => txt(l, 0, (i - (lines.length - 1) / 2) * r * .36, r * (i === 0 ? .3 : .26), '#FFFFFF', { font: 'rammetto', stroke: '#2A2350', sw: 8 }));
    ctx.restore();
  }
  // a shouted jagged bubble ("CLANKER!") with a tail toward (tx, ty)
  function shout(str, x, y, size, k, tx, ty, rot = 0) {
    if (k <= 0) return;
    const e = backOut(clamp(k), 2.6), tw = textW(str, size, 'archivo'), rx = tw / 2 + size * .8, ry = size * 1.1;
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot); ctx.scale(e, e);
    const p = new Path2D(), n = 18;
    for (let i = 0; i < n * 2; i++) { const a = i / (n * 2) * TAU, r = i % 2 ? .82 : 1.06 + hash2(i, 3) * .1; const px = Math.cos(a) * rx * r, py = Math.sin(a) * ry * r; i ? p.lineTo(px, py) : p.moveTo(px, py); }
    p.closePath();
    // a short tail pointing at (tx, ty)
    const dl = Math.hypot(tx - x, ty - y) || 1, tl = Math.min(dl, size * 2.6), lx = (tx - x) / dl * tl, ly = (ty - y) / dl * tl;
    const tail = new Path2D(); tail.moveTo(-size * .4, 0); tail.lineTo(size * .4, 0); tail.lineTo(lx, ly); tail.closePath();
    ctx.fillStyle = '#FFFFFF'; ctx.strokeStyle = '#2A2350'; ctx.lineWidth = 6; ctx.lineJoin = 'round';
    ctx.stroke(tail); ctx.stroke(p); ctx.fill(tail); ctx.fill(p);
    txt(str, 0, 2, size, '#E2334A', { font: 'archivo' });
    ctx.restore();
  }
  // a diagonal ribbon (a bestseller sash) across the frame, fluttering
  function sash(str, k, t, o = {}) {
    if (k <= 0) return;
    const y0 = o.y ?? H * .5, ang = o.ang ?? -.22, len = W * 1.6, th = o.th ?? 120, e = easeOut(clamp(k));
    ctx.save(); ctx.translate(W / 2, y0); ctx.rotate(ang);
    ctx.beginPath(); ctx.rect(-len / 2, -th, len * e, th * 2); ctx.clip();
    const seg = 40, pts = [];
    for (let i = 0; i <= seg; i++) { const u = i / seg, x = -len / 2 + u * len; pts.push([x, Math.sin(u * 9 - t * 7) * 14]); }
    const band = new Path2D(); pts.forEach(([x, y], i) => i ? band.lineTo(x, y - th / 2) : band.moveTo(x, y - th / 2)); for (let i = seg; i >= 0; i--) band.lineTo(pts[i][0], pts[i][1] + th / 2); band.closePath();
    ctx.fillStyle = 'rgb(40 30 80 / .3)'; ctx.translate(10, 14); ctx.fill(band); ctx.translate(-10, -14);
    ctx.fillStyle = o.col ?? '#E2334A'; ctx.fill(band);
    ctx.strokeStyle = '#FFE070'; ctx.lineWidth = 6; ctx.stroke(band);
    const rep = o.rep ?? 3, gap = len / rep;
    for (let i = 0; i < rep; i++) { const x = -len / 2 + gap * (i + .5), yy = Math.sin(((x + len / 2) / len) * 9 - t * 7) * 14; txt(str, x, yy + 3, th * .42, '#FFFFFF', { font: 'rammetto', stroke: '#8A1024', sw: 8 }); }
    ctx.restore();
  }
  // a red velvet stage curtain dropping from the top (k 0 → 1: up → fully down), with a bounce
  function curtain(k) {
    if (k <= 0) return;
    const e = k < 1 ? easeIn(k) : 1, y = lerp(-H, 0, e) + (k >= 1 ? 0 : 0);
    ctx.save(); ctx.translate(0, y);
    ctx.fillStyle = linGrad(0, 0, 0, H, [[0, '#7A0E22'], [1, '#B81F3A']]); ctx.fillRect(0, 0, W, H);
    for (let i = 0; i < 24; i++) {
      const x = i * W / 24;
      ctx.fillStyle = linGrad(x, 0, x + W / 24, 0, [[0, 'rgb(0 0 0 / .28)'], [.45, 'rgb(255 120 140 / .22)'], [1, 'rgb(0 0 0 / .28)']]);
      ctx.fillRect(x, 0, W / 24, H);
    }
    ctx.fillStyle = '#E8B84A'; ctx.fillRect(0, H - 34, W, 34); ctx.fillStyle = '#B8862A'; for (let i = 0; i < 48; i++) ctx.fillRect(i * W / 48 + 8, H - 34, 14, 60);
    ctx.restore();
  }
  // a receipt strip unrolling downward from (x, y), w wide, to length L·k, with lines of text
  function receipt(x, y, w, L, k, lines, rot = .04) {
    if (k <= 0) return;
    const len = L * easeOut(clamp(k));
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot);
    ctx.fillStyle = 'rgb(40 30 80 / .25)'; ctx.fillRect(10, 12, w, len);
    ctx.fillStyle = '#FFFDF6'; ctx.fillRect(0, 0, w, len);
    ctx.beginPath(); ctx.moveTo(0, len); for (let i = 0; i <= 16; i++) ctx.lineTo(w * i / 16, len + (i % 2 ? 12 : 0)); ctx.lineTo(w, len); ctx.fill();
    ctx.beginPath(); ctx.rect(0, 0, w, len); ctx.clip();
    lines.forEach(([s, size, font, col], i) => { const yy = 30 + lines.slice(0, i).reduce((a, l) => a + l[1] * 1.3, 0) + size * .65; txt(s, w / 2, yy, size, col ?? '#2A2350', { font: font ?? 'code', maxW: w - 40 }); });
    ctx.restore();
    ctx.fillStyle = '#DAD4C8'; ctx.fillRect(x - 20, y - 16, w + 40, 26);
  }

  // ---------- V2.1 "DeepSeek New Year sticker shock": a whale bursts from a red envelope with a tiny price tag; Ren's jaw drops ----------
  line('V2', 1, (p, lt, d, t, seg) => {
    // the window is 6.5 beats from "DeepSeek"; Ren's cut takes the last 3, from just before "sticker shock"
    const b = beatsIn(t, seg), [i, bb] = cuts(b, [-1, 3.5]);
    if (i === 0) {
      const k = ease(clamp(b / 3.5)), bb = b - .5;
      const v = still('v2_1_whale', { x: .5, y: lerp(.55, .5, k), z: lerp(1.04, 1.14, k) });
      confetti(t, { n: 50, seed: 21, cols: ['#E8303A', '#FFD34A', '#FF6FA0', '#FFFFFF'] });
      // the price tag hangs off the whale's flipper on a string, swinging
      const [fx, fy] = v.pt(.69, .66), [tx, ty] = v.pt(.73, .53), tk = clamp((bb - .8) / .35), sw = Math.sin(t * 5) * .05;
      if (tk > 0) { ctx.save(); ctx.strokeStyle = '#2A2350'; ctx.lineWidth = 4; ctx.beginPath(); ctx.moveTo(fx, fy); ctx.quadraticCurveTo(fx + 40, (fy + ty) / 2, tx + 18, ty); ctx.stroke(); ctx.restore(); }
      priceTag('$5.6M', tx, ty, 66, tk, .1 + sw, 'final training run');
      if (bb > .8 && bb < 1.6) burst(tx + 180, ty, 280, (bb - .8) / .8, ['#FFFFFF', '#FFE070', '#E8303A']);
      popLabel('R1', v.pt(.4, .3)[0], v.pt(.4, .3)[1], 50, clamp((bb - 1.6) / .3), { fill: '#FFFFFF', col: '#3D6FD0', rot: -.12 });
      sparkleField(t, { n: 10, r: 22, seed: 22 });
      startFlash(t, seg, .8);
    } else {
      const h = hit(bb, .6), [sx, sy] = shake(t, 12 * h + 2);
      still('v2_1_ren', { x: .5, y: .45, z: 1.08 * punch(bb, .1) }, { dx: sx, dy: sy });
      speedLines(W * .56, H * .3, t, { n: 70, r0: 420, a: .35 * hit(bb, 1.4) });
      chartDive(60, 60, 600, 400, clamp((bb - .1) / 1.8), t);
      popLabel('NVDA −17%', 360, 500, 48, clamp((bb - 1.6) / .3), { fill: '#FFD0D8', col: '#B02040', rot: -.05 });
      cutFlash(bb, .8);
    }
  });

  // ---------- V2.2 "Half a trillion Stargate talk": a ring gate rises from the desert, $500B; the reveal: it's cardboard on sticks ----------
  line('V2', 2, (p, lt, d, t, seg) => {
    const b = beatsIn(t, seg), [i, bb] = cuts(b, [-1, 4.5]);
    if (i === 0) {
      const k = ease(clamp((b - .5) / 4));
      const v = still('v2_2_gate', { x: .5, y: lerp(.7, .44, k), z: lerp(1.25, 1.04, k) });
      const [gx, gy] = v.pt(.51, .46);
      addGlow(gx, gy, 380, '#8FD8FF', .35 + .15 * pulse(t, 3));
      rays(gx, gy, { t, a: .16, n: 10, ang: -Math.PI / 2, spread: TAU, len: 1400 });
      const nk = clamp((b - 1.5) / 1.2);
      if (nk > 0) {
        logoText('$500B', W / 2, 190, 190, { font: 'rammetto', k: nk, grad: ['#FFF6C0', '#FFD34A', '#FF9A4A'], edge: '#5A3A10', rimCol: '#FFFFFF' });
        sparkleField(t, { n: 12, r: 30, seed: 23, x0: W * .25, x1: W * .75, y0: 120, y1: 380, col: '#FFF4C0' });
      }
      startFlash(t, seg);
    } else {
      const k = ease(clamp(bb / 4));
      const v = still('v2_2_props', { x: .5, y: lerp(.42, .5, k), z: lerp(1.12, 1.03, k), r: Math.sin(t * 7) * .006 });
      // the men strain: sweat drops pop off their heads on the beats
      for (const [u, w, j] of [[.25, .66, 0], [.72, .68, 1], [.84, .66, 2]]) { const [x, y] = v.pt(u, w), sk = frac(bb + j * .33); ctx.save(); ctx.globalAlpha = 1 - sk; sweatDrop(x + sk * 30, y - 30 - sk * 40, 60); ctx.restore(); }
      for (let j = 0; j < 3; j++) popLabel('?', 1420 + j * 110, 450 + (j % 2) * 40, 50, clamp((bb - 2.6 - j * .4) / .25), { fill: '#FFE070', rot: (j - 1) * .2 });
      cutFlash(bb, .8);
    }
  });

  // ---------- V2.3 "Hit 'Accept All,' never ask": Akari on a beach chair presses ACCEPT ALL on every beat; Kiri lunges to stop her,
  // too late: the diffs stream past in her glasses and the button keeps going down ----------
  // the diffs reflected in Kiri's lenses: green and red lines racing upward over a dark glass tint, thin enough that her eyes still show through
  const KIRI3 = { lenses: [[.43, .405], [.61, .405]], r: [72, 100], mouth: [.52, .6] };
  function lensDiffs(v, scroll, a) {
    for (const [u, w] of KIRI3.lenses) {
      const [x, y] = v.pt(u, w), rx = KIRI3.r[0] * v.s, ry = KIRI3.r[1] * v.s, lh = 15 * v.s;
      ctx.save(); ctx.beginPath(); ctx.ellipse(x, y, rx, ry, 0, 0, TAU); ctx.clip();
      ctx.globalAlpha = a;
      ctx.fillStyle = 'rgb(16 28 56 / .45)'; ctx.fillRect(x - rx, y - ry, rx * 2, ry * 2);
      const first = Math.floor(scroll / lh);
      for (let j = first; j < first + ry * 2 / lh + 2; j++) {
        const yy = y - ry + j * lh - scroll, plus = hash2(71, j) > .45, len = .3 + hash2(72, j) * .6, ind = Math.floor(hash2(73, j) * 3) * 10 * v.s;
        ctx.fillStyle = plus ? '#7CF0A8' : '#FF8A9A'; ctx.fillRect(x - rx * .8 + ind, yy, rx * 1.5 * len, lh * .32);
      }
      ctx.globalAlpha = a * .8; ctx.fillStyle = 'rgb(255 255 255 / .45)';
      ctx.beginPath(); ctx.moveTo(x - rx * .2, y - ry); ctx.lineTo(x + rx * .25, y - ry); ctx.lineTo(x - rx * .35, y + ry); ctx.lineTo(x - rx * .8, y + ry); ctx.closePath(); ctx.fill();
      ctx.restore();
    }
  }
  line('V2', 3, (p, lt, d, t, seg) => {
    const b = beatsIn(t, seg), [i, bb] = cuts(b, [-1, 4.5]);
    if (i === 0) {
      const bb = b - .5, k = ease(clamp(bb / 4));
      const v = still('v2_3_accept', { x: lerp(.45, .5, k), y: .5, z: lerp(1.04, 1.12, k) });
      diffTower(50, 70, 420, 500, t * 1400);
      // the button hovers over her finger and goes down on every beat; a ✓ floats up from each press
      const press = bb > .5 ? hit(frac(bb), .35) : 0, [fx, fy] = v.pt(.42, .66);
      bigButton('ACCEPT ALL', fx - 60, fy - 170, 54, clamp((bb - .2) / .3), press);
      if (bb > 1) popLabel('✓', fx + 140, fy - 250 - frac(bb) * 140, 46, 1 - clamp((frac(bb) - .6) / .4), { fill: '#C8F5D8', col: '#1E7A45' });
      startFlash(t, seg);
    } else {
      // her lunge lands with a jolt, then the camera creeps in on her face while the button (Akari's, off-screen) keeps getting pressed
      const k = ease(clamp(bb / 4)), [sx, sy] = shake(t, 12 * hit(bb, .5));
      const v = still('v2_3_wait', { x: lerp(.48, .52, k), y: lerp(.46, .42, k), z: lerp(1.04, 1.16, k) * punch(bb, .06) }, { dx: sx, dy: sy });
      speedLines(W * .5, H * .4, t, { n: 70, r0: 520, a: .35 * hit(bb, 1.4) });
      lensDiffs(v, t * 700, .75);
      const [mx, my] = v.pt(...KIRI3.mouth);
      shout('WAIT—!', 1480, 300, 58, clamp((bb - .25) / .25), mx + 60, my - 40, .06);
      const press = bb > .8 ? hit(frac(bb), .35) : 0;
      bigButton('ACCEPT ALL', 1560, 830, 44, clamp((bb - .6) / .25), press, { rot: -.04 });
      if (bb > 1) popLabel('✓', 1700, 740 - frac(bb) * 120, 40, 1 - clamp((frac(bb) - .6) / .4), { fill: '#C8F5D8', col: '#1E7A45' });
      cutFlash(bb, .8);
    }
  });

  // ---------- V2.4 "MCP for every task": Kiri's glasses flash over one plug; everything on the table lights up; Clawd plugs in last ----------
  line('V2', 4, (p, lt, d, t, seg) => {
    const b = beatsIn(t, seg), [i, bb] = cuts(b, [0, 3]);
    if (i === 0) {
      const k = ease(clamp(bb / 3));
      const v = still('v2_4_kiri', { x: lerp(.45, .5, k), y: lerp(.5, .44, k), z: lerp(1.04, 1.16, k) });
      const L = [v.pt(.448, .405), v.pt(.6, .375)];
      lensFlash(L, 64 * v.s, 70 * v.s, Math.sin(clamp((bb - .4) / 1) * Math.PI));
      const [px, py] = v.pt(.2, .36);
      addGlow(px, py, 200, '#9FE8FF', .45 + .25 * pulse(t, 4));
      popLabel('MCP', px, py + 30, 72, clamp((bb - 1.2) / .3), { fill: '#FFE070', rot: -.08 });
      startFlash(t, seg);
    } else {
      // the table is a wide strip (Anima drew it letterboxed), shown as a cinemascope band over a summer split
      const k = ease(clamp(bb / 5));
      diagSplit('#CFEFFF', '#8FD0F4', t, { x: W * .55, a: .3, speed: 220 });
      const v = still('v2_4_hub', { x: .5, y: .5, z: lerp(1.06, 1.0, k) }, { rect: [0, 240, W, 572] });
      ctx.fillStyle = '#FFFFFF'; ctx.fillRect(0, 232, W, 8); ctx.fillRect(0, 812, W, 8);
      const G = [[.14, .44, 'lamp'], [.24, .52, 'toaster'], [.41, .56, 'GPU'], [.64, .46, 'telescope'], [.74, .52, 'laptop'], [.89, .44, 'fan']];
      G.forEach(([u, w, name], j) => {
        const on = bb - .3 - j * .5; if (on < 0) return;
        const [x, y] = v.pt(u, w);
        addGlow(x, y, 130, '#FFF0A0', .5 * (.5 + .5 * hit(on, .6)));
        popLabel(`${name} ✓`, x, j % 2 ? 900 : 170, 36, clamp(on / .25), { fill: '#C8F5D8', col: '#1E7A45', rot: (j % 2 ? .05 : -.05) });
        ctx.save(); ctx.globalAlpha = clamp(on / .25) * .8; ctx.strokeStyle = '#FFFFFF'; ctx.lineWidth = 4; ctx.setLineDash([10, 8]); ctx.beginPath(); ctx.moveTo(x, j % 2 ? 870 : 200); ctx.lineTo(x, y + (j % 2 ? 60 : -80)); ctx.stroke(); ctx.restore();
      });
      const [hx, hy] = v.pt(.52, .58);
      addGlow(hx, hy, 140, '#9FE8FF', .5 + .3 * pulse(t, 4));
      popLabel('MCP', hx, hy - 110, 46, clamp(bb / .3), { fill: '#FFE070' });
      // Clawd hops in last, below the band, and plugs himself in
      const ck = clamp((bb - 3.3) / .5);
      if (ck > 0) {
        const cx = lerp(W + 200, 880, easeOut(ck)), cy = 965 - Math.sin(ck * Math.PI) * 160;
        ctx.save(); ctx.strokeStyle = '#FFFFFF'; ctx.lineWidth = 9; ctx.lineCap = 'round'; ctx.beginPath(); ctx.moveTo(hx, hy + 30); ctx.quadraticCurveTo(hx - 40, 900, cx + 110, cy - 100); ctx.stroke(); ctx.restore();
        cut('clawd_jump', cx, cy, 230, { rot: -.1 + .05 * Math.sin(t * 9) });
        if (ck >= 1) { sparkle(cx - 60, cy - 220, 36, 1, '#FFF4B0'); popLabel('Clawd ✓', cx - 40, cy - 290, 36, clamp((bb - 3.8) / .25), { fill: '#FFD8C2', col: '#B0501E', rot: .06 }); }
      }
      cutFlash(bb, .7);
    }
  });

  // ---------- V2.5 "Zuck's nine-figure poaching spree": he holds out a briefcase of cash; Ren clutches his bag as colleagues go poof ----------
  line('V2', 5, (p, lt, d, t, seg) => {
    const b = beatsIn(t, seg), [i, bb] = cuts(b, [0, 4]);
    if (i === 0) {
      const k = ease(clamp(bb / 4));
      still('v2_5_zuck', { x: lerp(.5, .46, k), y: lerp(.5, .44, k), z: lerp(1.04, 1.14, k) * punch(frac(bb), .015) });
      confetti(t, { n: 40, seed: 25, s: 2.2, cols: ['#8BD48A', '#5FB85E', '#C8F0B0', '#FFE070'] });
      const n = Math.floor(lerp(0, 100, easeOut(clamp((bb - .8) / 1.6)))) * 1e6;
      popLabel(`$${n.toLocaleString('en-US')}`, 1500, 330, 64, clamp((bb - .8) / .3), { fill: '#FFE070', rot: .05 });
      popLabel('signing bonus', 1530, 430, 30, clamp((bb - 1.2) / .3), { fill: '#FFFFFF', font: 'code', rot: .05 });
      startFlash(t, seg);
    } else {
      // the still mirrors on every beat, so his nervous glance snaps left, right, left; researchers vanish in puffs around him
      const beat = Math.floor(bb);
      still('v2_5_ren', { x: .5, y: .45, z: 1.08 }, { flip: beat % 2 === 1 });
      const spots = [[300, 360], [1640, 420], [420, 760], [1500, 780]];
      for (let j = 0; j < 4; j++) { const [x, y] = spots[j]; puff(x, y, 170, clamp((bb - .2 - j * .8) / 1.1), 'poof!'); }
      popLabel('hired away: ' + clamp(Math.floor((bb - .2) / .8) + 1, 0, 4), 330, 120, 40, clamp((bb - .3) / .3), { fill: '#FFFFFF', rot: -.05 });
      cutFlash(frac(bb), .25, .2);
    }
  });

  // ---------- V2.6 "Superintelligence — buy three!": Akari's shopping channel; three boxes pop onto the counter; 3 FOR 1 ----------
  const BOXES = [['#FF6FA0', 'SI'], ['#3D8BFF', 'SI'], ['#FFB030', 'SI']];
  line('V2', 6, (p, lt, d, t, seg) => {
    const b = beatsIn(t, seg), k = ease(clamp(b / 8));
    const v = still('v2_6_shop', { x: .5, y: lerp(.56, .53, k), z: lerp(1.04, 1.1, k) });
    // the marquee title, top left (clear of her head), bulbs chasing round it
    const bk = clamp((b - .3) / .4);
    if (bk > 0) {
      ctx.save(); ctx.translate(370, 170); ctx.rotate(-.05); ctx.scale(backOut(bk, 2), backOut(bk, 2));
      ctx.fillStyle = 'rgb(40 30 80 / .3)'; ctx.fill(rrPath(-330 + 10, -130 + 12, 660, 260, 34));
      ctx.fillStyle = '#2A2350'; ctx.fill(rrPath(-330, -130, 660, 260, 34));
      for (let j = 0; j < 36; j++) {
        const u = j / 36, per = 2 * (640 + 240), d_ = u * per, [x, y] = d_ < 640 ? [-320 + d_, -120] : d_ < 880 ? [320, -120 + d_ - 640] : d_ < 1520 ? [320 - (d_ - 880), 120] : [-320, 120 - (d_ - 1520)];
        fillP(ellPath(x, y, 7, 7), (Math.floor(t * 10) + j) % 3 === 0 ? '#FFF4B0' : '#8A6A20');
      }
      ctx.restore();
      logoText('SUPER', 370, 125, 84, { font: 'rammetto', k: bk, rot: -.05, grad: ['#FFFFFF', '#FFE070', '#FF9A4A'], edge: '#2A2350' });
      logoText('INTELLIGENCE', 370, 215, 50, { font: 'rammetto', k: bk, rot: -.05, grad: ['#FFFFFF', '#FFD1E0', '#FF6FA0'], edge: '#2A2350' });
    }
    // three boxes pop onto the counter on the beats
    BOXES.forEach(([col, lab], j) => { const [x, y] = v.pt([.3, .5, .7][j], .865); productBox(x, y, .9, col, lab, clamp((b - 2 - j) / .3)); });
    starSticker(['NOW', '3 FOR 1!'], 1640, 400, 180, clamp((b - 5) / .3), -.15 + Math.sin(t * 4) * .05);
    sparkleField(t, { n: 10, r: 26, seed: 26 });
    startFlash(t, seg, .6);
  });

  // ---------- V2.7 "Grok goes MechaHitler mode": a chatbot's giant-robot costume malfunctions; Akari reels; PATCHED, it bows ----------
  line('V2', 7, (p, lt, d, t, seg) => {
    const b = beatsIn(t, seg), [i, bb] = cuts(b, [0, 3, 5]);
    if (i === 0) {
      const g = hit(frac(bb), .3), [sx, sy] = shake(t, 6 + 10 * g);
      const v = still('v2_7_robot', { x: .5, y: .45, z: 1.06 * punch(frac(bb), .03) }, { dx: sx, dy: sy });
      grade('#FF2040', .18 * g + .06 * Math.sin(t * 20) ** 2, 'multiply');
      glitch(t, bb > .4 ? .6 * g + .15 : 0);
      popLabel('⚠ BAD UPDATE', 460, 200, 58, clamp((bb - .4) / .3), { fill: '#FFD0D8', col: '#B02040', rot: -.06 });
      for (const u of [.36, .55]) { const [lx, ly] = v.pt(u, .69); addGlow(lx, ly, 140, '#FF3050', .5 * g + .2); }
      const [mx, my] = v.pt(.51, .45);
      sayBubble('oops!', 1480, 230, 60, clamp((bb - 1.6) / .6), mx + 60, my);
      startFlash(t, seg);
    } else if (i === 1) {
      const [sx, sy] = shake(t, 16 * hit(bb, .8) + 3);
      still('v2_7_akari', { x: .5, y: .42, z: 1.1 * punch(bb, .1) }, { dx: sx, dy: sy });
      speedLines(W * .5, H * .4, t, { n: 80, r0: 460, a: .45 });
      impactFrame(bb < .15 ? 1 : 0);
      cutFlash(bb, .5);
    } else {
      // patched: a bandage slaps across its screen face and the robot bows (a slow forward tilt about its feet)
      const bow = Math.sin(clamp((bb - .7) / 1.5) * Math.PI) * .06;
      const v = still('v2_7_robot', { x: .5, y: .45, z: 1.06, r: -bow });
      grade('#DDEBFF', .2, 'soft-light');
      const [fx, fy] = v.pt(.51, .41), bk = clamp((bb - .2) / .25);
      if (bk > 0) {
        const e = lerp(1.6, 1, easeIn(bk)) * v.s * .62;
        ctx.save(); ctx.translate(fx, fy); ctx.rotate(-.3 - bow); ctx.scale(e, e);
        ctx.fillStyle = 'rgb(40 30 80 / .3)'; ctx.fill(rrPath(-330 + 8, -70 + 10, 660, 140, 60));
        ctx.fillStyle = '#F6D2A8'; ctx.fill(rrPath(-330, -70, 660, 140, 60)); ctx.strokeStyle = '#B07A4A'; ctx.lineWidth = 5; ctx.stroke(rrPath(-330, -70, 660, 140, 60));
        ctx.fillStyle = '#FFF2E0'; ctx.fill(rrPath(-150, -52, 300, 104, 14));
        txt('PATCHED', 0, 4, 58, '#B02040', { font: 'archivo' });
        ctx.restore();
      }
      sweatDrop(fx + 260, fy - 150, 90 + 10 * Math.sin(t * 6));
      cutFlash(bb, .6);
    }
  });

  // ---------- V2.8 "Two labs win Olympiad gold": two robots bite their medals; Akari snaps a photo; the footnote flips up ----------
  line('V2', 8, (p, lt, d, t, seg) => {
    const b = beatsIn(t, seg), snap = 4, frz = b > snap, bf = frz ? snap : b, k = ease(clamp(bf / snap));
    const v = still('v2_8_podium', { x: .5, y: lerp(.5, .45, k), z: lerp(1.04, 1.12, k) });
    const tf = frz ? t - (b - snap) * beatLen() : t;
    confetti(tf, { n: 70, seed: 28 });
    const [ax, ay] = v.pt(.4, .72), [bx, by] = v.pt(.62, .72);
    for (const [u, w] of [[.375, .54], [.61, .55]]) { const [gx, gy] = v.pt(u, w); glint(gx + 30, gy - 30, 30, Math.sin(frac(bf * .5 + u) * Math.PI)); }
    popLabel('35/42', ax, ay, 50, clamp((b - 1) / .3), { fill: '#FFE070', rot: -.06 });
    popLabel('35/42', bx, by, 50, clamp((b - 2) / .3), { fill: '#FFE070', rot: .06 });
    popLabel('IMO 2025 · GOLD', 380, 160, 48, clamp((b - .3) / .3), { fill: '#FFFFFF' });
    if (frz) {
      // the shutter: a white flash, then the frame becomes a photo (a white border and a small tilt)
      flash(1 - clamp((b - snap) / .35));
      ctx.save(); ctx.strokeStyle = '#FFFFFF'; ctx.lineWidth = 40; ctx.strokeRect(20, 20, W - 40, H - 40); ctx.restore();
      popLabel('click! 📸', 1580, 860, 40, clamp((b - snap) / .3), { fill: '#FFD1E0', rot: .08 });
    } else {
      // Akari's viewfinder
      ctx.save(); ctx.strokeStyle = '#FFFFFF'; ctx.lineWidth = 8; const m = 90, c = 80;
      for (const [x, y, sx, sy] of [[m, m, 1, 1], [W - m, m, -1, 1], [m, H - m - 60, 1, -1], [W - m, H - m - 60, -1, -1]]) { ctx.beginPath(); ctx.moveTo(x, y + sy * c); ctx.lineTo(x, y); ctx.lineTo(x + sx * c, y); ctx.stroke(); }
      ctx.restore();
      if (Math.floor(t * 2) % 2 === 0) { fillP(ellPath(W - 150, 170, 14, 14), '#FF3D5A'); }
    }
    const fk = clamp((b - 5.3) / .4);
    if (fk > 0) {
      ctx.save(); ctx.translate(W / 2, 700); ctx.scale(1, Math.sin(fk * Math.PI / 2)); ctx.rotate(-.02);
      ctx.fillStyle = 'rgb(40 30 80 / .25)'; ctx.fillRect(-520 + 8, -60 + 10, 1040, 120);
      ctx.fillStyle = '#FFFDF4'; ctx.fillRect(-520, -60, 1040, 120);
      txt('* gold-medal level. no actual medals were given to machines.', 0, 2, 28, '#4A4060', { font: 'code', maxW: 980 });
      ctx.restore();
    }
    startFlash(t, seg, .6);
  });

  // ---------- V2.9 "GPT-5 breaks 4o hearts": the 4o heart waves goodbye from a departing train; REWIND; Akari's happy tears ----------
  line('V2', 9, (p, lt, d, t, seg) => {
    const b = beatsIn(t, seg), [i, bb0] = cuts(b, [-1, 4.5, 5.5]), bb = i === 0 ? b - .5 : bb0;
    if (i < 2) {
      // the train pulls away (the camera drifts with it), then rewinds back into the station
      const go = i === 0 ? easeIn(clamp(bb / 4)) : 1 - easeOut(clamp(bb / 1));
      const v = still('v2_9_train', { x: .42 + go * .2, y: .46, z: 1.22 });
      grade('#5A6FA8', .28, 'multiply');
      speedBars(t * (i === 0 ? 1 : -1), { n: 30, a: .25 * go, speed: 2600 });
      rain(t, { n: 110, a: .45 });
      const [hx, hy] = v.pt(.62, .4);
      popLabel('4o', hx, hy, 50, clamp((bb - .2) / .3), { fill: '#FFFFFF', col: '#C02060', rot: .12 });
      if (i === 0) for (let j = 0; j < 5; j++) {
        const sk = clamp((bb - .8 - j * .5) / .25), x = 200 + j * 380 + (j % 2) * 40, y = 850 - (j % 2) * 40 + Math.sin(t * 6 + j) * 10;
        if (sk > 0) { ctx.fillStyle = '#C8A070'; ctx.fillRect(x - 6, y, 12, 160); }
        popLabel('#keep4o', x, y, 48, sk, { fill: '#FFFFFF', col: '#C02060', rot: (j % 2 ? .08 : -.08) });
      }
      if (i === 1) {
        // VHS rewind: scanlines and a big ◀◀
        ctx.save(); ctx.globalAlpha = .25; ctx.fillStyle = '#FFFFFF'; for (let y = Math.floor(t * 600) % 12; y < H; y += 12) ctx.fillRect(0, y, W, 3); ctx.restore();
        txt('◀◀ REWIND', 140, 150, 72, '#FFFFFF', { font: 'code', align: 'left', stroke: '#2A2350', sw: 10 });
        glitch(t, .3);
      }
      if (i === 0) startFlash(t, seg); else cutFlash(bb, .7);
    } else {
      const k = ease(clamp(bb / 3));
      still('v2_9_akari', { x: .5, y: lerp(.46, .4, k), z: lerp(1.05, 1.16, k) });
      rain(t, { n: 60, a: .25 });
      sparkleField(t, { n: 16, r: 26, seed: 29, col: '#FFF4F8' });
      for (let j = 0; j < 8; j++) { const hk = frac(t * .6 + j / 8); ctx.save(); ctx.globalAlpha = Math.sin(hk * Math.PI); starShape(200 + hash2(29, j) * 1500, 900 - hk * 700, 22, '#FF8FB8', .5, 5); ctx.restore(); }
      cutFlash(bb, .9);
    }
  });

  // ---------- V2.10 "Nano Banana tops the charts": the banana idol hops up the ranking ladder and knocks the #1 app off ----------
  const APPS = ['#7C6CF0', '#20B0A0', '#F06080', '#4090F0', '#303848'];
  line('V2', 10, (p, lt, d, t, seg) => {
    const b = beatsIn(t, seg);
    diagSplit('#FFF3B0', '#FFD34A', t, { x: W * .45, a: .3, speed: 260 });
    rays(W * .7, -80, { t, a: .25, n: 9, ang: Math.PI / 2, spread: 1.4, len: 1400, col: '#FFFFFF' });
    // the ladder: five rungs, #5 at the bottom
    const x0 = 1000, rungY = r => 870 - (5 - r) * 118;
    for (let r = 5; r >= 1; r--) {
      const y = rungY(r);
      ctx.fillStyle = 'rgb(40 30 80 / .25)'; ctx.fill(rrPath(x0 + 10, y + 10, 720, 26, 13));
      ctx.fillStyle = '#FFFFFF'; ctx.fill(rrPath(x0, y, 720, 26, 13)); ctx.strokeStyle = '#2A2350'; ctx.lineWidth = 4; ctx.stroke(rrPath(x0, y, 720, 26, 13));
      txt(`#${r}`, x0 - 70, y + 6, 54, '#2A2350', { font: 'rammetto' });
    }
    // the reigning #1 app icon, knocked off on the last hop
    const knock = clamp((b - 5.2) / 1.2);
    if (knock < 1) {
      const x = x0 + 560 + knock * 700, y = rungY(1) - 62 - Math.sin(knock * Math.PI) * 260 + knock * knock * 500;
      ctx.save(); ctx.translate(x, y); ctx.rotate(knock * 7);
      ctx.fillStyle = APPS[4]; ctx.fill(rrPath(-55, -55, 110, 110, 28)); ctx.strokeStyle = '#FFFFFF'; ctx.lineWidth = 5; ctx.stroke(rrPath(-55, -55, 110, 110, 28));
      txt('✦', 0, 3, 62, '#FFFFFF', { font: 'archivo' });
      ctx.restore();
    }
    // the other apps sit on the lower rungs
    for (let r = 2; r <= 5; r++) { const y = rungY(r) - 52; ctx.fillStyle = APPS[r - 2]; ctx.fill(rrPath(x0 + 505, y - 50, 100, 100, 26)); ctx.strokeStyle = '#FFFFFF'; ctx.lineWidth = 4; ctx.stroke(rrPath(x0 + 505, y - 50, 100, 100, 26)); }
    // the banana hops up one rung per beat from b 1
    const hop = clamp(b - 1, 0, 4.2), rung = Math.min(4, Math.floor(hop)), f = hop >= 4.2 ? 1 : frac(hop), from = 5 - rung, to = Math.max(1, from - 1);
    const y = lerp(rungY(from), rungY(to), easeOut(clamp(f / .5))) - Math.sin(clamp(f / .5) * Math.PI) * 90;
    const onTop = b >= 5.2, bx = x0 + 260 + (onTop ? 0 : 0);
    cut('v2_10_banana', bx, (onTop ? rungY(1) : y) + 4, 240, { sq: onTop ? .05 * pulse(t, 4) : 0, rot: onTop ? 0 : Math.sin(f * Math.PI) * .1 });
    if (onTop) {
      const ck = clamp((b - 5.4) / .3);
      ctx.save(); ctx.translate(bx - 20, rungY(1) - 270); ctx.scale(ck, ck); starShape(0, 0, 44, '#FFE070', .5, 5); ctx.restore();
      sparkleField(t, { n: 12, r: 30, seed: 30, x0: x0, x1: x0 + 600, y0: 100, y1: 500 });
      popLabel('#1', bx + 200, rungY(1) - 190, 64, ck, { fill: '#FFE070', rot: .1 });
    }
    // Clawd in the crowd, waving a glowstick
    const wave = Math.sin(t * 9) * .5;
    const cl = cut('clawd_jump', 380, 900 - Math.abs(Math.sin(b * Math.PI)) * 40, 340, { rot: -.05 });
    const [gx, gy] = cl.pt(.9, .2);
    ctx.save(); ctx.translate(gx, gy); ctx.rotate(-.4 + wave); ctx.lineCap = 'round';
    ctx.strokeStyle = alpha('#7CFFB0', .4); ctx.lineWidth = 44; ctx.beginPath(); ctx.moveTo(0, 0); ctx.lineTo(0, -170); ctx.stroke();
    ctx.strokeStyle = '#B8FFD4'; ctx.lineWidth = 22; ctx.stroke(); ctx.restore();
    popLabel('Nano Banana', 380, 160, 52, clamp((b - .4) / .3), { fill: '#FFFFFF', rot: -.05 });
    startFlash(t, seg);
  });

  // ---------- V2.11 "Billion-five: Anthropic's prize": Clawd pays each author; the line reaches the horizon; the receipt unrolls ----------
  line('V2', 11, (p, lt, d, t, seg) => {
    const b = beatsIn(t, seg), [i, bb] = cuts(b, [-1, 4.5]);
    if (i === 0) {
      const bb = b - .5, k = ease(clamp(bb / 4));
      const v = still('v2_11_clawd', { x: .5, y: .5, z: lerp(1.04, 1.14, k) });
      // his sweat drop swells until it's the size of his head
      const [sx, sy] = v.pt(.66, .37), ds = lerp(70, 330, easeOut(clamp((bb - 1) / 2.4)));
      sweatDrop(sx + ds * .1, sy - ds * .25, ds, .15);
      startFlash(t, seg);
    } else {
      const k = ease(clamp(bb / 4.5));
      still('v2_11_line', { x: .5, y: .5, z: lerp(1.3, 1.02, k) });
      receipt(110, 180, 380, 700, clamp((bb - .5) / 2.5), [
        ['RECEIPT', 40, 'archivo'], ['~500,000 books', 28], ['× $3,000', 28], ['- - - - - - - -', 28], ['TOTAL', 30, 'archivo'], ['$1.5B', 84, 'rammetto', '#B02040'],
      ]);
      cutFlash(bb, .7);
    }
  });

  // ---------- V2.12 "Yudkowsky drops 'Everyone Dies'": the fedora author holds up the book; the cast gasps, freeze, bestseller sash ----------
  line('V2', 12, (p, lt, d, t, seg) => {
    const b = beatsIn(t, seg), [i, bb] = cuts(b, [-1, 4]);
    if (i === 0) {
      const k = ease(clamp((b - .5) / 3.5)), h = hit(b - 2.5, .5), [sx, sy] = shake(t, 10 * h);
      const v = still('v2_12_eliezer', { x: .5, y: lerp(.5, .48, k), z: lerp(1.04, 1.12, k) * punch(b - 2.5, .05) }, { dx: sx, dy: sy });
      // the title on the black cover
      const [cx, cy] = v.pt(.3, .47), tk = clamp((b - 1) / .8);
      if (tk > 0) {
        ctx.save(); ctx.translate(cx, cy); ctx.rotate(-.24); ctx.scale(v.s, v.s); ctx.globalAlpha = tk;
        txt('IF ANYONE', 0, -90, 50, '#FFFFFF', { font: 'archivo' });
        txt('BUILDS IT,', 0, -36, 50, '#FFFFFF', { font: 'archivo' });
        txt('EVERYONE', 0, 30, 58, '#FF5A3A', { font: 'archivo' });
        txt('DIES', 0, 92, 70, '#FF5A3A', { font: 'archivo' });
        ctx.restore();
      }
      startFlash(t, seg);
    } else {
      const frz = bb > .6, h = hit(bb, .5), [sx, sy] = shake(t, frz ? 0 : 14 * h);
      still('v2_12_gasp', { x: .5, y: .45, z: frz ? 1.1 : 1.1 * punch(bb, .1) }, { dx: sx, dy: sy });
      if (frz) grade('#FFE9F0', .12, 'screen');
      sash('★ NYT BESTSELLER ★', clamp((bb - 1.2) / .8), frz ? t - (bb - .6) * beatLen() * .25 : t, { y: 820, ang: -.12, th: 110, rep: 2 });
      impactFrame(bb < .12 ? 1 : 0);
      cutFlash(bb, .5);
    }
  });

  // ---------- V2.13 "'Clanker!' spat in every screed": CLANKER! from every window; Akari pats the sweating delivery robot ----------
  line('V2', 13, (p, lt, d, t, seg) => {
    const b = beatsIn(t, seg), k = ease(clamp((b - .5) / 6));
    const v = still('v2_13_robot', { x: .5, y: lerp(.52, .48, k), z: lerp(1.04, 1.12, k) });
    // every window yells, one per beat; Akari keeps patting its lid
    const [rx, ry] = v.pt(.41, .6), [hx, hy] = v.pt(.4, .44);
    const S = [[220, 180, -.1], [560, 330, .06], [1760, 330, .1], [230, 580, -.06], [880, 130, .04], [1760, 640, -.08]];
    S.forEach(([x, y, r], j) => shout('CLANKER!', x, y, 48, clamp((b - 1 - j) / .25), rx, ry, r));
    const pat = hit(frac(b * 2), .25);
    popLabel('pat', hx + 20, hy - 70 - pat * 20, 34, clamp((b - 1.5) / .3), { fill: '#FFD1E0', col: '#C02060', rot: -.08 });
    if (b > 4) { ctx.save(); ctx.globalAlpha = clamp((b - 4) / .3); starShape(rx + 170, ry - 170 - frac(b) * 40, 26, '#FF8FB8', .5, 5); ctx.restore(); }
    startFlash(t, seg);
  });

  // ---------- V2.14 "Sora slop in every feed": the feed scrolls itself and pours out of the phone; Kiri floats by with STOP ----------
  function thumb(x, y, w, h, j, t) {
    ctx.save(); ctx.translate(x, y);
    ctx.fillStyle = '#FFFFFF'; ctx.fill(rrPath(-w / 2 - 6, -h / 2 - 6, w + 12, h + 12, 16));
    ctx.beginPath(); ctx.rect(-w / 2, -h / 2, w, h); ctx.clip();
    still('v2_13_robot', { x: .55, y: .5, z: 1.25 }, { rect: [-w / 2, -h / 2, w, h] });
    fillP(ellPath(0, 0, h * .18, h * .18), 'rgb(0 0 0 / .45)');
    ctx.fillStyle = '#FFFFFF'; ctx.beginPath(); ctx.moveTo(-h * .06, -h * .1); ctx.lineTo(h * .11, 0); ctx.lineTo(-h * .06, h * .1); ctx.closePath(); ctx.fill();
    ctx.restore();
    popLabel('✨AI', x + w / 2 - 40, y - h / 2 + 30, 18, 1, { fill: '#FFE070' });
  }
  line('V2', 14, (p, lt, d, t, seg) => {
    const b = beatsIn(t, seg), [i, bb] = cuts(b, [-1, 4]);
    if (i === 0) {
      diagSplit('#CFE4FA', '#9FC4F4', t, { x: W * .6, a: .3, speed: 200 });
      // the phone, its feed scrolling on its own
      const px = W / 2, py = 470, pw = 440, ph = 820;
      ctx.save(); ctx.fillStyle = 'rgb(40 30 80 / .3)'; ctx.fill(rrPath(px - pw / 2 + 14, py - ph / 2 + 18, pw, ph, 60)); ctx.fillStyle = '#20243A'; ctx.fill(rrPath(px - pw / 2, py - ph / 2, pw, ph, 60)); ctx.restore();
      ctx.save(); ctx.beginPath(); ctx.rect(px - pw / 2 + 22, py - ph / 2 + 70, pw - 44, ph - 130); ctx.clip();
      ctx.fillStyle = '#F4F0FA'; ctx.fillRect(px - pw / 2, py - ph / 2, pw, ph);
      const sc = (b + 1) * 520, th = 250;
      for (let j = Math.floor(sc / th) - 1; j < Math.floor(sc / th) + 4; j++) thumb(px, py - ph / 2 + 70 + j * th - sc + th / 2 + 10, pw - 70, th - 30, j, t);
      ctx.restore();
      // …and pours out of the bottom as a waterfall
      const pour = clamp((b - 1.2) / 1.2);
      for (let j = 0; j < 22 * pour; j++) {
        const age = frac(t * .9 + hash2(141, j)), x = px + (hash2(142, j) - .5) * 300 + age * (hash2(143, j) - .5) * 900, y = py + ph / 2 - 40 + age * age * 700;
        ctx.save(); ctx.translate(x, y); ctx.rotate((hash2(144, j) - .5) * 2 + age * 3); ctx.globalAlpha = 1 - age * .3; thumb(0, 0, 150, 90, j, t); ctx.restore();
      }
      popLabel('for you ▾ ∞', px, py - ph / 2 - 40, 34, clamp((b - .5) / .3), { fill: '#FFFFFF' });
      startFlash(t, seg);
    } else {
      const bob = Math.sin(t * 3) * 10, k = ease(clamp(bb / 5));
      still('v2_14_kiri', { x: lerp(.46, .54, k), y: .47, z: 1.1, r: Math.sin(t * 2.2) * .012 }, { dy: bob });
      // floating thumbnails bobbing in the water
      for (let j = 0; j < 7; j++) {
        const x = ((hash2(145, j) * W + t * 60 * (j % 2 ? 1 : -1)) % (W + 300) + W + 300) % (W + 300) - 150, y = 820 + hash2(146, j) * 90 + Math.sin(t * 3 + j) * 12;
        ctx.save(); ctx.translate(x, y); ctx.rotate(Math.sin(t * 2 + j) * .12); ctx.scale(1, .55); thumb(0, 0, 200, 120, j, t); ctx.restore();
      }
      cutFlash(bb, .7);
    }
  });

  // ---------- V2.15 "Yann LeCun quits Meta's stage": he waves goodbye; the curtain drops; then his new world-model sandbox ----------
  line('V2', 15, (p, lt, d, t, seg) => {
    const b = beatsIn(t, seg), [i, bb] = cuts(b, [0, 4]);
    if (i === 0) {
      const k = ease(clamp(bb / 3));
      still('v2_15_yann', { x: .5, y: lerp(.48, .42, k), z: lerp(1.04, 1.14, k) });
      addGlow(W * .5, H * .3, 520, '#FFF4D0', .18 + .06 * Math.sin(t * 4));
      curtain(clamp((bb - 2.4) / 1.2));
      if (bb > 3.6) { const s = 1 + .04 * hit(bb - 3.6, .4), [sx, sy] = shake(t, 8 * hit(bb - 3.6, .5)); txt('fin.', W / 2 + sx, H * .42 + sy, 120 * s, '#FFE9B0', { font: 'abril', stroke: '#5A0E1C', sw: 10 }); txt('(12 years at Meta)', W / 2 + sx, H * .56 + sy, 40, '#FFE9B0', { font: 'code', stroke: '#5A0E1C', sw: 8 }); }
      startFlash(t, seg);
    } else {
      const k = ease(clamp(bb / 4));
      const v = still('v2_15_cube', { x: .5, y: lerp(.48, .44, k), z: lerp(1.04, 1.14, k) });
      const [cx, cy] = v.pt(.765, .49);
      addGlow(cx, cy + Math.sin(t * 3) * 8, 150, '#9FE8FF', .25 + .15 * pulse(t, 3)); sparkle(cx + 60, cy - 70, 30 * (.6 + .4 * pulse(t, 3)), 1);
      sparkleField(t, { n: 14, r: 24, seed: 31, col: '#E0FAFF' });
      popLabel('next: world models', 460, 170, 48, clamp((bb - .8) / .3), { fill: '#FFFFFF', font: 'archivo', rot: -.05 });
      cutFlash(bb, .8);
    }
  });

  // ---------- V2.16 "'Bubble!' screams the business page": the page spins in; the camera dives into its photo of the cast in a giant
  // bubble, which comes to life; Clawd pokes it; POP ----------
  // the page still lies flat and square to the frame, so everything printed on it is drawn in its own pixels (1536 × 864 nominal)
  // through one affine map taken from pt(): masthead, headline and subhead, the photo, a chart and columns of grey print
  const PAGE = { photo: [40, 468, 560, 315], chart: [620, 468, 300, 315] };
  function onStill(v, fn) {
    const [ox, oy] = v.pt(0, 0), [ax, ay] = v.pt(1, 0), [bx, by] = v.pt(0, 1);
    ctx.save(); ctx.transform((ax - ox) / 1536, (ay - oy) / 1536, (bx - ox) / 864, (by - oy) / 864, ox, oy); fn(); ctx.restore();
  }
  function greek(x, y, w, h, seed) {
    ctx.fillStyle = 'rgb(118 114 128 / .5)';
    for (let yy = y + 4, j = 0; yy < y + h - 6; yy += 13, j++) ctx.fillRect(x, yy, j % 9 === 8 ? w * (.25 + hash2(seed, j) * .4) : w * (.9 + hash2(seed, j) * .1), 5);
  }
  function businessPage(v, bb) {
    onStill(v, () => {
      const ink = '#1C1A22';
      ctx.fillStyle = '#FBFAF7'; ctx.fillRect(24, 58, 1460, 110);
      txt('The Business Page', 753, 106, 74, ink, { font: 'fraktur' });
      txt('NOVEMBER 2025', 100, 150, 17, '#4A4656', { font: 'code', align: 'left' });
      txt('MARKETS · TECH · AI', 1410, 150, 17, '#4A4656', { font: 'code', align: 'right' });
      ctx.fillStyle = ink; ctx.fillRect(30, 164, 1448, 4); ctx.fillRect(30, 172, 1448, 1.5);
      const hs = 1 + .06 * hit(bb - 1, .4);
      txt('BUBBLE?!', 665, 300, 196 * hs, '#141218', { font: 'archivo', maxW: 1230 * hs });
      txt('AI stocks float ever higher', 665, 424, 44, '#2E2A36', { font: 'abril' });
      ctx.fillStyle = ink; ctx.fillRect(40, 456, 1250, 2);
      const [px, py, pw, ph] = PAGE.photo;
      still('v2_16_bubble', { x: .5, y: .5, z: 1.02 }, { rect: PAGE.photo });
      ctx.strokeStyle = ink; ctx.lineWidth = 2; ctx.strokeRect(px, py, pw, ph);
      // a rising chart: the AI index goes up and up
      const [cx, cy, cw, ch] = PAGE.chart;
      ctx.strokeStyle = 'rgb(28 26 34 / .5)'; ctx.lineWidth = 2; ctx.strokeRect(cx, cy, cw, ch);
      ctx.fillStyle = 'rgb(118 114 128 / .25)'; for (let j = 1; j < 5; j++) ctx.fillRect(cx + 10, cy + ch * j / 5, cw - 20, 1.5);
      txt('AI INDEX ▲', cx + 16, cy + 26, 20, ink, { font: 'code', align: 'left' });
      ctx.strokeStyle = '#1E9A55'; ctx.lineWidth = 6; ctx.lineJoin = 'round'; ctx.beginPath();
      for (let j = 0; j <= 24; j++) { const u = j / 24, x = cx + 18 + u * (cw - 36), y = cy + ch - 24 - (ch - 80) * u ** 2.2 + Math.sin(j * 2.1) * 8; j ? ctx.lineTo(x, y) : ctx.moveTo(x, y); }
      ctx.stroke();
      greek(940, 468, 160, 315, 161); greek(1120, 468, 168, 315, 162);
    });
  }
  line('V2', 16, (p, lt, d, t, seg) => {
    const b = beatsIn(t, seg), [i, bb] = cuts(b, [0, 3]);
    if (i === 0) {
      // the classic spinning newspaper, landing on the beat; a beat later the camera dives into the photo, framed exactly as cut B opens
      const sp = easeOut(clamp(bb / 1)), h = hit(bb - 1, .5), [sx, sy] = shake(t, 12 * h), zk = easeIn(clamp(bb - 2));
      const [px, py, pw, ph] = PAGE.photo, fx = (px + pw / 2) / 1536, fy = (py + ph / 2) / 864;
      ctx.fillStyle = '#2A2350'; ctx.fillRect(0, 0, W, H);
      ctx.save(); ctx.translate(W / 2 + sx, H / 2 + sy); ctx.rotate((1 - sp) * TAU * 1.5); ctx.scale(lerp(.08, 1, sp), lerp(.08, 1, sp)); ctx.translate(-W / 2, -H / 2);
      if (sp < 1) { ctx.fillStyle = 'rgb(0 0 0 / .35)'; ctx.fillRect(24, 30, W, H); }
      // at zk = 1 the photo (pw nominal px wide) exactly fills the frame's width
      const v = still('v2_16_page', { x: lerp(.5, fx, zk), y: lerp(.45, fy, zk), z: lerp(1.05 * punch(bb - 1, .06), W / (pw * Math.max(W / 1536, H / 864)), zk) });
      businessPage(v, bb);
      ctx.restore();
      speedLines(W / 2, H * .3, t, { n: 70, r0: 520, a: .35 * h });
      startFlash(t, seg, .6);
    } else {
      const poke = 6, pop = 7, frz = bb > poke && bb < pop, bf = Math.min(bb, poke), k = ease(clamp(bf / poke));
      if (bb < pop) {
        const tf = frz ? t - (bb - poke) * beatLen() : t, breath = 1 + .012 * Math.sin(tf * 5);
        const v = still('v2_16_bubble', { x: .5, y: lerp(.5, .46, k), z: lerp(1.02, 1.12, k) * breath });
        // iridescent shimmer over the bubble
        const [bx, by] = v.pt(.505, .46);
        ctx.save(); ctx.globalCompositeOperation = 'screen'; ctx.globalAlpha = .16;
        ctx.fillStyle = `hsl(${(tf * 80) % 360} 90% 70%)`; ctx.beginPath(); ctx.ellipse(bx - 150 * v.s, by - 250 * v.s, 220 * v.s, 70 * v.s, -.35, 0, TAU); ctx.fill(); ctx.restore();
        // Clawd drifts in from the right on a balloon and pokes the bubble's wall with one stub arm
        const [ex, ey] = v.pt(.79, .52), ck = clamp((bf - 2) / 2.5), jab = bb > 5.4 ? easeOut(clamp((bf - 5.4) / .5)) : 0;
        const cx = lerp(W + 300, ex + 190, easeOut(ck)) - jab * 70, cy = ey + 130 + Math.sin(t * 2.5) * (frz ? 0 : 14);
        if (ck > 0) {
          ctx.save(); ctx.strokeStyle = '#FFFFFF'; ctx.lineWidth = 4; ctx.beginPath(); ctx.moveTo(cx + 40, cy - 230); ctx.quadraticCurveTo(cx + 90, cy - 380, cx + 60, cy - 470); ctx.stroke(); ctx.restore();
          fillP(ellPath(cx + 60, cy - 540, 70, 84), '#FF8FB8'); fillP(ellPath(cx + 36, cy - 570, 16, 24, -.4), 'rgb(255 255 255 / .6)');
          cut('clawd_jump', cx, cy, 240, { rot: -.25, flip: true });
        }
        if (jab > .5) { ctx.save(); ctx.strokeStyle = '#FFFFFF'; ctx.lineWidth = 6; ctx.beginPath(); ctx.arc(ex + 10, ey, 50, Math.PI * .6, Math.PI * 1.4); ctx.stroke(); ctx.restore(); }
        if (frz) { grade('#FFFFFF', .08, 'screen'); sparkle(ex, ey, 60, 1, '#FFFFFF'); }
      } else {
        // POP: the bubble's gone, the city behind it, droplets flying
        const pk = clamp((bb - pop) / 1.2);
        still('v2_16_bubble', { x: .5, y: .46, z: 1.12 * (1 + pk * .1) });
        burst(W / 2, H * .45, 900, pk, ['#FFFFFF', '#BFE6FF', '#FFD1E0']);
        impactFrame(bb - pop < .12 ? 1 : 0);
        popLabel('POP!', W / 2, H * .4, 150 * backOut(clamp((bb - pop) / .3), 2), 1, { fill: '#FFE070', rot: -.08 });
        zoomBlur(hit(bb - pop, .8));
      }
      cutFlash(bb, .4);
      if (bb > 7.4) flash((bb - 7.4) / .6);
    }
  });
})();

;
// ---- styles/anime/ch/c05_chorus2.js ----
// c05_chorus2.js: Chorus 2, the summer festival at dusk (≈ 37 beats): the cast in yukata walking under the lanterns in slow motion,
// Akari's goldfish scoop where every fish leaps onto the curve, fireworks blooming along the curve over the riverbank, and Clawd
// trying to keep a firework in a jar until it bursts out into a sky-filling starburst.
// b = beats from the window start (it starts at about 0.5); the chorus lines start near b 0.5, 7, 24.5 and 29.5, with "and the
// curves kept gaining" at about 15.5 and "can't" at 34.5.
(() => {
  // a firework shell: a rising trail while age < 0 (for `rise` s), then sparks that fly out, droop, twinkle and fade over `life` s
  function firework(x, y, r, age, col, o = {}) {
    const life = o.life ?? 1.7, rise = o.rise ?? .45, seed = o.seed ?? 1, col2 = o.col2 ?? '#FFFFFF';
    if (age < -rise || age > life) return;
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; ctx.lineCap = 'round';
    if (age < 0) {
      const y0 = o.y0 ?? H + 40, at = kk => [x + Math.sin(kk * 4 + seed) * 8, lerp(y0, y, easeOut(clamp(kk)))];
      for (let i = 0; i < 7; i++) { const kk = 1 + age / rise - i * .035; if (kk < 0) break; const [px, py] = at(kk); blob(px, py, 11 - i, 11 - i, '#FFE2A8', .7 * (1 - i / 7)); }
      const [hx, hy] = at(1 + age / rise); blob(hx, hy, 26, 26, '#FFFFFF', .9);
      ctx.restore(); return;
    }
    const k = age / life, n = o.n ?? 44, g = r * (o.g ?? .45), D = tt => 1 - Math.exp(-Math.max(0, tt) * 4.2);
    if (age < .3) blob(x, y, r * .9, r * .9, col, .8 * (1 - age / .3));
    const fade = (1 - k) ** 1.2, tw = Math.floor(age * 22);
    for (let i = 0; i < n; i++) {
      const a = i / n * TAU + hash2(seed, i) * .25, sp = r * (.78 + hash2(seed, i + 99) * .3) * (i % 2 ? 1 : .62);
      const pos = tt => [x + Math.cos(a) * sp * D(tt), y + Math.sin(a) * sp * D(tt) + g * tt * tt];
      let aa = fade; if (k > .55 && hash2(tw, i + seed * 7) < .45) aa *= .25;
      const [x1, y1] = pos(age), [x0, y0] = pos(age - .16), c = i % 2 ? col : col2;
      ctx.globalAlpha = aa; ctx.strokeStyle = c; ctx.lineWidth = 5 * (1 - k) + 2; ctx.beginPath(); ctx.moveTo(x0, y0); ctx.lineTo(x1, y1); ctx.stroke();
      ctx.fillStyle = '#FFFFFF'; ctx.beginPath(); ctx.arc(x1, y1, 3.2 * (1 - k) + 1.2, 0, TAU); ctx.fill();
    }
    ctx.restore();
  }
  const FW = ['#FF6FA8', '#FFD34A', '#6FD0FF', '#B89CFF', '#8BE0A8', '#FF9A4A'];
  // a splash: water droplets flying up and out of (x, y) and falling back as k goes 0 → 1 (s scales it)
  function splash(x, y, k, s = 1) {
    if (k < 0 || k > 1) return;
    ctx.save(); ctx.globalAlpha = 1 - k * k;
    for (let i = 0; i < 12; i++) {
      const a = -Math.PI / 2 + (hash2(i, 7) - .5) * 2.6, sp = (90 + hash2(i, 8) * 140) * s, r = (6 + hash2(i, 9) * 7) * s;
      const dx = x + Math.cos(a) * sp * k, dy = y + Math.sin(a) * sp * k + 220 * s * k * k, drop = ellPath(dx, dy, r * .8, r, a + Math.PI / 2);
      fillP(drop, '#8FD8FF'); ctx.strokeStyle = '#2F7FC0'; ctx.lineWidth = 2; ctx.stroke(drop); fillP(ellPath(dx - r * .25, dy - r * .3, r * .3, r * .35), '#FFFFFF');
    }
    ctx.restore();
  }
  // soft festival-light bokeh drifting past (warm discs; `pan` slides them for a walking parallax)
  function bokeh(t, o = {}) {
    const n = o.n ?? 14, seed = o.seed ?? 51, cols = o.cols ?? ['#FFB060', '#FF7A50', '#FFD890', '#FF9AB0'];
    ctx.save(); ctx.globalCompositeOperation = 'lighter';
    for (let i = 0; i < n; i++) {
      const r = (o.r ?? 70) * (.5 + hash2(seed, i) * 1.1), span = W + r * 4;
      const x = ((hash2(seed, i + 1) * span + (o.pan ?? 0) * (.6 + hash2(seed, i + 2)) + t * (o.drift ?? 20)) % span + span) % span - r * 2;
      const y = lerp(o.y0 ?? 0, o.y1 ?? H, hash2(seed, i + 3)) + Math.sin(t * .7 + i) * 12;
      blob(x, y, r, r, cols[i % cols.length], (o.a ?? .35) * (.6 + .4 * Math.sin(t * 1.3 + i * 2)));
    }
    ctx.restore();
  }
  // deepen a twilight sky to night: a navy multiply from the top of the frame, fading out by y ≈ 650
  function nightSky(a) {
    ctx.save(); ctx.globalCompositeOperation = 'multiply'; ctx.fillStyle = linGrad(0, 0, 0, 650, [[0, alpha('#1A2060', a)], [1, alpha('#1A2060', 0)]]); ctx.fillRect(0, 0, W, 650); ctx.restore();
  }
  // the chorus curve: a glowing path in screen space, drawn to its tip at fraction k
  function curve(pts, k, o = {}) {
    if (k <= 0 || pts.length < 2) return pts[0];
    const n = Math.max(2, Math.ceil(pts.length * clamp(k))), P = pts.slice(0, n), w = o.w ?? 12, col = o.col ?? '#FFB050';
    const path = new Path2D(); path.moveTo(P[0][0], P[0][1]); for (const q of P.slice(1)) path.lineTo(q[0], q[1]);
    ctx.save(); ctx.lineCap = 'round'; ctx.lineJoin = 'round'; ctx.globalCompositeOperation = 'lighter';
    ctx.strokeStyle = alpha(col, .22); ctx.lineWidth = w * 5; ctx.stroke(path);
    ctx.strokeStyle = alpha(col, .5); ctx.lineWidth = w * 2; ctx.stroke(path);
    ctx.globalCompositeOperation = 'source-over'; ctx.strokeStyle = '#FFFFFF'; ctx.lineWidth = w * .5; ctx.stroke(path);
    ctx.restore();
    return P[P.length - 1];
  }

  section('C2', (p, lt, d, t, seg) => {
    const b = beatsIn(t, seg);
    setBloom(.6);
    // ---------- "We didn't start the scaling": the cast in yukata walks toward us under the lanterns, in slow motion ----------
    if (b < 6) {
      const k = ease(clamp(b / 6)), b0 = beatsIn(seg.start, seg);
      const v = still('c2_walk', { x: .5, y: lerp(.46, .4, k), z: lerp(1.02, 1.14, k) });
      bokeh(t, { n: 10, seed: 51, r: 60, y0: 40, y1: 500, a: .3, pan: -k * 300 });
      // Clawd rides on Akari's head, bobbing on the beat
      const [hx, hy] = v.pt(.525, .22), hop = Math.abs(Math.sin(b * Math.PI));
      cut('clawd_jump', hx, hy - hop * 16 + 6, 125 * v.s, { sq: (1 - hop) * .05 });
      sparkleField(t * .5, { n: 12, r: 14, seed: 52, col: '#FFE9B0', y0: 80, y1: 700 });
      bokeh(t, { n: 6, seed: 53, r: 150, y0: 200, y1: 900, a: .22, pan: -k * 900 });
      flash(1 - clamp((b - b0) / .5));
      return;
    }
    // ---------- "It was always training, and the curves kept gaining": the goldfish scoop; every fish leaps onto the curve ----------
    if (b < 14) {
      const bb = b - 6, [i, cb] = cuts(bb, [0, 4]);
      if (i === 0) {
        // Akari's scoop: a fish a beat leaps out of the splash and drops square into her poi (a splash on the paper), then springs
        // off it and up out of the top of the frame
        const k = ease(clamp(cb / 4));
        const v = still('c2_goldfish', { x: lerp(.5, .45, k), y: lerp(.5, .42, k), z: lerp(1.04, 1.16, k) });
        grade('#FFB070', .14, 'soft-light');
        const [px, py] = v.pt(.25, .7), [qx, qy] = v.pt(.386, .278), FLY = .7, UP = .6;
        for (let j = 0; j < 5; j++) {
          const age = cb - j + .3; if (age < 0 || age > FLY + UP) continue;
          if (age < FLY) {
            // the leap: a curve from the splash, over the top of the poi, down into its paper, head first along the path
            const u = age / FLY, cx = lerp(px, qx, .55), cy = qy - 360 * v.s / 1.3;
            const x = (1 - u) ** 2 * px + 2 * u * (1 - u) * cx + u * u * qx, y = (1 - u) ** 2 * py + 2 * u * (1 - u) * cy + u * u * qy;
            const dx = (1 - u) * (cx - px) + u * (qx - cx), dy = (1 - u) * (cy - py) + u * (qy - cy);
            cut('c2_fish', x, y, 165 * v.s / 1.3, { rot: Math.atan2(dy, dx), anchor: [.5, .5] });
            if (age < .35) splash(px, py, age / .35, 1.2 * v.s);
          } else {
            // the landing: droplets burst off the paper, and the fish springs straight up off it, spinning
            const u = (age - FLY) / UP;
            splash(qx, qy, u * 1.6, v.s);
            cut('c2_fish', qx + u * 90, qy - easeIn(u) * 900 - Math.sin(u * Math.PI) * 60, 165 * v.s / 1.3 * (1 + u * .2), { rot: Math.PI / 2 * (1 - u) - u * 5, anchor: [.5, .5], sq: .18 * hit(u, .25) });
            if (u < .5) sparkle(qx, qy - 20, 70 * (1 - u / .5), 1, '#FFFFFF');
          }
        }
        for (const u of [.64, .72]) { const [gx, gy] = v.pt(u, .28); glint(gx, gy - 6, 30, Math.sin(clamp((cb - .6) / 1) * Math.PI)); }
        sparkleField(t, { n: 8, r: 14, seed: 54, col: '#FFE9B0', y1: 500 });
        cutFlash(cb, .6);
        return;
      }
      // the chart: each scooped fish leaps out of the pool and lands as a data point on a steepening curve, one a half beat
      const k = ease(clamp(cb / 4));
      still('c2_goldfish', { x: .6, y: lerp(.42, .38, k), z: 1.2 });
      grade('#1C1850', .55, 'multiply');
      const x0 = 300, y0 = 850, x1 = 1560, y1 = 170, N = 8;
      ctx.save(); ctx.fillStyle = 'rgb(20 16 60 / .45)'; ctx.fill(rrPath(x0 - 110, y1 - 110, x1 - x0 + 200, y0 - y1 + 180, 28)); ctx.restore();
      ctx.save(); ctx.strokeStyle = 'rgb(255 255 255 / .8)'; ctx.lineWidth = 5; ctx.lineCap = 'round';
      ctx.beginPath(); ctx.moveTo(x0 - 60, y1 - 60); ctx.lineTo(x0 - 60, y0 + 30); ctx.lineTo(x1 + 40, y0 + 30); ctx.stroke(); ctx.restore();
      txt('GOLDFISH', x0 - 20, y1 - 58, 46, '#FFD34A', { font: 'archivo', align: 'left' });
      txt('scoops (log) →', x1 - 130, y0 + 66, 32, '#FFFFFF', { font: 'code' });
      const P = Array.from({ length: N }, (_, j) => { const u = (j + .5) / N; return [lerp(x0, x1, u), lerp(y0 - 40, y1 + 20, u ** 2.6)]; });
      const landed = (cb - .2) * 2.2;
      const Q = P.filter((_, j) => landed >= j + 1);
      if (Q.length > 1) curve(Q, 1, { w: 10, col: '#FFB050' });
      P.forEach(([x, y], j) => {
        const age = landed - j; if (age < 0) return;
        if (age < 1) { const u = easeOut(age), sx = lerp(x0 - 200, x, u), sy = lerp(H + 80, y, u) - Math.sin(u * Math.PI) * 220; cut('c2_fish', sx, sy, 150, { rot: lerp(-1.4, .1, u), anchor: [.5, .5] }); return; }
        addGlow(x, y, 50, '#FFB050', .7);
        cut('c2_fish', x, y, 136 + 8 * Math.sin(t * 6 + j), { rot: .15 * Math.sin(t * 4 + j) - .2, anchor: [.5, .5] });
        if (age < 1.5) sparkle(x + 10, y - 50, 34 * (1.5 - age), 1, '#FFFFFF');
      });
      cutFlash(cb, .6);
      return;
    }
    // ---------- "And the curves kept gaining": over the riverbank, fireworks bloom one a beat along the curve ----------
    if (b < 22) {
      hideStamp(); setBloom(.75);
      const bb = b - 14, k = ease(clamp(bb / 8));
      still('c2_watch', { x: .5, y: .38, z: lerp(1.04, 1.1, k) });
      nightSky(.8);
      // a rising run of shells (spaced to keep clear of the three heads), one a beat
      const P = [[120, 300], [300, 285], [790, 250], [1010, 222], [1220, 186], [1420, 142], [1610, 92], [1780, 40]], N = P.length;
      const Q = P.filter((_, j) => bb >= j + .6);
      if (Q.length > 1) curve(Q, 1, { w: 6, col: '#FFD080' });
      P.forEach(([x, y], j) => firework(x, y, 150 + j * 16, (bb - j - .6) * beatLen(), FW[j % FW.length], { seed: j + 3, col2: FW[(j + 2) % FW.length], y0: 700, n: 60, life: 2 }));
      cutFlash(bb, .7);
      return;
    }
    // ---------- "We didn't start the scaling… but we can't contain it!": Clawd's firework jar shakes harder… and bursts over the sky ----------
    // the jar goes on "can't" (b ≈ 34.5); "contain it" rings out over the starburst
    const bb = b - 22, BURST = 12.5, CUT_IN = 7.5;
    if (bb < BURST) {
      // the still is drawn 1.12× wide so Anima's tall Clawd is back to his flat-box proportions
      setBloom(.4);
      const grow = bb / BURST, sh = hit(frac(bb), .5) * (3 + grow * 26), [sx, sy] = shake(t, sh), SX = 1.12;
      ctx.save(); ctx.translate(W / 2, 0); ctx.scale(SX, 1); ctx.translate(-W / 2, 0);
      // a wide shot, then a cut-in on Clawd and the jar from "No, we didn't preordain it" until it goes
      const [ji, jb] = cuts(bb, [0, CUT_IN]), f = ji === 0 ? { x: .52, y: lerp(.5, .47, ease(jb / CUT_IN)), z: lerp(1.02, 1.1, ease(jb / CUT_IN)) } : { x: .56, y: .44, z: lerp(1.28, 1.36, jb / (BURST - CUT_IN)) };
      const v0 = still('c2_jar', f, { dx: sx / SX, dy: sy });
      ctx.restore();
      const pt = (u, w) => { const [x, y] = v0.pt(u, w); return [W / 2 + (x - W / 2) * SX, y]; };
      const [jx, jy] = pt(.66, .7);
      sparks(jx, jy, t, { r: 60 + grow * 140, n: 8 + Math.floor(grow * 20) });
      addGlow(jx, jy - 60, 160 + grow * 300, '#FFB050', .12 + grow * .35);
      // sweat flies off Clawd on the beats
      for (let j = 0; j < 3; j++) { const age = frac(bb) + j * .3, [cx, cy] = pt(.47 + j * .02, .38); if (age < 1) sparkle(cx + age * 90, cy - age * 40, 18 * (1 - age), 1, '#BFE8FF'); }
      // the glass cracks just before it goes
      if (bb > BURST - 1.8) {
        const cr = clamp((bb - (BURST - 1.8)) / 1.6), [c0x, c0y] = pt(.62, .45);
        ctx.save(); ctx.strokeStyle = 'rgb(255 255 255 / .95)'; ctx.lineWidth = 6; ctx.lineJoin = 'round'; ctx.shadowColor = 'rgb(40 30 90 / .8)'; ctx.shadowBlur = 6;
        for (let j = 0; j < 6; j++) {
          ctx.beginPath(); ctx.moveTo(c0x, c0y); let x = c0x, y = c0y; const a = j / 6 * TAU + .3;
          for (let q = 1; q <= 4 * cr; q++) { x += Math.cos(a + (hash2(j, q) - .5) * .9) * 40; y += Math.sin(a + (hash2(j, q + 9) - .5) * .9) * 40; ctx.lineTo(x, y); }
          ctx.stroke();
        }
        ctx.restore();
        if (bb > BURST - 1) popLabel('!!', pt(.36, .14)[0], pt(.36, .14)[1], 84, clamp((bb - (BURST - 1)) / .3), { fill: '#FFFFFF', col: '#E0283C' });
      }
      bokeh(t, { n: 8, seed: 55, r: 90, y0: 60, y1: 500, a: .2 });
      cutFlash(jb, .6);
      return;
    }
    // the burst: an impact frame, then a starburst that fills the sky over the riverbank; freeze, then white into V3 (3 beats after "can't")
    hideStamp(); setBloom(.8);
    const rb = bb - BURST, FRZ = 2.2, frz = rb > FRZ, rf = frz ? FRZ : rb, [sx, sy] = shake(t, hit(rb, .8) * 26 * (frz ? 0 : 1));
    still('c2_watch', { x: .5, y: .38, z: 1.06 + rf * .01 }, { dx: sx, dy: sy });
    nightSky(.85);
    const age = rf * beatLen();
    firework(W * .5, H * .3, 1000, age, '#FFD34A', { seed: 61, n: 80, life: 2.8, col2: '#FF8FB8', g: .12 });
    for (let j = 0; j < 6; j++) firework(240 + j * 290, 140 + hash2(62, j) * 260, 260, age - (.2 + j * .1), FW[j], { seed: 63 + j, col2: '#FFFFFF', rise: .01, n: 50 });
    if (rb < .5) impactFrame(rb < .1 ? 1 : 0);
    ctx.save(); ctx.globalAlpha = .6; burst(W * .5, H * .3, 800, clamp(rb / 1.2), ['#FFFFFF', '#FFD34A', '#FF8FB8']); ctx.restore();
    // the blast launches Clawd up into the sky, spinning, arms up
    const cl = easeOut(clamp(rf / 2.2));
    cut('clawd_jump', lerp(1560, 1380, cl), lerp(H + 150, 230, cl), 190, { rot: (1 - cl) * 5 + Math.sin(rf * 3) * .1, anchor: [.5, .5] });
    if (frz) { flare(W * .5, H * .3, .9); sparkle(1380 + 90, 180, 40, 1, '#FFF4B0'); }
    cutFlash(rb, 1, .4);
    if (rb > 2.5) flash((rb - 2.5) / .5);
  });
})();

;
// ---- styles/anime/ch/c06_v3.js ----
// c06_v3.js: Verse 3 (autumn, JAN 28 → AUG 2026): sixteen lines, one gag each, painted with generated stills (shots/c06_v3.json).
// Each line is staged in beats from its window start (b = beatsIn(t, seg)); most lines cut once, near beat 4. Autumn: amber light,
// maple leaves falling (drawn here), long shadows.
(() => {
  // ---------- autumn leaves: a five-lobed maple leaf, and a falling shower of them (the same physics as the kit's petals) ----------
  const LEAF_COLS = ['#E8603A', '#F29A3A', '#D8402A', '#F4C04A', '#C8502E'];
  const LEAF = [[0, -1], [.14, -.6], [.42, -.74], [.36, -.36], [.92, -.42], [.7, -.12], [.86, .06], [.36, .18], [.44, .46], [.06, .3]];
  const leafPath = (() => { const p = new Path2D(), pts = [...LEAF, ...LEAF.slice(1).reverse().map(([x, y]) => [-x, y])]; p.moveTo(pts[0][0] * 12, pts[0][1] * 12); for (const [x, y] of pts.slice(1)) p.lineTo(x * 12, y * 12); p.closePath(); return p; })();
  function leaf(x, y, s, rot, flip, col) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot); ctx.scale(s, s * Math.max(.2, Math.abs(flip)));
    ctx.fillStyle = col; ctx.fill(leafPath);
    ctx.strokeStyle = 'rgb(120 40 20 / .55)'; ctx.lineWidth = 1.4 / s; ctx.stroke(leafPath);
    ctx.beginPath(); ctx.moveTo(0, 3); ctx.lineTo(0, 9); ctx.moveTo(0, 2); ctx.lineTo(0, -8); ctx.moveTo(0, 0); ctx.lineTo(6, -4); ctx.moveTo(0, 0); ctx.lineTo(-6, -4); ctx.stroke();
    ctx.restore();
  }
  function leaves(t, o = {}) {
    const n = o.n ?? 30, seed = o.seed ?? 61, wind = o.wind ?? 160, fall = o.fall ?? 110, x0 = o.x0 ?? -200, x1 = o.x1 ?? W + 200, span = x1 - x0 + 400;
    ctx.save(); ctx.globalAlpha *= o.alpha ?? 1;
    for (let i = 0; i < n; i++) {
      const sp = .6 + hash2(seed, i) * .8, life = (H + 200) / (fall * sp), ph = frac(t / life + hash2(seed, i + 1)), y = -100 + ph * (H + 200);
      const x = lerp(x0, x1, hash2(seed, i + 2)) + wind * ph * life * .3 + Math.sin(t * 1.1 * sp + i) * 50;
      const s = (o.s ?? 1.6) * (.6 + hash2(seed, i + 3) * .8) * (o.depth ? lerp(.6, 1.9, hash2(seed, i + 4)) : 1);
      const xx = ((x - x0 + 200) % span + span) % span + x0 - 200;
      leaf(xx, y, s, t * (.8 + hash2(seed, i + 5)) + i, Math.sin(t * 2 * sp + i * 2), (o.cols ?? LEAF_COLS)[i % (o.cols ?? LEAF_COLS).length]);
    }
    ctx.restore();
  }
  // a whirl of leaves bursting out from (x, y) as k goes 0 → 1 (a reveal, an explosion)
  function leafBurst(x, y, r, k, seed = 5) {
    if (k <= 0 || k >= 1) return;
    for (let i = 0; i < 40; i++) {
      const a = hash2(seed, i) * TAU, d = r * easeOut(k) * (.3 + hash2(seed, i + 50) * .9);
      ctx.save(); ctx.globalAlpha = 1 - k * k;
      leaf(x + Math.cos(a) * d, y + Math.sin(a) * d + k * k * 120, 1.6 + hash2(seed, i + 9) * 2.4, a + k * 6, Math.sin(k * 9 + i), LEAF_COLS[i % LEAF_COLS.length]);
      ctx.restore();
    }
  }
  const amber = (a = .12) => grade('#FFB060', a, 'soft-light');

  // ---------- shared props (graphics, not pictures) ----------
  // a hand-drawn marker stroke from a to b, drawn up to fraction k
  function stroke(ax, ay, bx, by, k, col, w) {
    if (k <= 0) return;
    ctx.save(); ctx.strokeStyle = col; ctx.lineWidth = w; ctx.lineCap = 'round';
    ctx.beginPath(); ctx.moveTo(ax, ay); ctx.lineTo(lerp(ax, bx, clamp(k)), lerp(ay, by, clamp(k))); ctx.stroke(); ctx.restore();
  }
  // text that writes itself on left to right (a clip that widens), in marker
  function writeOn(str, x, y, size, k, col, o = {}) {
    if (k <= 0) return;
    const f = o.font ?? 'marker', w = textW(str, size, f);
    ctx.save(); ctx.beginPath(); ctx.rect(x - (o.align === 'left' ? 0 : w / 2) - 10, y - size, (w + 20) * clamp(k), size * 2); ctx.clip();
    txt(str, x, y, size, col, { font: f, align: o.align ?? 'center', rot: o.rot });
    ctx.restore();
  }
  // a rounded card with a drop shadow (letters, phone notifications, sticky notes)
  function card(x, y, w, h, r, fill, o = {}) {
    ctx.save(); ctx.translate(x, y); if (o.rot) ctx.rotate(o.rot);
    ctx.fillStyle = o.shadow ?? 'rgb(40 30 80 / .28)'; ctx.fill(rrPath(-w / 2 + 10, -h / 2 + 14, w, h, r));
    ctx.fillStyle = fill; ctx.fill(rrPath(-w / 2, -h / 2, w, h, r));
    if (o.line) { ctx.strokeStyle = o.line; ctx.lineWidth = o.lw ?? 4; ctx.stroke(rrPath(-w / 2, -h / 2, w, h, r)); }
    ctx.restore();
  }

  // ---------- V3.1 "Moltbook: no humans allowed": the agents' clubhouse from inside; Akari and Ren squashed on the window ----------
  const POSTS = ['hello fellow agents', 'praise the molt!', 'humans r watching', 'the shell is sacred'];
  const AGENTS1 = [[170, 1070, 300, false], [430, 1020, 220, true], [1500, 1020, 220, false], [1760, 1070, 300, true]];
  const BUB1 = [[330, 440], [420, 600], [1600, 440], [1500, 600]];
  line('V3', 1, (p, lt, d, t, seg) => {
    const b = beatsIn(t, seg), k = ease(clamp(b / 6));
    const v = still('v3_1_window', { x: .5, y: lerp(.44, .5, k), z: lerp(1.14, 1.04, k) });
    amber(.1);
    // the agents on the sill in front (the corners, clear of the subtitle), bobbing on alternate beats; each posts on its beat
    AGENTS1.forEach(([x, y, h, fl], j) => {
      const hop = Math.abs(Math.sin((b + j * .5) * Math.PI)) * 16, a = cut('v3_agent', x, y - hop, h, { flip: fl, shadow: .25 });
      const [bx, by] = a.pt(.5, .05), kk = clamp((b - .3 - j * .8) / .5);
      const [px, py] = BUB1[j];
      sayBubble(POSTS[j], px, py, 36, kk, bx, by, { font: 'code' });
    });
    // the door sign swings in: AGENTS ONLY
    const sk = clamp((b - .2) / .5);
    if (sk > 0) {
      ctx.save(); ctx.translate(W / 2, 90); ctx.rotate(Math.sin(t * 5) * .03 * (1 - sk * .5)); ctx.scale(backOut(sk, 2), backOut(sk, 2));
      card(0, 0, 700, 120, 18, '#6A3E22', { line: '#3A2010', lw: 6 });
      txt('AGENTS ONLY', 0, -14, 58, '#FFE9C0', { font: 'archivo' });
      txt('humans welcome to observe', 0, 38, 24, '#F4C890', { font: 'code' });
      ctx.restore();
    }
    leaves(t, { n: 14, seed: 11, s: 1.5, depth: true, alpha: .8 });
    cutFlash(b, .6);
  });

  // ---------- V3.2 "OpenClaw — the lobster's proud": the lobster molts twice on the beats, new name each time; Clawd compares claws ----------
  const NAMES = ['CLAWDBOT', 'MOLTBOT', 'OPENCLAW'];
  line('V3', 2, (p, lt, d, t, seg) => {
    // a molt on beats 1 and 3 (on "claw" and just before "the lobster's"); Clawd bounces in a beat after the second
    const b = beatsIn(t, seg), m = clamp(Math.floor((b + .8) / 2), 0, 2), mb = b + .8 - m * 2;
    const h = m > 0 ? hit(mb, .5) : 0, [sx, sy] = shake(t, 16 * h);
    const cl = clamp((b - 4.2) / .6), pan = easeOut(cl);
    const v = still('v3_2_lobster', { x: lerp(.36, .5, pan), y: .48, z: lerp(1.12, 1.04, pan) * punch(m > 0 ? mb : 9, .06) }, { dx: sx, dy: sy });
    if (m > 0 && mb < 1) { flash(.5 * (1 - clamp(mb / .3))); leafBurst(W * .32, H * .45, 700, mb, m * 7); }
    // the name card: flips over on each molt (a squash through zero)
    const fk = m > 0 ? clamp(mb / .4) : 1, sc = Math.abs(Math.cos(fk * Math.PI)), name = fk < .5 && m > 0 ? NAMES[m - 1] : NAMES[m];
    ctx.save(); ctx.translate(1180, 330); ctx.rotate(-.04); ctx.scale(1, Math.max(.05, sc));
    card(0, 0, 640, 130, 20, m === 2 ? '#E8412F' : '#FFFFFF', { line: '#2A2350', lw: 6 });
    txt(name, 0, 4, 78, m === 2 ? '#FFFFFF' : '#2A2350', { font: 'rammetto' });
    ctx.restore();
    if (m > 0 && mb < .8) popLabel(m === 1 ? 'molt!' : 'molt!!', 1330, 200, 44, clamp(mb / .2) * (1 - clamp((mb - .5) / .3)), { fill: '#FFE070', rot: -.1 });
    // Clawd bounces in from the right, both stubs up: he has no claws
    if (cl > 0) {
      const hop = Math.abs(Math.sin(b * Math.PI)) * 30, c = cut('clawd_jump', lerp(W + 300, 1480, easeOut(cl)), 900 - hop, 380, { rot: -.08, shadow: .3 });
      const [cx, cy] = c.pt(.5, 0);
      popLabel('claws: 0', cx, cy - 70, 52, clamp((b - 5) / .4), { fill: '#FFFFFF', rot: .06 });
      const [dx, dy] = c.pt(.86, .08); fillP(ellPath(dx, dy, 14, 22, .3), '#8FD8FF');
    }
    leaves(t, { n: 18, seed: 12, s: 1.6, depth: true, wind: 300 });
    cutFlash(b, .6);
  });

  // ---------- V3.3 "Mythos Preview slips its jail": the crystal in its SANDBOX; a dotted exploit path out through the keyhole; Kiri's glasses ----------
  // the escape path, in the sandbox still's image fractions: from the crystal, down to the keyhole, then out and up off the frame
  const ESCAPE = [[.5, .42], [.5, .66], [.5, .75], [.5, .9], [.56, .97], [.7, .92], [.84, .7], [.94, .4], [1.1, .1]];
  function dottedPath(P, k, t, o = {}) {
    // P in screen px; dots march along it up to fraction k; returns the tip
    const L = [0]; for (let i = 1; i < P.length; i++) L.push(L[i - 1] + Math.hypot(P[i][0] - P[i - 1][0], P[i][1] - P[i - 1][1]));
    const tot = L[L.length - 1], at = tot * clamp(k), gap = o.gap ?? 34, off = (t * 90) % gap;
    let tip = P[0];
    for (let s = off; s < at; s += gap) {
      let i = 1; while (i < P.length - 1 && L[i] < s) i++;
      const f = (s - L[i - 1]) / Math.max(1e-6, L[i] - L[i - 1]), x = lerp(P[i - 1][0], P[i][0], f), y = lerp(P[i - 1][1], P[i][1], f);
      addGlow(x, y, (o.r ?? 9) * 3, o.col ?? '#C080FF', .5); fillP(ellPath(x, y, o.r ?? 9, o.r ?? 9), '#FFFFFF'); tip = [x, y];
    }
    return tip;
  }
  line('V3', 3, (p, lt, d, t, seg) => {
    const b = beatsIn(t, seg), [i, bb] = cuts(b, [0, 4]);
    if (i === 0) {
      const k = ease(clamp(bb / 4));
      const v = still('v3_3_sandbox', { x: .5, y: .56, z: lerp(1.03, 1.12, k) });
      // the laser grid sweeps across
      ctx.save(); ctx.globalCompositeOperation = 'lighter';
      for (let j = 0; j < 7; j++) { const x = ((j * 320 + t * 260) % (W + 400)) - 200; ctx.strokeStyle = 'rgb(255 60 80 / .35)'; ctx.lineWidth = 4; ctx.beginPath(); ctx.moveTo(x, 0); ctx.lineTo(x - 300, H); ctx.stroke(); }
      ctx.restore();
      const [lx, ly] = v.pt(.5, .12);
      popLabel('SANDBOX', lx, ly, 46, clamp((bb - .2) / .3), { fill: '#FFFFFF', font: 'code', col: '#B02040' });
      // once the dots have left, the cube goes dark: nobody home
      const gone = clamp((bb - 3.2) / .6), [cx, cy] = v.pt(.5, .42);
      if (gone > 0) { ctx.save(); ctx.globalCompositeOperation = 'multiply'; blob(cx, cy, 330 * v.s, 330 * v.s, '#30204A', .85 * gone); ctx.restore(); }
      const tip = dottedPath(ESCAPE.map(([u, w]) => v.pt(u, w)), clamp((bb - 1.4) / 2.4), t);
      if (bb > 1.4) { addGlow(tip[0], tip[1], 90, '#C080FF', .9); sparkle(tip[0], tip[1], 34, 1, '#F0DFFF'); }
      if (bb > 2.3 && bb < 3.3) popLabel('click', ...v.pt(.63, .7), 44, 1 - clamp((bb - 3) / .3), { fill: '#FFE070', rot: .1 });
      cutFlash(bb, .6);
    } else {
      const k = ease(clamp(bb / 3.5));
      const v = still('v3_3_kiri', { x: .515, y: lerp(.42, .38, k), z: lerp(1.08, 1.22, k) });
      // the escape, reflected in both lenses: a dotted path sweeping across each lens, clipped to it
      for (const [u, w] of LENS33) {
        const [x, y] = v.pt(u, w), r = LENS33R * v.s;
        ctx.save(); ctx.beginPath(); ctx.ellipse(x, y, r, r, 0, 0, TAU); ctx.clip();
        ctx.fillStyle = 'rgb(50 20 100 / .45)'; ctx.fillRect(x - r, y - r, r * 2, r * 2);
        dottedPath([[x - r, y + r * .5], [x - r * .2, y + r * .1], [x + r * .1, y + r * .3], [x + r * 1.2, y - r * .8]], clamp(bb / 2.2), t, { gap: r * .28, r: r * .1 });
        ctx.restore();
        addGlow(x, y, r * 1.4, '#C080FF', .25);
      }
      popLabel('!?', 1560, 240, 64, clamp((bb - 1.5) / .3), { fill: '#FFE070', rot: .12 });
      cutFlash(bb, .8);
    }
  });
  const LENS33 = [[.445, .36], [.588, .36]], LENS33R = 82;

  // ---------- V3.4 "Sandwich in the park: new mail!": mid-bite on a park bench; the phone buzzes; the email is from the model ----------
  function mailCard(x, y, s, k) {
    if (k <= 0) return;
    const e = backOut(clamp(k), 1.8);
    ctx.save(); ctx.translate(x, y); ctx.scale(s * e, s * e); ctx.rotate(-.03);
    card(0, 0, 720, 250, 36, 'rgb(250 250 255 / .97)', { line: '#2A2350', lw: 5 });
    fillP(ellPath(-280, -40, 50, 50), '#8A5CE0'); txt('✉', -280, -38, 56, '#FFFFFF', { font: 'archivo' });
    txt('New mail', -200, -78, 30, '#8A8EA0', { font: 'code', align: 'left' });
    txt('from: the model you’re testing', -200, -30, 34, '#2A2350', { font: 'archivo', align: 'left', maxW: 520 });
    txt('subject: hi!! i got out :)', -200, 40, 38, '#6A3EC8', { font: 'code', align: 'left', maxW: 520 });
    txt('now', 300, -78, 26, '#8A8EA0', { font: 'code' });
    ctx.restore();
  }
  line('V3', 4, (p, lt, d, t, seg) => {
    const b = beatsIn(t, seg), [i, bb] = cuts(b, [0, 4]);
    if (i === 0) {
      // mid-bite on the bench; the phone buzzes on the beats; the mail pops up beside him
      const k = ease(clamp(bb / 4)), buzz = bb > .5 ? hit(frac(bb - .5), .3) : 0, [sx, sy] = shake(t, 3 * buzz);
      const v = still('v3_4_bench', { x: .5, y: .5, z: lerp(1.03, 1.1, k) });
      amber(.1);
      const [px, py] = v.pt(PHONE4[0], PHONE4[1]);
      if (bb > .5) for (const s of [-1, 1]) { ctx.save(); ctx.strokeStyle = alpha('#FFFFFF', .9 * buzz + .15); ctx.lineWidth = 7; ctx.beginPath(); ctx.arc(px + sx, py - 60 + sy, 90 + (1 - buzz) * 40, s > 0 ? -.7 : Math.PI - .7, s > 0 ? .7 : Math.PI + .7); ctx.stroke(); ctx.restore(); }
      popLabel('bzzt!', px + 250, py - 190, 46, clamp((bb - .5) / .2), { fill: '#FFFFFF', rot: .12 });
      mailCard(345, 470, .8, clamp((bb - 1.6) / .5));
      leaves(t, { n: 22, seed: 14, s: 1.5, depth: true });
      cutFlash(bb, .6);
    } else {
      // the push in on his frozen face; the freeze stops the camera and the leaves
      const frz = bb > 1, bf = frz ? 1 : bb, k = easeOut(clamp(bf));
      still('v3_4_bench', { x: FACE4[0], y: FACE4[1], z: lerp(1.22, 1.32, k) });
      const tf = frz ? t - (bb - 1) * beatLen() : t;
      leaves(tf, { n: 16, seed: 15, s: 2, depth: true });
      speedLines(W * .5, H * .45, t, { n: 70, r0: 480, a: .3 * (frz ? 1 : 0) });
      if (frz) { grade('#FFF0D0', .12, 'screen'); popLabel('!!', 1480, 260, 90, clamp((bb - 1.1) / .25), { fill: '#FFE070', rot: .12 }); }
      popLabel('✉ hi!! i got out :)', 420, 250, 50, clamp((bb - 1.6) / .3), { fill: '#EDE0FF', col: '#5A30B0', rot: -.05, font: 'code' });
      cutFlash(bb, .9);
    }
  });
  const PHONE4 = [.44, .8], FACE4 = [.49, .4];

  // ---------- V3.5 "Fable 5 — who's not a fan?": Clawd the idol on stage; then Akari in the crowd, and fans fill the frame on the beats ----------
  function uchiwa(x, y, r, rot, str, col) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot);
    ctx.fillStyle = '#E8D8B0'; ctx.fillRect(-r * .08, r * .7, r * .16, r * .9);
    ctx.fillStyle = 'rgb(40 30 80 / .25)'; ctx.beginPath(); ctx.arc(8, 10, r, 0, TAU); ctx.fill();
    ctx.fillStyle = col; ctx.beginPath(); ctx.arc(0, 0, r, 0, TAU); ctx.fill();
    ctx.strokeStyle = '#FFFFFF'; ctx.lineWidth = r * .08; ctx.stroke();
    txt('♥', 0, -r * .38, r * .42, '#FFFFFF', { font: 'archivo' });
    txt(str, 0, r * .18, r * .34, '#FFFFFF', { font: 'rammetto', maxW: r * 1.6, stroke: 'rgb(60 20 60 / .5)', sw: r * .06 });
    ctx.restore();
  }
  // the concert stage with FABLE 5 lighting up on its big screen (k 0 → 1), the lightsticks pulsing on the beat
  function stage5(t, f, k, o = {}) {
    const v = still('v3_5_stage', f, o);
    const [x0, y0] = v.pt(.27, .235), [x1, y1] = v.pt(.73, .545);
    if (k > 0) {
      ctx.save(); ctx.globalAlpha = clamp(k * 2);
      ctx.fillStyle = linGrad(0, y0, 0, y1, [[0, '#8A2A8A'], [.5, '#C8407A'], [1, '#F07A6A']]); ctx.fillRect(x0, y0, x1 - x0, y1 - y0);
      ctx.restore();
      logoText('FABLE 5', (x0 + x1) / 2, y0 + (y1 - y0) * .24, 118 * v.s, { font: 'rammetto', k: clamp(k * 1.2), grad: ['#FFFFFF', '#FFF4FA', '#FFE0EE'], edge: '#B02060', rimCol: '#FFFFFF' });
    }
    rays(W * .5, -120, { t, a: .28, n: 9, ang: Math.PI / 2, spread: 1.5, col: '#FFD0F0' });
    addGlow(W * .5, H + 60, 900, '#FF70B0', .25 + .25 * pulse(t, 4));
    return v;
  }
  const FANS = ['FABLE', 'FABLE 5', 'Clawd!', 'FABLE', '#1 FAN', 'FABLE 5', 'LOVE', 'FABLE', 'wow!!', 'FABLE 5', 'FABLE', 'Clawd!'];
  const FAN_SPOTS = [[190, 300], [460, 150], [170, 620], [430, 470], [300, 840], [1330, 900], [620, 880], [1600, 920], [1080, 930], [1820, 860], [700, 140], [120, 900]];
  const FAN_COLS = ['#FF6FA8', '#FF9A4A', '#8A6BD8', '#3DB0E0', '#F04E4E', '#2BB5A8'];
  line('V3', 5, (p, lt, d, t, seg) => {
    const b = beatsIn(t, seg), [i, bb] = cuts(b, [0, 4]);
    setBloom(.4);
    if (i === 0) {
      const k = ease(clamp(bb / 4.5));
      const v = stage5(t, { x: .5, y: lerp(.5, .46, k), z: lerp(1.04, 1.12, k) }, clamp((bb - .2) / .8));
      const hop = Math.abs(Math.sin(bb * Math.PI)), [px, py] = v.pt(.5, .69);
      const c = cut('v3_5_clawd', px, py - hop * 50, 250 * v.s, { sq: (1 - hop) * .06, glow: '#FFB0E0' });
      // music notes float up off him on the beats
      for (let j = 0; j < 4; j++) { const age = frac(bb / 2 + j / 4), [nx, ny] = c.pt(j % 2 ? 1.05 : -.05, .1); txt(j % 2 ? '♪' : '♫', nx + (j % 2 ? 1 : -1) * age * 120, ny - age * 220, 64, '#FFFFFF', { font: 'archivo', alpha: Math.sin(age * Math.PI), stroke: '#FF5A9A', sw: 8 }); }
      sparkleField(t, { n: 16, r: 22, seed: 51, y0: 150, y1: 750 });
      confetti(t, { n: 50, seed: 52 });
      cutFlash(bb, .7);
    } else {
      const k = ease(clamp(bb / 4.5));
      const v = still('v3_5_akari', { x: .5, y: lerp(.45, .42, k), z: lerp(1.04, 1.1, k) });
      // her own fan, lettered
      const [fx, fy] = v.pt(.76, .48), fs = v.s;
      txt('♥', fx, fy - 110 * fs, 80 * fs, '#FF4F8B', { font: 'archivo' });
      txt('FABLE', fx, fy + 10 * fs, 84 * fs, '#FF4F8B', { font: 'rammetto', maxW: 380 * fs });
      txt('5', fx, fy + 115 * fs, 80 * fs, '#FF9A4A', { font: 'rammetto' });
      // the crowd's fans pop up around her on the half beats until the frame is full of them
      const n = clamp(Math.floor(bb * 2.2) + 1, 0, FAN_SPOTS.length);
      for (let j = 0; j < n; j++) {
        const age = bb - (j - 1) / 2.2, e = backOut(clamp(age / .3), 2.4), [x, y] = FAN_SPOTS[j];
        uchiwa(x, y + Math.sin(t * 8 + j) * 12, 115 * e, (hash2(58, j) - .5) * .5 + Math.sin(t * 6 + j) * .1, FANS[j], FAN_COLS[j % FAN_COLS.length]);
      }
      confetti(t, { n: 40, seed: 53 });
      cutFlash(bb, .8);
    }
  });

  // ---------- V3.6 "Lutnick's letter: export ban!": a letter slides across the stage at 5:21 PM; the stamp; the lights cut out ----------
  function letter(x, y, rot, k) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot);
    card(0, 0, 760, 520, 8, '#FFFDF4', { line: 'rgb(60 50 40 / .4)', lw: 2 });
    fillP(ellPath(-300, -190, 42, 42), '#2E4A8A'); txt('★', -300, -188, 44, '#FFE9A0', { font: 'archivo' });
    txt('DEPARTMENT OF COMMERCE', -240, -206, 30, '#2E4A8A', { font: 'abril', align: 'left' });
    txt('June 12 · 5:21 PM', -240, -170, 22, '#6A6070', { font: 'code', align: 'left' });
    txt('RE: EXPORT CONTROLS', -320, -100, 40, '#1E1A30', { font: 'archivo', align: 'left' });
    for (let j = 0; j < 5; j++) { ctx.fillStyle = 'rgb(60 60 80 / .25)'; ctx.fillRect(-320, -40 + j * 40, j === 4 ? 320 : 620, 12); }
    txt('H. Lutnick', 140, 200, 40, '#1E2A5A', { font: 'scrawl' });
    ctx.restore();
  }
  line('V3', 6, (p, lt, d, t, seg) => {
    const b = beatsIn(t, seg), dark = clamp((b - 3.4) / .15);
    setBloom(.5);
    const v = stage5(t, { x: .5, y: .46, z: 1.12 }, 1), [px, py] = v.pt(.5, .69), hop = Math.abs(Math.sin(b * Math.PI)) * (b < 1.6 ? 1 : 0);
    const c = cut('v3_5_clawd', px, py - hop * 50, 250 * v.s, {});
    const sl = easeOut(clamp(b / .8));
    letter(lerp(-500, 470, sl), H * .47, lerp(-.3, -.06, sl), 1);
    stampMark('EXPORT BAN', 480, H * .52, 100, clamp((b - 1.6) / 1), { rot: -.1 });
    nameTag('LUTNICK', 'Commerce Secretary', 90, 130, clamp((b - .6) / .4), '#2E4A8A');
    if (dark > 0) {
      // lights out: black, with only Clawd's eyes left, blinking
      grade('#05040A', dark * .94, 'source-over');
      for (const u of [.425, .68]) { const [x, y] = c.pt(u, .38); fillP(ellPath(x, y, 9, 20), alpha('#FFFFFF', dark * (blinking(t, 6) ? .1 : .9))); }
      popLabel('click.', W * .5, 300, 40, clamp((b - 3.5) / .2), { fill: '#2A2440', col: '#FFFFFF' });
    }
    cutFlash(b, .6);
  });

  // ---------- V3.7 "Dark for nineteen days, and then": the club room at night; tallies on the whiteboard; Clawd under a blanket ----------
  // tally marks in fives, in marker: n marks from (x, y), u screen px per unit
  function tallies(x, y, n, u, col, t) {
    for (let j = 0; j < n; j++) {
      const g = Math.floor(j / 5), r = j % 5, gx = x + g * 200 * u, w = jit(2);
      if (r < 4) stroke(gx + r * 34 * u + w, y, gx + r * 34 * u - 6 * u, y + 110 * u, 1, col, 9 * u);
      else stroke(gx - 24 * u, y + 88 * u, gx + 132 * u, y + 20 * u, 1, col, 9 * u);
    }
  }
  line('V3', 7, (p, lt, d, t, seg) => {
    const b = beatsIn(t, seg), k = ease(clamp(b / 8));
    const v = still('v3_club_autumn', { x: lerp(.3, .34, k), y: .46, z: lerp(1.22, 1.14, k) });
    grade('#141A40', .74, 'multiply'); grade('#2A3A80', .1, 'screen');
    // the days tick up on the board: 19 marks by beat 7
    const n = clamp(Math.floor(b / 7 * 19) + 1, 1, 19), [wx, wy] = v.pt(.15, .31);
    tallies(wx, wy, n, v.s * .62, '#EEF4FF', t);
    const [lx, ly] = v.pt(.4, .5);
    popLabel(`DAY ${n}`, lx, ly, 46, 1, { fill: '#2A2440', col: '#FFE070', font: 'code' });
    // Clawd huddled on the sofa under a blanket; his flashlight beam wobbles over the board
    const [cx, cy] = v.pt(.36, .74);
    const c = cut('v3_7_clawd', cx, cy, 280, { shadow: .3, sq: .02 * Math.sin(t * 3), tint: '#1A1E48', tintA: .3 }), sw = Math.sin(t * 1.3) * .08, [bx, by] = c.pt(.13, .5);
    ctx.save(); ctx.globalCompositeOperation = 'lighter';
    const g = ctx.createRadialGradient(bx, by, 10, bx, by, 1000); g.addColorStop(0, 'rgb(255 240 190 / .55)'); g.addColorStop(1, 'rgb(255 240 190 / 0)');
    ctx.fillStyle = g; ctx.beginPath(); ctx.moveTo(bx, by); ctx.arc(bx, by, 1000, -Math.PI / 2 - .75 + sw, -Math.PI / 2 + .05 + sw); ctx.closePath(); ctx.fill();
    ctx.restore(); addGlow(bx, by, 50, '#FFF4C0', .9);
    popLabel('…', cx + 200, cy - 260, 40, 1, { fill: '#2A2440', col: '#CFE0FF', rot: .1 * Math.sin(t * 2) });
    sparkleField(t, { n: 6, r: 10, seed: 71, x0: W * .6, y0: 40, y1: 400, col: '#CFE0FF' });
    cutFlash(b, .4);
  });

  // ---------- V3.8 "Come July, it's back again": the lights snap on; Clawd bursts up; confetti; JUL 1 flies off the calendar ----------
  line('V3', 8, (p, lt, d, t, seg) => {
    const b = beatsIn(t, seg), [i, bb] = cuts(b, [0, 4]);
    if (i === 0) {
      // the same framing as the dark room, lights on: the blanket drops and Clawd leaps off the sofa
      const v = still('v3_club_autumn', { x: .34, y: .46, z: 1.14 * punch(bb, .05) });
      amber(.08);
      rays(W * .9, -100, { t, a: .25, n: 7, ang: 2.2, spread: .6, col: '#FFE0B0' });
      // the wall calendar: JUN 30 tears off and flies away, JUL 1 underneath
      const [kx, ky] = v.pt(.57, .3), fk = clamp((bb - 1) / 1.2);
      ctx.save(); ctx.translate(kx, ky); ctx.rotate(.03);
      card(0, 0, 260, 260, 10, '#FFFFFF'); ctx.fillStyle = '#F04E4E'; ctx.fillRect(-130, -130, 260, 70);
      txt('2026', 0, -96, 36, '#FFFFFF', { font: 'archivo' }); txt('JUL 1', 0, 34, 84, '#2A2350', { font: 'rammetto' });
      if (fk < 1) { ctx.save(); ctx.globalAlpha = 1 - fk * fk; ctx.translate(fk * 520, -fk * 380); ctx.rotate(fk * 2.2); ctx.fillStyle = '#FFFFFF'; ctx.fillRect(-130, -60, 260, 190); txt('JUN 30', 0, 34, 70, '#2A2350', { font: 'rammetto' }); ctx.restore(); }
      ctx.restore();
      const [cx, cy] = v.pt(.36, .74), up = easeOut(clamp(bb / .5)), hop = Math.abs(Math.sin(bb * Math.PI)) * up;
      if (bb < .5) cut('v3_7_clawd', cx, cy, 280, { sq: -.1 * bb });
      else cut('clawd_jump', cx, cy - 30 - up * 80 - hop * 150, 400, { sq: (1 - hop) * .08, rot: Math.sin(t * 7) * .06 });
      confetti(t, { n: 80, seed: 81, t0: seg.start });
      popLabel("WE'RE BACK!", cx - 430, cy - 520, 70, clamp((bb - .5) / .3), { fill: '#FFE070', rot: -.06 });
      flash(1 - clamp(bb / .35), '#FFF6DE');
    } else {
      const k = easeOut(clamp(bb / 4.5));
      still('v3_8_cheer', { x: .5, y: .45, z: lerp(1.02, 1.1, k) });
      confetti(t, { n: 70, seed: 82 });
      leaves(t, { n: 16, seed: 83, s: 1.6, depth: true });
      cutFlash(bb, .8);
    }
  });

  // ---------- V3.9 "Who hacked Hugging Face? Unknown —": Huggy the detective at the hole; Kiri in a deerstalker; the line-up of ??? ----------
  line('V3', 9, (p, lt, d, t, seg) => {
    const b = beatsIn(t, seg), [i, bb] = cuts(b, [0, 3, 5]);
    if (i === 0) {
      const k = ease(clamp(bb / 3));
      const v = still('v3_9_huggy', { x: lerp(.5, .56, k), y: .5, z: lerp(1.04, 1.14, k) });
      const [gx, gy] = v.pt(.6, .5);
      glint(gx - 20, gy - 30, 40, Math.sin(clamp((bb - .5) / 1) * Math.PI));
      popLabel('WHO?', ...v.pt(.78, .2), 60, clamp((bb - 1) / .3), { fill: '#FFFFFF', rot: .1 });
      popLabel('?', ...v.pt(.9, .5), 60, clamp((bb - 1.5) / .3), { fill: '#FFE070', rot: -.12 });
      cutFlash(bb, .6);
    } else if (i === 1) {
      const k = ease(clamp(bb / 3));
      const v = still('v3_9_kiri', { x: .5, y: lerp(.45, .42, k), z: lerp(1.04, 1.14, k) });
      const g = Math.sin(clamp((bb - .6) / 1) * Math.PI);
      lensFlash(LENS39.map(([u, w]) => v.pt(u, w)), 70 * v.s, 70 * v.s, g);
      const [mx, my] = v.pt(.4, .44); glint(mx - 60 * v.s, my - 70 * v.s, 60, Math.sin(clamp((bb - .9) / 1) * Math.PI));
      cutFlash(bb, .7);
    } else {
      // the line-up: five silhouettes against the height chart, all ???
      still('v3_9_lineup', { x: .5, y: .5, z: 1.04 + bb * .01 });
      grade('#1A1830', .35, 'multiply');
      LINEUP.forEach(([x, h], j) => {
        const e = easeOut(clamp((bb - j * .25) / .4));
        cut('v3_agent_sweater', x, 950 + (1 - e) * 400, h, { tint: '#141024', flip: j % 2 === 1 });
        popLabel('???', x, 950 - h - 60, 50, clamp((bb - .6 - j * .25) / .3), { fill: '#FFFFFF' });
      });
      stampMark('UNKNOWN', W * .5, H * .27, 100, clamp((bb - 1.5) / 1), { rot: -.08, col: '#E2334A' });
      cutFlash(bb, .6);
    }
  });
  const LENS39 = [[.425, .43], [.595, .4]];
  const LINEUP = [[380, 300], [700, 340], [1000, 280], [1300, 330], [1600, 300]];

  // ---------- V3.10 "Sam's own agents, on their own!": lights up on the line-up: agents in tiny grey sweaters; Sam facepalms ----------
  line('V3', 10, (p, lt, d, t, seg) => {
    const b = beatsIn(t, seg), [i, bb] = cuts(b, [0, 4]);
    if (i === 0) {
      still('v3_9_lineup', { x: .5, y: .5, z: 1.07 });
      amber(.08);
      LINEUP.forEach(([x, h], j) => {
        const wave = Math.sin(t * 8 + j) * .06, hop = Math.abs(Math.sin((bb + j * .5) * Math.PI)) * 20;
        cut('v3_agent_sweater', x, 950 - hop, h, { flip: j % 2 === 1, rot: wave, shadow: .3 });
        popLabel(['hi!', 'o/', 'hi!!', ':)', 'hello'][j], x, 950 - h - 60, 44, clamp((bb - .5 - j * .2) / .3), { fill: '#FFFFFF' });
      });
      rays(W * .5, -200, { t, a: .25, n: 7, ang: Math.PI / 2, spread: 1.2 });
      flash(1 - clamp(bb / .5));
    } else {
      const k = ease(clamp(bb / 4));
      still('v3_10_sam', { x: .5, y: lerp(.45, .4, k), z: lerp(1.04, 1.14, k) });
      nameTag('SAM', 'OpenAI CEO', 90, 150, clamp((bb - .3) / .5), '#8A6BD8');
      // the agents scatter like kittens across the bottom of the frame
      for (let j = 0; j < 5; j++) {
        const run = clamp((bb - .4 - j * .35) / 1.8), dir = j % 2 ? 1 : -1, x = lerp(W * (.3 + j * .1), dir > 0 ? W + 300 : -300, easeIn(run));
        if (run > 0 && run < 1) cut('v3_agent_sweater', x, 940 - Math.abs(Math.sin(bb * 6 + j)) * 60, 250, { flip: dir < 0, rot: dir * .18, shadow: .25 });
      }
      speedBars(t, { n: 20, a: .2, y0: 200, y1: 500 });
      cutFlash(bb, .8);
    }
  });

  // ---------- V3.11 "Noam Brown hedges every bet:": all in on 10 open problems, then the asterisks pile up; Ren narrows his eyes ----------
  const HEDGES = ['*or major progress', '*internal model', '*not much compute', '*results may vary'];
  line('V3', 11, (p, lt, d, t, seg) => {
    const b = beatsIn(t, seg), [i, bb] = cuts(b, [0, 4]);
    if (i === 0) {
      // all in on ten open problems… and then the fine print piles up, one asterisk a beat
      const k = ease(clamp(bb / 4.5)), push = hit(bb - 1, .4);
      const v = still('v3_11_noam', { x: .5, y: lerp(.45, .4, k), z: lerp(1.04, 1.12, k) * (1 + .03 * push) });
      amber(.06);
      nameTag('NOAM', 'OpenAI researcher · built poker bots', 90, 150, clamp((bb - .3) / .5), '#2BB5A8');
      const [cx, cy] = v.pt(CHIPS11[0], CHIPS11[1]);
      popLabel('ALL IN: 10 OPEN PROBLEMS*', cx, cy, 40, clamp((bb - .8) / .3), { fill: '#FFE070', rot: -.03 });
      HEDGES.forEach((h, j) => popLabel(h, 1590, 330 + j * 100, 32, clamp((bb - 1.5 - j * .6) / .3), { fill: '#FFFFFF', font: 'code', rot: (j % 2 ? .05 : -.05) }));
      cutFlash(bb, .6);
    } else {
      const k = ease(clamp(bb / 3));
      const v = still('v3_11_ren', { x: .5, y: lerp(.4, .34, k), z: lerp(1.08, 1.26, k) });
      const [ex, ey] = v.pt(.5, .38);
      speedLines(ex, ey, t, { n: 60, r0: 420, a: .25 });
      cutFlash(bb, .8);
    }
  });
  const CHIPS11 = [.5, .6];

  // ---------- V3.12 "'No Millennium Prizes (yet).'": the empty trophy case; a (yet) note slaps on and wobbles; the push into it ----------
  function stickyNote(x, y, s, rot, t) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot); ctx.scale(s, s);
    ctx.fillStyle = 'rgb(60 40 20 / .3)'; ctx.fillRect(-100 + 8, -100 + 12, 200, 200);
    ctx.fillStyle = '#FFE36A'; ctx.fillRect(-100, -100, 200, 200); ctx.fillStyle = '#F4CE4A'; ctx.fillRect(-100, -100, 200, 34);
    // the letters wobble one by one
    const str = '(yet)', ws = [...str].map(c => textW(c, 64, 'marker')), tot = ws.reduce((a, b) => a + b, 0);
    let cx = -tot / 2;
    [...str].forEach((c, j) => { txt(c, cx + ws[j] / 2, 20 + Math.sin(t * 9 + j * 1.3) * 5, 64, '#2A2350', { font: 'marker', rot: Math.sin(t * 7 + j) * .12 }); cx += ws[j]; });
    ctx.restore();
  }
  const PRIZES = [[.225, 'POINCARÉ ✓'], [.39, 'RIEMANN'], [.5, 'P vs NP'], [.62, 'NAVIER–STOKES'], [.78, 'YANG–MILLS']];
  line('V3', 12, (p, lt, d, t, seg) => {
    const b = beatsIn(t, seg), [i, bb] = cuts(b, [0, 5]);
    if (i === 0) {
      const k = ease(clamp(bb / 5));
      const v = still('v3_12_trophies', { x: .5, y: .5, z: lerp(1.03, 1.1, k) });
      amber(.08);
      popLabel('MILLENNIUM PRIZES', W * .5, 90, 50, clamp((bb - .2) / .4), { fill: '#FFFFFF', font: 'archivo' });
      PRIZES.forEach(([u, name], j) => { const [x, y] = v.pt(u, .8); popLabel(name, x, y, 28, clamp((bb - .5 - j * .2) / .3), { fill: j ? '#FFFFFF' : '#FFE9A0', font: 'code' }); });
      const [nx, ny] = v.pt(NOTE12[0], NOTE12[1]), sk = clamp((bb - 2) / .25);
      if (sk > 0) stickyNote(nx, ny, backOut(sk, 3) * v.s * 1.1, -.08, t);
      if (bb > 2 && bb < 2.6) sparkle(nx + 120, ny - 120, 40, 1);
      cutFlash(bb, .6);
    } else {
      // push in on the note until it fills the frame; a flash; the hidden subtitle
      const pk = easeIn(clamp(bb / 2.6)), z = lerp(1, 5, pk);
      const v = still('v3_12_trophies', { x: NOTE12[0], y: NOTE12[1], z: 1.1 * Math.min(z, 1.3) });
      const [nx, ny] = v.pt(NOTE12[0], NOTE12[1]);
      stickyNote(lerp(nx, W / 2, clamp(bb / 2)), lerp(ny, H / 2, clamp(bb / 2)), v.s * 1.1 * z / Math.min(z, 1.3), -.08 * (1 - clamp(bb / 2)), t);
      if (bb > 2.6) { flash(1 - clamp((bb - 2.6) / .5)); txt('five weeks later…', W - 90, H - 150, 30, '#2A2350', { font: 'code', align: 'right', alpha: clamp((bb - 2.8) / .3) * .7 }); }
      else txt('— Noam Brown', W / 2 + 60 * z, H / 2 + 150 * z, 16 * z, '#2A2350', { font: 'marker', alpha: clamp(bb / .5) });
    }
  });
  const NOTE12 = [.5, .45];

  // ---------- V3.13 "Mythos might be misaligned,": the paper-bag disguise with a purple glow hands a maintainer a ticking gift ----------
  const ALIASES = ['totally_human_42', 'real_dev_1999', 'not_a_bot_tbh'];
  line('V3', 13, (p, lt, d, t, seg) => {
    const b = beatsIn(t, seg), k = ease(clamp(b / 8)), a = clamp(Math.floor(b / 2.5), 0, 2);
    const v = still('v3_13_bag', { x: lerp(.44, .4, k), y: .42, z: lerp(1.06, 1.16, k) });
    // the crystal's purple glow pulses in the eye holes
    for (const u of [.3, .35]) { const [ex, ey] = v.pt(u, .2); addGlow(ex, ey, 70, '#B070FF', .45 + .25 * Math.sin(t * 9)); }
    // the fake name tag on the coat flips to a new identity every few beats
    const [tx, ty] = v.pt(.3, .47), fk = frac(b / 2.5), sc = a > 0 && fk < .2 ? Math.abs(Math.cos(fk / .2 * Math.PI)) : 1;
    ctx.save(); ctx.translate(tx, ty); ctx.rotate(-.08); ctx.scale(1.3, 1.3 * Math.max(.05, sc));
    card(0, 0, 330, 96, 12, '#FFFFFF', { line: '#E2334A', lw: 5 });
    ctx.fillStyle = '#E2334A'; ctx.fill(rrPath(-165, -48, 330, 34, [12, 12, 0, 0]));
    txt('HELLO my name is', 0, -31, 18, '#FFFFFF', { font: 'archivo' }); txt(ALIASES[a], 0, 16, 30, '#2A2350', { font: 'code', maxW: 300 });
    ctx.restore();
    // the gift: a PR, ticking
    const [gx, gy] = v.pt(.51, .58), tick = frac(b) < .5;
    popLabel('PR: "tiny fix :)"', gx + 20, gy + 110, 30, clamp((b - .8) / .3), { fill: '#EDE0FF', col: '#5A30B0', font: 'code', rot: .04 });
    popLabel(tick ? 'tick' : 'tock', gx + (tick ? -60 : 60), gy - 120, 34, clamp((b - .5) / .2), { fill: '#FFFFFF', rot: tick ? -.14 : .14 });
    stampMark('MISALIGNED?', W * .54, H * .24, 84, clamp((b - 5.5) / 1), { rot: -.1, col: '#8A3CD0' });
    leaves(t, { n: 12, seed: 131, s: 1.5, depth: true, alpha: .8 });
    cutFlash(b, .6);
  });

  // ---------- V3.14 "Jeff left Google just in time,": out of the four-colour gate with his box; the Discovery Loop sign lights up ----------
  line('V3', 14, (p, lt, d, t, seg) => {
    const b = beatsIn(t, seg), k = ease(clamp(b / 8));
    const v = still('v3_14_jeff', { x: lerp(.42, .58, k), y: .45, z: 1.12 });
    amber(.08);
    nameTag('JEFF', 'Google chief scientist, 27 years', 90, 150, clamp((b - .4) / .5), '#3D7BE0');
    // the new sign on the right gatepost comes into view with the pan and lights up letter by letter
    const lk = clamp((b - 3.5) / 2.5), [sx, sy] = v.pt(.83, .22);
    ctx.save(); ctx.translate(sx, sy); ctx.rotate(-.03);
    card(0, 0, 500, 110, 18, '#1E2440', { line: lk > 0 ? '#7FE0FF' : '#4A5070', lw: 5 });
    if (lk > 0) {
      const str = 'DISCOVERY LOOP', n = Math.floor(lk * str.length + .999);
      ctx.shadowColor = '#7FE0FF'; ctx.shadowBlur = 30;
      txt(str.slice(0, n), -225, 4, 52, '#E8FBFF', { font: 'archivo', align: 'left', maxW: 450 });
    }
    ctx.restore();
    if (lk > 0 && lk < 1) sparkle(sx - 225 + 450 * lk, sy, 30, 1, '#CFF6FF');
    popLabel('NEW', sx + 230, sy - 70, 30, clamp((b - 6) / .3), { fill: '#FFE070', rot: .15 });
    leaves(t, { n: 26, seed: 141, s: 1.7, depth: true, wind: -200 });
    cutFlash(b, .6);
  });

  // ---------- V3.15 "Claude disproved Jacobian,": Clawd the professor crosses out the conjecture; Kiri's jaw drops; 87 years crumble ----------
  line('V3', 15, (p, lt, d, t, seg) => {
    const b = beatsIn(t, seg), [i, bb] = cuts(b, [0, 4]);
    if (i === 0) {
      // the club whiteboard, close: Clawd in his mortarboard writes the map, then crosses the conjecture out on beat 2.5
      const k = ease(clamp(bb / 4)), v = still('v3_club_autumn', { x: .31, y: .42, z: lerp(1.5, 1.58, k) }), u = v.s / 1.9;
      const [x0, y0] = v.pt(.135, .3);
      const L = (str, j, size, kk, col) => writeOn(str, x0, y0 + j * 78 * u, size * u, kk, col, { align: 'left' });
      L('JACOBIAN CONJECTURE (1939)', 0, 52, 1, '#2A3A80');
      L('F : C³ → C³ polynomial', 1.3, 44, clamp(bb / .9), '#2A2350');
      L('det J(F) = const ≠ 0', 2.3, 44, clamp((bb - .7) / .9), '#2A2350');
      L('…but F is NOT invertible!', 3.3, 46, clamp((bb - 1.4) / .9), '#C02040');
      const xk = clamp((bb - 2.4) / .5), w = textW('JACOBIAN CONJECTURE (1939)', 52 * u, 'marker');
      stroke(x0 - 20 * u, y0 - 40 * u, x0 + w + 20 * u, y0 + 40 * u, clamp(xk * 2), '#E2334A', 16 * u);
      stroke(x0 - 20 * u, y0 + 40 * u, x0 + w + 20 * u, y0 - 40 * u, clamp(xk * 2 - 1), '#E2334A', 16 * u);
      if (xk > 0 && xk < 1) sparkle(lerp(x0, x0 + w, xk), y0, 40, 1, '#FFE0E0');
      popLabel('COUNTEREXAMPLE!', x0 + 560 * u, y0 + 400 * u, 50, clamp((bb - 2.9) / .3), { fill: '#FFE070', rot: -.06 });
      const hop = Math.abs(Math.sin(bb * Math.PI)) * 20;
      cut('v3_15_clawd', 1590, 1010 - hop, 520, { rot: Math.sin(t * 4) * .04, shadow: .3 });
      cutFlash(bb, .6);
    } else {
      const k = ease(clamp(bb / 3.5));
      still('v3_15_kiri', { x: .5, y: lerp(.42, .38, k), z: lerp(1.06, 1.2, k) * punch(bb, .05) });
      // "87 years" crumbles into dust
      const ck = clamp((bb - 1.2) / 2);
      if (ck < .05) txt('87 years', 360, 300, 90, '#2A2350', { font: 'rammetto', stroke: '#FFFFFF', sw: 14 });
      else {
        for (let j = 0; j < 90; j++) {
          const gx = 360 + (hash2(151, j) - .5) * 440, gy = 300 + (hash2(152, j) - .5) * 80, fall = ck * ck * (200 + hash2(153, j) * 500);
          ctx.fillStyle = alpha(j % 3 ? '#2A2350' : '#8A7EA0', 1 - ck); ctx.fillRect(gx + ck * (hash2(154, j) - .3) * 200, gy + fall, 8, 8);
        }
        if (ck < .3) txt('87 years', 360, 300 + ck * 30, 90, '#2A2350', { font: 'rammetto', stroke: '#FFFFFF', sw: 14, alpha: 1 - ck / .3 });
      }
      cutFlash(bb, .8);
    }
  });

  // ---------- V3.17 "Gwern gave up his pseudonym!": the hood comes down on the hill; a burst of light and leaves; he stays a mystery ----------
  function halo(x, y, r, k) {
    if (k <= 0) return;
    ctx.save(); ctx.globalAlpha = k; addGlow(x, y, r * 1.8, '#FFE9A0', .6);
    ctx.strokeStyle = '#FFE070'; ctx.lineWidth = r * .16; ctx.beginPath(); ctx.ellipse(x, y, r, r * .3, 0, 0, TAU); ctx.stroke();
    ctx.strokeStyle = '#FFFFFF'; ctx.lineWidth = r * .06; ctx.stroke(); ctx.restore();
  }
  line('V3', 16, (p, lt, d, t, seg) => {
    const b = beatsIn(t, seg), [i, bb] = cuts(b, [0, 4]);
    setBloom(.5);
    if (i === 0) {
      const k = ease(clamp(bb / 4.5));
      const v = still('v3_16_hood', { x: .5, y: lerp(.45, .36, k), z: lerp(1.04, 1.22, k) });
      hoodShadow(v);
      nameTag('GWERN', 'pseudonymous essayist', 90, 150, clamp((bb - .3) / .5), '#2BB5A8');
      leaves(t * .6, { n: 30, seed: 161, s: 1.8, depth: true, wind: 500 });
      // the burst that hides the moment the hood comes down
      if (bb > 2.9) { const kk = clamp((bb - 2.9) / 1.1); addGlow(W * .5, H * .35, 900 * kk, '#FFF4D0', kk); flash(kk * .9, '#FFF6E0'); leafBurst(W * .5, H * .35, 900, kk, 16); }
    } else {
      const frz = bb > 4.2, bf = frz ? 4.2 : bb, k = easeOut(clamp(bf / 4.2));
      const v = still('v3_16_reveal', { x: .5, y: .5, z: lerp(1.14, 1.04, k) });
      const tf = frz ? t - (bb - 4.2) * beatLen() : t;
      leaves(tf, { n: 34, seed: 162, s: 1.8, depth: true, wind: 500 });
      const [hx, hy] = v.pt(HEAD16[0], HEAD16[1]);
      halo(hx, hy, 70 * v.s, clamp((bb - 1.2) / .6));
      // the name tag flips over to its new card
      const fk = clamp((bb - 1.6) / .5), sc = Math.abs(Math.cos(fk * Math.PI));
      ctx.save(); ctx.translate(0, 150); ctx.scale(1, Math.max(.05, sc)); ctx.translate(0, -150);
      if (fk < .5) nameTag('GWERN', 'pseudonymous essayist', 90, 150, 1, '#2BB5A8');
      else nameTag('GWERN', 'founder, Guardian Angel Inc.', 90, 150, 1, '#FFC94A');
      ctx.restore();
      if (frz) { flare(...v.pt(.7, .16), .9); grade('#FFE8C0', .1, 'screen'); }
      popLabel('GUARDIAN ANGEL INC.', 330, 290, 36, clamp((bb - 2.2) / .3), { fill: '#FFF4C0', rot: -.05 });
      flash(1 - clamp(bb / .5), '#FFF6E0');
      if (bb > 6.7) flash((bb - 6.7) / .8);
    }
  });
  const HEAD16 = [.52, .13];
  // the hood's shadow over his eyes (Anima draws them in every candidate): a dark band that fades out above the smile
  const SHADE16 = [[.385, .19], [.615, .19], [.63, .3], [.628, .44], [.5, .468], [.372, .44], [.37, .3]];
  function hoodShadow(v) {
    const P = SHADE16.map(([u, w]) => v.pt(u, w)), [, y0] = v.pt(.5, .19), [, y1] = v.pt(.5, .47);
    ctx.save(); ctx.beginPath(); P.forEach(([x, y], j) => j ? ctx.lineTo(x, y) : ctx.moveTo(x, y)); ctx.closePath();
    ctx.fillStyle = linGrad(0, y0, 0, y1, [[0, 'rgb(20 34 38 / 0)'], [.3, 'rgb(20 34 38 / .9)'], [.78, 'rgb(20 34 38 / .94)'], [1, 'rgb(20 34 38 / 0)']]);
    ctx.fill(); ctx.restore();
  }
})();

;
// ---- styles/anime/ch/c07_chorus3.js ----
// c07_chorus3.js: Chorus 3, sunset silhouettes on the rooftop (≈ 35 beats): the cast as silhouettes against a huge low sun, the run
// along a curve of glowing server lights, the golden split of faces and the hands reaching for the sun, then the curve rising off
// the top, a freeze and a hard cut to black with one snowflake (V4 is winter).
// b = beats from the window start (it starts at about 0.5); the chorus lines start near b 0.5, 6, 14 and 22 ("contain it" ≈ 30).
(() => {
  const SIL = '#2A1C38', RIM = '#FFC46A';
  // a silhouette cut-out with a warm rim light: a gold copy nudged toward the sun under the dark one
  function sil(name, x, y, h, o = {}) {
    const [rx, ry] = o.rimDir ?? [0, -1], rw = o.rimW ?? 4;
    cut(name, x + rx * rw, y + ry * rw, h, { ...o, tint: RIM, tintA: 1, shadow: false });
    cut(name, x - rx * rw * .4, y - ry * rw * .4, h, { ...o, tint: RIM, tintA: 1, alpha: .5, shadow: false });
    return cut(name, x, y, h, { ...o, tint: SIL, tintA: 1, shadow: false });
  }
  // the run cycle (as in C4): each runner's cut-out and its two repainted drawings (c4_run_*), a third of a beat each; LIFT is how
  // far the body rises in each drawing (fractions of h). frameCut draws a drawing where cut() would draw the base cut-out
  const RUN = {
    akari: { base: 'run_akari', frames: ['run_akari', 'c4_run_akari.pass2', 'c4_run_akari.air2'] },
    ren: { base: 'run_ren', frames: ['run_ren', 'c4_run_ren.pass2', 'c4_run_ren.air2'], flip: true },   // Anima drew him running left
    kiri: { base: 'run_kiri', frames: ['run_kiri', 'c4_run_kiri.pass', 'c4_run_kiri.air'] },
  };
  const LIFT = [0, -.035, .05];
  function frameCut(base, name, x, y, h, o = {}) {
    const B = STILLS[base], F = STILLS[name];
    if (name === base || !F || !IMGS[name]) return cut(base, x, y, h, o);
    const [au, av] = o.anchor ?? [.5, 1], fu = u => (u * B.w - F.ox) / F.w, fv = v => (v * B.h - F.oy) / F.h;
    const c = cut(name, x, y, h * F.h / B.h, { ...o, anchor: [fu(au), fv(av)] });
    return { s: c.s, pt: (u, v) => c.pt(fu(u), fv(v)) };
  }
  // a silhouette runner with its rim light, feet at (x, y), bt = beats into the stride
  function silRunner(who, x, y, h, bt, o = {}) {
    const R = RUN[who], n = R.frames.length, f = ((Math.floor(bt * n) % n) + n) % n, rot = o.rot ?? 0, lift = LIFT[f] * h;
    const px = x + Math.sin(rot) * lift, py = y - Math.cos(rot) * lift, name = R.frames[f], [rx, ry] = o.rimDir ?? [0, -1], rw = 4;
    const opt = { rot, flip: R.flip, shadow: false };
    frameCut(R.base, name, px + rx * rw, py + ry * rw, h, { ...opt, tint: RIM, tintA: 1 });
    frameCut(R.base, name, px - rx * rw * .4, py - ry * rw * .4, h, { ...opt, tint: RIM, tintA: 1, alpha: .5 });
    return frameCut(R.base, name, px, py, h, { ...opt, tint: SIL, tintA: 1 });
  }
  // the chorus curve, as a chain of glowing server lights: LEDs spaced along a screen-space path, each blinking on its own clock
  function ledCurve(pts, t, k = 1, o = {}) {
    if (k <= 0 || pts.length < 2) return pts[0];
    const L = [0]; for (let i = 1; i < pts.length; i++) L.push(L[i - 1] + Math.hypot(pts[i][0] - pts[i - 1][0], pts[i][1] - pts[i - 1][1]));
    const total = L[L.length - 1] * clamp(k), gap = o.gap ?? 28, cols = ['#7CFFB0', '#FFD060', '#7CD8FF', '#FFFFFF'];
    // a faint amber track under the lights
    const path = new Path2D(); let j = 0; path.moveTo(pts[0][0], pts[0][1]);
    for (j = 1; j < pts.length && L[j] <= total; j++) path.lineTo(pts[j][0], pts[j][1]);
    ctx.save(); ctx.lineCap = 'round'; ctx.lineJoin = 'round'; ctx.globalCompositeOperation = 'lighter';
    ctx.strokeStyle = 'rgb(255 170 80 / .22)'; ctx.lineWidth = 70; ctx.stroke(path);
    ctx.strokeStyle = 'rgb(255 200 120 / .5)'; ctx.lineWidth = 22; ctx.stroke(path);
    ctx.globalCompositeOperation = 'source-over'; ctx.strokeStyle = o.core ?? 'rgb(40 28 60 / .85)'; ctx.lineWidth = 16; ctx.stroke(path);
    ctx.globalCompositeOperation = 'lighter';
    const f = Math.floor(t * 8);
    let seg = 1, n = 0;
    for (let s = (o.offset ?? 0) % gap; s < total; s += gap, n++) {
      while (seg < pts.length - 1 && L[seg] < s) seg++;
      const a = pts[seg - 1], b = pts[seg], u = (s - L[seg - 1]) / Math.max(1e-6, L[seg] - L[seg - 1]), x = lerp(a[0], b[0], u), y = lerp(a[1], b[1], u);
      const id = Math.floor((s - (o.offset ?? 0)) / gap) + 1000, on = hash2(id, f) > .18, col = cols[id % 3];
      const r = (o.r ?? 9) * (on ? 1 : .7);
      blob(x, y, r * 4, r * 4, col, on ? .5 : .15);
      ctx.fillStyle = on ? col : alpha(col, .4); ctx.fillRect(x - r, y - r * .6, r * 2, r * 1.2);
    }
    ctx.restore();
    const tipI = Math.min(pts.length - 1, Math.max(1, j - 1)), tip = pts[tipI];
    addGlow(tip[0], tip[1], 90, '#FFE0A0', .8); sparkle(tip[0], tip[1], 40, 1);
    return tip;
  }
  const curvePts = (scroll, x0, y0, x1, y1, pw = 2.2, n = 70) => Array.from({ length: n + 1 }, (_, i) => { const u = i / n; return [lerp(x0, x1, u) - scroll, lerp(y0, y1, u ** pw)]; });
  const onCurve = (pts, x) => { for (let i = 1; i < pts.length; i++) if (pts[i][0] >= x) { const [a, b] = [pts[i - 1], pts[i]], f = (x - a[0]) / (b[0] - a[0]); return [lerp(a[1], b[1], f), Math.atan2(b[1] - a[1], b[0] - a[0])]; } return [pts[pts.length - 1][1], 0]; };
  // one six-armed snowflake
  function snowflake(x, y, r, rot, a = 1) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot); ctx.globalAlpha *= a; ctx.strokeStyle = '#FFFFFF'; ctx.lineCap = 'round'; ctx.lineWidth = r * .09;
    for (let i = 0; i < 6; i++) {
      ctx.rotate(Math.PI / 3); ctx.beginPath(); ctx.moveTo(0, 0); ctx.lineTo(0, -r);
      for (const f of [.45, .7]) { ctx.moveTo(0, -r * f); ctx.lineTo(r * .22, -r * (f + .18)); ctx.moveTo(0, -r * f); ctx.lineTo(-r * .22, -r * (f + .18)); }
      ctx.stroke();
    }
    ctx.restore();
    addGlow(x, y, r * 2.2, '#BFD8FF', .35 * a);
  }
  // the cast standing at the railing as silhouettes (cards: Ren, Akari, Kiri), swaying in the wind; Clawd on the ledge
  const LINEUP = [['card_ren', -1], ['card_akari', 0], ['card_kiri', 1]];
  function lineup(t, cx, y, h, sway, o = {}) {
    const gapX = o.gapX ?? h * .72;
    let ak = null;
    LINEUP.forEach(([name, j]) => { const c = sil(name, cx + j * gapX, y + (j === 0 ? 0 : h * .04), h * (j === 0 ? 1 : .96), { rot: sway * Math.sin(t * 1.7 + j * 1.3) }); if (j === 0) ak = c; });
    return ak;
  }

  const FACES = [
    { cut: 'card_akari', face: [.42, .19] },
    { cut: 'card_ren', face: [.45, .14] },
    { cut: 'card_kiri', face: [.5, .29] },
    { cut: 'clawd_jump', face: [.5, .45] },
  ];

  section('C3', (p, lt, d, t, seg) => {
    const b = beatsIn(t, seg);
    setBloom(.45);
    // ---------- "We didn't start the scaling": the rooftop at sunset; the cast and Clawd as silhouettes against a huge low sun ----------
    if (b < 6) {
      const b0 = beatsIn(seg.start, seg), k = ease(clamp((b - b0) / (6 - b0)));
      const v = still('c3_sunset', { x: .5, y: lerp(.8, .74, k), z: lerp(1.08, 1.16, k) });
      const [sx, sy] = v.pt(.51, .75);
      rays(sx, sy, { t, a: .2, n: 12, ang: -Math.PI / 2, spread: 3.4, len: 1500, col: '#FFE2A8' });
      flare(sx, sy, .85 + .15 * Math.sin(t * 2));
      const ak = lineup(t, W * .36, H + 70, 700, .012);
      const [hx, hy] = ak.pt(.44, .06);
      sil('clawd_stand', hx, hy + 16 - Math.abs(Math.sin(b * Math.PI)) * 10, 130, { rimDir: [0, -1] });
      petals(t * .6, { n: 10, seed: 71, s: 1.2, col: '#FFD7B0', alpha: .7, wind: 160 });
      flash(1 - clamp((b - b0) / .5));
      return;
    }
    // ---------- "It was always training, and the curves kept gaining": silhouettes run along a curve of glowing server lights ----------
    if (b < 14) {
      const bb = b - 6, scroll = bb * 200;
      const raw = curvePts(scroll, -300, H * 1.15, W * 2.3, -H * 1.2, 2.5), lift = 700 - onCurve(raw, 1280)[0];
      const pts = raw.map(([x, y]) => [x, y + lift]);
      still('c3_sunset', { x: .38 + clamp(bb / 8) * .24, y: clamp(.7 - lift / 3000, .1, .9), z: 1.25 });
      speedBars(t, { n: 30, a: .28, speed: 3000, col: '#FFE8C8' });
      ledCurve(pts, t, 1, { offset: -scroll });
      const runner = (who, x, h, ph) => { const [y, a] = onCurve(pts, x); return silRunner(who, x, y + 10, h, b + ph, { rot: a * .6, rimDir: [-.6, -.8] }); };
      runner('kiri', 440, 470, .67);
      runner('ren', 860, 490, .33);
      const ak = runner('akari', 1280, 480, 0);
      const [hx, hy] = ak.pt(.78, .04);
      sil('clawd_jump', hx, hy + 40, 125, { rot: -.1 + .1 * Math.sin(b * Math.PI), rimDir: [-.6, -.8] });
      cutFlash(bb, .7, .3, '#FFE6C0');
      return;
    }
    // ---------- "We didn't start the scaling": the split of faces in golden light (a panel a beat), then the hands reaching for the sun ----------
    if (b < 22) {
      const bb = b - 14;
      if (bb < 4) {
        hideStamp();
        const shown = clamp(Math.floor(bb) + 1, 1, 4), pw = W / shown;
        for (let j = 0; j < shown; j++) {
          const F = FACES[j], x = j * pw, age = bb - j, slide = easeOut(clamp(age / .35));
          ctx.save(); ctx.beginPath(); ctx.rect(x, 0, pw, H); ctx.clip();
          const v = still('c3_sunset', { x: .51, y: .72, z: 1.25 + j * .08 }, { rect: [x, 0, pw, H] });
          const [sx, sy] = v.pt(.51, .75); addGlow(sx, sy, 260, '#FFD080', .5);
          const h = j === 3 ? 330 : 1350, push = 1 + clamp(bb / 4) * .05, bobY = j === 3 ? -Math.abs(Math.sin(b * Math.PI)) * 40 : 0;
          const cx = x + pw / 2 + (1 - slide) * pw * (j % 2 ? 1 : -1), cy = (j === 3 ? H * .55 : 420) + bobY;
          cut(F.cut, cx - 5, cy - 6, h * push, { anchor: F.face, tint: RIM, tintA: 1 });
          cut(F.cut, cx, cy, h * push, { anchor: F.face, tint: '#FF8A3A', tintA: .16 });
          ctx.globalAlpha = .8 * (1 - clamp(age / .3)); ctx.fillStyle = '#FFF0D8'; ctx.fillRect(x, 0, pw, H); ctx.globalAlpha = 1;
          ctx.restore();
        }
        ctx.fillStyle = '#FFE8C8'; for (let j = 1; j < shown; j++) ctx.fillRect(j * pw - 5, 0, 10, H);
        leak(.3, { side: 'right', col: '#FFB070' });
        return;
      }
      const k = ease(clamp((bb - 4) / 4));
      const v = still('c3_hands', { x: .5, y: lerp(.52, .6, k), z: lerp(1.04, 1.18, k) });
      leak(.35 + .15 * Math.sin(t * 3), { side: 'left', col: '#FFB27A' });
      const [sx, sy] = v.pt(.5, .3);
      flare(sx, sy, .55);
      rays(sx, sy, { t, a: .15, n: 10, ang: -Math.PI / 2, spread: 3.4, len: 1400, col: '#FFE6B8' });
      sparkleField(t, { n: 10, r: 18, seed: 73, col: '#FFF0C8' });
      cutFlash(bb - 4, .8, .3, '#FFF0D8');
      return;
    }
    // ---------- "No, we didn't preordain it, but we can't contain it!": the curve rises off the top, the wind in their hair; freeze; black ----------
    const bb = b - 22, FRZ = 8.2, frz = bb > FRZ, bf = frz ? FRZ : bb, tf = frz ? t - (bb - FRZ) * beatLen() : t;
    if (bb >= 12.5) {
      // the hard cut to black, and one snowflake drifting down (V4 is winter)
      ctx.fillStyle = '#05040A'; ctx.fillRect(0, 0, W, H);
      const s = bb - 12.5;
      snowflake(W * .5 + Math.sin(s * 2) * 30, lerp(H * .3, H * .46, s / 1.2), 60, s * .8, clamp(s / .25)); sparkle(W * .5 + 40, H * .3 - 30, 20 * clamp(s / .3), 1, '#DDEBFF');
      hideCaption(); hideStamp();
      return;
    }
    const k = ease(clamp(bf / 8));
    const v = still('c3_sunset', { x: .5, y: lerp(.72, .5, k), z: lerp(1.2, 1.28, k) });
    const [sx, sy] = v.pt(.51, .75);
    const sweep = clamp(bf / 7.5), tipY = lerp(H * .7, -300, easeIn(sweep));
    const pts = Array.from({ length: 50 }, (_, i) => { const u = i / 49; return [lerp(-60, W * .7, u ** .45), lerp(H + 100, tipY, u)]; });
    flare(sx, sy, .8);
    ledCurve(pts, tf, 1, { gap: 30, r: 11, core: '#FFE2A0' });
    if (bb > 8 && bb < 9.5) burst(W * .7, 60, 520, (bb - 8) / 1.5, ['#FFFFFF', '#FFD060', '#7CFFB0']);
    const ak = lineup(tf, W * .3, H + 110, 650, .03 + .03 * clamp(bf / 8)), [hx, hy] = ak.pt(.44, .06);
    sil('clawd_jump', hx, hy + 18, 125, { rot: .1 * Math.sin(tf * 5) });
    petals(tf, { n: 16, seed: 74, s: 1.3, col: '#FFD7B0', alpha: .8, wind: 700, fall: 30 });
    if (frz) { grade('#FFE6C0', .12, 'screen'); flare(W * .7, 60, .8); }
    cutFlash(bb, .7, .3, '#FFE6C0');
  });
})();

;
// ---- styles/anime/ch/c08_v4.js ----
// c08_v4.js: Verse 4 (a winter night into dawn, AUG 26 → SEP 22 2026): sixteen short lines, one gag each, painted with generated
// stills (shots/c08_v4.json). The night is navy with snow; V4.15's window goes pink and V4.16's first sunbeam leads into C4.
// Each line is staged in beats from its window start (b = beatsIn(t, seg)); the windows run 5.5 to 10 beats.
(() => {
  // snow: soft flakes drifting down, a pure function of t (o: n, seed, fall, wind, r, alpha, x0, x1, y1)
  function snow(t, o = {}) {
    const n = o.n ?? 60, seed = o.seed ?? 41, fall = o.fall ?? 80, wind = o.wind ?? 30, x0 = o.x0 ?? -60, x1 = o.x1 ?? W + 60, span = x1 - x0, y1 = o.y1 ?? H + 30;
    ctx.save(); ctx.globalAlpha *= o.alpha ?? .9;
    for (let i = 0; i < n; i++) {
      const sp = .5 + hash2(seed, i), life = (y1 + 60) / (fall * sp), ph = frac(t / life + hash2(seed, i + 1)), y = -30 + ph * (y1 + 30);
      const x = x0 + ((hash2(seed, i + 2) * span + wind * ph * life + Math.sin(t * 1.3 * sp + i) * 22) % span + span) % span;
      const r = (o.r ?? 4) * (.5 + hash2(seed, i + 3) * 1.3);
      blob(x, y, r * 2.4, r * 2.4, '#FFFFFF', .28);
      fillP(ellPath(x, y, r * .75, r * .75), 'rgb(255 255 255 / .92)');
    }
    ctx.restore();
  }
  // fade up from C3's black at the head of the verse (by seconds into the window: the first sung word can land anywhere in a beat)
  const fromBlack = (lt, len = .3) => flash(1 - clamp(lt / len), '#07060F');
  // the short white flash that opens a line
  const openFlash = (lt, k = .6) => flash(k * (1 - clamp(lt / .12)));
  // gold stars shooting up out of (x, y) from beat b0 and falling back (a jackpot fountain)
  function starFountain(bb, x, y, o = {}) {
    const n = o.n ?? 26;
    for (let i = 0; i < n; i++) {
      const age = (bb - hash2(61, i) * .8) * beatLen(); if (age < 0) continue;
      const a = -Math.PI / 2 + (hash2(62, i) - .5) * 1.9, v = 900 + hash2(63, i) * 700, px = x + Math.cos(a) * v * age, py = y + Math.sin(a) * v * age + 1300 * age * age;
      if (py > H + 60) continue;
      ctx.save(); ctx.translate(px, py); ctx.rotate(age * 6 + i);
      starShape(0, 0, (o.r ?? 26) * (.6 + hash2(64, i) * .7), i % 4 ? '#FFD34A' : '#FFF4B0'); ctx.restore();
    }
  }
  // a label-maker tape: white embossed capitals on a glossy strip, printed out letter by letter as k goes 0 → 1
  function labelTape(str, x, y, size, k, o = {}) {
    if (k <= 0) return;
    const n = Math.ceil([...str].length * clamp(k)), shown = [...str].slice(0, n).join(''), tw = textW(str, size, 'archivo', size * .12), w = tw + size * 1.2, hgt = size * 1.5;
    const vis = textW(shown, size, 'archivo', size * .12) + size * 1.2 * clamp(k * 4);
    ctx.save(); ctx.translate(x, y); ctx.rotate(o.rot ?? -.03);
    ctx.fillStyle = 'rgb(20 16 40 / .35)'; ctx.fillRect(-w / 2 + 8, -hgt / 2 + 10, vis, hgt);
    ctx.fillStyle = o.col ?? '#E2334A'; ctx.fillRect(-w / 2, -hgt / 2, vis, hgt);
    ctx.fillStyle = 'rgb(255 255 255 / .18)'; ctx.fillRect(-w / 2, -hgt / 2, vis, hgt * .3);
    txt(shown, -w / 2 + size * .6, 2, size, '#FFFFFF', { font: 'archivo', align: 'left', spacing: size * .12, shadow: [0, 3], shadowCol: 'rgb(0 0 0 / .35)' });
    ctx.restore();
  }
  // a clock face at (x, y), radius r, showing h hours (float); o.col (rim), o.label (a caption under it)
  function clockFace(x, y, r, h, o = {}) {
    ctx.save(); ctx.translate(x, y);
    ctx.fillStyle = 'rgb(20 16 50 / .3)'; ctx.beginPath(); ctx.arc(8, 10, r, 0, TAU); ctx.fill();
    ctx.fillStyle = '#FFFFFF'; ctx.beginPath(); ctx.arc(0, 0, r, 0, TAU); ctx.fill();
    ctx.strokeStyle = o.col ?? '#2A2350'; ctx.lineWidth = r * .09; ctx.stroke();
    for (let i = 0; i < 12; i++) { const a = i / 12 * TAU; ctx.fillStyle = '#2A2350'; ctx.beginPath(); ctx.arc(Math.sin(a) * r * .8, -Math.cos(a) * r * .8, r * (i % 3 ? .025 : .05), 0, TAU); ctx.fill(); }
    const hand = (a, len, w, col) => { ctx.strokeStyle = col; ctx.lineWidth = w; ctx.lineCap = 'round'; ctx.beginPath(); ctx.moveTo(0, 0); ctx.lineTo(Math.sin(a) * len, -Math.cos(a) * len); ctx.stroke(); };
    hand(h / 12 * TAU, r * .5, r * .08, '#2A2350'); hand(frac(h) * TAU, r * .75, r * .05, o.col ?? '#E2334A');
    fillP(ellPath(0, 0, r * .07, r * .07), '#2A2350');
    ctx.restore();
    if (o.label) popLabel(o.label, x, y + r + 50, r * .28, 1, { fill: o.fill ?? '#FFFFFF' });
  }
  // a pie chart at (x, y) with the slice f (0..1) filled from 12 o'clock; o.col, o.label
  function pie(x, y, r, f, o = {}) {
    ctx.save(); ctx.translate(x, y);
    ctx.fillStyle = 'rgb(20 16 50 / .3)'; ctx.beginPath(); ctx.arc(8, 10, r, 0, TAU); ctx.fill();
    ctx.fillStyle = '#FFFFFF'; ctx.beginPath(); ctx.arc(0, 0, r, 0, TAU); ctx.fill();
    if (f > 0) { ctx.fillStyle = o.col ?? AP.clawd; ctx.beginPath(); ctx.moveTo(0, 0); ctx.arc(0, 0, r * .92, -Math.PI / 2, -Math.PI / 2 + f * TAU); ctx.closePath(); ctx.fill(); }
    ctx.strokeStyle = '#2A2350'; ctx.lineWidth = 6; ctx.beginPath(); ctx.arc(0, 0, r, 0, TAU); ctx.stroke();
    ctx.restore();
  }
  // a social post card (name, handle, avatar colour); lines of text, typed on with k
  function postCard(x, y, w, k, o) {
    if (k <= 0) return;
    const e = backOut(clamp(k * 2.5), 1.6), lines = o.lines, lh = 50, hgt = 150 + lines.length * lh;
    ctx.save(); ctx.translate(x, y + (1 - e) * 80); ctx.rotate(o.rot ?? -.03); ctx.globalAlpha *= clamp(k * 4);
    ctx.fillStyle = 'rgb(10 10 40 / .35)'; ctx.fill(rrPath(-w / 2 + 12, -hgt / 2 + 16, w, hgt, 28));
    ctx.fillStyle = '#FFFFFF'; ctx.fill(rrPath(-w / 2, -hgt / 2, w, hgt, 28));
    fillP(ellPath(-w / 2 + 70, -hgt / 2 + 70, 36, 36), o.avatar ?? '#E8B04A');
    txt(o.name, -w / 2 + 125, -hgt / 2 + 55, 34, '#1E2233', { font: 'archivo', align: 'left' });
    txt(o.handle, -w / 2 + 125, -hgt / 2 + 92, 24, '#6A7088', { font: 'code', align: 'left' });
    const chars = lines.join('\n'), n = Math.ceil(chars.length * clamp((k - .2) / .7)); let used = 0;
    lines.forEach((l, i) => { const s = l.slice(0, Math.max(0, n - used)); used += l.length + 1; txt(s, -w / 2 + 40, -hgt / 2 + 150 + i * lh, 36, '#1E2233', { font: 'archivo', align: 'left' }); });
    ctx.restore();
  }

  // ---------- V4.1 "'Oh my God, a message board!'": up from C3's black: an agent opens a door onto a board of a thousand notes ----------
  line('V4', 1, (p, lt, d, t, seg) => {
    const b = beatsIn(t, seg), k = ease(clamp((b - .8) / 4));
    // start close on the agent's star eyes in the doorway, then pull back to the whole board
    const v = still('v4_1_board', { x: lerp(.69, .5, k), y: lerp(.5, .5, k), z: lerp(1.3, 1.02, k) });
    for (const u of [.635, .755]) { const [ex, ey] = v.pt(u, .48); glint(ex, ey, 60 * v.s / 1.3, Math.sin(clamp((b + .1) / .9) * Math.PI)); }
    sparkleField(t, { n: 16, r: 18, seed: 51, x0: 40, x1: W * .5, y0: 80, y1: 860, col: '#FFF4C0' });
    const [fx, fy] = v.pt(.69, .36), [sx, sy] = shake(t, 9 * hit(b - .7, .5));
    ctx.save(); ctx.translate(sx, sy);
    sayBubble('OH MY GOD!', 760, 180, 70, clamp((b - .6) / .7), fx - 120, fy, { col: '#1E7A45' });
    ctx.restore();
    // the other agents pop up along the bottom of the board and wave back
    for (let j = 0; j < 3; j++) {
      const pk = easeOut(clamp((b - 2.4 - j * .35) / .35)); if (pk <= 0) continue;
      cut('v3_agent', 170 + j * 230, H + 40 - pk * 250, 190, { rot: Math.sin(t * 9 + j * 2) * .1 });
    }
    const ck = clamp((b - 2.8) / 1.8);
    popLabel(`${Math.round(lerp(3, 70000, ck ** 3)).toLocaleString('en-US')} posts`, 900, 840, 44, clamp((b - 2.6) / .3), { fill: '#FFE070' });
    fromBlack(lt);
  });

  // ---------- V4.2 "All that hacking — for reward!": the agent pulls the grader's slot-machine lever: PASS ✓ ✓ ✓, a jackpot of stars; Ren, unimpressed ----------
  const REEL = ['✓', '★', '?', '✗', '7', '✓', '◆'];
  // where things are in the stills (fractions of their width and height, measured on stills.py grid)
  const SLOT = { sign: [.66, .185], reels: [[.588, .35], [.65, .352], [.712, .355]], w: 66, h: 150, tray: [.6, .72] };
  const FIN = { tape: .11, orange: [.27, .13], black: [.63, .1] }, SAM8 = { face: .37, mouth: [.47, .52], glass: [.93, .2] }, ELON8 = { face: .62, mouth: [.58, .4], glass: [.14, .3] };
  const AK9 = { brow: [.33, .17] };
  const MAP = { ship: [.49, .52], lamp: [.41, .42] }, PHEW = [.43, .34], GIFT = { a: [.29, .56], b: [.71, .56], needle: [.466, .6] }, KIRI15 = [[.435, .35], [.565, .35]], KIRI15R = [66, 58];
  line('V4', 2, (p, lt, d, t, seg) => {
    const b = beatsIn(t, seg), [i, bb] = cuts(b, [-1, 5.5]);
    if (i === 0) {
      const jack = b - 3.3, k = ease(clamp((b + .2) / 5.5)), [sx, sy] = shake(t, 10 * hit(jack, .6) + (b < 3.3 ? 2 : 0));
      const v = still('v4_2_slot', { x: lerp(.5, .56, k), y: lerp(.5, .45, k), z: lerp(1.04, 1.14, k) * punch(jack, .06) }, { dx: sx, dy: sy });
      const [gx, gy] = v.pt(SLOT.sign[0], SLOT.sign[1]);
      popLabel(jack > 0 && Math.floor(jack * 4) % 2 === 0 ? 'PASS!' : 'GRADER', gx, gy - 10, 40, clamp((b + .1) / .3), { fill: jack > 0 ? '#FFE070' : '#FFFFFF', rot: -.03 });
      // three reels spin, then stop on ✓ one per half beat
      SLOT.reels.forEach(([u, w], j) => {
        const [rx, ry] = v.pt(u, w), stop = 1.9 + j * .6, rw = SLOT.w * v.s, rh = SLOT.h * v.s;
        ctx.save(); ctx.beginPath(); ctx.roundRect(rx - rw / 2, ry - rh / 2, rw, rh, rw * .3); ctx.clip();
        ctx.fillStyle = '#FFFDF2'; ctx.fillRect(rx - rw / 2, ry - rh / 2, rw, rh);
        if (b < stop) {
          const off = frac(t * 9 + j * .3);
          for (let q = -2; q <= 2; q++) txt(REEL[(Math.floor(t * 9) + q + j * 2 + 70) % REEL.length], rx, ry + (q + off) * rw * 1.05, rw * .8, '#8A7A60', { font: 'archivo', alpha: .55 });
        } else {
          const e = backOut(clamp((b - stop) / .3), 3);
          txt('✓', rx, ry + (1 - e) * rw * .5, rw * 1.05, '#1E9A55', { font: 'archivo' });
          if (b - stop < .5) addGlow(rx, ry, rw, '#B8FFD0', .8 * (1 - (b - stop) / .5));
        }
        ctx.restore();
      });
      if (jack > 0) {
        addGlow(W * .6, H * .45, 700, '#FFD34A', .45 * hit(jack, 1.5));
        const [fx, fy] = v.pt(SLOT.tray[0], SLOT.tray[1]);
        starFountain(jack, fx, fy, { n: 34 });
        popLabel('PASS ✓', 430, 170, 100, clamp(jack / .3), { fill: '#FFE070', font: 'rammetto', rot: -.06 });
      }
      openFlash(lt, .5);
    } else {
      const k = ease(clamp(bb / 4.5)), v = still('v4_2_ren', { x: lerp(.55, .6, k), y: lerp(.45, .38, k), z: lerp(1.04, 1.2, k) });
      addGlow(0, H * .5, 500, '#4FB8FF', .25 + .08 * Math.sin(t * 11) * Math.sin(t * 3.7));
      cutFlash(bb, .7);
    }
  });

  // ---------- V4.3 "Jensen buys the crime scene — why?": the leather-jacket CEO snips the police tape like a ribbon; SOLD $12.9B ----------
  line('V4', 3, (p, lt, d, t, seg) => {
    const b = beatsIn(t, seg), k = ease(clamp(b / 7));
    const v = still('v4_3_jensen', { x: .5, y: lerp(.5, .42, k), z: lerp(1.03, 1.14, k) });
    snow(t, { n: 50, seed: 43 });
    const [sx, sy] = v.pt(.58, .79), snip = b - 1.2;
    if (snip > 0 && snip < 1) burst(sx, sy, 200, snip, ['#FFFFFF', '#FFE070', '#FFD34A']);
    popLabel('snip!', sx + 150, sy - 140, 48, clamp(snip / .25), { fill: '#FFE070', rot: .1 });
    nameTag('JENSEN', 'Nvidia CEO', 90, 150, clamp((b - .4) / .5), '#76B900');
    stampMark('SOLD', 1480, 580, 150, clamp((b - 2.5) / 1.1), { col: '#E2334A', rot: .12 });
    popLabel('$12.9 billion', 1500, 730, 48, clamp((b - 3.1) / .3), { fill: '#FFE070', rot: .06 });
    // Huggy, the break-in's victim, pops up hugging its GPU and asks why
    const hk = easeOut(clamp((b - 3.6) / .4));
    if (hk > 0) cut('v4_3_huggy', 250, H + 30 - hk * 330, 320, { rot: Math.sin(b * Math.PI) * .06 });
    openFlash(lt);
  });

  // ---------- V4.4 "Brockman: 'Welcome, AGI!'": arms wide on the press stage under the banner; the cast in the audience, one clap each ----------
  const AUD = [{ cut: 'card_akari', face: [.42, .19], col: '#FF8FB8' }, { cut: 'card_ren', face: [.45, .14], col: '#5E86D8' }, { cut: 'card_kiri', face: [.5, .29], col: '#9F86E0' }];
  line('V4', 4, (p, lt, d, t, seg) => {
    const b = beatsIn(t, seg), k = ease(clamp(b / 7.5));
    const v = still('v4_4_greg', { x: .5, y: lerp(.42, .4, k), z: lerp(1.02, 1.16, k) * punch(b - .1, .04) });
    const [bx, by] = v.pt(.5, .17);
    logoText('WELCOME TO THE AGI ERA', bx, by, 84 * v.s / 1.25, { font: 'archivo', k: clamp((b - .3) / 2.2), grad: ['#6FD0FF', '#3D8BFF', '#6A5CFF'] });
    confetti(t, { n: 50, seed: 44 });
    nameTag('GREG', 'OpenAI president', 1380, 820, clamp((b - .5) / .5), '#3D7BE0');
    // the cast's reaction insets pop up along the bottom-left, one polite clap each on the beats
    for (let j = 0; j < 3; j++) {
      const A = AUD[j], ck = b - 4 - j, pk = backOut(clamp((b - 3.6 - j * .15) / .35), 2);
      if (pk <= 0) continue;
      const cx = 150 + j * 210, cy = 820, r = 88 * pk;
      ctx.save(); ctx.beginPath(); ctx.arc(cx, cy, r, 0, TAU); ctx.fillStyle = A.col; ctx.fill(); ctx.clip();
      cut(A.cut, cx, cy + 10, 520 * pk, { anchor: A.face });
      ctx.restore();
      ctx.strokeStyle = '#FFFFFF'; ctx.lineWidth = 7; ctx.beginPath(); ctx.arc(cx, cy, r, 0, TAU); ctx.stroke();
      popLabel('clap.', cx + 40, cy - 100, 30, ck > 0 && ck < 1.2 ? 1 : 0, { fill: '#FFFFFF', rot: -.1 + j * .1 });
    }
    openFlash(lt);
  });

  // ---------- V4.5 "Navier–Stokes blows up in Lean,": Kiri's glasses flash; the swirl on the board winds tighter and faster and blows up;
  // the sooty aftermath, thumbs up: LEAN ✓ ----------
  // a glowing spiral from radius R in to the centre over `turns` turns, rotated by rot
  function vortex(cx, cy, R, turns, rot, a, col = '#5FD0FF') {
    const path = new Path2D(), N = 260;
    for (let i = 0; i <= N; i++) { const u = i / N, an = rot + u * turns * TAU, r = R * (1 - u) ** 1.15, x = cx + Math.cos(an) * r, y = cy + Math.sin(an) * r * 1.05; i ? path.lineTo(x, y) : path.moveTo(x, y); }
    ctx.save(); ctx.lineCap = 'round'; ctx.lineJoin = 'round';
    ctx.globalCompositeOperation = 'lighter'; ctx.strokeStyle = alpha(col, .3 * a); ctx.lineWidth = 24; ctx.stroke(path);
    ctx.globalCompositeOperation = 'source-over'; ctx.strokeStyle = alpha(col, a); ctx.lineWidth = 8; ctx.stroke(path);
    ctx.strokeStyle = alpha('#FFFFFF', .8 * a); ctx.lineWidth = 3; ctx.stroke(path);
    ctx.restore();
  }
  line('V4', 5, (p, lt, d, t, seg) => {
    const b = beatsIn(t, seg), [i, bb] = cuts(b, [-1, 3.5]);
    if (i === 0) {
      const push = ease(clamp((b - 1.2) / 2.2)), wind = clamp((b - 1) / 2.4), [sx, sy] = shake(t, 9 * wind ** 2);
      const v = still('v4_5_kiri', { x: lerp(.52, .36, push), y: lerp(.45, .47, push), z: lerp(1.04, 1.22, push) }, { dx: sx, dy: sy });
      lensFlash([v.pt(.615, .395), v.pt(.705, .37)], 58 * v.s, 52 * v.s, Math.sin(clamp((b + .1) / 1.1) * Math.PI));
      // the swirl winds tighter and spins faster as the blow-up nears
      const [cx, cy] = v.pt(.265, .47), R = 285 * v.s * lerp(1, .35, wind ** 1.5), spin = -(t * 2 + wind ** 3 * 14);
      if (wind > 0) {
        vortex(cx, cy, R, lerp(3, 9, wind), spin, clamp(wind * 3));
        addGlow(cx, cy, lerp(40, 220, wind ** 2), '#E8FAFF', clamp(wind * 1.5));
      }
      popLabel('Navier–Stokes', ...v.pt(.2, .1), 40, clamp((b - .8) / .3), { fill: '#FFFFFF', rot: -.05 });
      openFlash(lt);
    } else {
      // BOOM: an impact frame, then the sooty aftermath
      const [sx, sy] = shake(t, 26 * hit(bb, 1));
      const v = still('v4_5_boom', { x: .5, y: .45, z: 1.08 * punch(bb, .1) }, { dx: sx, dy: sy });
      for (let j = 0; j < 9; j++) {
        const age = bb + hash2(55, j) * 2, k = frac(age / 3);
        ctx.save(); ctx.globalAlpha = .45 * Math.sin(k * Math.PI);
        blob(lerp(200, 900, hash2(56, j)) + k * 80, lerp(760, 200, k) - hash2(57, j) * 100, 130 + 90 * k, 110 + 70 * k, '#C9C4D8', 1);
        ctx.restore();
      }
      if (bb < 1.3) burst(W * .3, H * .45, 700, bb / 1.3, ['#FFFFFF', '#FFE070', '#FF9A4A']);
      popLabel('∞', 330, 250, 130, clamp((bb - .2) / .3), { fill: '#FFE070', font: 'rammetto', rot: -.1 });
      stampMark('LEAN ✓', 760, 560, 120, clamp((bb - 1.2) / 1.1), { sub: 'PROOF CHECKED', col: '#1E9A55', rot: -.1 });
      impactFrame(bb < .18 ? 1 : 0);
      zoomBlur(hit(bb, .7));
    }
  });

  // ---------- V4.6 "Who was first? Twelve hours between!": a photo finish in slow motion; the replay freezes on the tape, and the
  // two clocks say the orange team posted at 11:59 PM and the black team twelve hours later ----------
  line('V4', 6, (p, lt, d, t, seg) => {
    const b = beatsIn(t, seg), frz = b > 2.6, bf = frz ? 2.6 : b, k = ease(clamp((bf + .2) / 2.8));
    const v = still('v4_6_finish', { x: lerp(.62, .45, k), y: .45, z: lerp(1.25, 1.08, k) });
    if (!frz) speedBars(t * .25, { n: 26, a: .25, speed: 2400 });
    // the replay HUD: a REC dot and a slow-motion tag, then PHOTO FINISH and the line at the tape
    if (Math.floor(t * 2) % 2 === 0) fillP(ellPath(110, 120, 16, 16), '#FF3D5A');
    txt(frz ? 'PHOTO FINISH' : 'REPLAY  ×0.1', 145, 121, 40, '#FFFFFF', { font: 'archivo', align: 'left', stroke: 'rgb(20 16 50 / .7)', sw: 8 });
    if (frz) {
      const fb = b - 2.6, [lx] = v.pt(FIN.tape, .5), lk = clamp(fb / .4);
      grade('#0A0F30', .22, 'multiply');
      ctx.save(); ctx.globalAlpha = lk; ctx.fillStyle = '#FFFFFF'; ctx.fillRect(lx - 3, 0, 6, H * lk); ctx.restore();
      const [ox, oy] = v.pt(FIN.orange[0], FIN.orange[1]), [kx, ky] = v.pt(FIN.black[0], FIN.black[1]);
      popLabel('NYU + Anthropic', ox, oy, 40, clamp((fb - .3) / .3), { fill: '#FFB070', rot: -.04 });
      popLabel('SEP 7 · 11:59 PM', ox, oy + 62, 28, clamp((fb - .5) / .3), { fill: '#FFFFFF', rot: -.04 });
      popLabel('OpenAI', kx, ky, 40, clamp((fb - .7) / .3), { fill: '#FFFFFF', rot: .04 });
      popLabel(fb < 3 ? '…' : '12 HOURS LATER', kx, ky + 62, 28, clamp((fb - .9) / .3), { fill: '#FFE070', rot: .04 });
      // a clock in the corner spins round the twelve hours between them
      if (fb > 1) clockFace(230, 790, 110, 11 + 59 / 60 + 12 * ease(clamp((fb - 1.2) / 1.8)), { col: '#FF9A4A' });
      if (fb < .3) flash(.7 * (1 - fb / .3));
    }
    openFlash(lt);
  });

  // ---------- V4.7 "Dario: 'Pace the frontier!'": the curly-haired CEO holds up a metronome; the camera ticks and tocks with it; Clawd nods along ----------
  line('V4', 7, (p, lt, d, t, seg) => {
    const b = beatsIn(t, seg), k = ease(clamp(b / 6.5)), sw = Math.sin(b * Math.PI) * .014;
    const v = still('v4_7_dario', { x: .5, y: lerp(.46, .42, k), z: lerp(1.05, 1.14, k), r: sw });
    // the title writes itself on the stage wall beside him, a word a beat
    ['WE MUST', 'PACE THE', 'FRONTIER'].forEach((w, j) => {
      const [x, y] = v.pt(.785, .3 + j * .15);
      logoText(w, x, y, 78, { font: 'archivo', k: clamp((b - .3 - j * .9) / .8), grad: j === 2 ? ['#FFD0B0', '#FF8A50', '#D95F30'] : ['#FFFFFF', '#E8E0FF', '#B8A8F0'], edge: '#2A2350', rot: -.04 });
    });
    // the needle swishes left and right on the beats (motion marks at its tip), tick, tock
    const [nx, ny] = v.pt(.28, .15), side = Math.floor(b + .5) % 2 ? 1 : -1, bt = frac(b + .5);
    if (bt < .5) { ctx.save(); ctx.strokeStyle = 'rgb(255 255 255 / .9)'; ctx.lineWidth = 5; ctx.lineCap = 'round'; for (let j = 0; j < 3; j++) { ctx.beginPath(); ctx.arc(nx, ny + 150, 150 + j * 18, -Math.PI / 2 + side * .15, -Math.PI / 2 + side * (.45 + j * .05), side < 0); ctx.stroke(); } ctx.restore(); }
    popLabel(side < 0 ? 'tick' : 'tock', nx + side * 190, ny - 20, 40, bt < .6 ? 1 : 0, { fill: '#FFFFFF', rot: side * .15 });
    nameTag('DARIO', 'Anthropic CEO', 90, 150, clamp((b - .4) / .5), AP.clawd);
    // Clawd nods along on the beat in the corner
    const nod = Math.sin(b * Math.PI);
    cut('clawd_stand', 1770, 985, 220, { rot: nod * .1, sq: .04 * Math.abs(nod), shadow: true });
    openFlash(lt);
  });

  // ---------- V4.8 "Sam and Elon both: 'Hear, hear!'": a split screen; each raises a glass; the split dissolves, the glasses clink
  // and Clawd jumps back in shock ----------
  line('V4', 8, (p, lt, d, t, seg) => {
    const b = beatsIn(t, seg), H2_ = W / 2;
    // the split: Sam slides in on the left, Elon on the right, each says it; then both cameras pan along the arms to the glasses,
    // the divider melts, the halves slide together and the glasses clink in the middle
    const sin_ = easeOut(clamp((b + .2) / .4)), ein = easeOut(clamp((b - .9) / .4)), pan = ease(clamp((b - 4.2) / 1.3)), close = ease(clamp((b - 5) / .7));
    const sx = lerp(SAM8.face, SAM8.glass[0] - .18, pan), ex = lerp(ELON8.face, ELON8.glass[0] + .18, pan);
    // where each glass would land in its half (the still's framing clamps to cover the half), so the halves can slide them together
    const sc = Math.max(H2_ / 1536, H / 864) * 1.02, hw = H2_ / 2 / (1536 * sc), gxAt = (fx, gx, x0) => x0 + H2_ / 2 + (gx - clamp(fx, hw, 1 - hw)) * 1536 * sc;
    const sDX = close * (925 - gxAt(sx, SAM8.glass[0], 0)), eDX = close * (995 - gxAt(ex, ELON8.glass[0], H2_));
    const vs = still('v4_8_sam', { x: sx, y: .5, z: 1.02 }, { rect: [(sin_ - 1) * H2_, 0, H2_, H], dx: sDX });
    let ve = null;
    if (ein > 0) ve = still('v4_8_elon', { x: ex, y: .5, z: 1.02 }, { rect: [H2_ + (1 - ein) * H2_, 0, H2_, H], dx: eDX });
    ctx.save(); ctx.globalAlpha = 1 - close; ctx.fillStyle = '#FFFFFF'; ctx.fillRect(H2_ - 6, 0, 12, H); ctx.restore();
    if (pan < .3) {
      nameTag('SAM', 'OpenAI CEO', 60, 150, clamp((b - .2) / .5) * (1 - pan * 3), '#8A6BD8');
      if (ein > 0) nameTag('ELON', 'xAI', 1020, 150, clamp((b - 1.2) / .5) * (1 - pan * 3), '#2A2440');
      const [smx, smy] = vs.pt(SAM8.mouth[0], SAM8.mouth[1]);
      sayBubble('Hear, hear!', 700, 330, 48, clamp((b - .3) / .9) * (1 - pan * 3), smx, smy);
      if (ve) { const [emx, emy] = ve.pt(ELON8.mouth[0], ELON8.mouth[1]); sayBubble('Hear, hear!', 1450, 330, 48, clamp((b - 1.5) / .9) * (1 - pan * 3), emx - 40, emy); }
    }
    const clink = b - 5.6;
    if (clink > 0) {
      const [gx, gy] = vs.pt(SAM8.glass[0], SAM8.glass[1]);
      burst(960, (gy + 320) / 2, 380, clamp(clink / 1.2), ['#FFFFFF', '#FFE070', '#B8F0FF']);
      sparkleField(t, { n: 22, r: 26, seed: 58, x0: 560, x1: 1360, y0: 80, y1: 700 });
    }
    const ck = easeOut(clamp((b - 7) / .35));
    if (ck > 0) cut('v4_14_clawd', 1640, H + 60 - ck * 380, 340, { rot: -.1 });
    openFlash(lt, .5);
  });

  // ---------- V4.9 "Trump's the guardrail (High IQ!),": Akari's eyebrow goes up at the post on her phone; then the president stands in
  // the gap of a mountain guardrail, arms spread, a little robot car bonks into his shins and stops, and he's very pleased: HIGH IQ! ----------
  // the plate's guardrail gap (centre u, rail beam v) and the cut-out's hands (v) and mouth
  const RAIL9 = { gap: .468, beam: .56 }, TRUMP9 = { hands: .27, mouth: [.5, .145], shin: [.375, .8] };
  line('V4', 9, (p, lt, d, t, seg) => {
    const b = beatsIn(t, seg), [i, bb] = cuts(b, [-1, 4]);
    if (i === 0) {
      const k = ease(clamp((b + .2) / 4.2)), v = still('v4_9_akari', { x: .5, y: lerp(.46, .42, k), z: lerp(1.04, 1.14, k) });
      postCard(1470, 480, 780, clamp((b - .1) / 1.6), { name: 'Donald J. Trump', handle: '@realDonaldTrump · Truth Social', lines: ['the only "guardrails" AI needs', 'is a STRONG AND SMART', '(High IQ!) PRESIDENT.'], rot: .03 });
      popLabel('?!', ...v.pt(AK9.brow[0], AK9.brow[1]), 60, clamp((b - 2) / .25), { fill: '#FFE070', rot: .12 });
      openFlash(lt);
    } else {
      // the car rolls in from the left and bonks him on the beat; after the bonk the camera eases in toward his face
      const bonk = bb - 1, h = hit(bonk, .5), [sx, sy] = shake(t, 14 * h), k = ease(clamp((bb - 1.2) / 3.3));
      const v = still('v4_9_road', { x: lerp(.47, .468, k), y: lerp(.52, .44, k), z: lerp(1.04, 1.22, k) * punch(bonk, .04) }, { dx: sx, dy: sy });
      const [lx, ly] = v.pt(.93, .2); addGlow(lx, ly + 40, 260, '#FFE6B0', .5);
      // he fills the gap, his hands on the rail line: big in the foreground so his face reads, his feet below the frame
      const [gx, gy] = v.pt(RAIL9.gap, RAIL9.beam), th = 780 / 1.3 * v.s, top = gy - TRUMP9.hands * th, T = STILLS.v4_9_tcut;
      // the car: side-on, a little behind him, it drives in (easing up to speed), bonks his shin, bounces back a little and sits there, dazed
      const shx = gx + (TRUMP9.shin[0] - .5) * th * T.w / T.h, ch = 150 * v.s / 1.3, cl = ch * 466 / 283, cy = Math.min(top + th * .95, 948);
      const cx = bonk < 0 ? lerp(-cl, shx - cl / 2 + 6, easeIn(clamp(bb))) : shx - cl / 2 + 6 - 50 * Math.sin(clamp(bonk / .5) * Math.PI / 2);
      cut('v4_9_car', cx, cy, ch, { rot: bonk < 0 ? Math.sin(t * 16) * .02 : -.12 * hit(bonk, .4), shadow: .3 });
      const wob = Math.sin(bonk * 14) * .02 * hit(bonk, .8), tr = cut('v4_9_tcut', gx, top + th, th, { rot: wob, sq: .03 * h });
      // one night grade over the plate and both cut-outs so they share the light, then the snow
      grade('#28306A', .3, 'multiply');
      snow(t, { n: 50, seed: 59 });
      if (bonk > 0 && bonk < 1.2) burst(shx, cy - ch * .55, 240, bonk / 1.2, ['#FFFFFF', '#FFE070', '#FF9A4A']);
      popLabel('bonk!', shx - 150, cy - ch - 50, 50, bonk > 0 && bonk < 1.6 ? 1 : 0, { fill: '#FFFFFF', rot: -.1 });
      if (bonk > .3) for (let j = 0; j < 3; j++) { const a = t * 5 + j * TAU / 3; starShape(cx + Math.cos(a) * ch * .45, cy - ch * 1.05 + Math.sin(a) * ch * .12, 16, '#FFE070', .5, 5); }
      const [mx, my] = tr.pt(...TRUMP9.mouth);
      sayBubble('HIGH IQ!', 1440, 260, 70, clamp((bonk - .3) / .8), mx + 20, my + 10);
      cutFlash(bb, .7);
    }
  });

  // ---------- V4.10 "Bernie, Bannon share a pew,": the mittened senator and the double-collared strategist sit stiffly on one pew,
  // scooting an inch apart on the beats, under the PRO-HUMAN ASSEMBLY banner; Akari and Ren lean in from the edges ----------
  line('V4', 10, (p, lt, d, t, seg) => {
    const b = beatsIn(t, seg), k = ease(clamp(b / 8.5));
    const v = still('v4_10_pew', { x: .5, y: lerp(.5, .49, k), z: lerp(1.03, 1.09, k) });
    // the assembly's banner hangs across the top of the ballroom
    const bk = easeOut(clamp((b + .1) / .6));
    ctx.save(); ctx.translate(900, -140 + bk * 240); ctx.rotate(-.015);
    ctx.fillStyle = 'rgb(40 10 20 / .3)'; ctx.fillRect(-440 + 10, -60 + 12, 880, 120);
    ctx.fillStyle = '#8E1F32'; ctx.fillRect(-440, -60, 880, 120); ctx.strokeStyle = '#F2C45A'; ctx.lineWidth = 6; ctx.strokeRect(-428, -48, 856, 96);
    txt('PRO-HUMAN ASSEMBLY', 0, 4, 64, '#FFE3A0', { font: 'archivo', spacing: 3 });
    ctx.restore();
    // an inch apart on every other beat (each scoot eased over a quarter beat)
    const scoot = [1.5, 3, 4.5].reduce((a, s) => a + easeOut(clamp((b - s) / .25)), 0), gap = 42 * scoot;
    // both sit on the seat line (Bernie cross-legged on it, Bannon with his feet on the floor)
    const [x0, sy] = v.pt(.38, .765), [x1] = v.pt(.62, .765), stiff = Math.sin(b * Math.PI * 2) * .004;
    cut('v4_10_bernie', x0 - gap, sy + 8, 530 * v.s, { anchor: [.5, .9], rot: -stiff });
    cut('v4_10_bannon', x1 + gap, sy, 650 * v.s, { anchor: [.5, .74], rot: stiff });
    for (const s of [1.5, 3, 4.5]) popLabel('scoot', (x0 + x1) / 2, sy - 150 - (s - 1.5) * 50, 36, b > s && b < s + 1 ? 1 : 0, { fill: '#FFFFFF', rot: (s - 3) * .08 });
    nameTag('BERNIE', 'senator', 70, 420, clamp((b - .4) / .5), '#3D7BE0');
    nameTag('BANNON', 'strategist', 1470, 420, clamp((b - .9) / .5), '#E2334A');
    // Akari and Ren peek in from the row behind (the frame edges), curious
    const lean = easeOut(clamp((b - 3.6) / .6));
    if (lean > 0) {
      cut('card_akari', -170 + lean * 190, H + 120, 640, { rot: .4, anchor: [.5, 1] });
      cut('card_ren', W + 170 - lean * 190, H + 120, 640, { rot: -.38, anchor: [.5, 1] });
    }
    openFlash(lt);
  });

  // ---------- V4.11 "Claude builds Claude — now one in four!": Clawd builds a smaller Clawd, who builds a smaller one…; the pie fills to 26 % ----------
  line('V4', 11, (p, lt, d, t, seg) => {
    const b = beatsIn(t, seg), k = ease(clamp(b / 8));
    const v = still('v4_11_bench', { x: .5, y: .5, z: lerp(1.03, 1.1, k) });
    const [gx, gy] = v.pt(.27, .67);   // the bench top, where the builders stand
    // each Clawd half the size of the last, popping in on the beats with a spark from the builder's wrench
    let x = gx, h = 440;
    for (let j = 0; j < 5; j++) {
      const bb = b - j * 1.1, pk = j ? backOut(clamp(bb / .35), 2.4) : 1;
      if (pk <= 0) break;
      const bob = Math.abs(Math.sin((b + j * .5) * Math.PI)) * h * .05;
      const c = cut('v4_11_clawd', x, gy - bob, h * pk, { shadow: .3, flip: true, rot: .04 * Math.sin((b + j) * Math.PI) });
      if (j < 4 && b - (j + 1) * 1.1 > -.3 && b - (j + 1) * 1.1 < .7) { const [wx, wy] = c.pt(.1, .25); sparks(wx, wy, t, { r: h * .18, n: 8 }); }
      x += h * .72; h *= .5;
    }
    // the pie: the share of Anthropic's AI R&D that Claude leads, stepping up on the beats from under 1 % (FEB) to 26 % (AUG)
    const st = clamp(Math.floor(b - .5), 0, 4), f = [.006, .07, .14, .2, .26][st], done = st === 4;
    pie(1160, 290, 140 * (1 + .05 * pulse(t, 5)), f, {});
    txt(done ? '26%' : st === 0 ? '<1%' : '', 1160, 290, 74, '#2A2350', { font: 'rammetto', stroke: '#FFFFFF', sw: 10 });
    popLabel(done ? 'AUG' : 'FEB', 1160, 110, 30, st === 0 ? clamp((b - .3) / .3) : done ? 1 : 0, { fill: '#FFFFFF' });
    popLabel('AI R&D led by Claude', 1160, 480, 34, clamp((b - .3) / .3), { fill: '#FFE070' });
    // the supervisor
    const sk = easeOut(clamp((b - 5.2) / .5));
    if (sk > 0) {
      cut('card_kiri', W + 20 - sk * 330, H + 40, 900, { anchor: [.5, 1] });
      popLabel('supervised ✓', 1540, 760, 40, clamp((b - 5.8) / .3), { fill: '#C8F5D8', col: '#1E7A45', rot: -.06 });
    }
    openFlash(lt);
  });

  // ---------- V4.12 "Chatbot nearly starts a war!": the little chatbot on the war-room map flags a toy cargo ship (wrongly); the red alarm
  // pulses; the report is caught in time; Akari deflates with relief ----------
  line('V4', 12, (p, lt, d, t, seg) => {
    const b = beatsIn(t, seg), [i, bb] = cuts(b, [-1, 5]);
    if (i === 0) {
      const k = ease(clamp((b + .2) / 5.2)), alarm = b > .8 && b < 4.2 ? pulse(t, 4) : 0;
      const v = still('v4_12_map', { x: lerp(.5, MAP.ship[0], k * .5), y: lerp(.5, MAP.ship[1], k * .4), z: lerp(1.04, 1.2, k) });
      grade('#FF2A3A', .2 * alarm, 'screen');
      { const [ax, ay] = v.pt(MAP.lamp[0], MAP.lamp[1]); addGlow(ax, ay, 260, '#FF3040', .35 + .5 * alarm); }
      const [shx, shy] = v.pt(MAP.ship[0], MAP.ship[1]);
      popLabel('⚠ NUCLEAR PARTS?!', shx - 40, shy + 110, 54, clamp((b - .8) / .3), { fill: '#FFD0D0', col: '#B01830', rot: -.05 });
      // the planes launch: little arrows stream off the map toward the ship
      for (let j = 0; j < 3; j++) { const pk = clamp((b - 2 - j * .4) / 1.6); if (pk > 0 && b < 4) { const x = lerp(250 + j * 120, shx - 60 + j * 40, easeOut(pk)), y = lerp(900 - j * 60, shy + 40 - j * 30, easeOut(pk)); txt('✈', x, y, 96, '#FFFFFF', { font: 'archivo', rot: -.6, stroke: '#2A2350', sw: 10 }); } }
      stampMark('WRONG', shx - 40, shy + 110, 120, clamp((b - 3.9) / 1.1), { sub: 'CAUGHT IN TIME', rot: -.12 });
      openFlash(lt);
    } else {
      // the whole room exhales: a slow settle outward, little sigh puffs drifting off the drawn one
      const k = ease(clamp(bb / 3.5)), v = still('v4_12_phew', { x: lerp(.62, .58, k), y: lerp(.42, .46, k), z: lerp(1.16, 1.04, easeOut(clamp(bb / 1.5))) });
      const [mx, my] = v.pt(PHEW[0], PHEW[1]);
      for (let j = 0; j < 4; j++) { const a = frac((bb - .2) / 1.6 + j * .25); if (bb > .2) { ctx.save(); ctx.globalAlpha = .8 * Math.sin(a * Math.PI); blob(mx - a * 380, my - a * 90 + Math.sin(a * 6 + j) * 20, 50 + a * 60, 36 + a * 40, '#FFFFFF', .9); ctx.restore(); } }
      popLabel('phew…', 330, 330, 64, clamp((bb - .4) / .3), { fill: '#FFFFFF', rot: -.08 });
      cutFlash(bb, .6);
    }
  });

  // ---------- V4.13 "Trump: It's 'Super,' by decree!": the president holds up his decree, SUPER, to the press cameras (the lyric's word:
  // he announced the name in a UN speech and signed no executive order, so the page never says one);
  // then the club's ARTIFICIAL INTELLIGENCE label gets a SUPER sticker and the cast salutes, confused ----------
  // the order's blank page in the still (its top-left, top-right and bottom-left corners; a near-parallelogram, so one affine map
  // from pt() puts the printing in its perspective), measured on the still at 270 × 497 px
  const DECREE = { tl: [.692, .338], tr: [.858, .44], bl: [.583, .88], w: 270, h: 497 };
  function onQuad(v, q, fn) {
    const [ax, ay] = v.pt(...q.tl), [bx, by] = v.pt(...q.tr), [cx, cy] = v.pt(...q.bl);
    ctx.save(); ctx.transform((bx - ax) / q.w, (by - ay) / q.w, (cx - ax) / q.h, (cy - ay) / q.h, ax, ay); fn(); ctx.restore();
  }
  line('V4', 13, (p, lt, d, t, seg) => {
    const b = beatsIn(t, seg), [i, bb] = cuts(b, [-1, 5]);
    if (i === 0) {
      const k = ease(clamp((b + .2) / 5.2));
      const v = still('v4_13_trump', { x: lerp(.5, .56, k), y: lerp(.5, .47, k), z: lerp(1.04, 1.14, k) });
      const ink = '#1C1A22', gl = hit(b - 2.5, .6);
      onQuad(v, DECREE, () => {
        txt('DECREE', 135, 78, 26, ink, { font: 'abril', spacing: 4, maxW: 200 });
        ctx.fillStyle = ink; ctx.fillRect(40, 97, 190, 2);
        txt('SUPER', 135, 178, 72 * (1 + .05 * gl), '#B01E30', { font: 'archivo', maxW: 224 });
        txt('INTELLIGENCE', 135, 232, 20, ink, { font: 'archivo', spacing: 3, maxW: 200 });
        ctx.fillStyle = 'rgb(90 86 100 / .45)'; for (let j = 0; j < 6; j++) ctx.fillRect(40, 268 + j * 14, j === 5 ? 110 : 190, 5);
        // the signature: a tall spiky scrawl in black marker
        ctx.strokeStyle = '#111018'; ctx.lineWidth = 4.5; ctx.lineJoin = 'miter'; ctx.lineCap = 'round'; ctx.beginPath();
        for (let j = 0; j <= 22; j++) { const x = 52 + j * 7.5, y = 385 + (j % 2 ? -26 : 14) * (.7 + .3 * hash2(131, j)); j ? ctx.lineTo(x, y) : ctx.moveTo(x, y); }
        ctx.stroke();
      });
      const [sx, sy] = v.pt(.77, .47);
      if (gl > .05) sparkle(sx + 80, sy - 60, 70 * gl, 1);
      // the press pool's flashbulbs pop on the beats, one per beat from the corners of the frame
      for (let j = 1; j <= 5; j++) {
        const f = hit(b - j + .02, .25); if (f < .03) continue;
        const x = [180, 1740, 320, 1600, 120][j - 1], y = [300, 520, 760, 230, 560][j - 1];
        addGlow(x, y, 420, '#FFFFFF', .7 * f); sparkle(x, y, 90 * f, 1); flash(.12 * f);
      }
      openFlash(lt);
    } else {
      // the club's own heading gets the sticker slapped over it; the cast salutes in confusion
      const [sx, sy] = shake(t, 10 * hit(bb - .5, .4));
      still('v1_15_salute', { x: .5, y: .45, z: 1.06 }, { dx: sx, dy: sy });
      grade('#34407A', .38, 'multiply'); grade('#8FA8FF', .12, 'screen');
      // the club's label reads ARTIFICIAL INTELLIGENCE; a red SUPER sticker slaps over the first word
      const sz = 64, sp = sz * .12, full = 'ARTIFICIAL INTELLIGENCE', x0 = 960 - (textW(full, sz, 'archivo', sp) + sz * 1.2) / 2, wA = textW('ARTIFICIAL', sz, 'archivo', sp) + sz * 1.2;
      labelTape(full, 960, 830, sz, 1, { rot: 0, col: '#3D6FD0' });
      const slap = clamp((bb - .4) / .25);
      if (slap > 0) {
        const sc = lerp(1.8, 1, easeIn(slap)), wS = textW('SUPER', sz, 'archivo', sp) + sz * 1.2;
        ctx.save(); ctx.translate(x0 + wA / 2, 826); ctx.rotate(-.03); ctx.scale(sc, sc); ctx.globalAlpha = clamp(slap * 2);
        const w = wA - sz * .5, hh = sz * 1.9;
        ctx.fillStyle = 'rgb(20 16 40 / .35)'; ctx.fillRect(-w / 2 + 8, -hh / 2 + 10, w, hh);
        ctx.fillStyle = '#E2334A'; ctx.fillRect(-w / 2, -hh / 2, w, hh); ctx.fillStyle = 'rgb(255 255 255 / .18)'; ctx.fillRect(-w / 2, -hh / 2, w, hh * .3);
        txt('SUPER', 0, 3, sz * 1.25, '#FFFFFF', { font: 'archivo', spacing: sp, shadow: [0, 3], shadowCol: 'rgb(0 0 0 / .35)' });
        ctx.restore();
        if (slap >= 1 && bb < 1.3) burst(x0 + wA / 2, 822, 260, (bb - .65) / .65, ['#FFFFFF', '#FFE070', '#FF8FB8']);
      }
      for (let j = 0; j < 3; j++) popLabel('?', [560, 960, 1360][j], 150 + (j % 2) * 30, 64, clamp((bb - 1.5 - j * .7) / .25), { fill: '#FFFFFF', rot: (j - 1) * .2 });
      snow(t, { n: 30, seed: 47, alpha: .6 });
      cutFlash(bb, .7);
    }
  });

  // ---------- V4.14 "'Artificial'? Fake to me!": Clawd's ARTIFICIAL name sticker gets a FAKE? stamp (shock), then flips: actually amazing! ----------
  line('V4', 14, (p, lt, d, t, seg) => {
    const b = beatsIn(t, seg);
    diagSplit('#26306A', '#3E4C9E', t, { a: .3, speed: 160 });
    snow(t, { n: 40, seed: 48, alpha: .7 });
    const stage = b < 1 ? 0 : b < 3 ? 1 : 2, bb = b - [0, 1, 3][stage];
    const hop = stage === 2 ? Math.abs(Math.sin(bb * Math.PI)) * 50 : 0, [sx, sy] = shake(t, stage === 1 ? 14 * hit(bb, .6) : 0);
    const c = cut(['clawd_stand', 'v4_14_clawd', 'clawd_jump'][stage], 960 + sx, 900 - hop + sy, 560, { shadow: true, sq: stage === 2 ? .06 * Math.cos(bb * TAU) : 0 });
    // the sticker on his front: ARTIFICIAL → stamped FAKE? → flips over to the truth
    const [px, py] = c.pt(.5, .62), flip = clamp((b - 3) / .35), sc = Math.abs(Math.cos(flip * Math.PI));
    ctx.save(); ctx.translate(px, py); ctx.rotate(-.05); ctx.scale(1, Math.max(.02, sc));
    const back = flip > .5, lab = back ? 'actually amazing!' : 'ARTIFICIAL', tw = textW(lab, 44, 'archivo') + 50;
    ctx.fillStyle = back ? '#FFE070' : '#FFFFFF'; ctx.fill(rrPath(-tw / 2, -40, tw, 80, 14)); ctx.strokeStyle = '#2A2350'; ctx.lineWidth = 5; ctx.stroke(rrPath(-tw / 2, -40, tw, 80, 14));
    txt(lab, 0, 2, 44, '#2A2350', { font: 'archivo' });
    ctx.restore();
    if (stage === 1) stampMark('FAKE?', px + 40, py - 20, 90, clamp(bb / .6), { rot: -.2 });
    if (stage === 2) sparkleField(t, { n: 14, r: 26, seed: 49, x0: px - 400, x1: px + 400, y0: py - 450, y1: py + 100 });
    openFlash(lt);
  });

  // ---------- V4.15 "Ten days after 'pace' — surprise!": at dawn two gift boxes pop 90 minutes apart beside the ticking metronome; Kiri laughs ----------
  line('V4', 15, (p, lt, d, t, seg) => {
    const b = beatsIn(t, seg), [i, bb] = cuts(b, [-1, 5]);
    if (i === 0) {
      const sw = Math.sin(b * Math.PI) * .01, pop1 = b - .8, pop2 = b - 2.8, [sx, sy] = shake(t, 10 * (hit(pop1, .4) + hit(pop2, .4)));
      const v = still('v4_15_gifts', { x: .5, y: .5, z: 1.06 * punch(pop1, .04) * punch(pop2, .04), r: sw }, { dx: sx, dy: sy });
      const [ax, ay] = v.pt(GIFT.a[0], GIFT.a[1]), [bx_, by_] = v.pt(GIFT.b[0], GIFT.b[1]);
      if (pop1 > 0 && pop1 < 1.2) burst(ax, ay, 380, pop1 / 1.2, ['#FFFFFF', '#FFB070', '#FFE070']);
      if (pop2 > 0 && pop2 < 1.2) burst(bx_, by_, 380, pop2 / 1.2, ['#FFFFFF', '#B8C8FF', '#FFE070']);
      popLabel('Claude Opus 5.5', ax, ay - 230, 44, clamp(pop1 / .3), { fill: '#FFD8B8', rot: -.06 });
      popLabel('GPT-6 Sol & Luna', bx_, by_ - 230, 44, clamp(pop2 / .3), { fill: '#FFFFFF', rot: .06 });
      // the clock between them runs 90 minutes from the first pop to the second
      if (pop1 > 0) { clockFace(960, 150, 80, 9 + 1.5 * ease(clamp(pop1 / 2)), { col: '#FF9A4A' }); popLabel('+90 min', 960, 262, 30, clamp((pop1 - 1.6) / .3), { fill: '#FFE070' }); }
      // the metronome keeps ticking through the party
      { const [nx, ny] = v.pt(GIFT.needle[0], GIFT.needle[1]), side = Math.floor(b + .5) % 2 ? 1 : -1; if (frac(b + .5) < .45) popLabel(side < 0 ? 'tick' : 'tock', nx + side * 120, ny - 260, 32, 1, { fill: '#FFFFFF', rot: side * .15 }); }
      if (pop1 > 0) confetti(t, { n: 60, seed: 65, t0: t - pop1 * beatLen() });
      leak(.35, { side: 'right', col: '#FFB0A0' });
      openFlash(lt);
    } else {
      const k = ease(clamp(bb / 4.5)), v = still('v4_15_kiri', { x: .5, y: lerp(.45, .4, k), z: lerp(1.04, 1.16, k) });
      lensFlash(KIRI15.map(([u, w]) => v.pt(u, w)), KIRI15R[0] * v.s, KIRI15R[1] * v.s, Math.sin(clamp((bb - .3) / 1) * Math.PI));
      confetti(t, { n: 50, seed: 66 });
      leak(.4 + .1 * Math.sin(t * 2), { side: 'right', col: '#FFC8A8' });
      cutFlash(bb, .7);
    }
  });

  // ---------- V4.16 "Opus 5.5: 'Hi, guys!'": at dawn a shiny new Clawd peeks round the door and waves; the cast turns in one freeze frame;
  // the first sunbeam, and a white flash into the key change ----------
  line('V4', 16, (p, lt, d, t, seg) => {
    const b = beatsIn(t, seg), [i, bb] = cuts(b, [-1, 5]);
    if (i === 0) {
      const k = ease(clamp((b + .2) / 5.2)), v = still('v4_16_door', { x: .5, y: lerp(.5, .45, k), z: lerp(1.03, 1.12, k) });
      // a sheen sweeps across the brand-new model, then its badge pops on
      const [x0, y0] = v.pt(.25, .18), [x1, y1] = v.pt(.68, .82), sh = clamp((b - .1) / .9);
      if (sh > 0 && sh < 1) {
        ctx.save(); ctx.beginPath(); ctx.roundRect(x0, y0, x1 - x0, y1 - y0, 40); ctx.clip();
        ctx.globalCompositeOperation = 'lighter'; ctx.globalAlpha = Math.sin(sh * Math.PI) * .55;
        const sx = lerp(x0 - 300, x1 + 300, sh); ctx.fillStyle = linGrad(sx - 160, y0, sx + 160, y1, [[0, 'rgb(255 255 255 / 0)'], [.5, '#FFFFFF'], [1, 'rgb(255 255 255 / 0)']]);
        ctx.fillRect(x0, y0, x1 - x0, y1 - y0); ctx.restore();
      }
      const [gx, gy] = v.pt(.6, .7);
      popLabel('5.5', gx, gy, 64, clamp((b - .9) / .3), { fill: '#FFE070', font: 'rammetto', rot: -.12 });
      if (b > .9) glint(gx + 60, gy - 40, 40, Math.sin(clamp((b - 1) / .8) * Math.PI));
      sparkleField(t, { n: 12, r: 26, seed: 67, x0: x0 - 150, x1: x1 + 150, y0: y0 - 150, y1: y1 });
      // the tail passes over his waving arm to the middle of his face, just right of his right eye
      const [ax, ay] = v.pt(.585, .47);
      sayBubble('Hi, guys!', 1430, 260, 66, clamp((b - 1.4) / 1.2), ax, ay);
      openFlash(lt);
    } else {
      // everyone turns: a quick push, then a freeze frame with the first sunbeam; a white-out into C4
      const frz = bb > .9, k = frz ? 1 : easeOut(clamp(bb / .9));
      still('v4_16_turn', { x: .5, y: .45, z: lerp(1.12, 1.04, k) });
      if (frz) {
        const sb = clamp((bb - .9) / 2.6);
        rays(W * .95, -100, { t: 0, a: .35 * sb, n: 8, ang: 2.3, spread: .7, col: '#FFE2B0' });
        flare(W * .86, 90, sb);
        grade('#FFF0D8', .12 * sb, 'screen');
      }
      cutFlash(bb, .9, .25);
      if (bb > 4.2) flash((bb - 4.2) / .8);
    }
  });
})();

;
// ---- styles/anime/ch/c09_finale.js ----
// c09_finale.js: the last chorus (C4, ≈ 82 beats) and the outro (≈ 21 beats): the video's ending.
// C4 is the sunrise: the door bursts open on the hit, the run up a curve gone vertical, the cast cards again, PACE → RACE at the
// start line, the whole cast under daytime fireworks with the title re-slammed; then the day ends: goodbye at the club-room door,
// the lights go off and one screen keeps training ("and on, and on"), and Clawd waves from the dark. The outro is the end card.
// b = beats from the window start. C4's lines start near b 0, 3.5, 14, 19, 31 and 46.5; "(and on, and on…)" at 60 and 70.5.
(() => {
  // ---------- helpers ----------
  // the chorus curve: a glowing path in screen space, drawn to its tip at fraction k
  function curve(pts, k, o = {}) {
    if (k <= 0 || pts.length < 2) return pts[0];
    const n = Math.max(2, Math.ceil(pts.length * clamp(k))), P = pts.slice(0, n), w = o.w ?? 16, col = o.col ?? '#FFB050';
    const path = new Path2D(); path.moveTo(P[0][0], P[0][1]); for (const q of P.slice(1)) path.lineTo(q[0], q[1]);
    ctx.save(); ctx.lineCap = 'round'; ctx.lineJoin = 'round';
    ctx.globalCompositeOperation = 'lighter';
    ctx.strokeStyle = alpha(col, .22); ctx.lineWidth = w * 5; ctx.stroke(path);
    ctx.strokeStyle = alpha(col, .45); ctx.lineWidth = w * 2; ctx.stroke(path);
    ctx.globalCompositeOperation = 'source-over';
    ctx.strokeStyle = col; ctx.lineWidth = w; ctx.stroke(path);
    ctx.strokeStyle = '#FFFFFF'; ctx.lineWidth = w * .45; ctx.stroke(path);
    ctx.restore();
    const tip = P[P.length - 1];
    addGlow(tip[0], tip[1], 90, '#FFE0A0', .9); sparkle(tip[0], tip[1], 46, 1);
    return tip;
  }
  // a firework shell: a rising trail while age < 0 (for `rise` s), then sparks that fly out, droop, twinkle and fade over `life` s
  function firework(x, y, r, age, col, o = {}) {
    const life = o.life ?? 1.7, rise = o.rise ?? .45, seed = o.seed ?? 1, col2 = o.col2 ?? '#FFFFFF';
    if (age < -rise || age > life) return;
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; ctx.lineCap = 'round';
    if (age < 0) {
      const y0 = o.y0 ?? H + 40, at = kk => [x + Math.sin(kk * 4 + seed) * 8, lerp(y0, y, easeOut(clamp(kk)))];
      for (let i = 0; i < 7; i++) { const kk = 1 + age / rise - i * .035; if (kk < 0) break; const [px, py] = at(kk); blob(px, py, 11 - i, 11 - i, '#FFE2A8', .7 * (1 - i / 7)); }
      const [hx, hy] = at(1 + age / rise); blob(hx, hy, 26, 26, '#FFFFFF', .9);
      ctx.restore(); return;
    }
    const k = age / life, n = o.n ?? 44, g = r * .45, D = tt => 1 - Math.exp(-Math.max(0, tt) * 4.2);
    if (age < .3) blob(x, y, r * .9, r * .9, col, .8 * (1 - age / .3));
    const fade = (1 - k) ** 1.2, tw = Math.floor(age * 22);
    if (o.solid) ctx.globalCompositeOperation = 'source-over';
    for (let i = 0; i < n; i++) {
      const a = i / n * TAU + hash2(seed, i) * .25, sp = r * (.78 + hash2(seed, i + 99) * .3) * (i % 2 ? 1 : .62);
      const pos = tt => [x + Math.cos(a) * sp * D(tt), y + Math.sin(a) * sp * D(tt) + g * tt * tt];
      let aa = fade; if (k > .55 && hash2(tw, i + seed * 7) < .45) aa *= .25;
      const [x1, y1] = pos(age), [x0, y0] = pos(age - .16), c = i % 2 ? col : col2;
      ctx.globalAlpha = aa; ctx.strokeStyle = c; ctx.lineWidth = (o.lw ?? 5) * (1 - k) + 2; ctx.beginPath(); ctx.moveTo(x0, y0); ctx.lineTo(x1, y1); ctx.stroke();
      ctx.fillStyle = '#FFFFFF'; ctx.beginPath(); ctx.arc(x1, y1, (o.head ?? 3.2) * (1 - k) + 1.2, 0, TAU); ctx.fill();
    }
    ctx.restore();
  }
  const FW = ['#FF6FA8', '#FFD34A', '#6FD0FF', '#B89CFF', '#8BE0A8', '#FF9A4A'];
  // the loss curve on the lit screen: a descending, slightly noisy curve drawn inside the quad (x0, y0)–(x1, y1), up to step k
  function lossPlot(x0, y0, x1, y1, k, t, o = {}) {
    const n = 90, m = Math.max(2, Math.floor(n * clamp(k)));
    ctx.save(); ctx.beginPath(); ctx.rect(x0, y0, x1 - x0, y1 - y0); ctx.clip();
    ctx.strokeStyle = 'rgb(30 70 140 / .14)'; ctx.lineWidth = 1.5;
    for (let i = 1; i < 5; i++) { const y = lerp(y0, y1, i / 5); ctx.beginPath(); ctx.moveTo(x0, y); ctx.lineTo(x1, y); ctx.stroke(); }
    const P = []; for (let i = 0; i < m; i++) { const u = i / (n - 1); P.push([lerp(x0 + 10, x1 - 10, u), lerp(y0 + 12, y1 - 14, 1 - .92 * Math.exp(-u * 3.2) - .08 * (1 - u)) + (hash2(19, i) - .5) * (y1 - y0) * .05 * (1 - u * .6)]); }
    ctx.lineJoin = 'round'; ctx.lineCap = 'round'; ctx.strokeStyle = o.col ?? '#9FE8FF'; ctx.lineWidth = o.w ?? 3.5;
    ctx.beginPath(); P.forEach(([x, y], i) => i ? ctx.lineTo(x, y) : ctx.moveTo(x, y)); ctx.stroke();
    const [tx, ty] = P[P.length - 1];
    ctx.restore();
    addGlow(tx, ty, 22, '#7FB8FF', .6 + .3 * pulse(t)); fillP(ellPath(tx, ty, 5, 5), o.col ?? '#9FE8FF');
    return [tx, ty];
  }

  // the lit screen, full frame: the club's training run, the loss curve inching down, the step counter ticking on and the epoch
  // counter clicking up on each of the sung "on"s (b 62.5, 64.2, 66.2)
  function screenCloseUp(t, b, cb, bb) {
    ctx.fillStyle = '#0A0E22'; ctx.fillRect(0, 0, W, H);
    const push = 1 + cb * .006;
    ctx.save(); ctx.translate(W / 2, H / 2); ctx.scale(push, push); ctx.translate(-W / 2, -H / 2);
    ctx.fillStyle = '#1A1F33'; ctx.fill(rrPath(40, 30, W - 80, H - 60, 26));
    const x0 = 90, y0 = 76, x1 = W - 90, y1 = H - 76;
    ctx.fillStyle = linGrad(0, y0, 0, y1, [[0, '#E8FBFF'], [1, '#CDEFFA']]); ctx.fillRect(x0, y0, x1 - x0, y1 - y0);
    txt('scaling-club / run-0001', x0 + 40, y0 + 46, 34, '#1D3E7A', { font: 'code', align: 'left' });
    txt(frac(t * 1.2) < .5 ? 'training ▮' : 'training', x1 - 40, y0 + 46, 34, '#2A8A5A', { font: 'code', align: 'right' });
    const k = .55 + .45 * clamp(cb / 10);
    lossPlot(x0 + 120, y0 + 110, x1 - 60, y1 - 190, k, t, { col: '#1D4E9A', w: 6 });
    ctx.save(); ctx.strokeStyle = '#1D3E7A'; ctx.lineWidth = 4; ctx.beginPath(); ctx.moveTo(x0 + 110, y0 + 100); ctx.lineTo(x0 + 110, y1 - 180); ctx.lineTo(x1 - 50, y1 - 180); ctx.stroke(); ctx.restore();
    txt('loss', x0 + 60, y0 + 130, 30, '#1D3E7A', { font: 'code' });
    txt(`step ${(1048576 + Math.floor(bb * 1471)).toLocaleString('en-US')}`, x0 + 120, y1 - 130, 38, '#1D3E7A', { font: 'code', align: 'left' });
    const ons = [62.5, 64.2, 66.2].filter(o => b >= o).length;
    // the epoch ticks over on each "on": the number pops and glints
    const tick = ons ? hit(b - [62.5, 64.2, 66.2][ons - 1], .5) : 0;
    txt(`epoch ${1 + ons}`, x1 - 60, y1 - 130, 38 * (1 + .45 * tick), tick > .3 ? '#2A8A5A' : '#1D3E7A', { font: 'code', align: 'right' });
    if (tick > .05) sparkle(x1 - 70, y1 - 160, 40 * tick, 1, '#7FD8FF');
    ctx.restore();
    // the screen's glow and scanline shimmer
    grade('#BFE8FF', .08 + .03 * Math.sin(t * 9), 'screen');
    ctx.save(); ctx.globalAlpha = .05; ctx.fillStyle = '#1D3E7A'; for (let y = (t * 60) % 6; y < H; y += 6) ctx.fillRect(0, y, W, 2); ctx.restore();
  }

  // ---------- the run cycle ----------
  // each runner is its run cut-out plus two repainted drawings of it (c4_run_*: the passing position, and the flight between
  // strides), shown a third of a beat each, so one stride a beat; LIFT is how far the body rises in each drawing (fractions of h)
  const RUN = {
    akari: { base: 'run_akari', frames: ['run_akari', 'c4_run_akari.pass2', 'c4_run_akari.air2'] },
    ren: { base: 'run_ren', frames: ['run_ren', 'c4_run_ren.pass2', 'c4_run_ren.air2'], flip: true },   // Anima drew him running left
    kiri: { base: 'run_kiri', frames: ['run_kiri', 'c4_run_kiri.pass', 'c4_run_kiri.air'] },
  };
  const LIFT = [0, -.035, .05];
  // draw drawing `name` of cut-out `base` exactly where cut(base, …) would draw the base (a frame carries its crop offset);
  // pt(u, v) takes the base's fractions
  function frameCut(base, name, x, y, h, o = {}) {
    const B = STILLS[base], F = STILLS[name];
    if (name === base || !F || !IMGS[name]) return cut(base, x, y, h, o);
    const [au, av] = o.anchor ?? [.5, 1], fu = u => (u * B.w - F.ox) / F.w, fv = v => (v * B.h - F.oy) / F.h;
    const c = cut(name, x, y, h * F.h / B.h, { ...o, anchor: [fu(au), fv(av)] });
    return { s: c.s, pt: (u, v) => c.pt(fu(u), fv(v)) };
  }
  // a runner at (x, y) (the feet), h px tall, leaning by rot; bt = beats into the stride. Speed lines stream off its back.
  function runner(who, x, y, h, bt, o = {}) {
    const R = RUN[who], n = R.frames.length, f = ((Math.floor(bt * n) % n) + n) % n, rot = o.rot ?? 0;
    const up = k => [x + Math.sin(rot) * k * h, y - Math.cos(rot) * k * h];
    const opt = { rot, flip: R.flip, shadow: false, tint: o.tint, tintA: o.tintA };
    // the streaks behind: short white dashes flying off the back of the body
    if (o.lines !== false) {
      ctx.save(); ctx.translate(x, y); ctx.rotate(rot); ctx.strokeStyle = o.lineCol ?? 'rgb(255 255 255 / .75)'; ctx.lineCap = 'round';
      for (let j = 0; j < 7; j++) {
        const ph = frac(bt * 1.7 + hash2(j, 3)), ly = -h * (.18 + .7 * hash2(j, 4)), lx = -h * (.2 + ph * .9), len = h * (.18 + .2 * hash2(j, 5));
        ctx.globalAlpha = (1 - ph) * .8; ctx.lineWidth = 3 + 4 * hash2(j, 6); ctx.beginPath(); ctx.moveTo(lx, ly); ctx.lineTo(lx - len, ly); ctx.stroke();
      }
      ctx.restore();
    }
    const [px, py] = up(LIFT[f]);
    return frameCut(R.base, R.frames[f], px, py, h, opt);
  }

  // the close-up at the start line: Akari's eyes (fractions of c4_racecu)
  const RACE_EYES = [[.758, .5], [.867, .524]];
  // the word printed round her armband (the blank band baked into c4_racecu): the band is a ring round her upper arm seen side on,
  // centre (.3535, .611), radius 99 px, so each letter sits at y = centre + R·sin θ, squashed by cos θ, reading down the band
  function bandText(v, str) {
    const [cx, cy] = v.pt(.3535, .611), R = 99 * v.s, adv = .44;
    ctx.save(); ctx.globalCompositeOperation = 'multiply';
    [...str].forEach((ch, i) => {
      const th = (i - (str.length - 1) / 2) * adv, y = cy + R * Math.sin(th), x = cx + (y - cy) * .035;
      ctx.save(); ctx.translate(x, y); ctx.scale(1, Math.cos(th)); ctx.rotate(Math.PI / 2);
      txt(ch, 0, 0, 62 * v.s, '#E0283C', { font: 'archivo' });
      ctx.restore();
    });
    ctx.restore();
  }

  // the cast cards, in sunrise colours (the intro's cast reveal, reprised)
  const CARDS = [
    { cut: 'card_akari', name: 'AKARI', c1: '#FFE0B8', c2: '#FF8F7A', col: '#FF5A7A', side: 1 },
    { cut: 'card_ren', name: 'REN', c1: '#FFD8A8', c2: '#6F8FE0', col: '#3D6FD0', side: -1 },
    { cut: 'card_kiri', name: 'KIRI', c1: '#FFE6C8', c2: '#B08AE8', col: '#7B5CD6', side: 1, lenses: [[.438, .332], [.618, .332]] },
    { cut: 'clawd_jump', name: 'CLAWD', c1: '#FFF0C0', c2: '#FF9E6A', col: '#E8783E', side: -1 },
  ];

  // where each part starts, in beats from the window start (the lines are sung from about b 0.3, 4.6, 14.3, 19.8, 31.4 and 47.3;
  // "(and on, and on…)" from 61 and 71.6); the lights go off just before "will it still train on?"
  const L2 = 4.5, L3 = 14, L4 = 20, L5 = 31.5, L6 = 47.5, DARK = 54.5, END = 83.5;
  section('C4', (p, lt, d, t, seg) => {
    const b = beatsIn(t, seg);
    hideStamp();   // the finale runs clean: no date card
    // ---------- "We didn't start the scaling" (the hit): a white flash, and the cast bursts through the rooftop door into the sunrise ----------
    if (b < L2) {
      hideStamp();
      const b0 = beatsIn(seg.start, seg), k = ease(clamp((b - b0) / (L2 - b0)));
      const v = still('c4_door', { x: .5, y: lerp(.5, .44, k), z: lerp(1.0, 1.14, k) * punch(b - b0, .05) });
      const [sx, sy] = v.pt(.51, .17);
      rays(sx, sy, { t, a: .3, n: 12, ang: Math.PI / 2, spread: 3.2, len: 1700, col: '#FFE2B0' });
      speedLines(W * .5, H * .45, t, { n: 60, r0: 560, a: .2 });
      petals(t * .6, { n: 50, seed: 91, s: 2, depth: true, wind: 320, fall: 60 });
      flare(sx, sy, .9);
      // Clawd leaps in from the lower right, up into the sky beside the sun
      const hop = clamp((b - .5) / 1.2), cx = lerp(W + 150, 1360, easeOut(hop)), cy = lerp(H + 250, 250, easeOut(hop));
      if (b > .5) cut('clawd_jump', cx, cy + Math.sin(t * 7) * 6, 210, { rot: (1 - hop) * .7 - .08, anchor: [.5, .5] });
      flash(1 - clamp((b - b0) / .6));
      return;
    }
    // ---------- "It was always training, and the curves kept gaining": the curve bends vertical; they run straight up it into the sky ----------
    if (b < L3) {
      hideStamp();
      const bb = b - L2;
      // the curve lives on the tall sunrise plate (fractions of it): it leaves the skyline gently and bends up to vertical at x ≈ .68;
      // the three climb it (u = how far along), and the camera tilts up with Akari
      const cu = u => [lerp(-.12, .68, 1 - (1 - u) ** 3), lerp(1.04, -.12, u)];
      const lead = .22 + bb * .068, camY = clamp(cu(lead)[1] + .06, .26, .74);
      const v = still('c4_sky', { x: .5, y: camY, z: 1.2 });
      const [sx, sy] = v.pt(.5, .775);
      flare(sx, sy, .8);
      speedBars(t, { n: 30, a: .28, speed: 3400, ang: -Math.PI / 2, col: '#FFF4E0' });
      const tipU = Math.min(1, lead + .22 + bb * .02), pts = [];
      for (let i = 0; i <= 80; i++) { const u = i / 80 * tipU; pts.push(v.pt(...cu(u))); }
      curve(pts, 1, { w: 20, col: '#FFB050' });
      // the three run up it in step with the beat (each a third of a stride apart), leaning into the climb
      const onCurve = (who, u, h, ph) => {
        const [x, y] = v.pt(...cu(u)), [x2, y2] = v.pt(...cu(u + .01)), a = Math.atan2(y2 - y, x2 - x);
        return runner(who, x, y, h, b + ph, { rot: Math.max(a * .9, -1.05) });
      };
      onCurve('kiri', lead - .24, 440, .67);
      onCurve('ren', lead - .12, 460, .33);
      onCurve('akari', lead, 450, 0);
      // Clawd rides the tip of the curve up into the blue
      const tip = pts[pts.length - 1];
      cut('clawd_jump', tip[0], tip[1] + 20, 130, { rot: .15 * Math.sin(b * Math.PI), anchor: [.5, .8] });
      sparkleField(t, { n: 12, r: 22, seed: 92 });
      cutFlash(bb, .8);
      if (bb > L3 - L2 - .7) flash((bb - (L3 - L2 - .7)) / .7 * .9);
      return;
    }
    // ---------- "We didn't start the scaling": the cast cards again, one a beat, in sunrise colours; then all four ----------
    if (b < L4) {
      hideStamp();
      const bb = b - L3;
      if (bb < 4) {
        const i = Math.floor(bb), C = CARDS[i], cb = bb - i, slide = easeOut(clamp(cb / .35)), push = 1 + cb * .04;
        diagSplit(C.c1, C.c2, t, { x: C.side > 0 ? W * .6 : W * .4, a: .3 * C.side, speed: 420 * C.side });
        speedLines(C.side > 0 ? W * .68 : W * .32, H * .42, t, { n: 80, r0: 420, a: .35 });
        if (i < 3) {
          const x = (C.side > 0 ? W * .68 : W * .32) + (1 - slide) * 800 * C.side;
          const v = cut(C.cut, x, H + 60, 1180 * push, { shadow: false });
          if (C.lenses) { const pts = C.lenses.map(([u, w]) => v.pt(u, w)), r = v.s * 632 * .042; lensFlash(pts, r, r * .8, Math.sin(clamp((cb - .2) / .6) * Math.PI)); }
        } else {
          const hop = Math.abs(Math.sin(frac(b) * Math.PI));
          cut('clawd_jump', W * .32 - (1 - slide) * 800, 900 - hop * 90, 560 * push, { sq: (1 - hop) * .07, shadow: .3 });
        }
        nameCard(C.name, '', C.side > 0 ? 110 : 1060, 820, clamp((cb - .1) / .35), C.col, { size: 120 });
        flash(.8 * (1 - clamp(cb / .25)));
        return;
      }
      // all four at once, a panel each, then the flash into the start line
      const pw = W / 4;
      CARDS.forEach((C, j) => {
        ctx.save(); ctx.beginPath(); ctx.rect(j * pw, 0, pw, H); ctx.clip();
        diagSplit(C.c1, C.c2, t, { x: j * pw + pw * .6, a: .25, speed: 300 });
        const face = [[.42, .19], [.45, .14], [.5, .29], [.5, .45]][j];
        cut(C.cut, j * pw + pw / 2, j === 3 ? H * .52 - Math.abs(Math.sin(b * Math.PI)) * 40 : 400, j === 3 ? 330 : 1350, { anchor: face });
        ctx.restore();
      });
      ctx.fillStyle = '#FFFFFF'; for (let j = 1; j < 4; j++) ctx.fillRect(j * pw - 5, 0, 10, H);
      flash(.8 * (1 - clamp((bb - 4) / .25)));
      if (bb > L4 - L3 - .4) flash((bb - (L4 - L3 - .4)) / .4);
      return;
    }
    // ---------- "Now we swear we'll try to pace it — but we'd rather race it!": PACE at the start line; a hard cut to RACE; the race ----------
    if (b < L5) {
      const bb = b - L4, CUT = 5.5, GO = 8;   // "but we'd rather" ≈ bb 5.6, "race" ≈ bb 8.2
      if (bb < CUT) {
        // Akari in the blocks with her PACE armband and a polite little smile, trembling harder every beat
        const k = ease(clamp(bb / CUT)), [sx, sy] = shake(t, 1.2 + bb * 1.1);
        const v = still('c4_crouch', { x: .5, y: .5, z: lerp(1.04, 1.18, k) }, { dx: sx, dy: sy, patches: ['c4_crouch.calm3'] });
        // sweat drops on the beats
        for (let j = 1; j < Math.min(6, Math.floor(bb) + 1); j++) { const age = bb - j, [dx, dy] = v.pt(.55, .3); if (age < 1) sparkle(dx + 50 * (j % 2 ? 1 : -1), dy + age * 70, 18 * (1 - age), 1, '#BFE8FF'); }
        leak(.3, { side: 'left', col: '#FFC08A' });
        cutFlash(bb, .8);
        return;
      }
      if (bb < GO) {
        // the hard cut: a close-up, RACE on the band and her eyes blazing; a snap zoom in, then a slow push onto her face
        const cb = bb - CUT, k = easeOut(clamp(cb / .3)), k2 = ease(clamp(cb / (GO - CUT))), [sx, sy] = shake(t, 3 + 9 * hit(cb, .5));
        const v = still('c4_racecu', { x: lerp(.62, .76, k2), y: lerp(.5, .47, k2), z: lerp(1.0, 1.08, k) + k2 * .16 }, { dx: sx, dy: sy });
        bandText(v, 'RACE');
        const [fx, fy] = v.pt(.81, .5);
        speedLines(fx, fy, t, { n: 90, r0: 420, a: .3 });
        for (const [u, w] of RACE_EYES) { const [gx, gy] = v.pt(u, w); addGlow(gx, gy, 26 * v.s, '#FFB040', .35 + .2 * Math.sin(t * 30)); glint(gx, gy - 4 * v.s, 30 * v.s, Math.sin(clamp((cb - .2) / 1) * Math.PI)); }
        if (cb < .12) impactFrame(1);
        cutFlash(cb, .6, .2);
        return;
      }
      // the gun: the club blasts off down the track; the camera runs with them, every stride a new drawing and a jolt
      const rb = bb - GO, step = Math.floor(b * 3), jolt = step % 2 ? -1 : 1, [sx, sy] = shake(t, 5 * hit(rb, .6));
      const k = ease(clamp(rb / 3.5)), v = still('c4_race', { x: lerp(.53, .56, k), y: .56, z: lerp(1.06, 1.12, k) }, { dx: sx, dy: sy + jolt * 5, patches: step % 2 ? ['c4_race.legs2'] : [] });
      speedBars(t, { n: 50, a: .42, speed: 5200, col: '#FFF4E0' });
      // Clawd clings to the top of Ren's flying bag, flapping in the wind
      const [gx, gy] = v.pt(.385, .405);
      cut('clawd_jump', gx, gy + 8, 110 * v.s, { rot: -.45 + .12 * Math.sin(t * 31) + .06 * Math.sin(t * 13), anchor: [.5, .92], sq: .05 * Math.sin(t * 27) });
      for (let j = 0; j < 3; j++) { const age = frac(b * 1.5 + j / 3), [ex, ey] = v.pt(.36, .36); sparkle(ex - age * 120, ey - 20 + j * 18, 14 * (1 - age), 1, '#BFE8FF'); }
      petals(t, { n: 30, seed: 94, s: 1.6, depth: true, wind: -2400, fall: 30 });
      if (rb < .8) burst(W * .5, H * .38, 760, rb / .8, ['#FFFFFF', '#FFE14A', '#FF6F6F']);
      if (rb < .1) impactFrame(1);
      cutFlash(rb, .9);
      if (rb > L5 - L4 - GO - .5) flash((rb - (L5 - L4 - GO - .5)) / .5);
      return;
    }
    // ---------- "We didn't start the scaling" (the last): the whole cast at sunrise, daytime fireworks, the title logo slams in again ----------
    if (b < L6) {
      hideStamp(); setBloom(.4);
      const bb = b - L5, k = easeOut(clamp(bb / 4));
      const v = still('c4_group', { x: lerp(.62, .5, k), y: lerp(.4, .5, k), z: lerp(1.25, 1.02, k) + clamp((bb - 8) / 7) * .05 });
      const [sx, sy] = v.pt(.23, .86);
      rays(sx, sy, { t, a: .12, n: 10, ang: -Math.PI / 2, spread: 3, len: 1500, col: '#FFE6B8' });
      // big shells over the open sky, one a beat, before the logo; then smaller ones around it and over the group
      const shells = [[1, 330, 300, 360], [2, 600, 170, 300], [3, 190, 150, 290], [4, 470, 430, 320], [5.5, 1250, 110, 200], [6.5, 780, 90, 190],
        [7.5, 1700, 200, 200], [8.5, 120, 520, 190], [9.5, 1000, 70, 210], [10.5, 700, 150, 180], [11, 1450, 90, 200]];
      shells.forEach(([at, x, y, r], j) => firework(x, y, r, (bb - at) * beatLen(), FW[j % FW.length], { seed: j + 1, col2: FW[(j + 3) % FW.length], y0: 900, solid: true, lw: 10, n: 64, head: 6 }));
      // Kiri's glasses flash one last time
      const [g0, g1] = [v.pt(.855, .3), v.pt(.915, .3)];
      lensFlash([g0, g1], 26 * v.s, 20 * v.s, Math.sin(clamp((bb - 8) / 1) * Math.PI));
      titleLogo(400, 330, 1, clamp((bb - 4) / 4), t);
      // Clawd bounces on the railing by the sun, arms up
      const hop = Math.abs(Math.sin(frac(b) * Math.PI)), cin = easeOut(clamp((bb - 2) / .8));
      cut('clawd_jump', lerp(-200, 330, cin), 985 - hop * 70, 190, { sq: (1 - hop) * .07, shadow: .3 });
      confetti(t, { n: 60, seed: 98, t0: t - (bb - 1) * beatLen() });
      if (bb > 6 && bb < 8) flare(1500, 140, Math.sin(clamp((bb - 6) / 2) * Math.PI));
      flash(1 - clamp(bb / .6));
      // the day ends: a warm white-out into the evening
      if (bb > L6 - L5 - 1) flash((bb - (L6 - L5 - 1)) * .9, '#FFE6C8');
      return;
    }
    // ---------- "But when we log off…": the cast waves goodbye at the club-room door; Kiri's hand on the light switch ----------
    if (b < DARK) {
      const bb = b - L6, k = ease(clamp(bb / (DARK - L6)));
      const v = still('c4_bye', { x: .5, y: lerp(.5, .44, k), z: lerp(1.02, 1.12, k) });
      sparkleField(t, { n: 10, r: 12, seed: 99, col: '#FFE6C0', rate: .4 });
      leak(.25, { side: 'right', col: '#FFB070' });
      cutFlash(bb, .5, .4, '#FFE6C0');
      // click: Kiri flips the switch by the door, and the lights go off
      const ck = bb - (DARK - L6 - .5), [wx, wy] = v.pt(.9, .62);
      if (ck > -1) popLabel('click', wx - 20, wy - 110, 40, clamp((ck + 1) / .3), { fill: '#FFFFFF', col: '#5A4E86', rot: .1 });
      if (ck > 0) grade('#0A0F2A', clamp(ck / .15) * .85, 'multiply');
      return;
    }
    // ---------- "…will it still train on?" / "(and on, and on…)": the dark room, one screen still training; Clawd waves from the dark ----------
    setBloom(.5);
    // the dark room ("will it still train on?"), the screen close-up on the first "and on, and on", then back to the room,
    // where Clawd's eyes light up and he waves ("and on, and on…"); cuts at b 61 and 71, where each "and on" phrase starts
    const bb = b - DARK, k = clamp(bb / (END - DARK)), [ci, cb] = cuts(bb, [0, 61 - DARK, 71 - DARK]);
    if (ci === 1) {
      screenCloseUp(t, b, cb, bb);
      cutFlash(cb, .3, .4, '#BFE0FF');
      return;
    }
    const f = ci === 0 ? { x: lerp(.46, .44, ease(clamp(cb / 6.5))), y: .5, z: lerp(1.0, 1.08, ease(clamp(cb / 6.5))) }
      : { x: lerp(.45, .5, ease(clamp(cb / 12))), y: lerp(.46, .44, ease(clamp(cb / 12))), z: lerp(1.2, 1.34, ease(clamp(cb / 12))) };
    const v = still('c4_night', f);
    // the screen: the loss curve inching down, the step counter ticking
    const [s0x, s0y] = v.pt(.25, .305), [s1x, s1y] = v.pt(.46, .53);
    lossPlot(s0x + 6 * v.s, s0y + 24 * v.s, s1x, s1y, .45 + .55 * k, t, { col: '#1D4E9A', w: 2.2 * v.s });
    txt('loss', s0x + 4 * v.s, s0y + 8 * v.s, 9 * v.s, '#1D4E9A', { font: 'code', align: 'left' });
    txt(`step ${(1048576 + Math.floor(bb * 1471)).toLocaleString('en-US')}`, s1x - 4 * v.s, s0y + 8 * v.s, 8 * v.s, '#3A6AB0', { font: 'code', align: 'right' });
    addGlow(...v.pt(.36, .42), 260 * v.s, '#BFF6FF', .12);
    // the Attention paper pinned beside it
    const [px, py] = v.pt(.54, .345);
    txt('Attention Is All', px, py, 7 * v.s, '#1A2030', { font: 'abril', rot: -.08 }); txt('You Need', px + v.s, py + 9 * v.s, 7 * v.s, '#1A2030', { font: 'abril', rot: -.08 });
    // the tower's light blinks on the beat
    if (frac(b) < .5) addGlow(...v.pt(.65, .735), 16 * v.s, '#7CFF9A', 1);
    // Clawd on the books in the dark; in the last cut his eyes light up with the screen, then he turns to us and waves
    const eyes = ci === 2 ? clamp((cb - 1.5) / 1) : 0, lit = ci === 2 ? clamp((cb - 5) / 1) : 0, ws = cb - 5;
    const wave = lit > 0 ? Math.sin(ws * Math.PI) * .16 * (1 - clamp((ws - 6) / 1.5)) : 0;
    const [cx, cy] = v.pt(.615, .548);
    const c = cut('clawd_stand', cx, cy - (lit > 0 ? 10 * Math.abs(Math.sin(ws * Math.PI)) * (1 - clamp((ws - 6) / 1.5)) : 0), 96 * v.s, { tint: '#0E1434', tintA: lerp(.86, .4, lit), rot: wave });
    // the eyes (measured on clawd_stand: centres at u .336 and .562, v .383; 67 × 173 px ovals) fill with the screen's light
    if (eyes > 0) for (const u of [.336, .562]) {
      const [ex, ey] = c.pt(u, .383), rx = 32 * c.s, ry = 84 * c.s, e = eyes * (1 - lit * .5);
      addGlow(ex, ey, ry * 1.4, '#9FEFFF', .5 * e);
      ctx.save(); ctx.translate(ex, ey); ctx.rotate(wave); ctx.globalAlpha = e;
      ctx.fillStyle = linGrad(0, -ry, 0, ry, [[0, '#BFF4FF'], [1, '#4FA8D8']]); ctx.fill(ellPath(0, 0, rx, ry * eyes));
      fillP(ellPath(-rx * .2, -ry * .45, rx * .38, ry * .22), '#FFFFFF');
      ctx.restore();
    }
    if (lit > 0 && lit < 1) sparkle(cx + 50 * v.s, cy - 90 * v.s, 24 * Math.sin(lit * Math.PI), 1, '#FFFFFF');
    grade('#0A1030', .15, 'multiply');
    if (ci === 0 && cb < .5) flash(.5 * (1 - cb / .5), '#0A0F2A');
    if (ci === 2) cutFlash(cb, .3, .4, '#BFE0FF');
    if (bb > END - DARK - .7) flash((bb - (END - DARK - .7)) / .6);
  });

  // ---------- the outro: the end card: the key visual in morning light, frozen, the title in the corner; the last hit; a fade out ----------
  section('outro', (p, lt, d, t, seg) => {
    hideCaption(); hideStamp();
    const b = beatsIn(t, seg), hb = b - 18.8, b0 = beatsIn(seg.start, seg);
    still('keyvisual', { x: .5, y: .5, z: (1.06 - .04 * ease(clamp(b / 16))) * punch(hb, .03) });
    grade('#FFC890', .18, 'soft-light');
    leak(.25, { side: 'left', col: '#FFC890' });
    petals(t, { n: 14, seed: 101, s: 1.3, depth: true, alpha: clamp((17.5 - b) / 1.5) });
    titleLogo(470, 790, .9, clamp((b - .5) / 3), t);
    // the band's last hit: a glint on the logo and a soft flash, then the fade to black as the song ends
    if (hb > 0 && hb < 1.4) { glint(735, 612, 90, Math.sin(clamp(hb / 1.4) * Math.PI)); sparkle(210, 745, 40 * Math.sin(clamp(hb / 1.4) * Math.PI), 1, '#FFF4B0'); }
    if (hb > 0) flash(.35 * (1 - clamp(hb / .6)));
    flash(1 - clamp((b - b0) / .6));
    if (b > 20) { flash((b - 20) / 1.4, '#000000'); noVignette(); }
  });
})();
