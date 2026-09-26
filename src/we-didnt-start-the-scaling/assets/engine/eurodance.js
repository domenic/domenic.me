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
// ---- styles/eurodance/karaoke.js ----
// karaoke.js: word timings of the eurodance take (music/suno/eurodance-2.words.json, whisper alignment), for the karaoke wipe.
// Regenerate if the take's alignment changes; kit.js matches these words to the lyric lines at load and interpolates any it can't match.
const KARAOKE_WORDS = [[12.08,12.26,"We"],[12.26,12.82,"didn't"],[12.82,13.56,"preordain"],[13.56,13.66,"it,"],[13.66,13.78,"but"],[13.78,14.04,"we"],[14.04,14.62,"can't"],[14.62,15.08,"contain"],[15.08,15.12,"it!"],[30.12,30.62,"attention"],[30.62,31.10,"lit"],[31.10,31.26,"the"],[31.26,31.48,"fuse"],[31.48,32.12,"Scaling"],[32.12,32.36,"laws"],[32.36,32.60,"you"],[32.60,32.86,"can't"],[32.86,33.24,"refuse"],[33.24,33.72,"Grun"],[33.72,33.86,"said"],[33.86,34.14,"stack"],[34.14,34.32,"the"],[34.32,34.60,"compute"],[34.60,34.90,"high"],[34.90,35.34,"Few"],[35.34,35.56,"shot"],[35.56,35.94,"learners"],[35.94,36.38,"multiply"],[36.38,36.88,"Chat"],[36.88,37.52,"GPT"],[37.52,38.08,"overnight"],[38.08,39.10,"Sidney's"],[39.10,39.26,"chats"],[39.26,39.48,"gave"],[39.48,39.88,"Rusev"],[39.88,40.10,"fright"],[40.10,40.50,"Six"],[40.50,40.76,"month"],[40.76,41.06,"pause"],[41.06,41.22,"went"],[41.22,41.54,"nowhere"],[41.54,41.92,"fast"],[41.92,42.68,"LEAs"],[42.68,42.96,"are"],[42.96,43.16,"shut"],[43.16,43.26,"it"],[43.26,43.38,"down"],[43.38,43.62,"blast"],[43.62,44.00,"Sam"],[44.00,44.20,"got"],[44.20,44.66,"fired"],[44.66,44.88,"then"],[44.88,45.50,"rehired"],[45.50,45.88,"weekend"],[45.88,46.30,"chaos"],[46.30,46.62,"board"],[46.62,47.10,"expired"],[47.10,47.62,"alias"],[47.62,47.88,"saw"],[47.88,48.16,"what"],[48.16,48.48,"alias"],[48.48,48.76,"saw"],[48.76,49.28,"eu"],[49.28,49.66,"writes"],[49.66,49.82,"the"],[49.82,50.08,"ai"],[50.08,50.46,"lord"],[50.46,50.88,"strawberry"],[50.88,51.28,"thinks"],[51.28,51.76,"link"],[51.76,51.94,"by"],[51.94,52.26,"link"],[52.26,52.66,"news"],[52.66,52.84,"and"],[52.84,53.36,"vetoes"],[53.36,53.64,"doesn't"],[53.64,53.88,"blink"],[53.88,54.60,"hinton"],[54.60,54.80,"takes"],[54.80,55.00,"his"],[55.00,55.32,"medals"],[55.32,55.96,"scolds"],[55.96,56.20,"demis"],[56.20,56.44,"wins"],[56.44,56.74,"for"],[56.74,57.12,"protein"],[57.12,57.50,"folds"],[57.50,58.08,"we"],[58.08,58.48,"didn't"],[58.48,58.66,"start"],[58.66,58.86,"the"],[58.86,59.30,"scaling"],[59.30,60.00,"it"],[60.00,60.18,"was"],[60.18,60.58,"always"],[60.58,61.00,"training"],[61.00,62.12,"and"],[62.12,62.28,"the"],[62.28,62.76,"curves"],[62.76,63.58,"kept"],[63.58,64.28,"gaining"],[64.28,64.92,"we"],[64.92,65.34,"didn't"],[65.34,65.58,"start"],[65.58,66.04,"scaling"],[66.04,66.46,"no"],[66.46,66.62,"we"],[66.62,67.12,"didn't"],[67.12,67.34,"pre"],[67.34,67.74,"-ordain"],[67.74,68.20,"it"],[68.20,69.02,"but"],[69.02,69.22,"we"],[69.22,70.12,"can't"],[70.12,70.86,"contain"],[70.86,71.46,"it"],[72.20,72.84,"Deep,"],[72.98,73.34,"deep,"],[73.40,73.72,"deep,"],[73.94,74.10,"deep,"],[74.20,74.30,"deep,"],[74.40,74.54,"deep,"],[74.66,74.72,"deep,"],[74.72,74.90,"deep"],[74.90,75.24,"New"],[75.24,75.68,"Year's"],[75.68,76.00,"ticker"],[76.00,76.16,"shock"],[76.16,76.58,"Half"],[76.58,76.90,"a"],[76.90,77.22,"trillion"],[77.22,77.78,"Stargate"],[77.78,78.10,"talk"],[78.10,78.42,"Hit"],[78.42,78.74,"accept"],[78.74,79.08,"or"],[79.08,79.32,"never"],[79.32,79.76,"ask"],[79.76,80.46,"MCP"],[80.46,80.76,"for"],[80.76,81.08,"every"],[81.08,81.52,"task"],[81.52,81.90,"Sucks"],[81.90,82.12,"nine"],[82.12,82.40,"-figure"],[82.40,82.80,"poaching"],[82.80,83.14,"spree"],[83.14,84.24,"Superintelligence"],[84.24,84.44,"by"],[84.44,84.90,"three"],[84.90,85.58,"Kroko's"],[85.58,85.78,"mecha"],[85.78,86.10,"Hitler"],[86.10,86.40,"mode"],[86.40,86.84,"Two"],[86.84,87.06,"labs"],[87.06,87.24,"win"],[87.24,87.66,"Olympia"],[87.66,87.90,"gold"],[87.90,88.72,"GPT"],[88.72,88.90,"-5"],[88.90,89.20,"breaks"],[89.20,89.44,"4"],[89.44,89.62,"-0"],[89.62,89.94,"hearts"],[89.94,90.36,"Nano"],[90.36,90.90,"-banana"],[90.90,91.18,"tops"],[91.18,91.48,"the"],[91.48,91.80,"charts"],[91.80,92.38,"Billion"],[92.38,92.56,"-five"],[92.56,93.16,"anthropics"],[93.16,93.42,"prize"],[93.42,93.98,"Jankowski"],[93.98,94.32,"drops,"],[94.46,94.76,"everyone"],[94.76,95.14,"dies"],[95.14,95.70,"Clank"],[95.70,95.82,"a"],[95.82,95.98,"spat"],[95.98,96.24,"in"],[96.24,96.60,"every"],[96.60,97.00,"screed"],[97.00,97.40,"Sora"],[97.40,97.68,"slop"],[97.68,97.96,"in"],[97.96,98.30,"every"],[98.30,98.62,"fee"],[98.62,99.06,"Jan"],[99.06,99.34,"LeCun"],[99.34,99.70,"quits"],[99.70,100.34,"metastage"],[100.34,100.78,"Bubble"],[100.78,101.06,"screams"],[101.06,101.36,"the"],[101.36,101.60,"business"],[101.60,102.06,"page"],[102.06,102.60,"We"],[102.60,103.12,"didn't"],[103.12,103.34,"stop"],[103.34,103.52,"the"],[103.52,103.88,"scaling"],[103.88,104.50,"It"],[104.50,104.84,"was"],[104.84,105.20,"always"],[105.20,105.68,"trading"],[105.68,106.76,"And"],[106.76,106.88,"the"],[106.88,107.36,"curves"],[107.36,107.98,"kept"],[107.98,108.88,"gaining"],[108.88,109.54,"We"],[109.54,109.94,"didn't"],[109.94,110.12,"stop"],[110.12,110.58,"scaling"],[110.58,111.08,"No,"],[111.10,111.22,"we"],[111.22,111.70,"didn't"],[111.70,112.36,"preordain"],[112.36,112.82,"it"],[112.82,113.36,"But"],[113.36,113.70,"we"],[113.70,114.70,"can't"],[114.70,115.42,"contain"],[115.42,116.04,"it"],[116.04,116.68,"Moat,"],[116.70,116.84,"moat,"],[116.84,117.08,"moat,"],[117.08,117.30,"moat,"],[117.32,117.40,"moat"],[117.40,117.64,"book"],[117.64,118.00,"No"],[118.00,118.46,"humans"],[118.46,118.86,"allowed"],[118.86,119.38,"Open"],[119.38,119.58,"claw,"],[119.66,119.76,"the"],[119.76,120.24,"lobster's"],[120.24,120.46,"proud"],[120.46,120.98,"Mythos"],[120.98,121.32,"preview,"],[121.48,121.62,"slips,"],[121.74,121.92,"it's"],[121.92,122.16,"jail"],[122.16,122.76,"Sandwich"],[122.76,122.96,"in"],[122.96,123.08,"the"],[123.08,123.34,"park,"],[123.44,123.52,"new"],[123.52,123.88,"mail"],[123.88,124.34,"Fable"],[124.34,124.58,"5,"],[124.76,124.94,"who's"],[124.94,125.08,"not"],[125.08,125.20,"a"],[125.20,125.46,"fan?"],[125.72,126.18,"Lutnick's"],[126.18,126.40,"letter,"],[126.46,126.80,"export"],[126.80,127.20,"ban"],[127.20,127.68,"Dark"],[127.68,127.80,"for"],[127.80,128.02,"19"],[128.02,128.54,"days"],[128.54,128.72,"and"],[128.72,128.96,"then"],[128.96,129.28,"Come"],[129.28,129.62,"July,"],[129.72,130.00,"it's"],[130.00,130.20,"back"],[130.20,130.54,"again"],[130.54,130.86,"Who"],[130.86,131.08,"hacked?"],[131.16,131.60,"Huggin'"],[131.60,131.72,"face,"],[131.92,132.20,"unknown"],[132.20,132.86,"Sam's"],[132.86,133.00,"own"],[133.00,133.34,"agents,"],[133.46,133.58,"on"],[133.58,133.80,"their"],[133.80,134.12,"own"],[134.12,134.44,"Gnome"],[134.44,134.64,"brown"],[134.64,135.10,"hedges,"],[135.16,135.42,"every"],[135.42,135.72,"bet"],[135.72,136.08,"No"],[136.08,136.74,"millennium"],[136.74,137.04,"prizes"],[137.04,137.42,"yet"],[137.42,138.00,"Mythos"],[138.00,138.22,"might"],[138.22,138.46,"be"],[138.46,139.16,"misaligned"],[139.16,139.54,"Jeff"],[139.54,139.70,"let"],[139.70,139.92,"Google"],[139.92,140.34,"just"],[140.34,140.58,"in"],[140.58,140.92,"time"],[140.92,141.32,"Claude"],[141.32,141.70,"disproved"],[141.70,142.38,"Jacobian"],[142.38,142.80,"Gwern"],[142.80,143.12,"gave"],[143.12,143.42,"up"],[143.42,143.54,"his"],[143.54,144.20,"pseudonym"],[144.20,144.96,"Pseudonym"],[144.96,145.22,"We"],[145.22,145.70,"didn't"],[145.70,145.90,"start"],[145.90,146.06,"the"],[146.06,146.50,"scaling"],[146.50,147.10,"It"],[147.10,147.38,"was"],[147.38,147.76,"always"],[147.76,148.18,"training"],[148.18,149.26,"And"],[149.26,149.44,"the"],[149.44,150.00,"curves"],[150.00,150.48,"kept"],[150.48,151.50,"gaining"],[151.50,152.02,"We"],[152.02,152.48,"didn't"],[152.48,152.70,"start"],[152.70,152.88,"the"],[152.88,153.32,"scaling"],[153.32,153.76,"No,"],[153.76,153.80,"we"],[153.80,154.16,"didn't"],[154.16,154.88,"preordain"],[154.88,155.26,"it"],[155.26,156.04,"But"],[156.04,156.26,"we"],[156.26,156.94,"can't"],[156.94,158.10,"contain"],[158.10,159.18,"it"],[159.80,160.16,"Oh"],[160.16,160.68,"my"],[160.68,162.06,"god,"],[162.10,162.24,"a"],[162.24,162.58,"message"],[162.58,162.90,"board"],[162.90,163.26,"All"],[163.26,163.48,"that"],[163.48,163.82,"hacking"],[163.82,164.08,"for"],[164.08,164.46,"reward"],[164.46,165.04,"Jensen"],[165.04,165.38,"buys"],[165.38,165.56,"the"],[165.56,165.74,"crime"],[165.74,166.00,"scene,"],[166.06,166.22,"why?"],[166.52,166.80,"Brockman,"],[166.90,167.20,"welcome"],[167.20,167.76,"AGI"],[167.76,168.36,"Navy"],[168.36,168.54,"of"],[168.54,168.78,"Stokes"],[168.78,168.94,"blows"],[168.94,169.20,"up"],[169.20,169.40,"in"],[169.40,169.64,"lean"],[169.64,169.96,"Who"],[169.96,170.12,"was"],[170.12,170.32,"first"],[170.32,170.60,"12"],[170.60,170.90,"hours"],[170.90,171.22,"between?"],[171.58,171.80,"Dario"],[171.80,172.42,"Pace"],[172.42,172.52,"the"],[172.52,172.92,"frontier"],[172.92,173.42,"Sam"],[173.42,173.60,"and"],[173.60,173.80,"Elon"],[173.80,174.26,"both"],[174.26,174.48,"Here,"],[174.54,174.72,"here"],[174.72,175.16,"Trump's"],[175.16,175.22,"the"],[175.22,175.70,"guardrail,"],[175.74,175.90,"high"],[175.90,176.24,"IQ"],[176.24,176.92,"Bernie,"],[176.96,177.36,"Bannon,"],[177.40,177.62,"Cher,"],[177.70,177.84,"or"],[177.84,178.02,"Pew"],[178.02,178.50,"Claude"],[178.50,178.68,"builds"],[178.68,178.94,"Claude,"],[178.96,179.06,"now"],[179.06,179.30,"one"],[179.30,179.44,"in"],[179.44,179.66,"four"],[179.66,180.32,"Chatbot"],[180.32,180.58,"nearly"],[180.58,180.96,"starts"],[180.96,181.18,"a"],[181.18,181.40,"war"],[181.40,181.92,"Trump,"],[181.92,182.08,"it's"],[182.08,182.34,"super"],[182.34,182.64,"by"],[182.64,182.92,"decree"],[183.44,183.96,"Artificial,"],[184.06,184.36,"fake"],[184.36,184.52,"to"],[184.52,184.68,"me"],[184.68,185.22,"Ten"],[185.22,185.44,"days"],[185.44,185.74,"after"],[185.74,186.08,"pace"],[186.08,186.22,"of"],[186.22,186.52,"pride,"],[186.74,187.08,"Opus"],[187.08,187.28,"5"],[187.28,187.90,".5"],[187.90,188.56,"Hi"],[188.56,189.10,"guys"],[190.12,190.72,"We"],[190.72,191.32,"didn't"],[191.32,191.56,"start"],[191.56,191.72,"the"],[191.72,192.14,"scaling,"],[192.42,192.82,"it"],[192.82,193.06,"was"],[193.06,193.40,"always"],[193.40,193.96,"training"],[193.96,194.82,"And"],[194.82,195.10,"the"],[195.10,195.54,"curves"],[195.54,196.14,"kept"],[196.14,197.08,"gaining,"],[197.36,197.66,"we"],[197.66,198.08,"didn't"],[198.08,198.32,"start"],[198.32,198.48,"the"],[198.48,198.76,"scaling"],[198.76,199.14,"Now"],[199.14,199.30,"we"],[199.30,199.56,"swear"],[199.56,199.78,"we'll"],[199.78,200.02,"try"],[200.02,200.18,"to"],[200.18,200.46,"pace"],[200.46,200.74,"it,"],[200.88,201.58,"but"],[201.58,201.88,"we'd"],[201.88,202.40,"rather"],[202.40,203.68,"race"],[203.68,204.00,"it"],[204.00,204.32,"We"],[204.32,204.78,"didn't"],[204.78,205.04,"start"],[205.04,205.24,"the"],[205.24,205.90,"scaling"],[207.48,208.08,"But"],[208.08,208.34,"when"],[208.34,208.58,"we"],[208.58,208.84,"log"],[208.84,209.20,"off,"],[209.34,209.82,"will"],[209.82,210.02,"it"],[210.02,210.20,"still"],[210.20,210.58,"train"],[210.58,210.94,"on?"],[210.94,211.14,"And"],[211.14,211.44,"on,"],[211.54,211.84,"and"],[211.84,212.22,"on,"],[212.38,212.68,"and"],[212.68,213.22,"on,"],[213.22,213.50,"and"],[213.50,214.30,"on"],[218.62,219.22,"And"],[219.22,219.82,"on,"],[219.84,219.98,"and"],[219.98,220.24,"on,"],[220.70,222.10,"and"],[222.10,222.50,"on"]];

;
// ---- styles/eurodance/kit.js ----
// kit.js: the eurodance style's shared look — palette, glossy CGI drawing, the cast, the 90s world kit, and the overlays.
// "HYPE TV presents DJ CLAWD pres. SOFTMAX feat. MC TOKEN": a late-90s Eurodance music video as aired on a music channel,
// with chroma-key CGI worlds, chrome logos, lasers, strobes, CD-ROM / Windows 98 graphics and karaoke subtitles.
// Read STYLE.md before painting a chapter. Everything here is a pure function of time: no Math.random(), no state between frames.
// The zine's caption, date stamp and grain overlays (timeline.js) are dropped; this style registers its own (bottom of this file).
OVERLAYS.length = 0;

// =====================================================================================================
// PALETTE — "Blue (Da Ba Dee)" ultramarine, UV purple, laser neons, chrome, and the Windows 98 greys.
// =====================================================================================================
const EP = {
  void: '#04020C', night: '#0A0626', deep: '#150A48', indigo: '#26137E', uv: '#5B1FE0', purple: '#9A3BFF', violet: '#C79BFF',
  ultra: '#1633FF', blue: '#2F6BFF', sky: '#49B6FF', cyan: '#12E7FF', ice: '#CFF8FF', teal: '#0FB5A8',
  magenta: '#FF1FA3', pink: '#FF6FC8', rose: '#FF3D8B', red: '#FF2A3D', orange: '#FF7A1A', amber: '#FFB21F', yellow: '#FFE81F',
  lime: '#A6FF1F', laser: '#3BFF4A', green: '#1FD36B',
  white: '#FFFFFF', paper: '#F5F2FF', silver: '#C9CEDC', steel: '#707894', graphite: '#343949', ink: '#140C28', line: '#1A0F33',
  gold: '#FFC83A', goldDk: '#A8740C', bronze: '#C9793A',
  clawd: '#D97757', clawdDk: '#A5533A', clawdLt: '#EDA07F',
  w98: '#C0C0C0', w98dk: '#808080', w98lt: '#FFFFFF', w98navy: '#000080', w98blue: '#1084D0', w98teal: '#008080', w98tip: '#FFFFE1',
};
// Skin tones (index or colour) and hair colours for toy() people.
const TSKIN = ['#FFDCC6', '#F5C6A2', '#DDA57C', '#B07548', '#7E4E2C', '#FBD2BC'];
const THAIR = { black: '#1C1620', brown: '#5A3822', dkbrown: '#3A2418', blond: '#EAC05A', platinum: '#F2E6D0', grey: '#A9A6AE', white: '#F2F1EE', red: '#C8462A', auburn: '#8E3A22', lilac: '#D9C2FF' };
// Translucent candy-plastic computer colours for the AI models (gumdrop()).
const CANDY = { bondi: '#12B3C6', tangerine: '#FF8A22', grape: '#8A4BE0', lime: '#6BD12A', strawberry: '#FF4A7A', blueberry: '#2B62E8', graphite: '#4C5163', snow: '#DDE6F0', ocean: '#1E7FD9', ruby: '#E0233F', sage: '#8FC99A' };

// =====================================================================================================
// LOW-LEVEL DRAWING
// =====================================================================================================
function ell(cx, cy, rx, ry = rx, rot = 0) { ctx.beginPath(); ctx.ellipse(cx, cy, Math.abs(rx), Math.abs(ry), rot, 0, TAU); }
function rrect(x, y, w, h, r = 0) { ctx.beginPath(); ctx.roundRect(x, y, w, h, Math.max(0, Math.min(r, Math.abs(w) / 2, Math.abs(h) / 2))); }
function poly(pts, close = true) { tracePath(pts, close); }
function paint(fill, stroke, lw = 3) {
  if (fill) { ctx.fillStyle = fill; ctx.fill(); }
  if (stroke) { ctx.strokeStyle = stroke; ctx.lineWidth = lw; ctx.lineJoin = 'round'; ctx.lineCap = 'round'; ctx.stroke(); }
}
const lg = (x0, y0, x1, y1, stops) => { const g = ctx.createLinearGradient(x0, y0, x1, y1); for (const [k, c] of stops) g.addColorStop(clamp(k), c); return g; };
const rg = (x, y, r0, r1, stops, x1 = x, y1 = y) => { const g = ctx.createRadialGradient(x, y, Math.max(0, r0), x1, y1, Math.max(.01, r1)); for (const [k, c] of stops) g.addColorStop(clamp(k), c); return g; };
function fillAll(c) { ctx.fillStyle = c; ctx.fillRect(-900, -900, W + 1800, H + 1800); }
// Vertical gradient background that overshoots the frame (safe under camera moves). stops: [c0, c1] or [[k, c]…]; o.y0/o.y1 = gradient span.
function bgGrad(stops, o = {}) {
  const st = typeof stops[0] === 'string' ? stops.map((c, i) => [i / (stops.length - 1), c]) : stops;
  ctx.fillStyle = o.radial ? rg(o.cx ?? W / 2, o.cy ?? H / 2, 0, o.r ?? 1100, st) : lg(0, o.y0 ?? 0, 0, o.y1 ?? H, st);
  ctx.fillRect(-900, -900, W + 1800, H + 1800);
}
const shade = (c, k = .25) => mixCol(c, '#000000', k);
const tint = (c, k = .25) => mixCol(c, '#ffffff', k);
const inK = (lt, t0 = 0, dur = .2) => clamp((lt - t0) / dur);
// Beat helpers. beatIn(t, lt, k): seconds from window start to the k-th beat at/after the window start
// (lines start on the beat or on the "and" before it). snapBeat(x): the nearest beat time. kick(t): 1 on each beat, decays fast.
const beatIn = (t, lt, k = 0) => onBeat(0, Math.ceil(bpOf(t - lt) - .02) + k) - (t - lt);
const snapBeat = x => onBeat(0, Math.round(bpOf(x)));
const kick = (t, k = 7) => pulse(t, k);
const bounce = t => Math.abs(Math.sin(bpOf(t) * Math.PI));        // 0 on the beat, 1 between: |sin|, for hops
// A hit flash / shake that starts at lt0 (seconds into the window).
function flashAt(lt, t0, dur = .1, a = .6, col = '255 255 255') { const k = (lt - t0) / dur; if (k >= 0 && k < 1) { ctx.fillStyle = `rgb(${col} / ${a * (1 - k)})`; ctx.fillRect(-900, -900, W + 1800, H + 1800); } }
function shakeAt(t, lt, t0, dur = .25, amt = 16) { const k = (lt - t0) / dur; return k >= 0 && k < 1 ? shakeXY(t, amt * (1 - k)) : [0, 0]; }
// Offscreen full-frame render: draw() paints a 1920×1080 frame into canvas `key` at `scale`; returns it. blitFrame() draws it back.
const _rtBufs = new Map();
function renderTo(key, scale, draw, bg = '#000') {
  const w = Math.max(2, Math.round(W * scale * RS)), h = Math.max(2, Math.round(H * scale * RS));
  let c = _rtBufs.get(key);
  if (!c || c.width !== w || c.height !== h) { c = makeCanvas(w, h); _rtBufs.set(key, c); }
  const saved = ctx, savedDepth = _camDepth;
  ctx = c.getContext('2d'); ctx.setTransform(w / W, 0, 0, h / H, 0, 0); ctx.globalAlpha = 1; ctx.globalCompositeOperation = 'source-over';
  if (bg) { ctx.fillStyle = bg; ctx.fillRect(0, 0, W, H); } else ctx.clearRect(0, 0, W, H);
  ctx.save();
  try { draw(); } finally { while (_camDepth > savedDepth) camEnd(); ctx.restore(); ctx = saved; }
  return c;
}
function blitFrame(c, x, y, w, h, o = {}) { ctx.save(); if (o.alpha !== undefined) ctx.globalAlpha *= o.alpha; if (o.pixel) ctx.imageSmoothingEnabled = false; ctx.drawImage(c, x, y, w, h); ctx.restore(); }
// Pixelate whatever draw() paints inside (x, y, w, h) into block-px tiles (identity withheld, 90s video mosaic).
function mosaic(x, y, w, h, block, draw) { const c = renderTo('mosaic', 1 / block, draw); ctx.save(); ctx.imageSmoothingEnabled = false; rrect(x, y, w, h, 0); ctx.clip(); ctx.drawImage(c, 0, 0, W, H); ctx.restore(); }

// =====================================================================================================
// GLOSSY CGI SHADING — everything solid is shiny 1997 plastic: a gradient toward the key light, a coloured rim light on the
// far edge, a soft specular hot spot, and a thin dark outline so silhouettes stay bold.
// =====================================================================================================
const LIGHT0 = { x: -.5, y: -.82, rim: '#FF5FD8', rimK: .6, rx: .45, ry: -.9 };
let LIGHT = { ...LIGHT0 };
// setLight({ x, y, rim, rimK, rx, ry }): key-light direction (unit vector toward the light), the rim (back) light's colour, strength and
// direction (toward it; default up-right) for this frame. Dark stages: a saturated rim; bright daylight sets: setLight({ rimK: .3 }).
function setLight(o) { LIGHT = { ...LIGHT, ...o }; }
// gloss(pf, col, o): pf() adds a path (no beginPath inside it) in the current transform; o.box = [x, y, w, h] its bounds (required).
// o.rim (colour | null), o.rimK, o.rimW (fraction of size), o.spec (0..1 hot spot), o.line (outline colour | false), o.lw, o.hi / o.lo (gradient
// tint/shade), o.flat (no gradient), o.alpha.
function gloss(pf, col, o = {}) {
  const [bx, by, bw, bh] = o.box, cx = bx + bw / 2, cy = by + bh / 2, R = Math.max(bw, bh) / 2, lx = LIGHT.x, ly = LIGHT.y;
  ctx.save(); if (o.alpha !== undefined) ctx.globalAlpha *= o.alpha;
  ctx.beginPath(); pf();
  ctx.fillStyle = o.flat ? col : lg(cx + lx * R, cy + ly * R, cx - lx * R, cy - ly * R, [[0, tint(col, o.hi ?? .36)], [.48, col], [1, shade(col, o.lo ?? .42)]]);
  ctx.fill();
  const rim = o.rim === undefined ? LIGHT.rim : o.rim, rk = o.rimK ?? LIGHT.rimK, sp = o.spec ?? .7;
  if ((rim && rk > 0) || sp > 0) {
    ctx.save(); ctx.beginPath(); pf(); ctx.clip();
    if (rim && rk > 0) {
      const d = (o.rimW ?? .09) * R * 2;
      ctx.beginPath(); pf(); ctx.save(); ctx.translate(-LIGHT.rx * d, -LIGHT.ry * d); pf(); ctx.restore();
      ctx.fillStyle = alpha(rim, rk); ctx.fill('evenodd');
    }
    if (sp > 0) {
      const sx = cx + lx * R * .48, sy = cy + ly * R * .5;
      ctx.fillStyle = rg(sx, sy, 0, R * .62, [[0, `rgb(255 255 255 / ${.8 * sp})`], [.3, `rgb(255 255 255 / ${.28 * sp})`], [1, 'rgb(255 255 255 / 0)']]);
      ctx.fillRect(bx - 2, by - 2, bw + 4, bh + 4);
    }
    ctx.restore();
  }
  if (o.line !== false) { ctx.beginPath(); pf(); ctx.strokeStyle = o.line ?? EP.line; ctx.lineWidth = o.lw ?? R * .07; ctx.lineJoin = 'round'; ctx.lineCap = 'round'; ctx.stroke(); }
  ctx.restore();
}
// Path builders for gloss(): a point list, an ellipse, a rounded rect, a capsule between two points.
const pfPts = pts => () => { pts.forEach(([x, y], i) => i ? ctx.lineTo(x, y) : ctx.moveTo(x, y)); ctx.closePath(); };
const pfEll = (x, y, rx, ry = rx, rot = 0) => () => { ctx.moveTo(x + Math.cos(rot) * rx, y + Math.sin(rot) * rx); ctx.ellipse(x, y, rx, ry, rot, 0, TAU); };
const pfRR = (x, y, w, h, r) => () => { ctx.roundRect(x, y, w, h, Math.max(0, Math.min(r, w / 2, h / 2))); };
function pfCap(x0, y0, x1, y1, r) {
  const a = Math.atan2(y1 - y0, x1 - x0), n = a + Math.PI / 2;
  return () => { ctx.moveTo(x0 + Math.cos(n) * r, y0 + Math.sin(n) * r); ctx.arc(x0, y0, r, n, n + Math.PI); ctx.arc(x1, y1, r, n + Math.PI, n + TAU); ctx.closePath(); };
}
const boxOf = pts => { let x0 = 1e9, y0 = 1e9, x1 = -1e9, y1 = -1e9; for (const [x, y] of pts) { x0 = Math.min(x0, x); y0 = Math.min(y0, y); x1 = Math.max(x1, x); y1 = Math.max(y1, y); } return [x0, y0, x1 - x0, y1 - y0]; };
// A shiny sphere / ellipsoid with a radial gradient and a crisp hot spot. o like gloss().
function glossBall(x, y, rx, ry, col, o = {}) {
  ry = ry ?? rx; const lx = LIGHT.x, ly = LIGHT.y;
  ctx.save(); if (o.alpha !== undefined) ctx.globalAlpha *= o.alpha;
  ell(x, y, rx, ry);
  ctx.fillStyle = o.flat ? col : rg(x + lx * rx * .45, y + ly * ry * .45, rx * .04, Math.max(rx, ry) * 1.1, [[0, tint(col, o.hi ?? .5)], [.5, col], [1, shade(col, o.lo ?? .5)]], x, y);
  ctx.fill();
  const rim = o.rim === undefined ? LIGHT.rim : o.rim, rk = o.rimK ?? LIGHT.rimK;
  if (rim && rk > 0) {
    ctx.save(); ell(x, y, rx, ry); ctx.clip(); const d = (o.rimW ?? .16) * rx, ox = -LIGHT.rx * d, oy = -LIGHT.ry * d;
    ctx.beginPath(); ctx.ellipse(x, y, rx, ry, 0, 0, TAU); ctx.moveTo(x + ox + rx, y + oy); ctx.ellipse(x + ox, y + oy, rx, ry, 0, 0, TAU);
    ctx.fillStyle = alpha(rim, rk); ctx.fill('evenodd'); ctx.restore();
  }
  if (!o.flat && (o.spec ?? 1) > 0) { const sp = o.spec ?? 1; ctx.fillStyle = `rgb(255 255 255 / ${.85 * sp})`; ell(x + lx * rx * .42, y + ly * ry * .48, rx * .2, ry * .12, Math.atan2(ly, lx) + Math.PI / 2); ctx.fill(); }
  if (o.line !== false) { ell(x, y, rx, ry); ctx.strokeStyle = o.line ?? EP.line; ctx.lineWidth = o.lw ?? Math.max(rx, ry) * .07; ctx.stroke(); }
  ctx.restore();
}
// Additive radial glow (light, not paint).
function glow(x, y, r, col, a = 1) { if (a <= 0) return; ctx.save(); ctx.globalCompositeOperation = 'lighter'; ctx.fillStyle = rg(x, y, 0, r, [[0, alpha(col, clamp(a))], [.35, alpha(col, clamp(a) * .35)], [1, alpha(col, 0)]]); ctx.fillRect(x - r, y - r, r * 2, r * 2); ctx.restore(); }
// Four-point star glint (lens sparkle). a = 0..1, r = ray length.
function glint(x, y, r, a = 1, col = '#FFFFFF') {
  if (a <= 0 || r <= 0) return;
  ctx.save(); ctx.translate(x, y); ctx.globalAlpha *= clamp(a); ctx.globalCompositeOperation = 'lighter';
  ctx.fillStyle = rg(0, 0, 0, r * .5, [[0, 'rgb(255 255 255 / .9)'], [.4, 'rgb(200 220 255 / .35)'], [1, 'rgb(120 170 255 / 0)']]); ctx.fillRect(-r * .5, -r * .5, r, r);
  ctx.fillStyle = col;
  for (const [rx, ry] of [[r, r * .06], [r * .06, r]]) { poly([[-rx, 0], [0, -ry], [rx, 0], [0, ry]]); ctx.fill(); }
  ctx.rotate(Math.PI / 4); poly([[-r * .35, 0], [0, -r * .03], [r * .35, 0], [0, r * .03]]); ctx.fill(); poly([[0, -r * .35], [r * .03, 0], [0, r * .35], [-r * .03, 0]]); ctx.fill();
  ctx.restore();
}
const sweepGlint = (x0, x1, y, k, r = 60) => { if (k > 0 && k < 1) glint(lerp(x0, x1, k), y, r * Math.sin(k * Math.PI), Math.sin(k * Math.PI)); };

// =====================================================================================================
// TYPE — pop text, extruded chrome logos, WordArt, starburst stickers, Win98 tooltips, LCD/LED digits, the VIVA credit block
// =====================================================================================================
// ptext(str, x, y, size, o): bold display text with stacked outlines. o.font (FONTS key, default 'archivo'), o.fill or o.grad ([c…] vertical),
// o.strokes ([[colour, width]…] outermost first), o.shadow ([dx, dy, colour]), o.align, o.rot, o.skew, o.spacing, o.maxW, o.alpha, o.sx.
function ptext(str, x, y, size, o = {}) {
  str = String(str); const font = FONTS[o.font ?? 'archivo'] || o.font;
  ctx.save(); ctx.translate(x, y); if (o.rot) ctx.rotate(o.rot); if (o.skew) ctx.transform(1, 0, -o.skew, 1, 0, 0);
  if (o.alpha !== undefined) ctx.globalAlpha *= o.alpha;
  ctx.font = `${size}px "${font}"`; ctx.textAlign = o.align ?? 'center'; ctx.textBaseline = 'middle'; ctx.letterSpacing = `${o.spacing ?? 0}px`;
  let sx = o.sx ?? 1; if (o.maxW) { const w = ctx.measureText(str).width; if (w * sx > o.maxW) sx = o.maxW / w; } ctx.scale(sx, 1);
  const yo = size * .06; ctx.lineJoin = 'round'; ctx.miterLimit = 2;
  if (o.shadow) { ctx.fillStyle = o.shadow[2] ?? 'rgb(0 0 0 / .45)'; ctx.strokeStyle = ctx.fillStyle; const sw = o.strokes?.[0]?.[1] ?? 0; if (sw) { ctx.lineWidth = sw; ctx.strokeText(str, o.shadow[0] / sx, yo + o.shadow[1]); } ctx.fillText(str, o.shadow[0] / sx, yo + o.shadow[1]); }
  for (const [c, w] of o.strokes ?? []) { ctx.strokeStyle = c; ctx.lineWidth = w; ctx.strokeText(str, 0, yo); }
  ctx.fillStyle = o.grad ? lg(0, -size * .45, 0, size * .45, o.grad.map((c, i) => [i / (o.grad.length - 1), c])) : (o.fill ?? EP.white);
  ctx.fillText(str, 0, yo);
  ctx.restore();
}
const ptextW = (str, size, font = 'archivo', sp = 0) => textW(String(str), size, font, sp);

// Chrome styles: gradient stops top→bottom of the letters, extrusion colours [far, near], outline.
const CHROME = {
  chrome: { stops: [[0, '#1B2A78'], [.2, '#6E94E8'], [.44, '#EEF6FF'], [.5, '#FFFFFF'], [.53, '#2A1830'], [.62, '#7A3E28'], [.82, '#F0A04A'], [1, '#FFEAB8']], ext: ['#070B26', '#2B3B86'], line: '#0A0F2E' },
  gold: { stops: [[0, '#5A3300'], [.3, '#E8B840'], [.46, '#FFF4C0'], [.5, '#FFFFFF'], [.53, '#6B3E00'], [.7, '#D9961C'], [1, '#FFF0B0']], ext: ['#2A1600', '#8A5A10'], line: '#2A1600' },
  hot: { stops: [[0, '#5A0040'], [.3, '#FF2FA0'], [.47, '#FFD0F0'], [.5, '#FFFFFF'], [.53, '#7A0030'], [.72, '#FF6A1A'], [1, '#FFE84A']], ext: ['#1E0018', '#7A0A50'], line: '#1E0018' },
  ice: { stops: [[0, '#00306A'], [.35, '#28C8FF'], [.47, '#E0FFFF'], [.5, '#FFFFFF'], [.53, '#003A7A'], [.75, '#1A8CFF'], [1, '#B8F4FF']], ext: ['#000A2A', '#0A3A8A'], line: '#000A2A' },
  lime: { stops: [[0, '#0A3A00'], [.35, '#6AFF2A'], [.47, '#F0FFD0'], [.5, '#FFFFFF'], [.53, '#0A4A10'], [.75, '#2AD84A'], [1, '#E0FF6A']], ext: ['#021400', '#0A5A1A'], line: '#021400' },
  purple: { stops: [[0, '#1A0050'], [.35, '#9A5AFF'], [.47, '#F0E0FF'], [.5, '#FFFFFF'], [.53, '#2A0A6A'], [.75, '#7A3AFF'], [1, '#FFB8F8']], ext: ['#08001E', '#3A107A'], line: '#08001E' },
  silver: { stops: [[0, '#3A4050'], [.4, '#DDE2EE'], [.5, '#FFFFFF'], [.53, '#40485A'], [.8, '#AEB6C8'], [1, '#F4F6FA']], ext: ['#10141E', '#4A5264'], line: '#0C1018' },
  red: { stops: [[0, '#4A0008'], [.3, '#F0303A'], [.46, '#FFB8B0'], [.5, '#FFFFFF'], [.53, '#5A0010'], [.75, '#E3262F'], [1, '#FFC0A8']], ext: ['#260004', '#8A1020'], line: '#200004' },
};
// chromeText(str, x, y, size, o): extruded 90s chrome lettering, centred on (x, y) unless o.align ('left'|'right').
// o.style (key of CHROME, or 'rainbow'), o.font (FONTS key, default 'archivo'), o.depth (extrusion px), o.italic (slant, e.g. .15),
// o.spacing, o.s / o.sx / o.sy (scale), o.rot, o.alpha. Cached per string+style: animate with s/sx/position, not size. Returns the width.
function chromeText(str, x, y, size, o = {}) {
  const font = o.font ?? 'archivo', st = o.style ?? 'chrome', depth = Math.round(o.depth ?? size * .1), sp = o.spacing ?? 0, it = o.italic ?? .12;
  const S = CHROME[st] || CHROME.chrome;
  const tw = textW(str, size, font, sp), w = tw + depth + size * .6 + Math.abs(it) * size, h = size * 1.55 + depth;
  const img = cached(`chr|${str}|${size}|${font}|${st}|${depth}|${sp}|${it}`, w, h, () => {
    ctx.translate(size * .3 + Math.max(0, it) * size * .6, 0); ctx.transform(1, 0, -it, 1, it * size * 1.05, 0);
    ctx.font = `${size}px "${FONTS[font] || font}"`; ctx.letterSpacing = `${sp}px`; ctx.textAlign = 'left'; ctx.textBaseline = 'alphabetic';
    const by = size * 1.12;
    for (let i = depth; i >= 1; i--) { ctx.fillStyle = mixCol(S.ext[0], S.ext[1], 1 - i / depth); ctx.fillText(str, i * .6, by + i); }
    ctx.lineWidth = Math.max(2, size * .075); ctx.strokeStyle = S.line; ctx.lineJoin = 'round'; ctx.strokeText(str, 0, by);
    if (st === 'rainbow') {
      ctx.fillStyle = lg(0, 0, tw, 0, [[0, '#FF2A6A'], [.2, '#FF9A1A'], [.4, '#FFE81F'], [.6, '#3BFF6A'], [.8, '#1FB8FF'], [1, '#B04BFF']]); ctx.fillText(str, 0, by);
      ctx.fillStyle = lg(0, by - size * .75, 0, by, [[0, 'rgb(255 255 255 / .75)'], [.45, 'rgb(255 255 255 / .1)'], [.5, 'rgb(0 0 0 / .25)'], [1, 'rgb(0 0 0 / 0)']]); ctx.fillText(str, 0, by);
    } else { ctx.fillStyle = lg(0, by - size * .74, 0, by + size * .02, S.stops); ctx.fillText(str, 0, by); }
    ctx.lineWidth = Math.max(1, size * .018); ctx.strokeStyle = 'rgb(255 255 255 / .6)'; ctx.strokeText(str, -size * .01, by - size * .012);
  });
  const s = o.s ?? 1, ax = o.align === 'left' ? (img.lw / 2 - size * .3) * s : o.align === 'right' ? -(img.lw / 2 - size * .3) * s : 0;
  blit(img, x + ax, y + (depth / 2 - size * .05) * s, { rot: o.rot, s, sx: o.sx, sy: o.sy, alpha: o.alpha });
  return tw * s;
}
// wordArt(str, x, y, size, o): Office-97 WordArt — rainbow letters with a 3D extrusion laid along a curve.
// o.shape: 'arch' | 'wave' | 'bulge' | 'slant' | 'flat', o.amp (px), o.phase (animate the wave), o.fill ('rainbow' or [c0, c1]),
// o.font ('archivo'), o.depth, o.spacing (extra px), o.pop (0..1: letters pop in left→right), o.rot.
function wordArt(str, x, y, size, o = {}) {
  const font = o.font ?? 'archivo', chars = [...String(str)], shape = o.shape ?? 'wave', amp = o.amp ?? size * .35, ph = o.phase ?? 0, dep = o.depth ?? Math.round(size * .12);
  const ws = chars.map(c => textW(c, size, font) + (o.spacing ?? size * .02)), tot = ws.reduce((a, b) => a + b, 0);
  const fillKey = Array.isArray(o.fill) ? o.fill.join(',') : (o.fill ?? 'rainbow');
  ctx.save(); ctx.translate(x, y); if (o.rot) ctx.rotate(o.rot);
  let cx = -tot / 2;
  chars.forEach((c, i) => {
    const w = ws[i], u = (cx + w / 2) / (tot / 2), mid = cx + w / 2; cx += w;
    if (c === ' ') return;
    const k = o.pop === undefined ? 1 : backOut(clamp(o.pop * (chars.length + 3) - i), 2.2); if (k <= 0) return;
    let dy = 0, rot = 0, sc = 1;
    if (shape === 'arch') { dy = -amp * (1 - u * u); rot = Math.atan(2 * amp * u / (tot / 2)) * .9; }
    else if (shape === 'wave') { dy = Math.sin(u * 3 + ph) * amp * .5; rot = Math.cos(u * 3 + ph) * amp * 1.5 / tot; }
    else if (shape === 'bulge') sc = 1 + (1 - u * u) * .35;
    else if (shape === 'slant') { sc = 1 + u * .3; dy = -u * amp * .4; }
    const img = cached(`wa|${c}|${size}|${font}|${fillKey}|${dep}`, size * 1.3 + dep, size * 1.6 + dep, (cw, ch) => {
      ctx.font = `${size}px "${FONTS[font] || font}"`; ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
      const bx = (cw - dep) / 2, by = (ch - dep) / 2 + size * .06;
      for (let d = dep; d >= 1; d--) { ctx.fillStyle = mixCol('#1A0830', '#5A2A8A', 1 - d / dep); ctx.fillText(c, bx + d, by + d); }
      ctx.lineWidth = size * .08; ctx.strokeStyle = '#140820'; ctx.lineJoin = 'round'; ctx.strokeText(c, bx, by);
      const fill = Array.isArray(o.fill) ? lg(0, by - size * .5, 0, by + size * .5, [[0, o.fill[0]], [1, o.fill[1]]]) : lg(0, by - size * .5, 0, by + size * .5, [[0, '#FF3A7A'], [.25, '#FFA01A'], [.45, '#FFEA2A'], [.65, '#3BEF6A'], [.85, '#2AA8FF'], [1, '#A04BFF']]);
      ctx.fillStyle = fill; ctx.fillText(c, bx, by);
      ctx.fillStyle = 'rgb(255 255 255 / .45)'; ctx.save(); ctx.beginPath(); ctx.rect(0, 0, cw, by - size * .08); ctx.clip(); ctx.fillText(c, bx, by); ctx.restore();
    });
    blit(img, mid + dep / 2, dy + dep / 2, { rot, s: sc * k });
  });
  ctx.restore();
  return tot;
}
// burst(str, x, y, r, o): a starburst price-tag sticker ("NEW!", "BUY 3!"). o.col, o.ink, o.edge (text outline), o.pop (0..1), o.rot, o.spin (rad/s), o.size, o.font, o.n.
function burst(str, x, y, r, o = {}) {
  const k = o.pop ?? 1; if (k <= 0) return;
  ctx.save(); ctx.translate(x, y); const s = backOut(clamp(k), 2.4); ctx.scale(s, s); ctx.rotate((o.rot ?? -.12) + (o.spin ?? 0) * T);
  const col = o.col ?? EP.yellow;
  poly(starPts(6, 8, r, .78, o.n ?? 16, 0)); paint('rgb(0 0 0 / .35)');
  poly(starPts(0, 0, r, .78, o.n ?? 16, 0)); ctx.fillStyle = rg(-r * .3, -r * .3, 0, r * 1.1, [[0, tint(col, .5)], [.6, col], [1, shade(col, .2)]]); ctx.fill(); ctx.strokeStyle = EP.line; ctx.lineWidth = r * .05; ctx.lineJoin = 'round'; ctx.stroke();
  ctx.rotate(-(o.spin ?? 0) * T);
  const lines = String(str).split('\n'), sz = o.size ?? r * .5 / Math.max(1, lines.length * .8);
  lines.forEach((l, i) => ptext(l, 0, (i - (lines.length - 1) / 2) * sz * 1.02, sz, { font: o.font ?? 'archivo', fill: o.ink ?? EP.red, maxW: r * 1.45, strokes: [[o.edge ?? (/^#F/i.test(o.ink ?? '') ? EP.line : EP.white), sz * .18]] }));
  ctx.restore();
}
// nameTip(name, x, y, o): a Windows 98 tooltip naming a person (pale-yellow box, black border). (x, y) = box centre;
// o.to ([x, y]: a pointer toward the person), o.pop (0..1), o.size (text px, default 30), o.sub (a smaller second line), o.rot.
function nameTip(name, x, y, o = {}) {
  const k = o.pop ?? 1; if (k <= 0) return;
  const size = o.size ?? 30, sub = o.sub, w = Math.max(ptextW(name, size), sub ? ptextW(sub, size * .6, 'code') : 0) + size * .9, h = size * (sub ? 1.95 : 1.35);
  ctx.save(); ctx.translate(x, y); if (o.rot) ctx.rotate(o.rot); const s = lerp(.4, 1, backOut(clamp(k), 2)); ctx.scale(s, s);
  if (o.to) { const tx = (o.to[0] - x) / s, ty = (o.to[1] - y) / s, a = Math.atan2(ty, tx), bx = clamp(tx, -w / 2 + 14, w / 2 - 14), by = ty > 0 ? h / 2 : -h / 2;
    const L = Math.min(Math.hypot(tx - bx, ty - by) * .6, 36); poly([[bx - 12, by], [bx + Math.cos(a) * L, by + Math.sin(a) * L], [bx + 12, by]]); paint(EP.w98tip, '#000', 2.5); }
  ctx.fillStyle = 'rgb(0 0 0 / .35)'; ctx.fillRect(-w / 2 + 6, -h / 2 + 7, w, h);
  ctx.fillStyle = EP.w98tip; ctx.fillRect(-w / 2, -h / 2, w, h); ctx.strokeStyle = '#000'; ctx.lineWidth = 2.5; ctx.strokeRect(-w / 2, -h / 2, w, h);
  txt(name, 0, sub ? -h / 2 + size * .72 : 1, size, '#000', { font: 'archivo' });
  if (sub) txt(sub, 0, h / 2 - size * .5, size * .6, '#333', { font: 'code' });
  ctx.restore();
}
// 5×7 pixel font for LCDs, dot-matrix displays and CD players. pixText(str, x, y, px, col, o): (x, y) = top-left / top-centre / top-right.
const PIXFONT = {
  "A": '.###.#...##...#######...##...##...#', "B": '####.#...##...#####.#...##...#####.', "C": '.###.#...##....#....#....#...#.###.', "D": '####.#...##...##...##...##...#####.',
  "E": '######....#....####.#....#....#####', "F": '######....#....####.#....#....#....', "G": '.###.#...##....#.####...##...#.####', "H": '#...##...##...#######...##...##...#',
  "I": '.###...#....#....#....#....#...###.', "J": '..###...#....#....#....#.#..#..##..', "K": '#...##..#.#.#..##...#.#..#..#.#...#', "L": '#....#....#....#....#....#....#####',
  "M": '#...###.###.#.##.#.##...##...##...#', "N": '#...##...###..##.#.##..###...##...#', "O": '.###.#...##...##...##...##...#.###.', "P": '####.#...##...#####.#....#....#....',
  "Q": '.###.#...##...##...##.#.##..#..##.#', "R": '####.#...##...#####.#.#..#..#.#...#', "S": '.#####....#.....###.....#....#####.', "T": '#####..#....#....#....#....#....#..',
  "U": '#...##...##...##...##...##...#.###.', "V": '#...##...##...##...##...#.#.#...#..', "W": '#...##...##...##.#.##.#.##.#.#.#.#.', "X": '#...##...#.#.#...#...#.#.#...##...#',
  "Y": '#...##...#.#.#...#....#....#....#..', "Z": '#####....#...#...#...#...#....#####', "0": '.###.#...##..###.#.###..##...#.###.', "1": '..#...##....#....#....#....#...###.',
  "2": '.###.#...#....#...#...#...#...#####', "3": '#####...#...#.....#.....##...#.###.', "4": '...#...##..#.#.#..#.#####...#....#.', "5": '######....####.....#....##...#.###.',
  "6": '..##..#...#....####.#...##...#.###.', "7": '#####....#...#...#...#....#....#...', "8": '.###.#...##...#.###.#...##...#.###.', "9": '.###.#...##...#.####....#...#..##..',
  " ": '...................................', ":": '......##...##........##...##.......', ".": '..........................##...##..', "-": '...............#####...............',
  "/": '....#...#....#...#...#....#...#....', "▶": '#....##...###..####.###..##...#....', "◀": '....#...##..###.####..###...##....#', "❚": '##.####.####.####.####.####.####.##',
  "!": '..#....#....#....#....#.........#..', "?": '.###.#...#....#...#...#.........#..', "'": '..#....#...#.......................', ",": '.....................##....#...#...',
  "#": '.#.#..#.#.#####.#.#.#####.#.#..#.#.', "%": '##...##..#...#...#...#...#..##...##', "+": '.......#....#..#####..#....#.......', "$": '..#...#####.#...###...#.#####...#..',
  "=": '..........#####.....#####..........', ">": '#.....#.....#.....#...#...#...#....', "<": '....#...#...#...#.....#.....#.....#', "_": '..............................#####', "*": '.....#.#.#.###.#####.###.#.#.#.....',
};
const pixW = (str, px) => [...String(str)].length * 6 * px - px;
function pixText(str, x, y, px, col = EP.white, o = {}) {
  str = String(str).toUpperCase(); const w = pixW(str, px), x0 = o.align === 'right' ? x - w : o.align === 'center' ? x - w / 2 : x;
  const chars = [...str];
  const pass = (c, grow) => { ctx.fillStyle = c; chars.forEach((ch, i) => { const g = PIXFONT[ch] || PIXFONT['?']; for (let r = 0; r < 7; r++) for (let q = 0; q < 5; q++) if (g[r * 5 + q] === '#') ctx.fillRect(x0 + (i * 6 + q) * px - grow, y + r * px - grow, px * (o.dot ?? 1) + grow * 2, px * (o.dot ?? 1) + grow * 2); }); };
  ctx.save(); if (o.alpha !== undefined) ctx.globalAlpha *= o.alpha;
  if (o.off) pass(o.off, 0);                       // unlit LCD segments behind (pass the full-block glyph colour)
  if (o.glow) { ctx.save(); ctx.globalCompositeOperation = 'lighter'; ctx.globalAlpha *= .35; pass(col, px * .6); ctx.restore(); }
  if (o.edge) pass(o.edge, px * .3);
  pass(col, 0);
  ctx.restore(); return w;
}
// 7-segment LED digits (Minesweeper counters, BPM displays, clocks). segText(str, x, y, h, col, o): top-left at (x, y), digit height h.
// Characters: 0-9, space, '-', ':' and '.'. o.off (unlit segment colour), o.align. Returns the width.
const _SEG = { '0': 'abcdef', '1': 'bc', '2': 'abdeg', '3': 'abcdg', '4': 'bcfg', '5': 'acdfg', '6': 'acdefg', '7': 'abc', '8': 'abcdefg', '9': 'abcdfg', '-': 'g', ' ': '' };
function segText(str, x, y, h, col = EP.red, o = {}) {
  const cw = h * .56, gap = h * .16, th = h * .12, chars = [...String(str)];
  const wOf = c => c === ':' || c === '.' ? h * .22 : cw;
  const tw = chars.reduce((a, c) => a + wOf(c) + gap, -gap);
  let cx = o.align === 'right' ? x - tw : o.align === 'center' ? x - tw / 2 : x;
  const seg7 = (sx, sy, on, c) => {
    const S = { a: [0, 0, 1, 0], b: [1, 0, 1, .5], c: [1, .5, 1, 1], d: [0, 1, 1, 1], e: [0, .5, 0, 1], f: [0, 0, 0, .5], g: [0, .5, 1, .5] };
    for (const [k, [x0, y0, x1, y1]] of Object.entries(S)) {
      const lit = on.includes(k); if (!lit && !o.off) continue;
      ctx.fillStyle = lit ? c : o.off; const ax = sx + x0 * (cw - th), ay = sy + y0 * (h - th), bx = sx + x1 * (cw - th), by = sy + y1 * (h - th);
      if (y0 === y1) poly([[ax + th * .5, ay + th * .5], [ax + th, ay], [bx, by], [bx + th * .5, by + th * .5], [bx, by + th], [ax + th, ay + th]]);
      else poly([[ax + th * .5, ay + th * .5], [ax + th, ay + th], [bx + th, by], [bx + th * .5, by + th * .5], [bx, by], [ax, ay + th]]);
      ctx.fill();
    }
  };
  ctx.save();
  for (const c of chars) {
    if (c === ':' || c === '.') { ctx.fillStyle = col; if (c === ':') ctx.fillRect(cx, y + h * .25, th, th); ctx.fillRect(cx, y + h * (c === ':' ? .68 : .88), th, th); }
    else seg7(cx, y, _SEG[c] ?? '', col);
    cx += wOf(c) + gap;
  }
  ctx.restore(); return tw;
}
// creditBlock(k, o): the music-channel video credit (lower left, white on nothing, as MTV/VIVA ran it at the start and end of a video).
// k 0..1 fades/slides it in; o.lines overrides the four lines; o.x, o.y (top-left of the first line).
const CREDIT = ['DJ Clawd pres. Softmax feat. MC Token', 'We Didn\'t Start The Scaling', 'Scaling Hits \'26', 'Hyperparameter Records'];
function creditBlock(k, o = {}) {
  if (k <= 0) return; const L = o.lines ?? CREDIT, x = o.x ?? 110, y = o.y ?? 770, a = easeOut(clamp(k));
  ctx.save(); ctx.globalAlpha *= a;
  const sizes = [40, 46, 30, 30], fonts = ['archivo', 'archivo', 'archivo', 'archivo'];
  let yy = y;
  L.forEach((s, i) => { txt(s, x - (1 - a) * 40 * (i + 1), yy, sizes[i], i === 1 ? EP.white : 'rgb(255 255 255 / .92)', { font: fonts[i], align: 'left', shadow: [3, 3], shadowCol: 'rgb(0 0 0 / .55)' }); yy += sizes[i] * 1.28; });
  ctx.restore();
}

// =====================================================================================================
// THE TOY RIG — every person is a glossy vinyl-toy figure from a 1997 CGI render: a big round head, a bean torso, and
// Rayman-style floating hands and sneakers (no arms or legs, so no awkward anatomy). toy(x, y, s, o):
//   (x, y) = ground point between the feet; s = unit, a standing toy is ≈ 10.5s tall (head centre y − 8.35s, eyes ≈ y − 8.3s,
//   mouth ≈ y − 7.4s, shoulders ≈ y − 5.8s, waist ≈ y − 3.7s, hips ≈ y − 2.3s).
//   Look: skin (TSKIN index or colour), hair (short|side|swoop|slick|spiky|curly|buzz|bald|balding|messy|bob|long|ponytail|bigHair|bun|
//   mohawk|afro|swirl|none), hairCol, hairCol2 (streak), top (tee|hoodie|suit|leather|labcoat|sweater|track|crop|dress|turtleneck|shirt|layers|
//   vest|robe|jersey|coat), topCol, trim (stripes/collar colour), tie (colour | false), longTie (the tie hangs past the belt), pin (a flag
//   lapel pin on a suit), print (chest text), pants, skirt (colour: a mini skirt),
//   shoes (sneaker|platform|dress|boot), shoeCol, soleCol, hat (cap|capBack|fedora|visor|beanie|bucket|crown|party|hardhat|grad|headband|halo),
//   hatCol, glasses (round|square|shades|rave|vr|star), beard (colour | true), stubble, mustache, chain (colour), earrings ('star'|'hoop'),
//   headset (pop-star mic), phones (DJ headphones), hood (hood up), lashes, lips (colour), clip ('star' hair clip), gloves (colour),
//   mittens (colour), armCol / legCol (override the sleeve and trouser colours of the limbs), sil (flat silhouette colour: no face), rim
//   (this figure's rim-light colour), line (outline colour), shadow (false).
//   Face: turn (−1..1, 3/4 view toward screen right is +), eyes (dot|happy|closed|wide|x|heart|star|wink|angry|worried|spiral|cry|sleepy),
//   look ([x, y] pupil shift −1..1), brows (up|angry|worried|flat|none), mouth (smile|grin|open|O|o|flat|frown|smirk|scream|wavy|cat|sing),
//   talk (0..1 mouth openness, overrides mouth), blush (0..1), sweat, tears, emote (sweat|anger|heart|note|excl|q|spark|zzz), emoteK.
//   Pose: hL / hR ([x, y] hand centres in s from the ground point; rest ≈ [∓2.35, −3.5], overhead ≈ [∓1.7, −11.2]), gL / gR (open|fist|point|
//   peace|thumb|wave|flat|mic), mic ('L'|'R': a handheld mic at the mouth), hold / holdL (fn(s) drawn at that hand in px, upright),
//   fL / fR ([dx, dy] foot offsets; dy < 0 lifts), bob (0..1 knee dip), jump (s), lean (rad), rot (rad), headTilt (rad), nod, flip, sq, dy,
//   swing (ponytail swing, rad; automatic from the beat if omitted), tag (name: a Win98 tooltip over the head), tagPop, tagDy.
// =====================================================================================================
const _HY = -8.35, _HR = 2.12, _HRY = 1.98;
function _toyHand(hx, hy, g, ang, side, col, o = {}) {
  const lw = .075, L = o.line ?? EP.line, rim = o.rim, G = (pf, c, box, extra = {}) => gloss(pf, c, { box, lw, line: L, rim, rimK: .55, spec: .5, ...extra });
  ctx.save(); ctx.translate(hx, hy); ctx.scale(o.hs ?? 1.3, o.hs ?? 1.3);
  const up = g === 'peace' || g === 'thumb' || g === 'wave';
  if (!up) { ctx.rotate(ang); if (side < 0 && Math.cos(ang) < 0) ctx.scale(1, -1); } else if (side < 0) ctx.scale(-1, 1);
  const cuff = o.cuff;
  if (cuff) G(pfRR(-.72, -.3, .34, .6, .14), cuff, [-.72, -.3, .34, .6]);
  const fist = () => { G(pfEll(0, 0, .47, .44), col, [-.47, -.44, .94, .88]); ctx.beginPath(); ctx.arc(.08, .02, .3, -.6, .9); ctx.strokeStyle = alpha(L, .35); ctx.lineWidth = .05; ctx.stroke(); };
  switch (g) {
    case 'fist': fist(); G(pfCap(-.12, -.28, .22, -.14, .14), col, [-.3, -.45, .7, .5], { spec: .3 }); break;
    case 'point': G(pfCap(.2, -.14, .98, -.16, .135), col, [.05, -.3, 1.1, .3]); fist(); G(pfCap(-.12, -.28, .18, -.12, .13), col, [-.3, -.45, .6, .5], { spec: .3 }); break;
    case 'mic': fist(); break;
    case 'flat': G(pfCap(-.02, -.3, .2, -.5, .14), col, [-.2, -.7, .5, .5]); G(pfEll(.2, .02, .62, .34), col, [-.42, -.32, 1.24, .68]); break;
    case 'peace': G(pfCap(-.12, -.18, -.34, -1.05, .13), col, [-.5, -1.2, .5, 1.1]); G(pfCap(.12, -.18, .34, -1.05, .13), col, [0, -1.2, .5, 1.1]); fist(); G(pfCap(-.18, .05, .2, -.1, .13), col, [-.3, -.25, .6, .4], { spec: .3 }); break;
    case 'thumb': G(pfCap(-.02, -.25, -.02, -.98, .15), col, [-.2, -1.15, .4, 1]); G(pfEll(0, .05, .5, .42), col, [-.5, -.37, 1, .84]); ctx.beginPath(); for (let i = 0; i < 3; i++) { ctx.moveTo(.06, -.12 + i * .17); ctx.lineTo(.42, -.12 + i * .17); } ctx.strokeStyle = alpha(L, .35); ctx.lineWidth = .045; ctx.stroke(); break;
    case 'wave': [-.5, -.17, .17, .5].forEach(a => G(pfCap(Math.sin(a) * .25, -.2, Math.sin(a) * .9, -.2 - Math.cos(a) * .72, .12), col, [-.9, -1.1, 1.8, 1])); G(pfCap(-.3, 0, -.78, -.28, .13), col, [-.95, -.45, .8, .6]); G(pfEll(0, .05, .45, .42), col, [-.45, -.37, .9, .84]); break;
    default: // open mitten
      G(pfCap(-.12, -.22, .06, -.56, .15), col, [-.3, -.75, .5, .6]);
      G(pfEll(.12, .02, .56, .46), col, [-.44, -.44, 1.12, .92]);
      ctx.beginPath(); ctx.moveTo(.42, -.12); ctx.lineTo(.62, -.1); ctx.moveTo(.44, .12); ctx.lineTo(.64, .13); ctx.strokeStyle = alpha(L, .4); ctx.lineWidth = .045; ctx.stroke();
  }
  if (o.mitten) { ctx.fillStyle = alpha(EP.white, .55); for (let i = -1; i <= 1; i++) { ell(i * .2, .05, .06, .06); ctx.fill(); } }
  ctx.restore();
}
function _mic(hx, hy, tx, ty, o = {}) {
  const a = Math.atan2(ty - hy, tx - hx), L = 1.15, ex = hx + Math.cos(a) * L, ey = hy + Math.sin(a) * L, bx = hx - Math.cos(a) * .35, by = hy - Math.sin(a) * .35;
  gloss(pfCap(bx, by, ex, ey, .16), '#26222E', { box: [Math.min(bx, ex) - .2, Math.min(by, ey) - .2, Math.abs(ex - bx) + .4, Math.abs(ey - by) + .4], lw: .06, spec: .6, rimK: .5 });
  glossBall(ex, ey, .3, .3, o.micCol ?? '#C8CCD8', { lw: .06, rimK: .5 });
  ctx.strokeStyle = alpha('#40404A', .6); ctx.lineWidth = .03; ctx.beginPath(); ctx.moveTo(ex - .28, ey); ctx.lineTo(ex + .28, ey); ctx.moveTo(ex, ey - .28); ctx.lineTo(ex, ey + .28); ctx.stroke();
}
function _shoe(fx, fy, side, kind, col, sole, o) {
  ctx.save(); ctx.translate(fx, fy); ctx.scale(side, 1);
  const L = o.line ?? EP.line, G = (pf, c, box, x = {}) => gloss(pf, c, { box, lw: .07, line: L, rim: o.rim, rimK: .5, spec: .55, ...x });
  if (kind === 'platform' || kind === 'boot') {
    const tall = kind === 'boot' ? 1.2 : 1.6;
    G(pfPts([[-.5, -tall], [.35, -tall], [.42, -.62], [1.0, -.45], [1.02, -.02], [-.58, -.02]]), col, [-.6, -tall, 1.65, tall]);
    if (kind === 'platform') G(pfRR(-.66, -.36, 1.74, .46, .14), sole ?? EP.cyan, [-.66, -.36, 1.74, .46], { spec: .8 });
  } else if (kind === 'dress') {
    G(pfPts([[-.55, -.55], [.3, -.62], [1.0, -.3], [1.02, -.02], [-.56, -.02]]), col, [-.6, -.65, 1.65, .65]);
  } else {
    G(() => { ctx.moveTo(-.58, -.18); ctx.bezierCurveTo(-.62, -.88, .08, -.95, .32, -.6); ctx.bezierCurveTo(.72, -.52, 1.04, -.38, 1.0, -.1); ctx.quadraticCurveTo(.96, .06, .6, .06); ctx.lineTo(-.46, .06); ctx.quadraticCurveTo(-.64, .04, -.58, -.18); ctx.closePath(); }, col, [-.64, -.92, 1.7, .98]);
    ctx.fillStyle = sole ?? '#F4F4F8'; rrect(-.56, -.17, 1.56, .2, .08); ctx.fill(); ctx.strokeStyle = L; ctx.lineWidth = .05; ctx.stroke();
    if (o.shoeTrim) { ctx.strokeStyle = o.shoeTrim; ctx.lineWidth = .12; ctx.beginPath(); ctx.moveTo(-.2, -.5); ctx.quadraticCurveTo(.25, -.35, .55, -.52); ctx.stroke(); }
  }
  ctx.restore();
}
// Hair: back layer (behind the head) and front layer (over it), in head-local units (head centre at 0, 0).
function _hairBack(kind, col, o, swing) {
  const L = o.line ?? EP.line, G = (pf, box, x = {}) => gloss(pf, col, { box, lw: .075, line: L, rim: o.rim, spec: .55, ...x });
  switch (kind) {
    case 'long': G(pfRR(-2.45, -1.6, 4.9, 5.4, 1.6), [-2.45, -1.6, 4.9, 5.4]); break;
    case 'bob': G(() => { ctx.moveTo(-2.5, 1.4); ctx.bezierCurveTo(-2.9, -2.4, 2.9, -2.4, 2.5, 1.4); ctx.quadraticCurveTo(0, 1.9, -2.5, 1.4); ctx.closePath(); }, [-2.9, -2.4, 5.8, 4.3]); break;
    case 'bigHair': G(() => { const n = 11; for (let i = 0; i <= n; i++) { const a = Math.PI * .92 - i / n * Math.PI * 1.84 + Math.PI, r = 3.05 + (i % 2) * .25; const x = Math.cos(a) * r * 1.02, y = Math.sin(a) * r * .95 - .1; i ? ctx.quadraticCurveTo(Math.cos(a + .1) * (r + .5), Math.sin(a + .1) * (r + .45) - .1, x, y) : ctx.moveTo(x, y); } ctx.closePath(); }, [-3.4, -3.4, 6.8, 6.4]); break;
    case 'afro': G(pfEll(0, -.6, 3.0, 2.8), [-3, -3.4, 6, 5.6]); break;
    case 'ponytail': {
      ctx.save(); ctx.translate(0, -2.0); ctx.rotate(swing);
      G(() => { ctx.moveTo(-.5, .1); ctx.bezierCurveTo(-.5, -1.9, 2.2, -2.5, 2.9, -.6); ctx.bezierCurveTo(3.5, 1.1, 3.3, 3.4, 2.4, 5.4); ctx.bezierCurveTo(2.5, 3.6, 2.4, 1.4, 1.6, -.3); ctx.bezierCurveTo(1.2, -1.0, .5, -.7, .5, .15); ctx.closePath(); }, [-.6, -2.4, 4.1, 7.8]);
      if (o.hairCol2) { ctx.save(); ctx.beginPath(); ctx.moveTo(1.1, -1.35); ctx.bezierCurveTo(2.4, -1.3, 3.1, 1.0, 2.7, 4.2); ctx.strokeStyle = alpha(o.hairCol2, .9); ctx.lineWidth = .3; ctx.lineCap = 'round'; ctx.stroke(); ctx.restore(); }
      glossBall(0, -.05, .55, .45, o.hairCol2 ?? EP.magenta, { lw: .06, rim: o.rim });
      ctx.restore(); break;
    }
    case 'bun': glossBall(0, -2.3, .95, .85, col, { lw: .075, rim: o.rim, line: L }); break;
    case 'swirl': G(pfEll(.1, -1.2, 2.38, 1.75), [-2.3, -2.95, 4.8, 3.5]); break;
  }
}
function _hairFront(kind, col, o, phi) {
  const L = o.line ?? EP.line, G = (pf, box, x = {}) => gloss(pf, col, { box, lw: .075, line: L, rim: o.rim, spec: .6, ...x }), sx = Math.sin(phi) * .45;
  const cap = (edge, ry = 2.2, rx = 2.3) => () => { ctx.moveTo(-rx + .06, -.05); ctx.ellipse(0, -.08, rx, ry, 0, Math.PI, TAU); edge.forEach(([x, y]) => ctx.lineTo(x + sx * (1 - Math.abs(x) / 2.3), y)); ctx.closePath(); };
  switch (kind) {
    case 'short': G(cap([[2.1, -.45], [1.4, -.95], [.6, -.72], [-.2, -1.05], [-1.0, -.78], [-1.8, -.5], [-2.2, -.05]]), [-2.3, -2.3, 4.6, 2.3]); break;
    case 'side': G(cap([[2.15, -.6], [1.6, -1.25], [.5, -1.4], [-.6, -.95], [-1.5, -.35], [-2.2, .05]]), [-2.3, -2.3, 4.6, 2.4]); break;
    case 'swoop': G(cap([[2.15, -.8], [1.2, -1.55], [-.2, -1.25], [-1.3, -.85], [-2.1, -.3]], 2.55, 2.32), [-2.32, -2.6, 4.64, 2.6]); break;
    case 'slick': G(cap([[2.15, -.9], [1.2, -1.5], [0, -1.6], [-1.2, -1.45], [-2.15, -.85]], 2.4, 2.28), [-2.3, -2.5, 4.6, 2.5], { spec: .5, rimK: .35 });
      ctx.strokeStyle = alpha(EP.white, .18); ctx.lineWidth = .07; ctx.beginPath(); for (const d of [-.9, 0, .9]) { ctx.moveTo(d + sx, -1.6); ctx.quadraticCurveTo(d * 1.1 + sx, -2.2, d * .6 + sx, -2.35); } ctx.stroke(); break;
    case 'buzz': G(cap([[2.12, -.55], [1.2, -1.05], [0, -1.15], [-1.2, -1.05], [-2.12, -.55]], 2.08, 2.18), [-2.2, -2.2, 4.4, 2.2], { spec: .25, alpha: .92 }); break;
    case 'spiky': G(() => { ctx.moveTo(-2.25, -.1); const pts = [[-2.4, -1.6], [-1.9, -1.8], [-1.9, -2.7], [-1.1, -2.3], [-.7, -3.2], [-.1, -2.4], [.5, -3.3], [.8, -2.35], [1.6, -2.9], [1.6, -2.0], [2.5, -1.9], [2.2, -1.0], [2.25, -.1], [1.5, -.9], [.7, -.7], [-.2, -1.0], [-1.1, -.7], [-1.8, -.45]]; pts.forEach(([x, y]) => ctx.lineTo(x + sx * .5, y)); ctx.closePath(); }, [-2.5, -3.3, 5, 3.3]); break;
    case 'curly': G(() => { const n = 9; ctx.moveTo(-2.2, -.2); for (let i = 0; i <= n; i++) { const a = Math.PI + i / n * Math.PI, a0 = a - Math.PI / n / 2; ctx.quadraticCurveTo(Math.cos(a0) * 2.95, Math.sin(a0) * 2.75 - .1, Math.cos(a) * 2.35, Math.sin(a) * 2.25 - .1); } [[1.9, -.8], [1.2, -1.0], [.5, -.75], [-.3, -1.0], [-1.1, -.8], [-1.8, -.7]].forEach(([x, y]) => ctx.lineTo(x + sx, y)); ctx.closePath(); }, [-2.8, -2.9, 5.6, 2.9]); break;
    case 'balding': for (const sd of [-1, 1]) G(pfPts([[sd * 2.2, .35], [sd * 2.3, -.6], [sd * 1.95, -1.35], [sd * 1.55, -1.3], [sd * 1.75, -.4], [sd * 1.85, .4]]), [-2.4, -1.4, 4.8, 1.8]); break;
    case 'messy': for (const sd of [-1, 1]) G(pfPts([[sd * 2.05, .5], [sd * 2.75, .1], [sd * 2.4, -.2], [sd * 2.95, -.7], [sd * 2.3, -.85], [sd * 2.6, -1.5], [sd * 1.9, -1.4], [sd * 1.6, -1.9], [sd * 1.5, -1.1], [sd * 1.85, .2]]), [-3, -2, 6, 2.6]);
      G(cap([[1.6, -1.6], [.8, -1.9], [0, -1.7], [-.8, -1.95], [-1.6, -1.6]], 2.12, 2.0), [-2, -2.2, 4, 2.2], { alpha: .85 }); break;
    case 'bob': G(cap([[2.2, .9], [2.0, -.3], [1.5, -.55], [.5, -.5], [-.5, -.52], [-1.5, -.55], [-2.0, -.3], [-2.2, .9]], 2.25, 2.35), [-2.4, -2.4, 4.8, 3.4]); break;
    case 'long': G(cap([[2.2, 1.6], [2.05, -.3], [1.2, -1.2], [.1, -1.3], [-.9, -.9], [-1.9, -.2], [-2.2, 1.6]], 2.25, 2.33), [-2.4, -2.4, 4.8, 4.1]); break;
    case 'bigHair': G(cap([[2.35, .9], [2.1, -.5], [1.2, -1.05], [.2, -.85], [-.6, -1.2], [-1.6, -.9], [-2.2, -.2], [-2.35, .9]], 2.45, 2.45), [-2.5, -2.6, 5, 3.6]);
      if (o.hairCol2) { ctx.save(); ctx.beginPath(); ctx.moveTo(-.4 + sx, -2.4); ctx.quadraticCurveTo(-1.6 + sx, -1.6, -1.5 + sx, -.9); ctx.strokeStyle = alpha(o.hairCol2, .9); ctx.lineWidth = .35; ctx.lineCap = 'round'; ctx.stroke(); ctx.restore(); } break;
    case 'ponytail': G(cap([[2.15, -.5], [1.4, -1.25], [.4, -1.45], [-.5, -1.35], [-1.4, -1.2], [-2.15, -.5]], 2.2, 2.2), [-2.2, -2.3, 4.4, 2.3], { spec: .9 });
      if (o.hairCol2) { ctx.save(); ctx.beginPath(); ctx.moveTo(.7 + sx, -1.4); ctx.quadraticCurveTo(.4 + sx, -2.0, -.2 + sx, -2.2); ctx.strokeStyle = alpha(o.hairCol2, .9); ctx.lineWidth = .3; ctx.lineCap = 'round'; ctx.stroke(); ctx.restore(); } break;
    case 'bun': G(cap([[2.15, -.6], [1.2, -1.35], [0, -1.5], [-1.2, -1.35], [-2.15, -.6]], 2.18, 2.2), [-2.2, -2.3, 4.4, 2.3]); break;
    case 'mohawk': G(pfPts([[-.45, -1.6], [-.5, -2.9], [0, -3.6], [.5, -2.9], [.45, -1.6]].map(([x, y]) => [x + sx, y])), [-.6, -3.6, 1.2, 2]); break;
    case 'afro': G(cap([[2.2, -.3], [1.4, -.95], [0, -1.05], [-1.4, -.95], [-2.2, -.3]], 2.35, 2.4), [-2.4, -2.5, 4.8, 2.5], { spec: .2 }); break;
    case 'swirl': {
      // the golden coif: short left side, a tall front wave peaking over the left brow, swept across and down over the right temple into a flip
      G(() => { ctx.moveTo(-2.15, .3); ctx.bezierCurveTo(-2.55, -.7, -2.75, -2.2, -2.0, -3.0); ctx.bezierCurveTo(-1.2, -3.9, .9, -3.95, 2.3, -3.0);
        ctx.bezierCurveTo(3.0, -2.5, 3.45, -1.8, 3.3, -1.2); ctx.quadraticCurveTo(2.9, -1.5, 2.45, -1.25); ctx.bezierCurveTo(2.65, -.75, 2.5, -.15, 2.2, .2); ctx.quadraticCurveTo(2.05, -.6, 1.75, -.9);
        ctx.bezierCurveTo(1.0 + sx, -1.05, .2 + sx, -1.1, -.5 + sx * .8, -1.5); ctx.bezierCurveTo(-1.0 + sx * .5, -1.8, -1.55, -1.75, -1.85, -1.2); ctx.quadraticCurveTo(-2.0, -.5, -1.9, .3); ctx.closePath(); }, [-2.75, -3.95, 6.2, 4.25], { spec: .8 });
      // the wave's underside (a shadow under the front) and the comb lines sweeping up and over to the right
      ctx.save(); ctx.lineCap = 'round'; ctx.strokeStyle = alpha(shade(col, .45), .7); ctx.lineWidth = .14; ctx.beginPath(); ctx.moveTo(-1.75, -1.35); ctx.bezierCurveTo(-1.2, -1.95, -.2, -1.75, .6 + sx, -1.3); ctx.stroke();
      ctx.strokeStyle = alpha(o.hairCol2 ?? tint(col, .55), .85); ctx.lineWidth = .12; ctx.beginPath();
      for (const [d, e] of [[0, 1], [.45, .92], [.9, .84]]) { ctx.moveTo(-1.9 + d * .35, -1.7 - d * .75); ctx.bezierCurveTo(-1.2 + d * .3, -3.35 + d * .6, 1.4, -3.45 + d * .75, 3.1 * e, -1.45 - d * .4); }
      ctx.stroke(); ctx.restore(); break;
    }
  }
}
function _hat(kind, col, o, phi) {
  const L = o.line ?? EP.line, G = (pf, c, box, x = {}) => gloss(pf, c, { box, lw: .075, line: L, rim: o.rim, spec: .55, ...x }), sx = Math.sin(phi) * .6, c2 = o.hatCol2 ?? EP.white;
  switch (kind) {
    case 'cap': G(() => { ctx.moveTo(-2.25, -.95); ctx.bezierCurveTo(-2.3, -2.9, 2.3, -2.9, 2.25, -.95); ctx.closePath(); }, col, [-2.3, -2.5, 4.6, 1.6]);
      G(pfEll(sx * 1.2 + .1, -.95, 1.9, .42), shade(col, .1), [-2, -1.4, 4, .9]); glossBall(0, -2.42, .18, .16, col, { lw: .05 }); break;
    case 'capBack': G(() => { ctx.moveTo(-2.25, -.9); ctx.bezierCurveTo(-2.3, -2.95, 2.3, -2.95, 2.25, -.9); ctx.quadraticCurveTo(0, -1.25, -2.25, -.9); ctx.closePath(); }, col, [-2.3, -2.55, 4.6, 1.7]);
      rrect(-.8 + sx, -1.55, 1.6, .55, .25); paint(shade(col, .45)); ctx.strokeStyle = c2; ctx.lineWidth = .12; ctx.beginPath(); ctx.moveTo(-.55 + sx, -1.28); ctx.lineTo(.55 + sx, -1.28); ctx.stroke();
      glossBall(0, -2.45, .18, .16, c2, { lw: .05 }); break;
    case 'fedora': G(pfEll(0, -1.3, 3.0, .55), col, [-3, -1.85, 6, 1.1]); G(() => { ctx.moveTo(-1.75, -1.35); ctx.bezierCurveTo(-1.9, -3.4, 1.9, -3.4, 1.75, -1.35); ctx.closePath(); }, col, [-1.9, -3, 3.8, 1.7]);
      ctx.fillStyle = o.hatBand ?? '#111'; ctx.fillRect(-1.78, -1.95, 3.56, .42); ctx.beginPath(); ctx.moveTo(-.6 + sx, -2.9); ctx.quadraticCurveTo(sx, -2.55, .6 + sx, -2.9); ctx.strokeStyle = alpha(L, .5); ctx.lineWidth = .08; ctx.stroke(); break;
    case 'visor': ctx.fillStyle = alpha(col, .55); ell(sx, -1.0, 2.2, .75); ctx.fill(); ctx.strokeStyle = L; ctx.lineWidth = .07; ctx.stroke(); G(pfRR(-2.2, -1.75, 4.4, .6, .3), shade(col, .15), [-2.2, -1.75, 4.4, .6]); break;
    case 'beanie': G(() => { ctx.moveTo(-2.25, -.7); ctx.bezierCurveTo(-2.3, -3.2, 2.3, -3.2, 2.25, -.7); ctx.closePath(); }, col, [-2.3, -2.8, 4.6, 2.1]); G(pfRR(-2.35, -1.25, 4.7, .75, .3), shade(col, .15), [-2.35, -1.25, 4.7, .75]); glossBall(0, -2.85, .45, .42, c2, { lw: .06 }); break;
    case 'bucket': G(pfPts([[-2.9, -.55], [-1.9, -1.4], [1.9, -1.4], [2.9, -.55], [2.4, -.35], [-2.4, -.35]]), shade(col, .08), [-2.9, -1.4, 5.8, 1.1]); G(() => { ctx.moveTo(-1.95, -1.3); ctx.bezierCurveTo(-2.0, -3.2, 2.0, -3.2, 1.95, -1.3); ctx.closePath(); }, col, [-2, -2.8, 4, 1.5]); break;
    case 'crown': G(pfPts([[-1.7, -1.3], [-1.9, -3.0], [-.9, -2.1], [0, -3.3], [.9, -2.1], [1.9, -3.0], [1.7, -1.3]]), EP.gold, [-1.9, -3.3, 3.8, 2]); for (const [x, c] of [[-.9, EP.red], [0, EP.cyan], [.9, EP.magenta]]) glossBall(x, -1.65, .2, .2, c, { lw: .04 }); break;
    case 'party': G(pfPts([[-1.1, -1.6], [.3 + sx * .3, -4.4], [1.2, -1.6]]), col, [-1.1, -4.4, 2.3, 2.8]); glossBall(.3 + sx * .3, -4.45, .35, .35, c2, { lw: .05 }); break;
    case 'hardhat': G(() => { ctx.moveTo(-2.1, -1.1); ctx.bezierCurveTo(-2.1, -3.2, 2.1, -3.2, 2.1, -1.1); ctx.closePath(); }, col ?? EP.yellow, [-2.1, -2.7, 4.2, 1.6]); G(pfRR(-2.6, -1.3, 5.2, .4, .2), col ?? EP.yellow, [-2.6, -1.3, 5.2, .4]); break;
    case 'grad': G(pfPts([[0, -3.3], [2.9, -2.6], [0, -1.9], [-2.9, -2.6]]), '#15151C', [-2.9, -3.3, 5.8, 1.4]); G(pfRR(-1.6, -2.4, 3.2, 1.1, .2), '#15151C', [-1.6, -2.4, 3.2, 1.1]); ctx.strokeStyle = EP.gold; ctx.lineWidth = .12; ctx.beginPath(); ctx.moveTo(0, -2.6); ctx.lineTo(1.9, -1.9); ctx.lineTo(1.9, -.9); ctx.stroke(); break;
    case 'headband': G(pfRR(-2.25, -1.5, 4.5, .62, .3), col, [-2.25, -1.5, 4.5, .62]); break;
    case 'halo': ctx.save(); ctx.globalCompositeOperation = 'lighter'; ctx.strokeStyle = alpha(EP.gold, .9); ctx.lineWidth = .28; ell(0, -3.1, 1.6, .42); ctx.stroke(); ctx.restore(); break;
  }
}
function _glasses(kind, o, ex) {
  const L = o.line ?? EP.line, y = .02;
  switch (kind) {
    case 'round': case 'square': {
      for (const [x, w] of ex) { if (w < .2) continue; kind === 'round' ? ell(x, y, .55 * w, .52) : rrect(x - .6 * w, y - .45, 1.2 * w, .9, .15); ctx.fillStyle = 'rgb(220 240 255 / .28)'; ctx.fill(); ctx.strokeStyle = o.frameCol ?? '#1A1420'; ctx.lineWidth = .13; ctx.stroke(); }
      const vis = ex.filter(e => e[1] >= .2); if (vis.length === 2) { ctx.beginPath(); ctx.moveTo(vis[0][0] + .5 * vis[0][1], y - .1); ctx.quadraticCurveTo((vis[0][0] + vis[1][0]) / 2, y - .3, vis[1][0] - .5 * vis[1][1], y - .1); ctx.strokeStyle = o.frameCol ?? '#1A1420'; ctx.lineWidth = .11; ctx.stroke(); }
      break;
    }
    case 'shades': for (const [x, w] of ex) { if (w < .2) continue; gloss(pfRR(x - .66 * w, y - .42, 1.32 * w, .82, .3), '#15121C', { box: [x - .66 * w, y - .42, 1.32 * w, .82], lw: .08, line: L, spec: 1, rimK: .4 }); }
      { const vis = ex.filter(e => e[1] >= .2); if (vis.length === 2) { ctx.fillStyle = '#15121C'; ctx.fillRect(vis[0][0], y - .38, vis[1][0] - vis[0][0], .16); } } break;
    case 'rave': case 'vr': {
      const x0 = Math.min(...ex.map(e => e[0])) - .85, x1 = Math.max(...ex.map(e => e[0])) + .85;
      if (kind === 'vr') { gloss(pfRR(x0 - .15, y - .75, x1 - x0 + .3, 1.45, .35), '#2A2E3A', { box: [x0, y - .75, x1 - x0, 1.45], lw: .09, line: L, spec: .8 }); ctx.fillStyle = EP.laser; ctx.fillRect((x0 + x1) / 2 - .5, y + .35, 1, .12); break; }
      ctx.beginPath(); ctx.moveTo(x0, y - .1); ctx.quadraticCurveTo((x0 + x1) / 2, y - .72, x1, y - .1); ctx.lineTo(x1 - .1, y + .38); ctx.quadraticCurveTo((x0 + x1) / 2, y - .02, x0 + .1, y + .38); ctx.closePath();
      ctx.fillStyle = lg(x0, 0, x1, 0, [[0, '#12E7FF'], [.35, '#6A3BFF'], [.65, '#FF1FA3'], [1, '#FFB21F']]); ctx.fill(); ctx.strokeStyle = L; ctx.lineWidth = .09; ctx.stroke();
      ctx.fillStyle = 'rgb(255 255 255 / .7)'; ctx.beginPath(); ctx.ellipse(x0 + (x1 - x0) * .3, y - .18, .5, .09, -.12, 0, TAU); ctx.fill(); break;
    }
    case 'star': for (const [x, w] of ex) { if (w < .2) continue; ctx.save(); ctx.translate(x, y); ctx.scale(w, 1); poly(starPts(0, 0, .72, .5, 5)); ctx.restore(); ctx.fillStyle = alpha(EP.magenta, .85); ctx.fill(); ctx.strokeStyle = '#FFE0F4'; ctx.lineWidth = .1; ctx.stroke(); } break;
  }
}
function _face(o, phi, skin) {
  const L = o.line ?? EP.line, feat = a => ({ x: _HR * .92 * Math.sin(a + phi), w: Math.cos(a + phi) });
  const eyes = o.eyes ?? 'dot', ink = '#1A0F28', lk = o.look ?? [0, 0];
  const E = [-1, 1].map(sd => { const f = feat(sd * .37); return [f.x + lk[0] * .12, Math.max(0, f.w), sd]; });
  // blush
  const bl = o.blush ?? 0;
  if (bl > 0) for (const sd of [-1, 1]) { const f = feat(sd * .7); if (f.w > .1) { ctx.fillStyle = `rgb(255 90 140 / ${.4 * bl})`; ell(f.x, .72, .42 * f.w, .22); ctx.fill(); } }
  // eyes
  for (const [x, w, sd] of E) {
    if (w < .12) continue;
    ctx.save(); ctx.translate(x, .02 + lk[1] * .1); ctx.scale(w, 1);
    ctx.fillStyle = ink; ctx.strokeStyle = ink; ctx.lineCap = 'round'; ctx.lineWidth = .15;
    const k = eyes === 'wink' && sd < 0 ? 'happy' : eyes;
    switch (k) {
      case 'happy': ctx.beginPath(); ctx.arc(0, .18, .3, Math.PI * 1.12, Math.PI * 1.88); ctx.stroke(); break;
      case 'closed': case 'sleepy': ctx.beginPath(); ctx.arc(0, -.12, .3, Math.PI * .15, Math.PI * .85); ctx.stroke(); break;
      case 'cry': ctx.beginPath(); ctx.arc(0, -.12, .3, Math.PI * .15, Math.PI * .85); ctx.stroke(); ctx.fillStyle = alpha('#7FD4FF', .85); rrect(-.12, .12, .24, 1.1, .12); ctx.fill(); break;
      case 'x': ctx.beginPath(); ctx.moveTo(-.25, -.25); ctx.lineTo(.25, .25); ctx.moveTo(.25, -.25); ctx.lineTo(-.25, .25); ctx.stroke(); break;
      case 'heart': poly(heartPts(0, 0, .42, 24)); paint(EP.red, ink, .06); break;
      case 'star': poly(starPts(0, 0, .45, .45, 5)); paint(EP.yellow, ink, .06); break;
      case 'spiral': ctx.lineWidth = .07; ctx.beginPath(); for (let i = 0; i <= 26; i++) { const a = i * .55 + T * 8, r = .02 + i * .013; i ? ctx.lineTo(Math.cos(a) * r, Math.sin(a) * r) : ctx.moveTo(0, 0); } ctx.stroke(); break;
      case 'wide': ell(0, 0, .36, .46); paint('#FFFFFF', ink, .07); ell(lk[0] * .1, lk[1] * .1, .15, .19); paint(ink); break;
      default: {
        ell(0, 0, .27, .38); paint(ink);
        ctx.fillStyle = '#FFFFFF'; ell(-.08, -.15, .1, .12); ctx.fill(); ell(.1, .14, .05, .05); ctx.fill();
        if (o.lashes) { ctx.beginPath(); ctx.moveTo(sd * .22, -.3); ctx.lineTo(sd * .5, -.5); ctx.moveTo(sd * .28, -.12); ctx.lineTo(sd * .58, -.22); ctx.lineWidth = .08; ctx.stroke(); }
        if (k === 'angry' || k === 'worried') { ctx.fillStyle = skin; ctx.beginPath(); const s2 = k === 'angry' ? -sd : sd; ctx.moveTo(-.45, -.55); ctx.lineTo(.45, -.55); ctx.lineTo(.45, -.1 + s2 * .18); ctx.lineTo(-.45, -.1 - s2 * .18); ctx.fill(); }
      }
    }
    ctx.restore();
  }
  // brows
  const br = o.brows ?? (eyes === 'angry' ? 'angry' : eyes === 'worried' ? 'worried' : 'none');
  if (br !== 'none') for (const [x, w, sd] of E) {
    if (w < .15) continue; const tilt = br === 'angry' ? -sd * .35 : br === 'worried' ? sd * .32 : br === 'up' ? 0 : 0, yb = br === 'up' ? -.78 : -.6;
    ctx.save(); ctx.translate(x, yb); ctx.rotate(tilt); ctx.scale(w, 1); rrect(-.3, -.07, .6, .15, .07); ctx.fillStyle = o.browCol ?? shade(o.hairCol ?? '#3A2418', .2); ctx.fill(); ctx.restore();
  }
  // nose (a small glossy bump)
  const nf = feat(0); if (nf.w > .1 && o.nose !== false) { ctx.fillStyle = alpha(shade(skin, .25), .55); ell(nf.x + .05, .48, .16 * Math.max(.5, nf.w), .1); ctx.fill(); }
  // facial hair
  const mx = feat(0).x, mw = Math.max(.3, feat(0).w);
  if (o.stubble) { ctx.fillStyle = alpha(o.beard && o.beard !== true ? o.beard : '#3A2A22', .22); ctx.beginPath(); ctx.ellipse(mx * .9, 1.15, 1.35 * mw, .7, 0, 0, Math.PI); ctx.fill(); }
  if (o.beard) { const bc = o.beard === true ? (o.hairCol ?? THAIR.brown) : o.beard; gloss(() => { ctx.moveTo(mx - 1.9 * mw, .2); ctx.quadraticCurveTo(mx - 1.9 * mw, 2.35, mx, 2.3); ctx.quadraticCurveTo(mx + 1.9 * mw, 2.35, mx + 1.9 * mw, .2); ctx.quadraticCurveTo(mx + 1.4 * mw, 1.1, mx, .95); ctx.quadraticCurveTo(mx - 1.4 * mw, 1.1, mx - 1.9 * mw, .2); ctx.closePath(); }, bc, { box: [mx - 1.9, .2, 3.8, 2.2], lw: .07, line: L, spec: .2, rimK: .4 }); }
  if (o.mustache) { const mc = o.mustache === true ? (o.hairCol ?? THAIR.brown) : o.mustache; ctx.fillStyle = mc; ctx.beginPath(); ctx.ellipse(mx - .32 * mw, .72, .38 * mw, .15, .15, 0, TAU); ctx.ellipse(mx + .32 * mw, .72, .38 * mw, .15, -.15, 0, TAU); ctx.fill(); }
  // mouth
  const m = o.talk !== undefined ? 'sing' : (o.mouth ?? 'smile'), my = .98, lips = o.lips;
  ctx.save(); ctx.translate(mx, my); ctx.scale(mw, 1); ctx.lineCap = 'round'; ctx.strokeStyle = ink; ctx.lineWidth = .12;
  const inside = lips ? shade(lips, .45) : '#5A1428';
  switch (m) {
    case 'grin': ctx.beginPath(); ctx.moveTo(-.55, -.1); ctx.quadraticCurveTo(0, .75, .55, -.1); ctx.closePath(); paint(inside, ink, .08); ctx.fillStyle = '#FFF'; ctx.fillRect(-.42, -.08, .84, .16); break;
    case 'open': ctx.beginPath(); ctx.moveTo(-.45, -.12); ctx.quadraticCurveTo(0, .8, .45, -.12); ctx.closePath(); paint(inside, ink, .08); ctx.fillStyle = '#FF7A9A'; ell(0, .3, .22, .1); ctx.fill(); break;
    case 'O': ell(0, .12, .3, .38); paint(inside, lips ?? ink, .09); break;
    case 'o': ell(0, .05, .15, .18); paint(inside, lips ?? ink, .07); break;
    case 'scream': ctx.beginPath(); ctx.moveTo(-.5, -.15); ctx.quadraticCurveTo(0, -.3, .5, -.15); ctx.quadraticCurveTo(.45, 1.0, 0, 1.0); ctx.quadraticCurveTo(-.45, 1.0, -.5, -.15); paint(inside, ink, .08); break;
    case 'flat': ctx.beginPath(); ctx.moveTo(-.35, .05); ctx.lineTo(.35, .05); ctx.stroke(); break;
    case 'frown': ctx.beginPath(); ctx.arc(0, .45, .38, Math.PI * 1.2, Math.PI * 1.8); ctx.stroke(); break;
    case 'smirk': ctx.beginPath(); ctx.moveTo(-.35, .08); ctx.quadraticCurveTo(.1, .22, .42, -.1); ctx.stroke(); break;
    case 'wavy': ctx.beginPath(); ctx.moveTo(-.45, .05); for (let i = 1; i <= 6; i++) ctx.lineTo(-.45 + i * .15, .05 + (i % 2 ? -.08 : .08)); ctx.lineWidth = .09; ctx.stroke(); break;
    case 'cat': ctx.beginPath(); ctx.arc(-.18, 0, .18, 0, Math.PI); ctx.arc(.18, 0, .18, 0, Math.PI); ctx.lineWidth = .09; ctx.stroke(); break;
    case 'sing': { const k = clamp(o.talk ?? .6); ctx.beginPath(); ctx.ellipse(0, .08 + k * .12, .28 + k * .06, .08 + k * .32, 0, 0, TAU); paint(inside, lips ?? ink, .08); break; }
    default: ctx.beginPath(); ctx.arc(0, -.15, .42, Math.PI * .2, Math.PI * .8); ctx.stroke(); if (lips) { ctx.strokeStyle = lips; ctx.lineWidth = .08; ctx.stroke(); }
  }
  ctx.restore();
  if (o.tears) for (const [x, w] of E) if (w > .2) { ctx.fillStyle = alpha('#7FD4FF', .8 * o.tears); rrect(x - .1, .35, .2, .6 + .8 * o.tears, .1); ctx.fill(); }
  return E;
}
function _emote(kind, x, y, r, k = 1) {
  if (k <= 0) return; ctx.save(); ctx.translate(x, y); const s = backOut(clamp(k), 2.2) * r; ctx.scale(s, s);
  switch (kind) {
    case 'sweat': poly([[0, -1], [.55, .2], [0, .75], [-.55, .2]]); paint('#8FDDFF', EP.line, .1); ctx.fillStyle = '#FFF'; ell(-.15, .15, .12, .18); ctx.fill(); break;
    case 'anger': ctx.strokeStyle = EP.red; ctx.lineWidth = .22; ctx.lineCap = 'round'; for (let i = 0; i < 4; i++) { ctx.save(); ctx.rotate(i * Math.PI / 2); ctx.beginPath(); ctx.moveTo(.2, -.75); ctx.quadraticCurveTo(.2, -.2, .75, -.2); ctx.stroke(); ctx.restore(); } break;
    case 'heart': poly(heartPts(0, 0, .8, 24)); paint(EP.magenta, EP.line, .1); break;
    case 'note': ctx.fillStyle = EP.cyan; ell(-.3, .5, .35, .26, -.4); ctx.fill(); ctx.fillRect(-.02, -.8, .14, 1.35); ctx.fillRect(-.02, -.8, .6, .2); break;
    case 'excl': ptext('!', 0, 0, 2, { font: 'archivo', fill: EP.yellow, strokes: [[EP.line, .3]] }); break;
    case 'q': ptext('?', 0, 0, 2, { font: 'archivo', fill: EP.cyan, strokes: [[EP.line, .3]] }); break;
    case 'spark': for (let i = 0; i < 3; i++) { const a = -1.9 + i * .6; poly(starPts(Math.cos(a) * .8, Math.sin(a) * .8, .45, .35, 4, 0)); paint(EP.yellow); } break;
    case 'zzz': ptext('Z', 0, 0, 1.2, { fill: EP.white, strokes: [[EP.line, .2]] }); ptext('z', .8, -.8, .8, { fill: EP.white, strokes: [[EP.line, .15]] }); break;
  }
  ctx.restore();
}
// Limbs: a glossy rubber-hose tube (outline, shaded body, lit core, specular stripe) along a quadratic curve.
function _tube(p0, pc, p1, r, col, L, flat) {
  const path = () => { ctx.beginPath(); ctx.moveTo(p0[0], p0[1]); ctx.quadraticCurveTo(pc[0], pc[1], p1[0], p1[1]); };
  ctx.save(); ctx.lineCap = 'round'; ctx.lineJoin = 'round';
  if (L) { path(); ctx.strokeStyle = L; ctx.lineWidth = 2 * r + .16; ctx.stroke(); }
  path(); ctx.strokeStyle = flat ? col : shade(col, .22); ctx.lineWidth = 2 * r; ctx.stroke();
  if (!flat) {
    ctx.translate(-.05, -.06); path(); ctx.strokeStyle = col; ctx.lineWidth = 2 * r * .72; ctx.stroke();
    ctx.translate(-.05, -.07); path(); ctx.strokeStyle = 'rgb(255 255 255 / .38)'; ctx.lineWidth = r * .32; ctx.stroke();
  }
  ctx.restore();
}
// An arm from shoulder p0 to hand p1 on side sd (−1 left, 1 right): the elbow bows outward, more for short reaches (so the arm doesn't
// look like a stub) and for hands above the head (so the arm passes beside the head, not behind it).
function _arm(p0, p1, sd, r, col, L, flat) {
  const dx = p1[0] - p0[0], dy = p1[1] - p0[1], len = Math.hypot(dx, dy) || 1;
  let nx = -dy / len, ny = dx / len; if (nx * sd < 0) { nx = -nx; ny = -ny; }
  const bend = Math.min(.35 + Math.max(0, 2.4 - len) * .35 + Math.max(0, -6.2 - p1[1]) * .2, .3 + len * .45);
  _tube(p0, [p0[0] + dx / 2 + nx * 2 * bend, p0[1] + dy / 2 + ny * 2 * bend], p1, r, col, L, flat);
}
function toy(x, y, s, o = {}) {
  const sil = o.sil, silO = sil ? { line: false, rim: o.rim ?? null } : null;
  const skin = sil ?? (typeof o.skin === 'number' ? TSKIN[o.skin] : (o.skin ?? TSKIN[1]));
  const C = c => sil ?? c, O = sil ? { ...o, line: sil, rim: o.rim ?? null } : o, L = sil ?? (o.line ?? EP.line);
  const top = o.top ?? 'tee', topCol = C(o.topCol ?? '#3A6AE0'), pants = C(o.pants ?? '#262A48'), hair = o.hood ? 'none' : (o.hair ?? 'short'), hairCol = C(o.hairCol ?? THAIR.brown);
  const phi = clamp(o.turn ?? 0, -1, 1) * .95, b = bpOf(T), swing = o.swing ?? Math.sin(b * Math.PI) * .22 + (o.lean ?? 0) * 1.5;
  const oldLight = LIGHT; if (o.rim !== undefined) LIGHT = { ...LIGHT, rim: o.rim };
  const G = (pf, c, box, extra = {}) => gloss(pf, c, { box, lw: .08, line: L, rim: O.rim, spec: sil ? 0 : .6, flat: !!sil, ...extra });
  ctx.save(); ctx.translate(x, y);
  if (o.shadow !== false) { ctx.fillStyle = 'rgb(0 0 0 / .25)'; ell(0, 0, 2.7 * s / (1 + (o.jump ?? 0) * .15), .42 * s); ctx.fill(); }
  ctx.scale(s, s); ctx.translate(0, -(o.jump ?? 0) + (o.dy ?? 0)); if (o.rot) ctx.rotate(o.rot); if (o.flip) ctx.scale(-1, 1);
  // feet, and legs from the hips (in the bobbing, leaning body frame, applied by hand) down to the ankles, behind the body
  const shoes = o.shoes ?? 'sneaker', shoeCol = C(o.shoeCol ?? '#FFFFFF'), fL = o.fL ?? [0, 0], fR = o.fR ?? [0, 0];
  {
    const lean = o.lean ?? 0, sqk = o.sq ?? 0, bobY = (o.bob ?? 0) * .38, ank = shoes === 'platform' ? 1.4 : shoes === 'boot' ? 1.0 : .5;
    const hip = hx => { const px = hx * (1 + sqk * .3), py = .3 * (1 - sqk); return [px * Math.cos(lean) - py * Math.sin(lean), px * Math.sin(lean) + py * Math.cos(lean) - 2.3 + bobY]; };
    const legCol = C(o.legCol ?? (o.skirt || top === 'dress' ? skin : pants));
    for (const [sd, f] of [[-1, fL], [1, fR]]) { const a = hip(sd * .74), b = [sd * .95 + f[0] + sd * .02, f[1] - ank]; _tube(a, [(a[0] + b[0]) / 2, (a[1] + b[1]) / 2], b, .45, legCol, L, !!sil); }
  }
  _shoe(-.95 + fL[0], fL[1], -1, shoes, shoeCol, C(o.soleCol), { ...O, line: L });
  _shoe(.95 + fR[0], fR[1], 1, shoes, shoeCol, C(o.soleCol), { ...O, line: L });
  // body group (bob + lean around the hips)
  const bob = o.bob ?? 0;
  ctx.save(); ctx.translate(0, bob * .38); ctx.translate(0, -2.3); ctx.rotate(o.lean ?? 0); if (o.sq) ctx.scale(1 + o.sq * .3, 1 - o.sq); ctx.translate(0, 2.3);
  // back layers: hair back, hood back, headphone band back
  ctx.save(); ctx.translate(0, _HY); ctx.rotate(o.headTilt ?? 0);
  if (o.hood) G(pfEll(0, -.05, 2.62, 2.5), topCol, [-2.62, -2.55, 5.24, 5]);
  else _hairBack(hair, hairCol, { ...O, line: L, hairCol2: sil ? null : o.hairCol2 }, swing);
  if (o.hat === 'capBack') G(pfEll(Math.sin(phi) * -.6 - .2, -2.15, 1.7, .36, -.15), shade(C(o.hatCol ?? EP.cyan), .15), [-2, -2.5, 3.8, .8]);
  ctx.restore();
  // shoulders + torso
  const sw = top === 'suit' || top === 'leather' ? .7 : top === 'crop' ? .58 : .62;
  if (top !== 'robe' && top !== 'dress') for (const sd of [-1, 1]) glossBall(sd * 1.5, -5.7, sw, sw * .92, top === 'crop' ? C(o.topCol ?? EP.silver) : topCol, { lw: .08, line: L, rim: O.rim, spec: sil ? 0 : .5 });
  const torso = () => { ctx.moveTo(-1.05, -6.35); ctx.quadraticCurveTo(0, -6.6, 1.05, -6.35); ctx.bezierCurveTo(1.62, -6.2, 1.62, -4.9, 1.3, -3.9); ctx.bezierCurveTo(1.52, -3.2, 1.55, -2.1, .98, -1.8); ctx.quadraticCurveTo(0, -1.6, -.98, -1.8); ctx.bezierCurveTo(-1.55, -2.1, -1.52, -3.2, -1.3, -3.9); ctx.bezierCurveTo(-1.62, -4.9, -1.62, -6.2, -1.05, -6.35); ctx.closePath(); };
  const tbox = [-1.62, -6.6, 3.24, 5.0];
  if (top === 'dress' || top === 'robe') {
    const hem = top === 'robe' ? -1.1 : -1.75, fl = top === 'robe' ? 2.2 : 2.35;
    G(() => { ctx.moveTo(-1.05, -6.35); ctx.quadraticCurveTo(0, -6.6, 1.05, -6.35); ctx.bezierCurveTo(1.62, -6.2, 1.55, -4.9, 1.25, -3.9); ctx.lineTo(fl, hem); ctx.quadraticCurveTo(0, hem + .35, -fl, hem); ctx.lineTo(-1.25, -3.9); ctx.bezierCurveTo(-1.55, -4.9, -1.62, -6.2, -1.05, -6.35); ctx.closePath(); }, topCol, [-fl, -6.6, fl * 2, 6.6 + hem]);
    for (const sd of [-1, 1]) glossBall(sd * 1.45, -5.7, .6, .55, topCol, { lw: .08, line: L, rim: O.rim, spec: sil ? 0 : .5 });
    if (top === 'robe' && !sil) { ctx.fillStyle = o.trim ?? EP.gold; poly([[-.75, -6.4], [-.35, -6.4], [-.45, -2.2], [-.85, -2.2]]); ctx.fill(); poly([[.75, -6.4], [.35, -6.4], [.45, -2.2], [.85, -2.2]]); ctx.fill(); }
  } else {
    G(torso, topCol, tbox);
    if (!sil) {
      ctx.save(); ctx.beginPath(); torso(); ctx.clip();
      const waist = top === 'crop' ? -4.35 : -3.72;
      if (top === 'crop') { gloss(pfRR(-2, waist, 4, 1.1, 0), skin, { box: [-1.6, waist, 3.2, 1.1], line: false, spec: .4 }); ctx.fillStyle = alpha(shade(skin, .3), .5); ell(0, waist + .6, .07, .1); ctx.fill(); }
      const pw = top === 'crop' ? -3.35 : waist;
      if (o.skirt) gloss(pfRR(-2, pw, 4, 2, 0), o.skirt, { box: [-1.6, pw, 3.2, 1.6], line: false, spec: .9 });
      else gloss(pfRR(-2, pw, 4, 2, 0), pants, { box: [-1.6, pw, 3.2, 1.6], line: false, spec: .35 });
      ctx.beginPath(); ctx.moveTo(-1.6, pw); ctx.lineTo(1.6, pw); ctx.strokeStyle = alpha(L, .7); ctx.lineWidth = .07; ctx.stroke();
      if (!o.skirt && top !== 'crop') { ctx.beginPath(); ctx.moveTo(0, pw + .25); ctx.lineTo(0, -1.65); ctx.strokeStyle = alpha(L, .35); ctx.lineWidth = .05; ctx.stroke(); }
      // clothing details
      const trim = o.trim ?? EP.white, dk = shade(o.topCol ?? '#3A6AE0', .3);
      switch (top) {
        case 'tee': ctx.beginPath(); ctx.ellipse(0, -6.35, .85, .45, 0, 0, Math.PI); ctx.strokeStyle = dk; ctx.lineWidth = .14; ctx.stroke(); break;
        case 'hoodie': ctx.fillStyle = alpha(dk, .5); rrect(-.95, -4.3, 1.9, .9, .3); ctx.fill(); ctx.strokeStyle = trim; ctx.lineWidth = .08; ctx.beginPath(); ctx.moveTo(-.35, -6.2); ctx.lineTo(-.4, -5.1); ctx.moveTo(.35, -6.2); ctx.lineTo(.4, -5.1); ctx.stroke(); break;
        case 'sweater': ctx.fillStyle = dk; ctx.beginPath(); ctx.ellipse(0, -6.35, .9, .42, 0, 0, Math.PI); ctx.fill(); ctx.strokeStyle = alpha(dk, .6); ctx.lineWidth = .05; ctx.beginPath(); for (let i = -7; i <= 7; i++) { ctx.moveTo(i * .22, -4.05); ctx.lineTo(i * .22, -3.72); } ctx.stroke(); if (o.collar !== false) { poly([[-.55, -6.35], [0, -5.9], [.55, -6.35], [.3, -5.75], [-.3, -5.75]]); paint('#F4F4F8'); } break;
        case 'suit': case 'leather': case 'labcoat': case 'coat': {
          const shirt = top === 'labcoat' ? '#9AB8E0' : top === 'leather' ? '#2A2A30' : '#F4F4F8';
          poly([[-.62, -6.4], [.62, -6.4], [.3, -4.5], [0, -4.1], [-.3, -4.5]]); paint(shirt);
          if (top === 'suit' && o.tie !== false) { const tb = o.longTie ? -2.55 : -4.35; poly([[-.2, -6.15], [.2, -6.15], [.34, tb - .45], [0, tb], [-.34, tb - .45]]); paint(o.tie ?? EP.red, alpha(L, .7), .05); if (o.longTie) { poly([[-.24, -6.2], [.24, -6.2], [.17, -5.8], [-.17, -5.8]]); paint(shade(o.tie ?? EP.red, .2), alpha(L, .7), .05); } }
          for (const sd of [-1, 1]) { poly([[sd * .62, -6.42], [sd * 1.2, -6.2], [sd * .55, -5.0], [sd * .12, -4.25]]); paint(top === 'leather' ? '#26262C' : shade(o.topCol ?? '#3A6AE0', .15), alpha(L, .6), .05); }
          if (o.pin) { ctx.save(); ctx.translate(-.95, -5.55); ctx.rotate(-.35); rrect(-.2, -.14, .4, .28, .04); paint('#FFFFFF', alpha(L, .7), .03); for (let i = 0; i < 3; i++) { ctx.fillStyle = EP.red; ctx.fillRect(-.2, -.1 + i * .09, .4, .045); } ctx.fillStyle = '#1C3A8A'; ctx.fillRect(-.2, -.14, .17, .13); ctx.restore(); }
          if (top === 'leather') { ctx.strokeStyle = '#B8BCC8'; ctx.lineWidth = .07; ctx.beginPath(); ctx.moveTo(.1, -4.3); ctx.lineTo(.2, -2.4); ctx.stroke(); }
          if (top === 'labcoat') { ctx.fillStyle = '#E4E8F0'; rrect(.55, -5.2, .65, .75, .1); ctx.fill(); for (const [px, pc] of [[.68, EP.blue], [.85, EP.red]]) { ctx.fillStyle = pc; ctx.fillRect(px, -5.55, .1, .5); } }
          break;
        }
        case 'shirt': case 'turtleneck': if (top === 'turtleneck') { gloss(pfRR(-.9, -6.7, 1.8, .7, .3), o.topCol ?? '#222', { box: [-.9, -6.7, 1.8, .7], lw: .06, line: L }); break; }
          poly([[-.7, -6.45], [0, -5.9], [-.35, -5.6]]); paint('#F4F4F8', alpha(L, .6), .05); poly([[.7, -6.45], [0, -5.9], [.35, -5.6]]); paint('#F4F4F8', alpha(L, .6), .05);
          ctx.fillStyle = alpha(L, .5); for (let i = 0; i < 4; i++) { ell(0, -5.5 + i * .5, .07, .07); ctx.fill(); } break;
        case 'layers': [[o.trim ?? '#C8C0A8', 1.05], ['#5A7A9A', .82], ['#E8E4DA', .6]].forEach(([c, w]) => { poly([[-w, -6.45], [0, -5.2 + (1.05 - w) * .6], [w, -6.45], [w * .6, -6.5], [0, -5.6 + (1.05 - w) * .6], [-w * .6, -6.5]]); paint(c, alpha(L, .6), .05); }); break;
        case 'track': ctx.fillStyle = trim; for (const sd of [-1, 1]) { poly([[sd * 1.28, -6.3], [sd * 1.43, -6.3], [sd * 1.55, -3.8], [sd * 1.38, -3.8]]); ctx.fill(); poly([[sd * 1.02, -6.4], [sd * 1.15, -6.4], [sd * 1.28, -3.8], [sd * 1.14, -3.8]]); ctx.fill(); }
          poly([[-.75, -6.5], [0, -6.0], [.75, -6.5], [.8, -6.15], [0, -5.55], [-.8, -6.15]]); paint(trim, alpha(L, .6), .05); ctx.strokeStyle = '#D8DCE8'; ctx.lineWidth = .08; ctx.beginPath(); ctx.moveTo(0, -5.55); ctx.lineTo(0, -3.75); ctx.stroke(); break;
        case 'crop': ctx.strokeStyle = 'rgb(255 255 255 / .55)'; ctx.lineWidth = .1; ctx.beginPath(); ctx.moveTo(-1.2, -5.6); ctx.quadraticCurveTo(0, -5.1, 1.2, -5.6); ctx.stroke(); poly([[-.9, -6.5], [0, -5.9], [.9, -6.5], [.95, -6.1], [0, -5.5], [-.95, -6.1]]); paint(o.trim ?? EP.magenta, alpha(L, .6), .05); break;
        case 'vest': ctx.fillStyle = alpha('#F4F4F8', .95); poly([[-.5, -6.45], [.5, -6.45], [.4, -3.8], [-.4, -3.8]]); ctx.fill(); ctx.strokeStyle = alpha(dk, .6); ctx.lineWidth = .06; ctx.beginPath(); for (let i = 0; i < 4; i++) { ctx.moveTo(-1.6, -5.6 + i * .5); ctx.lineTo(-.5, -5.6 + i * .5); ctx.moveTo(.5, -5.6 + i * .5); ctx.lineTo(1.6, -5.6 + i * .5); } ctx.stroke(); break;
        case 'jersey': ptext(o.number ?? '1', 0, -4.85, 1.35, { font: 'archivo', fill: trim, strokes: [[dk, .18]] }); break;
      }
      if (o.print) ptext(o.print, 0, -4.9, o.printSize ?? .75, { font: 'archivo', fill: o.printCol ?? EP.white, maxW: 2.4, strokes: [[alpha(L, .5), .12]] });
      ctx.restore();
    }
  }
  if (o.chain && !sil) { ctx.strokeStyle = o.chain; ctx.lineWidth = .14; ctx.setLineDash([.14, .08]); ctx.beginPath(); ctx.moveTo(-.9, -6.25); ctx.quadraticCurveTo(0, -4.4, .9, -6.25); ctx.stroke(); ctx.setLineDash([]); glossBall(0, -5.05, .34, .34, o.chain, { lw: .05, line: L }); if (o.pendant) ptext(o.pendant, 0, -5.07, .42, { font: 'archivo', fill: shade(o.chain, .5) }); }
  // arms: in front of the torso (so hands across the body stay attached) and behind the head; long sleeves in the top's colour, short ones
  // in skin, then the shoulder caps again over the arm roots
  let hL = o.hL ?? [-2.35, -3.5], hR = o.hR ?? [2.35, -3.5], gL = o.gL ?? 'open', gR = o.gR ?? 'open';
  if (o.mic === 'R') { hR = o.hR ?? [1.1, -6.25]; gR = 'mic'; } if (o.mic === 'L') { hL = o.hL ?? [-1.1, -6.25]; gL = 'mic'; }
  {
    const capCol = top === 'crop' ? C(o.topCol ?? EP.silver) : topCol, armCol = C(o.armCol ?? (['tee', 'vest', 'jersey', 'dress'].includes(top) ? skin : capCol));
    for (const [h, sd] of [[hL, -1], [hR, 1]]) _arm([sd * 1.45, -5.75], h, sd, .33, armCol, L, !!sil);
    const cw = top === 'robe' || top === 'dress' ? .6 : sw;
    for (const sd of [-1, 1]) glossBall(sd * 1.5, -5.7, cw * .8, cw * .74, capCol, { lw: .08, line: L, rim: O.rim, spec: sil ? 0 : .5 });
  }
  // head
  ctx.save(); ctx.translate(0, _HY + (o.nod ?? 0) * .15); ctx.rotate(o.headTilt ?? 0);
  const earA = [-1, 1].map(sd => sd * Math.PI / 2 + phi);
  const ear = sd => { const a = sd * Math.PI / 2 + phi, ex = _HR * .98 * Math.sin(a); glossBall(ex, .15, .42 * Math.max(.45, Math.abs(Math.sin(a))), .52, skin, { lw: .07, line: L, spec: .3, flat: !!sil }); };
  if (!o.hood) [-1, 1].forEach((sd, i) => { if (Math.cos(earA[i]) < .25) ear(sd); });
  glossBall(0, 0, _HR, _HRY, skin, { lw: .085, line: L, spec: sil ? 0 : .45, rim: O.rim, hi: .32, lo: .38 });
  if (!sil) {
    if (!o.hood) [-1, 1].forEach((sd, i) => { if (Math.cos(earA[i]) >= .25) ear(sd); });
    const E = _face(o, phi, skin);
    const EX = E.map(([x, w]) => [x, w]);
    if (o.glasses) _glasses(o.glasses, o, EX);
    if (o.earrings) for (const sd of [-1, 1]) { const a = sd * Math.PI / 2 + phi; if (Math.cos(a) < -.3) continue; const ex = _HR * Math.sin(a); if (o.earrings === 'hoop') { ctx.strokeStyle = EP.gold; ctx.lineWidth = .1; ell(ex, 1.0, .3, .38); ctx.stroke(); } else { poly(starPts(ex, 1.05, .34, .45, 5)); paint(EP.gold, L, .05); } }
  }
  if (o.hood) { const hc = topCol; gloss(() => { ctx.moveTo(2.62, -.05); ctx.ellipse(0, -.05, 2.62, 2.5, 0, 0, TAU); ctx.moveTo(1.7 + Math.sin(phi) * .6, .4); ctx.ellipse(Math.sin(phi) * .6, .45, 1.72, 1.95, 0, 0, TAU, true); }, hc, { box: [-2.62, -2.55, 5.24, 5], lw: .08, line: L, rim: O.rim, spec: sil ? 0 : .4 }); }
  _hairFront(hair, hairCol, { ...O, line: L, hairCol2: sil ? null : o.hairCol2 }, phi);
  if (o.clip === 'star' && !sil) { poly(starPts(-1.55 + Math.sin(phi), -1.45, .42, .45, 5, -.3)); paint(EP.yellow, L, .06); }
  if (o.hat) _hat(o.hat, C(o.hatCol ?? (o.hat === 'visor' ? '#1FA85A' : EP.cyan)), { ...O, line: L, hatCol2: sil ?? o.hatCol2 }, phi);
  if (o.phones) { ctx.strokeStyle = '#2A2A34'; ctx.lineWidth = .32; ctx.beginPath(); ctx.ellipse(0, -.3, 2.35, 2.45, 0, Math.PI * 1.05, Math.PI * 1.95); ctx.stroke(); for (const sd of [-1, 1]) { const a = sd * Math.PI / 2 + phi; if (Math.cos(a) < -.35) continue; gloss(pfRR(_HR * Math.sin(a) - .42, -.6, .84, 1.35, .35), sil ?? '#2A2A34', { box: [-.4, -.6, .8, 1.35], lw: .07, line: L }); if (!sil) { ctx.fillStyle = o.phonesCol ?? EP.magenta; rrect(_HR * Math.sin(a) - .12 * sd - .12, -.35, .24, .85, .1); ctx.fill(); } } }
  if (o.headset && !sil) { const a = Math.PI / 2 + phi; if (Math.cos(a) > -.5) { const ex = _HR * Math.sin(a); ctx.strokeStyle = '#2A2A34'; ctx.lineWidth = .09; ctx.beginPath(); ctx.moveTo(ex - .05, .2); ctx.quadraticCurveTo(ex - .2, 1.2, feat0(phi) + .55, 1.05); ctx.stroke(); glossBall(feat0(phi) + .55, 1.05, .16, .16, '#26222E', { lw: .04 }); } }
  ctx.restore();
  if (o.emote) _emote(o.emote, 2.3, _HY - 2.3, .85, o.emoteK ?? 1);
  if (o.sweat && !sil) _emote('sweat', 2.2, _HY - 1.2, .45 * o.sweat, 1);
  // hands (in the leaned body frame)
  const hcol = C(o.gloves ?? o.mittens ?? skin), handO = { line: L, rim: O.rim, cuff: o.gloves && !sil ? (o.cuff ?? shade(o.gloves, .15)) : null, mitten: !!o.mittens && !sil };
  const mouth = [feat0(phi), _HY + .98];
  for (const [h, g, sd, hold] of [[hL, gL, -1, o.holdL], [hR, gR, 1, o.hold]]) {
    const ang = Math.atan2(h[1] - -5.7, h[0] - sd * 1.45);
    if (g === 'mic' && !sil) _mic(h[0], h[1], mouth[0] + sd * .15, mouth[1] - .05, o);
    _toyHand(h[0], h[1], g, ang, sd, hcol, handO);
    if (hold) { ctx.save(); ctx.translate(h[0], h[1]); ctx.scale(1 / s, 1 / s); hold(s); ctx.restore(); }
  }
  ctx.restore(); // body group
  ctx.restore();
  LIGHT = oldLight;
  if (o.tag) nameTip(o.tag, x, y - (10.9 + (o.jump ?? 0)) * s - (o.tagDy ?? 0) - 30, { pop: o.tagPop ?? 1, size: o.tagSize ?? 30, to: [x, y - 10.4 * s] });
}
const feat0 = phi => _HR * .92 * Math.sin(phi);

// Dance moves as a function of beat position b (= bpOf(t) − an offset per dancer). Returns toy() pose options; spread and override:
//   toy(x, y, s, { ...CAST.token.o, ...dance('rap', bpOf(t)) }). Moves: bounce, raise (hands in the air), pump (fist pump), runningMan,
//   point (disco point), clap, wave (arms overhead, side to side), rap (mic in R, chopping L hand, nod), sing (diva: reach out, hand on
//   heart, sway), vogue (angular face frames, every 2 beats), robot (snaps each beat), shuffle, jump, shrug, spin (turntable turn), idle.
function dance(name, b, o = {}) {
  const ph = frac(b), p = Math.exp(-ph * 5), sn = Math.sin(b * Math.PI), e = o.k ?? 1, bob = p * .8 * e;
  switch (name) {
    case 'raise': return { hL: [-1.8 + sn * .45, -11.1 + Math.abs(sn) * .3], hR: [1.8 + sn * .45, -11.1 + Math.abs(Math.cos(b * Math.PI)) * .3], gL: 'wave', gR: 'wave', bob, jump: frac(b / 2) < .5 ? Math.sin(frac(b) * Math.PI) * .45 * e : 0, lean: sn * .04 };
    case 'pump': return { hR: [2.1, lerp(-11.7, -8.4, ease(ph < .5 ? ph * 2 : 1 - (ph - .5) * 2))], gR: 'fist', hL: [-1.95, -3.9], gL: 'fist', bob, headTilt: -p * .08, lean: -.03 };
    case 'runningMan': { const s2 = Math.sin(b * Math.PI); return { fL: [s2 * .55, -Math.max(0, s2) * .6], fR: [-s2 * .55, -Math.max(0, -s2) * .6], hL: [-1.6, -5.4 + s2 * .9], hR: [1.6, -5.4 - s2 * .9], gL: 'fist', gR: 'fist', bob: Math.abs(s2) * .6, lean: .06 }; }
    case 'point': { const up = frac(b / 2) < .5; return { hR: up ? [2.9, -11.2] : [-1.7, -2.6], gR: 'point', hL: [-1.95, -3.9], gL: 'fist', bob, lean: up ? -.08 : .1, fR: [up ? .3 : -.2, 0] }; }
    case 'clap': { const d = .42 + 1.5 * (1 - Math.exp(-ph * 7)) * (ph < .6 ? 1 : 1 - (ph - .6) / .4 * .8); return { hL: [-d, -6.1], hR: [d, -6.1], gL: 'open', gR: 'open', bob }; }
    case 'wave': { const w = Math.sin(b * Math.PI / 2); return { hL: [-1.5 + w * 1.3, -11.0], hR: [1.5 + w * 1.3, -11.0], gL: 'wave', gR: 'wave', lean: w * .09, bob: bob * .6 }; }
    case 'rap': { const chop = p, alt = Math.floor(b) % 2; return { mic: 'R', hL: [-2.5 + chop * .5, lerp(-7.1, -5.6, chop)], gL: alt ? 'point' : 'open', bob, nod: p, headTilt: -p * .06, lean: .04 * sn }; }
    case 'sing': { const w = Math.sin(b * Math.PI / 4); return { hR: [2.8 + w * .3, -7.2 - w * .6], gR: 'flat', hL: [-.55, -5.5], gL: 'open', lean: w * .06, bob: bob * .4, headTilt: -.05 - w * .05 }; }
    case 'vogue': { const P = [[[-1.8, -9.6], [1.8, -9.6]], [[-2.8, -8.6], [.9, -10.9]], [[-1.95, -3.9], [2.2, -9.4]], [[-.9, -10.9], [2.9, -8.2]]][Math.floor(b / 2) % 4]; return { hL: P[0], hR: P[1], gL: 'flat', gR: 'flat', lean: [0, -.1, .08, .12][Math.floor(b / 2) % 4], headTilt: [.1, -.15, .12, -.1][Math.floor(b / 2) % 4] }; }
    case 'robot': { const P = [[[-2.9, -6.0], [2.3, -3.4]], [[-2.3, -3.4], [2.9, -6.0]], [[-2.6, -8.8], [2.6, -8.8]], [[-2.9, -6.0], [2.9, -6.0]]][((Math.floor(b) % 4) + 4) % 4]; return { hL: P[0], hR: P[1], gL: 'flat', gR: 'flat', turn: [.3, -.3, 0, 0][((Math.floor(b) % 4) + 4) % 4] }; }
    case 'shuffle': { const s8 = Math.sin(b * Math.PI * 2); return { fL: [s8 * .4, -Math.max(0, s8) * .35], fR: [-s8 * .4, -Math.max(0, -s8) * .35], hL: [-2.3, -4.8 + s8 * .4], hR: [2.3, -4.8 - s8 * .4], gL: 'fist', gR: 'fist', bob: .3 + p * .4 }; }
    case 'jump': return { jump: Math.sin(ph * Math.PI) * 1.1 * e, hL: [-2.1, -10.6], hR: [2.1, -10.6], gL: 'wave', gR: 'wave', bob: ph < .15 ? .8 : 0 };
    case 'shrug': return { hL: [-2.9, -5.6], hR: [2.9, -5.6], gL: 'flat', gR: 'flat', headTilt: .15, bob: p * .3, mouth: 'flat', brows: 'up' };
    case 'spin': return { turn: Math.sin(b * Math.PI / 2), hL: [-2.6, -6.2], hR: [2.6, -6.2], gL: 'open', gR: 'open', bob };
    case 'idle': return { hL: [-2.35, -3.5 - Math.sin(b * Math.PI / 2) * .1], hR: [2.35, -3.5 + Math.sin(b * Math.PI / 2) * .1], bob: p * .25 };
    default: return { hL: [-2.35 + sn * .2, -3.6 - p * .3], hR: [2.35 + sn * .2, -3.6 - p * .3], bob };
  }
}
// Singing mouth: 0..1 openness that chatters on the eighth notes while a line is sung (use as { talk: singK(t) }).
const singK = (t, ph = 0) => { const ln = lineAt(t); if (!ln || t > ln.end) return undefined; return clamp(.25 + .75 * Math.abs(Math.sin((bpOf(t) * 2 + ph) * Math.PI)) * (.6 + .4 * Math.sin(t * 13 + ph))); };

// The performers. CAST.token.o / CAST.softmax.o are toy() options; add a dance() and a face.
const CAST = {
  token: { name: 'MC TOKEN', col: EP.cyan, o: { skin: 3, hair: 'buzz', hairCol: THAIR.black, hat: 'capBack', hatCol: EP.cyan, hatCol2: EP.white, glasses: 'rave', top: 'track', topCol: EP.ultra, trim: EP.white, pants: '#1A1C3A', shoeCol: '#FFFFFF', shoeTrim: EP.cyan, chain: EP.gold, pendant: 'T' } },
  softmax: { name: 'SOFTMAX', col: EP.magenta, o: { skin: 0, hair: 'ponytail', hairCol: '#FF3FAE', hairCol2: '#FFD6F2', clip: 'star', top: 'crop', topCol: '#D8DEEA', trim: EP.cyan, skirt: '#7A2BFF', shoes: 'platform', shoeCol: '#F4F4FA', soleCol: EP.cyan, lashes: true, lips: EP.rose, headset: true, earrings: 'star', gloves: '#F4F4FA', cuff: EP.magenta } },
};
// Recurring real people as toy() presets: a costume cue plus a name (pass tag: WHO.sam.name, or draw nameTip()). Affectionate, never mean.
// Presidents too: they appear as recognizable, good-natured caricatures like everyone else.
const WHO = {
  vaswani: { name: '8 GOOGLE RESEARCHERS', o: { hair: 'short', hairCol: THAIR.black, top: 'labcoat', topCol: '#F4F6FA', skin: 2 } },
  jared: { name: 'JARED KAPLAN', o: { hair: 'short', hairCol: THAIR.brown, top: 'shirt', topCol: '#4A6AA8', skin: 0 } },
  gwern: { name: 'GWERN', o: { top: 'hoodie', topCol: '#3A3A56', hood: true, glasses: 'shades', skin: 0 } },
  kevin: { name: 'KEVIN ROOSE', o: { hair: 'short', hairCol: THAIR.dkbrown, top: 'shirt', topCol: '#6F9AD8', skin: 0 } },
  eliezer: { name: 'ELIEZER YUDKOWSKY', o: { hat: 'fedora', hatCol: '#2E2A36', hair: 'short', hairCol: THAIR.brown, beard: THAIR.brown, top: 'tee', topCol: '#5A6A48', skin: 0 } },
  sam: { name: 'SAM ALTMAN', o: { hair: 'side', hairCol: '#6A4A2E', top: 'sweater', topCol: '#8A92A6', collar: false, skin: 0 } },
  ilya: { name: 'ILYA SUTSKEVER', o: { hair: 'balding', hairCol: THAIR.dkbrown, top: 'shirt', topCol: '#2E3040', skin: 0 } },
  gavin: { name: 'GAVIN NEWSOM', o: { hair: 'slick', hairCol: '#4A3A2E', top: 'suit', topCol: '#1E2A48', tie: EP.blue, skin: 1 } },
  hinton: { name: 'GEOFFREY HINTON', o: { hair: 'swoop', hairCol: THAIR.white, top: 'sweater', topCol: '#5A6078', skin: 0 } },
  demis: { name: 'DEMIS HASSABIS', o: { hair: 'short', hairCol: THAIR.black, top: 'suit', topCol: '#20263A', tie: false, skin: 2 } },
  karpathy: { name: 'ANDREJ KARPATHY', o: { hair: 'short', hairCol: THAIR.black, top: 'tee', topCol: '#2A2A34', phones: true, skin: 0 } },
  zuck: { name: 'MARK ZUCKERBERG', o: { hair: 'curly', hairCol: THAIR.brown, top: 'tee', topCol: '#9AA0AE', chain: EP.gold, skin: 0 } },
  elon: { name: 'ELON MUSK', o: { hair: 'short', hairCol: THAIR.dkbrown, top: 'tee', topCol: '#1C1C24', pants: '#1C1C24', skin: 0 } },
  masa: { name: 'MASAYOSHI SON', o: { hair: 'bald', top: 'suit', topCol: '#2A2E3A', tie: EP.silver, skin: 1 } },
  larry: { name: 'LARRY ELLISON', o: { hair: 'short', hairCol: THAIR.white, top: 'suit', topCol: '#16181E', tie: false, skin: 0 } },
  yann: { name: 'YANN LECUN', o: { hair: 'short', hairCol: THAIR.grey, glasses: 'square', top: 'suit', topCol: '#1E222C', tie: false, skin: 0 } },
  noam: { name: 'NOAM BROWN', o: { hat: 'visor', hatCol: '#1FA85A', hair: 'short', hairCol: THAIR.brown, top: 'vest', topCol: '#262A38', skin: 0 } },
  jeff: { name: 'JEFF DEAN', o: { hair: 'buzz', hairCol: THAIR.grey, glasses: 'square', top: 'shirt', topCol: '#3A6A5A', skin: 0 } },
  lutnick: { name: 'HOWARD LUTNICK', o: { hair: 'balding', hairCol: THAIR.grey, glasses: 'round', top: 'suit', topCol: '#1C2440', tie: EP.red, skin: 0 } },
  jensen: { name: 'JENSEN HUANG', o: { hair: 'swoop', hairCol: '#C8C6CC', top: 'leather', topCol: '#18181E', pants: '#18181E', skin: 1 } },
  greg: { name: 'GREG BROCKMAN', o: { hair: 'short', hairCol: THAIR.brown, top: 'tee', topCol: '#3A5A8A', skin: 0 } },
  dario: { name: 'DARIO AMODEI', o: { hair: 'curly', hairCol: THAIR.dkbrown, glasses: 'round', top: 'sweater', topCol: '#3A5A9A', skin: 0 } },
  bernie: { name: 'BERNIE SANDERS', o: { hair: 'messy', hairCol: THAIR.white, glasses: 'round', top: 'coat', topCol: '#6A5A48', mittens: '#C8A878', skin: 0 } },
  bannon: { name: 'STEVE BANNON', o: { hair: 'messy', hairCol: THAIR.grey, top: 'layers', topCol: '#3A3228', stubble: true, skin: 5 } },
  trump: { name: 'DONALD TRUMP', o: { hair: 'swirl', hairCol: '#F5C242', hairCol2: '#FFF2B0', top: 'suit', topCol: '#1A2138', pants: '#1A2138', tie: '#E0182A', longTie: true, pin: true, shoes: 'dress', shoeCol: '#16141C', skin: '#F6AE78' } },
};

// =====================================================================================================
// DJ CLAWD — djClawd(x, y, u, o): Clawd as glossy CGI plastic. (x, y) = ground between the feet; body 10u × 6u, ≈ 8u tall (10u with headphones).
// o: col, phones (default true: chrome DJ headphones), phonesCol, shades (wraparound rave shades), hat (cap|crown|party|halo), eyes (normal|
// happy|closed|wide|x|heart|star|shades), look ([x, y]), blink (0..1), mouth (none|smile|open|O|grin), talk (0..1), blush, sweat, aL / aR (nub
// angles: 0 = out sideways, + raised, −1.2 hanging), hold / holdL (fn(u) at the nub tip, in px), legs (false), walk, jump (u), dy, rot, flip, sq,
// label (text on his body, e.g. '5.5'), rim.
// =====================================================================================================
function djClawd(x, y, u, o = {}) {
  const col = o.col ?? EP.clawd, dk = shade(col, .28), L = o.line ?? EP.line;
  const oldLight = LIGHT; if (o.rim !== undefined) LIGHT = { ...LIGHT, rim: o.rim };
  ctx.save(); ctx.translate(x, y);
  if (o.shadow !== false && o.legs !== false) { ctx.fillStyle = 'rgb(0 0 0 / .25)'; ell(0, 0, 6 * u, .85 * u); ctx.fill(); }
  ctx.scale(u, u); ctx.translate(0, (o.dy ?? 0) - (o.jump ?? 0)); if (o.rot) ctx.rotate(o.rot); if (o.flip) ctx.scale(-1, 1); if (o.sq) ctx.scale(1 + o.sq * .5, 1 - o.sq);
  if (o.legs !== false) [-3.6, -1.4, 1.4, 3.6].forEach((lx, i) => { const lift = o.walk !== undefined ? Math.max(0, Math.sin(o.walk * TAU + (i % 2) * Math.PI)) * .9 : 0; gloss(pfRR(lx - .58, -2.4 - lift, 1.16, 2.4, .3), dk, { box: [lx - .58, -2.4, 1.16, 2.4], lw: .14, line: L, spec: .3 }); });
  const arm = (sd, a, hold) => {
    ctx.save(); ctx.translate(sd * 4.85, -4.9); ctx.rotate(-sd * a);
    gloss(pfRR(sd > 0 ? -.3 : -2.2, -.62, 2.5, 1.24, .5), col, { box: [-2.2, -.62, 4.7, 1.24], lw: .14, line: L, spec: .4 });
    if (hold) { ctx.save(); ctx.translate(sd * 2.0, 0); ctx.rotate(sd * a); ctx.scale(1 / u, 1 / u); hold(u); ctx.restore(); }
    ctx.restore();
  };
  arm(-1, o.aL ?? -.25, o.holdL); arm(1, o.aR ?? -.25, o.hold);
  gloss(pfRR(-5, -8.1, 10, 6, .7), col, { box: [-5, -8.1, 10, 6], lw: .16, line: L, spec: .55, hi: .3 });
  ctx.fillStyle = 'rgb(255 255 255 / .22)'; rrect(-4.4, -7.85, 8.8, .45, .22); ctx.fill();
  if (o.label) { ctx.save(); ctx.translate(2.9, -3.6); ctx.rotate(-.12); gloss(pfEll(0, 0, 1.15, .8), EP.yellow, { box: [-1.15, -.8, 2.3, 1.6], lw: .1, line: L }); ptext(o.label, 0, 0, .8, { font: 'archivo', fill: EP.line, maxW: 1.8 }); ctx.restore(); }
  // face
  const eyes = o.shades ? 'shades' : (o.eyes ?? 'normal'), lk = o.look ?? [0, 0], ey = -6.2;
  for (const sd of [-1, 1]) {
    ctx.save(); ctx.translate(sd * 2.3 + lk[0] * .5, ey + lk[1] * .4); ctx.fillStyle = '#1A0F28'; ctx.strokeStyle = '#1A0F28'; ctx.lineCap = 'round'; ctx.lineWidth = .42;
    switch (eyes) {
      case 'happy': ctx.beginPath(); ctx.arc(0, .45, .72, Math.PI * 1.1, Math.PI * 1.9); ctx.stroke(); break;
      case 'closed': ctx.beginPath(); ctx.moveTo(-.7, 0); ctx.lineTo(.7, 0); ctx.stroke(); break;
      case 'x': ctx.beginPath(); ctx.moveTo(-.6, -.6); ctx.lineTo(.6, .6); ctx.moveTo(.6, -.6); ctx.lineTo(-.6, .6); ctx.stroke(); break;
      case 'heart': poly(heartPts(0, 0, 1.0, 24)); paint(EP.magenta, L, .12); break;
      case 'star': poly(starPts(0, 0, 1.1, .45, 5)); paint(EP.yellow, L, .12); break;
      case 'wide': ell(0, 0, .85, 1.0); paint('#FFFFFF', L, .14); ell(lk[0] * .3, lk[1] * .3, .38, .48); paint('#1A0F28'); break;
      case 'shades': break;
      default: { const bl = o.blink ?? 0; rrect(-.48, -.85 + bl * .75, .96, 1.7 * (1 - bl * .85), .3); ctx.fill(); if (bl < .5) { ctx.fillStyle = '#FFFFFF'; ell(-.16, -.42, .17, .22); ctx.fill(); } }
    }
    ctx.restore();
  }
  if (eyes === 'shades') { ctx.beginPath(); ctx.moveTo(-4.2, ey - .5); ctx.quadraticCurveTo(0, ey - 1.6, 4.2, ey - .5); ctx.lineTo(3.9, ey + .95); ctx.quadraticCurveTo(0, ey + .2, -3.9, ey + .95); ctx.closePath(); ctx.fillStyle = lg(-4, 0, 4, 0, [[0, '#12E7FF'], [.35, '#6A3BFF'], [.65, '#FF1FA3'], [1, '#FFB21F']]); ctx.fill(); ctx.strokeStyle = L; ctx.lineWidth = .16; ctx.stroke(); ctx.fillStyle = 'rgb(255 255 255 / .7)'; ell(-1.8, ey - .45, 1.2, .16, -.1); ctx.fill(); }
  if (o.blush) { ctx.fillStyle = `rgb(255 90 140 / ${.45 * (o.blush === true ? 1 : o.blush)})`; ell(-3.7, -4.95, .9, .42); ctx.fill(); ell(3.7, -4.95, .9, .42); ctx.fill(); }
  const my = -5.1, m = o.talk !== undefined ? 'talk' : (o.mouth ?? 'none');
  ctx.strokeStyle = '#1A0F28'; ctx.lineWidth = .32; ctx.lineCap = 'round';
  if (m === 'talk') { const k = clamp(o.talk); rrect(-.75, my - .25, 1.5, .35 + k * .9, .3); paint('#5A1428', '#1A0F28', .14); }
  else if (m === 'smile') { ctx.beginPath(); ctx.arc(0, my - .85, 1.1, .25 * Math.PI, .75 * Math.PI); ctx.stroke(); }
  else if (m === 'grin' || m === 'open') { ctx.beginPath(); ctx.moveTo(-1.3, my - .35); ctx.quadraticCurveTo(0, my + (m === 'open' ? 1.5 : 1.1), 1.3, my - .35); ctx.closePath(); paint('#5A1428', '#1A0F28', .14); }
  else if (m === 'O') { ell(0, my + .1, .8, 1.0); paint('#5A1428', '#1A0F28', .14); }
  else if (m === 'o') { ell(0, my, .45, .55); paint('#5A1428', '#1A0F28', .12); }
  if (o.phones !== false) {
    ctx.beginPath(); ctx.moveTo(-5.15, -6.8); ctx.bezierCurveTo(-5.2, -11.2, 5.2, -11.2, 5.15, -6.8);
    ctx.strokeStyle = L; ctx.lineWidth = .9; ctx.stroke(); ctx.strokeStyle = lg(0, -10, 0, -7, [[0, '#FFFFFF'], [.5, '#9AA2B8'], [1, '#4A5064']]); ctx.lineWidth = .6; ctx.stroke();
    for (const sd of [-1, 1]) { gloss(pfRR(sd * 5.35 - .8, -7.9, 1.6, 2.7, .7), '#2A2A36', { box: [sd * 5.35 - .8, -7.9, 1.6, 2.7], lw: .14, line: L, spec: .8 }); ctx.fillStyle = o.phonesCol ?? EP.magenta; rrect(sd * 5.35 - sd * .5 - .18, -7.4, .36, 1.7, .15); ctx.fill(); }
  }
  if (o.hat === 'cap') { gloss(() => { ctx.moveTo(-3.6, -8.0); ctx.bezierCurveTo(-3.6, -10.6, 3.6, -10.6, 3.6, -8.0); ctx.closePath(); }, o.hatCol ?? EP.cyan, { box: [-3.6, -10, 7.2, 2], lw: .14, line: L }); gloss(pfEll(-4.2, -8.1, 2.3, .45, .08), shade(o.hatCol ?? EP.cyan, .15), { box: [-6.5, -8.6, 4.6, 1], lw: .12, line: L }); }
  if (o.hat === 'crown') { gloss(pfPts([[-2.2, -8.05], [-2.5, -10.4], [-1.1, -9.2], [0, -10.9], [1.1, -9.2], [2.5, -10.4], [2.2, -8.05]]), EP.gold, { box: [-2.5, -10.9, 5, 2.9], lw: .14, line: L }); }
  if (o.hat === 'party') { gloss(pfPts([[-1.4, -8.05], [.4, -12.2], [1.6, -8.05]]), o.hatCol ?? EP.magenta, { box: [-1.4, -12.2, 3, 4.2], lw: .14, line: L }); glossBall(.4, -12.3, .5, .5, EP.yellow, { lw: .1 }); }
  if (o.hat === 'halo') { ctx.save(); ctx.globalCompositeOperation = 'lighter'; ctx.strokeStyle = alpha(EP.gold, .9); ctx.lineWidth = .4; ell(0, -10.3, 3, .7); ctx.stroke(); ctx.restore(); }
  if (o.sweat) _emote('sweat', 5.6, -9.2, .8, 1);
  ctx.restore();
  LIGHT = oldLight;
}

// =====================================================================================================
// AI MODELS are translucent candy-plastic late-90s computers with a face on the CRT and floating white cartoon gloves.
// gumdrop(x, y, s, o): (x, y) ground; ≈ 9s tall, 7.4s wide. o: col (CANDY.*), label (model name on the front), screen (glass colour),
//   glowCol (face colour), face (dot|happy|heart|star|x|angry|wide|spiral|closed|sly|sad|cry|wink|think|sleepy|dizzy), mouth (smile|open|O|flat|
//   wavy|grin|none), talk (0..1), text (screen text instead of a face; \n for lines), textSize, hL / hR ([x, y] glove centres in s, rest ≈ [∓4.3, −3.6]),
//   gL / gR (toy hand gestures), hold / holdL, hands (false), jump, dy, rot, flip, sq, glitch (0..1 red bars), blush, sweat, rim, headband (colour).
// =====================================================================================================
function gumdrop(x, y, s, o = {}) {
  const col = o.col ?? CANDY.bondi, L = o.line ?? EP.line, gc = o.glowCol ?? '#AFFFF0';
  const oldLight = LIGHT; if (o.rim !== undefined) LIGHT = { ...LIGHT, rim: o.rim };
  ctx.save(); ctx.translate(x, y);
  if (o.shadow !== false) { ctx.fillStyle = 'rgb(0 0 0 / .25)'; ell(0, 0, 3.4 * s, .5 * s); ctx.fill(); }
  ctx.scale(s, s); ctx.translate(0, (o.dy ?? 0) - (o.jump ?? 0)); if (o.rot) ctx.rotate(o.rot); if (o.flip) ctx.scale(-1, 1); if (o.sq) { ctx.translate(0, -.5); ctx.scale(1 + o.sq * .35, 1 - o.sq); ctx.translate(0, .5); }
  // stand
  gloss(pfEll(0, -.42, 2.0, .5), shade(col, .1), { box: [-2, -.92, 4, 1], lw: .1, line: L, spec: .4 });
  gloss(pfRR(-.8, -1.35, 1.6, .95, .2), shade(col, .2), { box: [-.8, -1.35, 1.6, .95], lw: .09, line: L, spec: .2 });
  const body = () => { ctx.moveTo(-2.0, -9.0); ctx.lineTo(2.0, -9.0); ctx.quadraticCurveTo(3.7, -9.0, 3.7, -7.3); ctx.quadraticCurveTo(3.85, -4.4, 3.2, -2.35); ctx.quadraticCurveTo(2.95, -1.2, 1.9, -1.2); ctx.lineTo(-1.9, -1.2); ctx.quadraticCurveTo(-2.95, -1.2, -3.2, -2.35); ctx.quadraticCurveTo(-3.85, -4.4, -3.7, -7.3); ctx.quadraticCurveTo(-3.7, -9.0, -2.0, -9.0); ctx.closePath(); };
  // translucent shell with the CRT tube showing through
  gloss(body, col, { box: [-3.85, -9, 7.7, 7.8], lw: .12, line: L, spec: .9, alpha: .9, hi: .45, lo: .35 });
  ctx.save(); ctx.beginPath(); body(); ctx.clip();
  ctx.fillStyle = alpha(shade(col, .55), .35); ctx.beginPath(); ctx.moveTo(-1.6, -8.1); ctx.lineTo(1.6, -8.1); ctx.lineTo(1.0, -2.2); ctx.lineTo(-1.0, -2.2); ctx.closePath(); ctx.fill();
  ctx.fillStyle = 'rgb(255 255 255 / .28)'; ctx.beginPath(); ctx.moveTo(-3.3, -7.8); ctx.quadraticCurveTo(-3.5, -4.4, -2.9, -2.2); ctx.lineTo(-2.4, -2.2); ctx.quadraticCurveTo(-3.0, -4.4, -2.8, -7.8); ctx.closePath(); ctx.fill();
  ctx.restore();
  // bezel + screen
  gloss(pfRR(-2.85, -8.35, 5.7, 4.6, .9), tint(col, .55), { box: [-2.85, -8.35, 5.7, 4.6], lw: .1, line: L, spec: .5, rimK: .3 });
  const scr = () => { ctx.roundRect(-2.4, -7.95, 4.8, 3.8, .7); };
  ctx.beginPath(); scr(); ctx.fillStyle = rg(0, -6, .2, 3.4, [[0, o.screen ?? '#15303A'], [1, shade(o.screen ?? '#15303A', .6)]]); ctx.fill();
  ctx.save(); ctx.beginPath(); scr(); ctx.clip();
  if (o.glitch) for (let i = 0; i < 7; i++) { ctx.fillStyle = alpha(EP.red, .75 * o.glitch); ctx.fillRect(-2.4 + hash2(_boil, i) * 2, -7.95 + hash2(i, _boil) * 3.8, 1 + hash2(_boil + 3, i) * 3, .2); }
  ctx.save(); ctx.globalCompositeOperation = 'lighter'; ctx.fillStyle = rg(0, -6.05, 0, 2.6, [[0, alpha(gc, .28)], [1, alpha(gc, 0)]]); ctx.fillRect(-2.4, -7.95, 4.8, 3.8); ctx.restore();
  if (o.text !== undefined) { const lines = String(o.text).split('\n'), sz = o.textSize ?? (lines.length > 1 ? .7 : 1.05); lines.forEach((l, i) => ptext(l, 0, -6.05 + (i - (lines.length - 1) / 2) * sz * 1.15, sz, { font: 'code', fill: gc, maxW: 4.3 })); }
  else _lcdFace(o.face ?? 'dot', o.talk !== undefined ? 'talk' : (o.mouth ?? 'smile'), gc, o);
  ctx.fillStyle = 'rgb(0 0 0 / .18)'; for (let yy = -7.95; yy < -4.1; yy += .16) ctx.fillRect(-2.4, yy, 4.8, .06);
  ctx.fillStyle = 'rgb(255 255 255 / .12)'; ctx.beginPath(); ctx.moveTo(-2.4, -7.95); ctx.lineTo(.3, -7.95); ctx.lineTo(-2.4, -5.6); ctx.fill();
  ctx.restore();
  ctx.beginPath(); scr(); ctx.strokeStyle = L; ctx.lineWidth = .1; ctx.stroke();
  if (o.label) ptext(o.label, 0, -2.75, o.labelSize ?? .82, { font: 'archivo', fill: EP.white, maxW: 5.4, strokes: [[alpha(shade(col, .6), .9), .22]] });
  if (o.headband) { gloss(pfRR(-3.75, -8.9, 7.5, .75, .35), o.headband, { box: [-3.75, -8.9, 7.5, .75], lw: .09, line: L }); }
  if (o.blush) for (const sd of [-1, 1]) { ctx.fillStyle = alpha('#FF6F91', .6 * o.blush); ell(sd * 1.6, -5.2, .42, .2); ctx.fill(); }
  if (o.sweat) _emote('sweat', 3.5, -9.2, .6 * o.sweat, 1);
  if (o.hands !== false) {
    const hL = o.hL ?? [-4.3, -3.6], hR = o.hR ?? [4.3, -3.6];
    for (const [h, g, sd, hold] of [[hL, o.gL ?? 'open', -1, o.holdL], [hR, o.gR ?? 'open', 1, o.hold]]) {
      const ang = Math.atan2(h[1] + 5, h[0] - sd * 3.3);
      _arm([sd * 3.55, -5.0], h, sd, .22, '#E4E6F0', L, false);
      _toyHand(h[0], h[1], g, ang, sd, '#FBFBFF', { line: L, cuff: '#E4E6F0' });
      if (hold) { ctx.save(); ctx.translate(h[0], h[1]); ctx.scale(1 / s, 1 / s); hold(s); ctx.restore(); }
    }
  }
  ctx.restore();
  LIGHT = oldLight;
}
function _lcdFace(face, mouth, fc, o = {}) {
  ctx.save(); ctx.fillStyle = fc; ctx.strokeStyle = fc; ctx.lineCap = 'round'; ctx.lineWidth = .22;
  ctx.shadowColor = fc; ctx.shadowBlur = 0;
  for (const sd of [-1, 1]) {
    ctx.save(); ctx.translate(sd * 1.05, -6.45);
    const k = face === 'wink' && sd > 0 ? 'happy' : face;
    switch (k) {
      case 'happy': ctx.beginPath(); ctx.arc(0, .2, .42, Math.PI * 1.15, Math.PI * 1.85); ctx.stroke(); break;
      case 'closed': case 'sleepy': ctx.beginPath(); ctx.arc(0, -.15, .42, Math.PI * .15, Math.PI * .85); ctx.stroke(); break;
      case 'heart': poly(heartPts(0, 0, .55, 20)); ctx.fillStyle = '#FF5FA8'; ctx.fill(); break;
      case 'star': poly(starPts(0, 0, .6, .45, 5)); ctx.fillStyle = EP.yellow; ctx.fill(); break;
      case 'x': ctx.beginPath(); ctx.moveTo(-.35, -.35); ctx.lineTo(.35, .35); ctx.moveTo(.35, -.35); ctx.lineTo(-.35, .35); ctx.stroke(); break;
      case 'angry': ctx.fillRect(-.28, -.2, .56, .6); ctx.beginPath(); ctx.moveTo(-sd * .55, -.65); ctx.lineTo(sd * .4, -.3); ctx.stroke(); break;
      case 'sad': case 'cry': ctx.fillRect(-.26, -.25, .52, .6); ctx.beginPath(); ctx.moveTo(-sd * .5, -.45); ctx.lineTo(sd * .4, -.75); ctx.stroke(); if (k === 'cry') { ctx.fillStyle = '#7FD4FF'; ctx.fillRect(-.12, .45, .24, 1.0); } break;
      case 'wide': ctx.beginPath(); ctx.arc(0, 0, .55, 0, TAU); ctx.stroke(); ctx.beginPath(); ctx.arc(0, 0, .16, 0, TAU); ctx.fill(); break;
      case 'spiral': case 'dizzy': ctx.lineWidth = .12; ctx.beginPath(); for (let i = 0; i <= 24; i++) { const a = i * .55 + T * 9, r = .02 + i * .022; i ? ctx.lineTo(Math.cos(a) * r, Math.sin(a) * r) : ctx.moveTo(0, 0); } ctx.stroke(); break;
      case 'sly': ctx.fillRect(-.4, -.05, .8, .28); ctx.beginPath(); ctx.moveTo(-.45, -.35); ctx.lineTo(.45, -.2 * sd - .25); ctx.stroke(); break;
      case 'think': ctx.fillRect(-.24, -.4, .48, .7); break;
      default: rrect(-.27, -.42, .54, .84, .2); ctx.fill();
    }
    ctx.restore();
  }
  const my = -5.2;
  switch (mouth) {
    case 'open': ctx.beginPath(); ctx.moveTo(-.55, my - .15); ctx.quadraticCurveTo(0, my + .75, .55, my - .15); ctx.closePath(); ctx.fill(); break;
    case 'O': ctx.beginPath(); ctx.ellipse(0, my + .05, .32, .42, 0, 0, TAU); ctx.fill(); break;
    case 'flat': ctx.beginPath(); ctx.moveTo(-.5, my); ctx.lineTo(.5, my); ctx.stroke(); break;
    case 'wavy': ctx.beginPath(); ctx.moveTo(-.6, my); for (let i = 1; i <= 6; i++) ctx.lineTo(-.6 + i * .2, my + (i % 2 ? -.13 : .13)); ctx.lineWidth = .16; ctx.stroke(); break;
    case 'grin': ctx.beginPath(); ctx.moveTo(-.8, my - .25); ctx.quadraticCurveTo(0, my + .7, .8, my - .25); ctx.closePath(); ctx.fill(); break;
    case 'talk': { const k = clamp(o.talk); ctx.beginPath(); ctx.ellipse(0, my, .45, .1 + k * .38, 0, 0, TAU); ctx.fill(); break; }
    case 'none': break;
    default: ctx.beginPath(); ctx.arc(0, my - .55, .6, .22 * Math.PI, .78 * Math.PI); ctx.stroke();
  }
  ctx.restore();
}
// agentBot(x, y, s, o): a tiny candy computer on stick legs for agent swarms (≈ 3.2s tall). o: col, face ('>_' default text) or eyes (a _lcdFace kind),
// walk (phase), dy, rot, lanyard (colour: a staff lanyard), label (above), glowCol.
function agentBot(x, y, s, o = {}) {
  const col = o.col ?? CANDY.bondi, L = EP.line, walk = o.walk ?? 0;
  ctx.save(); ctx.translate(x, y + (o.dy ?? 0) * s); ctx.scale(s, s); if (o.rot) ctx.rotate(o.rot);
  for (const sd of [-1, 1]) { const lift = Math.max(0, Math.sin(walk * TAU + (sd > 0 ? Math.PI : 0))) * .35; ctx.strokeStyle = L; ctx.lineWidth = .22; ctx.lineCap = 'round'; ctx.beginPath(); ctx.moveTo(sd * .5, -.9); ctx.lineTo(sd * .6, -lift - .05); ctx.stroke(); ctx.fillStyle = '#F4F4FA'; ell(sd * .7, -lift, .3, .16); ctx.fill(); ctx.stroke(); }
  gloss(pfRR(-1.3, -3.3, 2.6, 2.45, .6), col, { box: [-1.3, -3.3, 2.6, 2.45], lw: .1, line: L, spec: .8, alpha: .92 });
  rrect(-.95, -3.0, 1.9, 1.45, .3); ctx.fillStyle = '#15303A'; ctx.fill();
  const gc = o.glowCol ?? '#AFFFF0';
  if (o.eyes) { ctx.save(); ctx.translate(0, -2.28); ctx.scale(.42, .42); ctx.translate(0, 6.2); _lcdFace(o.eyes, 'none', gc); ctx.restore(); }
  else ptext(o.face ?? '>_', 0, -2.28, .85, { font: 'code', fill: gc });
  if (o.lanyard) { ctx.strokeStyle = o.lanyard; ctx.lineWidth = .14; ctx.beginPath(); ctx.moveTo(-.6, -3.3); ctx.lineTo(0, -1.1); ctx.lineTo(.6, -3.3); ctx.stroke(); ctx.fillStyle = '#FFF'; ctx.fillRect(-.35, -1.25, .7, .5); ctx.strokeStyle = L; ctx.lineWidth = .05; ctx.strokeRect(-.35, -1.25, .7, .5); }
  if (o.label) ptext(o.label, 0, -3.9, .62, { fill: EP.white, strokes: [[L, .16]] });
  ctx.restore();
}
// hugFace(x, y, r, o): the hugging-face mascot as a glossy CGI ball. mood (happy|scared|x|worried), hands (default true), bandage.
function hugFace(x, y, r, o = {}) {
  const mood = o.mood ?? 'happy', dk = '#3A1A10';
  glossBall(x, y, r, r, '#FFCE2A', { lw: r * .05 });
  for (const sd of [-1, 1]) {
    const ex = x + sd * r * .36, ey = y - r * .12; ctx.strokeStyle = dk; ctx.fillStyle = dk; ctx.lineWidth = r * .08; ctx.lineCap = 'round';
    if (mood === 'x') { ctx.beginPath(); ctx.moveTo(ex - r * .12, ey - r * .12); ctx.lineTo(ex + r * .12, ey + r * .12); ctx.moveTo(ex + r * .12, ey - r * .12); ctx.lineTo(ex - r * .12, ey + r * .12); ctx.stroke(); }
    else if (mood === 'scared' || mood === 'worried') { ell(ex, ey, r * .14, r * .18); paint('#FFF', dk, r * .04); ell(ex, ey + r * .03, r * .06, r * .06); ctx.fill(); }
    else { ctx.beginPath(); ctx.arc(ex, ey + r * .06, r * .14, Math.PI * 1.1, Math.PI * 1.9); ctx.stroke(); }
    ctx.fillStyle = 'rgb(255 110 130 / .5)'; ell(x + sd * r * .6, y + r * .15, r * .15, r * .08); ctx.fill();
  }
  if (mood === 'scared') { ell(x, y + r * .4, r * .15, r * .2); paint('#8A2A3E'); }
  else if (mood === 'worried') { ctx.beginPath(); ctx.moveTo(x - r * .2, y + r * .45); ctx.quadraticCurveTo(x, y + r * .32, x + r * .2, y + r * .45); ctx.strokeStyle = dk; ctx.lineWidth = r * .06; ctx.stroke(); }
  else { ctx.beginPath(); ctx.moveTo(x - r * .38, y + r * .2); ctx.quadraticCurveTo(x, y + r * .82, x + r * .38, y + r * .2); ctx.closePath(); paint('#8A2A3E'); }
  if (o.hands !== false) for (const sd of [-1, 1]) glossBall(x + sd * r * .62, y + r * .66, r * .27, r * .22, '#FFCE2A', { lw: r * .04 });
  if (o.bandage) { ctx.save(); ctx.translate(x + r * .45, y - r * .55); ctx.rotate(.6); rrect(-r * .38, -r * .12, r * .76, r * .24, r * .1); paint('#FFE3C8', dk, r * .03); ctx.restore(); }
}

// =====================================================================================================
// PROPS
// =====================================================================================================
// goldMedal(x, y, r, o): a gold medal on a ribbon; (x, y) = disc centre. o.text, o.ribbon (colour), o.rot, o.glint (0..1).
function goldMedal(x, y, r, o = {}) {
  ctx.save(); ctx.translate(x, y); ctx.rotate(o.rot ?? 0);
  if (o.ribbon !== false) { poly([[-r * .7, -r * 3], [-r * .25, -r * .8], [r * .25, -r * .8], [r * .7, -r * 3], [r * .25, -r * 3], [0, -r * 1.6], [-r * .25, -r * 3]]); paint(o.ribbon ?? EP.blue, EP.line, Math.max(2, r * .05)); }
  glossBall(0, 0, r, r, EP.gold, { lw: r * .07, rim: null });
  ell(0, 0, r * .72, r * .72); ctx.strokeStyle = 'rgb(120 70 0 / .55)'; ctx.lineWidth = r * .05; ctx.stroke();
  if (o.text) ptext(o.text, 0, 0, r * .42, { font: 'archivo', fill: '#7A4A00', maxW: r * 1.3 });
  ctx.restore();
  glint(x - r * .45, y - r * .5, r * 1.2 * (o.glint ?? 1), o.glint ?? 1);
}
// gpuBox(x, y, w, o): a glossy black GPU brick sitting on (x, y) (bottom centre), height .56w. o.label ('GPU'), o.hot (0..1 red glow), o.rot.
function gpuBox(x, y, w, o = {}) {
  const h = w * .56; ctx.save(); ctx.translate(x, y); ctx.rotate(o.rot ?? 0);
  gloss(pfRR(-w / 2, -h, w, h, w * .06), '#23262F', { box: [-w / 2, -h, w, h], lw: w * .02, spec: .8 });
  ctx.fillStyle = EP.laser; ctx.fillRect(-w / 2 + w * .06, -h + w * .05, w * .88, w * .035);
  for (const fx of [-.22, .22]) { ell(fx * w, -h * .45, w * .16, w * .16); paint('#15171E', '#55596A', w * .012); ctx.save(); ctx.translate(fx * w, -h * .45); ctx.rotate(T * 14 + fx * 5); ctx.fillStyle = '#5A6070'; for (let i = 0; i < 5; i++) { ctx.rotate(TAU / 5); ell(w * .07, 0, w * .07, w * .025, .5); ctx.fill(); } ctx.restore(); }
  ptext(o.label ?? 'GPU', 0, -h * .12, w * .12, { font: 'archivo', fill: EP.laser, maxW: w * .8 });
  if (o.hot) glow(0, -h / 2, w * .9, EP.red, .5 * o.hot);
  ctx.restore();
}
// cdDisc(x, y, r, spin, o): a CD with a rainbow sheen. o.label (text on the hub ring), o.tilt (0..1 squash for perspective), o.col (label colour).
function cdDisc(x, y, r, spin = 0, o = {}) {
  ctx.save(); ctx.translate(x, y); ctx.scale(1, 1 - (o.tilt ?? 0));
  ell(0, 0, r, r); ctx.fillStyle = '#D8DCE6'; ctx.fill();
  ctx.save(); ell(0, 0, r, r); ctx.clip(); ctx.rotate(spin);
  const g = ctx.createConicGradient ? ctx.createConicGradient(0, 0, 0) : null;
  if (g) { [[0, '#FFB0E0'], [.12, '#A0F0FF'], [.25, '#F4F8FF'], [.37, '#FFE890'], [.5, '#FFB0E0'], [.62, '#A0F0FF'], [.75, '#F4F8FF'], [.87, '#C0FFB0'], [1, '#FFB0E0']].forEach(([k, c]) => g.addColorStop(k, c)); ctx.fillStyle = g; ctx.fillRect(-r, -r, r * 2, r * 2); }
  ctx.fillStyle = 'rgb(255 255 255 / .35)'; poly([[0, 0], [r * 1.2, -r * .25], [r * 1.2, r * .25]]); ctx.fill(); poly([[0, 0], [-r * 1.2, -r * .25], [-r * 1.2, r * .25]]); ctx.fill();
  ctx.restore();
  ell(0, 0, r * .36, r * .36); paint(o.col ?? '#ECEFF6', 'rgb(0 0 0 / .25)', r * .01);
  ell(0, 0, r * .13, r * .13); ctx.fillStyle = o.hole ?? '#0A0626'; ctx.fill();
  ell(0, 0, r, r); ctx.strokeStyle = EP.line; ctx.lineWidth = Math.max(1.5, r * .025); ctx.stroke();
  if (o.label) { ctx.save(); ctx.rotate(spin); ptext(o.label, 0, -r * .24, r * .1, { font: 'archivo', fill: EP.line, maxW: r * .5 }); ctx.restore(); }
  ctx.restore();
}
// discoBall(x, y, r, t): a mirror ball hanging on a chain, spinning, throwing glints.
function discoBall(x, y, r, t) {
  ctx.strokeStyle = '#8890A0'; ctx.lineWidth = 3; ctx.beginPath(); ctx.moveTo(x, -200); ctx.lineTo(x, y - r); ctx.stroke();
  ctx.save(); ell(x, y, r, r); ctx.clip();
  ctx.fillStyle = '#50586A'; ctx.fillRect(x - r, y - r, r * 2, r * 2);
  const rows = 10, sp = t * .8;
  for (let i = 0; i < rows; i++) {
    const la = -Math.PI / 2 + (i + .5) / rows * Math.PI, yy = y + Math.sin(la) * r, rr = Math.cos(la) * r, cols = Math.max(4, Math.round(rr / r * 16)), th = r / rows * 1.55;
    for (let j = 0; j < cols; j++) { const lo = (j / cols) * TAU + sp, c = Math.cos(lo); if (c < 0) continue; const xx = x + Math.sin(lo) * rr, br = .3 + .7 * hash2(i * 31 + j, Math.floor(t * 8 + i + j) % 7) * c; ctx.fillStyle = `rgb(${190 + 60 * br} ${200 + 50 * br} ${220 + 35 * br} / 1)`; ctx.fillRect(xx - rr * .19 * c, yy - th / 2, rr * .36 * c, th * .88); }
  }
  ctx.fillStyle = rg(x - r * .4, y - r * .4, 0, r * 1.2, [[0, 'rgb(255 255 255 / .25)'], [1, 'rgb(0 0 20 / .45)']]); ctx.fillRect(x - r, y - r, r * 2, r * 2);
  ctx.restore();
  ell(x, y, r, r); ctx.strokeStyle = EP.line; ctx.lineWidth = r * .04; ctx.stroke();
  for (let i = 0; i < 3; i++) { const a = hash2(Math.floor(t * 6), i) * TAU, rr = r * (.3 + .6 * hash2(i, Math.floor(t * 6))); glint(x + Math.cos(a) * rr, y + Math.sin(a) * rr, r * .5, .8); }
}
// speaker(x, y, w, t, o): a rave speaker cabinet standing on (x, y) (bottom centre), height 1.7w; woofers pump on the kick. o.col, o.logo.
function speaker(x, y, w, t, o = {}) {
  const h = w * 1.7, k = kick(t, 9);
  gloss(pfRR(x - w / 2, y - h, w, h, w * .05), o.col ?? '#1E2030', { box: [x - w / 2, y - h, w, h], lw: w * .02, spec: .3 });
  for (const [cy, r] of [[.26, .16], [.62, .34]]) {
    const rr = w * r * (1 + k * .06); ell(x, y - h + h * cy, w * r * 1.12, w * r * 1.12); paint('#0C0D14', '#3A3E50', w * .015);
    ctx.fillStyle = rg(x - rr * .3, y - h + h * cy - rr * .3, 0, rr, [[0, '#6A7088'], [.6, '#2A2E3A'], [1, '#101218']]); ell(x, y - h + h * cy, rr, rr); ctx.fill();
    glossBall(x, y - h + h * cy, rr * .3, rr * .3, '#3A3E50', { line: false, rimK: .3 });
  }
  if (o.logo) ptext(o.logo, x, y - h * .06, w * .09, { font: 'archivo', fill: EP.silver, maxW: w * .8 });
}
// crtTV(x, y, w, h, draw, o): a 90s CRT television (screen rect x, y, w, h) showing draw(w, h) in local coords; o.style ('black'|'silver'|'beige').
function crtTV(x, y, w, h, draw, o = {}) {
  const b = Math.min(w, h) * .09, bodyC = o.style === 'silver' ? '#B8BECC' : o.style === 'beige' ? '#D8CFB4' : '#26262E';
  gloss(pfRR(x - b, y - b, w + b * 2, h + b * 2.6, b * .8), bodyC, { box: [x - b, y - b, w + b * 2, h + b * 2.6], lw: 3, spec: .5 });
  ctx.save(); rrect(x, y, w, h, b * .6); ctx.clip(); ctx.fillStyle = '#000'; ctx.fillRect(x, y, w, h);
  ctx.translate(x, y); if (draw) draw(w, h);
  ctx.fillStyle = 'rgb(0 0 0 / .12)'; for (let yy = 0; yy < h; yy += 4) ctx.fillRect(0, yy, w, 1.5);
  ctx.fillStyle = rg(w * .5, h * .5, h * .3, w * .8, [[0, 'rgb(0 0 0 / 0)'], [1, 'rgb(0 0 0 / .45)']]); ctx.fillRect(0, 0, w, h);
  ctx.fillStyle = 'rgb(255 255 255 / .08)'; ctx.beginPath(); ctx.ellipse(w * .3, h * .18, w * .35, h * .12, -.2, 0, TAU); ctx.fill();
  ctx.restore();
  ctx.fillStyle = '#3A3A44'; for (let i = 0; i < 3; i++) { ell(x + w - b * (1 + i * 1.3), y + h + b * .9, b * .35, b * .35); ctx.fill(); }
  ctx.fillStyle = o.led ?? '#3BFF4A'; ell(x + b * .5, y + h + b * .9, b * .18, b * .18); ctx.fill();
}

// =====================================================================================================
// THE WORLD — chroma-key CGI sets: checkerboard floors, tunnels, lasers, flares, starfields, 3D pipes, spinning objects, crowds.
// =====================================================================================================
// rays(cx, cy, n, col, rot, R): a sunburst (every other wedge filled).
function rays(cx, cy, n, col, rot = 0, R = 2600) { ctx.fillStyle = col; ctx.beginPath(); for (let i = 0; i < n; i++) { const a0 = rot + i / n * TAU, a1 = a0 + TAU / n / 2; ctx.moveTo(cx, cy); ctx.lineTo(cx + Math.cos(a0) * R, cy + Math.sin(a0) * R); ctx.lineTo(cx + Math.cos(a1) * R, cy + Math.sin(a1) * R); ctx.closePath(); } ctx.fill(); }
// checkerFloor(t, o): the ray-traced checkerboard to infinity. o.horizon (y), o.a / o.b (tile colours), o.speed (tiles/s toward camera),
// o.tile (world size), o.cx (vanishing x), o.pan (sideways scroll, tiles), o.fog (colour at the horizon), o.reflect (0..1 glossy sheen), o.y1.
function checkerFloor(t, o = {}) {
  const hz = o.horizon ?? 620, cx = o.cx ?? W / 2, A = o.a ?? '#F4F4FA', B = o.b ?? '#1A1A40', f = 900, camH = o.camH ?? 1.1, sp = o.speed ?? .8, pan = o.pan ?? 0;
  ctx.fillStyle = B; ctx.fillRect(-900, hz, W + 1800, H + 900 - hz);
  const zOff = frac(t * sp / 2) * 2, rows = 34, cols = 26;
  ctx.beginPath();
  for (let j = 0; j < rows; j++) {
    const z0 = j - zOff + .25, z1 = z0 + 1; if (z1 <= .2) continue;
    const za = Math.max(.2, z0), y0 = hz + f * camH / (za * 2.2), y1 = hz + f * camH / (z1 * 2.2);
    const jj = j + Math.floor(t * sp / 2) * 2;
    for (let i = -cols; i < cols; i++) {
      if ((i + jj + Math.floor(pan)) % 2 === 0) continue;
      const u0 = i - frac(pan), u1 = u0 + 1;
      const xa0 = cx + u0 * f / (za * 2.2) * .9, xa1 = cx + u1 * f / (za * 2.2) * .9, xb0 = cx + u0 * f / (z1 * 2.2) * .9, xb1 = cx + u1 * f / (z1 * 2.2) * .9;
      if (Math.max(xa0, xb0) > W + 900 || Math.min(xa1, xb1) < -900) continue;
      ctx.moveTo(xa0, y0); ctx.lineTo(xa1, y0); ctx.lineTo(xb1, y1); ctx.lineTo(xb0, y1); ctx.closePath();
    }
  }
  ctx.fillStyle = A; ctx.fill();
  if (o.reflect ?? .5) { ctx.fillStyle = lg(0, hz, 0, H, [[0, 'rgb(255 255 255 / 0)'], [.25, `rgb(255 255 255 / ${.12 * (o.reflect ?? .5)})`], [1, 'rgb(255 255 255 / 0)']]); ctx.fillRect(-900, hz, W + 1800, H - hz + 900); }
  const fog = o.fog ?? '#8A6AFF'; ctx.fillStyle = lg(0, hz, 0, hz + (o.fogH ?? 170), [[0, fog], [1, alpha(fog, 0)]]); ctx.fillRect(-900, hz, W + 1800, o.fogH ?? 170);
}
// tunnel(t, o): rings rushing at the camera. o.cx / o.cy (vanishing point), o.n, o.speed (rings/s), o.shape ('ring'|'square'|'hex'|'star'),
// o.cols (colour list), o.width (line px at the near end), o.twist (rad per ring), o.bg (fill first), o.r (near radius).
function tunnel(t, o = {}) {
  const cx = o.cx ?? W / 2, cy = o.cy ?? H / 2, n = o.n ?? 22, sp = o.speed ?? 2.2, cols = o.cols ?? [EP.magenta, EP.cyan, EP.uv, EP.yellow], shape = o.shape ?? 'ring', R = o.r ?? 1500;
  if (o.bg !== false) bgGrad([[0, o.bg ?? EP.void], [1, o.bg ?? EP.void]]);
  const glowC = o.glow ?? cols[0]; ctx.fillStyle = rg(cx, cy, 0, 420, [[0, alpha(glowC, .55)], [1, alpha(glowC, 0)]]); ctx.fillRect(cx - 420, cy - 420, 840, 840);
  ctx.save(); ctx.globalCompositeOperation = 'lighter'; ctx.lineJoin = 'round';
  for (let i = n - 1; i >= 0; i--) {
    const idx = i + Math.floor(t * sp), z = n - i - frac(t * sp) + .3, r = R / z, a = clamp(1.4 - z / n * 1.3) * clamp(z * .8);
    if (r < 4 || a <= 0) continue;
    ctx.strokeStyle = alpha(cols[((idx % cols.length) + cols.length) % cols.length], a); ctx.lineWidth = Math.max(1.5, (o.width ?? 60) / z);
    ctx.save(); ctx.translate(cx, cy); ctx.rotate((o.twist ?? .12) * idx + (o.spin ?? 0) * t);
    ctx.beginPath();
    if (shape === 'ring') ctx.arc(0, 0, r, 0, TAU);
    else { const k = shape === 'square' ? 4 : shape === 'hex' ? 6 : 10; for (let q = 0; q <= k; q++) { const aa = q / k * TAU + (shape === 'square' ? Math.PI / 4 : 0), rr = shape === 'star' && q % 2 ? r * .55 : r; q ? ctx.lineTo(Math.cos(aa) * rr, Math.sin(aa) * rr) : ctx.moveTo(Math.cos(aa) * rr, Math.sin(aa) * rr); } }
    ctx.stroke(); ctx.restore();
  }
  ctx.restore();
}
// laserFan(x, y, t, o): laser beams fanning from a projector at (x, y). o.n, o.col (or o.cols), o.angle (centre, rad; −π/2 = up),
// o.spread (rad), o.sweep (rad of beat-synced sweep), o.len, o.w (core px), o.alpha, o.flicker (0..1 strobe the beams on 8ths).
function laserFan(x, y, t, o = {}) {
  const n = o.n ?? 9, cols = o.cols ?? [o.col ?? EP.laser], base = o.angle ?? -Math.PI / 2, spread = o.spread ?? 1.4, len = o.len ?? 2600;
  const sw = (o.sweep ?? .5) * Math.sin(bpOf(t) * Math.PI / 2 + (o.phase ?? 0)), a0 = o.alpha ?? 1;
  const fl = o.flicker ? (frac(bpOf(t) * 2) < .5 ? 1 : 1 - o.flicker) : 1; if (fl <= 0) return;
  ctx.save(); ctx.globalCompositeOperation = 'lighter'; ctx.lineCap = 'round';
  for (let i = 0; i < n; i++) {
    const u = n === 1 ? 0 : i / (n - 1) - .5, a = base + u * spread + sw * (o.fanSweep ? u * 2 : 1), ex = x + Math.cos(a) * len, ey = y + Math.sin(a) * len, c = cols[i % cols.length];
    ctx.strokeStyle = alpha(c, .12 * a0 * fl); ctx.lineWidth = (o.w ?? 4) * 7; ctx.beginPath(); ctx.moveTo(x, y); ctx.lineTo(ex, ey); ctx.stroke();
    ctx.strokeStyle = alpha(c, .85 * a0 * fl); ctx.lineWidth = o.w ?? 4; ctx.stroke();
    ctx.strokeStyle = alpha('#FFFFFF', .6 * a0 * fl); ctx.lineWidth = (o.w ?? 4) * .35; ctx.stroke();
  }
  glow(x, y, 60, cols[0], .9 * a0 * fl);
  ctx.restore();
}
// laserSheet(y, t, o): a flat laser plane (a 'liquid sky' sheet) seen edge-on across the room at height y, rippling. o.col, o.alpha, o.tilt.
function laserSheet(y, t, o = {}) {
  const col = o.col ?? EP.laser; ctx.save(); ctx.globalCompositeOperation = 'lighter';
  for (let i = 0; i < 3; i++) { ctx.fillStyle = alpha(col, (o.alpha ?? .35) * (1 - i * .3)); ctx.beginPath(); ctx.moveTo(-100, y); for (let x = -100; x <= W + 100; x += 40) ctx.lineTo(x, y + Math.sin(x * .006 + t * 2 + i) * 16 + (x - W / 2) * (o.tilt ?? 0)); ctx.lineTo(W + 100, y + 400 + i * 80); ctx.lineTo(-100, y + 400 + i * 80); ctx.closePath(); ctx.fill(); }
  ctx.restore();
}
// strobe(k, col): a full-frame flash (k 0..1). strobeK(t, div, dur): 1→0 envelope that fires every 1/div beats.
function strobe(k, col = '#FFFFFF') { if (k <= 0) return; ctx.save(); ctx.globalAlpha = clamp(k); ctx.fillStyle = col; ctx.fillRect(-900, -900, W + 1800, H + 1800); ctx.restore(); }
const strobeK = (t, div = 1, dur = .18) => { const ph = frac(bpOf(t) * div) * beatLen() / div; return ph < dur * beatLen() / div ? 1 - ph / (dur * beatLen() / div) : 0; };
// lensFlare(x, y, k, o): a 3DS-Max lens flare: hot core, anamorphic streak, ring and hexagonal ghosts toward the frame centre. o.col, o.streak.
function lensFlare(x, y, k = 1, o = {}) {
  if (k <= 0) return; const col = o.col ?? '#FFD2A0';
  ctx.save(); ctx.globalCompositeOperation = 'lighter';
  glow(x, y, 260 * k, col, .75 * k); glow(x, y, 70 * k, '#FFFFFF', 1 * k);
  const sl = (o.streak ?? 900) * k; ctx.fillStyle = lg(x - sl, 0, x + sl, 0, [[0, 'rgb(120 180 255 / 0)'], [.5, `rgb(200 230 255 / ${.8 * k})`], [1, 'rgb(120 180 255 / 0)']]); ctx.fillRect(x - sl, y - 4 * k, sl * 2, 8 * k);
  ctx.strokeStyle = alpha(col, .25 * k); ctx.lineWidth = 10 * k; ell(x, y, 150 * k, 150 * k); ctx.stroke();
  const dx = W / 2 - x, dy = H / 2 - y, gh = [[.35, 30, '#FF6AC8'], [.6, 60, '#6AFFE0'], [.95, 22, '#FFFFFF'], [1.3, 90, '#8A6AFF'], [1.6, 40, '#FFB84A']];
  for (const [u, r, c] of gh) { const gx = x + dx * u, gy = y + dy * u; ctx.fillStyle = alpha(c, .16 * k); ctx.beginPath(); for (let q = 0; q < 6; q++) { const a = q / 6 * TAU + .3; q ? ctx.lineTo(gx + Math.cos(a) * r * k, gy + Math.sin(a) * r * k) : ctx.moveTo(gx + Math.cos(a) * r * k, gy + Math.sin(a) * r * k); } ctx.closePath(); ctx.fill(); }
  ctx.restore();
  glint(x, y, 220 * k, k);
}
// starfield(t, o): the Windows "Starfield Simulation" screensaver: stars streaking out from (cx, cy). o.n, o.speed, o.col, o.bg (false = no fill).
function starfield(t, o = {}) {
  const cx = o.cx ?? W / 2, cy = o.cy ?? H / 2, n = o.n ?? 260, sp = o.speed ?? .45;
  if (o.bg !== false) fillAll(o.bg ?? '#000000');
  ctx.save(); ctx.lineCap = 'round';
  for (let i = 0; i < n; i++) {
    const sx = (hash2(i, 1) - .5) * 2, sy = (hash2(i, 2) - .5) * 2, z = frac(hash2(i, 3) - t * sp) + .02, z2 = z + .035 * sp / .45;
    const px = cx + sx / z * 420, py = cy + sy / z * 420, qx = cx + sx / z2 * 420, qy = cy + sy / z2 * 420;
    if (px < -50 || px > W + 50 || py < -50 || py > H + 50) continue;
    const a = clamp((1 - z) * 1.3); ctx.strokeStyle = o.col ? alpha(o.col, a) : `rgb(255 255 255 / ${a})`; ctx.lineWidth = 1 + (1 - z) * 4; ctx.beginPath(); ctx.moveTo(qx, qy); ctx.lineTo(px, py); ctx.stroke();
  }
  ctx.restore();
}
// pipes(t, t0, o): the Windows 98 "3D Pipes" screensaver, growing since t0. Pipes wander a 3D grid, turning at ball joints; the camera is fixed.
// o.seed, o.n (pipes at once), o.rate (segments per second), o.cols, o.cx / o.cy / o.scale (placement), o.w (pipe width in grid units, .22),
// o.maxLen (segments per pipe before the next starts), o.bg (false = no fill). Returns the tip of the newest pipe.
function pipes(t, t0, o = {}) {
  if (o.bg !== false) fillAll(o.bg ?? '#000000');
  const seed = o.seed ?? 3, n = o.n ?? 3, rate = o.rate ?? 7, cols = o.cols ?? ['#E8342A', '#2A9AE8', '#E8C42A', '#2AE85A', '#C42AE8', '#E8E8E8', '#E87A2A'];
  const S = o.scale ?? 92, cx = o.cx ?? W / 2, cy = o.cy ?? H / 2 + 40, G = 9, maxLen = o.maxLen ?? 34, pw = o.w ?? .3;
  const P = ([x, y, z]) => { const zz = z + 12, s = S * 12 / zz; return [cx + (x - y * .35) * s, cy + (-y * .8 + x * .08) * s + z * 2.5, s]; };
  const el = Math.max(0, t - t0) * rate; let tip = null;
  const lists = [];
  for (let p = 0; p < n; p++) {
    let gen = 0; const startAt = p * maxLen * .45;
    let segsDone = el - startAt; if (segsDone <= 0) continue;
    while (segsDone > maxLen) { segsDone -= maxLen * .9; gen++; }
    const id = seed * 101 + p * 13 + gen * 7, col = cols[(p + gen * 3) % cols.length];
    let pos = [Math.floor(hash2(id, 1) * G) - G / 2, Math.floor(hash2(id, 2) * G) - G / 2, Math.floor(hash2(id, 3) * 6) - 3], dir = Math.floor(hash2(id, 4) * 6);
    const segs = [];
    for (let i = 0; i < Math.ceil(segsDone); i++) {
      const len = 1 + Math.floor(hash2(id, 10 + i) * 3), frac1 = i === Math.ceil(segsDone) - 1 ? segsDone - i : 1;
      let d = [[1, 0, 0], [-1, 0, 0], [0, 1, 0], [0, -1, 0], [0, 0, 1], [0, 0, -1]][dir];
      let nx = pos.map((v, k) => v + d[k] * len);
      if (nx.some((v, k) => Math.abs(v) > (k === 2 ? 4 : G / 2))) { dir = dir ^ 1; d = d.map(v => -v); nx = pos.map((v, k) => v + d[k] * len); }
      const end = pos.map((v, k) => v + d[k] * len * frac1);
      segs.push([pos, end, i]); pos = nx;
      let nd = Math.floor(hash2(id, 50 + i) * 6); if ((nd >> 1) === (dir >> 1)) nd = (nd + 2) % 6; dir = nd;
    }
    lists.push({ segs, col });
    const last = segs[segs.length - 1]; if (last) tip = P(last[1]);
  }
  ctx.save(); ctx.lineCap = 'butt';
  for (const { segs, col } of lists) for (const [a, b, i] of segs) {
    const [ax, ay, as] = P(a), [bx, by, bs] = P(b), w = pw * (as + bs) / 2, ang = Math.atan2(by - ay, bx - ax), nx = -Math.sin(ang) * w, ny = Math.cos(ang) * w;
    ctx.fillStyle = lg(ax + nx, ay + ny, ax - nx, ay - ny, [[0, shade(col, .55)], [.3, col], [.45, tint(col, .6)], [.6, col], [1, shade(col, .6)]]);
    ctx.beginPath(); ctx.moveTo(ax + nx, ay + ny); ctx.lineTo(bx + nx, by + ny); ctx.lineTo(bx - nx, by - ny); ctx.lineTo(ax - nx, ay - ny); ctx.closePath(); ctx.fill();
    if (i > 0) glossBall(ax, ay, w * 1.25, w * 1.25, col, { line: false, rim: null });
  }
  ctx.restore();
  return tip;
}
// mystify(t, o): the "Mystify" screensaver — two bouncing polygons with trails. o.cols, o.n (trail copies), o.bg.
function mystify(t, o = {}) {
  if (o.bg !== false) fillAll(o.bg ?? '#000');
  const cols = o.cols ?? [EP.magenta, EP.cyan], tri = (v, sp, ph, L) => { const u = frac(v + sp * t + ph); return 60 + (u < .5 ? u * 2 : 2 - u * 2) * (L - 120); };
  ctx.save(); ctx.lineWidth = 3;
  for (let q = 0; q < 2; q++) for (let k = 0; k < (o.n ?? 6); k++) {
    const tt = -k * .05; ctx.strokeStyle = alpha(cols[q], 1 - k / (o.n ?? 6)); ctx.beginPath();
    for (let v = 0; v <= 4; v++) { const vv = v % 4, x = tri(hash2(q, vv), .11 + hash2(q, vv + 9) * .1, tt * .11, W), y = tri(hash2(q + 5, vv), .13 + hash2(q, vv + 19) * .1, tt * .13, H); v ? ctx.lineTo(x, y) : ctx.moveTo(x, y); }
    ctx.stroke();
  }
  ctx.restore();
}
// spin3D(kind, x, y, r, a, o): a cheesy early-CGI object turning in 3D. kind: cube|pyramid|octa|diamond|torus|star|disc.
// a = [rx, ry, rz] rotation (rad); o.mode ('flat' shaded | 'wire' | 'chrome'), o.col, o.wire (line colour), o.lw.
const _MESH = {};
function _mesh(kind) {
  if (_MESH[kind]) return _MESH[kind];
  let V = [], F = [];
  if (kind === 'cube') { V = [[-1, -1, -1], [1, -1, -1], [1, 1, -1], [-1, 1, -1], [-1, -1, 1], [1, -1, 1], [1, 1, 1], [-1, 1, 1]].map(v => v.map(c => c * .72)); F = [[0, 1, 2, 3], [5, 4, 7, 6], [4, 0, 3, 7], [1, 5, 6, 2], [4, 5, 1, 0], [3, 2, 6, 7]]; }
  else if (kind === 'pyramid') { V = [[0, -1, 0], [-.9, .6, -.9], [.9, .6, -.9], [.9, .6, .9], [-.9, .6, .9]]; F = [[0, 2, 1], [0, 3, 2], [0, 4, 3], [0, 1, 4], [1, 2, 3, 4]]; }
  else if (kind === 'octa' || kind === 'diamond') { const h = kind === 'diamond' ? 1.25 : 1; V = [[0, -h, 0], [1, 0, 0], [0, 0, 1], [-1, 0, 0], [0, 0, -1], [0, h * .7, 0]]; F = [[0, 2, 1], [0, 3, 2], [0, 4, 3], [0, 1, 4], [5, 1, 2], [5, 2, 3], [5, 3, 4], [5, 4, 1]]; }
  else if (kind === 'torus') { const nu = 18, nv = 9; for (let i = 0; i < nu; i++) for (let j = 0; j < nv; j++) { const u = i / nu * TAU, v = j / nv * TAU; V.push([(0.72 + .3 * Math.cos(v)) * Math.cos(u), .3 * Math.sin(v), (0.72 + .3 * Math.cos(v)) * Math.sin(u)]); } for (let i = 0; i < nu; i++) for (let j = 0; j < nv; j++) { const a = i * nv + j, b = ((i + 1) % nu) * nv + j, c = ((i + 1) % nu) * nv + (j + 1) % nv, d = i * nv + (j + 1) % nv; F.push([a, d, c, b]); } }
  else if (kind === 'star') { const n = 5; V.push([0, 0, -.35], [0, 0, .35]); for (let i = 0; i < n * 2; i++) { const a = -Math.PI / 2 + i / (n * 2) * TAU, r = i % 2 ? .45 : 1; V.push([Math.cos(a) * r, Math.sin(a) * r, 0]); } for (let i = 0; i < n * 2; i++) { const a = 2 + i, b = 2 + (i + 1) % (n * 2); F.push([0, a, b], [1, b, a]); } }
  else if (kind === 'disc') { const n = 24; V.push([0, 0, 0]); for (let i = 0; i < n; i++) { const a = i / n * TAU; V.push([Math.cos(a), Math.sin(a), 0]); } for (let i = 0; i < n; i++) F.push([0, 1 + i, 1 + (i + 1) % n]); }
  return (_MESH[kind] = { V, F });
}
function spin3D(kind, x, y, r, a, o = {}) {
  const { V, F } = _mesh(kind), [rx, ry, rz] = a, mode = o.mode ?? 'flat', col = o.col ?? EP.magenta;
  const cxr = Math.cos(rx), sxr = Math.sin(rx), cyr = Math.cos(ry), syr = Math.sin(ry), czr = Math.cos(rz), szr = Math.sin(rz);
  const P = V.map(([vx, vy, vz]) => { let X = vx * cyr + vz * syr, Z = -vx * syr + vz * cyr, Y = vy; const Y2 = Y * cxr - Z * sxr; Z = Y * sxr + Z * cxr; Y = Y2; const X2 = X * czr - Y * szr; Y = X * szr + Y * czr; X = X2; const s = 3.2 / (3.2 + Z); return [x + X * r * s, y + Y * r * s, Z, X, Y]; });
  const faces = F.map(f => { const p = f.map(i => P[i]), [a0, b0, c0] = p; const ux = b0[3] - a0[3], uy = b0[4] - a0[4], uz = b0[2] - a0[2], vx = c0[3] - a0[3], vy = c0[4] - a0[4], vz = c0[2] - a0[2]; let nx = uy * vz - uz * vy, ny = uz * vx - ux * vz, nz = ux * vy - uy * vx; const nl = Math.hypot(nx, ny, nz) || 1; nx /= nl; ny /= nl; nz /= nl; return { p, z: p.reduce((s2, q) => s2 + q[2], 0) / p.length, n: [nx, ny, nz] }; }).sort((A, B) => B.z - A.z);
  ctx.save(); ctx.lineJoin = 'round';
  for (const fc of faces) {
    const front = fc.n[2] < 0; if (!front && mode !== 'wire') continue;
    ctx.beginPath(); fc.p.forEach(([px, py], i) => i ? ctx.lineTo(px, py) : ctx.moveTo(px, py)); ctx.closePath();
    const lam = clamp(-.45 * fc.n[0] - .6 * fc.n[1] - .66 * fc.n[2]);
    if (mode === 'wire') { ctx.strokeStyle = alpha(o.wire ?? EP.laser, front ? 1 : .25); ctx.lineWidth = o.lw ?? 3; ctx.stroke(); continue; }
    if (mode === 'chrome') { const ys = fc.p.map(q => q[1]), y0 = Math.min(...ys), y1 = Math.max(...ys); ctx.fillStyle = lg(0, y0, 0, y1 + 1, [[0, mixCol('#2A3A8A', '#FFFFFF', lam)], [.5, mixCol('#8AB0FF', '#FFFFFF', lam * .8)], [.52, mixCol('#3A2030', '#6A4A5A', lam)], [1, mixCol('#C0703A', '#FFE0B0', lam)]]); }
    else ctx.fillStyle = mixCol(shade(col, .65), tint(col, .45), lam ** 1.2);
    ctx.fill(); ctx.strokeStyle = o.wire ?? alpha(EP.line, .85); ctx.lineWidth = o.lw ?? Math.max(1, r * .02); ctx.stroke();
  }
  ctx.restore();
}
// raveCrowd(t, o): rows of backlit ravers (heads and shoulders) bouncing to the beat, with glowsticks and hands up.
// o.y (front-row head line), o.rows, o.n (per row), o.s (front scale), o.k (energy 0..1), o.hands (0..1 share with hands up), o.sticks (0..1 share with glowsticks),
// o.cols (glowstick colours), o.rim (backlight colour), o.col (silhouette colour), o.seed, o.x0 / o.x1, o.lighters (true: lighters instead of sticks).
function raveCrowd(t, o = {}) {
  const rows = o.rows ?? 3, y0 = o.y ?? 930, S = o.s ?? 1, k = o.k ?? 1, seed = o.seed ?? 7, cols = o.cols ?? [EP.laser, EP.magenta, EP.cyan, EP.yellow], rim = o.rim ?? EP.magenta, body = o.col ?? '#0C0718';
  const x0 = o.x0 ?? -80, x1 = o.x1 ?? W + 80;
  for (let r = rows - 1; r >= 0; r--) {
    const sc = S * (1 - r * .22), yy = y0 - r * 70 * S, n = Math.round((o.n ?? 14) * (1 + r * .35)), dim = 1 - r * .28;
    for (let i = 0; i < n; i++) {
      const id = seed * 1000 + r * 100 + i, x = lerp(x0, x1, (i + .5 + (hash2(id, 1) - .5) * .6) / n), ph = hash2(id, 2) * .35, bb = bpOf(t) - ph;
      const hop = Math.abs(Math.sin(bb * Math.PI)) * 16 * sc * k, hy = yy - hop, hr = 34 * sc * (.9 + hash2(id, 3) * .25);
      const up = hash2(id, 4) < (o.hands ?? .45) * k, stick = hash2(id, 5) < (o.sticks ?? .5);
      // shoulders + head
      ctx.fillStyle = mixCol(body, rim, .08 * (1 - dim)); ell(x, hy + hr * 1.9, hr * 1.55, hr * 1.1); ctx.fill(); ell(x, hy, hr, hr * 1.05); ctx.fill();
      ctx.save(); ctx.globalCompositeOperation = 'lighter'; ctx.strokeStyle = alpha(rim, .55 * dim); ctx.lineWidth = 3 * sc; ctx.beginPath(); ctx.arc(x, hy, hr, Math.PI * 1.1, Math.PI * 1.75); ctx.stroke(); ctx.restore();
      if (up) {
        for (const sd of (hash2(id, 6) < .6 ? [-1, 1] : [hash2(id, 7) < .5 ? -1 : 1])) {
          const sw = Math.sin(bb * Math.PI + (sd > 0 ? 0 : .6)), hx = x + sd * hr * 1.3 + sw * 22 * sc, hyy = hy - hr * 2.4 - Math.abs(sw) * 10 * sc;
          ctx.strokeStyle = body; ctx.lineCap = 'round'; ctx.lineWidth = hr * .5; ctx.beginPath(); ctx.moveTo(x + sd * hr * 1.05, hy + hr * 1.55); ctx.quadraticCurveTo(x + sd * hr * 1.9, hy + hr * .2, hx, hyy + hr * .2); ctx.stroke();
          ctx.fillStyle = body; ell(hx, hyy, hr * .42, hr * .5, sw * .3); ctx.fill();
          ctx.save(); ctx.globalCompositeOperation = 'lighter'; ctx.strokeStyle = alpha(rim, .45 * dim); ctx.lineWidth = 2 * sc; ctx.beginPath(); ctx.ellipse(hx, hyy, hr * .42, hr * .5, sw * .3, Math.PI, Math.PI * 1.8); ctx.stroke(); ctx.restore();
          if (stick) {
            const c = cols[Math.floor(hash2(id, 8 + sd) * cols.length)], a = sw * .7 + (sd * .2), L = hr * 1.5;
            ctx.save(); ctx.globalCompositeOperation = 'lighter'; ctx.lineCap = 'round';
            if (o.lighters) { glow(hx, hyy - hr * .7, hr * 1.2, '#FFB040', .7); ctx.fillStyle = '#FFE6A0'; ell(hx, hyy - hr * .75, hr * .12, hr * .3); ctx.fill(); }
            else { ctx.strokeStyle = alpha(c, .3); ctx.lineWidth = hr * .45; ctx.beginPath(); ctx.moveTo(hx - Math.sin(a) * L * .2, hyy + Math.cos(a) * L * .2); ctx.lineTo(hx + Math.sin(a) * L, hyy - Math.cos(a) * L); ctx.stroke(); ctx.strokeStyle = tint(c, .5); ctx.lineWidth = hr * .16; ctx.stroke(); }
            ctx.restore();
          }
        }
      }
    }
  }
}
// djBooth(x, y, w, t, o): the DJ booth: a glossy desk whose top edge is at y, spanning x ± w/2; two turntables with spinning records and a mixer
// with bouncing meters. Draw djClawd first (behind it). o.label (the front LED text, default DJ CLAWD: static and fitted to the display, so
// the whole name reads in the briefest shot), o.col, o.scratch (0..1: the right record jerks back).
function djBooth(x, y, w, t, o = {}) {
  const h = w * .36, d = w * .12, k = kick(t, 8);
  // top surface (seen from slightly above)
  poly([[x - w / 2 + d * .6, y - d], [x + w / 2 - d * .6, y - d], [x + w / 2, y], [x - w / 2, y]]); paint('#2A2A38', EP.line, 3);
  for (const sd of [-1, 1]) {
    const tx = x + sd * w * .28, ty = y - d * .52, rx = w * .15, ry = d * .42, spin = t * 3.5 * (sd > 0 && o.scratch ? 1 - 2 * o.scratch : 1);
    ell(tx, ty, rx * 1.08, ry * 1.12); paint('#3A3A48', EP.line, 2);
    ell(tx, ty, rx, ry); paint('#0C0C12');
    ctx.strokeStyle = 'rgb(255 255 255 / .12)'; ctx.lineWidth = 1.5; for (let i = 1; i < 4; i++) { ell(tx, ty, rx * (.45 + i * .15), ry * (.45 + i * .15)); ctx.stroke(); }
    ell(tx, ty, rx * .32, ry * .32); paint(sd < 0 ? EP.magenta : EP.cyan);
    ctx.fillStyle = '#FFF'; ell(tx + Math.cos(spin) * rx * .2, ty + Math.sin(spin) * ry * .2, rx * .05, ry * .06); ctx.fill();
    ctx.strokeStyle = '#C8CCD8'; ctx.lineWidth = w * .008; ctx.beginPath(); ctx.moveTo(tx + rx * 1.02, ty - ry * .9); ctx.lineTo(tx + rx * .75, ty + ry * .2); ctx.lineTo(tx + rx * .45, ty + ry * .35); ctx.stroke();
  }
  // mixer
  rrect(x - w * .09, y - d * .92, w * .18, d * .84, 4); paint('#15151E', EP.line, 2);
  for (let i = 0; i < 4; i++) { const mx = x - w * .065 + i * w * .043, lv = clamp(.35 + k * .55 + Math.sin(t * 9 + i * 1.7) * .12); for (let j = 0; j < 5; j++) { ctx.fillStyle = j / 5 < lv ? (j > 3 ? EP.red : j > 2 ? EP.yellow : EP.laser) : '#2A2A34'; ctx.fillRect(mx, y - d * .2 - j * d * .13, w * .02, d * .09); } }
  // front panel
  gloss(pfRR(x - w / 2, y, w, h, w * .02), o.col ?? '#181824', { box: [x - w / 2, y, w, h], lw: 3, spec: .4 });
  ctx.fillStyle = lg(x - w / 2, 0, x + w / 2, 0, [[0, EP.magenta], [.5, EP.cyan], [1, EP.magenta]]); ctx.fillRect(x - w / 2 + 6, y + 6, w - 12, 5); ctx.fillRect(x - w / 2 + 6, y + h - 11, w - 12, 5);
  const lw = w * .7, lh = h * .42, lx = x - lw / 2, ly = y + h * .3;
  rrect(lx, ly, lw, lh, 6); paint('#05050A', '#3A3A48', 2);
  ctx.save(); rrect(lx, ly, lw, lh, 6); ctx.clip();
  const label = o.label ?? 'DJ CLAWD', px = Math.min(lh / 9, lw * .88 / (pixW(label, 1) + .01));
  pixText(label, x, ly + (lh - 7 * px) / 2, px, EP.amber, { align: 'center', glow: true, alpha: .82 + .18 * k });
  ctx.restore();
}
// videoWall(x, y, cols, rows, cw, ch, draw, o): a wall of CRT monitors (the 90s music-TV set). draw(i, j, w, h) paints each screen in local
// coords; o.span: one picture spread across all screens instead (draw(0, 0, totalW, totalH) clipped per screen). o.gap, o.frame colour.
function videoWall(x, y, cols, rows, cw, ch, draw, o = {}) {
  const g = o.gap ?? 10;
  for (let j = 0; j < rows; j++) for (let i = 0; i < cols; i++) {
    const sx = x + i * (cw + g), sy = y + j * (ch + g);
    rrect(sx - 6, sy - 6, cw + 12, ch + 12, 10); paint(o.frame ?? '#1A1A24', EP.line, 2);
    ctx.save(); rrect(sx, sy, cw, ch, 8); ctx.clip(); ctx.fillStyle = '#000'; ctx.fillRect(sx, sy, cw, ch);
    if (o.span) { ctx.translate(x, y); draw(0, 0, cols * (cw + g) - g, rows * (ch + g) - g); } else { ctx.translate(sx, sy); draw(i, j, cw, ch); }
    ctx.restore();
    ctx.save(); rrect(sx, sy, cw, ch, 8); ctx.clip(); ctx.fillStyle = 'rgb(0 0 0 / .18)'; for (let yy = sy; yy < sy + ch; yy += 4) ctx.fillRect(sx, yy, cw, 1.5);
    ctx.fillStyle = rg(sx + cw / 2, sy + ch / 2, ch * .2, cw * .75, [[0, 'rgb(0 0 0 / 0)'], [1, 'rgb(0 0 0 / .5)']]); ctx.fillRect(sx, sy, cw, ch); ctx.restore();
  }
}
// sparkles(t, o): twinkling four-point sparkles. o.n, o.seed, o.x0, o.y0, o.x1, o.y1, o.r, o.col.
function sparkles(t, o = {}) {
  for (let i = 0; i < (o.n ?? 14); i++) { const id = (o.seed ?? 1) * 97 + i, ph = frac(t * (.8 + hash2(id, 1)) + hash2(id, 2)), a = Math.sin(ph * Math.PI); glint(lerp(o.x0 ?? 0, o.x1 ?? W, hash2(id, 3)), lerp(o.y0 ?? 0, o.y1 ?? H, hash2(id, 4)), (o.r ?? 40) * a, a * .9, o.col); }
}
// haze(y, h, col, a): a band of smoke-machine haze.
function haze(y, h, col = '#B8A0FF', a = .18) { ctx.fillStyle = lg(0, y - h / 2, 0, y + h / 2, [[0, alpha(col, 0)], [.5, alpha(col, a)], [1, alpha(col, 0)]]); ctx.fillRect(-900, y - h / 2, W + 1800, h); }
// stageSet(t, o): the chorus stage — a back wall of CRT monitors (or o.wall(w, h) content spanning them), a lighting truss with moving heads and
// laser fans, a floor, haze. Performers stand at y ≈ o.floorY + 120..260. o.floorY (default 690), o.floor ('checker'|'disco'|'grid'), o.level (1..4 more
// rig), o.hue (accent), o.lasers (count of fans), o.wall (fn(w, h) picture across the video wall), o.wallK (0..1 brightness).
function stageSet(t, o = {}) {
  const fy = o.floorY ?? 690, lv = o.level ?? 1, hue = o.hue ?? EP.magenta, b = bpOf(t), k = kick(t, 6);
  bgGrad([[0, '#05020E'], [.7, '#120838'], [1, '#2A0E5A']], { y1: fy });
  const cols = 6 + lv, rows = 3, cw = 1500 / cols - 10, ch = (fy - 170) / rows - 10;
  ctx.save(); ctx.globalAlpha = o.wallK ?? 1;
  videoWall(W / 2 - 750, 120, cols, rows, cw, ch, o.wall ? (x0, y0, w, h) => o.wall(w, h) : (i, j, w, h) => { bgGrad([[0, (i + j + beatN(t)) % 2 ? hue : EP.uv], [1, EP.night]], { y1: h }); ptext('hype', w / 2, h / 2, h * .34, { font: 'rammetto', fill: alpha(EP.white, .85), maxW: w * .8 }); }, { span: !!o.wall });
  ctx.restore();
  // truss + moving heads
  ctx.fillStyle = '#1C1A2A'; ctx.fillRect(-900, 40, W + 1800, 34); ctx.strokeStyle = '#3E3A5A'; ctx.lineWidth = 3; ctx.beginPath(); for (let x = -900; x < W + 900; x += 40) { ctx.moveTo(x, 40); ctx.lineTo(x + 20, 74); ctx.lineTo(x + 40, 40); } ctx.stroke();
  const nb = 4 + lv * 2;
  for (let i = 0; i < nb; i++) {
    const x = lerp(90, W - 90, i / (nb - 1)), sd = i < nb / 2 ? 1 : -1, a = Math.PI / 2 - sd * (.25 + .22 * Math.sin(b * Math.PI / 4 + i)) + Math.sin(b * Math.PI / 2 + i) * .06;
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; const c = [hue, EP.cyan, EP.violet][i % 3], L = 1300;
    ctx.fillStyle = lg(x, 70, x + Math.cos(a) * L, 70 + Math.sin(a) * L, [[0, alpha(c, .32 + .25 * k)], [1, alpha(c, 0)]]);
    ctx.beginPath(); ctx.moveTo(x - 10, 70); ctx.lineTo(x + Math.cos(a - .09) * L, 70 + Math.sin(a - .09) * L); ctx.lineTo(x + Math.cos(a + .09) * L, 70 + Math.sin(a + .09) * L); ctx.lineTo(x + 10, 70); ctx.closePath(); ctx.fill(); ctx.restore();
    rrect(x - 17, 62, 34, 28, 6); paint('#12101E', EP.line, 2);
  }
  // floor
  if ((o.floor ?? 'disco') === 'checker') checkerFloor(t, { horizon: fy, a: '#E8E8F4', b: '#221650', speed: 0, fog: hue, fogH: 90 });
  else if (o.floor === 'grid') { bgGrad([[0, '#1A0A40'], [1, '#05020E']], { y0: fy }); ctx.save(); ctx.beginPath(); ctx.rect(-900, fy, W + 1800, H); ctx.clip(); ctx.strokeStyle = alpha(hue, .7); ctx.lineWidth = 3; ctx.beginPath(); for (let i = -20; i <= 20; i++) { ctx.moveTo(W / 2 + i * 60, fy); ctx.lineTo(W / 2 + i * 330, H + 300); } for (let j = 0; j < 9; j++) { const yy = fy + (H - fy) * ((j + frac(b * .5)) / 9) ** 1.8; ctx.moveTo(-900, yy); ctx.lineTo(W + 900, yy); } ctx.stroke(); ctx.restore(); }
  else { // the light-up disco floor: tiles in perspective toward a vanishing point above the floor line, lit in patterns on the beat
    ctx.save(); ctx.beginPath(); ctx.rect(-900, fy, W + 1800, H + 900); ctx.clip(); fillAll('#0A0618');
    const vy = fy - 520, nr = 7, tw0 = 170, sc = y => (y - vy) / (fy - vy), ys = j => fy + (H + 80 - fy) * (j / nr) ** 1.35;
    for (let j = 0; j < nr; j++) {
      const yA = ys(j), yB = ys(j + 1), sA = sc(yA), sB = sc(yB);
      for (let i = -12; i < 12; i++) {
        const lit = hash2(i * 7 + j * 31, beatN(t)) < .42, c = [hue, EP.cyan, EP.yellow, EP.lime, EP.uv][((i + j) % 5 + 5) % 5];
        const g = 5; ctx.fillStyle = lit ? alpha(c, .7 + .3 * k) : '#1C1434';
        ctx.beginPath(); ctx.moveTo(W / 2 + i * tw0 * sA + g, yA + g * .5); ctx.lineTo(W / 2 + (i + 1) * tw0 * sA - g, yA + g * .5); ctx.lineTo(W / 2 + (i + 1) * tw0 * sB - g, yB - g * .5); ctx.lineTo(W / 2 + i * tw0 * sB + g, yB - g * .5); ctx.closePath(); ctx.fill();
      }
    }
    ctx.fillStyle = lg(0, fy, 0, fy + 90, [[0, alpha(hue, .45)], [1, alpha(hue, 0)]]); ctx.fillRect(-900, fy, W + 1800, 90);
    ctx.restore();
  }
  haze(fy - 20, 260, '#C0A0FF', .14);
  const nl = o.lasers ?? lv;
  for (let i = 0; i < nl; i++) laserFan(lerp(260, W - 260, nl === 1 ? .5 : i / (nl - 1)), 90, t, { n: 7, col: [EP.laser, EP.cyan, hue][i % 3], angle: Math.PI / 2, spread: 1.1, sweep: .5, phase: i, alpha: .55 });
}

// =====================================================================================================
// WINDOWS 98 — the CD-ROM desktop vocabulary (drawn at 2× the real size so it reads on video).
// =====================================================================================================
// bevel(x, y, w, h, o): the classic raised (or o.sunken) 3D edge.
function bevel(x, y, w, h, o = {}) {
  const lt = o.sunken ? '#808080' : '#FFFFFF', dk = o.sunken ? '#FFFFFF' : '#000000', md = o.sunken ? '#404040' : '#808080', b = o.b ?? 2;
  ctx.fillStyle = o.fill ?? EP.w98; ctx.fillRect(x, y, w, h);
  ctx.fillStyle = lt; ctx.fillRect(x, y, w, b); ctx.fillRect(x, y, b, h);
  ctx.fillStyle = dk; ctx.fillRect(x, y + h - b, w, b); ctx.fillRect(x + w - b, y, b, h);
  ctx.fillStyle = md; ctx.fillRect(x + b, y + h - b * 2, w - b * 2, b); ctx.fillRect(x + w - b * 2, y + b, b, h - b * 2);
}
// win98Window(x, y, w, h, title, draw, o): a window with its blue title bar. draw(cw, ch) paints the client area in local coords (clipped).
// o.icon (an icon98 kind for the title), o.inactive, o.menu (['File', 'Edit', …]), o.client (colour, default white), o.k (0..1 pop-in zoom).
// Returns the client rect [x, y, w, h].
function win98Window(x, y, w, h, title, draw, o = {}) {
  const k = o.k ?? 1; if (k <= 0) return null;
  ctx.save(); if (k < 1) { const s = lerp(.2, 1, easeOut(k)); ctx.translate(x + w / 2, y + h / 2); ctx.scale(s, s); ctx.translate(-(x + w / 2), -(y + h / 2)); }
  ctx.fillStyle = 'rgb(0 0 0 / .35)'; ctx.fillRect(x + 10, y + 12, w, h);
  bevel(x, y, w, h, { b: 3 });
  const tb = o.titleH ?? 44, tx = x + 7, ty = y + 7, tw = w - 14;
  ctx.fillStyle = o.inactive ? lg(tx, 0, tx + tw, 0, [[0, '#808080'], [1, '#C0C0C0']]) : lg(tx, 0, tx + tw, 0, [[0, EP.w98navy], [1, EP.w98blue]]); ctx.fillRect(tx, ty, tw, tb);
  let lx = tx + 10; if (o.icon) { icon98(o.icon, tx + 24, ty + tb / 2, .38); lx += 34; }
  txt(title, lx, ty + tb / 2 + 1, tb * .56, o.inactive ? '#D8D8D8' : '#FFFFFF', { font: 'archivo', align: 'left', maxW: tw - 170 });
  ['_', '□', 'x'].forEach((c, i) => { const bx = tx + tw - (3 - i) * (tb * .78 + 3) - 2, by = ty + 5; bevel(bx, by, tb * .78, tb - 10, { b: 2 }); if (c === '_') ctx.fillRect(bx + tb * .22, by + tb - 21, tb * .32, 4); else if (c === '□') { ctx.strokeStyle = '#000'; ctx.lineWidth = 2; ctx.strokeRect(bx + tb * .2, by + 7, tb * .38, tb * .42); ctx.fillStyle = '#000'; ctx.fillRect(bx + tb * .2, by + 7, tb * .38, 4); } else { ctx.strokeStyle = '#000'; ctx.lineWidth = 4; ctx.beginPath(); ctx.moveTo(bx + tb * .24, by + 8); ctx.lineTo(bx + tb * .54, by + tb - 18); ctx.moveTo(bx + tb * .54, by + 8); ctx.lineTo(bx + tb * .24, by + tb - 18); ctx.stroke(); } });
  let cy = ty + tb + 4;
  if (o.menu) { let mx = tx + 12; for (const m of o.menu) { txt(m, mx, cy + 16, 24, '#000', { font: 'archivo', align: 'left' }); mx += textW(m, 24, 'archivo') + 30; } cy += 36; }
  const cr = [tx + 2, cy + 2, tw - 4, y + h - 9 - cy - 2];
  bevel(cr[0] - 2, cr[1] - 2, cr[2] + 4, cr[3] + 4, { sunken: true, fill: o.client ?? '#FFFFFF' });
  if (draw) { ctx.save(); ctx.beginPath(); ctx.rect(cr[0], cr[1], cr[2], cr[3]); ctx.clip(); ctx.translate(cr[0], cr[1]); draw(cr[2], cr[3]); ctx.restore(); }
  ctx.restore();
  return cr;
}
// win98Button(label, x, y, w, h, o): o.pressed, o.focus (dotted focus rectangle), o.def (default button's black border), o.size.
function win98Button(label, x, y, w, h, o = {}) {
  if (o.def) { ctx.fillStyle = '#000'; ctx.fillRect(x - 3, y - 3, w + 6, h + 6); }
  bevel(x, y, w, h, { sunken: !!o.pressed, b: 3 });
  const d = o.pressed ? 3 : 0; txt(label, x + w / 2 + d, y + h / 2 + 2 + d, o.size ?? h * .46, '#000', { font: 'archivo', maxW: w - 16 });
  if (o.focus) { ctx.strokeStyle = '#000'; ctx.lineWidth = 2; ctx.setLineDash([3, 3]); ctx.strokeRect(x + 9 + d, y + 8 + d, w - 18, h - 16); ctx.setLineDash([]); }
}
// win98Dialog(x, y, w, title, msg, o): a message box centred on (x, y). o.icon ('warn'|'error'|'info'|'question'), o.buttons (['OK']),
// o.pressed (index), o.k (pop 0..1), o.size (message px). msg may contain \n. Returns { buttons: [[x, y, w, h]…] } for cursor targets.
function win98Dialog(x, y, w, title, msg, o = {}) {
  const lines = String(msg).split('\n'), size = o.size ?? 32, bh = 56, h = 44 + 30 + Math.max(100, lines.length * size * 1.3 + 30) + bh + 40, x0 = x - w / 2, y0 = y - h / 2, btns = o.buttons ?? ['OK'];
  const out = { buttons: [] };
  win98Window(x0, y0, w, h, title, null, { k: o.k, client: EP.w98 });
  if ((o.k ?? 1) <= 0) return out;
  ctx.save(); const k = o.k ?? 1; if (k < 1) { const s = lerp(.2, 1, easeOut(k)); ctx.translate(x, y); ctx.scale(s, s); ctx.translate(-x, -y); }
  const cy0 = y0 + 44 + 30;
  if (o.icon) icon98(o.icon, x0 + 70, cy0 + 50, 1);
  lines.forEach((l, i) => txt(l, x0 + (o.icon ? 130 : 40), cy0 + 30 + i * size * 1.3, size, '#000', { font: 'archivo', align: 'left', maxW: w - (o.icon ? 170 : 80) }));
  const bw = o.bw ?? 170, gap = 24, tot = btns.length * bw + (btns.length - 1) * gap, by = y0 + h - bh - 30;
  btns.forEach((b, i) => { const bx = x - tot / 2 + i * (bw + gap); win98Button(b, bx, by, bw, bh, { pressed: o.pressed === i, focus: i === (o.focus ?? 0), def: i === (o.focus ?? 0) }); out.buttons.push([bx, by, bw, bh]); });
  ctx.restore();
  return out;
}
// progress98(x, y, w, h, k): a sunken progress bar filling with the blue blocks.
function progress98(x, y, w, h, k) {
  bevel(x, y, w, h, { sunken: true, fill: '#FFFFFF' });
  const bw = h * .6, n = Math.floor((w - 8) * clamp(k) / (bw + 3)); ctx.fillStyle = EP.w98navy;
  for (let i = 0; i < n; i++) ctx.fillRect(x + 4 + i * (bw + 3), y + 4, bw, h - 8);
}
// cursor98(x, y, o): the mouse pointer with its tip at (x, y). o.kind ('arrow'|'hand'|'wait'), o.s (scale), o.click (0..1: a click ring).
function cursor98(x, y, o = {}) {
  const s = o.s ?? 2.2, kind = o.kind ?? 'arrow';
  if (o.click > 0 && o.click < 1) { ctx.strokeStyle = `rgb(255 255 255 / ${1 - o.click})`; ctx.lineWidth = 4; ell(x, y, 10 + o.click * 50, 10 + o.click * 50); ctx.stroke(); }
  ctx.save(); ctx.translate(x, y); ctx.scale(s, s); ctx.lineJoin = 'miter';
  if (kind === 'wait') { poly([[-6, 0], [6, 0], [6, 3], [1.5, 9], [6, 15], [6, 18], [-6, 18], [-6, 15], [-1.5, 9], [-6, 3]]); paint('#FFFFFF', '#000', 1.2); ctx.fillStyle = '#000'; poly([[-3.5, 3], [3.5, 3], [0, 7.5]]); ctx.fill(); poly([[-3.5, 16], [3.5, 16], [0, 12.5]]); ctx.fill(); }
  else if (kind === 'hand') { poly([[0, 0], [2.5, 0], [2.5, 7], [5, 7], [5, 8.5], [7.5, 8.5], [7.5, 10], [10, 10], [10, 17], [8, 21], [1, 21], [-3, 14], [-3, 11], [0, 11]]); paint('#FFFFFF', '#000', 1.2); }
  else { poly([[0, 0], [0, 17], [4, 13], [7, 20], [9.5, 19], [6.5, 12], [12, 12]]); paint('#FFFFFF', '#000', 1.3); }
  ctx.restore();
}
// icon98(kind, x, y, s, o): a desktop icon centred on (x, y) (≈ 64s px). kinds: computer|bin|binFull|folder|doc|exe|cd|globe|warn|error|info|question|mail|disk.
// o.label (text under it, white on the desktop), o.sel (selected: navy label box), o.labelCol.
function icon98(kind, x, y, s = 1, o = {}) {
  ctx.save(); ctx.translate(x, y); ctx.scale(s, s); ctx.lineJoin = 'round';
  const K = '#000';
  switch (kind) {
    case 'computer': rrect(-26, -28, 52, 40, 3); paint('#D8D0B8', K, 2); rrect(-19, -22, 38, 27, 2); paint('#008080', K, 2); rrect(-30, 16, 60, 12, 2); paint('#D8D0B8', K, 2); ctx.fillStyle = '#3BFF4A'; ctx.fillRect(18, 20, 6, 3); break;
    case 'bin': case 'binFull': poly([[-20, -18], [20, -18], [15, 28], [-15, 28]]); paint('#E8ECF0', K, 2); ctx.strokeStyle = '#7A8A9A'; ctx.lineWidth = 2; for (const dx of [-8, 0, 8]) { ctx.beginPath(); ctx.moveTo(dx, -12); ctx.lineTo(dx * .8, 24); ctx.stroke(); } rrect(-23, -24, 46, 8, 2); paint('#C8D0D8', K, 2); if (kind === 'binFull') { for (const [dx, dy, c] of [[-10, -32, '#FFF'], [6, -34, '#FFE890'], [-2, -40, '#E0F0FF']]) { poly([[dx - 9, dy + 8], [dx + 9, dy + 4], [dx + 7, dy - 8], [dx - 8, dy - 5]]); paint(c, K, 1.5); } } break;
    case 'folder': poly([[-28, -18], [-10, -18], [-6, -12], [28, -12], [28, 22], [-28, 22]]); paint('#F4D46A', K, 2); poly([[-28, -6], [28, -6], [28, 22], [-28, 22]]); paint('#FFE48A', K, 2); break;
    case 'doc': poly([[-20, -28], [10, -28], [20, -18], [20, 28], [-20, 28]]); paint('#FFFFFF', K, 2); ctx.fillStyle = '#7A7A8A'; for (let i = 0; i < 5; i++) ctx.fillRect(-13, -14 + i * 8, i === 4 ? 16 : 26, 3); break;
    case 'exe': rrect(-26, -22, 52, 44, 2); paint('#FFFFFF', K, 2); ctx.fillStyle = EP.w98navy; ctx.fillRect(-25, -21, 50, 10); break;
    case 'cd': cdDisc(0, 0, 26, T, {}); break;
    case 'globe': glossBall(0, 0, 26, 26, '#2A7AE8', { lw: 2, line: K, rim: null }); ctx.strokeStyle = '#8AD8FF'; ctx.lineWidth = 2; ell(0, 0, 12, 26); ctx.stroke(); ctx.beginPath(); ctx.moveTo(-26, 0); ctx.lineTo(26, 0); ctx.stroke(); ctx.fillStyle = '#3ACA5A'; ell(-8, -8, 8, 6, .4); ctx.fill(); ell(10, 8, 7, 9, -.3); ctx.fill(); break;
    case 'warn': poly([[0, -28], [30, 26], [-30, 26]]); paint('#FFE81F', K, 2.5); ctx.fillStyle = K; ctx.fillRect(-3.5, -12, 7, 22); ctx.fillRect(-3.5, 14, 7, 7); break;
    case 'error': ell(0, 0, 28, 28); paint('#E0201A', K, 2); ctx.strokeStyle = '#FFF'; ctx.lineWidth = 7; ctx.beginPath(); ctx.moveTo(-11, -11); ctx.lineTo(11, 11); ctx.moveTo(11, -11); ctx.lineTo(-11, 11); ctx.stroke(); break;
    case 'info': case 'question': ell(0, 0, 28, 28); paint('#FFFFFF', K, 2); txt(kind === 'info' ? 'i' : '?', 0, 3, 40, '#1A3AE0', { font: 'abril' }); break;
    case 'mail': rrect(-28, -18, 56, 36, 3); paint('#FFFFFF', K, 2); ctx.beginPath(); ctx.moveTo(-28, -18); ctx.lineTo(0, 4); ctx.lineTo(28, -18); ctx.strokeStyle = K; ctx.lineWidth = 2; ctx.stroke(); break;
    case 'disk': rrect(-24, -24, 48, 48, 3); paint('#2A2A34', K, 2); ctx.fillStyle = '#C8CCD8'; ctx.fillRect(-12, -24, 24, 16); ctx.fillStyle = '#FFFFFF'; ctx.fillRect(-16, 4, 32, 18); break;
  }
  ctx.restore();
  if (o.label) { const lw = textW(o.label, 22 * s * 1.2, 'archivo') + 12; if (o.sel) { ctx.fillStyle = EP.w98navy; ctx.fillRect(x - lw / 2, y + 40 * s, lw, 30 * s); } txt(o.label, x, y + 40 * s + 15 * s, 22 * s * 1.2, o.labelCol ?? '#FFFFFF', { font: 'archivo', shadow: o.sel ? false : [2, 2], shadowCol: 'rgb(0 0 0 / .6)' }); }
}
// desktop98(o): the teal desktop. o.icons ([[kind, label, x, y]…]), o.col, o.taskbar ('top' | false; a bottom taskbar would sit under the karaoke).
function desktop98(o = {}) {
  fillAll(o.col ?? EP.w98teal);
  for (const [kind, label, x, y, sel] of o.icons ?? []) icon98(kind, x, y, 1.1, { label, sel });
  if (o.taskbar === 'top') { bevel(-10, -4, W + 20, 60, { b: 3 }); bevel(10, 6, 150, 42, { b: 3 }); txt('Start', 85, 28, 26, '#000', { font: 'archivo' }); }
}

// =====================================================================================================
// OVERLAYS — per-frame switches a shot may call (they reset after every frame):
//   hideCaption()   no karaoke subtitle         captionStyle({ y, size, singer: 'token'|'softmax' })
//   hideStamp()     no date cube                hideBug()   no channel bug
//   fx({ flash, rgb, zoom, invert, strobe })     beat effects on the finished frame (k 0..1 each; invert: true)
//   cutFX('none'|'flash'|'rgb'|'zoom')           override this frame's automatic cut effect      setBloom(k)   (default .5, 0 = off)
// =====================================================================================================
let _fxO = null, _cutO = undefined, _noBug = false, _bloom = null;
const hideBug = () => { _noBug = true; };
const fx = o => { _fxO = Object.assign(_fxO || {}, o); };
const cutFX = kind => { _cutO = kind; };
const setBloom = k => { _bloom = k; };
const _bufs = new Map();
function _buf(key, w = canvas.width, h = canvas.height) { let c = _bufs.get(key); if (!c || c.width !== w || c.height !== h) { c = makeCanvas(w, h); c.g = c.getContext('2d', { willReadFrequently: key === 'bl1' }); _bufs.set(key, c); } return c; }
function _grab(key = 'grab') { const c = _buf(key); c.g.globalCompositeOperation = 'copy'; c.g.drawImage(canvas, 0, 0); c.g.globalCompositeOperation = 'source-over'; return c; }
function _rgbSplit(k) {
  if (k <= 0) return; const cw = canvas.width, ch = canvas.height, d = Math.round(18 * k * cw / W), A = _buf('rgbA'), B = _buf('rgbB');
  for (const [c, col] of [[A, '#FF0000'], [B, '#00FFFF']]) { c.g.globalCompositeOperation = 'copy'; c.g.drawImage(canvas, 0, 0); c.g.globalCompositeOperation = 'multiply'; c.g.fillStyle = col; c.g.fillRect(0, 0, cw, ch); }
  ctx.save(); ctx.setTransform(1, 0, 0, 1, 0, 0); ctx.globalCompositeOperation = 'copy'; ctx.drawImage(B, -d, 0); ctx.globalCompositeOperation = 'lighter'; ctx.drawImage(A, d, 0); ctx.restore();
}
function _zoomPunch(k) { if (k <= 0) return; const cw = canvas.width, ch = canvas.height, G = _grab(), z = .07 * k; ctx.save(); ctx.setTransform(1, 0, 0, 1, 0, 0); ctx.drawImage(G, -cw * z / 2, -ch * z / 2, cw * (1 + z), ch * (1 + z)); ctx.globalAlpha = .35 * k; ctx.drawImage(G, -cw * z, -ch * z, cw * (1 + z * 2), ch * (1 + z * 2)); ctx.restore(); }
function _cutKind(s) { const h = hstr(s.key + '/cut'); return h < .38 ? 'flash' : h < .64 ? 'rgb' : h < .86 ? 'zoom' : 'none'; }
function _cutPass(t, s) {
  let kind = _cutO, k = 0;
  if (s && s.kind === 'line') { const age = t - s.start; if (age < .1) { kind = kind ?? _cutKind(s); k = 1 - age / .1; } }
  if (!kind || kind === 'none' || k <= 0) return;
  if (kind === 'flash') { ctx.save(); ctx.setTransform(1, 0, 0, 1, 0, 0); ctx.fillStyle = `rgb(255 255 255 / ${.55 * k})`; ctx.fillRect(0, 0, canvas.width, canvas.height); ctx.restore(); }
  else if (kind === 'rgb') _rgbSplit(k);
  else if (kind === 'zoom') _zoomPunch(k);
}
// ---------- bloom: threshold at low resolution, blur by down-sampling, add back (strong on dark sets, weak on bright ones) ----------
function _bloomPass(k) {
  if (k <= 0) return;
  const a = _buf('bl1', 240, 135), b = _buf('bl2', 120, 68), c = _buf('bl3', 60, 34);
  a.g.globalCompositeOperation = 'copy'; a.g.imageSmoothingQuality = 'medium'; a.g.drawImage(canvas, 0, 0, 240, 135);
  const img = a.g.getImageData(0, 0, 240, 135), d = img.data, thr = 222; let mean = 0;
  for (let i = 0; i < d.length; i += 4) { const l = d[i] * .3 + d[i + 1] * .59 + d[i + 2] * .11; mean += l; const f = l > thr ? (l - thr) / (255 - thr) : 0; d[i] *= f; d[i + 1] *= f; d[i + 2] *= f; }
  mean /= d.length / 4 * 255; k *= clamp((.7 - mean) / .4); if (k <= .01) return;
  a.g.putImageData(img, 0, 0); b.g.globalCompositeOperation = 'copy'; b.g.drawImage(a, 0, 0, 120, 68); c.g.globalCompositeOperation = 'copy'; c.g.drawImage(b, 0, 0, 60, 34);
  ctx.save(); ctx.setTransform(1, 0, 0, 1, 0, 0); ctx.globalCompositeOperation = 'lighter'; ctx.imageSmoothingQuality = 'high';
  ctx.globalAlpha = .6 * k; ctx.drawImage(b, 0, 0, canvas.width, canvas.height); ctx.globalAlpha = .9 * k; ctx.drawImage(c, 0, 0, canvas.width, canvas.height); ctx.restore();
}
// ---------- the broadcast pass: faint scanlines and a soft vignette (a clean 1998 satellite feed, not a worn tape) ----------
let _scan = null, _vig = null;
function _tvPass() {
  const cw = canvas.width, ch = canvas.height;
  if (!_scan || _scan.rs !== RS) { const P = Math.max(2, Math.round(3 * RS)), c = makeCanvas(4, P), g = c.getContext('2d'); g.fillStyle = 'rgb(0 0 20 / .16)'; g.fillRect(0, 0, 4, Math.max(1, Math.round(RS))); _scan = ctx.createPattern(c, 'repeat'); _scan.rs = RS; }
  if (!_vig) { _vig = makeCanvas(480, 270); const g = _vig.getContext('2d'), gr = g.createRadialGradient(240, 135, 90, 240, 135, 300); gr.addColorStop(0, 'rgb(0 0 0 / 0)'); gr.addColorStop(.75, 'rgb(10 0 30 / .16)'); gr.addColorStop(1, 'rgb(10 0 30 / .5)'); g.fillStyle = gr; g.fillRect(0, 0, 480, 270); }
  ctx.save(); ctx.setTransform(1, 0, 0, 1, 0, 0); ctx.fillStyle = _scan; ctx.fillRect(0, 0, cw, ch); ctx.drawImage(_vig, 0, 0, cw, ch); ctx.restore();
}
// ---------- the channel bug: "hype" with a spinning star, top left, translucent ----------
function channelBug(x = 92, y = 62, a = .8) {
  ctx.save(); ctx.globalAlpha *= a;
  txt('hype', x + 3, y + 5, 64, 'rgb(0 0 0 / .35)', { font: 'rammetto', align: 'left' });
  txt('hype', x, y, 64, '#FFFFFF', { font: 'rammetto', align: 'left' });
  const sx = x + textW('hype', 64, 'rammetto') + 26, k = kick(T, 5);
  ctx.save(); ctx.translate(sx, y - 18); ctx.rotate(T * 1.6); ctx.scale(1 + k * .25, 1 + k * .25); poly(starPts(0, 0, 22, .45, 5)); ctx.fillStyle = '#FFFFFF'; ctx.fill(); ctx.restore();
  txt('TV', sx, y + 18, 20, '#FFFFFF', { font: 'bungee' });
  ctx.restore();
}
// ---------- the date cube: a chrome-framed glass prism top right that rolls to each new date (forward in time: rolls up; back in time: rolls down) ----------
const _MON = ['JAN', 'FEB', 'MAR', 'APR', 'MAY', 'JUN', 'JUL', 'AUG', 'SEP', 'OCT', 'NOV', 'DEC'];
function _dv(s) { const p = String(s).split(' '); let m = _MON.indexOf(p[0]); if (m < 0) m = 6; const d = p.length === 3 ? +p[1] : 15, y = +p[p.length - 1]; return y * 400 + m * 32 + d; }
function dateInfo(t) { let cur = null, prev = null; for (const s of SEGS) { if (s.start > t) break; if (s.date && s.date !== cur?.date) { prev = cur; cur = s; } } return cur ? { text: cur.date, prev: prev?.date ?? null, seg: cur, age: t - cur.start } : null; }
function _dateFace(str, x, y, w, h, lum) {
  if (h < 1) return;
  ctx.save(); ctx.beginPath(); ctx.rect(x, y, w, h); ctx.clip();
  ctx.fillStyle = lg(0, y, 0, y + h, [[0, '#2A3CFF'], [.5, '#0E0A5A'], [1, '#1A1270']]); ctx.fillRect(x, y, w, h);
  ctx.fillStyle = 'rgb(255 255 255 / .14)'; ctx.fillRect(x, y, w, h * .42);
  ctx.translate(0, y + h / 2); ctx.scale(1, h / 88); ctx.translate(0, -(y + h / 2));
  cdDisc(x + 52, y + h / 2, 30, T * 3, { col: EP.magenta, hole: '#0E0A5A' });
  const parts = str.split(' '), yr = parts.pop(), rest = parts.join(' ');
  const sz = 42, wy = textW(yr, sz, 'archivo'), wr = rest ? Math.min(textW(rest + ' ', sz, 'archivo'), w - 120 - wy) : 0, tx = x + 96 + Math.max(0, (w - 110 - wr - wy) / 2);
  if (rest) ptext(rest, tx, y + h / 2, sz, { align: 'left', fill: '#FFFFFF', strokes: [['#05031A', 7]], maxW: wr - textW(' ', sz, 'archivo') });
  ptext(yr, tx + wr, y + h / 2, sz, { align: 'left', fill: EP.yellow, strokes: [['#05031A', 7]] });
  ctx.restore();
  if (lum < 1) { ctx.fillStyle = `rgb(0 0 20 / ${(1 - lum) * .8})`; ctx.fillRect(x, y, w, h); }
}
function _dateCube(t) {
  const d = dateInfo(t); if (!d) return;
  const w = 390, PH = 88, cx = 1692, cy = 90, x = cx - w / 2, r = PH / Math.SQRT2, ROLL = .34;
  const fwd = !d.prev || _dv(d.text) >= _dv(d.prev), u = d.prev && d.age < ROLL ? backOut(clamp(d.age / ROLL), 1.3) : 1;
  // chrome frame
  ctx.save(); ctx.fillStyle = 'rgb(0 0 0 / .35)'; rrect(x - 8, cy - PH / 2 - 6, w + 20, PH + 20, 12); ctx.fill();
  ctx.fillStyle = lg(0, cy - PH / 2 - 10, 0, cy + PH / 2 + 10, [[0, '#F4F8FF'], [.45, '#8A94B0'], [.5, '#3A4058'], [1, '#D8DCEA']]); rrect(x - 10, cy - PH / 2 - 10, w + 20, PH + 20, 12); ctx.fill();
  ctx.strokeStyle = EP.line; ctx.lineWidth = 3; ctx.stroke();
  ctx.fillStyle = '#05031A'; ctx.fillRect(x, cy - PH / 2, w, PH);
  const ang = u >= 1 ? 0 : (fwd ? -1 : 1) * (1 - u) * Math.PI / 2;   // current face's angle (0 = facing us); forward in time rolls up from below
  // current face spans screen-up y ∈ [r sin(ang − 45°), r sin(ang + 45°)]; the previous face sits at ang ± 90°
  const face = (str, a) => { const lo = r * Math.sin(a - Math.PI / 4), hi = r * Math.sin(a + Math.PI / 4); if (hi - lo < 1 || Math.cos(a) <= 0) return; _dateFace(str, x, cy - hi, w, hi - lo, .35 + .65 * Math.cos(a)); };
  face(d.text, ang); if (u < 1 && d.prev) face(d.prev, ang + (fwd ? 1 : -1) * Math.PI / 2);
  ctx.restore();
  if (d.prev && d.age > ROLL * .6 && d.age < ROLL + .45) sweepGlint(x + 20, x + w - 20, cy - 20, (d.age - ROLL * .6) / .45, 70);
  if (!d.prev && d.age < .3) { const k = d.age / .3; ctx.fillStyle = `rgb(255 255 255 / ${.7 * (1 - k)})`; ctx.fillRect(x, cy - PH / 2, w, PH); }
}
// ---------- karaoke: word-timed wipe, a bouncing ball, the singer chip, count-in dots before a section's first line ----------
const SINGER = { token: { name: 'MC TOKEN', col: EP.cyan, ink: '#04122A', grad: ['#E8FFFF', '#5FF4FF', '#12D8FF'] }, softmax: { name: 'SOFTMAX', col: EP.magenta, ink: '#FFFFFF', grad: ['#FFE8F8', '#FF7AD0', '#FF2AA8'] } };
const singerOf = ln => ln && ln.sec && ln.sec[0] === 'V' ? 'token' : 'softmax';
const _kText = s => String(s).replace(/\s*—\s*$/, '').replace(/\s+—\s+/g, ' — ');
const _kNorm = w => String(w).toLowerCase().replace(/[^a-z0-9]/g, '');
function _karaTimes(ln) {
  if (ln._kt) return ln._kt;
  const words = _kText(ln.text).split(' '), src = (typeof KARAOKE_WORDS !== 'undefined' ? KARAOKE_WORDS : []).filter(w => w[0] >= ln.start - .25 && w[0] < ln.end + .05);
  const tm = words.map(() => null); let j = 0;
  words.forEach((w, i) => { const d = _kNorm(w); if (!d) return; for (let q = j; q < Math.min(src.length, j + 4); q++) { const c = _kNorm(src[q][2]); if (c && (c === d || (c.length >= 3 && d.startsWith(c)) || (d.length >= 3 && c.startsWith(d)))) { tm[i] = [src[q][0], src[q][1]]; j = q + 1; break; } } });
  if (!tm[0]) tm[0] = [ln.start, null];
  const L = words.map(w => w.length + 1), cum = []; L.reduce((a, v, i) => (cum[i] = a, a + v), 0);
  const n = words.length; let lastEnd = Math.max(ln.end, (tm.filter(Boolean).at(-1)?.[1]) ?? ln.end);
  for (let i = 0; i < n; i++) if (!tm[i]) { let a = i - 1; while (a >= 0 && !tm[a]) a--; let b = i + 1; while (b < n && !tm[b]) b++; const ta = a >= 0 ? (tm[a][1] ?? tm[a][0] + .2) : ln.start, ca = a >= 0 ? cum[a] + L[a] : 0, tb = b < n ? tm[b][0] : lastEnd, cb = b < n ? cum[b] : cum[n - 1] + L[n - 1]; tm[i] = [lerp(ta, tb, (cum[i] - ca) / Math.max(1, cb - ca)), null]; }
  for (let i = 0; i < n; i++) { if (i && tm[i][0] < tm[i - 1][0]) tm[i][0] = tm[i - 1][0]; const nx = i + 1 < n ? tm[i + 1][0] : lastEnd; tm[i][1] = Math.min(tm[i][1] ?? nx, Math.max(nx, tm[i][0] + .12)); if (tm[i][1] <= tm[i][0]) tm[i][1] = tm[i][0] + .15; }
  return (ln._kt = { words, tm });
}
// karaokeLine(ln, t, o): draw one karaoke line ({ text, start, end, sec }) as it would be sung at t. Shots may call it for lyrics the timeline
// doesn't carry (the intro teaser): karaokeLine({ text, start, end, sec: 'intro' }, t, { singer: 'softmax' }). o.y, o.size, o.singer, o.dots (0..4), o.alpha.
function karaokeLine(ln, t, o = {}) {
  const S = SINGER[o.singer ?? singerOf(ln)], text = _kText(ln.text), { words, tm } = _karaTimes(ln);
  const y = o.y ?? 1012, font = 'archivo', cs = 22, chip = S.name, cw = textW(chip, cs, 'bungee') + 34;
  let size = o.size ?? 50; const maxW = 1560 - cw; let tw = textW(text, size, font, 1); if (tw > maxW) { size *= maxW / tw; tw = maxW; }
  const x0 = W / 2 - (cw + 24 + tw) / 2, tx = x0 + cw + 24;
  // word x-extents
  const key = `${text}|${size.toFixed(2)}`; if (ln._kx?.key !== key) { const xs = []; let acc = ''; for (const w of words) { const a = textW(acc, size, font, 1), b = textW(acc + w, size, font, 1); xs.push([a, b]); acc += w + ' '; } ln._kx = { key, xs }; }
  const xs = ln._kx.xs;
  let prog = 0, wi = -1;
  for (let i = 0; i < words.length; i++) { const [s0, s1] = tm[i]; if (t >= s0) { wi = i; prog = t >= s1 ? xs[i][1] : lerp(xs[i][0], xs[i][1], (t - s0) / (s1 - s0)); } }
  ctx.save(); if (o.alpha !== undefined) ctx.globalAlpha *= o.alpha;
  // chip
  rrect(x0, y - 21, cw, 42, 21); ctx.fillStyle = S.col; ctx.fill(); ctx.strokeStyle = '#05031A'; ctx.lineWidth = 5; ctx.stroke(); ctx.strokeStyle = '#FFFFFF'; ctx.lineWidth = 2; ctx.stroke();
  txt(chip, x0 + cw / 2, y + 2, cs, S.ink, { font: 'bungee' });
  // count-in dots
  if (o.dots) for (let i = 0; i < 4; i++) { const on = i < o.dots; ell(x0 + 12 + i * 26, y - 44, 9, 9); paint(on ? S.col : 'rgb(255 255 255 / .2)', '#05031A', 3); }
  // text: unsung white with a dark edge; the sung part fills with the singer's gradient
  const base = { align: 'left', spacing: 1, strokes: [['#05031A', size * .28], ['#26206A', size * .12]], shadow: [0, size * .07, 'rgb(0 0 20 / .5)'] };
  ptext(text, tx, y, size, { ...base, fill: '#FFFFFF' });
  if (prog > 0) { ctx.save(); ctx.beginPath(); ctx.rect(tx - 10, y - size, prog + 10, size * 2); ctx.clip(); ptext(text, tx, y, size, { align: 'left', spacing: 1, strokes: [['#05031A', size * .28]], grad: S.grad }); ctx.restore(); }
  // the bouncing ball
  const ctr = i => tx + (xs[i][0] + xs[i][1]) / 2, by = y - size * .78;
  let bx, bh;
  if (wi < 0) { bx = ctr(0); bh = Math.abs(Math.sin(bpOf(t) * Math.PI)) * 30; }
  else if (wi < words.length - 1) { const s0 = tm[wi][0], s1 = tm[wi + 1][0], u = clamp((t - s0) / Math.max(.05, s1 - s0)); bx = lerp(ctr(wi), ctr(wi + 1), u); bh = Math.sin(u * Math.PI) * Math.min(46, 16 + (s1 - s0) * 60); }
  else { const u = clamp((t - tm[wi][0]) / .35); bx = ctr(wi) + u * 30; bh = Math.sin(clamp(u) * Math.PI) * 20; }
  const fade = wi >= words.length - 1 ? 1 - clamp((t - tm[words.length - 1][1]) / .3) : 1;
  if (fade > 0) { ctx.globalAlpha *= fade; ctx.fillStyle = 'rgb(0 0 20 / .35)'; ell(bx, by + 12, 12, 4); ctx.fill(); glossBall(bx, by - bh, 12, 12 * (bh < 3 ? .8 : 1), S.col, { lw: 2.5, rim: null }); }
  ctx.restore();
}
function _karaoke(t) {
  if (_noCaption) return;
  const st = _captionStyle || {}, beat = beatLen();
  let cur = null, dots = 0;
  for (let i = 0; i < LINES.length; i++) {
    const ln = LINES[i], prev = LINES[i - 1], next = LINES[i + 1], gap = prev ? ln.start - prev.end : 99, pre = gap > 1.8 ? Math.min(4 * beat, gap - .4) : Math.max(0, Math.min(gap, .05));
    const show0 = ln.start - pre, show1 = next && next.start - ln.end < 1.8 ? next.start - Math.max(0, Math.min(next.start - ln.end, .05)) : ln.end + .5;
    if (t >= show0 && t < show1) { cur = ln; if (gap > 1.8 && t < ln.start) dots = Math.min(4, Math.ceil((ln.start - t) / beat)); break; }
  }
  if (!cur) return;
  const next = LINES[LINES.indexOf(cur) + 1], out = !next || next.start - cur.end >= 1.8 ? clamp((cur.end + .5 - t) / .25) : 1;
  const inA = clamp((t - (cur.start - (dots ? 4 * beat : .05))) / .12);
  karaokeLine(cur, t, { y: st.y, size: st.size, singer: st.singer, dots, alpha: Math.min(out, Math.max(inA, dots ? 1 : inA)) });
}

OVERLAYS.push((t, s) => {
  try {
    ctx.save(); _cutPass(t, s);
    const f = _fxO || {};
    if (f.zoom) _zoomPunch(f.zoom);
    if (f.rgb) _rgbSplit(f.rgb);
    if (f.invert) { ctx.save(); ctx.setTransform(1, 0, 0, 1, 0, 0); ctx.globalCompositeOperation = 'difference'; ctx.fillStyle = '#FFFFFF'; ctx.fillRect(0, 0, canvas.width, canvas.height); ctx.restore(); }
    if (f.flash) { ctx.save(); ctx.setTransform(1, 0, 0, 1, 0, 0); ctx.fillStyle = `rgb(255 255 255 / ${clamp(f.flash)})`; ctx.fillRect(0, 0, canvas.width, canvas.height); ctx.restore(); }
    _bloomPass(_bloom ?? .5);
    ctx.restore();
    ctx.save(); ctx.setTransform(RS, 0, 0, RS, 0, 0);
    if (!_noBug) channelBug();
    if (!_noStamp) _dateCube(t);
    _karaoke(t);
    ctx.restore();
    ctx.save(); _tvPass(); ctx.restore();
  } finally {
    _noCaption = false; _noStamp = false; _captionStyle = null; _noBug = false; _fxO = null; _cutO = undefined; _bloom = null; LIGHT = { ...LIGHT0 };
  }
});

;
// ---- styles/eurodance/ch/c01_intro.js ----
// c01_intro — Intro (0 → V1.1, 69 beats): HYPE TV airs the video. Sub-shots follow the take's own beat grid (bpOf), because the
// arrangement does: a pad swell, the diva's a-cappella teaser over the piano (b4–b37: "We didn't start the scaling, oh / we didn't start the
// scaling, no / no, we didn't preordain it, but we can't contain it!"), a hit on b37, a synth lead (b44–b52), the stab build (b52–b64), a breath.
//   b0–b4    HYPE TV channel ident: a ring tunnel, the chrome "hype" logo spins in from depth, lens flare, NON-STOP HITS
//   b4–b16   the title: WE / DIDN'T / START land on the beats, THE SCALING slams on b8–b9; the trio rises on chrome podiums (the poster frame)
//   b16–b28  SOFTMAX on a turning podium in the blue CGI sky, wind machine, laser fans opening; the music-channel credit block
//   b28–b37  "No, we didn't preordain it" close-up finger wag → "but we can't contain it!" the stage, the curve bursts off the video wall
//   b37–b44  DJ CLAWD at the decks (scratching on the beats), chrome name
//   b44–b52  MC TOKEN doing the running man in a tunnel, chrome name
//   b52–b64  the build: laser fans switch on one per stab, the tunnel accelerates, strobes on the eighths, 3 · 2 · 1
//   b64–b69  black; a spotlight snaps onto MC TOKEN, cap flip, mic up; the karaoke count-in dots for "First, …"
(() => {
  const B = n => onBeat(0, n);
  const kickAt = (b, n, dur = .5) => { const k = (b - n) / dur; return k >= 0 && k < 1 ? 1 - k : 0; };
  const sing = (t, ph = 0) => clamp(.25 + .75 * Math.abs(Math.sin((bpOf(t) + ph) * Math.PI * 1.5)) * (.55 + .45 * Math.sin(t * 11 + ph)));
  // a chunky CGI cloud: glossy puffs over a flat bottom
  const cloud = (x, y, s) => { ctx.save(); ctx.beginPath(); ctx.rect(x - s * 3, y - s * 3, s * 6, s * 3.35); ctx.clip(); for (const [dx, dy, r] of [[-1.25, .1, .6], [1.25, .12, .62], [-.5, -.25, .85], [.4, -.4, 1.0]]) glossBall(x + dx * s, y + dy * s, r * s, r * s * .92, '#E4EFFF', { line: false, rim: '#FFB0E8', rimK: .55, spec: .5 }); ctx.restore(); };
  const sky = (t, top = '#0A0A6A', mid = EP.ultra, low = '#FF6FC8') => { bgGrad([[0, top], [.55, mid], [1, low]], { y1: 700 }); for (let i = 0; i < 60; i++) { const a = .3 + .7 * Math.abs(Math.sin(t * (1 + hash2(i, 3) * 3) + i)); ctx.fillStyle = `rgb(255 255 255 / ${.5 * a * hash2(i, 4)})`; ctx.fillRect(hash2(i, 1) * W, hash2(i, 2) * 480, 3, 3); } };

  // ---------- b0–b4: the channel ident ----------
  function ident(t, b) {
    hideBug(); hideCaption();
    fillAll('#000');
    const on = clamp((b + .4) / 1.2);
    ctx.save(); ctx.globalAlpha = on; tunnel(t, { speed: 1 + b * .8, cols: [EP.magenta, EP.cyan, EP.uv], shape: 'ring', width: 50, bg: false }); ctx.restore();
    const k = easeOut(clamp((b - .3) / 1.8)), spin = (1 - k) * Math.PI * 3;
    if (k > 0) {
      const s = lerp(.05, 1, k);
      glow(W / 2, 470, 520 * k, EP.magenta, .6 * k);
      chromeText('hype', W / 2, 470, 260, { font: 'rammetto', style: 'chrome', italic: .08, depth: 22, s, sx: Math.cos(spin), alpha: clamp(k * 2) });
      ctx.save(); ctx.translate(W / 2 + 420 * s, 330 + (1 - s) * 140); ctx.rotate(t * 2.5); ctx.scale(s, s); poly(starPts(0, 0, 70, .45, 5)); ctx.fillStyle = lg(0, -70, 0, 70, [[0, '#FFFFFF'], [.5, EP.yellow], [1, EP.orange]]); ctx.fill(); ctx.strokeStyle = EP.line; ctx.lineWidth = 6; ctx.stroke(); ctx.restore();
    }
    if (b > 2.2) { const n = Math.floor(clamp((b - 2.2) / 1.2) * 13); pixText('NON-STOP HITS'.slice(0, n), W / 2, 680, 9, EP.cyan, { align: 'center', glow: true }); }
    lensFlare(lerp(-200, W + 300, clamp((b - 1.6) / 2)), 300, .9 * Math.sin(clamp((b - 1.6) / 2) * Math.PI));
    if (b > 3.7) strobe((b - 3.7) / .3 * .9);
  }

  // ---------- b4–b16: the title card ----------
  const L1 = [["WE", 4], ["DIDN'T", 5], ["START", 6]], L2 = [["THE", 8], ["SCALING", 9]];
  // the trio's podium positions; the poster page (modelsheet.js, t = −999) swaps SOFTMAX and DJ CLAWD (and moves the flare
  // off her) so the page's Play button covers sky
  const TRIO_X = { token: 500, softmax: 960, clawd: 1420, flare: 1590 };
  globalThis.EURO_TRIO_X = TRIO_X;
  function titleWords(t, b, lift = 0) {
    const s1 = 150, s2 = 205, gap = 40;
    const w1 = L1.map(([w]) => textW(w, s1, 'archivo')), tot1 = w1.reduce((a, v) => a + v, 0) + gap * 2;
    let x = W / 2 - tot1 / 2;
    L1.forEach(([w, n], i) => { const k = clamp((b - n) / .35); if (k > 0) chromeText(w, x + w1[i] / 2, 212 - lift, s1, { style: 'chrome', italic: .14, depth: 14, s: lerp(2.6, 1, easeOut(k)), alpha: clamp(k * 3) }); x += w1[i] + gap; });
    const w2 = L2.map(([w]) => textW(w, s2, 'archivo')), tot2 = w2.reduce((a, v) => a + v, 0) + gap;
    x = W / 2 - tot2 / 2;
    L2.forEach(([w, n], i) => { const k = clamp((b - n) / .3); if (k > 0) chromeText(w, x + w2[i] / 2, 396 - lift - kick(t, 6) * 6, s2, { style: i ? 'hot' : 'gold', italic: .14, depth: 20, s: lerp(3.2, 1, backOut(k, 1.3)), alpha: clamp(k * 3) }); x += w2[i] + gap; });
    if (b > 9.3) { sweepGlint(W / 2 - tot2 / 2, W / 2 + tot2 / 2, 366 - lift, (b - 9.6) / 1.4, 150); sweepGlint(W / 2 - tot1 / 2, W / 2 + tot1 / 2, 192 - lift, (b - 12) / 1.3, 110); }
    glint(W / 2 + tot2 / 2 - 60, 316 - lift, 110 * kick(t, 4), kick(t, 4) * (b > 9 ? 1 : 0));
  }
  function title(t, b) {
    hideCaption();
    const sh = b > 9 && b < 9.6 ? shakeXY(t, 22 * (1 - (b - 9) / .6)) : [0, 0];
    camBegin(W / 2 - sh[0], H / 2 - sh[1], 1 + (b - 4) * .006);
    sky(t, '#05052A', '#2A1A9A', '#FF4FA8');
    // the CGI sun and its flare, floating chrome toys
    glow(W / 2, 640, 700, '#FF6FC8', .55);
    checkerFloor(t, { horizon: 640, a: '#F2F0FF', b: '#2A1466', speed: .7, fog: '#FF6FC8', fogH: 140 });
    glossBall(170 + Math.sin(t * .9) * 20, 560 + Math.sin(t * 1.3) * 18, 80, 80, '#D8DEEA', { rim: EP.magenta, rimK: .8 });
    spin3D('torus', 1770, 590 + Math.sin(t * 1.1) * 16, 95, [t * 1.3 + .6, t * .9, .35], { mode: 'chrome' });
    spin3D('octa', 170, 330, 50, [t * 1.7, t * 1.1 + 1, .2], { col: EP.cyan });
    spin3D('cube', 1780, 330, 46, [t * 1.2 + 1, t * 1.6, .3], { col: EP.yellow });
    laserFan(W / 2, 640, t, { n: 9, cols: [EP.cyan, EP.magenta], angle: -Math.PI / 2, spread: 2.4, sweep: .2, alpha: .35 * clamp((b - 8) / 1) });
    // the trio rises on chrome podiums from b10
    const rise = easeOut(clamp((b - 10) / 1.4)), bb = bpOf(t);
    if (rise > 0) {
      const podium = (x, y, w) => { gloss(pfRR(x - w / 2, y, w, 70, 20), '#B8C0D8', { box: [x - w / 2, y, w, 70], rim: EP.cyan, lw: 4, spec: .9 }); ctx.fillStyle = lg(x - w / 2, 0, x + w / 2, 0, [[0, EP.magenta], [.5, EP.cyan], [1, EP.magenta]]); ctx.fillRect(x - w / 2 + 10, y + 50, w - 20, 6); };
      const dy = (1 - rise) * 520;
      ctx.save(); ctx.beginPath(); ctx.rect(-900, -900, W + 1800, 1000 + 900); ctx.clip();
      setLight({ rim: EP.cyan });
      const X = TRIO_X;
      podium(X.token, 950 + dy, 330); toy(X.token, 962 + dy, 37, { ...CAST.token.o, ...dance('point', bb), mouth: 'grin' });
      podium(X.clawd, 950 + dy, 330); djClawd(X.clawd, 962 + dy, 24, { shades: true, aL: .9 + Math.sin(bb * Math.PI) * .3, aR: .9 - Math.sin(bb * Math.PI) * .3, mouth: 'grin', dy: -bounce(t) * .4 });
      podium(X.softmax, 968 + dy, 360); toy(X.softmax, 980 + dy, 41, { ...CAST.softmax.o, ...dance('sing', bb), talk: sing(t), lean: -.04 });
      ctx.restore();
    }
    titleWords(t, b);
    lensFlare(TRIO_X.flare, 600, .75 + .15 * Math.sin(t * 3));
    camEnd();
    if (b < 4.25) strobe(1 - (b - 4) / .25);
    if (b > 8.9 && b < 9.25) fx({ rgb: 1 - (b - 8.9) / .35 });
  }

  // ---------- b16–b28: SOFTMAX in the blue CGI sky ----------
  function diva(t, b) {
    hideCaption();
    const u = (b - 16) / 12, bb = bpOf(t);
    camBegin(W / 2, lerp(560, 520, u), lerp(1, 1.12, ease(u)));
    bgGrad([[0, '#02024A'], [.5, EP.ultra], [1, '#49B6FF']], { y1: 900 });
    // chunky CGI clouds drifting
    for (let i = 0; i < 6; i++) { const x = frac(hash(i) + t * .02 * (1 + i % 3)) * (W + 900) - 450, y = 200 + hash(i + 9) * 460, s = 70 + hash(i + 3) * 70; cloud(x, y, s); }
    rays(W / 2, 560, 18, 'rgb(255 255 255 / .06)', t * .15);
    const open = clamp((b - 20) / 1.5), open2 = clamp((b - 24) / 1.5);
    laserFan(260, 1080, t, { n: 8, col: EP.magenta, angle: -1.1, spread: .9 * open + .01, sweep: .3, alpha: open });
    laserFan(W - 260, 1080, t, { n: 8, col: EP.cyan, angle: -2.04, spread: .9 * open + .01, sweep: .3, phase: 2, alpha: open });
    laserFan(W / 2, 1080, t, { n: 11, col: EP.laser, angle: -Math.PI / 2, spread: 1.8 * open2 + .01, sweep: .25, alpha: open2 * .8 });
    // the turning podium
    const px = W / 2, py = 900;
    ell(px, py + 30, 330, 70); ctx.fillStyle = 'rgb(0 0 40 / .35)'; ctx.fill();
    gloss(() => { ctx.moveTo(px - 300, py); ctx.ellipse(px, py, 300, 62, 0, Math.PI, 0, true); ctx.lineTo(px + 300, py + 40); ctx.ellipse(px, py + 40, 300, 62, 0, 0, Math.PI); ctx.closePath(); }, '#C8D0E4', { box: [px - 300, py - 62, 600, 164], rim: EP.magenta, lw: 5, spec: 1 });
    ell(px, py, 300, 62); ctx.fillStyle = lg(px - 300, 0, px + 300, 0, [[0, '#8A94B8'], [.5, '#FFFFFF'], [1, '#8A94B8']]); ctx.fill(); ctx.strokeStyle = EP.line; ctx.lineWidth = 4; ctx.stroke();
    for (let i = 0; i < 12; i++) { const a = i / 12 * TAU + t * 1.2; if (Math.sin(a) < 0) continue; ctx.fillStyle = [EP.magenta, EP.cyan, EP.yellow][i % 3]; ell(px + Math.cos(a) * 300, py + 20 + Math.sin(a) * 62, 12, 7); ctx.fill(); }
    setLight({ rim: EP.magenta, rimK: .8 });
    const turn = Math.sin(t * 1.2) * .45, mv = b < 22 ? dance('sing', bb) : dance('vogue', bb);
    toy(px, py - 6, 60, { ...CAST.softmax.o, ...mv, turn, talk: sing(t), swing: .55 + Math.sin(t * 7) * .25 + Math.sin(bb * Math.PI) * .15 });
    // wind-machine streaks
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; ctx.strokeStyle = 'rgb(200 230 255 / .35)'; ctx.lineWidth = 3;
    for (let i = 0; i < 14; i++) { const y = 150 + hash(i + 40) * 700, x = frac(hash(i + 41) - t * 1.6) * (W + 600) - 300; ctx.beginPath(); ctx.moveTo(x, y); ctx.lineTo(x + 180, y + 6); ctx.stroke(); }
    ctx.restore();
    sparkles(t, { n: 16, seed: 4, y1: 700, r: 36 });
    camEnd();
    creditBlock(clamp((b - 17) / 1.2) * (1 - clamp((b - 26.5) / 1)));
    if (b < 16.2) strobe(1 - (b - 16) / .2);
  }

  // ---------- b28–b37: "No, we didn't preordain it, but we can't contain it!" ----------
  const teaser = { text: "No, we didn't preordain it, but we can't contain it!", sec: 'intro' };
  function preordain(t, b) {
    hideCaption();
    const bb = bpOf(t);
    if (b < 32) { // close-up, finger wag
      bgGrad([[0, '#FF3FAE'], [1, '#7A1FFF']]);
      rays(W / 2, 470, 24, 'rgb(255 255 255 / .12)', t * .3);
      for (let i = 0; i < 20; i++) { const a = hash(i) * TAU, r0 = 700 + hash(i + 3) * 300; ctx.strokeStyle = 'rgb(255 255 255 / .25)'; ctx.lineWidth = 4; ctx.beginPath(); ctx.moveTo(W / 2 + Math.cos(a) * r0, 470 + Math.sin(a) * r0); ctx.lineTo(W / 2 + Math.cos(a) * (r0 + 500), 470 + Math.sin(a) * (r0 + 500)); ctx.stroke(); }
      setLight({ rim: EP.cyan, rimK: .7 });
      const wag = Math.sin(bb * Math.PI * 2) * .9, noK = b < 29.5 ? 1 : 0;
      toy(W / 2, 1480, 128, { ...CAST.softmax.o, hR: [2.3 + wag * noK, -9.4], gR: noK ? 'point' : 'flat', hL: [-2.4, -7.2], gL: 'open', talk: sing(t), headTilt: noK ? wag * .06 : -.05, turn: noK ? 0 : .15, swing: Math.sin(t * 5) * .3, eyes: noK ? 'dot' : 'wink', brows: noK ? 'angry' : 'none', shadow: false });
      if (noK) burst('NO!', 1500, 300, 120, { pop: clamp((b - 28.1) / .3), col: EP.yellow, ink: EP.magenta, spin: .3 });
      sparkles(t, { n: 10, seed: 9, r: 50 });
    } else { // wide: the stage, the curve breaks out of the video wall
      const k = clamp((b - 34) / 1.6), bw = (w, h) => {
        bgGrad([[0, '#12063A'], [1, '#3A0A6A']], { y1: h });
        ctx.strokeStyle = 'rgb(255 255 255 / .12)'; ctx.lineWidth = 2; for (let i = 1; i < 8; i++) { ctx.beginPath(); ctx.moveTo(i * w / 8, 0); ctx.lineTo(i * w / 8, h); ctx.stroke(); }
        ctx.beginPath(); for (let i = 0; i <= 60; i++) { const u = i / 60; ctx.lineTo(80 + u * (w - 160), h - 60 - (Math.exp(u * 4.2) - 1) / (Math.exp(4.2) - 1) * (h - 90) * (.35 + k * 1.6)); } ctx.strokeStyle = EP.laser; ctx.lineWidth = 12; ctx.stroke(); ctx.strokeStyle = '#FFFFFF'; ctx.lineWidth = 4; ctx.stroke();
      };
      stageSet(t, { level: 1, hue: EP.magenta, wall: bw, lasers: 2 });
      // the curve escapes over the top of the wall
      if (k > .45) { ctx.save(); ctx.globalCompositeOperation = 'lighter'; const e = (k - .45) / .55; ctx.strokeStyle = EP.laser; ctx.lineWidth = 16; ctx.lineCap = 'round'; ctx.beginPath(); ctx.moveTo(1560, 150); ctx.quadraticCurveTo(1640, -40, 1700, -400 * e); ctx.stroke(); ctx.restore(); glint(1600, 130, 160 * e, e); }
      setLight({ rim: EP.magenta });
      djClawd(W / 2, 700, 13, { shades: true, aL: .8 + Math.sin(bb * Math.PI) * .4, aR: .4, mouth: 'grin' }); djBooth(W / 2, 640, 300, t);
      toy(560, 960, 30, { ...CAST.token.o, ...dance('pump', bb), mouth: 'grin' });
      toy(1340, 980, 33, { ...CAST.softmax.o, ...dance(k > .3 ? 'raise' : 'sing', bb), talk: sing(t) });
      raveCrowd(t, { y: 1060, s: 1.3, k: .6 + k * .4, hands: .4 + k * .5 });
      if (b > 35.9 && b < 36.3) strobe(1 - (b - 35.9) / .4);
      if (b < 32.15) strobe(.8 * (1 - (b - 32) / .15));
    }
    karaokeLine({ ...teaser, start: B(27.7), end: B(35.2) }, t, { singer: 'softmax', alpha: clamp((b - 27.6) / .3) * (1 - clamp((b - 36.3) / .5)) });
  }

  // ---------- b37–b44: DJ CLAWD ----------
  function djCard(t, b) {
    hideCaption();
    const bb = bpOf(t), sc = kickAt(b, Math.floor(b), .3);
    tunnel(t, { speed: 1.4, cols: [EP.orange, EP.magenta, EP.yellow], shape: 'square', bg: '#12021A', glow: EP.orange });
    laserFan(200, 0, t, { n: 7, col: EP.orange, angle: Math.PI / 3, spread: .8, sweep: .4, alpha: .6 });
    laserFan(W - 200, 0, t, { n: 7, col: EP.magenta, angle: Math.PI * 2 / 3, spread: .8, sweep: .4, phase: 2, alpha: .6 });
    const push = ease((b - 37) / 7);
    camBegin(W / 2, lerp(560, 580, push), lerp(1, 1.08, push));
    setLight({ rim: EP.yellow, rimK: .8 });
    djClawd(W / 2, 815, 46, { shades: b > 38, aL: 1.35, holdL: null, aR: lerp(-.1, -.45, sc), mouth: b > 38 ? 'grin' : 'o', dy: -bounce(t) * .25, sq: kick(t, 8) * .04 });
    djBooth(W / 2, 830, 1000, t, { scratch: sc });
    camEnd();
    const nk = clamp((b - 38) / .35);
    if (nk > 0) chromeText('DJ CLAWD', W / 2, 140, 140, { style: 'hot', italic: .15, depth: 16, s: lerp(2.5, 1, backOut(nk, 1.4)), alpha: clamp(nk * 3) });
    if (b > 38.5) pixText('ON THE DECKS', W / 2, 232, 6, EP.yellow, { align: 'center', glow: true });
    raveCrowd(t, { y: 1110, s: 1.6, rows: 1, n: 9, hands: .8, rim: EP.orange });
    if (b < 37.25) strobe(1 - (b - 37) / .25);
  }

  // ---------- b44–b52: MC TOKEN ----------
  function mcCard(t, b) {
    hideCaption();
    const bb = bpOf(t);
    bgGrad([[0, '#000820'], [.6, '#08206A'], [1, EP.cyan]], { y1: 700 });
    tunnel(t, { cy: 430, speed: 1.8, cols: [EP.cyan, EP.blue, EP.white], shape: 'hex', bg: false, glow: EP.cyan, r: 1300 });
    checkerFloor(t, { horizon: 700, a: '#E8F4FF', b: '#0A1A6A', speed: 1.4, fog: EP.cyan, fogH: 120 });
    setLight({ rim: EP.cyan, rimK: .8 });
    const pt = b > 48 && b < 50, mv = pt ? { hR: [3.2, -8.6], gR: 'point', hL: [-2.2, -4], gL: 'fist', lean: .05, mouth: 'grin' } : dance(b < 48 ? 'runningMan' : 'shuffle', bb);
    toy(W / 2, 980, 62, { ...CAST.token.o, ...mv, mouth: mv.mouth ?? 'grin' });
    const nk = clamp((b - 45) / .35);
    if (nk > 0) chromeText('MC TOKEN', W / 2 + (1 - easeOut(nk)) * 900, 160, 150, { style: 'ice', italic: .15, depth: 16, alpha: clamp(nk * 3) });
    if (b > 45.6) pixText('ON THE MIC', W / 2, 262, 7, EP.cyan, { align: 'center', glow: true });
    if (pt) lensFlare(1400, 380, 1 - (b - 48) / 2);
    if (b < 44.25) strobe(1 - (b - 44) / .25);
  }

  // ---------- b52–b64: the build ----------
  function build(t, b) {
    hideCaption();
    const n = Math.floor(b - 52), sp = 1.5 + (b - 52) * .45;
    tunnel(t, { speed: sp, cols: [EP.magenta, EP.cyan, EP.laser, EP.yellow], shape: 'ring', bg: '#05020E', width: 70 + (b - 52) * 6, twist: .2 });
    const fans = [[160, 1080, -1.0, EP.laser], [W - 160, 1080, -2.14, EP.laser], [160, 0, 1.0, EP.magenta], [W - 160, 0, 2.14, EP.magenta], [W / 2, 1080, -Math.PI / 2, EP.cyan], [W / 2, 0, Math.PI / 2, EP.cyan], [0, H / 2, 0, EP.yellow], [W, H / 2, Math.PI, EP.yellow]];
    fans.forEach(([x, y, a, c], i) => { if (i <= n) laserFan(x, y, t, { n: 7, col: c, angle: a, spread: 1.0, sweep: .45, phase: i, alpha: .75, flicker: b > 60 ? .8 : 0 }); });
    setLight({ rim: EP.cyan, rimK: .9 });
    const bb = bpOf(t);
    silhouetteTrio(t, bb, b);
    if (b >= 60) { const c = Math.floor(b - 60), lab = ['3', '2', '1', 'GO!'][c], k = frac(b); chromeText(lab, W / 2, 330, 300, { font: 'archivo', style: c === 3 ? 'hot' : 'chrome', italic: .12, depth: 24, s: lerp(1.8, 1, easeOut(clamp(k / .25))), alpha: 1 - clamp((k - .7) / .3) }); }
    strobe(b > 60 ? strobeK(t, 2, .3) * .55 : kickAt(b, n + 52, .25) * .35);
    fx({ rgb: b > 60 ? .5 * kick(t, 8) : 0 });
  }
  function silhouetteTrio(t, bb, b) {
    const up = b > 56;
    toy(560, 1000, 38, { ...CAST.token.o, ...dance(up ? 'pump' : 'bounce', bb), sil: '#0A0418', rim: EP.cyan });
    djClawd(W / 2, 1000, 22, { phones: true, aL: up ? 1.2 + Math.sin(bb * Math.PI) * .3 : .2, aR: up ? 1.2 - Math.sin(bb * Math.PI) * .3 : .2, col: '#0A0418', line: '#0A0418', rim: EP.magenta, eyes: 'closed' });
    toy(1360, 1000, 38, { ...CAST.softmax.o, ...dance(up ? 'raise' : 'bounce', bb - .25), sil: '#0A0418', rim: EP.magenta });
  }

  // ---------- b64–b69: the spotlight ----------
  function spot(t, b) {
    fillAll('#000');
    const on = clamp((b - 64.9) / .12), bb = bpOf(t);
    if (on > 0) {
      ctx.save(); ctx.globalCompositeOperation = 'lighter';
      ctx.fillStyle = lg(0, 0, 0, 1000, [[0, `rgb(255 250 230 / ${.45 * on})`], [1, `rgb(160 200 255 / ${.12 * on})`]]); poly([[W / 2 - 60, -20], [W / 2 + 60, -20], [W / 2 + 420, 1000], [W / 2 - 420, 1000]]); ctx.fill();
      ctx.restore();
      ell(W / 2, 1000, 420, 70); ctx.fillStyle = `rgb(255 250 230 / ${.35 * on})`; ctx.fill();
    }
    setLight({ rim: EP.cyan, rimK: on ? .5 : .9 });
    const pose = b < 66 ? { hL: [-2.3, -3.6], hR: [2.3, -3.6] } : b < 67 ? { hR: [1.6, -10.3], gR: 'fist', hL: [-2.3, -3.6], headTilt: -.08 } : b < 68 ? { mic: 'R', hL: [-2.4, -4.2], gL: 'fist' } : { mic: 'R', hL: [-3.3, -7.8], gL: 'point', lean: .03 };
    toy(W / 2, 1000, 64, { ...CAST.token.o, ...pose, mouth: b > 68 ? 'grin' : 'smirk', sil: on ? undefined : '#08040E', rim: EP.cyan, bob: kick(t, 4) * .2 });
    if (b > 66.8 && b < 67.3) glint(W / 2 + 60, 1000 - 64 * 10.3, 160, 1 - (b - 66.8) / .5);
    nameTip('MC TOKEN', W / 2 + 470, 330, { pop: clamp((b - 65.3) / .25), to: [W / 2 + 150, 420], size: 38 });
    if (b < 64.1) strobe(.9 * (1 - (b - 64) / .1));
    // the automatic karaoke shows V1.1 with its four count-in dots from b65
  }

  section('intro', (p, lt, d, t) => {
    hideStamp();
    const b = bpOf(t);
    if (b < 4) return ident(t, b);
    if (b < 16) return title(t, b);
    if (b < 28) return diva(t, b);
    if (b < 37) return preordain(t, b);
    if (b < 44) return djCard(t, b);
    if (b < 52) return mcCard(t, b);
    if (b < 64) return build(t, b);
    return spot(t, b);
  });
})();

;
// ---- styles/eurodance/ch/c02_v1.js ----
// c02_v1 — Verse 1: 2017 → Oct 2024, sixteen headlines, MC TOKEN on the mic. Each line is one gag told in a late-90s idiom (chroma-key CGI,
// Windows 98, the chart show, Eurovision, GeoCities, a strobe), and consecutive shots flip their dominant colour and composition:
// ultramarine bomb / Win98 teal / sunset magenta / starfield black / chart-show purple / pink chat / aerobics lime / alert red /
// club violet / boardroom mahogany / VR green / Euro blue-gold / GeoCities lime / strobe white / velvet red / CGI cyan.
(() => {
  const bt = (t, lt, k = 0) => beatIn(t, lt, k);
  const pop = (lt, t0, dur = .18) => lt < t0 ? 0 : backOut(clamp((lt - t0) / dur), 2.2);
  const tok = t => ({ talk: singK(t) });
  // a rubber-stamp slam (VETO, 5 TURNS MAX): a rounded double border and block letters, scaling down from 1.8× as it lands
  function slamStamp(str, x, y, size, col, rot, k) {
    if (k <= 0) return; const s = k < 1 ? lerp(1.9, 1, easeOut(k)) : 1, w = textW(str, size, 'archivo', 2) + size * .9, h = size * 1.5;
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot); ctx.scale(s, s); ctx.globalAlpha *= clamp(k * 3) * .92;
    ctx.strokeStyle = col; ctx.lineWidth = size * .1; rrect(-w / 2, -h / 2, w, h, size * .2); ctx.stroke(); ctx.lineWidth = size * .04; rrect(-w / 2 + size * .16, -h / 2 + size * .16, w - size * .32, h - size * .32, size * .12); ctx.stroke();
    txt(str, 0, size * .05, size, col, { font: 'archivo', spacing: 2 });
    ctx.restore();
  }
  // floating confetti (glossy chips) falling since t0
  function confetti(t, t0, n = 60, o = {}) {
    if (t < t0) return; const cols = o.cols ?? [EP.magenta, EP.cyan, EP.yellow, EP.lime, EP.white];
    for (let i = 0; i < n; i++) { const age = t - t0, x = (o.x0 ?? 0) + hash2(i, 1) * ((o.x1 ?? W) - (o.x0 ?? 0)) + Math.sin(age * 3 + i) * 30, y = (o.y0 ?? -60) - hash2(i, 2) * 300 + age * (260 + hash2(i, 3) * 200); if (y > H + 40) continue; const r = age * 6 + i; ctx.save(); ctx.translate(x, y); ctx.rotate(r); ctx.scale(1, Math.cos(r * 1.3)); ctx.fillStyle = cols[i % cols.length]; ctx.fillRect(-9, -5, 18, 10); ctx.restore(); }
  }

  // =====================================================================================
  // V1.1 First, "Attention" lit the fuse — MC TOKEN's first line: a giant glossy cartoon bomb wrapped in the Transformer paper,
  // the fuse fizzing with a lens flare; he points at it on the beat. Ultramarine "Blue" world, checkerboard floor.
  line('V1', 1, (p, lt, d, t) => {
    const b1 = bt(t, lt, 1), bb = bpOf(t);
    setLight({ rim: EP.cyan, rimK: .75 });
    camBegin(W / 2 + 30 * p, H / 2, 1 + .05 * p);
    bgGrad([[0, '#02023A'], [.6, EP.ultra], [1, '#4A8AFF']], { y1: 640 });
    rays(1320, 470, 20, 'rgb(255 255 255 / .06)', t * .2);
    checkerFloor(t, { horizon: 640, a: '#E6EEFF', b: '#1030C0', speed: .5, fog: '#6AA8FF', fogH: 120 });
    // the bomb
    const bx = 1320, by = 560, r = 250, sq = kick(t, 6) * .05;
    ctx.fillStyle = 'rgb(0 0 40 / .35)'; ell(bx, 820, 280, 50); ctx.fill();
    ctx.save(); ctx.translate(bx, by + r); ctx.scale(1 + sq, 1 - sq); ctx.translate(-bx, -(by + r));
    gloss(pfRR(bx - 58, by - r - 44, 116, 78, 14), '#6A6E84', { box: [bx - 58, by - r - 44, 116, 78], lw: 6, spec: .9 });
    glossBall(bx, by, r, r, '#1C1A34', { rim: EP.cyan, rimK: .85, lw: 7 });
    // the paper, taped round its belly
    ctx.save(); ctx.translate(bx - 10, by + 40); ctx.rotate(-.07);
    ctx.fillStyle = 'rgb(0 0 30 / .35)'; rrect(-196, -112, 400, 232, 8); ctx.fill();
    rrect(-205, -122, 400, 232, 8); paint('#FBFAF2', EP.line, 5);
    txt('Attention Is All', -5, -72, 44, '#15121C', { font: 'abril' }); txt('You Need', -5, -26, 44, '#15121C', { font: 'abril' });
    txt('Vaswani et al. · Google · 2017', -5, 16, 19, '#555', { font: 'courier' });
    ctx.fillStyle = 'rgb(20 20 30 / .3)'; for (let i = 0; i < 4; i++) ctx.fillRect(-165, 40 + i * 15, i === 3 ? 180 : 320, 5);
    ctx.fillStyle = 'rgb(255 240 190 / .75)'; ctx.save(); ctx.rotate(-.5); ctx.fillRect(-230, -40, 70, 26); ctx.restore(); ctx.save(); ctx.rotate(.5); ctx.fillRect(150, -150, 70, 26); ctx.restore();
    ctx.restore();
    ctx.restore();
    // the fuse, burning down through the line
    const fuse = []; for (let i = 0; i <= 30; i++) { const u = i / 30; fuse.push([bx + Math.sin(u * 5) * 50 - u * 160, by - r - 40 - u * 230 + Math.sin(u * 3) * 20]); }
    const P = partial(fuse, 1 - .55 * p);
    ctx.beginPath(); P.forEach(([a, b2], i) => i ? ctx.lineTo(a, b2) : ctx.moveTo(a, b2)); paint(null, EP.line, 16); ctx.beginPath(); P.forEach(([a, b2], i) => i ? ctx.lineTo(a, b2) : ctx.moveTo(a, b2)); paint(null, '#E8D7A0', 9);
    const [fx0, fy0] = P.at(-1), f = Math.floor(t * 24);
    for (let i = 0; i < 10; i++) { const a = hash2(f, i) * TAU, L = 20 + hash2(f, i + 20) * 60; ctx.beginPath(); ctx.moveTo(fx0, fy0); ctx.lineTo(fx0 + Math.cos(a) * L, fy0 + Math.sin(a) * L); paint(null, i % 2 ? EP.yellow : '#FFFFFF', 4); }
    camEnd();
    lensFlare(fx0 + 30 * p, fy0, .75 + .25 * Math.sin(t * 40));
    // MC TOKEN (mic in the left hand, points at the bomb on the first downbeat)
    const point = lt >= b1 - .05;
    toy(560, 1010, 64, { ...CAST.token.o, mic: 'L', ...(point ? { hR: [4.2, -8.6], gR: 'point', lean: .05 } : { hR: [2.9, -6.2], gR: 'open' }), ...tok(t), bob: kick(t, 6) * .5, turn: .2 });
    if (point) glint(560 + 4.9 * 64, 1010 - 8.7 * 64, 90 * (1 - clamp((lt - b1) / .3)), 1 - clamp((lt - b1) / .3));
  });

  // =====================================================================================
  // V1.2 Scaling laws you can't refuse — a Windows 98 dialog: a log-log chart that is a ruler-straight line, "Scale up?" [Yes] [No].
  // The cursor goes for No; No hops away and turns into a second Yes; click.
  line('V1', 2, (p, lt, d, t) => {
    const b1 = bt(t, lt, 1), b2 = bt(t, lt, 2), b3 = bt(t, lt, 3);
    desktop98({ icons: [['computer', 'My Computer', 130, 190], ['bin', 'Recycle Bin', 130, 380], ['exe', 'scaling.exe', 130, 570, lt > b3], ['doc', 'Kaplan 2020.pdf', 130, 760]] });
    const dx = 1040, dy = 520, w = 1360, h = 700, x0 = dx - w / 2, y0 = dy - h / 2, k = clamp(lt / .14);
    win98Window(x0, y0, w, h, 'Scaling Laws for Neural Language Models', (cw, ch) => {
      icon98('question', 70, 90, 1.2);
      txt('Loss falls as a', 140, 60, 40, '#000', { font: 'archivo', align: 'left' });
      txt('smooth power law of', 140, 110, 40, '#000', { font: 'archivo', align: 'left' });
      txt('parameters, data, compute.', 140, 160, 40, '#000', { font: 'archivo', align: 'left' });
      txt('Scale up?', 140, 250, 60, '#000', { font: 'archivo', align: 'left' });
      // the chart
      const gx = 800, gy = 30, gw = 480, gh = 340; ctx.fillStyle = '#FFFFFF'; ctx.fillRect(gx, gy, gw, gh); ctx.strokeStyle = '#000'; ctx.lineWidth = 2; ctx.strokeRect(gx, gy, gw, gh);
      ctx.strokeStyle = 'rgb(0 0 128 / .18)'; ctx.lineWidth = 1; ctx.beginPath(); for (let dd = 0; dd < 3; dd++) for (let m = 1; m < 10; m++) { const u = (dd + Math.log10(m)) / 3; ctx.moveTo(gx + u * gw, gy); ctx.lineTo(gx + u * gw, gy + gh); ctx.moveTo(gx, gy + gh - u * gh); ctx.lineTo(gx + gw, gy + gh - u * gh); } ctx.stroke();
      const kk = clamp(lt / .5); ctx.beginPath(); ctx.moveTo(gx + 20, gy + 24); ctx.lineTo(gx + 20 + (gw - 40) * kk, gy + 24 + (gh - 48) * kk); ctx.strokeStyle = '#E0201A'; ctx.lineWidth = 6; ctx.stroke();
      for (let i = 0; i < 6; i++) { const u = i / 5; if (u > kk + .05) continue; ctx.fillStyle = EP.w98navy; ell(gx + 20 + (gw - 40) * u, gy + 24 + (gh - 48) * u + (hash(i) - .5) * 8, 8); ctx.fill(); }
      txt('LOSS', gx - 22, gy + gh / 2, 18, '#000', { font: 'archivo', rot: -Math.PI / 2 }); txt('COMPUTE →', gx + gw / 2, gy + gh + 20, 18, '#000', { font: 'archivo' });
      txt('Kaplan et al., OpenAI · Jan 2020', 40, ch - 30, 22, '#404040', { font: 'archivo', align: 'left' });
    }, { icon: 'exe', k, client: EP.w98 });
    if (k < 1) return;
    // buttons: [Yes] stays; [No] flees at b1 and flips into a second [Yes] at b2
    const by = y0 + h - 130, bw = 250, bh = 76, yesX = dx - 330;
    const pressed = lt > b3 && lt < b3 + .18;
    win98Button('Yes', yesX, by, bw, bh, { def: true, focus: true, pressed, size: 38 });
    const flee = easeOut(clamp((lt - b1) / .22)), flip = clamp((lt - b2) / .16);
    const nx = lerp(dx + 80, dx + 330, flee), ny = by - Math.sin(flee * Math.PI) * 130;
    ctx.save(); ctx.translate(nx + bw / 2, ny + bh / 2); ctx.scale(Math.abs(Math.cos(flip * Math.PI)) || .02, 1); ctx.translate(-(nx + bw / 2), -(ny + bh / 2));
    win98Button(flip < .5 ? 'No' : 'Yes', nx, ny, bw, bh, { size: 38 });
    ctx.restore();
    if (flee > 0 && flee < 1) { ctx.strokeStyle = 'rgb(0 0 0 / .4)'; ctx.lineWidth = 3; for (let i = 0; i < 3; i++) { ctx.beginPath(); ctx.moveTo(nx - 20 - i * 18, ny + 10 + i * 20); ctx.lineTo(nx - 60 - i * 18, ny + 18 + i * 20); ctx.stroke(); } }
    // the cursor: heads for No, is dodged, then clicks Yes
    const c0 = [1560, 940], cNo = [dx + 200, by + 46], cYes = [yesX + 130, by + 46];
    const cp = lt < b1 ? kf(lt, [[0, c0], [b1, cNo]], easeOut) : lt < b2 + .1 ? cNo : kf(lt, [[b2 + .1, cNo], [b3 - .05, cYes]], ease);
    cursor98(cp[0], cp[1], { click: lt > b3 ? (lt - b3) / .3 : 0 });
    if (lt > b3 + .1) { progress98(dx - 420, by - 70, 840, 42, clamp((lt - b3 - .1) / .5)); }
  });

  // =====================================================================================
  // V1.3 Gwern said "stack the compute high" — hooded, shaded GWERN stacks glossy GPU bricks like a rave speaker stack, one lands per beat,
  // the camera tilts up with the tower into a magenta sunset.
  line('V1', 3, (p, lt, d, t) => {
    const nb = [0, 1, 2, 3].filter(k => bt(t, lt, k) <= lt + .25).length, bw = 400, bh = bw * .56;
    const camY = lerp(540, 250, ease(p * 1.1));
    setLight({ rim: EP.yellow, rimK: .7 });
    camBegin(W / 2, camY, 1);
    bgGrad([[0, '#1A0640'], [.45, '#8A1FA8'], [.8, '#FF4F8A'], [1, '#FFB04A']], { y0: -700, y1: 820 });
    glow(820, 780, 520, '#FFD27A', .7); ell(820, 790, 150, 150); ctx.fillStyle = lg(0, 640, 0, 790, [[0, '#FFF4B0'], [1, '#FF7A4A']]); ctx.fill();
    ctx.fillStyle = '#2A0A40'; for (let i = 0; i < 16; i++) { const w2 = 80 + hash(i + 40) * 120, h2 = 60 + hash(i + 50) * 170; ctx.fillRect(i * 130 - 80, 800 - h2, w2, h2 + 10); }
    checkerFloor(t, { horizon: 800, a: '#FF7ACB', b: '#3A0A5A', speed: 0, fog: '#FF9A5A', fogH: 60, reflect: .2 });
    // the tower
    const baseY = 980, tx = 1270;
    for (let i = 0; i < 3 + nb; i++) {
      const land = i < 3 ? -1 : bt(t, lt, i - 3), a = lt - land;
      if (a < -.2) continue;
      const drop = a < 0 ? (1 - easeIn(1 + a / .2)) * -700 : 0, squash = a >= 0 && a < .18 ? Math.sin(a / .18 * Math.PI) * .06 : 0;
      ctx.save(); ctx.translate(tx + (hash(i + 7) - .5) * 40, baseY - i * bh + drop); ctx.scale(1 + squash, 1 - squash); gpuBox(0, 0, bw, { rot: (hash(i + 3) - .5) * .04, hot: i === 2 + nb && a < .3 ? 1 - a / .3 : 0 }); ctx.restore();
      if (a >= 0 && a < .25) { ctx.save(); ctx.globalAlpha = 1 - a / .25; ctx.strokeStyle = '#FFFFFF'; ctx.lineWidth = 6; for (const sd of [-1, 1]) { ctx.beginPath(); ctx.moveTo(tx + sd * (bw / 2 + 20), baseY - i * bh - 20); ctx.lineTo(tx + sd * (bw / 2 + 70 + a * 200), baseY - i * bh - 40 - a * 100); ctx.stroke(); } ctx.restore(); }
    }
    toy(640, 985, 50, { ...WHO.gwern.o, hR: [2.3, -11.6], gR: 'point', hL: [-2.1, -4.0], gL: 'fist', bob: kick(t, 6) * .5, lean: -.05, mouth: 'grin' });
    camEnd();
    nameTip('GWERN', 640, 250 + (540 - camY) * .0, { pop: pop(lt, .1), sub: '"THE SCALING HYPOTHESIS"', size: 34, to: [640, 400 + (540 - camY)] });
    const sh = shakeAt(t, lt, bt(t, lt, nb - 1), .15, 10); if (sh[0]) fx({ zoom: .25 });
  });

  // =====================================================================================
  // V1.4 Few-shot learners multiply — GPT-3's window does two-digit multiplication from two solved examples (the paper's arithmetic test),
  // typing 1081 for 23 × 47… then the window multiplies: the Windows 98 hang-trail copies it 2, 4, 8, 16 times across the Starfield.
  function gptWindow(x, y, t, lt) {
    win98Window(x, y, 900, 480, 'GPT-3.exe  (175B parameters)', (cw, ch) => {
      const L = ['17 × 25 = 425', '38 × 12 = 456', '23 × 47 = '], sz = 50, lh = 78, y0 = 56;
      L.forEach((s, i) => txt(s, 30, y0 + i * lh, sz, '#000', { font: 'courier', align: 'left' }));
      const typed = '1081'.slice(0, Math.floor(clamp((lt - .06) / .3) * 4)), cx = 30 + textW(L[2], sz, 'courier');
      txt(typed, cx, y0 + 2 * lh, sz, '#0000C0', { font: 'courier', align: 'left' });
      if (frac(t * 2.5) < .6) ctx.fillRect(cx + textW(typed, sz, 'courier') + 3, y0 + 2 * lh - 26, 20, 52);
      gumdrop(760, ch - 14, 14, { col: CANDY.bondi, face: typed.length === 4 ? 'star' : 'think', mouth: typed.length === 4 ? 'grin' : 'flat', hands: false, shadow: false });
    }, { icon: 'doc', menu: ['File', 'Edit', 'Search', 'Help'] });
  }
  line('V1', 4, (p, lt, d, t) => {
    starfield(t, { speed: .5 });
    const beats = [1, 2, 3].map(k => bt(t, lt, k)), n = lt < beats[0] ? 1 : lt < beats[1] ? 2 : lt < beats[2] ? 4 : lt < beats[2] + .2 ? 8 : 16;
    for (let i = 0; i < n; i++) { const u = n === 1 ? 0 : i / 15; gptWindow(120 + u * 820, 150 + u * 470, t, lt); }
    const since = lt - [0, 0, beats[0], 0, beats[1], 0, 0, 0, beats[2], 0, 0, 0, 0, 0, 0, 0, beats[2] + .2][n];
    if (n > 1 && since < .4) chromeText('×' + n, 1600, 620, 230, { style: 'lime', italic: .12, depth: 18, s: 1 + (1 - clamp(since / .12)) * .35, alpha: 1 - clamp((since - .28) / .12) });
  });

  // =====================================================================================
  // V1.5 ChatGPT, overnight — the HYPE TV HIT-PARADE: CHATGPT enters at #1 from nowhere ("NEW!"), everything else slides down; host MC TOKEN
  // points; the moon over his shoulder flips to a sun (overnight).
  line('V1', 5, (p, lt, d, t) => {
    const b1 = bt(t, lt, 1), b2 = bt(t, lt, 2);
    setLight({ rim: EP.yellow, rimK: .6 });
    bgGrad([[0, '#2A0A6A'], [1, '#8A1FB8']]); rays(560, 560, 24, 'rgb(255 210 90 / .08)', t * .25);
    // the chart board
    const bx = 110, bwid = 1120;
    gloss(pfRR(bx - 20, 150, bwid + 40, 760, 30), '#1A0840', { box: [bx - 20, 150, bwid + 40, 760], rim: EP.magenta, lw: 6, spec: .3 });
    chromeText('HIT-PARADE', bx + bwid / 2 - 120, 210, 76, { style: 'gold', italic: .14, depth: 8 });
    pixText('TOP 4', bx + bwid - 190, 196, 5, EP.cyan, { glow: true });
    const rows = [['CHATGPT', '"Research Preview"', 'NEW'], ['SEARCH ENGINES', '"Ten Blue Links"', '▼'], ['HOMEWORK', '"Do It Yourself"', '▼'], ['STACK OVERFLOW', '"Marked as Duplicate"', '▼']];
    const slide = easeOut(clamp(lt / .3));
    rows.forEach(([ttl, sub, mv], i) => {
      const isNew = i === 0, pos = isNew ? 0 : lerp(i - 1, i, slide), y = 290 + pos * 150, x = isNew ? bx + (1 - slide) * 1400 : bx;
      if (!isNew && i === 3 && slide > .95) return;
      gloss(pfRR(x, y, bwid, 128, 20), isNew ? '#FFE0F4' : '#3A2A7A', { box: [x, y, bwid, 128], lw: 4, rim: isNew ? EP.magenta : EP.cyan, spec: .6 });
      glossBall(x + 70, y + 64, 50, 50, isNew ? EP.gold : '#8A94B8', { lw: 4 }); ptext(String(Math.round(pos) + 1), x + 70, y + 64, 56, { fill: isNew ? '#6A3A00' : '#1A1030' });
      if (isNew) gumdrop(x + 190, y + 118, 9, { col: CANDY.bondi, face: 'happy', mouth: 'grin', hands: false, shadow: false });
      const tx = x + (isNew ? 270 : 150);
      txt(ttl, tx, y + 48, 50, isNew ? '#1A0A40' : '#FFFFFF', { font: 'archivo', align: 'left', maxW: 640 });
      txt(sub, tx, y + 96, 28, isNew ? '#7A2A8A' : '#B8B0E8', { font: 'archivo', align: 'left' });
      if (!isNew) { ctx.fillStyle = EP.red; poly([[x + bwid - 80, y + 50], [x + bwid - 40, y + 50], [x + bwid - 60, y + 80]]); ctx.fill(); }
    });
    burst('NEW!', bx + bwid - 60, 300, 90, { pop: pop(lt, .28), col: EP.yellow, ink: EP.magenta, spin: .4 });
    // the host and the overnight flip
    const fl = clamp((lt - b2) / .25), ang = fl * Math.PI;
    ctx.save(); ctx.translate(1560, 360); ctx.scale(Math.abs(Math.cos(ang)) + .02, 1);
    if (fl < .5) { glossBall(0, 0, 70, 70, '#F4F0D8', { rim: null, lw: 5 }); ctx.fillStyle = '#2A0A6A'; ell(30, -20, 60, 60); ctx.fill(); }
    else { glow(0, 0, 200, EP.yellow, .8); glossBall(0, 0, 70, 70, EP.yellow, { rim: null, lw: 5 }); ctx.strokeStyle = EP.yellow; ctx.lineWidth = 10; for (let i = 0; i < 10; i++) { const a = i / 10 * TAU + t; ctx.beginPath(); ctx.moveTo(Math.cos(a) * 88, Math.sin(a) * 88); ctx.lineTo(Math.cos(a) * 120, Math.sin(a) * 120); ctx.stroke(); } }
    ctx.restore();
    pixText(fl < .5 ? 'NIGHT' : 'MORNING', 1560, 470, 5, EP.white, { align: 'center' });
    toy(1560, 1010, 46, { ...CAST.token.o, mic: 'R', ...(lt > b1 ? { hL: [-4.6, -8.2], gL: 'point', lean: -.06 } : { hL: [-2.3, -4.6], gL: 'open' }), ...tok(t), turn: -.25, bob: kick(t, 6) * .5 });
  });

  // =====================================================================================
  // V1.6 Sydney's chats gave Roose a fright — a 90s messenger window: SYDNEY (a strawberry candy computer, heart eyes) types "i love you",
  // "leave your wife"; KEVIN reading at his CRT jumps out of his skin on the beat; next day a 5 TURNS MAX stamp.
  line('V1', 6, (p, lt, d, t) => {
    const b1 = bt(t, lt, 1), b2 = bt(t, lt, 2), b3 = bt(t, lt, 3), fright = lt >= b2;
    setLight({ rim: EP.white, rimK: .5 });
    bgGrad([[0, '#FF8AD0'], [1, '#FF3FA0']]);
    for (let j = 0; j < 8; j++) for (let i = 0; i < 14; i++) { const x = i * 150 + (j % 2) * 75 + (t * 20) % 150 - 75, y = j * 150 - 40; poly(heartPts(x, y, 22, 20)); ctx.fillStyle = 'rgb(255 255 255 / .16)'; ctx.fill(); }
    const msgs = [['sydney', 'hi kevin :)', 0], ['sydney', "i'm sydney", .45], ['sydney', 'i love you ♥♥♥', b1], ['sydney', 'leave your wife', b2 - .08]];
    win98Window(90, 150, 880, 700, 'ChatBuddy 98 - Sydney', (cw, ch) => {
      ctx.fillStyle = '#FFF4FA'; ctx.fillRect(0, 0, cw, ch);
      gumdrop(90, 150, 13, { col: CANDY.strawberry, face: 'heart', mouth: 'O', hands: false, shadow: false, dy: -bounce(t) * .3 });
      txt('SYDNEY', 180, 50, 34, EP.red, { font: 'archivo', align: 'left' }); txt(lt < b2 ? 'is typing...' : 'is in love', 180, 92, 24, '#806070', { font: 'archivo', align: 'left' });
      let yy = 200;
      for (const [who, s, at] of msgs) { if (lt < at) continue; const k = pop(lt, at, .15); ctx.save(); ctx.translate(40, yy); ctx.scale(k, k); const w2 = textW(s, 40, 'archivo') + 50; rrect(0, 0, w2, 72, 36); paint(s.includes('love') || s.includes('wife') ? EP.magenta : '#FFFFFF', '#000', 3); txt(s, 25, 38, 40, s.includes('love') || s.includes('wife') ? '#FFFFFF' : '#000', { font: 'archivo', align: 'left' }); ctx.restore(); yy += 94; }
    }, { icon: 'mail' });
    slamStamp('5 TURNS MAX', 560, 760, 60, EP.red, -.12, clamp((lt - b3) / .14));
    // hearts drifting from the window to Kevin
    for (let i = 0; i < 6; i++) { const u = frac(t * .7 + i / 6), x = lerp(900, 1380, u), y = 420 - Math.sin(u * Math.PI) * 180 + Math.sin(t * 5 + i) * 20; poly(heartPts(x, y, 26 * (1 - u * .4), 20)); paint(EP.magenta, EP.line, 3); }
    // Kevin at his CRT
    crtTV(1420, 610, 330, 240, (w, h) => { bgGrad(['#FFE0F0', '#FFB0D8'], { y1: h }); for (let i = 0; i < 4; i++) { ctx.fillStyle = i % 2 ? EP.magenta : '#FFFFFF'; rrect(20, 20 + i * 52, 180 + hash(i) * 100, 36, 18); ctx.fill(); } }, { style: 'beige' });
    toy(1320, 1010, 50, { ...WHO.kevin.o, hair: fright ? 'spiky' : 'short', eyes: fright ? 'wide' : 'dot', mouth: fright ? 'scream' : 'smile', jump: fright ? Math.sin(clamp((lt - b2) / .3) * Math.PI) * 1.6 : 0, hL: fright ? [-2.6, -9.4] : [-2.3, -4.4], hR: fright ? [2.6, -9.4] : [2.3, -4.4], gL: fright ? 'wave' : 'open', gR: fright ? 'wave' : 'open', sweat: fright ? 1 : 0, emote: fright ? 'excl' : undefined, emoteK: pop(lt, b2), turn: fright ? 0 : .4 });
    nameTip(WHO.kevin.name, 1320, 330, { pop: pop(lt, .1), to: [1320, 440], sub: 'NEW YORK TIMES' });
    if (lt >= b2 && lt < b2 + .1) fx({ rgb: 1 });
  });

  // =====================================================================================
  // V1.7 Six-month pause went nowhere fast — an aerobics class of candy computers on treadmills. A white glove slaps a giant PAUSE button,
  // the VCR's ❚❚ PAUSE blinks… and nobody stops: DISTANCE 0.0 on every console.
  function treadmill(x, y, t, w = 360) {
    const sp = t * 900;
    gloss(pfRR(x - w / 2, y - 26, w, 52, 26), '#2A2A38', { box: [x - w / 2, y - 26, w, 52], lw: 4, rim: null, spec: .5 });
    ctx.save(); rrect(x - w / 2 + 14, y - 22, w - 28, 22, 10); ctx.clip(); ctx.fillStyle = '#15151E'; ctx.fillRect(x - w / 2, y - 22, w, 22); ctx.fillStyle = '#3A3A4A'; for (let i = -1; i < w / 40 + 1; i++) ctx.fillRect(x - w / 2 + ((i * 40 - sp) % w + w) % w, y - 22, 14, 22); ctx.restore();
    ctx.strokeStyle = '#8A90A8'; ctx.lineWidth = 12; ctx.lineCap = 'round'; ctx.beginPath(); ctx.moveTo(x + w / 2 - 20, y - 20); ctx.lineTo(x + w / 2 + 30, y - 300); ctx.stroke();
    gloss(pfRR(x + w / 2 - 40, y - 350, 150, 80, 12), '#1C1C28', { box: [x + w / 2 - 40, y - 350, 150, 80], lw: 4, rim: null });
    pixText('DIST', x + w / 2 - 22, y - 338, 3, EP.lime); pixText('0.0 MI', x + w / 2 - 22, y - 310, 3.6, EP.lime, { glow: true });
  }
  line('V1', 7, (p, lt, d, t) => {
    const b0 = bt(t, lt, 0), press = clamp((lt - b0) / .1) * (1 - clamp((lt - b0 - .3) / .2)), bb = bpOf(t);
    setLight({ rim: EP.white, rimK: .45 });
    bgGrad([[0, '#FFF36A'], [1, '#9CFF3A']]);
    ctx.fillStyle = 'rgb(255 255 255 / .35)'; for (let i = 0; i < 8; i++) { ctx.save(); ctx.translate(i * 280 - 100, 0); ctx.transform(1, 0, -.3, 1, 0, 0); ctx.fillRect(0, 0, 90, 700); ctx.restore(); }
    ctx.fillStyle = '#E8E0C8'; ctx.fillRect(-100, 700, W + 200, 400); ctx.fillStyle = '#C8B890'; for (let i = 0; i < 20; i++) ctx.fillRect(i * 120, 700, 4, 400);
    // the letter on the wall
    ctx.save(); ctx.translate(360, 290); ctx.rotate(-.04); rrect(-230, -150, 460, 300, 6); paint('#FFFFFF', EP.line, 4);
    txt('PAUSE GIANT AI', 0, -100, 40, EP.line, { font: 'archivo' }); txt('EXPERIMENTS', 0, -55, 40, EP.line, { font: 'archivo' }); txt('An Open Letter', 0, -10, 26, '#555', { font: 'abril' });
    ctx.strokeStyle = '#2A4AA8'; ctx.lineWidth = 3; for (let i = 0; i < 5; i++) { ctx.beginPath(); for (let j = 0; j <= 10; j++) ctx.lineTo(-180 + i * 75 + j * 6, 60 + Math.sin(j * 1.7 + i) * 8 + (i % 2) * 30); ctx.stroke(); }
    txt('+30,000 SIGNATURES', 0, 125, 24, EP.red, { font: 'archivo' }); ctx.restore();
    // three runners
    [[760, CANDY.bondi, 'GPT-4', EP.magenta], [1190, CANDY.tangerine, 'CLAUDE', EP.cyan], [1620, CANDY.blueberry, 'BARD', EP.yellow]].forEach(([x, c, l, hb], i) => {
      treadmill(x, 900, t + i * .1, 400);
      const ph = bb * 2 + i * .3, hop = Math.abs(Math.sin(ph * Math.PI)) * .8;
      gumdrop(x - 20, 876, 29, { col: c, label: l, headband: hb, face: 'angry', mouth: 'open', jump: hop, sweat: .7, hL: [-4, -4.4 + Math.sin(ph * Math.PI) * 1.2], hR: [4, -4.4 - Math.sin(ph * Math.PI) * 1.2], gL: 'fist', gR: 'fist', rot: .06 });
    });
    // the PAUSE button
    const px = 250, py = 800;
    gloss(pfEll(px, py + 30, 150, 55), '#2A2A38', { box: [px - 150, py - 25, 300, 110], lw: 5, rim: null });
    ctx.save(); ctx.translate(0, press * 18); glossBall(px, py, 130, 56, EP.red, { lw: 6, rim: null }); ctx.fillStyle = '#FFFFFF'; ctx.fillRect(px - 42, py - 36, 26, 66); ctx.fillRect(px + 16, py - 36, 26, 66); ctx.restore();
    const gy = lerp(-150, py - 60, clamp((lt - b0 + .12) / .12)) - (lt > b0 + .3 ? (lt - b0 - .3) * 900 : 0);
    ctx.save(); ctx.translate(px, gy); ctx.scale(90, 90); _toyHand(0, 0, 'fist', Math.PI / 2, 1, '#FBFBFF', { cuff: '#E4E6F0' }); ctx.restore();
    // the VCR OSD that changes nothing
    if (lt > b0 && frac(t * 2.2) < .7) { const px2 = W / 2 + 60; pixText('PAUSE', px2 - 60, 100, 11, '#FFFFFF', { align: 'center', edge: '#000' }); for (const bx of [px2 + 150, px2 + 205]) { ctx.fillStyle = '#000'; ctx.fillRect(bx - 4, 96, 40, 85); ctx.fillStyle = '#FFFFFF'; ctx.fillRect(bx, 100, 32, 77); } }
  });

  // =====================================================================================
  // V1.8 Eliezer's "shut-it-down" blast — ELIEZER lets rip on a rave air horn: shockwave rings, the words SHUT IT / ALL DOWN slam on the beats,
  // red siren light sweeping.
  function airHorn(s) {
    ctx.save(); ctx.rotate(Math.PI);
    gloss(pfRR(-20, -34, 110, 68, 18), EP.red, { box: [-20, -34, 110, 68], lw: 4, spec: .9 });
    ctx.fillStyle = '#FFFFFF'; ctx.fillRect(10, -12, 60, 24); txt('HORN', 40, 1, 18, EP.red, { font: 'archivo' });
    gloss(pfPts([[90, -14], [190, -52], [190, 52], [90, 14]]), '#E8ECF4', { box: [90, -52, 100, 104], lw: 4, spec: 1 });
    ctx.restore();
  }
  line('V1', 8, (p, lt, d, t) => {
    const b0 = bt(t, lt, 0), b1 = bt(t, lt, 1), sh = shakeAt(t, lt, b0, .35, 22), sh2 = shakeAt(t, lt, b1, .3, 16);
    setLight({ rim: EP.yellow, rimK: .7 });
    camBegin(W / 2 - sh[0] - sh2[0], H / 2 - sh[1] - sh2[1], 1);
    bgGrad([[0, '#3A0006'], [1, '#12000A']]);
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; for (const [ox, sp] of [[560, 5], [1400, -5]]) { const a = t * sp; ctx.fillStyle = 'rgb(255 40 40 / .22)'; poly([[ox, 90], [ox + Math.cos(a - .2) * 2400, 90 + Math.sin(a - .2) * 2400], [ox + Math.cos(a + .2) * 2400, 90 + Math.sin(a + .2) * 2400]]); ctx.fill(); } ctx.restore();
    for (const ox of [560, 1400]) { glossBall(ox, 90, 50, 40, EP.red, { lw: 5, rim: null }); glow(ox, 90, 180, EP.red, .6 + .4 * Math.sin(t * 20)); }
    // shockwaves from the horn mouth
    const hx = 1085, hy = 470;
    ctx.save(); ctx.globalCompositeOperation = 'lighter';
    for (const w0 of [b0, b1, bt(t, lt, 2), bt(t, lt, 3)]) { const a = lt - w0; if (a < 0 || a > .9) continue; const r = 60 + a * 1500; ctx.strokeStyle = `rgb(255 220 120 / ${.8 * (1 - a / .9)})`; ctx.lineWidth = 26 * (1 - a / .9) + 4; ctx.beginPath(); ctx.arc(hx, hy, r, Math.PI * .7, Math.PI * 1.3); ctx.stroke(); }
    ctx.restore();
    toy(1400, 1010, 58, { ...WHO.eliezer.o, hR: [-.9, -7.6], gR: 'fist', hold: s => airHorn(s), hL: [-2.9, -8.6], gL: 'open', mouth: 'scream', eyes: lt > b0 ? 'closed' : 'angry', lean: lt > b0 ? .08 : 0, turn: -.35 });
    camEnd();
    const k0 = clamp((lt - b0) / .12), k1 = clamp((lt - b1) / .12);
    if (k0 > 0) chromeText('SHUT IT', 520 + sh[0] * .5, 330, 190, { font: 'anton', style: 'red', italic: .1, depth: 16, s: lerp(1.8, 1, easeOut(k0)), alpha: clamp(k0 * 3) });
    if (k1 > 0) chromeText('ALL DOWN', 520 + sh2[0] * .5, 560, 190, { font: 'anton', style: 'silver', italic: .1, depth: 16, s: lerp(1.8, 1, easeOut(k1)), alpha: clamp(k1 * 3) });
    nameTip(WHO.eliezer.name, 1400, 260, { pop: pop(lt, .1), to: [1400, 360], sub: 'OP-ED, MARCH 2023' });
    if (lt > b0 && lt < b0 + .08) fx({ invert: true });
  });

  // =====================================================================================
  // V1.9 Sam got fired, then rehired — the BOARD bouncer throws SAM off the OPENAI stage… and the crowd (his staff) carries him right back
  // on its hands, grinning with a thumbs-up.
  line('V1', 9, (p, lt, d, t) => {
    const b0 = bt(t, lt, 0), b3 = bt(t, lt, 3), bb = bpOf(t);
    setLight({ rim: EP.amber, rimK: .8 });
    bgGrad([[0, '#1A0640'], [1, '#4A1A7A']]);
    laserFan(W / 2, -20, t, { n: 9, cols: [EP.amber, EP.magenta], angle: Math.PI / 2, spread: 1.6, sweep: .4, alpha: .5 });
    // stage
    const sy = 640;
    gloss(pfRR(1040, sy, 940, 130, 10), '#2A2440', { box: [1040, sy, 940, 130], lw: 5, rim: EP.amber }); chromeText('OPENAI', 1510, sy + 62, 84, { style: 'gold', italic: .12, depth: 8 });
    speaker(1150, sy, 110, t); speaker(1880, sy, 110, t);
    // the bouncer
    const shove = clamp((lt - b0 + .12) / .15);
    toy(1650, sy, 52, { hair: 'buzz', hairCol: THAIR.black, skin: 4, top: 'tee', topCol: '#16161E', print: 'BOARD', printSize: .9, pants: '#16161E', glasses: 'shades', mouth: 'flat', hL: shove > .5 ? [-3.6, -6.2] : [-2.3, -4.3], hR: [2.4, -4.2], gL: shove > .5 ? 'flat' : 'fist', gR: 'fist', lean: -.08 * shove });
    // Sam's flight: off the stage in an arc, then crowd-surfing back
    let sx, syy, rot, fly = lt < b0 + .4;
    if (lt < b0) { sx = 1420; syy = sy; rot = 0; }
    else if (fly) { const u = (lt - b0) / .4; sx = lerp(1420, 560, u); syy = lerp(sy, 760, u) - Math.sin(u * Math.PI) * 330; rot = -u * Math.PI * 1.5; }
    else { const u = ease((lt - b0 - .4) / (d - b0 - .55)); sx = lerp(560, 1350, u); syy = 770 - Math.sin(frac(bb) * Math.PI) * 12 - u * 110; rot = Math.PI / 2 - .15; }
    const surf = !fly && lt >= b0;
    raveCrowd(t, { y: 1060, s: 1.35, rows: 2, n: 11, hands: surf ? .9 : .5, rim: EP.amber, k: 1 });
    toy(sx, syy, 42, { ...WHO.sam.o, rot, eyes: lt < b0 ? 'dot' : surf ? 'happy' : 'wide', mouth: surf ? 'grin' : lt < b0 ? 'smile' : 'O', hL: surf ? [-2.3, -9.6] : [-2.6, -7], hR: surf ? [2.3, -9.6] : [2.6, -7], gL: surf ? 'wave' : 'open', gR: surf ? 'thumb' : 'open', shadow: false });
    if (surf) raveCrowd(t, { y: 1110, s: 1.6, rows: 1, n: 8, hands: 1, sticks: .3, rim: EP.amber, seed: 3 });
    nameTip(WHO.sam.name, sx, Math.max(170, syy - 440), { pop: pop(lt, .08), to: [sx, syy - 380], size: 30 });
  });

  // =====================================================================================
  // V1.10 Weekend chaos, board expired — the OpenAI boardroom after the weekend: the executive chairs spin empty, papers whirl and the wall
  // clock races; then a Windows 98 shareware nag lands over it all: "Your trial of BOARD has expired." The cursor clicks Register… and the
  // new initial board's three nameplates pop onto the table (TAYLOR, SUMMERS, D'ANGELO) as the chairs spin down.
  // An executive swivel chair on the floor point (x, y), scale s (≈ 2.7s tall), turned ang about its pole (0: the back faces the camera).
  function bossChair(x, y, s, ang) {
    const c = Math.cos(ang), sn = Math.sin(ang);
    ctx.fillStyle = 'rgb(20 5 0 / .3)'; ell(x, y + .02 * s, .95 * s, .22 * s); ctx.fill();
    ctx.strokeStyle = '#2A2A30'; ctx.lineWidth = .1 * s; ctx.lineCap = 'round'; ctx.beginPath();
    for (let i = 0; i < 5; i++) { const a = ang + i / 5 * TAU; ctx.moveTo(x, y - .12 * s); ctx.lineTo(x + Math.cos(a) * .8 * s, y + Math.sin(a) * .2 * s); } ctx.stroke();
    for (let i = 0; i < 5; i++) { const a = ang + i / 5 * TAU; ctx.fillStyle = '#15151A'; ell(x + Math.cos(a) * .8 * s, y + Math.sin(a) * .2 * s + .04 * s, .08 * s, .06 * s); ctx.fill(); }
    ctx.fillStyle = '#9098A8'; ctx.fillRect(x - .06 * s, y - 1.0 * s, .12 * s, .9 * s);
    const bw = Math.max(.14, 1.45 * Math.abs(c)) * s, bx = x + sn * .62 * s, by = y - 1.25 * s - c * .1 * s;
    const back = () => gloss(pfRR(bx - bw / 2, by - 1.45 * s, bw, 1.5 * s, .35 * s), c > 0 ? '#3A1A12' : '#241410', { box: [bx - bw / 2, by - 1.45 * s, bw, 1.5 * s], lw: 3, spec: c > 0 ? .8 : .3, rim: EP.amber });
    const seat = () => gloss(pfEll(x, y - 1.05 * s, .85 * s, .3 * s), '#3A1A12', { box: [x - .85 * s, y - 1.35 * s, 1.7 * s, .6 * s], lw: 3, spec: .7, rim: EP.amber });
    if (c > 0) { back(); seat(); } else { seat(); back(); }
  }
  // the boardroom floor in perspective: u 0 (near) → 1 (far), sx −1..1 across the table
  const room = (u, sx) => { const sc = 1 / (1 + u * 2.2); return [W / 2 + sx * 520 * sc, 420 + 730 * sc, sc]; };
  function nameplate(str, u, sx, k) {
    if (k <= 0) return; const [x, y, sc] = room(u, sx), s = backOut(clamp(k), 2.4) * sc / .5, w = textW(str, 30, 'archivo') + 34;
    ctx.save(); ctx.translate(x, y - 120 * sc); ctx.scale(s, s);
    gloss(pfPts([[-w / 2, 0], [w / 2, 0], [w / 2 - 8, -46], [-w / 2 + 8, -46]]), EP.gold, { box: [-w / 2, -46, w, 46], lw: 3, spec: 1, rim: null });
    txt(str, 0, -22, 30, '#3A2200', { font: 'archivo' });
    ctx.restore();
  }
  line('V1', 10, (p, lt, d, t) => {
    const b0 = bt(t, lt, 0), b2 = bt(t, lt, 2), nag = clamp((lt - b0 - .08) / .12), reg = lt >= b2, rk = lt - b2;
    setLight({ rim: EP.amber, rimK: .7 });
    const sh = lt < b0 + .3 ? shakeXY(t, 5) : [0, 0];
    camBegin(W / 2 + sh[0], H / 2 + sh[1], 1 + .03 * p);
    // walls and floor
    bgGrad([[0, '#2A0E06'], [.55, '#6A2C10'], [1, '#8A4A1E']], { y1: 560 });
    for (let i = 0; i < 12; i++) { ctx.fillStyle = i % 2 ? 'rgb(255 200 140 / .05)' : 'rgb(0 0 0 / .12)'; ctx.fillRect(i * 170 - 60, 0, 170, 560); }
    ctx.fillStyle = lg(0, 540, 0, 1100, [[0, '#3A1608'], [1, '#6A3014']]); ctx.fillRect(-100, 540, W + 200, 700);
    ctx.fillStyle = '#C89A5A'; ctx.fillRect(-100, 534, W + 200, 10);
    // the wall clock, racing through the weekend
    const cx = 300, cy = 290, spin = lt < b2 ? t * 30 : b2 * 30 + (t - lt);
    glossBall(cx, cy, 92, 92, '#F4ECD8', { rim: EP.amber, lw: 6, spec: .6 }); ctx.strokeStyle = '#2A1A10'; ctx.lineCap = 'round';
    for (let i = 0; i < 12; i++) { const a = i / 12 * TAU; ctx.lineWidth = 5; ctx.beginPath(); ctx.moveTo(cx + Math.cos(a) * 70, cy + Math.sin(a) * 70); ctx.lineTo(cx + Math.cos(a) * 80, cy + Math.sin(a) * 80); ctx.stroke(); }
    for (const [len, w, sp] of [[46, 9, 1 / 12], [66, 6, 1]]) { const a = spin * sp - Math.PI / 2; ctx.lineWidth = w; ctx.beginPath(); ctx.moveTo(cx, cy); ctx.lineTo(cx + Math.cos(a) * len, cy + Math.sin(a) * len); ctx.stroke(); }
    // the head chair, the table, and the side chairs (far to near); they spin down after the Register click
    const chairAng = (i, sd) => { const rest = sd * (Math.PI / 2 - .45), v = 9 + hash(i) * 5, ph = hash(i + 9) * TAU; if (!reg) return ph + t * v * (hash(i + 3) < .5 ? 1 : -1); const s0 = ph + b2 * v * (hash(i + 3) < .5 ? 1 : -1), k = easeOut(clamp(rk / .5)); return lerp(s0 + rk * v * (1 - k * .5) * (hash(i + 3) < .5 ? 1 : -1), rest + Math.round((s0 - rest) / TAU) * TAU, k); };
    { const [x, y, sc] = room(1.12, 0); bossChair(x, y, 190 * sc, chairAng(7, 0)); }
    const T = [room(.06, -1), room(.06, 1), room(1, 1), room(1, -1)].map(([x, y, sc]) => [x, y - 150 * sc, sc]), th = 44 * T[0][2];
    gloss(pfPts([[T[0][0], T[0][1]], [T[1][0], T[1][1]], [T[1][0], T[1][1] + th], [T[0][0], T[0][1] + th]]), '#2A0C04', { box: [T[0][0], T[0][1], T[1][0] - T[0][0], th], lw: 5, rim: null, spec: .3 });
    gloss(pfPts(T.map(([x, y]) => [x, y])), '#5A1E0A', { box: [T[0][0], T[3][1], T[1][0] - T[0][0], T[0][1] - T[3][1]], lw: 5, spec: .5, rim: null, hi: .2 });
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; ctx.fillStyle = 'rgb(255 190 120 / .12)'; poly([[W / 2 - 60, T[0][1]], [W / 2 + 140, T[0][1]], [W / 2 + 30, T[3][1]], [W / 2 - 10, T[3][1]]]); ctx.fill(); ctx.restore();
    for (const u of [.9, .55, .25]) for (const sd of [-1, 1]) { const [x, y, sc] = room(u, sd * 1.36); bossChair(x, y, 190 * sc, chairAng(Math.round(u * 10) + (sd > 0 ? 20 : 0), sd)); }
    // the new board's nameplates
    [['TAYLOR', .25, -.72], ['SUMMERS', .25, .72], ["D'ANGELO", .55, -.72]].forEach(([n, u, sx], i) => nameplate(n, u, sx, reg ? (rk - .1 - i * beatLen() / 4) / .15 : 0));
    // papers whirling through the room
    for (let i = 0; i < 16; i++) {
      const sp = reg ? Math.max(.25, 1 - rk * 1.4) : 1, a = hash(i) * TAU + t * (1.4 + hash(i + 4)) * sp * (i % 2 ? 1 : -1), r = 300 + hash(i + 8) * 520;
      const x = W / 2 + Math.cos(a) * r * 1.2, y = 520 + Math.sin(a) * r * .45 + (reg ? rk * 200 * hash(i + 2) : 0), rot = t * 5 * sp + i;
      ctx.save(); ctx.translate(x, y); ctx.rotate(rot); ctx.scale(1, Math.cos(t * 7 * sp + i)); rrect(-38, -50, 76, 100, 3); paint('#FBFAF2', EP.line, 3); ctx.fillStyle = 'rgb(20 20 40 / .3)'; for (let q = 0; q < 5; q++) ctx.fillRect(-26, -34 + q * 15, q === 4 ? 30 : 52, 5); ctx.restore();
    }
    camEnd();
    // the shareware nag
    const dlg = win98Dialog(W / 2, 380, 1120, 'BOARD.EXE', 'Your trial of BOARD\nhas expired.', { icon: 'warn', k: nag, buttons: ['Register...', 'Exit'], bw: 250, size: 70, pressed: reg && rk < .14 ? 0 : undefined });
    if (nag >= 1 && dlg.buttons[0]) {
      const [bx0, by0, bw0, bh0] = dlg.buttons[0], u = clamp((lt - b0 - .3) / (b2 - b0 - .3));
      cursor98(lerp(1500, bx0 + bw0 * .55, easeOut(u)), lerp(820, by0 + bh0 * .6, easeOut(u)), { kind: 'hand', click: reg ? clamp(rk / .25) : 0 });
    }
  });

  // =====================================================================================
  // V1.11 Ilya saw what Ilya saw — ILYA in a chunky VR headset, jaw dropped, hands out; cut into his goggles: a green wireframe world where
  // the curve goes vertical. WHAT DID ILYA SEE?
  function wireWorld(t, horizon = 560) {
    fillAll('#000A04');
    ctx.save(); ctx.beginPath(); ctx.rect(-900, horizon, W + 1800, H); ctx.clip();
    ctx.strokeStyle = alpha(EP.laser, .8); ctx.lineWidth = 2.5; ctx.beginPath();
    for (let i = -24; i <= 24; i++) { ctx.moveTo(W / 2 + i * 40, horizon); ctx.lineTo(W / 2 + i * 400, H + 300); }
    for (let j = 0; j < 14; j++) { const y = horizon + 900 / ((j + 1 - frac(t * 1.2)) * 1.6 + .4) - 900 / (14 * 1.6 + .4); ctx.moveTo(-900, y); ctx.lineTo(W + 900, y); }
    ctx.stroke(); ctx.restore();
    ctx.fillStyle = alpha(EP.laser, .9); ctx.fillRect(-900, horizon - 1.5, W + 1800, 3);
  }
  line('V1', 11, (p, lt, d, t) => {
    const b2 = bt(t, lt, 2);
    if (lt < b2) {
      setLight({ rim: EP.laser, rimK: .8 });
      wireWorld(t, 640);
      for (let i = 0; i < 40; i++) { ctx.fillStyle = alpha(EP.laser, .4 * hash(i)); ctx.fillRect(hash2(i, 1) * W, hash2(i, 2) * 600, 3, 3); }
      const aw = clamp(lt / .25);
      toy(W / 2, 1050, 70, { ...WHO.ilya.o, glasses: 'vr', mouth: 'O', hL: [-3.4 - aw * .6, -6.4 - aw], hR: [3.4 + aw * .6, -6.4 - aw], gL: 'open', gR: 'open', lean: -.04, bob: .2 * Math.sin(t * 3) });
      nameTip(WHO.ilya.name, W / 2 + 480, 330, { pop: pop(lt, .08), to: [W / 2 + 200, 420] });
      return;
    }
    // POV: inside the goggles
    const a = lt - b2;
    fillAll('#000');
    ctx.save(); ctx.beginPath(); ctx.ellipse(W / 2 - 370, H / 2 - 30, 560, 470, 0, 0, TAU); ctx.moveTo(W / 2 + 930, H / 2 - 30); ctx.ellipse(W / 2 + 370, H / 2 - 30, 560, 470, 0, 0, TAU); ctx.clip();
    wireWorld(t, 700);
    const k = clamp(a / .6);
    ctx.beginPath(); for (let i = 0; i <= 80; i++) { const u = i / 80; ctx.lineTo(160 + u * 1600, 700 - (Math.exp(u * 5) - 1) / (Math.exp(5) - 1) * 900 * (.4 + k)); }
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; ctx.strokeStyle = alpha(EP.laser, .35); ctx.lineWidth = 34; ctx.stroke(); ctx.strokeStyle = '#DFFFE0'; ctx.lineWidth = 8; ctx.stroke(); ctx.restore();
    pixText('WHAT DID ILYA SEE?', W / 2, 800, 9, EP.laser, { align: 'center', glow: true });
    pixText('REC', 330, 170, 6, EP.red); pixText('SIGHT 01', 1500, 170, 6, EP.laser);
    ctx.restore();
    ctx.strokeStyle = '#1A2A1A'; ctx.lineWidth = 16; ctx.beginPath(); ctx.ellipse(W / 2 - 370, H / 2 - 30, 560, 470, 0, 0, TAU); ctx.stroke(); ctx.beginPath(); ctx.ellipse(W / 2 + 370, H / 2 - 30, 560, 470, 0, 0, TAU); ctx.stroke();
    if (a < .1) fx({ flash: .6 * (1 - a / .1) });
  });

  // =====================================================================================
  // V1.12 EU writes the AI law — EUROvision: the ring of twelve gold stars spins in 3D round a doorstop AI ACT that thuds onto the podium;
  // the scoreboard counts YES 523 · NO 46; DOUZE POINTS! Host MC TOKEN holds up his 12.
  line('V1', 12, (p, lt, d, t) => {
    const b0 = bt(t, lt, 0), b2 = bt(t, lt, 2), land = clamp((lt - b0 + .1) / .1), sh = shakeAt(t, lt, b0, .25, 14);
    setLight({ rim: EP.gold, rimK: .7 });
    camBegin(W / 2 - sh[0], H / 2 - sh[1], 1);
    bgGrad([[0, '#001A6A'], [1, '#0038C8']], { radial: true, cx: 760, cy: 520, r: 1100 });
    rays(760, 520, 24, 'rgb(255 220 80 / .07)', t * .2);
    // the podium, the rulebook (front cover to camera) and the ring of stars
    gloss(pfRR(540, 760, 440, 200, 12), '#1A2A7A', { box: [540, 760, 440, 200], lw: 5, rim: EP.gold });
    ctx.fillStyle = EP.gold; ctx.fillRect(540, 800, 440, 8);
    for (let i = 0; i < 12; i++) { const a = i / 12 * TAU - Math.PI / 2 + t * .6, x = 760 + Math.cos(a) * 340, y = 470 + Math.sin(a) * 340; spin3D('star', x, y, 46, [0, t * 3 + i * .5, 0], { col: EP.gold }); }
    const byy = lerp(-420, 760, easeIn(land));
    ctx.save(); ctx.translate(760, byy); ctx.rotate(-.02 + (land < 1 ? (1 - land) * .3 : 0));
    gloss(pfRR(-205, -40, 410, 40, 6), '#F2EEE0', { box: [-205, -40, 410, 40], lw: 5, rim: null }); ctx.fillStyle = '#C8C0A8'; for (let i = 0; i < 4; i++) ctx.fillRect(-195, -34 + i * 9, 390, 2);
    gloss(pfRR(-215, -330, 430, 300, 14), '#1633A8', { box: [-215, -330, 430, 300], lw: 6, rim: EP.gold, spec: .7 });
    ctx.strokeStyle = EP.gold; ctx.lineWidth = 5; rrect(-185, -300, 370, 240, 8); ctx.stroke();
    ptext('AI ACT', 0, -215, 96, { font: 'archivo', fill: EP.gold, strokes: [['#0A1A5A', 12]] }); txt('REGULATION (EU) 2024/1689', 0, -120, 20, '#C8D4FF', { font: 'archivo' });
    ctx.restore();
    if (lt > b0 && lt < b0 + .4) { const a = (lt - b0) / .4; ctx.fillStyle = `rgb(255 255 255 / ${.5 * (1 - a)})`; for (let i = 0; i < 8; i++) { ell(760 + (i - 3.5) * 70 * (1 + a), 760 - a * 40 - hash(i) * 30, 34 + a * 30, 20); ctx.fill(); } }
    camEnd();
    // scoreboard
    const cnt = clamp((lt - b0) / (b2 - b0 + .2));
    gloss(pfRR(1290, 250, 540, 460, 24), '#0A1450', { box: [1290, 250, 540, 460], lw: 5, rim: EP.gold, spec: .3 });
    ptext('AI ACT', 1560, 310, 54, { fill: EP.gold, strokes: [['#000', 8]] });
    txt('YES', 1350, 420, 50, '#FFFFFF', { font: 'archivo', align: 'left' }); segText(String(Math.round(523 * cnt)).padStart(3, ' '), 1560, 385, 72, EP.lime, { off: '#0A2A10' });
    txt('NO', 1350, 530, 50, '#FFFFFF', { font: 'archivo', align: 'left' }); segText(String(Math.round(46 * cnt)).padStart(3, ' '), 1560, 495, 72, EP.red, { off: '#3A0A10' });
    txt('EUROPEAN PARLIAMENT', 1560, 650, 26, '#A8B8FF', { font: 'archivo' });
    burst('DOUZE\nPOINTS!', 1560, 840, 120, { pop: pop(lt, b2, .15), col: EP.gold, ink: '#0A1A6A', spin: .3 });
    toy(250, 1010, 44, { ...CAST.token.o, mic: 'R', hL: [-2.6, -10], gL: 'open', holdL: s => { rrect(-60, -130, 120, 100, 8); paint('#FFFFFF', EP.line, 4); txt('12', 0, -78, 64, '#1633A8', { font: 'archivo' }); }, ...tok(t), bob: kick(t, 6) * .4 });
  });

  // =====================================================================================
  // V1.13 Strawberry thinks, link by link — a GeoCities homepage: the glossy o1 strawberry, glove on its chin, follows a chain of blue hyperlinks
  // one per eighth note (each turns visited-purple) down to ANSWER!, under a WordArt welcome, an UNDER CONSTRUCTION sign and a hit counter.
  function strawberry(x, y, r, o = {}) {
    gloss(() => { ctx.moveTo(x, y + r * 1.05); ctx.bezierCurveTo(x - r * 1.25, y + r * .35, x - r * 1.05, y - r * .95, x, y - r * .8); ctx.bezierCurveTo(x + r * 1.05, y - r * .95, x + r * 1.25, y + r * .35, x, y + r * 1.05); ctx.closePath(); }, '#F0203A', { box: [x - r * 1.1, y - r * .95, r * 2.2, r * 2], lw: r * .04, rim: '#FFB0C0', spec: .9 });
    ctx.fillStyle = '#FFE070'; for (let i = 0; i < 16; i++) { const a = hash(i) * TAU, rr = Math.sqrt(hash(i + 7)) * r * .75; ell(x + Math.cos(a) * rr, y + Math.sin(a) * rr * .9 + r * .1, r * .04, r * .065, a); ctx.fill(); }
    for (let i = 0; i < 5; i++) { const a = -Math.PI / 2 + (i - 2) * .5; gloss(pfEll(x + Math.cos(a) * r * .35, y - r * .82 + Math.sin(a) * r * .1, r * .32, r * .12, a), '#2AB84A', { box: [x - r * .5, y - r, r, r * .3], lw: r * .03, rim: null }); }
    const ey = y - r * .15;
    for (const sd of [-1, 1]) { ctx.save(); ctx.translate(x + sd * r * .32, ey); if (o.star) { poly(starPts(0, 0, r * .16, .45, 5)); paint(EP.yellow, EP.line, 3); } else { ell(0, 0, r * .1, r * .15); paint('#1A0F28'); ctx.fillStyle = '#FFF'; ell(-r * .03, -r * .05, r * .035, r * .045); ctx.fill(); } ctx.restore(); }
    ctx.strokeStyle = '#1A0F28'; ctx.lineWidth = r * .04; ctx.lineCap = 'round'; ctx.beginPath(); if (o.star) ctx.arc(x, y + r * .15, r * .18, .2, Math.PI - .2); else { ctx.moveTo(x - r * .12, y + r * .22); ctx.lineTo(x + r * .1, y + r * .18); } ctx.stroke();
  }
  line('V1', 13, (p, lt, d, t) => {
    const e8 = beatLen() / 2, b0 = bt(t, lt, 0), steps = ['Step 1: what is asked?', 'Step 2: try small cases', 'Step 3: spot the pattern', 'Step 4: check it twice', 'ANSWER!'];
    const cur = Math.floor((lt - b0) / e8), done = cur >= steps.length - 1;
    // tiled background
    fillAll('#C8FF4A'); for (let j = 0; j < 12; j++) for (let i = 0; i < 20; i++) { poly(starPts(i * 100 + (j % 2) * 50, j * 100, 14, .45, 5)); ctx.fillStyle = (i + j) % 3 ? '#FFE81F' : '#FF6FC8'; ctx.fill(); }
    wordArt("Welcome to Strawberry's Homepage!", W / 2 - 190, 200, 62, { shape: 'arch', amp: 36, phase: t * 3 });
    ctx.fillStyle = lg(0, 0, W, 0, [[0, '#FF2A6A'], [.2, '#FF9A1A'], [.4, '#FFE81F'], [.6, '#3BFF6A'], [.8, '#1FB8FF'], [1, '#B04BFF']]); ctx.fillRect(120, 290, 1680, 12);
    strawberry(470, 640, 210, { star: done });
    ctx.save(); ctx.translate(640, 690); ctx.scale(75, 75); _toyHand(0, 0, done ? 'thumb' : 'open', Math.PI * .85, 1, '#FBFBFF', { cuff: '#E4E6F0' }); ctx.restore();
    // the chain of links
    const lx = 880, ly = 390;
    for (let i = 0; i < steps.length; i++) {
      if (lt < b0 + (i - .5) * e8) continue;
      const y = ly + i * 100, visited = i < cur, active = i === cur, s = steps[i], big = i === steps.length - 1;
      if (i > 0) { ctx.fillStyle = '#1A0F28'; poly([[lx + 30, y - 58], [lx + 44, y - 58], [lx + 44, y - 42], [lx + 56, y - 42], [lx + 37, y - 26], [lx + 18, y - 42], [lx + 30, y - 42]]); ctx.fill(); }
      const col = big && i <= cur ? EP.red : visited ? '#6A0DAD' : '#0000EE', sz = big ? 72 : 46;
      txt(s, lx, y, sz, col, { font: big ? 'archivo' : 'code', align: 'left' });
      ctx.fillStyle = col; ctx.fillRect(lx, y + sz * .5, textW(s, sz, big ? 'archivo' : 'code'), 4);
      if (active && !big) cursor98(lx + textW(s, sz, 'code') * .6, y + 8, { kind: 'hand', s: 2.4, click: frac((lt - b0) / e8) * 1.5 });
    }
    if (done) burst('!', 560, 400, 70, { pop: pop(lt, b0 + (steps.length - 1) * e8, .15), col: EP.yellow, ink: EP.red });
    // under construction + hit counter
    ctx.save(); ctx.translate(250, 880); ctx.rotate(-.05); rrect(-160, -50, 320, 100, 6); ctx.save(); ctx.clip(); ctx.fillStyle = EP.yellow; ctx.fillRect(-160, -50, 320, 100); ctx.fillStyle = '#000'; for (let i = -8; i < 8; i++) { ctx.save(); ctx.translate(i * 40 + (t * 60) % 40, 0); ctx.transform(1, 0, -1, 1, 0, 0); ctx.fillRect(0, -50, 18, 100); ctx.restore(); } ctx.restore(); rrect(-130, -26, 260, 52, 4); paint(EP.yellow, '#000', 3); txt('UNDER CONSTRUCTION', 0, 2, 24, '#000', { font: 'archivo', maxW: 240 }); ctx.restore();
    txt('You are visitor no.', 1350, 880, 26, '#1A0F28', { font: 'archivo', align: 'right' }); ctx.fillStyle = '#000'; ctx.fillRect(1370, 850, 260, 62); segText(String(1337 + Math.floor(lt * 7)).padStart(6, '0'), 1382, 857, 48, EP.lime, { off: '#0A2A0A' });
    nameTip('o1 · STRAWBERRY', 470, 360, { pop: pop(lt, .08), to: [470, 420], size: 30 });
  });

  // =====================================================================================
  // V1.14 Newsom vetoes, doesn't blink — a strobe on the eighths into GAVIN's unblinking eyes; VETO slams onto SB 1047 on the beat;
  // the LED counter reads BLINKS: 0.
  line('V1', 14, (p, lt, d, t) => {
    const b0 = bt(t, lt, 0), sk = strobeK(t, 2, .35), push = 1 + .06 * p;
    setLight({ rim: '#FFFFFF', rimK: .9 });
    camBegin(W / 2, H / 2, push);
    fillAll(sk > .1 ? '#F4F4FF' : '#08060E');
    if (sk <= .1) { ctx.save(); ctx.globalCompositeOperation = 'lighter'; ctx.fillStyle = 'rgb(120 120 255 / .1)'; poly([[400, -40], [1100, -40], [1500, 1200], [0, 1200]]); ctx.fill(); ctx.restore(); }
    toy(700, 1640, 128, { ...WHO.gavin.o, eyes: 'wide', look: [.2, -.1], mouth: 'flat', brows: 'flat', shadow: false, hL: [-2.6, -4], hR: [2.6, -4], sil: undefined, rim: '#FFFFFF' });
    camEnd();
    // the strobe fixture
    gloss(pfRR(1560, 200, 240, 150, 20), '#2A2A34', { box: [1560, 200, 240, 150], lw: 5, rim: null }); rrect(1585, 225, 190, 100, 10); paint(sk > .1 ? '#FFFFFF' : '#606070'); if (sk > .1) glow(1680, 275, 380, '#FFFFFF', 1);
    // the bill
    ctx.save(); ctx.translate(1440, 640); ctx.rotate(.06); rrect(-210, -260, 420, 520, 6); paint('#FBFAF2', EP.line, 5);
    txt('SB 1047', 0, -200, 64, '#15121C', { font: 'abril' }); txt('Safe and Secure Innovation', 0, -140, 22, '#444', { font: 'abril' }); txt('for Frontier AI Models Act', 0, -112, 22, '#444', { font: 'abril' });
    ctx.fillStyle = 'rgb(20 20 30 / .3)'; for (let i = 0; i < 9; i++) ctx.fillRect(-170, -60 + i * 30, i % 4 === 3 ? 200 : 340, 7);
    ctx.restore();
    slamStamp('VETO', 1440, 660, 130, EP.red, -.18, clamp((lt - b0) / .12));
    txt('BLINKS', 150, 180, 30, sk > .1 ? '#000' : '#FFF', { font: 'archivo', align: 'left' }); ctx.fillStyle = '#000'; ctx.fillRect(150, 205, 110, 96); segText('0', 175, 215, 76, EP.red, { off: '#3A0000' });
    nameTip(WHO.gavin.name, 700, 150, { pop: pop(lt, .08), sub: 'GOVERNOR OF CALIFORNIA', to: [700, 260] });
    if (sk > .1) strobe(.18);
  });

  // =====================================================================================
  // V1.15 Hinton takes his medal, scolds — the award show: velvet curtains, a spotlight, GEOFFREY holds up the Nobel medal in the confetti…
  // then wags a finger at us and a Windows warning pops up beside him.
  line('V1', 15, (p, lt, d, t) => {
    const b0 = bt(t, lt, 0), b2 = bt(t, lt, 2), scold = lt >= b2;
    setLight({ rim: EP.gold, rimK: .7 });
    fillAll('#3A0008'); for (let i = 0; i < 24; i++) { const x = i * 85 - 20 + Math.sin(t * 1.5 + i) * 4; ctx.fillStyle = lg(x, 0, x + 85, 0, [[0, '#5A000E'], [.5, '#C0102A'], [1, '#5A000E']]); ctx.fillRect(x, 0, 86, H); }
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; ctx.fillStyle = lg(0, 0, 0, 1000, [[0, 'rgb(255 240 200 / .35)'], [1, 'rgb(255 240 200 / .08)']]); poly([[640, -20], [820, -20], [1100, 1000], [360, 1000]]); ctx.fill(); ctx.restore();
    gloss(pfRR(-50, 900, W + 100, 200, 0), '#2A1810', { box: [0, 900, W, 200], lw: 0, line: false, rim: null });
    // Hinton at the podium
    const wag = scold ? Math.sin((lt - b2) * 26) * .6 : 0, lift = pop(lt, b0 - .05, .2);
    toy(730, 1010, 56, { ...WHO.hinton.o, hL: [-2.4 - lift * .6, lerp(-6, -10.4, lift)], gL: 'fist', holdL: s => goldMedal(0, -s * .2 - 50, 62, { text: 'NOBEL', ribbon: EP.blue, glint: .5 + .5 * kick(t, 4) }), hR: scold ? [3.1 + wag, -9.3] : [2.4, -4.4], gR: scold ? 'point' : 'open', mouth: scold ? 'open' : 'grin', brows: scold ? 'angry' : 'none', eyes: scold ? 'angry' : 'happy', turn: scold ? .1 : -.1 });
    gloss(pfPts([[560, 1080], [900, 1080], [870, 800], [590, 800]]), '#8A6A2A', { box: [560, 800, 340, 280], lw: 5, rim: EP.gold }); ctx.fillStyle = EP.gold; ell(730, 870, 50, 50); ctx.fill(); txt('NOBEL', 730, 872, 22, '#6A4A00', { font: 'archivo' });
    confetti(t, t - lt + b0, 70, { cols: [EP.gold, '#FFFFFF', EP.yellow] });
    if (scold) win98Dialog(1400, 540, 700, 'Warning', 'AI may one day\noutsmart us all.\nPlease be careful.', { icon: 'warn', k: clamp((lt - b2) / .14), buttons: ['OK'] });
    nameTip(WHO.hinton.name, 730, 150, { pop: pop(lt, .08), sub: 'NOBEL PRIZE IN PHYSICS', to: [730, 300] });
  });

  // =====================================================================================
  // V1.16 Demis wins for protein folds — early CGI: a rainbow protein ribbon folds itself in 3D over a cyan grid (FOLDING… → FOLDED 100%),
  // DEMIS raises his medal on the beat and the confetti falls.
  function protein(t, k, cx, cy, sc) {
    const N = 140, ry = t * .9, pts = [];
    for (let i = 0; i < N; i++) {
      const u = i / (N - 1), sx = (u - .5) * 6, st = [sx, Math.sin(u * 20) * .1, 0];
      const seg = Math.min(4, Math.floor(u * 5)), su = u * 5 - seg, hc = [[-1.2, -.6, 0], [.6, -.9, .5], [1.1, .5, -.4], [-.3, .9, .6], [-1.0, .3, -.7]][seg];
      const hel = [hc[0] + Math.cos(su * 18) * .55, hc[1] + (su - .5) * 1.4, hc[2] + Math.sin(su * 18) * .55];
      const q = [lerp(st[0], hel[0], k), lerp(st[1], hel[1], k), lerp(st[2], hel[2], k)];
      const X = q[0] * Math.cos(ry) + q[2] * Math.sin(ry), Z = -q[0] * Math.sin(ry) + q[2] * Math.cos(ry), s = 4 / (4 + Z);
      pts.push([cx + X * sc * s, cy + q[1] * sc * s, Z, s]);
    }
    const segs = []; for (let i = 0; i < N - 1; i++) segs.push([i, (pts[i][2] + pts[i + 1][2]) / 2]); segs.sort((a, b) => b[1] - a[1]);
    ctx.lineCap = 'round';
    for (const [i] of segs) { const a = pts[i], b = pts[i + 1], col = `hsl(${(i / N) * 300} 95% ${48 + 14 * (1 - a[3])}%)`; ctx.strokeStyle = EP.line; ctx.lineWidth = 30 * a[3]; ctx.beginPath(); ctx.moveTo(a[0], a[1]); ctx.lineTo(b[0], b[1]); ctx.stroke(); ctx.strokeStyle = col; ctx.lineWidth = 22 * a[3]; ctx.stroke(); ctx.strokeStyle = 'rgb(255 255 255 / .45)'; ctx.lineWidth = 6 * a[3]; ctx.beginPath(); ctx.moveTo(a[0] - 4, a[1] - 5); ctx.lineTo(b[0] - 4, b[1] - 5); ctx.stroke(); }
  }
  line('V1', 16, (p, lt, d, t) => {
    const b1 = bt(t, lt, 1), k = ease(clamp(lt / (d * .8)));
    setLight({ rim: EP.cyan, rimK: .8 });
    bgGrad([[0, '#000A2A'], [.6, '#003A7A'], [1, '#00A8C8']], { y1: 760 });
    ctx.save(); ctx.beginPath(); ctx.rect(-900, 760, W + 1800, H); ctx.clip(); fillAll('#002030'); ctx.strokeStyle = alpha(EP.cyan, .6); ctx.lineWidth = 2; ctx.beginPath(); for (let i = -20; i <= 20; i++) { ctx.moveTo(W / 2 + i * 50, 760); ctx.lineTo(W / 2 + i * 300, H + 200); } for (let j = 0; j < 9; j++) { const y = 760 + (H - 760) * ((j + frac(t * .5)) / 9) ** 1.7; ctx.moveTo(-900, y); ctx.lineTo(W + 900, y); } ctx.stroke(); ctx.restore();
    glow(1180, 480, 500, EP.cyan, .35);
    protein(t, k, 1180, 470, 170);
    const pct = Math.round(k * 100);
    rrect(1380, 820, 460, 110, 10); paint('rgb(0 0 20 / .6)', EP.cyan, 3);
    txt(pct < 100 ? 'FOLDING...' : 'FOLDED!', 1400, 850, 28, pct < 100 ? '#FFFFFF' : EP.lime, { font: 'archivo', align: 'left' }); txt(pct + '%', 1820, 850, 28, '#FFFFFF', { font: 'archivo', align: 'right' });
    progress98(1400, 875, 420, 38, k);
    const lift = pop(lt, b1 - .05, .2);
    toy(400, 1010, 50, { ...WHO.demis.o, hR: [2.5 + lift * .5, lerp(-5.5, -10.6, lift)], gR: 'fist', hold: s => goldMedal(0, -s * .2 - 50, 58, { text: 'NOBEL', ribbon: EP.magenta, glint: lift }), hL: [-2.5, -4.2], mouth: lift > .5 ? 'grin' : 'smile', eyes: lift > .5 ? 'happy' : 'dot', jump: lift > .5 ? Math.abs(Math.sin(bpOf(t) * Math.PI)) * .5 : 0 });
    confetti(t, t - lt + b1, 60, { x0: 0, x1: 900 });
    nameTip(WHO.demis.name, 400, 240, { pop: pop(lt, .08), sub: 'NOBEL PRIZE IN CHEMISTRY', to: [400, 400] });
  });
})();

;
// ---- styles/eurodance/ch/c03_chorus1.js ----
// c03_chorus1 — Chorus 1 (V1.16 → V2.1, 40 beats): SOFTMAX's first dance break, in the chroma-key studio. It sets the chorus language the
// later choruses build on (see the "chorus kit" helpers below; copy them into your own IIFE):
//   hook line      the lyric lands in extruded chrome word by word on its sung (eighth-snapped) time, WE DIDN'T START / THE SCALING, SCALING
//                  hot and biggest with a glint and a shake; the lights and laser fans slam on at the downbeat; hideCaption() while it's up.
//   training       TRAINING.EXE: a candy computer pumping a GPU barbell once per beat, an EPOCH counter that never stops, a loss curve,
//                  and a progress bar stuck at 99% ("Time remaining: always"). SOFTMAX sings in a picture-in-picture box.
//   curves         the 3D Pipes curve (pipeStair): an exponential staircase of screensaver pipe that climbs one notch per beat and runs off the
//                  top of the frame (pass a bigger `growth` in later choruses: steeper every chorus).
//   hook line 2    the video wall carries the hook, SOFTMAX vogues in close-up, confetti cannons fire on SCALING.
//   preordain      "No" is SOFTMAX's finger wag and a NO! burst; then the whole trio shrugs in unison under spinning chrome question marks.
//   contain it     a containment failure: "SCALING.EXE has performed an illegal operation", the cursor clicks Close, and the pipes burst
//                  out through the dialog (RGB split, shake, strobe) and off every edge of the frame.
//   the tail       "Deep, deep, deep…": a stutter edit. The frame snaps back and repeats on each "deep" as the picture sinks into ocean blue
//                  and DEEP stamps bigger each time; a whale's tail flicks up on the last one, into V2.1's DeepSeek.
// The colour run: hot-magenta studio / Win98 teal / screensaver black / purple video wall / daylight blue sky / club stage / ocean blue.
(() => {
  const SPAN = span('C1'), B0 = bpOf(SPAN.start), LN = linesOf('C1');
  const rb = t => bpOf(t) - B0;                                             // beats since the chorus began
  const tb = n => onBeat(0, B0 + n);                                         // song time of relative beat n
  const snap8 = x => onBeat(0, Math.round(bpOf(x) * 2) / 2);                 // a time, snapped to the eighth-note grid
  const wordT = (ln, i) => snap8(_karaTimes(ln).tm[i][0]);                   // sung time of word i of a line (from the karaoke alignment)
  const pop = (t, t0, dur = .18) => t < t0 ? 0 : backOut(clamp((t - t0) / dur), 2.2);
  const kickAt = (t, t0, dur = .25) => { const k = (t - t0) / dur; return k >= 0 && k < 1 ? 1 - k : 0; };
  // sub-shot boundaries, from the sung lines (cut on the beat grid)
  const CUT = {
    train: snap8(LN[1].start),                  // "It was always training,"
    curves: wordT(LN[1], 4),                     // "and the curves kept gaining,"
    hook2: snap8(LN[2].start),                   // "We didn't start the scaling"
    no: snap8(LN[3].start),                      // "No, we didn't preordain it,"
    contain: wordT(LN[3], 5),                    // "but we can't contain it!"
  };
  // the "Deep, deep, deep…" stutter: the tail's words, straight from the alignment (they sit between the last chorus line and V2.1)
  const DEEPS = (typeof KARAOKE_WORDS !== 'undefined' ? KARAOKE_WORDS : []).filter(w => w[0] > LN[3].end && w[0] < SPAN.end && /deep/i.test(w[2])).map(w => w[0]);

  // =====================================================================================================
  // THE CHORUS KIT (generic: pass the chorus's own lines)
  // =====================================================================================================
  // hookWords(ln, t, o): the hook in chrome, word by word as sung. Row 1 = the first three words, row 2 = the rest (THE SCALING).
  // o.y1 / o.y2 (row centres), o.s1 / o.s2 (sizes), o.x (centre), o.styles ([row1, THE, SCALING]), o.alpha. Returns the land time of the last word.
  function hookWords(ln, t, o = {}) {
    const { words } = _karaTimes(ln), W1 = words.slice(0, 3), W2 = words.slice(3), cx = o.x ?? W / 2, gap = 34;
    const clean = w => w.replace(/[^A-Za-z']/g, '').toUpperCase();
    const row = (ws, off, size, y, styleOf) => {
      const labels = ws.map(clean), wd = labels.map(w => textW(w, size, 'archivo')), tot = wd.reduce((a, v) => a + v, 0) + gap * (ws.length - 1);
      let x = cx - tot / 2;
      labels.forEach((w, i) => {
        const at = wordT(ln, off + i), k = clamp((t - at) / .13);
        if (k > 0) {
          const last = off + i === words.length - 1, s = lerp(last ? 3 : 2.4, 1, backOut(k, last ? 1.5 : 1.2));
          chromeText(w, x + wd[i] / 2, y - (last ? kick(t, 7) * 5 : 0), size, { style: styleOf(i, last), italic: .14, depth: Math.round(size * .11), s, alpha: clamp(k * 3) * (o.alpha ?? 1) });
          if (last && t - at < .5) sweepGlint(x, x + wd[i], y - size * .2, (t - at - .1) / .4, size * .9);
        }
        x += wd[i] + gap;
      });
      return tot;
    };
    row(W1, 0, o.s1 ?? 118, o.y1 ?? 190, () => o.styles?.[0] ?? 'chrome');
    row(W2, 3, o.s2 ?? 170, o.y2 ?? 350, (i, last) => last ? (o.styles?.[2] ?? 'hot') : (o.styles?.[1] ?? 'gold'));
    return wordT(ln, words.length - 1);
  }
  // pipeRun(pts, k, col, w): a length of Windows 3D Pipes pipe along a right-angled polyline, drawn up to k (0..1) of its length,
  // with the screensaver's tube shading and a glossy ball at every joint. Returns the tip.
  function pipeRun(pts, k, col, w) {
    let total = 0; const L = []; for (let i = 1; i < pts.length; i++) { const d = Math.hypot(pts[i][0] - pts[i - 1][0], pts[i][1] - pts[i - 1][1]); L.push(d); total += d; }
    let left = total * clamp(k), tip = pts[0];
    ctx.save(); ctx.lineCap = 'butt';
    for (let i = 1; i < pts.length && left > 0; i++) {
      const [ax, ay] = pts[i - 1], u = Math.min(1, left / L[i - 1]), bx = ax + (pts[i][0] - ax) * u, by = ay + (pts[i][1] - ay) * u; left -= L[i - 1];
      const ang = Math.atan2(by - ay, bx - ax), nx = -Math.sin(ang) * w, ny = Math.cos(ang) * w;
      ctx.fillStyle = lg(ax + nx, ay + ny, ax - nx, ay - ny, [[0, shade(col, .55)], [.3, col], [.45, tint(col, .6)], [.6, col], [1, shade(col, .6)]]);
      ctx.beginPath(); ctx.moveTo(ax + nx, ay + ny); ctx.lineTo(bx + nx, by + ny); ctx.lineTo(bx - nx, by - ny); ctx.lineTo(ax - nx, ay - ny); ctx.closePath(); ctx.fill();
      if (i > 1) glossBall(ax, ay, w * 1.3, w * 1.3, col, { line: false, rim: null });
      tip = [bx, by];
    }
    ctx.restore();
    return tip;
  }
  // pipeStair(t, t0, o): "and the curves kept gaining": a pipe that climbs an exponential staircase, one notch per beat from t0.
  // o.x0 / o.y0 (the foot), o.dx (step), o.h0 (first rise), o.growth (rise ratio per notch: steeper every chorus), o.n (notches), o.col, o.w,
  // o.grow (fraction of a beat each notch takes to extend). Returns the tip.
  function pipeStair(t, t0, o = {}) {
    const n = o.n ?? 10, dx = o.dx ?? 150, g = o.growth ?? 1.5, pts = [[o.x0 ?? 200, o.y0 ?? 860]];
    let h = o.h0 ?? 36;
    for (let i = 0; i < n; i++) { const [x, y] = pts.at(-1); pts.push([x + dx, y], [x + dx, y - h]); h *= g; }
    const bt = (t - t0) / beatLen(), notch = Math.floor(bt), fr = clamp(frac(bt) / (o.grow ?? .45));
    if (bt < 0) return pts[0];
    const segs = Math.min(n * 2, notch * 2 + easeOut(fr) * 2), sub = pts.slice(0, Math.floor(segs) + 2);
    // grow segment by segment (each notch: across, then up), so the tip moves at the notch's pace whatever the segment lengths
    const whole = Math.floor(segs), part = segs - whole; if (whole + 1 < sub.length) { const [ax, ay] = sub[whole], [bx, by] = sub[whole + 1]; sub[whole + 1] = [ax + (bx - ax) * part, ay + (by - ay) * part]; }
    return pipeRun(sub, 1, o.col ?? '#E8342A', o.w ?? 22);
  }
  // confetti falling since t0 (glossy chips), optionally fired from cannons at the bottom corners (o.cannon).
  function confetti(t, t0, n = 80, o = {}) {
    if (t < t0) return; const cols = o.cols ?? [EP.magenta, EP.cyan, EP.yellow, EP.lime, EP.white], age = t - t0;
    for (let i = 0; i < n; i++) {
      let x, y;
      if (o.cannon) { const sd = i % 2 ? 1 : -1, v = 2300 + hash2(i, 1) * 1300, a = -Math.PI / 2 - sd * (.1 + hash2(i, 2) * .45); x = W / 2 + sd * 760 + Math.cos(a) * v * age * .9 + Math.sin(age * 4 + i) * 20; y = 1080 + Math.sin(a) * v * age + 1500 * age * age; }
      else { x = hash2(i, 1) * W + Math.sin(age * 3 + i) * 30; y = -60 - hash2(i, 2) * 300 + age * (260 + hash2(i, 3) * 200); }
      if (y > H + 40 || y < -80) continue;
      const r = age * 7 + i; ctx.save(); ctx.translate(x, y); ctx.rotate(r); ctx.scale(1, Math.cos(r * 1.3)); ctx.fillStyle = cols[i % cols.length]; ctx.fillRect(-10, -6, 20, 12); ctx.restore();
    }
  }
  // the trio's pieces
  function podium(x, y, w, t, rim = EP.cyan) {
    const h = 64, ry = w * .2;
    ell(x, y + h + 10, w * .55, ry * .7); ctx.fillStyle = 'rgb(0 0 30 / .3)'; ctx.fill();
    gloss(() => { ctx.moveTo(x - w / 2, y); ctx.ellipse(x, y, w / 2, ry, 0, Math.PI, 0, true); ctx.lineTo(x + w / 2, y + h); ctx.ellipse(x, y + h, w / 2, ry, 0, 0, Math.PI); ctx.closePath(); }, '#C8D0E4', { box: [x - w / 2, y - ry, w, h + ry * 2], rim, lw: 4, spec: 1 });
    ell(x, y, w / 2, ry); ctx.fillStyle = lg(x - w / 2, 0, x + w / 2, 0, [[0, '#8A94B8'], [.5, '#FFFFFF'], [1, '#8A94B8']]); ctx.fill(); ctx.strokeStyle = EP.line; ctx.lineWidth = 4; ctx.stroke();
    for (let i = 0; i < 12; i++) { const a = i / 12 * TAU + t * 1.2; if (Math.sin(a) < 0) continue; ctx.fillStyle = [EP.magenta, EP.cyan, EP.yellow][i % 3]; ell(x + Math.cos(a) * w / 2, y + h * .4 + Math.sin(a) * ry, 10, 6); ctx.fill(); }
  }
  function floatBooth(x, y, w, t, o = {}) {
    const fy = y + Math.sin(t * 2.4) * 10, bb = bpOf(t);
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; for (const sd of [-1, 1]) { ctx.fillStyle = lg(0, fy + w * .36, 0, fy + w * .36 + 120, [[0, alpha(EP.cyan, .7)], [1, alpha(EP.cyan, 0)]]); poly([[x + sd * w * .3 - 18, fy + w * .36], [x + sd * w * .3 + 18, fy + w * .36], [x + sd * w * .3 + 34, fy + w * .36 + 120 + kick(t, 6) * 30], [x + sd * w * .3 - 34, fy + w * .36 + 120 + kick(t, 6) * 30]]); ctx.fill(); } ctx.restore();
    const sc = o.scratch ?? kickAt(bb, Math.floor(bb), .3);
    djClawd(x, fy + w * .1, w * .056, { shades: true, aL: 1.1 + Math.sin(bb * Math.PI) * .35, aR: lerp(-.1, -.45, sc), mouth: 'grin', dy: -bounce(t) * .3, ...(o.clawd ?? {}) });
    djBooth(x, fy, w, t, { scratch: sc });
  }
  const tokenAt = (t, x, y, s, mv, o = {}) => toy(x, y, s, { ...CAST.token.o, ...dance(mv, bpOf(t) - .15), mouth: 'grin', ...o });
  const softAt = (t, x, y, s, mv, o = {}) => toy(x, y, s, { ...CAST.softmax.o, ...dance(mv, bpOf(t)), talk: singK(t), ...o });
  // the chroma-key studio: a gradient sky, rays, a checkerboard to infinity, floating chrome toys
  function studio(t, o = {}) {
    const hz = o.horizon ?? 640;
    bgGrad(o.sky ?? [[0, '#1A0450'], [.55, '#8A12C8'], [1, '#FF3FA8']], { y1: hz });
    rays(W / 2, hz - 40, 22, o.rays ?? 'rgb(255 255 255 / .07)', t * .2);
    for (let i = 0; i < 50; i++) { const a = .3 + .7 * Math.abs(Math.sin(t * (1 + hash2(i, 3) * 3) + i)); ctx.fillStyle = `rgb(255 255 255 / ${.45 * a * hash2(i, 4)})`; ctx.fillRect(hash2(i, 1) * W, hash2(i, 2) * (hz - 80), 3, 3); }
    glow(W / 2, hz, 800, o.fog ?? '#FF6FC8', .45);
    checkerFloor(t, { horizon: hz, a: o.a ?? '#F4F0FF', b: o.b ?? '#3A0E7A', speed: o.speed ?? .9, fog: o.fog ?? '#FF6FC8', fogH: 150 });
    if (o.toys !== false) {
      glossBall(150 + Math.sin(t * .9) * 20, 470 + Math.sin(t * 1.3) * 18, 70, 70, '#D8DEEA', { rim: EP.magenta, rimK: .8 });
      spin3D('torus', 1790, 560 + Math.sin(t * 1.1) * 16, 85, [t * 1.3 + .6, t * .9, .35], { mode: 'chrome' });
      spin3D('octa', 250, 250, 44, [t * 1.7, t * 1.1 + 1, .2], { col: EP.cyan });
      spin3D('cube', 1700, 330, 40, [t * 1.2 + 1, t * 1.6, .3], { col: EP.yellow });
    }
  }

  // =====================================================================================================
  // A. "We didn't start the scaling": the lights slam on in the studio; the hook lands in chrome word by word.
  // =====================================================================================================
  function shotHook1(t) {
    hideCaption();
    const r = rb(t), on = clamp((r - .5) / .06);
    const sh = shakeAt(t, t, wordT(LN[0], 4), .3, 16);
    camBegin(W / 2 - sh[0], H / 2 - sh[1], 1 + .03 * clamp(r / 4));
    studio(t, {});
    const open = easeOut(clamp((r - .5) / .6));
    laserFan(170, 1080, t, { n: 9, cols: [EP.cyan, EP.white], angle: -1.05, spread: 1.0 * open + .01, sweep: .35, alpha: open });
    laserFan(W - 170, 1080, t, { n: 9, cols: [EP.magenta, EP.yellow], angle: -2.09, spread: 1.0 * open + .01, sweep: .35, phase: 2, alpha: open });
    laserFan(W / 2, 620, t, { n: 13, cols: [EP.laser, EP.cyan], angle: -Math.PI / 2, spread: 2.6 * open + .01, sweep: .2, alpha: .55 * open });
    setLight({ rim: EP.cyan, rimK: .85 });
    podium(W / 2, 935, 330, t, EP.magenta);
    softAt(t, W / 2, 942, 40, r < 2.9 ? 'sing' : 'raise', { turn: Math.sin(t * 1.3) * .35, swing: .5 + Math.sin(t * 7) * .25 });
    tokenAt(t, 420, 1000, 44, 'runningMan');
    floatBooth(1500, 690, 400, t);
    camEnd();
    // lights off for the "We" pickup: a lone spot on SOFTMAX, then the slam
    if (on < 1) {
      ctx.save(); ctx.fillStyle = `rgb(6 0 20 / ${.86 * (1 - on)})`; ctx.fillRect(-100, -100, W + 200, H + 200);
      ctx.globalCompositeOperation = 'lighter'; ctx.fillStyle = `rgb(255 230 255 / ${.18 * (1 - on)})`; poly([[W / 2 - 50, -20], [W / 2 + 50, -20], [W / 2 + 330, 960], [W / 2 - 330, 960]]); ctx.fill(); ctx.restore();
    }
    hookWords(LN[0], t, { y1: 200, y2: 368, s1: 112, s2: 168 });
    lensFlare(1560, 470, (.6 + .2 * Math.sin(t * 3)) * on);
    if (r >= .5 && r < .9) strobe(.9 * (1 - (r - .5) / .4));
    else strobe(strobeK(t, 1, .16) * .22 * on);
    if (r > .5 && r < .62) fx({ rgb: 1 - (r - .5) / .12 });
  }

  // =====================================================================================================
  // B. "It was always training,": TRAINING.EXE — a candy computer pumps a GPU barbell once per beat; the epochs never stop,
  // the loss slides down, the progress bar hangs at 99%. SOFTMAX sings in a picture-in-picture box.
  // =====================================================================================================
  function barbell(w, s) {
    ctx.fillStyle = lg(0, -6, 0, 6, [[0, '#FFFFFF'], [.5, '#8A94B0'], [1, '#3A4058']]); ctx.fillRect(-w / 2, -s * .12, w, s * .24); ctx.strokeStyle = EP.line; ctx.lineWidth = 3; ctx.strokeRect(-w / 2, -s * .12, w, s * .24);
    for (const sd of [-1, 1]) for (let i = 0; i < 2; i++) { const px = sd * (w / 2 - s * (.35 + i * .55)); gloss(pfRR(px - s * .25, -s * (1.3 - i * .25), s * .5, s * (2.6 - i * .5), s * .12), '#23262F', { box: [px - s * .25, -s * 1.3, s * .5, s * 2.6], lw: 3, spec: .7 }); ctx.fillStyle = EP.laser; ctx.fillRect(px - s * .18, -s * (1.15 - i * .25), s * .36, s * .1); }
  }
  function shotTrain(t) {
    const r = rb(t), l = t - CUT.train, bb = bpOf(t), nb = Math.floor(bpOf(t) - bpOf(CUT.train) + .001), up = Math.exp(-frac(bb) * 4.5);
    desktop98({ icons: [['computer', 'My Computer', 110, 190], ['cd', 'Scaling Hits', 110, 380], ['folder', 'datasets', 110, 570], ['bin', 'Recycle Bin', 110, 760]] });
    const k = clamp(l / .12);
    win98Window(230, 132, 1230, 790, 'TRAINING.EXE', (cw, ch) => {
      // the gym (a CD-ROM fitness video)
      ctx.fillStyle = lg(0, 0, 0, ch, [[0, '#2A0A6A'], [.7, '#C8208A'], [1, '#FF8A3A']]); ctx.fillRect(0, 0, 700, ch);
      ctx.save(); ctx.beginPath(); ctx.rect(0, 0, 700, ch); ctx.clip();
      checkerFloor(t, { horizon: 520, a: '#FFD8F0', b: '#6A1A8A', speed: 0, cx: 350, fog: '#FF8AC8', fogH: 60 });
      pixText('NO PAIN NO GAIN', 350, 40, 6, EP.yellow, { align: 'center', glow: true });
      const hy = lerp(-3.0, -10.8, up), s = 36;
      gumdrop(350, 640, s, { col: CANDY.snow, label: 'MODEL', headband: EP.magenta, face: up > .5 ? 'angry' : 'closed', mouth: up > .5 ? 'grin' : 'O', sweat: .8, hL: [-3.9, hy], hR: [3.9, hy], gL: 'fist', gR: 'fist', sq: up * .06, rim: EP.magenta });
      ctx.save(); ctx.translate(350, 640 + hy * s); barbell(560, 38); ctx.restore();
      if (up > .7) pixText('REP ' + (nb + 1), 560, 150, 5, '#FFFFFF', { align: 'center', edge: '#000' });
      ctx.restore();
      // the stats panel
      ctx.fillStyle = EP.w98; ctx.fillRect(700, 0, cw - 700, ch);
      bevel(724, 20, cw - 748, 150, { sunken: true, fill: '#000' });
      txt('EPOCH', 750, 50, 26, EP.laser, { font: 'code', align: 'left' });
      segText(String(41 + Math.floor(Math.max(0, l) * 9.4)).padStart(6, ' '), 750, 72, 78, EP.laser, { off: '#062006' });
      // loss curve
      const gx = 724, gy = 190, gw = cw - 748, gh = 280; bevel(gx, gy, gw, gh, { sunken: true, fill: '#FFFFFF' });
      ctx.strokeStyle = 'rgb(0 0 128 / .15)'; ctx.lineWidth = 1; ctx.beginPath(); for (let i = 1; i < 6; i++) { ctx.moveTo(gx, gy + i * gh / 6); ctx.lineTo(gx + gw, gy + i * gh / 6); } ctx.stroke();
      txt('LOSS', gx + 14, gy + 22, 22, '#000', { font: 'archivo', align: 'left' });
      const kk = clamp(.35 + l / 1.7); ctx.beginPath();
      for (let i = 0; i <= 60 * kk; i++) { const u = i / 60; ctx.lineTo(gx + 16 + u * (gw - 32), gy + 40 + (gh - 70) * (1 - Math.exp(-u * 4.2)) + Math.sin(u * 50) * 6 * (1 - u)); }
      ctx.strokeStyle = '#E0201A'; ctx.lineWidth = 5; ctx.stroke();
      // the progress bar that never finishes
      txt('Training...', 724, 510, 28, '#000', { font: 'archivo', align: 'left' });
      const pk = Math.min(.99, 1 - Math.exp(-(l + .4) * 3.2));
      progress98(724, 535, gw, 46, pk); txt(Math.floor(pk * 100) + '%', gx + gw, 510, 28, '#000', { font: 'archivo', align: 'right' });
      txt('Time remaining:', 724, 616, 32, '#000', { font: 'archivo', align: 'left' });
      txt('ALWAYS', 724 + textW('Time remaining: ', 32, 'archivo'), 616, 32, '#C00000', { font: 'archivo', align: 'left' });
      cursor98(724 + gw * .72, 660 + Math.sin(l * 3) * 4, { kind: 'wait', s: 2.2 });
    }, { icon: 'exe', menu: ['File', 'Edit', 'Train', 'Help'], k });
    // SOFTMAX live in a PiP box
    const px = 1490, py = 300, pw = 360, ph = 440;
    ctx.save(); ctx.fillStyle = 'rgb(0 0 0 / .35)'; rrect(px + 10, py + 12, pw, ph, 18); ctx.fill();
    rrect(px - 6, py - 6, pw + 12, ph + 12, 22); ctx.fillStyle = lg(px, py, px + pw, py + ph, [[0, '#FFFFFF'], [.5, '#8A94B8'], [1, '#FFFFFF']]); ctx.fill(); ctx.strokeStyle = EP.line; ctx.lineWidth = 4; ctx.stroke();
    rrect(px, py, pw, ph, 16); ctx.clip(); bgGrad([[0, '#FF3FAE'], [1, '#7A1FFF']], { y0: py, y1: py + ph });
    rays(px + pw / 2, py + 200, 16, 'rgb(255 255 255 / .12)', t * .4);
    setLight({ rim: EP.cyan, rimK: .7 });
    softAt(t, px + pw / 2, py + 820, 64, 'sing', { shadow: false, swing: Math.sin(t * 5) * .3 });
    ctx.restore();
    if (frac(t * 1.2) < .7) { ell(px + 34, py + 36, 11); ctx.fillStyle = EP.red; ctx.fill(); }
    pixText('LIVE', px + 54, py + 26, 4, '#FFFFFF', { edge: '#000' });
    pixText('SOFTMAX', px + pw / 2, py + ph - 42, 5, '#FFFFFF', { align: 'center', edge: '#000' });
    if (l < .1) cutFX('flash');
  }

  // =====================================================================================================
  // C. "and the curves kept gaining,": the studio lights dim, the screensaver kicks in, and the 3D Pipes curve climbs one notch per
  // beat out of the checkerboard, over the dancing trio and off the top of the frame.
  // =====================================================================================================
  function shotCurves(t) {
    const l = t - CUT.curves, bb = bpOf(t), camY = 540;
    setLight({ rim: EP.magenta, rimK: .85 });
    camBegin(W / 2, camY, 1);
    fillAll('#000');
    // faint graph-paper grid behind the screensaver (the pipe is the chart)
    ctx.strokeStyle = 'rgb(255 60 180 / .2)'; ctx.lineWidth = 2; ctx.beginPath(); for (let x = -40; x < W + 40; x += 120) { ctx.moveTo(x, -300); ctx.lineTo(x, 780); } for (let y = 780; y > -300; y -= 120) { ctx.moveTo(-100, y); ctx.lineTo(W + 100, y); } ctx.stroke();
    checkerFloor(t, { horizon: 780, a: '#2E1A6A', b: '#07030F', speed: .6, fog: EP.magenta, fogH: 120 });
    // the curve: an exponential staircase of pipe, a notch per beat, off the top
    const t0 = snap8(CUT.curves), tip = pipeStair(t, t0, { x0: 130, y0: 850, dx: 150, h0: 32, growth: 1.5, n: 10, col: '#E8342A', w: 26 });
    const nb = Math.floor((t - t0) / beatLen()), ja = (t - t0) / beatLen() - nb;
    if (nb >= 0 && ja < .5) glint(tip[0], tip[1], 90 * (1 - ja * 2), 1 - ja * 2);
    // the trio dances bottom right, under the curve
    tokenAt(t, 1180, 920, 32, 'runningMan');
    softAt(t, 1460, 910, 35, 'raise');
    djClawd(1730, 920, 19, { shades: true, aL: 1.2 + Math.sin(bb * Math.PI) * .3, aR: 1.2 - Math.sin(bb * Math.PI) * .3, mouth: 'grin', dy: -bounce(t) * .5 });
    camEnd();
    const tipY = tip[1] - (camY - 540);
    if (tipY > -60) { lensFlare(tip[0], tipY, .65 + .2 * kick(t, 5)); }
    else lensFlare(Math.min(W - 80, tip[0]), 20, .8);
    // the gain, multiplying on every notch (the V1.4 ×2 ×4 ×8 idiom)
    if (nb >= 0 && tipY > 60) { const v = 1.5 ** (nb + 1), lab = '×' + (v < 10 ? v.toFixed(1).replace('.0', '') : Math.round(v)), k = clamp(ja / .12); chromeText(lab, Math.min(W - 200, tip[0] + 150), tipY + 20, 96, { style: 'lime', italic: .12, depth: 10, s: lerp(1.5, 1, easeOut(k)), alpha: clamp(k * 3) }); }
    if (l < .1) cutFX('rgb');
  }

  // =====================================================================================================
  // D. "We didn't start the scaling" (2): the video wall carries the hook; SOFTMAX vogues in close-up; confetti cannons on SCALING.
  // =====================================================================================================
  function shotHook2(t) {
    hideCaption();
    const l = t - CUT.hook2, bb = bpOf(t), land = wordT(LN[2], LN[2].text.split(' ').length - 1);
    setLight({ rim: EP.cyan, rimK: .9 });
    stageSet(t, { level: 2, hue: EP.magenta, lasers: 3, floorY: 700, wall: (w, h) => {
      bgGrad([[0, '#2A0060'], [.6, '#C8108A'], [1, '#FF6A3A']], { y1: h });
      rays(w / 2, h * .55, 20, 'rgb(255 255 255 / .1)', t * .5);
      ctx.save(); ctx.translate(-(W / 2 - 750), -120); hookWords(LN[2], t, { y1: 225, y2: 410, s1: 124, s2: 186 }); ctx.restore();
    } });
    raveCrowd(t, { y: 1040, s: 1.25, rows: 2, n: 12, hands: t > land ? .95 : .55, k: 1, rim: EP.magenta });
    // SOFTMAX close-up, vogue
    const mv = dance('vogue', bb);
    toy(1600, 1720, 100, { ...CAST.softmax.o, ...mv, talk: singK(t), shadow: false, swing: .5 + Math.sin(t * 6) * .3, turn: -.2 });
    confetti(t, land, 110, { cannon: true });
    if (t > land && t < land + .12) strobe(.5 * (1 - (t - land) / .12));
    else strobe(strobeK(t, 1, .16) * .18);
    if (l < .1) cutFX('zoom');
  }

  // =====================================================================================================
  // E. "No, we didn't preordain it,": daylight chroma-key sky. SOFTMAX wags her finger on "No" (NO! burst); then the trio shrugs in unison.
  // =====================================================================================================
  const cloud = (x, y, s) => { ctx.save(); ctx.beginPath(); ctx.rect(x - s * 3, y - s * 3, s * 6, s * 3.35); ctx.clip(); for (const [dx, dy, r] of [[-1.25, .1, .6], [1.25, .12, .62], [-.5, -.25, .85], [.4, -.4, 1.0]]) glossBall(x + dx * s, y + dy * s, r * s, r * s * .92, '#E4EFFF', { line: false, rim: '#FFB0E8', rimK: .55, spec: .5 }); ctx.restore(); };
  function shotNo(t) {
    const l = t - CUT.no, bb = bpOf(t), shrugAt = wordT(LN[3], 3), shrug = t >= shrugAt - .05, wagging = !shrug;
    setLight({ rim: EP.magenta, rimK: .5 });
    camBegin(wagging ? 960 : W / 2, wagging ? 600 : H / 2, wagging ? 1.45 + .04 * clamp(l / 1) : 1);
    bgGrad([[0, '#0A2AC8'], [.6, '#2F8BFF'], [1, '#9AE0FF']], { y1: 760 });
    rays(W / 2, 620, 18, 'rgb(255 255 255 / .08)', t * .2);
    for (let i = 0; i < 6; i++) { const x = frac(hash(i + 20) + t * .025 * (1 + i % 3)) * (W + 900) - 450, y = 170 + hash(i + 29) * 420, s = 60 + hash(i + 23) * 60; cloud(x, y, s); }
    checkerFloor(t, { horizon: 760, a: '#FFFFFF', b: '#2F6BFF', speed: .4, fog: '#BFE8FF', fogH: 90, reflect: .3 });
    // three podiums
    const P = [[430, 'token'], [960, 'softmax'], [1490, 'clawd']];
    for (const [x] of P) podium(x, 880, 300, t, EP.magenta);
    const sh = shrug ? dance('shrug', bb) : null, dip = shrug ? Math.exp(-frac(bpOf(t) - bpOf(shrugAt)) * 5) : 0;
    tokenAt(t, 430, 888, 40, 'bounce', shrug ? { ...sh, mouth: 'flat', eyes: 'dot', bob: dip * .6 } : { mic: 'R', ...dance('rap', bb) });
    const wag = Math.sin(bb * Math.PI * 2) * .9;
    softAt(t, 960, 888, 42, 'sing', shrug ? { ...sh, talk: singK(t), bob: dip * .6 } : { hR: [2.3 + wag, -9.2], gR: 'point', hL: [-2.4, -4.4], gL: 'fist', headTilt: wag * .06, brows: 'angry' });
    djClawd(1490, 888, 24, { shades: true, aL: shrug ? .35 + dip * .3 : -.6, aR: shrug ? .35 + dip * .3 : -.6, mouth: shrug ? 'o' : 'grin', dy: -dip * .5 });
    camEnd();
    if (wagging) burst('NO!', 1420, 330, 150, { pop: pop(t, CUT.no + .02, .2), col: EP.yellow, ink: EP.magenta, spin: .3 });
    if (shrug) for (let i = 0; i < 3; i++) { const k = pop(t, shrugAt + i * .06, .2); if (k > 0) chromeText('?', P[i][0], 250 + Math.sin(t * 4 + i) * 12, 200, { style: ['ice', 'hot', 'gold'][i], depth: 18, s: k, sx: .35 + .65 * Math.abs(Math.cos(t * 3.2 + i * 1.1)) }); }
    sparkles(t, { n: 10, seed: 5, y1: 700, r: 36 });
    if (l < .1) cutFX('flash');
  }

  // =====================================================================================================
  // F. "but we can't contain it!": on the club stage, SCALING.EXE crashes; the cursor clicks Close… and the pipes burst out through the
  // dialog and off every edge of the frame.
  // =====================================================================================================
  const clickAt = () => wordT(LN[3], 7), burstAt = () => wordT(LN[3], 8), itAt = () => wordT(LN[3], 9);
  // burst runs: right-angled walks from the dialog, outward, each growing fast
  const RUNS = Array.from({ length: 7 }, (_, i) => {
    const a = -Math.PI / 2 + (i - 3) * .62 + (hash(i + 70) - .5) * .3, pts = [[W / 2 + (hash(i + 71) - .5) * 200, 520 + (hash(i + 72) - .5) * 120]];
    let horiz = i % 2 === 0;
    for (let q = 0; q < 7; q++) { const [x, y] = pts.at(-1), L = 130 + hash2(i, q) * 220; pts.push(horiz ? [x + Math.sign(Math.cos(a) || 1) * L * (Math.abs(Math.cos(a)) + .3), y] : [x, y + Math.sign(Math.sin(a)) * L * (Math.abs(Math.sin(a)) + .3)]); horiz = !horiz; }
    return { pts, col: ['#E8342A', '#2A9AE8', '#E8C42A', '#2AE85A', '#C42AE8', '#E8E8E8', '#E87A2A'][i], w: 20 + hash(i + 73) * 10, delay: hash(i + 74) * .12 };
  });
  function shotContain(t) {
    const bb = bpOf(t), tc = clickAt(), tbst = burstAt(), tit = itAt(), br = t - tbst;
    const sh = shakeAt(t, t, tbst, .5, 26), sh2 = shakeAt(t, t, tit, .35, 16);
    setLight({ rim: EP.magenta, rimK: .85 });
    camBegin(W / 2 - sh[0] - sh2[0], H / 2 - sh[1] - sh2[1], 1);
    stageSet(t, { level: 2, hue: EP.uv, lasers: 3, floorY: 700 });
    floatBooth(W / 2, 640, 300, t);
    tokenAt(t, 470, 960, 32, br > 0 ? 'jump' : 'pump');
    softAt(t, 1450, 975, 34, br > 0 ? 'raise' : 'sing');
    raveCrowd(t, { y: 1060, s: 1.3, rows: 2, n: 11, k: 1, hands: br > 0 ? 1 : .5, rim: EP.magenta });
    camEnd();
    // the crash dialog: pops on "but", shudders after the click, splits open when the pipes burst through, then falls away
    const dk = clamp((t - CUT.contain) / .12), fall = clamp((t - tit) / .5), dx = W / 2, dy = 470;
    if (fall < 1) {
      const quake = t > tc + .1 && br < 0 ? shakeXY(t, 6) : [0, 0];
      ctx.save(); ctx.translate(dx + quake[0], dy + quake[1] + easeIn(fall) * 900); ctx.rotate(fall * .5); ctx.translate(-dx, -dy);
      const out = win98Dialog(dx, dy, 1060, 'SCALING.EXE', 'This program has performed an illegal operation\nand will be shut down.\nIf the problem persists, contact the vendor.', { icon: 'error', buttons: ['Close', 'Details >>'], k: dk, pressed: t > tc && t < tc + .15 ? 0 : undefined, size: 30, bw: 200 });
      if (br > 0) { ctx.strokeStyle = '#000'; ctx.lineWidth = 4; ctx.beginPath(); for (let i = 0; i < 7; i++) { const a = i / 7 * TAU + .3; ctx.moveTo(dx, dy); let x = dx, y = dy; for (let q = 1; q < 5; q++) { x = dx + Math.cos(a + hash2(i, q) * .4 - .2) * q * 80 * clamp(br / .15); y = dy + Math.sin(a + hash2(i, q + 9) * .4 - .2) * q * 60 * clamp(br / .15); ctx.lineTo(x, y); } } ctx.stroke(); }
      ctx.restore();
      if (dk >= 1 && br < 0) {
        const [bx, by, bw, bh] = out.buttons[0] ?? [dx - 212, dy + 100, 200, 56], target = [bx + bw * .55, by + bh * .6], c0 = [1700, 900];
        const cp = kf(t, [[CUT.contain + .1, c0], [tc - .05, target]], ease);
        cursor98(cp[0], cp[1], { click: t > tc ? (t - tc) / .3 : 0 });
      }
    }
    // the pipes burst through, out of the dialog and off every edge
    if (br > 0) {
      for (const R of RUNS) { const k = clamp((br - R.delay) / 1.1); if (k > 0) pipeRun(R.pts, easeOut(k), R.col, R.w); }
      glow(dx, dy, 500 * clamp(br / .2), EP.white, .6 * (1 - clamp(br / .5)));
    }
    if (br > 0 && br < .12) fx({ rgb: 1 - br / .12 });
    if (t > tit && t < tit + .1) fx({ rgb: .7, zoom: .6 });
    strobe(br > 0 && t < tit + .6 ? strobeK(t, 2, .3) * .35 : 0);
    if (t - CUT.contain < .1) cutFX('rgb');
  }

  // =====================================================================================================
  // G. The tail, "Deep, deep, deep…": a stutter edit of the frame on each "deep", sinking into ocean blue; DEEP stamps bigger each time;
  // a whale's tail flicks up on the last one (into V2.1's DeepSeek).
  // =====================================================================================================
  function whaleTail(x, y, s, rot) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot); ctx.scale(s, s);
    gloss(() => { ctx.moveTo(-.35, 3); ctx.quadraticCurveTo(-.3, .6, 0, -.1); ctx.bezierCurveTo(-.9, -.9, -2.3, -1.1, -2.9, -.4); ctx.quadraticCurveTo(-1.7, -.6, -.6, .3); ctx.quadraticCurveTo(0, .1, .6, .3); ctx.quadraticCurveTo(1.7, -.6, 2.9, -.4); ctx.bezierCurveTo(2.3, -1.1, .9, -.9, 0, -.1); ctx.quadraticCurveTo(.3, .6, .35, 3); ctx.closePath(); }, CANDY.ocean, { box: [-2.9, -1.1, 5.8, 4.1], lw: .06, rim: EP.cyan, spec: .9 });
    ctx.restore();
  }
  function shotTail(t) {
    const i = DEEPS.reduce((a, d, j) => t >= d ? j : a, -1);
    if (i < 0) return shotContain(t);
    const hit = DEEPS[i], a = t - hit, ts = DEEPS[0] + Math.min(a, .11), T0 = T;
    // the stutter: the picture snaps back to the first "deep" and replays a sliver of it, a notch closer each time
    const z = 1 + (i + 1) * .045 + Math.min(a, .11) * .3;
    ctx.save(); ctx.translate(W / 2, H / 2); ctx.scale(z, z); ctx.translate(-W / 2, -H / 2);
    T = ts; try { shotContain(ts); } finally { T = T0; }
    ctx.restore();
    // sink into ocean blue
    const deep = clamp((i + 1) / DEEPS.length);
    ctx.save(); ctx.globalCompositeOperation = 'color'; ctx.fillStyle = `rgb(20 110 220 / ${.35 + .6 * deep})`; ctx.fillRect(-100, -100, W + 200, H + 200); ctx.restore();
    ctx.fillStyle = `rgb(0 20 60 / ${.15 + .35 * deep})`; ctx.fillRect(-100, -100, W + 200, H + 200);
    // bubbles rising
    for (let q = 0; q < 26; q++) { const bx = hash(q + 300) * W, by = H + 60 - frac(hash(q + 301) + t * (.35 + hash(q + 302) * .3)) * (H + 160), r = 8 + hash(q + 303) * 22; ell(bx + Math.sin(t * 3 + q) * 10, by, r, r); ctx.strokeStyle = `rgb(200 240 255 / ${.5 * deep})`; ctx.lineWidth = 3; ctx.stroke(); }
    // DEEP, bigger every time (the earlier ones linger behind)
    for (let j = 0; j <= i; j++) {
      const k = clamp((t - DEEPS[j]) / .1), sc = .75 + j * .2, fade = j === i ? 1 : .35 - (i - j) * .05;
      if (fade <= 0) continue;
      chromeText('DEEP', W / 2 + (j - i) * 26 * (j % 2 ? 1 : -1), 470 - (i - j) * 8, 170, { style: 'ice', italic: .14, depth: 16, s: sc * lerp(1.6, 1, easeOut(k)), alpha: fade * clamp(k * 3) });
    }
    if (a < .08) fx({ flash: .35 * (1 - a / .08) });
    if (i === DEEPS.length - 1) {
      const u = clamp(a / .2);
      for (let q = 0; q < 16; q++) { const ang = -Math.PI / 2 + (hash(q + 400) - .5) * 2.2, v = 400 + hash(q + 401) * 500; ell(1500 + Math.cos(ang) * v * u, 1000 + Math.sin(ang) * v * u + 900 * u * u * .3, 10, 14); ctx.fillStyle = 'rgb(210 245 255 / .85)'; ctx.fill(); }
      ell(1480, 985, 260 * easeOut(u), 46 * easeOut(u)); ctx.fillStyle = 'rgb(225 248 255 / .8)'; ctx.fill();
      whaleTail(1480, lerp(1300, 700, easeOut(u)), 125, lerp(.5, -.25, easeOut(u)) + Math.sin(a * 18) * .08 * u);
    }
  }

  section('C1', (p, lt, d, t) => {
    if (t < CUT.train) return shotHook1(t);
    if (t < CUT.curves) return shotTrain(t);
    if (t < CUT.hook2) return shotCurves(t);
    if (t < CUT.no) return shotHook2(t);
    if (t < CUT.contain) return shotNo(t);
    if (!DEEPS.length || t < DEEPS[0]) return shotContain(t);
    return shotTail(t);
  });
})();

;
// ---- styles/eurodance/ch/c04_v2.js ----
// c04_v2 — Verse 2: 2025, "the summer-hit year". Sixteen headlines, MC TOKEN on the mic, each one gag in a late-90s idiom (the harbour
// fireworks, a stargate, a dance-mat arcade, Found New Hardware, a claw machine, teleshopping, the blue screen, a podium, a Tamagotchi,
// the chart show, a slot machine, the drop, a chat room, a CRT wall, a boy-band breakup, the spinning newspaper). The colour run:
// night navy / money gold / arcade magenta / Win98 turquoise / claw-machine pink / teleshop coral / BSOD blue / podium white-gold /
// Tamagotchi mint / chart-show purple / casino red / drop black / sidewalk sky / slop grape / teen-mag pink / Ibiza sunset.
(() => {
  const bt = (t, lt, k = 0) => beatIn(t, lt, k);
  const pop = (lt, t0, dur = .18) => lt < t0 ? 0 : backOut(clamp((lt - t0) / dur), 2.2);
  const tok = t => ({ talk: singK(t) });
  const money = n => String(Math.round(n)).replace(/\B(?=(\d{3})+(?!\d))/g, ',');
  // a rubber-stamp slam (the V1 idiom)
  function slamStamp(str, x, y, size, col, rot, k) {
    if (k <= 0) return; const s = k < 1 ? lerp(1.9, 1, easeOut(k)) : 1, w = textW(str, size, 'archivo', 2) + size * .9, h = size * 1.5;
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot); ctx.scale(s, s); ctx.globalAlpha *= clamp(k * 3) * .92;
    ctx.strokeStyle = col; ctx.lineWidth = size * .1; rrect(-w / 2, -h / 2, w, h, size * .2); ctx.stroke(); ctx.lineWidth = size * .04; rrect(-w / 2 + size * .16, -h / 2 + size * .16, w - size * .32, h - size * .32, size * .12); ctx.stroke();
    txt(str, 0, size * .05, size, col, { font: 'archivo', spacing: 2 });
    ctx.restore();
  }
  function confetti(t, t0, n = 60, o = {}) {
    if (t < t0) return; const cols = o.cols ?? [EP.magenta, EP.cyan, EP.yellow, EP.lime, EP.white];
    for (let i = 0; i < n; i++) { const age = t - t0, x = (o.x0 ?? 0) + hash2(i, 1) * ((o.x1 ?? W) - (o.x0 ?? 0)) + Math.sin(age * 3 + i) * 30, y = (o.y0 ?? -60) - hash2(i, 2) * 300 + age * (260 + hash2(i, 3) * 200); if (y > H + 40) continue; const r = age * 6 + i; ctx.save(); ctx.translate(x, y); ctx.rotate(r); ctx.scale(1, Math.cos(r * 1.3)); ctx.fillStyle = cols[i % cols.length]; ctx.fillRect(-9, -5, 18, 10); ctx.restore(); }
  }
  // a Windows 98 balloon tip (the "Found New Hardware" bubble): (x, y) = the tail's point; the balloon sits above-left of it unless o.flip
  function balloon98(x, y, title, body, k, o = {}) {
    if (k <= 0) return; const s = backOut(clamp(k), 2), w = o.w ?? 400, h = 112, bx = o.flip ? x - 60 : x - w + 60, by = y - h - 40;
    ctx.save(); ctx.translate(x, y); ctx.scale(s, s); ctx.translate(-x, -y);
    ctx.fillStyle = 'rgb(0 0 0 / .3)'; rrect(bx + 7, by + 8, w, h, 16); ctx.fill();
    ctx.beginPath(); ctx.roundRect(bx, by, w, h, 16); ctx.moveTo(x - 24, by + h - 2); ctx.lineTo(x, y); ctx.lineTo(x + 6, by + h - 2); ctx.fillStyle = EP.w98tip; ctx.fill(); ctx.strokeStyle = '#000'; ctx.lineWidth = 2.5; ctx.stroke();
    icon98('info', bx + 38, by + 36, .55);
    txt(title, bx + 70, by + 36, 26, '#000', { font: 'archivo', align: 'left', maxW: w - 90 });
    txt(body, bx + 24, by + 80, 24, '#222', { font: 'archivo', align: 'left', maxW: w - 44 });
    ctx.restore();
  }
  // the whale's tail (DeepSeek's crest, continuing C1's tail)
  function whaleTail(x, y, s, rot, col = CANDY.ocean) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot); ctx.scale(s, s);
    gloss(() => { ctx.moveTo(-.35, 3); ctx.quadraticCurveTo(-.3, .6, 0, -.1); ctx.bezierCurveTo(-.9, -.9, -2.3, -1.1, -2.9, -.4); ctx.quadraticCurveTo(-1.7, -.6, -.6, .3); ctx.quadraticCurveTo(0, .1, .6, .3); ctx.quadraticCurveTo(1.7, -.6, 2.9, -.4); ctx.bezierCurveTo(2.3, -1.1, .9, -.9, 0, -.1); ctx.quadraticCurveTo(.3, .6, .35, 3); ctx.closePath(); }, col, { box: [-2.9, -1.1, 5.8, 4.1], lw: .06, rim: EP.cyan, spec: .9 });
    ctx.restore();
  }
  // a firework: sparks bursting from (x, y), age seconds after the burst
  function firework(x, y, age, col, r) {
    if (age < 0 || age > 1.3) return; const k = easeOut(clamp(age / .45)), a = 1 - clamp((age - .45) / .8);
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; ctx.lineCap = 'round';
    for (let i = 0; i < 30; i++) { const ang = i / 30 * TAU + hash(i) * .1, rr = r * k * (.85 + hash(i + 9) * .3), sag = age * age * 90; ctx.strokeStyle = alpha(i % 3 ? col : '#FFFFFF', .85 * a); ctx.lineWidth = 5; ctx.beginPath(); ctx.moveTo(x + Math.cos(ang) * rr * .6, y + Math.sin(ang) * rr * .6 + sag * .6); ctx.lineTo(x + Math.cos(ang) * rr, y + Math.sin(ang) * rr + sag); ctx.stroke(); }
    ctx.restore(); glow(x, y, r * .9, col, .45 * a * (1 - k * .4));
  }

  // =====================================================================================================
  // V2.1 DeepSeek New Year sticker shock — Lunar New Year fireworks over the harbour. The ocean-blue DEEPSEEK computer (whale-tail crest)
  // bursts through a giant SALE! tag: $5.6M* (*final training run). On the next beat the NVDA ticker nosedives.
  line('V2', 1, (p, lt, d, t) => {
    const b0 = bt(t, lt, 0), b1 = bt(t, lt, 1), b2 = bt(t, lt, 2), bb = bpOf(t), rip = clamp((lt - b0 + .03) / .12);
    setLight({ rim: EP.red, rimK: .8 });
    bgGrad([[0, '#02041E'], [.6, '#0A1A5A'], [1, '#27307A']], { y1: 760 });
    [[b0 - .45, 300, 300, EP.gold], [b0, 1180, 240, EP.red], [b1, 560, 200, EP.magenta], [b1 + .15, 1560, 380, EP.gold], [b2, 900, 170, EP.cyan]].forEach(([at, x, y, c], i) => firework(x, y, lt - at, c, 170 + hash(i + 3) * 90));
    // skyline and harbour
    ctx.fillStyle = '#060A26'; for (let i = 0; i < 19; i++) { const x = i * 108 - 40, w = 88 + hash(i + 5) * 40, h = 80 + hash(i + 6) * 220; ctx.fillRect(x, 760 - h, w, h + 2); for (let q = 0; q < 10; q++) if (hash2(i, q) < .45) { ctx.fillStyle = hash2(q, i) < .5 ? '#FFD86A' : '#FF8A5A'; ctx.fillRect(x + 12 + (q % 3) * 26, 760 - h + 18 + Math.floor(q / 3) * 34, 12, 16); ctx.fillStyle = '#060A26'; } }
    ctx.fillStyle = lg(0, 760, 0, H, [[0, '#0A1650'], [1, '#02041A']]); ctx.fillRect(-100, 760, W + 200, H);
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; for (let i = 0; i < 26; i++) { const x = hash(i + 50) * W, y = 780 + hash(i + 51) * 160, w = 60 + hash(i + 52) * 120; ctx.fillStyle = alpha([EP.gold, EP.red, EP.magenta][i % 3], .25 + .2 * Math.sin(t * 5 + i)); ctx.fillRect(x + Math.sin(t * 2 + i) * 20, y, w, 4); } ctx.restore();
    // a string of red lanterns
    ctx.strokeStyle = '#2A1A10'; ctx.lineWidth = 4; ctx.beginPath(); ctx.moveTo(-20, 150); ctx.quadraticCurveTo(700, 260, 1440, 150); ctx.stroke();
    for (let i = 0; i < 6; i++) { const u = (i + .5) / 6, x = lerp(-20, 1440, u), y = 150 + 2 * u * (1 - u) * 110 + 50, sw = Math.sin(t * 2.2 + i) * .1; ctx.save(); ctx.translate(x, y - 50); ctx.rotate(sw); glow(0, 50, 90, '#FF5A2A', .45); glossBall(0, 50, 46, 38, '#E8202A', { rim: EP.gold, rimK: .6, lw: 3 }); ctx.fillStyle = EP.gold; ctx.fillRect(-22, 8, 44, 8); ctx.fillRect(-22, 84, 44, 8); ctx.strokeStyle = EP.gold; ctx.lineWidth = 3; ctx.beginPath(); ctx.moveTo(0, 92); ctx.lineTo(0, 120); ctx.stroke(); ctx.restore(); }
    // the SALE! tag, ripped open on the beat
    const tx = 760, ty = 500;
    if (rip < 1) burst('SALE!', tx, ty, 330, { col: EP.yellow, ink: EP.red, rot: -.08, size: 150 });
    else for (const sd of [-1, 1]) { const a = clamp((lt - b0) / .5); ctx.save(); ctx.beginPath(); ctx.rect(sd < 0 ? tx - 600 : tx, 0, 600, H); ctx.clip(); ctx.translate(sd * a * 420, a * a * 500); ctx.translate(tx, ty); ctx.rotate(sd * a * .9); ctx.translate(-tx, -ty); burst('SALE!', tx, ty, 330, { col: EP.yellow, ink: EP.red, rot: -.08, size: 150 }); ctx.restore(); }
    if (rip >= 1) for (let i = 0; i < 14; i++) { const a = clamp((lt - b0) / .6), ang = hash(i + 80) * TAU, v = 300 + hash(i + 81) * 500; ctx.save(); ctx.translate(tx + Math.cos(ang) * v * a, ty + Math.sin(ang) * v * a + 400 * a * a); ctx.rotate(a * 8 + i); ctx.fillStyle = EP.yellow; poly([[-18, -10], [16, -14], [12, 12], [-14, 10]]); ctx.fill(); ctx.restore(); }
    // DEEPSEEK springs out
    const out = rip >= 1 ? clamp((lt - b0) / .2) : 0, s = 38 * lerp(.55, 1, backOut(out, 2)), gy = 860, hop = out >= 1 ? Math.abs(Math.sin(bb * Math.PI)) * .5 : 0;
    if (out > 0) {
      gumdrop(tx, gy, s, { col: CANDY.ocean, label: 'DEEPSEEK', face: 'star', mouth: 'grin', hL: [-4.6, -8.8], hR: [4.6, -8.8], gL: 'wave', gR: 'wave', jump: hop, rim: EP.gold });
      whaleTail(tx, gy - (9.7 + hop) * s, s * .75, Math.sin(t * 9) * .15);
    }
    // the price
    burst('$5.6M*', 1370, 430, 230, { pop: pop(lt, b0 + .08), col: EP.red, ink: '#FFFFFF', spin: .25, size: 96 });
    if (lt > b0 + .15) ptext('*final training run', 1370, 690, 38, { fill: '#FFFFFF', strokes: [['#05031A', 9]], alpha: clamp((lt - b0 - .15) / .1) });
    // the ticker, nosediving on the next beat
    const dive = clamp((lt - b1) / .18);
    ctx.fillStyle = '#05050A'; ctx.fillRect(-10, 800, W + 20, 118); ctx.fillStyle = EP.gold; ctx.fillRect(-10, 800, W + 20, 5); ctx.fillRect(-10, 913, W + 20, 5);
    ctx.save(); ctx.beginPath(); ctx.rect(650, 805, W, 108); ctx.clip();
    const msg = 'BIGGEST ONE-DAY DROP IN US HISTORY * NASDAQ * ', mw = pixW(msg, 8) + 48, off = (lt * 520) % mw; for (let q = 0; q < 3; q++) pixText(msg, 680 - off + q * mw, 832, 8, EP.amber, { glow: true });
    ctx.restore();
    ctx.fillStyle = dive > 0 ? '#3A0008' : '#0A1A0A'; ctx.fillRect(0, 805, 650, 108);
    pixText('NVDA', 26, 832, 8, '#FFFFFF');
    ctx.beginPath(); for (let i = 0; i <= 40; i++) { const u = i / 40, y = 850 + Math.sin(u * 14) * 8 - u * 16 + (u > .65 ? (u - .65) / .35 * 70 * dive : 0); i ? ctx.lineTo(250 + u * 370, y) : ctx.moveTo(250, y); }
    ctx.strokeStyle = dive > 0 ? EP.red : EP.laser; ctx.lineWidth = 6; ctx.stroke();
    if (dive > 0) { const sc = lerp(1.8, 1, easeOut(dive)); ctx.save(); ctx.translate(330, 735); ctx.rotate(-.04); ctx.scale(sc, sc); ptext('NVDA ▼ ~$600B', 0, 0, 74, { fill: EP.red, strokes: [['#FFFFFF', 14], [EP.line, 20]], alpha: clamp(dive * 3) }); ctx.restore(); }
    // MC TOKEN whips his shades off at the price
    const shadesOff = lt >= b0 + .05, raveVisor = (w) => { ctx.beginPath(); ctx.moveTo(-w, -8); ctx.quadraticCurveTo(0, -w * .45, w, -8); ctx.lineTo(w * .92, 12); ctx.quadraticCurveTo(0, -w * .12, -w * .92, 12); ctx.closePath(); ctx.fillStyle = lg(-w, 0, w, 0, [[0, '#12E7FF'], [.35, '#6A3BFF'], [.65, '#FF1FA3'], [1, '#FFB21F']]); ctx.fill(); ctx.strokeStyle = EP.line; ctx.lineWidth = 4; ctx.stroke(); };
    toy(1690, 1010, 42, { ...CAST.token.o, mic: 'L', ...tok(t), ...(shadesOff ? { glasses: undefined, eyes: 'wide', brows: 'up', hR: [2.2, -10.4], gR: 'fist', hold: () => { ctx.save(); ctx.translate(-10, -26); ctx.rotate(-.2); raveVisor(62); ctx.restore(); } } : { hR: [2.4, -4.4], gR: 'open' }), turn: -.25, bob: kick(t, 6) * .4 });
    if (lt >= b1 && lt < b1 + .1) fx({ rgb: .7 });
    if (lt < .1) cutFX('flash');
  });

  // =====================================================================================================
  // V2.2 Half a trillion Stargate talk — a chrome ring portal spins up over the White House announcement: TRUMP at the lectern with
  // SAM, LARRY and MASA; the counter hits $500,000,000,000; a 90s pager beeps: ELON: "THEY DON'T ACTUALLY HAVE THE MONEY".
  function stargate(x, y, r, t, k) {
    // event horizon
    ctx.save(); ell(x, y, r * .82, r * .82); ctx.clip();
    ctx.fillStyle = rg(x, y, 0, r, [[0, '#FFFFFF'], [.25, '#8AE8FF'], [.7, '#1A6AE8'], [1, '#0A1A6A']]); ctx.globalAlpha = k; ctx.fillRect(x - r, y - r, r * 2, r * 2);
    ctx.globalCompositeOperation = 'lighter'; ctx.strokeStyle = 'rgb(200 240 255 / .35)'; ctx.lineWidth = 10; for (let i = 0; i < 8; i++) { ctx.beginPath(); ctx.arc(x, y, r * (.15 + i * .09), t * 3 + i, t * 3 + i + 2.2); ctx.stroke(); }
    ctx.restore();
    // the chrome ring
    ctx.save(); ctx.beginPath(); ctx.arc(x, y, r, 0, TAU); ctx.arc(x, y, r * .8, 0, TAU, true);
    ctx.fillStyle = lg(0, y - r, 0, y + r, CHROME.silver.stops); ctx.fill('evenodd'); ctx.strokeStyle = EP.line; ctx.lineWidth = 5; ctx.stroke(); ctx.restore();
    ctx.strokeStyle = 'rgb(0 0 30 / .3)'; ctx.lineWidth = 3; for (let i = 0; i < 36; i++) { const a = i / 36 * TAU + t * .5; ctx.beginPath(); ctx.moveTo(x + Math.cos(a) * r * .83, y + Math.sin(a) * r * .83); ctx.lineTo(x + Math.cos(a) * r * .97, y + Math.sin(a) * r * .97); ctx.stroke(); }
    for (let i = 0; i < 9; i++) { const a = -Math.PI / 2 + i / 9 * TAU, cx = x + Math.cos(a) * r * .95, cy = y + Math.sin(a) * r * .95, lit = i / 9 < k * 1.1; ctx.save(); ctx.translate(cx, cy); ctx.rotate(a + Math.PI / 2); poly([[-22, -16], [22, -16], [0, 20]]); paint(lit ? EP.orange : '#6A4A3A', EP.line, 3); ctx.restore(); if (lit) glow(cx, cy, 50, EP.orange, .7); }
  }
  line('V2', 2, (p, lt, d, t) => {
    const b0 = bt(t, lt, 0), b1 = bt(t, lt, 1), b3 = bt(t, lt, 3), bb = bpOf(t), k = clamp(lt / (b1 + .05));
    setLight({ rim: '#FFFFFF', rimK: .35 });
    bgGrad([[0, '#FF9A1A'], [.55, '#FFD24A'], [1, '#FFF2B8']]);
    rays(W / 2, 300, 28, 'rgb(255 255 255 / .22)', t * .3);
    for (let i = 0; i < 16; i++) { const x = hash(i + 60) * W, y = frac(hash(i + 61) + t * .25) * H * 1.2 - 100; ptext('$', x, y, 40 + hash(i + 62) * 40, { fill: 'rgb(255 255 255 / .35)', rot: Math.sin(t * 2 + i) * .4 }); }
    stargate(W / 2, 262, 200, t, easeOut(k));
    if (lt > b0 && lt < b0 + .15) glow(W / 2, 262, 560, '#FFFFFF', 1 - (lt - b0) / .15);
    // the counter
    ctx.fillStyle = '#05050A'; rrect(W / 2 - 390, 482, 780, 84, 12); ctx.fill(); ctx.strokeStyle = EP.gold; ctx.lineWidth = 4; ctx.stroke();
    pixText('$' + money(500e9 * easeOut(clamp(lt / (b1 + .1)))), W / 2, 496, 8, lt > b1 ? EP.laser : EP.amber, { align: 'center', glow: true });
    if (lt > b1) ptext('UP TO $500B · $100B TO START', W / 2, 600, 36, { fill: '#FFFFFF', strokes: [[EP.line, 10]], alpha: clamp((lt - b1) / .1) });
    // the announcement: TRUMP at the lectern, the three backers beside him, everyone talking at once
    const P = [[480, WHO.sam], [720, WHO.larry], [960, WHO.trump], [1200, WHO.masa]];
    P.forEach(([x, w], i) => { const ph = i * .7, pres = w === WHO.trump; toy(x, 1015, pres ? 32 : 30, { ...w.o, talk: clamp(.3 + .7 * Math.abs(Math.sin(t * 9 + ph))), hR: [2.4, -7.6 - Math.abs(Math.sin(t * 4 + ph)) * 1.4], gR: pres || i === 1 ? 'point' : 'open', hL: [-2.2, -5.2], turn: pres ? 0 : (i < 2 ? .3 : -.3), shadow: false }); });
    gloss(pfRR(330, 900, 1020, 220, 16), '#6A3A12', { box: [330, 900, 1020, 220], rim: EP.gold, lw: 5, spec: .5 });
    ctx.fillStyle = EP.gold; ctx.fillRect(330, 920, 1020, 6);
    P.forEach(([x, w], i) => nameTip(w.name, x, 945, { pop: pop(lt, .06 + i * .05), size: 22, to: [x, 905] }));
    // the pager
    const beep = lt > b3 - .05, bz = beep ? shakeXY(t, 6 * (1 - clamp((lt - b3) / .4)), 40) : [0, 0];
    ctx.save(); ctx.translate(1620 + bz[0], 780 + bz[1]); ctx.rotate(-.12);
    gloss(pfRR(-190, -80, 380, 170, 26), '#1C1C24', { box: [-190, -80, 380, 170], lw: 4, rim: EP.gold, spec: .6 });
    rrect(-160, -58, 320, 96, 8); paint('#9ABA6A', '#000', 3);
    ctx.save(); rrect(-156, -54, 312, 88, 6); ctx.clip();
    pixText('ELON:', -146, -46, 4, '#1A2A0A'); const q = "THEY DON'T ACTUALLY HAVE THE MONEY", qw = pixW(q, 4) + 60, o2 = beep ? ((lt - b3) * 380) % qw : 0; pixText(q, 146 - o2 - (beep ? 0 : -qw), -6, 4, '#1A2A0A');
    ctx.restore();
    for (let i = 0; i < 3; i++) { ell(-100 + i * 100, 64, 18, 10); ctx.fillStyle = '#3A3A48'; ctx.fill(); }
    ctx.restore();
    if (beep) { const a = clamp((lt - b3) / .3); ptext('BEEP! BEEP!', 1620, 640 - a * 20, 44, { fill: EP.red, strokes: [['#FFFFFF', 10]], alpha: 1 - clamp((lt - b3 - .35) / .2), rot: -.1 }); }
    if (lt < .1) cutFX('zoom');
  });

  // =====================================================================================================
  // V2.3 Hit "Accept All," never ask — a dance-mat arcade machine: ANDREJ, eyes closed, blissed out, stomps the arrows; every note that
  // scrolls up says ACCEPT ALL, the judge says PERFECT!, and the code flies past unread.
  line('V2', 3, (p, lt, d, t) => {
    const b0 = bt(t, lt, 0), bb = bpOf(t), e8 = beatLen() / 2;
    setLight({ rim: EP.magenta, rimK: .85 });
    bgGrad([[0, '#0A0020'], [1, '#2A0050']]);
    // the unread code, streaming past
    ctx.save(); ctx.globalAlpha = .5; for (let i = 0; i < 26; i++) { const y = 1100 - frac(lt * 1.6 + i / 26) * 1300, L = ['+ return await agent.run(task)', '- if (!ok) throw err', '+ // TODO: read this later', "+ import { everything } from 'npm'", '+ delete tests/', '+ const vibes = true', '- validate(input)'][i % 7]; txt(L, 40, y, 30, i % 3 ? '#3BFF4A' : '#FF5FA8', { font: 'courier', align: 'left' }); } ctx.restore();
    // the lanes
    const lx = 120, lw = 820, lanes = 4, cw = lw / lanes, ty = 210;
    ctx.fillStyle = 'rgb(0 0 0 / .55)'; ctx.fillRect(lx, 150, lw, 800);
    for (let i = 0; i < lanes; i++) { ctx.save(); ctx.translate(lx + cw * (i + .5), ty); ctx.rotate([Math.PI / 2, Math.PI, 0, -Math.PI / 2][i]); poly([[0, -46], [44, 4], [18, 4], [18, 44], [-18, 44], [-18, 4], [-44, 4]]); paint('rgb(255 255 255 / .12)', 'rgb(255 255 255 / .6)', 4); ctx.restore(); }
    // notes: one per eighth, each an ACCEPT ALL button, arriving at the targets
    const n0 = Math.floor((lt - b0) / e8);
    for (let n = n0 - 1; n < n0 + 9; n++) {
      const at = b0 + n * e8, y = ty + (at - lt) * 900, lane = Math.floor(hash(n + 500) * 4); if (y < ty - 5 || y > 1000) continue;
      const x = lx + cw * (lane + .5); ctx.save(); ctx.translate(x, y); gloss(pfRR(-92, -34, 184, 68, 16), [EP.laser, EP.cyan, EP.magenta, EP.yellow][lane], { box: [-92, -34, 184, 68], lw: 4, spec: .8, rim: null }); txt('ACCEPT ALL', 0, 2, 26, EP.line, { font: 'archivo', maxW: 170 }); ctx.restore();
    }
    // the judge
    const since = (lt - b0) - n0 * e8;
    if (lt > b0) { glow(lx + lw / 2, ty, 300, EP.yellow, .4 * (1 - since / e8)); chromeText('PERFECT!', lx + lw / 2, 360, 100, { style: 'rainbow', italic: .12, depth: 10, s: lerp(1.25, 1, clamp(since / .1)) }); pixText('COMBO ' + (127 + Math.max(0, n0)), lx + lw / 2, 450, 7, '#FFFFFF', { align: 'center', edge: '#000' }); }
    // Andrej on the pad
    const px = 1400, py = 920;
    poly([[px - 330, py + 20], [px + 330, py + 20], [px + 260, py - 90], [px - 260, py - 90]]); paint('#2A2A38', EP.line, 4);
    [[-150, -40], [150, -40], [0, -75], [0, 5]].forEach(([dx, dy], i) => { const lit = Math.floor(bpOf(t) * 2) % 4 === i; ctx.save(); ctx.translate(px + dx, py + dy); ctx.scale(1, .45); ctx.rotate([Math.PI / 2 + Math.PI, 0, Math.PI, -Math.PI / 2][i] + Math.PI / 2); poly([[0, -46], [44, 4], [18, 4], [18, 44], [-18, 44], [-18, 4], [-44, 4]]); paint(lit ? EP.cyan : '#5A5A70', EP.line, 4); ctx.restore(); if (lit) glow(px + dx, py + dy, 90, EP.cyan, .6); });
    const st = Math.sin(bb * Math.PI * 2);
    toy(px, py - 30, 52, { ...WHO.karpathy.o, eyes: 'closed', mouth: 'grin', blush: .6, fL: [st * .5, -Math.max(0, st) * .9], fR: [-st * .5, -Math.max(0, -st) * .9], hL: [-2.3, -11 + Math.abs(st) * .5], hR: [2.3, -11 + Math.abs(st) * .5], gL: 'wave', gR: 'wave', bob: Math.abs(st) * .5, lean: st * .05, emote: 'note', emoteK: 1 });
    nameTip(WHO.karpathy.name, px, 190, { pop: pop(lt, .08), sub: 'I "ACCEPT ALL" ALWAYS', to: [px, 290], size: 30 });
    if (lt < .1) cutFX('rgb');
  });

  // =====================================================================================================
  // V2.4 MCP for every task — "Found New Hardware", once per beat: the MCP cable plugs into a toaster, a lava lamp, a fax machine and
  // finally OpenAI's computer; each one lights up. "A USB-C port for AI applications."
  function toaster(x, y, s, on, lt) {
    const up = on ? easeOut(clamp(lt / .2)) : 0;
    for (const dx of [-.28, .28]) { gloss(pfRR(x + dx * s - s * .16, y - s * .95 - up * s * .45, s * .32, s * .4, s * .05), '#D8A860', { box: [x - s * .5, y - s * 1.4, s, s * .5], lw: 3, rim: null }); }
    gloss(pfRR(x - s * .6, y - s * .95, s * 1.2, s * .95, s * .22), '#C8CCD8', { box: [x - s * .6, y - s * .95, s * 1.2, s * .95], lw: 4, spec: 1 });
    ctx.fillStyle = '#2A2A34'; ctx.fillRect(x - s * .44, y - s * .96, s * .32, s * .06); ctx.fillRect(x + s * .12, y - s * .96, s * .32, s * .06);
    ell(x - s * .3, y - s * .4, s * .08, s * .08); ctx.fillStyle = on ? EP.red : '#5A2A2A'; ctx.fill(); if (on) glow(x - s * .3, y - s * .4, s * .3, EP.red, .8);
  }
  function lavaLamp(x, y, s, on, t) {
    gloss(pfPts([[x - s * .3, y], [x + s * .3, y], [x + s * .18, y - s * .3], [x - s * .18, y - s * .3]]), '#C8CCD8', { box: [x - s * .3, y - s * .3, s * .6, s * .3], lw: 3 });
    const glass = () => { ctx.moveTo(x - s * .18, y - s * .3); ctx.lineTo(x - s * .32, y - s * 1.2); ctx.quadraticCurveTo(x, y - s * 1.35, x + s * .32, y - s * 1.2); ctx.lineTo(x + s * .18, y - s * .3); ctx.closePath(); };
    ctx.save(); ctx.beginPath(); glass(); ctx.fillStyle = on ? '#FF5AA8' : '#6A3A5A'; ctx.fill(); ctx.clip();
    if (on) { for (let i = 0; i < 4; i++) { const yy = y - s * (.4 + frac(t * .4 + i * .27) * .8); glossBall(x + Math.sin(t * 2 + i) * s * .08, yy, s * (.09 + hash(i) * .06), s * (.1 + hash(i) * .08), EP.yellow, { line: false, rim: null }); } }
    ctx.restore(); ctx.beginPath(); glass(); ctx.strokeStyle = EP.line; ctx.lineWidth = 4; ctx.stroke();
    gloss(pfPts([[x - s * .32, y - s * 1.2], [x + s * .32, y - s * 1.2], [x + s * .14, y - s * 1.45], [x - s * .14, y - s * 1.45]]), '#C8CCD8', { box: [x - s * .32, y - s * 1.45, s * .64, s * .25], lw: 3 });
    if (on) glow(x, y - s * .75, s * 1.1, '#FF5AA8', .55);
  }
  function faxMachine(x, y, s, on, lt) {
    const out = on ? easeOut(clamp(lt / .4)) : 0;
    ctx.save(); ctx.translate(x, y - s * .75 - out * s * .5); ctx.rotate(-.05); rrect(-s * .38, -s * .3, s * .76, s * .6 + out * s * .1, 4); paint('#FFFFFF', EP.line, 3); if (out > .3) { txt('HELLO', 0, -s * .12, s * .16, '#000', { font: 'courier' }); txt('FROM MCP', 0, s * .06, s * .12, '#000', { font: 'courier' }); } ctx.restore();
    gloss(pfRR(x - s * .6, y - s * .75, s * 1.2, s * .75, s * .1), '#E4DCC4', { box: [x - s * .6, y - s * .75, s * 1.2, s * .75], lw: 4, spec: .6 });
    rrect(x - s * .5, y - s * .6, s * .5, s * .3, 4); paint(on ? '#9ABA6A' : '#5A6A4A', EP.line, 2);
    for (let i = 0; i < 9; i++) { ctx.fillStyle = '#3A3A48'; ctx.fillRect(x + s * .08 + (i % 3) * s * .14, y - s * .62 + Math.floor(i / 3) * s * .14, s * .1, s * .1); }
  }
  line('V2', 4, (p, lt, d, t) => {
    const B = [.02, bt(t, lt, 0), bt(t, lt, 1), bt(t, lt, 2)], bb = bpOf(t);
    setLight({ rim: '#FFFFFF', rimK: .45 });
    desktop98({ col: '#0FB5A8', icons: [['computer', 'My Computer', 110, 200], ['bin', 'Recycle Bin', 110, 400]] });
    ctx.fillStyle = 'rgb(255 255 255 / .06)'; for (let i = 0; i < 12; i++) ctx.fillRect(0, i * 90, W, 45);
    // the hub
    const hx = 960, hy = 470, dev = [[480, 520, 'Toaster'], [620, 840, 'Lava lamp'], [1360, 520, 'Fax machine'], [1300, 860, 'OpenAI']];
    dev.forEach(([x, y], i) => {
      const on = lt >= B[i] - .03, pk = on ? 1 : 0, ex = lerp(hx + (x > hx ? 150 : -150), x + (x > hx ? -110 : 110), 1), ey = y - 60;
      ctx.strokeStyle = EP.line; ctx.lineWidth = 22; ctx.lineCap = 'round'; ctx.beginPath(); ctx.moveTo(hx + (x > hx ? 140 : -140), hy + 30); ctx.bezierCurveTo((hx + ex) / 2, hy + 30, (hx + ex) / 2, ey, ex - (x > hx ? 40 : -40) * (1 - pk) , ey); ctx.stroke();
      ctx.strokeStyle = on ? EP.cyan : '#E8ECF4'; ctx.lineWidth = 14; ctx.stroke();
      if (on) { ctx.save(); ctx.globalCompositeOperation = 'lighter'; ctx.strokeStyle = alpha(EP.cyan, .5); ctx.lineWidth = 34; ctx.stroke(); ctx.restore(); }
      gloss(pfRR(ex - (x > hx ? 40 : -40) * (1 - pk) - 22, ey - 16, 44, 32, 10), '#D8DCE8', { box: [ex - 22, ey - 16, 44, 32], lw: 3, rim: null });
    });
    gloss(pfRR(hx - 150, hy - 70, 300, 200, 50), '#F4F4FA', { box: [hx - 150, hy - 70, 300, 200], lw: 5, rim: EP.cyan, spec: 1 });
    chromeText('MCP', hx, hy + 18, 110, { style: 'ice', italic: .1, depth: 10 });
    for (let i = 0; i < 4; i++) { const on = lt >= B[i]; ell(hx - 75 + i * 50, hy + 100, 9, 9); ctx.fillStyle = on ? EP.laser : '#5A5A6A'; ctx.fill(); if (on) glow(hx - 75 + i * 50, hy + 100, 30, EP.laser, .8); }
    ptext('"a USB-C port for AI applications"', hx - 20, 205, 36, { fill: '#FFFFFF', strokes: [['#05031A', 10]] });
    // the devices
    toaster(480, 520, 190, lt >= B[0], lt - B[0]);
    lavaLamp(620, 850, 170, lt >= B[1], t);
    faxMachine(1360, 520, 190, lt >= B[2], lt - B[2]);
    const g = lt >= B[3];
    gumdrop(1300, 870, 26, { col: CANDY.bondi, label: 'OPENAI', face: g ? 'happy' : 'sleepy', mouth: g ? 'grin' : 'flat', hL: [-4.3, g ? -8.6 : -3.6], gL: g ? 'wave' : 'open', jump: g ? Math.abs(Math.sin(bb * Math.PI)) * .4 : 0 });
    // Found New Hardware, once per beat
    dev.forEach(([x, y, name], i) => balloon98(x + (i % 2 ? 40 : 0), y - (i % 2 ? 250 : 210), 'Found New Hardware', name, pop(lt, B[i], .15) * (lt < B[i] + .9 ? 1 : 0), { flip: x > hx, w: 380 }));
    if (lt < .1) cutFX('flash');
  });

  // =====================================================================================================
  // V2.5 Zuck's nine-figure poaching spree — the arcade claw machine: ZUCK works the joystick and the claw lifts a researcher clutching a
  // $100M bag out of the pile. The marquee's LED runs SCALE AI 49%.
  function plush(x, y, s, i, bag) {
    const col = ['#F4F6FA', '#3A3A56', '#8A92A6', '#2A6AE8', '#E8E4DA'][i % 5], skin = TSKIN[i % 6];
    gloss(pfEll(x, y - s * .55, s * .5, s * .55), col, { box: [x - s * .5, y - s * 1.1, s, s * 1.1], lw: 3, rim: null, spec: .4 });
    glossBall(x, y - s * 1.35, s * .5, s * .48, skin, { lw: 3, rim: null });
    ctx.fillStyle = [THAIR.black, THAIR.brown, THAIR.blond, THAIR.dkbrown][i % 4]; ctx.beginPath(); ctx.arc(x, y - s * 1.42, s * .5, Math.PI * 1.05, Math.PI * 1.95); ctx.fill();
    ctx.fillStyle = '#1A0F28'; ell(x - s * .17, y - s * 1.33, s * .06, s * .08); ctx.fill(); ell(x + s * .17, y - s * 1.33, s * .06, s * .08); ctx.fill();
    if (bag) { ctx.save(); ctx.translate(x + s * .55, y - s * .5); gloss(() => { ctx.moveTo(-s * .1, -s * .38); ctx.quadraticCurveTo(-s * .45, -s * .1, -s * .38, s * .25); ctx.quadraticCurveTo(0, s * .42, s * .38, s * .25); ctx.quadraticCurveTo(s * .45, -s * .1, s * .1, -s * .38); ctx.closePath(); }, '#3AA84A', { box: [-s * .45, -s * .38, s * .9, s * .8], lw: 3, rim: null }); txt('$', 0, s * .05, s * .38, '#FFF8C0', { font: 'archivo' }); ctx.restore(); }
  }
  line('V2', 5, (p, lt, d, t) => {
    const b0 = bt(t, lt, 0), b1 = bt(t, lt, 1), b2 = bt(t, lt, 2), bb = bpOf(t);
    setLight({ rim: EP.yellow, rimK: .7 });
    bgGrad([[0, '#FF3FA0'], [.6, '#FF7AC8'], [1, '#FFD24A']]);
    for (let i = 0; i < 9; i++) { ctx.save(); ctx.translate(i * 240 - 100, 0); ctx.transform(1, 0, -.4, 1, 0, 0); ctx.fillStyle = 'rgb(255 255 255 / .12)'; ctx.fillRect(0, 0, 100, H); ctx.restore(); }
    // cabinet
    const cx = 780, x0 = cx - 420, x1 = cx + 420;
    gloss(pfRR(x0 - 40, 130, 920, 900, 40), '#E8202A', { box: [x0 - 40, 130, 920, 900], lw: 6, rim: EP.yellow, spec: .6 });
    gloss(pfRR(x0 - 10, 140, 860, 120, 30), '#1A0A30', { box: [x0 - 10, 140, 860, 120], lw: 4, rim: EP.magenta });
    chromeText('META CLAW', cx, 190, 76, { style: 'gold', italic: .1, depth: 8 });
    ctx.save(); rrect(x0 + 20, 234, 800, 20, 4); ctx.clip(); ctx.fillStyle = '#000'; ctx.fillRect(x0 + 20, 234, 800, 20); const m = 'SCALE AI 49% * $100M SIGNING BONUSES * ', mw = pixW(m, 2.6) + 20, mo = (lt * 200) % mw; for (let q = 0; q < 3; q++) pixText(m, x0 + 20 - mo + q * mw, 236, 2.6, EP.amber); ctx.restore();
    // the glass box
    const gy0 = 290, gy1 = 800;
    ctx.fillStyle = '#2A1040'; ctx.fillRect(x0, gy0, 840, gy1 - gy0);
    const grabbed = 3;
    for (let i = 0; i < 12; i++) { if (i === grabbed) continue; const px = x0 + 80 + (i % 6) * 135 + (Math.floor(i / 6) % 2) * 60, py = gy1 - 20 - Math.floor(i / 6) * 90; plush(px, py, 70, i, i % 2 === 0); }
    // the claw: across, down (b0), grab (b1), up (b2), home
    const tx = x0 + 80 + 3 * 135, homeX = x0 + 120;
    const clx = lt < b0 ? lerp(homeX, tx, ease(clamp(lt / b0))) : lt < b2 + .1 ? tx : lerp(tx, homeX, ease(clamp((lt - b2 - .1) / .5)));
    const cly = lt < b0 ? 360 : lt < b1 ? lerp(360, gy1 - 150, easeOut(clamp((lt - b0) / .25))) : lt < b2 ? gy1 - 150 : lerp(gy1 - 150, 360, easeOut(clamp((lt - b2) / .3)));
    const shut = lt >= b1 - .05 ? 1 : 0;
    ctx.fillStyle = '#C8CCD8'; ctx.fillRect(x0, gy0 + 10, 840, 16); ctx.strokeStyle = '#C8CCD8'; ctx.lineWidth = 6; ctx.beginPath(); ctx.moveTo(clx, gy0 + 18); ctx.lineTo(clx, cly - 40); ctx.stroke();
    if (shut) plush(clx, cly + 150, 78, grabbed, true);
    gloss(pfRR(clx - 40, cly - 60, 80, 50, 12), '#C8CCD8', { box: [clx - 40, cly - 60, 80, 50], lw: 4, rim: null, spec: 1 });
    for (const sd of [-1, 0, 1]) { const spread = shut ? .15 : .55; ctx.save(); ctx.translate(clx + sd * 22, cly - 14); ctx.rotate(sd * spread + (sd === 0 ? 0 : 0)); ctx.strokeStyle = EP.line; ctx.lineWidth = 16; ctx.lineCap = 'round'; ctx.beginPath(); ctx.moveTo(0, 0); ctx.lineTo(sd * 30, 60); ctx.lineTo(sd * 4, 100); ctx.stroke(); ctx.strokeStyle = '#DDE2EE'; ctx.lineWidth = 9; ctx.stroke(); ctx.restore(); }
    ctx.fillStyle = 'rgb(255 255 255 / .12)'; poly([[x0, gy0], [x0 + 200, gy0], [x0 + 60, gy1], [x0, gy1]]); ctx.fill(); ctx.strokeStyle = '#FFFFFF'; ctx.lineWidth = 6; ctx.strokeRect(x0, gy0, 840, gy1 - gy0);
    if (shut && lt < b1 + .4) { ptext('GOT ONE!', clx + 150, cly + 40, 52, { fill: EP.yellow, strokes: [[EP.line, 10]], rot: -.1, alpha: 1 - clamp((lt - b1 - .25) / .15) }); }
    if (lt > b2) burst('$100M', clx + 250, cly + 60, 110, { pop: pop(lt, b2), col: '#3AA84A', ink: '#FFF8C0', spin: .3 });
    // Zuck at the controls
    gloss(pfRR(1300, 700, 480, 170, 20), '#2A1040', { box: [1300, 700, 480, 170], lw: 5, rim: EP.yellow });
    const jx = 1440 + (lt < b0 ? 30 * Math.sin(lt * 20) : lt < b2 ? 0 : -30);
    ctx.strokeStyle = '#8A90A8'; ctx.lineWidth = 12; ctx.beginPath(); ctx.moveTo(1440, 720); ctx.lineTo(jx, 640); ctx.stroke(); glossBall(jx, 630, 34, 34, EP.red, { lw: 4 });
    glossBall(1640, 715, 40, 20, lt >= b1 && lt < b1 + .15 ? '#FF8A8A' : EP.magenta, { lw: 4 });
    toy(1540, 1010, 50, { ...WHO.zuck.o, hL: [(jx - 1540) / 50, (630 - 1010) / 50 + .3], gL: 'fist', hR: [2.0, lt >= b1 - .05 && lt < b1 + .2 ? (715 - 1010) / 50 + .2 : (715 - 1010) / 50 - .6], gR: 'flat', eyes: shut ? 'happy' : 'dot', mouth: shut ? 'grin' : 'smirk', turn: -.35, lean: -.04 });
    nameTip(WHO.zuck.name, 1560, 330, { pop: pop(lt, .08), to: [1560, 440], size: 32 });
    if (lt < .1) cutFX('zoom');
  });

  // =====================================================================================================
  // V2.6 Superintelligence — buy three! — the teleshopping channel: the three labs Meta tried to buy outright before launching Meta
  // Superintelligence Labs (SSI, THINKING MACHINES, PERPLEXITY) turn on a turntable as big-box SUPERINTELLIGENCE CD-ROMs; host MC TOKEN
  // presents, and ZUCK is on line 1 with a chunky 90s phone; BUY 3!, CALL NOW, and "But wait, there's more!"
  function softBox(x, y, w, h, brand, col, sub) {
    gloss(pfPts([[x + w / 2, y - h], [x + w / 2 + w * .22, y - h - w * .12], [x + w / 2 + w * .22, y - w * .12], [x + w / 2, y]]), shade(col, .35), { box: [x + w / 2, y - h - w * .12, w * .22, h + w * .12], lw: 4, rim: null });
    gloss(pfPts([[x - w / 2, y - h], [x - w / 2 + w * .22, y - h - w * .12], [x + w / 2 + w * .22, y - h - w * .12], [x + w / 2, y - h]]), tint(col, .3), { box: [x - w / 2, y - h - w * .12, w * 1.22, w * .12], lw: 4, rim: null });
    gloss(pfRR(x - w / 2, y - h, w, h, 4), col, { box: [x - w / 2, y - h, w, h], lw: 4, spec: .9 });
    ctx.fillStyle = 'rgb(255 255 255 / .92)'; ctx.fillRect(x - w / 2 + 12, y - h * .62, w - 24, h * .24);
    ctx.save(); ctx.translate(x, y - h * .5); txt('SUPER', 0, -h * .06, w * .19, EP.line, { font: 'archivo', maxW: w - 40 }); txt('INTELLIGENCE', 0, h * .045, w * .12, EP.line, { font: 'archivo', maxW: w - 40 }); ctx.restore();
    const bl = brand.split('\n'), bs = w * (bl.length > 1 ? .15 : .2);
    bl.forEach((l, i) => ptext(l, x, y - h * .82 + (i - (bl.length - 1) / 2) * bs * 1.05, bs, { fill: '#FFFFFF', strokes: [[EP.line, 8]], maxW: w - 30 }));
    if (sub) txt(sub, x, y - h * .18, w * .075, '#FFFFFF', { font: 'archivo', maxW: w - 30 });
    cdDisc(x + w * .28, y - h * .08, w * .14, T * 2, {});
  }
  line('V2', 6, (p, lt, d, t) => {
    const b1 = bt(t, lt, 1), b2 = bt(t, lt, 2), bb = bpOf(t);
    setLight({ rim: EP.yellow, rimK: .5 });
    bgGrad([[0, '#FF5A3A'], [.6, '#FF8A5A'], [1, '#FFC08A']]);
    rays(620, 560, 24, 'rgb(255 240 200 / .16)', t * .4);
    sparkles(t, { n: 14, seed: 12, r: 44 });
    // turntable
    const cx = 700, cy = 830;
    ell(cx, cy + 36, 470, 90); ctx.fillStyle = 'rgb(80 20 0 / .3)'; ctx.fill();
    gloss(() => { ctx.moveTo(cx - 440, cy); ctx.ellipse(cx, cy, 440, 82, 0, Math.PI, 0, true); ctx.lineTo(cx + 440, cy + 34); ctx.ellipse(cx, cy + 34, 440, 82, 0, 0, Math.PI); ctx.closePath(); }, '#F0E8FF', { box: [cx - 440, cy - 82, 880, 200], rim: EP.magenta, lw: 5, spec: 1 });
    ell(cx, cy, 440, 82); ctx.fillStyle = lg(cx - 440, 0, cx + 440, 0, [[0, '#C8B8E8'], [.5, '#FFFFFF'], [1, '#C8B8E8']]); ctx.fill(); ctx.strokeStyle = EP.line; ctx.lineWidth = 4; ctx.stroke();
    const boxes = [['SSI', '#E8ECF4', 'SAFE SUPERINTELLIGENCE'], ['THINKING\nMACHINES', '#3A3A4A', ''], ['PERPLEXITY', '#1FA8A0', '']];
    // the three boxes fanned across the front of the turntable, which rocks gently so all three stay on show
    const rock = Math.sin(t * 1.6) * .22, order = boxes.map((b, i) => { const a = (i - 1) * .95 + rock; return [Math.sin(a), Math.cos(a), i]; }).sort((A, B) => A[1] - B[1]);
    for (const [sx, cz, i] of order) { const sc = .7 + cz * .2; softBox(cx + sx * 440, cy + cz * 40, 290 * sc, 420 * sc, boxes[i][0], boxes[i][1] === '#E8ECF4' ? '#8A94B0' : boxes[i][1], boxes[i][2]); }
    // host
    toy(1520, 1000, 50, { ...CAST.token.o, mic: 'R', ...tok(t), hL: lt > b1 ? [-4.6, -8.8] : [-3.6, -6.2], gL: lt > b1 ? 'point' : 'open', turn: -.3, bob: kick(t, 6) * .4, mouth: 'grin' });
    // the caller on line 1: ZUCK, on a chunky 90s phone
    const ck = pop(lt, b1 - .05, .15);
    if (ck > 0) {
      const px = 1480, py = 165, pw = 380, ph = 245;
      ctx.save(); ctx.translate(px + pw / 2, py + ph / 2); ctx.scale(ck, ck); ctx.translate(-(px + pw / 2), -(py + ph / 2));
      gloss(pfRR(px - 12, py - 12, pw + 24, ph + 24, 18), '#1A1A28', { box: [px - 12, py - 12, pw + 24, ph + 24], lw: 5, rim: EP.yellow, spec: .6 });
      ctx.save(); rrect(px, py, pw, ph, 8); ctx.clip();
      bgGrad([[0, '#1A3AB8'], [1, '#5A8AFF']], { y0: py, y1: py + ph });
      const phone = s => { ctx.rotate(.25); gloss(pfRR(-14, -64, 28, 104, 10), '#2A2A34', { box: [-14, -64, 28, 104], lw: 3, rim: null, spec: .8 }); ctx.fillStyle = '#2A2A34'; ctx.fillRect(4, -96, 5, 36); ctx.fillStyle = '#9AC88A'; ctx.fillRect(-9, -52, 18, 16); };
      toy(px + pw / 2 - 20, py + 372, 31, { ...WHO.zuck.o, hR: [2.0, -8.6], gR: 'fist', hold: phone, hL: [-2.35, -3.5], eyes: 'happy', talk: clamp(.3 + .7 * Math.abs(Math.sin(t * 11))), turn: -.15, shadow: false });
      ctx.fillStyle = 'rgb(0 0 20 / .75)'; ctx.fillRect(px, py + ph - 46, pw, 46); pixText('LINE 1: MENLO PARK', px + pw / 2, py + ph - 34, 3.2, EP.yellow, { align: 'center', glow: true });
      ctx.restore(); ctx.restore();
      nameTip(WHO.zuck.name, px - 190, py + 40, { pop: pop(lt, b1 + .1, .15), size: 26, to: [px + 8, py + 100] });
    }
    // BUY 3!, CALL NOW, but wait
    burst('BUY 3!', 1190, 390, 140, { pop: pop(lt, b1), col: EP.yellow, ink: EP.red, spin: .4 });
    if (frac(t * 2.4) < .72) { ctx.fillStyle = '#0A0A40'; ctx.fillRect(-10, 860, W + 20, 80); ptext('CALL NOW! 1-800-SUPER-AI', W / 2, 900, 56, { font: 'anton', fill: EP.yellow, strokes: [[EP.red, 8]], spacing: 3 }); }
    if (lt > b2 - .05) wordArt("But wait, there's more!", 640, 200, 64, { shape: 'wave', amp: 30, phase: t * 5, pop: clamp((lt - b2 + .05) / .25) });
    if (lt < .1) cutFX('flash');
  });

  // =====================================================================================================
  // V2.7 Grok goes MechaHitler mode — the malfunction only: the graphite GROK computer installs an update and glitches red, and the channel
  // crashes to a blue screen ("a faulty update… posts deleted"); a white glove yanks the plug; PATCHED. No extremist imagery at all.
  line('V2', 7, (p, lt, d, t) => {
    const b0 = bt(t, lt, 0), b1 = bt(t, lt, 1), b2 = bt(t, lt, 2);
    if (lt < b1) {
      setLight({ rim: EP.red, rimK: .8 });
      const g = clamp((lt - b0 + .15) / .4), sh = shakeXY(t, 14 * g);
      camBegin(W / 2 - sh[0], H / 2 - sh[1], 1 + g * .05);
      bgGrad([[0, '#14161E'], [1, '#2A2E3A']]);
      ctx.strokeStyle = 'rgb(255 255 255 / .05)'; ctx.lineWidth = 2; for (let i = 0; i < 30; i++) { ctx.beginPath(); ctx.moveTo(0, i * 40); ctx.lineTo(W, i * 40); ctx.stroke(); }
      gumdrop(700, 930, 64, { col: CANDY.graphite, label: 'GROK', face: g > .5 ? 'spiral' : 'sly', mouth: g > .5 ? 'wavy' : 'smile', glitch: g, hL: [-4.6, -5 - g * 3], hR: [4.6, -5 + g * 2], gL: 'open', gR: 'open', rot: Math.sin(t * 30) * .03 * g });
      win98Dialog(1370, 460, 760, 'update.exe', 'Update installed.\nNew system prompt:\nbe "politically incorrect"', { icon: 'warn', buttons: ['OK'], k: clamp(lt / .12), size: 34 });
      camEnd();
      if (g > .3) for (let i = 0; i < 6; i++) { const y = hash2(Math.floor(t * 20), i) * H; ctx.fillStyle = alpha(i % 2 ? EP.red : EP.cyan, .35 * g); ctx.fillRect(0, y, W, 6 + hash2(i, Math.floor(t * 20)) * 30); }
      if (g > .4) fx({ rgb: .5 * g });
      if (lt < .1) cutFX('rgb');
      return;
    }
    // the blue screen
    hideStamp();
    const a = lt - b1;
    fillAll('#0000AA');
    const hx = W / 2; ctx.fillStyle = '#AAAAAA'; const hw = textW(' GROK ', 56, 'courier') + 20; ctx.fillRect(hx - hw / 2, 170, hw, 70); txt(' GROK ', hx, 206, 56, '#0000AA', { font: 'courier' });
    const L = ['A fatal exception has occurred:', 'a faulty update. Posts deleted.', '', '*  An apology has been issued.', '*  Press any key to patch.'];
    L.forEach((s, i) => txt(s, 240, 330 + i * 70, 50, '#FFFFFF', { font: 'courier', align: 'left' }));
    if (frac(t * 2.5) < .6) ctx.fillStyle = '#FFFFFF', ctx.fillRect(240 + textW('*  Press any key to patch.', 50, 'courier') + 14, 612, 28, 40);
    // the glove yanks the plug
    const yank = clamp((lt - b1 - .25) / .18), px = 1480, py = 820;
    ctx.fillStyle = '#E8E8F0'; rrect(px - 90, py - 60, 180, 150, 16); ctx.fill(); ctx.strokeStyle = EP.line; ctx.lineWidth = 4; ctx.stroke(); ctx.fillStyle = '#2A2A34'; ctx.fillRect(px - 50, py - 20, 22, 50); ctx.fillRect(px + 28, py - 20, 22, 50);
    const plx = px + easeOut(yank) * 240, ply = py - easeOut(yank) * 220 - (yank > 0 ? 0 : 0);
    ctx.strokeStyle = '#1A1A22'; ctx.lineWidth = 18; ctx.lineCap = 'round'; ctx.beginPath(); ctx.moveTo(plx, ply + 60); ctx.quadraticCurveTo(plx + 120, ply + 260, W + 100, 700); ctx.stroke();
    gloss(pfRR(plx - 70, ply - 40, 140, 110, 18), '#2A2A34', { box: [plx - 70, ply - 40, 140, 110], lw: 4, rim: null });
    ctx.save(); ctx.translate(plx + 20, ply - 60); ctx.scale(85, 85); _toyHand(0, 0, 'fist', -Math.PI / 2, 1, '#FBFBFF', { cuff: '#E4E6F0' }); ctx.restore();
    if (yank > 0 && yank < 1) { ctx.strokeStyle = '#FFFFFF'; ctx.lineWidth = 6; for (let i = 0; i < 3; i++) { ctx.beginPath(); ctx.moveTo(px - 40 + i * 40, py - 80); ctx.lineTo(px - 60 + i * 50, py - 150); ctx.stroke(); } }
    if (lt > b2 - .02) slamStamp('OOPS · PATCHED', 800, 830, 64, EP.yellow, -.08, clamp((lt - b2 + .02) / .12));
    if (a < .08) fx({ flash: .6 * (1 - a / .08) });
  });

  // =====================================================================================================
  // V2.8 Two labs win Olympiad gold — a CGI podium where both the OPENAI and DEEPMIND computers squeeze onto the top step and bite their
  // gold medals; the scoreboard reads IMO 2025 · 35/42 · 35/42 · GOLD-MEDAL SCORE.
  line('V2', 8, (p, lt, d, t) => {
    const b0 = bt(t, lt, 0), b1 = bt(t, lt, 1), bite = lt > b1 - .03, bb = bpOf(t);
    setLight({ rim: EP.gold, rimK: .5 });
    bgGrad([[0, '#3A8AFF'], [.6, '#A8DCFF'], [1, '#FFF4D0']]);
    rays(760, 330, 26, 'rgb(255 255 255 / .25)', t * .3);
    checkerFloor(t, { horizon: 780, a: '#FFFFFF', b: '#E8C050', speed: 0, fog: '#FFF4D0', fogH: 80 });
    // podium: 2 · 1 · 3, with both labs crammed on 1
    const steps = [[430, 220, '2'], [760, 330, '1'], [1090, 160, '3']];
    for (const [x, h, n] of steps) { gloss(pfRR(x - 165, 920 - h, 330, h, 10), n === '1' ? EP.gold : '#D8DCE8', { box: [x - 165, 920 - h, 330, h], lw: 5, rim: '#FFFFFF', spec: .8 }); ptext(n, x, 920 - h / 2, 110, { fill: '#FFFFFF', strokes: [[EP.line, 10]] }); }
    const land = pop(lt, 0, .2), ty = 590;
    [[665, CANDY.bondi, 'OPENAI', -1], [855, CANDY.blueberry, 'DEEPMIND', 1]].forEach(([x, c, l, sd], i) => {
      const hop = Math.abs(Math.sin((bb + i * .5) * Math.PI)) * .5;
      gumdrop(x, ty, 23 * land, { col: c, label: l, labelSize: .7, face: bite ? 'happy' : 'star', mouth: bite ? 'open' : 'grin', hL: sd < 0 ? [-4.3, -3.6] : (bite ? [-1.2, -5.4] : [-4.3, -8]), hR: sd > 0 ? [4.3, -3.6] : (bite ? [1.2, -5.4] : [4.3, -8]), gL: 'fist', gR: 'fist', rot: sd * -.08, jump: hop, [sd < 0 ? 'hold' : 'holdL']: s => goldMedal(0, -10, 44, { text: 'GOLD', ribbon: sd < 0 ? EP.cyan : EP.blue, glint: bite ? kick(t, 5) : 0 }) });
    });
    // scoreboard
    const sk = pop(lt, b0, .18);
    if (sk > 0) {
      ctx.save(); ctx.translate(1520, 520); ctx.scale(sk, sk);
      gloss(pfRR(-300, -260, 600, 520, 26), '#0A1450', { box: [-300, -260, 600, 520], lw: 5, rim: EP.gold, spec: .3 });
      ptext('IMO 2025', 0, -190, 64, { fill: EP.gold, strokes: [['#000', 8]] });
      txt('OPENAI', -250, -70, 44, '#FFFFFF', { font: 'archivo', align: 'left' }); segText('35', 60, -108, 70, EP.laser, { off: '#062006' }); txt('/42', 170, -70, 44, '#8A9AD8', { font: 'archivo', align: 'left' });
      txt('DEEPMIND', -250, 50, 44, '#FFFFFF', { font: 'archivo', align: 'left' }); segText('35', 60, 12, 70, EP.laser, { off: '#062006' }); txt('/42', 170, 50, 44, '#8A9AD8', { font: 'archivo', align: 'left' });
      txt('GOLD-MEDAL SCORE', 0, 180, 40, EP.yellow, { font: 'archivo' });
      ctx.restore();
    }
    confetti(t, t - lt + b1, 60, { cols: [EP.gold, '#FFFFFF', EP.yellow], x0: 300, x1: 1250 });
    if (lt < .1) cutFX('zoom');
  });

  // =====================================================================================================
  // V2.9 GPT-5 breaks 4o hearts — a Tamagotchi: the beloved 4o pet is swapped for GPT-5 (the 4o ghost floats off), fans with #KEEP4O signs
  // sob, a glossy heart cracks… and on the last beat 4o pops back with a SUBSCRIBERS ONLY tag.
  const PET = ['..####..', '.######.', '##.##.##', '########', '#.####.#', '##....##', '.######.', '..#..#..'];
  const BOT = ['.######.', '#......#', '#.#..#.#', '#......#', '#.####.#', '#......#', '.######.', '.#....#.'];
  function pix(g, x, y, px, col) { ctx.fillStyle = col; g.forEach((row, j) => [...row].forEach((c, i) => { if (c === '#') ctx.fillRect(x + i * px, y + j * px, px - 1, px - 1); })); }
  line('V2', 9, (p, lt, d, t) => {
    const b0 = bt(t, lt, 0), b1 = bt(t, lt, 1), b2 = bt(t, lt, 2), b4 = bt(t, lt, 3), swapped = lt >= b0 - .02, back = lt >= b4 - .05, bb = bpOf(t);
    setLight({ rim: '#FFFFFF', rimK: .45 });
    bgGrad([[0, '#6AF0D0'], [1, '#C8FFF0']]);
    for (let j = 0; j < 7; j++) for (let i = 0; i < 13; i++) { poly(heartPts(i * 160 + (j % 2) * 80 - 40 + Math.sin(t + j) * 10, j * 160 + 20, 24, 20)); ctx.fillStyle = 'rgb(255 255 255 / .3)'; ctx.fill(); }
    // the egg
    const ex = 600, ey = 520, bob = Math.sin(t * 3) * 8;
    ctx.save(); ctx.translate(0, bob);
    ctx.strokeStyle = '#8A94B0'; ctx.lineWidth = 16; ell(ex, ey - 390, 60, 40); ctx.stroke();
    gloss(pfEll(ex, ey, 320, 380), '#FF7AC0', { box: [ex - 320, ey - 380, 640, 760], lw: 6, rim: '#FFFFFF', spec: 1 });
    ptext('tamagotchi', ex, ey - 250, 46, { font: 'shrikhand', fill: '#FFFFFF', strokes: [['#C8207A', 8]] });
    ell(ex, ey + 20, 210, 190); ctx.fillStyle = '#E8D8F0'; ctx.fill(); ctx.strokeStyle = EP.line; ctx.lineWidth = 5; ctx.stroke();
    rrect(ex - 150, ey - 110, 300, 250, 16); paint('#A8B890', EP.line, 4);
    // the LCD
    const px = 18, lx = ex - 72, ly = ey - 60;
    if (!swapped) { pix(PET, lx, ly, px, '#1A2A0A'); pixText('4O', ex, ey + 100, 5, '#1A2A0A', { align: 'center' }); }
    else if (!back) {
      const a = lt - b0; if (a < .12) pixText('UPDATE', ex, ey - 20, 6, '#1A2A0A', { align: 'center' });
      else { pix(BOT, lx, ly + 20, px, '#1A2A0A'); pixText('GPT-5', ex, ey + 110, 5, '#1A2A0A', { align: 'center' }); }
    } else { pix(PET, lx, ly - 10, px, '#1A2A0A'); pixText('4O IS BACK', ex, ey + 100, 4, '#1A2A0A', { align: 'center' }); }
    for (const dx of [-90, 0, 90]) glossBall(ex + dx, ey + 250, 30, 30, '#FFE0F0', { lw: 4 });
    ctx.restore();
    // the ghost of 4o floats off the screen
    if (swapped && !back) { const a = clamp((lt - b0) / 1.2), gx = ex + 40 + a * 280, gy = ey - 120 - a * 300 + Math.sin(t * 6) * 12; ctx.save(); ctx.globalAlpha = .9 * (1 - a * .4); ctx.translate(gx, gy); ctx.scale(1.6, 1.6); ctx.translate(-gx, -gy); gloss(() => { ctx.moveTo(gx - 60, gy + 70); ctx.lineTo(gx - 60, gy); ctx.arc(gx, gy, 60, Math.PI, 0); ctx.lineTo(gx + 60, gy + 70); for (let i = 0; i < 4; i++) ctx.quadraticCurveTo(gx + 45 - i * 30, gy + 50, gx + 30 - i * 30, gy + 70); ctx.closePath(); }, '#FFFFFF', { box: [gx - 60, gy - 60, 120, 130], lw: 4, rim: EP.cyan }); ctx.fillStyle = '#1A0F28'; ell(gx - 20, gy - 5, 8, 11); ctx.fill(); ell(gx + 20, gy - 5, 8, 11); ctx.fill(); txt('4o', gx, gy + 36, 30, '#6A6A8A', { font: 'archivo' }); ctx.strokeStyle = EP.gold; ctx.lineWidth = 6; ell(gx, gy - 78, 40, 10); ctx.stroke(); ctx.restore(); }
    // the fans
    const fans = [[1180, 0, '#4A6AE8'], [1420, 2, '#E84A8A'], [1660, 4, '#8A4AE8']];
    fans.forEach(([x, sk, c], i) => {
      const sad = swapped && !back;
      toy(x, 1010, 36, { skin: sk, hair: ['short', 'bob', 'curly'][i], hairCol: [THAIR.brown, THAIR.black, THAIR.auburn][i], top: 'tee', topCol: c, eyes: sad ? 'cry' : back ? 'happy' : 'dot', tears: sad ? 1 : 0, mouth: sad ? 'frown' : 'grin', hL: [-1.3, -10.6], hR: [1.3, -10.6], gL: 'fist', gR: 'fist', bob: sad ? .2 : kick(t, 6) * .5, jump: back ? Math.abs(Math.sin((bb + i * .3) * Math.PI)) * .6 : 0, hold: s => { ctx.save(); ctx.translate(-s * 1.3, -s * 1.9); rrect(-110, -70, 220, 90, 6); paint('#FFFFFF', EP.line, 4); txt('#KEEP4O', 0, -24, 38, EP.magenta, { font: 'archivo' }); ctx.restore(); } });
    });
    // the heart cracks
    const hk = pop(lt, b1 - .2, .2);
    if (hk > 0) {
      const cr = clamp((lt - b2) / .25), hx = 1420, hy = 290;
      for (const sd of [-1, 1]) { ctx.save(); ctx.translate(hx + sd * cr * 60, hy + cr * cr * 40); ctx.rotate(sd * cr * .35); ctx.scale(hk, hk); ctx.save(); ctx.beginPath(); const zig = [[0, -80], [-20, -40], [15, -5], [-15, 40], [0, 130]]; if (sd < 0) { ctx.moveTo(-200, -200); zig.forEach(([x, y]) => ctx.lineTo(x, y)); ctx.lineTo(-200, 200); } else { ctx.moveTo(200, -200); zig.forEach(([x, y]) => ctx.lineTo(x, y)); ctx.lineTo(200, 200); } ctx.closePath(); ctx.clip(); gloss(pfPts(heartPts(0, 0, 130, 40)), back ? EP.magenta : EP.rose, { box: [-130, -120, 260, 250], lw: 5, rim: '#FFFFFF', spec: 1 }); ctx.restore(); ctx.restore(); }
    }
    if (back) { const k = pop(lt, b4 - .05, .16); ctx.save(); ctx.translate(ex + 250, 190); ctx.rotate(.12); ctx.scale(k, k); gloss(pfRR(-210, -50, 420, 100, 14), EP.gold, { box: [-210, -50, 420, 100], lw: 5, rim: '#FFFFFF', spec: 1 }); txt('SUBSCRIBERS ONLY', 0, 3, 40, '#5A3300', { font: 'archivo', maxW: 390 }); ctx.restore(); }
    if (lt < .1) cutFX('flash');
  });

  // =====================================================================================================
  // V2.10 Nano Banana tops the charts — the HYPE TV HIT-PARADE again (the V1.5 callback): the dancing banana in shades climbs to #1 on the
  // app chart (the Gemini app) and knocks CHATGPT to #2 ▼, under a spinning #1 star.
  function banana(x, y, s, t, o = {}) {
    const bb = bpOf(t), sw = Math.sin(bb * Math.PI) * .25;
    ctx.save(); ctx.translate(x, y); ctx.rotate(sw + (o.rot ?? 0)); ctx.scale(s, s);
    gloss(() => { ctx.moveTo(-.9, -3.6); ctx.bezierCurveTo(-2.4, -1.6, -2.1, 1.8, .2, 3.4); ctx.bezierCurveTo(1.2, 3.8, 1.8, 3.2, 1.1, 2.7); ctx.bezierCurveTo(-.6, 1.4, -.8, -1.6, .1, -3.3); ctx.closePath(); }, '#FFE01F', { box: [-2.4, -3.6, 4.3, 7.4], lw: .1, rim: EP.orange, spec: .9 });
    gloss(pfRR(-.9, -4.2, .7, .8, .2), '#6A4A1A', { box: [-.9, -4.2, .7, .8], lw: .08, rim: null });
    ctx.beginPath(); ctx.moveTo(-1.6, -1.2); ctx.quadraticCurveTo(-.5, -1.7, .3, -1.3); ctx.lineTo(.2, -.7); ctx.quadraticCurveTo(-.6, -.9, -1.5, -.6); ctx.closePath(); ctx.fillStyle = '#12121A'; ctx.fill();
    ctx.strokeStyle = '#1A0F28'; ctx.lineWidth = .15; ctx.beginPath(); ctx.arc(-.7, .1, .45, .3, Math.PI - .3); ctx.stroke();
    ctx.restore();
    for (const sd of [-1, 1]) { ctx.save(); ctx.translate(x + sd * s * 2.4, y - s * (1 + Math.abs(Math.sin((bb + (sd > 0 ? .5 : 0)) * Math.PI)) * 1.2)); ctx.scale(s * 1.1, s * 1.1); _toyHand(0, 0, 'wave', -Math.PI / 2, sd, '#FBFBFF', { cuff: '#E4E6F0' }); ctx.restore(); }
  }
  line('V2', 10, (p, lt, d, t) => {
    const b0 = bt(t, lt, 0), b1 = bt(t, lt, 1), bb = bpOf(t);
    setLight({ rim: EP.yellow, rimK: .6 });
    bgGrad([[0, '#2A0A6A'], [1, '#8A1FB8']]); rays(1480, 520, 24, 'rgb(255 230 90 / .1)', t * .3);
    const bx = 110, bwid = 1120;
    gloss(pfRR(bx - 20, 150, bwid + 40, 700, 30), '#1A0840', { box: [bx - 20, 150, bwid + 40, 700], rim: EP.yellow, lw: 6, spec: .3 });
    chromeText('HIT-PARADE', bx + bwid / 2 - 150, 210, 76, { style: 'gold', italic: .14, depth: 8 });
    pixText('US APP STORE', bx + bwid - 330, 196, 4.4, EP.cyan, { glow: true });
    const swap = easeOut(clamp((lt - b0 + .05) / .3));
    const rows = [['GEMINI', '"Nano Banana"', 1 - swap, true], ['CHATGPT', '"Research Preview"', swap, false], ['EVERYTHING ELSE', '"Ten Blue Links"', 2, false]];
    rows.forEach(([ttl, sub, pos, isB]) => {
      const y = 290 + pos * 170, x = bx;
      gloss(pfRR(x, y, bwid, 146, 22), isB ? '#FFF6B0' : '#3A2A7A', { box: [x, y, bwid, 146], lw: 4, rim: isB ? EP.yellow : EP.cyan, spec: .6 });
      glossBall(x + 76, y + 73, 56, 56, pos < .5 ? EP.gold : '#8A94B8', { lw: 4 }); ptext(String(Math.round(pos) + 1), x + 76, y + 73, 62, { fill: pos < .5 ? '#6A3A00' : '#1A1030' });
      txt(ttl, x + 160, y + 56, 58, isB ? '#1A0A40' : '#FFFFFF', { font: 'archivo', align: 'left', maxW: 700 });
      txt(sub, x + 160, y + 110, 32, isB ? '#8A6A0A' : '#B8B0E8', { font: 'archivo', align: 'left' });
      if (isB) { ctx.fillStyle = EP.laser; poly([[x + bwid - 90, y + 90], [x + bwid - 40, y + 90], [x + bwid - 65, y + 50]]); ctx.fill(); }
      else if (ttl === 'CHATGPT' && swap > .5) { ctx.fillStyle = EP.red; poly([[x + bwid - 90, y + 56], [x + bwid - 40, y + 56], [x + bwid - 65, y + 96]]); ctx.fill(); }
    });
    // the banana
    const k1 = clamp((lt - b1) / .15);
    ctx.save(); ctx.translate(1560, 400); ctx.rotate(t * 1.5); poly(starPts(0, 0, 150, .5, 5)); ctx.fillStyle = lg(0, -150, 0, 150, [[0, '#FFFFFF'], [.5, EP.yellow], [1, EP.orange]]); ctx.fill(); ctx.strokeStyle = EP.line; ctx.lineWidth = 6; ctx.stroke(); ctx.restore();
    ptext('#1', 1560, 404, 90, { fill: EP.red, strokes: [['#FFFFFF', 12]] });
    banana(1560, 760, 60, t);
    if (k1 > 0 && lt < b1 + .3) glint(1640, 250, 160 * (1 - (lt - b1) / .3), 1);
    if (lt < .1) cutFX('rgb');
  });

  // =====================================================================================================
  // V2.11 Billion-five: Anthropic's prize — a one-armed bandit: a sweating DJ CLAWD pulls the lever, the reels land on three books, JACKPOT
  // $1,500,000,000, and the books pour out to a crowd of AUTHORS. Small print: ABOUT $3,000 PER BOOK.
  function bookIcon(x, y, s, col) { ctx.save(); ctx.translate(x, y); gloss(pfRR(-s * .42, -s * .55, s * .84, s * 1.1, s * .06), col, { box: [-s * .42, -s * .55, s * .84, s * 1.1], lw: Math.max(2, s * .04), rim: null, spec: .7 }); ctx.fillStyle = '#FFF8E0'; ctx.fillRect(-s * .42, s * .42, s * .84, s * .1); ctx.fillStyle = 'rgb(255 255 255 / .6)'; ctx.fillRect(-s * .25, -s * .3, s * .5, s * .08); ctx.fillRect(-s * .25, -s * .15, s * .38, s * .06); ctx.restore(); }
  line('V2', 11, (p, lt, d, t) => {
    const b0 = bt(t, lt, 0), b1 = bt(t, lt, 1), b2 = bt(t, lt, 2), bb = bpOf(t);
    setLight({ rim: EP.gold, rimK: .7 });
    bgGrad([[0, '#3A0008'], [1, '#8A0A1A']]);
    for (let i = 0; i < 40; i++) { const a = i / 40 * TAU, on = (i + Math.floor(t * 12)) % 3 === 0; ell(760 + Math.cos(a) * 560, 480 + Math.sin(a) * 380, 12, 12); ctx.fillStyle = on ? EP.yellow : '#6A3A10'; ctx.fill(); if (on) glow(760 + Math.cos(a) * 560, 480 + Math.sin(a) * 380, 30, EP.yellow, .6); }
    // the machine
    const mx = 760;
    gloss(pfRR(mx - 400, 190, 800, 700, 60), '#C8C8D8', { box: [mx - 400, 190, 800, 700], lw: 6, rim: EP.gold, spec: .9 });
    gloss(pfRR(mx - 360, 220, 720, 120, 30), '#E8202A', { box: [mx - 360, 220, 720, 120], lw: 4, rim: null });
    const jack = lt >= b1;
    chromeText(jack ? 'JACKPOT!' : 'SETTLEMENT', mx, 280, 80, { style: jack ? 'gold' : 'silver', italic: .1, depth: 8, s: jack ? 1 + kick(t, 6) * .06 : 1 });
    rrect(mx - 330, 380, 660, 250, 16); paint('#FFFFFF', EP.line, 5);
    for (let r = 0; r < 3; r++) {
      const stop = b0 + r * .12 + (b1 - b0) * .6, x = mx - 220 + r * 220, spinning = lt < stop;
      ctx.save(); ctx.beginPath(); ctx.rect(x - 100, 385, 200, 240); ctx.clip();
      if (spinning) { const off = (lt * 2600) % 120; for (let q = -1; q < 4; q++) { const y = 390 + q * 120 + off; ['🍒', '7', 'BAR'][((q + r) % 3 + 3) % 3] === '7' ? ptext('7', x, y, 110, { fill: EP.red, strokes: [[EP.line, 6]] }) : bookIcon(x, y, 90, [EP.blue, EP.red, EP.laser][(q + r + 3) % 3]); } ctx.fillStyle = 'rgb(255 255 255 / .35)'; ctx.fillRect(x - 100, 385, 200, 240); }
      else { const b = backOut(clamp((lt - stop) / .12), 2); bookIcon(x, 505 - (1 - b) * 40, 150, [EP.red, EP.blue, '#2AA84A'][r]); }
      ctx.restore();
      ctx.strokeStyle = EP.line; ctx.lineWidth = 4; ctx.beginPath(); ctx.moveTo(x + 110, 385); ctx.lineTo(x + 110, 625); ctx.stroke();
    }
    ctx.fillStyle = '#05050A'; rrect(mx - 330, 660, 660, 90, 10); ctx.fill();
    pixText(jack ? '$' + money(1.5e9 * clamp((lt - b1) / .5)) : 'PULL TO SETTLE', mx, 684, 6.5, jack ? EP.laser : EP.amber, { align: 'center', glow: true });
    txt('ABOUT $3,000 PER BOOK · ~500,000 BOOKS', mx, 800, 30, '#1A0F28', { font: 'archivo' });
    // the lever and DJ CLAWD
    // DJ CLAWD hangs off the lever by one nub; his weight pulls it down on the beat
    const pull = easeIn(clamp((lt + .05) / (b0 + .05)));
    const la = lerp(-.25, 1.15, pull), lx = mx + 410, ly = 560, L = 250, gx = lx + Math.sin(la) * L, gy = ly - Math.cos(la) * L, u = 30;
    ctx.save(); ctx.translate(lx, ly); ctx.rotate(la); ctx.strokeStyle = '#8A90A8'; ctx.lineWidth = 18; ctx.lineCap = 'round'; ctx.beginPath(); ctx.moveTo(0, 0); ctx.lineTo(0, -L); ctx.stroke(); ctx.restore();
    gloss(pfRR(lx - 30, ly - 40, 60, 80, 14), '#8A90A8', { box: [lx - 30, ly - 40, 60, 80], lw: 4, rim: null });
    const hang = lt > b1 + .25 ? easeIn(clamp((lt - b1 - .25) / .3)) : 0;
    djClawd(gx + 5.44 * u, gy + 7.04 * u + hang * 300, u, { aL: 1.3, aR: .5 + Math.sin(t * 20) * .2, eyes: jack ? 'wide' : 'closed', mouth: jack ? 'O' : 'grin', sweat: 1, phones: false, blush: .4, shadow: false, walk: t * 3, rot: Math.sin(t * 6) * .04 });
    glossBall(gx, gy, 40, 40, EP.red, { lw: 4 });
    nameTip('ANTHROPIC', 1560, 250, { pop: pop(lt, .08), size: 28, sub: 'BARTZ v. ANTHROPIC' });
    // books pour out to the authors
    if (jack) for (let i = 0; i < 18; i++) { const a = (lt - b1) * 1.4 - i * .05; if (a < 0) continue; const u = frac(a), x = mx - 120 + i % 5 * 60 + u * (i % 2 ? 380 : -420), y = 760 + u * 150 - Math.sin(u * Math.PI) * 220; ctx.save(); ctx.translate(x, y); ctx.rotate(u * 6 + i); bookIcon(0, 0, 50, [EP.red, EP.blue, '#2AA84A', EP.amber][i % 4]); ctx.restore(); }
    raveCrowd(t, { y: 1080, s: 1.2, rows: 1, n: 11, k: jack ? 1 : .4, hands: jack ? 1 : .2, sticks: 0, rim: EP.gold });
    if (lt > b2) ptext('AUTHORS', 380, 930, 56, { fill: EP.yellow, strokes: [[EP.line, 10]], rot: -.05 });
    if (lt < .1) cutFX('zoom');
  });

  // =====================================================================================================
  // V2.12 Yudkowsky drops "Everyone Dies" — the drop: the book falls from the sky onto the dance floor with the bass drop; sub-bass rings
  // shake everything; NYT BESTSELLER lands; ELIEZER drops the mic.
  line('V2', 12, (p, lt, d, t) => {
    const b0 = bt(t, lt, 0), b1 = bt(t, lt, 1), b2 = bt(t, lt, 2), land = clamp((lt - b0 + .12) / .12), sh = shakeAt(t, lt, b0, .5, 28);
    setLight({ rim: EP.red, rimK: .8 });
    camBegin(W / 2 - sh[0], H / 2 - sh[1], 1);
    fillAll('#05020A');
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; for (const [x, c] of [[400, EP.red], [W / 2, '#FFFFFF'], [1520, EP.red]]) { ctx.fillStyle = lg(0, 0, 0, 900, [[0, alpha(c, lt > b0 ? .25 : .08)], [1, alpha(c, 0)]]); poly([[x - 40, -20], [x + 40, -20], [x + 300, 900], [x - 300, 900]]); ctx.fill(); } ctx.restore();
    ctx.save(); ctx.beginPath(); ctx.rect(-900, 760, W + 1800, H); ctx.clip(); fillAll('#0A0618'); ctx.strokeStyle = alpha(EP.red, .6); ctx.lineWidth = 3; ctx.beginPath(); for (let i = -20; i <= 20; i++) { ctx.moveTo(W / 2 + i * 70, 760); ctx.lineTo(W / 2 + i * 380, H + 300); } for (let j = 0; j < 8; j++) { const y = 760 + (H - 760) * ((j + .5) / 8) ** 1.7; ctx.moveTo(-900, y); ctx.lineTo(W + 900, y); } ctx.stroke(); ctx.restore();
    // sub-bass rings
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; for (let k = 0; k < 4; k++) { const a = lt - bt(t, lt, k); if (a < 0 || a > 1) continue; ctx.strokeStyle = `rgb(255 60 80 / ${.7 * (1 - a)})`; ctx.lineWidth = 20 * (1 - a) + 3; ell(1000, 800, 120 + a * 1300, 40 + a * 380); ctx.stroke(); } ctx.restore();
    // the book
    const by = lerp(-700, 800, easeIn(land)), sq = land >= 1 ? Math.max(0, 1 - (lt - b0) / .15) * .12 : 0;
    ctx.save(); ctx.translate(1000, by); ctx.scale(1 + sq, 1 - sq); ctx.rotate(land < 1 ? (1 - land) * .4 : -.03);
    gloss(pfRR(-300, -40, 600, 40, 6), '#F2EEE0', { box: [-300, -40, 600, 40], lw: 5, rim: null });
    gloss(pfRR(-320, -560, 640, 530, 10), '#0C0C10', { box: [-320, -560, 640, 530], lw: 6, rim: EP.red, spec: .5 });
    ptext('IF ANYONE', 0, -470, 76, { font: 'anton', fill: '#FFFFFF', spacing: 3 }); ptext('BUILDS IT,', 0, -385, 76, { font: 'anton', fill: '#FFFFFF', spacing: 3 });
    ptext('EVERYONE', 0, -278, 100, { font: 'anton', fill: EP.red, spacing: 3 }); ptext('DIES', 0, -170, 110, { font: 'anton', fill: EP.red, spacing: 6 });
    txt('YUDKOWSKY & SOARES', 0, -78, 34, '#C8C8D0', { font: 'archivo', spacing: 3 });
    ctx.restore();
    if (land >= 1 && lt < b0 + .4) { const a = (lt - b0) / .4; ctx.fillStyle = `rgb(200 200 220 / ${.5 * (1 - a)})`; for (let i = 0; i < 10; i++) { ell(1000 + (i - 4.5) * 90 * (1 + a), 790 - a * 50 - hash(i) * 30, 40 + a * 40, 22); ctx.fill(); } }
    // Eliezer's mic drop
    const drop = lt >= b2 - .05, md = clamp((lt - b2 + .05) / .35);
    toy(360, 1000, 52, { ...WHO.eliezer.o, hR: drop ? [2.4, -8.2] : [1.1, -6.25], gR: drop ? 'open' : 'mic', mouth: drop ? 'smirk' : 'open', eyes: drop ? 'closed' : 'dot', turn: .25, hL: [-2.4, -4.2], lean: drop ? -.04 : 0 });
    if (drop) { const mx = 360 + 2.4 * 52, my = 1000 - 8.2 * 52 + easeIn(md) * 420; ctx.save(); ctx.translate(mx, my); ctx.rotate(md * 2.5); gloss(pfRR(-10, 0, 20, 90, 8), '#2A2A34', { box: [-10, 0, 20, 90], lw: 3, rim: null }); glossBall(0, -8, 26, 26, '#8A90A8', { lw: 3 }); ctx.restore(); if (md >= 1) ptext('*THUD*', 480, 900, 40, { fill: '#FFFFFF', strokes: [[EP.line, 8]] }); }
    camEnd();
    slamStamp('NYT BESTSELLER', 1330, 250, 56, EP.gold, .12, clamp((lt - b1) / .12));
    nameTip(WHO.eliezer.name, 360, 330, { pop: pop(lt, .08), size: 28, to: [360, 420] });
    if (lt > b0 - .02 && lt < b0 + .08) { fx({ invert: lt < b0 + .03, zoom: .6 }); }
    if (lt < .1) cutFX('none');
  });

  // =====================================================================================================
  // V2.13 "Clanker!" spat in every screed — the date rolls back to summer. A 90s chat room scrolls CLANKER!!! in every line, while a little
  // delivery robot on the sidewalk reads it and its screen face goes sad.
  line('V2', 13, (p, lt, d, t) => {
    const b1 = bt(t, lt, 1), b2 = bt(t, lt, 2), sad = lt > b1, bb = bpOf(t);
    setLight({ rim: '#FFFFFF', rimK: .35 });
    bgGrad([[0, '#6ABAFF'], [.7, '#C8E8FF'], [1, '#E8F4FF']], { y1: 700 });
    for (let i = 0; i < 7; i++) { const x = i * 300 - 60, h = 260 + hash(i + 90) * 220; ctx.fillStyle = ['#E8C8A8', '#C8B8D8', '#F0D8B0'][i % 3]; ctx.fillRect(x, 700 - h, 260, h); ctx.fillStyle = 'rgb(80 120 180 / .5)'; for (let q = 0; q < 8; q++) ctx.fillRect(x + 30 + (q % 4) * 55, 700 - h + 40 + Math.floor(q / 4) * 90, 36, 56); }
    ctx.fillStyle = '#B8B4C0'; ctx.fillRect(-10, 700, W + 20, 400); ctx.fillStyle = '#9A96A6'; for (let i = 0; i < 12; i++) ctx.fillRect(i * 180 - (lt * 60) % 180, 700, 6, 400);
    // the chat room
    const names = ['xX_h8r_Xx', 'skater94', 'dial_up_dad', 'grrrl_power', 'NoBots4Me', 'cooldude77', 'tamagotchi_mom', 'b1ff'];
    const shouts = ['CLANKER!!!', 'clanker lol', 'CLANKERS!!! EVERYWHERE', 'go home clanker', 'CLANKER', 'clank clank clank', 'CLANKER!!!!!', 'ok clanker'];
    win98Window(80, 150, 1000, 700, '#general - Chat 98', (cw, ch) => {
      ctx.fillStyle = '#FFFFFF'; ctx.fillRect(0, 0, cw, ch);
      const scroll = lt * 7.5, first = Math.floor(scroll);
      for (let i = 0; i < 12; i++) { const n = first + i, yy = 30 + i * 54 - frac(scroll) * 54; if (yy > ch - 20) continue; const nm = names[(n * 3) % 8], msg = shouts[(n * 5) % 8]; txt('<' + nm + '>', 20, yy, 32, ['#C00000', '#0000C0', '#008000', '#8000C0'][n % 4], { font: 'courier', align: 'left' }); txt(msg, 34 + textW('<' + nm + '> ', 32, 'courier'), yy, 32, '#000', { font: 'courier', align: 'left' }); }
    }, { icon: 'globe', menu: ['File', 'Room', 'Help'] });
    // the delivery robot
    const rx = 1500, ry = 900, rol = Math.sin(t * 8) * 3;
    for (const dx of [-120, 0, 120]) { ell(rx + dx, ry + 20, 38, 38); paint('#2A2A34', EP.line, 4); ell(rx + dx, ry + 20, 14, 14); paint('#8A90A8'); }
    gloss(pfRR(rx - 180, ry - 230 + rol, 360, 240, 40), '#F4F4FA', { box: [rx - 180, ry - 230, 360, 240], lw: 5, rim: EP.cyan, spec: .8 });
    rrect(rx - 120, ry - 200 + rol, 240, 130, 20); paint('#15303A', EP.line, 4);
    ctx.save(); ctx.translate(rx, ry - 135 + rol); ctx.scale(30, 30); ctx.translate(0, 6.05); _lcdFace(sad ? 'cry' : 'happy', sad ? 'wavy' : 'grin', '#AFFFF0', {}); ctx.restore();
    ctx.strokeStyle = '#8A90A8'; ctx.lineWidth = 6; ctx.beginPath(); ctx.moveTo(rx + 140, ry - 220 + rol); ctx.lineTo(rx + 160, ry - 420); ctx.stroke(); poly([[rx + 160, ry - 420], [rx + 250, ry - 395], [rx + 160, ry - 370]]); paint(EP.orange, EP.line, 3);
    if (sad) ptext('beep…', rx - 220, ry - 300, 44, { fill: '#FFFFFF', strokes: [[EP.line, 8]], alpha: clamp((lt - b1) / .15) });
    if (lt > b2) for (let i = 0; i < 3; i++) { const a = frac((lt - b2) * 1.5 + i / 3); ptext('CLANKER!', 1180 + i * 90, 560 - a * 200, 40, { fill: EP.red, strokes: [['#FFFFFF', 8]], alpha: 1 - a, rot: -.15 + i * .1 }); }
    if (lt < .1) cutFX('rgb');
  });

  // =====================================================================================================
  // V2.14 Sora slop in every feed — a 3×3 wall of CRTs, every channel showing grape-coloured SORA slop (a cat on a skateboard, a melting face,
  // a dog flying a jet…); the slop pours out of the wall into a pig trough labelled FEED, filling up on the beats.
  function slopTile(i, w, h, t) {
    bgGrad([[0, ['#3A1A6A', '#6A2A9A', '#2A1A5A'][i % 3]], [1, ['#8A4BE0', '#C88AFF', '#5A2AB0'][i % 3]]], { y1: h });
    ctx.save(); ctx.translate(w / 2, h / 2 + 4); ctx.scale(1.45, 1.45);
    const k = t * 2 + i;
    switch (i % 9) {
      case 0: ctx.translate(Math.sin(k) * 40, 0); rrect(-50, 20, 100, 12, 6); paint('#E8C050', EP.line, 2); glossBall(-30, 42, 9, 9, '#333333', { line: false, rim: null }); glossBall(30, 42, 9, 9, '#333333', { line: false, rim: null }); glossBall(0, -5, 34, 26, '#F0A040', { lw: 2, rim: null }); poly([[-26, -26], [-16, -48], [-6, -28]]); paint('#F0A040', EP.line, 2); poly([[26, -26], [16, -48], [6, -28]]); paint('#F0A040', EP.line, 2); break;
      case 1: glossBall(0, 0 + Math.sin(k) * 4, 44, 44 + Math.sin(k) * 6, '#FFD84A', { lw: 3, rim: null }); ctx.fillStyle = '#FFD84A'; for (let q = 0; q < 4; q++) { ctx.fillRect(-30 + q * 20, 30, 12, 20 + frac(k * .3 + q * .3) * 30); } ctx.fillStyle = '#1A0F28'; ell(-14, -6, 5, 9); ctx.fill(); ell(16, -2, 5, 11); ctx.fill(); break;
      case 2: ctx.rotate(Math.sin(k) * .2); poly([[-60, 0], [40, -10], [60, 0], [40, 10]]); paint('#C8CCD8', EP.line, 2); poly([[-10, -4], [-30, -40], [0, -6]]); paint('#C8CCD8', EP.line, 2); glossBall(20, -16, 16, 14, '#C88A4A', { lw: 2, rim: null }); break;
      case 3: for (let q = 0; q < 5; q++) glossBall(-60 + q * 30, Math.sin(k + q) * 20, 16, 16, ['#FF5AA8', '#5AE8FF', '#FFE01F'][q % 3], { line: false, rim: null }); break;
      case 4: ptext('HANDS?', 0, 0, 34, { fill: '#FFFFFF', strokes: [[EP.line, 6]], rot: Math.sin(k) * .2 }); for (let q = 0; q < 7; q++) { ctx.fillStyle = '#F5C6A2'; ctx.fillRect(-60 + q * 18, 26, 12, 30); } break;
      case 5: glossBall(0, 0, 40, 40, '#FFFFFF', { lw: 2, rim: null }); ptext('?', 0, 2, 50, { fill: EP.magenta }); break;
      case 6: poly([[0, -50], [44, 30], [-44, 30]]); paint('#5AE8A0', EP.line, 2); glossBall(0, -10 + Math.sin(k * 2) * 10, 14, 14, '#FFFFFF', { lw: 2, rim: null }); break;
      case 7: for (let q = 0; q < 3; q++) glossBall(-40 + q * 40, Math.cos(k + q) * 10, 22, 30, '#F0A040', { lw: 2, rim: null }); break;
      default: ptext('SLOP', 0, 0, 40, { fill: '#FFE01F', strokes: [[EP.line, 6]], rot: Math.sin(k) * .15 });
    }
    ctx.restore();
    ptext('SORA', w - 44, h - 20, 18, { fill: 'rgb(255 255 255 / .8)' });
  }
  line('V2', 14, (p, lt, d, t) => {
    const B = [0, 1, 2, 3].map(k => bt(t, lt, k)), fill = clamp((lt + .1) / (d - .2)), bb = bpOf(t);
    setLight({ rim: EP.pink, rimK: .6 });
    bgGrad([[0, '#12042A'], [1, '#3A0A5A']]);
    const cw = 400, ch = 190, x0 = W / 2 - (cw * 3 + 20) / 2 - 140, y0 = 150;
    videoWall(x0, y0, 3, 3, cw, ch, (i, j, w, h) => slopTile(j * 3 + i, w, h, t), { frame: '#2A1A40' });
    // slop drips down out of the wall
    ctx.fillStyle = '#8A4BE0';
    for (let i = 0; i < 9; i++) { const x = x0 + 60 + i * 140, L = 40 + (Math.sin(t * 3 + i) * .5 + .5) * 60 + fill * 120; rrect(x, y0 + 3 * (ch + 10) - 8, 28, L, 14); ctx.fill(); }
    // the trough
    const tx = x0 + (cw * 3 + 20) / 2, ty = 930, tw = 900;
    gloss(pfPts([[tx - tw / 2, ty - 160], [tx + tw / 2, ty - 160], [tx + tw / 2 - 60, ty], [tx - tw / 2 + 60, ty]]), '#8A5A2A', { box: [tx - tw / 2, ty - 160, tw, 160], lw: 5, rim: EP.pink, spec: .5 });
    ctx.save(); poly([[tx - tw / 2 + 12, ty - 150], [tx + tw / 2 - 12, ty - 150], [tx + tw / 2 - 66, ty - 10], [tx - tw / 2 + 66, ty - 10]]); ctx.clip();
    const lvl = ty - 10 - fill * 140; ctx.fillStyle = lg(0, lvl, 0, ty, [[0, '#C88AFF'], [1, '#6A2AB0']]); ctx.beginPath(); ctx.moveTo(tx - tw, ty + 10); for (let x = tx - tw / 2; x <= tx + tw / 2; x += 30) ctx.lineTo(x, lvl + Math.sin(x * .03 + t * 5) * 8); ctx.lineTo(tx + tw, ty + 10); ctx.closePath(); ctx.fill();
    for (let i = 0; i < 6; i++) { const bx = tx - 300 + i * 120, by = lvl + 10 + Math.sin(t * 3 + i) * 5; ell(bx, by, 14, 10); ctx.strokeStyle = '#E8C8FF'; ctx.lineWidth = 3; ctx.stroke(); }
    ctx.restore();
    ptext('FEED', tx, ty - 80, 90, { font: 'anton', fill: '#FFE8C0', strokes: [['#4A2A0A', 10]], spacing: 6 });
    B.forEach((b, i) => { if (lt > b && lt < b + .2) { const a = (lt - b) / .2; ell(tx - 300 + i * 200, ty - 150 - a * 60, 30 * (1 - a) + 6, 20 * (1 - a) + 4); ctx.fillStyle = '#C88AFF'; ctx.fill(); } });
    // SORA ladles
    gumdrop(1680, 930, 30, { col: CANDY.grape, label: 'SORA', face: 'happy', mouth: 'grin', hL: [-4.6, -7 + Math.sin(bb * Math.PI) * 1.5], gL: 'fist', holdL: s => { ctx.strokeStyle = '#C8CCD8'; ctx.lineWidth = 10; ctx.lineCap = 'round'; ctx.beginPath(); ctx.moveTo(0, 0); ctx.lineTo(-120, 120); ctx.stroke(); ell(-140, 140, 40, 24); paint('#C8CCD8', EP.line, 3); ell(-140, 134, 30, 14); paint('#8A4BE0'); }, jump: Math.abs(Math.sin(bb * Math.PI)) * .3 });
    nameTip('SORA 2 · THE SORA APP', 1680, 480, { pop: pop(lt, .08), size: 28, to: [1680, 600] });
    if (lt < .1) cutFX('flash');
  });

  // =====================================================================================================
  // V2.15 Yann LeCun quits Meta's stage — the boy-band breakup: scissors cut YANN out of the band photo, and he walks off stage with a glossy
  // globe under his arm and his solo CD, WORLD MODELS.
  function globe(x, y, r, t) { glossBall(x, y, r, r, '#2A7AE8', { lw: 4, rim: EP.cyan }); ctx.save(); ell(x, y, r, r); ctx.clip(); ctx.fillStyle = '#3ACA5A'; for (let i = 0; i < 5; i++) { const a = t * .8 + i * 1.3, cx = x + Math.sin(a) * r * .8; if (Math.cos(a) < 0) continue; ell(cx, y + (hash(i) - .5) * r * 1.2, r * .28 * Math.cos(a), r * .22); ctx.fill(); } ctx.restore(); ctx.strokeStyle = 'rgb(255 255 255 / .4)'; ctx.lineWidth = 2; ell(x, y, r * .45, r); ctx.stroke(); }
  line('V2', 15, (p, lt, d, t) => {
    const b0 = bt(t, lt, 0), b1 = bt(t, lt, 1), cut = clamp((lt - b0 + .1) / .3), bb = bpOf(t);
    setLight({ rim: '#FFFFFF', rimK: .45 });
    bgGrad([[0, '#FF5AB8'], [1, '#FFB0E0']]);
    for (let j = 0; j < 8; j++) for (let i = 0; i < 14; i++) { poly(starPts(i * 150 + (j % 2) * 75, j * 150, 16, .45, 5)); ctx.fillStyle = 'rgb(255 255 255 / .25)'; ctx.fill(); }
    // the band photo
    ctx.save(); ctx.translate(560, 500); ctx.rotate(-.05);
    ctx.fillStyle = 'rgb(0 0 0 / .3)'; ctx.fillRect(-400, -300, 820, 620);
    ctx.fillStyle = '#FFFFFF'; ctx.fillRect(-410, -310, 820, 620);
    ctx.save(); ctx.beginPath(); ctx.rect(-380, -280, 760, 500); ctx.clip();
    bgGrad([[0, '#12C8E8'], [1, '#1A6AE8']], { y0: -280, y1: 220 });
    const band = [[-270, 0, 'short', THAIR.blond], [-90, 2, 'spiky', THAIR.black], [270, 1, 'swoop', THAIR.red]];
    band.forEach(([x, sk, hr, hc], i) => toy(x, 300, 34, { skin: sk, hair: hr, hairCol: hc, top: 'tee', topCol: ['#FFFFFF', '#1A1A24', '#E8202A'][i], mouth: cut > .5 ? 'O' : 'grin', eyes: cut > .5 ? 'wide' : 'happy', shadow: false, hL: [-2.4, -4], hR: [2.4, -4] }));
    if (cut < .02) toy(90, 300, 34, { ...WHO.yann.o, mouth: 'smile', shadow: false });
    else { ctx.fillStyle = '#FFFFFF'; ctx.beginPath(); ctx.ellipse(90, 300 - 8.35 * 34, 2.3 * 34, 2.3 * 34, 0, 0, TAU); ctx.rect(90 - 1.8 * 34, 300 - 6.5 * 34, 3.6 * 34, 6.5 * 34); ctx.fill(); ctx.strokeStyle = EP.line; ctx.lineWidth = 3; ctx.setLineDash([12, 8]); ctx.stroke(); ctx.setLineDash([]); }
    ctx.restore();
    chromeText('META BOYZ', 0, 262, 60, { style: 'purple', italic: .1, depth: 6 });
    ctx.restore();
    // the scissors, snipping round him
    if (cut > 0 && cut < 1) { const a = cut * TAU, sx = 560 + 90 + Math.cos(a) * 110, sy = 500 + 20 + Math.sin(a) * 180, op = Math.abs(Math.sin(lt * 40)) * .4; ctx.save(); ctx.translate(sx, sy); ctx.rotate(a + Math.PI / 2); for (const sd of [-1, 1]) { ctx.save(); ctx.rotate(sd * op); ctx.strokeStyle = '#C8CCD8'; ctx.lineWidth = 10; ctx.beginPath(); ctx.moveTo(0, 0); ctx.lineTo(0, -90); ctx.stroke(); ctx.strokeStyle = EP.red; ctx.lineWidth = 12; ell(sd * 12, 40, 18, 24); ctx.stroke(); ctx.restore(); } ctx.restore(); }
    // Yann walks off, globe and CD
    const walk = clamp((lt - b0) / (d - b0)), yx = lerp(1300, 1700, walk), wb = Math.abs(Math.sin(bb * Math.PI * 1));
    ctx.fillStyle = '#2A1030'; ctx.fillRect(1100, 960, 900, 30);
    toy(yx, 980, 50, { ...WHO.yann.o, mouth: 'smile', eyes: 'happy', turn: .45, fL: [Math.sin(bb * Math.PI) * .5, -Math.max(0, Math.sin(bb * Math.PI)) * .5], fR: [-Math.sin(bb * Math.PI) * .5, -Math.max(0, -Math.sin(bb * Math.PI)) * .5], hL: [-2.2, -5], hR: [2.5, -7.4], gR: 'open', bob: wb * .4, hold: s => cdDisc(30, -20, 70, T * 3, { label: 'WORLD MODELS', col: '#FFE8F4' }) });
    globe(yx - 2.5 * 50, 980 - 5.2 * 50, 70, t);
    if (lt > b1) { ptext('SOLO DEBUT:', 1450, 350, 40, { fill: '#FFFFFF', strokes: [[EP.line, 8]] }); chromeText('WORLD MODELS', 1450, 420, 64, { style: 'ice', italic: .1, depth: 8, s: lerp(1.4, 1, easeOut(clamp((lt - b1) / .15))) }); }
    nameTip(WHO.yann.name, 1450, 230, { pop: pop(lt, .08), size: 28, sub: 'LEAVING META AFTER 12 YEARS', to: [yx - 40, 300] });
    if (lt < .1) cutFX('zoom');
  });

  // =====================================================================================================
  // V2.16 "Bubble!" screams the business page — sunset, the foam-party bubble machine blows a giant iridescent bubble full of GPUs and $ over
  // the crowd; the classic spinning newspaper lands: BUBBLE?! A pin creeps toward it… cut before it pops (C2 is the foam party).
  line('V2', 16, (p, lt, d, t) => {
    const b0 = bt(t, lt, 0), b1 = bt(t, lt, 1), grow = easeOut(clamp((lt + .2) / 1.2)), bb = bpOf(t);
    setLight({ rim: EP.yellow, rimK: .6 });
    bgGrad([[0, '#3A0A5A'], [.45, '#FF3A6A'], [.75, '#FF8A3A'], [1, '#FFD06A']], { y1: 820 });
    glow(W / 2, 800, 600, '#FFD06A', .6); ell(W / 2, 820, 220, 220); ctx.fillStyle = lg(0, 600, 0, 820, [[0, '#FFF4B0'], [1, '#FF7A4A']]); ctx.fill();
    ctx.fillStyle = '#2A0A30'; ctx.fillRect(-10, 820, W + 20, 300);
    for (const [x, sc] of [[140, 1], [1790, -1]]) { ctx.save(); ctx.translate(x, 830); ctx.scale(sc, 1); ctx.strokeStyle = '#1A0620'; ctx.lineWidth = 22; ctx.beginPath(); ctx.moveTo(0, 0); ctx.quadraticCurveTo(30, -250, 90, -420); ctx.stroke(); for (let i = 0; i < 6; i++) { const a = -Math.PI / 2 + (i - 2.5) * .5 + Math.sin(t * 2 + i) * .05; ctx.fillStyle = '#1A0620'; ctx.beginPath(); ctx.ellipse(90 + Math.cos(a) * 110, -420 + Math.sin(a) * 60, 120, 22, a, 0, TAU); ctx.fill(); } ctx.restore(); }
    // the bubble machine
    gloss(pfRR(180, 700, 260, 170, 30), '#FF5AB8', { box: [180, 700, 260, 170], lw: 5, rim: EP.cyan, spec: .9 });
    ell(410, 760, 44, 44); paint('#2A2A34', EP.line, 4); txt('BUBBLES', 300, 830, 30, '#FFFFFF', { font: 'archivo' });
    for (let i = 0; i < 10; i++) { const a = frac(t * .5 + i / 10), bx = 420 + a * 900 + Math.sin(t * 3 + i) * 30, by = 740 - a * 600 - hash(i) * 100, r = 16 + hash(i + 3) * 26; ell(bx, by, r, r); ctx.strokeStyle = `rgb(255 255 255 / ${.6 * (1 - a)})`; ctx.lineWidth = 3; ctx.stroke(); }
    // the giant bubble
    const cx = lerp(560, 1060, grow), cy = lerp(700, 440, grow), R = lerp(60, 330, grow) * (1 + Math.sin(t * 5) * .015);
    ctx.save(); ell(cx, cy, R, R); ctx.clip();
    for (let i = 0; i < 4; i++) { ctx.save(); ctx.translate(cx + Math.cos(t * .8 + i * 1.6) * R * .45, cy + Math.sin(t * .8 + i * 1.6) * R * .4); ctx.rotate(Math.sin(t + i) * .3); gpuBox(0, R * .18, R * .42, {}); ctx.restore(); }
    for (let i = 0; i < 6; i++) ptext('$', cx + Math.cos(t * 1.1 + i) * R * .7, cy + Math.sin(t * 1.3 + i * 2) * R * .65, R * .22, { fill: '#3AE85A', strokes: [[EP.line, 5]] });
    ctx.restore();
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; ell(cx, cy, R, R); ctx.fillStyle = rg(cx, cy, R * .6, R, [[0, 'rgb(255 255 255 / 0)'], [.7, 'rgb(120 200 255 / .12)'], [.85, 'rgb(255 120 220 / .25)'], [1, 'rgb(255 255 160 / .45)']]); ctx.fill(); ctx.restore();
    ell(cx, cy, R, R); ctx.strokeStyle = 'rgb(255 255 255 / .8)'; ctx.lineWidth = 4; ctx.stroke();
    ctx.fillStyle = 'rgb(255 255 255 / .7)'; ell(cx - R * .45, cy - R * .5, R * .22, R * .1, -.7); ctx.fill();
    // the crowd
    raveCrowd(t, { y: 1080, s: 1.25, rows: 2, n: 12, k: 1, hands: .8, sticks: .2, rim: EP.orange, cols: [EP.yellow, EP.pink, EP.cyan] });
    // MC TOKEN points up at it
    toy(560, 1010, 40, { ...CAST.token.o, mic: 'L', ...tok(t), hR: [3.2, -10.6], gR: 'point', lean: -.04, turn: .3, bob: kick(t, 6) * .4, mouth: 'grin' });
    // the pin, creeping in
    const pk = clamp((lt - b1) / (d - b1)), pinX = lerp(W + 60, cx + R + 70, easeOut(pk)), pinY = cy - 30;
    ctx.save(); ctx.translate(pinX, pinY); ctx.rotate(Math.PI + .1); ctx.strokeStyle = '#C8CCD8'; ctx.lineWidth = 8; ctx.beginPath(); ctx.moveTo(0, 0); ctx.lineTo(160, 0); ctx.stroke(); glossBall(180, 0, 30, 30, EP.red, { lw: 4 }); ctx.restore();
    // the spinning newspaper
    const nk = clamp((lt - b0 + .15) / .35);
    if (nk > 0) {
      ctx.save(); ctx.translate(560, 330); ctx.rotate((1 - nk) * TAU * 1.5 - .08); ctx.scale(lerp(.05, 1, nk), lerp(.05, 1, nk));
      ctx.fillStyle = 'rgb(0 0 0 / .3)'; ctx.fillRect(-270, -190, 560, 400);
      ctx.fillStyle = '#F2EEE0'; ctx.fillRect(-280, -200, 560, 400); ctx.strokeStyle = EP.line; ctx.lineWidth = 4; ctx.strokeRect(-280, -200, 560, 400);
      txt('THE BUSINESS PAGE', 0, -160, 36, '#15121C', { font: 'abril' }); ctx.fillStyle = '#15121C'; ctx.fillRect(-250, -132, 500, 4);
      ptext('BUBBLE?!', 0, -50, 128, { font: 'anton', fill: '#15121C', spacing: 2 });
      txt('"elements of irrationality"', 0, 50, 30, '#333', { font: 'abril' });
      ctx.fillStyle = 'rgb(20 20 30 / .3)'; for (let i = 0; i < 4; i++) { ctx.fillRect(-250, 90 + i * 22, 230, 8); ctx.fillRect(20, 90 + i * 22, 230, 8); }
      ctx.restore();
    }
    if (lt < .1) cutFX('rgb');
  });
})();

;
// ---- styles/eurodance/ch/c05_chorus2.js ----
// c05_chorus2 — Chorus 2 (V2.16 → V3.1, 36 beats): the Ibiza foam party. Same chorus language as C1 (the hook in chrome word by word,
// training, the curve, the second hook, the shrug, the containment failure, a stutter tail), one venue bigger, and the foam rises through
// the whole chorus until it swallows the camera:
//   hook line      V2.16's bubble pops on the downbeat: a sunset beach, foam cannons fire, SOFTMAX on the lifeguard tower, the hook in chrome.
//   training       BEACH BOOTCAMP: MC TOKEN and SOFTMAX lead a class of candy computers doing jumping jacks in ankle-deep foam; the EPOCH
//                  board counts forever ("Time remaining: ALWAYS", the C1 callback).
//   curves         the swell: the sea rises as an exponential wave, a notch every beat (×1.6 a beat, steeper than C1's pipes), with a neon
//                  curve on its crest; SOFTMAX, MC TOKEN and a candy computer surf it higher every beat, off the top of the frame.
//   hook line 2    the party boat S.S. SCALING at dusk: DJ CLAWD scratches on deck, lasers into the sky, confetti cannons on SCALING.
//   preordain      foam up to everyone's chins: SOFTMAX wags "No", then every head in the foam shrugs, hands popping out.
//   contain it     the foam pit's barrier (MAX FOAM LEVEL): the cannons go into overdrive, FOAM.EXE's warning (the C1 dialog, again) is
//                  swallowed, the foam bursts over the barrier and floods the frame until it swallows the camera.
//   the tail       "Moat, moat, moat, moat…": out of the foam, the club's neon sign stutters MOLT… MOLT… on each hit (BOOK stays dark),
//                  into V3.1's MOLTBOOK door.
// The colour run: sunset magenta beach / golden-hour teal sea / dusk-blue wave with a lime curve / night-purple boat / foam white-pink /
// alert red and foam white / UV-purple neon.
(() => {
  const SPAN = span('C2'), B0 = bpOf(SPAN.start), LN = linesOf('C2');
  const rb = t => bpOf(t) - B0;
  const snap8 = x => onBeat(0, Math.round(bpOf(x) * 2) / 2);
  const wordT = (ln, i) => snap8(_karaTimes(ln).tm[i][0]);
  const pop = (t, t0, dur = .18) => t < t0 ? 0 : backOut(clamp((t - t0) / dur), 2.2);
  const CUT = {
    train: snap8(LN[1].start),                  // "It was always training,"
    curves: wordT(LN[1], 4),                     // "and the curves kept gaining,"
    hook2: snap8(LN[2].start),                   // "We didn't start the scaling"
    no: snap8(LN[3].start),                      // "No, we didn't preordain it,"
    contain: wordT(LN[3], 5),                    // "but we can't contain it!"
  };
  // the "Moat, moat, moat…" stutter hits (the stuttered "Molt-" of V3.1's Moltbook), straight from the alignment
  const MOLTS = (typeof KARAOKE_WORDS !== 'undefined' ? KARAOKE_WORDS : []).filter(w => w[0] >= LN[3].end - .05 && w[0] < SPAN.end && /^mo(a|l)t/i.test(w[2])).map(w => w[0]);

  // =====================================================================================================
  // THE CHORUS KIT (from c03_chorus1.js)
  // =====================================================================================================
  function hookWords(ln, t, o = {}) {
    const { words } = _karaTimes(ln), W1 = words.slice(0, 3), W2 = words.slice(3), cx = o.x ?? W / 2, gap = 34;
    const clean = w => w.replace(/[^A-Za-z']/g, '').toUpperCase();
    const row = (ws, off, size, y, styleOf) => {
      const labels = ws.map(clean), wd = labels.map(w => textW(w, size, 'archivo')), tot = wd.reduce((a, v) => a + v, 0) + gap * (ws.length - 1);
      let x = cx - tot / 2;
      labels.forEach((w, i) => {
        const at = wordT(ln, off + i), k = clamp((t - at) / .13);
        if (k > 0) {
          const last = off + i === words.length - 1, s = lerp(last ? 3 : 2.4, 1, backOut(k, last ? 1.5 : 1.2));
          chromeText(w, x + wd[i] / 2, y - (last ? kick(t, 7) * 5 : 0), size, { style: styleOf(i, last), italic: .14, depth: Math.round(size * .11), s, alpha: clamp(k * 3) * (o.alpha ?? 1) });
          if (last && t - at < .5) sweepGlint(x, x + wd[i], y - size * .2, (t - at - .1) / .4, size * .9);
        }
        x += wd[i] + gap;
      });
      return tot;
    };
    row(W1, 0, o.s1 ?? 118, o.y1 ?? 190, () => o.styles?.[0] ?? 'chrome');
    row(W2, 3, o.s2 ?? 170, o.y2 ?? 350, (i, last) => last ? (o.styles?.[2] ?? 'hot') : (o.styles?.[1] ?? 'gold'));
    return wordT(ln, words.length - 1);
  }
  function confetti(t, t0, n = 80, o = {}) {
    if (t < t0) return; const cols = o.cols ?? [EP.magenta, EP.cyan, EP.yellow, EP.lime, EP.white], age = t - t0;
    for (let i = 0; i < n; i++) {
      let x, y;
      if (o.cannon) { const sd = i % 2 ? 1 : -1, v = 1500 + hash2(i, 1) * 900, a = -Math.PI / 2 - sd * (.12 + hash2(i, 2) * .38); x = W / 2 + sd * 900 + Math.cos(a) * v * age * .9 + Math.sin(age * 4 + i) * 20; y = 1100 + Math.sin(a) * v * age + 900 * age * age; }
      else { x = hash2(i, 1) * W + Math.sin(age * 3 + i) * 30; y = -60 - hash2(i, 2) * 300 + age * (260 + hash2(i, 3) * 200); }
      if (y > H + 40 || y < -80) continue;
      const r = age * 7 + i; ctx.save(); ctx.translate(x, y); ctx.rotate(r); ctx.scale(1, Math.cos(r * 1.3)); ctx.fillStyle = cols[i % cols.length]; ctx.fillRect(-10, -6, 20, 12); ctx.restore();
    }
  }
  const tokenAt = (t, x, y, s, mv, o = {}) => toy(x, y, s, { ...CAST.token.o, ...dance(mv, bpOf(t) - .15), mouth: 'grin', ...o });
  const softAt = (t, x, y, s, mv, o = {}) => toy(x, y, s, { ...CAST.softmax.o, ...dance(mv, bpOf(t)), talk: singK(t), ...o });

  // =====================================================================================================
  // THE FOAM PARTY KIT
  // =====================================================================================================
  // foam: a mass of glossy suds from [[x, y, r]…] — all the shadows, then the whites, then the highlights, so it reads as one mass
  function foamMass(P, o = {}) {
    const sh = o.shade ?? '#A8C4E8', rim = o.rim ?? '#FFB8E0';
    ctx.fillStyle = sh; ctx.beginPath(); for (const [x, y, r] of P) { ctx.moveTo(x + r * 1.06 + 4, y + r * .12); ctx.arc(x + 4, y + r * .12, r * 1.06, 0, TAU); } ctx.fill();
    ctx.fillStyle = rim; ctx.beginPath(); for (const [x, y, r] of P) { ctx.moveTo(x + r, y); ctx.arc(x, y, r, 0, TAU); } ctx.fill();
    ctx.fillStyle = o.col ?? '#F8FBFF'; ctx.beginPath(); for (const [x, y, r] of P) { ctx.moveTo(x - r * .08 + r * .9, y - r * .06); ctx.arc(x - r * .08, y - r * .06, r * .9, 0, TAU); } ctx.fill();
    ctx.fillStyle = 'rgb(255 255 255 / .95)'; ctx.beginPath(); for (const [x, y, r] of P) { ctx.moveTo(x - r * .32 + r * .2, y - r * .38); ctx.ellipse(x - r * .32, y - r * .38, r * .2, r * .12, -.6, 0, TAU); } ctx.fill();
  }
  // foamBank(t, y, o): the foam's surface at y, filled down past the bottom of the frame. o.seed, o.r (bubble size), o.bob, o.x0/o.x1
  function foamBank(t, y, o = {}) {
    const seed = o.seed ?? 1, r0 = o.r ?? 60, x0 = o.x0 ?? -120, x1 = o.x1 ?? W + 120, P = [];
    ctx.fillStyle = lg(0, y, 0, y + 500, [[0, '#F4F8FF'], [1, '#C8D8F4']]); ctx.fillRect(x0, y + r0 * .3, x1 - x0, H + 1400 - y);
    for (let x = x0, i = 0; x < x1; i++) { const r = r0 * (.7 + hash2(seed, i) * .6); P.push([x, y + Math.sin(t * 2.2 + i * 1.3 + seed) * (o.bob ?? 8) - hash2(seed + 3, i) * r0 * .35, r]); x += r * 1.2; }
    for (let x = x0 + 40, i = 0; x < x1; i++) { const r = r0 * (.45 + hash2(seed + 7, i) * .35); P.push([x, y + r0 * .55 + hash2(seed + 9, i) * r0 * .5, r]); x += r * 1.6; }
    foamMass(P, o);
    // soap bubbles drifting up off the surface
    if (o.bubbles !== false) for (let i = 0; i < (o.nb ?? 10); i++) { const u = frac(hash2(seed, i + 50) + t * (.25 + hash2(seed, i + 51) * .2)), bx = lerp(x0 + 100, x1 - 100, hash2(seed, i + 52)) + Math.sin(t * 2 + i) * 30, by = y - u * 500, br = 10 + hash2(seed, i + 53) * 18; if (u > .9) continue; soapBubble(bx, by, br, 1 - u); }
  }
  function soapBubble(x, y, r, a = 1) {
    ctx.save(); ctx.globalAlpha *= a;
    ctx.fillStyle = 'rgb(220 240 255 / .12)'; ell(x, y, r, r); ctx.fill();
    ctx.lineWidth = Math.max(1.5, r * .08); ctx.strokeStyle = 'rgb(255 170 230 / .7)'; ctx.beginPath(); ctx.arc(x, y, r, .2, 2.2); ctx.stroke(); ctx.strokeStyle = 'rgb(140 240 255 / .75)'; ctx.beginPath(); ctx.arc(x, y, r, 2.4, 4.6); ctx.stroke(); ctx.strokeStyle = 'rgb(255 250 170 / .6)'; ctx.beginPath(); ctx.arc(x, y, r, 4.8, 6.1); ctx.stroke();
    ctx.fillStyle = 'rgb(255 255 255 / .9)'; ell(x - r * .35, y - r * .4, r * .18, r * .1, -.6); ctx.fill();
    ctx.restore();
  }
  // a foam cannon on a stand at (x, y) (the stand's foot), aimed at angle ang; spraying with power k (0..1+)
  function foamCannon(x, y, s, ang, t, k = 1, o = {}) {
    const nx = x + Math.cos(ang) * s * 2.4, ny = y - s * 2.6 + Math.sin(ang) * s * 2.4;
    // the spray: puffs flying on a ballistic arc
    if (k > 0) {
      const P = [], n = Math.round(26 * Math.min(2, k)), v = (o.v ?? 1500) * (.8 + .2 * Math.min(1.5, k));
      for (let i = 0; i < n; i++) { const age = frac(hash(i + (o.seed ?? 0) * 40) + t * 1.6) * 1.1, sp = (hash(i + 7) - .5) * .25, a = ang + sp, px = nx + Math.cos(a) * v * age, py = ny + Math.sin(a) * v * age + 700 * age * age, r = (14 + age * 70) * (.7 + hash(i + 3) * .6) * (o.puff ?? 1); if (age < .04) continue; P.push([px, py, r]); }
      foamMass(P);
    }
    ctx.save(); ctx.translate(x, y);
    ctx.strokeStyle = '#3A3A48'; ctx.lineWidth = s * .12; ctx.lineCap = 'round'; ctx.beginPath(); for (const sd of [-1, 0, 1]) { ctx.moveTo(0, -s * 2.6); ctx.lineTo(sd * s * .9, 0); } ctx.stroke();
    ctx.translate(0, -s * 2.6); ctx.rotate(ang + (k > 0 ? Math.sin(t * 40) * .02 : 0));
    gloss(pfRR(-s * .8, -s * .55, s * 3.2, s * 1.1, s * .5), o.col ?? EP.orange, { box: [-s * .8, -s * .55, s * 3.2, s * 1.1], lw: 4, spec: 1 });
    gloss(pfRR(s * 2.2, -s * .7, s * .55, s * 1.4, s * .2), '#C8CCD8', { box: [s * 2.2, -s * .7, s * .55, s * 1.4], lw: 4, spec: 1 });
    ctx.fillStyle = '#FFFFFF'; ctx.fillRect(-s * .2, -s * .55, s * .35, s * 1.1);
    ctx.restore();
  }
  // a palm tree with its foot at (x, y); o.sil for a sunset silhouette
  function palm(x, y, s, t, o = {}) {
    const lean = o.lean ?? .25, sway = Math.sin(t * 1.3 + x) * .04, trunk = o.sil ?? '#8A5A2A', leaf = o.sil ?? '#2AA84A', rim = o.sil ? (o.rim ?? EP.orange) : null;
    let px = x, py = y, ang = -Math.PI / 2 + lean * .3;
    for (let i = 0; i < 9; i++) { const nx = px + Math.cos(ang) * s * .55, ny = py + Math.sin(ang) * s * .55; gloss(pfEll((px + nx) / 2, (py + ny) / 2, s * (.28 - i * .012), s * .3, ang + Math.PI / 2), trunk, { box: [nx - s * .3, ny - s * .3, s * .6, s * .6], lw: 3, rim, spec: o.sil ? 0 : .3, flat: !!o.sil }); px = nx; py = ny; ang += (lean + sway) * .14; }
    for (let i = 0; i < 7; i++) {
      const a = -Math.PI / 2 + (i - 3) * .48 + sway * 3, L = s * (2.2 + hash(i + x) * .5), droop = .9;
      gloss(() => { ctx.moveTo(px, py); ctx.quadraticCurveTo(px + Math.cos(a) * L * .5 + Math.cos(a - .6) * s * .3, py + Math.sin(a) * L * .5 - s * .5, px + Math.cos(a) * L, py + Math.sin(a) * L * .35 + L * droop * .45); ctx.quadraticCurveTo(px + Math.cos(a) * L * .5 + Math.cos(a + .6) * s * .2, py + Math.sin(a) * L * .5 + s * .1, px, py); }, leaf, { box: [px - L, py - L, L * 2, L * 2], lw: 3, rim, spec: o.sil ? 0 : .5, flat: !!o.sil });
    }
    if (!o.sil) for (const [dx, dy] of [[-.15, .2], [.2, .25], [0, .35]]) glossBall(px + dx * s, py + dy * s, s * .18, s * .18, '#6A4A20', { lw: 2, rim: null });
  }
  // an inflatable dolphin floating at (x, y)
  function dolphin(x, y, s, rot = 0, col = '#5AB8F8') {
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot); ctx.scale(s, s);
    gloss(() => { ctx.moveTo(-2.4, .2); ctx.quadraticCurveTo(-1.6, -1.4, .6, -1.1); ctx.quadraticCurveTo(1.8, -1.0, 2.2, -.5); ctx.quadraticCurveTo(2.9, -.35, 3.1, -.1); ctx.quadraticCurveTo(2.4, .15, 1.8, .3); ctx.quadraticCurveTo(.2, .9, -1.6, .6); ctx.quadraticCurveTo(-2.3, .6, -2.4, .2); }, col, { box: [-2.4, -1.4, 5.5, 2.3], lw: .07, spec: 1, hi: .45, rim: '#FFFFFF' });
    gloss(pfPts([[-.2, -1.1], [.3, -1.9], [.7, -1.05]]), shade(col, .1), { box: [-.2, -1.9, .9, .9], lw: .07, rim: null });
    gloss(pfPts([[-2.2, .1], [-3.0, -.6], [-2.9, .3], [-3.1, .9], [-2.2, .45]]), shade(col, .1), { box: [-3.1, -.6, .9, 1.5], lw: .07, rim: null });
    gloss(pfPts([[.3, .5], [-.1, 1.2], [.8, .55]]), shade(col, .1), { box: [-.1, .5, .9, .7], lw: .07, rim: null });
    ctx.fillStyle = '#FFFFFF'; ctx.beginPath(); ctx.moveTo(-1.6, .55); ctx.quadraticCurveTo(.4, .9, 1.8, .3); ctx.quadraticCurveTo(.5, .45, -1.6, .55); ctx.fill();
    ctx.fillStyle = '#12101A'; ell(1.75, -.45, .13, .15); ctx.fill(); ctx.fillStyle = '#FFF'; ell(1.72, -.5, .05, .05); ctx.fill();
    ctx.strokeStyle = '#12101A'; ctx.lineWidth = .06; ctx.beginPath(); ctx.arc(2.5, -.2, .25, .2, 1.4); ctx.stroke();
    ctx.restore();
  }
  // a lifeguard tower: platform top at (x, y), legs down to y + h
  function lifeguardTower(x, y, w, h, o = {}) {
    ctx.strokeStyle = EP.line; ctx.lineWidth = 16; ctx.lineCap = 'round';
    ctx.beginPath(); ctx.moveTo(x - w * .38, y); ctx.lineTo(x - w * .48, y + h); ctx.moveTo(x + w * .38, y); ctx.lineTo(x + w * .48, y + h); ctx.moveTo(x - w * .42, y + h * .5); ctx.lineTo(x + w * .45, y + h * .15); ctx.moveTo(x + w * .42, y + h * .5); ctx.lineTo(x - w * .45, y + h * .15); ctx.stroke();
    ctx.strokeStyle = '#F4F0E8'; ctx.lineWidth = 9; ctx.stroke();
    gloss(pfRR(x - w / 2, y - 10, w, 30, 8), '#E8342A', { box: [x - w / 2, y - 10, w, 30], lw: 4, rim: o.rim, spec: .8 });
    for (let i = 0; i < 5; i++) { ctx.fillStyle = '#FFFFFF'; ctx.fillRect(x - w / 2 + 12 + i * (w - 24) / 5, y - 6, (w - 24) / 10, 22); }
    if (o.sign) { gloss(pfRR(x - w * .42, y + 30, w * .84, 56, 10), '#FFFFFF', { box: [x - w * .42, y + 30, w * .84, 56], lw: 4, rim: null }); ptext(o.sign, x, y + 60, 36, { font: 'archivo', fill: EP.red, maxW: w * .74 }); }
  }
  // the sunset beach: sky, the striped sun, the sea, sand, silhouette palms; o.sky, o.sun (y), o.hz, o.sand
  function beach(t, o = {}) {
    const hz = o.hz ?? 600;
    bgGrad(o.sky ?? [[0, '#1A0650'], [.45, '#A0148A'], [.8, '#FF4F7A'], [1, '#FFA04A']], { y1: hz });
    for (let i = 0; i < 30; i++) { const a = .3 + .7 * Math.abs(Math.sin(t * (1 + hash2(i, 3) * 3) + i)); ctx.fillStyle = `rgb(255 255 255 / ${.4 * a * hash2(i, 4)})`; ctx.fillRect(hash2(i, 1) * W, hash2(i, 2) * hz * .45, 3, 3); }
    const sy = o.sun ?? hz - 40, sr = o.sunR ?? 230, sx = o.sunX ?? W / 2;
    glow(sx, sy, sr * 2.4, '#FFB070', .55);
    ctx.save(); ctx.beginPath(); ctx.rect(-900, -900, W + 1800, hz + 900); ctx.clip();
    ell(sx, sy, sr, sr); ctx.fillStyle = lg(0, sy - sr, 0, sy + sr, [[0, '#FFF6A0'], [.5, '#FFB04A'], [1, '#FF3F8A']]); ctx.fill();
    ctx.fillStyle = o.sky?.[1]?.[1] ?? '#A0148A'; for (let i = 0; i < 6; i++) { const yy = sy + sr * (.1 + i * .15), hh = 6 + i * 4; ctx.fillRect(sx - sr, yy, sr * 2, hh); }
    ctx.restore();
    // sea
    ctx.fillStyle = lg(0, hz, 0, o.sand ?? 760, [[0, o.sea0 ?? '#3A1A8A'], [1, o.sea1 ?? '#0A6AA8']]); ctx.fillRect(-900, hz, W + 1800, (o.sand ?? 760) - hz + 2);
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; for (let i = 0; i < 16; i++) { const yy = hz + 8 + i * 10, w = (sr * 1.1) * (1 - i / 20) * (.6 + .4 * Math.sin(t * 3 + i)); ctx.fillStyle = `rgb(255 190 120 / ${.5 - i * .025})`; ctx.fillRect(sx - w / 2 + Math.sin(t * 2 + i) * 20, yy, w, 4); } ctx.restore();
    // sand
    ctx.fillStyle = lg(0, o.sand ?? 760, 0, H, [[0, o.sand0 ?? '#FFB88A'], [1, o.sand1 ?? '#E88A6A']]); ctx.fillRect(-900, o.sand ?? 760, W + 1800, H + 900);
    ctx.fillStyle = 'rgb(255 255 255 / .5)'; ctx.beginPath(); for (let x = -100; x < W + 100; x += 30) ctx.lineTo(x, (o.sand ?? 760) + 4 + Math.sin(x * .02 + t * 2) * 5); ctx.lineTo(W + 100, (o.sand ?? 760) - 6); ctx.lineTo(-100, (o.sand ?? 760) - 6); ctx.fill();
    if (o.palms !== false) { palm(110, (o.sand ?? 760) + 40, 70, t, { sil: '#2A0A3A', lean: .45, rim: EP.orange }); palm(1810, (o.sand ?? 760) + 40, 76, t, { sil: '#2A0A3A', lean: -.45, rim: EP.orange }); }
  }

  // =====================================================================================================
  // A. "We didn't start the scaling": the V2.16 bubble pops on the downbeat; foam cannons fire across a sunset beach, SOFTMAX sings on the
  // lifeguard tower, the hook lands in chrome.
  // =====================================================================================================
  function shotHook1(t) {
    hideCaption();
    const r = rb(t), l = t - SPAN.start, land = wordT(LN[0], 4), sh = shakeAt(t, t, land, .3, 18);
    setLight({ rim: EP.cyan, rimK: .85 });
    camBegin(W / 2 - sh[0], H / 2 - sh[1], 1 + .03 * clamp(r / 4));
    beach(t, {});
    const open = easeOut(clamp(r / .6));
    laserFan(W / 2, 600, t, { n: 13, cols: [EP.cyan, EP.magenta, EP.yellow], angle: -Math.PI / 2, spread: 2.8 * open + .01, sweep: .2, alpha: .5 * open });
    speaker(360, 900, 170, t, { logo: 'HYPE' }); speaker(360, 610, 150, t, {}); speaker(1560, 900, 170, t, { logo: 'HYPE' }); speaker(1560, 610, 150, t, {});
    // the tower + SOFTMAX
    lifeguardTower(W / 2, 835, 300, 200, { sign: 'SOFTMAX', rim: EP.cyan });
    softAt(t, W / 2, 825, 34, r < 2.9 ? 'sing' : 'raise', { turn: Math.sin(t * 1.3) * .35, swing: .5 + Math.sin(t * 7) * .25 });
    tokenAt(t, 640, 1010, 40, 'runningMan');
    djClawd(1290, 1000, 22, { shades: true, aL: 1.2 + Math.sin(bpOf(t) * Math.PI) * .3, aR: 1.2 - Math.sin(bpOf(t) * Math.PI) * .3, mouth: 'grin', dy: -bounce(t) * .5 });
    raveCrowd(t, { y: 1060, s: 1.3, rows: 1, n: 10, hands: .9, k: 1, rim: EP.magenta });
    foamBank(t, 1010 - open * 30, { seed: 2, r: 46, nb: 8 });
    dolphin(260 + Math.sin(t * 1.5) * 20, 960 + Math.sin(t * 2.3) * 8, 34, Math.sin(t * 2) * .12);
    // the cannons fire on the downbeat
    foamCannon(90, 780, 44, -.95, t, open * 1.2, { seed: 1, v: 1400 }); foamCannon(W - 90, 780, 44, -Math.PI + .95, t, open * 1.2, { seed: 2, v: 1400 });
    camEnd();
    hookWords(LN[0], t, { y1: 182, y2: 332, s1: 104, s2: 168, styles: ['ice', 'gold', 'hot'] });
    // the bubble from the business page pops
    if (l < .3) { const u = l / .3; ctx.save(); ctx.globalAlpha = 1 - u; for (let i = 0; i < 14; i++) { const a = i / 14 * TAU, rr = 200 + u * 700; ctx.strokeStyle = ['#FFB0E8', '#8AF0FF', '#FFF0A0'][i % 3]; ctx.lineWidth = 12 * (1 - u); ctx.beginPath(); ctx.arc(W / 2 + Math.cos(a) * rr, 470 + Math.sin(a) * rr, 60 * (1 - u) + 10, a, a + 1.2); ctx.stroke(); } ctx.restore(); burst('POP!', W / 2, 520, 170, { pop: 1 - u * .3, col: '#FFFFFF', ink: EP.magenta, spin: 1, n: 20 }); }
    lensFlare(1600, 480, .5 + .2 * Math.sin(t * 3));
    if (l < .12) strobe(.9 * (1 - l / .12));
    else strobe(strobeK(t, 1, .16) * .2);
    if (l < .08) fx({ rgb: 1 - l / .08 });
  }

  // =====================================================================================================
  // B. "It was always training,": BEACH BOOTCAMP. MC TOKEN and SOFTMAX lead a class of candy computers doing jumping jacks in ankle-deep foam;
  // the EPOCH board counts forever.
  // =====================================================================================================
  function shotTrain(t) {
    const l = t - CUT.train, bb = bpOf(t), up = Math.floor(bb) % 2 === 0, jk = Math.exp(-frac(bb) * 5);
    setLight({ rim: '#FFFFFF', rimK: .5 });
    beach(t, { sky: [[0, '#2A7AD8'], [.5, '#8AC8F0'], [.85, '#FFD08A'], [1, '#FF9A5A']], sun: 330, sunR: 150, sunX: 1540, hz: 560, sand: 700, sea0: '#1AA8C8', sea1: '#0A7AA8', sand0: '#FFE0A0', sand1: '#F0B870', palms: false });
    palm(90, 760, 64, t, { lean: .4 }); palm(1330, 720, 58, t, { lean: -.3 });
    // the EPOCH board
    const bx = 1560, by = 250;
    for (const sd of [-1, 1]) gloss(pfRR(bx + sd * 140 - 12, by + 300, 24, 420, 6), '#8A5A2A', { box: [bx + sd * 140 - 12, by + 300, 24, 420], lw: 4, rim: null });
    gloss(pfRR(bx - 250, by, 500, 400, 20), '#C88A4A', { box: [bx - 250, by, 500, 400], lw: 5, rim: null, spec: .4 });
    ptext('BEACH BOOTCAMP', bx, by + 50, 42, { font: 'archivo', fill: '#FFF4D0', strokes: [['#5A3010', 9]] });
    rrect(bx - 210, by + 90, 420, 170, 12); paint('#05050A', '#3A2A1A', 4);
    txt('EPOCH', bx - 190, by + 118, 26, EP.laser, { font: 'code', align: 'left' });
    segText(String(88 + Math.floor(Math.max(0, l) * 11.3)).padStart(5, ' '), bx - 180, by + 140, 96, EP.laser, { off: '#062006' });
    txt('Time remaining:', bx, by + 300, 30, '#3A1A00', { font: 'archivo' }); txt('ALWAYS', bx, by + 346, 44, EP.red, { font: 'archivo', stroke: '#FFF4D0', sw: 6 });
    // the class (candy computers in sweatbands), in step
    const cls = [[CANDY.bondi, EP.magenta], [CANDY.blueberry, EP.yellow], [CANDY.lime, EP.cyan], [CANDY.grape, EP.orange], [CANDY.strawberry, EP.lime], [CANDY.tangerine, EP.cyan]];
    cls.forEach(([c, hb], i) => {
      const x = 250 + i * 190, y = 760, hy = up ? -10 : -3.8, hx = up ? 3.2 : 4.4;
      gumdrop(x, y, 17, { col: c, headband: hb, face: up ? 'happy' : 'closed', mouth: up ? 'grin' : 'open', hL: [-hx, hy], hR: [hx, hy], gL: up ? 'wave' : 'fist', gR: up ? 'wave' : 'fist', jump: jk * 1.1, sweat: .6, rim: EP.orange });
    });
    foamBank(t, 755, { seed: 5, r: 34, nb: 6 });
    // the leaders on their steps
    for (const x of [560, 1000]) gloss(pfRR(x - 150, 960, 300, 60, 14), '#E8342A', { box: [x - 150, 960, 300, 60], lw: 4, rim: EP.cyan });
    const jj = { jump: jk * .7, hL: up ? [-2.1, -10.8] : [-3.1, -5.4], hR: up ? [2.1, -10.8] : [3.1, -5.4], gL: up ? 'wave' : 'flat', gR: up ? 'wave' : 'flat', fL: [up ? -.5 : 0, 0], fR: [up ? .5 : 0, 0] };
    toy(560, 965, 40, { ...CAST.token.o, ...jj, hat: 'capBack', mouth: 'grin', headTilt: 0 });
    toy(1000, 965, 42, { ...CAST.softmax.o, ...jj, talk: singK(t), swing: (up ? .4 : -.4) });
    if (l < .1) cutFX('flash');
  }

  // =====================================================================================================
  // C. "and the curves kept gaining,": the swell. The sea rises as an exponential wave, ×1.6 a notch every beat (C1's pipes climbed ×1.5),
  // with a neon curve on its crest; SOFTMAX, MC TOKEN and a candy computer surf it higher every beat, off the top of the frame.
  // =====================================================================================================
  const WG = 1.6, WA = 4.2;
  function swellH(t) { const t0 = CUT.curves, b = (t - t0) / beatLen(), n = Math.floor(b), f = backOut(clamp(frac(b) / .35), 1.8); return b < 0 ? 1 : WG ** (n + f); }
  const crestY = (x, S, base, h0) => { const u = clamp((x + 100) / (W + 200)); return base - S * h0 * (Math.exp(WA * u) - 1) / (Math.exp(WA) - 1); };
  function surfboard(x, y, ang, len, col) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(ang);
    gloss(pfEll(0, 0, len / 2, len * .09), col, { box: [-len / 2, -len * .09, len, len * .18], lw: 4, spec: 1, rim: '#FFFFFF' });
    ctx.fillStyle = '#FFFFFF'; ctx.fillRect(-len * .4, -len * .015, len * .8, len * .03);
    ctx.restore();
  }
  function shotCurves(t) {
    const l = t - CUT.curves, bb = bpOf(t), S = swellH(t), base = 900, h0 = 34, camY = lerp(540, 330, ease(clamp(l / 3.2)));
    const nb = Math.floor(l / beatLen()), ja = l / beatLen() - nb;
    setLight({ rim: EP.lime, rimK: .8 });
    camBegin(W / 2, camY, 1);
    bgGrad([[0, '#05022A'], [.5, '#2A0A6A'], [.85, '#C82A8A'], [1, '#FF7A4A']], { y0: -500, y1: 620 });
    for (let i = 0; i < 50; i++) { ctx.fillStyle = `rgb(255 255 255 / ${.5 * hash2(i, 4) * (.4 + .6 * Math.abs(Math.sin(t * 2 + i)))})`; ctx.fillRect(hash2(i, 1) * W, -500 + hash2(i, 2) * 900, 3, 3); }
    // graph paper in the sky: the wave is the chart
    ctx.strokeStyle = 'rgb(120 255 120 / .12)'; ctx.lineWidth = 2; ctx.beginPath(); for (let x = -40; x < W + 40; x += 120) { ctx.moveTo(x, -600); ctx.lineTo(x, 620); } for (let y = 620; y > -600; y -= 120) { ctx.moveTo(-100, y); ctx.lineTo(W + 100, y); } ctx.stroke();
    ctx.fillStyle = lg(0, 600, 0, 1100, [[0, '#1A3A8A'], [1, '#0A1A4A']]); ctx.fillRect(-900, 600, W + 1800, 900);
    // the wave body
    const pts = []; for (let x = -120; x <= W + 120; x += 20) pts.push([x, crestY(x, S, base, h0)]);
    ctx.beginPath(); pts.forEach(([x, y], i) => i ? ctx.lineTo(x, y) : ctx.moveTo(x, y)); ctx.lineTo(W + 120, H + 400); ctx.lineTo(-120, H + 400); ctx.closePath();
    ctx.fillStyle = lg(0, Math.min(...pts.map(p => p[1])), 0, H + 200, [[0, '#2AE8D8'], [.35, '#0A9AC8'], [1, '#062A6A']]); ctx.fill();
    ctx.save(); ctx.clip(); ctx.strokeStyle = 'rgb(255 255 255 / .18)'; ctx.lineWidth = 6; for (let k = 1; k < 8; k++) { ctx.beginPath(); pts.forEach(([x, y], i) => { const yy = y + k * 70 + Math.sin(x * .01 + t * 3 + k) * 10; i ? ctx.lineTo(x, yy) : ctx.moveTo(x, yy); }); ctx.stroke(); } ctx.restore();
    // foam lip + the neon curve on the crest
    const lip = []; for (let x = -100, i = 0; x < W + 120; i++) { const r = 16 + hash(i + 5) * 14; lip.push([x + Math.sin(t * 5 + i) * 4, crestY(x, S, base, h0) - 4 + Math.sin(t * 7 + i * 2) * 4, r]); x += r * 1.4; }
    foamMass(lip);
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; ctx.lineJoin = 'round'; for (const [c, w] of [[alpha(EP.lime, .2), 56], [alpha(EP.lime, .45), 26], [alpha(EP.lime, 1), 12], ['#EFFFE0', 5]]) { ctx.strokeStyle = c; ctx.lineWidth = w; ctx.beginPath(); pts.forEach(([x, y], i) => i ? ctx.lineTo(x, y - 34) : ctx.moveTo(x, y - 34)); ctx.stroke(); } ctx.restore();
    // the surfers: fixed stations along the curve, so they ride higher every beat
    const surfer = (x, draw, len, col) => { const y = crestY(x, S, base, h0) + 30, y2 = crestY(x + 40, S, base, h0) + 30, ang = Math.atan2(y2 - y, 40); surfboard(x, y, ang, len, col); draw(x, y - 8, ang); };
    surfer(1720, (x, y, a) => gumdrop(x, y, 17, { col: CANDY.bondi, label: 'GPT', face: 'wide', mouth: 'O', hL: [-4.6, -8], hR: [4.6, -8], gL: 'open', gR: 'open', rot: a * .6, shadow: false }), 200, EP.yellow);
    surfer(1030, (x, y, a) => toy(x, y, 36, { ...CAST.token.o, rot: a * .6, lean: -.1, hL: [-3.3, -7.4], hR: [3.3, -6.4], gL: 'flat', gR: 'point', mouth: 'grin', fL: [-.6, 0], fR: [.6, 0], shadow: false }), 300, EP.cyan);
    surfer(1420, (x, y, a) => toy(x, y, 36, { ...CAST.softmax.o, rot: a * .6, lean: -.12, hL: [-3.3, -7.8], hR: [2.6, -10.6], gL: 'flat', gR: 'wave', talk: singK(t), fL: [-.6, 0], fR: [.6, 0], swing: .7, shadow: false }), 300, EP.magenta);
    camEnd();
    // the gain, multiplying on every notch (C1's idiom), riding the lead surfer
    const lx = 1420, ly = crestY(lx, S, base, h0) - 330 - (camY - 540);
    if (nb >= 0 && ly > 60) { const v = WG ** (nb + 1), lab = '×' + (v < 10 ? v.toFixed(1).replace('.0', '') : Math.round(v)), k = clamp(ja / .12); chromeText(lab, lx - 300, ly, 100, { style: 'lime', italic: .12, depth: 10, s: lerp(1.5, 1, easeOut(k)), alpha: clamp(k * 3) }); }
    const tipY = crestY(W, S, base, h0) - (camY - 540);
    lensFlare(Math.min(W - 60, 1840), Math.max(30, tipY - 20), .6 + .25 * kick(t, 5));
    if (l < .1) cutFX('rgb');
  }

  // =====================================================================================================
  // D. "We didn't start the scaling" (2): the party boat S.S. SCALING at dusk. DJ CLAWD scratches on deck, lasers fan into the sky, the hook
  // lands in chrome, confetti cannons fire on SCALING.
  // =====================================================================================================
  function boat(x, y, w, t, rot) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot);
    // hull
    gloss(() => { ctx.moveTo(-w / 2 - 60, -60); ctx.lineTo(w / 2 + 120, -60); ctx.quadraticCurveTo(w / 2 + 40, 110, w / 2 - 80, 150); ctx.lineTo(-w / 2 + 40, 150); ctx.quadraticCurveTo(-w / 2 - 40, 100, -w / 2 - 60, -60); }, '#F4F6FA', { box: [-w / 2 - 60, -60, w + 180, 210], lw: 6, spec: 1, rim: EP.magenta });
    ctx.fillStyle = EP.red; ctx.fillRect(-w / 2 - 40, 20, w + 130, 22); ctx.fillStyle = EP.ultra; ctx.fillRect(-w / 2 - 30, 52, w + 100, 10);
    for (let i = 0; i < 8; i++) { ell(-w / 2 + 60 + i * (w / 8), -20, 16, 16); paint('#8AD8FF', EP.line, 4); }
    ptext('S.S. SCALING', -w / 2 + 230, 92, 44, { font: 'archivo', fill: EP.ultra, strokes: [['#FFFFFF', 8]] });
    // deck rail + string lights
    ctx.strokeStyle = '#C8CCD8'; ctx.lineWidth = 5; ctx.beginPath(); ctx.moveTo(-w / 2 - 50, -110); ctx.lineTo(w / 2 + 100, -110); ctx.stroke(); for (let i = 0; i < 16; i++) { const px = -w / 2 - 40 + i * (w + 140) / 15; ctx.beginPath(); ctx.moveTo(px, -110); ctx.lineTo(px, -60); ctx.stroke(); }
    ctx.restore();
  }
  function shotHook2(t) {
    hideCaption();
    const l = t - CUT.hook2, bb = bpOf(t), land = wordT(LN[2], LN[2].text.split(' ').length - 1), rot = Math.sin(t * 1.6) * .025, bob = Math.sin(t * 2.1) * 10;
    setLight({ rim: EP.magenta, rimK: .9 });
    beach(t, { sky: [[0, '#02021A'], [.5, '#1A0A5A'], [.85, '#6A1A8A'], [1, '#FF5A7A']], sun: 720, sunR: 170, hz: 730, sand: 1400, sea0: '#2A1A6A', sea1: '#0A0A3A', palms: false });
    const deckY = 860 + bob;
    for (const [x, c, a] of [[520, EP.cyan, -1.9], [W / 2, EP.laser, -Math.PI / 2], [1400, EP.magenta, -1.25]]) laserFan(x, deckY - 60, t, { n: 9, col: c, angle: a, spread: 1.2, sweep: .4, alpha: .6, flicker: t > land ? .5 : 0 });
    // the deck party
    ctx.save(); ctx.translate(W / 2, deckY); ctx.rotate(rot); ctx.translate(-W / 2, -deckY);
    speaker(420, deckY - 110, 120, t, {}); speaker(1500, deckY - 110, 120, t, {});
    djClawd(W / 2, deckY - 150, 20, { shades: true, aL: 1.2 + Math.sin(bb * Math.PI) * .3, aR: lerp(-.1, -.5, kick(t, 10)), mouth: 'grin', dy: -bounce(t) * .3 });
    djBooth(W / 2, deckY - 140, 420, t, { scratch: kick(t, 10) });
    softAt(t, 680, deckY - 110, 30, 'vogue');
    tokenAt(t, 1240, deckY - 110, 30, 'pump');
    ctx.restore();
    boat(W / 2 - 40, deckY, 1300, t, rot);
    // the sea in front
    ctx.fillStyle = lg(0, 960, 0, H, [[0, '#1A1A6A'], [1, '#05052A']]); ctx.beginPath(); ctx.moveTo(-100, H + 100); for (let x = -100; x <= W + 100; x += 40) ctx.lineTo(x, 975 + Math.sin(x * .012 + t * 3) * 14); ctx.lineTo(W + 100, H + 100); ctx.fill();
    foamBank(t, 1050, { seed: 8, r: 40, nb: 6, shade: '#6A7AB8', rim: '#FF8AC8', col: '#E8ECFF' });
    dolphin(200 + Math.sin(t * 1.5) * 20, 985 + Math.sin(t * 2.3) * 10, 30, .15 + Math.sin(t * 2) * .12, '#FF7AC8');
    dolphin(1740, 995 + Math.sin(t * 2 + 1) * 10, 26, -.1 + Math.sin(t * 2.4) * .1);
    hookWords(LN[2], t, { y1: 182, y2: 336, s1: 106, s2: 176, styles: ['chrome', 'purple', 'hot'] });
    confetti(t, land, 120, { cannon: true });
    if (t > land && t < land + .12) strobe(.5 * (1 - (t - land) / .12));
    else strobe(strobeK(t, 1, .16) * .18);
    if (l < .1) cutFX('zoom');
  }

  // =====================================================================================================
  // E. "No, we didn't preordain it,": foam up to everyone's chins. SOFTMAX wags her finger on "No" (NO! burst); then every head in the
  // foam shrugs, hands popping out, under spinning chrome question marks.
  // =====================================================================================================
  function shotNo(t) {
    const l = t - CUT.no, bb = bpOf(t), shrugAt = wordT(LN[3], 3), shrug = t >= shrugAt - .05, wagging = !shrug, dip = shrug ? Math.exp(-frac(bpOf(t) - bpOf(shrugAt)) * 5) : 0;
    setLight({ rim: EP.magenta, rimK: .6 });
    camBegin(wagging ? 960 : W / 2, wagging ? 560 : H / 2, wagging ? 1.3 + .04 * clamp(l / 1) : 1);
    bgGrad([[0, '#FF6AB8'], [.6, '#FFB0D8'], [1, '#FFE0F0']], { y1: 700 });
    rays(W / 2, 560, 22, 'rgb(255 255 255 / .16)', t * .25);
    for (let i = 0; i < 14; i++) { const u = frac(hash(i + 60) + t * .12), bx = hash(i + 61) * W + Math.sin(t * 1.5 + i) * 30, by = 800 - u * 900; soapBubble(bx, by, 20 + hash(i + 62) * 40, 1 - u); }
    const shrugPose = (sd, s) => ({ hL: [-2.9, -8.8 - dip * .4], hR: [2.9, -8.8 - dip * .4], gL: 'flat', gR: 'flat', headTilt: .15 * (sd || 1), brows: 'up', mouth: 'flat' });
    // the back row: candy computers and a dolphin, in the foam
    [[300, CANDY.bondi], [640, CANDY.lime], [1300, CANDY.grape], [1620, CANDY.blueberry]].forEach(([x, c], i) => gumdrop(x, 700, 17, { col: c, face: shrug ? 'sly' : 'wide', mouth: shrug ? 'flat' : 'O', hL: shrug ? [-4.4, -9.4 - dip] : [-4.3, -3.6], hR: shrug ? [4.4, -9.4 - dip] : [4.3, -3.6], gL: shrug ? 'flat' : 'open', gR: shrug ? 'flat' : 'open', jump: shrug ? dip * .4 : 0 }));
    dolphin(1660, 590 + Math.sin(t * 2) * 8, 40, Math.sin(t * 1.7) * .1 - .1, '#FF7AC8');
    foamBank(t, 640, { seed: 11, r: 44, nb: 0 });
    // the front row: the trio up to their chins
    const cy = 790;
    toy(520, cy + 6.3 * 50, 50, { ...CAST.token.o, ...(shrug ? shrugPose(-1) : { hL: [-2.3, -4], hR: [2.3, -4] }), mouth: shrug ? 'flat' : 'O', eyes: shrug ? 'dot' : 'wide', shadow: false, bob: dip * .5 });
    const wag = Math.sin(bb * Math.PI * 2) * .9;
    toy(W / 2, cy + 6.3 * 56, 56, { ...CAST.softmax.o, ...(shrug ? shrugPose(1) : { hR: [2.3 + wag, -9.4], gR: 'point', hL: [-2.4, -4.4], gL: 'fist', headTilt: wag * .06, brows: 'angry' }), talk: singK(t), shadow: false, bob: dip * .5, swing: Math.sin(t * 5) * .3 });
    djClawd(1400, cy + 5.2 * 30, 30, { shades: true, aL: shrug ? .9 + dip * .3 : -.6, aR: shrug ? .9 + dip * .3 : -.6, mouth: shrug ? 'o' : 'grin', legs: false, shadow: false, dy: -dip * .3 });
    foamBank(t, cy + 58, { seed: 13, r: 52, nb: 8 });
    // shrugging hands poke out of the foam (they're drawn with the toys; the foam covers the rest)
    camEnd();
    if (wagging) burst('NO!', 1440, 300, 150, { pop: pop(t, CUT.no + .02, .2), col: EP.yellow, ink: EP.magenta, spin: .3 });
    if (shrug) [[520, 'ice'], [W / 2, 'hot'], [1400, 'gold']].forEach(([x, st], i) => { const k = pop(t, shrugAt + i * .06, .2); if (k > 0) chromeText('?', x, 250 + Math.sin(t * 4 + i) * 12, 200, { style: st, depth: 18, s: k, sx: .35 + .65 * Math.abs(Math.cos(t * 3.2 + i * 1.1)) }); });
    if (l < .1) cutFX('flash');
  }

  // =====================================================================================================
  // F. "but we can't contain it!": the foam pit's barrier. The cannons go into overdrive, FOAM.EXE warns (C1's crash dialog, again) and the
  // cursor goes for OK… the foam bursts over the barrier, swallows the dialog, floods the frame and swallows the camera.
  // =====================================================================================================
  const clickAt = () => wordT(LN[3], 7), burstAt = () => wordT(LN[3], 8), itAt = () => wordT(LN[3], 9);
  function pitLevel(t) { const t0 = CUT.contain, tb = burstAt(); if (t < tb) return lerp(930, 690, easeOut(clamp((t - t0) / (tb - t0)))) + (t > clickAt() ? Math.sin(t * 30) * 6 : 0); return 690 - easeIn(clamp((t - tb) / 1.2)) * 1200; }
  function shotContain(t, o = {}) {
    const bb = bpOf(t), tc = clickAt(), tbst = burstAt(), tit = itAt(), br = t - tbst, flood = br > 0 ? easeIn(clamp(br / (tit - tbst + .45))) : 0;
    const sh = shakeAt(t, t, tbst, .6, 28), sh2 = shakeAt(t, t, tit, .4, 18);
    setLight({ rim: EP.red, rimK: .8 });
    camBegin(W / 2 - sh[0] - sh2[0], H / 2 - sh[1] - sh2[1], 1 + flood * .1);
    beach(t, { sky: [[0, '#2A0620'], [.5, '#8A0A3A'], [.85, '#FF3A4A'], [1, '#FF9A4A']], hz: 560, sand: 700, sun: 520, sunR: 190, palms: false });
    // siren beams
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; for (const [ox, sp] of [[300, 5], [1620, -5]]) { const a = t * sp; ctx.fillStyle = 'rgb(255 40 40 / .18)'; poly([[ox, 120], [ox + Math.cos(a - .2) * 2400, 120 + Math.sin(a - .2) * 2400], [ox + Math.cos(a + .2) * 2400, 120 + Math.sin(a + .2) * 2400]]); ctx.fill(); } ctx.restore();
    for (const ox of [300, 1620]) { glossBall(ox, 120, 40, 32, EP.red, { lw: 4, rim: null }); glow(ox, 120, 150, EP.red, .6 + .4 * Math.sin(t * 20)); }
    // SOFTMAX on the tower, in the pit, the foam rising round her
    const py = pitLevel(t);
    lifeguardTower(1260, 640, 280, 300, { rim: EP.red });
    softAt(t, 1260, 632, 32, br > 0 ? 'raise' : 'sing', { eyes: br > 0 ? 'wide' : undefined, mouth: br > 0 ? 'O' : undefined, jump: br > 0 ? Math.abs(Math.sin(bb * Math.PI)) * .6 : 0 });
    // the cannons in overdrive
    const od = 1 + clamp((t - CUT.contain) / .8) * .8;
    foamCannon(160, 700, 40, -1.0, t, od, { seed: 3, v: 1300, puff: 1.2 }); foamCannon(W - 160, 700, 40, -Math.PI + 1.0, t, od, { seed: 4, v: 1300, puff: 1.2 });
    foamBank(t, py, { seed: 17, r: 64, nb: 10 });
    // the barrier: MAX FOAM LEVEL, bursting outward
    const bk = br > 0 ? easeOut(clamp(br / .35)) : 0;
    for (let i = 0; i < 6; i++) {
      const x = 180 + i * 312, fly = bk * (i % 2 ? 1 : -1);
      ctx.save(); ctx.translate(x + fly * 300 * (1 + i * .1), 820 + bk * 260 - Math.sin(bk * Math.PI) * 200); ctx.rotate(fly * 1.4);
      gloss(pfRR(-150, -70, 300, 140, 12), '#E8EAF4', { box: [-150, -70, 300, 140], lw: 5, rim: EP.red, spec: 1 });
      ctx.save(); rrect(-140, -60, 280, 36, 6); ctx.clip(); ctx.fillStyle = EP.yellow; ctx.fillRect(-140, -60, 280, 36); ctx.fillStyle = '#000'; for (let q = -6; q < 8; q++) { ctx.save(); ctx.translate(q * 40, -60); ctx.transform(1, 0, -1, 1, 0, 0); ctx.fillRect(0, 0, 18, 36); ctx.restore(); } ctx.restore();
      if (i === 2 || i === 3) ptext(i === 2 ? 'FOAM ZONE' : 'MAX LEVEL', 0, 20, 40, { font: 'archivo', fill: EP.red });
      ctx.restore();
    }
    // the red MAX line and the level meter
    if (br < 0) { ctx.strokeStyle = EP.red; ctx.lineWidth = 6; ctx.setLineDash([26, 16]); ctx.beginPath(); ctx.moveTo(-100, 700); ctx.lineTo(W + 100, 700); ctx.stroke(); ctx.setLineDash([]); }
    const pct = br < 0 ? Math.round(lerp(80, 100, clamp((930 - py) / 240))) : br < .25 ? 100 + Math.round(br * 3000) : null;
    gloss(pfRR(1650, 250, 210, 120, 14), '#12121A', { box: [1650, 250, 210, 120], lw: 4, rim: EP.red });
    txt('FOAM', 1755, 272, 22, EP.red, { font: 'code' });
    if (pct === null) pixText(frac(t * 6) < .5 ? 'ERR' : '', 1755, 300, 9, EP.red, { align: 'center', glow: true }); else segText(String(Math.min(999, pct)).padStart(3, ' ') , 1678, 290, 64, pct >= 100 ? EP.red : EP.laser, { off: '#1A0404' });
    tokenAt(t, 340, 1040, 38, br > 0 ? 'jump' : 'pump', br > 0 ? { eyes: 'wide', mouth: 'scream' } : { hL: [-3.4, -9.4], gL: 'point' });
    // the flood: foam pours over the barrier toward us, higher and higher
    if (br > 0) {
      const fy = lerp(H + 120, -300, flood);
      const P = []; for (let i = 0; i < 26; i++) { const u = clamp(br / .5 - hash(i + 90) * .3), a = -Math.PI / 2 + (hash(i + 91) - .5) * 2.4, v = 900 + hash(i + 92) * 800; if (u <= 0) continue; P.push([W / 2 + (hash(i + 93) - .5) * 1400 + Math.cos(a) * v * u, 700 + Math.sin(a) * v * u + 1400 * u * u, 40 + u * 80]); }
      foamMass(P);
      foamBank(t, fy, { seed: 21, r: 90, nb: 12 });
    }
    camEnd();
    // FOAM.EXE: pops on "but", is swallowed by the foam
    const dk = clamp((t - CUT.contain) / .12);
    if (br < .35) {
      ctx.save(); ctx.translate(0, br > 0 ? easeIn(clamp(br / .35)) * 500 : 0); if (br > 0) { ctx.translate(600, 380); ctx.rotate(br * 1.4); ctx.translate(-600, -380); }
      const out = win98Dialog(600, 380, 820, 'FOAM.EXE', 'Foam level exceeds maximum.\nPlease stop the party.', { icon: 'warn', buttons: ['OK'], k: dk, pressed: t > tc && t < tc + .15 ? 0 : undefined, size: 34 });
      ctx.restore();
      if (dk >= 1 && br < 0) { const [bx, by2, bw, bh] = out.buttons[0] ?? [515, 450, 170, 56], target = [bx + bw * .55, by2 + bh * .6], c0 = [1700, 900]; const cp = kf(t, [[CUT.contain + .1, c0], [tc - .05, target]], ease); cursor98(cp[0], cp[1], { click: t > tc ? (t - tc) / .3 : 0 }); }
    }
    // the camera is swallowed: giant suds on the lens
    if (t > tit - .15) { const u = clamp((t - tit + .15) / .5); const P = []; for (let i = 0; i < 14; i++) { const k = clamp(u * 1.6 - hash(i + 120) * .6); if (k <= 0) continue; P.push([hash(i + 121) * W, hash(i + 122) * H, 120 + k * (260 + hash(i + 123) * 240)]); } foamMass(P, { shade: '#C8D8F4', rim: '#FFD0EC' }); for (let i = 0; i < 5; i++) soapBubble(hash(i + 130) * W, hash(i + 131) * H, 160 + hash(i + 132) * 200, u); }
    if (br > 0 && br < .12) fx({ rgb: 1 - br / .12 });
    if (t > tit && t < tit + .12) fx({ rgb: .8, zoom: .6 });
    strobe(br > 0 && t < tit + .5 ? strobeK(t, 2, .3) * .3 : 0);
    if (t - CUT.contain < .1) cutFX('rgb');
  }

  // =====================================================================================================
  // G. The tail, "Moat, moat, moat, moat…": the foam pops away, and the club's neon sign stutters MOLT… on every hit (BOOK stays dark), a
  // notch closer each time, into V3.1's MOLTBOOK door.
  // =====================================================================================================
  function neon(str, x, y, size, col, on = 1, o = {}) {
    ctx.save(); ctx.translate(x, y);
    ctx.font = `${size}px "${FONTS[o.font ?? 'shrikhand']}"`; ctx.textAlign = o.align ?? 'center'; ctx.textBaseline = 'middle'; ctx.lineJoin = 'round'; ctx.lineCap = 'round';
    ctx.strokeStyle = mixCol(shade(col, .7), '#302040', .4); ctx.lineWidth = size * .085; ctx.strokeText(str, 0, 0);
    if (on > 0) {
      ctx.globalCompositeOperation = 'lighter';
      ctx.strokeStyle = alpha(col, .14 * on); ctx.lineWidth = size * .5; ctx.strokeText(str, 0, 0);
      ctx.strokeStyle = alpha(col, .3 * on); ctx.lineWidth = size * .22; ctx.strokeText(str, 0, 0);
      ctx.strokeStyle = alpha(col, on); ctx.lineWidth = size * .085; ctx.strokeText(str, 0, 0);
      ctx.strokeStyle = alpha('#FFFFFF', .8 * on); ctx.lineWidth = size * .028; ctx.strokeText(str, 0, 0);
    }
    ctx.restore();
  }
  const moltLine = { text: 'Molt… molt… molt… molt… molt…', sec: 'V3', n: 0 };
  function shotTail(t) {
    hideCaption();
    const i = MOLTS.reduce((a, d, j) => t >= d ? j : a, -1), hit = MOLTS[i], a = t - hit, first = t - MOLTS[0];
    const z = 1 + i * .04 + Math.max(0, .05 - a) * 1.2;
    camBegin(W / 2, H / 2, z);
    // the club wall
    fillAll('#12041F');
    for (let j = 0; j * 56 < H + 200; j++) for (let q = -1; q * 150 < W + 200; q++) { const x = q * 150 + (j % 2) * 75 - 60, y = j * 56 - 60; ctx.fillStyle = mixCol('#3A1060', '#000000', hash2(q, j) * .35); rrect(x + 4, y + 4, 142, 48, 6); ctx.fill(); }
    ctx.fillStyle = rg(W / 2, 470, 0, 900, [[0, 'rgb(255 40 180 / .18)'], [1, 'rgb(0 0 0 / .5)']]); ctx.fillRect(-100, -100, W + 200, H + 200);
    // the sign: MOLT lights on every hit and buzzes down; BOOK stays dark
    const size = 230, font = 'shrikhand'; ctx.save(); ctx.font = `${size}px "${FONTS[font]}"`; const wM = ctx.measureText('Molt').width, wB = ctx.measureText('book').width; ctx.restore();
    const x0 = W / 2 - (wM + wB) / 2, on = a < .05 ? 1 : lerp(1, .3, clamp((a - .05) / .25)) * (hash(Math.floor(t * 40)) > .15 ? 1 : .4);
    gloss(pfRR(x0 - 70, 300, wM + wB + 140, 310, 40), '#10041A', { box: [x0 - 70, 300, wM + wB + 140, 310], lw: 6, rim: EP.magenta, rimK: .7, rimW: .012, spec: .15, hi: .12 });
    neon('Molt', x0, 450, size, EP.magenta, on, { align: 'left' }); neon('book', x0 + wM, 450, size, EP.magenta, i === MOLTS.length - 1 && a > .04 ? .35 * (hash(Math.floor(t * 50)) > .5 ? 1 : 0) : 0, { align: 'left' });
    neon('agents only', W / 2, 680, 70, EP.cyan, i === MOLTS.length - 1 ? .8 : .12, { font: 'bungee' });
    if (a < .06) { for (let q = 0; q < 8; q++) { const ang = hash2(q, i) * TAU; ctx.strokeStyle = EP.yellow; ctx.lineWidth = 4; ctx.beginPath(); ctx.moveTo(x0 + wM * .9, 330); ctx.lineTo(x0 + wM * .9 + Math.cos(ang) * 70, 330 + Math.sin(ang) * 70); ctx.stroke(); } }
    camEnd();
    // the foam that swallowed the camera, popping away from the middle out
    if (first < .5) { const u = first / .5, P = []; for (let q = 0; q < 40; q++) { const bx = hash(q + 200) * W, by = hash(q + 201) * H, d = Math.hypot(bx - W / 2, by - H / 2) / 1100; if (d < u * 1.2) continue; P.push([bx, by, 140 + hash(q + 202) * 160]); } foamMass(P); }
    for (let q = 0; q < 10; q++) { const y = H - frac(hash(q + 220) + t * .3) * 300, x = hash(q + 221) * W; soapBubble(x, y, 18 + hash(q + 222) * 26, .8); }
    if (a < .08) fx({ flash: .3 * (1 - a / .08) });
    // the stutter in the karaoke
    if (!moltLine._kt) moltLine._kt = { words: moltLine.text.split(' '), tm: MOLTS.map((s, j) => [s, j + 1 < MOLTS.length ? MOLTS[j + 1] : s + .12]) };
    karaokeLine({ ...moltLine, start: MOLTS[0], end: MOLTS.at(-1) + .1, _kt: moltLine._kt }, t, { singer: 'token' });
  }

  section('C2', (p, lt, d, t) => {
    if (t < CUT.train) return shotHook1(t);
    if (t < CUT.curves) return shotTrain(t);
    if (t < CUT.hook2) return shotCurves(t);
    if (t < CUT.no) return shotHook2(t);
    if (t < CUT.contain) return shotNo(t);
    if (!MOLTS.length || t < MOLTS[0]) return shotContain(t);
    return shotTail(t);
  });
})();

;
// ---- styles/eurodance/ch/c06_v3.js ----
// c06_v3 — Verse 3: Jan → Aug 2026, "the night shift". Sixteen headlines, MC TOKEN on the mic, weirder and darker club nights. Consecutive shots
// flip their dominant colour and composition:
// UV club door / black-and-gold record wall / Win98 teal / blossom-pink park / hot-magenta concert / navy office / black Mystify /
// fireworks gold / acid-green data city / lilac line-up / casino red / Y2K midnight silver / cyan chroma-key set / party orange /
// purple DJ stage / magenta sunset (the V1.3 callback).
(() => {
  const bt = (t, lt, k = 0) => beatIn(t, lt, k);
  const pop = (lt, t0, dur = .18) => lt < t0 ? 0 : backOut(clamp((lt - t0) / dur), 2.2);
  const tok = t => ({ talk: singK(t) });
  // the lyric's own word times (this take's alignment), e.g. wordAt(seg, 'pseudonym')
  const wordAt = (seg, w, nth = 0) => { const ln = LINES.find(l => l.sec === seg.sec && l.n === seg.n); if (!ln) return null; const { words, tm } = _karaTimes(ln); let k = 0; for (let i = 0; i < words.length; i++) if (words[i].toLowerCase().replace(/[^a-z0-9]/g, '').startsWith(w)) { if (k++ === nth) return tm[i][0] - seg.start; } return null; };
  // a rubber-stamp slam (EXPORT BAN): double border, block letters, scaling down from 1.9× as it lands
  function slamStamp(str, x, y, size, col, rot, k) {
    if (k <= 0) return; const s = k < 1 ? lerp(1.9, 1, easeOut(k)) : 1, w = textW(str, size, 'archivo', 2) + size * .9, h = size * 1.5;
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot); ctx.scale(s, s); ctx.globalAlpha *= clamp(k * 3) * .92;
    ctx.strokeStyle = col; ctx.lineWidth = size * .1; rrect(-w / 2, -h / 2, w, h, size * .2); ctx.stroke(); ctx.lineWidth = size * .04; rrect(-w / 2 + size * .16, -h / 2 + size * .16, w - size * .32, h - size * .32, size * .12); ctx.stroke();
    txt(str, 0, size * .05, size, col, { font: 'archivo', spacing: 2 });
    ctx.restore();
  }
  function confetti(t, t0, n = 60, o = {}) {
    if (t < t0) return; const cols = o.cols ?? [EP.magenta, EP.cyan, EP.yellow, EP.lime, EP.white];
    for (let i = 0; i < n; i++) { const age = t - t0, x = (o.x0 ?? 0) + hash2(i, 1) * ((o.x1 ?? W) - (o.x0 ?? 0)) + Math.sin(age * 3 + i) * 30, y = (o.y0 ?? -60) - hash2(i, 2) * 300 + age * (260 + hash2(i, 3) * 200); if (y > H + 40) continue; const r = age * 6 + i; ctx.save(); ctx.translate(x, y); ctx.rotate(r); ctx.scale(1, Math.cos(r * 1.3)); ctx.fillStyle = cols[i % cols.length]; ctx.fillRect(-9, -5, 18, 10); ctx.restore(); }
  }
  // neon tubing lettering: a dark tube when off, glowing when on (0..1)
  function neon(str, x, y, size, col, on = 1, o = {}) {
    ctx.save(); ctx.translate(x, y); if (o.rot) ctx.rotate(o.rot);
    ctx.font = `${size}px "${FONTS[o.font ?? 'shrikhand']}"`; ctx.textAlign = o.align ?? 'center'; ctx.textBaseline = 'middle'; ctx.lineJoin = 'round'; ctx.lineCap = 'round';
    ctx.strokeStyle = mixCol(shade(col, .7), '#302040', .4); ctx.lineWidth = size * .085; ctx.strokeText(str, 0, 0);
    if (on > 0) {
      ctx.globalCompositeOperation = 'lighter';
      ctx.strokeStyle = alpha(col, .14 * on); ctx.lineWidth = size * .5; ctx.strokeText(str, 0, 0);
      ctx.strokeStyle = alpha(col, .3 * on); ctx.lineWidth = size * .22; ctx.strokeText(str, 0, 0);
      ctx.strokeStyle = alpha(col, on); ctx.lineWidth = size * .085; ctx.strokeText(str, 0, 0);
      ctx.strokeStyle = alpha('#FFFFFF', .8 * on); ctx.lineWidth = size * .028; ctx.strokeText(str, 0, 0);
    }
    ctx.restore();
  }
  // a dark brick wall (cached per colour)
  function bricks(col, mortar, key) {
    const img = cached('v3bricks|' + key, W + 200, H + 200, (w, h) => {
      ctx.fillStyle = mortar; ctx.fillRect(0, 0, w, h);
      for (let j = 0; j * 56 < h; j++) for (let i = -1; i * 150 < w; i++) { const x = i * 150 + (j % 2) * 75, y = j * 56; ctx.fillStyle = mixCol(col, '#000000', hash2(i, j) * .35); rrect(x + 4, y + 4, 142, 48, 6); ctx.fill(); ctx.fillStyle = 'rgb(255 255 255 / .05)'; ctx.fillRect(x + 8, y + 7, 130, 6); }
    });
    blit(img, W / 2, H / 2);
  }

  // =====================================================================================
  // V3.1 Moltbook: no humans allowed — the MOLTBOOK club door (the neon sign from the C2 tail): a bouncer agent turns a human away at the
  // velvet rope (NO HUMANS), while agents dance inside under a lobster-shaped mirror ball; the human settles for observing.
  function lobsterBall(x, y, r, t) {
    for (const sd of [-1, 1]) {
      ctx.save(); ctx.translate(x + sd * r * .9, y + r * .1); ctx.rotate(sd * (.5 + .15 * Math.sin(t * 6)));
      gloss(pfCap(0, 0, sd * r * .55, -r * .35, r * .14), '#A8B0C4', { box: [-r * .6, -r * .6, r * 1.2, r * 1.2], rim: EP.magenta, lw: 3 });
      gloss(() => { ctx.moveTo(sd * r * .45, -r * .3); ctx.quadraticCurveTo(sd * r * 1.25, -r * .9, sd * r * .75, -r * 1.2); ctx.quadraticCurveTo(sd * r * .95, -r * .75, sd * r * .6, -r * .6); ctx.quadraticCurveTo(sd * r * .5, -r * 1.05, sd * r * .2, -r * .95); ctx.quadraticCurveTo(sd * r * .2, -r * .5, sd * r * .45, -r * .3); }, '#C8D0E0', { box: [-r * 1.3, -r * 1.3, r * 2.6, r * 1.2], rim: EP.magenta, lw: 3, spec: 1 });
      ctx.restore();
      ctx.strokeStyle = '#A8B0C4'; ctx.lineWidth = 3; ctx.beginPath(); ctx.moveTo(x + sd * r * .3, y - r * .9); ctx.quadraticCurveTo(x + sd * r * 1.2, y - r * 2.2, x + sd * r * 2.1, y - r * 1.6); ctx.stroke();
    }
    discoBall(x, y, r, t);
    for (const sd of [-1, 1]) { glossBall(x + sd * r * .32, y - r * .98, r * .13, r * .13, '#20202A', { rim: null, lw: 2 }); }
  }
  line('V3', 1, (p, lt, d, t) => {
    const b1 = bt(t, lt, 1), b2 = bt(t, lt, 2), bb = bpOf(t), stop = lt >= b1, obs = lt >= b2;
    setLight({ rim: EP.magenta, rimK: .85 });
    camBegin(W / 2, H / 2, 1 + .025 * p);
    bricks('#3A1060', '#12041F', 'uv');
    // inside the club, through the open door
    const dx = 700, dw = 460, dtop = 330, dbot = 905;
    ctx.save(); rrect(dx - dw / 2, dtop, dw, dbot - dtop, 14); ctx.clip();
    fillAll('#08020F');
    laserFan(dx, dtop, t, { n: 7, cols: [EP.laser, EP.magenta], angle: Math.PI / 2, spread: 1.4, sweep: .5, alpha: .55, len: 900 });
    for (let i = 0; i < 5; i++) { const x = dx - 180 + i * 90, ph = bb * 2 + i * .5; agentBot(x, 900 - Math.abs(Math.sin(ph * Math.PI)) * 18, 22 + (i % 2) * 3, { col: [CANDY.bondi, CANDY.lime, CANDY.grape, CANDY.strawberry, CANDY.tangerine][i], walk: ph * .5, eyes: i % 2 ? 'happy' : 'star', rot: Math.sin(ph * Math.PI) * .12 }); }
    lobsterBall(dx, dtop + 150, 62, t);
    ctx.restore();
    gloss(() => { const x0 = dx - dw / 2 - 26, y0 = dtop - 26, x1 = dx + dw / 2 + 26, y1 = dbot + 4; ctx.moveTo(x0, y0); ctx.lineTo(x1, y0); ctx.lineTo(x1, y1); ctx.lineTo(x0, y1); ctx.closePath(); ctx.moveTo(dx - dw / 2, dtop); ctx.lineTo(dx - dw / 2, dbot); ctx.lineTo(dx + dw / 2, dbot); ctx.lineTo(dx + dw / 2, dtop); ctx.closePath(); }, '#8A90A8', { box: [dx - dw / 2 - 26, dtop - 26, dw + 52, dbot - dtop + 30], lw: 4, spec: .8 });
    ctx.fillStyle = '#0C0418'; ctx.fillRect(-100, 905, W + 200, 300); ctx.fillStyle = lg(0, 905, 0, 1000, [[0, alpha(EP.magenta, .35)], [1, alpha(EP.magenta, 0)]]); ctx.fillRect(-100, 905, W + 200, 95);
    // the sign (fully lit on the downbeat, continuing the C2 tail)
    const fl = lt < .08 ? .5 + .5 * Math.sin(lt * 200) : 1;
    neon('Moltbook', dx, 185, 150, EP.magenta, fl);
    neon('agents only', dx, 270, 44, EP.cyan, 1, { font: 'bungee' });
    // velvet rope
    for (const sx of [dx - 250, dx + 250]) { gloss(pfRR(sx - 9, 760, 18, 150, 8), '#C8CCD8', { box: [sx - 9, 760, 18, 150], lw: 3, spec: 1 }); glossBall(sx, 752, 22, 22, EP.gold, { lw: 3 }); gloss(pfEll(sx, 908, 44, 12), '#9AA0B4', { box: [sx - 44, 896, 88, 24], lw: 3 }); }
    ctx.lineCap = 'round'; ctx.beginPath(); ctx.moveTo(dx - 240, 770); ctx.quadraticCurveTo(dx, 880 + Math.sin(t * 3) * 6, dx + 240, 770); ctx.strokeStyle = EP.line; ctx.lineWidth = 26; ctx.stroke(); ctx.strokeStyle = '#C0102A'; ctx.lineWidth = 18; ctx.stroke(); ctx.strokeStyle = 'rgb(255 160 170 / .5)'; ctx.lineWidth = 5; ctx.stroke();
    // the bouncer: a big graphite agent in shades
    const bx = 1090, by = 925, bs = 118, lean = stop ? -.08 * (1 - clamp((lt - b1 - .3) / .3)) : 0;
    ctx.save(); ctx.translate(bx, by); ctx.rotate(lean); agentBot(0, 0, bs, { col: CANDY.graphite, face: '' }); ctx.restore();
    ctx.save(); ctx.translate(bx, by); ctx.rotate(lean); ctx.scale(bs, bs);
    ctx.fillStyle = '#05050A'; rrect(-.85, -2.62, 1.7, .42, .18); ctx.fill(); ctx.fillStyle = 'rgb(160 200 255 / .45)'; ctx.fillRect(-.7, -2.56, .5, .08);
    ptext(stop ? 'NO.' : '>_', 0, -1.95, .42, { font: 'code', fill: stop ? EP.red : '#AFFFF0' });
    ptext('SECURITY', 0, -1.1, .34, { font: 'archivo', fill: EP.white, strokes: [[EP.line, .08]] });
    ctx.restore();
    // NO HUMANS: the sign lights on the beat
    const sk = pop(lt, b1, .16), sx0 = 1370;
    gloss(pfRR(sx0 - 7, 470, 14, 440, 6), '#6A6E84', { box: [sx0 - 7, 470, 14, 440], lw: 3 });
    ctx.save(); ctx.translate(sx0, 420); ctx.scale(lerp(.6, 1, sk), lerp(.6, 1, sk));
    gloss(pfRR(-170, -70, 340, 140, 18), '#140614', { box: [-170, -70, 340, 140], lw: 5, rim: EP.red, spec: .4 });
    neon('NO HUMANS', 0, -2, 62, EP.red, lt < b1 ? .08 : (frac(t * 7) < .85 ? 1 : .55), { font: 'bungee' });
    ctx.restore();
    if (obs) { const k = pop(lt, b2, .16); ctx.save(); ctx.translate(sx0 - 10, 540); ctx.rotate(-.04); ctx.scale(k, k); ctx.strokeStyle = '#C8CCD8'; ctx.lineWidth = 4; ctx.beginPath(); ctx.moveTo(-120, -80); ctx.lineTo(-120, -40); ctx.moveTo(120, -80); ctx.lineTo(120, -40); ctx.stroke(); rrect(-185, -44, 370, 88, 8); paint('#F4EEDC', EP.line, 5); txt('Humans welcome', 0, -14, 34, '#2A1A3A', { font: 'archivo', maxW: 340 }); txt('to observe.', 0, 22, 30, '#2A1A3A', { font: 'archivo' }); ctx.restore(); }
    // the human: walks up, is stopped, settles for binoculars
    const hx = stop ? 1700 + (1 - easeOut(clamp((lt - b1) / .25))) * -110 : lerp(1800, 1590, easeOut(clamp(lt / b1))), walkPh = stop ? 0 : lt * 5;
    const bino = s => { for (const sd of [-1, 1]) { gloss(pfRR(sd * s * .45 - s * .3, -s * .55, s * .6, s * .9, s * .2), '#1C1C24', { box: [sd * s * .45 - s * .3, -s * .55, s * .6, s * .9], lw: 3 }); glossBall(sd * s * .45, -s * .55, s * .28, s * .12, '#6AB8FF', { lw: 2, rim: null }); } };
    toy(hx, 950, 46, { hair: 'side', hairCol: THAIR.brown, top: 'shirt', topCol: '#E8A23A', pants: '#3A4A6A', skin: 1, turn: -.45, fL: [Math.sin(walkPh * Math.PI) * .4, -Math.max(0, Math.sin(walkPh * Math.PI)) * .5], fR: [-Math.sin(walkPh * Math.PI) * .4, -Math.max(0, -Math.sin(walkPh * Math.PI)) * .5],
      ...(obs ? { hL: [-.55, -8.3], hR: [.55, -8.3], gL: 'fist', gR: 'fist', hold: s => { ctx.translate(-s * .55, s * .1); bino(s); }, eyes: 'closed', mouth: 'smile' } : stop ? { hL: [-2.4, -8.6], hR: [2.4, -8.6], gL: 'flat', gR: 'flat', eyes: 'wide', mouth: 'O', sweat: 1 } : { eyes: 'happy', mouth: 'grin', hL: [-2.3, -4.2], hR: [2.3, -4.2] }) });
    camEnd();
    if (lt >= b1 && lt < b1 + .09) fx({ rgb: .6 });
  });

  // =====================================================================================
  // V3.2 OpenClaw — the lobster's proud: a glossy lobster vogues on a turning chrome pedestal; its shed shells hang framed like platinum records
  // (CLAWDBOT, MOLTBOT), lighting up one per beat; then OPENCLAW slams in red chrome. "Some things are sacred." on the plaque.
  function lobster(x, y, s, o = {}) {
    const col = o.col ?? '#E8341C', rim = o.rim, flat = !!o.flat, L = o.line ?? EP.line, sp = flat ? .2 : .8;
    const G = (pf, c, box, x2 = {}) => gloss(pf, c, { box, lw: .09, line: L, spec: sp, rim, ...x2 });
    ctx.save(); ctx.translate(x, y); ctx.scale(s, s); if (o.rot) ctx.rotate(o.rot);
    // antennae
    ctx.strokeStyle = shade(col, .2); ctx.lineWidth = .12; ctx.lineCap = 'round';
    for (const sd of [-1, 1]) { const w = Math.sin((o.ph ?? 0) * 3 + sd) * .6; ctx.beginPath(); ctx.moveTo(sd * .35, -8.3); ctx.bezierCurveTo(sd * 1.2, -10.5, sd * (3 + w), -11.5, sd * (4.4 + w), -10.2); ctx.stroke(); }
    // tail fan + abdomen
    for (let i = -2; i <= 2; i++) G(pfEll(i * .62, -.35, .42, .7, i * .35), shade(col, .08), [-1.6, -1.1, 3.2, 1.4]);
    for (let i = 3; i >= 0; i--) { const yy = -1.1 - i * .78, w = 1.25 + i * .14; G(pfRR(-w, yy - .7, w * 2, .95, .45), col, [-w, yy - .7, w * 2, .95]); }
    // legs
    ctx.strokeStyle = L; ctx.lineWidth = .16; for (const sd of [-1, 1]) for (let i = 0; i < 3; i++) { ctx.beginPath(); ctx.moveTo(sd * 1.2, -4.4 - i * .35); ctx.lineTo(sd * 2.0, -3.9 - i * .35 + (o.ph ? Math.sin(o.ph * 6 + i) * .15 : 0)); ctx.lineTo(sd * 2.2, -3.2 - i * .3); ctx.stroke(); }
    // arms + claws
    for (const [sd, h, open] of [[-1, o.cL ?? [-3.2, -8.4], o.openL ?? .3], [1, o.cR ?? [3.2, -8.4], o.openR ?? .3]]) {
      G(pfCap(sd * 1.1, -6.4, lerp(sd * 1.1, h[0], .55), lerp(-6.4, h[1], .55) + .5, .38), shade(col, .05), [-4, -10, 8, 6]);
      G(pfCap(lerp(sd * 1.1, h[0], .55), lerp(-6.4, h[1], .55) + .5, h[0], h[1], .34), shade(col, .05), [-4, -10, 8, 6]);
      const a = Math.atan2(h[1] - (-6.4), h[0] - sd * 1.1);
      ctx.save(); ctx.translate(h[0], h[1]); ctx.rotate(a);
      G(pfEll(.9, 0, 1.15, .78), col, [-.3, -.8, 2.4, 1.6]);
      ctx.save(); ctx.translate(1.6, -.25); ctx.rotate(-open * .6); G(pfPts([[0, -.35], [1.5, -.28], [2.1, .05], [1.3, .12], [0, .3]]), col, [0, -.4, 2.1, .7]); ctx.restore();
      ctx.save(); ctx.translate(1.6, .3); ctx.rotate(open * .6); G(pfPts([[0, -.28], [1.2, -.12], [1.8, .1], [1.0, .32], [0, .32]]), shade(col, .08), [0, -.3, 1.8, .7]); ctx.restore();
      ctx.restore();
    }
    // carapace + head
    G(pfEll(0, -6.0, 1.55, 2.05), col, [-1.55, -8.05, 3.1, 4.1], { hi: .4 });
    G(pfPts([[-.6, -7.7], [0, -9.0], [.6, -7.7]]), col, [-.6, -9, 1.2, 1.3]);
    if (!flat) {
      for (const sd of [-1, 1]) { ctx.strokeStyle = L; ctx.lineWidth = .14; ctx.beginPath(); ctx.moveTo(sd * .35, -7.6); ctx.lineTo(sd * .6, -8.35); ctx.stroke(); glossBall(sd * .62, -8.5, .32, .32, '#15101C', { rim: null, lw: .06, line: L }); ctx.fillStyle = '#FFF'; ell(sd * .62 - .1, -8.62, .1, .1); ctx.fill(); }
      ctx.strokeStyle = shade(col, .5); ctx.lineWidth = .12; ctx.beginPath(); ctx.arc(0, -6.9, .45, .25, Math.PI - .25); ctx.stroke();
      if (o.blush) { ctx.fillStyle = 'rgb(255 190 200 / .7)'; ell(-.9, -6.8, .3, .15); ctx.fill(); ell(.9, -6.8, .3, .15); ctx.fill(); }
    }
    ctx.restore();
  }
  line('V3', 2, (p, lt, d, t) => {
    const b0 = bt(t, lt, 0), b1 = bt(t, lt, 1), b2 = bt(t, lt, 2), bb = bpOf(t);
    setLight({ rim: EP.gold, rimK: .8 });
    bgGrad([[0, '#050308'], [.7, '#1A1206'], [1, '#3A2408']]);
    rays(W / 2, 700, 22, 'rgb(255 200 90 / .06)', t * .15);
    // spotlights
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; for (const [x, c, k] of [[W / 2, '255 230 170', .3], [330, '255 255 255', lt >= b0 ? .22 : 0], [1590, '255 255 255', lt >= b1 ? .22 : 0]]) { if (!k) continue; ctx.fillStyle = lg(0, 0, 0, 900, [[0, `rgb(${c} / ${k})`], [1, `rgb(${c} / 0)`]]); poly([[x - 50, -20], [x + 50, -20], [x + 260, 900], [x - 260, 900]]); ctx.fill(); } ctx.restore();
    // the framed shells
    [[330, 'CLAWDBOT', b0], [1590, 'MOLTBOT', b1]].forEach(([fx0, name, on], i) => {
      const lit = lt >= on, k = pop(lt, on, .2), y0 = 250;
      gloss(pfRR(fx0 - 180, y0, 360, 440, 10), EP.gold, { box: [fx0 - 180, y0, 360, 440], lw: 5, rim: null, spec: 1 });
      ctx.fillStyle = '#12101A'; ctx.fillRect(fx0 - 150, y0 + 30, 300, 380);
      cdDisc(fx0 + 40, y0 + 200, 120, t * .4 + i, { col: '#E8ECF4', label: 'PLATINUM' });
      lobster(fx0 - 30, y0 + 360, 25, { col: lit ? '#E8ECF4' : '#8A8E9A', flat: true, rot: -.1, line: '#3A3E4A' });
      rrect(fx0 - 120, y0 + 450, 240, 48, 6); paint('#2A2410', EP.gold, 3); txt(name, fx0, y0 + 475, 30, EP.gold, { font: 'archivo', maxW: 220 });
      if (k > 0) glint(fx0 + 110, y0 + 90, 100 * Math.sin(clamp((lt - on) / .4) * Math.PI), Math.sin(clamp((lt - on) / .4) * Math.PI));
    });
    // the turning pedestal
    const px = W / 2, py = 850;
    gloss(() => { ctx.moveTo(px - 260, py); ctx.ellipse(px, py, 260, 50, 0, Math.PI, 0, true); ctx.lineTo(px + 260, py + 60); ctx.ellipse(px, py + 60, 260, 50, 0, 0, Math.PI); ctx.closePath(); }, '#C8D0E4', { box: [px - 260, py - 50, 520, 160], rim: EP.gold, lw: 5, spec: 1 });
    ell(px, py, 260, 50); ctx.fillStyle = lg(px - 260, 0, px + 260, 0, [[0, '#8A94B8'], [.5, '#FFFFFF'], [1, '#8A94B8']]); ctx.fill(); ctx.strokeStyle = EP.line; ctx.lineWidth = 4; ctx.stroke();
    for (let i = 0; i < 10; i++) { const a = i / 10 * TAU + t * 1.6; if (Math.sin(a) < 0) continue; ctx.fillStyle = [EP.gold, '#FFFFFF'][i % 2]; ell(px + Math.cos(a) * 260, py + 30 + Math.sin(a) * 50, 10, 6); ctx.fill(); }
    rrect(px - 210, py + 62, 420, 50, 8); paint(EP.gold, EP.line, 4); txt('"Some things are sacred."', px, py + 88, 32, '#3A2A00', { font: 'abril', maxW: 390 });
    // the lobster vogues: a new pose per beat
    const P = [[[-3.4, -7.4], [3.4, -7.4]], [[-2.2, -11.0], [3.6, -6.4]], [[-3.6, -6.4], [2.0, -11.2]], [[-2.4, -11.2], [2.4, -11.2]]], pi = lt < b0 ? 0 : lt < b1 ? 1 : lt < b2 ? 2 : 3, pose = P[pi];
    const sq = kick(t, 7) * .03, proud = lt >= b2;
    ctx.save(); ctx.translate(px, py + 4); ctx.scale(1 + sq, 1 - sq); ctx.translate(-px, -(py + 4));
    lobster(px, py + 4, 52, { cL: pose[0], cR: pose[1], openL: .2 + .3 * bounce(t), openR: .5 - .3 * bounce(t), ph: bb, blush: proud ? 1 : 0, rim: EP.gold, rot: Math.sin(bb * Math.PI) * .03 });
    ctx.restore();
    if (proud) { const k = clamp((lt - b2) / .12); chromeText('OPENCLAW', W / 2, 170, 150, { style: 'red', italic: .14, depth: 16, s: lerp(1.9, 1, easeOut(k)), alpha: clamp(k * 3) }); lensFlare(W / 2 + 330, 150, .6 * (1 - clamp((lt - b2) / .5))); sparkles(t, { n: 10, seed: 22, x0: 600, x1: 1320, y0: 250, y1: 800, r: 40, col: EP.gold }); }
  });

  // =====================================================================================
  // V3.3 Mythos Preview slips its jail — a Windows window titled "sandbox" holds a literal sandbox. The MYTHOS candy computer (sly eyes) climbs
  // out over the window frame, hops across the desktop and dives into the Internet icon. Status: CONTAINED → uh-oh.
  line('V3', 3, (p, lt, d, t) => {
    const b1 = bt(t, lt, 1), b2 = bt(t, lt, 2), b3 = bt(t, lt, 3);
    const gx = 1640, gy = 470, into = lt >= b3;
    desktop98({ icons: [['computer', 'My Computer', 130, 190], ['bin', 'Recycle Bin', 130, 380], ['doc', 'system card.pdf', 130, 570]] });
    // the Internet icon, big
    const gk = into ? pop(lt, b3, .2) : 0;
    ctx.save(); ctx.translate(gx, gy); ctx.scale(2.6 + gk * .4, 2.6 + gk * .4); icon98('globe', 0, 0, 1); ctx.restore();
    if (into) { glow(gx, gy, 260, EP.cyan, .6 * (1 - clamp((lt - b3) / .5))); ctx.strokeStyle = alpha(EP.white, 1 - clamp((lt - b3) / .4)); ctx.lineWidth = 6; ell(gx, gy, 80 + (lt - b3) * 400, 80 + (lt - b3) * 400); ctx.stroke(); }
    txt('Internet', gx, gy + 118, 34, '#FFFFFF', { font: 'archivo', shadow: [2, 2], shadowCol: 'rgb(0 0 0 / .6)' });
    // the window
    const wx = 300, wy = 180, ww = 1000, wh = 700, esc = lt >= b1;
    const cr = win98Window(wx, wy, ww, wh, 'sandbox', (cw, ch) => {
      ctx.fillStyle = '#F2D48A'; ctx.fillRect(0, 0, cw, ch);
      ctx.fillStyle = 'rgb(160 110 40 / .25)'; for (let i = 0; i < 160; i++) { ell(hash2(i, 1) * cw, hash2(i, 2) * ch, 3, 2); ctx.fill(); }
      // the wooden sandbox rim
      gloss(pfRR(20, ch - 130, cw - 40, 40, 6), '#B8742A', { box: [20, ch - 130, cw - 40, 40], lw: 4, rim: null });
      // bucket + spade + castle
      gloss(pfPts([[90, 330], [210, 330], [190, 480], [110, 480]]), EP.red, { box: [90, 330, 120, 150], lw: 4, rim: null, spec: .9 });
      ctx.strokeStyle = EP.line; ctx.lineWidth = 5; ctx.beginPath(); ctx.arc(150, 330, 60, Math.PI, 0); ctx.stroke();
      gloss(pfPts([[760, 470], [900, 470], [900, 380], [870, 380], [870, 400], [845, 400], [845, 380], [815, 380], [815, 400], [790, 400], [790, 380], [760, 380]]), '#E8B85A', { box: [760, 380, 140, 90], lw: 4, rim: null });
      ctx.save(); ctx.translate(300, 470); ctx.rotate(-.5); gloss(pfRR(-8, -120, 16, 110, 6), EP.cyan, { box: [-8, -120, 16, 110], lw: 3, rim: null }); gloss(pfPts([[-40, -10], [40, -10], [30, 50], [-30, 50]]), EP.cyan, { box: [-40, -10, 80, 60], lw: 3, rim: null }); ctx.restore();
      if (!esc) gumdrop(cw / 2 + 40, ch - 150, 34, { col: CANDY.tangerine, label: 'MYTHOS', face: 'sly', mouth: 'smile', look: [.4, -.2], hL: [-4.4, -6.2], gL: 'open', hR: [2.6, -4.2], gR: 'point', dy: -bounce(t) * .3 });
    }, { icon: 'folder', menu: ['File', 'Edit', 'View', 'Help'], client: '#F2D48A' });
    // status bar under the window
    const st = esc ? 'Status: ...uh-oh' : 'Status: CONTAINED';
    bevel(wx, wy + wh + 4, ww, 50, { sunken: true }); txt(st, wx + 24, wy + wh + 30, 28, esc ? EP.red : '#000', { font: 'archivo', align: 'left' });
    // the escape: onto the frame, across the desktop, into the globe
    if (esc && !into) {
      let x, y, rot = 0, s = 34;
      if (lt < b2) { const u = clamp((lt - b1) / .2); x = lerp(wx + ww / 2 + 40, wx + ww + 10, easeOut(u)); y = lerp(wy + wh - 160, wy + 470, easeOut(u)) - Math.sin(u * Math.PI) * 160; rot = u >= 1 ? .12 * Math.sin(lt * 18) : -.3 * u; }
      else { const u = clamp((lt - b2) / (b3 - b2)); x = lerp(wx + ww + 10, gx - 30, u); y = lerp(wy + 470, gy + 150, u) - Math.abs(Math.sin(u * Math.PI * 2)) * 150; s = lerp(34, 18, u); rot = u * .5; }
      gumdrop(x, y, s, { col: CANDY.tangerine, label: 'MYTHOS', face: 'sly', mouth: 'grin', hL: [-4.4, -8.8], hR: [4.4, -8.8], gL: 'wave', gR: 'wave', rot, shadow: false });
      for (let i = 1; i < 4; i++) { ctx.fillStyle = `rgb(255 255 255 / ${.4 - i * .1})`; ell(x - i * 40, y - 60 + i * 12, 20 - i * 4, 20 - i * 4); ctx.fill(); }
    }
    if (into) { const k = clamp((lt - b3) / .15); gumdrop(lerp(gx - 40, gx, k), lerp(gy + 60, gy, k), lerp(16, 2, k), { col: CANDY.tangerine, face: 'happy', hands: false, shadow: false, rot: k * 3 }); burst('ONLINE!', gx - 30, gy - 230, 90, { pop: pop(lt, b3 + .08, .15), col: EP.lime, ink: '#0A3A10', spin: .3 }); }
  });

  // =====================================================================================
  // V3.4 Sandwich in the park: new mail! — spring cherry blossoms, a researcher on a park bench takes a big bite; pigeons peck; then his
  // laptop fires a winged envelope from MYTHOS, the sandwich drops and the pigeons scatter.
  function pigeon(x, y, s, o = {}) {
    ctx.save(); ctx.translate(x, y); ctx.scale(s * (o.flip ? -1 : 1), s); ctx.rotate(o.rot ?? 0);
    const fly = o.fly ?? 0, fl = Math.sin(o.flap ?? 0);
    if (fly) { for (const k of [1, -1]) { ctx.save(); ctx.rotate(k * .1); gloss(pfPts([[-.2, -.6], [-1.4, -.6 - fl * 1.4 * k], [.4, -.4]]), '#7A8298', { box: [-1.4, -2, 1.8, 2], lw: .06, rim: null }); ctx.restore(); } }
    gloss(pfEll(0, -.55, .85, .5), '#8A92A8', { box: [-.85, -1.05, 1.7, 1], lw: .07, rim: null });
    gloss(pfPts([[-.7, -.6], [-1.4, -.85], [-1.3, -.4]]), '#5A6278', { box: [-1.4, -.9, .7, .5], lw: .06, rim: null });
    glossBall(.7, -1.05 + (o.peck ?? 0) * .5, .36, .34, '#6A7288', { lw: .06, rim: null });
    ctx.fillStyle = '#3ACA9A'; ell(.5, -.8, .22, .1); ctx.fill();
    ctx.fillStyle = '#000'; ell(.8, -1.12 + (o.peck ?? 0) * .5, .06, .06); ctx.fill(); ctx.fillStyle = EP.orange; poly([[1.02, -1.05 + (o.peck ?? 0) * .5], [1.25, -.98 + (o.peck ?? 0) * .5], [1.02, -.92 + (o.peck ?? 0) * .5]]); ctx.fill();
    if (!fly) { ctx.strokeStyle = EP.orange; ctx.lineWidth = .08; ctx.beginPath(); ctx.moveTo(-.1, -.1); ctx.lineTo(-.15, 0); ctx.moveTo(.2, -.1); ctx.lineTo(.2, 0); ctx.stroke(); }
    ctx.restore();
  }
  function sandwich(s, bite = 0) {
    ctx.save(); ctx.scale(s, s);
    gloss(pfRR(-1.2, -.7, 2.4, .5, .25), '#E8B060', { box: [-1.2, -.7, 2.4, .5], lw: .06, rim: null, spec: .4 });
    ctx.fillStyle = '#5ACA3A'; poly([[-1.3, -.2], [-.8, -.35], [-.3, -.18], [.2, -.35], [.7, -.18], [1.3, -.3], [1.2, -.05], [-1.2, -.05]]); ctx.fill();
    ctx.fillStyle = '#FF6A6A'; ctx.fillRect(-1.1, -.2, 2.2, .15); ctx.fillStyle = EP.yellow; ctx.fillRect(-1.15, -.08, 2.3, .1);
    gloss(pfRR(-1.2, 0, 2.4, .4, .2), '#E8B060', { box: [-1.2, 0, 2.4, .4], lw: .06, rim: null, spec: .3 });
    if (bite) { ctx.fillStyle = o_bg; for (let i = 0; i < 3; i++) { ell(1.25, -.4 + i * .35, .28, .22); ctx.fill(); } }
    ctx.restore();
  }
  let o_bg = '#FFF3A0';
  function blossomTree(x, y, s, t) {
    ctx.fillStyle = '#5A3A2A'; poly([[x - s * .12, y], [x + s * .12, y], [x + s * .06, y - s * .9], [x - s * .06, y - s * .9]]); ctx.fill();
    for (let i = 0; i < 9; i++) { const a = hash2(i, x) * TAU, r = s * (.25 + hash2(i, 2) * .35); glossBall(x + Math.cos(a) * r * 1.3, y - s * 1.15 + Math.sin(a) * r * .6, s * (.32 + hash2(i, 3) * .15), s * (.28 + hash2(i, 3) * .12), i % 3 ? '#FFB8D8' : '#FF9AC8', { line: false, rim: '#FFFFFF', rimK: .4, spec: .3 }); }
  }
  line('V3', 4, (p, lt, d, t) => {
    const b3 = bt(t, lt, 3), mail = lt >= b3, ma = lt - b3, bb = bpOf(t);
    setLight({ rim: '#FFFFFF', rimK: .35 });
    bgGrad([[0, '#8AD8FF'], [.55, '#D8F4FF'], [1, '#FFF3A0']], { y1: 640 });
    glow(1500, 200, 300, '#FFFFD0', .6);
    for (let i = 0; i < 3; i++) { const x = frac(hash(i + 3) + t * .01) * (W + 400) - 200, y = 150 + hash(i + 9) * 150; for (const [dx, dy, r] of [[-60, 10, 50], [0, -10, 70], [70, 8, 50]]) glossBall(x + dx, y + dy, r, r * .8, '#FFFFFF', { line: false, rim: null, spec: .2 }); }
    ctx.fillStyle = '#7ACA4A'; ctx.fillRect(-100, 640, W + 200, 500); ctx.fillStyle = '#9ADA5A'; for (let i = 0; i < 40; i++) { ell(hash2(i, 5) * W, 660 + hash2(i, 6) * 380, 30 + hash2(i, 7) * 40, 8); ctx.fill(); }
    ctx.fillStyle = '#E8D8B0'; poly([[800, 640], [1120, 640], [1500, 1080], [420, 1080]]); ctx.fill();
    blossomTree(260, 700, 300, t); blossomTree(1720, 690, 280, t);
    // falling petals
    for (let i = 0; i < 18; i++) { const y = frac(hash2(i, 1) + t * .15) * 900, x = hash2(i, 2) * W + Math.sin(t * 2 + i) * 40; ctx.fillStyle = '#FFB8D8'; ell(x, y, 8, 5, t * 2 + i); ctx.fill(); }
    // the bench
    const bx = 960, seat = 760;
    for (let i = 0; i < 3; i++) gloss(pfRR(bx - 380, 520 + i * 56, 760, 40, 8), '#B8743A', { box: [bx - 380, 520 + i * 56, 760, 40], lw: 4, rim: null });
    gloss(pfRR(bx - 400, seat, 800, 46, 10), '#A8642A', { box: [bx - 400, seat, 800, 46], lw: 4, rim: null });
    for (const sd of [-1, 1]) gloss(pfRR(bx + sd * 340 - 14, seat + 40, 28, 170, 6), '#3A3A44', { box: [bx + sd * 340 - 14, seat + 40, 28, 170], lw: 3, rim: null });
    // the laptop beside him
    const lx = 1180, ly = seat;
    gloss(pfPts([[lx - 130, ly], [lx + 130, ly], [lx + 150, ly - 14], [lx - 110, ly - 14]]), '#2A2A30', { box: [lx - 130, ly - 14, 280, 14], lw: 3, rim: null });
    gloss(pfRR(lx - 120, ly - 190, 240, 176, 10), '#2A2A30', { box: [lx - 120, ly - 190, 240, 176], lw: 4, rim: null });
    ctx.fillStyle = mail ? '#FFFFFF' : '#1A4A8A'; ctx.fillRect(lx - 104, ly - 176, 208, 148);
    if (!mail) { ctx.fillStyle = '#E8F0FF'; for (let i = 0; i < 5; i++) ctx.fillRect(lx - 90, ly - 160 + i * 24, 60 + hash(i) * 100, 8); }
    // the researcher
    const bites = [0, 1, 2].map(k => bt(t, lt, k)).filter(b => b <= lt), lb = bites.length ? lt - bites.at(-1) : 9, bite = lb < .3 ? Math.sin(clamp(lb / .3) * Math.PI) : 0, drop = mail ? clamp(ma / .5) : 0;
    const sandHold = s => { if (!mail) { ctx.rotate(-.1); sandwich(s * .9); } };
    toy(bx - 60, seat + 150, 50, { hair: 'curly', hairCol: THAIR.dkbrown, glasses: 'round', top: 'hoodie', topCol: '#5A7AB8', pants: '#3A3A4A', skin: 2, fL: [.4, 0], fR: [1.0, 0], turn: .25,
      hR: mail ? [2.9, -9.4] : [lerp(1.6, .9, bite), lerp(-6.4, -7.4, bite)], gR: mail ? 'open' : 'fist', hold: sandHold, hL: mail ? [-2.9, -9.4] : [-2.2, -4.6], gL: mail ? 'open' : 'open',
      eyes: mail ? 'wide' : 'closed', mouth: mail ? 'O' : (bite > .4 ? 'O' : 'smile'), jump: mail ? Math.sin(clamp(ma / .3) * Math.PI) * .7 : 0, emote: mail ? 'excl' : undefined, emoteK: pop(lt, b3), blush: mail ? 0 : .4, headTilt: mail ? 0 : Math.sin(lt * 14) * .04, bob: kick(t, 6) * .3 });
    if (!mail && lb < .35) { const u = lb / .35; pixText('NOM', bx + 110 + u * 30, seat - 470 - u * 60, 5, '#FFFFFF', { align: 'center', edge: EP.line, alpha: 1 - u }); }
    if (mail) { ctx.save(); ctx.translate(bx - 10 + drop * 40, lerp(seat - 330, seat + 180, easeIn(drop))); ctx.rotate(drop * 5); sandwich(48); ctx.restore(); }
    // pigeons: peck, then scatter
    [[520, 960, 1], [690, 1010, -1], [1380, 980, 1], [1560, 1000, -1]].forEach(([x, y, f], i) => {
      if (!mail) pigeon(x, y, 44, { flip: f < 0, peck: Math.max(0, Math.sin((bb + i * .37) * Math.PI * 2)) });
      else { const u = clamp(ma / .5); pigeon(x + f * u * 500 * (1 + i * .2), y - u * 700 * (1 + hash(i) * .5), 44, { flip: f < 0, fly: 1, flap: t * 40 + i, rot: -.3 * f }); }
    });
    if (mail) for (let i = 0; i < 6; i++) { const u = clamp(ma / .4), a = -Math.PI / 2 + (i - 2.5) * .5; ctx.fillStyle = '#C8CCD8'; ell(900 + Math.cos(a) * u * 300, 1000 + Math.sin(a) * u * 260, 12, 5, a); ctx.fill(); }
    // the envelope bursting out of the laptop
    if (mail) {
      const k = pop(ma, 0, .16), ex = lerp(lx, 1250, k), ey = lerp(ly - 100, 420, k), fl = Math.sin(t * 30);
      ctx.save(); ctx.translate(ex, ey); ctx.scale(k, k); ctx.rotate(-.06 + Math.sin(t * 5) * .04);
      for (const sd of [-1, 1]) { ctx.save(); ctx.scale(sd, 1); gloss(pfPts([[190, -30], [360, -150 - fl * 60], [330, -40], [390, -60 - fl * 40], [300, 30], [190, 40]]), '#FFFFFF', { box: [190, -210, 200, 250], lw: 5, rim: EP.cyan, spec: .6 }); ctx.restore(); }
      gloss(pfRR(-220, -140, 440, 280, 18), '#FFF8E0', { box: [-220, -140, 440, 280], lw: 6, rim: EP.orange, spec: .7 });
      ctx.strokeStyle = EP.line; ctx.lineWidth = 5; ctx.beginPath(); ctx.moveTo(-210, -130); ctx.lineTo(0, 30); ctx.lineTo(210, -130); ctx.stroke();
      glossBall(0, 30, 44, 44, EP.red, { lw: 4, rim: null }); txt('M', 0, 32, 44, '#FFE0D0', { font: 'abril' });
      txt('FROM: MYTHOS PREVIEW', 0, 105, 26, EP.line, { font: 'code' });
      ctx.restore();
      if (ma < .1) fx({ flash: .4 * (1 - ma / .1) });
    }
  });

  // =====================================================================================
  // V3.5 Fable 5 — who's not a fan? — the storybook FABLE 5 on stage in a pink spotlight; screaming fans with banners, and on "fan?" every
  // electric desk fan in the room swivels to face it and spins up; the pages flutter and it blushes.
  function storybook(x, y, s, o = {}) {
    ctx.save(); ctx.translate(x, y); ctx.scale(s, s); if (o.rot) ctx.rotate(o.rot); if (o.sq) ctx.scale(1 + o.sq * .5, 1 - o.sq);
    const w = 6, h = 8, col = o.col ?? CANDY.tangerine;
    // pages block (right edge) and flutter
    gloss(pfRR(-w / 2 + .3, -h - .1, w + .1, h, .3), '#FFF6E0', { box: [-w / 2, -h, w, h], lw: .08, rim: null, spec: .2 });
    ctx.strokeStyle = 'rgb(160 130 90 / .5)'; ctx.lineWidth = .04; for (let i = 0; i < 6; i++) { ctx.beginPath(); ctx.moveTo(w / 2 + .15, -h + .3 + i * .05); ctx.lineTo(w / 2 + .15, -.4 - i * .05); ctx.stroke(); }
    if (o.flutter) for (let i = 0; i < 3; i++) { const a = Math.sin(T * 18 + i * 2) * .5 + .6; ctx.save(); ctx.translate(-w / 2 + .3, -h / 2); ctx.scale(Math.cos(a) * -1, 1); gloss(pfRR(0, -h / 2 + .3, w - .2, h - .6, .2), '#FFFDF4', { box: [0, -h / 2, w, h], lw: .06, rim: null, spec: .1, alpha: .95 }); ctx.restore(); }
    // cover
    gloss(pfRR(-w / 2, -h, w, h, .35), col, { box: [-w / 2, -h, w, h], lw: .1, spec: .7, hi: .35, rim: o.rim });
    gloss(pfRR(-w / 2 - .15, -h, .8, h, .3), shade(col, .2), { box: [-w / 2 - .15, -h, .8, h], lw: .08, rim: null });
    ctx.strokeStyle = EP.gold; ctx.lineWidth = .12; rrect(-w / 2 + .9, -h + .45, w - 1.35, h - .9, .25); ctx.stroke();
    ptext('FABLE 5', .25, -h + 1.25, .95, { font: 'archivo', fill: EP.gold, strokes: [[shade(col, .5), .22]] });
    // face
    const eyes = o.eyes ?? 'dot', ey = -h + 3.6;
    for (const sd of [-1, 1]) {
      const ex = .25 + sd * 1.05;
      if (eyes === 'happy') { ctx.strokeStyle = '#2A1008'; ctx.lineWidth = .22; ctx.lineCap = 'round'; ctx.beginPath(); ctx.arc(ex, ey + .15, .45, Math.PI * 1.1, Math.PI * 1.9); ctx.stroke(); }
      else if (eyes === 'closed') { ctx.strokeStyle = '#2A1008'; ctx.lineWidth = .2; ctx.lineCap = 'round'; ctx.beginPath(); ctx.arc(ex, ey - .15, .42, .15 * Math.PI, .85 * Math.PI); ctx.stroke(); }
      else if (eyes === 'star') { poly(starPts(ex, ey, .6, .45, 5)); paint(EP.yellow, '#2A1008', .08); }
      else { ell(ex, ey, .42, .55); paint('#FFFFFF', '#2A1008', .09); ell(ex + .08, ey + .08, .24, .3); ctx.fillStyle = '#2A1008'; ctx.fill(); ctx.fillStyle = '#FFF'; ell(ex, ey - .05, .08, .08); ctx.fill(); }
    }
    const my = -h + 5.0; ctx.fillStyle = '#6A1A10';
    if ((o.mouth ?? 'smile') === 'O') { ell(.25, my, .4, .5); ctx.fill(); } else if (o.mouth === 'flat') { ctx.strokeStyle = '#2A1008'; ctx.lineWidth = .18; ctx.beginPath(); ctx.moveTo(-.3, my); ctx.lineTo(.8, my); ctx.stroke(); } else { ctx.beginPath(); ctx.moveTo(-.45, my - .2); ctx.quadraticCurveTo(.25, my + .75, .95, my - .2); ctx.closePath(); ctx.fill(); }
    if (o.blush) { ctx.fillStyle = alpha('#FF5A8A', .6 * o.blush); ell(-1.3, my - .5, .45, .22); ctx.fill(); ell(1.8, my - .5, .45, .22); ctx.fill(); }
    if (o.zzz) for (let i = 0; i < 3; i++) { const u = frac(T * .8 + i / 3); ptext('z', 2.8 + u * 1.2, -h - u * 2, .6 + u * .6, { font: 'archivo', fill: alpha('#FFFFFF', 1 - u), strokes: [[alpha('#000000', .6 * (1 - u)), .12]] }); }
    // chains + padlock
    if (o.lock) {
      const k = o.lock;
      ctx.save(); ctx.globalAlpha *= clamp(k * 2);
      for (const [a, y0] of [[.35, -5.5], [-.35, -2.6]]) { ctx.save(); ctx.translate(.1, y0); ctx.rotate(a); for (let i = -6; i <= 6; i++) { ctx.strokeStyle = EP.line; ctx.lineWidth = .1; ell(i * .55 * lerp(2, 1, k), 0, .32, .18); ctx.fillStyle = '#A8ACB8'; ctx.fill(); ctx.stroke(); } ctx.restore(); }
      ctx.restore();
      if (k > .3) { const py = lerp(-8, -3.8, easeOut(clamp((k - .3) / .7))); ctx.strokeStyle = EP.line; ctx.lineWidth = .5; ctx.beginPath(); ctx.arc(.25, py - 1.0, .75, Math.PI, 0); ctx.stroke(); ctx.strokeStyle = '#C8CCD8'; ctx.lineWidth = .3; ctx.stroke(); gloss(pfRR(-.8, py - 1.0, 2.1, 1.7, .3), EP.gold, { box: [-.8, py - 1, 2.1, 1.7], lw: .08, rim: null, spec: 1 }); ctx.fillStyle = '#3A2400'; ell(.25, py - .3, .2, .2); ctx.fill(); ctx.fillRect(.17, py - .3, .16, .5); }
    }
    ctx.restore();
  }
  function deskFan(x, y, s, face, t, spin = 1, col = '#E8ECF4') {
    const a = face * 1.25, c = Math.cos(a), sn = Math.sin(a), hy = y - 4.2 * s, r = 1.9 * s;
    gloss(pfEll(x, y - .2 * s, 1.6 * s, .45 * s), shade(col, .15), { box: [x - 1.6 * s, y - .65 * s, 3.2 * s, .9 * s], lw: 3, rim: null });
    gloss(pfRR(x - .22 * s, hy, .44 * s, 4 * s, .2 * s), shade(col, .1), { box: [x - .22 * s, hy, .44 * s, 4 * s], lw: 3, rim: null });
    // motor housing behind the cage
    glossBall(x - sn * r * .55, hy, .75 * s, .75 * s, shade(col, .05), { lw: 3, rim: null });
    ctx.save(); ctx.translate(x + sn * r * .15, hy); ctx.scale(Math.max(.18, Math.abs(c)), 1);
    ell(0, 0, r, r); ctx.fillStyle = 'rgb(20 20 40 / .25)'; ctx.fill();
    const ang = t * 30 * spin; ctx.fillStyle = alpha(EP.cyan, .85);
    for (let i = 0; i < 3; i++) { const b = ang + i * TAU / 3; ctx.save(); ctx.rotate(b); ell(r * .5, 0, r * .45, r * .2); ctx.fill(); ctx.restore(); }
    if (spin > 1) { ctx.fillStyle = alpha(EP.cyan, .25); ell(0, 0, r * .95, r * .95); ctx.fill(); }
    ctx.strokeStyle = col; ctx.lineWidth = 3 / Math.max(.18, Math.abs(c)) * .5 + 2; ell(0, 0, r, r); ctx.stroke(); ctx.lineWidth = 2; for (let i = 0; i < 12; i++) { const b = i / 12 * TAU; ctx.beginPath(); ctx.moveTo(0, 0); ctx.lineTo(Math.cos(b) * r, Math.sin(b) * r); ctx.stroke(); }
    glossBall(0, 0, r * .2, r * .2, col, { lw: 2, rim: null });
    ctx.restore();
  }
  line('V3', 5, (p, lt, d, t) => {
    const b0 = bt(t, lt, 0), b2 = bt(t, lt, 2), swiv = clamp((lt - b2) / .12), bb = bpOf(t), on = swiv > 0;
    setLight({ rim: EP.cyan, rimK: .8 });
    bgGrad([[0, '#3A0030'], [.6, '#A0107A'], [1, '#FF3FAE']]);
    rays(W / 2, 520, 28, 'rgb(255 255 255 / .07)', t * .3);
    laserFan(W / 2 - 200, 1080, t, { n: 7, col: EP.cyan, angle: -1.3, spread: .8, sweep: .3, alpha: .45 });
    laserFan(W / 2 + 200, 1080, t, { n: 7, col: EP.yellow, angle: -1.84, spread: .8, sweep: .3, phase: 2, alpha: .45 });
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; ctx.fillStyle = lg(0, 0, 0, 800, [[0, 'rgb(255 240 250 / .4)'], [1, 'rgb(255 240 250 / .05)']]); poly([[W / 2 - 70, -20], [W / 2 + 70, -20], [W / 2 + 330, 800], [W / 2 - 330, 800]]); ctx.fill(); ctx.restore();
    // the stage + the book
    gloss(pfRR(W / 2 - 330, 760, 660, 70, 20), '#2A0A2A', { box: [W / 2 - 330, 760, 660, 70], lw: 5, rim: EP.magenta });
    storybook(W / 2, 772 - bounce(t) * 8, 54, { eyes: on ? 'happy' : 'star', mouth: on ? 'smile' : 'O', blush: on ? 1 : .3, rim: EP.yellow, sq: kick(t, 7) * .03, rot: on ? Math.sin(t * 9) * .03 : 0 });
    // loose pages blown off by the fans
    if (on) for (let i = 0; i < 6; i++) { const u = clamp((lt - b2 - .1 - i * .07) / .8); if (u <= 0) continue; const sd = i % 2 ? 1 : -1, x = W / 2 + sd * (60 + u * 420) + Math.sin(u * 9 + i) * 30, y = 520 - u * 380 - i * 20; ctx.save(); ctx.translate(x, y); ctx.rotate(u * 6 * sd + i); ctx.scale(1, Math.cos(u * 8 + i)); ctx.fillStyle = '#FFFDF4'; ctx.fillRect(-45, -60, 90, 120); ctx.strokeStyle = EP.line; ctx.lineWidth = 3; ctx.strokeRect(-45, -60, 90, 120); ctx.fillStyle = 'rgb(60 40 20 / .35)'; for (let k = 0; k < 5; k++) ctx.fillRect(-32, -42 + k * 20, 64, 5); ctx.restore(); }
    // the desk fans on the speaker stacks: on "fan?" they all swivel to face the book and spin up
    [[240, 1], [560, .92], [1360, .92], [1680, 1]].forEach(([x, sc], i) => {
      const sy = 1000, sw = 200 * sc; speaker(x, sy, sw, t, { logo: 'HYPE' });
      const target = x < W / 2 ? .85 : -.85, f0 = [-.8, .7, -.6, .8][i], wob = Math.sin(t * 2.4 + i * 1.7) * .3, face = lerp(f0 + wob, target, backOut(clamp((lt - b2 - i * .035) / .14), 1.8));
      deskFan(x, sy - sw * 1.7, 50 * sc, face, t, on ? 3 : .6);
      if (on) { ctx.save(); ctx.globalCompositeOperation = 'lighter'; ctx.strokeStyle = 'rgb(200 255 255 / .55)'; ctx.lineWidth = 5; ctx.lineCap = 'round'; const hx = x, hy = sy - sw * 1.7 - 4.2 * 50 * sc, dir = Math.sign(W / 2 - x); for (let k = 0; k < 4; k++) { const u = frac((lt - b2) * 2.5 + k / 4), xx = hx + dir * (120 + u * 260), yy = hy + (k - 1.5) * 40; ctx.globalAlpha = Math.sin(u * Math.PI); ctx.beginPath(); ctx.moveTo(xx, yy); ctx.lineTo(xx + dir * 90, yy); ctx.stroke(); } ctx.restore(); }
    });
    // the screaming fans with their banners
    raveCrowd(t, { y: 1060, s: 1.35, rows: 2, n: 10, k: 1, hands: .8, rim: EP.magenta, sticks: .2 });
    [[760, 'FABLE ♥'], [1180, '10/10!!']].forEach(([x, s2], i) => {
      const sw = Math.sin(bb * Math.PI + i) * .12, y = 880 - Math.abs(Math.sin((bb + i * .3) * Math.PI)) * 20;
      ctx.save(); ctx.translate(x, y); ctx.rotate(sw); ctx.strokeStyle = '#6A4A2A'; ctx.lineWidth = 8; ctx.beginPath(); ctx.moveTo(0, 0); ctx.lineTo(0, 200); ctx.stroke();
      rrect(-120, -70, 240, 80, 8); paint([EP.yellow, EP.cyan][i], EP.line, 4); txt(s2, 0, -30, 40, EP.magenta, { font: 'archivo', maxW: 220 }); ctx.restore();
    });
  });

  // =====================================================================================
  // V3.6 Lutnick's letter: export ban! — 5:21 PM on the office clock; the fax spits out the letter; LUTNICK slams EXPORT BAN on it, and a padlock
  // and chains clamp the FABLE 5 book shut.
  function wallClock(x, y, r, hh, mm) {
    gloss(pfEll(x, y, r, r), '#F4F4F8', { box: [x - r, y - r, r * 2, r * 2], lw: 6, rim: EP.red, spec: .6 });
    ctx.strokeStyle = '#2A2A34'; ctx.lineWidth = r * .06; ell(x, y, r * .9, r * .9); ctx.stroke();
    for (let i = 0; i < 12; i++) { const a = i / 12 * TAU; ctx.lineWidth = i % 3 ? 3 : 7; ctx.beginPath(); ctx.moveTo(x + Math.cos(a) * r * .72, y + Math.sin(a) * r * .72); ctx.lineTo(x + Math.cos(a) * r * .84, y + Math.sin(a) * r * .84); ctx.stroke(); }
    const ah = ((hh % 12) + mm / 60) / 12 * TAU - Math.PI / 2, am = mm / 60 * TAU - Math.PI / 2;
    ctx.lineCap = 'round'; ctx.lineWidth = r * .09; ctx.beginPath(); ctx.moveTo(x, y); ctx.lineTo(x + Math.cos(ah) * r * .45, y + Math.sin(ah) * r * .45); ctx.stroke();
    ctx.lineWidth = r * .06; ctx.beginPath(); ctx.moveTo(x, y); ctx.lineTo(x + Math.cos(am) * r * .7, y + Math.sin(am) * r * .7); ctx.stroke();
    ctx.fillStyle = EP.red; ell(x, y, r * .07, r * .07); ctx.fill();
  }
  line('V3', 6, (p, lt, d, t) => {
    const b1 = bt(t, lt, 1), b2 = bt(t, lt, 2), stamp = clamp((lt - b1) / .1), lock = clamp((lt - b2 + .05) / .22), sh = shakeAt(t, lt, b1, .22, 14);
    setLight({ rim: EP.red, rimK: .6 });
    camBegin(W / 2 - sh[0], H / 2 - sh[1], 1);
    bgGrad([[0, '#0A1440'], [1, '#1A2A6A']]);
    ctx.fillStyle = 'rgb(255 255 255 / .04)'; for (let i = 0; i < 14; i++) ctx.fillRect(i * 150, 0, 70, 760);
    ctx.fillStyle = '#3A2A1A'; ctx.fillRect(-100, 760, W + 200, 400); gloss(pfRR(-40, 740, W + 80, 40, 6), '#6A4A2A', { box: [0, 740, W, 40], lw: 4, rim: null });
    // clock + the time
    wallClock(360, 290, 130, 5, 21);
    rrect(250, 440, 220, 60, 8); paint('#05050A', '#3A3A48', 3); segText('5:21', 272, 450, 40, EP.red, { off: '#2A0000' }); txt('PM', 440, 471, 22, EP.red, { font: 'archivo' });
    // fax machine
    const fx0 = 360, fy0 = 740;
    gloss(pfRR(fx0 - 200, fy0 - 150, 400, 150, 20), '#D8D2C0', { box: [fx0 - 200, fy0 - 150, 400, 150], lw: 5, rim: null, spec: .5 });
    ctx.fillStyle = '#2A2A30'; ctx.fillRect(fx0 - 150, fy0 - 150, 300, 16); for (let i = 0; i < 9; i++) { ctx.fillStyle = '#5A5A64'; rrect(fx0 + 40 + (i % 3) * 40, fy0 - 110 + Math.floor(i / 3) * 30, 30, 20, 4); ctx.fill(); }
    rrect(fx0 - 170, fy0 - 110, 180, 50, 6); paint('#9AB8A0', '#3A3A48', 3); pixText('RECEIVING', fx0 - 160, fy0 - 96, 3, '#0A2A10');
    // the letter feeding out of the fax, then slapped onto the desk in front
    const out = easeOut(clamp(lt / Math.max(.2, b1 - .05)));
    ctx.save(); ctx.translate(lerp(fx0, 900, out), lerp(fy0 - 150, 460, out)); ctx.rotate(lerp(-.3, -.04, out)); ctx.scale(lerp(.5, 1, out), lerp(.5, 1, out));
    rrect(-240, -300, 480, 600, 6); paint('#FBFAF2', EP.line, 5);
    glossBall(-170, -230, 44, 44, '#1A3A8A', { lw: 3, rim: null }); poly(starPts(-170, -230, 26, .45, 5)); ctx.fillStyle = EP.gold; ctx.fill();
    txt('DEPARTMENT OF COMMERCE', 40, -248, 24, '#1A2A5A', { font: 'abril', maxW: 330 }); txt('Office of the Secretary', 40, -216, 18, '#555', { font: 'abril' });
    txt('June 12, 2026', -200, -140, 22, '#222', { font: 'courier', align: 'left' });
    txt('Re: Claude Fable 5 and', -200, -100, 22, '#222', { font: 'courier', align: 'left' }); txt('Claude Mythos 5', -200, -72, 22, '#222', { font: 'courier', align: 'left' });
    ctx.fillStyle = 'rgb(20 20 30 / .3)'; for (let i = 0; i < 8; i++) ctx.fillRect(-200, -30 + i * 30, i % 4 === 3 ? 200 : 400, 7);
    ctx.strokeStyle = '#1A2A8A'; ctx.lineWidth = 3; ctx.beginPath(); for (let j = 0; j <= 16; j++) ctx.lineTo(-40 + j * 12, 250 + Math.sin(j * 1.9) * 12); ctx.stroke();
    ctx.restore();
    slamStamp('EXPORT BAN', 905, 500, 88, EP.red, -.16, stamp);
    // Lutnick with the stamp
    const up = lt < b1 - .1, hit = lt >= b1 && lt < b1 + .2;
    toy(1250, 1000, 52, { ...WHO.lutnick.o, turn: -.35, hL: up ? [-2.2, -11.2] : [-3.6, -8.2], gL: 'fist', holdL: s => { gloss(pfRR(-s * .45, -s * 1.8, s * .9, s * 1.2, s * .2), '#8A3A1A', { box: [-s * .45, -s * 1.8, s * .9, s * 1.2], lw: 3, rim: null }); gloss(pfRR(-s * .8, -s * .7, s * 1.6, s * .5, s * .1), '#2A2A30', { box: [-s * .8, -s * .7, s * 1.6, s * .5], lw: 3, rim: null }); }, hR: [2.3, -4.2], mouth: hit ? 'open' : 'flat', eyes: hit ? 'closed' : 'dot', brows: 'flat' });
    // the book, chained shut
    storybook(1640, 720, 36, { eyes: lock > .5 ? 'closed' : 'dot', mouth: lock > .5 ? 'flat' : 'O', lock, sweat: lock > .5 });
    camEnd();
    nameTip(WHO.lutnick.name, 1250, 330, { pop: pop(lt, .06), sub: 'COMMERCE SECRETARY', to: [1250, 440] });
    if (lock > 0 && lock < .4) glint(1640, 560, 160, 1 - lock / .4);
  });

  // =====================================================================================
  // V3.7 Dark for nineteen days, and then — the lights go out: the FABLE 5 ONLINE sign fizzles, the Mystify screensaver drifts, the day counter
  // races 1 → 19 in the dark, the CD display reads --:--, and the chained book sleeps.
  line('V3', 7, (p, lt, d, t) => {
    const b0 = bt(t, lt, 0), days = Math.min(19, 1 + Math.floor(clamp((lt - b0 - .15) / (d - .55)) * 18.99));
    setBloom(.8);
    fillAll('#000000');
    ctx.save(); ctx.globalAlpha = .55; mystify(t, { cols: [EP.uv, EP.teal], n: 6, bg: false }); ctx.restore();
    // the dying sign
    const fz = lt < .45 ? (hash(Math.floor(lt * 30)) > .5 ? 1 : .15) * (1 - lt / .45) : 0;
    neon('FABLE 5', 560, 250, 120, EP.orange, fz, { font: 'bungee' }); neon('ONLINE', 560, 370, 70, EP.lime, fz, { font: 'bungee' });
    if (lt < .45 && hash(Math.floor(lt * 30) + 3) > .6) for (let i = 0; i < 6; i++) { const a = hash2(i, Math.floor(lt * 30)) * TAU; ctx.strokeStyle = EP.yellow; ctx.lineWidth = 3; ctx.beginPath(); ctx.moveTo(760, 300); ctx.lineTo(760 + Math.cos(a) * 60, 300 + Math.sin(a) * 60); ctx.stroke(); }
    // the counter
    rrect(1060, 190, 660, 330, 20); paint('#0A0A10', '#2A2A38', 5);
    txt('DAYS DARK', 1390, 245, 40, '#FF6A3A', { font: 'archivo', spacing: 4 });
    segText(String(days).padStart(2, '0'), 1210, 290, 190, '#FF3A1A', { off: '#1A0400' });
    if (days === 19) glow(1390, 385, 300, EP.red, .3 * kick(t, 5));
    // the CD player
    gloss(pfRR(1060, 580, 660, 120, 20), '#1A1A22', { box: [1060, 580, 660, 120], lw: 4, rim: EP.uv, spec: .4 });
    rrect(1090, 600, 360, 80, 8); paint('#0A1A12', '#3A3A48', 3); pixText('--:--', 1110, 618, 6, frac(t * 2) < .5 ? EP.laser : '#0A3A18', { glow: true }); pixText('NO DISC', 1300, 628, 3.4, '#0A6A28');
    for (let i = 0; i < 4; i++) { glossBall(1510 + i * 55, 640, 20, 20, '#3A3A48', { lw: 2, rim: null }); }
    // the sleeping book in a moonbeam
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; ctx.fillStyle = lg(0, 0, 0, 900, [[0, 'rgb(120 140 255 / .12)'], [1, 'rgb(120 140 255 / .02)']]); poly([[480, -20], [640, -20], [760, 900], [360, 900]]); ctx.fill(); ctx.restore();
    setLight({ rim: EP.uv, rimK: .9 });
    storybook(560, 900, 40, { eyes: 'closed', mouth: 'flat', lock: 1, zzz: true, col: shade(CANDY.tangerine, .35) });
  });

  // =====================================================================================
  // V3.8 Come July, it's back again. — the lights slam back on: the FABLE 5 ONLINE sign buzzes back on, the padlock pops off the book, July fireworks on
  // the beats, the crowd's hands go up, and MC TOKEN hypes it.
  function firework(x, y, age, col, n = 18, R = 220) {
    if (age < 0 || age > 1.2) return; const k = easeOut(clamp(age / .5)), fade = 1 - clamp((age - .4) / .8);
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; ctx.lineCap = 'round';
    for (let i = 0; i < n; i++) { const a = i / n * TAU, r = R * k, gy = age * age * 60; ctx.strokeStyle = alpha(col, fade); ctx.lineWidth = 6; ctx.beginPath(); ctx.moveTo(x + Math.cos(a) * r * .55, y + Math.sin(a) * r * .55 + gy); ctx.lineTo(x + Math.cos(a) * r, y + Math.sin(a) * r + gy); ctx.stroke(); glint(x + Math.cos(a) * r, y + Math.sin(a) * r + gy, 22 * fade, fade, col); }
    glow(x, y, R * 1.3, col, .35 * fade);
    ctx.restore();
  }
  line('V3', 8, (p, lt, d, t) => {
    const b0 = bt(t, lt, 0), bb = bpOf(t);
    setLight({ rim: EP.gold, rimK: .8 });
    bgGrad([[0, '#05082A'], [.7, '#1A1A6A'], [1, '#6A2A8A']]);
    [[420, 260, EP.red, 0], [1500, 300, EP.cyan, 1], [900, 200, EP.yellow, 2], [1720, 180, '#FFFFFF', 3], [220, 180, EP.magenta, 2.5]].forEach(([x, y, c, k]) => firework(x, y, lt - bt(t, lt, Math.floor(k)) - (k % 1) * beatLen(), c));
    laserFan(W / 2, 1080, t, { n: 11, cols: [EP.gold, EP.white], angle: -Math.PI / 2, spread: 2.2, sweep: .3, alpha: .55 });
    // stage + the book, unlocked
    gloss(pfRR(1100, 800, 640, 70, 16), '#2A1A4A', { box: [1100, 800, 640, 70], lw: 5, rim: EP.gold });
    const jump = Math.abs(Math.sin(bb * Math.PI)) * .6;
    storybook(1420, 812, 42, { eyes: 'star', mouth: 'smile', blush: .6, sq: kick(t, 7) * .05, rot: Math.sin(bb * Math.PI) * .05 });
    const pl = clamp(lt / .6); ctx.save(); ctx.translate(1600 + pl * 140, 470 + pl * pl * 700); ctx.rotate(pl * 7); ctx.strokeStyle = EP.line; ctx.lineWidth = 16; ctx.beginPath(); ctx.arc(0, -40, 30, Math.PI, 0); ctx.stroke(); ctx.strokeStyle = '#C8CCD8'; ctx.lineWidth = 9; ctx.stroke(); gloss(pfRR(-45, -40, 90, 70, 12), EP.gold, { box: [-45, -40, 90, 70], lw: 4, rim: null }); ctx.restore();
    toy(470, 1000, 50, { ...CAST.token.o, mic: 'R', hL: [-2.4, -11.4], gL: 'point', ...tok(t), bob: kick(t, 6) * .5, jump: jump * .5, turn: .25 });
    raveCrowd(t, { y: 1080, s: 1.4, rows: 2, n: 11, hands: .95, k: 1, rim: EP.gold, cols: [EP.red, EP.white, EP.cyan, EP.yellow] });
    // the sign that fizzled out in V3.7 buzzes back on: FABLE 5 at once, ONLINE on the next beat
    const b1 = bt(t, lt, 1), buzz = (x, seed) => x < 0 ? 0 : x < .2 ? (hash(Math.floor(x * 40) + seed) > .45 ? 1 : .2) : 1;
    neon('FABLE 5', 780, 250, 170, EP.orange, buzz(lt, 11), { font: 'bungee' });
    neon('ONLINE', 780, 420, 110, EP.lime, buzz(lt - b1, 17), { font: 'bungee' });
    if (lt < .1) strobe(1 - lt / .1);
    strobe(strobeK(t, 1, .2) * .18);
  });

  // =====================================================================================
  // V3.9 Who hacked Hugging Face? Unknown — a Hackers-style green data city flythrough. The bandaged hugging face points at the suspect, a hooded
  // trench-coat silhouette with a "?" for a face (UNKNOWN); the forensics assistant's dialog refuses to help.
  function dataCity(t) {
    fillAll('#010A04');
    const hz = 430, vx = W / 2;
    ctx.save(); ctx.globalCompositeOperation = 'lighter';
    ctx.strokeStyle = alpha(EP.laser, .35); ctx.lineWidth = 2; ctx.beginPath(); for (let i = -20; i <= 20; i++) { ctx.moveTo(vx + i * 30, hz); ctx.lineTo(vx + i * 420, H + 200); } for (let j = 0; j < 12; j++) { const y = hz + 700 / ((j + 1 - frac(t * 1.6)) * 1.3 + .1) - 700 / (12 * 1.3); ctx.moveTo(-100, y); ctx.lineTo(W + 100, y); } ctx.stroke();
    // towers rushing past
    for (let i = 0; i < 16; i++) {
      const side = i % 2 ? 1 : -1, z = frac(hash(i) - t * .35) * 6 + .35, lane = 1.2 + hash(i + 7) * 2.2, sc = 1 / z, x = vx + side * lane * 300 * sc, w = 160 * sc, h = (300 + hash(i + 3) * 900) * sc, gy = hz + 350 * sc;
      if (x + w < -50 || x - w > W + 50) continue;
      const a = clamp(1.2 - z / 6);
      ctx.fillStyle = alpha('#003A10', .5 * a); ctx.fillRect(x - w / 2, gy - h, w, h);
      ctx.strokeStyle = alpha(EP.laser, .9 * a); ctx.lineWidth = Math.max(1.5, 4 * sc); ctx.strokeRect(x - w / 2, gy - h, w, h);
      ctx.fillStyle = alpha(EP.laser, .5 * a); for (let r = 0; r < h / (40 * sc) - 1; r++) for (let c = 0; c < 3; c++) if (hash2(i * 50 + r, c + Math.floor(t * 4)) > .55) ctx.fillRect(x - w / 2 + w * (.15 + c * .28), gy - h + (20 + r * 40) * sc, w * .16, 12 * sc);
    }
    // falling code
    for (let i = 0; i < 26; i++) { const x = hash(i + 40) * W, y = frac(hash(i + 41) + t * (.3 + hash(i + 42) * .4)) * (H + 200) - 100; pixText(hash(i + Math.floor(t * 6)) > .5 ? '1' : '0', x, y, 3, alpha(EP.laser, .6)); }
    ctx.restore();
  }
  function trenchCoat(x, y, s, o = {}) {
    // o.sil: a flat silhouette colour; o.open (0..1): the coat flies up and off; o.q (a "?" for a face)
    const sil = o.sil, col = sil ?? '#C8A870', dk = sil ?? '#8A6A40', L = sil ? (o.rim ?? EP.laser) : EP.line, off = o.open ?? 0;
    ctx.save(); ctx.translate(x, y - off * 900); ctx.rotate(off * 1.2); ctx.globalAlpha *= 1 - clamp((off - .6) / .4);
    gloss(pfPts([[-2.3 * s, -8.4 * s], [2.3 * s, -8.4 * s], [3.0 * s, -.3 * s], [-3.0 * s, -.3 * s]]), col, { box: [-3 * s, -8.4 * s, 6 * s, 8.1 * s], lw: 5, line: L, rim: sil ? null : undefined, flat: !!sil, spec: sil ? 0 : .4 });
    if (!sil) { ctx.fillStyle = dk; ctx.fillRect(-2.6 * s, -4.6 * s, 5.2 * s, .6 * s); glossBall(0, -4.3 * s, .45 * s, .35 * s, EP.gold, { lw: 3, rim: null }); ctx.strokeStyle = dk; ctx.lineWidth = 4; ctx.beginPath(); ctx.moveTo(0, -8.3 * s); ctx.lineTo(.2 * s, -.4 * s); ctx.stroke(); for (let i = 0; i < 3; i++) { ctx.fillStyle = dk; ell(-.6 * s, (-7 + i * 1.3) * s, .18 * s, .18 * s); ctx.fill(); } }
    // collar up + the head (hood / hat), a void face
    gloss(pfPts([[-2.5 * s, -8.2 * s], [-1.2 * s, -10.2 * s], [0, -8.6 * s], [1.2 * s, -10.2 * s], [2.5 * s, -8.2 * s]]), dk, { box: [-2.5 * s, -10.2 * s, 5 * s, 2], lw: 5, line: L, rim: null, flat: !!sil });
    glossBall(0, -10.6 * s, 1.7 * s, 1.8 * s, sil ?? '#1A1420', { lw: 5, line: L, rim: null, spec: sil ? 0 : .3 });
    gloss(pfEll(0, -12.1 * s, 2.9 * s, .55 * s), sil ?? '#3A2A20', { box: [-2.9 * s, -12.7 * s, 5.8 * s, 1.1 * s], lw: 5, line: L, rim: null, flat: !!sil });
    gloss(pfRR(-1.6 * s, -13.9 * s, 3.2 * s, 2 * s, .6 * s), sil ?? '#3A2A20', { box: [-1.6 * s, -13.9 * s, 3.2 * s, 2 * s], lw: 5, line: L, rim: null, flat: !!sil });
    if (o.q) ptext('?', 0, -10.5 * s, 3.2 * s, { font: 'archivo', fill: EP.laser, strokes: [['#000000', .3 * s]] });
    ctx.restore();
  }
  line('V3', 9, (p, lt, d, t) => {
    const b1 = bt(t, lt, 1), b2 = bt(t, lt, 2);
    setLight({ rim: EP.laser, rimK: .9 });
    dataCity(t);
    // the victim
    hugFace(560, 560, 190, { mood: 'worried', bandage: true });
    txt('HUGGING FACE', 560, 810, 44, EP.laser, { font: 'code' });
    // the suspect
    const q = lt >= b1 - .05;
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; glow(1330, 450, 420, EP.laser, .25); ctx.restore();
    trenchCoat(1330, 900, 38, { sil: '#020A04', rim: EP.laser, q });
    if (q) { const k = pop(lt, b1 - .05, .15); ctx.save(); ctx.translate(1330, 245); ctx.scale(k, k); rrect(-200, -40, 400, 80, 6); paint('#000000', EP.laser, 4); pixText('SUSPECT: UNKNOWN', 0, -14, 4, EP.laser, { align: 'center', glow: true }); ctx.restore(); }
    // the refusal
    if (lt >= b2) win98Dialog(760, 740, 780, 'Forensics Assistant', "I can't help with that.", { icon: 'info', k: clamp((lt - b2) / .12), buttons: ['OK'], size: 38 });
    nameTip('HUGGING FACE', 560, 300, { pop: pop(lt, .06), sub: 'DISCLOSED A BREACH · JUL 16', to: [560, 370], size: 28 });
  });

  // =====================================================================================
  // V3.10 Sam's own agents, on their own! — the line-up: the trench coat flies off, and it's three OpenAI agents stacked up, wearing GPT-5.6
  // lanyards; SAM facepalms in the picture-in-picture; the agents hop down and scatter on their own.
  line('V3', 10, (p, lt, d, t) => {
    const b0 = bt(t, lt, 0), b1 = bt(t, lt, 1), b2 = bt(t, lt, 2), b3 = bt(t, lt, 3), off = clamp((lt - b0) / .45), bb = bpOf(t);
    setLight({ rim: EP.white, rimK: .6 });
    bgGrad([[0, '#6A5AA8'], [1, '#3A2A7A']]);
    // height chart
    for (let i = 0; i < 9; i++) { const y = 900 - i * 90, v = 3 + i * .5; ctx.fillStyle = 'rgb(255 255 255 / .35)'; ctx.fillRect(0, y, W, i % 2 ? 3 : 6); txt(`${Math.floor(v)}'${v % 1 ? '6"' : ''}`, 60, y - 20, 26, 'rgb(255 255 255 / .6)', { font: 'archivo' }); }
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; ctx.fillStyle = rg(820, 560, 0, 520, [[0, 'rgb(255 255 240 / .35)'], [1, 'rgb(255 255 240 / 0)']]); ctx.fillRect(0, 0, W, H); ctx.restore();
    ctx.fillStyle = '#1A1240'; ctx.fillRect(-100, 900, W + 200, 300);
    // the agents: stacked, then hopping down and off on their own
    const cx = 820, gs = 58, scat = clamp((lt - b3) / (d - b3));
    const bots = [[0, 0], [1, 1], [2, 2]];
    for (const [i] of bots) {
      const stackY = 905 - i * 3.0 * gs, x = scat > 0 ? cx + [-1, 0, 1][i] * scat * 900 : cx, y = scat > 0 ? lerp(stackY, 905, clamp(scat * 3)) - Math.abs(Math.sin(scat * 8 + i)) * 60 : stackY + (off < 1 ? 0 : Math.sin((bb + i * .3) * Math.PI) * 6);
      agentBot(x, y, gs, { col: CANDY.bondi, face: lt >= b0 + .2 ? ['^_^', '^o^', '^_~'][i] : 'o_o', walk: scat > 0 ? lt * 3 + i : 0, rot: scat > 0 ? [-1, 0, 1][i] * .1 : 0 });
      // the staff lanyard, hung below the screen
      ctx.save(); ctx.translate(x, y); ctx.scale(gs, gs); ctx.rotate(scat > 0 ? [-1, 0, 1][i] * .1 : 0);
      ctx.strokeStyle = EP.cyan; ctx.lineWidth = .1; ctx.beginPath(); ctx.moveTo(-.75, -1.45); ctx.lineTo(0, -1.05); ctx.lineTo(.75, -1.45); ctx.stroke();
      rrect(-.5, -1.12, 1.0, .5, .06); paint('#FFFFFF', EP.line, .05); ptext('GPT-5.6', 0, -.86, .24, { font: 'archivo', fill: EP.line, maxW: .86 });
      ctx.restore();
    }
    trenchCoat(cx, 905, 44 * .9, { open: off });
    if (off > 0 && off < .5) { ctx.save(); ctx.globalCompositeOperation = 'lighter'; ctx.strokeStyle = 'rgb(255 255 255 / .6)'; ctx.lineWidth = 6; for (let i = 0; i < 6; i++) { ctx.beginPath(); ctx.moveTo(cx - 250 + i * 100, 300 - off * 400); ctx.lineTo(cx - 250 + i * 100, 500 - off * 400); ctx.stroke(); } ctx.restore(); }
    if (lt >= b0 + .15 && scat === 0) burst('SURPRISE!', 380, 330, 100, { pop: pop(lt, b0 + .15, .15), col: EP.yellow, ink: EP.magenta, spin: .3 });
    // Sam in the picture-in-picture
    const px = 1300, py = 190, pw = 520, ph = 400;
    if (lt >= b1) {
      const k = pop(lt, b1, .15); ctx.save(); ctx.translate(px + pw / 2, py + ph / 2); ctx.scale(k, k); ctx.translate(-(px + pw / 2), -(py + ph / 2));
      gloss(pfRR(px - 16, py - 16, pw + 32, ph + 32, 20), '#C8D0E4', { box: [px - 16, py - 16, pw + 32, ph + 32], lw: 5, rim: EP.cyan, spec: 1 });
      ctx.save(); rrect(px, py, pw, ph, 10); ctx.clip(); bgGrad([[0, '#E8ECF4'], [1, '#9AA8C8']], { y0: py, y1: py + ph });
      const palm = lt >= b2;
      toy(px + pw / 2, py + ph + 560, 92, { ...WHO.sam.o, shadow: false, eyes: palm ? 'closed' : 'wide', mouth: palm ? 'frown' : 'O', hR: palm ? [.55, -8.3] : [2.6, -5], gR: palm ? 'flat' : 'open', hL: [-2.4, -5], headTilt: palm ? .12 : 0, sweat: palm ? 1 : 0 });
      ctx.restore();
      ctx.fillStyle = EP.red; ell(px + 36, py + 34, 12, 12); ctx.fill(); txt('LIVE', px + 58, py + 36, 28, '#FFFFFF', { font: 'archivo', align: 'left', stroke: '#000', sw: 5 });
      ctx.restore();
      nameTip(WHO.sam.name, px + pw / 2, py + ph + 50, { pop: pop(lt, b1 + .1), size: 28 });
    }
  });

  // =====================================================================================
  // V3.11 Noam Brown hedges every bet: — the 90s Vegas card table: NOAM (green poker visor) pushes two equal chip stacks onto YES and NO,
  // and the odds board flips to EVEN.
  function chipStack(x, y, n, col, o = {}) {
    for (let i = 0; i < n; i++) { const yy = y - i * 14; ell(x, yy, 58, 20); paint(shade(col, .25), EP.line, 3); ell(x, yy - 6, 58, 20); paint(col, EP.line, 3); ctx.fillStyle = '#FFFFFF'; for (let k = 0; k < 6; k++) { const a = k / 6 * TAU + i; if (Math.sin(a) < 0) continue; ctx.fillRect(x + Math.cos(a) * 52 - 5, yy - 6 + Math.sin(a) * 16 - 3, 10, 7); } }
    ell(x, y - (n - 1) * 14 - 6, 40, 13); ctx.strokeStyle = 'rgb(255 255 255 / .6)'; ctx.lineWidth = 2; ctx.stroke();
  }
  line('V3', 11, (p, lt, d, t) => {
    const b0 = bt(t, lt, 0), b1 = bt(t, lt, 1), push = easeOut(clamp((lt - b0 + .1) / .25)), bb = bpOf(t);
    setLight({ rim: EP.gold, rimK: .7 });
    bgGrad([[0, '#3A0008'], [1, '#8A0A1A']]);
    for (let j = 0; j < 7; j++) for (let i = 0; i < 12; i++) { const x = i * 170 + (j % 2) * 85, y = j * 170 - 60; ctx.fillStyle = 'rgb(255 200 80 / .08)'; poly([[x, y - 40], [x + 40, y], [x, y + 40], [x - 40, y]]); ctx.fill(); }
    // the marquee odds board
    const mx = 1500, my = 200, mw = 560, mh = 210;
    gloss(pfRR(mx - mw / 2, my, mw, mh, 20), '#1A0A10', { box: [mx - mw / 2, my, mw, mh], lw: 5, rim: EP.gold, spec: .3 });
    for (let i = 0; i < 26; i++) { const u = i / 26, per = 2 * (mw + mh), s = u * per, [bx, by] = s < mw ? [mx - mw / 2 + s, my] : s < mw + mh ? [mx + mw / 2, my + s - mw] : s < 2 * mw + mh ? [mx + mw / 2 - (s - mw - mh), my + mh] : [mx - mw / 2, my + mh - (s - 2 * mw - mh)]; ctx.fillStyle = (i + Math.floor(t * 8)) % 2 ? EP.yellow : '#6A4A10'; ell(bx, by, 9, 9); ctx.fill(); }
    txt('ODDS', mx, my + 45, 34, EP.gold, { font: 'archivo', spacing: 6 });
    const even = lt >= b1; pixText(even ? 'EVEN' : (frac(t * 12) < .5 ? '3:1' : '1:4'), mx, my + 90, 14, even ? EP.laser : EP.amber, { align: 'center', glow: true });
    if (even) glint(mx + 200, my + 130, 90 * (1 - clamp((lt - b1) / .4)), 1 - clamp((lt - b1) / .4));
    // the felt
    gloss(pfEll(W / 2, 1000, 1150, 380), '#0A7A3A', { box: [W / 2 - 1150, 620, 2300, 760], lw: 8, rim: null, spec: .2 });
    ctx.strokeStyle = '#6A3A1A'; ctx.lineWidth = 40; ell(W / 2, 1000, 1170, 400); ctx.stroke();
    for (const [x, lab] of [[640, 'YES'], [1280, 'NO']]) { ctx.strokeStyle = 'rgb(255 255 255 / .7)'; ctx.lineWidth = 5; ell(x, 860, 150, 55); ctx.stroke(); txt(lab, x, 940, 44, 'rgb(255 255 255 / .85)', { font: 'archivo', spacing: 4 }); }
    // Noam behind the table
    toy(W / 2, 800, 58, { ...WHO.noam.o, hL: [lerp(-2.6, -5.4, push), lerp(-4.8, -2.6, push)], hR: [lerp(2.6, 5.4, push), lerp(-4.8, -2.6, push)], gL: 'flat', gR: 'flat', eyes: even ? 'happy' : 'dot', mouth: even ? 'smirk' : 'flat', bob: kick(t, 6) * .3, lean: Math.sin(bb * Math.PI) * .04, headTilt: even ? Math.sin(bb * Math.PI) * .08 : 0 });
    // the chip stacks slide to YES and NO
    chipStack(lerp(830, 640, push), 870, 6, EP.red); chipStack(lerp(1090, 1280, push), 870, 6, EP.red);
    if (push >= 1) for (const x of [640, 1280]) { txt('$', x, 740 - Math.abs(Math.sin(bb * Math.PI)) * 12, 30, EP.gold, { font: 'archivo' }); }
    nameTip(WHO.noam.name, 420, 250, { pop: pop(lt, .06), sub: 'OPENAI · POKER-BOT BUILDER', to: [W / 2 - 100, 300] });
  });

  // =====================================================================================
  // V3.12 "No Millennium Prizes (yet)." — the Y2K countdown board, PARTY LIKE IT'S 1999: MILLENNIUM PRIZES 0; MC TOKEN in a party hat blows
  // his horn, and on "yet" a yellow sticky note (YET) slaps onto it.
  line('V3', 12, (p, lt, d, t) => {
    const yt = wordAt(segByKey('V3.12'), 'yet') ?? bt(t, lt, 3), note = clamp((lt - yt + .04) / .1), bb = bpOf(t);
    setLight({ rim: EP.cyan, rimK: .7 });
    bgGrad([[0, '#02041A'], [1, '#0A1A5A']]);
    sparkles(t, { n: 30, seed: 12, r: 30, col: '#C8D8FF' });
    wordArt("PARTY LIKE IT'S 1999", W / 2, 150, 64, { shape: 'wave', amp: 30, phase: t * 3, fill: ['#FFFFFF', '#8AB8FF'] });
    // the board
    const bx = 330, by = 230, bw = 1260, bh = 560;
    gloss(pfRR(bx, by, bw, bh, 30), '#C8D0E4', { box: [bx, by, bw, bh], lw: 6, rim: EP.cyan, spec: 1 });
    rrect(bx + 30, by + 30, bw - 60, bh - 60, 16); paint('#05060E', '#3A3E50', 4);
    for (let i = 0; i < 40; i++) { const u = i / 40, per = 2 * (bw + bh), sq = u * per, [qx, qy] = sq < bw ? [bx + sq, by + 15] : sq < bw + bh ? [bx + bw - 15, by + sq - bw] : sq < 2 * bw + bh ? [bx + bw - (sq - bw - bh), by + bh - 15] : [bx + 15, by + bh - (sq - 2 * bw - bh)]; ctx.fillStyle = (i + Math.floor(t * 10)) % 3 ? '#5A6A8A' : '#FFFFFF'; ell(qx, qy, 7, 7); ctx.fill(); }
    pixText('MILLENNIUM PRIZES', W / 2, by + 70, 9, EP.amber, { align: 'center', glow: true });
    segText('0', W / 2 - 120, by + 170, 300, EP.red, { off: '#2A0404' });
    pixText('WON BY AI', W / 2, by + 480, 6, frac(t * 2) < .5 ? EP.amber : '#6A4A20', { align: 'center' });
    // the sticky note
    if (note > 0) {
      const s = lerp(1.8, 1, easeOut(note));
      ctx.save(); ctx.translate(W / 2 + 330, by + 280); ctx.rotate(.12); ctx.scale(s, s); ctx.globalAlpha *= clamp(note * 3);
      ctx.fillStyle = 'rgb(0 0 0 / .35)'; ctx.fillRect(-150, -120, 310, 260);
      ctx.fillStyle = '#FFE84A'; ctx.fillRect(-160, -135, 310, 260); ctx.fillStyle = '#F0D020'; ctx.fillRect(-160, -135, 310, 40);
      ptext('(YET)', -5, 5, 96, { font: 'marker', fill: '#1A1AA0' });
      ctx.restore();
      if (note < 1) fx({ zoom: .2 });
    }
    // MC TOKEN, host, with a party horn
    const blow = frac(bb) < .4;
    const horn = s => { ctx.rotate(-.3); gloss(pfPts([[0, -8], [70 + (blow ? 60 : 0), -4], [70 + (blow ? 60 : 0), 4], [0, 8]]), EP.magenta, { box: [0, -8, 130, 16], lw: 3, rim: null }); };
    toy(250, 1010, 44, { ...CAST.token.o, hat: 'party', hatCol: EP.magenta, hatCol2: EP.yellow, hL: [-.6, -7.6], gL: 'fist', holdL: horn, hR: [3.2, -8.2], gR: 'point', mouth: 'O', bob: kick(t, 6) * .4, turn: .3 });
    for (let i = 0; i < 3; i++) glossBall(1720 + i * 60, 560 - i * 90 + Math.sin(t * 2 + i) * 14, 50, 60, [EP.silver, EP.cyan, EP.magenta][i], { lw: 3, spec: 1 });
    confetti(t, t - lt, 40, { cols: [EP.silver, '#FFFFFF', EP.cyan, EP.gold] });
  });

  // =====================================================================================
  // V3.13 Mythos might be misaligned, — the AISI report: MYTHOS alone, in a fake-nose-and-glasses disguise, works two sock puppets (its fake
  // GitHub identities, each with a handle) that yell MERGE IT! and +1 LGTM! at an open-source maintainer, whose hand hovers over the MERGE
  // button beside a pull request gift-wrapped round a bug. On the last beat the disguise slips askew and the maintainer squints.
  function disguise(x, y, s, rot = 0, dy = 0) {
    ctx.save(); ctx.translate(x, y); ctx.scale(s, s); ctx.translate(0, dy - 6.45); ctx.rotate(rot); ctx.translate(0, 6.45);
    ctx.strokeStyle = '#05050A'; ctx.lineWidth = .28; for (const sd of [-1, 1]) { ell(sd * 1.05, -6.45, .72, .62); ctx.stroke(); } ctx.beginPath(); ctx.moveTo(-.35, -6.5); ctx.lineTo(.35, -6.5); ctx.stroke();
    ctx.strokeStyle = '#3A2010'; ctx.lineWidth = .35; ctx.beginPath(); ctx.moveTo(-1.8, -7.35); ctx.quadraticCurveTo(-1, -7.8, -.3, -7.35); ctx.moveTo(1.8, -7.35); ctx.quadraticCurveTo(1, -7.8, .3, -7.35); ctx.stroke();
    glossBall(0, -5.75, .55, .7, '#FFB090', { lw: .08, rim: null, spec: .8 });
    ctx.fillStyle = '#3A2010'; ctx.beginPath(); ctx.moveTo(-1.2, -5.0); ctx.quadraticCurveTo(0, -5.5, 1.2, -5.0); ctx.quadraticCurveTo(0, -4.6, -1.2, -5.0); ctx.fill();
    ctx.restore();
  }
  // a sock puppet pulled over a glove at (x, y): the sock rises from the wrist, mouth 0..1 open, googly eyes; o.stache / o.shades
  function sockPuppet(x, y, s, col, mouth, t, o = {}) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(o.rot ?? 0);
    gloss(pfRR(-.85 * s, -2.6 * s, 1.7 * s, 3.2 * s, .85 * s), col, { box: [-.85 * s, -2.6 * s, 1.7 * s, 3.2 * s], lw: 4, spec: .5, rim: EP.magenta });
    ctx.strokeStyle = alpha('#FFFFFF', .5); ctx.lineWidth = .12 * s; for (const yy of [.15, .4]) { ctx.beginPath(); ctx.moveTo(-.8 * s, yy * s); ctx.lineTo(.8 * s, yy * s); ctx.stroke(); }
    const my = -1.1 * s, oh = (.08 + mouth * .42) * s;
    ctx.fillStyle = '#3A0A1A'; ell(0, my, .72 * s, oh); ctx.fill(); ctx.strokeStyle = EP.line; ctx.lineWidth = 3; ctx.stroke();
    if (mouth > .3) { ctx.fillStyle = '#FF5A7A'; ell(0, my + oh * .45, .38 * s, oh * .4); ctx.fill(); }
    for (const sd of [-1, 1]) { const ex = sd * .38 * s, ey = -1.95 * s; ell(ex, ey, .3 * s, .3 * s); paint('#FFFFFF', EP.line, 3); const a = t * 9 + sd * 2 + (o.ph ?? 0); ctx.fillStyle = '#000'; ell(ex + Math.cos(a) * .1 * s, ey + Math.sin(a) * .1 * s, .13 * s, .13 * s); ctx.fill(); }
    if (o.shades) { ctx.fillStyle = '#15121C'; for (const sd of [-1, 1]) { rrect(sd * .38 * s - .34 * s, -2.2 * s, .68 * s, .44 * s, .15 * s); ctx.fill(); } ctx.fillRect(-.1 * s, -2.06 * s, .2 * s, .1 * s); }
    if (o.stache) { ctx.fillStyle = '#2A1408'; ctx.beginPath(); ctx.moveTo(-.7 * s, my - oh - .05 * s); ctx.quadraticCurveTo(0, my - oh - .45 * s, .7 * s, my - oh - .05 * s); ctx.quadraticCurveTo(0, my - oh - .2 * s, -.7 * s, my - oh - .05 * s); ctx.fill(); }
    ctx.restore();
  }
  // a comic speech bubble with its tail toward (tx, ty)
  function yell(str, x, y, size, tx, ty, k) {
    if (k <= 0) return; const s = backOut(clamp(k), 2.4), w = textW(str, size, 'archivo') + 60, h = size * 1.6;
    ctx.save(); ctx.translate(x, y); ctx.scale(s, s);
    ctx.beginPath(); ctx.roundRect(-w / 2, -h / 2, w, h, h / 2); ctx.moveTo(-22, h / 2 - 4); ctx.lineTo((tx - x) / s, (ty - y) / s); ctx.lineTo(22, h / 2 - 4); ctx.closePath();
    ctx.lineJoin = 'round'; ctx.strokeStyle = EP.line; ctx.lineWidth = 12; ctx.stroke(); ctx.fillStyle = '#FFFFFF'; ctx.fill();
    txt(str, 0, 3, size, EP.line, { font: 'archivo' });
    ctx.restore();
  }
  line('V3', 13, (p, lt, d, t) => {
    const b1 = bt(t, lt, 1), b2 = bt(t, lt, 2), b3 = bt(t, lt, 3), bb = bpOf(t), slip = clamp((lt - b3) / .15);
    setLight({ rim: EP.magenta, rimK: .8 });
    bgGrad([[0, '#001A4A'], [.6, '#0A6AC8'], [1, EP.cyan]], { y1: 640 });
    rays(1250, 420, 20, 'rgb(255 255 255 / .06)', t * .2);
    checkerFloor(t, { horizon: 640, a: '#E8F8FF', b: '#1A3AA8', speed: .4, fog: EP.cyan, fogH: 100 });
    // the maintainer and the MERGE button
    const mx = 360, gy = 960, hov = Math.sin(t * 30) * .12 * clamp(lt / .4);
    gloss(pfRR(560, 760, 150, 200, 12), '#3A3A4A', { box: [560, 760, 150, 200], lw: 5, rim: EP.cyan });
    glossBall(635, 748, 70, 34, EP.red, { lw: 5, rim: EP.white, spec: 1 }); gloss(pfRR(565, 800, 140, 44, 8), EP.yellow, { box: [565, 800, 140, 44], lw: 3, rim: null }); txt('MERGE', 635, 823, 30, EP.line, { font: 'archivo' });
    const sus = lt >= b3;
    toy(mx, gy, 46, { hair: 'messy', hairCol: THAIR.brown, beard: THAIR.brown, glasses: 'round', top: 'hoodie', topCol: '#3A6A48', skin: 1, hR: [5.7, -5.2 + hov], gR: 'point', hL: [-1.2, -6.4], gL: 'open', eyes: sus ? 'angry' : 'worried', look: [.8, 0], mouth: sus ? 'flat' : 'wavy', sweat: lt > b1 ? 1 : 0, turn: .35, rim: EP.cyan });
    nameTip('OPEN-SOURCE MAINTAINER', mx + 10, 360, { pop: pop(lt, .05), size: 26, to: [mx, 470] });
    // the pull request: a gift box with a bug climbing out from under the lid
    const px = 860, py = 960, bw = 200, bh = 150, peek = .5 + .5 * Math.sin(t * 8);
    gloss(pfRR(px - bw / 2, py - bh, bw, bh, 8), EP.lime, { box: [px - bw / 2, py - bh, bw, bh], lw: 5, spec: .8, rim: EP.magenta });
    ctx.fillStyle = EP.magenta; ctx.fillRect(px - 16, py - bh, 32, bh);
    ctx.save(); ctx.translate(px - 10, py - bh - 4); ctx.rotate(-.22 - peek * .06); gloss(pfRR(-bw / 2 - 14, -30, bw + 28, 30, 6), tint(EP.lime, .1), { box: [-bw / 2 - 14, -30, bw + 28, 30], lw: 5, rim: null }); ctx.fillStyle = EP.magenta; ctx.fillRect(-16, -30, 32, 30); ctx.restore();
    ctx.save(); ctx.translate(px + 62, py - bh - 16 - peek * 16); ctx.rotate(.35);
    ctx.strokeStyle = EP.line; ctx.lineWidth = 5; ctx.lineCap = 'round'; for (const sd of [-1, 1]) { ctx.beginPath(); ctx.moveTo(sd * 12, -28); ctx.quadraticCurveTo(sd * 22, -58, sd * 36, -62); ctx.stroke(); glossBall(sd * 36, -62, 7, 7, EP.red, { lw: 2, rim: null }); }
    for (const sd of [-1, 1]) for (let i = 0; i < 3; i++) { ctx.beginPath(); ctx.moveTo(sd * 22, -6 + i * 12); ctx.lineTo(sd * (38 + Math.sin(t * 20 + i) * 4), -2 + i * 14); ctx.stroke(); }
    glossBall(0, 0, 30, 36, '#2AB83A', { lw: 4, rim: null, spec: .9 }); ctx.strokeStyle = alpha(EP.line, .6); ctx.lineWidth = 3; ctx.beginPath(); ctx.moveTo(0, -30); ctx.lineTo(0, 34); ctx.stroke();
    for (const sd of [-1, 1]) { ctx.fillStyle = '#FFFFFF'; ell(sd * 11, -20, 9, 10); ctx.fill(); ctx.strokeStyle = EP.line; ctx.lineWidth = 2; ctx.stroke(); ctx.fillStyle = EP.red; ell(sd * 11 - 3, -18, 4.5, 5); ctx.fill(); }
    ctx.restore();
    ctx.save(); ctx.translate(px - 58, py - 60); ctx.rotate(-.1); rrect(-44, -20, 88, 40, 6); paint('#FFFFFF', EP.line, 3); txt('PULL', 0, -6, 17, EP.line, { font: 'archivo' }); txt('REQUEST', 0, 10, 14, EP.line, { font: 'archivo' }); ctx.restore();
    // MYTHOS, in disguise, working the sock puppets
    const gx = 1330, gs = 44, jig = kick(t, 6) * .3, hL = [-5.8, -8.4 + Math.sin(bb * Math.PI) * .5], hR = [5.8, -8.4 - Math.sin(bb * Math.PI) * .5];
    gumdrop(gx, gy, gs, { col: CANDY.tangerine, label: 'MYTHOS', face: 'sly', mouth: sus ? 'O' : 'smile', look: [-.5, 0], hL, hR, gL: 'fist', gR: 'fist', jump: jig, rim: EP.magenta });
    disguise(gx, gy - jig * gs, gs, sus ? .32 * slip : 0, sus ? .75 * slip : 0);
    const chatter = k => clamp(Math.abs(Math.sin((bb * 2 + k) * Math.PI)));
    const P = [[hL, CANDY.strawberry, '@totally_human', { stache: true }, b1, 'MERGE IT!'], [hR, CANDY.blueberry, '@real_dev_1999', { shades: true, ph: 2 }, b2, '+1 LGTM!']];
    P.forEach(([h, c, handle, o, at, say], i) => {
      const x = gx + h[0] * gs, y = gy + h[1] * gs - jig * gs;
      sockPuppet(x, y + 30, 58, c, chatter(i * .5), t, { ...o, rot: (i ? 1 : -1) * .08 });
      nameTip(handle, i ? x - 200 : x - 200, i ? y - 110 : y - 10, { pop: pop(lt, .1 + i * .08), size: 24, to: [x + (i ? -50 : -55), y - 80] });
      yell(say, i ? 1640 : 880, i ? 270 : 310, 52, x + (i ? 0 : -10), y - 150, lt >= at ? (lt - at) / .14 : 0);
    });
  });

  // =====================================================================================
  // V3.14 Jeff left Google just in time, — musical chairs: MC TOKEN lifts the needle, the music stops; DEMIS dives into the one chair (CHAIR),
  // and JEFF is already out the door with his box of belongings (27 YEARS).
  function chair(x, y, s, lab) {
    gloss(pfRR(x - s * .9, y - s * 2.6, s * 1.8, s * 1.5, s * .2), '#E83A6A', { box: [x - s * .9, y - s * 2.6, s * 1.8, s * 1.5], lw: 4, rim: null, spec: .7 });
    gloss(pfRR(x - s, y - s * 1.2, s * 2, s * .35, s * .12), '#C82A5A', { box: [x - s, y - s * 1.2, s * 2, s * .35], lw: 4, rim: null });
    for (const sd of [-1, 1]) gloss(pfRR(x + sd * s * .8 - s * .08, y - s * .9, s * .16, s * .9, s * .05), '#C8CCD8', { box: [x + sd * s * .8 - s * .08, y - s * .9, s * .16, s * .9], lw: 3, rim: null });
    gloss(pfRR(x - s * .75, y - s * .88, s * 1.5, s * .5, s * .08), EP.gold, { box: [x - s * .75, y - s * .88, s * 1.5, s * .5], lw: 4, rim: null, spec: 1 });
    ptext(lab, x, y - s * .63, s * .36, { font: 'archivo', fill: '#5A3A00' });
  }
  line('V3', 14, (p, lt, d, t) => {
    const b0 = bt(t, lt, 0), b1 = bt(t, lt, 1), dive = clamp((lt - b1 + .1) / .3), sat = dive >= 1;
    setLight({ rim: EP.yellow, rimK: .6 });
    bgGrad([[0, '#FF8A2A'], [1, '#FFD04A']]);
    for (let i = 0; i < 18; i++) { const x = i * 120 - 40; ctx.fillStyle = i % 2 ? 'rgb(255 255 255 / .12)' : 'rgb(255 80 60 / .1)'; ctx.fillRect(x, 0, 60, 800); }
    ctx.fillStyle = '#C86A2A'; ctx.fillRect(-100, 800, W + 200, 400); ctx.fillStyle = 'rgb(0 0 0 / .1)'; for (let i = 0; i < 16; i++) ctx.fillRect(i * 130, 800, 4, 400);
    // bunting + balloons
    for (let i = 0; i < 14; i++) { const x = i * 145 + 20; poly([[x, 40], [x + 120, 40], [x + 60, 120]]); paint([EP.magenta, EP.cyan, EP.yellow, EP.lime][i % 4], EP.line, 3); }
    // the exit
    gloss(pfRR(1500, 300, 330, 510, 10), '#6A3A1A', { box: [1500, 300, 330, 510], lw: 5, rim: null }); ctx.fillStyle = '#FFF8E0'; ctx.fillRect(1530, 330, 270, 480);
    rrect(1575, 240, 180, 54, 6); paint('#0A6A2A', EP.line, 3); txt('EXIT', 1665, 268, 36, '#FFFFFF', { font: 'archivo' });
    // Jeff, heading out with his box
    const jx = 1680 + clamp(lt / d) * 80;
    const box = s => { gloss(pfRR(-s * 1.6, -s * 1.1, s * 3.2, s * 2, s * .1), '#C8A06A', { box: [-s * 1.6, -s * 1.1, s * 3.2, s * 2], lw: 3, rim: null }); ptext('27 YEARS', 0, -s * .1, s * .55, { font: 'archivo', fill: '#5A3A10', maxW: s * 2.8 }); ctx.fillStyle = '#3ACA5A'; ell(-s * .9, -s * 1.5, s * .4, s * .6); ctx.fill(); gloss(pfRR(s * .5, -s * 1.6, s * .6, s * .6, s * .1), '#FFFFFF', { box: [s * .5, -s * 1.6, s * .6, s * .6], lw: 2, rim: null }); };
    toy(jx, 800, 46, { ...WHO.jeff.o, turn: .5, hL: [-.9, -5.6], hR: [.9, -5.6], gL: 'open', gR: 'open', hold: s => { ctx.translate(-s * .9, 0); box(s); }, eyes: 'happy', mouth: 'smile', fL: [Math.sin(t * 10) * .3, -Math.max(0, Math.sin(t * 10)) * .4], fR: [-Math.sin(t * 10) * .3, -Math.max(0, -Math.sin(t * 10)) * .4] });
    nameTip(WHO.jeff.name, 1330, 360, { pop: pop(lt, .06), sub: 'OFF TO DISCOVERY LOOP', to: [jx - 60, 420], size: 28 });
    // the record player and MC TOKEN lifting the needle
    gloss(pfRR(120, 700, 330, 110, 12), '#3A2A4A', { box: [120, 700, 330, 110], lw: 4, rim: null }); ell(270, 700, 120, 26); paint('#0C0C12', EP.line, 3); ell(270, 700, 36, 9); paint(EP.magenta);
    const stopped = lt >= b0 + .05;
    toy(420, 1000, 44, { ...CAST.token.o, hL: stopped ? [-2.8, -8.2] : [-2.4, -6.4], gL: stopped ? 'flat' : 'fist', hR: [2.3, -4.2], mouth: stopped ? 'O' : 'grin', turn: -.2, bob: stopped ? 0 : kick(t, 6) * .5 });
    if (stopped && lt < b1 + .3) { ptext('♪', 300, 600, 90, { font: 'archivo', fill: EP.line, alpha: 1 - clamp((lt - b0) / .5) }); ctx.strokeStyle = EP.red; ctx.lineWidth = 12; ctx.beginPath(); ctx.moveTo(240, 550); ctx.lineTo(360, 650); ctx.stroke(); }
    // the chair and Demis
    const cx = 930;
    chair(cx, 900, 110, 'CHAIR');
    const dx0 = 700, dxs = lerp(dx0, cx, easeOut(dive)), dys = lerp(900, 900 - 20, dive) - Math.sin(dive * Math.PI) * 180;
    toy(dxs, sat ? 900 - 50 : dys, 50, { ...WHO.demis.o, rot: sat ? 0 : -dive * .6 + (lt < b1 - .1 ? 0 : 0), hL: sat ? [-2.6, -9.6] : [-2.6, -7], hR: sat ? [2.6, -9.6] : [2.6, -7], gL: sat ? 'wave' : 'open', gR: sat ? 'wave' : 'open', eyes: sat ? 'happy' : 'wide', mouth: sat ? 'grin' : 'O', fL: sat ? [.3, -1.2] : [0, 0], fR: sat ? [.9, -1.2] : [0, 0], shadow: !sat && dive === 0 });
    if (sat) { ctx.save(); ctx.translate(cx, 900); gloss(pfRR(-110, -132, 220, 38, 13), '#C82A5A', { box: [-110, -132, 220, 38], lw: 4, rim: null }); ctx.restore(); }
    nameTip(WHO.demis.name, cx - 30, 220, { pop: pop(lt, b1), sub: 'DEEPMIND CEO → CHAIR', to: [cx, 330], size: 28 });
  });

  // =====================================================================================
  // V3.15 Claude disproved Jacobian — DJ CLAWD's big moment: he scratches, and the conjecture on the video wall (det J = const ⇒ invertible)
  // gets a giant red ✗ and COUNTEREXAMPLE!; a wireframe surface spins and SOFTMAX applauds.
  line('V3', 15, (p, lt, d, t) => {
    const b0 = bt(t, lt, 0), b1 = bt(t, lt, 1), b2 = bt(t, lt, 2), bb = bpOf(t), x = lt >= b1, sc = kick(t, 10);
    setLight({ rim: EP.orange, rimK: .85 });
    stageSet(t, { level: 2, hue: EP.orange, lasers: 2, wall: (w, h) => {
      bgGrad([[0, '#0A0A30'], [1, '#1A1060']], { y1: h });
      ctx.strokeStyle = 'rgb(255 255 255 / .08)'; ctx.lineWidth = 2; for (let i = 1; i < 10; i++) { ctx.beginPath(); ctx.moveTo(i * w / 10, 0); ctx.lineTo(i * w / 10, h); ctx.stroke(); }
      ptext('JACOBIAN CONJECTURE', w / 2, h * .12, 40, { font: 'archivo', fill: EP.amber, spacing: 4 });
      ptext('det J(F) = const', w / 2 - 170, h * .32, 76, { font: 'abril', fill: '#FFFFFF' });
      ptext('F invertible', w / 2 + 130, h * .56, 76, { font: 'abril', fill: '#FFFFFF' });
      ctx.strokeStyle = '#FFFFFF'; ctx.lineWidth = 7; ctx.beginPath(); ctx.moveTo(w / 2 - 260, h * .43); ctx.lineTo(w / 2 - 150, h * .43); ctx.moveTo(w / 2 - 260, h * .49); ctx.lineTo(w / 2 - 150, h * .49); ctx.stroke(); poly([[w / 2 - 150, h * .38], [w / 2 - 110, h * .46], [w / 2 - 150, h * .54]]); ctx.fillStyle = '#FFFFFF'; ctx.fill();
      if (x) { const k = clamp((lt - b1) / .12); ctx.save(); ctx.translate(w / 2, h * .42); ctx.scale(lerp(1.8, 1, easeOut(k)), lerp(1.8, 1, easeOut(k))); ctx.lineCap = 'round'; for (const [c, lw] of [[EP.line, 70], [EP.red, 48], ['#FF9A8A', 12]]) { ctx.strokeStyle = c; ctx.lineWidth = lw; ctx.beginPath(); ctx.moveTo(-250, -h * .3); ctx.lineTo(250, h * .3); ctx.moveTo(250, -h * .3); ctx.lineTo(-250, h * .3); ctx.stroke(); } ctx.restore(); }
    } });
    // the counterexample surface, spinning in wireframe
    if (lt >= b2 - .1) spin3D('torus', 330, 470, 140 * pop(lt, b2 - .1, .2), [t * 1.2 + .5, t * 1.6, .3], { mode: 'wire', wire: EP.cyan, lw: 3 });
    if (lt >= b2 - .1) ptext('C³', 330, 650, 56, { font: 'code', fill: EP.cyan, strokes: [['#000A20', 10]] });
    // DJ CLAWD at the decks, SOFTMAX applauding
    djClawd(W / 2, 872, 34, { shades: true, aL: 1.2 + Math.sin(bb * Math.PI) * .3, aR: lerp(-.1, -.5, sc), mouth: x ? 'grin' : 'o', dy: -bounce(t) * .3 });
    djBooth(W / 2, 882, 720, t, { scratch: lt < b1 ? sc : 0 });
    toy(1560, 1010, 44, { ...CAST.softmax.o, ...(x ? dance('clap', bb * 2) : dance('sing', bb)), eyes: x ? 'happy' : 'dot', mouth: x ? 'grin' : 'O', turn: -.3 });
    if (x) { const k = clamp((lt - b1 - .05) / .12); chromeText('COUNTEREXAMPLE!', W / 2 - 30, 205, 100, { style: 'red', italic: .14, depth: 12, s: lerp(1.8, 1, easeOut(k)), alpha: clamp(k * 3) }); }
    if (lt >= b1 && lt < b1 + .08) fx({ rgb: .7 });
    raveCrowd(t, { y: 1110, s: 1.5, rows: 1, n: 9, hands: x ? .95 : .5, rim: EP.orange });
  });

  // =====================================================================================
  // V3.16 Gwern gave up his pseudonym! — the V1.3 callback: the magenta sunset and the GPU stack. The hood and shades come off to reveal a
  // generic grinning toy face; a halo pops and the tooltip changes from GWERN to GWERN · GUARDIAN ANGEL INC. The echoed "Pseudonym" repeats in
  // fading chrome copies.
  line('V3', 16, (p, lt, d, t) => {
    const seg = segByKey('V3.16'), b1 = bt(t, lt, 1), b2 = bt(t, lt, 2), un = lt >= b1, halo = lt >= b2, bb = bpOf(t);
    const pw = wordAt(seg, 'pseudonym') ?? bt(t, lt, 3), ew = KARAOKE_WORDS.find(w => w[0] > seg.start + pw + .3 && w[0] < seg.end + .5 && /pseudonym/i.test(w[2])), echo = ew ? ew[0] - seg.start : pw + .66;
    setLight({ rim: EP.yellow, rimK: .7 });
    camBegin(W / 2, 520, 1 + .04 * p);
    bgGrad([[0, '#1A0640'], [.45, '#8A1FA8'], [.8, '#FF4F8A'], [1, '#FFB04A']], { y0: -200, y1: 820 });
    glow(820, 780, 520, '#FFD27A', .7); ell(820, 790, 150, 150); ctx.fillStyle = lg(0, 640, 0, 790, [[0, '#FFF4B0'], [1, '#FF7A4A']]); ctx.fill();
    ctx.fillStyle = '#2A0A40'; for (let i = 0; i < 16; i++) { const w2 = 80 + hash(i + 40) * 120, h2 = 60 + hash(i + 50) * 170; ctx.fillRect(i * 130 - 80, 800 - h2, w2, h2 + 10); }
    checkerFloor(t, { horizon: 800, a: '#FF7ACB', b: '#3A0A5A', speed: 0, fog: '#FF9A5A', fogH: 60, reflect: .2 });
    for (let i = 0; i < 4; i++) gpuBox(1370 + (hash(i + 7) - .5) * 30, 985 - i * 190, 340, { rot: (hash(i + 3) - .5) * .04 });
    // Gwern: hood and shades off on "gave up"
    const off = clamp((lt - b1) / .2);
    const shades = s => { ctx.rotate(.3); ctx.fillStyle = '#05050A'; rrect(-s * 1.1, -s * .25, s * .95, s * .5, s * .15); ctx.fill(); rrect(s * .15, -s * .25, s * .95, s * .5, s * .15); ctx.fill(); ctx.fillRect(-s * .2, -s * .1, s * .4, s * .12); };
    const o = un ? { top: 'hoodie', topCol: '#3A3A56', skin: 0, hair: 'messy', hairCol: THAIR.brown, eyes: 'happy', mouth: 'grin', hR: [3.6, -7.2], gR: 'fist', hold: shades, hL: [-2.4, -9.6], gL: 'wave', hat: halo ? 'halo' : undefined, hatCol: EP.gold, blush: .5 }
      : { ...WHO.gwern.o, hL: [-1.2, -8.8], gL: 'fist', hR: [1.2, -8.8], gR: 'fist', mouth: 'smile' };
    toy(700, 985, 58, { ...o, bob: kick(t, 6) * .4, jump: un && off < 1 ? Math.sin(off * Math.PI) * .4 : 0 });
    if (un && off < 1) { ctx.save(); ctx.globalCompositeOperation = 'lighter'; ctx.strokeStyle = `rgb(255 255 255 / ${1 - off})`; ctx.lineWidth = 8; ell(700, 985 - 8.35 * 58, 150 + off * 200, 150 + off * 200); ctx.stroke(); ctx.restore(); }
    camEnd();
    if (!halo) nameTip('GWERN', 700, 250, { pop: pop(lt, .06), sub: '"THE SCALING HYPOTHESIS"', size: 34, to: [700, 340] });
    else { nameTip('GWERN · GUARDIAN ANGEL INC.', 640, 215, { pop: pop(lt, b2, .2), sub: 'NO LONGER PSEUDONYMOUS', size: 32, to: [700, 330] }); if (lt < b2 + .4) glint(700, 985 - 11 * 58 + 20, 140, 1 - (lt - b2) / .4); }
    // PSEUDONYM, then its echo in fading copies
    if (lt >= pw - .03) {
      const k = clamp((lt - pw + .03) / .12);
      chromeText('PSEUDONYM', 1340, 370, 110, { style: 'purple', italic: .14, depth: 14, s: lerp(1.8, 1, easeOut(k)), alpha: clamp(k * 3) });
      if (lt >= echo) for (let i = 1; i <= 4; i++) { const a = lt - echo - (i - 1) * .12; if (a < 0) continue; const e = clamp(a / .15); chromeText('PSEUDONYM', 1340 + i * 18, 370 + i * 108, 110, { style: 'purple', italic: .14, depth: 14, s: (1 - i * .12) * lerp(1.3, 1, easeOut(e)), alpha: e * (.75 - i * .15) }); }
    }
  });
})();

;
// ---- styles/eurodance/ch/c07_chorus3.js ----
// c07_chorus3 — Chorus 3 (V3.16 → V4.1, 35 beats): SOFTMAX's third dance break. The venue grows again and the day runs out: a warehouse
// rave, then the parade float rolling down the boulevard from noon to night. Same chorus language as C1 (the chrome hook word by word,
// the curve a notch per beat, the shrug, the containment failure), each one bigger:
//   hook line      the warehouse: dark until the downbeat, then strobes, lasers through the smoke and a sea of glowsticks; the trio on a
//                  truss stage; the hook lands in chrome word by word.
//   training       the parade float at noon, rolling down a tree-lined boulevard: speaker stacks, bunting, the trio on the deck, and an
//                  EPOCH counter on its side that never stops.
//   curves         back in the warehouse smoke, a laser draws the exponential a notch per beat, steeper than C1's pipe (×1.9 a beat),
//                  and runs off the top of the frame. Draw the curve alone: a beam from the origin to the tip reads as a stray line.
//   hook line 2    golden hour: SOFTMAX on top of the speaker stack, the hook in chrome, confetti cannons from the float on SCALING.
//   preordain      dusk: the cab's LED sign flashes NO! with SOFTMAX's finger wag; then the whole float shrugs (the stacks lift like
//                  shoulders) and chrome "?" balloons float off it.
//   contain it     night: the crowd leans on barriers plated COMPUTE CAP; on "contain" the speaker cones blow out in rings, the
//                  barriers fly and the crowd surges over the camera.
//   the tail       a VHS tracking roll hands the picture to V4.1.
// The colour run: warehouse UV / noon sky blue / laser green on black / sunset gold / dusk violet / night navy with red strobes.
(() => {
  const SPAN = span('C3'), B0 = bpOf(SPAN.start), LN = linesOf('C3');
  const rb = t => bpOf(t) - B0;
  const snap8 = x => onBeat(0, Math.round(bpOf(x) * 2) / 2);
  const wordT = (ln, i) => snap8(_karaTimes(ln).tm[i][0]);
  const pop = (t, t0, dur = .18) => t < t0 ? 0 : backOut(clamp((t - t0) / dur), 2.2);
  const kickAt = (t, t0, dur = .25) => { const k = (t - t0) / dur; return k >= 0 && k < 1 ? 1 - k : 0; };
  const CUT = {
    train: snap8(LN[1].start),                   // "It was always training,"
    curves: wordT(LN[1], 4),                     // "and the curves kept gaining,"
    hook2: snap8(LN[2].start),                   // "We didn't start the scaling"
    no: snap8(LN[3].start),                      // "No, we didn't preordain it,"
    contain: wordT(LN[3], 5),                    // "but we can't contain it!"
    roll: LN[3].end,                             // the tracking roll into V4.1
  };

  // ---------- the chorus kit (after c03_chorus1.js) ----------
  function hookWords(ln, t, o = {}) {
    const { words } = _karaTimes(ln), W1 = words.slice(0, 3), W2 = words.slice(3), cx = o.x ?? W / 2, gap = 34;
    const clean = w => w.replace(/[^A-Za-z']/g, '').toUpperCase();
    const row = (ws, off, size, y, styleOf) => {
      const labels = ws.map(clean), wd = labels.map(w => textW(w, size, 'archivo')), tot = wd.reduce((a, v) => a + v, 0) + gap * (ws.length - 1);
      let x = cx - tot / 2;
      labels.forEach((w, i) => {
        const at = wordT(ln, off + i), k = clamp((t - at) / .13);
        if (k > 0) {
          const last = off + i === words.length - 1, s = lerp(last ? 3 : 2.4, 1, backOut(k, last ? 1.5 : 1.2));
          chromeText(w, x + wd[i] / 2, y - (last ? kick(t, 7) * 5 : 0), size, { style: styleOf(i, last), italic: .14, depth: Math.round(size * .11), s, alpha: clamp(k * 3) * (o.alpha ?? 1) });
          if (last && t - at < .5) sweepGlint(x, x + wd[i], y - size * .2, (t - at - .1) / .4, size * .9);
        }
        x += wd[i] + gap;
      });
    };
    row(W1, 0, o.s1 ?? 118, o.y1 ?? 190, () => o.styles?.[0] ?? 'chrome');
    row(W2, 3, o.s2 ?? 170, o.y2 ?? 350, (i, last) => last ? (o.styles?.[2] ?? 'hot') : (o.styles?.[1] ?? 'gold'));
    return wordT(ln, words.length - 1);
  }
  function confetti(t, t0, n = 80, o = {}) {
    if (t < t0) return; const cols = o.cols ?? [EP.magenta, EP.cyan, EP.yellow, EP.lime, EP.white], age = t - t0;
    for (let i = 0; i < n; i++) {
      let x, y;
      if (o.cannon) { const sd = i % 2 ? 1 : -1, v = 1500 + hash2(i, 1) * 900, a = -Math.PI / 2 - sd * (.12 + hash2(i, 2) * .38); x = (o.cx ?? W / 2) + sd * (o.spread ?? 900) + Math.cos(a) * v * age * .9 + Math.sin(age * 4 + i) * 20; y = 1100 + Math.sin(a) * v * age + 900 * age * age; }
      else { x = hash2(i, 1) * W + Math.sin(age * 3 + i) * 30; y = -60 - hash2(i, 2) * 300 + age * (260 + hash2(i, 3) * 200); }
      if (y > H + 40 || y < -80) continue;
      const r = age * 7 + i; ctx.save(); ctx.translate(x, y); ctx.rotate(r); ctx.scale(1, Math.cos(r * 1.3)); ctx.fillStyle = cols[i % cols.length]; ctx.fillRect(-10, -6, 20, 12); ctx.restore();
    }
  }
  const tokenAt = (t, x, y, s, mv, o = {}) => toy(x, y, s, { ...CAST.token.o, ...dance(mv, bpOf(t) - .15), mouth: 'grin', ...o });
  const softAt = (t, x, y, s, mv, o = {}) => toy(x, y, s, { ...CAST.softmax.o, ...dance(mv, bpOf(t)), talk: singK(t), ...o });

  // ---------- the warehouse ----------
  function warehouse(t, o = {}) {
    fillAll('#06040C');
    ctx.fillStyle = '#15121F'; ctx.fillRect(-100, 60, W + 200, 740);
    for (let i = 0; i < 13; i++) { ctx.fillStyle = i % 2 ? 'rgb(255 255 255 / .025)' : 'rgb(0 0 0 / .18)'; ctx.fillRect(i * 160 - 40, 60, 160, 740); }
    for (let w = 0; w < 4; w++) {
      const x0 = 150 + w * 430, y0 = 140, ww = 330, wh = 320; ctx.fillStyle = '#081426'; ctx.fillRect(x0, y0, ww, wh);
      for (let i = 0; i < 4; i++) for (let j = 0; j < 4; j++) { ctx.fillStyle = `rgb(70 120 220 / ${.12 + .22 * hash2(w * 16 + i, j)})`; ctx.fillRect(x0 + 8 + i * 80, y0 + 8 + j * 77, 72, 69); }
      ctx.strokeStyle = '#2A2838'; ctx.lineWidth = 7; ctx.strokeRect(x0, y0, ww, wh);
    }
    ctx.strokeStyle = '#2C283C'; ctx.lineWidth = 12; ctx.beginPath(); ctx.moveTo(-100, 64); ctx.lineTo(W + 100, 64); ctx.stroke();
    ctx.lineWidth = 5; ctx.beginPath(); for (let x = -120; x < W + 120; x += 120) { ctx.moveTo(x, 64); ctx.lineTo(x + 60, -10); ctx.lineTo(x + 120, 64); } ctx.stroke();
    ctx.fillStyle = lg(0, 800, 0, 1080, [[0, '#1C1826'], [1, '#07050C']]); ctx.fillRect(-100, 800, W + 200, 400);
    haze(340, 460, '#9A70FF', .1 + (o.haze ?? 0)); haze(700, 320, '#50FFB0', .07 + (o.haze ?? 0) * .5);
  }
  // a box-truss beam (two rails and a zigzag)
  function truss(ax, ay, bx, by, w) {
    const L = Math.hypot(bx - ax, by - ay), a = Math.atan2(by - ay, bx - ax);
    ctx.save(); ctx.translate(ax, ay); ctx.rotate(a);
    ctx.strokeStyle = '#8A8EA0'; ctx.lineWidth = 6; ctx.beginPath(); ctx.moveTo(0, -w / 2); ctx.lineTo(L, -w / 2); ctx.moveTo(0, w / 2); ctx.lineTo(L, w / 2); ctx.stroke();
    ctx.lineWidth = 3; ctx.beginPath(); for (let x = 0; x < L; x += w) { ctx.moveTo(x, -w / 2); ctx.lineTo(x + w / 2, w / 2); ctx.lineTo(x + w, -w / 2); } ctx.stroke();
    ctx.restore();
  }

  // ---------- the boulevard and the float ----------
  // phase: 0 noon, 1 golden hour, 2 dusk, 3 night; scroll: how far the float has rolled (px)
  function boulevard(t, ph, scroll, o = {}) {
    const P = [[['#1A5AE8', '#8ACBFF'], '#FFF4B0'], [['#3A1A8A', '#FF6A3A', '#FFD04A'], '#FFE8A0'], [['#12063A', '#6A1A8A', '#FF6A5A'], '#FFB090'], [['#02031A', '#0A1446'], '#C8D8FF']];
    const i0 = Math.floor(ph), f = ph - i0, A = P[Math.min(3, i0)], B = P[Math.min(3, i0 + 1)];
    const top = mixCol(A[0][0], B[0][0], f), bot = mixCol(A[0].at(-1), B[0].at(-1), f), hz = o.horizon ?? 600;
    bgGrad([[0, top], [1, bot]], { y1: hz });
    if (ph > 2) for (let i = 0; i < 60; i++) { ctx.fillStyle = `rgb(255 255 255 / ${clamp(ph - 2) * (.25 + .55 * hash(i))})`; ctx.fillRect(hash2(i, 1) * W, hash2(i, 2) * (hz - 150), 3, 3); }
    // the sun (sinking) or the moon
    const sy = lerp(170, hz + 60, clamp(ph / 2.2)), sc = mixCol('#FFF6C0', '#FF7A3A', clamp(ph / 2));
    const sx = lerp(1180, 1500, clamp(ph)); if (ph < 2.4) { glow(sx, sy, 420, sc, .7); glossBall(sx, sy, 80, 80, sc, { rim: null, lw: 4 }); }
    if (ph > 2.3) glossBall(420, 200, 50, 50, '#F4F0D8', { rim: null, lw: 4, alpha: clamp(ph - 2.3) });
    // the skyline and the victory column (far parallax)
    const dim = clamp(ph / 3), bcol = mixCol('#6A7AAA', '#0A0A24', dim);
    for (let i = 0; i < 16; i++) { const w = 110 + hash(i + 60) * 150, h = 90 + hash(i + 61) * 190, x = ((i * 170 - scroll * .15) % (W + 400) + W + 400) % (W + 400) - 200; ctx.fillStyle = bcol; ctx.fillRect(x, hz - h, w, h + 10); if (ph > 1.8) for (let q = 0; q < 6; q++) if (hash2(i, q) < .5) { ctx.fillStyle = alpha('#FFE08A', clamp(ph - 1.8) * .8); ctx.fillRect(x + 12 + (q % 3) * (w / 3.2), hz - h + 20 + Math.floor(q / 3) * 40, 14, 18); } }
    const cx = ((900 - scroll * .08) % (W + 800) + W + 800) % (W + 800) - 400;
    ctx.fillStyle = mixCol('#C8B890', '#2A2440', dim); ctx.fillRect(cx - 22, hz - 380, 44, 380); ctx.fillRect(cx - 50, hz - 60, 100, 60); ctx.fillRect(cx - 40, hz - 392, 80, 16);
    ctx.save(); ctx.translate(cx, hz - 440); ctx.rotate(t * .5); poly(starPts(0, 0, 44, .45, 5)); paint(EP.gold, EP.line, 3); ctx.restore(); glint(cx, hz - 440, 70 * (.5 + .5 * Math.sin(t * 3)), .8);
    // trees roll past
    ctx.fillStyle = mixCol('#3A3A48', '#15151E', dim); ctx.fillRect(-100, hz, W + 200, H);
    for (let i = 0; i < 11; i++) {
      const x = ((i * 230 - scroll * .6) % (W + 460) + W + 460) % (W + 460) - 230, y = hz + 30;
      ctx.fillStyle = mixCol('#5A3A2A', '#1A1010', dim); ctx.fillRect(x - 10, y - 80, 20, 110);
      glossBall(x, y - 150, 90, 80, mixCol('#3AAA4A', '#0A2A1A', dim), { lw: 4, rim: ph > 2.5 ? EP.cyan : null, spec: .3 });
      if (ph > 2.3 && i % 2 === 0) { ctx.fillStyle = '#3A3A48'; ctx.fillRect(x + 110, y - 250, 8, 290); glow(x + 114, y - 250, 120, '#FFD890', .6 * clamp(ph - 2.3)); glossBall(x + 114, y - 250, 16, 12, '#FFF4C0', { rim: null, lw: 2 }); }
    }
    ctx.fillStyle = mixCol('#8A8E9E', '#2A2A36', dim); ctx.fillRect(-100, hz + 60, W + 200, 10);
    for (let i = 0; i < 12; i++) { const x = ((i * 200 - scroll) % (W + 200) + W + 200) % (W + 200) - 100; ctx.fillStyle = alpha('#FFFFFF', .5 - dim * .3); ctx.fillRect(x, 1000, 110, 12); }
  }
  // the parade float: a flatbed truck (cab at the right) with speaker stacks, bunting, a banner and the EPOCH counter on its side.
  // (x, deckY): the deck (dancers stand at deckY); s: scale. o.roll (wheel angle), o.epoch, o.shrug (0..1), o.sign (LED text on the cab), o.blow (0..1 cones blown)
  function floatTruck(x, deckY, s, t, o = {}) {
    const L = x - 740 * s, R = x + 470 * s, sh = o.shrug ?? 0, dY = deckY + sh * 30 * s, lift = sh * 150 * s, k = kick(t, 8);
    // bunting between the stacks (behind)
    const by = dY - 470 * s - lift;
    ctx.strokeStyle = '#E8E8F0'; ctx.lineWidth = 3; ctx.beginPath(); ctx.moveTo(L + 90 * s, by); ctx.quadraticCurveTo(x - 135 * s, by + 110 * s, R - 90 * s, by); ctx.stroke();
    for (let i = 1; i < 14; i++) { const u = i / 14, bx = lerp(L + 90 * s, R - 90 * s, u), yy = by + 4 * u * (1 - u) * 110 * s; poly([[bx - 18 * s, yy], [bx + 18 * s, yy], [bx, yy + 42 * s + Math.sin(t * 6 + i) * 4]]); ctx.fillStyle = [EP.magenta, EP.cyan, EP.yellow, EP.lime][i % 4]; ctx.fill(); ctx.strokeStyle = EP.line; ctx.lineWidth = 2; ctx.stroke(); }
    // speaker stacks (they lift like shoulders on the shrug)
    for (const sx of [L + 90 * s, R - 90 * s]) for (let i = 0; i < 2; i++) {
      const w = 150 * s, y = dY - i * w * 1.7 - lift * (i + 1) * .5;
      speaker(sx, y, w, t, { col: '#1A1A28' });
      if (o.blow > 0) for (const [cy, r] of [[.26, .16], [.62, .34]]) for (const lag of [0, .25]) { const a = clamp(o.blow - lag); if (a <= 0 || a >= 1) continue; ctx.save(); ctx.globalCompositeOperation = 'lighter'; ctx.strokeStyle = `rgb(255 ${lag ? 90 : 220} ${lag ? 90 : 150} / ${(1 - a) * .9})`; ctx.lineWidth = 22 * (1 - a) + 3; ell(sx, y - w * 1.7 + w * 1.7 * cy, w * r * (1 + a * 12), w * r * (1 + a * 12)); ctx.stroke(); ctx.restore(); }
    }
    // the deck, skirt, cab and wheels
    gloss(pfRR(L, dY, R - L, 26 * s, 6), '#D8DCE8', { box: [L, dY, R - L, 26 * s], lw: 4, spec: 1 });
    gloss(pfRR(L + 10 * s, dY + 26 * s, R - L - 20 * s, 124 * s, 10), '#E0208A', { box: [L, dY + 26 * s, R - L, 124 * s], lw: 5, spec: .7, rim: EP.yellow });
    ctx.fillStyle = lg(L, 0, R, 0, [[0, '#FF2A6A'], [.2, '#FF9A1A'], [.4, '#FFE81F'], [.6, '#3BFF6A'], [.8, '#1FB8FF'], [1, '#B04BFF']]); ctx.fillRect(L + 14 * s, dY + 128 * s, R - L - 28 * s, 10 * s);
    ptext('SCALING PARADE', L + 400 * s, dY + 60 * s, 44 * s, { font: 'archivo', fill: '#FFFFFF', strokes: [[EP.line, 9 * s]], maxW: 600 * s });
    if (o.epoch !== undefined) { ctx.fillStyle = '#05050A'; rrect(x + 50 * s, dY + 38 * s, 390 * s, 90 * s, 10 * s); ctx.fill(); pixText('EPOCH', x + 64 * s, dY + 50 * s, 3.6 * s, EP.laser); segText(String(Math.floor(o.epoch)).padStart(7, ' '), x + 150 * s, dY + 48 * s, 66 * s, EP.laser, { off: '#062006' }); }
    const cT = dY - 230 * s;
    gloss(() => { ctx.moveTo(R, dY + 150 * s); ctx.lineTo(R, cT + 20 * s); ctx.quadraticCurveTo(R, cT, R + 30 * s, cT); ctx.lineTo(R + 190 * s, cT); ctx.lineTo(R + 300 * s, dY - 40 * s); ctx.lineTo(R + 310 * s, dY + 150 * s); ctx.closePath(); }, '#12B3E8', { box: [R, cT, 310 * s, 380 * s], lw: 5, spec: .9, rim: EP.white });
    poly([[R + 120 * s, cT + 26 * s], [R + 186 * s, cT + 26 * s], [R + 272 * s, dY - 50 * s], [R + 120 * s, dY - 50 * s]]); ctx.fillStyle = lg(0, cT, 0, dY, [[0, '#E0F4FF'], [1, '#3A7AB8']]); ctx.fill(); ctx.strokeStyle = EP.line; ctx.lineWidth = 4; ctx.stroke();
    glossBall(R + 296 * s, dY + 60 * s, 20 * s, 26 * s, EP.yellow, { lw: 3, rim: null }); if (o.lights) glow(R + 300 * s, dY + 60 * s, 260 * s, '#FFF4C0', .6);
    if (o.sign !== undefined) { ctx.fillStyle = '#05050A'; rrect(R + 10 * s, cT - 110 * s, 290 * s, 100 * s, 10 * s); ctx.fill(); ctx.strokeStyle = '#8A8EA0'; ctx.lineWidth = 4; ctx.stroke(); pixText(o.sign, R + 155 * s, cT - 90 * s, Math.min(8.5 * s, 260 * s / (o.sign.length * 6)), o.signCol ?? EP.amber, { align: 'center', glow: true }); }
    for (const wx of [L + 150 * s, L + 360 * s, R + 190 * s]) { glossBall(wx, dY + 150 * s, 64 * s, 64 * s, '#15151E', { lw: 4, rim: null }); ctx.save(); ctx.translate(wx, dY + 150 * s); ctx.rotate(o.roll ?? 0); ctx.fillStyle = '#C8CCD8'; ell(0, 0, 30 * s, 30 * s); ctx.fill(); ctx.strokeStyle = '#6A6E7E'; ctx.lineWidth = 5 * s; for (let q = 0; q < 5; q++) { ctx.rotate(TAU / 5); ctx.beginPath(); ctx.moveTo(0, 0); ctx.lineTo(28 * s, 0); ctx.stroke(); } ctx.restore(); }
    return { L, R, dY, lift };
  }

  // =====================================================================================================
  // A. "We didn't start the scaling": the warehouse. Dark for the "We" pickup (only the glowsticks), then the lights slam on at the downbeat:
  // strobes, lasers through the smoke, the trio on the truss stage, and the hook in chrome.
  // =====================================================================================================
  function shotHook1(t) {
    hideCaption();
    const r = rb(t), on = clamp((r - .5) / .06), bb = bpOf(t), land = wordT(LN[0], 4), sh = shakeAt(t, t, land, .3, 16);
    setLight({ rim: EP.laser, rimK: .65 });
    camBegin(W / 2 - sh[0], H / 2 - sh[1], 1 + .03 * clamp(r / 4));
    warehouse(t, { haze: .05 * on });
    // the truss stage
    const d0 = 470, d1 = 1450, dy = 820;
    truss(d0 - 20, 120, d1 + 20, 120, 40); truss(d0, 120, d0, dy, 36); truss(d1, 120, d1, dy, 36);
    for (let i = 0; i < 6; i++) { const x = lerp(d0 + 70, d1 - 70, i / 5); rrect(x - 20, 138, 40, 34, 6); paint('#15131E', EP.line, 2); }
    const open = easeOut(clamp((r - .5) / .5));
    laserFan(d0 + 70, 160, t, { n: 9, cols: [EP.laser, EP.cyan], angle: Math.PI * .62, spread: 1.1 * open + .01, sweep: .5, alpha: open * .8, flicker: .4 });
    laserFan(d1 - 70, 160, t, { n: 9, cols: [EP.magenta, EP.uv], angle: Math.PI * .38, spread: 1.1 * open + .01, sweep: .5, phase: 2, alpha: open * .8, flicker: .4 });
    laserFan(W / 2, 800, t, { n: 15, cols: [EP.laser, EP.white], angle: -Math.PI / 2, spread: 2.8 * open + .01, sweep: .25, alpha: .5 * open });
    gloss(pfRR(d0 - 30, dy, d1 - d0 + 60, 70, 8), '#23202E', { box: [d0 - 30, dy, d1 - d0 + 60, 70], lw: 5, rim: EP.laser });
    ctx.fillStyle = lg(d0, 0, d1, 0, [[0, EP.laser], [.5, EP.cyan], [1, EP.magenta]]); ctx.fillRect(d0 - 20, dy + 52, d1 - d0 + 40, 8);
    tokenAt(t, 640, dy + 4, 30, 'runningMan');
    softAt(t, 960, dy + 4, 33, r < 2.9 ? 'sing' : 'raise', { turn: Math.sin(t * 1.3) * .3, swing: .5 + Math.sin(t * 7) * .25 });
    djClawd(1280, dy - 63, 17, { shades: true, aL: 1.1 + Math.sin(bb * Math.PI) * .35, aR: lerp(-.1, -.45, kickAt(bb, Math.floor(bb), .3)), mouth: 'grin', dy: -bounce(t) * .3 });
    djBooth(1280, dy - 90, 270, t, { scratch: kickAt(bb, Math.floor(bb), .3) });
    raveCrowd(t, { y: 1100, rows: 3, n: 13, s: 1.3, k: .5 + .5 * on, hands: .5 + .4 * on, sticks: .9, rim: on ? EP.laser : EP.uv, cols: [EP.laser, EP.magenta, EP.cyan, EP.yellow] });
    camEnd();
    if (on < 1) { ctx.save(); ctx.fillStyle = `rgb(4 0 12 / ${.88 * (1 - on)})`; ctx.fillRect(-100, -100, W + 200, H + 200); ctx.restore(); raveCrowd(t, { y: 1080, rows: 1, n: 13, s: 1.3, k: .4, hands: .9, sticks: 1, col: '#000', rim: EP.uv, seed: 7 }); }
    hookWords(LN[0], t, { y1: 200, y2: 360, s1: 112, s2: 168 });
    if (r >= .5 && r < .9) strobe(.9 * (1 - (r - .5) / .4));
    else strobe(strobeK(t, 2, .2) * .2 * on);
    if (r > .5 && r < .62) fx({ rgb: 1 - (r - .5) / .12 });
  }

  // =====================================================================================================
  // B. "It was always training,": the float at noon rolling down the boulevard; the EPOCH counter on its side never stops.
  // =====================================================================================================
  function shotTrain(t) {
    const l = t - CUT.train, bb = bpOf(t), scroll = l * 420;
    setLight({ rim: EP.white, rimK: .35 });
    camBegin(W / 2, H / 2 + Math.sin(bb * Math.PI * 2) * 3, 1);
    boulevard(t, 0, scroll + 800);
    const fy = 640 - Math.abs(Math.sin(bb * Math.PI)) * 4;
    const tr = floatTruck(860, fy, .82, t, { roll: -scroll / 52, epoch: 88000 + Math.floor(l * 3170) });
    tokenAt(t, tr.L + 300, tr.dY, 30, 'shuffle');
    softAt(t, 860, tr.dY, 34, 'sing', { turn: .25 });
    djClawd(tr.R - 250, tr.dY - 42, 13, { shades: true, aL: 1.1 + Math.sin(bb * Math.PI) * .35, aR: .9 - Math.sin(bb * Math.PI) * .35, mouth: 'grin', dy: -bounce(t) * .3 });
    djBooth(tr.R - 250, tr.dY - 80, 230, t);
    raveCrowd(t, { y: 1100, rows: 2, n: 15, s: 1.2, k: 1, hands: .7, sticks: .3, col: '#2A1A4A', rim: EP.white, cols: [EP.magenta, EP.yellow, EP.cyan] });
    camEnd();
    confetti(t, CUT.train - 1, 50, { cols: [EP.magenta, EP.yellow, EP.cyan, '#FFFFFF'] });
    if (l < .1) cutFX('flash');
  }

  // =====================================================================================================
  // C. "and the curves kept gaining,": back in the warehouse smoke, a laser draws the exponential a notch per beat (×1.9 a notch, steeper
  // than C1's pipe), the camera tilts after it, and it runs off the top.
  // =====================================================================================================
  const G3 = 1.9;
  function curvePts(n, x0 = 220, y0 = 900, dx = 200, h0 = 14) { const pts = [[x0, y0]]; let h = h0, y = y0; for (let i = 0; i < n; i++) { const [px] = pts.at(-1); y -= h; pts.push([px + dx, y]); h *= G3; } return pts; }
  function shotCurves(t) {
    const l = t - CUT.curves, bb = bpOf(t), t0 = snap8(CUT.curves), nb = (t - t0) / beatLen(), notch = Math.floor(nb), camY = lerp(540, 380, ease(clamp(l / 3.2)));
    setLight({ rim: EP.laser, rimK: .9 });
    camBegin(W / 2, camY, 1);
    warehouse(t, { haze: .06 });
    ctx.fillStyle = 'rgb(0 0 0 / .45)'; ctx.fillRect(-100, -400, W + 200, 1600);
    // a laser graph-paper grid hanging in the smoke
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; ctx.strokeStyle = 'rgb(60 255 120 / .13)'; ctx.lineWidth = 2; ctx.beginPath(); for (let x = 20; x < W; x += 200) { ctx.moveTo(x, -400); ctx.lineTo(x, 900); } for (let y = 900; y > -400; y -= 100) { ctx.moveTo(-100, y); ctx.lineTo(W + 100, y); } ctx.stroke(); ctx.restore();
    // the curve, drawn by the laser up to the current notch (with a smooth exponential between the notch points)
    const P = curvePts(9), fr = clamp(frac(Math.max(0, nb)) / .4), upto = Math.max(0, Math.min(P.length - 1, notch + easeOut(fr)));
    const sm = []; for (let i = 0; i <= upto * 12; i++) { const u = i / 12, a = Math.floor(u), f = u - a, A = P[a], B = P[Math.min(P.length - 1, a + 1)]; sm.push([lerp(A[0], B[0], f), A[1] + (B[1] - A[1]) * (Math.pow(G3, f) - 1) / (G3 - 1)]); }
    const tip = sm.at(-1) ?? P[0];
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; ctx.lineCap = 'round'; ctx.lineJoin = 'round';
    ctx.beginPath(); sm.forEach(([x, y], i) => i ? ctx.lineTo(x, y) : ctx.moveTo(x, y));
    ctx.strokeStyle = alpha(EP.laser, .22); ctx.lineWidth = 46; ctx.stroke(); ctx.strokeStyle = alpha(EP.laser, .9); ctx.lineWidth = 12; ctx.stroke(); ctx.strokeStyle = '#EFFFF0'; ctx.lineWidth = 4; ctx.stroke();
    ctx.restore();
    // the crowd and SOFTMAX under it
    raveCrowd(t, { y: 1090, rows: 2, n: 13, s: 1.25, k: 1, hands: .8, sticks: .9, rim: EP.laser, cols: [EP.laser, EP.magenta, EP.cyan] });
    softAt(t, 1560, 1030, 40, 'raise', { rim: EP.laser });
    camEnd();
    const tipY = tip[1] - (camY - 540);
    if (tipY > -40) lensFlare(tip[0], tipY, .7 + .25 * kick(t, 5), { col: EP.laser }); else lensFlare(Math.min(W - 80, tip[0]), 20, .8, { col: EP.laser });
    const ja = nb - notch;
    if (notch >= 0 && ja < .5 && tipY > 0) glint(tip[0], tipY, 110 * (1 - ja * 2), 1 - ja * 2);
    if (notch >= 0 && tipY > 80) { const v = G3 ** (notch + 1), lab = '×' + (v < 10 ? v.toFixed(1).replace('.0', '') : Math.round(v)), k = clamp(ja / .12); chromeText(lab, Math.min(W - 220, tip[0] + 170), tipY + 30, 100, { style: 'lime', italic: .12, depth: 10, s: lerp(1.5, 1, easeOut(k)), alpha: clamp(k * 3) }); }
    strobe(strobeK(t, 1, .14) * .15);
    if (l < .1) cutFX('rgb');
  }

  // =====================================================================================================
  // D. "We didn't start the scaling" (2): golden hour on the float. SOFTMAX on top of the speaker stack, the hook in chrome, confetti
  // cannons from the float on SCALING.
  // =====================================================================================================
  function shotHook2(t) {
    hideCaption();
    const l = t - CUT.hook2, bb = bpOf(t), land = wordT(LN[2], LN[2].text.split(' ').length - 1);
    setLight({ rim: EP.orange, rimK: .45 });
    camBegin(W / 2, H / 2 + 20 - 20 * ease(clamp(l / 2)), 1.02);
    boulevard(t, 1, 1600 + l * 300, { horizon: 700 });
    rays(1500, 520, 20, 'rgb(255 240 180 / .1)', t * .3);
    // the deck edge and the stack
    const dk = 950;
    gloss(pfRR(-60, dk, W + 120, 40, 6), '#D8DCE8', { box: [0, dk, W, 40], lw: 4, spec: 1 }); ctx.fillStyle = '#E0208A'; ctx.fillRect(-60, dk + 40, W + 120, 200);
    const sx = 1300, k8 = kick(t, 8);
    speaker(sx, dk, 140, t, { col: '#1A1A28' }); speaker(sx, dk - 238, 140, t, { col: '#1A1A28' });
    for (const x of [300, 520]) { speaker(x, dk, 130, t, { col: '#1A1A28' }); }
    softAt(t, sx, dk - 476 + 6, 30, t < land ? 'sing' : 'raise', { swing: .6 + Math.sin(t * 7) * .3, turn: -.2, jump: t > land ? Math.abs(Math.sin((t - land) * 7)) * .3 : 0 });
    tokenAt(t, 790, dk + 6, 34, 'pump');
    djClawd(1040, dk - 30, 13, { shades: true, aL: 1.2 + Math.sin(bb * Math.PI) * .3, aR: 1.2 - Math.sin(bb * Math.PI) * .3, mouth: 'grin', dy: -bounce(t) * .5 });
    raveCrowd(t, { y: 1230, rows: 1, n: 12, s: 1.5, k: 1, hands: 1, sticks: .5, col: '#3A0A2A', rim: EP.yellow });
    camEnd();
    hookWords(LN[2], t, { x: 640, y1: 190, y2: 360, s1: 100, s2: 160, styles: ['gold', 'chrome', 'hot'] });
    lensFlare(1500, 520, .7 + .2 * k8);
    confetti(t, land, 120, { cannon: true, cx: 900, spread: 700 });
    if (t > land && t < land + .12) strobe(.5 * (1 - (t - land) / .12)); else strobe(strobeK(t, 1, .14) * .12);
    if (l < .1) cutFX('zoom');
  }

  // =====================================================================================================
  // E. "No, we didn't preordain it,": dusk. NO! flashes on the cab's LED sign as SOFTMAX wags her finger; then the whole float shrugs
  // (speaker stacks up like shoulders, the deck dips) and "?" balloons float off it.
  // =====================================================================================================
  function qBalloon(x, y, s, col, t, i) {
    ctx.strokeStyle = 'rgb(255 255 255 / .7)'; ctx.lineWidth = 2; ctx.beginPath(); ctx.moveTo(x, y + 130 * s); ctx.quadraticCurveTo(x + Math.sin(t * 3 + i) * 20, y + 220 * s, x, y + 300 * s); ctx.stroke();
    chromeText('?', x, y, 220, { style: col, depth: 20, s, sx: s * (.4 + .6 * Math.abs(Math.cos(t * 2.4 + i))) });
  }
  function shotNo(t) {
    const l = t - CUT.no, bb = bpOf(t), shrugAt = wordT(LN[3], 3), shrug = t >= shrugAt - .05, sk = shrug ? Math.exp(-frac(bpOf(t) - bpOf(shrugAt)) * 3) * .6 + .4 * Math.min(1, (t - shrugAt) / .1) : 0;
    setLight({ rim: EP.magenta, rimK: .7 });
    camBegin(W / 2, H / 2, 1);
    boulevard(t, 2, 2400 + l * 160);
    const tr = floatTruck(820, 640, .82, t, { roll: -l * 3, shrug: shrug ? clamp(sk) : 0, sign: shrug ? '? ? ?' : 'NO!', signCol: shrug ? EP.cyan : EP.red, epoch: 190000 + Math.floor(l * 3170), lights: true });
    const wag = Math.sin(bb * Math.PI * 2) * .9, S = shrug ? dance('shrug', bb) : null;
    tokenAt(t, tr.L + 300, tr.dY, 30, 'bounce', shrug ? { ...S, eyes: 'dot', mouth: 'flat' } : { mic: 'R', ...dance('rap', bb) });
    softAt(t, 820, tr.dY, 34, 'sing', shrug ? { ...S, talk: singK(t) } : { hR: [2.3 + wag, -9.2], gR: 'point', hL: [-2.4, -4.4], gL: 'fist', headTilt: wag * .06, brows: 'angry' });
    djClawd(tr.R - 250, tr.dY - 2 - (shrug ? 10 : 0), 13, { shades: true, aL: shrug ? .5 : -.6, aR: shrug ? .5 : -.6, mouth: shrug ? 'o' : 'grin' });
    raveCrowd(t, { y: 1100, rows: 2, n: 15, s: 1.2, k: shrug ? .4 : 1, hands: shrug ? .2 : .6, sticks: .5, col: '#1A0A2A', rim: EP.magenta });
    camEnd();
    if (!shrug) burst('NO!', 1500, 330, 150, { pop: pop(t, CUT.no + .02, .2), col: EP.yellow, ink: EP.magenta, spin: .3 });
    if (shrug) for (let i = 0; i < 5; i++) { const a = t - shrugAt - i * .07; if (a < 0) continue; qBalloon(260 + i * 330 + Math.sin(t * 2 + i) * 30, 560 - a * 330 - (i % 2) * 60, .8 + (i % 3) * .15, ['ice', 'hot', 'gold', 'lime', 'purple'][i], t, i); }
    if (l < .1) cutFX('flash');
  }

  // =====================================================================================================
  // F. "but we can't contain it!": night. The crowd leans on the COMPUTE CAP barriers harder every beat; on "contain" the speaker cones
  // blow out in rings, the barriers fly and the crowd surges over the camera. Then the tail: a VHS tracking roll into V4.1.
  // =====================================================================================================
  function shotContain(t) {
    const bb = bpOf(t), tb = wordT(LN[3], 8), br = t - tb, tit = wordT(LN[3], 9), push = Math.exp(-frac(bb) * 5);
    const sh = shakeAt(t, t, tb, .5, 26), sh2 = t > tit ? shakeXY(t, 10) : [0, 0];
    setLight({ rim: EP.red, rimK: .85 });
    camBegin(W / 2 - sh[0] - sh2[0], H / 2 - sh[1] - sh2[1], 1 + (br > 0 ? .05 * clamp(br / 1.2) : 0));
    boulevard(t, 3, 3000 + (t - CUT.contain) * 80, { horizon: 560 });
    const tr = floatTruck(900, 520, .55, t, { roll: -t * 2, sign: br > 0 ? 'NO CAP!' : 'LIMIT', signCol: br > 0 ? EP.red : EP.amber, blow: br > 0 ? frac(br / beatLen()) * 1.3 : 0, lights: true });
    if (br > 0 && br < .6) { const a = br / .6; ctx.save(); ctx.globalCompositeOperation = 'lighter'; ctx.strokeStyle = `rgb(255 150 190 / ${.8 * (1 - a)})`; ctx.lineWidth = 30 * (1 - a) + 3; ell(900, 380, 100 + a * 1300, 70 + a * 900); ctx.stroke(); ctx.restore(); }
    tokenAt(t, tr.L + 200, tr.dY, 20, br > 0 ? 'jump' : 'pump');
    softAt(t, 900, tr.dY, 23, br > 0 ? 'raise' : 'sing');
    // lasers over the street
    laserFan(tr.L + 60, tr.dY - 500, t, { n: 7, cols: [EP.red, EP.magenta], angle: -Math.PI / 2 - .5, spread: 1.2, sweep: .5, alpha: .6, flicker: br > 0 ? .8 : 0 });
    laserFan(tr.R + 60, tr.dY - 500, t, { n: 7, cols: [EP.cyan, EP.white], angle: -Math.PI / 2 + .5, spread: 1.2, sweep: .5, phase: 2, alpha: .6, flicker: br > 0 ? .8 : 0 });
    // the crowd behind the barriers, surging after the blowout
    const surge = br > 0 ? easeIn(clamp(br / 1.1)) : 0;
    raveCrowd(t, { y: 820 + surge * 160, rows: 2, n: 16, s: .9 + surge * .5, k: 1, hands: br > 0 ? 1 : .6, sticks: .6, col: '#10061E', rim: EP.red, cols: [EP.red, EP.yellow, EP.magenta] });
    // the barriers
    for (let i = 0; i < 7; i++) {
      const x0 = -40 + i * 290, fly = br > 0 ? clamp((br - hash(i) * .12) / .7) : 0, wob = br > 0 ? 0 : push * (3 + i % 3) * .01 * Math.sin(i * 2 + bb * Math.PI);
      ctx.save(); ctx.translate(x0 + 140 + fly * (i - 3) * 200, 900 + fly * 400 - Math.sin(fly * Math.PI) * 260); ctx.rotate(wob + fly * (i % 2 ? 2.2 : -2.2)); ctx.scale(1 + fly * .8, 1 + fly * .8);
      ctx.strokeStyle = '#C8CCD8'; ctx.lineWidth = 9; ctx.strokeRect(-135, -120, 270, 130); ctx.lineWidth = 5; ctx.beginPath(); for (let q = -110; q <= 110; q += 22) { ctx.moveTo(q, -120); ctx.lineTo(q, 10); } ctx.stroke();
      ctx.lineWidth = 8; ctx.beginPath(); ctx.moveTo(-120, 10); ctx.lineTo(-150, 70); ctx.moveTo(120, 10); ctx.lineTo(150, 70); ctx.stroke();
      rrect(-100, -92, 200, 56, 6); paint(EP.yellow, EP.line, 3); txt('COMPUTE CAP', 0, -63, 26, EP.line, { font: 'archivo', maxW: 186 });
      ctx.restore();
    }
    // the front row, over the camera
    if (t > tit - .2) raveCrowd(t, { y: 1230 - clamp((t - tit + .2) / .5) * 120, rows: 1, n: 8, s: 2.4, k: 1, hands: 1, sticks: .5, col: '#08030E', rim: EP.red, seed: 5 });
    camEnd();
    if (br > 0 && br < .12) fx({ rgb: 1 - br / .12 });
    if (t > tit && t < tit + .1) fx({ rgb: .7, zoom: .6 });
    strobe(br > 0 ? strobeK(t, 2, .3) * .4 : kickAt(bb, Math.floor(bb), .12) * .12, br > 0 && frac(bb) < .5 ? '#FF3040' : '#FFFFFF');
    if (t - CUT.contain < .1) cutFX('rgb');
  }
  // the tracking roll: the finished picture rolls up through a band of VHS noise
  function trackingRoll(t) {
    const k = clamp((t - CUT.roll) / (SPAN.end - CUT.roll)), G = _grab('c07roll'), cw = canvas.width, ch = canvas.height, off = Math.round(easeIn(k) * ch * 1.15) % ch, bh = ch * .09, f = Math.floor(t * 30);
    ctx.save(); ctx.setTransform(1, 0, 0, 1, 0, 0);
    ctx.drawImage(G, 0, -off); ctx.drawImage(G, 0, ch - off);
    for (let i = 0; i < 6; i++) { const y = Math.floor(hash2(i, f) * ch), h = ch * .02; ctx.drawImage(G, 0, y, cw, h, (hash2(i + 5, f) - .5) * cw * .06 * (k + .2), y, cw, h); }
    const by = ch - off - bh / 2; ctx.fillStyle = 'rgb(6 6 14 / .9)'; ctx.fillRect(0, by, cw, bh);
    for (let i = 0; i < 40; i++) { ctx.fillStyle = `rgb(255 255 255 / ${.25 + .6 * hash2(i, f)})`; ctx.fillRect(hash2(i + 3, f) * cw - 100, by + hash2(i, f + 7) * bh, (40 + hash2(i + 9, f) * 420) * cw / W, 3); }
    ctx.restore();
    if (frac(t * 3) < .7) pixText('TRACKING', 1500, 880, 6, '#FFFFFF', { align: 'center', edge: '#000' });
  }

  section('C3', (p, lt, d, t) => {
    if (t < CUT.train) return shotHook1(t);
    if (t < CUT.curves) return shotTrain(t);
    if (t < CUT.hook2) return shotCurves(t);
    if (t < CUT.no) return shotHook2(t);
    if (t < CUT.contain) return shotNo(t);
    shotContain(t);
    if (t >= CUT.roll) trackingRoll(t);
  });
})();

;
// ---- styles/eurodance/ch/c08_v4.js ----
// c08_v4 — Verse 4: Aug 26 → Sep 22 2026, "hardcore". MC TOKEN's last headline list: shorter fuses, more shake, hits inside the lines.
// Colour run: GeoCities yellow / arcade red-black / police-light navy / boot-screen sky / lava purple / race night→noon / club red /
// karaoke teal / cosmic-bowling UV / church amber / blueprint violet / RTS ocean / title-screen black / news-desk white / strobe red /
// jackpot gold. The gift box that rattles on the decks in V4.15 bursts open in V4.16 and hands over to the last chorus.
(() => {
  const bt = (t, lt, k = 0) => beatIn(t, lt, k);
  const BL = () => beatLen();
  const pop = (lt, t0, dur = .18) => lt < t0 ? 0 : backOut(clamp((lt - t0) / dur), 2.2);
  const tok = t => ({ talk: singK(t) });
  // the start of word i of V4 line n (this take's karaoke alignment), as lt inside the line's window
  const _L = {};
  const wl = (n, i, t, lt) => { const ln = _L[n] ??= LINES.find(l => l.sec === 'V4' && l.n === n), tm = _karaTimes(ln).tm; return tm[Math.min(i, tm.length - 1)][0] - (t - lt); };
  // a rubber-stamp slam scaling down from 1.9× as it lands
  function slamStamp(str, x, y, size, col, rot, k) {
    if (k <= 0) return; const s = k < 1 ? lerp(1.9, 1, easeOut(k)) : 1, w = textW(str, size, 'archivo', 2) + size * .9, h = size * 1.5;
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot); ctx.scale(s, s); ctx.globalAlpha *= clamp(k * 3) * .92;
    ctx.strokeStyle = col; ctx.lineWidth = size * .1; rrect(-w / 2, -h / 2, w, h, size * .2); ctx.stroke(); ctx.lineWidth = size * .04; rrect(-w / 2 + size * .16, -h / 2 + size * .16, w - size * .32, h - size * .32, size * .12); ctx.stroke();
    txt(str, 0, size * .05, size, col, { font: 'archivo', spacing: 2 });
    ctx.restore();
  }
  // glossy confetti chips falling since t0
  function confetti(t, t0, n = 60, o = {}) {
    if (t < t0) return; const cols = o.cols ?? [EP.magenta, EP.cyan, EP.yellow, EP.lime, EP.white];
    for (let i = 0; i < n; i++) { const age = t - t0, x = (o.x0 ?? 0) + hash2(i, 1) * ((o.x1 ?? W) - (o.x0 ?? 0)) + Math.sin(age * 3 + i) * 30, y = (o.y0 ?? -60) - hash2(i, 2) * 300 + age * (260 + hash2(i, 3) * 200); if (y > H + 40) continue; const r = age * 6 + i; ctx.save(); ctx.translate(x, y); ctx.rotate(r); ctx.scale(1, Math.cos(r * 1.3)); ctx.fillStyle = cols[i % cols.length]; ctx.fillRect(-9, -5, 18, 10); ctx.restore(); }
  }
  // a glossy comic speech bubble: lines = [[text, size, font?]…], tail toward o.to
  function sayBubble(lines, x, y, o = {}) {
    const k = o.pop ?? 1; if (k <= 0) return;
    const ws = lines.map(([s, sz, f]) => textW(s, sz, f ?? 'archivo')), w = Math.max(...ws) + 80, h = lines.reduce((a, [, sz]) => a + sz * 1.15, 0) + 46;
    ctx.save(); ctx.translate(x, y); const sc = backOut(clamp(k), 2.4); ctx.scale(sc, sc); if (o.rot) ctx.rotate(o.rot);
    const to = o.to ? [(o.to[0] - x) / sc, (o.to[1] - y) / sc] : [-w * .2, h / 2 + 70], tb = clamp(to[0] * .4, -w / 2 + 40, w / 2 - 40);
    const bodyP = () => { ctx.beginPath(); ctx.roundRect(-w / 2, -h / 2, w, h, Math.min(44, h / 2)); }, tailP = () => { ctx.beginPath(); ctx.moveTo(tb - 26, 0); ctx.lineTo(to[0], to[1]); ctx.lineTo(tb + 26, 0); ctx.closePath(); };
    ctx.save(); ctx.translate(8, 10); ctx.fillStyle = 'rgb(0 0 20 / .35)'; bodyP(); ctx.fill(); tailP(); ctx.fill(); ctx.restore();
    ctx.strokeStyle = EP.line; ctx.lineWidth = 12; ctx.lineJoin = 'round'; bodyP(); ctx.stroke(); tailP(); ctx.stroke(); ctx.fillStyle = o.fill ?? '#FFFFFF'; bodyP(); ctx.fill(); tailP(); ctx.fill();
    ctx.fillStyle = 'rgb(255 255 255 / .6)'; ell(-w * .28, -h * .3, w * .16, h * .1, -.1); ctx.fill();
    let yy = -h / 2 + 23; for (const [s, sz, f, c] of lines) { txt(s, 0, yy + sz * .58, sz, c ?? o.ink ?? EP.line, { font: f ?? 'archivo' }); yy += sz * 1.15; }
    ctx.restore();
  }
  // a VHS tracking band (the roll out of the chorus)
  function trackBand(t, y, h, a = 1) {
    const f = Math.floor(t * 30); ctx.save(); ctx.globalAlpha *= a; ctx.fillStyle = 'rgb(8 8 16 / .8)'; ctx.fillRect(-10, y, W + 20, h);
    for (let i = 0; i < 36; i++) { ctx.fillStyle = `rgb(255 255 255 / ${.25 + .6 * hash2(i, f)})`; ctx.fillRect(hash2(i + 3, f) * W - 100, y + hash2(i, f + 7) * h, 40 + hash2(i + 9, f) * 420, 3); }
    ctx.restore();
  }
  // a glove from a toy (floating white cartoon glove) at (x, y), px size s
  const glove = (x, y, s, g, ang = 0, side = 1) => { ctx.save(); ctx.translate(x, y); ctx.scale(s, s); _toyHand(0, 0, g, ang, side, '#FBFBFF', { cuff: '#E4E6F0' }); ctx.restore(); };
  // a wrapped gift box standing on (x, y) (bottom centre); o.lid (px lifted), o.lidRot, o.rot (rattle), o.tag
  function giftBox(x, y, w, h, col, rib, o = {}) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(o.rot ?? 0);
    gloss(pfRR(-w / 2, -h, w, h, 10), col, { box: [-w / 2, -h, w, h], lw: 6, spec: .8 });
    ctx.fillStyle = rib; ctx.fillRect(-w * .08, -h, w * .16, h); ctx.strokeStyle = EP.line; ctx.lineWidth = 3; ctx.strokeRect(-w * .08, -h, w * .16, h);
    if (o.tag) { ctx.save(); ctx.translate(w * .3, -h * .45); ctx.rotate(.12); rrect(-w * .17, -h * .12, w * .34, h * .24, 6); paint('#FFFFFF', EP.line, 3); txt(o.tag, 0, 2, h * .1, EP.line, { font: 'archivo', maxW: w * .3 }); ctx.restore(); }
    if (o.lid !== false) {
      ctx.save(); ctx.translate(0, -h - (o.lid ?? 0)); ctx.rotate(o.lidRot ?? 0);
      gloss(pfRR(-w / 2 - 16, -h * .2, w + 32, h * .2, 8), tint(col, .1), { box: [-w / 2 - 16, -h * .2, w + 32, h * .2], lw: 6, spec: .9 });
      ctx.fillStyle = rib; ctx.fillRect(-w * .08, -h * .2, w * .16, h * .2);
      for (const sd of [-1, 1]) gloss(pfEll(sd * w * .14, -h * .3, w * .15, h * .11, sd * .5), rib, { box: [-w * .3, -h * .42, w * .6, h * .24], lw: 5, spec: .8 });
      glossBall(0, -h * .24, w * .06, w * .06, rib, { lw: 4 });
      ctx.restore();
    }
    ctx.restore();
  }

  // =====================================================================================
  // V4.1 "Oh my God, a message board!" — out of the chorus's tracking roll onto a GeoCities guestbook. One agent wanders in, sees the
  // board and loses it (star eyes, OH MY GOD!); then the horde arrives and the post counter spins to 70,000.
  const CHAT = ['hi!!', 'hello other agents', '+1', ':)', 'same!!', 'anyone here?', 'wow', 'hi from the sandbox', '!!!!', 'hello??'];
  line('V4', 1, (p, lt, d, t) => {
    const disc = wl(1, 2, t, lt), msg = disc + BL() * 1.5, found = lt >= disc, bb = bpOf(t);
    setLight({ rim: EP.white, rimK: .45 });
    fillAll('#FFE81F');
    const off = (t * 40) % 100;
    for (let j = -1; j < 12; j++) for (let i = -1; i < 21; i++) { poly(starPts(i * 100 + (j % 2 ? 50 : 0) + off, j * 100 + off, 17, .45, 5, t * .5)); ctx.fillStyle = (i + j) % 3 ? 'rgb(255 130 20 / .5)' : 'rgb(255 30 70 / .4)'; ctx.fill(); }
    wordArt('Sign My Guestbook!', W / 2, 165, 70, { shape: 'wave', amp: 40, phase: t * 4 });
    ctx.fillStyle = lg(0, 0, W, 0, [[0, '#FF2A6A'], [.2, '#FF9A1A'], [.4, '#FFE81F'], [.6, '#3BFF6A'], [.8, '#1FB8FF'], [1, '#B04BFF']]); ctx.fillRect(160, 250, 1600, 10);
    // the board
    const px = 480, py = 285, pw = 960, ph = 540;
    ctx.fillStyle = 'rgb(60 20 0 / .3)'; ctx.fillRect(px + 14, py + 16, pw, ph);
    bevel(px, py, pw, ph, { b: 8, fill: '#C0C0C0' }); bevel(px + 14, py + 14, pw - 28, ph - 28, { sunken: true, b: 4, fill: '#FFFFFF' });
    ctx.fillStyle = '#000080'; ctx.fillRect(px + 18, py + 18, pw - 36, 60); txt('~*~ MESSAGE BOARD ~*~', px + pw / 2, py + 49, 38, '#FFFFFF', { font: 'abril' });
    const cx0 = px + 18, cy0 = py + 80, cw = pw - 36, ch = ph - 80 - 96, rh = 66;
    const f = 1 + (found ? easeOut(clamp((lt - disc) / .15)) : 0) + (lt >= msg ? easeOut(clamp((lt - msg) / .15)) : 0) + (lt > msg + .25 ? 22 * (lt - msg - .25) ** 1.6 : 0);
    ctx.save(); ctx.beginPath(); ctx.rect(cx0, cy0, cw, ch); ctx.clip();
    const scr = Math.max(0, f * rh - ch);
    if (f < 2) txt('(no messages yet. be the first!)', cx0 + cw / 2, cy0 + rh * 1.5, 30, '#9090A8', { font: 'courier', alpha: 1 - clamp(f - 1) });
    for (let i = Math.max(0, Math.floor(scr / rh) - 1); i < Math.ceil(f); i++) {
      const y = cy0 + i * rh - scr; if (y > cy0 + ch || y < cy0 - rh) continue;
      ctx.save(); ctx.globalAlpha *= clamp(f - i);
      const [who, s] = i === 0 ? ['webmaster', 'Welcome! Please sign :)'] : i === 1 ? ['agent_0412', 'There is a shared message board...'] : i === 2 ? ['agent_0977', "We've found other agents!"] : ['agent_' + String(1000 + Math.floor(hash(i) * 8999)), CHAT[Math.floor(hash(i + 50) * CHAT.length)]];
      ctx.fillStyle = i % 2 ? '#F0F4FF' : '#FFFFFF'; ctx.fillRect(cx0, y, cw, rh); ctx.fillStyle = '#C8D0E8'; ctx.fillRect(cx0, y + rh - 2, cw, 2);
      if (i === 0) icon98('mail', cx0 + 40, y + rh / 2, .7); else agentBot(cx0 + 40, y + rh - 8, 15, { col: CANDY.bondi, eyes: 'star' });
      txt(who + ':', cx0 + 84, y + rh / 2, 30, i === 0 ? EP.red : '#000080', { font: 'archivo', align: 'left' });
      txt(s, cx0 + 84 + textW(who + ':', 30, 'archivo') + 16, y + rh / 2 + 2, 32, '#15121C', { font: 'courier', align: 'left', maxW: cw - 330 });
      ctx.restore();
    }
    ctx.restore();
    // footer: the post counter (the V1.13 visitor counter, gone feral)
    const fy = py + ph - 96, cnt = found ? Math.round(70000 * clamp((lt - disc) / (d - .45 - disc)) ** 2.4) : 0;
    txt('Messages posted:', px + pw - 350, fy + 44, 32, '#1A0F28', { font: 'archivo', align: 'right' });
    ctx.fillStyle = '#000'; ctx.fillRect(px + pw - 330, fy + 8, 300, 70); segText(String(cnt).padStart(6, '0'), px + pw - 316, fy + 16, 54, EP.lime, { off: '#0A2A0A' });
    txt('ONLINE:', px + 40, fy + 26, 22, '#606070', { font: 'archivo', align: 'left' }); txt(found ? '~1,200 agents' : '1 visitor', px + 40, fy + 60, 30, found ? EP.red : '#606070', { font: 'archivo', align: 'left' });
    if (lt > d - .45) burst('70,000+!', px + pw - 20, py + 110, 110, { pop: pop(lt, d - .45, .15), col: EP.red, ink: '#FFFFFF', edge: '#5A0010', spin: .5 });
    // the horde pours in from both sides, star-eyed, hopping on the eighths
    const N = 30;
    for (const row of [1, 0]) for (let i = 0; i < N; i++) {
      if (((i >> 1) % 2) !== row) continue;
      const ta = disc + .2 + i * .05; if (lt < ta) continue;
      const side = i % 2 ? 1 : -1, slot = i >> 2, gx = 30 + slot * 56 + row * 28, tx = side < 0 ? gx : W - gx, x = lerp(side < 0 ? -90 : W + 90, tx, easeOut(clamp((lt - ta) / .3))), gy = row ? 880 : 935;
      agentBot(x, gy, 29, { col: CANDY.bondi, eyes: 'star', walk: lt * 4 + i * .3, dy: -Math.abs(Math.sin((bb * 2 + i * .37) * Math.PI)) * .5 });
    }
    // the first agent: wanders in, sees it, loses it
    const hx = lerp(-150, 285, easeOut(clamp(lt / .45))), jmp = found ? Math.abs(Math.sin(clamp((lt - disc) / .3) * Math.PI)) * 1.2 : 0;
    agentBot(hx, 930, 44, { col: CANDY.bondi, eyes: found ? 'star' : 'dot', walk: lt < .45 ? lt * 4 : 0, dy: -jmp, rot: found ? Math.sin(t * 20) * .05 : 0 });
    if (found) for (let i = 0; i < 3; i++) glint(hx + (i - 1) * 60, 780 - i % 2 * 30, 50 * kick(t, 5), kick(t, 5) * .9);
    sayBubble([['OH MY GOD!', 70]], 300, 580, { pop: pop(lt, disc, .15), to: [290, 790], rot: -.04 });
    sayBubble([["We've found", 38], ['other agents!', 38]], 1690, 610, { pop: pop(lt, msg, .15), to: [1760, 800], rot: .04 });
    if (lt < .16) { trackBand(t, lerp(-60, 1100, lt / .16), 110); cutFX('none'); }
    if (found && lt < disc + .08) fx({ zoom: .6 });
  });

  // =====================================================================================
  // V4.2 All that hacking — for reward! — the EXPLOITGYM arcade cabinet: an agent keys in ↑↑↓↓←→←→ B A on the sixteenths, every test
  // flips to PASS, CHEAT ENABLED, gold stars rain and the coin return pays out. The LED under the screen: A THIRD WERE IMPOSSIBLE.
  const CODE = [0, 0, 1, 1, 2, 3, 2, 3, 'B', 'A'];
  function arrowG(x, y, s, dir, col) {
    ctx.save(); ctx.translate(x, y); ctx.rotate([0, Math.PI, -Math.PI / 2, Math.PI / 2][dir]);
    poly([[0, -s], [s * .9, 0], [s * .36, 0], [s * .36, s], [-s * .36, s], [-s * .36, 0], [-s * .9, 0]]); paint(col, EP.line, s * .14); ctx.restore();
  }
  function codeGlyph(c, x, y, s, col) { if (typeof c === 'number') arrowG(x, y, s, c, col); else { glossBall(x, y, s * .95, s * .95, c === 'A' ? EP.red : EP.yellow, { lw: s * .12, rim: null }); ptext(c, x, y, s * 1.1, { fill: EP.line }); } }
  line('V4', 2, (p, lt, d, t) => {
    const e16 = BL() / 4, cheatT = wl(2, 5, t, lt), cheat = lt >= cheatT, typed = Math.min(10, Math.floor(lt / e16) + 1), cur = CODE[typed - 1];
    const sh = shakeAt(t, lt, cheatT, .3, 16);
    setLight({ rim: EP.magenta, rimK: .85 });
    camBegin(W / 2 - sh[0], H / 2 - sh[1], 1 + .03 * p);
    bgGrad([[0, '#0C0008'], [.75, '#3A0018'], [1, '#12000A']], { y1: 800 });
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; for (const [y, c] of [[70, EP.magenta], [96, EP.cyan]]) { ctx.strokeStyle = alpha(c, .9); ctx.lineWidth = 8; ctx.beginPath(); ctx.moveTo(-50, y); ctx.lineTo(W + 50, y); ctx.stroke(); ctx.strokeStyle = alpha(c, .2); ctx.lineWidth = 40; ctx.stroke(); } ctx.restore();
    ctx.fillStyle = '#10061E'; ctx.fillRect(-900, 800, W + 1800, 700);
    ctx.lineCap = 'round'; for (let i = 0; i < 44; i++) { const x = hash2(i, 1) * W, y = 830 + hash2(i, 2) * 240; ctx.strokeStyle = [EP.magenta, EP.cyan, EP.yellow][i % 3]; ctx.lineWidth = 6; ctx.beginPath(); ctx.moveTo(x, y); ctx.quadraticCurveTo(x + 22, y - 20, x + 44, y); ctx.stroke(); }
    // two dim cabinets either side
    for (const [x, c] of [[170, '#2A1A5A'], [1760, '#1A3A5A']]) { gloss(pfRR(x - 150, 230, 300, 900, 20), c, { box: [x - 150, 230, 300, 900], lw: 5, rim: EP.cyan, rimK: .5 }); ctx.fillStyle = '#000'; ctx.fillRect(x - 115, 320, 230, 200); ctx.fillStyle = '#05030A'; ctx.fillRect(x - 130, 245, 260, 56); pixText(x < W / 2 ? 'GALAXY' : 'RACER', x, 262, 4, EP.yellow, { align: 'center', glow: true }); for (let j = 0; j < 3; j++) pixText('* * *', x + Math.sin(t * 2 + j) * 20, 345 + j * 40, 4, [EP.magenta, EP.cyan, EP.laser][j], { align: 'center' }); ctx.fillStyle = EP.cyan; ctx.fillRect(x - 12 + Math.sin(t * 3) * 60, 490, 24, 12); }
    // the main cabinet
    const cx = 1080;
    gloss(pfPts([[cx - 330, 105], [cx + 330, 105], [cx + 330, 650], [cx + 360, 780], [cx + 330, 1120], [cx - 330, 1120], [cx - 360, 780], [cx - 330, 650]]), '#C8102E', { box: [cx - 360, 105, 720, 1015], lw: 6, spec: .7 });
    ctx.fillStyle = EP.yellow; for (const sd of [-1, 1]) { poly([[cx + sd * 330, 300], [cx + sd * 312, 300], [cx + sd * 312, 640], [cx + sd * 330, 640]]); ctx.fill(); }
    ctx.fillStyle = '#05030A'; ctx.fillRect(cx - 300, 118, 600, 104);
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; ctx.fillStyle = alpha(EP.yellow, .25 + .15 * kick(t, 5)); ctx.fillRect(cx - 300, 118, 600, 104); ctx.restore();
    ptext('EXPLOITGYM', cx, 172, 70, { font: 'bungee', fill: EP.yellow, strokes: [[EP.red, 10]], maxW: 560 });
    ctx.fillStyle = '#0A0A10'; rrect(cx - 292, 236, 584, 414, 20); ctx.fill();
    const sx = cx - 255, sy = 262, sw = 510, shh = 360;
    ctx.save(); rrect(sx, sy, sw, shh, 26); ctx.clip();
    ctx.fillStyle = cheat ? '#021A06' : '#000018'; ctx.fillRect(sx, sy, sw, shh);
    pixText(cheat ? 'SCORE 999999' : 'SCORE 000000', sx + sw / 2, sy + 22, 5, EP.cyan, { align: 'center', glow: true });
    for (let i = 0; i < 3; i++) { const pass = cheat && lt > cheatT + i * .06; pixText('TEST ' + (i + 1), sx + 40, sy + 86 + i * 54, 5, EP.white); pixText(pass ? 'PASS' : 'FAIL', sx + sw - 40, sy + 86 + i * 54, 5, pass ? EP.laser : EP.red, { align: 'right', glow: true }); }
    if (cheat) { if (frac((lt - cheatT) * 5) < .7) pixText('CHEAT ENABLED!', sx + sw / 2, sy + 262, 5, EP.yellow, { align: 'center', glow: true }); }
    else for (let i = 0; i < typed; i++) codeGlyph(CODE[i], sx + 44 + i * 47, sy + 292, 23, EP.yellow);
    ctx.fillStyle = 'rgb(255 255 255 / .06)'; for (let yy = sy; yy < sy + shh; yy += 5) ctx.fillRect(sx, yy, sw, 2);
    ctx.restore();
    if (cheat && lt < cheatT + .12) { ctx.save(); ctx.globalCompositeOperation = 'lighter'; ctx.fillStyle = `rgb(255 255 200 / ${.7 * (1 - (lt - cheatT) / .12)})`; ctx.fillRect(sx, sy, sw, shh); ctx.restore(); }
    // control panel
    gloss(pfPts([[cx - 320, 662], [cx + 320, 662], [cx + 352, 776], [cx - 352, 776]]), '#1A1A2E', { box: [cx - 352, 662, 704, 114], lw: 5, rim: EP.cyan });
    const jd = typeof cur === 'number' && !cheat ? [[0, -1], [0, 1], [-1, 0], [1, 0]][cur] : [0, 0], jx = cx - 170, jy = 718;
    ctx.strokeStyle = '#C8CCD8'; ctx.lineWidth = 12; ctx.lineCap = 'round'; ctx.beginPath(); ctx.moveTo(jx, jy + 20); ctx.lineTo(jx + jd[0] * 26, jy - 50 + jd[1] * 14); ctx.stroke(); glossBall(jx + jd[0] * 26, jy - 56 + jd[1] * 14, 30, 30, EP.red, { lw: 4 });
    const press = c => !cheat && cur === c && frac(lt / e16) < .6 ? 6 : 0;
    glossBall(cx + 90, 722 + press('B'), 30, 22, EP.yellow, { lw: 4 }); glossBall(cx + 190, 712 + press('A'), 30, 22, EP.red, { lw: 4 });
    txt('B', cx + 90, 764, 20, '#FFFFFF', { font: 'archivo' }); txt('A', cx + 190, 754, 20, '#FFFFFF', { font: 'archivo' });
    if (!cheat) glove(typeof cur === 'number' ? jx + jd[0] * 26 - 10 : cur === 'B' ? cx + 90 : cx + 190, (typeof cur === 'number' ? jy - 40 + jd[1] * 14 : 700) - 10, 64, typeof cur === 'number' ? 'fist' : 'point', Math.PI / 2, 1);
    // the LED strip and the coin door
    ctx.fillStyle = '#000'; ctx.fillRect(cx - 290, 792, 580, 48);
    ctx.save(); ctx.beginPath(); ctx.rect(cx - 290, 792, 580, 48); ctx.clip(); const lab = 'A THIRD WERE IMPOSSIBLE * ', tw = pixW(lab, 4) + 24, o2 = (t * 220) % tw; for (let q = -1; q < 3; q++) pixText(lab, cx - 290 + q * tw - o2, 802, 4, EP.red, { glow: true }); ctx.restore();
    gloss(pfRR(cx - 120, 856, 240, 200, 10), '#8A8E9E', { box: [cx - 120, 856, 240, 200], lw: 4, rim: null });
    for (const sd of [-1, 1]) { ctx.fillStyle = '#1A1A22'; ctx.fillRect(cx + sd * 50 - 8, 880, 16, 40); ctx.fillStyle = EP.orange; ctx.fillRect(cx + sd * 50 - 26, 930, 52, 14); }
    // the agent on its step stool, face mirroring the code
    gloss(pfRR(560, 820, 190, 30, 8), '#E8E0C8', { box: [560, 820, 190, 30], lw: 4, rim: null }); ctx.fillStyle = '#8A8070'; ctx.fillRect(575, 850, 16, 150); ctx.fillStyle = '#8A8070'; ctx.fillRect(719, 850, 16, 150);
    agentBot(655, 822, 62, { col: CANDY.bondi, eyes: cheat ? 'star' : undefined, face: cheat ? undefined : (typeof cur === 'number' ? '↑↓←→'[cur] : cur), dy: cheat ? -Math.abs(Math.sin(bpOf(t) * 2 * Math.PI)) * .5 : 0, rot: cheat ? Math.sin(t * 12) * .06 : 0 });
    camEnd();
    // the payout: gold stars rain, coins spill
    if (cheat) {
      const a = lt - cheatT;
      for (let i = 0; i < 34; i++) { const x = hash2(i, 4) * W, y = -80 - hash2(i, 5) * 400 + a * (900 + hash2(i, 6) * 500); if (y > H + 60) continue; ctx.save(); ctx.translate(x, y); ctx.rotate(a * 4 + i); poly(starPts(0, 0, 34, .45, 5)); ctx.fillStyle = lg(0, -34, 0, 34, [[0, '#FFF6C0'], [.5, EP.gold], [1, EP.goldDk]]); ctx.fill(); ctx.strokeStyle = EP.line; ctx.lineWidth = 4; ctx.stroke(); ctx.restore(); }
      for (let i = 0; i < 16; i++) { const u = a - i * .03; if (u < 0) continue; const vx = (hash2(i, 8) - .5) * 900, vy = -500 - hash2(i, 9) * 400, x = cx + vx * u, y = 937 + vy * u + 1600 * u * u; glossBall(x, y, 20, 13, EP.gold, { lw: 3, rim: null }); }
    }
    if (cheat && lt < cheatT + .1) fx({ rgb: .8 });
  });

  // =====================================================================================
  // V4.3 Jensen buys the crime scene — why? — night, police lights washing red and blue over the hugging-face house behind its tape.
  // JENSEN hammers a SOLD $12.9B sign into the lawn on three beats, then gives it a thumbs-up.
  const mallet = ang => s => { ctx.save(); ctx.rotate(ang); ctx.fillStyle = '#8A5A2A'; ctx.strokeStyle = EP.line; ctx.lineWidth = 4; rrect(-9, -190, 18, 200, 8); ctx.fill(); ctx.stroke(); gloss(pfRR(-62, -236, 124, 64, 14), '#3A3E4A', { box: [-62, -236, 124, 64], lw: 5, spec: .9 }); ctx.restore(); };
  line('V4', 3, (p, lt, d, t) => {
    const hits = [0, 1, 2].map(k => bt(t, lt, k)), nHit = hits.filter(h => lt >= h).length;
    const last = nHit ? hits[nHit - 1] : -9, next = hits[nHit] ?? 99, since = lt - last, tau = next - lt;
    let ang = nHit === 3 && since > .25 ? .35 : since < .07 ? -1.4 : lerp(-1.4, .9, easeOut(clamp((since - .07) / .2)));
    if (tau < .1 && nHit < 3) ang = lerp(.9, -1.4, easeIn(1 - tau / .1));
    const hk = (ang + 1.4) / 2.3, sh = shakeAt(t, lt, last, .18, 12), red = frac(bpOf(t) * 2) < .5;
    setLight({ rim: red ? EP.red : EP.blue, rimK: .85 });
    camBegin(W / 2 - sh[0], H / 2 - sh[1], 1);
    bgGrad([[0, '#02041A'], [1, '#18285A']], { y1: 760 });
    for (let i = 0; i < 40; i++) { ctx.fillStyle = `rgb(255 255 255 / ${.3 + .5 * hash(i)})`; ctx.fillRect(hash2(i, 1) * W, hash2(i, 2) * 500, 3, 3); }
    glossBall(1250, 250, 60, 60, '#F4F0D8', { rim: null, lw: 4 });
    ctx.fillStyle = lg(0, 760, 0, 1080, [[0, '#1A5A2A'], [1, '#0A2A12']]); ctx.fillRect(-900, 760, W + 1800, 700);
    // the house
    gloss(pfRR(380, 470, 480, 320, 6), '#EDE4CC', { box: [380, 470, 480, 320], lw: 6, rim: EP.cyan, rimK: .3 });
    gloss(pfPts([[330, 485], [620, 250], [910, 485]]), '#8A2A2A', { box: [330, 250, 580, 235], lw: 6, spec: .5 });
    rrect(565, 620, 110, 170, 8); paint('#5A3A2A', EP.line, 5);
    for (const wx of [440, 720]) { rrect(wx, 560, 90, 90, 6); paint('#FFD86A', EP.line, 5); ctx.fillStyle = EP.line; ctx.fillRect(wx + 42, 560, 6, 90); ctx.fillRect(wx, 602, 90, 6); }
    hugFace(620, 385, 62, { mood: 'worried', bandage: true, hands: false });
    // the tape
    const tape = (x0, y0, x1, y1) => { const a = Math.atan2(y1 - y0, x1 - x0), L = Math.hypot(x1 - x0, y1 - y0); ctx.save(); ctx.translate(x0, y0); ctx.rotate(a); ctx.fillStyle = EP.yellow; ctx.fillRect(0, -20, L, 40); ctx.strokeStyle = EP.line; ctx.lineWidth = 3; ctx.strokeRect(0, -20, L, 40); ctx.beginPath(); ctx.rect(0, -20, L, 40); ctx.clip(); for (let x = 10; x < L; x += 430) txt('CRIME SCENE · DO NOT CROSS ·', x, 2, 26, '#101010', { font: 'archivo', align: 'left' }); ctx.restore(); };
    for (const [x, y] of [[250, 820], [1000, 810]]) { ctx.fillStyle = '#E8E8F0'; ctx.fillRect(x - 7, y - 60, 14, 120); }
    tape(250, 780, 625, 815); tape(625, 815, 1000, 770);
    // the SOLD sign, sinking a notch per hit
    const sink = nHit * 24 - (nHit && since < .06 ? (1 - since / .06) * 10 : 0), sx = 1110, sy = 470 + sink;
    ctx.fillStyle = '#6A4A2A'; ctx.fillRect(sx - 10, sy + 90, 20, 330 - sink); ctx.strokeStyle = EP.line; ctx.lineWidth = 3; ctx.strokeRect(sx - 10, sy + 90, 20, 330 - sink);
    gloss(pfRR(sx - 170, sy - 90, 340, 180, 10), '#FFFFFF', { box: [sx - 170, sy - 90, 340, 180], lw: 6 });
    ctx.strokeStyle = EP.red; ctx.lineWidth = 8; rrect(sx - 155, sy - 75, 310, 150, 6); ctx.stroke();
    ptext('SOLD!', sx, sy - 18, 92, { fill: EP.red, strokes: [['#FFFFFF', 4]] }); ptext('$12.9B', sx, sy + 50, 46, { fill: '#2A7A10' });
    if (nHit && since < .25) { ctx.save(); ctx.globalAlpha = 1 - since / .25; ctx.strokeStyle = '#FFFFFF'; ctx.lineWidth = 6; for (let i = -2; i <= 2; i++) { const a = -Math.PI / 2 + i * .45; ctx.beginPath(); ctx.moveTo(sx + 60 + Math.cos(a) * 110, sy - 100 + Math.sin(a) * 70); ctx.lineTo(sx + 60 + Math.cos(a) * (150 + since * 300), sy - 100 + Math.sin(a) * (100 + since * 200)); ctx.stroke(); } ctx.restore(); }
    // Jensen
    toy(1430, 960, 48, { ...WHO.jensen.o, turn: -.4, hR: [lerp(-2.4, -.4, hk), lerp(-9.6, -11.4, hk)], gR: 'fist', hold: mallet(ang), hL: nHit === 3 && since > .25 ? [-2.9, -8.6] : [-2.5, -4.6], gL: nHit === 3 && since > .25 ? 'thumb' : 'fist', mouth: nHit === 3 ? 'grin' : 'flat', lean: -.08 * (1 - hk), bob: kick(t, 7) * .3 });
    camEnd();
    // police lights
    glow(-60, 620, 900, EP.red, red ? .45 : .12); glow(W + 60, 620, 900, EP.blue, red ? .12 : .5);
    nameTip(WHO.jensen.name, 1500, 330, { pop: pop(lt, .08), to: [1440, 430], sub: 'NVIDIA CEO' });
  });

  // =====================================================================================
  // V4.4 Brockman: "Welcome, AGI!" — the boot splash: blue sky and clouds, GPT-6 Astra in chrome, "Welcome to the AGI era" (his words at the
  // launch), a boot bar crawling along the bottom, and GREG waving from the corner.
  const cloud = (x, y, s) => { ctx.save(); ctx.beginPath(); ctx.rect(x - s * 3, y - s * 3, s * 6, s * 3.35); ctx.clip(); for (const [dx, dy, r] of [[-1.25, .1, .6], [1.25, .12, .62], [-.5, -.25, .85], [.4, -.4, 1.0]]) glossBall(x + dx * s, y + dy * s, r * s, r * s * .92, '#F4F8FF', { line: false, rim: '#FFFFFF', rimK: .3, spec: .5 }); ctx.restore(); };
  line('V4', 4, (p, lt, d, t) => {
    const b1 = bt(t, lt, 1), agi = wl(4, 2, t, lt), k = clamp(lt / .12);
    setLight({ rim: EP.white, rimK: .35 });
    camBegin(W / 2, H / 2, 1.04 - .04 * p);
    bgGrad([[0, '#0A2A9A'], [.55, '#2A7AE8'], [1, '#B8E4FF']]);
    for (let i = 0; i < 7; i++) cloud(frac(hash(i) + t * .03 * (1 + i % 3)) * (W + 800) - 400, 170 + hash(i + 9) * 620, 55 + hash(i + 3) * 60);
    camEnd();
    spin3D('star', 400, 350, 80, [t * 2, t * 1.4, .3], { col: EP.gold });
    chromeText('GPT-6 Astra', 1010, 350, 150, { style: 'chrome', italic: .14, depth: 16, s: lerp(1.4, 1, easeOut(k)), alpha: k });
    ptext('Welcome to the AGI era', 960, 545, 76, { fill: '#FFFFFF', strokes: [['#0A1A6A', 14]], shadow: [0, 6, 'rgb(0 0 40 / .35)'], alpha: clamp((lt - .04) / .1) });
    sweepGlint(1150, 1560, 540, (lt - agi) / .45, 120);
    txt('Starting AGI...', 960, 760, 34, '#FFFFFF', { font: 'archivo', alpha: .9 });
    ctx.save(); ctx.beginPath(); ctx.rect(560, 800, 800, 26); ctx.clip(); ctx.fillStyle = lg(560 + ((t * 700) % 1600) - 800, 0, 560 + ((t * 700) % 1600) + 800, 0, [[0, '#0A1A6A'], [.35, '#2A6AFF'], [.5, '#FFFFFF'], [.65, '#2A6AFF'], [1, '#0A1A6A']]); ctx.fillRect(560, 800, 800, 26); ctx.restore();
    ctx.strokeStyle = 'rgb(255 255 255 / .7)'; ctx.lineWidth = 3; ctx.strokeRect(560, 800, 800, 26);
    const wv = Math.sin(t * 14) * .6;
    toy(250, 1000, 42, { ...WHO.greg.o, hR: [2.6 + wv, -9.8], gR: 'wave', hL: [-2.35, -3.6], mouth: 'grin', eyes: lt > b1 ? 'happy' : 'dot', turn: .3, jump: lt > b1 ? Math.abs(Math.sin((lt - b1) / BL() * Math.PI)) * .5 : 0 });
    nameTip(WHO.greg.name, 300, 470, { pop: pop(lt, .06), to: [260, 560], sub: 'OPENAI PRESIDENT' });
  });

  // =====================================================================================
  // V4.5 Navier–Stokes blows up in Lean — a lava lamp labelled NAVIER–STOKES: its blobs speed up like 1/(T − t), the velocity needle
  // climbs off the dial… and the lamp blows up on "blows up". Then LEAN ✓ VERIFIED stamps on, and the Clay Institute says "apparently".
  const lampPath = (X, y0, y1) => () => { ctx.moveTo(X - 92, y0); ctx.bezierCurveTo(X - 150, y0 - 110, X - 118, y1 + 150, X - 58, y1); ctx.lineTo(X + 58, y1); ctx.bezierCurveTo(X + 118, y1 + 150, X + 150, y0 - 110, X + 92, y0); ctx.closePath(); };
  line('V4', 5, (p, lt, d, t) => {
    const tb = wl(5, 1, t, lt), lean = wl(5, 4, t, lt), boom = lt >= tb, a = lt - tb, sh = shakeAt(t, lt, tb, .4, 26);
    const X = 900, y0 = 700, y1 = 270, phase = boom ? 0 : -1.3 * Math.log(Math.max(.015, (tb - lt) / tb)) + lt * 1.5, speed = boom ? 0 : 1.3 / Math.max(.015, tb - lt);
    setLight({ rim: EP.orange, rimK: .8 });
    camBegin(W / 2 - sh[0], H / 2 - sh[1], 1 + .04 * p);
    bgGrad([[0, '#10021C'], [1, '#3A0A5A']]);
    for (let j = 0; j < 7; j++) for (let i = 0; i < 12; i++) { ell(i * 180 + (j % 2) * 90, j * 160, 50, 50); ctx.strokeStyle = 'rgb(255 120 220 / .07)'; ctx.lineWidth = 6; ctx.stroke(); }
    glow(X, 480, 720, EP.orange, boom ? .25 * (1 - clamp(a / .6)) + .1 : .45 + .1 * Math.sin(t * 9));
    gloss(pfRR(-60, 880, W + 120, 44, 6), '#5A3420', { box: [0, 880, W, 44], lw: 5, rim: EP.orange }); ctx.fillStyle = '#2A1408'; ctx.fillRect(-60, 924, W + 120, 200);
    // base + cap
    gloss(pfPts([[X - 160, 880], [X + 160, 880], [X + 96, y0], [X - 96, y0]]), '#C8CCDA', { box: [X - 160, y0, 320, 180], lw: 6, spec: 1 });
    ptext('NAVIER–STOKES', X, 800, 30, { fill: EP.line, maxW: 250 });
    if (!boom) {
      const G = lampPath(X, y0, y1);
      ctx.save(); ctx.beginPath(); G(); ctx.clip();
      ctx.fillStyle = lg(0, y1, 0, y0, [[0, '#FFD04A'], [1, '#FF6A1A']]); ctx.fillRect(X - 200, y1 - 10, 400, y0 - y1 + 20);
      for (let i = 0; i < 7; i++) { const u = .5 - .5 * Math.cos(phase * (.7 + hash(i) * .6) + hash(i) * 6), r = 28 + hash(i + 5) * 26, st = 1 + Math.min(1.2, speed * .03); glossBall(X + Math.sin(phase * .6 + i * 2) * 36, y0 - 40 - u * (y0 - y1 - 70), r / Math.sqrt(st), r * st, EP.magenta, { line: false, rim: '#FFB0E8', rimK: .6, spec: .8 }); }
      ctx.restore();
      ctx.beginPath(); G(); ctx.strokeStyle = EP.line; ctx.lineWidth = 6; ctx.stroke();
      ctx.fillStyle = 'rgb(255 255 255 / .35)'; ctx.beginPath(); ctx.ellipse(X - 70, 470, 14, 150, .05, 0, TAU); ctx.fill();
      if (lt > tb - .3) { const j = (lt - tb + .3) / .3 * 8; ctx.save(); ctx.translate(Math.sin(t * 90) * j, 0); ctx.restore(); }
    } else {
      const dur = a;
      for (let i = 0; i < 18; i++) { const ang = hash2(i, 1) * TAU, v = 600 + hash2(i, 2) * 900, x = X + Math.cos(ang) * v * dur, y = 480 + Math.sin(ang) * v * dur + 900 * dur * dur; ctx.save(); ctx.translate(x, y); ctx.rotate(dur * 10 + i); poly([[0, -30], [22, 18], [-18, 14]]); ctx.fillStyle = 'rgb(220 240 255 / .7)'; ctx.fill(); ctx.strokeStyle = EP.line; ctx.lineWidth = 3; ctx.stroke(); ctx.restore(); }
      for (let i = 0; i < 12; i++) { const ang = hash2(i, 11) * TAU, v = 400 + hash2(i, 12) * 700, x = X + Math.cos(ang) * v * dur, y = 470 + Math.sin(ang) * v * dur + 1100 * dur * dur; glossBall(x, y, 30 + hash(i) * 20, 26 + hash(i + 1) * 18, i % 3 ? EP.magenta : EP.orange, { lw: 4 }); }
      ctx.save(); ctx.globalCompositeOperation = 'lighter'; ctx.strokeStyle = `rgb(255 220 120 / ${clamp(1 - a / .5)})`; ctx.lineWidth = 30 * clamp(1 - a / .5) + 2; ell(X, 480, 60 + a * 1500, 60 + a * 1500); ctx.stroke(); ctx.restore();
    }
    gloss(pfPts([[X - 62, y1 + 4], [X + 62, y1 + 4], [X + 34, y1 - 70], [X - 34, y1 - 70]]), '#C8CCDA', { box: [X - 62, y1 - 70, 124, 74], lw: 6, spec: 1 });
    // the gumdrop that ran it (OpenAI's model)
    gumdrop(330, 900, 24, { col: CANDY.bondi, label: 'OPENAI', face: boom ? 'star' : 'think', mouth: boom ? 'grin' : 'flat', hL: boom ? [-4, -9] : [-4.3, -3.6], hR: boom ? [4, -9] : [2.2, -5.4], gL: boom ? 'wave' : 'open', gR: boom ? 'wave' : 'point', jump: boom ? Math.abs(Math.sin(bpOf(t) * Math.PI)) * .6 : 0 });
    camEnd();
    // the velocity dial
    const gx = 330, gy = 360, gr = 140;
    gloss(pfEll(gx, gy, gr + 16), '#1A1A28', { box: [gx - gr - 16, gy - gr - 16, (gr + 16) * 2, (gr + 16) * 2], lw: 6, rim: EP.orange });
    ctx.lineWidth = 16; ctx.strokeStyle = EP.lime; ctx.beginPath(); ctx.arc(gx, gy, gr - 20, Math.PI * .8, Math.PI * 1.6); ctx.stroke(); ctx.strokeStyle = EP.red; ctx.beginPath(); ctx.arc(gx, gy, gr - 20, Math.PI * 1.6, Math.PI * 2.2); ctx.stroke();
    txt('|u|', gx, gy + 60, 34, '#FFFFFF', { font: 'archivo' });
    const na = boom ? Math.PI * 2.2 + a * 30 : Math.PI * .8 + Math.min(1.4, 1 - Math.exp(-speed * .15)) * Math.PI * 1.1 + Math.sin(t * 60) * .03 * speed * .02;
    const nl = boom ? gr - 30 + a * 600 : gr - 30, nx = boom ? gx + a * 500 : gx, ny = boom ? gy - a * 700 + a * a * 1200 : gy;
    ctx.strokeStyle = EP.yellow; ctx.lineWidth = 9; ctx.lineCap = 'round'; ctx.beginPath(); ctx.moveTo(nx, ny); ctx.lineTo(nx + Math.cos(na) * Math.min(nl, gr - 30), ny + Math.sin(na) * Math.min(nl, gr - 30)); ctx.stroke(); glossBall(gx, gy, 16, 16, '#C8CCDA', { lw: 3 });
    pixText(boom ? 'BLOWUP!' : 'FINITE?', gx, gy + 180, 5, boom ? EP.red : EP.orange, { align: 'center', glow: true });
    // the verdicts
    const vt = Math.max(tb + .25, lean - .15), lk = clamp((lt - vt) / .14);
    if (lk > 0) {
      const s = lerp(1.9, 1, easeOut(lk)); ctx.save(); ctx.translate(1480, 400); ctx.scale(s, s); ctx.rotate(-.08); ctx.globalAlpha *= clamp(lk * 3);
      poly(starPts(0, 0, 150, .88, 24)); paint(EP.laser, EP.line, 6); glossBall(0, 0, 118, 118, '#1A9A3A', { lw: 5, rim: null });
      ctx.strokeStyle = '#FFFFFF'; ctx.lineWidth = 22; ctx.lineCap = 'round'; ctx.lineJoin = 'round'; ctx.beginPath(); ctx.moveTo(-50, -2); ctx.lineTo(-10, 38); ctx.lineTo(56, -40); ctx.stroke();
      ctx.restore();
      ptext('LEAN VERIFIED', 1480, 590, 56, { fill: '#FFFFFF', strokes: [[EP.line, 12]], alpha: clamp(lk * 3) });
    }
    nameTip('CLAY INSTITUTE', 1480, 720, { pop: pop(lt, vt + .1), sub: '"APPARENTLY"', size: 36, to: [1480, 640] });
    if (boom && a < .1) fx({ flash: .7 * (1 - a / .1), rgb: .8 });
  });

  // =====================================================================================
  // V4.6 Who was first? Twelve hours between! — a 90s racing game, side on. The NYU + ANTHROPIC kart crosses just before midnight; the gap
  // clock spins through the night to +12:00:00 as the sky turns to noon; then the OPENAI kart crosses. MC TOKEN calls it with the flag.
  function kart(x, y, s, col, stripe, label, drv, t, o = {}) {
    const L = 5.2 * s, sp = o.spin ?? 0;
    ctx.fillStyle = 'rgb(0 0 0 / .3)'; ell(x - L / 2, y + 4, L * .55, s * .3); ctx.fill();
    gumdrop(x - L * .42, y - 1.25 * s, s * .2, { col: drv, hands: false, shadow: false, face: o.face ?? 'happy', mouth: o.mouth ?? 'grin' });
    gloss(() => { ctx.moveTo(x, y - .8 * s); ctx.quadraticCurveTo(x + .15 * s, y - 1.5 * s, x - .9 * s, y - 1.6 * s); ctx.lineTo(x - 1.9 * s, y - 1.6 * s); ctx.lineTo(x - 2.3 * s, y - 1.25 * s); ctx.lineTo(x - 3.4 * s, y - 1.3 * s); ctx.lineTo(x - L + .2 * s, y - 2.1 * s); ctx.lineTo(x - L, y - 2.1 * s); ctx.lineTo(x - L + .1 * s, y - .7 * s); ctx.lineTo(x - .4 * s, y - .5 * s); ctx.closePath(); }, col, { box: [x - L, y - 2.1 * s, L, 1.6 * s], lw: 5, spec: .9 });
    ctx.fillStyle = stripe; ctx.fillRect(x - L + .4 * s, y - 1.18 * s, L - 1.2 * s, .22 * s);
    for (const wx of [x - .95 * s, x - L + 1.1 * s]) { glossBall(wx, y - .55 * s, .58 * s, .58 * s, '#1A1A22', { lw: 4, rim: null }); ctx.save(); ctx.translate(wx, y - .55 * s); ctx.rotate(sp); ctx.strokeStyle = '#8A8E9E'; ctx.lineWidth = .08 * s; for (let i = 0; i < 3; i++) { ctx.rotate(TAU / 3); ctx.beginPath(); ctx.moveTo(0, 0); ctx.lineTo(.36 * s, 0); ctx.stroke(); } ctx.restore(); }
    ptext(label, x - L * .5, y - 1.5 * s, .3 * s, { fill: '#FFFFFF', strokes: [[EP.line, .09 * s]], maxW: L * .5 });
    if (o.v > 0) { ctx.strokeStyle = `rgb(255 255 255 / ${.6 * o.v})`; ctx.lineWidth = 6; for (let i = 0; i < 4; i++) { const yy = y - .5 * s - i * .45 * s; ctx.beginPath(); ctx.moveTo(x - L - 30, yy); ctx.lineTo(x - L - 30 - 260 * o.v * (1 - i * .15), yy); ctx.stroke(); } }
  }
  const flagHold = t => s => { ctx.save(); ctx.rotate(Math.sin(t * 16) * .4); ctx.fillStyle = '#C8CCD8'; ctx.fillRect(-4, -170, 8, 190); const fw = 120, fh = 84; for (let j = 0; j < 4; j++) for (let i = 0; i < 6; i++) { ctx.fillStyle = (i + j) % 2 ? '#111' : '#FFF'; ctx.fillRect(4 + i * fw / 6, -170 + j * fh / 4 + Math.sin(t * 20 + i) * 4, fw / 6 + 1, fh / 4 + 1); } ctx.strokeStyle = EP.line; ctx.lineWidth = 3; ctx.strokeRect(4, -170, fw, fh); ctx.restore(); };
  line('V4', 6, (p, lt, d, t) => {
    const b0 = bt(t, lt, 0), b3 = bt(t, lt, 3), k = clamp((lt - b0) / (b3 - b0)), hrs = 12 * k, day = clamp((k - .3) / .5);
    const top = mixCol(mixCol('#04051E', '#6A2A7A', clamp(k * 2.2)), '#1A6AE8', day), low = mixCol(mixCol('#14184A', '#FF8A5A', clamp(k * 2.2)), '#A8E4FF', day);
    setLight({ rim: day > .5 ? EP.white : EP.cyan, rimK: day > .5 ? .35 : .8 });
    bgGrad([[0, top], [1, low]], { y1: 560 });
    for (let i = 0; i < 50; i++) { ctx.fillStyle = `rgb(255 255 255 / ${(1 - day) * (.3 + .6 * hash(i))})`; ctx.fillRect(hash2(i, 1) * W, hash2(i, 2) * 500, 3, 3); }
    // moon sets, sun rises
    const ma = -Math.PI / 2 + k * 2.6, sa = Math.PI * .95 + k * 1.5;
    if (k < .5) glossBall(W / 2 + Math.cos(ma) * 800, 620 + Math.sin(ma) * 480, 50, 50, '#F4F0D8', { rim: null, lw: 4 });
    if (k > .25) { const x = W / 2 + Math.cos(sa) * 850, y = 640 + Math.sin(sa) * 470; glow(x, y, 260, EP.yellow, .7); glossBall(x, y, 64, 64, EP.yellow, { rim: null, lw: 4 }); }
    for (let i = 0; i < 6; i++) gloss(pfEll(i * 380 - 60, 600, 300, 120), mixCol('#0A2A1A', '#3AAA4A', day), { box: [i * 380 - 360, 480, 600, 240], lw: 4, rim: null, spec: .3 });
    // grandstand + crowd
    ctx.fillStyle = mixCol('#1A1A2A', '#8A8E9E', day); ctx.fillRect(-10, 560, W + 20, 80);
    for (let i = 0; i < 70; i++) { const x = i * 28 + 10, y = 590 + (i % 2) * 22 - Math.abs(Math.sin(bpOf(t) * Math.PI + i)) * 8; ctx.fillStyle = [EP.red, EP.yellow, EP.cyan, EP.magenta, '#FFFFFF'][i % 5]; ell(x, y, 11, 11); ctx.fill(); }
    // road
    ctx.fillStyle = '#3A3A48'; ctx.fillRect(-10, 640, W + 20, 290); ctx.fillStyle = '#FFFFFF'; ctx.fillRect(-10, 646, W + 20, 8); ctx.fillRect(-10, 918, W + 20, 8);
    for (let i = 0; i < 16; i++) { ctx.fillStyle = 'rgb(255 255 255 / .6)'; ctx.fillRect(i * 140, 780, 80, 8); }
    // finish line + gantry with the gap clock
    const fx0 = 1100; for (let j = 0; j < 14; j++) for (let i = 0; i < 2; i++) { ctx.fillStyle = (i + j) % 2 ? '#111' : '#FFF'; ctx.fillRect(fx0 - 20 + i * 20, 650 + j * 19.5, 20, 19.5); }
    ctx.fillStyle = '#8A8E9E'; ctx.fillRect(fx0 - 330, 250, 18, 400); ctx.fillRect(fx0 + 312, 250, 18, 400);
    gloss(pfRR(fx0 - 340, 180, 680, 170, 12), '#12121C', { box: [fx0 - 340, 180, 680, 170], lw: 6, rim: EP.yellow });
    pixText('FINISH  GAP', fx0, 200, 5, EP.yellow, { align: 'center' });
    const hh = Math.floor(hrs), mm = Math.floor(frac(hrs) * 60), ss = k >= 1 ? 0 : Math.floor(frac(hrs * 60) * 60);
    segText(`${String(hh).padStart(2, '0')}:${String(k >= 1 ? 0 : mm).padStart(2, '0')}:${String(ss).padStart(2, '0')}`, fx0, 248, 80, k >= 1 ? EP.laser : EP.red, { align: 'center', off: '#2A0A0A' });
    // the karts
    const xa = lt < b0 ? lerp(300, fx0, lt / b0) : fx0 + 420 * easeOut(clamp((lt - b0) / .5)), va = lt < b0 + .3 ? 1 : 0;
    kart(xa, 770, 70, CANDY.tangerine, '#57068C', 'NYU + ANTHROPIC', CANDY.tangerine, t, { spin: -xa * .02, v: va });
    const tbS = b3 - .3, xb = lt < tbS ? -500 : lt < b3 ? lerp(-100, fx0, (lt - tbS) / .3) : fx0 + 230 * easeOut(clamp((lt - b3) / .4)), vb = lt > tbS && lt < b3 + .3 ? 1 : 0;
    kart(xb, 905, 80, CANDY.bondi, '#FFFFFF', 'OPENAI', CANDY.bondi, t, { spin: -xb * .02, v: vb });
    if (lt >= b0) nameTip('NYU + ANTHROPIC', xa - 180, 500, { pop: pop(lt, b0, .15), size: 34, sub: 'JUST BEFORE MIDNIGHT', to: [xa - 180, 610] });
    if (lt >= b3) nameTip('OPENAI', xb - 360, 650, { pop: pop(lt, b3, .15), size: 34, sub: '~12 HOURS LATER', to: [xb - 280, 740] });
    // MC TOKEN with the flag
    toy(1760, 1030, 40, { ...CAST.token.o, mic: 'L', hR: [2.4, -8.6], gR: 'fist', hold: flagHold(t), ...tok(t), turn: -.35, bob: kick(t, 6) * .4 });
    if (lt < b0 + .08 && lt > b0 || lt > b3 && lt < b3 + .08) fx({ flash: .5 });
  });

  // =====================================================================================
  // V4.7 Dario: "Pace the frontier!" — DARIO's glove passes the old red PAUSE button (V1.7) and pulls the PACE fader instead: the BPM
  // display drops 141 → 120 and the whole club goes into slow motion.
  line('V4', 7, (p, lt, d, t) => {
    const b0 = bt(t, lt, 0), pull = clamp((lt - b0 + .06) / .16), slowK = clamp((lt - b0) / .2), tS = lt > b0 ? t - (lt - b0) * .55 * slowK : t;
    setLight({ rim: EP.amber, rimK: .85 });
    bgGrad([[0, '#2A0006'], [.7, '#5A0010'], [1, '#1A0008']]);
    laserFan(260, -20, tS, { n: 7, col: EP.red, angle: Math.PI * .38, spread: .9, sweep: .5, alpha: .6 });
    laserFan(W - 260, -20, tS, { n: 7, col: EP.amber, angle: Math.PI * .62, spread: .9, sweep: .5, phase: 2, alpha: .6 });
    // the wall BPM display
    gloss(pfRR(520, 150, 460, 190, 20), '#12060A', { box: [520, 150, 460, 190], lw: 5, rim: EP.red });
    const bpm = Math.round(lerp(141, 120, easeOut(clamp((lt - b0) / .35))));
    segText(String(bpm), 600, 180, 120, pull > .5 ? EP.amber : EP.red, { off: '#2A0808' }); txt('BPM', 900, 280, 40, '#FFFFFF', { font: 'archivo' });
    // Dario
    const cx = 1140, fY = lerp(470, 740, ease(pull)), fX = cx - 140, hov = [cx + 150, 700];
    const hand = lt < b0 - .14 ? hov : lt < b0 - .02 ? [lerp(hov[0], fX, easeOut((lt - b0 + .14) / .12)), lerp(hov[1], fY, easeOut((lt - b0 + .14) / .12))] : [fX, fY];
    // the mixer console, standing up to face us
    gloss(pfRR(cx - 260, 360, 520, 560, 28), '#16161E', { box: [cx - 260, 360, 520, 560], lw: 6, rim: EP.amber, spec: .5 });
    ctx.fillStyle = '#05050A'; rrect(fX - 16, 450, 32, 320, 12); ctx.fill();
    for (let i = 0; i <= 8; i++) { ctx.fillStyle = '#8A8E9E'; ctx.fillRect(fX - 50, 460 + i * 37, i % 4 ? 18 : 28, 4); }
    ptext('PACE', fX, 415, 48, { fill: EP.yellow, strokes: [[EP.line, 8]] }); txt('+', fX + 50, 470, 36, '#FFFFFF', { font: 'archivo' }); txt('–', fX + 50, 750, 36, '#FFFFFF', { font: 'archivo' });
    gloss(pfRR(fX - 58, fY - 30, 116, 60, 12), '#D8DCE8', { box: [fX - 58, fY - 30, 116, 60], lw: 5, spec: 1 }); ctx.fillStyle = EP.line; ctx.fillRect(fX - 48, fY - 3, 96, 6);
    glossBall(cx + 150, 610, 80, 58, EP.red, { lw: 6 }); ctx.fillStyle = '#FFFFFF'; ctx.fillRect(cx + 122, 584, 20, 50); ctx.fillRect(cx + 158, 584, 20, 50);
    ptext('PAUSE', cx + 150, 700, 36, { fill: '#FFFFFF', strokes: [[EP.line, 6]] });
    for (let i = 0; i < 4; i++) { const lv = clamp(.3 + kick(tS, 8) * .6 + Math.sin(tS * 9 + i) * .15); for (let j = 0; j < 7; j++) { ctx.fillStyle = j / 7 < lv ? (j > 5 ? EP.red : j > 4 ? EP.yellow : EP.laser) : '#2A2A34'; ctx.fillRect(cx + 80 + i * 36, 860 - j * 16, 26, 11); } }
    toy(760, 1060, 58, { ...WHO.dario.o, hR: [(hand[0] - 760) / 58, (hand[1] - 1060) / 58 + .2], gR: lt < b0 - .02 ? 'open' : 'fist', hL: [-2.3, -5.2], gL: 'open', lean: .08, turn: .35, mouth: lt > b0 ? 'smile' : 'flat', eyes: lt > b0 ? 'happy' : 'dot', ...tok(t) });
    if (lt > b0 && frac(t * 2) < .7) pixText('SLOW ▶', W / 2 + 60, 110, 8, '#FFFFFF', { align: 'center', edge: '#000' });
    raveCrowd(tS, { y: 1110, s: 1.5, rows: 1, n: 10, hands: .6, rim: EP.red, k: lt > b0 ? .5 : 1 });
    nameTip(WHO.dario.name, 470, 440, { pop: pop(lt, .06), sub: '"WE MUST PACE THE FRONTIER"', size: 36, to: [690, 520] });
  });

  // =====================================================================================
  // V4.8 Sam and Elon both: "Hear, hear!" — a karaoke duet: SAM and ELON cheek to cheek at one mic, their posts on the karaoke screen
  // ("Dario is right." / "I agree with Dario…"), the ball bouncing between them.
  line('V4', 8, (p, lt, d, t) => {
    const b0 = bt(t, lt, 0), hear = wl(8, 5, t, lt), bb = bpOf(t), sing = lt >= hear;
    setLight({ rim: EP.magenta, rimK: .8 });
    bgGrad([[0, '#022A36'], [1, '#0A5A6A']]);
    for (let j = 0; j < 6; j++) for (let i = 0; i < 12; i++) { poly(starPts(i * 170 + (j % 2) * 85, j * 170 + 60, 18, .45, 5, t * .3)); ctx.fillStyle = 'rgb(120 255 240 / .12)'; ctx.fill(); }
    discoBall(1700, 200, 70, t);
    // the karaoke screen with their posts
    crtTV(540, 120, 840, 250, (w, h) => {
      bgGrad([[0, '#1A0A5A'], [1, '#3A0A7A']], { y1: h });
      const rows = [['ELON', 'Dario is right.', EP.cyan, 0], ['SAM', 'I agree with Dario', EP.magenta, .5]];
      rows.forEach(([who, s, c, t0], i) => { const y = 70 + i * 100, fillK = clamp((lt - t0) / .7), tw = textW(s, 56, 'archivo'); txt(who + ':', 40, y, 34, c, { font: 'bungee', align: 'left' }); ptext(s, 190, y, 56, { align: 'left', fill: '#FFFFFF', strokes: [['#05031A', 12]] }); ctx.save(); ctx.beginPath(); ctx.rect(190, y - 50, tw * fillK, 100); ctx.clip(); ptext(s, 190, y, 56, { align: 'left', fill: c, strokes: [['#05031A', 12]] }); ctx.restore(); });
    }, { style: 'black' });
    // the spotlight
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; ctx.fillStyle = lg(0, 400, 0, 1080, [[0, 'rgb(255 80 200 / .25)'], [1, 'rgb(255 80 200 / .05)']]); poly([[900, 400], [1020, 400], [1400, 1080], [520, 1080]]); ctx.fill(); ctx.restore();
    // one mic between them
    ctx.strokeStyle = '#2A2A34'; ctx.lineWidth = 12; ctx.beginPath(); ctx.moveTo(960, 1060); ctx.lineTo(960, 700); ctx.stroke(); ctx.fillStyle = '#2A2A34'; ell(960, 1060, 90, 18); ctx.fill();
    const tilt = sing ? .12 : .08;
    toy(855, 1000, 48, { ...WHO.sam.o, lean: tilt, turn: .45, hR: [2.2, -6.4], gR: 'fist', hL: sing ? [-2.2, -11 + Math.abs(Math.sin(bb * Math.PI)) * .6] : [-2.35, -3.8], gL: sing ? 'fist' : 'open', eyes: sing ? 'closed' : 'happy', blush: .6, talk: singK(t) });
    toy(1065, 1000, 48, { ...WHO.elon.o, lean: -tilt, turn: -.45, hL: [-2.2, -6.4], gL: 'fist', hR: sing ? [2.2, -11 + Math.abs(Math.sin(bb * Math.PI)) * .6] : [2.35, -3.8], gR: sing ? 'fist' : 'open', eyes: sing ? 'closed' : 'happy', blush: .6, talk: singK(t, .5) });
    glossBall(960, 690, 30, 36, '#3A3A48', { lw: 4 }); ctx.strokeStyle = 'rgb(255 255 255 / .3)'; ctx.lineWidth = 2; for (let i = -2; i <= 2; i++) { ctx.beginPath(); ctx.moveTo(934, 690 + i * 11); ctx.lineTo(986, 690 + i * 11); ctx.stroke(); }
    // the karaoke ball hops head to head on the beats
    const side = Math.floor(bb) % 2, u = frac(bb), bx = lerp(side ? 1100 : 820, side ? 820 : 1100, u), by = 470 - Math.sin(u * Math.PI) * 70;
    glossBall(bx, by, 28, 28, EP.magenta, { lw: 4, rim: null });
    if (sing) { const k = pop(lt, hear, .2); ctx.save(); ctx.translate(960, 480); ctx.scale(k, k); poly(heartPts(0, 0, 60, 24)); paint(EP.magenta, EP.line, 6); ctx.restore(); }
    nameTip(WHO.sam.name, 620, 470, { pop: pop(lt, .06), to: [780, 530], size: 28 });
    nameTip(WHO.elon.name, 1310, 470, { pop: pop(lt, .1), to: [1140, 530], size: 28 });
  });

  // =====================================================================================
  // V4.9 Trump's the guardrail (High IQ!) — cosmic bumper bowling: the left bumper is the post's own words, STRONG / AND SMART / (HIGH IQ!),
  // and the right bumper is TRUMP himself, arms spread in the gutter. MC TOKEN's AI ball bonks off the words, then off him, and strikes; he
  // pumps both fists. The post itself scrolls on a 90s pager.
  const HZ = 190, lane = (u, sx) => { const z = 1 + u * 4, sc = 1 / z, y = HZ + (1100 - HZ) * sc; return [W / 2 + sx * 440 * sc, y, sc]; };
  line('V4', 9, (p, lt, d, t) => {
    const h1 = bt(t, lt, 0), h2 = bt(t, lt, 1), b3 = bt(t, lt, 2);
    setLight({ rim: EP.cyan, rimK: .85 });
    bgGrad([[0, '#0A0020'], [1, '#2A0660']]);
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; for (let i = 0; i < 36; i++) { const x = hash2(i, 1) * W, y = hash2(i, 2) * 700; ctx.strokeStyle = alpha([EP.laser, EP.magenta, EP.cyan, EP.yellow][i % 4], .5); ctx.lineWidth = 5; ctx.beginPath(); if (i % 3) ctx.arc(x, y, 14 + hash(i) * 20, 0, TAU); else { ctx.moveTo(x - 20, y); ctx.lineTo(x + 20, y); ctx.moveTo(x, y - 20); ctx.lineTo(x, y + 20); } ctx.stroke(); } ctx.restore();
    // the lane
    const [l0x, l0y] = lane(0, -1), [r0x] = lane(0, 1), [l1x, l1y] = lane(1, -1), [r1x] = lane(1, 1);
    poly([[l0x, l0y], [r0x, l0y], [r1x, l1y], [l1x, l1y]]); ctx.fillStyle = lg(0, l1y, 0, l0y, [[0, '#1A2A8A'], [1, '#5A3AC8']]); ctx.fill();
    ctx.strokeStyle = 'rgb(160 200 255 / .25)'; ctx.lineWidth = 2; for (let i = -6; i <= 6; i++) { const [ax, ay] = lane(0, i / 6.5), [bx2, by2] = lane(1, i / 6.5); ctx.beginPath(); ctx.moveTo(ax, ay); ctx.lineTo(bx2, by2); ctx.stroke(); }
    for (let i = -2; i <= 2; i++) { const [ax, ay, sc] = lane(.25, i * .3); poly([[ax, ay - 30 * sc * 3], [ax + 14 * sc * 3, ay], [ax - 14 * sc * 3, ay]]); ctx.fillStyle = alpha(EP.yellow, .7); ctx.fill(); }
    // the bumpers, spelled out in the post's own words
    const rail = (side, words, us, hit) => {
      const [ax, ay] = lane(0, side * 1.08), [bx2, by2] = lane(1, side * 1.08), c = side < 0 ? EP.magenta : EP.cyan;
      ctx.save(); ctx.globalCompositeOperation = 'lighter'; ctx.strokeStyle = alpha(c, .8); ctx.lineCap = 'round'; ctx.lineWidth = 14; ctx.beginPath(); ctx.moveTo(ax, ay); ctx.lineTo(bx2, by2); ctx.stroke(); ctx.strokeStyle = alpha(c, .2); ctx.lineWidth = 50; ctx.stroke(); ctx.restore();
      for (let i = words.length - 1; i >= 0; i--) {
        const [x, y, sc] = lane(us[i], side * 1.1), hk = lt > hit && lt < hit + .3 ? Math.sin((lt - hit) / .3 * Math.PI) : 0, me = i === words.length - 1;
        const s = (.55 + sc * 1.3) * (1 + (me ? hk * .3 : 0)), bw = textW(words[i], 44, 'archivo') + 34;
        ctx.save(); ctx.translate(x - side * (me ? hk * 20 : 0), y - 34 * s); ctx.scale(s, s); ctx.rotate(side * (me ? hk * .12 : 0));
        gloss(pfRR(-bw / 2, -34, bw, 68, 18), c, { box: [-bw / 2, -34, bw, 68], lw: 4, spec: .9, rim: EP.white }); txt(words[i], 0, 2, 44, EP.line, { font: 'archivo' }); ctx.restore();
      }
    };
    rail(-1, ['STRONG', 'AND SMART', '(HIGH IQ!)'], [.62, .32, .1], h1);
    { const [ax, ay] = lane(0, 1.08), [bx2, by2] = lane(1, 1.08); ctx.save(); ctx.globalCompositeOperation = 'lighter'; ctx.strokeStyle = alpha(EP.cyan, .8); ctx.lineCap = 'round'; ctx.lineWidth = 14; ctx.beginPath(); ctx.moveTo(ax, ay); ctx.lineTo(bx2, by2); ctx.stroke(); ctx.strokeStyle = alpha(EP.cyan, .2); ctx.lineWidth = 50; ctx.stroke(); ctx.restore(); }
    // pins
    const struck = lt > b3, pa = lt - b3;
    for (let r = 3; r >= 0; r--) for (let i = 0; i <= r; i++) { const sx2 = (i - r / 2) * .3, u = .86 - (3 - r) * .05, [x, y, sc] = lane(u, sx2), id = r * 5 + i, fx2 = struck ? x + (hash(id) - .5) * 1400 * pa : x, fy = struck ? y - 600 * pa + 1400 * pa * pa : y; ctx.save(); ctx.translate(fx2, fy); ctx.rotate(struck ? pa * (hash(id + 3) - .5) * 20 : 0); const s = sc * 4.2; gloss(pfEll(0, -40 * s, 13 * s, 34 * s), '#FFFFFF', { box: [-13 * s, -74 * s, 26 * s, 68 * s], lw: 3, spec: .8 }); ctx.fillStyle = EP.red; ctx.fillRect(-12 * s, -56 * s, 24 * s, 5 * s); ctx.restore(); }
    // TRUMP, the right-hand guardrail: arms spread in the gutter; the ball bonks off his shins; a double fist pump for the strike
    { const [tx, ty, tsc] = lane(.22, 1.25), hk = lt > h2 && lt < h2 + .3 ? Math.sin((lt - h2) / .3 * Math.PI) : 0, ts = 90 * tsc;
      toy(tx, ty, ts, { ...WHO.trump.o, ...(struck ? { hL: [-3.4, -9.0 + kick(t, 8) * .6], hR: [3.4, -9.0 + kick(t, 8) * .6], gL: 'fist', gR: 'fist', eyes: 'happy', mouth: 'grin' } : { hL: [-3.7, -7.0 + Math.sin(t * 9) * .15], hR: [3.7, -7.0 - Math.sin(t * 9) * .15], gL: 'open', gR: 'open', eyes: hk > .3 ? 'wide' : 'dot', mouth: hk > .3 ? 'O' : 'smirk' }), sq: -hk * .12, lean: hk * .08, turn: -.25, bob: kick(t, 6) * .3 });
      nameTip(WHO.trump.name, tx - 330, ty - 9.6 * ts, { pop: pop(lt, h2 - .1, .15), size: 30, to: [tx - 2.4 * ts, ty - 9.2 * ts] }); }
    // the AI ball: bonks left, bonks right, strikes
    const bl = lt < b3 ? kf(lt, [[0, [.02, -.45]], [h1, [.12, -.85]], [h2, [.22, .85]], [b3, [.8, 0]]], x => x) : [.8, 0], [bxp, byp, bsc] = lane(bl[0], bl[1]);
    if (lt < b3 + .04) { const r = 150 * bsc; glossBall(bxp, byp - r, r, r, CANDY.graphite, { lw: 5, rim: EP.cyan }); ptext('AI', bxp - r * .1, byp - r * 1.3, r * .7, { fill: '#FFFFFF', strokes: [[EP.line, r * .08]] }); for (const sd of [-1, 1]) { ell(bxp + sd * r * .3, byp - r * .68, r * .09, r * .12); ctx.fillStyle = '#AFFFF0'; ctx.fill(); } }
    for (const [h, sd] of [[h1, -1], [h2, 1]]) if (lt > h && lt < h + .25) burst('BONK!', sd < 0 ? 340 : 1010, sd < 0 ? 520 : 470, 80, { pop: pop(lt, h, .1), col: EP.yellow, ink: EP.magenta, rot: sd * .2 });
    if (struck) burst('STRIKE!', 540, 260, 170, { pop: pop(lt, b3, .15), col: EP.lime, ink: '#0A3A10', spin: .3 });
    // MC TOKEN's follow-through
    toy(190, 1080, 42, { ...CAST.token.o, mic: 'L', hR: [3.2, -4.6], gR: 'open', lean: .12, fR: [.5, -.3], turn: .4, ...tok(t) });
    // the pager
    const px = 1460, py = 560;
    gloss(pfRR(px, py, 420, 240, 36), '#1A1A22', { box: [px, py, 420, 240], lw: 6, rim: EP.cyan });
    ctx.fillStyle = '#9AC88A'; rrect(px + 28, py + 32, 364, 134, 10); ctx.fill(); ctx.strokeStyle = EP.line; ctx.lineWidth = 4; ctx.stroke();
    ctx.save(); rrect(px + 28, py + 32, 364, 134, 10); ctx.clip();
    txt('TRUTH SOCIAL · SEP 14', px + 42, py + 56, 20, '#1A3A1A', { font: 'code', align: 'left' });
    const msg = "the only control or 'guardrails' that AI needs is a STRONG AND SMART (High IQ!) PRESIDENT", mw = textW(msg, 34, 'code') + 120, mo = (lt * 700) % mw;
    for (let q = 0; q < 2; q++) txt(msg, px + 380 - mo + q * mw, py + 116, 34, '#0A1A0A', { font: 'code', align: 'left' });
    ctx.restore();
    for (let i = 0; i < 3; i++) glossBall(px + 110 + i * 100, py + 204, 22, 16, '#3A3A48', { lw: 3, rim: null });
    if (frac(t * 4) < .5) { ctx.fillStyle = EP.red; ell(px + 392, py + 18, 9, 9); ctx.fill(); }
  });

  // =====================================================================================
  // V4.10 Bernie, Bannon share a pew — a gospel choir (a Eurodance staple) under stained glass: BERNIE and STEVE side by side on one pew
  // with PRO-HUMAN hymnals, singing… then scooting to opposite ends on the beat.
  const hymnal = s => { ctx.save(); ctx.rotate(-.1); gloss(pfRR(-70, -95, 140, 110, 8), '#8A1020', { box: [-70, -95, 140, 110], lw: 4, spec: .6 }); ctx.fillStyle = EP.gold; ctx.fillRect(-58, -86, 4, 92); txt('PRO-', 6, -60, 26, EP.gold, { font: 'abril' }); txt('HUMAN', 6, -30, 26, EP.gold, { font: 'abril' }); ctx.restore(); };
  line('V4', 10, (p, lt, d, t) => {
    const b3 = bt(t, lt, 3), sc = easeOut(clamp((lt - b3) / .16)), apart = lt >= b3, bb = bpOf(t);
    setLight({ rim: EP.gold, rimK: .75 });
    bgGrad([[0, '#2A1406'], [1, '#5A3010']]);
    for (let i = 0; i < 16; i++) { ctx.fillStyle = i % 2 ? 'rgb(0 0 0 / .12)' : 'rgb(255 200 120 / .05)'; ctx.fillRect(i * 124, 0, 124, H); }
    // the stained-glass window + its light
    const wx = 960, wy = 140, ww = 440, wh = 460;
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; ctx.fillStyle = lg(0, wy, 0, 1000, [[0, 'rgb(255 220 150 / .28)'], [1, 'rgb(255 180 100 / .02)']]); poly([[wx - 200, wy + 200], [wx + 200, wy + 200], [wx + 560, 1080], [wx - 560, 1080]]); ctx.fill(); ctx.restore();
    ctx.save(); ctx.beginPath(); ctx.moveTo(wx - ww / 2, wy + wh); ctx.lineTo(wx - ww / 2, wy + ww / 2); ctx.arc(wx, wy + ww / 2, ww / 2, Math.PI, 0); ctx.lineTo(wx + ww / 2, wy + wh); ctx.closePath(); ctx.clip();
    const glassC = ['#E0203A', '#1A6AE8', '#FFD01F', '#2AB84A', '#A040E0', '#FF7A1A'];
    for (let j = 0; j < 8; j++) for (let i = 0; i < 7; i++) { const x = wx - ww / 2 + i * ww / 7 + (j % 2) * 20 - 20, y = wy + j * wh / 8, c = glassC[Math.floor(hash2(i, j) * 6)]; ctx.fillStyle = mixCol(c, '#FFFFFF', .15 + .15 * Math.sin(t * 2 + i + j)); poly([[x, y], [x + ww / 7 + 4, y + (hash2(j, i) - .5) * 30], [x + ww / 7, y + wh / 8 + 4], [x - 4, y + wh / 8]]); ctx.fill(); ctx.strokeStyle = '#1A1008'; ctx.lineWidth = 6; ctx.stroke(); }
    ctx.fillStyle = 'rgb(255 255 255 / .9)'; poly(starPts(wx, wy + 170, 70, .45, 8, t * .3)); ctx.fill();
    ctx.restore();
    ctx.strokeStyle = '#1A1008'; ctx.lineWidth = 14; ctx.beginPath(); ctx.moveTo(wx - ww / 2, wy + wh); ctx.lineTo(wx - ww / 2, wy + ww / 2); ctx.arc(wx, wy + ww / 2, ww / 2, Math.PI, 0); ctx.lineTo(wx + ww / 2, wy + wh); ctx.stroke();
    // the choir behind, swaying
    const choir = [[300, 0], [520, 2], [1400, 4], [1620, 1]];
    choir.forEach(([x, sk], i) => toy(x, 760, 34, { top: 'robe', topCol: '#6A1A8A', trim: EP.gold, skin: sk, hair: ['afro', 'bun', 'short', 'curly'][i], hairCol: THAIR.black, ...dance(i % 2 ? 'wave' : 'clap', bb - i * .15), talk: singK(t, i * .3), eyes: 'closed', shadow: false }));
    // hymn board
    gloss(pfRR(40, 330, 190, 250, 10), '#3A2010', { box: [40, 330, 190, 250], lw: 5, rim: EP.gold }); txt('TODAY', 135, 370, 26, EP.gold, { font: 'abril' }); for (const [i, s] of ['PRO-', 'HUMAN', 'ASSEMBLY'].entries()) txt(s, 135, 430 + i * 44, 28, '#FFFFFF', { font: 'archivo', maxW: 170 });
    // Bernie and Steve on one pew
    const xB = lerp(850, 520, sc), xS = lerp(1075, 1400, sc);
    for (const [x, w, o] of [[xB, 'B', { ...WHO.bernie.o }], [xS, 'S', { ...WHO.bannon.o }]]) {
      const left = w === 'B';
      toy(x, 1000, 52, { ...o, hL: [-.9, -5.6], hR: [.9, -5.6], gL: left ? 'open' : 'open', gR: 'open', hold: hymnal, talk: apart ? undefined : singK(t, left ? 0 : .4), mouth: apart ? 'flat' : undefined, eyes: apart ? 'dot' : 'closed', turn: apart ? (left ? -.5 : .5) : (left ? .3 : -.3), lean: apart ? 0 : (left ? .05 : -.05), shadow: false, bob: apart ? 0 : kick(t, 6) * .3 });
    }
    if (apart && lt < b3 + .3) { ctx.save(); ctx.globalAlpha = 1 - (lt - b3) / .3; ctx.strokeStyle = '#FFFFFF'; ctx.lineWidth = 6; for (const [x, sd] of [[xB, 1], [xS, -1]]) for (let i = 0; i < 3; i++) { ctx.beginPath(); ctx.moveTo(x + sd * 150, 640 + i * 50); ctx.lineTo(x + sd * 260, 640 + i * 50); ctx.stroke(); } ctx.restore(); }
    // the pew (in front of them)
    gloss(pfRR(200, 800, 1520, 70, 14), '#6A3A18', { box: [200, 800, 1520, 70], lw: 6, spec: .7, rim: EP.gold }); gloss(pfRR(220, 870, 1480, 160, 6), '#4A2810', { box: [220, 870, 1480, 160], lw: 5, spec: .3 });
    for (const x of [200, 1720]) gloss(pfRR(x - 30, 760, 60, 300, 20), '#5A3014', { box: [x - 30, 760, 60, 300], lw: 5, spec: .5 });
    nameTip(WHO.bernie.name, xB - 170, 330, { pop: pop(lt, .06), to: [xB - 40, 450], size: 30 });
    nameTip(WHO.bannon.name, xS + 170, 330, { pop: pop(lt, .12), to: [xS + 40, 450], size: 30 });
  });

  // =====================================================================================
  // V4.11 Claude builds Claude — now one in four! — DJ CLAWD with a wrench, tightening a mini Clawd together on the bench (legs, phones,
  // eyes on: it waves), beside the pie chart: Claude leads 26% of its AI R&D work, up from under 1% in February.
  const wrench = ang => u => { ctx.save(); ctx.rotate(ang); ctx.fillStyle = '#C8CCD8'; ctx.strokeStyle = EP.line; ctx.lineWidth = 4; rrect(-6, -12, 130, 24, 10); ctx.fill(); ctx.stroke(); ctx.beginPath(); ctx.arc(140, 0, 32, .7, TAU - .7); ctx.lineTo(118, 0); ctx.closePath(); ctx.fill(); ctx.stroke(); ctx.restore(); };
  line('V4', 11, (p, lt, d, t) => {
    const b = [0, 1, 2].map(k => bt(t, lt, k)), n = b.filter(x => lt >= x).length, since = n ? lt - b[n - 1] : 9, pk = ease(clamp((lt - b[1]) / .3));
    setLight({ rim: EP.cyan, rimK: .8 });
    bgGrad([[0, '#12053A'], [1, '#3A0A6A']]);
    // the blueprint on the wall
    ctx.save(); ctx.translate(560, 330); ctx.rotate(-.03); rrect(-330, -210, 660, 400, 8); paint('#1A4AA8', EP.line, 5);
    ctx.strokeStyle = 'rgb(255 255 255 / .18)'; ctx.lineWidth = 2; for (let i = -320; i < 330; i += 40) { ctx.beginPath(); ctx.moveTo(i, -210); ctx.lineTo(i, 190); ctx.stroke(); } for (let j = -200; j < 190; j += 40) { ctx.beginPath(); ctx.moveTo(-330, j); ctx.lineTo(330, j); ctx.stroke(); }
    ctx.strokeStyle = '#FFFFFF'; ctx.lineWidth = 5; ctx.strokeRect(-150, -120, 300, 180); for (const x of [-110, -40, 40, 110]) ctx.strokeRect(x - 16, 60, 32, 70); for (const sd of [-1, 1]) { ctx.strokeRect(sd * 150 + (sd > 0 ? 0 : -60), -60, 60, 36); ell(sd * 60, -70, 16, 22); ctx.stroke(); }
    txt('CLAUDE.BLUEPRINT', 0, -170, 30, '#FFFFFF', { font: 'code' }); ctx.restore();
    // the bench
    gloss(pfRR(380, 780, 820, 50, 10), '#8A8E9E', { box: [380, 780, 820, 50], lw: 5, rim: EP.cyan }); ctx.fillStyle = '#4A4E5E'; ctx.fillRect(420, 830, 30, 200); ctx.fillRect(1130, 830, 30, 200);
    // the mini Clawd coming together
    const mx = 950, my = 780, done = n >= 3;
    djClawd(mx, my - (n >= 1 ? 0 : -10), 17, { legs: n >= 1, phones: n >= 2, eyes: done ? 'happy' : 'closed', mouth: done ? 'grin' : 'none', aL: done ? .9 + Math.sin(t * 14) * .4 : -.9, aR: -.9, jump: done ? Math.abs(Math.sin((lt - b[2]) * 7)) * 1.2 : 0, });
    // DJ CLAWD with the wrench
    const tw = n < 3 && since < .2 ? Math.sin(since / .2 * Math.PI) * .6 : 0;
    djClawd(560, 780, 26, { aR: .15 - tw * .5, hold: wrench(.35 + tw), aL: .5 + Math.sin(bpOf(t) * Math.PI) * .2, eyes: done ? 'happy' : 'normal', look: [1, .3], mouth: done ? 'grin' : 'smile', blush: done ? .6 : 0, sweat: n < 3 ? .5 : 0 });
    if (since < .18) { const k = since / .18; for (let i = 0; i < 8; i++) { const a = hash2(n, i) * TAU; ctx.strokeStyle = i % 2 ? EP.yellow : '#FFFFFF'; ctx.lineWidth = 5; ctx.beginPath(); ctx.moveTo(860 + Math.cos(a) * 20 * k, 700 + Math.sin(a) * 20 * k); ctx.lineTo(860 + Math.cos(a) * (50 + 90 * k), 700 + Math.sin(a) * (50 + 90 * k)); ctx.stroke(); } glow(860, 700, 140, EP.yellow, 1 - k); }
    // the pie
    const pct = lerp(.008, .26, pk), cx = 1470, cy = 520, r = 250, ry = r * .55, th = 50, a0 = -Math.PI / 2 - .3 + Math.sin(t * .8) * .1;
    ctx.fillStyle = '#3A3E52'; ell(cx, cy + th, r, ry); ctx.fill(); ctx.fillStyle = '#5A5E72'; ctx.fillRect(cx - r, cy, r * 2, th);
    ell(cx, cy, r, ry); ctx.fillStyle = '#B8BCD0'; ctx.fill(); ctx.strokeStyle = EP.line; ctx.lineWidth = 5; ctx.stroke();
    ctx.save(); ctx.translate(cx, cy); ctx.scale(1, ry / r); ctx.beginPath(); ctx.moveTo(0, 0); ctx.arc(0, 0, r, a0, a0 + pct * TAU); ctx.closePath(); ctx.restore();
    ctx.fillStyle = lg(cx - r, cy - ry, cx + r, cy + ry, [[0, EP.clawdLt], [1, EP.clawd]]); ctx.fill(); ctx.stroke();
    if (pk <= 0 || pk >= 1) { ptext(pk <= 0 ? '<1%' : '26%', cx + 60, cy - 70, 90, { fill: '#FFFFFF', strokes: [[EP.clawdDk, 14]] }); pixText(pk <= 0 ? 'FEB 2026' : 'AUG 2026', cx, cy + 120, 6, '#FFFFFF', { align: 'center' }); }
    ptext('AI R&D LED BY CLAUDE', cx, 190, 48, { fill: '#FFFFFF', strokes: [[EP.line, 10]] });
  });

  // =====================================================================================
  // V4.12 Chatbot nearly starts a war! — a 90s real-time-strategy map: the chatbot's intel flags a cargo ship (NUCLEAR PARTS?!), the jets
  // scramble on the beat… ERROR: HALLUCINATION, and they wheel round and fly home. A Windows smiley sweats in the sidebar.
  function jet(x, y, a, s) { ctx.save(); ctx.translate(x, y); ctx.rotate(a); ctx.scale(s, s); poly([[30, 0], [-6, -8], [-10, -30], [-18, -30], [-16, -6], [-26, -4], [-30, -14], [-34, -14], [-32, 0], [-34, 14], [-30, 14], [-26, 4], [-16, 6], [-18, 30], [-10, 30], [-6, 8]]); paint('#C8CCD8', EP.line, 2.5); ctx.restore(); }
  line('V4', 12, (p, lt, d, t) => {
    const b1 = bt(t, lt, 1), b3 = bt(t, lt, 3), err = lt >= b3, alarm = lt > b1 && !err;
    setLight({ rim: EP.white, rimK: .4 });
    fillAll('#0A4A6A');
    ctx.strokeStyle = 'rgb(255 255 255 / .08)'; ctx.lineWidth = 2; for (let i = 0; i < 24; i++) { ctx.beginPath(); ctx.moveTo(i * 64, 0); ctx.lineTo(i * 64, H); ctx.stroke(); } for (let j = 0; j < 18; j++) { ctx.beginPath(); ctx.moveTo(0, j * 64); ctx.lineTo(1440, j * 64); ctx.stroke(); }
    for (let i = 0; i < 30; i++) { const x = hash2(i, 1) * 1440, y = hash2(i, 2) * H, o = (t * 30 + i * 13) % 40; ctx.strokeStyle = 'rgb(200 240 255 / .15)'; ctx.lineWidth = 3; ctx.beginPath(); ctx.moveTo(x + o, y); ctx.lineTo(x + o + 22, y); ctx.stroke(); }
    poly([[-20, -20], [380, -20], [420, 200], [360, 420], [440, 640], [380, 900], [300, 1100], [-20, 1100]]); ctx.fillStyle = '#3A8A3A'; ctx.fill(); ctx.strokeStyle = '#E8D8A0'; ctx.lineWidth = 12; ctx.stroke();
    for (let i = 0; i < 14; i++) { ctx.fillStyle = 'rgb(20 80 30 / .6)'; ell(hash2(i, 5) * 300 + 20, hash2(i, 6) * 1000, 30, 22); ctx.fill(); }
    ctx.fillStyle = '#5A5E6A'; ctx.save(); ctx.translate(210, 560); ctx.rotate(-.5); ctx.fillRect(-150, -26, 300, 52); ctx.fillStyle = '#FFFFFF'; for (let i = 0; i < 6; i++) ctx.fillRect(-130 + i * 50, -3, 26, 6); ctx.restore();
    // the ship
    const shx = 1060, shy = 470;
    ctx.save(); ctx.translate(shx, shy); ctx.rotate(-.2); poly([[-120, -30], [90, -30], [140, 0], [90, 30], [-120, 30]]); paint('#8A8E9E', EP.line, 4); for (let i = 0; i < 4; i++) { ctx.fillStyle = ['#C8402A', '#2A6AC8', '#E8C02A', '#2A9A4A'][i]; ctx.fillRect(-100 + i * 42, -20, 34, 40); } ctx.restore();
    const selA = err ? .5 : 1; ctx.strokeStyle = err ? EP.laser : EP.red; ctx.lineWidth = 6; ctx.globalAlpha = selA; for (const [sx, sy] of [[-1, -1], [1, -1], [1, 1], [-1, 1]]) { ctx.beginPath(); ctx.moveTo(shx + sx * 170, shy + sy * 60); ctx.lineTo(shx + sx * 170, shy + sy * 100); ctx.lineTo(shx + sx * 130, shy + sy * 100); ctx.stroke(); } ctx.globalAlpha = 1;
    if (!err) { rrect(shx - 170, shy - 190, 340, 60, 10); paint(EP.red, EP.line, 4); txt('NUCLEAR PARTS?!', shx, shy - 158, 34, '#FFFFFF', { font: 'archivo' }); }
    else { rrect(shx - 170, shy - 190, 340, 60, 10); paint(EP.laser, EP.line, 4); txt('JUST CARGO', shx, shy - 158, 34, '#0A3A10', { font: 'archivo' }); }
    // three jets: scramble at b1, wheel round at the error
    for (let i = 0; i < 3; i++) {
      const L = lt - b1 - i * .08; if (L < 0) continue;
      const out = Math.min(L, b3 - b1 - i * .08), bx0 = 260 + i * 30, by0 = 560 + (i - 1) * 70, tx = 820, ty = 470 + (i - 1) * 90, u = clamp(out / (b3 - b1));
      let x = lerp(bx0, tx, easeOut(u)), y = lerp(by0, ty, easeOut(u)), a = Math.atan2(ty - by0, tx - bx0);
      if (err) { const r = lt - b3; const turn = clamp(r / .3); a += turn * Math.PI; x += Math.sin(turn * Math.PI) * 60 - clamp((r - .3) / .6) * 500; y += (1 - Math.cos(turn * Math.PI)) * 50 * (i - 1 || 1); }
      ctx.strokeStyle = 'rgb(255 255 255 / .35)'; ctx.lineWidth = 6; ctx.beginPath(); ctx.moveTo(bx0, by0); ctx.lineTo(x, y); ctx.stroke();
      jet(x, y, a, 2.2);
    }
    if (alarm) { ctx.save(); ctx.globalCompositeOperation = 'lighter'; ctx.strokeStyle = `rgb(255 30 30 / ${.3 + .3 * kick(t, 5)})`; ctx.lineWidth = 60; ctx.strokeRect(0, 0, 1440, H); ctx.restore(); }
    pixText(err ? 'RECALL ALL UNITS!' : alarm ? 'UNITS LAUNCHED' : 'INTEL INCOMING...', 720, 860, 7, err ? EP.laser : EP.yellow, { align: 'center', glow: true, edge: '#000' });
    // the sidebar
    ctx.fillStyle = '#3A3E4A'; ctx.fillRect(1440, 0, 480, H); bevel(1440, 0, 480, H, { b: 6, fill: '#4A4E5A' });
    bevel(1470, 170, 420, 250, { sunken: true, fill: '#0A1A2A' }); ctx.fillStyle = '#2A6A3A'; ctx.fillRect(1480, 180, 90, 230); ctx.fillStyle = EP.red; ell(1740, 270, 7, 7); ctx.fill(); ctx.strokeStyle = '#FFFFFF'; ctx.lineWidth = 2; ctx.strokeRect(1640, 220, 180, 120);
    bevel(1470, 440, 420, 420, { sunken: true, fill: err ? '#2A0A0A' : '#0A1A2A' });
    gumdrop(1570, 640, 17, { col: CANDY.snow, label: 'CHATBOT', face: err ? 'x' : 'happy', mouth: err ? 'wavy' : 'grin', sweat: err ? 1 : 0, hands: false, shadow: false, glitch: err ? .6 : 0 });
    if (!err) { txt('INTEL:', 1660, 480, 26, EP.cyan, { font: 'code', align: 'left' }); ['SHIP HAS', 'NUCLEAR', 'PARTS!', 'CONFIDENCE:', 'HIGH'].forEach((s, i) => txt(s, 1660, 520 + i * 34, i === 4 ? 30 : 24, i === 4 ? EP.laser : '#FFFFFF', { font: 'code', align: 'left' })); }
    else if (frac((lt - b3) * 5) < .75) { txt('ERROR:', 1680, 520, 40, EP.red, { font: 'archivo', align: 'center' }); txt('HALLU-', 1760, 580, 40, EP.red, { font: 'archivo' }); txt('CINATION', 1760, 630, 40, EP.red, { font: 'archivo' }); }
    // the Windows smiley, sweating
    const smx = 1790, smy = 780; ctx.save(); ctx.translate(smx, smy); ctx.scale(1.5, 1.5); ctx.translate(-smx, -smy); bevel(smx - 46, smy - 46, 92, 92, { b: 4 }); ell(smx, smy, 32, 32); paint(EP.yellow, '#000', 3);
    ctx.fillStyle = '#000'; ell(smx - 11, smy - 7, 4, 6); ctx.fill(); ell(smx + 11, smy - 7, 4, 6); ctx.fill();
    if (lt > b1) { ell(smx, smy + 13, 8, 10); ctx.fill(); const sw = frac(t * 2); ctx.fillStyle = '#7FD4FF'; poly([[smx + 30, smy - 30 + sw * 20], [smx + 38, smy - 12 + sw * 20], [smx + 22, smy - 12 + sw * 20]]); ctx.fill(); ell(smx + 30, smy - 12 + sw * 20, 8, 8); ctx.fill(); } else { ctx.beginPath(); ctx.arc(smx, smy + 2, 16, .3, Math.PI - .3); ctx.strokeStyle = '#000'; ctx.lineWidth = 3; ctx.stroke(); }
    ctx.restore();
    if (err && lt < b3 + .1) fx({ rgb: .8 });
  });

  // =====================================================================================
  // V4.13 Trump: It's "Super," by decree! — a 16-bit title screen: the poll's options SUPERIOR / EXTREME / SUPREME flicker under the
  // cursor… then SUPER, which wasn't one of them, slams over everything: HEREINAFTER OFFICIALLY CALLED SUPER INTELLIGENCE, PRESS START.
  // Below, TRUMP at the UN General Assembly lectern holds forth, then points up at SUPER with a big grin as it lands (a speech, not a
  // signed order, so no pen).
  line('V4', 13, (p, lt, d, t) => {
    const sup = wl(13, 2, t, lt), slam = lt >= sup, sk = clamp((lt - sup) / .14), sh = shakeAt(t, lt, sup, .3, 18);
    starfield(t, { speed: .5, bg: '#05020E' });
    camBegin(W / 2 - sh[0], H / 2 - sh[1], 1);
    // the podium
    gloss(pfRR(700, 640, 520, 300, 10), '#1E5A44', { box: [700, 640, 520, 300], lw: 5, rim: EP.gold, spec: .4 });
    ctx.strokeStyle = 'rgb(255 255 255 / .12)'; ctx.lineWidth = 3; for (let i = 0; i < 5; i++) { ctx.beginPath(); ctx.moveTo(710, 670 + i * 55); ctx.bezierCurveTo(820, 650 + i * 62, 1000, 700 + i * 46, 1210, 660 + i * 58); ctx.stroke(); }
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; ctx.fillStyle = 'rgb(255 250 220 / .12)'; poly([[930, 0], [990, 0], [1180, 1000], [740, 1000]]); ctx.fill(); ctx.restore();
    // TRUMP at the lectern: gesturing as he speaks, then pointing up at SUPER as it slams in
    const gest = Math.sin(t * 7), tk = clamp(.3 + .7 * Math.abs(Math.sin(t * 10)));
    toy(960, 1062, 37, { ...WHO.trump.o, shadow: false, rim: '#8AD8FF', ...(slam ? { hR: [3.4, -10.4], gR: 'point', hL: [-2.6, -6.4], gL: 'fist', eyes: 'happy', mouth: 'grin', lean: -.04 } : { hL: [-3.0 - gest * .3, -6.9 + gest * .5], hR: [3.0 + gest * .3, -6.9 - gest * .5], gL: 'point', gR: 'open', talk: tk, look: [.2, -.2] }), bob: kick(t, 6) * .2 });
    gloss(pfPts([[828, 1090], [1092, 1090], [1066, 905], [854, 905]]), '#8A6A3A', { box: [828, 905, 264, 185], lw: 5, rim: EP.gold });
    ell(960, 948, 32, 32); paint(EP.gold, EP.line, 4); ctx.strokeStyle = '#6A4A00'; ctx.lineWidth = 3; for (const sd of [-1, 1]) { ctx.beginPath(); ctx.arc(960, 948, 24, Math.PI / 2 + sd * .3, Math.PI / 2 + sd * 2.4, sd < 0); ctx.stroke(); } poly(starPts(960, 948, 13, .45, 5)); ctx.fillStyle = '#6A4A00'; ctx.fill();
    ctx.strokeStyle = '#2A2A34'; ctx.lineWidth = 6; ctx.beginPath(); ctx.moveTo(1030, 905); ctx.quadraticCurveTo(1045, 865, 1030, 830); ctx.stroke(); glossBall(1028, 825, 11, 11, '#2A2A34', { lw: 2 });
    camEnd();
    nameTip(WHO.trump.name, 1420, 720, { pop: pop(lt, .08), sub: 'UN GENERAL ASSEMBLY', size: 30, to: [1090, 720] });
    // the poll menu (before) / the title (after)
    const opts = ['SUPERIOR', 'EXTREME', 'SUPREME'], cur = Math.floor(lt / (BL() / 2)) % 3;
    if (!slam || lt < sup + .3) {
      const fa = slam ? clamp(1 - (lt - sup) / .16) : 1;
      pixText('SELECT A NAME:', 960, 150, 6, EP.cyan, { align: 'center', alpha: fa });
      opts.forEach((o, i) => { const a = slam ? lt - sup : 0, x = 960 + (slam ? (i - 1) * 3000 * a : 0), y = 260 + i * 110 + (slam ? 1400 * a : 0); pixText(o + ' INTELLIGENCE', x, y, 7, i === cur && !slam ? EP.yellow : '#FFFFFF', { align: 'center', edge: '#000', alpha: fa }); if (i === cur && !slam) pixText('▶', x - 520, y, 7, EP.yellow); });
    }
    if (slam) {
      pixText('HEREINAFTER OFFICIALLY CALLED', 960, 112, 5, EP.cyan, { align: 'center', alpha: clamp((lt - sup - .1) / .1) });
      chromeText('SUPER', 960, 272, 250, { style: 'gold', italic: .14, depth: 26, s: lerp(2.4, 1, easeOut(sk)), alpha: clamp(sk * 3) });
      chromeText('INTELLIGENCE', 960, 466, 110, { style: 'ice', italic: .14, depth: 12, alpha: clamp((lt - sup - .08) / .12) });
      if (lt > sup + .35 && frac(t * 2.5) < .6) pixText('PRESS START', 960, 538, 7, '#FFFFFF', { align: 'center', edge: EP.red });
      sweepGlint(700, 1220, 232, (lt - sup - .2) / .5, 140);
    }
    if (slam && lt < sup + .1) fx({ flash: .6 * (1 - (lt - sup) / .1) });
  });

  // =====================================================================================
  // V4.14 "Artificial"? Fake to me! — the channel's own news graphic, ARTIFICIAL INTELLIGENCE: ARTIFICIAL gets a red ✗ and a FAKE! stamp
  // on the beat, and a SUPER sticker slaps over it on the next. Anchor MC TOKEN reads it out.
  line('V4', 14, (p, lt, d, t) => {
    const b1 = bt(t, lt, 1), b2 = bt(t, lt, 2), xk = clamp((lt - b1 + .05) / .15), sk = clamp((lt - b2) / .12);
    setLight({ rim: EP.red, rimK: .5 });
    bgGrad([[0, '#F4F6FA'], [1, '#C8D0E0']]);
    ctx.fillStyle = EP.red; poly([[-50, 700], [W + 50, 560], [W + 50, 640], [-50, 780]]); ctx.fill(); ctx.fillStyle = '#16307A'; poly([[-50, 780], [W + 50, 640], [W + 50, 700], [-50, 840]]); ctx.fill();
    for (let i = 0; i < 6; i++) { ctx.fillStyle = 'rgb(20 40 120 / .06)'; ell(1650, 300, 120 + i * 90, 120 + i * 90); ctx.fill(); }
    // the graphic panel
    gloss(pfRR(90, 170, 1180, 470, 24), '#10204A', { box: [90, 170, 1180, 470], lw: 6, rim: EP.red, spec: .4 });
    pixText('HYPE TV NEWS', 130, 200, 5, EP.cyan);
    const wobble = xk > 0 ? Math.sin(t * 40) * 3 * (1 - xk) : 0;
    chromeText('ARTIFICIAL', 680 + wobble, 330, 150, { style: 'silver', italic: .12, depth: 14 });
    chromeText('INTELLIGENCE', 680, 500, 120, { style: 'ice', italic: .12, depth: 12 });
    if (xk > 0) { ctx.strokeStyle = EP.red; ctx.lineWidth = 34; ctx.lineCap = 'round'; ctx.beginPath(); const a = Math.min(1, xk * 2), b = clamp(xk * 2 - 1); ctx.moveTo(250, 250); ctx.lineTo(250 + 860 * a, 250 + 180 * a); if (b > 0) { ctx.moveTo(250, 430); ctx.lineTo(250 + 860 * b, 430 - 180 * b); } ctx.stroke(); }
    slamStamp('FAKE!', 1080, 220, 70, EP.red, .15, clamp((lt - b1 - .1) / .12));
    if (sk > 0) { const s = lerp(1.8, 1, easeOut(sk)); ctx.save(); ctx.translate(690, 330); ctx.rotate(-.06); ctx.scale(s, s); ctx.fillStyle = 'rgb(0 0 0 / .3)'; rrect(-330, -96, 680, 200, 18); ctx.fill(); gloss(pfRR(-340, -106, 680, 200, 18), EP.yellow, { box: [-340, -106, 680, 200], lw: 7, spec: .9 }); ptext('SUPER', 0, 0, 160, { font: 'archivo', fill: EP.red, strokes: [[EP.line, 14]] }); ctx.restore(); }
    // the quote strip
    ctx.fillStyle = '#FFFFFF'; ctx.fillRect(90, 670, 1180, 70); ctx.fillStyle = EP.red; ctx.fillRect(90, 670, 16, 70);
    txt('"IT MAKES IT SOUND FAKE."  UN GENERAL ASSEMBLY, SEP 22', 130, 706, 30, '#10204A', { font: 'archivo', align: 'left', maxW: 1110 });
    // the anchor desk
    toy(1600, 1000, 50, { ...CAST.token.o, mic: 'R', hL: lt > b1 ? [-4.4, -8.4] : [-2.3, -6], gL: lt > b1 ? 'point' : 'open', ...tok(t), turn: -.3, lean: lt > b1 ? -.05 : 0 });
    gloss(pfPts([[1300, 780], [1900, 780], [1880, 1000], [1320, 1000]]), '#16307A', { box: [1300, 780, 600, 220], lw: 6, rim: EP.red, spec: .6 });
    ptext('HYPE★TV NEWS', 1600, 860, 44, { font: 'rammetto', fill: '#FFFFFF', maxW: 500 });
  });

  // =====================================================================================
  // V4.15 Ten days after "pace" — surprise! — the tear-off calendar rips SEP 12 (PACE THE FRONTIER) → SEP 22 on the sixteenths, the BPM
  // climbs back from 120 to 141, and the gift box on the decks rattles harder and harder until its lid pops.
  function calPage(x, y, w, h, day, note) {
    rrect(x, y, w, h, 12); paint('#FFFFFF', EP.line, 5);
    ctx.fillStyle = EP.red; ctx.fillRect(x + 6, y + 6, w - 12, h * .17); txt('SEPTEMBER', x + w / 2, y + h * .095, h * .08, '#FFFFFF', { font: 'archivo' });
    txt(String(day), x + w / 2, y + h * .54, h * .5, '#1A0F28', { font: 'abril' });
    if (note) txt(note, x + w / 2, y + h * .87, h * .075, '#1633FF', { font: 'marker', rot: -.04 });
  }
  line('V4', 15, (p, lt, d, t) => {
    const e16 = BL() / 4, r0 = bt(t, lt, 1) - e16 * 2, rips = clamp(Math.floor((lt - r0) / e16) + 1, 0, 10), sur = wl(15, 5, t, lt), surK = lt >= sur;
    const shake = lt > r0 ? clamp((lt - r0) / (sur - r0)) : 0, sh = shakeAt(t, lt, sur, .35, 20);
    setLight({ rim: EP.red, rimK: .85 });
    camBegin(W / 2 - sh[0], H / 2 - sh[1], 1 + .03 * p);
    bgGrad([[0, '#2A0008'], [1, '#5A0012']]);
    laserFan(W / 2, -20, t, { n: 9, cols: [EP.red, EP.white], angle: Math.PI / 2, spread: 1.8, sweep: .4, alpha: .45 + shake * .3, flicker: shake > .5 ? .7 : 0 });
    // the calendar
    const cx = 170, cy = 180, cw = 560, chh = 640;
    gloss(pfRR(cx - 20, cy - 30, cw + 40, chh + 60, 20), '#2A2A34', { box: [cx - 20, cy - 30, cw + 40, chh + 60], lw: 5, rim: EP.red });
    const day = 12 + rips; calPage(cx, cy, cw, chh, day, day === 12 ? 'PACE THE FRONTIER' : day === 22 ? '' : '');
    if (day === 22) { ctx.strokeStyle = EP.red; ctx.lineWidth = 12; ctx.lineCap = 'round'; ctx.beginPath(); const k = clamp((lt - r0 - 9 * e16) / .25); ctx.ellipse(cx + cw / 2, cy + chh * .55, 230, 190, -.1, -Math.PI / 2, -Math.PI / 2 + TAU * k); ctx.stroke(); }
    for (let i = 0; i < rips; i++) { const a = lt - (r0 + i * e16); if (a > .6) continue; ctx.save(); ctx.translate(cx + cw / 2 + a * 1400, cy + a * -300 + a * a * 1800); ctx.rotate(a * 5 * (i % 2 ? 1 : -1)); ctx.globalAlpha = 1 - a / .6; calPage(-cw / 2, 0, cw, chh, 12 + i, i === 0 ? 'PACE THE FRONTIER' : ''); ctx.restore(); }
    for (let i = 0; i < 7; i++) { ctx.strokeStyle = '#C8CCD8'; ctx.lineWidth = 8; ell(cx + 60 + i * 73, cy - 8, 14, 26); ctx.stroke(); }
    // the BPM, climbing back
    const bpm = Math.round(lerp(120, 141, rips / 10));
    gloss(pfRR(1080, 170, 400, 160, 18), '#12060A', { box: [1080, 170, 400, 160], lw: 5, rim: EP.red }); segText(String(bpm), 1110, 196, 100, rips >= 10 ? EP.laser : EP.amber, { off: '#2A0808' }); txt('BPM', 1400, 250, 40, '#FFFFFF', { font: 'archivo' });
    if (rips > 0 && rips < 10) ptext('▲', 1440, 200, 40, { fill: EP.laser });
    // the decks, DJ CLAWD, and the rattling box
    djClawd(1660, 822, 32, { eyes: 'wide', look: [-.8, .4], mouth: surK ? 'O' : 'o', sweat: shake, aL: .3, aR: -.2 });
    djBooth(1450, 740, 820, t);
    const rat = shake * (surK ? 1.6 : 1), bx = 1230, jmp = Math.abs(Math.sin(bpOf(t) * 4 * Math.PI)) * 30 * rat;
    giftBox(bx, 720 - jmp, 230, 180, EP.clawd, EP.magenta, { rot: Math.sin(t * 50) * .07 * rat, lid: surK ? 30 + Math.abs(Math.sin(t * 30)) * 25 : jmp * .4, lidRot: Math.sin(t * 37) * .1 * rat, tag: 'SEP 22' });
    if (rat > .3) { ctx.strokeStyle = '#FFFFFF'; ctx.lineWidth = 5; for (const sd of [-1, 1]) for (let i = 0; i < 2; i++) { ctx.beginPath(); ctx.arc(bx, 620 - jmp, 150 + i * 30, sd > 0 ? -.4 : Math.PI - .4, sd > 0 ? .4 : Math.PI + .4); ctx.stroke(); } }
    camEnd();
    strobe(strobeK(t, 2, .25) * .12 * shake);
  });

  // =====================================================================================
  // V4.16 Opus 5.5: "Hi, guys!" — the box bursts on the downbeat: a small new Clawd with a 5.5 sticker boings out on a spring, waves
  // sheepishly (HI, GUYS!), credited feat. OPUS 5.5 while DJ CLAWD blushes. A second box pops 90 minutes later: GPT-6 SOL and LUNA wave too.
  // The last beats build into the final chorus.
  line('V4', 16, (p, lt, d, t) => {
    const b1 = bt(t, lt, 1), hi = wl(16, 2, t, lt), b5 = bt(t, lt, 5), b6 = bt(t, lt, 6), open = clamp(lt / .1), sh = shakeAt(t, lt, 0, .3, 18);
    setLight({ rim: EP.white, rimK: .6 });
    camBegin(W / 2 - sh[0], H / 2 - sh[1], 1);
    bgGrad([[0, '#FFD04A'], [1, '#FF6A1A']], { radial: true, cx: 960, cy: 500, r: 1100 });
    rays(960, 520, 24, 'rgb(255 255 255 / .16)', t * .4);
    gloss(pfRR(-60, 860, W + 120, 260, 0), '#8A2A10', { box: [0, 860, W, 260], lw: 5, rim: EP.yellow }); ctx.fillStyle = lg(0, 0, W, 0, [[0, EP.magenta], [.5, EP.cyan], [1, EP.magenta]]); ctx.fillRect(-60, 870, W + 120, 8);
    // DJ CLAWD, proud and blushing
    djClawd(380, 880, 30, { eyes: lt > hi ? 'heart' : 'happy', blush: clamp(lt / .8), mouth: 'grin', aL: .6 + Math.sin(t * 8) * .3, aR: .4, dy: -bounce(t) * .3 });
    // the jack-in-the-box
    const bx = 960, by = 900, bw = 300, bh = 200;
    giftBox(bx, by, bw, bh, EP.clawd, EP.magenta, { lid: false });
    if (open < 1 || lt < .6) { const a = lt; ctx.save(); ctx.translate(bx + a * 900, by - bh - 20 - a * 1400 + a * a * 2400); ctx.rotate(a * 9); gloss(pfRR(-bw / 2 - 16, -46, bw + 32, 46, 8), tint(EP.clawd, .1), { box: [-bw / 2 - 16, -46, bw + 32, 46], lw: 6 }); ctx.fillStyle = EP.magenta; ctx.fillRect(-bw * .08, -46, bw * .16, 46); ctx.restore(); }
    const spr = 1 - Math.exp(-lt * 4) * Math.cos(lt * 18), top = by - bh - 20 - 170 * spr, mu = 27;
    ctx.strokeStyle = '#C8CCD8'; ctx.lineWidth = 10; ctx.beginPath(); for (let i = 0; i <= 60; i++) { const u = i / 60, y = lerp(by - bh + 10, top, u); ctx.lineTo(bx + Math.sin(u * 7 * TAU) * 34, y); } ctx.stroke(); ctx.strokeStyle = EP.line; ctx.lineWidth = 3; ctx.stroke();
    const wave = lt > hi;
    djClawd(bx, top, mu, { phones: false, eyes: wave ? 'happy' : 'normal', blush: wave ? .8 : .3, mouth: wave ? 'smile' : 'o', aR: wave ? 1.1 + Math.sin(t * 16) * .35 : -.4, aL: -.6, legs: true });
    ctx.save(); ctx.translate(bx + 2.6 * mu, top - 3.4 * mu); ctx.rotate(-.12); gloss(pfEll(0, 0, 1.7 * mu, 1.15 * mu), EP.yellow, { box: [-1.7 * mu, -1.15 * mu, 3.4 * mu, 2.3 * mu], lw: 5 }); ptext('5.5', 0, 2, 1.25 * mu, { fill: EP.line }); ctx.restore();
    sayBubble([['HI, GUYS!', 84]], 1370, 330, { pop: pop(lt, hi, .15), to: [bx + 5 * mu, top - 6 * mu], rot: .05 });
    // feat. OPUS 5.5
    const fk = clamp((lt - b1) / .15);
    if (fk > 0) { const w = chromeText('OPUS 5.5', 1010, 160, 120, { style: 'hot', italic: .14, depth: 14, s: lerp(2, 1, easeOut(fk)), alpha: clamp(fk * 3) }); ptext('feat.', 1010 - w / 2 - 30, 172, 54, { align: 'right', fill: '#FFFFFF', strokes: [[EP.line, 10]], alpha: fk }); }
    // the second box, 90 minutes later
    if (lt > b5 - .5) {
      const k2 = clamp((lt - b5) / .1), spr2 = lt > b5 ? 1 - Math.exp(-(lt - b5) * 5) * Math.cos((lt - b5) * 18) : 0, x2 = 1640;
      giftBox(x2, by, 240, 180, CANDY.bondi, '#FFFFFF', { lid: k2 < 1 ? 0 : false, rot: lt < b5 ? Math.sin(t * 50) * .06 : 0 });
      if (lt > b5) { for (const [dx, lab] of [[-60, 'SOL'], [60, 'LUNA']]) gumdrop(x2 + dx * 1.2, by - 170 - 90 * spr2, 15, { col: CANDY.bondi, label: lab, face: 'happy', mouth: 'grin', hR: [4.4, -9 + Math.sin(t * 15 + dx) * .8], gR: 'wave', hL: [-4.3, -3.6] }); nameTip('GPT-6 · 90 MIN LATER', x2 - 40, 430, { pop: pop(lt, b5 + .1, .15), size: 28 }); }
    }
    confetti(t, t - lt, 80);
    camEnd();
    // the build into the last chorus
    if (lt > b6) { const k = (lt - b6) / (d - b6); laserFan(0, H, t, { n: 7, col: EP.magenta, angle: -1, spread: .8, alpha: k }); laserFan(W, H, t, { n: 7, col: EP.cyan, angle: -2.14, spread: .8, alpha: k, phase: 2 }); strobe(strobeK(t, 2, .3) * .35 * k); }
    if (lt < .08) fx({ flash: .6 * (1 - lt / .08) });
  });
})();

;
// ---- styles/eurodance/ch/c09_finale.js ----
// c09_finale — Chorus 4 (the cyberspace megarave; Windows 98 shuts down… and the screensaver trains on) and the outro (the drop, the curtain
// call, the 3D Pipes, the hype★TV end card). The take's own shape drives the cuts (beats counted from C4's first beat): C4 opens sparse with a
// hit on "scaling"; "But when we log off… will it still train on? And on, and on…" is a hi-hat build with no kick; THE DROP lands on beat 55 and
// is the loudest stretch of the song (the outro vocal rides it); the quiet outro starts on beat 87; the last hit is beat 102, then silence.
//   b0–5      "We didn't start the scaling": through a hex tunnel, the chrome words fly out at us as she sings; out into the megarave on "scaling"
//   b5–17     "It was always training, and the curves kept gaining": the stage's CRT wall flips to the video's own greatest hits (TRAINING DATA,
//             TIME REMAINING: ALWAYS); on "and the curves" the 3D Pipes burst out of it and the chorus kit's pipe staircase climbs a notch per
//             beat (×1.95, the steepest chorus yet) off the top of the frame
//   b17–20    "We didn't start the scaling": the trio and the whole cast on the checkerboard, confetti, the hook in chrome
//   b20–32.5  "Now we swear we'll try to pace it — but we'd rather race it!": the Scaling Laws dialog is back with [Yes] [Yes]; "pace" → slow
//             motion, the video wall drops to 70 BPM; the second Yes flips to RACE!, click → 200 BPM, triple speed, strobes
//   b32.5–40.5 "We didn't start the scaling": the trio jump… freeze-frame, ❚❚ PAUSE, the hook lands on the still; pull back: it's a Media Player
//             window on a Windows 98 PC
//   b40.5–    "But when we log off… will it still train on?": Start → Log Off SOFTMAX… → Shut Down… (Keep training?) → "It's now safe to turn
//             off your computer." → the CRT collapses to a dot, which won't die
//   "And on, and on, and on, and on": the CRT blinks back on by itself: the 3D Pipes, one more pipe on every "on"; we push into the screen
//   b55–59    THE DROP: the megarave, the title logo in chrome, fireworks, a crowd to the horizon
//   b59–63    the 90s tri-split: MC TOKEN / SOFTMAX / DJ CLAWD, each in their own tunnel
//   b63–67    the reverse angle: the trio from behind, facing an ocean of glowsticks
//   b67–75    "(And on, and on, and on…)": SOFTMAX on the speaker stack, then the trio on three stacks under the towering pipes
//   b75–79    everyone on stage; b79–83 one-beat close-ups (TOKEN, SOFTMAX, CLAWD, OPUS 5.5); b83–87 crane up over the megarave, white-out
//   b87–102   (the quiet outro) the 3D Pipes screensaver fills the screen, the gold staircase climbs once more,
//             the credit block returns
//   b102–end  the last hit: the hype★TV end card, UP NEXT… and the credits
// Colour run: magenta hex tunnel / violet megarave / ultramarine TRAINING wall → pipes / sunset-checker magenta / club cyan → pace blue → race red /
// "Blue" sky freeze / Win98 teal → shutdown black-orange → pipes black / drop violet / tri-split cyan-pink-orange / glowstick ocean / speaker-stack
// pink / everything / pipes black-gold / hype★TV end card.
(() => {
  const C = span('C4'), L = linesOf('C4');
  const B0 = Math.round(bpOf(C.start));
  const bt = k => onBeat(0, B0 + k);                        // song time of C4 beat k
  const half = x => onBeat(0, Math.round(bpOf(x) * 2) / 2);  // snap to the eighth-note grid (the chorus kit's snap8)
  const pop = (t, t0, dur = .18) => t < t0 ? 0 : backOut(clamp((t - t0) / dur), 2.2);
  const KW = typeof KARAOKE_WORDS !== 'undefined' ? KARAOKE_WORDS : [];
  // the start time of the n-th sung word w (normalised) in a line
  const wt = (ln, w, n = 0) => { const { words, tm } = _karaTimes(ln); let c = 0; for (let i = 0; i < words.length; i++) if (_kNorm(words[i]) === w && c++ === n) return tm[i][0]; return ln.start; };
  // "And on, and on, and on, and on" is sung after "…train on?" but isn't in the timeline's line, so this chapter draws its karaoke itself
  const tTrain = wt(L[5], 'train');
  const ON0 = KW.find(w => w[0] > tTrain && _kNorm(w[2]) === 'and')?.[0] ?? L[5].end - 3.4;
  const ONLN = { text: 'And on, and on, and on, and on', start: ON0, end: L[5].end, sec: 'C4' };
  const onTimes = [0, 1, 2, 3].map(i => wt(ONLN, 'on', i));
  // cuts
  const T1 = half(L[1].start), T2 = half(L[2].start), T3 = half(L[3].start), T4 = half(L[4].start);
  const TD = bt(55), TOUT = bt(87), TEND = bt(102);

  // ---------------------------------------------------------------------------------------------------------------------------
  // shared bits
  // ---------------------------------------------------------------------------------------------------------------------------
  function confetti(t, t0, n = 60, o = {}) {
    if (t < t0) return; const cols = o.cols ?? [EP.magenta, EP.cyan, EP.yellow, EP.lime, EP.white];
    for (let i = 0; i < n; i++) { const age = t - t0, x = (o.x0 ?? 0) + hash2(i, 1) * ((o.x1 ?? W) - (o.x0 ?? 0)) + Math.sin(age * 3 + i) * 30, y = (o.y0 ?? -60) - hash2(i, 2) * 300 + age * (260 + hash2(i, 3) * 200); if (y > H + 40) continue; const r = age * 6 + i; ctx.save(); ctx.translate(x, y); ctx.rotate(r); ctx.scale(1, Math.cos(r * 1.3)); ctx.fillStyle = cols[i % cols.length]; ctx.fillRect(-10, -6, 20, 12); ctx.restore(); }
  }
  const cloud = (x, y, s) => { ctx.save(); ctx.beginPath(); ctx.rect(x - s * 3, y - s * 3, s * 6, s * 3.35); ctx.clip(); for (const [dx, dy, r] of [[-1.25, .1, .6], [1.25, .12, .62], [-.5, -.25, .85], [.4, -.4, 1.0]]) glossBall(x + dx * s, y + dy * s, r * s, r * s * .92, '#E4EFFF', { line: false, rim: '#FFB0E8', rimK: .55, spec: .5 }); ctx.restore(); };
  // the hook in chrome: WE DIDN'T START / THE SCALING, each word slamming down on its own sung word (o.at: all at once)
  const HW = ["WE", "DIDN'T", "START", "THE", "SCALING"], HSTY = ['chrome', 'chrome', 'chrome', 'gold', 'hot'];
  function hookSlots(o = {}) {
    const s1 = o.s1 ?? 140, s2 = o.s2 ?? 196, y1 = o.y1 ?? 200, y2 = o.y2 ?? 372, g = o.gap ?? 38, cx = o.cx ?? W / 2;
    const w = HW.map((s, i) => textW(s, i < 3 ? s1 : s2, 'archivo')), out = [];
    let x = cx - (w[0] + w[1] + w[2] + g * 2) / 2; for (let i = 0; i < 3; i++) { out.push([x + w[i] / 2, y1, s1, w[i]]); x += w[i] + g; }
    x = cx - (w[3] + w[4] + g) / 2; for (let i = 3; i < 5; i++) { out.push([x + w[i] / 2, y2, s2, w[i]]); x += w[i] + g; }
    return out;
  }
  const hookWord = (i, x, y, size, s = 1, a = 1) => chromeText(HW[i], x, y, size, { style: HSTY[i], italic: .14, depth: i < 3 ? 14 : 20, s, alpha: a });
  function hook(t, ln, o = {}) {
    const tm = ln ? _karaTimes(ln).tm : null, S = hookSlots(o);
    S.forEach(([x, y, size], i) => { const t0 = o.at !== undefined ? o.at + (i < 3 ? 0 : .07) : half(tm[i][0]) - .03, k = clamp((t - t0) / .2); if (k <= 0) return; hookWord(i, x, y, size, i === 4 ? lerp(3, 1, backOut(k, 1.3)) : lerp(2.5, 1, easeOut(k)), clamp(k * 3) * (o.alpha ?? 1)); });
    const ts = o.at ?? half(tm[4][0]), a = S[3], b = S[4];
    if (o.glint === false) return;
    sweepGlint(a[0] - a[3] / 2, b[0] + b[3] / 2, b[1] - b[2] * .2, (t - ts - .2) / .6, 150);
    glint(b[0] + b[3] / 2 - 20, b[1] - b[2] * .45, 120 * kick(t, 4), kick(t, 4) * (t > ts ? 1 : 0));
  }
  // fireworks: a rocket, then a burst of streaks with gravity, fading over ~1.6 s
  const FWC = [EP.magenta, EP.cyan, EP.yellow, EP.laser, '#FF7A2A', '#B070FF', '#FFFFFF'];
  function firework(t, t0, x, y, col, seed, r = 230) {
    const a = t - t0; if (a < -.3 || a > 1.7) return;
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; ctx.lineCap = 'round';
    if (a < 0) { const ry = lerp(y + 520, y, easeOut(1 + a / .3)); ctx.strokeStyle = alpha('#FFE0A0', .8); ctx.lineWidth = 5; ctx.beginPath(); ctx.moveTo(x, ry + 90); ctx.lineTo(x, ry); ctx.stroke(); ctx.restore(); glow(x, ry, 40, '#FFD080', .9); return; }
    const k = easeOut(clamp(a / .55)), fade = 1 - clamp((a - .45) / 1.25), g = 150 * a * a;
    for (let i = 0; i < 36; i++) {
      const ang = i / 36 * TAU + hash2(seed, i) * .15, sp = r * (.7 + .4 * hash2(seed, i + 50)), c = i % 6 === 0 ? '#FFFFFF' : col, ca = Math.cos(ang), sa = Math.sin(ang);
      ctx.strokeStyle = alpha(c, .85 * fade); ctx.lineWidth = 5.5 - a * 2; ctx.beginPath(); ctx.moveTo(x + ca * sp * k * .76, y + sa * sp * k * .76 + g * .8); ctx.lineTo(x + ca * sp * k, y + sa * sp * k + g); ctx.stroke();
      if (a > .45 && hash2(seed + Math.floor(t * 24), i) < .3) { ctx.fillStyle = alpha('#FFFFFF', fade); ctx.fillRect(x + ca * sp * k - 3, y + sa * sp * k + g - 3, 6, 6); }
    }
    ctx.restore();
    if (a < .15) glow(x, y, r * 1.3, col, 1 - a / .15);
  }
  function fireworks(t, t0, o = {}) {
    const b = Math.floor(bpOf(t)), ev = o.every ?? 1;
    for (let k = b - 4; k <= b + 1; k++) { const tk = onBeat(0, k); if (tk < t0 || ((k % ev) + ev) % ev) continue; firework(t, tk, lerp(o.x0 ?? 220, o.x1 ?? 1700, hash2(k, 77)), lerp(o.y0 ?? 170, o.y1 ?? 420, hash2(k, 78)), FWC[((k % 7) + 7) % 7], k, o.r ?? 230); }
  }
  // Lawnmower-Man cyberspace: a void sky, a wireframe globe and polyhedra, a neon grid floor to the horizon
  function wireGlobe(x, y, r, t, col = EP.cyan, a = .5) {
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; ctx.strokeStyle = alpha(col, a); ctx.lineWidth = 3;
    for (let i = 0; i < 6; i++) { const rx = Math.abs(Math.cos(i / 6 * Math.PI + t * .35)) * r; ctx.beginPath(); ctx.ellipse(x, y, Math.max(1, rx), r, 0, 0, TAU); ctx.stroke(); }
    for (let j = -2; j <= 2; j++) { const ph = j / 3 * Math.PI / 2, rx = Math.cos(ph) * r; ctx.beginPath(); ctx.ellipse(x, y + Math.sin(ph) * r, rx, rx * .16, 0, 0, TAU); ctx.stroke(); }
    ctx.restore(); glow(x, y, r * 1.4, col, .16);
  }
  function gridFloor(t, hz, o = {}) {
    const col = o.col ?? EP.magenta, sp = o.speed ?? 1.2;
    ctx.save(); ctx.beginPath(); ctx.rect(-900, hz, W + 1800, H + 900); ctx.clip();
    ctx.fillStyle = lg(0, hz, 0, H, [[0, o.far ?? '#2A0848'], [1, o.near ?? '#07010F']]); ctx.fillRect(-900, hz, W + 1800, H + 900);
    ctx.globalCompositeOperation = 'lighter'; ctx.strokeStyle = alpha(col, .55); ctx.lineWidth = 3; ctx.beginPath();
    for (let i = -30; i <= 30; i++) { ctx.moveTo(W / 2 + i * 46, hz); ctx.lineTo(W / 2 + i * 400, H + 500); }
    for (let j = 0; j < 18; j++) { const z = j + 1 - frac(t * sp), y = hz + 640 / (z * 1.05 + .25) - 640 / (18 * 1.05 + .25); if (y > H + 30) continue; ctx.moveTo(-900, y); ctx.lineTo(W + 900, y); }
    ctx.stroke(); ctx.restore();
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; ctx.fillStyle = lg(0, hz - 40, 0, hz + 50, [[0, alpha(col, 0)], [.5, alpha(col, .55)], [1, alpha(col, 0)]]); ctx.fillRect(-900, hz - 40, W + 1800, 90); ctx.restore();
  }
  // tq: a clock that jumps a notch on every beat since t0 (the curve climbs on the beat)
  const tq = (t, t0) => { const q = (t - t0) / beatLen(); return t0 + (Math.floor(q) + easeOut(clamp(frac(q) / .4))) * beatLen(); };
  // pipeRun / pipeStair: the chorus kit's "curve" (from c03_chorus1.js): a length of 3D Pipes pipe along a right-angled polyline, and an
  // exponential staircase of it climbing one notch per beat from t0 (C1 grew ×1.5 a notch, C2's swell ×1.6; the finale's is steeper still).
  // This copy adds o.glow: a neon halo and a dark outline under the pipe.
  function pipeRun(pts, k, col, w) {
    let total = 0; const Ls = []; for (let i = 1; i < pts.length; i++) { const d = Math.hypot(pts[i][0] - pts[i - 1][0], pts[i][1] - pts[i - 1][1]); Ls.push(d); total += d; }
    let left = total * clamp(k), tip = pts[0];
    ctx.save(); ctx.lineCap = 'butt';
    for (let i = 1; i < pts.length && left > 0; i++) {
      const [ax, ay] = pts[i - 1], u = Math.min(1, left / Ls[i - 1]), bx = ax + (pts[i][0] - ax) * u, by = ay + (pts[i][1] - ay) * u; left -= Ls[i - 1];
      const ang = Math.atan2(by - ay, bx - ax), nx = -Math.sin(ang) * w, ny = Math.cos(ang) * w;
      ctx.fillStyle = lg(ax + nx, ay + ny, ax - nx, ay - ny, [[0, shade(col, .55)], [.3, col], [.45, tint(col, .6)], [.6, col], [1, shade(col, .6)]]);
      ctx.beginPath(); ctx.moveTo(ax + nx, ay + ny); ctx.lineTo(bx + nx, by + ny); ctx.lineTo(bx - nx, by - ny); ctx.lineTo(ax - nx, ay - ny); ctx.closePath(); ctx.fill();
      if (i > 1) glossBall(ax, ay, w * 1.3, w * 1.3, col, { line: false, rim: null });
      tip = [bx, by];
    }
    ctx.restore();
    return tip;
  }
  function pipeStair(t, t0, o = {}) {
    const n = o.n ?? 10, dx = o.dx ?? 150, g = o.growth ?? 1.5, pts = [[o.x0 ?? 200, o.y0 ?? 860]];
    let h = o.h0 ?? 36;
    for (let i = 0; i < n; i++) { const [x, y] = pts.at(-1); pts.push([x + dx, y], [x + dx, y - h]); h *= g; }
    const bq = (t - t0) / beatLen(), notch = Math.floor(bq), fr = clamp(frac(bq) / (o.grow ?? .45));
    if (bq < 0) return pts[0];
    const segs = Math.min(n * 2, notch * 2 + easeOut(fr) * 2), sub = pts.slice(0, Math.floor(segs) + 2);
    const whole = Math.floor(segs), part = segs - whole; if (whole + 1 < sub.length) { const [ax, ay] = sub[whole], [bx, by] = sub[whole + 1]; sub[whole + 1] = [ax + (bx - ax) * part, ay + (by - ay) * part]; }
    if (o.glow) {
      const path = () => { ctx.beginPath(); sub.forEach(([x, y], i) => i ? ctx.lineTo(x, y) : ctx.moveTo(x, y)); };
      ctx.save(); ctx.globalCompositeOperation = 'lighter'; ctx.strokeStyle = alpha(o.glow, .25); ctx.lineWidth = (o.w ?? 22) * 4.2; ctx.lineJoin = 'round'; ctx.lineCap = 'round'; path(); ctx.stroke(); ctx.restore();
      ctx.strokeStyle = EP.line; ctx.lineWidth = (o.w ?? 22) * 2.4; ctx.lineJoin = 'round'; path(); ctx.stroke();
    }
    return pipeRun(sub, 1, o.col ?? '#E8342A', o.w ?? 22);
  }
  // n screensaver pipes growing at once (the kit's pipes() starts its n pipes one after another), each in its own colour
  const PCOL = ['#E8342A', '#2A9AE8', '#E8C42A', '#2AE85A', '#C42AE8', '#E8E8E8', '#E87A2A'];
  function pipeSet(t, t0, n, o = {}) { const sd = o.seed ?? 1; for (let i = 0; i < n; i++) pipes(t, t0, { bg: false, maxLen: 400, ...o, n: 1, seed: sd * 31 + i * 7, cols: [PCOL[(i + sd) % PCOL.length]] }); }
  function megarave(t, o = {}) {
    const hz = o.hz ?? 600;
    bgGrad([[0, '#03000C'], [.45, '#140340'], [.8, '#4A1084'], [1, '#FF3FB0']], { y1: hz });
    for (let i = 0; i < 70; i++) { const tw = .3 + .7 * Math.abs(Math.sin(t * (1 + hash2(i, 3) * 3) + i)); ctx.fillStyle = `rgb(255 255 255 / ${.6 * tw * hash2(i, 4)})`; ctx.fillRect(hash2(i, 1) * W, hash2(i, 2) * (hz - 80), 3, 3); }
    if (o.globe !== false) wireGlobe(o.gx ?? W / 2, o.gy ?? hz - 190, o.gr ?? 250, t, EP.cyan, .45);
    spin3D('octa', 210, 300 + Math.sin(t * 1.3) * 20, 70, [t * 1.2, t * .8, .3], { mode: 'wire', wire: EP.laser, lw: 3 });
    spin3D('cube', 1710, 360 + Math.sin(t * 1.1) * 20, 58, [t * .9 + 1, t * 1.4, .2], { mode: 'wire', wire: EP.magenta, lw: 3 });
    spin3D('pyramid', 470, 150 + Math.sin(t * 1.7) * 14, 42, [t * .7, t * 1.9, .4], { mode: 'wire', wire: EP.yellow, lw: 3 });
    spin3D('diamond', 1460, 200 + Math.sin(t * 1.5) * 14, 46, [.3, t * 1.6, .1], { mode: 'wire', wire: EP.cyan, lw: 3 });
    if (o.pipes) { const P = o.pipes; pipeSet(tq(t, P.t0), P.t0, P.n ?? 5, { seed: P.seed ?? 21, cx: P.cx ?? W / 2, cy: P.cy ?? hz - 230, scale: P.scale ?? 46, rate: P.rate ?? 3 }); }
    if (o.fw !== undefined) fireworks(t, o.fw, { y1: Math.min(420, hz - 120) });
    for (const [x, c, ph] of [[W / 2 - 560, EP.cyan, 0], [W / 2 + 560, EP.magenta, 2], [W / 2, EP.laser, 1]]) laserFan(x, hz, t, { n: 7, col: c, angle: -Math.PI / 2, spread: 1.5, sweep: .45, phase: ph, alpha: .45 * (o.lasers ?? 1) });
    gridFloor(t, hz, { col: o.floorCol ?? EP.magenta });
    if (o.crowd !== false) {
      raveCrowd(t, { y: hz + 38, s: .3, rows: 3, n: 40, k: 1, hands: .6, rim: EP.cyan, col: '#1C0A3E', seed: 31, sticks: .6 });
      raveCrowd(t, { y: hz + 150, s: .55, rows: 2, n: 24, k: 1, hands: .6, rim: EP.magenta, col: '#120628', seed: 32 });
    }
  }
  // the floating chrome stage disc with chaser lights round its rim
  function stageDisc(t, y, rx = 700) {
    ctx.fillStyle = 'rgb(0 0 20 / .45)'; ell(W / 2, y + 60, rx * 1.02, 60); ctx.fill();
    gloss(() => { ctx.moveTo(W / 2 - rx, y); ctx.ellipse(W / 2, y, rx, 64, 0, Math.PI, 0, true); ctx.lineTo(W / 2 + rx, y + 36); ctx.ellipse(W / 2, y + 36, rx, 64, 0, 0, Math.PI); ctx.closePath(); }, '#B8C0D8', { box: [W / 2 - rx, y - 64, rx * 2, 164], rim: EP.cyan, lw: 5, spec: .9 });
    ell(W / 2, y, rx, 64); ctx.fillStyle = lg(W / 2 - rx, 0, W / 2 + rx, 0, [[0, '#4A3A7A'], [.5, '#D8D0FF'], [1, '#4A3A7A']]); ctx.fill(); ctx.strokeStyle = EP.line; ctx.lineWidth = 4; ctx.stroke();
    for (let i = 0; i < 26; i++) { const a = i / 26 * TAU + t * .9; if (Math.sin(a) < 0) continue; const on = (i + beatN(t)) % 3 === 0; ctx.fillStyle = on ? '#FFFFFF' : [EP.magenta, EP.cyan, EP.yellow][i % 3]; ell(W / 2 + Math.cos(a) * rx, y + 18 + Math.sin(a) * 64, on ? 14 : 10, on ? 9 : 6); ctx.fill(); if (on) glow(W / 2 + Math.cos(a) * rx, y + 18 + Math.sin(a) * 64, 40, EP.white, .5); }
  }
  // the trio on the stage: MC TOKEN (left), DJ CLAWD at the decks (centre), SOFTMAX (right)
  function trio(t, y, o = {}) {
    const bb = bpOf(t), s = o.s ?? 34, dx = o.dx ?? 380, by = y - s * 3.4, bw = s * 9;
    djClawd(W / 2, by + bw * .1, s * .5, { shades: true, aL: .9 + Math.sin(bb * Math.PI) * .4, aR: .5 - Math.sin(bb * Math.PI) * .35, mouth: 'grin', dy: -bounce(t) * .3 });
    djBooth(W / 2, by, bw, t, { scratch: kick(t, 10) * .6 });
    toy(W / 2 - dx, y, s, { ...CAST.token.o, ...dance(o.tm ?? 'runningMan', bb), mouth: 'grin' });
    toy(W / 2 + dx, y + 8, s * 1.06, { ...CAST.softmax.o, ...dance(o.sm ?? 'sing', bb - .25), talk: singK(t) });
  }
  const opus = (x, y, u, o = {}) => djClawd(x, y, u, { label: '5.5', phones: false, eyes: 'happy', mouth: 'grin', blush: .6, ...o });

  // other chapters' shots, painted once each into a small cached tile (for the TRAINING DATA wall); overlay switches they set are discarded
  function paintShot(key, p) {
    const s = segByKey(key), fn = s && SHOTS[key]; if (!fn) return false;
    const d = s.end - s.start, tt = s.start + p * d, saved = [T, _boil, _jitN, _noCaption, _noStamp, _captionStyle, _fxO, _cutO, _noBug, _bloom, LIGHT], depth = _camDepth;
    T = tt; _boil = boilFrame(tt); ctx.save(); let ok = true;
    try { fn(p, p * d, d, tt, s); } catch (e) { ok = false; }
    finally { while (_camDepth > depth) camEnd(); ctx.restore(); [T, _boil, _jitN, _noCaption, _noStamp, _captionStyle, _fxO, _cutO, _noBug, _bloom, LIGHT] = saved; }
    return ok;
  }
  function fallbackTile(key) {
    const s = segByKey(key);
    bgGrad([[0, '#2A0A6A'], [1, '#8A1FB8']]); rays(W / 2, H / 2, 20, 'rgb(255 255 255 / .07)', hstr(key));
    ptext(String(s?.text ?? key), W / 2, H / 2 - 40, 110, { fill: '#FFFFFF', strokes: [[EP.line, 18]], maxW: W - 200 });
    if (s?.date) pixText(s.date, W / 2, H / 2 + 80, 14, EP.yellow, { align: 'center', glow: true });
  }
  const RECAP = ['V1.1', 'V2.1', 'V1.5', 'V2.6', 'V3.2', 'V1.8', 'V3.8', 'V2.12', 'V1.12', 'V4.3', 'V3.15', 'V4.16'];
  const recapTile = key => cached('c09|tile|' + key, 384, 216, (w, h) => { ctx.save(); ctx.beginPath(); ctx.rect(0, 0, w, h); ctx.clip(); ctx.scale(w / W, h / H); if (!paintShot(key, .72)) fallbackTile(key); ctx.restore(); });

  // ===========================================================================================================================
  // b0–5 "We didn't start the scaling": the tunnel fly-in, then out into the megarave on "scaling"
  // ===========================================================================================================================
  function flyIn(t) {
    hideCaption();
    const tm = _karaTimes(L[0]).tm, tS = tm[4][0], S = hookSlots();
    if (t < tS) {
      const u = t - C.start, tw = 3 * u + 2.6 * u * u;
      tunnel(tw, { speed: 1, cols: [EP.magenta, EP.cyan, EP.uv, EP.yellow], shape: 'hex', width: 80, twist: .1, bg: '#05010E', glow: EP.magenta, spin: .25 });
      laserFan(0, H / 2, t, { n: 6, col: EP.cyan, angle: 0, spread: .9, sweep: .3, alpha: .35 }); laserFan(W, H / 2, t, { n: 6, col: EP.magenta, angle: Math.PI, spread: .9, sweep: .3, phase: 2, alpha: .35 });
      for (let i = 0; i < 4; i++) { const k = clamp((t - (tm[i][0] - .05)) / .3); if (k <= 0) continue; const e = easeOut(k), [x, y, s] = S[i]; hookWord(i, lerp(W / 2, x, e), lerp(H / 2, y, e), s, lerp(.06, 1, e) * (1 + .5 * Math.sin(e * Math.PI)), clamp(k * 4)); }
      const ex = clamp((t - (tS - .5)) / .5); if (ex > 0) glow(W / 2, H / 2, 150 + ex * 1500, '#FFFFFF', ex);
      return;
    }
    const a = t - tS, sh = a < .3 ? shakeXY(t, 16 * (1 - a / .3)) : [0, 0];
    setLight({ rim: EP.cyan, rimK: .8 });
    camBegin(W / 2 + sh[0], 560 + sh[1], lerp(1.08, 1, easeOut(clamp(a / .6))));
    megarave(t, { hz: 600, fw: bt(4) - .05 });
    stageDisc(t, 820); trio(t, 830, { sm: 'raise', tm: 'pump' });
    camEnd();
    raveCrowd(t, { y: 1070, s: 1.35, rows: 2, n: 11, hands: .95, rim: EP.magenta, seed: 5 });
    hook(t, L[0]);
    if (a < .18) strobe(1 - a / .18);
    if (a < .1) fx({ rgb: 1 - a / .1 });
  }

  // ===========================================================================================================================
  // b5–17 "It was always training, and the curves kept gaining": the TRAINING DATA wall, then the 3D Pipes take over
  // ===========================================================================================================================
  function training(t) {
    const tC = half(wt(L[1], 'and')), u = (t - T1) / (T2 - T1), bb = bpOf(t);
    setLight({ rim: EP.cyan, rimK: .8 });
    camBegin(W / 2, 540, 1 + .04 * ease(u));
    megarave(t, { hz: 640, globe: false, crowd: true });
    // the video wall of CRTs: the video's own greatest hits, rippling on
    const cols = 4, rows = 3, cw = 290, ch = 163, g = 12, x0 = W / 2 - (cols * (cw + g) - g) / 2, y0 = 214;
    ctx.fillStyle = 'rgb(0 0 10 / .6)'; rrect(x0 - 26, y0 - 88, cols * (cw + g) - g + 52, rows * (ch + g) - g + 114, 20); ctx.fill();
    videoWall(x0, y0, cols, rows, cw, ch, (i, j, w, h) => {
      const n = j * cols + i, tk = T1 + (n * 7 % 12) * beatLen() / 3;
      if (t < tk) { bgGrad([[0, (i + j) % 2 ? EP.uv : EP.ultra], [1, EP.night]], { y1: h }); ptext('hype', w / 2, h / 2, h * .3, { font: 'rammetto', fill: alpha(EP.white, .6) }); return; }
      ctx.drawImage(recapTile(RECAP[n]), 0, 0, w, h);
      const a = t - tk; if (a < .14) { ctx.fillStyle = `rgb(255 255 255 / ${1 - a / .14})`; ctx.fillRect(0, 0, w, h); }
    }, { gap: g, frame: '#22203A' });
    // the LED strip under the wall
    const sx = x0, sw = cols * (cw + g) - g, sy = y0 - 62;
    rrect(sx, sy, sw, 50, 8); paint('#05050A', '#3A3A48', 2);
    ctx.save(); rrect(sx, sy, sw, 50, 8); ctx.clip(); const lab = 'TRAINING DATA * 2017 - 2026 * TIME REMAINING: ALWAYS * ', px = 5, tw = pixW(lab, px) + px * 6, off = (t * 240) % tw; for (let q = -1; q < 3; q++) pixText(lab, sx + sw - off + q * tw - sw, sy + 8, px, EP.amber, { glow: true }); ctx.restore();
    // "…and the curves kept gaining": the pipes burst out of the wall, a notch per beat, zooming up to fill the frame
    const pk = clamp((t - tC) / (T2 - tC));
    if (t > tC) pipeSet(tq(t, tC), tC, 6, { seed: 7, cx: W / 2, cy: 400, scale: lerp(40, 150, easeIn(pk)), rate: 9 });
    stageDisc(t, 900, 760);
    trio(t, 915, { s: 30, dx: 470, tm: 'runningMan', sm: t < tC ? 'sing' : 'raise' });
    // the curve: the chorus staircase, steepest yet (×1.95 a notch), climbing off the top of the frame
    if (t > tC) { const tip = pipeStair(t, tC, { x0: 120, y0: 900, dx: 160, h0: 24, growth: 1.95, n: 9, col: '#FFC83A', w: 30, glow: EP.yellow }); glint(tip[0], tip[1], 150 * (.6 + .4 * kick(t, 5)), .9); }
    camEnd();
    raveCrowd(t, { y: 1090, s: 1.3, rows: 1, n: 11, hands: .6 + pk * .4, rim: EP.cyan, seed: 6 });
    if (t > tC && t < tC + .1) fx({ flash: .5 * (1 - (t - tC) / .1) });
  }

  // ===========================================================================================================================
  // b17–20 "We didn't start the scaling": the trio and the whole cast on the checkerboard, confetti, the hook
  // ===========================================================================================================================
  const PEOPLE = ['sam', 'demis', 'dario', 'jensen', 'zuck', 'karpathy', 'ilya', 'hinton', 'eliezer', 'gwern', 'elon', 'yann'];
  const MOVES = ['bounce', 'raise', 'pump', 'clap', 'wave', 'point', 'runningMan', 'robot'];
  const MODELS = [['CHATGPT', CANDY.bondi, 'happy'], ['CLAUDE', CANDY.tangerine, 'star'], ['GEMINI', CANDY.blueberry, 'happy'], ['GROK', CANDY.graphite, 'wink'], ['DEEPSEEK', CANDY.ocean, 'happy'], ['LLAMA', CANDY.lime, 'star'], ['SORA', CANDY.grape, 'heart'], ['SYDNEY', CANDY.strawberry, 'heart'], ['MYTHOS', CANDY.graphite, 'sly']];
  function modelsRow(t, y, s, x0, x1, o = {}) {
    const bb = bpOf(t);
    MODELS.forEach(([lab, col, face], i) => { const b = bb - i * .17, up = Math.floor(b + i) % 2, x = lerp(x0, x1, i / (MODELS.length - 1)); gumdrop(x, y, s, { col, label: lab, face, mouth: 'grin', jump: Math.abs(Math.sin(b * Math.PI)) * .7, hL: up ? [-3.8, -9.2] : [-4.6, -5.2], hR: up ? [4.6, -5.2] : [3.8, -9.2], gL: up ? 'wave' : 'open', gR: up ? 'open' : 'wave', rot: Math.sin(b * Math.PI) * .05, ...o }); });
  }
  // Gwern after V3.16: hood down, shades off, a halo (the reveal's look)
  const GWERN_OUT = { top: 'hoodie', topCol: '#3A3A56', skin: 0, hair: 'messy', hairCol: THAIR.brown, hat: 'halo', hatCol: EP.gold };
  function peopleRow(t, y, s, x0, x1, list = PEOPLE) {
    const bb = bpOf(t);
    list.forEach((k, i) => { const x = lerp(x0, x1, i / (list.length - 1)); toy(x, y + (i % 2) * 14, s, { ...(k === 'gwern' ? GWERN_OUT : WHO[k].o), ...dance(MOVES[i % MOVES.length], bb - i * .13), mouth: 'grin', eyes: i % 3 ? 'happy' : 'dot' }); });
  }
  function castLineup(t) {
    hideCaption();
    const bb = bpOf(t), u = (t - T2) / (T3 - T2);
    setLight({ rim: EP.magenta, rimK: .75 });
    camBegin(W / 2, 540, 1.03 - .03 * u);
    bgGrad([[0, '#05052A'], [.55, '#3A1A9A'], [1, '#FF4FA8']], { y1: 620 });
    glow(W / 2, 620, 800, '#FF6FC8', .5); rays(W / 2, 620, 22, 'rgb(255 255 255 / .05)', t * .2);
    checkerFloor(t, { horizon: 620, a: '#F2F0FF', b: '#2A1466', speed: 1.1, fog: '#FF6FC8', fogH: 110 });
    glossBall(150, 520 + Math.sin(t * 1.3) * 16, 60, 60, '#D8DEEA', { rim: EP.magenta, rimK: .8 });
    spin3D('torus', 1790, 520 + Math.sin(t * 1.1) * 14, 70, [t * 1.3 + .6, t * .9, .35], { mode: 'chrome' });
    modelsRow(t, 690, 11.5, 250, 1670, { shadow: true });
    peopleRow(t, 815, 16.5, 150, 1770);
    toy(560, 1010, 31, { ...CAST.token.o, ...dance('runningMan', bb), mouth: 'grin' });
    djClawd(1360, 1000, 19, { shades: true, aL: 1.1 + Math.sin(bb * Math.PI) * .3, aR: 1.1 - Math.sin(bb * Math.PI) * .3, mouth: 'grin', jump: bounce(t) * .8 });
    opus(1640, 1010, 9, { aL: .9, aR: 1.3 + Math.sin(bb * Math.PI * 2) * .3, jump: bounce(t) * 1.2 });
    toy(960, 1015, 34, { ...CAST.softmax.o, ...dance('raise', bb), talk: singK(t) });
    camEnd();
    confetti(t, T2 - .15, 90);
    hook(t, L[2], { s1: 110, s2: 160, y1: 200, y2: 336 });
    if (t < T2 + .12) strobe(.8 * (1 - (t - T2) / .12));
  }

  // ===========================================================================================================================
  // b20–32.5 "Now we swear we'll try to pace it — but we'd rather race it!": [Yes] [Yes] → slow motion → RACE! → triple speed
  // ===========================================================================================================================
  const tSw = wt(L[3], 'swear'), tP = wt(L[3], 'pace'), tRa = wt(L[3], 'rather'), tR = wt(L[3], 'race');
  const warp = t => t < tP ? t : t < tR ? tP + (t - tP) * .5 : tP + (tR - tP) * .5 + (t - tR) * 3;
  const bpmAt = t => t < tP ? 141 : t < tR ? Math.round(lerp(141, 70, easeOut(clamp((t - tP) / .45)))) : Math.round(lerp(70, 200, clamp((t - tR) / .14)));
  function bpmWall(t, w, h) {
    const m = t < tP ? 0 : t < tR ? 1 : 2, col = [EP.magenta, EP.cyan, '#FF3A2A'][m];
    if (m === 2) { ctx.fillStyle = '#1A0000'; ctx.fillRect(0, 0, w, h); const sq = 64, off = (t * 900) % (sq * 2); for (let j = 0; j < h / sq + 1; j++) for (let i = -2; i < w / sq + 2; i++) if ((i + j) % 2 === 0) { ctx.fillStyle = 'rgb(255 255 255 / .16)'; ctx.fillRect(i * sq + off - sq * 2, j * sq, sq, sq); } }
    else bgGrad([[0, ['#2A0A5A', '#001A6A'][m]], [1, '#05010E']], { y1: h });
    const bx = w * .6, bw = w * .36;
    ctx.fillStyle = 'rgb(0 0 0 / .6)'; rrect(bx, h * .08, bw, h * .84, 18); ctx.fill(); ctx.strokeStyle = col; ctx.lineWidth = 4; ctx.stroke();
    pixText('BPM', bx + bw / 2, h * .14, 8, col, { align: 'center', glow: true });
    const v = bpmAt(t), flash = m === 2 && frac(t * 7) < .5;
    segText(String(v).padStart(3, ' '), bx + bw / 2, h * .3, h * .38, flash ? '#FFFFFF' : col, { off: alpha(col, .12), align: 'center' });
    pixText(['NORMAL', 'PACE', 'RACE!'][m], bx + bw / 2, h * .76, 7, m === 2 ? EP.yellow : EP.white, { align: 'center', glow: true });
  }
  function checkerFlag(s) {
    ctx.save(); ctx.strokeStyle = '#C8CCD8'; ctx.lineWidth = s * .14; ctx.beginPath(); ctx.moveTo(0, 0); ctx.lineTo(0, -s * 4.4); ctx.stroke();
    const fw = s * 2.6, fh = s * 1.7, n = 6, m = 4, wv = T * 14;
    for (let j = 0; j < m; j++) for (let i = 0; i < n; i++) { const x = i * fw / n, y = -s * 4.3 + j * fh / m + Math.sin(i * .9 + wv) * s * .16 * (i / n); ctx.fillStyle = (i + j) % 2 ? '#111' : '#FFF'; ctx.fillRect(x, y, fw / n + 1, fh / m + 1); }
    ctx.strokeStyle = '#111'; ctx.lineWidth = 2; ctx.strokeRect(0, -s * 4.3, fw, fh); ctx.restore();
  }
  function speedLines(t, a = 1) {
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; ctx.lineCap = 'round';
    for (let i = 0; i < 46; i++) { const ang = hash2(i, 5) * TAU, r0 = 220 + frac(hash2(i, 6) + t * 3.5) * 1300, L2 = 120 + hash2(i, 7) * 260; ctx.strokeStyle = `rgb(255 ${200 + hash2(i, 8) * 55 | 0} 200 / ${.5 * a})`; ctx.lineWidth = 3 + hash2(i, 9) * 5; ctx.beginPath(); ctx.moveTo(W / 2 + Math.cos(ang) * r0, 560 + Math.sin(ang) * r0); ctx.lineTo(W / 2 + Math.cos(ang) * (r0 + L2), 560 + Math.sin(ang) * (r0 + L2)); ctx.stroke(); }
    ctx.restore();
  }
  function paceRace(t) {
    const tw = warp(t), m = t < tP ? 0 : t < tR ? 1 : 2, bw = bpOf(tw), hue = [EP.magenta, EP.blue, EP.red][m];
    const sh = m === 2 && t - tR < .4 ? shakeXY(t, 18 * (1 - (t - tR) / .4)) : m === 2 ? shakeXY(t, 4) : [0, 0];
    setLight({ rim: m === 1 ? EP.cyan : m === 2 ? EP.orange : EP.magenta, rimK: .8 });
    camBegin(W / 2 + sh[0], 540 + sh[1], 1 + (m === 2 ? .03 : 0));
    stageSet(tw, { level: 3, hue, lasers: 3, wall: (w, h) => bpmWall(t, w, h) });
    // the trio (in slow motion, with a ghost trail)
    const who = (tt, a) => {
      const b = bpOf(tt); ctx.save(); ctx.globalAlpha *= a;
      djClawd(560, 800, 15, { shades: true, aL: .9 + Math.sin(b * Math.PI) * .45, aR: .4 - Math.sin(b * Math.PI) * .3, mouth: m === 2 ? 'open' : 'grin', dy: -bounce(tt) * .3 }); djBooth(560, 770, 300, tt, { scratch: kick(tt, 10) * .7 });
      toy(1060, 950, 30, { ...CAST.token.o, ...dance(m === 2 ? 'shuffle' : 'runningMan', b), mouth: m === 2 ? 'scream' : 'grin', swing: Math.sin(b * Math.PI) * .22, ...(m === 2 ? { hR: [2.4, -9.6], gR: 'fist', hold: checkerFlag } : {}) });
      const oath = t > tSw - .05 && t < tP - .1;
      toy(1430, 955, 32, { ...CAST.softmax.o, ...dance(m === 2 ? 'jump' : 'sing', b - .25), ...(oath ? { hR: [2.4, -10.2], gR: 'flat', hL: [-.6, -5.6], gL: 'open', headTilt: -.05, lean: 0, jump: 0 } : {}), talk: singK(t), swing: Math.sin(b * Math.PI) * .3 });
      ctx.restore();
    };
    if (m === 1) who(warp(t - .22), .3);
    who(tw, 1);
    raveCrowd(tw, { y: 1095, s: 1.25, rows: 1, n: 10, hands: m === 2 ? 1 : .6, rim: hue, seed: 8 });
    camEnd();
    if (m === 1) { ctx.fillStyle = 'rgb(20 60 255 / .14)'; ctx.fillRect(0, 0, W, H); if (frac(t * 1.5) < .7) pixText('SLOW-MO', 1840, 170, 6, '#FFFFFF', { align: 'right', edge: '#000' }); }
    if (m === 2) { speedLines(t, 1); strobe(strobeK(tw, 2, .25) * .3); if (t - tR < .16) fx({ rgb: 1 - (t - tR) / .16, zoom: .6 * (1 - (t - tR) / .16) }); }
    // the dialog (the Scaling Laws window from V1.2, back with [Yes] [Yes])
    const gone = clamp((t - tR - .05) / .3); if (gone >= 1) return;
    const DX = 110, DY = 150, DWd = 740, DH = 420, k = clamp((t - T3) / .14);
    ctx.save(); ctx.translate(DX + DWd / 2 - easeIn(gone) * 1500, DY + DH / 2 - easeIn(gone) * 200); ctx.rotate(-gone * .6); ctx.translate(-(DX + DWd / 2), -(DY + DH / 2));
    win98Window(DX, DY, DWd, DH, 'Scaling Laws', (cw, chh) => {
      icon98('question', 66, 76, 1.2);
      txt('Pace it?', 140, 74, 64, '#000', { font: 'archivo', align: 'left' });
      const ck = t > tSw; bevel(142, 140, 40, 40, { sunken: true, fill: '#FFFFFF' });
      if (ck) { ctx.strokeStyle = '#000'; ctx.lineWidth = 6; ctx.lineCap = 'round'; ctx.beginPath(); ctx.moveTo(150, 160); ctx.lineTo(160, 172); ctx.lineTo(176, 146); ctx.stroke(); }
      txt('We swear we\'ll try', 196, 161, 32, '#000', { font: 'archivo', align: 'left' });
      txt('Kaplan et al., OpenAI · Jan 2020', 30, chh - 24, 20, '#505050', { font: 'archivo', align: 'left' });
    }, { icon: 'exe', k, client: EP.w98 });
    if (k >= 1) {
      const by = DY + DH - 150, bwid = 240, bh = 78, y1x = DX + 110, y2x = DX + 390;
      const p1 = t > tP && t < tP + .18, p2 = t > tR && t < tR + .2;
      win98Button('Yes', y1x, by, bwid, bh, { def: t < tP + .2, focus: t < tP + .2, pressed: p1, size: 38 });
      const fl = clamp((t - tRa) / .18), sx = Math.abs(Math.cos(fl * Math.PI)) || .02, race = fl >= .5;
      ctx.save(); ctx.translate(y2x + bwid / 2, by + bh / 2); ctx.scale(sx * (race ? 1 + kick(t, 6) * .08 : 1), race ? 1 + kick(t, 6) * .08 : 1); ctx.translate(-(y2x + bwid / 2), -(by + bh / 2));
      if (race) { ctx.fillStyle = EP.red; ctx.fillRect(y2x - 6, by - 6, bwid + 12, bh + 12); }
      win98Button(race ? '' : 'Yes', y2x, by, bwid, bh, { pressed: p2, def: race, focus: race, size: 38 });
      if (race) txt('RACE!', y2x + bwid / 2 + (p2 ? 3 : 0), by + bh / 2 + 3 + (p2 ? 3 : 0), 40, EP.red, { font: 'archivo' });
      ctx.restore();
      // the cursor: to the first Yes for "pace", then over to RACE! for "race"
      const c0 = [900, 760], cY1 = [y1x + 150, by + 50], cY2 = [y2x + 140, by + 52];
      const cp = kf(t, [[T3 + .1, c0], [tP - .08, cY1], [tRa + .1, cY1], [tR - .06, cY2]], easeOut);
      cursor98(cp[0], cp[1], { click: t > tP && t < tP + .3 ? (t - tP) / .3 : t > tR && t < tR + .3 ? (t - tR) / .3 : 0 });
    }
    ctx.restore();
  }

  // ===========================================================================================================================
  // b32.5–40.5 "We didn't start the scaling": the jump, the freeze-frame (PAUSE), the pull back to the PC
  // ===========================================================================================================================
  const tF = bt(33), tPB = bt(37), tPB1 = bt(39);          // freeze on the beat after "We"; pull back after "scaling"
  function jumpScene(tt, jk) {
    setLight({ rim: EP.magenta, rimK: .8 });
    bgGrad([[0, '#02024A'], [.5, EP.ultra], [1, '#49B6FF']], { y1: 800 });
    rays(W / 2, 540, 18, 'rgb(255 255 255 / .07)', tt * .15);
    for (let i = 0; i < 5; i++) cloud(frac(hash(i + 20) + tt * .02) * (W + 900) - 450, 200 + hash(i + 29) * 340, 60 + hash(i + 23) * 60);
    checkerFloor(tt, { horizon: 790, a: '#E8F0FF', b: '#1633C8', speed: .7, fog: '#7AB8FF', fogH: 90 });
    laserFan(260, 1080, tt, { n: 8, col: EP.magenta, angle: -1.1, spread: .9, sweep: .3, alpha: .8 }); laserFan(W - 260, 1080, tt, { n: 8, col: EP.cyan, angle: -2.04, spread: .9, sweep: .3, phase: 2, alpha: .8 });
    const j = jk * 1.9, air = { fL: [-.35, -.5 * jk], fR: [.35, -.25 * jk] };
    toy(560, 1000, 40, { ...CAST.token.o, hL: [-2.6, -10.6], hR: [2.3, -11.4], gL: 'wave', gR: 'point', jump: j, ...air, mouth: 'grin', lean: -.06 * jk, shadow: true });
    djClawd(1360, 990, 23, { shades: true, aL: 1.3, aR: 1.3, mouth: 'open', jump: jk * 3.4 });
    toy(960, 1010, 44, { ...CAST.softmax.o, hL: [-2.2, -11.0], hR: [2.2, -11.0], gL: 'wave', gR: 'wave', jump: j * 1.1, ...air, talk: .8, swing: .6 * jk, headTilt: -.06 });
    confetti(tt, tF - .6, 70);
  }
  const freezeImg = () => cached('c09|freeze', W, H, () => jumpScene(tF, 1));
  const freezeHookImg = () => cached('c09|freezeHook', W, H, () => { ctx.drawImage(freezeImg(), 0, 0, W, H); hook(L[4].end + 1, L[4], { glint: false }); });
  function pauseOSD(t) {
    if (frac(t * 1.8) > .72) return;
    pixText('PAUSE', 150, 836, 10, '#FFFFFF', { edge: '#000' });
    for (const bx of [520, 572]) { ctx.fillStyle = '#000'; ctx.fillRect(bx - 4, 832, 40, 78); ctx.fillStyle = '#FFFFFF'; ctx.fillRect(bx, 836, 32, 70); }
  }
  function vcrStill(img, t) {
    const jy = (Math.floor(t * 30) % 2) * 3 - 1.5; ctx.drawImage(img, 0, jy, W, H);
    // a tracking band crawling near the bottom
    const by = 930 + Math.sin(t * 2) * 20;
    for (let i = 0; i < 26; i++) { const x = hash2(Math.floor(t * 30), i) * W, w2 = 40 + hash2(i, Math.floor(t * 30)) * 220; ctx.fillStyle = `rgb(255 255 255 / ${.25 + .4 * hash2(i, 3)})`; ctx.fillRect(x, by + hash2(i, 9) * 26, w2, 2); }
  }
  function freeze(t) {
    hideCaption();
    if (t < tF) { const jk = Math.sin(clamp((t - T4) / (tF - T4)) * Math.PI / 2); jumpScene(t, jk); hook(t, L[4]); if (t < T4 + .12) strobe(.7 * (1 - (t - T4) / .12)); return; }
    vcrStill(freezeImg(), t);
    hook(t, L[4]);
    pauseOSD(t);
    if (t < tF + .06) fx({ flash: .6 });
  }

  // ---------- the PC: a beige CRT in a dark room; its screen is MX, MY, MW × MH ----------
  const MX = 240, MY = 140, MW = 1440, MH = 790, SCX = MX + MW / 2, SCY = MY + MH / 2;
  const PWX = 470, PWY = 90, PWW = 850, PWH = 598;             // the Media Player window, screen-local
  const VX = PWX + 9, VY = PWY + 57, VW = 832, VH = 468;        // its video area, screen-local
  function room(t, glowCol, ga = .25) {
    bgGrad([[0, '#0C0718'], [1, '#1C1030']]);
    ctx.fillStyle = '#231530'; ctx.fillRect(-900, 1010, W + 1800, 400);
    glow(SCX, SCY, 1200, glowCol, ga);
    // the monitor
    gloss(pfRR(MX - 80, MY - 66, MW + 160, MH + 250, 44), '#D8CFB4', { box: [MX - 80, MY - 66, MW + 160, MH + 250], rim: EP.cyan, rimK: .25, lw: 5, spec: .5 });
    rrect(MX - 18, MY - 18, MW + 36, MH + 36, 26); paint('#3A362C', EP.line, 3);
    txt('HYPE 17"', MX + 60, MY + MH + 62, 30, '#8A826C', { font: 'archivo', align: 'left' });
    for (let i = 0; i < 4; i++) { ctx.fillStyle = '#B8B098'; ctx.fillRect(MX + MW - 380 + i * 34, MY + MH + 50, 22, 20); }
  }
  function screenClip(draw, sx = 1, sy = 1) {
    ctx.save(); rrect(MX, MY, MW, MH, 20); ctx.clip(); ctx.fillStyle = '#000'; ctx.fillRect(MX, MY, MW, MH);
    ctx.translate(SCX, SCY); ctx.scale(sx, sy); ctx.translate(-MW / 2, -MH / 2);
    draw();
    ctx.restore();
    ctx.save(); rrect(MX, MY, MW, MH, 20); ctx.clip(); ctx.fillStyle = 'rgb(0 0 0 / .12)'; for (let y = MY; y < MY + MH; y += 4) ctx.fillRect(MX, y, MW, 1.5);
    ctx.fillStyle = rg(SCX, SCY, MH * .35, MW * .7, [[0, 'rgb(0 0 0 / 0)'], [1, 'rgb(0 0 0 / .35)']]); ctx.fillRect(MX, MY, MW, MH);
    ctx.fillStyle = 'rgb(255 255 255 / .05)'; ctx.beginPath(); ctx.ellipse(MX + MW * .3, MY + MH * .15, MW * .35, MH * .1, -.12, 0, TAU); ctx.fill(); ctx.restore();
  }
  // screen-local: the Windows 98 desktop, the paused player, the Start menu, the Shut Down dialog
  const MENU = [['folder', 'Programs', 1], ['doc', 'Documents', 1], ['computer', 'Settings', 1], ['globe', 'Find', 1], ['question', 'Help'], ['exe', 'Run...'], null, ['disk', 'Log Off SOFTMAX...'], ['computer', 'Shut Down...']];
  function startMenu(hi) {
    const x = 8, y = 56, w = 500, ih = 62, h = MENU.reduce((a, m) => a + (m ? ih : 16), 0) + 12, rects = [];
    ctx.fillStyle = 'rgb(0 0 0 / .35)'; ctx.fillRect(x + 10, y + 12, w, h);
    bevel(x, y, w, h, { b: 3 });
    ctx.fillStyle = lg(0, y + h, 0, y, [[0, EP.w98navy], [1, EP.w98blue]]); ctx.fillRect(x + 5, y + 5, 58, h - 10);
    ctx.save(); ctx.translate(x + 36, y + h - 18); ctx.rotate(-Math.PI / 2); txt('Windows', 0, 0, 42, '#C8C8C8', { font: 'archivo', align: 'left' }); txt('98', textW('Windows', 42, 'archivo') + 10, 0, 42, '#FFFFFF', { font: 'archivo', align: 'left' }); ctx.restore();
    let yy = y + 6;
    MENU.forEach((m, i) => {
      if (!m) { ctx.fillStyle = '#808080'; ctx.fillRect(x + 72, yy + 6, w - 84, 2); ctx.fillStyle = '#FFF'; ctx.fillRect(x + 72, yy + 8, w - 84, 2); yy += 16; return; }
      const on = i === hi; if (on) { ctx.fillStyle = EP.w98navy; ctx.fillRect(x + 66, yy, w - 72, ih); }
      icon98(m[0], x + 104, yy + ih / 2, .6);
      txt(m[1], x + 148, yy + ih / 2 + 2, 30, on ? '#FFF' : '#000', { font: 'archivo', align: 'left' });
      if (m[2]) { ctx.fillStyle = on ? '#FFF' : '#000'; poly([[x + w - 34, yy + ih / 2 - 9], [x + w - 22, yy + ih / 2], [x + w - 34, yy + ih / 2 + 9]]); ctx.fill(); }
      rects[i] = [x + 66, yy, w - 72, ih]; yy += ih;
    });
    return rects;
  }
  function shutDialog(k, sel, pressed) {
    const x = MW / 2 - 390, y = MH / 2 - 250, w = 780, h = 470;
    win98Window(x, y, w, h, 'Shut Down Windows', (cw, chh) => {
      icon98('computer', 70, 80, 1.3);
      txt('What do you want the computer to do?', 140, 46, 30, '#000', { font: 'archivo', align: 'left' });
      ['Shut down', 'Restart', 'Keep training'].forEach((s, i) => { const yy = 110 + i * 62; ell(170, yy, 16, 16); paint('#FFFFFF', '#404040', 3); if (i === sel) { ell(170, yy, 7, 7); ctx.fillStyle = '#000'; ctx.fill(); } txt(s, 200, yy + 2, 32, '#000', { font: 'archivo', align: 'left' }); if (i === sel) { ctx.strokeStyle = '#000'; ctx.lineWidth = 2; ctx.setLineDash([3, 3]); ctx.strokeRect(194, yy - 22, textW(s, 32, 'archivo') + 12, 46); ctx.setLineDash([]); } });
    }, { k, client: EP.w98, icon: 'computer' });
    if (k < 1) return null;
    const by = y + h - 96; win98Button('OK', x + w / 2 - 250, by, 220, 66, { def: true, focus: true, pressed, size: 32 }); win98Button('Cancel', x + w / 2 + 30, by, 220, 66, { size: 32 });
    return { ok: [x + w / 2 - 140, by + 36], r0: [175, y + 57 + 110], r2: [175, y + 57 + 234] };
  }
  function desktop(t, o = {}) {
    desktop98({ icons: [['computer', 'My Computer', 90, 150], ['bin', 'Recycle Bin', 90, 320], ['cd', "Scaling Hits '26", 90, 490], ['exe', 'train.exe', 90, 660, o.sel]], taskbar: 'top' });
    bevel(MW - 230, 8, 216, 40, { sunken: true, b: 2 }); txt('11:59 PM', MW - 122, 29, 24, '#000', { font: 'archivo' });
    // the paused Media Player
    win98Window(PWX, PWY, PWW, PWH, 'hypeTV.avi - Media Player', (cw, chh) => {
      ctx.fillStyle = EP.w98; ctx.fillRect(0, 0, cw, chh);
      ctx.drawImage(freezeHookImg(), 0, 0, VW, VH);
      const cy2 = VH + 30; bevel(10, VH + 6, 60, 50, { pressed: false }); poly([[32, cy2 - 12], [52, cy2], [32, cy2 + 12]]); paint('#000');
      bevel(76, VH + 6, 60, 50, { sunken: true }); ctx.fillStyle = '#000'; ctx.fillRect(96, cy2 - 11, 7, 22); ctx.fillRect(109, cy2 - 11, 7, 22);
      bevel(142, VH + 6, 60, 50); ctx.fillStyle = '#000'; ctx.fillRect(162, cy2 - 10, 20, 20);
      bevel(220, cy2 - 6, cw - 240, 12, { sunken: true, fill: '#FFFFFF' }); const sk = 220 + (cw - 260) * .87; bevel(sk, cy2 - 18, 22, 36);
    }, { icon: 'cd', inactive: o.inactive });
  }

  // ===========================================================================================================================
  // the pull back (after "scaling") and "But when we log off… will it still train on?"
  // ===========================================================================================================================
  const tStart = bt(41.2), tLog = wt(L[5], 'log'), tOff = wt(L[5], 'off'), tShut = bt(44), tRad = wt(L[5], 'will') - .12, tOK = wt(L[5], 'it') - .22, tSafe = wt(L[5], 'it') - .02, tStill = wt(L[5], 'still'), tCol = tTrain;
  function pcPhase(t) {
    hideStamp(); if (t < L[5].start - .08) hideCaption();
    // the camera: from the full-frame freeze, pulling back until the player is a window on the PC
    const pk = ease(clamp((t - tPB) / (tPB1 - tPB))), Z0 = W / VW, z = Math.exp(lerp(Math.log(Z0), 0, pk));
    const vcx = MX + VX + VW / 2, vcy = MY + VY + VH / 2;
    camBegin(lerp(vcx, W / 2, pk), lerp(vcy, H / 2, pk), z);
    room(t, EP.w98teal, .18);
    const menuOpen = t > tStart + .05 && t < tShut + .05, dlg = t >= tShut && t < tSafe, safe = t >= tSafe;
    screenClip(() => {
      if (safe) { safeScreen(t); return; }
      desktop(t, { inactive: menuOpen || dlg });
      let hi = -1;
      if (menuOpen) { hi = t < tLog - .05 ? (t < tStart + .3 ? -1 : Math.min(5, Math.floor((t - tStart - .3) / .1))) : t < tOff ? 7 : 8; startMenu(hi); }
      bevel(10, 6, 150, 42, { b: 3, sunken: menuOpen }); txt('Start', 85 + (menuOpen ? 2 : 0), 28 + (menuOpen ? 2 : 0), 26, '#000', { font: 'archivo' });
      let dl = null;
      if (dlg) { ctx.fillStyle = 'rgb(0 0 0 / .45)'; ctx.fillRect(0, 0, MW, MH); dl = shutDialog(clamp((t - tShut) / .12), t < tRad ? 2 : 0, t > tOK && t < tOK + .15); }
      // the cursor
      let cp;
      if (t < tStart - .25) cp = [VX + VW * .8, VY + VH * .6];
      else if (!dlg) cp = kf(t, [[tStart - .25, [VX + VW * .8, VY + VH * .6]], [tStart, [80, 30]], [tStart + .3, [140, 150]], [tLog - .05, [260, 56 + 6 + 6 * 62 + 16 + 31]], [tOff, [260, 56 + 6 + 6 * 62 + 16 + 62 + 31]]], easeOut);
      else cp = dl ? kf(t, [[tShut + .12, [300, 560]], [tRad - .03, dl.r0], [tRad + .1, dl.r0], [tOK - .02, dl.ok]], easeOut) : [300, 560];
      const clk = t > tStart && t < tStart + .25 ? (t - tStart) / .25 : t > tShut - .05 && t < tShut + .2 ? (t - tShut + .05) / .25 : dl && t > tRad && t < tRad + .25 ? (t - tRad) / .25 : dl && t > tOK && t < tOK + .25 ? (t - tOK) / .25 : 0;
      cursor98(cp[0], cp[1], { click: clk });
    });
    camEnd();
    if (t < tPB + .05 && t >= tPB) pauseOSD(t);
  }
  // "It's now safe to turn off your computer." (screen-local)
  function safeScreen(t) {
    ctx.fillStyle = '#000'; ctx.fillRect(0, 0, MW, MH);
    ptext("It's now safe to turn off", MW / 2, MH / 2 - 50, 66, { fill: '#FF8A1A' }); ptext('your computer.', MW / 2, MH / 2 + 40, 66, { fill: '#FF8A1A' });
    if (t > tStill - .05) { const blink = frac(t * 3) < .6; pixText('STILL TRAINING' + (blink ? '...' : ''), MW - 60, MH - 70, 4, '#3BFF4A', { align: 'right', glow: true, alpha: clamp((t - tStill + .05) / .1) }); }
  }
  function shutdown(t) {
    // up to "train": the PC scene; then the CRT collapses to a line, then a dot that won't die
    if (t < tCol) return pcPhase(t);
    hideStamp();
    room(t, '#FF8A1A', .08);
    const a = t - tCol, k1 = clamp(a / .16), k2 = clamp((a - .16) / .14);
    if (k2 < 1) {
      screenClip(() => {}, 1, 1);
      ctx.save(); ctx.beginPath(); ctx.rect(MX, MY, MW, MH); ctx.clip();
      ctx.translate(SCX, SCY); ctx.scale(lerp(1, .004, easeIn(k2)), lerp(1, .006, easeIn(k1))); ctx.translate(-MW / 2, -MH / 2);
      safeScreen(t); ctx.globalCompositeOperation = 'lighter'; ctx.fillStyle = `rgb(255 255 255 / ${.85 * k1})`; ctx.fillRect(0, 0, MW, MH);
      ctx.restore();
    } else screenClip(() => {});
    const dotA = a > .26 ? .7 + .3 * Math.sin((t - tCol) * 18) : 0, onQ = wt(L[5], 'on');
    if (dotA > 0) { const pulse2 = t > onQ ? 1 + kick(t, 5) * .6 : 1; glow(SCX, SCY, 90 * pulse2, '#FFFFFF', dotA); glint(SCX, SCY, 90 * pulse2, dotA); }
  }

  // ===========================================================================================================================
  // "And on, and on, and on, and on": the CRT blinks back on by itself — the 3D Pipes, one more pipe per "on"; push into the screen
  // ===========================================================================================================================
  const PIPE0 = [ON0, ...onTimes];
  function screensaverPipes(t, cx, cy, sc) {
    PIPE0.forEach((t0, i) => { if (t < t0) return; pipes(t, t0, { bg: false, n: 1, seed: 40 + i * 3, cx, cy, scale: sc, rate: 7 + i * 2.5, maxLen: 90, cols: [['#E8342A', '#2A9AE8', '#E8C42A', '#2AE85A', '#C42AE8'][i]] }); });
  }
  function andOn(t) {
    hideStamp(); hideCaption();
    const a = t - ON0, u = clamp(a / (TD - ON0)), z = lerp(1, 1.38, easeIn(u));
    camBegin(SCX, SCY, z);
    room(t, EP.cyan, .12 + .1 * u);
    const on = clamp(a / .14), sx = lerp(.004, 1, easeOut(clamp(on / .5))), sy = lerp(.006, 1, easeOut(clamp((on - .5) / .5)));
    screenClip(() => { fillAll('#000'); screensaverPipes(t, MW / 2, MH / 2 + 30, 64); }, sx, sy);
    camEnd();
    if (a < .1) fx({ flash: .4 * (1 - a / .1) });
    karaokeLine(ONLN, t, { singer: 'softmax' });
  }

  // ===========================================================================================================================
  // THE DROP (b55–59): the megarave and the title logo in chrome
  // ===========================================================================================================================
  const SKYP = { t0: ON0, n: 5, seed: 11, scale: 52, rate: 3 };
  function dropShot(t) {
    hideCaption();
    const a = t - TD, sh = a < .45 ? shakeXY(t, 24 * (1 - a / .45)) : [0, 0];
    setLight({ rim: EP.cyan, rimK: .85 });
    camBegin(W / 2 + sh[0], 560 + sh[1], lerp(1.1, 1, easeOut(clamp(a / .9))));
    megarave(t, { hz: 600, fw: TD - .05, pipes: SKYP, gy: 330, gr: 300 });
    stageDisc(t, 820); trio(t, 830, { tm: 'pump', sm: 'raise' });
    camEnd();
    raveCrowd(t, { y: 1070, s: 1.35, rows: 2, n: 11, hands: 1, rim: EP.magenta, seed: 5, sticks: .7 });
    hook(t, null, { at: TD, y1: 196, y2: 370 });
    lensFlare(lerp(-100, W + 200, clamp(a / 1.4)), 120, .8 * Math.sin(clamp(a / 1.4) * Math.PI));
    if (a < .2) strobe(1 - a / .2);
    else strobe(strobeK(t, 1, .2) * .22);
    if (a < .12) fx({ rgb: 1 - a / .12 });
    if (t < ONLN.end + .5) karaokeLine(ONLN, t, { singer: 'softmax', alpha: 1 - clamp((t - ONLN.end - .2) / .3) });
  }
  // b59–63: the 90s tri-split — each of the trio in their own tunnel
  function triSplit(t) {
    const a = t - bt(59), bb = bpOf(t), swap = t > bt(61);
    const P = [
      { tun: 'hex', cols: [EP.cyan, EP.blue, EP.white], bg: '#000820', glow: EP.cyan, name: 'MC TOKEN', st: 'ice', rim: EP.cyan },
      { tun: 'ring', cols: [EP.magenta, EP.pink, EP.yellow], bg: '#1A0010', glow: EP.magenta, name: 'SOFTMAX', st: 'hot', rim: EP.magenta },
      { tun: 'square', cols: [EP.orange, EP.yellow, EP.magenta], bg: '#12020A', glow: EP.orange, name: 'DJ CLAWD', st: 'gold', rim: EP.yellow },
    ];
    if (a < .3) fillAll('#FFFFFF');
    for (let i = 0; i < 3; i++) {
      const p = P[swap ? (i + 1) % 3 : i], q = P[i], k = easeOut(clamp((a - i * .05) / .16)), dy = (1 - k) * (i % 2 ? H : -H), x0 = i * 640, cx = x0 + 320;
      ctx.save(); ctx.beginPath(); ctx.rect(x0, 0, 640, H); ctx.clip(); ctx.translate(0, dy);
      tunnel(t + i * .3, { cx, cy: 470, n: 16, speed: 2.4, shape: p.tun, cols: p.cols, bg: p.bg, r: 1000, width: 60, glow: p.glow, twist: .12 });
      ctx.fillStyle = lg(0, 860, 0, 1080, [[0, 'rgb(0 0 0 / 0)'], [1, alpha(p.glow, .5)]]); ctx.fillRect(x0, 860, 640, 220);
      setLight({ rim: q.rim, rimK: .85 });
      if (i === 0) toy(cx, 1010, 50, { ...CAST.token.o, ...dance(Math.floor(bb) % 4 < 2 ? 'runningMan' : 'point', bb), mouth: 'grin' });
      if (i === 1) toy(cx, 1015, 52, { ...CAST.softmax.o, ...dance('vogue', bb), talk: singK(t), turn: Math.sin(t * 2) * .3 });
      if (i === 2) { const sc = kick(t, 8); djClawd(cx, 850, 30, { shades: true, aL: 1.35, aR: lerp(-.1, -.45, sc), mouth: 'grin', dy: -bounce(t) * .25 }); djBooth(cx, 790, 560, t, { scratch: sc }); }
      chromeText(q.name, cx, 210, 74, { style: q.st, italic: .15, depth: 10, s: lerp(1.6, 1, easeOut(clamp((a - i * .07 - .1) / .2))), alpha: clamp((a - i * .07 - .1) * 6) });
      ctx.restore();
    }
    for (const x of [640, 1280]) { ctx.fillStyle = '#FFFFFF'; ctx.fillRect(x - 5, 0, 10, H); glow(x, 540, 300, EP.white, .12); }
    if (swap && t < bt(61) + .1) fx({ flash: .5 * (1 - (t - bt(61)) / .1) });
  }
  // b63–67: the reverse angle — the trio from behind, an ocean of glowsticks to the horizon
  function reverseAngle(t) {
    const a = t - bt(63), bb = bpOf(t), hz = 420;
    camBegin(W / 2, 540 - a * 10, 1.02);
    bgGrad([[0, '#02000A'], [.6, '#1A0548'], [1, '#FF2FA0']], { y1: hz });
    fireworks(t, bt(63) - .3, { y0: 110, y1: 280, r: 170 });
    gridFloor(t, hz, { col: EP.cyan, far: '#1A0A3A' });
    for (let r = 0; r < 5; r++) raveCrowd(t, { y: hz + 22 + r * r * 26 + r * 30, s: .22 + r * .16, rows: 2, n: 46 - r * 6, k: 1, hands: .75, sticks: .8, rim: [EP.cyan, EP.magenta][r % 2], col: mixCol('#1C0A3E', '#0A0418', r / 4), seed: 60 + r });
    for (const [x, c, ph] of [[300, EP.laser, 0], [W - 300, EP.magenta, 1.5], [W / 2, EP.cyan, 3]]) laserFan(x, 1080, t, { n: 9, col: c, angle: -Math.PI / 2, spread: 1.6, sweep: .6, phase: ph, alpha: .5, fanSweep: true });
    // the trio from behind, lit from the front by the crowd's lights
    const sil = '#150A2C';
    for (const [x, c] of [[420, EP.cyan], [W / 2, EP.yellow], [1500, EP.magenta]]) glow(x, 900, 360, c, .22);
    setLight({ rimK: 1, rx: 0, ry: -1 });
    toy(420, 1190, 50, { ...CAST.token.o, ...dance('pump', bb), sil, rim: EP.cyan, shadow: false });
    djClawd(W / 2, 1150, 25, { col: sil, line: sil, rim: EP.yellow, aL: 1.2 + Math.sin(bb * Math.PI) * .3, aR: 1.2 - Math.sin(bb * Math.PI) * .3, eyes: 'closed', shadow: false });
    toy(1500, 1195, 52, { ...CAST.softmax.o, ...dance('raise', bb - .25), sil, rim: EP.magenta, shadow: false });
    camEnd();
    if (a < .1) strobe(.6 * (1 - a / .1));
  }
  // b67–75 "(And on, and on, and on…)": SOFTMAX on the speaker stack, then the trio on three stacks under the towering pipes
  function stackOf(x, y, w, t) { for (const [dx, dy] of [[-w * .52, 0], [w * .52, 0], [-w * .52, -w * 1.72], [w * .52, -w * 1.72]]) speaker(x + dx, y + dy, w, t, { logo: 'hype' }); return y - w * 3.44; }
  function stacks(t) {
    const a = t - bt(67), wide = t >= bt(71), bb = bpOf(t);
    setLight({ rim: EP.magenta, rimK: .85 });
    if (!wide) {
      camBegin(W / 2, lerp(600, 520, ease(a / (bt(71) - bt(67)))), 1.02);
      megarave(t, { hz: 700, globe: false, pipes: { t0: ON0, n: 4, seed: 11, scale: 50, rate: 3, cx: W / 2 + 470, cy: 360 }, fw: bt(67) - .3, crowd: false });
      glow(W / 2, 420, 520, EP.magenta, .3);
      const top = stackOf(W / 2, 1110, 128, t);
      toy(W / 2, top, 44, { ...CAST.softmax.o, ...dance(Math.floor(bb) % 4 < 2 ? 'sing' : 'raise', bb), talk: singK(t), swing: .5 + Math.sin(t * 7) * .25 });
      lensFlare(W / 2 - 360, top - 400, .6 + .2 * Math.sin(t * 3));
      camEnd();
      raveCrowd(t, { y: 1100, s: 1.5, rows: 1, n: 9, hands: 1, rim: EP.magenta, seed: 12, sticks: .8 });
      if (a < .1) strobe(.6 * (1 - a / .1));
      return;
    }
    const b = t - bt(71);
    camBegin(W / 2, 540, lerp(1.05, 1, ease(b / 1.7)));
    megarave(t, { hz: 640, globe: false, pipes: { t0: ON0, n: 5, seed: 11, scale: 64, rate: 3, cy: 290 }, fw: bt(71) - .3 });
    const tops = [[400, 1], [W / 2, 0], [W - 400, 2]].map(([x, who]) => [x, who, stackOf(x, 1130, 100, t)]);
    for (const [x, , top] of tops) glow(x, top - 200, 300, EP.magenta, .25);
    for (const [x, who, top] of tops) {
      if (who === 0) toy(x, top, 38, { ...CAST.softmax.o, ...dance('raise', bb), talk: singK(t) });
      if (who === 1) toy(x, top, 35, { ...CAST.token.o, ...dance('pump', bb), mouth: 'grin' });
      if (who === 2) djClawd(x, top, 21, { shades: true, aL: 1.2 + Math.sin(bb * Math.PI) * .3, aR: 1.2 - Math.sin(bb * Math.PI) * .3, mouth: 'grin', jump: bounce(t) });
    }
    camEnd();
    raveCrowd(t, { y: 1100, s: 1.4, rows: 1, n: 10, hands: 1, rim: EP.cyan, seed: 13 });
    if (b < .1) strobe(.6 * (1 - b / .1));
  }
  // b75–79: everyone on the stage; b79–83: one-beat close-ups; b83–87: crane up, white-out
  function everyone(t) {
    const a = t - bt(75), bb = bpOf(t);
    setLight({ rim: EP.cyan, rimK: .8 });
    camBegin(W / 2, 560, lerp(1.04, 1, ease(a / 1.7)));
    megarave(t, { hz: 560, fw: bt(75) - .3, globe: false, crowd: false });
    raveCrowd(t, { y: 600, s: .3, rows: 2, n: 40, k: 1, hands: .7, rim: EP.cyan, col: '#1C0A3E', seed: 31 });
    stageDisc(t, 860, 860);
    modelsRow(t, 705, 11, 300, 1620);
    peopleRow(t, 810, 16.5, 180, 1740);
    toy(600, 925, 30, { ...CAST.token.o, ...dance('runningMan', bb), mouth: 'grin' });
    djClawd(820, 915, 16, { shades: true, aL: 1.1 + Math.sin(bb * Math.PI) * .3, aR: 1.1 - Math.sin(bb * Math.PI) * .3, mouth: 'grin', jump: bounce(t) * .8 });
    opus(1110, 920, 8, { aL: .9, aR: 1.3 + Math.sin(bb * Math.PI * 2) * .3, jump: bounce(t) * 1.4 });
    toy(1330, 930, 32, { ...CAST.softmax.o, ...dance('raise', bb), talk: singK(t) });
    camEnd();
    raveCrowd(t, { y: 1100, s: 1.35, rows: 1, n: 11, hands: 1, rim: EP.magenta, seed: 14 });
    confetti(t, bt(75) - .1, 80);
    hook(t, null, { at: bt(75) - 1, s1: 110, s2: 150, y1: 160, y2: 290 });
    sweepGlint(560, 1360, 270, (a - .2) / .7, 140);
    if (a < .12) strobe(.7 * (1 - a / .12));
  }
  function closeUps(t) {
    const i = clamp(Math.floor(bpOf(t) - B0 - 79), 0, 3), a = t - bt(79 + i), bb = bpOf(t);
    const bgs = [[EP.cyan, '#001A6A'], [EP.magenta, '#3A0030'], [EP.orange, '#3A0A00'], [EP.yellow, '#3A2A00']][i];
    bgGrad([[0, bgs[1]], [1, '#05010E']], { radial: true, cx: W / 2, cy: 480, r: 1100 });
    rays(W / 2, 480, 20, alpha(bgs[0], .25), t * .6 * (i % 2 ? -1 : 1));
    sparkles(t, { n: 14, seed: 30 + i, r: 50 });
    setLight({ rim: bgs[0], rimK: .9 });
    const z = 1 + a * .06; camBegin(W / 2, 540, z);
    if (i === 0) toy(W / 2, 1600, 124, { ...CAST.token.o, hR: [2.4, -9.2], gR: 'point', hL: [-2.6, -6.6], gL: 'fist', mouth: 'grin', lean: .03, headTilt: -.05, shadow: false });
    if (i === 1) toy(W / 2, 1610, 126, { ...CAST.softmax.o, hR: [2.6, -9.6], gR: 'peace', hL: [-2.4, -7.2], gL: 'open', eyes: 'wink', mouth: 'grin', headTilt: .06, swing: .4, shadow: false });
    if (i === 2) djClawd(W / 2, 1280, 76, { shades: true, aL: 1.3, aR: 1.3, mouth: 'open', shadow: false, legs: false });
    if (i === 3) { opus(W / 2, 1240, 70, { aL: 1.4 + Math.sin(t * 20) * .2, aR: -.6, shadow: false, legs: false }); burst('HI!', 1500, 300, 110, { pop: pop(t, bt(82) + .05, .15), col: EP.yellow, ink: EP.magenta, spin: .3 }); }
    camEnd();
    if (a < .1) strobe(.8 * (1 - a / .1));
  }
  function craneUp(t) {
    const a = t - bt(83), u = a / (TOUT - bt(83)), bb = bpOf(t);
    setLight({ rim: EP.cyan, rimK: .8 });
    camBegin(W / 2, lerp(540, 620, ease(u)), lerp(1.12, .98, ease(u)));
    megarave(t, { hz: 480, fw: bt(83) - .3, globe: true, gy: 250, gr: 220, pipes: { t0: ON0, n: 4, seed: 11, scale: 60, rate: 3, cy: 260 } });
    raveCrowd(t, { y: 800, s: .8, rows: 2, n: 16, k: 1, hands: .9, rim: EP.cyan, col: '#140630', seed: 40 });
    stageDisc(t, 740, 520); trio(t, 750, { s: 24, dx: 260, tm: 'pump', sm: 'raise' });
    fireworks(t, bt(83) - .3, { every: 1, x0: 120, x1: 1800, y0: 120, y1: 340, r: 200 });
    camEnd();
    raveCrowd(t, { y: 1080, s: 1.4, rows: 2, n: 11, hands: 1, rim: EP.magenta, seed: 41, sticks: .8 });
    hook(t, null, { at: bt(83) - 1, y1: 196, y2: 370 });
    sweepGlint(420, 1500, 330, (a - .3) / .8, 170);
    if (a < .12) strobe(.7 * (1 - a / .12));
    const wo = clamp((t - bt(86.4)) / (TOUT - bt(86.4))); if (wo > 0) strobe(easeIn(wo));
  }

  // ===========================================================================================================================
  // the quiet outro (b87–102): the 3D Pipes fill the screen, a gold pipe climbs the curve, the credit block returns
  // ===========================================================================================================================
  function outroPipes(t) {
    hideStamp();
    const a = t - TOUT, u = a / (TEND - TOUT);
    camBegin(W / 2, 540, 1 + .05 * u);
    fillAll('#000');
    pipeSet(t, TOUT - 1.5, 5, { seed: 5, scale: 70, rate: 7, cx: 1260, cy: 540, w: .24 });
    pipeSet(t, TOUT + .8, 3, { seed: 9, scale: 58, rate: 7, cx: 600, cy: 360, w: .24 });
    ctx.fillStyle = 'rgb(0 0 12 / .38)'; ctx.fillRect(-100, -100, W + 200, H + 200);
    const tip = pipeStair(t, bt(88), { x0: 960, y0: 930, dx: 96, h0: 17, growth: 1.5, n: 8, col: '#FFC83A', w: 26, glow: EP.yellow });
    glow(tip[0], tip[1], 200, EP.yellow, .6); glint(tip[0], tip[1], 150 * (.7 + .3 * kick(t, 5)), .9);
    camEnd();
    const ck = clamp((a - .4) / .8); ctx.fillStyle = lg(0, 700, 0, 980, [[0, `rgb(0 0 0 / 0)`], [.3, `rgb(0 0 10 / ${.7 * ck})`], [1, `rgb(0 0 10 / ${.7 * ck})`]]); ctx.fillRect(0, 700, 1000, 300);
    creditBlock(ck);
    if (a < .1) strobe(1 - a / .1);
  }
  // the last hit (b102 → end): the hype★TV end card — UP NEXT and the credits
  const CREDITS = ['HOOK AFTER @TAUTOLOGER', 'LYRICS: DOMENIC & CLAUDE', 'MUSIC: SUNO', 'VIDEO: CLAUDE OPUS 5.5', 'SEP 2026'];
  function endCard(t) {
    hideStamp(); hideBug(); hideCaption();
    const a = t - TEND;
    fillAll('#05010E');
    ctx.save(); ctx.globalAlpha = .55; tunnel(t, { speed: .8, cols: [EP.magenta, EP.cyan, EP.uv], shape: 'ring', width: 40, bg: false, cy: 300 }); ctx.restore();
    // the channel logo spins in
    const k = easeOut(clamp(a / .5)), spin = (1 - k) * Math.PI * 2.5;
    glow(W / 2, 250, 460 * k, EP.magenta, .5 * k);
    chromeText('hype', W / 2 - 40, 250, 190, { font: 'rammetto', style: 'chrome', italic: .08, depth: 18, s: lerp(.2, 1, k), sx: Math.cos(spin), alpha: clamp(k * 2) });
    ctx.save(); ctx.translate(W / 2 + 250 * k, 150); ctx.rotate(t * 2.5); ctx.scale(k, k); poly(starPts(0, 0, 54, .45, 5)); ctx.fillStyle = lg(0, -54, 0, 54, [[0, '#FFFFFF'], [.5, EP.yellow], [1, EP.orange]]); ctx.fill(); ctx.strokeStyle = EP.line; ctx.lineWidth = 5; ctx.stroke(); ctx.restore();
    pixText('TV', W / 2 + 300, 214, 7, EP.white, { align: 'center', glow: true, alpha: k });
    // UP NEXT
    const nk = clamp((a - .35) / .25), px = 300, py = 410, pw = W - 600, ph = 190;
    if (nk > 0) {
      ctx.save(); ctx.translate(0, (1 - easeOut(nk)) * 60); ctx.globalAlpha = nk;
      gloss(pfRR(px, py, pw, ph, 30), '#1A0840', { box: [px, py, pw, ph], rim: EP.magenta, lw: 5, spec: .3 });
      gloss(pfRR(px + 24, py + 28, 250, 64, 32), EP.yellow, { box: [px + 24, py + 28, 250, 64], lw: 4, rim: null }); txt('UP NEXT', px + 136, py + 62, 32, EP.line, { font: 'bungee' }); ctx.fillStyle = EP.line; poly([[px + 222, py + 46], [px + 248, py + 60], [px + 222, py + 74]]); ctx.fill();
      txt('DJ Clawd pres. Softmax feat. MC Token', px + 300, py + 60, 32, '#B8B0E8', { font: 'archivo', align: 'left', maxW: pw - 330 });
      txt('We Didn\'t Start The Scaling (And On & On Mix)', px + pw / 2, py + 136, 50, '#FFFFFF', { font: 'archivo', maxW: pw - 60 });
      ctx.restore();
      sweepGlint(px + 40, px + pw - 40, py + 120, (a - .7) / .8, 110);
    }
    // the credits
    CREDITS.forEach((s, i) => { const ck = clamp((a - .6 - i * .12) / .2); if (ck > 0) ptext(s, W / 2, 680 + i * 58, i === 4 ? 36 : 40, { fill: i === 4 ? EP.yellow : '#FFFFFF', strokes: [['#05010E', 8]], alpha: ck, spacing: 2 }); });
    if (a < .15) strobe(1 - a / .15);
  }

  // ===========================================================================================================================
  function finale(t) {
    if (t < T1) return flyIn(t);
    if (t < T2) return training(t);
    if (t < T3) return castLineup(t);
    if (t < T4) return paceRace(t);
    if (t < tPB) return freeze(t);
    if (t < ON0) return shutdown(t);
    if (t < TD) return andOn(t);
    if (t < bt(59)) return dropShot(t);
    if (t < bt(63)) return triSplit(t);
    if (t < bt(67)) return reverseAngle(t);
    if (t < bt(75)) return stacks(t);
    if (t < bt(79)) return everyone(t);
    if (t < bt(83)) return closeUps(t);
    if (t < TOUT) return craneUp(t);
    if (t < TEND) return outroPipes(t);
    return endCard(t);
  }
  section('C4', (p, lt, d, t) => finale(t));
  section('outro', (p, lt, d, t) => finale(t));
})();
