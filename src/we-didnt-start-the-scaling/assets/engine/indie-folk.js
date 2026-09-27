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
// ---- styles/dither/kit.js ----
// kit.js: the "dither" style's shared look. Quiet, starlit pixel art for the album's hushed closing ballad.
// Every frame is painted into a 480×270 indexed framebuffer (FB) with a fixed 16-colour palette and ordered (Bayer) dithering,
// then upscaled ×4 to 1920×1080 with nearest-neighbour. No smooth alpha, no anti-aliasing, no ctx drawing: use only this API.
// Read STYLE.md before painting a chapter. Everything is a pure function of song time: no Math.random(), no state between frames.
// The zine's caption, date stamp and grain overlays (timeline.js) are dropped; this style registers its own (bottom of this file).
OVERLAYS.length = 0;

// =====================================================================================================
// FRAMEBUFFER, PALETTE, DITHER
// =====================================================================================================
const LW = 480, LH = 270, PXS = W / LW;          // low-res canvas; 1 low-res pixel = 4×4 output pixels
const FB = new Uint8Array(LW * LH);               // palette indices, row-major
const CLEAR = 255;                                // "untouched" marker inside layer()
const _FB2 = new Uint8Array(LW * LH), _FB3 = new Uint8Array(LW * LH);
// the incoming shot's frame while _dissolve() re-runs the previous shot (which may itself use _FB2, e.g. through reflect())
const _FBD = new Uint8Array(LW * LH);
const _lo = makeCanvas(LW, LH), _lg = _lo.getContext('2d');
const _img = _lg.createImageData(LW, LH), _u32 = new Uint32Array(_img.data.buffer);

// The palette: night navies, dusty warms, a few cool accents. Refer to colours by name: C.navy, C.gold, …
const C = { void: 0, ink: 1, night: 2, navy: 3, dusk: 4, haze: 5, wine: 6, rust: 7, clay: 8, amber: 9, gold: 10, cream: 11, pine: 12, teal: 13, mint: 14, violet: 15 };
const PALETTE = [
  '#05071a', '#0b1030', '#141d4d', '#213178', '#3a4f9e', '#7185c9', // void ink night navy dusk haze
  '#4a1733', '#9c3a3c', '#d9774f', '#f0a45c', '#f5d489', '#fff5e0', // wine rust clay amber gold cream
  '#10303a', '#2f7a78', '#8fe0b8', '#7a4fa0',                       // pine teal mint violet
];
const _PAL32 = new Uint32Array(256);
PALETTE.forEach((h, i) => { const r = parseInt(h.slice(1, 3), 16), g = parseInt(h.slice(3, 5), 16), b = parseInt(h.slice(5, 7), 16); _PAL32[i] = (0xff000000 | (b << 16) | (g << 8) | r) >>> 0; });
_PAL32[CLEAR] = _PAL32[0];
const col = c => typeof c === 'string' ? C[c] : c;   // 'gold' → 10

// Colour-remap tables (Doom COLORMAP style): LIT one step lighter, DIM one step darker, WARM toward lantern light, COOL toward moonlight.
function makeTab(pairs) { const t = new Uint8Array(256); for (let i = 0; i < 256; i++) t[i] = i; for (const k in pairs) t[C[k]] = C[pairs[k]]; return t; }
const LIT = makeTab({ void: 'ink', ink: 'night', night: 'navy', navy: 'dusk', dusk: 'haze', haze: 'cream', wine: 'rust', rust: 'clay', clay: 'amber', amber: 'gold', gold: 'cream', pine: 'teal', teal: 'mint', mint: 'cream', violet: 'haze' });
const DIM = makeTab({ ink: 'void', night: 'ink', navy: 'night', dusk: 'navy', haze: 'dusk', wine: 'ink', rust: 'wine', clay: 'rust', amber: 'clay', gold: 'amber', cream: 'gold', pine: 'void', teal: 'pine', mint: 'teal', violet: 'navy' });
const WARM = makeTab({ void: 'ink', ink: 'wine', night: 'wine', navy: 'violet', dusk: 'violet', haze: 'gold', wine: 'rust', rust: 'clay', clay: 'amber', amber: 'gold', gold: 'cream', pine: 'wine', teal: 'amber', mint: 'gold', violet: 'rust' });
const COOL = makeTab({ void: 'ink', ink: 'night', night: 'navy', navy: 'dusk', dusk: 'haze', wine: 'violet', rust: 'violet', clay: 'haze', amber: 'haze', gold: 'cream', pine: 'teal', teal: 'mint', violet: 'dusk' });
const GREEN = makeTab({ void: 'pine', ink: 'pine', night: 'pine', navy: 'teal', dusk: 'teal', haze: 'mint', violet: 'teal', wine: 'pine', rust: 'teal', clay: 'mint', amber: 'mint', gold: 'cream', pine: 'teal', teal: 'mint', mint: 'cream' });

// 8×8 Bayer thresholds in (0, 1). A pixel "passes" level k when bay(x, y) < k.
const BAYER = new Float32Array(64);
[0, 32, 8, 40, 2, 34, 10, 42, 48, 16, 56, 24, 50, 18, 58, 26, 12, 44, 4, 36, 14, 46, 6, 38, 60, 28, 52, 20, 62, 30, 54, 22,
  3, 35, 11, 43, 1, 33, 9, 41, 51, 19, 59, 27, 49, 17, 57, 25, 15, 47, 7, 39, 13, 45, 5, 37, 63, 31, 55, 23, 61, 29, 53, 21].forEach((v, i) => { BAYER[i] = (v + .5) / 64; });
const bay = (x, y) => BAYER[((y & 7) << 3) | (x & 7)];

// =====================================================================================================
// VIEW, CLIP, INKS
// =====================================================================================================
// view(x, y): world→screen offset for everything drawn after it (camera pans/tilts). Integer pixels; reset every frame.
let VX = 0, VY = 0, CX0 = 0, CY0 = 0, CX1 = LW - 1, CY1 = LH - 1;
function view(x = 0, y = 0) { VX = Math.round(x); VY = Math.round(y); }
function clipRect(x, y, w, h) { CX0 = Math.max(0, Math.round(x - VX)); CY0 = Math.max(0, Math.round(y - VY)); CX1 = Math.min(LW - 1, Math.round(x - VX + w) - 1); CY1 = Math.min(LH - 1, Math.round(y - VY + h) - 1); }
function noClip() { CX0 = 0; CY0 = 0; CX1 = LW - 1; CY1 = LH - 1; }

// An INK is what every fill takes: a palette index (C.gold), or one of these dithered inks.
//   mix(a, b, k)   ordered-dither blend, k = 0 → all a, 1 → all b (0.5 = checkerboard)
//   veil(c, k)     screen-door transparency: c covers fraction k of the pixels, the rest shows through
//   tint(tab, k)   remap what's underneath through a table (LIT/DIM/WARM/COOL/GREEN); k > 1 applies several steps
//   lit(k) dim(k) warm(k)   shorthands for tint()
//   grad(cols, fn) fn(x, y) → 0..1 picks a dithered position along the colour list (screen coords)
//   inkFn(fn)      fn(x, y, under) → palette index, or -1 to leave the pixel
function mix(a, b, k) {
  a = col(a); b = col(b);
  if (k <= 0) return a; if (k >= 1) return b;
  return { s(row, x0, x1, y) { const br = (y & 7) << 3; for (let x = x0; x <= x1; x++) FB[row + x] = BAYER[br | (x & 7)] < k ? b : a; } };
}
function veil(c, k) {
  c = col(c);
  if (!(k > 0)) return -1; if (k >= 1) return c;
  return { s(row, x0, x1, y) { const br = (y & 7) << 3; for (let x = x0; x <= x1; x++) if (BAYER[br | (x & 7)] < k) FB[row + x] = c; } };
}
function tint(tab, k = 1) {
  if (!(k > 0)) return -1;
  return {
    s(row, x0, x1, y) {
      const br = (y & 7) << 3, whole = Math.floor(k), f = k - whole;
      for (let x = x0; x <= x1; x++) { const i = row + x; let v = FB[i]; for (let j = 0; j < whole; j++) v = tab[v]; if (f > 0 && BAYER[br | (x & 7)] < f) v = tab[v]; FB[i] = v; }
    }
  };
}
const lit = (k = 1) => tint(LIT, k), dim = (k = 1) => tint(DIM, k), warm = (k = 1) => tint(WARM, k);
function grad(cols, fn) {
  cols = cols.map(col); const n = cols.length - 1;
  return {
    s(row, x0, x1, y) {
      const br = (y & 7) << 3;
      for (let x = x0; x <= x1; x++) {
        const v = fn(x, y) * n;
        if (!(v > 0)) { FB[row + x] = cols[0]; continue; }
        if (v >= n) { FB[row + x] = cols[n]; continue; }
        const i = v | 0; FB[row + x] = BAYER[br | (x & 7)] < v - i ? cols[i + 1] : cols[i];
      }
    }
  };
}
function inkFn(fn) { return { s(row, x0, x1, y) { for (let x = x0; x <= x1; x++) { const v = fn(x, y, FB[row + x]); if (v >= 0) FB[row + x] = v; } } }; }

// The one place pixels are written: a clipped horizontal span in screen coords.
function _sp(y, x0, x1, ink) {
  if (y < CY0 || y > CY1) return;
  if (x0 < CX0) x0 = CX0; if (x1 > CX1) x1 = CX1; if (x0 > x1) return;
  const row = y * LW;
  if (typeof ink === 'number') { if (ink >= 0) FB.fill(ink, row + x0, row + x1 + 1); return; }
  if (typeof ink === 'string') { FB.fill(C[ink], row + x0, row + x1 + 1); return; }
  if (ink) ink.s(row, x0, x1, y);
}

// =====================================================================================================
// PRIMITIVES (world coords; integer-snapped; all take an INK)
// =====================================================================================================
const _r = Math.round;
function cls(ink = C.void) { for (let y = CY0; y <= CY1; y++) _sp(y, CX0, CX1, ink); }
function rectf(x, y, w, h, ink) { x = _r(x - VX); y = _r(y - VY); w = _r(w); h = _r(h); for (let j = 0; j < h; j++) _sp(y + j, x, x + w - 1, ink); }
function rectb(x, y, w, h, ink) { rectf(x, y, w, 1, ink); rectf(x, y + h - 1, w, 1, ink); rectf(x, y + 1, 1, h - 2, ink); rectf(x + w - 1, y + 1, 1, h - 2, ink); }
// Rounded box: corners clipped by `r` pixels (1 or 2 look best).
function rboxf(x, y, w, h, ink, r = 1) { x = _r(x); y = _r(y); w = _r(w); h = _r(h); for (let j = 0; j < h; j++) { const e = j < r ? r - j : j >= h - r ? j - (h - r) + 1 : 0; rectf(x + e, y + j, w - 2 * e, 1, ink); } }
function pset(x, y, ink) { x = _r(x - VX); y = _r(y - VY); _sp(y, x, x, ink); }
function pget(x, y) { x = _r(x - VX); y = _r(y - VY); return x < 0 || y < 0 || x >= LW || y >= LH ? -1 : FB[y * LW + x]; }
function hline(x0, x1, y, ink) { if (x1 < x0) [x0, x1] = [x1, x0]; _sp(_r(y - VY), _r(x0 - VX), _r(x1 - VX), ink); }
function vline(x, y0, y1, ink) { if (y1 < y0) [y0, y1] = [y1, y0]; x = _r(x - VX); for (let y = _r(y0 - VY); y <= _r(y1 - VY); y++) _sp(y, x, x, ink); }
// Bresenham line. every/phase make it dashed: draws steps where (i + phase) % every < on.
function pline(x0, y0, x1, y1, ink, o) {
  x0 = _r(x0 - VX); y0 = _r(y0 - VY); x1 = _r(x1 - VX); y1 = _r(y1 - VY);
  const dx = Math.abs(x1 - x0), dy = -Math.abs(y1 - y0), sx = x0 < x1 ? 1 : -1, sy = y0 < y1 ? 1 : -1;
  const every = o && o.every || 0, on = o && o.on || 1, ph = o && o.phase || 0;
  let err = dx + dy, i = 0;
  for (;;) {
    if (!every || ((i + ph) % every + every) % every < on) _sp(y0, x0, x0, ink);
    if (x0 === x1 && y0 === y1) break;
    const e2 = 2 * err; if (e2 >= dy) { err += dy; x0 += sx; } if (e2 <= dx) { err += dx; y0 += sy; }
    i++;
  }
}
function plines(pts, ink, close = false, o) { for (let i = 0; i + 1 < pts.length; i++) pline(pts[i][0], pts[i][1], pts[i + 1][0], pts[i + 1][1], ink, o); if (close && pts.length > 2) pline(pts[pts.length - 1][0], pts[pts.length - 1][1], pts[0][0], pts[0][1], ink, o); }
// Thick line: a filled quad of width w (w ≥ 2).
function thick(x0, y0, x1, y1, w, ink) {
  const L = Math.hypot(x1 - x0, y1 - y0) || 1, nx = -(y1 - y0) / L * w / 2, ny = (x1 - x0) / L * w / 2;
  polyf([[x0 + nx, y0 + ny], [x1 + nx, y1 + ny], [x1 - nx, y1 - ny], [x0 - nx, y0 - ny]], ink);
}
// Filled circle centred on pixel (cx, cy). r may be fractional; r = 1 is a plus, r = 2 a round 5×5.
function circf(cx, cy, r, ink) {
  cx = _r(cx - VX); cy = _r(cy - VY);
  if (r < .5) return _sp(cy, cx, cx, ink);
  const rr = r * r + r * .8, R = Math.ceil(r);
  for (let dy = -R; dy <= R; dy++) { const q = rr - dy * dy; if (q < 0) continue; const hw = Math.floor(Math.sqrt(q)); _sp(cy + dy, cx - hw, cx + hw, ink); }
}
function circb(cx, cy, r, ink) { ringf(cx, cy, r - 1, r, ink); }
// Ring between radii r0 < r1 (inclusive of r1's disc, exclusive of r0's).
function ringf(cx, cy, r0, r1, ink) {
  cx = _r(cx - VX); cy = _r(cy - VY);
  const R = Math.ceil(r1), oo = r1 * r1 + r1 * .8, ii = r0 < .5 ? -1 : r0 * r0 + r0 * .8;
  for (let dy = -R; dy <= R; dy++) {
    const qo = oo - dy * dy; if (qo < 0) continue;
    const ho = Math.floor(Math.sqrt(qo)), qi = ii - dy * dy;
    if (qi < 0) { _sp(cy + dy, cx - ho, cx + ho, ink); continue; }
    const hi = Math.floor(Math.sqrt(qi));
    _sp(cy + dy, cx - ho, cx - hi - 1, ink); _sp(cy + dy, cx + hi + 1, cx + ho, ink);
  }
}
function ellf(cx, cy, rx, ry, ink) {
  cx = _r(cx - VX); cy = _r(cy - VY);
  const R = Math.ceil(ry), ey = ry + .45;
  for (let dy = -R; dy <= R; dy++) { const q = 1 - (dy / ey) ** 2; if (q < 0) continue; const hw = Math.floor(rx * Math.sqrt(q) + .35); _sp(cy + dy, cx - hw, cx + hw, ink); }
}
// Polygon fill (even-odd), sampled at pixel centres. pts = [[x, y], …] in world coords.
function polyf(pts, ink) {
  const n = pts.length; if (n < 3) return;
  const P = new Float64Array(n * 2); let ymin = Infinity, ymax = -Infinity;
  for (let i = 0; i < n; i++) { P[2 * i] = pts[i][0] - VX; P[2 * i + 1] = pts[i][1] - VY; ymin = Math.min(ymin, P[2 * i + 1]); ymax = Math.max(ymax, P[2 * i + 1]); }
  const y0 = Math.max(CY0, Math.ceil(ymin - .5)), y1 = Math.min(CY1, Math.floor(ymax - .5)), xs = [];
  for (let y = y0; y <= y1; y++) {
    const sy = y + .5; xs.length = 0;
    for (let i = 0, j = n - 1; i < n; j = i++) {
      const ay = P[2 * i + 1], by = P[2 * j + 1];
      if ((ay <= sy) !== (by <= sy)) xs.push(P[2 * i] + (sy - ay) / (by - ay) * (P[2 * j] - P[2 * i]));
    }
    xs.sort((a, b) => a - b);
    for (let k = 0; k + 1 < xs.length; k += 2) { const xa = Math.ceil(xs[k] - .5), xb = Math.ceil(xs[k + 1] - .5) - 1; if (xb >= xa) _sp(y, xa, xb, ink); }
  }
}
function triPx(x0, y0, x1, y1, x2, y2, ink) { polyf([[x0, y0], [x1, y1], [x2, y2]], ink); }
// Star polygon: n points, outer radius r, inner radius r·inner, rotated by rot.
function burstPx(cx, cy, r, inner, n, rot, ink) {
  const pts = []; for (let i = 0; i < n * 2; i++) { const a = rot + i / (n * 2) * TAU - Math.PI / 2, rr = i % 2 ? r * inner : r; pts.push([cx + Math.cos(a) * rr, cy + Math.sin(a) * rr]); }
  polyf(pts, ink);
}
// The dusty-red starburst (the style's signature bloom): spikes with a dithered fringe and a solid core.
// k 0..1 grows it; o: n (spikes), rot, inner, ink (core), fringe (fringe colour), long (alternate long/short spikes)
function starburst(cx, cy, r, k = 1, o = {}) {
  if (k <= 0) return;
  const n = o.n ?? 14, rot = o.rot ?? 0, inner = o.inner ?? .32, R = r * k;
  const pts = (rr, inn) => { const a = []; for (let i = 0; i < n * 2; i++) { const ang = rot + i / (n * 2) * TAU - Math.PI / 2, long = o.long !== false && (i >> 1) % 2 ? .72 : 1; a.push([cx + Math.cos(ang) * (i % 2 ? rr * inn : rr * long), cy + Math.sin(ang) * (i % 2 ? rr * inn : rr * long)]); } return a; };
  polyf(pts(R * 1.16, inner * 1.2), veil(o.fringe ?? C.wine, .38));
  polyf(pts(R * 1.07, inner * 1.1), mix(o.fringe ?? C.wine, o.ink ?? C.rust, .5));
  polyf(pts(R, inner), o.ink ?? C.rust);
  if (o.core !== false) circf(cx, cy, Math.max(1, R * inner * .9), o.ink ?? C.rust);
}
// Shaded sphere: ramp from dark to light, lit from (lx, ly) (−1..1, default upper-left).
function ball(cx, cy, r, ramp, o = {}) {
  ramp = ramp.map(col); const n = ramp.length - 1, lx = o.lx ?? -.55, ly = o.ly ?? -.65, lz = Math.sqrt(Math.max(.05, 1 - lx * lx - ly * ly));
  const sx = _r(cx - VX), sy = _r(cy - VY);
  circf(cx, cy, r, inkFn((x, y) => {
    const nx = (x - sx) / (r + .5), ny = (y - sy) / (r + .5), nz = Math.sqrt(Math.max(0, 1 - nx * nx - ny * ny));
    const v = clamp((nx * lx + ny * ly + nz * lz) * (o.contrast ?? 1.1) + (o.bias ?? 0)) * n, i = Math.min(n - 1, v | 0);
    return bay(x, y) < v - i ? ramp[i + 1] : ramp[i];
  }));
}
// Glow: remap what's underneath through a table, strongest (k steps) at the centre, fading out to radius r.
// o: tab (LIT), k (steps at centre, default 1.6), pow (falloff, default 1.6), ry (vertical radius)
function glow(cx, cy, r, o = {}) {
  const tab = o.tab ?? LIT, k = o.k ?? 1.6, pw = o.pow ?? 1.6, ry = o.ry ?? r;
  const sx = cx - VX, sy = cy - VY, x0 = Math.max(CX0, Math.floor(sx - r)), x1 = Math.min(CX1, Math.ceil(sx + r)), y0 = Math.max(CY0, Math.floor(sy - ry)), y1 = Math.min(CY1, Math.ceil(sy + ry));
  for (let y = y0; y <= y1; y++) {
    const row = y * LW, br = (y & 7) << 3, dy = (y - sy) / ry;
    for (let x = x0; x <= x1; x++) {
      const dx = (x - sx) / r, d = dx * dx + dy * dy; if (d >= 1) continue;
      let v = k * (1 - Math.sqrt(d)) ** pw, i = row + x, c = FB[i];
      while (v >= 1) { c = tab[c]; v -= 1; }
      if (v > 0 && BAYER[br | (x & 7)] < v) c = tab[c];
      FB[i] = c;
    }
  }
}
// Whole-frame tint: fadeAll(1.5) dims everything 1.5 steps (dithered); fadeAll(k, LIT) brightens. Respects clipRect.
function fadeAll(k, tab = DIM) { if (k > 0) for (let y = CY0; y <= CY1; y++) _sp(y, CX0, CX1, tint(tab, k)); }
// Fill everything OUTSIDE a circle (telescope/iris vignettes).
function outsideCircle(cx, cy, r, ink) {
  const sx = _r(cx - VX), sy = _r(cy - VY), rr = r * r + r * .8;
  for (let y = CY0; y <= CY1; y++) { const q = rr - (y - sy) ** 2; if (q < 0) { _sp(y, CX0, CX1, ink); continue; } const hw = Math.floor(Math.sqrt(q)); _sp(y, CX0, sx - hw - 1, ink); _sp(y, sx + hw + 1, CX1, ink); }
}

// =====================================================================================================
// LAYERS (cache static art) and FRAME COPIES
// =====================================================================================================
// layer(key, fn): the first call runs fn() and remembers exactly which pixels it painted; later calls just stamp them.
// Use it for anything static that costs more than a millisecond (skies, towns, detailed props). The key must capture
// every parameter the drawing depends on. Drawn with view(0, 0); position it through your key/parameters.
const _layers = new Map();
function layer(key, fn) {
  let L = _layers.get(key);
  if (!L) {
    _FB3.set(FB); FB.fill(CLEAR);
    const vx = VX, vy = VY, c = [CX0, CY0, CX1, CY1]; VX = VY = 0; noClip();
    try { fn(); } finally { VX = vx; VY = vy; [CX0, CY0, CX1, CY1] = c; }
    L = FB.slice(); FB.set(_FB3);
    _layers.set(key, L); if (_layers.size > 64) _layers.delete(_layers.keys().next().value);
  }
  if (CX0 === 0 && CY0 === 0 && CX1 === LW - 1 && CY1 === LH - 1) { for (let i = 0; i < L.length; i++) { const v = L[i]; if (v !== CLEAR) FB[i] = v; } return; }
  for (let y = CY0; y <= CY1; y++) for (let x = CX0, i = y * LW + CX0; x <= CX1; x++, i++) { const v = L[i]; if (v !== CLEAR) FB[i] = v; }
}
// crossfade(k, drawA, drawB): paint two sub-shots and mix them with the ordered-dither dissolve (k = 0 all A … 1 all B).
// For cuts inside one window (chorus sub-shots). Both functions paint the whole frame; each starts from the same view/clip.
function crossfade(k, drawA, drawB) {
  if (k <= 0) return drawA(); if (k >= 1) return drawB();
  const vx = VX, vy = VY, c = [CX0, CY0, CX1, CY1];
  drawA(); const A = FB.slice();
  VX = vx; VY = vy; [CX0, CY0, CX1, CY1] = c;
  drawB();
  for (let y = 0; y < LH; y++) { const row = y * LW, br = (y & 7) << 3; for (let x = 0; x < LW; x++) if (BAYER[br | (x & 7)] >= k) FB[row + x] = A[row + x]; }
  VX = vx; VY = vy; [CX0, CY0, CX1, CY1] = c;
}
// Mirror the rows above `y` into the rows below it (a lake). o: wave (px of wobble), t, tab (DIM), k (dim steps), gap (lines)
function reflect(y, o = {}) {
  y = _r(y - VY); const t = o.t ?? T, amp = o.wave ?? 1.5, k = o.k ?? 1, tab = o.tab ?? DIM, y1 = Math.min(CY1, o.to ?? LH - 1);
  _FB2.set(FB);
  for (let yy = Math.max(y, CY0); yy <= y1; yy++) {
    const d = yy - y, src = y - 1 - Math.floor(d * (o.squash ?? 1)); if (src < 0) continue;
    const off = Math.round(Math.sin(yy * .9 + t * 2.2) * amp * Math.min(1, d / 6 + .3));
    const row = yy * LW, srow = src * LW, br = (yy & 7) << 3;
    for (let x = CX0; x <= CX1; x++) {
      let c = _FB2[srow + clamp(x + off, 0, LW - 1)];
      let v = k + d * (o.fade ?? .02); while (v >= 1) { c = tab[c]; v -= 1; } if (v > 0 && BAYER[br | (x & 7)] < v) c = tab[c];
      FB[row + x] = c;
    }
  }
}

// =====================================================================================================
// TIME: slow beats (the felt pulse, ~75 BPM), sections, seasons
// =====================================================================================================
// The beat tracker's 150 BPM grid drifts against this track, so the slow beats are baked from the audio (every other tracked beat).
const SLOW_BEATS = [
  0.482, 1.318, 2.107, 2.897, 3.686, 4.476, 5.265, 6.054, 6.844, 7.633, 8.423, 9.212, 10.002, 10.791, 11.581, 12.37, 13.16, 13.926, 14.692, 15.482,
  16.271, 17.061, 17.827, 18.57, 19.36, 20.172, 20.962, 21.798, 22.587, 23.4, 24.166, 24.932, 25.745, 26.604, 27.44, 28.276, 29.089, 29.878, 30.714, 31.504,
  32.316, 33.129, 33.942, 34.754, 35.567, 36.38, 37.169, 37.959, 38.795, 39.584, 40.42, 41.233, 42.045, 42.835, 43.624, 44.414, 45.25, 46.062, 46.852, 47.665,
  48.454, 49.267, 50.08, 50.869, 51.682, 52.494, 53.307, 54.097, 54.886, 55.699, 56.488, 57.301, 58.09, 58.833, 59.6, 60.343, 61.109, 61.898, 62.665, 63.431,
  64.22, 65.01, 65.776, 66.612, 67.425, 68.238, 69.027, 69.84, 70.652, 71.442, 72.231, 73.021, 73.834, 74.646, 75.436, 76.248, 77.038, 77.851, 78.663, 79.453,
  80.265, 81.055, 81.868, 82.68, 83.47, 84.283, 85.072, 85.885, 86.674, 87.487, 88.276, 89.089, 89.879, 90.691, 91.481, 92.293, 93.083, 93.896, 94.685, 95.498,
  96.287, 97.1, 97.889, 98.679, 99.468, 100.281, 101.071, 101.86, 102.673, 103.462, 104.252, 105.064, 105.854, 106.667, 107.456, 108.246, 109.035, 109.824, 110.637, 111.45,
  112.239, 113.029, 113.818, 114.631, 115.42, 116.21, 116.999, 117.789, 118.602, 119.414, 120.204, 120.993, 121.783, 122.572, 123.385, 124.174, 124.964, 125.753, 126.566, 127.356,
  128.145, 128.958, 129.747, 130.537, 131.326, 132.116, 132.905, 133.718, 134.507, 135.297, 136.109, 136.899, 137.688, 138.478, 139.267, 140.057, 140.846, 141.613, 142.402, 143.192,
  143.981, 144.794, 145.583, 146.373, 147.162, 147.975, 148.764, 149.554, 150.367, 151.156, 151.969, 152.758, 153.548, 154.36, 155.15, 155.963, 156.752, 157.565, 158.354, 159.167,
  159.956, 160.746, 161.559, 162.348, 163.137, 163.95, 164.74, 165.552, 166.342, 167.155, 167.944, 168.757, 169.546, 170.336, 171.125, 171.938, 172.727, 173.54, 174.329, 175.119,
  175.932, 176.721, 177.534, 178.323, 179.136, 179.926, 180.715, 181.504, 182.294, 183.107, 183.896, 184.686, 185.498, 186.288, 187.1, 187.89, 188.679, 189.492, 190.305, 191.094,
  191.884, 192.696, 193.486, 194.252, 195.088, 195.878, 196.69, 197.48, 198.269, 199.082, 199.871, 200.661, 201.45, 202.263, 203.053, 203.842, 204.632, 205.444, 206.234, 207.046,
  207.836, 208.625, 209.415, 210.204, 210.994, 211.807, 212.596, 213.385, 214.175, 214.988, 215.777, 216.567, 217.356, 218.146, 218.935, 219.725, 220.514, 221.35, 222.139, 222.929,
  223.742, 224.531, 225.344, 226.133, 226.923, 227.712, 228.525, 229.314, 230.104, 230.917, 231.729, 232.519, 233.308, 234.121, 234.91, 235.7, 236.489, 237.302, 238.091, 238.881,
  239.67, 240.46, 241.273, 242.062, 242.852, 243.641, 244.431, 245.243, 246.033, 246.822, 247.635, 248.424, 249.214, 250.003, 250.793, 251.606, 252.395, 253.184, 253.974, 254.763,
  255.553, 256.342, 257.132, 257.921, 258.711, 259.524, 260.313, 261.102, 261.892, 262.681, 263.471, 264.26, 265.05, 265.839, 266.629, 267.418, 268.208, 268.997, 269.787, 270.599,
  271.412, 272.202, 272.991, 273.804, 274.593, 275.406, 276.219, 277.008, 277.798, 278.61, 279.4, 280.212, 281.002, 281.791, 282.604, 283.417, 284.206, 284.996, 285.785, 286.598,
  287.411, 288.223, 289.013, 289.802, 290.592, 291.405, 292.171, 292.937, 293.703, 294.516, 295.329, 296.141, 296.977, 297.813, 298.603, 299.439, 300.251, 301.041, 301.853, 302.643,
  303.456, 304.245, 305.058, 305.847, 306.66, 307.449, 308.262, 309.052, 309.841, 310.654, 311.443, 312.256, 313.046, 313.858, 314.648, 315.46, 316.25, 317.039, 317.852, 318.642,
  319.454, 320.244, 321.033, 321.753, 322.519, 323.286, 324.052, 324.841, 325.631, 326.397, 327.186, 327.929, 328.719, 329.532, 330.368, 331.157, 331.993, 332.806, 333.618, 334.431,
  335.244, 336.056, 336.892, 337.705, 338.495, 339.238, 339.981, 340.77,
];
const _slowOK = Math.abs(DUR - 343.60) < .5;   // another take → fall back to the tracker grid
// sbp(t): slow-beat position (float; integer on each felt beat). sbeat(t): its floor. sbeatT(n): time of slow beat n (fractional n ok).
function sbp(t) {
  if (!_slowOK) return bpOf(t) / 2;
  const S = SLOW_BEATS, n = S.length;
  if (t < S[0]) return (t - S[0]) / .8;
  if (t >= S[n - 1]) return n - 1 + (t - S[n - 1]) / .8;
  let lo = 0, hi = n - 1; while (hi - lo > 1) { const m = (lo + hi) >> 1; if (S[m] <= t) lo = m; else hi = m; }
  return lo + (t - S[lo]) / (S[lo + 1] - S[lo]);
}
const sbeat = t => Math.floor(sbp(t));
function sbeatT(n) {
  if (!_slowOK) return onBeat(0, n * 2);
  const S = SLOW_BEATS, L = S.length, i = Math.floor(n), f = n - i;
  const at = k => k < 0 ? S[0] + k * .8 : k >= L ? S[L - 1] + (k - L + 1) * .8 : S[k];
  return f ? lerp(at(i), at(i + 1), f) : at(i);
}
const spulse = (t, k = 4) => Math.exp(-frac(sbp(t)) * k);                           // 1 on each slow beat, decays
const breathe = (t, per = 2, ph = 0) => .5 - .5 * Math.cos((sbp(t) / per + ph) * TAU); // 0..1 swell, one cycle per `per` slow beats
// Slow beats inside a window, as lt offsets: beatsIn(seg) → [0.05, 0.88, 1.70, 2.52]. beatAt(seg, i): lt of the window's i-th slow beat
// (i may be fractional, 1.5 = halfway between beats 1 and 2; extrapolates past the end).
function beatsIn(s) { const out = []; for (let n = Math.ceil(sbp(s.start) - 1e-6); ; n++) { const bt = sbeatT(n); if (bt >= s.end) break; out.push(bt - s.start); } return out; }
function beatAt(s, i) { const n0 = Math.ceil(sbp(s.start) - 1e-6); return sbeatT(n0 + i) - s.start; }
// Rise 0→1 starting at lt0 over dur (eased). The workhorse for slow reveals: k = rise(lt, beatAt(seg, 1), .6).
const rise = (lt, lt0, dur = .5, fn = ease) => fn(clamp((lt - lt0) / dur));

// Section and colour script. skyRamp(t) is the default sky from zenith to horizon glow; it slowly warms toward dawn over the song.
function sectionAt(t) { const s = segAt(t); return s ? s.sec : 'intro'; }
const SKY_RAMPS = {
  cool: [C.void, C.ink, C.night, C.navy, C.dusk],                    // intro, V1, C1
  glow: [C.void, C.ink, C.night, C.navy, C.violet],                  // V2, C2: the city's light on the horizon
  late: [C.void, C.ink, C.night, C.navy, C.violet, C.wine],          // V3, C3
  predawn: [C.ink, C.night, C.navy, C.violet, C.rust],               // V4
  dawn: [C.night, C.navy, C.violet, C.rust, C.clay, C.amber],        // C4
  day: [C.navy, C.dusk, C.violet, C.rust, C.clay, C.amber, C.gold],  // outro
};
function skyRamp(t = T) {
  const s = sectionAt(t);
  return SKY_RAMPS[{ intro: 'cool', V1: 'cool', C1: 'cool', V2: 'glow', C2: 'glow', V3: 'late', C3: 'late', V4: 'predawn', C4: 'dawn', outro: 'day' }[s] || 'cool'];
}
// Seasons from the date ticker ("NOV 30 2022" → autumn). weather(t, 'auto') uses it.
function seasonOf(date) {
  if (!date) return 'none';
  if (/SUMMER/.test(date)) return 'summer';
  const m = (date.match(/^[A-Z]{3}/) || [''])[0];
  return { DEC: 'winter', JAN: 'winter', FEB: 'winter', MAR: 'spring', APR: 'spring', MAY: 'spring', JUN: 'summer', JUL: 'summer', AUG: 'summer', SEP: 'autumn', OCT: 'autumn', NOV: 'autumn' }[m] || 'none';
}
const seasonAt = t => { const d = dateAt(t); return seasonOf(d && d.text); };

// =====================================================================================================
// PIXEL FONTS: F5 (5×7, lowercase with descenders; captions, signs) and F3 (3×5 caps; labels, tiny text)
// =====================================================================================================
const _F5_SRC = `
A .###. #...# #...# ##### #...# #...# #...#
B ####. #...# #...# ####. #...# #...# ####.
C .###. #...# #.... #.... #.... #...# .###.
D ####. #...# #...# #...# #...# #...# ####.
E ##### #.... #.... ####. #.... #.... #####
F ##### #.... #.... ####. #.... #.... #....
G .###. #...# #.... #.### #...# #...# .###.
H #...# #...# #...# ##### #...# #...# #...#
I ### .#. .#. .#. .#. .#. ###
J ...# ...# ...# ...# #..# #..# .##.
K #...# #..#. #.#.. ##... #.#.. #..#. #...#
L #.... #.... #.... #.... #.... #.... #####
M #...# ##.## #.#.# #.#.# #...# #...# #...#
N #...# #...# ##..# #.#.# #..## #...# #...#
O .###. #...# #...# #...# #...# #...# .###.
P ####. #...# #...# ####. #.... #.... #....
Q .###. #...# #...# #...# #.#.# #..#. .##.#
R ####. #...# #...# ####. #.#.. #..#. #...#
S .###. #...# #.... .###. ....# #...# .###.
T ##### ..#.. ..#.. ..#.. ..#.. ..#.. ..#..
U #...# #...# #...# #...# #...# #...# .###.
V #...# #...# #...# #...# #...# .#.#. ..#..
W #...# #...# #...# #.#.# #.#.# #.#.# .#.#.
X #...# #...# .#.#. ..#.. .#.#. #...# #...#
Y #...# #...# .#.#. ..#.. ..#.. ..#.. ..#..
Z ##### ....# ...#. ..#.. .#... #.... #####
a ..... ..... .###. ....# .#### #...# .####
b #.... #.... #.##. ##..# #...# #...# ####.
c .... .... .### #... #... #... .###
d ....# ....# .##.# #..## #...# #...# .####
e ..... ..... .###. #...# ##### #.... .###.
f ..## .#.. .#.. ###. .#.. .#.. .#..
g ..... ..... .#### #...# #...# #...# .#### ....# .###.
h #.... #.... #.##. ##..# #...# #...# #...#
i .#. ... ##. .#. .#. .#. ###
j ..# ... .## ..# ..# ..# ..# #.# .#.
k #... #... #..# #.#. ##.. #.#. #..#
l ##. .#. .#. .#. .#. .#. ###
m ..... ..... ##.#. #.#.# #.#.# #.#.# #.#.#
n ..... ..... #.##. ##..# #...# #...# #...#
o ..... ..... .###. #...# #...# #...# .###.
p ..... ..... ####. #...# #...# #...# ####. #.... #....
q ..... ..... .#### #...# #...# #...# .#### ....# ....#
r .... .... #.## ##.. #... #... #...
s ..... ..... .#### #.... .###. ....# ####.
t .#.. .#.. #### .#.. .#.. .#.. ..##
u ..... ..... #...# #...# #...# #..## .##.#
v ..... ..... #...# #...# #...# .#.#. ..#..
w ..... ..... #...# #...# #.#.# #.#.# .#.#.
x ..... ..... #...# .#.#. ..#.. .#.#. #...#
y ..... ..... #...# #...# #...# #...# .#### ....# .###.
z ..... ..... ##### ...#. ..#.. .#... #####
0 .###. #...# #..## #.#.# ##..# #...# .###.
1 ..#.. .##.. ..#.. ..#.. ..#.. ..#.. .###.
2 .###. #...# ....# ...#. ..#.. .#... #####
3 ####. ....# ....# .###. ....# ....# ####.
4 ...#. ..##. .#.#. #..#. ##### ...#. ...#.
5 ##### #.... ####. ....# ....# #...# .###.
6 .###. #.... #.... ####. #...# #...# .###.
7 ##### ....# ...#. ..#.. .#... .#... .#...
8 .###. #...# #...# .###. #...# #...# .###.
9 .###. #...# #...# .#### ....# ....# .###.
. . . . . . . #
, .. .. .. .. .. .# .# #.
! # # # # # . #
? .###. #...# ....# ...#. ..#.. ..... ..#..
' # # . . . . .
" #.# #.# ... ... ... ... ...
- .... .... .... #### .... .... ....
— ..... ..... ..... ##### ..... ..... .....
: . . # . . # .
; .. .. .# .. .. .# .# #.
( ..# .#. #.. #.. #.. .#. ..#
) #.. .#. ..# ..# ..# .#. #..
/ ....# ....# ...#. ..#.. .#... #.... #....
& .##.. #..#. #.#.. .#... #.#.# #..#. .##.#
$ ..#.. .#### #.#.. .###. ..#.# ####. ..#..
% ##... ##..# ...#. ..#.. .#... #..## ...##
+ ..... ..#.. ..#.. ##### ..#.. ..#.. .....
= ..... ..... ##### ..... ##### ..... .....
# .#.#. .#.#. ##### .#.#. ##### .#.#. .#.#.
* ..... ..#.. #.#.# .###. #.#.# ..#.. .....
… ..... ..... ..... ..... ..... ..... #.#.#
♥ ..... .#.#. ##### ##### .###. ..#.. .....
× ..... #...# .#.#. ..#.. .#.#. #...# .....
@ .###. #...# #.### #.#.# #.### #.... .####
< ...# ..#. .#.. #... .#.. ..#. ...#
> #... .#.. ..#. ...# ..#. .#.. #...
[ ### #.. #.. #.. #.. #.. ###
] ### ..# ..# ..# ..# ..# ###
_ ..... ..... ..... ..... ..... ..... #####
^ .#. #.# ... ... ... ... ...
→ ..... ..#.. ...#. ##### ...#. ..#.. .....
← ..... ..#.. .#... ##### .#... ..#.. .....
↑ ..#.. .###. #.#.# ..#.. ..#.. ..#.. ..#..
↓ ..#.. ..#.. ..#.. ..#.. #.#.# .###. ..#..
✓ ..... ....# ...#. #.#.. .#... ..... .....
★ ..#.. ..#.. ##### .###. .#.#. #...# .....
~ ..... ..... .#... #.#.# ...#. ..... .....
· . . . # . . .
`;
const _F3_SRC = `
A .#. #.# ### #.# #.#
B ##. #.# ##. #.# ##.
C .## #.. #.. #.. .##
D ##. #.# #.# #.# ##.
E ### #.. ##. #.. ###
F ### #.. ##. #.. #..
G .## #.. #.# #.# .##
H #.# #.# ### #.# #.#
I ### .#. .#. .#. ###
J ..# ..# ..# #.# .#.
K #.# #.# ##. #.# #.#
L #.. #.. #.. #.. ###
M #...# ##.## #.#.# #...# #...#
N #..# ##.# #.## #..# #..#
O .#. #.# #.# #.# .#.
P ##. #.# ##. #.. #..
Q .#. #.# #.# ##. .##
R ##. #.# ##. #.# #.#
S .## #.. .#. ..# ##.
T ### .#. .#. .#. .#.
U #.# #.# #.# #.# ###
V #.# #.# #.# #.# .#.
W #...# #...# #.#.# ##.## #...#
X #.# #.# .#. #.# #.#
Y #.# #.# .#. .#. .#.
Z ### ..# .#. #.. ###
0 ### #.# #.# #.# ###
1 .#. ##. .#. .#. ###
2 ##. ..# .#. #.. ###
3 ##. ..# .#. ..# ##.
4 #.# #.# ### ..# ..#
5 ### #.. ##. ..# ##.
6 .## #.. ### #.# ###
7 ### ..# .#. .#. .#.
8 ### #.# ### #.# ###
9 ### #.# ### ..# ##.
. . . . . #
, .. .. .. .# #.
! # # # . #
? ##. ..# .#. ... .#.
' # # . . .
" #.# #.# ... ... ...
- ... ... ### ... ...
— .... .... #### .... ....
: . # . # .
; .. .# .. .# #.
( .# #. #. #. .#
) #. .# .# .# #.
/ ..# ..# .#. #.. #..
+ ... .#. ### .#. ...
= ... ### ... ### ...
% #.# ..# .#. #.. #.#
$ .## ##. .#. .## ##.
# #.# ### #.# ### #.#
& .#. #.# .#. #.# .##
* #.# .#. #.# ... ...
× ... #.# .#. #.# ...
♥ .#.#. ##### ##### .###. ..#..
… ..... ..... ..... ..... #.#.#
✓ ... ..# ..# #.# .#.
→ .... ..#. #### ..#. ....
← .... .#.. #### .#.. ....
↑ .#. ### .#. .#. .#.
^ .#. #.# ... ... ...
_ ... ... ... ... ###
< ..# .#. #.. .#. ..#
> #.. .#. ..# .#. #..
[ ## #. #. #. ##
] ## .# .# .# ##
~ .... .#.# #.#. .... ....
· . . # . .
`;
function _parseFont(src, h, spaceW) {
  const F = { _h: h, ' ': { w: spaceW, rows: [] } };
  for (const raw of src.split('\n')) {
    const s = raw.trim(); if (!s) continue;
    const cps = [...s], ch = cps[0], rows = cps.slice(1).join('').trim().split(/\s+/);
    F[ch] = { w: rows[0].length, rows: rows.map(r => [...r].map(c => c === '#' ? 1 : 0)) };
  }
  return F;
}
const F5 = _parseFont(_F5_SRC, 7, 3), F3 = _parseFont(_F3_SRC, 5, 2);
const _GLYPH_ALIAS = { '“': '"', '”': '"', '„': '"', '‘': "'", '’': "'", 'ʼ': "'", '–': '-', '‑': '-', 'é': 'e', 'É': 'E', 'ö': 'o', 'ü': 'u', 'á': 'a', 'ó': 'o', 'í': 'i', 'ñ': 'n' };
function _glyph(F, ch) {
  if (F[ch]) return F[ch];
  const a = _GLYPH_ALIAS[ch]; if (a && F[a]) return F[a];
  const u = ch.toUpperCase(); if (F[u]) return F[u];
  const l = ch.toLowerCase(); if (F[l]) return F[l];
  return F['?'];
}
function _fontOf(o) { return o && (o.font === 3 || o.font === 'F3') ? F3 : F5; }
// Width in pixels of one line of text.
function ptextW(str, o = {}) {
  const F = _fontOf(o), s = o.scale || 1, gap = o.gap ?? 1; let w = 0, n = 0;
  for (const ch of String(str)) { w += (_glyph(F, ch).w + gap) * s; n++; }
  return n ? w - gap * s : 0;
}
function _wrapText(str, o) {
  const out = []; for (const para of String(str).split('\n')) {
    let cur = ''; for (const word of para.split(' ')) { const tryS = cur ? cur + ' ' + word : word; if (cur && ptextW(tryS, o) > o.maxW) { out.push(cur); cur = word; } else cur = tryS; }
    out.push(cur);
  }
  return out;
}
// ptext(str, x, y, ink, o): draw pixel text with its top-left (cap top) at (x, y). Returns the widest line's width.
// o: font (5 | 3), scale (int), align ('left'|'center'|'right'), gap (px between glyphs, default 1), lineH,
//    shadow (ink: 1-px drop shadow down-right), outline (ink: 1-px ring), dots (dot-matrix: each font pixel becomes a
//    (scale-1)² dot with a gap; needs scale ≥ 2), off (ink for unlit dot-matrix cells), n (show only the first n chars: typing),
//    maxW (wrap), each(i, ch, x, y) → {dx, dy, ink} | falsy (per-letter animation hook)
function ptext(str, x, y, ink, o = {}) {
  const F = _fontOf(o), s = o.scale || 1, gap = o.gap ?? 1, lines = o.maxW ? _wrapText(str, o) : String(str).split('\n');
  const lh = (o.lineH ?? (F._h + (F === F5 ? 4 : 2))) * s;
  let left = o.n ?? Infinity, maxw = 0, idx = 0;
  const stamp = (g, gx, gy, ik, dots) => {
    for (let r = 0; r < g.rows.length; r++) {
      const row = g.rows[r];
      for (let c = 0; c < row.length; c++) {
        if (row[c]) rectf(gx + c * s, gy + r * s, dots ? s - 1 : s, dots ? s - 1 : s, ik);
        else if (o.off !== undefined && dots && r < F._h) rectf(gx + c * s, gy + r * s, s - 1, s - 1, o.off);
      }
    }
  };
  lines.forEach((ln, li) => {
    const w = ptextW(ln, o); maxw = Math.max(maxw, w);
    let cx = Math.round(o.align === 'center' ? x - w / 2 : o.align === 'right' ? x - w : x);
    const cy = Math.round(y + li * lh);
    for (const ch of ln) {
      if (left-- <= 0) return;
      const g = _glyph(F, ch);
      let gx = cx, gy = cy, ik = ink;
      if (o.each) { const e = o.each(idx, ch, cx, cy); if (e === false) { cx += (g.w + gap) * s; idx++; continue; } if (e) { gx += e.dx ?? 0; gy += e.dy ?? 0; if (e.ink !== undefined) ik = e.ink; } }
      if (o.outline !== undefined) for (const [dx, dy] of [[-1, 0], [1, 0], [0, -1], [0, 1], [-1, -1], [1, -1], [-1, 1], [1, 1]]) stamp(g, gx + dx, gy + dy, o.outline, false);
      if (o.shadow !== undefined) stamp(g, gx + 1, gy + 1, o.shadow, o.dots && s > 1);
      stamp(g, gx, gy, ik, o.dots && s > 1);
      cx += (g.w + gap) * s; idx++;
    }
  });
  return maxw;
}
// Glyph dot positions (for making text out of stars, fireflies, lanterns…): [{x, y, i}] with the pixel centres of every lit dot.
function textDots(str, x, y, o = {}) {
  const F = _fontOf(o), s = o.scale || 1, gap = o.gap ?? 1, w = ptextW(str, o), out = [];
  let cx = Math.round(o.align === 'center' ? x - w / 2 : o.align === 'right' ? x - w : x), ci = 0;
  for (const ch of String(str)) { const g = _glyph(F, ch); g.rows.forEach((row, r) => row.forEach((on, c) => { if (on) out.push({ x: cx + c * s, y: y + r * s, i: ci }); })); cx += (g.w + gap) * s; ci++; }
  return out;
}

// =====================================================================================================
// SPRITES: rows of hex digits (palette indices 0–f), '.' transparent. Custom legends map other characters.
// =====================================================================================================
function sprite(src, legend) {
  const rows = (Array.isArray(src) ? src : src.split('\n')).map(r => r.replace(/\s+/g, '')).filter(r => r.length);
  const h = rows.length, w = Math.max(...rows.map(r => r.length)), d = new Int16Array(w * h).fill(-1);
  rows.forEach((r, y) => [...r].forEach((ch, x) => {
    let v = legend && ch in legend ? col(legend[ch]) : ch === '.' ? -1 : parseInt(ch, 16);
    if (v >= 0 && !isNaN(v)) d[y * w + x] = v;
  }));
  return { w, h, d };
}
// spr(S, x, y, o): top-left at (x, y). o: flip, flipY, ink (paint every pixel this ink: silhouettes), map ({from: to} or table),
// k (veil coverage 0..1 for dithered fades), scale (integer; avoid mixing scales in one shot), center (x is the centre), bottom (y is the bottom)
function spr(S, x, y, o = {}) {
  const sc = o.scale || 1;
  if (o.center) x -= (S.w * sc) / 2; if (o.bottom) y -= S.h * sc;
  x = _r(x); y = _r(y);
  const map = o.map, k = o.k ?? 1;
  for (let j = 0; j < S.h; j++) for (let i = 0; i < S.w; i++) {
    let v = S.d[(o.flipY ? S.h - 1 - j : j) * S.w + (o.flip ? S.w - 1 - i : i)]; if (v < 0) continue;
    if (map) v = map[v] ?? v; if (o.ink !== undefined) v = col(o.ink);
    const px = x + i * sc, py = y + j * sc;
    if (k < 1 && bay(px - VX, py - VY) >= k) continue;
    if (sc === 1) pset(px, py, v); else rectf(px, py, sc, sc, v);
  }
}

// =====================================================================================================
// NOISE & SHAPES
// =====================================================================================================
function noise1(x, seed = 0) { const i = Math.floor(x), f = x - i, u = f * f * (3 - 2 * f); return lerp(hash2(i, seed), hash2(i + 1, seed), u); }
// Ridge line height at x: y ± amp, smooth multi-octave noise. o: y, amp, freq (default 1/60), seed.
function ridgeY(x, o = {}) { const f = o.freq ?? 1 / 60, s = o.seed ?? 1; return (o.y ?? 200) - (o.amp ?? 12) * (noise1(x * f, s) * .62 + noise1(x * f * 2.3, s + 9) * .28 + noise1(x * f * 5.1, s + 17) * .1); }

// =====================================================================================================
// SKY
// =====================================================================================================
// sky(o): the dithered night gradient (cached). Radial glow around (cx, cy) plus a vertical falloff; ramp from zenith to glow.
// o: ramp (default skyRamp(T)), cx, cy (glow centre, default below the horizon), r (glow radius), vert (0..1 weight of the
//    vertical term), dy (tilt: shift the whole gradient down by dy px), squash (horizontal stretch of the radial glow)
function sky(o = {}) {
  const ramp = (o.ramp || skyRamp(T)).map(col), cx = o.cx ?? 240, cy = o.cy ?? 300, r = o.r ?? 360, vert = o.vert ?? .35, dy = _r(o.dy ?? 0), sq = o.squash ?? .7, top = o.top ?? 0, hy = o.hy ?? 230;
  layer(`sky|${ramp}|${cx}|${cy}|${r}|${vert}|${dy}|${sq}|${top}|${hy}`, () => {
    rectf(0, 0, LW, LH, grad(ramp, (x, y) => {
      const d = Math.hypot((x - cx) * sq, y - dy - cy) / r, v = clamp((y - dy - top) / (hy - top));
      return clamp((1 - d) * (1 - vert) * 1.25 + v * vert);
    }));
  });
}
// The sky slowly turns all song long (stars drift left→right around a pole above the frame).
const SKY_POLE = [240, -250];
const skyRot = t => t * .0032;
const _STARS = (() => {
  const a = []; for (let i = 0; i < 1100; i++) {
    const r = Math.sqrt(lerp(200 * 200, 660 * 660, hash2(i, 1))), ang = lerp(-2.3, 1.25, hash2(i, 2)), m = hash2(i, 3);
    a.push({ r, ang, cls: m < .035 ? 3 : m < .11 ? 2 : m < .4 ? 1 : 0, ph: hash2(i, 4), tw: hash2(i, 5) });
  }
  return a;
})();
// sparkle(x, y, size, ink, arm): the cream 4-point twinkle. size 0 = 1 px, 1 = plus, 2 = long plus, 3 = plus + diagonals.
function sparkle(x, y, size = 1, ink = C.cream, arm = C.haze) {
  x = _r(x); y = _r(y);
  if (size >= 2) { pset(x - 2, y, arm); pset(x + 2, y, arm); pset(x, y - 2, arm); pset(x, y + 2, arm); }
  if (size >= 3) { pset(x - 3, y, arm); pset(x + 3, y, arm); pset(x, y - 3, arm); pset(x, y + 3, arm); pset(x - 1, y - 1, arm); pset(x + 1, y - 1, arm); pset(x - 1, y + 1, arm); pset(x + 1, y + 1, arm); }
  if (size >= 1) { const c2 = size >= 2 ? ink : arm; pset(x - 1, y, c2); pset(x + 1, y, c2); pset(x, y - 1, c2); pset(x, y + 1, c2); }
  pset(x, y, ink);
}
// starfield(t, o): ~150 stars on the turning sky; they twinkle on the slow beat. o: density (0..1, default 1), y1 (no stars
// below this screen y), dy (tilt offset), rot (extra rotation), appear (0..1: stars fade in brightest-first), seed, bright (0..1 twinkle amount)
function starfield(t, o = {}) {
  const [px, py] = SKY_POLE, rot = skyRot(t) + (o.rot ?? 0), dy = o.dy ?? 0, y1 = o.y1 ?? LH, dens = o.density ?? 1, ap = o.appear ?? 1, sb = sbeat(t), sp = spulse(t, 3), seed = o.seed ?? 0;
  const vx = VX, vy = VY; VX = 0; VY = 0;
  for (let i = 0; i < _STARS.length; i++) {
    const S = _STARS[i];
    if (S.tw > dens) continue;
    const a = S.ang + rot, x = Math.round(px + Math.sin(a) * S.r), y = Math.round(py + Math.cos(a) * S.r + dy);
    if (x < -3 || x > LW + 3 || y < -3 || y > y1) continue;
    const order = (S.cls + hash2(i, 9 + seed)) / 4;               // brightest stars appear first
    if (ap < 1 && 1 - order > ap * 1.25) continue;
    const twk = hash2(i * 7 + seed, sb) < (o.bright ?? .16) ? sp : 0; // this star's twinkle on this slow beat
    const lvl = S.cls + (twk > .45 ? 1 : 0);
    if (lvl === 0) pset(x, y, C.dusk);
    else if (lvl === 1) pset(x, y, S.ph < .5 ? C.haze : C.dusk);
    else if (lvl === 2) pset(x, y, C.cream);
    else if (lvl === 3) sparkle(x, y, S.ph < .7 ? 0 : 1);
    else sparkle(x, y, breathe(t, 2, S.ph) > .5 ? 2 : 1);
  }
  VX = vx; VY = vy;
}
// A shooting star from (x0, y0) toward (x1, y1); k = 0..1 progress. o: len (trail px), ink
function shootingStar(x0, y0, x1, y1, k, o = {}) {
  if (k <= 0 || k >= 1) return;
  const e = easeOut(k), hx = lerp(x0, x1, e), hy = lerp(y0, y1, e), len = (o.len ?? 26) * Math.min(1, k * 4) * (1 - k * .5);
  const dx = x1 - x0, dy = y1 - y0, L = Math.hypot(dx, dy) || 1;
  for (let i = 0; i < len; i++) { const f = i / len; pset(hx - dx / L * i, hy - dy / L * i, f < .25 ? C.cream : f < .6 ? veil(C.haze, 1 - f * .8) : veil(C.dusk, .9 - f)); }
  sparkle(hx, hy, k < .8 ? 1 : 0, o.ink ?? C.cream);
}
// The moon. o: phase (0 full → .9 thin crescent, lit side right), glow (0..1), ramp
function moon(x, y, r, o = {}) {
  if (o.glow !== 0) glow(x, y, r * 3.2, { k: (o.glow ?? 1) * 1.2, pow: 2 });
  const ph = o.phase ?? .55, ox = x - r * 2 * ph, sx = _r(x - VX), sy = _r(y - VY), rr = r * r + r * .8, cut = _r(ox - VX);
  const ramp = (o.ramp || [C.gold, C.cream]).map(col);
  circf(x, y, r, inkFn((px, py) => {
    if (ph > 0 && (px - cut) ** 2 + (py - sy) ** 2 <= rr) return -1;
    const lvl = clamp(.5 + (px - sx) / r * .4 - (py - sy) / r * .3);
    return bay(px, py) < lvl ? ramp[1] : ramp[0];
  }));
}

// =====================================================================================================
// THE LEDGER: every verse line leaves a star; the 64 stars rise across the sky as a scaling curve.
// =====================================================================================================
// LEDGER[i] = {key, x, y, i}. ledger(t, o) draws the stars born so far (a star is born when its line starts).
const LEDGER = (() => {
  const keys = SEGS.filter(s => s.kind === 'line'), n = keys.length, out = [];
  keys.forEach((s, i) => {
    const u = (i + .5) / n, e = (Math.exp(3.4 * u) - 1) / (Math.exp(3.4) - 1);
    const bx = 30 + u * 420, by = 188 - e * 160, jit = (hash2(i, 77) - .5) * 16, ang = Math.atan2(-160 * 3.4 * Math.exp(3.4 * u) / (Math.exp(3.4) - 1), 420);
    out.push({ key: s.key, seg: s, i, x: Math.round(bx - Math.sin(ang) * jit), y: Math.round(by + Math.cos(ang) * jit), big: hash2(i, 78) < .3 });
  });
  return out;
})();
const ledgerIndex = key => LEDGER.findIndex(L => L.key === key);
// o: upto (index or key: only stars up to it), links (0..1 dotted constellation lines drawn so far), dx, dy, ink, band (0..1 faint
//    dithered milky-way band along the curve), newborn (true: the newest star flares), pulse (true: stars swell on the slow beat)
function ledger(t, o = {}) {
  const dx = o.dx ?? 0, dy = o.dy ?? 0, lim = typeof o.upto === 'string' ? ledgerIndex(o.upto) : o.upto ?? 999;
  const born = LEDGER.filter(L => L.i <= lim && L.seg.start <= t + 1e-6);
  if (!born.length) return;
  if (o.band) for (let i = 0; i + 1 < born.length; i++) { const a = born[i], b = born[i + 1]; for (let s = 0; s < 6; s++) glow(lerp(a.x, b.x, s / 6) + dx, lerp(a.y, b.y, s / 6) + dy, 14, { tab: LIT, k: o.band * .9, pow: 2 }); }
  if (o.links > 0) {
    const nl = (born.length - 1) * clamp(o.links), whole = Math.floor(nl);
    for (let i = 0; i < whole; i++) pline(born[i].x + dx, born[i].y + dy, born[i + 1].x + dx, born[i + 1].y + dy, o.linkInk ?? C.dusk, { every: 2 });
    if (whole < born.length - 1 && nl > whole) { const a = born[whole], b = born[whole + 1], f = nl - whole; pline(a.x + dx, a.y + dy, lerp(a.x, b.x, f) + dx, lerp(a.y, b.y, f) + dy, o.linkInk ?? C.dusk, { every: 2 }); }
  }
  const sb = sbeat(t);
  born.forEach(L => {
    const age = t - L.seg.start, x = L.x + dx, y = L.y + dy;
    const tw = o.pulse !== false && hash2(L.i, sb) < .25 ? spulse(t, 3) : 0;
    if (o.newborn !== false && age < 1.2) { sparkle(x, y, age < .4 ? 3 : age < .8 ? 2 : 1, C.cream, C.gold); return; }
    if (L.big || tw > .5) sparkle(x, y, 1, o.ink ?? C.cream, C.gold); else pset(x, y, o.ink ?? C.gold);
  });
}

// =====================================================================================================
// LAND, WATER, WEATHER
// =====================================================================================================
// ridge(o): a silhouette from its noisy top edge down to the bottom. Returns the height array (screen x → top y).
// o: y, amp, freq, seed, ink, rim (ink of the 1-px top edge: moonlight), x (scroll offset for parallax), snow (ink of a snow cap), to (bottom y)
function ridge(o = {}) {
  const tops = new Int16Array(LW), ink = o.ink ?? C.ink, sx = o.x ?? 0;
  for (let x = 0; x < LW; x++) {
    const top = Math.round(ridgeY(x + sx + VX, o)) - VY; tops[x] = top;
    _sp(top, x, x, o.rim ?? ink); for (let y = top + 1; y <= (o.to ?? LH - 1) - VY; y++) _sp(y, x, x, ink);
    if (o.snow !== undefined && bay(x, top + 1) < .6) _sp(top + 1, x, x, o.snow);
  }
  return tops;
}
// hill(o): Clawd's rounded hill. Returns groundY(x) (world coords). o: cx, y (summit y), w (half-width at which it has dropped
// `drop` px), drop, ink, rim, snow
function hill(o = {}) {
  const cx = o.cx ?? 120, y = o.y ?? 190, w = o.w ?? 110, drop = o.drop ?? 40, ink = o.ink ?? C.void;
  const gy = x => y + drop * Math.pow(Math.abs(x - cx) / w, 1.8) + (noise1(x * .08, 5) - .5) * 1.4;
  for (let sx = CX0; sx <= CX1; sx++) {
    const wx = sx + VX, top = Math.round(gy(wx)) - VY; if (top > CY1) continue;
    _sp(top, sx, sx, o.rim ?? C.pine); for (let yy = top + 1; yy <= CY1; yy++) _sp(yy, sx, sx, ink);
    if (o.snow !== undefined && bay(sx, top + 1) < .7) _sp(top + 1, sx, sx, o.snow);
  }
  return x => Math.round(gy(x));
}
// Grass tufts along a ground function, swaying on the slow beat. o: ink, step (px between tufts), h (max height), seed
function grass(x0, x1, groundY, t, o = {}) {
  const step = o.step ?? 3, sway = breathe(t, 2) > .5 ? 1 : 0;
  for (let x = Math.ceil(x0 / step) * step; x <= x1; x += step) {
    const h = 1 + Math.floor(hash2(x, o.seed ?? 3) * (o.h ?? 3)), gy = groundY(x) - 1, lean = hash2(x, 4) < .5 ? sway : 0;
    for (let j = 0; j < h; j++) pset(x + (j === h - 1 ? lean : 0), gy - j, o.ink ?? C.pine);
  }
}
// A pine tree silhouette. o: ink, snow (ink), rim (ink of lit edge on the right)
function pineTree(x, y, h, o = {}) {
  const ink = o.ink ?? C.void, tiers = Math.max(2, Math.round(h / 7));
  vline(x, y - 2, y, ink);
  for (let i = 0; i < tiers; i++) {
    const ty = y - 2 - i * (h - 3) / tiers, hw = (tiers - i) * h / tiers * .38 + 1;
    triPx(x - hw, ty, x + hw + 1, ty, x + .5, ty - (h - 3) / tiers * 1.7, ink);
    if (o.snow !== undefined) { hline(x - hw * .6, x - 1, ty - 1, o.snow); }
    if (o.rim !== undefined) pset(x + Math.round(hw * .6), Math.round(ty - 2), o.rim);
  }
}
// A little house. (x, y) = bottom-left. Returns window centres. o: w, h, wall, roof, lit(i) → ink|false (window state), ws (window size, 3; ≥5 gets mullions),
// windows (count), snow (roof ink), chimney (bool: smoke), door (ink|false)
function house(x, y, o = {}) {
  const w = o.w ?? 18, h = o.h ?? 11, wall = o.wall ?? C.night, roof = o.roof ?? C.ink, nw = o.windows ?? 2, wins = [];
  rectf(x, y - h, w, h, wall);
  triPx(x - 2, y - h + .5, x + w + 2, y - h + .5, x + w / 2, y - h - w * .45, roof);
  if (o.snow !== undefined) { for (let i = 0; i < w + 2; i++) { const px = x - 1 + i, py = Math.round(y - h - w * .45 * (1 - Math.abs(i - (w + 2) / 2) / ((w + 2) / 2)) + 1); pset(px, py - 1, o.snow); } }
  if (o.chimney) rectf(x + w * .72, y - h - w * .38, 2, 4, roof);
  for (let i = 0; i < nw; i++) {
    const ws = o.ws ?? 3, wx = Math.round(x + (i + 1) * w / (nw + 1) - ws / 2), wy = y - Math.round(h * .62) - (ws > 3 ? 1 : 0);
    const ink = o.lit ? o.lit(i) : false, on = !(ink === false || ink === undefined);
    rectf(wx, wy, ws, ws, on ? ink : C.void);
    if (ws >= 5) { vline(wx + (ws >> 1), wy, wy + ws - 1, on ? C.cream : C.ink); hline(wx, wx + ws - 1, wy + (ws >> 1), on ? C.cream : C.ink); }
    wins.push([wx + (ws >> 1), wy + (ws >> 1)]);
  }
  if (o.door) rectf(x + (nw > 1 ? Math.round(w / 2) - 1 : w - 5), y - 5, 3, 5, o.door);
  return wins;
}
// A distant skyline along the horizon, with windows that light up (and a data-centre block whose lights blink).
// o: y (base), ink, grow (0..1: how built-up the city is), lit (0..1 fraction of windows on), seed, x0, x1, dc (data centre x or false)
function city(t, o = {}) {
  const base = o.y ?? 205, grow = o.grow ?? .5, seed = o.seed ?? 7, x0 = o.x0 ?? 250, x1 = o.x1 ?? LW, ink = o.ink ?? C.void, lit = o.lit ?? .35;
  let x = x0, b = 0;
  while (x < x1) {
    const bw = 3 + Math.floor(hash2(b, seed) * 7), tall = hash2(b, seed + 2) < grow * .35;
    const bh = Math.round((2 + hash2(b, seed + 1) * 8) * (.4 + grow)) + (tall ? Math.round(5 + 11 * grow) : 0);
    rectf(x, base - bh, bw, LH - base + bh, ink);
    for (let wy = base - bh + 2; wy < base; wy += 3) for (let wx = x + 1; wx < x + bw - 1; wx += 2) {
      const h = hash2(wx * 31 + wy, seed + 3), on = h < lit * (1 + .25 * Math.sin(t * .3 + wx));
      if (on) pset(wx, wy, h < lit * .3 ? C.gold : h < lit * .7 ? C.amber : C.clay);
    }
    x += bw + (hash2(b, seed + 4) < .35 ? 1 + Math.floor(hash2(b, seed + 5) * 5) : 0); b++;
  }
  if (o.dc !== false && o.dc !== undefined) {
    const dx = o.dc, dw = Math.round(22 + 22 * grow), dh = Math.round(4 + 6 * grow);
    glow(dx + dw / 2, base - dh, dw, { tab: COOL, k: .5 + .5 * grow, ry: 12 + 8 * grow });
    rectf(dx, base - dh, dw, LH - base + dh, ink);
    for (let r = 0; r < Math.max(1, dh / 3 - 1); r++) for (let i = 0; i < dw / 3 - 1; i++) { const on = hash2(i + r * 20, Math.floor(t * 2.5 + i * .37)) < .55; pset(dx + 2 + i * 3, base - dh + 2 + r * 3, on ? C.mint : C.pine); }
  }
}
// Water from y down, reflecting what's above with a gentle wobble; moon/lantern glints shimmer. o: see reflect()
function water(y, o = {}) {
  reflect(y, { wave: 1.2, k: 1, fade: .015, ...o });
  const t = o.t ?? T;
  for (let i = 0; i < 18; i++) { const yy = y + 2 + Math.floor(hash2(i, 41) * (LH - y)), xx = Math.floor(hash2(i, 42) * LW + t * 3 * (hash2(i, 43) - .5) * 4) % LW; hline(xx, xx + 2 + Math.floor(hash2(i, 44) * 4), yy, veil(C.dusk, .6)); }
}
// Weather particles. kind: 'snow' | 'petals' | 'leaves' | 'fireflies' | 'rain' | 'auto' (from the date ticker's season).
// o: n (count), y1 (ground: particles stop above it), x0, x1, wind
function weather(t, kind = 'auto', o = {}) {
  if (kind === 'auto') kind = { winter: 'snow', spring: 'petals', summer: 'fireflies', autumn: 'leaves' }[seasonAt(t)] || 'none';
  const y1 = o.y1 ?? LH, x0 = o.x0 ?? 0, x1 = o.x1 ?? LW, wd = x1 - x0, wind = o.wind ?? 1;
  if (kind === 'snow') for (let i = 0; i < (o.n ?? 60); i++) {
    const sp = 6 + hash2(i, 1) * 8, y = (hash2(i, 2) * (y1 + 20) + t * sp) % (y1 + 20) - 10, x = x0 + ((hash2(i, 3) * wd + Math.sin(t * .7 + i) * 4 + t * 3 * wind) % wd + wd) % wd;
    pset(x, y, hash2(i, 4) < .3 ? C.cream : C.haze);
  }
  else if (kind === 'petals') for (let i = 0; i < (o.n ?? 26); i++) {
    const sp = 5 + hash2(i, 1) * 6, y = (hash2(i, 2) * (y1 + 20) + t * sp) % (y1 + 20) - 10, x = x0 + ((hash2(i, 3) * wd + Math.sin(t * 1.1 + i) * 8 + t * 9 * wind) % wd + wd) % wd;
    const flip = Math.sin(t * 3 + i * 2) > 0; pset(x, y, hash2(i, 4) < .5 ? C.cream : C.haze); if (flip) pset(x + 1, y, C.violet);
  }
  else if (kind === 'leaves') for (let i = 0; i < (o.n ?? 22); i++) {
    const sp = 8 + hash2(i, 1) * 8, y = (hash2(i, 2) * (y1 + 20) + t * sp) % (y1 + 20) - 10, x = x0 + ((hash2(i, 3) * wd + Math.sin(t * .9 + i) * 10 + t * 14 * wind) % wd + wd) % wd;
    const c = [C.clay, C.rust, C.amber][i % 3]; pset(x, y, c); if (Math.sin(t * 4 + i) > 0) pset(x + 1, y + 1, c); else pset(x - 1, y, c);
  }
  else if (kind === 'fireflies') for (let i = 0; i < (o.n ?? 14); i++) {
    const x = x0 + hash2(i, 1) * wd + Math.sin(t * .5 + i * 2.1) * 12, y = (o.y0 ?? y1 - 60) + hash2(i, 2) * ((y1 - 4) - (o.y0 ?? y1 - 60)) + Math.sin(t * .7 + i) * 6;
    firefly(x, y, t, i);
  }
  else if (kind === 'rain') for (let i = 0; i < (o.n ?? 70); i++) {
    const y = (hash2(i, 2) * (y1 + 30) + t * 140) % (y1 + 30) - 15, x = x0 + ((hash2(i, 3) * wd - t * 20 * wind) % wd + wd) % wd;
    pline(x, y, x - 1, y + 3, veil(C.dusk, .8));
  }
}
// A firefly that blinks on its own slow rhythm: a gold point that swells into a small cream plus.
function firefly(x, y, t, i = 0) {
  const b = breathe(t, 3, hash(i + 11));
  if (b < .2) return;
  if (b < .45) return pset(x, y, C.amber);
  if (b < .75) return pset(x, y, C.gold);
  sparkle(x, y, 1, C.cream, C.amber);
}
// A sky lantern (paper, glowing). (x, y) = centre. o: k (glow 0..1.5), s (size 1|2), ink
function lantern(x, y, o = {}) {
  const s = o.s ?? 1, k = o.k ?? 1;
  glow(x, y, 10 * s, { tab: WARM, k: 1.4 * k });
  rectf(x - s - 1, y - 2 * s - 1, 2 * s + 3, 4 * s + 2, o.ink ?? C.amber);
  rectf(x - s, y - 2 * s, 2 * s + 1, 2 * s, C.gold);
  hline(x - s - 1, x + s + 1, y + 2 * s, C.clay);
  if (s > 1) pset(x, y + 2 * s - 1, C.cream);
}
// A hand lantern (Clawd carries one; it sits beside him on the hill). (x, y) = bottom-centre. o: k (flame 0..1.5), glow (radius px, 0 = none)
function handLantern(x, y, o = {}) {
  x = _r(x); y = _r(y); const k = (o.k ?? 1) * (.9 + .1 * breathe(T, 1, hash(x)));
  if ((o.glow ?? 15) > 0) glow(x, y - 4, o.glow ?? 15, { tab: WARM, k: 1.25 * k, pow: 1.7 });
  pset(x, y - 8, C.void); hline(x - 1, x + 1, y - 7, C.void);
  rectf(x - 2, y - 6, 5, 1, C.void); rectf(x - 2, y - 1, 5, 1, C.void);
  rectf(x - 1, y - 5, 3, 4, k > .3 ? C.gold : C.clay); pset(x, y - 4, k > .6 ? C.cream : C.amber); pset(x, y - 3, k > .3 ? C.cream : C.gold);
  vline(x - 2, y - 5, y - 2, C.ink); vline(x + 2, y - 5, y - 2, C.ink);
}
// Smoke wisps rising from (x, y) (candles, chimneys). o: n, h (height), ink
function smoke(x, y, t, o = {}) {
  const n = o.n ?? 6, h = o.h ?? 18;
  for (let i = 0; i < n; i++) { const f = frac(t * .45 + i / n), yy = y - f * h, xx = x + Math.sin(f * 5 + t * 1.3 + i) * f * 4; pset(xx, yy, veil(o.ink ?? C.haze, 1 - f)); }
}
// Aurora curtains for the choruses. o: curve (x → top y of the curtain), len (curtain length px), k (0..1 intensity),
//   cols (dithered ramp from faint to bright, default teal→mint), x0, x1, shimmer
function aurora(t, o = {}) {
  const cols = (o.cols || [C.pine, C.teal, C.mint]).map(col), n = cols.length, k = o.k ?? 1, len = o.len ?? 40, x0 = o.x0 ?? 0, x1 = o.x1 ?? LW - 1;
  const curve = o.curve || (x => 90 + Math.sin(x * .02 + t * .4) * 18), sh = o.shimmer ?? 1;
  for (let sx = Math.max(CX0, x0 - VX); sx <= Math.min(CX1, x1 - VX); sx++) {
    const wx = sx + VX, top = curve(wx);
    const ray = 1 - sh * .45 * (.5 + .5 * Math.sin(wx * .31 + t * 1.7 + Math.sin(wx * .07 - t * .6) * 3)), L = len * (.65 + .35 * ray);
    for (let yy = Math.max(CY0, Math.floor(top - 3 - VY)); yy <= Math.min(CY1, Math.ceil(top + L - VY)); yy++) {
      const d = (yy + VY - top) / L, e = d < 0 ? 1 + d / .1 : (1 - d) ** 1.3;
      const v = clamp(e) * k * ray * n, i = Math.floor(v), lv = i + (BAYER[((yy & 7) << 3) | (sx & 7)] < v - i ? 1 : 0);
      if (lv >= 1) FB[yy * LW + sx] = cols[Math.min(n, lv) - 1];
    }
  }
}

// =====================================================================================================
// CAST: Clawd, people, name tags, agents, bots
// =====================================================================================================
// clawdPx(x, y, o): the pixel Clawd. (x, y) = ground point under its middle. u = 1 (10×8 px, a speck on a hill) … 6 (close-up).
// o: u, pose ('stand'|'sit'|'sleep'), walk (phase: legs step), eyes ('open'|'closed'|'happy'|'wide'|'up'|'spark'|'heart'),
//    lookX (−1..1), lookY (−1 up … 1 down), aL / aR (arm angles: 0 straight out (default), + up, − down), mouth ('none'|'o'|'smile'),
//    dy (hop, px up), blink (default true: blinks now and then), hat ('nightcap'|'beanie'), scarf (ink), glow (tint halo),
//    outline (ink: a 1-px ring so Clawd reads against warm or busy backgrounds, e.g. C.wine at dawn),
//    shadow (default true), col / dk / hi (recolour). Returns {x, top, handL: [x, y], handR: [x, y]}.
function clawdPx(x, y, o = {}) {
  const u = Math.max(1, Math.round(o.u ?? 1)), t = T, colB = col(o.col ?? C.clay), dk = col(o.dk ?? C.rust), hi = col(o.hi ?? C.amber);
  x = _r(x); y = _r(y);
  if (o.outline !== undefined && !o._sil) {   // 1-px silhouette ring (for warm or busy backgrounds)
    const ol = col(o.outline);
    for (const [dx, dy] of [[-1, 0], [1, 0], [0, -1], [0, 1]]) clawdPx(x + dx, y + dy, { ...o, _sil: true, _hx: x, col: ol, dk: ol, hi: ol, eyes: 'none', mouth: 'none', blush: false, shadow: false, glow: undefined, hat: undefined, zzz: false, blink: false, scarf: o.scarf !== undefined ? ol : undefined });
  }
  const pose = o.pose ?? 'stand', sit = pose === 'sit' || pose === 'sleep';
  const bw = 10 * u, bh = 6 * u, legH = sit ? Math.max(1, u >> 1) : 2 * u, hop = _r(o.dy ?? 0);
  const breath = u >= 3 && pose !== 'walk' ? Math.round(breathe(t, 2, hash(o._hx ?? x)) * (u >= 4 ? 1 : .6)) : 0;
  const by = y - legH - bh - hop + breath, bx = x - 5 * u;
  if (o.glow) glow(x, by + bh / 2, bw * 1.3, { tab: o.glow === true ? WARM : o.glow, k: 1.2 });
  if (o.shadow !== false && !o._sil) ellf(x, y, 5 * u + 1, Math.max(0, u * .5), dim(.8));
  // legs
  const lw = Math.max(1, Math.round(1.1 * u));
  [-3.6, -1.4, 1.4, 3.6].forEach((lx, i) => {
    const lift = o.walk !== undefined ? Math.max(0, Math.round(Math.sin((o.walk + (i % 2) * .5) * TAU) * Math.max(1, u * .7))) : 0;
    rectf(x + Math.round(lx * u - lw / 2 + .01), y - legH - lift - hop, lw, legH, dk);
  });
  // arms (nubs): a short thick stroke from the shoulder; angle 0 = straight out like the logo
  const arm = (side, a) => {
    const th = Math.max(1, Math.round(1.2 * u)), len = 2 * u, sx = side < 0 ? bx - 1 : bx + bw, sy = by + Math.round(2.4 * u);
    const dx = Math.cos(a) * side, dy = -Math.sin(a);
    let ex = sx, ey = sy;
    for (let i = 0; i < len; i++) { ex = Math.round(sx + dx * i - (side < 0 ? th - 1 : 0) * (1 - Math.abs(dy))); ey = Math.round(sy + dy * i); rectf(ex, ey, th, th, colB); }
    return [ex + (th >> 1), ey + (th >> 1)];
  };
  const handL = arm(-1, o.aL ?? 0), handR = arm(1, o.aR ?? 0);
  // body with shading
  rectf(bx, by, bw, bh, colB);
  if (u >= 2) { rectf(bx + bw - Math.max(1, u >> 1), by + 1, Math.max(1, u >> 1), bh - 1, dk); rectf(bx, by + bh - Math.max(1, u >> 1), bw, Math.max(1, u >> 1), dk); rectf(bx, by, bw - 1, Math.max(1, u >> 2), hi); }
  if (o.scarf !== undefined) { rectf(bx - 1, by + Math.round(bh * .55), bw + 2, Math.max(1, u), o.scarf); rectf(bx + bw - 2 * u, by + Math.round(bh * .55), Math.max(1, u), Math.max(2, 2 * u), o.scarf); }
  // eyes
  const ew = Math.max(1, Math.round(.9 * u)), eh = Math.max(2, Math.round(1.6 * u));
  const lookX = Math.round((o.lookX ?? 0) * Math.max(1, u * .5)), lookY = Math.round((o.lookY ?? 0) * Math.max(1, u * .4));
  let eyes = o.eyes ?? 'open';
  if (eyes === 'up') { eyes = 'open'; }
  const upShift = (o.eyes === 'up' ? -Math.max(1, Math.round(u * .6)) : 0) + lookY;
  if ((eyes === 'open' || eyes === 'wide') && o.blink !== false) { const b = sbp(t) + hash(x * 3 + 1) * 7; if (hash2(Math.floor(b / 3), 91 + x) < .5 && frac(b / 3) > .9 && frac(b / 3) < .96) eyes = 'closed'; }
  for (const side of [-1, 1]) {
    const ex = x + Math.round(side * 2.3 * u - ew / 2 + .01) + lookX, ey = by + Math.round(1.2 * u) + upShift;
    if (eyes === 'open') rectf(ex, ey, ew, eh, C.void);
    else if (eyes === 'closed') rectf(ex - (u === 1 ? 0 : Math.floor(u / 3)), ey + eh - 1, ew + (u === 1 ? 1 : 2 * Math.floor(u / 3)), Math.max(1, u >> 2), C.void);
    else if (eyes === 'happy') { rectf(ex, ey + 1, ew, 1, C.void); pset(ex - 1, ey + 2, C.void); pset(ex + ew, ey + 2, C.void); }
    else if (eyes === 'wide') { rectf(ex - 1, ey - 1, ew + 2, eh + 2, C.cream); rectf(ex + (lookX > 0 ? 1 : 0), ey + (upShift < 0 ? 0 : 1), Math.max(1, ew - 1), Math.max(1, eh - 1), C.void); }
    else if (eyes === 'spark') sparkle(ex + (ew >> 1), ey + (eh >> 1), u >= 3 ? 1 : 0, C.cream, C.gold);
    else if (eyes === 'heart') heartPx(ex + (ew >> 1), ey + (eh >> 1), 1, C.wine);
  }
  if (o.mouth === 'o' && u >= 2) rectf(x - Math.floor(u / 2), by + Math.round(3.6 * u) + upShift, Math.max(1, u >> 1) + 1, Math.max(1, u >> 1) + 1, C.void);
  if (o.mouth === 'smile' && u >= 2) { hline(x - u, x + u - 1, by + Math.round(3.8 * u) + upShift, C.void); pset(x - u - 1, by + Math.round(3.8 * u) - 1 + upShift, C.void); pset(x + u, by + Math.round(3.8 * u) - 1 + upShift, C.void); }
  if (o.blush && u >= 2) { rectf(bx + u, by + Math.round(3.2 * u), u, Math.max(1, u >> 1), C.rust); rectf(bx + bw - 2 * u, by + Math.round(3.2 * u), u, Math.max(1, u >> 1), C.rust); }
  if (o.hat === 'nightcap') {
    const hx = bx + u, hw = bw - 3 * u, cap = Math.max(2, 2 * u), tipX = bx + bw + 2 * u, tipY = by + Math.round(1.5 * u);
    polyf([[hx, by + .5], [hx + hw, by + .5], [hx + hw * .7, by - cap - u], [tipX + .5, tipY]], C.violet);
    polyf([[hx + hw * .55, by - cap * .6], [hx + hw * .72, by - cap - u + 1], [tipX, tipY - 1], [hx + hw * .9, by - 1]], mix(C.violet, C.haze, .25));
    rectf(hx - 1, by - Math.max(1, u >> 1), hw + 2, Math.max(1, u >> 1) + 1, C.cream);
    circf(tipX, tipY + 1, Math.max(1, u * .6), C.cream);
  } else if (o.hat === 'beanie') { rectf(bx + u, by - u - 1, bw - 2 * u, u + 1, o.hatInk ?? C.teal); rectf(bx + u, by - 1, bw - 2 * u, 1, C.mint); pset(x, by - u - 2, C.cream); }
  if (pose === 'sleep' && o.zzz !== false) { const zf = frac(t * .5); for (let i = 0; i < 3; i++) { const f = frac(zf + i / 3); ptext('z', x + 6 * u + f * 10, by - 2 - f * 16, veil(C.haze, 1 - f), { font: 3 }); } }
  return { x, top: by, left: bx, right: bx + bw - 1, handL, handR };
}
// Heart. s = 1 (5×4), 2 (7×6), 3 (9×8). (x, y) = centre.
function heartPx(x, y, s = 1, ink = C.rust, hiInk) {
  const rows = s <= 1 ? ['.#.#.', '#####', '.###.', '..#..'] : s === 2 ? ['.##.##.', '#######', '#######', '.#####.', '..###..', '...#...'] : ['.###.###.', '#########', '#########', '#########', '.#######.', '..#####..', '...###...', '....#....'];
  const w = rows[0].length, h = rows.length, x0 = _r(x - w / 2 + .01), y0 = _r(y - h / 2 + .01);
  rows.forEach((r, j) => [...r].forEach((c, i) => { if (c === '#') pset(x0 + i, y0 + j, ink); }));
  if (hiInk !== undefined && s >= 2) pset(x0 + 1, y0 + 1, hiInk);
}
// tagPx(name, cx, bottom, o): the pixel name label (3×5 caps, cream on a dark plate with a tiny pointer). o: font (3|5), ink, plate, edge.
function tagPx(name, cx, bottom, o = {}) {
  const f = o.font ?? 3, th = f === 3 ? 5 : 7, w = ptextW(name, { font: f }), pw = w + 4, x = _r(cx - pw / 2), y = _r(bottom - th - 3);
  rectf(x, y, pw, th + 2, o.plate ?? C.void); rectb(x - 1, y - 1, pw + 2, th + 4, o.edge ?? C.navy);
  pset(_r(cx), y + th + 3, o.edge ?? C.navy);
  ptext(name, x + 2, y + 1, o.ink ?? C.cream, { font: f });
  return pw;
}
const SKIN = [C.amber, C.gold, C.clay];
// personPx(x, y, o): a small pixel person, (x, y) = ground point between the feet. u = 1 (~10 px tall), 2 (~19), 3 (~27).
// o: u, name (tag above), skin (ink), hair ('short'|'long'|'bald'|'spiky'|'slick'|'curly'|'bun'|'hood'|'none'), hairC,
//    top (shirt ink), pants, suit (true: shirt V + tie), tie (ink), hat ('fedora'|'cap'|'beanie'), hatC, glasses, beard (ink),
//    aL / aR (arm angles as clawdPx: 0 out, + up, − hanging, default −1.25), walk (phase), eyes ('dot'|'closed'|'wide'|'up'|'none'),
//    mouth ('none'|'o'|'smile'|'frown'), lookX (−1..1), flip, sit (legs forward, flip = legs to the left), dy (hop), medal (bool),
//    hold (fn(hx, hy) draws in the right hand), hoodC (hood colour)
// Returns {top, headY, handL, handR}.
function personPx(x, y, o = {}) {
  const u = Math.max(1, Math.round(o.u ?? 1)); x = _r(x); y = _r(y - (o.dy ?? 0));
  const skin = col(o.skin ?? C.amber), top = col(o.top ?? C.navy), pants = col(o.pants ?? C.ink), hairC = col(o.hairC ?? C.void);
  const tw = 3 * u + (u % 2 ? 0 : 1), th = 4 * u, sitting = !!o.sit, legH = sitting ? u : 2 * u, hs = 2 * u + 1;
  const tx = x - (tw >> 1), ty = y - legH - th, hx = x - u, hy = ty - hs;
  // legs
  const lw = Math.max(1, u), step = o.walk !== undefined ? Math.sin(o.walk * TAU) : 0;
  const lx1 = x - lw + Math.round(step * (u > 1 ? 1 : 0)), lx2 = x + 1 - Math.round(step * (u > 1 ? 1 : 0));
  if (sitting) { const dir = o.flip ? -1 : 1, lx = dir > 0 ? x - (tw >> 1) : x - (tw >> 1) - 2 * u; rectf(lx, y - u, tw + 2 * u, u, pants); rectf(dir > 0 ? lx + tw + 2 * u - 1 : lx, y - u - (u > 1 ? 1 : 0), 1, u + (u > 1 ? 1 : 0), C.void); }
  else {
    rectf(lx1, y - legH + (step > .3 ? -1 : 0), lw, legH, pants); rectf(lx2, y - legH + (step < -.3 ? -1 : 0), lw, legH, pants);
    if (u >= 2) { rectf(lx1 - (u > 2 ? 1 : 0), y - 1, lw + (u > 2 ? 1 : 0), 1, C.void); rectf(lx2, y - 1, lw + (u > 2 ? 1 : 0), 1, C.void); }
  }
  // torso
  rectf(tx, ty, tw, th, top);
  if (u >= 2) rectf(tx + tw - 1, ty + 1, 1, th - 1, tint(DIM, 1));
  if (o.suit && u >= 2) { triPx(x - u + .5, ty, x + u + .5, ty, x + .5, ty + u * 1.6, C.cream); vline(x, ty + 1, ty + Math.round(th * .7), o.tie ?? C.rust); }
  if (o.medal) { const my = ty + Math.round(th * .45); if (u >= 2) { pline(x - u + 1, ty, x, my - 1, C.rust); pline(x + u - 1, ty, x, my - 1, C.rust); } circf(x, my, u >= 2 ? 1 : 0, C.gold); if (u >= 2) pset(x - 1, my - 1, C.cream); }
  // arms
  const arm = (side, a) => {
    const sx = side < 0 ? tx - 1 : tx + tw, sy = ty + (u >= 2 ? 1 : 0), len = 3 * u + (u > 1 ? 1 : 0), aw = Math.max(1, u - (u > 2 ? 1 : 0));
    const dx = Math.cos(a) * side, dy = -Math.sin(a); let ex = sx, ey = sy;
    for (let i = 0; i < len; i++) { ex = Math.round(sx + dx * i - (side < 0 ? aw - 1 : 0)); ey = Math.round(sy + dy * i); rectf(ex, ey, aw, aw, i >= len - Math.max(1, u >> 1) ? skin : top); }
    return [ex + (aw >> 1), ey + (aw >> 1)];
  };
  const handL = arm(-1, o.aL ?? -1.25), handR = arm(1, o.aR ?? -1.25);
  // head
  rectf(hx, hy, hs, hs, skin);
  if (u >= 2) rectf(hx + hs - 1, hy + 1, 1, hs - 1, tint(DIM, 1));
  // face
  const eyes = o.eyes ?? 'dot', ey = hy + Math.round(hs * .45) + (o.eyes === 'up' ? -1 : 0), fl = o.flip ? -1 : 1, lk = Math.round((o.lookX ?? 0));
  if (eyes !== 'none') {
    if (u === 1) { if (eyes !== 'closed') { pset(x - 1 + lk, ey, C.void); pset(x + 1 + lk, ey, C.void); } }
    else {
      const ex = u === 2 ? 1 : Math.round(u * .7);
      for (const s of [-1, 1]) {
        const px = x + s * ex + lk;
        if (eyes === 'closed') hline(px - (u > 2 ? 1 : 0), px, ey + 1, C.void);
        else if (eyes === 'wide') { rectf(px - (u > 2 ? 1 : 0), ey - 1, u > 2 ? 2 : 1, u > 2 ? 3 : 2, C.cream); pset(px, ey, C.void); }
        else rectf(px, ey, 1, u > 2 ? 2 : 1, C.void);
      }
      if (o.glasses) { for (const s of [-1, 1]) rectb(x + s * ex - 1 + lk, ey - 1, 3, 3, o.glasses === true ? C.haze : o.glasses); }
    }
    if (u >= 2) {
      const my = hy + hs - (u > 2 ? 2 : 1), m = o.mouth ?? 'none';
      if (m === 'o') rectf(x - (u > 2 ? 1 : 0), my - (u > 2 ? 1 : 0), u > 2 ? 2 : 1, u > 2 ? 2 : 1, C.void);
      else if (m === 'smile') { hline(x - 1, x + 1, my, C.rust); }
      else if (m === 'frown') { hline(x - 1, x + 1, my, C.void); }
    }
  }
  if (o.beard !== undefined && u >= 2) { rectf(hx, hy + hs - u, hs, u, col(o.beard)); rectf(hx + 1, hy + hs, hs - 2, 1, col(o.beard)); if (o.mouth && o.mouth !== 'none') pset(x, hy + hs - u, C.void); }
  // hair / hood / hat
  const hair = o.hair ?? 'short';
  if (hair === 'short') { rectf(hx, hy - 1, hs, u >= 2 ? 2 : 1, hairC); if (u >= 2) { vline(hx, hy, hy + u - 1, hairC); vline(hx + hs - 1, hy, hy + u - 1, hairC); } }
  else if (hair === 'long') { rectf(hx - (u > 1 ? 1 : 0), hy - 1, hs + (u > 1 ? 2 : 0), u >= 2 ? 2 : 1, hairC); vline(hx - (u > 1 ? 1 : 0), hy, hy + hs + u, hairC); vline(hx + hs - (u > 1 ? 0 : 1), hy, hy + hs + u, hairC); }
  else if (hair === 'spiky') { rectf(hx, hy - 1, hs, 1, hairC); for (let i = 0; i < hs; i += 2) vline(hx + i, hy - 2 - (i % 4 ? 1 : 0) - (u > 1 ? 1 : 0), hy - 1, hairC); }
  else if (hair === 'slick') { rectf(hx, hy - 1, hs, u >= 2 ? 2 : 1, hairC); pset(hx + hs, hy - 1, hairC); if (u >= 2) pset(hx + 1, hy + 1, hairC); }
  else if (hair === 'curly') { for (let i = -1; i <= hs; i++) pset(hx + i, hy - 1 - (i % 2 ? 1 : 0), hairC); rectf(hx, hy - 1, hs, 1, hairC); if (u >= 2) { vline(hx - 1, hy, hy + u, hairC); vline(hx + hs, hy, hy + u, hairC); } }
  else if (hair === 'bun') { rectf(hx, hy - 1, hs, 1, hairC); circf(x, hy - 2 - (u > 1 ? 1 : 0), u > 1 ? 1 : 0, hairC); }
  else if (hair === 'bald' && u >= 2) { pset(hx, hy + 1, hairC); pset(hx + hs - 1, hy + 1, hairC); }
  else if (hair === 'hood') {
    const hc = col(o.hoodC ?? C.ink);
    rectf(hx - 1, hy - 2, hs + 2, hs + 3, hc); rectf(tx, ty, tw, Math.max(2, u + 1), hc);
    rectf(hx + (u > 1 ? 1 : 0), hy + (u > 1 ? 1 : 0), hs - (u > 1 ? 2 : 0), hs - (u > 1 ? 1 : 0), C.void);
    if (u >= 2) { pset(x - 1, ey, C.gold); pset(x + 1, ey, C.gold); }
  }
  if (o.hat === 'fedora') { const hc = col(o.hatC ?? C.ink); rectf(hx - u - 1, hy - 1, hs + 2 * u + 2, 1, hc); rectf(hx, hy - 1 - (u + 1), hs, u + 1, hc); rectf(hx, hy - 2, hs, 1, o.band ?? C.rust); }
  else if (o.hat === 'cap') { const hc = col(o.hatC ?? C.rust); rectf(hx, hy - 1 - u, hs, u + 1, hc); rectf(hx + (fl > 0 ? hs - 1 : -u), hy - 1, u + 1, 1, hc); }
  else if (o.hat === 'beanie') { const hc = col(o.hatC ?? C.teal); rectf(hx, hy - 1 - u, hs, u + 1, hc); pset(x, hy - 2 - u, C.cream); }
  if (o.hold) o.hold(handR[0], handR[1]);
  if (o.name) tagPx(o.name, x, hy - 3 - (o.hat ? u + 2 : hair === 'spiky' ? 2 : 0) - (o.tagUp ?? 0), o.tag || {});
  return { top: hy, headY: hy, handL, handR, x };
}
// torso box of a personPx figure (for costume overlays): {tx, ty, tw, th}
const torso = (x, y, u, sit = false, dy = 0) => { const tw = 3 * u + (u % 2 ? 0 : 1), th = 4 * u, legH = sit ? u : 2 * u; return { tx: Math.round(x) - (tw >> 1), ty: Math.round(y - dy) - legH - th, tw, th }; };
// trumpPx: President Trump as a pixel caricature, personPx's build with his look on top: the tall golden swoop combed
// over to a flip above the right brow, a tan face with a narrow squint and a pursed "o", a broad navy suit with a flag
// pin, and the long red tie that hangs past the belt. (x, y) = ground point; o: u (≥ 4), aL, aR, mouth ('o'|'none'), sit
function trumpPx(x, y, o = {}) {
  const u = o.u ?? 6, P = personPx(x, y, { u, suit: true, top: C.navy, pants: C.ink, tie: C.rust, hair: 'none', skin: C.clay, eyes: 'none', aL: o.aL, aR: o.aR, dy: o.dy });
  const { tx, ty, tw, th } = torso(x, y, u, false, o.dy ?? 0), hs = 2 * u + 1, hx = Math.round(x) - u, hy = ty - hs, X = Math.round(x);
  // a broad jacket, a white collar and the long tie
  rectf(tx - 1, ty + 1, 1, th - 1, C.navy); rectf(tx + tw, ty + 1, 1, th - 1, C.night);
  triPx(X - u + .5, ty, X + u + .5, ty, X + .5, ty + u * 1.6, C.cream);
  const tl = th + Math.round(u * .6);
  rectf(X - 1, ty + 1, 3, 2, C.wine); rectf(X - 1, ty + 3, 3, tl - 4, C.rust); rectf(X, ty + tl - 1, 1, 1, C.rust); vline(X + 1, ty + 3, ty + tl - 2, C.wine);
  pset(X - u + 1, ty + Math.round(u * .9), C.rust); pset(X - u + 2, ty + Math.round(u * .9), C.cream);
  // face: squint, pale brows, pursed mouth, a touch of jowl
  const ey = hy + Math.round(hs * .5), ex = Math.round(u * .7);
  for (const sd of [-1, 1]) { hline(X + sd * ex - 1, X + sd * ex + (u > 4 ? 1 : 0), ey, C.void); hline(X + sd * ex - 1, X + sd * ex + 1, ey - 2, C.gold); }
  const my = hy + hs - Math.round(u * .45);
  if ((o.mouth ?? 'o') === 'o') { rectf(X - 1, my - 1, 2, 2, C.void); pset(X - 2, my, C.wine); pset(X + 1, my, C.wine); } else hline(X - 1, X + 1, my, C.wine);
  hline(hx + 1, hx + hs - 2, hy + hs - 1, tint(DIM, 1));
  // the hair: a tall golden mass wider than the head, combed from the left across to a flip over the right brow
  rectf(hx - 1, hy - 4, hs + 2, 6, C.gold); rectf(hx, hy - 5, hs - 1, 1, C.gold);
  rectf(hx - 1, hy + 2, 2, Math.round(u * .6), C.gold); rectf(hx + hs - 1, hy + 2, 2, Math.round(u * .6), C.gold);
  rectf(hx + hs - Math.round(u * .9), hy + 2, Math.round(u * .9), 2, C.gold); pset(hx + hs + 1, hy + 1, C.gold); pset(hx + hs + 1, hy + 2, C.amber);
  hline(hx, hx + hs - 4, hy + 2, C.amber);
  pline(hx + 1, hy - 1, hx + hs - 2, hy + 1, C.amber);
  hline(hx + 1, hx + hs - 3, hy - 4, C.cream); pset(hx + hs - 2, hy - 3, C.cream);
  return { ...P, top: hy - 5 };
}
// agentPx: a tiny terminal-window critter (swarms of them in V3/V4). (x, y) = ground point. o: u (1|2), bar (ink), walk, eyes ('>'|'dot'|'x'|'heart')
function agentPx(x, y, o = {}) {
  const u = o.u ?? 1; x = _r(x); y = _r(y - (o.dy ?? 0));
  const w = 5 * u + (u > 1 ? 1 : 0), h = 4 * u, bx = x - (w >> 1), by = y - h - u;
  rectf(bx, by, w, h, o.body ?? C.ink); rectf(bx, by, w, u, o.bar ?? C.clay); rectb(bx, by, w, h, o.edge ?? C.dusk);
  if (o.eyes === 'x') { pset(bx + u + 1, by + u + 1, C.rust); pset(bx + w - u - 2, by + u + 1, C.rust); }
  else if (o.eyes === 'heart') heartPx(x, by + h / 2 + 1, 1, C.rust);
  else { pset(bx + 1 + (u > 1 ? 1 : 0), by + u + 1, C.mint); if (u > 1) { pset(bx + 3, by + u + 2, C.mint); pset(bx + 2, by + u + 3, C.mint); } pset(bx + w - 2 - (u > 1 ? 1 : 0), by + h - 2, C.cream); }
  const st = o.walk !== undefined ? Math.sin(o.walk * TAU) > 0 : false;
  rectf(bx + 1, y - u, u, u - (st ? 1 : 0) || 1, C.dusk); rectf(bx + w - 1 - u, y - u, u, u - (st ? 0 : 1) || 1, C.dusk);
}
// botPx: a small boxy robot/AI model. (x, y) = ground point. o: u (1..3), body (ink), screen (ink), face ('dot'|'x'|'heart'|'happy'|'sad'|'angry'), label (F3 text on chest), aL, aR, glow
function botPx(x, y, o = {}) {
  const u = o.u ?? 2; x = _r(x); y = _r(y - (o.dy ?? 0));
  const bw = 6 * u + 1, bh = 5 * u, hw = 5 * u + 1, hh = 4 * u, body = col(o.body ?? C.dusk), dk = DIM[body];
  const bx = x - (bw >> 1), by = y - u - bh, hx = x - (hw >> 1), hy = by - hh - 1;
  if (o.glow) glow(x, hy + hh / 2, 5 * u + 6, { tab: o.glow === true ? LIT : o.glow, k: 1.1 });
  rectf(x - u - 1, y - u, u, u, dk); rectf(x + 1, y - u, u, u, dk);
  rectf(bx, by, bw, bh, body); rectf(bx + bw - 1, by + 1, 1, bh - 1, dk);
  rectf(x, hy - u - 1, 1, u + 1, dk); pset(x, hy - u - 2, o.antenna ?? C.rust);
  rectf(hx, hy, hw, hh, body); rectf(hx + hw - 1, hy + 1, 1, hh - 1, dk);
  const scr = col(o.screen ?? C.ink); rectf(hx + 1, hy + 1, hw - 2, hh - 2, scr);
  const fc = col(o.faceInk ?? C.mint), ey = hy + Math.round(hh * .45), ex = Math.max(1, u);
  const f = o.face ?? 'dot';
  if (f === 'x') { for (const s of [-1, 1]) { const cx = x + s * ex; pset(cx - 1, ey - 1, fc); pset(cx + 1, ey + 1, fc); pset(cx, ey, fc); pset(cx + 1, ey - 1, fc); pset(cx - 1, ey + 1, fc); } }
  else if (f === 'heart') heartPx(x, ey, 1, C.rust);
  else {
    for (const s of [-1, 1]) rectf(x + s * ex, ey, 1, f === 'happy' ? 1 : Math.max(1, u - 1), fc);
    if (u > 1 && f === 'happy') hline(x - 1, x + 1, ey + 2, fc);
    if (u > 1 && f === 'sad') hline(x - 1, x + 1, ey + 3, fc);
    if (u > 1 && f === 'angry') { pset(x - ex - 1, ey - 1, fc); pset(x + ex + 1, ey - 1, fc); }
  }
  const arm = (side, a) => { const sx = side < 0 ? bx - 1 : bx + bw, sy = by + 1; for (let i = 0; i < 3 * u; i++) rectf(Math.round(sx + Math.cos(a) * side * i), Math.round(sy - Math.sin(a) * i), Math.max(1, u - 1), Math.max(1, u - 1), dk); };
  arm(-1, o.aL ?? -1.2); arm(1, o.aR ?? -1.2);
  if (o.label) ptext(o.label, x, by + 2, o.labelInk ?? C.cream, { font: 3, align: 'center' });
  return { top: hy - u - 2, x };
}

// huggyPx: the 🤗 hugging face (Hugging Face). (x, y) = face centre. o: r (radius, default 8), mood ('happy'|'scared'|'x'|'sleep'), hands (bool), bandage
function huggyPx(x, y, o = {}) {
  const r = o.r ?? 8, mood = o.mood ?? 'happy'; x = _r(x); y = _r(y);
  ball(x, y, r, [C.clay, C.amber, C.gold], { lx: -.4, ly: -.6 });
  const ex = Math.max(2, Math.round(r * .38)), ey = y - Math.round(r * .2);
  if (mood === 'x') for (const s of [-1, 1]) { pset(x + s * ex - 1, ey - 1, C.void); pset(x + s * ex + 1, ey + 1, C.void); pset(x + s * ex, ey, C.void); pset(x + s * ex + 1, ey - 1, C.void); pset(x + s * ex - 1, ey + 1, C.void); }
  else if (mood === 'scared') for (const s of [-1, 1]) { rectf(x + s * ex - 1, ey - 1, 3, 3, C.cream); pset(x + s * ex, ey, C.void); }
  else if (mood === 'sleep') for (const s of [-1, 1]) hline(x + s * ex - 1, x + s * ex + 1, ey, C.void);
  else for (const s of [-1, 1]) { pset(x + s * ex - 1, ey, C.void); pset(x + s * ex, ey - 1, C.void); pset(x + s * ex + 1, ey, C.void); }
  const my = y + Math.round(r * .3);
  if (mood === 'scared') rectf(x - 1, my, 3, 2, C.void);
  else { hline(x - Math.round(r * .4), x + Math.round(r * .4), my, C.void); hline(x - Math.round(r * .3), x + Math.round(r * .3), my + 1, C.wine); }
  if (o.hands !== false) for (const s of [-1, 1]) { const hx = x + s * Math.round(r * .75), hy = y + Math.round(r * .55); circf(hx, hy, Math.max(1, r * .28), C.gold); pset(hx - s, hy - 1, C.amber); }
  if (o.bandage) { rectf(x + Math.round(r * .2), y - r + 1, Math.round(r * .7), 2, C.cream); pset(x + Math.round(r * .5), y - r + 1, C.haze); }
}
// lobsterPx: a proud red lobster, front-on, claws up (OpenClaw). (x, y) = ground point. o: u (1..3), claws (0..1: raised), eyes ('dot'|'happy')
function lobsterPx(x, y, o = {}) {
  const u = o.u ?? 2, raise = o.claws ?? 0; x = _r(x); y = _r(y);
  polyf([[x - 3 * u, y], [x + 3 * u + 1, y], [x + .5, y - 3 * u]], C.rust);                       // tail fan
  ellf(x, y - 7 * u, 3 * u, 5 * u, C.rust);                                                        // body
  for (let i = 1; i < 4; i++) hline(x - 2 * u, x + 2 * u, y - 3 * u - i * 2 * u, C.wine);       // shell segments
  ellf(x - u, y - 9 * u, u, 2 * u, C.clay);                                                        // shine
  for (let i = 0; i < 3; i++) for (const s of [-1, 1]) pline(x + s * 3 * u, y - 5 * u - i * u * 1.5, x + s * 5 * u, y - 3 * u - i * u * 1.5, C.wine);  // legs
  for (const s of [-1, 1]) {                                                                          // arms + big claws
    const ax = x + s * 3 * u, ay = y - 9 * u, ex = x + s * 7 * u, ey = y - (9 + 4 * raise) * u;
    thick(ax, ay, ex, ey, Math.max(2, u), C.rust);
    ellf(ex, ey - 2 * u, 2 * u, 3 * u, C.rust); ellf(ex - s * u * .5, ey - 3 * u, u * .8, 1.6 * u, C.clay);
    rectf(ex - (s < 0 ? 0 : 1), ey - 5 * u, 1, 2 * u, C.void);                                    // pincer notch
  }
  for (const s of [-1, 1]) { pline(x + s * u, y - 12 * u, x + s * 2 * u, y - 14 * u, C.rust); pset(x + s * 2 * u, y - 14 * u, C.void); if (o.eyes === 'happy') pset(x + s * 2 * u, y - 15 * u, C.void); }
  for (const s of [-1, 1]) plines([[x + s * u, y - 12 * u], [x + s * 5 * u, y - 18 * u], [x + s * 10 * u, y - 19 * u]], C.clay);   // antennae
}

// =====================================================================================================
// PROPS
// =====================================================================================================
// medalPx: gold medal on a ribbon. (x, y) = medal centre. o: r (radius 2..6), ribbon (ink), shine (0..1 sparkle)
function medalPx(x, y, o = {}) {
  const r = o.r ?? 3;
  if (o.ribbon !== false) { const rb = col(o.ribbon ?? C.rust); thick(x - r, y - r * 3.2, x - 1, y - r + 1, Math.max(2, r * .6), rb); thick(x + r, y - r * 3.2, x + 1, y - r + 1, Math.max(2, r * .6), mix(rb, C.wine, .5)); }
  circf(x, y, r, C.amber); circf(x, y, r - 1, C.gold); if (r >= 3) { pset(x - 1, y - 1, C.cream); circb(x, y, r - 1, C.amber); circf(x, y, r - 2, C.gold); }
  if (o.shine) sparkle(x + r - 1, y - r + 1, o.shine > .6 ? 2 : 1);
}
// bubblePx: a pixel speech bubble. (x, y) = bottom-centre of the bubble box; tail points to (tx, ty).
// o: font (3|5), ink (text), fill, edge, n (typing), maxW, pad
function bubblePx(text, x, y, o = {}) {
  const f = o.font ?? 3, pad = o.pad ?? 2, lines = o.maxW ? _wrapText(text, { font: f, maxW: o.maxW }) : String(text).split('\n');
  const F = f === 3 ? F3 : F5, lh = F._h + (f === 3 ? 2 : 4), w = Math.max(...lines.map(l => ptextW(l, { font: f }))) + pad * 2 + 2, h = lines.length * lh - (f === 3 ? 2 : 4) + pad * 2 + 2 + (f === 5 && /[gjpqy,]/.test(text) ? 2 : 0);
  const bx = _r(x - w / 2), by = _r(y - h), fill = o.fill ?? C.cream, edge = o.edge ?? C.void;
  if (o.tail) { const [tx, ty] = o.tail; triPx(x - 3, y - 1, x + 2, y - 1, tx, ty, edge); triPx(x - 2, y - 2, x + 1, y - 2, lerp(x, tx, .75), lerp(y, ty, .75), fill); }
  rboxf(bx - 1, by - 1, w + 2, h + 2, edge, 2); rboxf(bx, by, w, h, fill, 1);
  ptext(lines.join('\n'), x, by + pad + 1, o.ink ?? C.void, { font: f, align: 'center', n: o.n });
  return { x: bx, y: by, w, h };
}
// signPx: a text plate. (x, y) = top-centre. o: font, ink, plate, edge, pad, scale, dots
function signPx(text, x, y, o = {}) {
  const f = o.font ?? 3, s = o.scale ?? 1, pad = o.pad ?? 2, w = ptextW(text, { font: f, scale: s }) + pad * 2, h = (f === 3 ? 5 : 7) * s + pad * 2;
  const bx = _r(x - w / 2);
  rectf(bx, y, w, h, o.plate ?? C.void); if (o.edge !== false) rectb(bx - 1, y - 1, w + 2, h + 2, o.edge ?? C.dusk);
  ptext(text, bx + pad, y + pad, o.ink ?? C.cream, { font: f, scale: s, dots: o.dots, n: o.n });
  return { x: bx, w, h };
}
// paperPx: a sheet of paper (letters, bills, essays). (x, y) = top-left. o: title (F3), lines (count of scribble lines), ink, fold
function paperPx(x, y, w, h, o = {}) {
  rectf(x + 1, y + 1, w, h, C.void); rectf(x, y, w, h, o.fill ?? C.cream); if (o.fold !== false) { pset(x + w - 1, y, C.void); pset(x + w - 2, y, C.gold); pset(x + w - 1, y + 1, C.gold); }
  let ly = y + 3;
  if (o.title) { ptext(o.title, x + w / 2, ly, o.titleInk ?? C.void, { font: 3, align: 'center', maxW: w - 4 }); ly += 7 * _wrapText(o.title, { font: 3, maxW: w - 4 }).length; }
  for (let i = 0; i < (o.lines ?? 3) && ly < y + h - 2; i++, ly += 3) hline(x + 3, x + w - 4 - (hash2(i, x) * 6 | 0), ly, o.lineInk ?? C.haze);
}
// gpuPx: a glowing compute box (GPU / server blade). (x, y) = top-left. o: w (default 18), h (default 7), k (fan spin phase), hot (glow 0..1)
function gpuPx(x, y, o = {}) {
  const w = o.w ?? 18, h = o.h ?? 7, k = o.k ?? T * 3, hot = o.hot ?? .6;
  if (hot > 0) glow(x + w / 2, y + h / 2, w * .9, { tab: WARM, k: hot * 1.3, ry: h * 1.6 });
  rectf(x, y, w, h, C.night); rectf(x, y, w, 1, C.dusk); rectf(x, y + h - 1, w, 1, C.void);
  for (const fx of [x + 4, x + w - 5]) { circf(fx, y + (h >> 1), 2, C.ink); const a = Math.floor(k * 4) % 2; pset(fx + (a ? 1 : 0), y + (h >> 1) - (a ? 0 : 1), C.haze); pset(fx - (a ? 1 : 0), y + (h >> 1) + (a ? 0 : 1), C.haze); }
  hline(x + 7, x + w - 8, y + 2, C.amber); hline(x + 7, x + w - 8, y + h - 3, hot > .5 ? C.gold : C.clay);
}
// laptopPx: open laptop, screen facing the viewer. (x, y) = bottom-centre of the base. o: w, screen (ink), glow (tab|false)
function laptopPx(x, y, o = {}) {
  const w = o.w ?? 16, sh = Math.round(w * .62), sx = _r(x - w / 2), scr = col(o.screen ?? C.mint);
  if (o.glow !== false) glow(x, y - sh / 2, w * 1.3, { tab: o.glow ?? GREEN, k: 1.1 });
  rectf(sx, y - sh - 2, w, sh, C.void); rectf(sx + 1, y - sh - 1, w - 2, sh - 2, scr);
  rectf(sx - 2, y - 2, w + 4, 2, C.dusk); pset(sx - 2, y - 1, C.navy); pset(sx + w + 1, y - 1, C.navy);
  return { sx: sx + 1, sy: y - sh - 1, sw: w - 2, sh: sh - 2 };
}

// =====================================================================================================
// STANDARD SETS
// =====================================================================================================
// homeScene(t, o): Clawd's hill under the turning sky: the style's home base (intro, choruses, placeholders).
// o: sky ({…} sky options), stars ({…}), moon ([x, y, r] | false), moonOpts, ledger ({…} | false), city ({…} | false),
//    weather (kind | false), clawd ({…} clawdPx options plus x | false), lantern (false to drop Clawd's lantern), hillX (summit x),
//    dy (tilt: positive moves the land down, i.e. the camera looks up; sky and stars move at 30 %, far ridge at 60 %)
// Returns {ground(x) → screen y of the hill top, clawd: clawdPx info}.
function homeScene(t, o = {}) {
  const dy = o.dy ?? 0;
  sky({ dy: Math.round(dy * .3), ...(o.sky || {}) });
  starfield(t, { dy: dy * .3, ...(o.stars || {}) });
  if (o.moon !== false) { const [mx, my, mr] = o.moon || [392, 46, 9]; moon(mx, my + dy * .3, mr, o.moonOpts || {}); }
  if (o.ledger !== false) ledger(t, { dy: dy * .3, ...(o.ledger || {}) });
  view(0, -Math.round(dy * .6));
  if (o.city !== false) city(t, { y: 204, x0: 262, grow: { intro: .15, V1: .25, C1: .3, V2: .5, C2: .55, V3: .75, C3: .8, V4: .95, C4: 1, outro: 1 }[sectionAt(t)] ?? .5, dc: 380, lit: .3, ...(o.city || {}) });
  ridge({ y: 214, amp: 14, seed: 3, ink: C.ink, rim: C.night, freq: 1 / 80 });
  view(0, -dy);
  const hx = o.hillX ?? 118, g = hill({ cx: hx, y: 196, w: 150, drop: 46, ink: C.void, rim: C.pine, snow: seasonAt(t) === 'winter' ? C.haze : undefined });
  grass(0, LW, g, t, { ink: C.pine });
  let info = null;
  if (o.clawd !== false) {
    const cl = o.clawd || {}, x = cl.x ?? hx - 2;
    if (o.lantern !== false) handLantern(x + 18, g(x + 18));
    info = clawdPx(x, g(x), { u: 2, pose: 'sit', eyes: 'up', outline: ['C4', 'outro'].includes(sectionAt(t)) ? C.wine : undefined, ...cl });
  }
  view(0, 0);
  if (o.weather !== false) weather(t, o.weather ?? 'auto');
  return { ground: x => g(x) + dy, clawd: info };
}

// =====================================================================================================
// OVERLAYS: dissolves between shots, the typed caption, the dot-matrix date, and the final upscale
// =====================================================================================================
// Transitions: by default each shot dissolves in from the previous one over DISSOLVE s (an ordered-dither crossfade).
// A shot may call cutIn() (hard cut) or dissolveIn(dur) on any frame of its window.
const DISSOLVE = .5;
let _trans = null;
function cutIn() { _trans = { dur: 0 }; }
function dissolveIn(dur = DISSOLVE) { _trans = { dur }; }

function _dissolve(t, s) {
  const lt = t - s.start, dur = _trans ? _trans.dur : DISSOLVE;
  if (dur <= 0 || lt >= dur) return;
  const i = SEGS.indexOf(s), prev = SEGS[i - 1];
  if (!prev || !SHOTS[prev.key]) return;
  _FBD.set(FB);
  const saved = [_noCaption, _noStamp, _captionStyle, _trans, VX, VY];
  FB.fill(0); VX = VY = 0; noClip();
  try { const d = prev.end - prev.start; SHOTS[prev.key](clamp((t - prev.start) / d), t - prev.start, d, t, prev); }
  catch (e) { console.error(`dissolve: shot ${prev.key} @ ${t.toFixed(2)}: ${e.stack || e}`); }
  [_noCaption, _noStamp, _captionStyle, _trans, VX, VY] = saved; noClip();
  const k = ease(lt / dur);
  for (let y = 0; y < LH; y++) { const row = y * LW, br = (y & 7) << 3; for (let x = 0; x < LW; x++) if (BAYER[br | (x & 7)] < k) FB[row + x] = _FBD[row + x]; }
}
// The sung line, typed out at the bottom. Caption rules: see STYLE.md. captionStyle({color, y}) recolours (palette name or index) /
// moves it (y = cap-top in low-res px, default 252); hideCaption() hides it for this frame.
const CAPTION_Y = 252;
function _curLine(t) { for (let i = LINES.length - 1; i >= 0; i--) if (LINES[i].start <= t) return LINES[i]; return null; }
function captionText(L) { return L.text.replace(/\s*—\s*$/, '').replace(/\s+—\s+/g, ' — '); }
function _drawCaption(t) {
  if (_noCaption) return;
  const L = _curLine(t); if (!L) return;
  const fade = clamp((t - (L.end + .35)) / .35); if (fade >= 1) return;
  const st = _captionStyle || {}, text = captionText(L), age = t - L.start, dur = L.end - L.start;
  const typeDur = clamp(text.length / 16, .45, Math.max(.45, dur * .75)), n = Math.max(1, Math.ceil(text.length * clamp(age / typeDur)));
  let ink = st.color !== undefined ? col(st.color) : L.sec[0] === 'C' ? C.gold : L.sec === 'outro' ? C.haze : C.cream;
  if (typeof ink !== 'number' || ink > 15) ink = C.cream;  // zine-style hex colours don't apply here
  let y = st.y ?? CAPTION_Y; if (y > LH) y = Math.round(y / PXS) - 4;
  const w = ptextW(text), x0 = Math.round((LW - w) / 2), vis = 1 - fade;
  rectf(x0 - 5, y - 4, w + 10, 16, dim(.55 * vis));
  const typing = n < text.length;
  ptext(text, x0, y, vis < 1 ? veil(ink, vis) : ink, { n, shadow: vis < 1 ? veil(C.void, vis) : C.void });
  if (typing) { const cw = ptextW(text.slice(0, n)); rectf(x0 + cw + 2, y, 3, 7, veil(ink, .9 * vis)); }
}
// The date: small dot-matrix year (rolls through the years it skips) with the month/day above it, top-left.
function _dateInfo(t) {
  let cur = null, prev = null;
  for (const s of SEGS) { if (s.start > t) break; if (s.date && (!cur || s.date !== cur.date)) { prev = cur; cur = s; } }
  return cur ? { text: cur.date, age: t - cur.start, prev: prev ? prev.date : null } : null;
}
const DATE_X = 9, DATE_Y = 8;
function _drawDate(t) {
  if (_noStamp) return;
  const d = _dateInfo(t); if (!d) return;
  const m = d.text.match(/^(.*?)\s*(\d{4})$/), md = m ? m[1] : d.text, yr = m ? +m[2] : null;
  const pm = d.prev && d.prev.match(/(\d{4})$/), py = pm ? +pm[1] : yr;
  const kY = easeOut(clamp(d.age / (.35 * Math.max(1, Math.abs(yr - py))))), shownY = py && yr && yr !== py ? Math.round(lerp(py, yr, kY)) : yr;
  const kM = clamp(d.age / .45), pmd = d.prev ? (d.prev.match(/^(.*?)\s*\d{4}$/) || [0, d.prev])[1] : '';
  // a soft dithered plate keeps it legible over busy scenes; month/day in F3 (cross-dissolves from the previous one), year in dot-matrix F5 ×2
  rectf(DATE_X - 4, DATE_Y - 3, 57, 28, dim(.6));
  if (md !== pmd && kM < 1 && pmd) ptext(pmd, DATE_X, DATE_Y, veil(C.haze, 1 - kM), { font: 3, shadow: veil(C.void, 1 - kM) });
  if (md) ptext(md, DATE_X, DATE_Y, md !== pmd ? veil(C.haze, kM) : C.haze, { font: 3, shadow: md !== pmd ? veil(C.void, kM) : C.void });
  if (shownY) ptext(String(shownY), DATE_X, DATE_Y + 8, C.cream, { scale: 2, dots: true, shadow: C.ink, off: C.ink });
}
// Frames with no shot yet (unpainted chapters): the home scene with the line written in the sky.
function _placeholder(t, s) {
  FB.fill(0); VX = VY = 0; noClip();
  homeScene(t, {});
  if (s) { ptext(s.key, 240, 80, C.gold, { align: 'center', scale: 2, dots: true }); if (s.text) ptext(s.text, 240, 104, C.haze, { align: 'center', maxW: 300 }); }
}
function _flush() {
  for (let i = 0; i < FB.length; i++) _u32[i] = _PAL32[FB[i]];
  _lg.putImageData(_img, 0, 0);
  ctx.save(); ctx.setTransform(RS, 0, 0, RS, 0, 0); ctx.globalAlpha = 1; ctx.globalCompositeOperation = 'source-over';
  ctx.imageSmoothingEnabled = false; ctx.drawImage(_lo, 0, 0, W, H); ctx.restore();
}
OVERLAYS.push((t, s) => {
  try {
    if (!(s && SHOTS[s.key])) _placeholder(t, s);
    else _dissolve(t, s);
    VX = VY = 0; noClip();
    _drawCaption(t); _drawDate(t);
  } catch (e) { console.error(`dither overlay @ ${t.toFixed(2)}: ${e.stack || e}`); }
  _flush();
  FB.fill(0); VX = VY = 0; noClip(); _trans = null;
  _noCaption = false; _noStamp = false; _captionStyle = null;
});

;
// ---- styles/dither/ch/c01_intro.js ----
// c01_intro.js: Intro (0 → V1.1, ~12 s, fingerpicked guitar alone).
// The sky wakes up star by star; the camera tilts down to a dark hill; tiny Clawd climbs it with a lantern and sits;
// the title is written across the sky in stars, holds, then drifts apart into the starfield as a shooting star falls.
(() => {
  const TITLE = ["WE DIDN'T START", 'THE SCALING'];
  const SUB = '(indie folk)';
  // Star-dots of the title, computed once: dot-matrix letters at scale 3 (1-px stars, 2-px gaps).
  let dots = null;
  const titleDots = () => dots || (dots = [
    ...textDots(TITLE[0], 240, 44, { scale: 3, align: 'center' }).map(d => ({ ...d, line: 0 })),
    ...textDots(TITLE[1], 240, 74, { scale: 3, align: 'center' }).map(d => ({ ...d, i: d.i + TITLE[0].length, line: 1 })),
  ]);

  section('intro', (p, lt, d, t, s) => {
    hideCaption();
    const b = i => beatAt(s, i);                       // slow beat i of the intro (≈0.8 s apart)
    // Camera: looking up at the sky, then a slow tilt down to the hill (beats 4 → 8).
    const tilt = Math.round(150 * (1 - ease(clamp((lt - b(3.6)) / (b(8) - b(3.6))))));
    // Clawd walks in from the left (beats 5 → 8), sits at the summit, sets the lantern down.
    const hx = 118, walkK = clamp((lt - b(5)) / (b(8) - b(5) + .2)), arrived = walkK >= 1;
    const cx = Math.round(lerp(-14, hx - 2, easeOut(walkK) * .15 + walkK * .85));

    const home = homeScene(t, {
      dy: tilt,
      stars: { appear: clamp((lt - .3) / 3.2) },
      ledger: false,
      clawd: false,
      weather: false,
      moonOpts: { glow: 1 },
    });
    view(0, -tilt);
    const gy = x => home.ground(x) - tilt;
    // fireflies in the grass (June night)
    for (let i = 0; i < 9; i++) firefly(30 + hash2(i, 5) * 200 + Math.sin(t * .4 + i) * 10, gy(30 + hash2(i, 5) * 200) - 6 - hash2(i, 6) * 18 + Math.sin(t * .6 + i * 2) * 4, t, i);
    if (!arrived) {
      const c = clawdPx(cx, gy(cx), { u: 2, walk: lt * 1.25, eyes: 'open', lookX: .6 });
      handLantern(c.handR[0] + 2, c.handR[1] + 8, { glow: 22 });
    } else {
      const lookUp = lt > b(8.6), follow = lt > b(13.2);
      handLantern(hx + 16, gy(hx + 16), { glow: 24 });
      clawdPx(hx - 2, gy(hx - 2), { u: 2, pose: 'sit', eyes: lookUp ? 'up' : 'open', lookX: follow ? 1 : lookUp ? .5 : 0, lookY: follow ? -.5 : 0 });
    }
    view(0, 0);

    // The title in stars: letters light one by one (beats 8.5 → 11), hold, then drift up and dissolve into the sky.
    const t0 = b(8.5), drift0 = b(12), n = TITLE[0].length + TITLE[1].length;
    if (lt > t0) {
      const sb = sbeat(t);
      for (const dt of titleDots()) {
        const born = t0 + dt.i / n * 2.1 + hash2(dt.x, dt.y) * .25, age = lt - born;
        if (age < 0) continue;
        const dk = clamp((lt - drift0 - hash2(dt.x, 3) * .8) / 2.2);
        const x = dt.x + (hash2(dt.x, dt.y + 9) - .5) * 30 * ease(dk), y = dt.y - (6 + hash2(dt.y, dt.x) * 16) * ease(dk);
        if (dk >= 1) continue;
        const big = hash2(dt.x * 3, dt.y) < .07, tw = hash2(dt.x + dt.y * 480, sb) < .12;
        if (age < .35) sparkle(x, y, 1, C.cream, C.gold);
        else if (dk > .55) pset(x, y, veil(C.dusk, 1 - (dk - .55) / .45));
        else if (dk > .25) pset(x, y, C.haze);
        else if (big || (tw && spulse(t, 3) > .5)) sparkle(x, y, 1, C.cream, C.haze);
        else pset(x, y, hash2(dt.x, dt.y + 1) < .75 ? C.cream : C.gold);
      }
      const sk = rise(lt, b(10.4), .8) * (1 - rise(lt, drift0 + .4, 1));
      if (sk > 0) ptext(SUB, 240, 102, veil(C.haze, sk), { align: 'center' });
    }
    // A shooting star as the title scatters: the first thing to fall.
    shootingStar(300, 30, 430, 92, (lt - b(13.1)) / 1.1, { len: 30 });

    // Fade up from black: every colour climbs out of the void (dithered, no alpha).
    const fk = 7 * (1 - ease(clamp(lt / 2.8)));
    if (fk > 0) fadeAll(fk);
  });
})();

;
// ---- styles/dither/ch/c02_v1.js ----
// c02_v1.js: Verse 1, Jun 2017 → Oct 2024. Each headline arrives as a small light in a big night.
// Palette leans cool navy with one warm event per shot; consecutive shots alternate wide/close and warm/cool.
(() => {
  // ---------- private helpers ----------
  const B = (s, i) => beatAt(s, i);
  const fx = (seed, n = 0) => hash2(seed, boilFrame(T) * 7 + n);   // per-frame flicker (12/s)
  // a far hill silhouette with a lit rim; returns ground fn
  const farHill = (cx, y, w, drop, ink = C.ink, rim = C.night) => hill({ cx, y, w, drop, ink, rim });
  // 5-px gold star (EU circle, badges)
  const STAR5 = sprite(['..a..', '.aaa.', 'aabaa', '.aaa.', '.a.a.']);
  const ROCKET = sprite(['..7..', '.777.', '.bbb.', '.b7b.', '.bbb.', '.bbb.', '..1..', '..1..', '..1..']);

  // ======================================================================
  // V1.1 First, "Attention" lit the fuse — eight Googlers light a paper rocket on a far hill; it blooms into the dusty-red
  // starburst, ATTENTION. Clawd watches from its own hill.
  line('V1', 1, (p, lt, d, t, s) => {
    const b = i => B(s, i);
    sky({ cy: 320, r: 380 });
    starfield(t, { density: .8 });
    // far hill (right) with the launch party
    const g = farHill(360, 200, 130, 34);
    const lx = 362, ly = g(lx);
    const party = [318, 327, 336, 345, 380, 389, 398, 407];
    const burstT = b(2) - .05, launchT = b(1) - .05;
    party.forEach((x, i) => personPx(x, g(x), { u: 1, skin: SKIN[i % 3], top: [C.navy, C.teal, C.violet, C.dusk][i % 4], hair: ['short', 'long', 'curly', 'short', 'bun', 'short', 'slick', 'short'][i], hairC: [C.void, C.wine, C.void, C.rust][i % 4], aR: i === 3 && lt < launchT ? -.2 : lt > burstT ? 1.1 : -1.25, aL: lt > burstT ? 1.1 : -1.25, eyes: lt > launchT ? 'up' : 'dot' }));
    tagPx('GOOGLE ×8', 420, g(420) - 16);
    // the fuse: from the match (x 350) along the ground to the stand
    const fk = rise(lt, .08, launchT - .18, k => k), fuse0 = 348, fuse1 = lx - 2, burnX = lerp(fuse0, fuse1, fk);
    for (let x = Math.ceil(burnX); x <= fuse1; x += 2) pset(x, g(x) - 1, C.haze);
    if (lt > .1 && lt < launchT + .05) {
      glow(burnX, g(burnX) - 2, 9, { tab: WARM, k: 1.4 });
      sparkle(burnX, g(burnX) - 2, 1, C.cream, C.gold);
      for (let i = 0; i < 4; i++) pset(burnX + (fx(i) - .5) * 6, g(burnX) - 2 - fx(i, 1) * 5, i % 2 ? C.gold : C.amber);
    }
    // launch stand + rocket
    pline(lx - 3, ly, lx, ly - 7, C.void); pline(lx + 3, ly, lx, ly - 7, C.void);
    const rk = clamp((lt - launchT) / (burstT - launchT)), ry = lerp(ly - 9, 62, rk ** 1.7);
    if (rk < 1) {
      if (rk > 0) {
        for (let i = 0; i < 14; i++) { const f = i / 14; pset(lx + (fx(i) - .5) * (1 + i * .35), ry + 9 + i * 2.2, f < .3 ? C.cream : f < .6 ? veil(C.gold, 1 - f) : veil(C.clay, 1 - f)); }
        glow(lx, ry + 8, 12, { tab: WARM, k: 1.3 });
      }
      spr(ROCKET, lx - 2, Math.round(ry));
    }
    // the bloom
    const bk = clamp((lt - burstT) / .45);
    if (bk > 0) {
      const cx = lx, cy = 62, R = 44;
      if (bk < .35) glow(cx, cy, 90, { tab: LIT, k: 1.2 * (1 - bk / .35) });
      glow(cx, cy, 70, { tab: WARM, k: .7 * easeOut(bk) });
      starburst(cx, cy, R, easeOut(bk) * (1 + .03 * breathe(t, 2)), { n: 14, rot: lt * .12, inner: .38 });
      // willow sparks falling from the bloom
      const age = lt - burstT;
      for (let i = 0; i < 26; i++) {
        const a = i / 26 * TAU + hash(i) * .2, sp = 34 + hash2(i, 2) * 26, x = cx + Math.cos(a) * sp * easeOut(clamp(age / .9)) * 1.25, y = cy + Math.sin(a) * sp * easeOut(clamp(age / .9)) + age * age * 14;
        if (age > .1) pset(x, y, age < .5 ? C.cream : age < .8 ? C.gold : veil(C.amber, 1.4 - age));
      }
      for (let i = 0; i < 7; i++) { const a = i / 7 * TAU + .3, r = R * 1.35 + 4 * breathe(t, 2, i / 7); sparkle(cx + Math.cos(a) * r, cy + Math.sin(a) * r, hash2(i, sbeat(t)) < .5 ? 1 : 2); }
      const tk = rise(lt, burstT + .12, .35);
      if (tk > 0) {
        ptext('ATTENTION', cx, cy - 4, veil(C.cream, tk), { align: 'center', shadow: veil(C.wine, tk) });
        ptext('is all you need', cx, cy + R + 10, veil(C.haze, rise(lt, burstT + .35, .4)), { align: 'center' });
      }
    }
    // Clawd's hill (foreground left)
    const hg = hill({ cx: 64, y: 214, w: 120, drop: 44, ink: C.void, rim: C.pine });
    grass(0, 200, hg, t);
    handLantern(84, hg(84));
    clawdPx(62, hg(62), { u: 2, pose: 'sit', eyes: lt > launchT ? 'up' : 'open', lookX: 1, blink: lt < burstT });
    weather(t, 'fireflies', { n: 10, x0: 0, x1: 240, y1: 240 });
  });

  // ======================================================================
  // V1.2 Scaling laws you can't refuse — the winter sky turns into log-log paper; stars land on a perfectly straight line,
  // and the line's next star slides down into Clawd's paws (an offer you can't refuse).
  line('V1', 2, (p, lt, d, t, s) => {
    const b = i => B(s, i);
    sky({ cy: 330, r: 360 });
    starfield(t, { density: .45 });
    // graph paper: decades + log minors, dotted
    const X0 = 70, X1 = 460, Y0 = 34, Y1 = 196, DX = 78, DY = 54, gk = rise(lt, 0, .5);
    const lg = [0, .301, .477, .602, .699, .778, .845, .903, .954];
    for (let k = 0; k < 5; k++) lg.forEach((l, m) => { const x = Math.round(X0 + DX * (k + l)); if (x <= X1) pline(x, Y0, x, Y1, veil(m ? C.navy : C.dusk, gk), { every: m ? 4 : 2 }); });
    for (let k = 0; k < 3; k++) lg.forEach((l, m) => { const y = Math.round(Y1 - DY * (k + l)); if (y >= Y0) pline(X0, y, X1, y, veil(m ? C.navy : C.dusk, gk), { every: m ? 4 : 2 }); });
    ptext('LOSS', X0 + 3, Y0 + 3, veil(C.haze, gk), { font: 3 });
    ptext('COMPUTE →', X1 - 2, Y1 - 8, veil(C.haze, gk), { font: 3, align: 'right' });
    // the law: stars landing on a straight line, one per eighth
    const P0 = [X0 + 14, Y0 + 14], P1 = [X1 - 40, Y1 - 12], N = 9, dt = .19, t0 = .12;
    const at = i => [lerp(P0[0], P1[0], i / (N - 1)), lerp(P0[1], P1[1], i / (N - 1))];
    const nOn = clamp((lt - t0) / (dt * (N - 1)), 0, 1) * (N - 1);
    plines([P0, [lerp(P0[0], P1[0], nOn / (N - 1)), lerp(P0[1], P1[1], nOn / (N - 1))]], C.haze);
    for (let i = 0; i < N; i++) {
      const age = lt - (t0 + i * dt); if (age < 0) continue;
      const [x, y] = at(i); sparkle(x, y, age < .15 ? 3 : age < .3 ? 2 : 1, C.cream, age < .3 ? C.gold : C.haze);
    }
    // snowy field + Clawd
    const gy = x => Math.round(222 + Math.sin(x * .02) * 3 + Math.sin(x * .07 + 1) * 1.5);
    for (let x = 0; x < LW; x++) { const top = gy(x); pset(x, top, C.cream); rectf(x, top + 1, 1, LH - top, grad([C.haze, C.dusk, C.navy], (xx, yy) => (yy - top) / 30)); }
    const cx = 432, cyG = gy(cx);
    // the prediction line runs on, and the next star slides down it
    const pk = rise(lt, b(1.9), .5, k => k);
    if (pk > 0) {
      const ex = lerp(P1[0], cx, pk), ey = lerp(P1[1], cyG - 20, pk);
      pline(P1[0], P1[1], ex, ey, C.gold, { every: 3 });
    }
    const sk = rise(lt, b(2.2), .45, easeIn);
    const holding = sk >= 1;
    if (sk > 0 && !holding) sparkle(lerp(P1[0] + 16, cx, sk), lerp(P1[1] + 5, cyG - 17, sk), 2, C.cream, C.gold);
    const c = clawdPx(cx, cyG, { u: 2, pose: 'sit', eyes: holding ? 'spark' : 'up', lookX: holding ? 0 : -1, hat: 'beanie', hatInk: C.rust, aL: sk > .3 ? 1.1 : 0, aR: sk > .3 ? 1.1 : 0 });
    if (holding) { glow(cx, c.top - 4, 14, { tab: LIT, k: 1.2 }); sparkle(cx, c.top - 4, spulse(t, 3) > .5 ? 2 : 1, C.cream, C.gold); }
    weather(t, 'snow', { n: 50 });
  });

  // ======================================================================
  // V1.3 Gwern said "stack the compute high" — a hooded figure on a hill conducts a tower of glowing GPU boxes up into the stars.
  line('V1', 3, (p, lt, d, t, s) => {
    sky({ cy: 300, r: 330, vert: .45 });
    starfield(t, { density: .9 });
    moon(352, 34, 8, { phase: .15 });
    const g = hill({ cx: 250, y: 226, w: 200, drop: 34, ink: C.void, rim: C.pine });
    grass(0, LW, g, t);
    // the tower: boxes drop onto the stack faster and faster, up past the moon's height
    const N = 17, bx = 250, gy = g(262) - 1, BW = 26, BH = 9, SP = 10;
    for (let i = 0; i < N; i++) {
      const land = .08 + 2.45 * (i / (N - 1)) ** .7, age = lt - land;
      if (age < -.18) break;
      const slot = gy - SP * (i + 1) + 1, fall = age < 0 ? easeIn(clamp(1 + age / .18)) : 1, y = Math.round(lerp(slot - 40, slot, fall)) + (age > 0 && age < .08 ? 1 : 0);
      gpuPx(bx, y, { w: BW, h: BH, hot: i >= N - 2 ? 1 : .4, k: t * 3 + i });
    }
    if (lt > 2.55) sparkle(bx + BW / 2, gy - SP * N - 6, spulse(t, 3) > .5 ? 3 : 2, C.cream, C.gold);
    // Gwern, hood up, conducting: "higher"
    const up = .75 + .35 * breathe(t, 1);
    personPx(214, g(214), { u: 3, hair: 'hood', hoodC: C.ink, top: C.ink, pants: C.void, aR: up, aL: -1.1 });
    paperPx(186, g(186) - 9, 10, 8, { lines: 2 });
    weather(t, 'petals', { n: 20 });
  });

  // ======================================================================
  // V1.4 Few-shot learners multiply — one firefly becomes two, four, eight… sixty-four, then they settle into GPT-3.
  line('V1', 4, (p, lt, d, t, s) => {
    sky({ cy: 310, r: 340, ramp: [C.void, C.ink, C.night, C.navy, C.dusk] });
    starfield(t, { density: .6 });
    ridge({ y: 206, amp: 12, seed: 11, ink: C.ink, rim: C.night, freq: 1 / 70 });
    const g = hill({ cx: 240, y: 230, w: 300, drop: 30, ink: C.void, rim: C.pine });
    grass(0, LW, g, t, { h: 4, step: 2 });
    const C0 = [240, 138], N = 64, gen = j => j === 0 ? 0 : Math.floor(Math.log2(j)) + 1, tb = g0 => g0 === 0 ? 0 : .12 + .34 * (g0 - 1);
    const formT = 2.25, targets = textDots('GPT-3', 240, 56, { scale: 4, align: 'center' });
    const pos = [];
    const wander = j => { const a = hash2(j, 1) * TAU + t * .5 * (hash2(j, 2) - .5), r = 6 + Math.sqrt(hash2(j, 3)) * (12 + 70 * clamp(lt / 2.3)); return [C0[0] + Math.cos(a) * r * 1.5 + Math.sin(t * 1.3 + j) * 3, C0[1] + Math.sin(a) * r * .75 + Math.cos(t * 1.1 + j * 2) * 3]; };
    for (let j = 0; j < N; j++) {
      const g0 = gen(j), age = lt - tb(g0);
      if (age < 0) { pos.push(null); continue; }
      const par = j === 0 ? null : pos[j - 2 ** (g0 - 1)], w = wander(j), k = easeOut(clamp(age / .35));
      let x = par ? lerp(par[0], w[0], k) : w[0], y = par ? lerp(par[1], w[1], k) : w[1];
      const tg = targets[j], fk = tg ? ease(clamp((lt - formT - hash(j) * .3) / .55)) : 0;
      if (tg) { x = lerp(x, tg.x, fk); y = lerp(y, tg.y, fk); }
      pos.push([x, y]);
      if (fk >= 1) sparkle(x, y, hash2(j, sbeat(t)) < .15 && spulse(t, 3) > .5 ? 2 : 1, C.cream, C.gold);
      else if (age < .15) { glow(x, y, 8, { tab: LIT, k: 1 }); sparkle(x, y, 2, C.cream, C.gold); }
      else { const bl = breathe(t, 2, hash(j + 3)); if (bl > .25) sparkle(x, y, bl > .7 ? 1 : 0, bl > .7 ? C.cream : C.gold, C.amber); else pset(x, y, C.amber); }
    }
    const lk = rise(lt, formT + .6, .4);
    if (lk > 0) ptext('175 BILLION PARAMETERS', 240, 94, veil(C.haze, lk), { font: 3, align: 'center' });
    clawdPx(70, g(70), { u: 1, pose: 'sit', eyes: 'up', lookX: 1 });
  });

  // ======================================================================
  // V1.5 ChatGPT, overnight — a sleeping valley; one window lights up green, then the whole town does, faster and faster,
  // while the moon crosses the sky and dawn starts to show. The counter climbs to 100,000,000.
  const TOWN = (() => {
    const rows = [
      { y: 172, n: 22, w: [9, 12], h: [6, 8], wall: C.ink, roof: C.void, x0: 6, gap: [4, 14], win: 1, ws: 3 },
      { y: 200, n: 13, w: [16, 20], h: [10, 12], wall: C.ink, roof: C.void, x0: 2, gap: [8, 22], win: 2, ws: 3 },
      { y: 238, n: 7, w: [30, 36], h: [18, 20], wall: C.night, roof: C.ink, x0: 14, gap: [22, 40], win: 2, ws: 5 },
    ];
    const H = []; let wi = 0;
    rows.forEach((r, ri) => { let x = r.x0; for (let i = 0; i < r.n && x < 470; i++) { const w = Math.round(lerp(r.w[0], r.w[1], hash2(i, ri + 30))), h = Math.round(lerp(r.h[0], r.h[1], hash2(i, ri + 40))); H.push({ x, y: r.y + Math.round(hash2(i, ri + 50) * 3), w, h, row: ri, wall: r.wall, roof: r.roof, win: r.win, ws: r.ws, w0: wi }); wi += r.win; x += w + Math.round(lerp(r.gap[0], r.gap[1], hash2(i, ri + 60))); } });
    const rank = Array.from({ length: wi }, (_, i) => i).sort((a, b) => hash(a * 13 + 7) - hash(b * 13 + 7));
    const first = H.find(h => h.row === 2 && h.x > 180).w0;   // the first window: a near house, centre-right
    rank.splice(rank.indexOf(first), 1); rank.unshift(first);
    const order = new Int16Array(wi); rank.forEach((w, i) => { order[w] = i; });
    return { H, order, N: wi };
  })();
  line('V1', 5, (p, lt, d, t, s) => {
    sky({ cy: 320, r: 370 });
    starfield(t, { density: .9, rot: lt * .22 });   // time-lapse: the sky wheels overnight
    const mk = clamp(lt / d), mx = lerp(40, 440, mk), my = 140 - Math.sin(mk * Math.PI) * 78;
    moon(mx, my, 7, { phase: .3 });
    const dawn = rise(lt, 2.2, 1.2, k => k);
    if (dawn > 0) { glow(240, 250, 320, { tab: LIT, k: 1.6 * dawn, ry: 120, pow: 1.3 }); glow(240, 250, 220, { tab: WARM, k: .8 * dawn, ry: 70 }); }
    ridge({ y: 172, amp: 10, seed: 21, ink: C.ink, rim: C.night });
    // how many windows are lit: exponential, 1 → all
    const k = clamp((lt - .25) / 2.35), nLit = k <= 0 ? 0 : Math.floor(TOWN.N ** k);
    const lit = w => TOWN.order[w] < nLit;
    let firstPos = null;
    // rows drawn back to front with their own ground
    [0, 1, 2].forEach(row => {
      if (row === 1) ridge({ y: 196, amp: 8, seed: 22, ink: C.ink, rim: C.navy, freq: 1 / 50 });
      if (row === 2) ridge({ y: 232, amp: 6, seed: 23, ink: C.void, rim: C.night, freq: 1 / 40 });
      for (const hs of TOWN.H) if (hs.row === row) {
        const wins = house(hs.x, hs.y, { w: hs.w, h: hs.h, wall: hs.wall, roof: hs.roof, windows: hs.win, ws: hs.ws, lit: i => lit(hs.w0 + i) ? C.mint : false, snow: row >= 1 ? C.haze : undefined, chimney: row === 2 });
        wins.forEach(([wx, wy], i) => { if (lit(hs.w0 + i)) { if (row > 0) glow(wx, wy, row === 2 ? 14 : 7, { tab: GREEN, k: row === 2 ? 1.2 : .9 }); if (row < 2) pset(wx, wy, C.cream); } if (TOWN.order[hs.w0 + i] === 0) firstPos = [wx, wy]; });
      }
    });
    if (firstPos && lt > .3 && lt < 1.5) bubblePx('hi!', firstPos[0], firstPos[1] - 8, { tail: [firstPos[0], firstPos[1] - 3], n: Math.ceil((lt - .3) * 12) });
    // the counter
    const users = k <= 0 ? 0 : Math.round(10 ** (8 * k)), txt = users.toLocaleString('en-US');
    if (lt > .25) { ptext(txt, 240, 22, C.cream, { align: 'center', scale: 2, dots: true, off: C.ink }); ptext(users === 1 ? 'user' : 'users', 240, 40, C.haze, { align: 'center' }); }
    weather(t, 'snow', { n: 18 });
  });

  // ======================================================================
  // V1.6 Sydney's chats gave Roose a fright — through a snowy window: Kevin at his laptop; hearts pour out of the screen
  // ("I'm Sydney ♥ I love you"); his hair stands on end and he slams the lid.
  line('V1', 6, (p, lt, d, t, s) => {
    const b = i => B(s, i);
    const WX = 120, WY = 44, WW = 240, WH = 150;
    const fright = lt > b(1) - .1, shut = lt > b(2);
    layer('v1.6-wall', () => {
      rectf(0, 0, LW, LH, C.night);
      for (let y = 0; y < LH; y += 5) { hline(0, LW, y, C.ink); for (let x = (y / 5) % 2 ? 0 : 9; x < LW; x += 18) vline(x, y, y + 4, C.ink); }
      rectf(0, 0, LW, 18, C.ink); for (let x = 0; x < LW; x++) pset(x, 18 + (hash(x) < .5 ? 1 : 0), C.cream); rectf(0, 16, LW, 2, C.haze);
    });
    // the room through the window
    clipRect(WX, WY, WW, WH);
    rectf(WX, WY, WW, WH, C.wine);
    for (let x = WX + 6; x < WX + WW; x += 14) vline(x, WY, WY + 122, C.ink);   // wallpaper stripes
    const DT = WY + 124, kx = WX + WW / 2;
    glow(WX + 30, WY + 30, 60, { tab: WARM, k: .8 });                     // a warm lamp, off to the left
    rectf(WX + 22, WY + 20, 16, 8, C.amber); vline(WX + 30, WY + 28, DT, C.void);
    // Kevin, lit blue by his screen
    const hop = fright && !shut ? Math.round(3 * Math.abs(Math.sin((lt - b(1)) * 9))) : 0;
    personPx(kx, DT + 20, { u: 5, dy: hop, top: C.dusk, hair: fright ? 'spiky' : 'short', hairC: C.void, eyes: fright ? 'wide' : 'dot', mouth: fright ? 'o' : 'smile', aL: fright ? 1.25 : -.6, aR: fright ? 1.25 : -.6, skin: C.gold });
    if (!shut) glow(kx, DT - 14, 30, { tab: COOL, k: 1.1 });
    rectf(WX, DT, WW, WH - (DT - WY), C.ink); hline(WX, WX + WW, DT, C.rust);     // desk
    // the laptop: we see the back of the lid; the screen faces Kevin
    const lx = kx, ly = DT;
    if (!shut) { rectf(lx - 15, ly - 18, 30, 18, C.navy); rectb(lx - 15, ly - 18, 30, 18, C.void); circf(lx, ly - 10, 2, C.dusk); hline(lx - 14, lx + 14, ly - 18, C.haze); }
    else { rectf(lx - 16, ly - 3, 32, 3, C.navy); hline(lx - 16, lx + 15, ly - 3, C.haze); }
    // hearts pour out of the screen while it's on; after the slam they fade
    for (let i = 0; i < 28; i++) {
      const born = .1 + i / 28 * (b(2) - .1), age = lt - born, fade = shut ? 1 - clamp((lt - b(2)) / .5) : 1;
      if (age < 0 || fade <= 0) continue;
      const side = hash(i) < .5 ? -1 : 1, x = lx + side * (4 + age * (18 + hash2(i, 4) * 60)) + Math.sin(age * 3 + i) * 4, y = ly - 20 - age * (16 + hash2(i, 1) * 34);
      if (fade < 1 && bay(Math.round(x), Math.round(y)) > fade) continue;
      heartPx(x, y, hash2(i, 2) < .3 ? 2 : 1, hash2(i, 3) < .5 ? C.rust : C.clay, C.amber);
    }
    if (!shut) {
      const bx = WX + 50, by = WY + 76;
      if (lt < b(1)) bubblePx("I'm Sydney ♥", bx, by, { font: 5, tail: [lx - 14, ly - 16], n: Math.ceil((lt - .1) * 22) });
      else bubblePx('I love you.', bx, by, { font: 5, tail: [lx - 14, ly - 16], n: Math.ceil((lt - b(1)) * 22), fill: C.gold });
    }
    noClip();
    // window frame, mullions, sill
    rectb(WX - 1, WY - 1, WW + 2, WH + 2, C.void); rectb(WX - 2, WY - 2, WW + 4, WH + 4, C.ink);
    vline(WX + WW / 3, WY, WY + WH, C.void); vline(WX + WW * 2 / 3, WY, WY + WH, C.void); hline(WX, WX + WW, WY + 40, C.void);
    rectf(WX - 8, WY + WH + 2, WW + 16, 4, C.dusk); rectf(WX - 8, WY + WH + 1, WW + 16, 1, C.cream);
    // one heart left stuck to the glass after the slam
    if (shut) heartPx(WX + WW * 2 / 3 + 22, WY + 60 + Math.min(20, (lt - b(2)) * 12), 2, C.rust, C.amber);
    weather(t, 'snow', { n: 70 });
  });

  // ======================================================================
  // V1.7 Six-month pause went nowhere fast — letter-signers hold up a PAUSE banner on a night platform; the AI express
  // thunders past without stopping.
  line('V1', 7, (p, lt, d, t, s) => {
    sky({ cy: 300, r: 340 });
    starfield(t, { density: .8 });
    moon(90, 40, 7, { phase: .5 });
    ridge({ y: 176, amp: 14, seed: 31, ink: C.ink, rim: C.night });
    // rails
    rectf(0, 186, LW, 6, C.ink); for (let x = (-Math.floor(t * 0) % 6); x < LW; x += 6) rectf(x, 191, 3, 1, C.night);
    hline(0, LW, 189, C.dusk);
    // the train: steam locomotive + lit carriages, never slowing
    const head = -40 + (lt - .35) * 230, cars = 6;
    const vx = head;
    if (head > -400) {
      for (let c = 0; c < cars; c++) {
        const x1 = vx - 42 - c * 50, x0 = x1 - 46;
        if (x1 < -10 || x0 > LW + 10) continue;
        rectf(x0, 160, 46, 26, C.ink); rectf(x0, 158, 46, 2, C.night); hline(x0, x1, 160, C.navy);
        for (let w = 0; w < 5; w++) { rectf(x0 + 4 + w * 9, 166, 5, 6, C.gold); pset(x0 + 4 + w * 9, 166, C.cream); }
        rectf(x0 + 2, 184, 42, 2, C.void); circf(x0 + 8, 186, 2, C.void); circf(x1 - 8, 186, 2, C.void);
      }
      // locomotive
      const lx = vx - 42;
      rectf(lx, 164, 36, 22, C.void); rectf(lx - 2, 154, 14, 32, C.void); rectf(lx + 26, 156, 5, 8, C.void);
      rectf(lx + 1, 158, 8, 6, C.amber); circf(lx + 36, 172, 3, C.gold); glow(lx + 38, 172, 26, { tab: LIT, k: 1.2 });
      polyf([[lx + 38, 169], [lx + 110, 150], [lx + 110, 196], [lx + 38, 176]], lit(.6));
      for (let w = 0; w < 3; w++) circf(lx + 6 + w * 11, 186, 3, C.void);
      ptext('AI', lx + 14, 169, C.rust, { font: 3 });
      // steam
      for (let i = 0; i < 10; i++) { const f = frac(t * .8 + i / 10), px = lx + 28 - f * 60, py = 150 - f * 26 - Math.sin(i) * 3; circf(px, py, 1 + f * 4, veil(C.haze, .75 * (1 - f))); }
    }
    // platform
    rectf(0, 204, LW, 66, C.night); hline(0, LW, 204, C.dusk); rectf(0, 205, LW, 1, C.navy);
    // the pause signal
    vline(70, 150, 204, C.void); circf(70, 146, 8, C.rust); circb(70, 146, 8, C.wine); rectf(66, 142, 3, 9, C.cream); rectf(72, 142, 3, 9, C.cream);
    glow(70, 146, 18, { tab: WARM, k: .6 });
    signPx('6 MONTHS', 70, 158, { font: 3 });
    // the signers and their banner (it flaps in the train's wind)
    const wind = head > 60 && head < 900 ? 1 : 0;
    const xs = [150, 168, 186, 204, 222, 240, 258, 276, 294];
    xs.forEach((x, i) => personPx(x, 238, { u: 2, skin: SKIN[i % 3], top: [C.teal, C.violet, C.dusk, C.clay, C.navy][i % 5], hair: ['short', 'long', 'curly', 'bun', 'short'][i % 5], hairC: [C.void, C.wine, C.gold, C.void][i % 4], aL: i === 0 ? 1.3 : -1.25, aR: i === xs.length - 1 ? 1.3 : -1.25, eyes: 'dot', lookX: wind ? -1 : 0, mouth: wind ? 'o' : 'none' }));
    vline(139, 186, 222, C.clay); vline(305, 186, 222, C.clay);
    const wave = x => wind ? Math.round(Math.sin(x * .22 - t * 18) * 1.6) : Math.round(Math.sin(x * .1 - t * 2) * .6);
    for (let x = 140; x < 305; x++) { const wv = wave(x); vline(x, 188 + wv, 206 + wv, C.cream); pset(x, 207 + wv, C.gold); }
    ptext('PAUSE', 222, 190, C.rust, { scale: 2, align: 'center', each: (i, ch, x) => ({ dy: wave(x + 5) }) });
    weather(t, 'petals', { n: wind ? 10 : 16, wind: wind ? 6 : 1 });
  });

  // ======================================================================
  // V1.8 Eliezer's "shut-it-down" blast — from a rooftop, a fedora'd figure blasts the city through a megaphone; the
  // lights go out in a wave… then flicker back on, one by one.
  line('V1', 8, (p, lt, d, t, s) => {
    const b = i => B(s, i);
    sky({ cy: 300, r: 340, ramp: [C.void, C.ink, C.night, C.navy, C.dusk] });
    starfield(t, { density: .7 });
    const blast = b(1) - .15, front = lt > blast ? (lt - blast) * 260 : -1, MX0 = 142, MY0 = 146;
    // the city (right), windows off once the blast front passes, back on later
    for (let bi = 0; bi < 11; bi++) {
      const x = 196 + bi * 26 + Math.round(hash(bi) * 6), w = 16 + Math.round(hash2(bi, 1) * 8), h = 30 + Math.round(hash2(bi, 2) * 70);
      rectf(x, 210 - h, w, h + 60, bi % 2 ? C.ink : C.void); hline(x, x + w - 1, 210 - h, C.navy);
      for (let wy = 210 - h + 4; wy < 206; wy += 5) for (let wx = x + 2; wx < x + w - 2; wx += 4) {
        const hs = hash2(wx, wy); if (hs > .55) continue;
        const d0 = Math.hypot(wx - MX0, wy - MY0), off = front > d0, back = lt > b(2.6) + hs * 1.2;
        if (off && !back) continue;
        pset(wx, wy, hs < .15 ? C.cream : hs < .35 ? C.gold : C.amber); pset(wx + 1, wy, hs < .35 ? C.gold : C.clay);
      }
    }
    // rooftop
    rectf(0, 180, 176, 90, C.void); hline(0, 176, 180, C.navy); rectf(24, 164, 12, 16, C.void); rectf(22, 162, 16, 2, C.ink);
    // Eliezer with the megaphone
    const shout = lt > blast && lt < b(2.2);
    const E = personPx(100, 180, { u: 4, hat: 'fedora', hatC: C.ink, beard: C.wine, top: C.ink, pants: C.void, aR: .25, mouth: shout ? 'o' : 'none', eyes: shout ? 'closed' : 'dot' });
    const [hx, hy] = E.handR;
    polyf([[hx, hy - 3], [hx + 18, hy - 9], [hx + 18, hy + 5], [hx, hy + 1]], C.haze); pline(hx + 18, hy - 9, hx + 18, hy + 5, C.cream); pline(hx, hy - 3, hx + 18, hy - 9, C.cream);
    rectf(hx - 2, hy - 2, 3, 4, C.dusk);
    const mx = hx + 19, my = hy - 2;
    // sound rings
    for (let k = 0; k < 4; k++) {
      const r = (lt - blast - k * .16) * 260; if (r <= 4 || r > 520) continue;
      for (let a = -.55; a <= .55; a += .7 / r) { const x = mx + Math.cos(a) * r, y = my + Math.sin(a) * r; if (bay(Math.round(x), Math.round(y)) < 1 - r / 560) pset(x, y, k === 0 ? C.cream : C.haze); }
    }
    const tk = clamp((lt - blast) / .6);
    if (tk > 0) ptext('SHUT IT ALL DOWN', 220, 34, C.cream, { align: 'center', scale: 2, n: Math.ceil(tk * 16), shadow: C.rust });
  });

  // ======================================================================
  // V1.9 Sam got fired, then rehired — booted out of a lit doorway into the autumn night… then the door bursts open again,
  // hearts in the doorway, and he walks back into the light.
  line('V1', 9, (p, lt, d, t, s) => {
    const b = i => B(s, i);
    layer('v1.9-facade', () => {
      rectf(0, 0, LW, LH, C.ink);
      for (let y = 0; y < 206; y += 6) { hline(0, LW, y, C.void); for (let x = (y / 6) % 2 ? 4 : 16; x < LW; x += 24) vline(x, y, y + 5, C.void); }
      for (const wx of [40, 90, 300, 350, 400]) for (const wy of [40, 110]) { rectf(wx, wy, 26, 34, C.void); rectf(wx + 2, wy + 2, 22, 30, C.night); vline(wx + 13, wy + 2, wy + 31, C.void); }
      rectf(0, 206, LW, 64, C.night); hline(0, LW, 206, C.dusk);
    });
    signPx('OPENAI', 170, 118, { font: 3, ink: C.haze });
    const DX = 156, DY = 140, DW = 28, DH = 66;
    const fired = b(.6), shutT = b(.9), reopen = b(2) - .1, inT = b(3.4);
    const open = lt < shutT ? 1 : lt < reopen ? 0 : lt < inT ? 1 : 1 - clamp((lt - inT) / .25);
    rectf(DX, DY, DW, DH, C.void);
    if (open > 0) {
      const ow = Math.round(DW * open);
      rectf(DX, DY, ow, DH, grad([C.amber, C.gold, C.cream], (x, y) => 1 - (y - DY) / DH * .7));
      polyf([[DX, DY + DH], [DX + ow, DY + DH], [DX + ow + 80 * open, LH], [DX - 34 * open, LH]], inkFn((x, y, u) => { const k = 1.6 - (y - DY - DH) / 50; return bay(x, y) < k - 1 ? (k > 1.3 ? C.gold : C.amber) : bay(x, y) < k ? LIT[LIT[u]] : LIT[u]; }));
      hline(DX, DX + ow - 1, DY + DH, C.cream);
      glow(DX + DW / 2, DY + DH / 2, 44, { tab: LIT, k: .9 * open });
    }
    // Sam: in the doorway → flung out → sits in the leaves → walks back in
    const landX = 300;
    if (lt < fired) personPx(DX + 14, DY + DH, { u: 3, top: C.navy, hair: 'short', hairC: C.wine });
    else if (lt < fired + .45) {
      const k = (lt - fired) / .45, x = lerp(DX + 14, landX, k), y = lerp(DY + DH, 222, k) - Math.sin(k * Math.PI) * 30;
      personPx(x, y, { u: 3, top: C.navy, hair: 'short', hairC: C.wine, aL: 1.2, aR: 1.2, eyes: 'wide', mouth: 'o' });
      rectf(x - 30 * (1 - k) - 20, y - 20 - Math.sin(k * 3) * 10, 10, 8, C.clay);
    } else if (lt < reopen + .2) {
      personPx(landX, 222, { u: 2, sit: true, top: C.navy, hair: 'short', hairC: C.wine, eyes: 'closed', mouth: 'frown' });
      rectf(landX + 14, 212, 14, 10, C.clay); hline(landX + 14, landX + 27, 212, C.amber); vline(landX + 21, 212, 221, C.rust);
    } else {
      const k = clamp((lt - reopen - .2) / (inT - reopen - .2)), x = lerp(landX, DX + 14, k), y = lerp(222, DY + DH, k);
      personPx(x, y, { u: 3, top: C.navy, hair: 'short', hairC: C.wine, walk: lt * 2.4, flip: true, eyes: 'happy', mouth: 'smile' });
      rectf(landX + 14, 212, 14, 10, C.clay); hline(landX + 14, landX + 27, 212, C.amber); vline(landX + 21, 212, 221, C.rust);
    }
    // the reopened door: silhouettes holding up hearts
    if (lt > reopen && lt < inT + .25) {
      for (let i = 0; i < 3; i++) { const hx = DX + 5 + i * 9; personPx(hx, DY + DH, { u: 1, top: C.void, pants: C.void, skin: C.void, hair: 'none', eyes: 'none', aL: 1, aR: 1 }); heartPx(hx, DY + DH - 16 - Math.round(breathe(t, 1, i / 3) * 2), 1, C.rust); }
    }
    // streetlamp
    vline(440, 120, 206, C.void); rectf(434, 116, 12, 4, C.void); glow(440, 124, 36, { tab: LIT, k: 1.1 }); rectf(437, 120, 6, 2, C.gold); ellf(440, 207, 26, 3, lit(1));
    weather(t, 'leaves', { n: 24 });
  });

  // ======================================================================
  // V1.10 Weekend chaos, board expired — four candles stand on a plank marked BOARD; the weekend blows through as calendar
  // pages, and three of the four flames go out.
  line('V1', 10, (p, lt, d, t, s) => {
    const b = i => B(s, i);
    rectf(0, 0, LW, LH, C.ink);
    // a window at the back: the night outside
    rectf(36, 26, 94, 104, C.void); clipRect(38, 28, 90, 100); sky({ cy: 190, r: 200 }); starfield(t, { density: .6 }); city(t, { y: 126, x0: 38, grow: .2, lit: .4 }); noClip();
    vline(83, 28, 127, C.void); hline(38, 127, 76, C.void); rectf(30, 130, 106, 4, C.night); hline(30, 135, 130, C.navy);
    // table + the board
    rectf(0, 206, LW, 64, C.void); hline(0, LW, 206, C.night);
    const px0 = 104, px1 = 376;
    rectf(px0, 186, px1 - px0, 18, C.rust); hline(px0, px1 - 1, 186, C.clay); hline(px0, px1 - 1, 203, C.wine); rectf(px0 + 2, 204, px1 - px0 - 4, 2, C.void);
    for (let x = px0 + 9; x < px1; x += 29) { pset(x, 191, C.wine); pset(x + 13, 199, C.wine); }
    ptext('THE BOARD', 240, 191, C.gold, { align: 'center', shadow: C.wine });
    // four candles; three go out, one on each beat
    const outs = [b(1) - .1, -1, b(2) - .1, b(3) - .1], xs = [150, 205, 262, 318], hs = [42, 54, 36, 48];
    xs.forEach((x, i) => { const since = outs[i] < 0 ? 0 : lt - outs[i], gk = outs[i] < 0 || since < 0 ? 1 : clamp(1 - since / .35); if (gk > 0) glow(x, 186 - hs[i] - 6, 64, { tab: WARM, k: 1.1 * gk }); });
    xs.forEach((x, i) => {
      const h = hs[i], top = 186 - h, lit = outs[i] < 0 || lt < outs[i], since = outs[i] < 0 ? 0 : lt - outs[i];
      rectf(x - 4, top, 9, h, C.cream); vline(x + 4, top + 1, 185, C.gold); vline(x + 3, top + 2, 185, C.gold);
      rectf(x - 4, top, 3, 4 + (i % 2) * 3, C.cream); pset(x - 3, top + 5 + (i % 2) * 3, C.gold); hline(x - 4, x + 4, top, C.gold);
      vline(x, top - 3, top - 1, C.void);
      if (lit) {
        const lean = lt > .2 && lt < 2.6 ? 1 : 0, fl = fx(i) < .4 ? 1 : 0;
        polyf([[x - 2.5 + lean, top - 3], [x + 3.5 + lean, top - 3], [x + 3 + lean * 2, top - 8], [x + .5 + lean * 3, top - 14 + fl], [x - 2 + lean * 2, top - 8]], C.amber);
        polyf([[x - 1.5 + lean, top - 3], [x + 2.5 + lean, top - 3], [x + 1.5 + lean * 2, top - 8], [x + .5 + lean * 2.5, top - 11 + fl]], C.gold);
        rectf(x + lean, top - 6, 1, 3, C.cream);
      } else if (since < 2.5) smoke(x, top - 4, t, { h: 44, n: 10 });
    });
    // the weekend blows through: calendar pages
    ['FRI', 'SAT', 'SUN', 'MON', 'TUE'].forEach((dname, i) => {
      const k = (lt - .05 - i * .4) / 1.4; if (k <= 0 || k >= 1) return;
      const x = lerp(-30, 500, k), y = 60 + Math.sin(k * 7 + i) * 22 + i * 16, edge = Math.sin(lt * 9 + i * 2) < -.6;
      if (edge) { vline(x + 12, y, y + 21, C.cream); return; }
      rectf(x + 1, y + 1, 24, 22, C.void); rectf(x, y, 24, 22, C.cream); rectf(x, y, 24, 6, C.rust); pset(x + 5, y + 1, C.void); pset(x + 18, y + 1, C.void);
      ptext(dname, x + 12, y + 10, C.void, { align: 'center' });
    });
  });

  // ======================================================================
  // V1.11 Ilya saw what Ilya saw — a telescope on a hilltop; the stars it points at join into a question mark;
  // the astronomer's eyes go wide.
  const QMARK = [[0, 10], [4, 3], [13, 0], [22, 3], [26, 11], [23, 19], [16, 25], [13, 33], [13, 41]];
  line('V1', 11, (p, lt, d, t, s) => {
    const b = i => B(s, i);
    sky({ cy: 320, r: 380 });
    starfield(t, { density: 1 });
    const g = hill({ cx: 360, y: 200, w: 160, drop: 50, ink: C.void, rim: C.pine });
    grass(200, LW, g, t);
    // the question mark in the stars
    const qx = 118, qy = 46, sc = 2.6, pts = QMARK.map(([x, y]) => [qx + x * sc, qy + y * sc]);
    const n = clamp((lt - .15) / 1.6) * (pts.length - 1), sure = lt > b(2) - .1;
    for (let i = 0; i < Math.floor(n); i++) pline(pts[i][0], pts[i][1], pts[i + 1][0], pts[i + 1][1], sure ? C.haze : C.dusk, { every: 2 });
    if (n % 1 > 0 && n < pts.length - 1) { const i = Math.floor(n), f = n - i; pline(pts[i][0], pts[i][1], lerp(pts[i][0], pts[i + 1][0], f), lerp(pts[i][1], pts[i + 1][1], f), C.dusk, { every: 2 }); }
    pts.forEach(([x, y], i) => { if (i <= n + .01) sparkle(x, y, sure && spulse(t, 3) > .4 ? 2 : 1, C.cream, sure ? C.gold : C.haze); });
    const dotK = rise(lt, 1.8, .2);
    if (dotK > 0) { const x = qx + 13 * sc, y = qy + 52 * sc; sparkle(x, y, sure ? 3 : 2, C.cream, C.gold); if (sure) glow(x, y, 14, { tab: LIT, k: 1 }); }
    // telescope pointing at it
    const tx = 322, ty = g(322) - 1;
    pline(tx, ty - 20, tx - 8, ty, C.dusk); pline(tx, ty - 20, tx + 8, ty, C.dusk); pline(tx, ty - 20, tx, ty, C.dusk);
    thick(tx + 10, ty - 14, tx - 30, ty - 44, 6, C.navy); pline(tx + 10, ty - 17, tx - 30, ty - 47, C.dusk); thick(tx - 26, ty - 39, tx - 34, ty - 45, 8, C.night);
    circf(tx - 33, ty - 46, 3, C.haze); pset(tx - 34, ty - 47, C.cream);
    if (sure) pline(tx - 36, ty - 49, qx + 13 * sc, qy + 30 * sc, veil(C.gold, .35), { every: 3 });
    personPx(344, g(344), { u: 3, hair: 'bald', hairC: C.dusk, top: C.ink, pants: C.void, eyes: sure ? 'wide' : 'dot', mouth: sure ? 'o' : 'none', lookX: -1, aL: .2, skin: C.gold });
    weather(t, 'petals', { n: 12 });
  });

  // ======================================================================
  // V1.12 EU writes the AI law — twelve gold stars take their places in a ring; inside it, a scroll unrolls and writes itself.
  line('V1', 12, (p, lt, d, t, s) => {
    sky({ ramp: [C.ink, C.night, C.navy, C.navy, C.dusk], cy: 110, cx: 240, r: 260, vert: 0 });
    starfield(t, { density: .35 });
    const cx = 240, cy = 104, R = 64;
    glow(cx, cy, 110, { tab: LIT, k: .5 });
    for (let i = 0; i < 12; i++) {
      const born = .08 + i * .09, age = lt - born; if (age < 0) continue;
      const a = -Math.PI / 2 + i / 12 * TAU, x = Math.round(cx + Math.cos(a) * R), y = Math.round(cy + Math.sin(a) * R);
      if (age < .18) sparkle(x, y, 2, C.cream, C.gold);
      else { spr(STAR5, x - 2, y - 2); if (hash2(i, sbeat(t)) < .3 && spulse(t, 3) > .5) pset(x, y, C.cream); }
    }
    // the scroll
    const uk = rise(lt, .9, .5, easeOut), sh = Math.round(64 * uk);
    if (uk > 0) {
      const sx = cx - 26, sy = cy - 34;
      rectf(sx - 2, sy - 3, 56, 4, C.gold); hline(sx - 2, sx + 53, sy - 3, C.cream);
      rectf(sx + 1, sy + 1, 52, sh, C.void); rectf(sx, sy, 52, sh, C.cream);
      rectf(sx - 2, sy + sh, 56, 4, C.gold); hline(sx - 2, sx + 53, sy + sh + 3, C.amber);
      if (sh > 14) ptext('AI ACT', cx, sy + 5, C.navy, { align: 'center' });
      const nl = Math.floor(clamp((lt - 1.3) / 1.2) * 11);
      for (let i = 0; i < nl && 17 + i * 4 < sh - 3; i++) hline(sx + 5, sx + 46 - (hash(i) * 12 | 0), sy + 17 + i * 4, i % 4 === 3 ? C.rust : C.haze);
      if (nl < 11 && lt > 1.3 && 17 + nl * 4 < sh) { const qx = sx + 5 + (frac(lt * 1.5) * 38 | 0), qy = sy + 17 + nl * 4; pline(qx, qy, qx + 6, qy - 9, C.void); pline(qx + 1, qy - 2, qx + 7, qy - 10, C.haze); }
    }
    ridge({ y: 214, amp: 8, seed: 41, ink: C.ink, rim: C.night });
    const vk = rise(lt, 2.0, .3);
    if (vk > 0) ptext('523 FOR · 46 AGAINST', cx, 184, veil(C.haze, vk), { font: 3, align: 'center' });
  });

  // ======================================================================
  // V1.13 Strawberry thinks, link by link — a strawberry on a hill thinks in a chain: link after link climbs the sky,
  // star by star, until the last one lights up.
  function strawberry(x, y, o = {}) {   // (x, y) = bottom point; ~36×40 px
    const P = pts => pts.map(([px, py]) => [x + px, y + py]);
    polyf(P([[-17, -30], [-12, -36], [12, -36], [17, -30], [16, -20], [8, -7], [2, 0], [-2, 0], [-8, -7], [-16, -20]]), C.rust);
    polyf(P([[-15, -31], [-10, -34], [-4, -34], [-9, -18], [-13, -16]]), C.clay);
    polyf(P([[12, -32], [16, -29], [14, -18], [6, -6], [2, -2], [8, -14]]), C.wine);
    for (let j = 0; j < 7; j++) for (let i = -6; i <= 6; i++) {
      const px = i * 2.6 + (j % 2) * 1.3, py = -31 + j * 4.2, half = 16 - j * 2.1 - (j > 3 ? (j - 3) * 1.2 : 0);
      if (Math.abs(px) < half - 1 && !(Math.abs(px) < 11 && py > -29 && py < -16)) { pset(x + px, y + py, C.gold); pset(x + px, y + py + 1, C.amber); }
    }
    polyf(P([[-14, -35], [-4, -38], [0, -44], [4, -38], [14, -35], [6, -33], [0, -36], [-6, -33]]), C.teal);
    polyf(P([[-9, -36], [0, -41], [9, -36], [0, -38]]), C.mint);
    rectf(x - 1, y - 49, 2, 7, C.teal); pset(x, y - 49, C.mint);
    const ey = y - 24;
    if (o.eyes === 'spark') { sparkle(x - 6, ey, 2, C.cream, C.gold); sparkle(x + 6, ey, 2, C.cream, C.gold); rectf(x - 2, ey + 5, 5, 2, C.void); pset(x, ey + 7, C.wine); }
    else if (o.eyes === 'closed') { hline(x - 8, x - 5, ey + 1, C.void); pset(x - 9, ey, C.void); hline(x + 5, x + 8, ey + 1, C.void); pset(x + 9, ey, C.void); hline(x - 1, x + 1, ey + 6, C.void); }
    else { rectf(x - 7, ey - 1, 2, 3, C.void); rectf(x + 6, ey - 1, 2, 3, C.void); }
    pset(x - 11, ey + 4, C.clay); pset(x + 11, ey + 4, C.clay);
  }
  line('V1', 13, (p, lt, d, t, s) => {
    const b = i => B(s, i);
    sky({ cy: 320, r: 380, ramp: [C.void, C.ink, C.night, C.navy, C.violet] });
    starfield(t, { density: .7 });
    const g = hill({ cx: 120, y: 214, w: 200, drop: 40, ink: C.void, rim: C.pine });
    grass(0, LW, g, t);
    const sx = 104, sy = g(104) + 2;
    // the chain of thought: link after link, star to star, up the sky
    const nodes = [[sx + 16, sy - 58], [160, 138], [196, 112], [236, 122], [266, 90], [304, 86], [330, 58], [368, 54], [404, 30]];
    const tEnd = b(3) - .2, n = clamp((lt - .3) / (tEnd - .3)) * (nodes.length - 1), done = lt > tEnd;
    for (let i = 0; i < nodes.length - 1; i++) {
      const f = clamp(n - i); if (f <= 0) break;
      const [x0, y0] = nodes[i], [x1, y1] = nodes[i + 1], L = Math.hypot(x1 - x0, y1 - y0), ux = (x1 - x0) / L, uy = (y1 - y0) / L, steps = Math.floor(L / 4 * f);
      for (let k = 1; k < steps; k++) {
        const x = x0 + ux * k * 4, y = y0 + uy * k * 4;
        if (k % 2) { ringf(x, y, 1, 2.2, C.haze); pset(x - 1, y - 2, C.cream); }
        else { thick(x - ux * 2.5, y - uy * 2.5, x + ux * 2.5, y + uy * 2.5, 2, C.dusk); pset(x, y, C.haze); }
      }
    }
    nodes.forEach(([x, y], i) => { if (i > 0 && i <= n + .01) sparkle(x, y, 1, C.cream, C.gold); });
    if (lt < .5) for (let i = 0; i < 3; i++) if (lt > i * .12) circf(sx + 8 + i * 4, sy - 50 - i * 4, i === 2 ? 1.5 : 1, C.haze);
    if (done) {
      const k = clamp((lt - tEnd) / .4), [x, y] = nodes[nodes.length - 1];
      glow(x, y, 44, { tab: LIT, k: 1.4 * easeOut(k) });
      starburst(x, y, 16, easeOut(k), { n: 8, ink: C.gold, fringe: C.amber, inner: .4, rot: lt * .3 });
      sparkle(x, y, 2, C.cream, C.cream);
    }
    strawberry(sx, sy, { eyes: done ? 'spark' : 'closed' });
    tagPx('o1', sx - 30, sy - 40, { font: 5 });
  });

  // ======================================================================
  // V1.14 Newsom vetoes, doesn't blink — the governor stamps VETO on SB 1047 at his balcony desk. Everything else blinks:
  // the stars, the owl in the palm, Clawd on the rail. He doesn't.
  function owl(x, y, closed) {
    rectf(x - 3, y - 7, 7, 8, C.dusk); rectf(x - 3, y - 7, 7, 1, C.haze); pset(x - 3, y - 8, C.dusk); pset(x + 3, y - 8, C.dusk);
    rectf(x - 2, y - 2, 5, 3, C.navy);
    if (closed) { hline(x - 2, x - 1, y - 5, C.void); hline(x + 1, x + 2, y - 5, C.void); }
    else { rectf(x - 2, y - 6, 2, 2, C.gold); rectf(x + 1, y - 6, 2, 2, C.gold); pset(x - 2, y - 5, C.void); pset(x + 2, y - 5, C.void); }
    pset(x, y - 4, C.amber);
  }
  line('V1', 14, (p, lt, d, t, s) => {
    const b = i => B(s, i);
    sky({ cy: 300, r: 340, ramp: [C.void, C.ink, C.night, C.navy, C.violet] });
    starfield(t, { density: 1, bright: .5 });
    // palm tree (right) with an owl that blinks on every beat
    for (let i = 0; i < 60; i++) { const k = i / 60; rectf(420 - Math.sin(k * 1.4) * 22, 240 - k * 150, 4, 3, C.void); }
    const top = [420 - Math.sin(1.4) * 22 + 2, 90];
    [[-44, 16], [-30, 26], [40, 18], [30, 30], [-8, 34], [10, -12], [-20, -8]].forEach(([dx, dy], i) => { const sw = Math.round(Math.sin(t * 1.2 + i) * 1.5); polyf([[top[0], top[1]], [top[0] + dx * .5, top[1] + dy * .3 - 6 + sw], [top[0] + dx, top[1] + dy + sw], [top[0] + dx * .5, top[1] + dy * .3 + sw]], C.void); });
    owl(top[0] - 24, top[1] + 12, frac(sbp(t)) < .2);
    // balcony
    rectf(0, 214, LW, 56, C.ink); for (let x = 4; x < LW; x += 10) rectf(x, 218, 3, 40, C.void); rectf(0, 213, LW, 3, C.void); hline(0, LW, 213, C.dusk);
    clawdPx(40, 213, { u: 1, eyes: frac(sbp(t) + .5) < .2 ? 'closed' : 'open', lookX: 1, blink: false });
    // desk lamp: a small pool of light
    const DT = 196, px = 282, py = DT + 1, slam = b(1.6) - .1, raised = lt > b(.7) && lt < slam;
    glow(160, 146, 34, { tab: WARM, k: 1 });
    polyf([[154, 138], [166, 138], [190, DT], [130, DT]], lit(.8));
    // Gavin: wide awake, staring straight at us
    const G = personPx(222, 214, { u: 5, top: C.ink, suit: true, tie: C.navy, hair: 'slick', hairC: C.wine, skin: C.gold, eyes: 'wide', mouth: 'flat', aR: raised ? 1.25 : -.15, aL: -.2 });
    // the desk (top surface + front)
    rectf(120, DT, 210, 7, C.navy); hline(120, 329, DT, C.dusk); rectf(116, DT + 7, 218, 30, C.night); hline(116, 333, DT + 7, C.ink);
    pline(160, DT, 160, 142, C.void); polyf([[150, 142], [170, 142], [166, 132], [154, 132]], C.amber); hline(151, 169, 142, C.gold);
    // the bill + the stamp
    rectf(px - 17, py, 34, 6, C.cream); ptext('SB 1047', px, py, C.navy, { font: 3, align: 'center' });
    if (lt < slam) { const [hx, hy] = raised ? G.handR : [px + 8, py - 4]; rectf(hx - 4, hy + 1, 9, 3, C.rust); rectf(hx - 1, hy - 5, 3, 6, C.clay); circf(hx, hy - 6, 1, C.rust); }
    else {
      const k = clamp((lt - slam) / .14);
      rectf(px - 15, py - 15, 30, 13, C.cream); rectb(px - 15, py - 15, 30, 13, C.rust); rectb(px - 13, py - 13, 26, 9, C.rust); ptext('VETO', px, py - 12, C.rust, { align: 'center' });
      if (k < 1) circb(px, py - 8, 12 + k * 18, veil(C.cream, 1 - k));
    }
  });

  // ======================================================================
  // V1.15 Hinton takes his medal, scolds — in a spotlight, a gold medal is lowered around his neck; he wags a finger at us.
  line('V1', 15, (p, lt, d, t, s) => {
    const b = i => B(s, i);
    layer('v1.15-stage', () => {
      rectf(0, 0, LW, LH, C.void);
      for (let x = 0; x < LW; x++) { const f = Math.min(x, LW - 1 - x); if (f < 70) { const fold = Math.sin(x * .4) > 0 ? C.wine : C.rust; vline(x, 0, 205, f < 60 - Math.sin(x * .08) * 8 ? fold : C.void); } }
      rectf(0, 0, LW, 14, C.wine); for (let x = 0; x < LW; x += 16) rectf(x, 14, 8, 4, C.wine);
      rectf(0, 205, LW, 65, C.night); hline(0, LW, 205, C.dusk);
    });
    // spotlight cone + pool
    polyf([[224, -2], [256, -2], [312, 206], [168, 206]], lit(2));
    ellf(240, 208, 70, 6, lit(2.4));
    // the medal comes down on its ribbon, then settles on his chest
    const mk = rise(lt, .05, .75, easeOut), chestY = 186, my = lerp(-10, chestY, mk);
    const wag = lt > b(1.9) - .1;
    const P = personPx(240, 206, { u: 4, hair: 'short', hairC: C.cream, glasses: true, suit: true, top: C.ink, tie: C.rust, skin: C.gold, eyes: 'dot', mouth: wag ? 'o' : 'smile', aR: wag ? 1.4 + (Math.floor(lt * 5) % 2 ? .22 : -.18) : -.4, aL: -.4 });
    if (mk < 1) { pline(235, -2, 238, my - 3, C.rust); pline(245, -2, 242, my - 3, C.rust); medalPx(240, my, { r: 4, ribbon: false }); }
    else { pline(235, 174, 239, chestY - 3, C.rust); pline(245, 174, 241, chestY - 3, C.rust); medalPx(240, chestY, { r: 3, ribbon: false, shine: spulse(t, 3) }); }
    if (wag) {
      const [hx, hy] = P.handR; rectf(hx, hy - 5, 1, 4, C.gold);
      bubblePx('be careful.', hx + 40, hy - 10, { font: 5, tail: [hx + 6, hy - 4], n: Math.ceil((lt - b(1.9) + .1) * 20) });
    }
    signPx('NOBEL PRIZE · PHYSICS', 240, 222, { font: 3, ink: C.gold, plate: C.void, edge: C.wine });
    // the audience
    for (let i = 0; i < 26; i++) { const x = 8 + i * 18.5 + (i % 2) * 5, y = 262 - (i % 3); circf(x, y, 5, C.void); }
    clawdPx(206, 270, { u: 1, eyes: 'up', shadow: false });
  });

  // ======================================================================
  // V1.16 Demis wins for protein folds — a chain of coloured beads hangs in the sky, then folds itself into a protein;
  // a gold medal lands around Demis's neck.
  const BEADS = 28;
  const beadCol = i => [C.amber, C.mint, C.violet, C.clay, C.gold, C.teal, C.haze, C.rust][(i * 3) % 8];
  const folded = i => {        // a compact fold: an α-helix, a loop, and a β-hairpin (unit coords, centred)
    if (i < 14) { const a = i * 1.75; return [-6 + Math.cos(a) * 8, -17 + i * 2.6, Math.sin(a) * 8]; }
    if (i < 17) return [[-2, 18, 6], [6, 20, 8], [12, 16, 6]][i - 14];
    const j = i - 17, strand = j < 6 ? 0 : 1, k = strand ? j - 6 : j;
    return [strand ? 20 : 13, strand ? -16 + k * 6.4 : 12 - k * 6, strand ? -6 : 2];
  };
  line('V1', 16, (p, lt, d, t, s) => {
    const b = i => B(s, i);
    sky({ cy: 320, r: 380 });
    starfield(t, { density: .8 });
    const g = hill({ cx: 150, y: 214, w: 190, drop: 44, ink: C.void, rim: C.pine });
    grass(0, LW, g, t);
    const cx = 292, cy = 100, won = lt > b(3) - .1, rot = .4 + lt * .8, S = 2.2;
    const P = [];
    for (let i = 0; i < BEADS; i++) {
      const k = ease(clamp((lt - .2 - i * .03) / 1.6)), [fx0, fy0, fz0] = folded(i);
      const sxp = 128 + i * 11 - cx, syp = 46 + Math.sin(i * .55 + lt * 2.2) * 4 - cy;
      const x3 = lerp(sxp, fx0 * S, k), y3 = lerp(syp, fy0 * S, k), z3 = lerp(0, fz0 * S, k);
      const a = rot * k, ca = Math.cos(a), sa = Math.sin(a);
      P.push({ x: cx + x3 * ca + z3 * sa, y: cy + y3, z: -x3 * sa + z3 * ca, i });
    }
    if (won) glow(cx, cy, 70, { tab: LIT, k: 1.1 * rise(lt, b(3) - .1, .4) });
    const order = [...P].sort((a, c) => a.z - c.z);
    // bonds first (back to front by their mid-depth), then beads
    const bonds = []; for (let i = 0; i + 1 < BEADS; i++) bonds.push([P[i], P[i + 1]]);
    bonds.sort((u, v) => (u[0].z + u[1].z) - (v[0].z + v[1].z)).forEach(([u, v]) => { const z = (u.z + v.z) / 2; thick(u.x, u.y, v.x, v.y, 2, z < -6 ? C.night : z < 6 ? C.navy : C.dusk); });
    order.forEach(q => { const c = beadCol(q.i), r = q.z > 10 ? 3 : q.z < -10 ? 2 : 2.5; circf(q.x, q.y, r, q.z < -8 ? DIM[c] : c); if (q.z > 0) pset(q.x - 1, q.y - 1, LIT[c]); });
    if (won) ptext('ALPHAFOLD', cx, cy + 58, veil(C.gold, rise(lt, b(3), .3)), { font: 3, align: 'center' });
    personPx(130, g(130), { u: 3, top: C.navy, hair: 'short', hairC: C.void, skin: C.clay, eyes: won ? 'closed' : 'up', mouth: won ? 'smile' : 'none', aR: won ? 1.2 : -1.1, aL: won ? 1.2 : -1.1 });
    if (won) { const mk = rise(lt, b(3) - .1, .35, easeOut), my = g(130) - 17; medalPx(130, lerp(110, my, mk), { r: 3, ribbon: false, shine: 1 }); if (mk >= 1) { pline(127, my - 7, 129, my - 3, C.rust); pline(133, my - 7, 131, my - 3, C.rust); } }
    handLantern(62, g(62));
    clawdPx(42, g(42), { u: 1, pose: 'sit', eyes: 'up', lookX: 1 });
  });
})();

;
// ---- styles/dither/ch/c03_chorus1.js ----
// c03_chorus1.js: Chorus 1, the first aurora. Back on Clawd's hill: the sixteen V1 stars connect into the first, low
// stretch of the curve; aurora curtains rise along exponential curves; close on Clawd shrugging "not us"; Clawd catches
// a ribbon of aurora in a jar, the lid pops, and the light streams back up into the sky. End wide, the curve still rising.
(() => {
  // aurora light: dark things go teal, warm things one step lighter
  const AUR = makeTab({ void: 'pine', ink: 'pine', night: 'pine', navy: 'teal', dusk: 'teal', haze: 'mint', violet: 'teal', pine: 'teal', teal: 'mint', mint: 'cream', wine: 'rust', rust: 'clay', clay: 'amber', amber: 'gold', gold: 'cream' });
  const E = (u, c) => (Math.exp(c * u) - 1) / (Math.exp(c) - 1);
  const V1N = 16;                                    // the V1 stars are LEDGER[0..15]

  // Clawd's hill with a hook for things that sit behind the land (aurora). Mirrors homeScene().
  function home(t, o = {}) {
    const dy = o.dy ?? 0;
    sky({ dy: Math.round(dy * .3) });
    starfield(t, { dy: dy * .3, ...(o.stars || {}) });
    moon(100, 62 + dy * .3, 8, { phase: .55 });
    if (o.behind) o.behind(dy);
    if (o.ledger !== false) ledger(t, { dy: dy * .3, linkInk: C.haze, ...(o.ledger || {}) });
    view(0, -Math.round(dy * .6));
    city(t, { y: 204, x0: 262, grow: .3, dc: 380, lit: .3 });
    ridge({ y: 214, amp: 14, seed: 3, ink: C.ink, rim: C.night, freq: 1 / 80 });
    view(0, -dy);
    const g = hill({ cx: 118, y: 196, w: 150, drop: 46, ink: C.void, rim: C.pine });
    grass(0, LW, g, t, { ink: C.pine });
    let info = null;
    if (o.clawd !== false) {
      const cl = o.clawd || {}, x = 116;
      if (o.jar) jarPx(x + 13, g(x + 13), { w: 5, h: 6, fill: 0, glint: true });
      handLantern(x + 18, g(x + 18));
      info = clawdPx(x, g(x), { u: 2, pose: 'sit', eyes: 'up', ...cl });
    }
    view(0, 0);
    return { ground: x => g(x) + dy, clawd: info };
  }

  // Aurora curtains along exponential curves (they pick up where the V1 stars leave off and sweep up to the upper right).
  // k: intensity, gain: how far the right ends have climbed (0..1), rise: how far they have come up from behind the land.
  const CURVES = [
    { x0: 40, y0: 150, y1: -30, c: 2.4, len: 30, cols: [C.pine, C.teal, C.mint], ph: 1.7, k: .75 },
    { x0: 96, y0: 190, y1: 8, c: 2.2, len: 34, cols: [C.pine, C.teal, C.mint, C.cream], ph: 0, k: 1 },
    { x0: 150, y0: 206, y1: 70, c: 2.6, len: 22, cols: [C.pine, C.teal], ph: 3.1, k: .7 },
  ];
  const curveY = (S, x, low, gain, t) => low + lerp(S.y0, lerp(S.y0 - 10, S.y1, gain), E(clamp((x - S.x0) / (LW - S.x0), -.3, 1.1), S.c)) + Math.sin(x * .025 + t * .45 + S.ph) * 4;
  function curtains(t, dy, k, gain, rise = 1, o = {}) {
    const low = 90 * (1 - rise) + dy * .3 + (o.dy ?? 0);
    CURVES.forEach(S => {
      const kk = k * S.k; if (kk <= 0) return;
      aurora(t, { k: kk, len: S.len, cols: S.cols, shimmer: 1, x0: S.x0 - 30, curve: x => curveY(S, x, low, gain, t) });
    });
  }

  // A glass jar. (x, y) = bottom centre. o: w, h, fill (0..1 light level), lid (true | {dy, tilt}), glint, shake
  function jarPx(x, y, o = {}) {
    const w = o.w ?? 16, h = o.h ?? 20, x0 = Math.round(x - w / 2), y0 = Math.round(y - h), lv = o.fill ?? 0;
    if (w <= 6) {   // tiny version for the wide shot
      rectb(x0, y0 + 1, w, h - 1, C.dusk); hline(x0, x0 + w - 1, y0, C.haze);
      if (o.glint) pset(x0 + 1, y0 + 2, breathe(T, 2) > .5 ? C.mint : C.teal);
      return;
    }
    if (lv > 0) {
      const fy = Math.round(lerp(y - 2, y0 + 4, lv));
      glow(x, (fy + y) / 2, w * 1.4 + lv * 10, { tab: GREEN, k: .5 + lv * .9, ry: (y - fy) / 2 + 12 });
      rectf(x0 + 1, fy, w - 2, y - 1 - fy, grad([C.teal, C.mint, C.cream], (xx, yy) => clamp(.2 + .55 * (1 - (yy - fy) / Math.max(1, y - fy)) + .18 * Math.sin(xx * .35 + yy * .25 + T * 3))));
      hline(x0 + 1, x0 + w - 2, fy, C.cream);
      for (let i = 0; i < 7; i++) { const sx = x0 + 2 + hash2(i, boilFrame(T) >> 2) * (w - 4), sy = fy + 2 + hash2(i + 9, boilFrame(T) >> 2) * Math.max(1, y - fy - 4); if (sy < y - 2) pset(sx, sy, C.cream); }
    } else rectf(x0 + 1, y0 + 3, w - 2, h - 4, veil(C.haze, .12));
    // glass
    vline(x0, y0 + 3, y - 3, C.haze); vline(x0 + w - 1, y0 + 3, y - 3, C.haze);
    hline(x0 + 2, x0 + w - 3, y - 1, C.haze); pset(x0 + 1, y - 2, C.haze); pset(x0 + w - 2, y - 2, C.haze);
    rectb(x0 + 1, y0, w - 2, 3, C.haze); hline(x0 + 2, x0 + w - 3, y0, C.cream);
    vline(x0 + 2, y0 + 5, y - 5, C.cream); vline(x0 + 3, y0 + 6, y0 + 8, veil(C.cream, .5));
    if (o.lid) {
      const L = o.lid === true ? {} : o.lid, ly = y0 - 3 - Math.round(L.dy ?? 0), lx = x0 + Math.round(L.dx ?? 0), tilt = L.tilt ?? 0;
      for (let i = 0; i < w; i++) { const yy = ly + Math.round((i - w / 2) * tilt); rectf(lx + i, yy, 1, 4, i === 0 || i === w - 1 ? C.dusk : C.haze); pset(lx + i, yy, C.cream); pset(lx + i, yy + 3, C.dusk); }
    }
  }

  // A glowing ribbon of aurora from A to B, drawn between path fractions s0..s1. wig: sideways wiggle amplitude.
  function ribbon(ax, ay, bx, by, s0, s1, t, o = {}) {
    if (s1 <= s0) return;
    const L = Math.hypot(bx - ax, by - ay), nx = -(by - ay) / L, ny = (bx - ax) / L, wig = o.wig ?? 14, r = o.r ?? 2.2;
    const P = s => { const off = Math.sin(s * Math.PI) * wig * Math.sin(s * 9 - t * 2.2); return [lerp(ax, bx, s) + nx * off, lerp(ay, by, s) + ny * off]; };
    const n = Math.ceil(L * (s1 - s0) / 1.5);
    for (let i = 0; i <= n; i++) { const s = lerp(s0, s1, i / n), [x, y] = P(s); circf(x, y, r + 1, veil(C.teal, .55)); }
    for (let i = 0; i <= n; i++) { const s = lerp(s0, s1, i / n), [x, y] = P(s); circf(x, y, r - .6, C.mint); pset(x, y, C.cream); }
    for (let i = 0; i < 5; i++) { const s = lerp(s0, s1, frac(hash(i) + t * .3)), [x, y] = P(s); sparkle(x + (hash2(i, 3) - .5) * 8, y, 1, C.cream, C.mint); }
    const [hx, hy] = P(s1); glow(hx, hy, 12, { tab: GREEN, k: 1 }); sparkle(hx, hy, 2, C.cream, C.mint);
    return P;
  }

  // A bigger hand lantern for close-ups (same design as handLantern at 3×). (x, y) = bottom centre.
  function bigLantern(x, y, k = 1) {
    const fl = .9 + .1 * breathe(T, 1, .3);
    glow(x, y - 12, 38, { tab: WARM, k: 1.3 * k * fl, pow: 1.7 });
    rectf(x - 2, y - 26, 5, 2, C.void); pline(x - 4, y - 22, x - 2, y - 25, C.void); pline(x + 4, y - 22, x + 2, y - 25, C.void);
    rectf(x - 7, y - 22, 15, 3, C.void); rectf(x - 7, y - 3, 15, 3, C.void);
    rectf(x - 5, y - 19, 11, 16, C.gold); rectf(x - 4, y - 18, 3, 14, C.amber); rectf(x + 3, y - 18, 2, 14, C.amber);
    const fh = 7 + (hash2(1, boilFrame(T)) < .4 ? 1 : 0);
    polyf([[x - 2, y - 6], [x + 3, y - 6], [x + 1.5, y - 6 - fh * .6], [x + .5, y - 6 - fh], [x - 1, y - 6 - fh * .6]], C.cream);
    vline(x - 6, y - 19, y - 4, C.ink); vline(x + 6, y - 19, y - 4, C.ink);
  }

  // snap an lt to the nearest slow beat of the window
  const snap = (s, lt) => { const bs = beatsIn(s); let best = lt, bd = 9; for (const b of bs) if (Math.abs(b - lt) < bd) { bd = Math.abs(b - lt); best = b; } return best; };

  section('C1', (p, lt, d, t, s) => {
    dissolveIn(1.2);
    const L = linesOf('C1').map(l => ({ a: l.start - s.start, b: l.end - s.start }));
    const cut1 = L[1].a - .2, cut2 = L[2].a - .25, cut3 = L[3].a - .25, cut4 = L[3].b + .05;
    const popT = snap(s, L[3].a + .66 * (L[3].b - L[3].a));

    // --- 1: "We didn't start the scaling": the V1 stars connect, one by one --------------------------------
    const shotA = () => {
      const dy = Math.round(lerp(18, 26, clamp(lt / cut1))), lk = rise(lt, .45, 2.1, k => k);
      const head = lk * (V1N - 1), hs = LEDGER[Math.min(V1N - 1, Math.round(head))];
      home(t, {
        dy, ledger: { links: lk },
        clawd: { eyes: 'up', lookX: clamp((hs.x - 116) / 50, -1, 1) },
        behind: () => {},
      });
      for (let i = 0; i < V1N; i++) {
        const age = (head - i) * 2.1 / (V1N - 1); if (age < 0 || age > .7) continue;
        const S = LEDGER[i], y = S.y + dy * .3;
        glow(S.x, y, 12, { tab: LIT, k: 1.4 * (1 - age / .7) });
        sparkle(S.x, y, age < .2 ? 3 : age < .45 ? 2 : 1, C.cream, C.gold);
      }
      weather(t, 'leaves', { n: 10 });
    };

    // --- 2: "It was always training, and the curves kept gaining": aurora rises along exponential curves ------
    const shotB = () => {
      const k2 = clamp((lt - L[1].a) / (L[1].b - L[1].a)), dy = Math.round(lerp(26, 46, ease(k2)));
      home(t, {
        dy, ledger: { links: 1 },
        clawd: { eyes: 'up', lookX: .4 + .3 * Math.sin(lt * .8) },
        behind: dy2 => curtains(t, dy2, .8 * rise(lt, L[1].a - .2, 1.6), ease(k2) * .9, rise(lt, L[1].a - .2, 2.2)),
      });
      weather(t, 'leaves', { n: 10 });
    };

    // aurora light on Clawd's top: the upper rows of warm pixels turn mint, thinning out downward
    const auroraRim = (c, rows) => {
      for (let j = 0; j < rows; j++) {
        const k = 1 - j / rows;
        rectf(c.left - 2, c.top + j, c.right - c.left + 5, 1, inkFn((x, y, u) => (u === C.clay || u === C.amber || u === C.rust) && bay(x, y) < k * .9 ? (j === 0 ? C.cream : C.mint) : -1));
      }
    };

    // --- 3: "We didn't start the scaling": close on Clawd, eyes closed, shaking its head (not us) -----------
    const shotC = () => {
      sky({ cy: 360, r: 400 });
      starfield(t, { density: .7 });
      curtains(t, 0, .8, 1, 1, { dy: -40 });
      const g = hill({ cx: 250, y: 224, w: 300, drop: 30, ink: C.void, rim: C.pine });
      glow(236, g(236) + 2, 120, { tab: AUR, k: .9, ry: 10 });
      grass(0, LW, g, t, { h: 4, step: 2, ink: C.teal });
      bigLantern(318, g(318));
      const ph = (lt - L[2].a) / 1.05, sway = Math.round(Math.sin(ph * TAU) * 3 * rise(lt, L[2].a + .15, .4));
      const c = clawdPx(236 + sway, g(236), { u: 7, pose: 'sit', eyes: 'closed', mouth: 'smile', aL: .55, aR: .55, lookX: Math.sign(sway) * .5 });
      auroraRim(c, 5);
      // little motion ticks at the ends of each shake
      if (Math.abs(sway) === 3) { const sx = sway > 0 ? c.right + 14 : c.left - 14; for (let j = 0; j < 3; j++) pset(sx, c.top + 8 + j * 3, C.haze); }
      weather(t, 'leaves', { n: 12 });
    };

    // --- 4: "No, we didn't preordain it, but we can't contain it!": the aurora in a jar ------------------------
    const shotD = () => {
      const t0 = L[3].a, catchT = t0 + .55, fullT = t0 + 1.9, lidT = fullT + .45;
      sky({ cy: 360, r: 400 });
      starfield(t, { density: .8 });
      curtains(t, 0, .8, 1, 1, { dy: -34 });
      const g = hill({ cx: 220, y: 228, w: 320, drop: 26, ink: C.void, rim: C.pine });
      glow(230, g(230) + 2, 110, { tab: AUR, k: .8, ry: 9 });
      grass(0, LW, g, t, { h: 4, step: 2, ink: C.teal });
      bigLantern(140, g(140));
      // arm: raised to catch, lowered to shoulder height to close the lid
      const armK = rise(lt, fullT, .4), aR = lerp(1.1, .3, armK);
      const popped = lt > popT, pk = clamp((lt - popT) / 1.3);
      const shake = !popped && lt > lidT + .15 ? Math.round((hash2(3, boilFrame(T)) - .5) * 2.4 * clamp((lt - lidT - .15) / (popT - lidT - .15))) : 0;
      const eyes = popped ? (pk < .4 ? 'wide' : 'up') : lt < catchT + .3 ? 'up' : lt < lidT ? 'happy' : 'open';
      const cx = 214, gy = g(cx), jw = 30, jh = 38;
      const opts = { u: 6, eyes, aR, aL: lt > lidT - .5 && lt < lidT + .2 ? 1 : popped ? .9 : -.3, mouth: popped && pk < .5 ? 'o' : lt > catchT + .3 && lt < lidT ? 'smile' : undefined, lookX: popped ? .6 : .5, lookY: popped && pk > .4 ? -1 : 0, blink: !popped };
      const tmp = FB.slice(); const c0 = clawdPx(cx, gy, opts); FB.set(tmp);   // where the paw ends up (this draw is discarded)
      const jx = c0.handR[0] + 6 + shake, jy = c0.handR[1] + 3;
      const inK = rise(lt, t0 + .05, catchT - t0 + .5, k => k), fillK = clamp((lt - catchT) / (fullT - catchT)) * (popped ? 1 - clamp(pk * 1.6) : 1);
      // the ribbon comes down from the aurora into the jar
      if (inK > 0 && lt < fullT + .2) ribbon(380, 60, jx, jy - jh + 3, clamp((lt - catchT) / (fullT - catchT + .1)), inK, t, { wig: 18 });
      // …and after the pop streams back up into the sky
      if (popped) ribbon(jx, jy - jh, 330, -30, clamp((pk - .45) * 1.9), easeOut(clamp(pk * 1.4)), t, { wig: 20, r: 2.8 });
      const c = clawdPx(cx, gy, opts);
      auroraRim(c, 4);
      const lid = lt < lidT ? (lt > lidT - .45 ? { dy: 12 * (1 - ease(clamp((lt - lidT + .45) / .45))) } : false)
        : !popped ? true : { dy: 70 * easeOut(clamp(pk * 1.2)), dx: 20 * pk, tilt: Math.sin(pk * 6) * .6 };
      jarPx(jx, jy, { w: jw, h: jh, fill: fillK, lid });
      if (popped && pk < .5) for (let i = 0; i < 6; i++) { const a = -Math.PI / 2 + (i - 2.5) * .45, r = 10 + pk * 34; sparkle(jx + Math.cos(a) * r, jy - jh + Math.sin(a) * r, 1, C.cream, C.mint); }
      weather(t, 'leaves', { n: 10 });
    };

    // --- 5: end wide, the curve still rising ------------------------------------------------------------
    const shotE = () => {
      const k = clamp((lt - cut4) / (d - cut4 + .5)), dy = Math.round(lerp(34, 44, k));
      home(t, {
        dy, jar: true, ledger: { links: 1 },
        clawd: { eyes: 'up', lookX: .3 + k * .7, lookY: -1 },
        behind: dy2 => {
          curtains(t, dy2, .8, 1, 1);
          // the escaped light runs on up the curve and off the top of the frame
          const S = CURVES[1], y = x => curveY(S, x, dy2 * .3, 1, t);
          const hx = lerp(200, 520, easeIn(clamp(k * 1.1)));
          for (let i = 0; i < 26; i++) { const x = hx - i * 3; if (x < 150) break; pset(x, y(x) - 2, i < 6 ? C.cream : veil(C.mint, 1 - i / 26)); }
          glow(hx, y(hx) - 2, 12, { tab: GREEN, k: 1.2 }); sparkle(hx, y(hx) - 2, 2, C.cream, C.mint);
        },
      });
      weather(t, 'leaves', { n: 10 });
    };

    const cf = (at, dur = .5) => rise(lt, at, dur, k => k);
    if (lt < cut1 + .5) crossfade(cf(cut1), shotA, shotB);
    else if (lt < cut2 + .5) crossfade(cf(cut2), shotB, shotC);
    else if (lt < cut3 + .5) crossfade(cf(cut3), shotC, shotD);
    else crossfade(cf(cut4, .6), shotD, shotE);
  });
})();

;
// ---- styles/dither/ch/c04_v2.js ----
// c04_v2.js: Verse 2, 2025. The city on the horizon glows violet now; each headline is one small, big-enough joke.
// Consecutive shots alternate wide/close and warm/cool; the verse's one dusty-red starburst is V2.6's "BUY 3!".
(() => {
  // ---------- private helpers ----------
  const B = (s, i) => beatAt(s, i);
  const fx = (seed, n = 0) => hash2(seed, boilFrame(T) * 7 + n);   // per-frame flicker (12/s)

  // A red paper lantern (Lunar New Year). (x, y) = centre. s: size 1..2
  function redLantern(x, y, s = 1, lit = 1) {
    const rx = 3 * s + 1, ry = 3 * s + 1;
    glow(x, y, 9 * s + 4, { tab: WARM, k: .9 * lit });
    rectf(x - rx + 1, y - ry - 1, 2 * rx - 1, 1, C.gold); rectf(x - rx + 1, y + ry, 2 * rx - 1, 1, C.gold);
    ellf(x, y, rx, ry - .5, C.rust);
    ellf(x - 1, y - 1, rx - 2, ry - 2, C.clay);
    if (s > 1) { vline(x - 2, y - ry + 1, y + ry - 1, C.rust); vline(x + 2, y - ry + 1, y + ry - 1, C.rust); }
    pset(x - 1, y - 1, C.amber);
    vline(x, y + ry + 1, y + ry + 2 + s, C.gold);
  }

  // ======================================================================
  // V2.1 DeepSeek New Year sticker shock — red lanterns rise over a snowy town at Lunar New Year; among them floats a
  // big blue whale lantern with a tiny price tag, $5.6M. The ticker on the tower flips to NVDA ↓17% and the city shivers.
  function whaleLantern(x, y, t, tagK) {
    x = Math.round(x); y = Math.round(y);
    const S = 2;
    glow(x, y, 80, { tab: LIT, k: 1.3, ry: 60 });
    // tail flukes (left), lifting on the breath
    const fl = Math.round(breathe(t, 2) * 4);
    polyf([[x - 44, y + 4], [x - 68, y - 14 - fl], [x - 60, y + 2], [x - 72, y + 16 + fl], [x - 44, y + 12]], C.navy);
    polyf([[x - 46, y + 6], [x - 64, y - 8 - fl], [x - 58, y + 4]], C.dusk);
    // body: a round paper whale, lit from inside
    ellf(x, y, 26 * S, 14 * S, C.navy);
    ellf(x + 1, y - 1, 25 * S - 1, 13 * S - 1, C.dusk);
    ellf(x + 5, y - 5, 19 * S, 9 * S, mix(C.dusk, C.haze, .5));
    ellf(x + 8, y - 7, 14 * S, 6 * S, C.haze);
    ellf(x + 12, y - 9, 8 * S, 3 * S, mix(C.haze, C.cream, .5));
    // paper ribs
    for (const rx of [-26, -8, 10, 28]) for (let yy = -28; yy <= 28; yy++) { const q = 1 - (rx / 52) ** 2 - (yy / 28) ** 2; if (q > 0 && yy % 2 === 0) pset(x + rx + Math.round(yy * yy / 200), y + yy, C.navy); }
    // belly stripes, eye, smile, fin
    for (let xx = -36; xx <= 40; xx++) { const by = Math.round(y + 27 * Math.sqrt(Math.max(0, 1 - (xx / 52) ** 2))) - 2; pset(x + xx, by, C.cream); if (xx % 3 === 0) { pset(x + xx, by - 3, C.haze); pset(x + xx, by - 6, C.haze); } }
    rectf(x + 28, y - 6, 4, 5, C.void); pset(x + 28, y - 6, C.cream);
    hline(x + 32, x + 44, y + 8, C.navy); pset(x + 45, y + 7, C.navy); pset(x + 46, y + 6, C.navy);
    polyf([[x - 4, y + 12], [x + 12, y + 12], [x - 8, y + 26]], C.navy);
    // spout
    for (let i = 0; i < 6; i++) { const f = frac(t * .9 + i / 6); pset(x + 18 + Math.sin(i * 2) * 6 * f, y - 30 - f * 18, veil(C.cream, 1 - f)); }
    // gold cap and bottom ring like a paper lantern
    rectf(x - 8, y - 31, 17, 3, C.gold); hline(x - 8, x + 8, y - 31, C.cream); rectf(x - 8, y + 27, 17, 3, C.gold);
    vline(x, y - 40, y - 32, C.haze);
    // the price tag, dangling
    const sw = Math.sin(t * 1.6) * 4, tx = x + Math.round(sw), ty = y + 50;
    pline(x, y + 30, tx, ty - 9, C.haze);
    if (tagK > 0) {
      const k = tagK;
      rboxf(tx - 32, ty - 9, 64, 22, veil(C.void, k), 2);
      rboxf(tx - 31, ty - 8, 62, 20, veil(C.cream, k), 1);
      circf(tx - 25, ty + 2, 2, veil(C.haze, k)); pset(tx - 25, ty + 2, C.void);
      if (k > .5) ptext('$5.6M', tx + 4, ty - 5, C.rust, { align: 'center', scale: 2 });
    }
  }
  line('V2', 1, (p, lt, d, t, s) => {
    const b = i => B(s, i), crash = b(2) - .1, pops = b(3) - .1;
    const shiver = lt > crash && lt < crash + .9;
    sky({ cy: 320, r: 380 });
    starfield(t, { density: .7 });
    // far city, shivering after the crash
    city(t, { y: 206, x0: 0, x1: 320, grow: .5, lit: shiver ? (fx(1) < .5 ? .06 : .3) : .32, seed: 12 });
    // the ticker tower (right)
    const TX = 318, TY = 54;
    rectf(TX, TY, 162, 216, C.ink); hline(TX, TX + 161, TY, C.navy); vline(TX, TY, 230, C.night);
    rectf(TX + 70, TY - 22, 4, 22, C.ink); pset(TX + 71, TY - 23, hash2(4, sbeat(t)) < .5 ? C.rust : C.wine);
    for (let wy = TY + 66; wy < 206; wy += 9) for (let wx = TX + 8; wx < TX + 154; wx += 10) {
      const h = hash2(wx, wy); if (h > .5) continue;
      const on = !shiver || fx(wx + wy) < .45;
      rectf(wx, wy, 5, 5, on ? (h < .15 ? C.gold : C.amber) : C.night);
    }
    const flipped = lt > crash, scramble = flipped && lt < crash + .14;
    const SX = TX + 8, SW = 148;
    rectf(SX, TY + 6, SW, 52, C.void); rectb(SX - 1, TY + 5, SW + 2, 54, C.navy);
    const lnA = 'NVDA', lnB = flipped ? (scramble ? '#%*@' : '↓17%') : '142.6', ink = flipped ? C.clay : C.mint;
    ptext(lnA, SX + SW / 2, TY + 9, ink, { scale: 3, dots: true, off: C.ink, align: 'center' });
    ptext(lnB, SX + SW / 2, TY + 34, ink, { scale: 3, dots: true, off: C.ink, align: 'center' });
    if (flipped && lt < crash + .6) glow(SX + SW / 2, TY + 32, 70, { tab: WARM, k: .9 * (1 - (lt - crash) / .6) });
    // snowy town rooftops
    layer('v2.1-town', () => {
      ridge({ y: 216, amp: 6, seed: 51, ink: C.ink, rim: C.navy, freq: 1 / 40 });
      const hs = [[4, 36], [48, 30], [86, 40], [134, 28], [170, 36], [214, 30], [252, 42], [302, 30], [340, 36], [384, 40], [432, 40]];
      hs.forEach(([x, w], i) => house(x, 250 + (i % 3) * 2, { w, h: 16 + (i % 2) * 4, wall: C.night, roof: C.ink, snow: C.cream, windows: 2, ws: 4, lit: j => hash2(i, j) < .7 ? (hash2(i, j + 5) < .5 ? C.amber : C.gold) : false, chimney: i % 3 === 0 }));
    });
    // red lanterns drifting up from the rooftops
    for (let i = 0; i < 12; i++) {
      const sp = 14 + hash2(i, 1) * 10, y0 = 250 - frac(hash2(i, 2) + (t * sp) / 300) * 270, x0 = 16 + hash2(i, 3) * 450 + Math.sin(t * .6 + i) * 6;
      if (x0 > 318 && y0 < 110) continue;                          // keep the ticker readable
      if (Math.abs(x0 - 150) < 80 && Math.abs(y0 - 118) < 60) continue;   // and the whale
      redLantern(x0, y0, hash2(i, 4) < .45 ? 2 : 1);
    }
    // the whale lantern, rising
    const wy = lerp(128, 104, easeOut(clamp(lt / (d + .4)))) + Math.sin(t * 1.1) * 2, wx = 146 + lt * 3;
    whaleLantern(wx, wy, t, rise(lt, b(.7), .3));
    // firecrackers pop on beat 3
    [[40, 200], [300, 188], [236, 206]].forEach(([x, y], i) => {
      const k = clamp((lt - pops - i * .12) / .35); if (k <= 0) return;
      if (k < 1) starburst(x, y, 11, easeOut(k), { n: 8, ink: i % 2 ? C.gold : C.rust, fringe: C.wine, inner: .35 });
      for (let j = 0; j < 10; j++) { const a = j / 10 * TAU, age = lt - pops - i * .12, r = 6 + easeOut(clamp(age / .5)) * 16; if (age < 1.2) pset(x + Math.cos(a) * r, y + Math.sin(a) * r + age * age * 10, age < .4 ? C.cream : age < .8 ? C.gold : C.clay); }
    });
    weather(t, 'snow', { n: 50 });
  });

  // ======================================================================
  // V2.2 Half a trillion Stargate talk — a huge ring of lights on the horizon; its chevrons lock one by one and a dot-matrix
  // "$500,000,000,000" scrolls across it… but through the ring there's only more night. Below it TRUMP announces it from the podium,
  // SAM, LARRY and MASA beside him. Far off, ELON: "they don't actually have the money".
  line('V2', 2, (p, lt, d, t, s) => {
    const b = i => B(s, i);
    const cx = 196, cy = 116, R = 88, Ri = 72;
    sky({ cy: 320, r: 380 });
    starfield(t, { density: .9 });
    // the gate
    glow(cx, cy, R + 16, { tab: LIT, k: .5 });
    ringf(cx, cy, Ri, R, C.night);
    circb(cx, cy, R, C.dusk); circb(cx, cy, Ri + 1, C.dusk);
    ringf(cx, cy, Ri + 5, Ri + 7, C.ink);
    for (let i = 0; i < 39; i++) { const a = i / 39 * TAU, r = Ri + 11; pset(cx + Math.cos(a) * r, cy + Math.sin(a) * r, C.navy); pset(cx + Math.cos(a) * (r + 1), cy + Math.sin(a) * (r + 1), C.navy); }
    // chevrons lock one by one
    const nOn = clamp((lt - .1) / (b(1.6) - .1)) * 9;
    for (let i = 0; i < 9; i++) {
      const a = -Math.PI / 2 + i / 9 * TAU, on = i < nOn, ox = cx + Math.cos(a) * (R - 1), oy = cy + Math.sin(a) * (R - 1), ix = cx + Math.cos(a) * (Ri + 4), iy = cy + Math.sin(a) * (Ri + 4), px = -Math.sin(a) * 6, py = Math.cos(a) * 6;
      if (on) glow(ix, iy, 14, { tab: WARM, k: 1.1 });
      polyf([[ox + px, oy + py], [ox - px, oy - py], [ix, iy]], on ? C.amber : C.wine);
      polyf([[ox + px * .5, oy + py * .5], [ox - px * .5, oy - py * .5], [lerp(ox, ix, .6), lerp(oy, iy, .6)]], on ? C.gold : C.rust);
    }
    // the money marquee across the ring's mouth
    const mk = lt - b(.5);   // starts early enough that the whole number has scrolled through the ring's mouth by the cut
    if (mk > 0) {
      const txt = '$500,000,000,000', w = ptextW(txt, { scale: 2 }), x0 = cx + Ri - 4 - mk * 84;
      rectf(cx - Ri + 6, cy - 12, 2 * Ri - 12, 22, veil(C.void, .5));
      clipRect(cx - Ri + 8, cy - 11, 2 * Ri - 16, 20);
      ptext(txt, Math.round(x0), cy - 7, C.gold, { scale: 2, dots: true, off: C.ink });
      noClip();
      hline(cx - Ri + 6, cx + Ri - 7, cy - 12, C.dusk); hline(cx - Ri + 6, cx + Ri - 7, cy + 9, C.dusk);
    }
    // ramp and horizon
    ridge({ y: 208, amp: 8, seed: 61, ink: C.ink, rim: C.navy, freq: 1 / 60 });
    polyf([[cx - 40, 214], [cx + 40, 214], [cx + 28, 204], [cx - 28, 204]], C.night); hline(cx - 28, cx + 28, 204, C.dusk);
    // TRUMP at the podium, talking, one hand up; the three backers in suits beside him (SAM cheering)
    const P = [[-88, 'MASA', C.amber, 'bald', C.void, C.teal], [-44, 'SAM', C.clay, 'short', C.wine, C.rust], [44, 'LARRY', C.gold, 'bald', C.haze, C.navy]];
    rectf(0, 226, LW, 44, C.void); hline(0, LW, 226, C.navy);
    P.forEach(([dx, n, skin, hair, hc, tie]) => {
      const sam = n === 'SAM';
      personPx(cx + dx, 240, { u: 5, suit: true, top: C.ink, tie, skin, hair, hairC: hc, eyes: 'dot', mouth: 'smile', aL: sam ? 1.3 : -1.1, aR: sam ? .2 : -1.1, name: n, tagUp: sam ? 6 : 0 });
    });
    const TR = trumpPx(cx, 240, { u: 6, aL: -1.1, aR: .9 + spulse(t, 2) * .3, mouth: frac(lt * 2.4) < .6 ? 'o' : 'none' });
    tagPx('TRUMP', cx, TR.top - 2);
    rectf(cx - 16, 214, 32, 26, C.navy); rectb(cx - 16, 214, 32, 26, C.dusk); circf(cx, 225, 5, C.gold); circf(cx, 225, 3, C.amber); pset(cx - 1, 224, C.cream);
    // far hill: Elon
    const g = hill({ cx: 430, y: 200, w: 90, drop: 30, ink: C.ink, rim: C.night });
    personPx(430, g(430), { u: 2, top: C.void, hair: 'short', hairC: C.void, skin: C.gold, name: 'ELON', aR: .6 });
    const ek = lt - b(1.3);   // early enough that the whole quote is up for most of a second before the cut
    if (ek > 0) bubblePx("they don't actually\nhave the money", 404, g(430) - 30, { font: 5, tail: [424, g(430) - 22], n: Math.ceil(ek * 44) });
  });

  // ======================================================================
  // V2.3 Hit "Accept All," never ask — ANDREJ dozes in a hammock, laptop on his belly; on every beat it flashes ACCEPT ALL
  // and another lit room is bolted onto the crooked house of code behind him, taller and wobblier.
  const ROOMS = [[74, 28], [66, 26], [78, 28], [60, 24], [70, 26], [56, 22], [64, 24], [50, 20]];
  function noteSpr(x, y, ink) { vline(x + 3, y - 7, y, ink); rectf(x, y - 1, 4, 3, ink); hline(x + 3, x + 5, y - 7, ink); pset(x + 6, y - 6, ink); }
  line('V2', 3, (p, lt, d, t, s) => {
    const beats = beatsIn(s);
    const nAdd = beats.filter(bt => lt > bt - .05).length;   // one room per beat
    sky({ cy: 320, r: 380 });
    starfield(t, { density: .8 });
    moon(250, 34, 7, { phase: .35 });
    ridge({ y: 210, amp: 8, seed: 71, ink: C.ink, rim: C.navy, freq: 1 / 60 });
    // the crooked house of code (right), one room bolted on per beat
    const nR = 3 + nAdd, baseX = 404, sway = Math.sin(t * 1.4);
    let y = 228, lean = 0;
    for (let i = 0; i < Math.min(nR, ROOMS.length); i++) {
      const [w, h] = ROOMS[i], bt = i >= 3 ? beats[i - 3] : -9, age = lt - bt;
      lean += (i % 2 ? 7 : -3) + i * 1.2 + sway * i * .5;
      const drop = age < .2 ? Math.round((1 - age / .2) ** 2 * 30) : 0, x = Math.round(baseX + lean - w / 2);
      const ry = y - h - drop;
      rectf(x, ry, w, h, C.night); rectb(x, ry, w, h, C.dusk); hline(x, x + w - 1, ry, C.haze);
      triPx(x - 2, ry + 1, x + 8, ry + 1, x - 2, ry - 5, C.ink);                        // a crooked eave
      // lit window full of code
      rectf(x + 4, ry + 4, w - 8, h - 8, C.ink);
      for (let l = 0; l < (h - 10) / 3; l++) { const ind = (l % 3) * 4, lw = 6 + Math.floor(hash2(i, l) * (w - 24)); hline(x + 7 + ind, x + 7 + ind + lw, ry + 6 + l * 3, [C.mint, C.gold, C.haze, C.clay][(i + l) % 4]); }
      if (age >= 0 && age < .6) glow(x + w / 2, ry + h / 2, w * .9, { tab: GREEN, k: 1.3 * (1 - age / .6) });
      // bolts and props
      pset(x + 2, ry + h - 3, C.gold); pset(x + w - 3, ry + h - 3, C.gold); pset(x + 2, ry + 2, C.gold);
      if (i > 0) pline(x + w - 4, ry + h, x + w + 6, ry + h + 10, C.clay);
      y = ry + 1;
    }
    // ground
    const g = x => 228 + Math.round(Math.sin(x * .03) * 2);
    for (let x = 0; x < LW; x++) { pset(x, g(x), C.pine); vline(x, g(x) + 1, LH - 1, C.void); }
    grass(0, LW, g, t);
    // two trees and the hammock between them
    const T1 = 22, T2 = 330;
    for (const tx of [T1, T2]) {
      rectf(tx - 5, 70, 11, 160, C.ink); vline(tx + 5, 72, 228, C.void); vline(tx - 5, 72, 228, C.night);
      circf(tx, 50, 38, C.pine); circf(tx - 24, 68, 24, C.pine); circf(tx + 26, 64, 26, C.pine); circf(tx - 6, 40, 26, mix(C.pine, C.teal, .3));
    }
    const hx0 = T1 + 26, hx1 = T2 - 22, hy0 = 142, sag = 46 + Math.round(breathe(t, 2) * 2);
    const hy = x => hy0 + sag * Math.sin(Math.PI * clamp((x - hx0) / (hx1 - hx0)));
    pline(T1 + 6, 128, hx0, hy0, C.haze); pline(T1 + 6, 132, hx0, hy0 + 2, C.dusk);
    pline(T2 - 6, 128, hx1, hy0, C.haze); pline(T2 - 6, 132, hx1, hy0 + 2, C.dusk);
    // Andrej lying in it, head at the left end
    const body = x => hy(x) - 8;
    const headX = 78, hipX = 196, footX = 270;
    for (let x = headX + 10; x <= footX; x++) { const top = Math.round(body(x)), tor = x < hipX; rectf(x, top - (tor ? 8 : 4), 1, tor ? 12 : 7, tor ? C.navy : C.ink); if (tor) pset(x, top - 8, C.dusk); }
    rectf(footX, Math.round(body(footX)) - 9, 5, 9, C.void);
    // head (tilted back on a pillow), eyes closed, smiling
    const hdy = Math.round(body(headX)) - 16;
    rectf(headX - 16, hdy + 10, 18, 8, C.cream);
    rectf(headX - 8, hdy, 18, 18, C.gold); rectf(headX + 9, hdy + 1, 1, 17, C.amber);
    rectf(headX - 9, hdy - 2, 20, 5, C.void); vline(headX - 9, hdy, hdy + 9, C.void); vline(headX - 8, hdy, hdy + 5, C.void);
    hline(headX - 3, headX, hdy + 8, C.void); hline(headX + 4, headX + 7, hdy + 8, C.void);
    hline(headX - 1, headX + 5, hdy + 13, C.rust); pset(headX - 2, hdy + 12, C.rust); pset(headX + 6, hdy + 12, C.rust);
    // an arm resting behind the head
    thick(headX + 12, hdy + 20, headX + 2, hdy - 4, 4, C.navy); rectf(headX - 1, hdy - 6, 5, 4, C.gold);
    // the hammock fabric (over the lower body)
    for (let x = hx0; x <= hx1; x++) { const yy = Math.round(hy(x)); vline(x, yy - 4, yy + 1, (x >> 1) % 2 ? C.rust : C.clay); pset(x, yy - 5, C.amber); pset(x, yy + 2, C.wine); }
    tagPx('ANDREJ', headX, hdy - 12, { font: 5 });
    // laptop on the belly, lid open toward him
    const lx = 150, ly = Math.round(body(lx)) - 8;
    const flash = beats.some(bt => lt > bt - .05 && lt < bt + .3);
    glow(lx - 8, ly - 10, 34, { tab: GREEN, k: flash ? 1.8 : 1 });
    rectf(lx - 16, ly, 34, 3, C.dusk); hline(lx - 16, lx + 17, ly, C.haze);
    polyf([[lx - 16, ly], [lx - 24, ly - 22], [lx - 20, ly - 24], [lx - 12, ly]], C.void);
    pline(lx - 15, ly - 1, lx - 22, ly - 21, flash ? C.cream : C.mint);
    // "ACCEPT ALL" buttons pop out of the laptop on each beat and float up
    beats.forEach((bt, i) => {
      const age = lt - bt + .05; if (age < 0 || age > 1.8) return;
      const bx = lx + 6 + Math.sin(age * 2 + i) * 8 + i * 6, by = ly - 38 - age * 40, k = 1 - clamp((age - 1.1) / .7);
      rboxf(bx - 34, by - 2, 68, 15, veil(C.void, k), 2); rboxf(bx - 33, by - 1, 66, 13, veil(C.teal, k), 2); hline(bx - 31, bx + 30, by - 1, veil(C.mint, k));
      ptext('ACCEPT ALL', bx, by + 2, veil(C.cream, k), { align: 'center' });
      if (age < .15) sparkle(bx + 34, by - 2, 2, C.cream, C.mint);
    });
    // music notes drifting up
    for (let i = 0; i < 4; i++) { const f = frac(t * .35 + i / 4); noteSpr(98 + i * 7 + Math.sin(f * 6 + i) * 6, 110 - f * 80, veil(i % 2 ? C.haze : C.gold, 1 - f)); }
  });

  // ======================================================================
  // V2.4 MCP for every task — Clawd walks down a night street with a glowing cable and a plug marked MCP, connecting
  // everything it passes on the beats: a streetlamp, a mailbox, a window… then it flings the plug up to a star.
  // The camera follows Clawd along the street.
  function plugPx(x, y) {
    rectf(x - 9, y - 5, 18, 11, C.teal); rectb(x - 9, y - 5, 18, 11, C.mint); hline(x - 8, x + 8, y - 4, C.mint);
    ptext('MCP', x - 6, y - 2, C.cream, { font: 3 });
    rectf(x + 9, y - 3, 3, 1, C.haze); rectf(x + 9, y + 2, 3, 1, C.haze);
  }
  function cableSeg(x0, y0, x1, y1, sag, t) {
    const n = Math.max(2, Math.ceil(Math.hypot(x1 - x0, y1 - y0) / 1.5));
    for (let i = 0; i <= n; i++) {
      const f = i / n, x = lerp(x0, x1, f), y = lerp(y0, y1, f) + Math.sin(f * Math.PI) * sag;
      pset(x, y - 1, C.mint); pset(x, y, C.teal); pset(x, y + 1, C.pine);
      if (frac(f * 3 - t * 1.5) < .05) { pset(x, y - 1, C.cream); pset(x, y, C.cream); }      // light pulses along the cable
    }
  }
  line('V2', 4, (p, lt, d, t, s) => {
    const b = i => B(s, i);
    const GY = 230, LX = 150, MX = 330, WX = 520, SX = 668, SY = 52;
    const tLamp = b(.7), tMail = b(1.6), tWin = b(2.5), tStar = b(3.2);
    const on = tt => lt > tt;
    // Clawd's path: walk, stop to plug in, walk on
    const stops = [[0, 40], [tLamp - .05, LX - 34], [tMail - .1, MX - 52], [tWin - .1, WX - 46]];
    let cx = stops[0][1];
    for (let i = 0; i + 1 < stops.length; i++) { const [t0, x0] = stops[i], [t1, x1] = stops[i + 1]; const ta = i === 0 ? t0 : t0 + .25; if (lt >= ta) cx = lerp(x0, x1, ease(clamp((lt - ta) / (t1 - ta - .05)))); }
    const walking = [[.0, tLamp - .1], [tLamp + .25, tMail - .15], [tMail + .25, tWin - .15]].some(([a, c]) => lt > a && lt < c);
    const throwing = lt > tStar - .15;
    const cam = Math.round(clamp(cx - 150, 0, 330) + (throwing ? 10 * rise(lt, tStar, .8) : 0));
    sky({ cy: 320, r: 380 });
    starfield(t, { density: .7 });
    // far buildings with the billboard (parallax)
    view(cam * .35, 0);
    for (const [bx, bw, bh] of [[260, 50, 100], [318, 70, 124], [396, 44, 90], [450, 60, 110], [520, 50, 80]]) {
      rectf(bx, 214 - bh, bw, bh + 20, C.ink); hline(bx, bx + bw - 1, 214 - bh, C.night);
      for (let wy = 222 - bh; wy < 210; wy += 7) for (let wx = bx + 4; wx < bx + bw - 3; wx += 6) if (hash2(wx, wy) < .28) pset(wx, wy, C.amber);
    }
    signPx('PEOPLE LOVE MCP', 353, 74, { font: 3, ink: C.mint, plate: C.void, edge: C.pine });
    vline(336, 84, 90, C.void); vline(370, 84, 90, C.void);
    view(cam, 0);
    // street
    rectf(cam, GY, LW, 40, C.night); hline(cam, cam + LW, GY, C.dusk); rectf(cam, GY + 8, LW, 32, C.ink);
    for (let x = Math.floor(cam / 40) * 40; x < cam + LW; x += 40) hline(x, x + 16, GY + 18, C.navy);
    // house with a low window
    rectf(466, 150, 150, 80, C.ink); triPx(458, 151, 624, 151, 541, 112, C.void); rectf(580, 118, 8, 22, C.void);
    const wk = on(tWin) ? rise(lt, tWin, .3) : 0;
    rectf(WX - 18, 168, 36, 32, wk > 0 ? mix(C.night, C.gold, wk) : C.night);
    if (wk > .5) { rectf(WX - 16, 186, 10, 14, C.amber); circf(WX + 8, 176, 3, C.amber); }
    rectb(WX - 19, 167, 38, 34, C.void); vline(WX, 168, 199, C.void); hline(WX - 18, WX + 17, 183, C.void);
    if (wk > 0) glow(WX, 184, 50, { tab: WARM, k: 1.1 * wk });
    rectf(WX - 22, 201, 44, 3, C.dusk); hline(WX - 22, WX + 21, 201, C.haze);
    rectf(570, 186, 18, 44, C.void); pset(584, 208, C.gold);
    // streetlamp
    rectf(LX - 1, 84, 3, GY - 84, C.void); rectf(LX - 3, GY - 8, 7, 8, C.void); hline(LX - 1, LX + 26, 82, C.void); hline(LX, LX + 26, 83, C.void);
    polyf([[LX + 16, 84], [LX + 32, 84], [LX + 29, 90], [LX + 19, 90]], C.void);
    const lk = on(tLamp) ? rise(lt, tLamp, .25) : 0;
    hline(LX + 19, LX + 29, 90, lk > 0 ? C.gold : C.navy); hline(LX + 20, LX + 28, 91, lk > 0 ? C.cream : C.night);
    if (lk > 0) { glow(LX + 24, 96, 44, { tab: LIT, k: 1.4 * lk }); polyf([[LX + 19, 92], [LX + 29, 92], [LX + 62, GY], [LX - 14, GY]], lit(.8 * lk)); ellf(LX + 24, GY + 2, 38, 4, lit(1.2 * lk)); }
    // mailbox (the classic round-top kind)
    const mk = on(tMail) ? rise(lt, tMail, .25) : 0;
    rectf(MX - 3, 206, 6, GY - 206, C.void);
    rectf(MX - 14, 178, 28, 28, C.navy); ellf(MX, 178, 14, 8, C.navy); rectf(MX - 14, 178, 28, 1, C.dusk); vline(MX + 13, 176, 205, C.night);
    rectf(MX - 8, 184, 16, 3, C.void); ptext('MAIL', MX, 192, C.dusk, { font: 3, align: 'center' });
    if (mk > .5) { vline(MX + 15, 168, 190, C.void); rectf(MX + 16, 168, 8, 6, C.rust); } else { hline(MX + 15, MX + 28, 190, C.void); rectf(MX + 24, 187, 6, 5, C.rust); }
    if (mk > 0) { glow(MX, 190, 34, { tab: GREEN, k: 1.3 * mk }); rectf(MX - 8, 184, 16, 3, C.mint); }
    // the star
    const sk = on(tStar + .35) ? rise(lt, tStar + .35, .3) : 0;
    if (sk > 0) glow(SX, SY, 40, { tab: LIT, k: 1.6 * sk });
    sparkle(SX, SY, sk > 0 ? 3 : 1, C.cream, sk > 0 ? C.gold : C.haze);
    // Clawd
    const c = clawdPx(cx, GY, { u: 5, walk: walking ? lt * 1.6 : undefined, eyes: throwing ? 'up' : on(tLamp) ? 'happy' : 'open', lookX: throwing ? .6 : .4, aR: throwing ? 1.2 : .15, aL: -.3 });
    const hand = c.handR;
    // cable: through every socket it has been plugged into, in order, then to Clawd's paw (or up to the star)
    const pts = [[cam - 20, GY - 8], [LX, 214], [MX + 14, 196], [WX, 206]];
    const conn = [true, on(tLamp), on(tMail), on(tWin)];
    let last = pts[0];
    for (let i = 1; i < pts.length; i++) if (conn[i]) { cableSeg(last[0], last[1], pts[i][0], pts[i][1], 8, t); rectf(pts[i][0] - 2, pts[i][1] - 2, 5, 5, C.teal); pset(pts[i][0], pts[i][1], C.cream); last = pts[i]; }
    if (!throwing) {
      cableSeg(last[0], last[1], hand[0], hand[1] + 1, 10, t);
      plugPx(hand[0] + 9, hand[1]);
    } else {
      const k = clamp((lt - tStar + .15) / .5), e = easeOut(k), px = lerp(hand[0] + 9, SX - 12, e), py = lerp(hand[1], SY + 4, e) - Math.sin(k * Math.PI) * 30;
      cableSeg(last[0], last[1], px, py, 12 * (1 - k), t);
      plugPx(px, py);
    }
    // plug-in flashes
    [[tLamp, LX, 214], [tMail, MX + 14, 196], [tWin, WX, 206], [tStar + .35, SX, SY]].forEach(([tt, x, y]) => { const a = lt - tt; if (a > 0 && a < .4) { sparkle(x, y, a < .15 ? 3 : 2, C.cream, C.mint); glow(x, y, 14, { tab: GREEN, k: 1.2 * (1 - a / .4) }); } });
    view(0, 0);
    weather(t, 'petals', { n: 18 });
  });

  // ======================================================================
  // V2.5 Zuck's nine-figure poaching spree — ZUCK fishes off a pier at night with a $100M money bag for bait; one by one,
  // tiny researchers are reeled up out of the dark water, glinting, and dropped into a bucket marked MSL.
  function moneyBag(x, y) {        // (x, y) = centre of the sack
    ellf(x, y + 3, 16, 13, C.clay); ellf(x - 3, y, 11, 9, C.amber); pset(x - 8, y - 4, C.gold); pset(x - 7, y - 5, C.gold);
    polyf([[x - 5, y - 10], [x + 5, y - 10], [x + 10, y - 17], [x + 3, y - 14], [x, y - 18], [x - 3, y - 14], [x - 10, y - 17]], C.clay);
    hline(x - 5, x + 5, y - 10, C.rust); hline(x - 5, x + 5, y - 9, C.wine);
    ptext('$100M', x + 1, y - 1, C.wine, { align: 'center' });
  }
  line('V2', 5, (p, lt, d, t, s) => {
    const b = i => B(s, i);
    sky({ cy: 230, r: 300 });
    starfield(t, { density: .8, y1: 132 });
    moon(410, 34, 9, { phase: .3 });
    city(t, { y: 132, x0: 170, grow: .5, lit: .35, seed: 21 });
    ridge({ y: 134, amp: 4, seed: 81, ink: C.ink, rim: C.navy, freq: 1 / 50 });
    water(136, { k: 1.2 });
    // the catches: reel up → swing over → drop in the bucket → cast back out
    const WX = 380, WY = 216, BX = 52, BTOP = 178, D = 1.05;
    const catches = [b(.4), b(1.5), b(2.6)];
    let bag = [WX, WY], ferry = -1, inBucket = 0;
    const HANG = [BX + 4, BTOP - 50];
    catches.forEach((c0, i) => {
      const u = (lt - c0) / D;
      if (u >= .8) inBucket = i + 1;
      if (u < 0 || u >= 1) return;
      if (u < .35) { const k = ease(u / .35); bag = [lerp(WX, WX - 16, k), lerp(WY, 96, k)]; ferry = i; }
      else if (u < .8) { const k = ease((u - .35) / .45); bag = [lerp(WX - 16, HANG[0], k), lerp(96, HANG[1], k) - Math.sin(k * Math.PI) * 50]; ferry = i; }
      else { const k = ease((u - .8) / .2); bag = [lerp(HANG[0], WX, k), lerp(HANG[1], WY, k) - Math.sin(k * Math.PI) * 50]; }
    });
    const resting = bag[1] >= WY - 1;
    if (resting) bag = [bag[0], WY + Math.round(Math.sin(t * 2.2) * 1.5)];
    // ripples where the bait sits in the water
    if (resting) for (let r = 0; r < 3; r++) { const f = frac(t * .6 + r / 3); ellf(WX, WY + 12, 10 + f * 30, 1 + f * 4, veil(C.haze, .5 * (1 - f))); }
    // the pier
    rectf(0, 214, 236, 6, C.navy); hline(0, 235, 214, C.dusk); for (let x = 8; x < 236; x += 16) vline(x, 215, 219, C.ink);
    for (const px of [14, 84, 154, 222]) { rectf(px, 220, 6, 50, C.ink); vline(px + 5, 220, 269, C.void); }
    rectf(0, 220, 236, 2, C.void);
    // the bucket
    polyf([[BX - 24, BTOP], [BX + 24, BTOP], [BX + 20, 214], [BX - 20, 214]], C.dusk);
    hline(BX - 24, BX + 23, BTOP, C.haze); hline(BX - 23, BX + 22, BTOP + 1, C.cream); vline(BX + 20, BTOP + 2, 213, C.navy);
    hline(BX - 22, BX + 21, BTOP + 30, C.navy);
    ptext('MSL', BX, BTOP + 9, C.cream, { align: 'center', scale: 2, shadow: C.navy });
    pline(BX - 23, BTOP, BX, BTOP - 16, C.haze); pline(BX + 23, BTOP, BX, BTOP - 16, C.haze);
    // researchers peeking out of the bucket
    for (let i = 0; i < inBucket; i++) {
      const hx = BX - 13 + i * 13, hy = BTOP - 5 - (i === inBucket - 1 ? Math.round(breathe(t, 1) * 2) : 0);
      rectf(hx - 4, hy - 4, 9, 9, SKIN[i % 3]); rectf(hx - 4, hy - 6, 9, 3, [C.void, C.wine, C.rust][i]);
      pset(hx - 2, hy, C.void); pset(hx + 2, hy, C.void); hline(hx - 1, hx + 1, hy + 3, C.rust);
      if (i === inBucket - 1) { rectf(hx - 7, hy - 5, 2, 4, SKIN[i % 3]); rectf(hx + 6, hy - 5, 2, 4, SKIN[i % 3]); }
      rectf(BX - 22, BTOP, 44, 1, C.haze);
    }
    // Zuck with the rod
    const Z = personPx(150, 214, { u: 7, top: C.haze, pants: C.ink, hair: 'curly', hairC: C.wine, skin: C.gold, eyes: 'dot', mouth: 'smile', aR: .55, aL: -.9 });
    const [hx, hy] = Z.handR, aim = Math.atan2(bag[1] - 80 - hy, bag[0] - hx), RL = 170;
    const tipX = hx + Math.cos(aim) * RL, tipY = hy + Math.sin(aim) * RL;
    for (let i = 0; i <= 50; i++) { const f = i / 50, x = lerp(hx, tipX, f), y = lerp(hy, tipY, f) + Math.sin(f * Math.PI) * (ferry >= 0 ? 12 : 5); pset(x, y, f < .25 ? C.clay : C.dusk); if (f < .15) pset(x, y + 1, C.rust); }
    circf(hx + 6, hy + 2, 2, C.void); pset(hx + 6, hy + 2, C.haze);
    rectf(hx - 2, hy - 2, 4, 4, C.gold);
    pline(tipX, tipY, bag[0], bag[1] - 18, C.haze);
    // the bait (and whoever is clinging to it)
    if (ferry >= 0) {
      personPx(bag[0], bag[1] + 50, { u: 4, top: [C.teal, C.violet, C.rust][ferry], hair: ['short', 'long', 'curly'][ferry], hairC: [C.void, C.wine, C.void][ferry], skin: SKIN[ferry % 3], aL: 1.4, aR: 1.4, eyes: 'up', mouth: 'o' });
      sparkle(bag[0] + 18, bag[1] - 6, spulse(t, 3) > .5 ? 3 : 2, C.cream, C.gold);
    }
    moneyBag(bag[0], bag[1]);
    weather(t, 'fireflies', { n: 12, x0: 240, x1: 480, y0: 140, y1: 240 });
  });

  // ======================================================================
  // V2.6 Superintelligence — buy three! — a late-night TV glows in a dark room: an infomercial with three boxed
  // SUPERINTELLIGENCEs on a shelf, and the dusty-red starburst "BUY 3!" pops on the first beat.
  // the labs Meta held talks to buy that June: SSI, Thinking Machines ("Thinky") and Perplexity
  const BOXES = [['SSI', C.teal, C.pine], ['THINKY', C.dusk, C.navy], ['PERPLEXITY', C.violet, C.wine]];
  line('V2', 6, (p, lt, d, t, s) => {
    cutIn();
    const burstT = B(s, 0) - .02;
    rectf(0, 0, LW, LH, C.void);
    // wall and floor of the dark room
    rectf(0, 0, LW, 214, C.ink); for (let x = 12; x < LW; x += 26) vline(x, 0, 213, C.void);
    rectf(0, 214, LW, 56, C.void); hline(0, LW, 214, C.night);
    glow(240, 120, 250, { tab: LIT, k: 1.3, ry: 150 });
    // TV
    const X0 = 86, Y0 = 16, X1 = 394, Y1 = 214;
    rboxf(X0, Y0, X1 - X0, Y1 - Y0, C.night, 2); rboxf(X0 + 1, Y0 + 1, X1 - X0 - 2, Y1 - Y0 - 2, C.ink, 2); hline(X0 + 3, X1 - 4, Y0 + 1, C.navy);
    rectf(X0 + 30, Y1, 10, 8, C.night); rectf(X1 - 40, Y1, 10, 8, C.night);
    for (let i = 0; i < 5; i++) hline(X1 - 70, X1 - 30, Y1 - 12 + i * 2, C.void);
    circf(X0 + 24, Y1 - 9, 3, C.dusk); circf(X0 + 40, Y1 - 9, 3, C.dusk); pset(X0 + 24, Y1 - 11, C.haze);
    const SX0 = X0 + 10, SY0 = Y0 + 10, SW = X1 - X0 - 20, SH = Y1 - Y0 - 36;
    clipRect(SX0, SY0, SW, SH);
    const on = clamp(lt / .14);
    if (on < 1) {           // the set switching on: a bright line opening up
      rectf(SX0, SY0, SW, SH, C.void);
      const hh = Math.max(1, Math.round(SH * on * .5)), mid = SY0 + SH / 2;
      rectf(SX0, mid - hh, SW, hh * 2, C.haze); hline(SX0, SX0 + SW, mid, C.cream);
    } else {
      // infomercial set: rotating rays
      const cx = 240, cy = 140, rot = lt * .25;
      rectf(SX0, SY0, SW, SH, inkFn((x, y) => { const a = Math.atan2(y - cy, x - cx) + rot; return (Math.floor(a / TAU * 24) & 1) ? C.wine : C.violet; }));
      glow(cx, 110, 150, { tab: LIT, k: .8, ry: 80 });
      // headline
      ptext('AS SEEN ON TV', SX0 + 10, SY0 + 6, C.gold, { font: 3, shadow: C.void });
      // shelf + three boxes
      const shelfY = SY0 + 142;
      BOXES.forEach(([brand, face, side], i) => {
        const bx = SX0 + 26 + i * 86, bw = 64, bh = 74, by = shelfY - bh;
        polyf([[bx, by], [bx + 6, by - 6], [bx + bw + 6, by - 6], [bx + bw, by]], LIT[face]);
        rectf(bx + bw, by, 6, bh, side); polyf([[bx + bw, by], [bx + bw + 6, by - 6], [bx + bw + 6, by + bh - 6], [bx + bw, by + bh]], side);
        rectf(bx, by, bw, bh, face); rectb(bx, by, bw, bh, C.void);
        rectf(bx + 1, by + 1, bw - 2, 11, C.void); ptext(brand, bx + bw / 2, by + 4, C.gold, { font: 3, align: 'center' });
        ptext('SUPER', bx + bw / 2 + 1, by + 18, C.cream, { scale: 2, align: 'center', shadow: C.void, gap: 1 });
        ptext('INTELLIGENCE', bx + bw / 2, by + 38, C.cream, { font: 3, align: 'center' });
        sparkle(bx + bw / 2, by + 60, hash2(i, sbeat(t)) < .5 ? 2 : 1, C.cream, C.gold);
        hline(bx + 8, bx + bw - 9, by + 70, LIT[face]);
      });
      rectf(SX0, shelfY, SW, 5, C.clay); hline(SX0, SX0 + SW, shelfY, C.amber); rectf(SX0, shelfY + 5, SW, 2, C.wine);
      // ticker
      rectf(SX0, SY0 + SH - 12, SW, 12, C.rust); hline(SX0, SX0 + SW, SY0 + SH - 12, C.clay);
      const msg = 'CALL NOW · OPERATORS STANDING BY · 1-800-SUPER-AI · ', mw = ptextW(msg, { font: 3 }), off = (lt * 60) % mw;
      for (let k = -1; k < 3; k++) ptext(msg, SX0 + 4 - off + k * mw, SY0 + SH - 9, C.cream, { font: 3 });
      // BUY 3! bursts in on the first beat
      const bk = clamp((lt - burstT) / .22);
      if (bk > 0) {
        // (clear of the boxes' labels, PERPLEXITY's the longest)
        const bxc = SX0 + SW - 52, byc = SY0 + 29, R = 36 * (1 + .04 * breathe(t, 1));
        starburst(bxc, byc, R, easeOut(bk), { n: 16, inner: .55, rot: lt * .2, fringe: C.wine });
        if (bk > .6) ptext('BUY 3!', bxc + 1, byc - 6, C.cream, { scale: 2, align: 'center', shadow: C.wine });
        if (bk < 1) glow(bxc, byc, 70, { tab: LIT, k: 1.4 * (1 - bk) });
      }
      // scanlines
      for (let y = SY0 + 1; y < SY0 + SH; y += 2) rectf(SX0, y, SW, 1, dim(.3));
    }
    noClip();
    rectb(SX0 - 1, SY0 - 1, SW + 2, SH + 2, C.void);
    // Clawd on the couch, back to us, lit by the screen
    rectf(300, 232, 180, 38, C.void); rboxf(290, 222, 190, 14, C.ink, 2); hline(292, 478, 222, C.navy);
    rectf(390, 196, 50, 32, C.ink); hline(390, 439, 196, C.haze); vline(390, 197, 227, C.navy); vline(439, 197, 227, C.navy);
    rectf(384, 206, 6, 6, C.ink); rectf(440, 206, 6, 6, C.ink); hline(384, 389, 206, C.dusk); hline(440, 445, 206, C.dusk);
  });

  // ======================================================================
  // V2.7 Grok goes MechaHitler mode — tasteful: a robot on a hill, its screen glitching red behind a black REDACTED bar,
  // sparks crackling; a hand reaches in from the edge of frame and yanks its plug. Its light dies.
  line('V2', 7, (p, lt, d, t, s) => {
    const b = i => B(s, i);
    const reach = b(.7), yank = b(1.5);
    const dead = lt > yank, dieK = clamp((lt - yank) / .3);
    sky({ cy: 320, r: 380 });
    starfield(t, { density: .8 });
    ridge({ y: 214, amp: 10, seed: 91, ink: C.ink, rim: C.navy, freq: 1 / 70 });
    const g = hill({ cx: 180, y: 232, w: 320, drop: 24, ink: C.void, rim: C.pine });
    grass(0, LW, g, t);
    const x = 176, gy = g(x), slump = dead ? Math.round(3 * rise(lt, yank + .2, .4)) : 0;
    // socket post on the right; the cord runs from the robot's back along the grass to it
    const PX = 404, PY = 176;
    rectf(PX - 3, PY + 10, 7, g(PX) - PY - 8, C.ink); vline(PX + 3, PY + 10, g(PX), C.void);
    rboxf(PX - 11, PY - 12, 23, 24, C.navy, 1); rectb(PX - 11, PY - 12, 23, 24, C.dusk); hline(PX - 10, PX + 10, PY - 11, C.haze);
    rectf(PX - 4, PY - 4, 2, 5, C.void); rectf(PX + 3, PY - 4, 2, 5, C.void);
    const handK = rise(lt, reach - .4, .4), pull = dead ? easeOut(clamp((lt - yank) / .25)) : 0;
    const plug = dead ? [lerp(PX + 16, 500, pull), lerp(PY, PY - 40, pull)] : [PX + 16, PY];
    const cordPts = [[x + 34, gy - 44], [x + 44, gy - 3], [300, g(300) - 2], [PX - 16, g(PX - 16) - 2]];
    for (let k = 0; k < 2; k++) plines(cordPts.map(([a, c]) => [a, c - k]), k ? C.ink : C.void);
    pline(PX - 16, g(PX - 16) - 2, plug[0] - 8, plug[1] + 3, C.void); pline(PX - 16, g(PX - 16) - 3, plug[0] - 8, plug[1] + 2, C.ink);
    rectf(plug[0] - 9, plug[1] - 5, 12, 11, C.haze); hline(plug[0] - 9, plug[0] + 2, plug[1] - 5, C.cream); vline(plug[0] + 2, plug[1] - 4, plug[1] + 5, C.dusk);
    if (dead) { rectf(plug[0] - 12, plug[1] - 3, 3, 2, C.dusk); rectf(plug[0] - 12, plug[1] + 2, 3, 2, C.dusk); }
    // the hand from off-frame right
    if (handK > 0) {
      const hx = dead ? plug[0] + 4 : lerp(510, PX + 20, easeOut(handK)), hy = dead ? plug[1] : lerp(PY - 16, PY, handK);
      thick(hx + 12, hy - 1, 520, hy - 10, 14, C.navy); thick(hx + 10, hy - 1, hx + 14, hy - 2, 14, C.haze);
      rboxf(hx - 4, hy - 7, 16, 14, C.gold, 2); rectf(hx - 8, hy - 7, 5, 4, C.gold); rectf(hx - 7, hy - 2, 4, 3, C.gold); rectf(hx - 7, hy + 2, 4, 3, C.gold);
      hline(hx - 3, hx + 10, hy + 6, C.amber); pset(hx - 8, hy - 8, C.amber);
    }
    // the robot
    rectf(x - 22, gy - 18, 13, 18, C.dusk); rectf(x + 10, gy - 18, 13, 18, C.dusk); rectf(x - 24, gy - 3, 17, 3, C.navy); rectf(x + 8, gy - 3, 17, 3, C.navy);
    const bdy = gy - 18 - 46 + slump;
    rectf(x - 34, bdy, 68, 46, C.navy); rectb(x - 34, bdy, 68, 46, C.dusk); hline(x - 33, x + 32, bdy + 1, C.haze); vline(x + 32, bdy + 2, bdy + 44, C.night);
    rectf(x - 27, bdy + 6, 54, 20, C.void); ptext('GROK', x + 1, bdy + 9, dead ? C.dusk : C.cream, { align: 'center', scale: 2 });
    for (let i = 0; i < 4; i++) rectf(x - 21 + i * 12, bdy + 33, 4, 4, dead ? C.ink : hash2(i, boilFrame(T) >> 1) < .5 ? C.rust : C.gold);
    const armA = dead ? .05 : .45;
    for (const sd of [-1, 1]) { const ax = x + sd * 36, ay = bdy + 6; thick(ax, ay, ax + sd * Math.sin(armA) * 10, ay + Math.cos(armA) * 30, 8, C.dusk); rectf(ax + sd * Math.sin(armA) * 10 - 4, ay + Math.cos(armA) * 30 - 1, 9, 6, C.navy); }
    rectf(x - 6, bdy - 6, 12, 6, C.dusk);
    const hdy = bdy - 6 - 60 + slump;
    rectf(x - 44, hdy, 88, 60, C.dusk); rectb(x - 44, hdy, 88, 60, C.navy); hline(x - 43, x + 42, hdy + 1, C.haze); vline(x + 42, hdy + 2, hdy + 58, C.navy);
    vline(x, hdy - 14, hdy, C.navy); circf(x, hdy - 16, 3, dead ? C.ink : spulse(t, 3) > .4 ? C.rust : C.wine);
    const SX = x - 38, SY = hdy + 6, SW = 76, SH = 48;
    rectf(SX, SY, SW, SH, C.void);
    if (!dead) {
      // glitching red face behind a black bar
      glow(x, SY + SH / 2, 64, { tab: WARM, k: .8 + .4 * fx(9) });
      rectf(SX, SY, SW, SH, C.void);
      for (let r = 0; r < SH; r += 2) { const o = Math.round((fx(r) - .5) * 12), on = fx(r, 3) < .72; if (on) hline(SX + 2 + Math.max(0, o), SX + SW - 3 + Math.min(0, o), SY + r, fx(r, 5) < .3 ? C.clay : fx(r, 6) < .5 ? C.rust : C.wine); }
      rectf(SX + 18, SY + 34, 40, 4, C.void);
      rectf(SX - 6, SY + 10, SW + 12, 15, C.void); rectb(SX - 6, SY + 10, SW + 12, 15, C.ink);
      ptext('REDACTED', x, SY + 14, C.cream, { align: 'center' });
      for (let i = 0; i < 7; i++) if (fx(i, 11) < .55) { const a = fx(i, 12) * TAU, r = 52 + fx(i, 13) * 12, sx = x + Math.cos(a) * r, sy = hdy + 30 + Math.sin(a) * r * .75; pset(sx, sy, C.cream); pset(sx + (fx(i, 14) < .5 ? 1 : -1), sy + 1, C.gold); pset(sx, sy - 1, C.gold); }
    } else if (dieK < 1) {
      // CRT collapse: a line, then a dot
      if (dieK < .5) { const hh = Math.max(1, Math.round((1 - dieK * 2) * SH / 2)); rectf(SX, SY + SH / 2 - hh, SW, hh * 2, C.haze); hline(SX, SX + SW - 1, SY + SH / 2, C.cream); }
      else circf(x, SY + SH / 2, Math.max(0, 6 * (1 - dieK)), C.cream);
    }
    weather(t, 'fireflies', { n: dead ? 14 : 8, y0: 200, y1: 244 });
  });

  // ======================================================================
  // V2.8 Two labs win Olympiad gold — two robots squeeze onto the top step of a starlit podium; gold medals come down
  // around their necks while π, √ and ∑ drift around them like fireflies. "35/42" above.
  const MATH = [
    ['#####', '.#.#.', '.#.#.', '.#.#.', '.#..#'],                          // π
    ['....###', '....#..', '#...#..', '.#.#...', '..#....'],                // √
    ['#####', '.#...', '..#..', '.#...', '#####'],                          // ∑
    ['..##', '..#.', '..#.', '..#.', '##..'],                               // ∫
    ['.#.#.', '#.#.#', '.#.#.'],                                            // ∞
    ['#...#', '.#.#.', '..#..', '.#.#.', '#...#'],                          // x
  ];
  const glyphPx = (rows, x, y, ink) => rows.forEach((r, j) => [...r].forEach((c, i) => { if (c === '#') pset(x + i, y + j, ink); }));
  line('V2', 8, (p, lt, d, t, s) => {
    const b = i => B(s, i);
    sky({ cy: 150, cx: 240, r: 300, vert: .2 });
    starfield(t, { density: 1, bright: .4 });
    glow(240, 150, 170, { tab: LIT, k: .7, ry: 120 });
    // podium
    const PX = 240, TOP = 168;
    rectf(PX - 62, TOP, 124, 74, C.navy); hline(PX - 62, PX + 61, TOP, C.haze); vline(PX + 61, TOP + 1, 241, C.night);
    rectf(PX - 140, 196, 78, 46, C.night); hline(PX - 140, PX - 63, 196, C.dusk);
    rectf(PX + 62, 208, 78, 34, C.night); hline(PX + 62, PX + 139, 208, C.dusk);
    ptext('1', PX, 186, C.gold, { scale: 3, align: 'center', shadow: C.void });
    ptext('2', PX - 101, 210, C.haze, { scale: 2, align: 'center' });
    ptext('3', PX + 101, 218, C.haze, { scale: 2, align: 'center' });
    rectf(0, 242, LW, 28, C.void); hline(0, LW, 242, C.ink);
    ptext('IMO 2025', PX, 230, C.dusk, { font: 3, align: 'center' });
    // the two robots, squeezed together onto the top step
    const medK = rise(lt, b(1) - .3, .45, easeOut), won = medK >= 1;
    const bots = [[PX - 26, C.teal, 'OPENAI'], [PX + 26, C.violet, 'DEEPMIND']];
    bots.forEach(([bx, body, name], i) => {
      const hop = won && lt < b(3.2) ? Math.round(Math.max(0, Math.sin((lt - b(1.2)) * 5 + i * 1.6)) * 3) : 0;
      const r = botPx(bx, TOP, { u: 6, body, face: won ? 'happy' : 'dot', aL: i === 1 && won ? 1.2 : -1.1, aR: i === 0 && won ? 1.2 : -1.1, dy: hop, antenna: C.gold });
      tagPx(name, bx + (i ? 10 : -10), r.top - 3 - hop, { font: 5 });
      const chest = TOP - 6 - 22 - hop, my = lerp(-20, chest, medK);
      if (medK < 1) { pline(bx - 4, -2, bx - 2, my - 5, C.rust); pline(bx + 4, -2, bx + 2, my - 5, C.rust); }
      else { thick(bx - 7, chest - 12, bx - 1, my - 4, 2, C.rust); thick(bx + 7, chest - 12, bx + 1, my - 4, 2, C.wine); glow(bx, my, 18, { tab: WARM, k: 1 }); }
      medalPx(bx, Math.round(my), { r: 6, ribbon: false, shine: won ? spulse(t + i * .3, 3) : 0 });
    });
    // score
    const sk = rise(lt, b(2) - .1, .3);
    if (sk > 0) {
      ptext('35/42', PX, 26, veil(C.gold, sk), { scale: 3, dots: true, align: 'center', off: veil(C.ink, sk) });
      ptext('GOLD', PX, 52, veil(C.amber, sk), { font: 3, align: 'center' });
    }
    // math symbols drifting like fireflies
    for (let i = 0; i < 16; i++) {
      const gx = 30 + hash2(i, 1) * 420 + Math.sin(t * .5 + i * 2.1) * 14, gy = 64 + hash2(i, 2) * 120 + Math.sin(t * .7 + i) * 8;
      if (Math.abs(gx - PX) < 80 && gy > 70) continue;
      const bl = breathe(t, 3, hash(i + 5)); if (bl < .15) continue;
      if (bl > .6) glow(gx + 2, gy + 2, 10, { tab: WARM, k: .9 });
      glyphPx(MATH[i % MATH.length], Math.round(gx), Math.round(gy), bl < .4 ? C.amber : bl < .7 ? C.gold : C.cream);
    }
  });

  // ======================================================================
  // V2.9 GPT-5 breaks 4o hearts — a glowing heart balloon marked 4o floats away over a hill while people reach up with
  // #KEEP4O signs; it cracks down the middle. Then its string snaps down to a paywall post and ties itself on
  // (4o came back, for paying users), and a bandage covers the crack.
  function bigHeart(x, y, fill) {       // (x, y) = centre; ~84 × 72
    circf(x - 20, y - 12, 21, fill); circf(x + 20, y - 12, 21, fill);
    polyf([[x - 41, y - 7], [x + 42, y - 7], [x + .5, y + 40]], fill);
  }
  function heartBalloon(x, y, crackK, split, bandage, t) {
    x = Math.round(x); y = Math.round(y);
    glow(x, y, 70, { tab: WARM, k: .8 });
    const draw = () => {
      bigHeart(x, y, C.rust);
      circf(x - 23, y - 16, 13, C.clay); circf(x + 15, y - 18, 10, mix(C.rust, C.clay, .5));
      circf(x - 27, y - 22, 4, C.amber); pset(x - 28, y - 24, C.gold); pset(x - 27, y - 24, C.cream); pset(x - 29, y - 23, C.cream);
      ptext('4o', x + 1, y - 16, C.cream, { scale: 3, align: 'center', shadow: C.wine });
      rectf(x - 2, y + 40, 5, 3, C.wine);
    };
    if (split > 0) {
      const sx = Math.round(split);
      clipRect(0, 0, x, LH); view(sx, 0); draw(); view(0, 0); noClip();
      clipRect(x, 0, LW - x, LH); view(-sx, 0); draw(); view(0, 0); noClip();
    } else draw();
    if (crackK > 0) {
      const pts = [[x, y - 18], [x - 4, y - 8], [x + 3, y + 1], [x - 3, y + 11], [x + 2, y + 21], [x - 1, y + 30], [x, y + 40]], n = crackK * (pts.length - 1);
      const seg = (a, c) => { thick(a[0], a[1], c[0], c[1], split > 0 ? 3 : 2, C.void); };
      for (let i = 0; i < Math.floor(n); i++) seg(pts[i], pts[i + 1]);
      if (n % 1 && n < pts.length - 1) { const i = Math.floor(n), f = n - i; seg(pts[i], [lerp(pts[i][0], pts[i + 1][0], f), lerp(pts[i][1], pts[i + 1][1], f)]); }
    }
    if (bandage > 0) {
      const k = bandage;
      for (const [bx, by, ang] of [[x, y + 2, .5], [x, y + 20, -.4]]) {
        const w = 32 * k, dx = Math.cos(ang) * w / 2, dy = Math.sin(ang) * w / 2;
        thick(bx - dx, by - dy, bx + dx, by + dy, 7, C.cream); thick(bx - dx * .3, by - dy * .3, bx + dx * .3, by + dy * .3, 7, C.gold);
        pset(bx - dx * .6, by - dy * .6, C.haze); pset(bx + dx * .6, by + dy * .6, C.haze);
      }
    }
  }
  line('V2', 9, (p, lt, d, t, s) => {
    const b = i => B(s, i);
    const crackT = b(1.1), tieT = b(2.2);
    sky({ cy: 320, r: 380 });
    starfield(t, { density: .8 });
    ridge({ y: 206, amp: 10, seed: 101, ink: C.ink, rim: C.navy, freq: 1 / 70 });
    const g = hill({ cx: 240, y: 214, w: 300, drop: 24, ink: C.void, rim: C.pine });
    grass(0, LW, g, t);
    const tied = lt > tieT, tk = rise(lt, tieT, .5, easeOut);
    // the balloon: drifting away, then hauled back down to the post
    const fx0 = lerp(226, 290, easeOut(clamp(lt / (tieT + .2)))), fy0 = lerp(128, 62, easeOut(clamp(lt / (tieT + .2))));
    const PX = 240, PY = g(240) - 34;
    const hx = tied ? lerp(fx0, PX + 6, tk) : fx0, hy = (tied ? lerp(fy0, 100, tk) : fy0) + Math.sin(t * 1.4) * 2;
    // the paywall post
    rectf(PX - 3, PY, 6, g(PX) - PY + 2, C.dusk); hline(PX - 3, PX + 2, PY, C.haze); vline(PX + 2, PY + 1, g(PX), C.navy);
    if (tied) { const tg = rise(lt, tieT + .3, .3); if (tg > 0) { pline(PX + 3, PY + 6, PX + 10, PY + 12, C.haze); rboxf(PX + 8, PY + 11, 36, 11, veil(C.cream, tg), 1); if (tg > .5) ptext('$20/MO', PX + 26, PY + 13, C.wine, { font: 3, align: 'center' }); } }
    // the string
    const sy0 = hy + 43;
    if (!tied) { for (let i = 0; i < 40; i++) { const f = i / 40; pset(hx + Math.sin(f * 7 + t * 3) * 4 * f, sy0 + f * 50, C.haze); } }
    else { const n = 40; for (let i = 0; i < n; i++) { const f = i / n, x = lerp(hx, PX, f) + Math.sin(f * Math.PI) * 6 * (1 - tk), y = lerp(sy0, PY + 4, f); pset(x, y, C.haze); } circf(PX, PY + 4, 1, C.cream); }
    // people reaching up with signs
    const folk = [[60, C.teal, 'long', C.wine], [122, C.violet, 'short', C.void], [362, C.clay, 'curly', C.void], [420, C.dusk, 'bun', C.rust]];
    folk.forEach(([x, top, hair, hairC], i) => {
      const P = personPx(x, g(x), { u: 6, top, hair, hairC, skin: SKIN[i % 3], eyes: tied ? 'closed' : 'up', mouth: tied ? 'smile' : lt > crackT ? 'o' : 'none', aL: 1.3, aR: i % 2 ? 1.1 : -.8, dy: tied && hash2(i, sbeat(t)) < .5 ? Math.round(spulse(t, 3) * 3) : 0 });
      {
        const [sx, sy] = P.handL; vline(sx, sy - 14, sy, C.clay); vline(sx + 1, sy - 14, sy, C.rust);
        rectf(sx - 25, sy - 29, 50, 15, C.cream); rectb(sx - 25, sy - 29, 50, 15, C.void);
        ptext('#keep4o', sx, sy - 26, C.rust, { align: 'center' });
      }
    });
    // the balloon itself
    const crackK = clamp((lt - crackT) / .35), split = lt > crackT + .35 && !tied ? 2 : 0;
    heartBalloon(hx, hy, crackK, split, rise(lt, tieT + .45, .3), t);
    if (lt > crackT && lt < crackT + .4) for (let i = 0; i < 7; i++) pset(hx + (fx(i) - .5) * 20, hy - 18 + fx(i, 1) * 56, C.cream);
    weather(t, 'fireflies', { n: 12, y0: 170, y1: 240 });
  });

  // ======================================================================
  // V2.10 Nano Banana tops the charts — the skyline is a bar chart of app icons; the moon rises as a golden banana,
  // climbs to perch on top of the tallest bar, and puts on sunglasses. #1.
  const BARS = [[26, 44, C.violet], [72, 66, C.teal], [118, 54, C.rust], [164, 88, C.dusk], [214, 124, C.mint], [264, 98, C.clay], [310, 70, C.gold], [356, 58, C.haze], [402, 40, C.violet], [448, 30, C.teal]];
  function bananaPx(x, y, shades) {   // (x, y) = centre of the curve's bottom; a smiling crescent ~50 × 20
    const R = 26, cyO = y - R + 6, cyI = cyO - 9;
    const sx = Math.round(x), sy0 = Math.round(cyO), sy1 = Math.round(cyI);
    rectf(x - R - 1, y - 24, 2 * R + 3, 32, inkFn((px, py, u) => {
      const wx = px + VX, wy = py + VY, dO = Math.hypot(wx - sx, wy - sy0), dI = Math.hypot((wx - sx) * .92, wy - sy1);
      if (dO > R || dI < R - 1 || wy < sy0 - 2) return -1;
      const edge = R - dO, low = (wy - sy0) / R;
      if (edge < 1.2) return C.clay;
      return low > .78 && bay(px, py) < .6 ? C.amber : edge > 5 && low < .6 && bay(px, py) < .5 ? C.cream : C.gold;
    }));
    // stem and tip
    rectf(x - R - 2, y - 26, 5, 5, C.wine); pset(x - R - 3, y - 27, C.rust);
    rectf(x + R - 2, y - 23, 3, 3, C.wine);
    if (shades !== undefined) {
      const sy = Math.round(y - 6 - shades);
      rectf(x - 13, sy, 11, 6, C.void); rectf(x + 2, sy, 11, 6, C.void); hline(x - 2, x + 2, sy + 1, C.void);
      hline(x - 15, x - 13, sy + 1, C.void); hline(x + 13, x + 15, sy + 1, C.void);
      pset(x - 11, sy + 1, C.haze); pset(x + 4, sy + 1, C.haze); pset(x - 10, sy + 1, C.cream);
    }
  }
  line('V2', 10, (p, lt, d, t, s) => {
    const b = i => B(s, i);
    const landT = b(2) - .1, shadesT = b(2.7) - .1;
    sky({ cy: 320, r: 380 });
    starfield(t, { density: .8 });
    // the banana moon: arcs up from behind the bars and lands on the tallest one
    const tb = BARS[4], topX = tb[0] + 18, topY = 226 - tb[1] - 12;
    const k = clamp(lt / landT), e = ease(k);
    const bx = lerp(60, topX, e), by = lerp(236, topY, e) - Math.sin(k * Math.PI) * 110 + (k >= 1 ? Math.round(breathe(t, 2) * 1) : 0);
    if (k < 1) glow(bx, by - 12, 60, { tab: LIT, k: 1.1 });
    // chart gridlines + axis
    for (let gy = 226 - 30; gy > 60; gy -= 30) pline(14, gy, 466, gy, C.night, { every: 3 });
    // bars (buildings), each topped with an app icon
    BARS.forEach(([x, h, ic], i) => {
      const top = 226 - h, w = 36;
      rectf(x, top, w, h, C.ink); hline(x, x + w - 1, top, C.navy); vline(x + w - 1, top + 1, 225, C.void);
      for (let wy = top + 6; wy < 222; wy += 6) for (let wx = x + 4; wx < x + w - 4; wx += 6) if (hash2(wx, wy) < .45) rectf(wx, wy, 2, 2, hash2(wy, wx) < .5 ? C.amber : C.gold);
      if (i !== 4) { rboxf(x + 10, top - 16, 16, 16, ic, 2); rectf(x + 14, top - 12, 8, 8, DIM[ic]); pset(x + 15, top - 11, LIT[ic]); }
    });
    // the tallest bar's icon gets nudged aside when the banana lands
    const nudge = k >= 1 ? Math.round(rise(lt, landT, .3) * 22) : 0;
    rboxf(tb[0] + 10 + nudge, 226 - tb[1] - 16 + Math.round(nudge * .3), 16, 16, C.mint, 2); rectf(tb[0] + 14 + nudge, 226 - tb[1] - 12 + Math.round(nudge * .3), 8, 6, C.teal); pset(tb[0] + 16 + nudge, 226 - tb[1] - 6 + Math.round(nudge * .3), C.teal);
    rectf(0, 226, LW, 44, C.void); hline(8, 472, 226, C.haze);
    for (let x = 26; x < 480; x += 46) vline(x + 18, 227, 229, C.dusk);
    // banana + sunglasses
    const sk = lt > shadesT ? 1 - rise(lt, shadesT, .25, easeIn) : null;
    bananaPx(bx, by, sk === null ? undefined : Math.round(sk * 26));
    if (k >= 1 && lt < landT + .3) sparkle(bx, by + 4, 3, C.cream, C.gold);
    // #1
    const nk = rise(lt, shadesT + .2, .3);
    if (nk > 0) {
      ptext('#1', topX + 44, topY - 40, veil(C.gold, nk), { scale: 3, shadow: veil(C.wine, nk) });
      sparkle(topX + 90, topY - 42, spulse(t, 3) > .5 ? 3 : 2, C.cream, C.gold);
    }
    weather(t, 'fireflies', { n: 10, y0: 120, y1: 220 });
  });

  // ======================================================================
  // V2.11 Billion-five: Anthropic's prize — books fly out of a library's windows like birds and settle in a row with
  // little faces; a sheepish Clawd (sweat drop, blushing) holds out a giant cheque. $3,000 a book.
  const BOOKC = [C.rust, C.teal, C.violet, C.gold, C.dusk, C.clay, C.mint, C.haze, C.rust];
  line('V2', 11, (p, lt, d, t, s) => {
    const b = i => B(s, i);
    const chequeT = b(1.6) - .1;
    sky({ cy: 320, r: 380 });
    starfield(t, { density: .7 });
    ridge({ y: 206, amp: 8, seed: 111, ink: C.ink, rim: C.navy, freq: 1 / 60 });
    // the library (left)
    layer('v2.11-library', () => {
      rectf(14, 108, 186, 120, C.night); triPx(6, 109, 208, 109, 107, 70, C.navy); triPx(18, 106, 196, 106, 107, 78, C.ink);
      rectf(8, 104, 198, 6, C.navy); hline(8, 205, 104, C.dusk);
      ptext('LIBRARY', 107, 90, C.haze, { font: 3, align: 'center' });
      for (let i = 0; i < 6; i++) { const cx = 26 + i * 33; rectf(cx, 112, 8, 108, C.dusk); vline(cx, 112, 219, C.haze); vline(cx + 7, 112, 219, C.navy); rectf(cx - 2, 110, 12, 3, C.haze); rectf(cx - 2, 218, 12, 3, C.navy); }
      for (let i = 0; i < 5; i++) { const wx = 38 + i * 33; rectf(wx, 128, 16, 26, C.gold); rectf(wx, 128, 16, 3, C.amber); vline(wx + 8, 128, 153, C.clay); for (let r = 0; r < 3; r++) for (let c = 0; c < 4; c++) rectf(wx + 1 + c * 4, 134 + r * 7, 2, 5, [C.rust, C.teal, C.violet, C.clay][(c + r + i) % 4]); }
      rectf(8, 220, 198, 8, C.navy); hline(8, 205, 220, C.dusk);
    });
    for (let i = 0; i < 5; i++) glow(46 + i * 33, 141, 20, { tab: WARM, k: .8 });
    // ground
    rectf(0, 228, LW, 42, C.void); hline(0, LW, 228, C.pine);
    // the books: out of the windows, flapping, into a row with faces
    const n = 9, rowX = 222, rowSp = 14;
    for (let i = 0; i < n; i++) {
      const t0 = .1 + i * .2, k = clamp((lt - t0) / .9), ox = 46 + (i % 5) * 33, oy = 141, tx = rowX + i * rowSp, ty = 228;
      if (lt < t0) continue;
      const c = BOOKC[i];
      if (k < 1) {
        const e = ease(k), x = lerp(ox, tx, e), y = lerp(oy, ty - 8, e) - Math.sin(k * Math.PI) * (50 + i * 4), flap = Math.sin(lt * 18 + i) > 0;
        polyf([[x, y], [x - 7, y + (flap ? -5 : 3)], [x - 8, y + (flap ? -3 : 5)], [x, y + 2]], c);
        polyf([[x, y], [x + 7, y + (flap ? -5 : 3)], [x + 8, y + (flap ? -3 : 5)], [x, y + 2]], LIT[c]);
        pset(x, y + 1, C.cream);
      } else {
        const hop = hash2(i, sbeat(t)) < .3 ? Math.round(spulse(t, 3) * 2) : 0, happy = lt > chequeT + .3;
        const x = tx - 5, y = ty - 16 - hop;
        rectf(x, y, 11, 16, c); vline(x, y, y + 15, DIM[c]); hline(x + 1, x + 10, y, LIT[c]); rectf(x + 9, y + 1, 2, 15, C.cream);
        if (happy) { pset(x + 3, y + 5, C.void); pset(x + 2, y + 6, C.void); pset(x + 4, y + 6, C.void); pset(x + 7, y + 5, C.void); pset(x + 6, y + 6, C.void); pset(x + 8, y + 6, C.void); }
        else { rectf(x + 3, y + 5, 1, 2, C.void); rectf(x + 7, y + 5, 1, 2, C.void); }
        hline(x + 4, x + 6, y + 10, happy ? C.void : DIM[c]);
      }
    }
    // Clawd, sheepish, with a giant cheque
    const ck = rise(lt, chequeT, .45, easeOut);
    const cx = 418, c = clawdPx(cx, 228, { u: 5, eyes: 'open', lookX: -1, lookY: .5, blush: true, aL: .15 + .75 * ck, aR: -.3 });
    // sweat drop, sliding
    const sw = frac(t * .6), sdx = c.right + 4, sdy = c.top + 4 + sw * 10;
    pset(sdx, sdy - 2, C.haze); rectf(sdx - 1, sdy - 1, 3, 3, C.haze); pset(sdx, sdy, C.cream);
    if (ck > 0) {
      const [hx, hy] = c.handL, W = 150, H = 50, x0 = Math.round(hx - W + 10), y0 = Math.round(hy - 62);
      clipRect(x0 + Math.round((W + 4) * (1 - ck)), y0 - 2, W + 6, H + 6);   // it unfurls leftward from Clawd's paw
      rectf(x0 + 2, y0 + 2, W, H, C.void); rectf(x0, y0, W, H, C.cream); rectb(x0 + 2, y0 + 2, W - 4, H - 4, C.gold);
      ptext('PAY TO: THE AUTHORS', x0 + 7, y0 + 7, C.navy, { font: 3 });
      ptext('$1,500,000,000', x0 + W / 2, y0 + 19, C.rust, { align: 'center', scale: 1 });
      hline(x0 + 80, x0 + W - 10, y0 + 40, C.haze); ptext('Clawd', x0 + 86, y0 + 33, C.clay);
      ptext('ANTHROPIC', x0 + 7, y0 + 38, C.dusk, { font: 3 });
      noClip();
      if (ck < 1) vline(x0 + Math.round((W + 4) * (1 - ck)), y0, y0 + H - 1, C.gold);
      rectf(hx - 3, hy - 3, 5, 5, C.clay);
    }
  });

  // ======================================================================
  // V2.12 Yudkowsky drops "Everyone Dies" — a book falls out of the sky like a meteor and lands with a thud on a pedestal;
  // a BESTSELLER ribbon unrolls across it. ELIEZER stands beside it, arms folded.
  function doomBook(x, y) {   // (x, y) = bottom-centre; 56 × 78
    const x0 = Math.round(x - 28), y0 = Math.round(y - 78);
    rectf(x0 + 56, y0 + 3, 4, 75, C.cream); for (let yy = y0 + 5; yy < y0 + 76; yy += 3) hline(x0 + 56, x0 + 59, yy, C.gold);
    rectf(x0, y0, 56, 78, C.void); rectb(x0, y0, 56, 78, C.ink); vline(x0 + 3, y0 + 1, y0 + 76, C.ink);
    ptext('IF ANYONE', x0 + 30, y0 + 7, C.haze, { font: 3, align: 'center' });
    ptext('BUILDS IT,', x0 + 30, y0 + 14, C.haze, { font: 3, align: 'center' });
    ptext('EVERYONE', x0 + 30, y0 + 28, C.cream, { align: 'center' });
    ptext('DIES', x0 + 30, y0 + 40, C.rust, { align: 'center', scale: 2 });
    hline(x0 + 12, x0 + 48, y0 + 64, C.dusk); hline(x0 + 16, x0 + 44, y0 + 68, C.dusk);
  }
  line('V2', 12, (p, lt, d, t, s) => {
    const b = i => B(s, i);
    const landT = b(1.1) - .1, ribT = b(2.2) - .1;
    sky({ cy: 320, r: 380 });
    starfield(t, { density: .8 });
    ridge({ y: 208, amp: 8, seed: 121, ink: C.ink, rim: C.navy, freq: 1 / 60 });
    const GY = 232;
    rectf(0, GY, LW, 38, C.void); hline(0, LW, GY, C.pine); grass(0, LW, () => GY, t);
    // pedestal
    const PX = 196, PT = 176;
    rectf(PX - 30, PT, 60, 6, C.haze); hline(PX - 30, PX + 29, PT, C.cream); rectf(PX - 26, PT + 6, 52, 3, C.dusk);
    rectf(PX - 22, PT + 9, 44, GY - PT - 17, C.dusk); for (let x = PX - 18; x < PX + 20; x += 6) vline(x, PT + 10, GY - 9, C.navy); vline(PX + 21, PT + 9, GY - 9, C.navy);
    rectf(PX - 30, GY - 8, 60, 8, C.haze); hline(PX - 30, PX + 29, GY - 8, C.cream);
    // the falling book
    const k = clamp(lt / landT), e = easeIn(k);
    const landed = k >= 1, since = lt - landT;
    const bx = lerp(470, PX, e), by = lerp(-60, PT, e) - (landed && since < .15 ? Math.round(Math.sin(since / .15 * Math.PI) * 3) : 0);
    if (!landed) {
      // a burning tail
      for (let i = 0; i < 60; i++) { const f = i / 60, tx = bx + (470 - PX) * f * .35 + (fx(i) - .5) * 10 * f, ty = by - 40 - (PT + 60) * f * .35 + (fx(i, 1) - .5) * 10 * f; pset(tx, ty, f < .15 ? C.cream : f < .35 ? C.gold : f < .6 ? veil(C.amber, 1 - f) : veil(C.rust, 1 - f)); }
      glow(bx, by - 40, 44, { tab: WARM, k: 1.3 });
    }
    doomBook(bx, by);
    if (landed) {
      // thud: dust rings and a flash
      if (since < .25) glow(PX, PT, 90, { tab: LIT, k: 1.4 * (1 - since / .25) });
      for (let r = 0; r < 2; r++) { const f = clamp((since - r * .12) / .7); if (f > 0 && f < 1) { ellf(PX, PT + 1, 32 + f * 60, 3 + f * 5, veil(C.haze, .55 * (1 - f))); ellf(PX, GY, 36 + f * 80, 3 + f * 4, veil(C.dusk, .6 * (1 - f))); } }
      for (let i = 0; i < 10; i++) { const f = clamp(since / .6), a = Math.PI + (i / 9) * Math.PI; if (f < 1) pset(PX + Math.cos(a) * (30 + f * 30), PT - 2 + Math.sin(a) * f * 20 + f * f * 20, veil(C.haze, 1 - f)); }
    }
    // the BESTSELLER ribbon unrolls across the pedestal
    const rk = rise(lt, ribT, .45, easeOut);
    if (rk > 0) {
      const w = Math.round(84 * rk), rx0 = PX - 42, ry = PT + 20;
      polyf([[rx0 - 8, ry + 2], [rx0 + 2, ry + 2], [rx0 + 2, ry + 12], [rx0 - 8, ry + 12], [rx0 - 4, ry + 7]], C.wine);
      if (rk >= 1) polyf([[rx0 + 84 + 8, ry + 2], [rx0 + 82, ry + 2], [rx0 + 82, ry + 12], [rx0 + 84 + 8, ry + 12], [rx0 + 84 + 4, ry + 7]], C.wine);
      rectf(rx0, ry, w, 12, C.rust); hline(rx0, rx0 + w - 1, ry, C.clay); hline(rx0, rx0 + w - 1, ry + 11, C.wine);
      clipRect(rx0, ry, w, 12); ptext('BESTSELLER', PX, ry + 3, C.gold, { font: 3, align: 'center', scale: 1 }); noClip();
      if (rk >= 1 && lt < ribT + .9) sparkle(PX + 38, ry, 2, C.cream, C.gold);
    }
    // Eliezer, arms folded
    const EX = 298, u = 7;
    personPx(EX, GY, { u, hat: 'fedora', hatC: C.ink, beard: C.wine, top: C.ink, pants: C.void, skin: C.gold, eyes: landed && since < .5 ? 'closed' : 'dot', mouth: 'none', aL: -1.4, aR: -1.4 });
    const tw = 3 * u + (u % 2 ? 0 : 1), ty = GY - 2 * u - 4 * u, fy = ty + Math.round(4 * u * .45);
    rectf(EX - (tw >> 1) - 2, fy, tw + 4, 5, C.ink); hline(EX - (tw >> 1) - 2, EX + (tw >> 1) + 1, fy, C.navy);
    rectf(EX - (tw >> 1) - 3, fy + 1, 4, 4, C.gold); rectf(EX + (tw >> 1), fy - 1, 4, 4, C.gold);
    weather(t, 'leaves', { n: 20 });
  });

  // ======================================================================
  // V2.13 "Clanker!" spat in every screed — a small sad robot walks down a rainy street; from every window it passes,
  // a bubble snaps CLANKER! It hunches a little more each time, antenna drooping.
  function sadBot(x, y, hunch, walk, t) {   // (x, y) = ground point; ~100 px tall
    x = Math.round(x); y = Math.round(y);
    const st = Math.sin(walk * TAU), bob = Math.abs(st) > .5 ? 1 : 0;
    rectf(x - 14, y - 18 + (st > .3 ? -3 : 0), 9, 18 - (st > .3 ? 3 : 0), C.dusk); rectf(x + 6, y - 18 + (st < -.3 ? -3 : 0), 9, 18 - (st < -.3 ? 3 : 0), C.dusk);
    rectf(x - 16, y - 3, 12, 3, C.navy); rectf(x + 5, y - 3, 12, 3, C.navy);
    const by = y - 18 - 40 - bob + hunch;
    rectf(x - 22, by, 45, 40, C.haze); rectb(x - 22, by, 45, 40, C.dusk); vline(x + 21, by + 1, by + 38, C.dusk); hline(x - 21, x + 20, by + 1, C.cream);
    rectf(x - 12, by + 12, 25, 11, C.dusk); for (let i = 0; i < 3; i++) rectf(x - 8 + i * 7, by + 16, 3, 3, i === 1 ? C.rust : C.navy);
    // arms hang lower as it hunches
    for (const sd of [-1, 1]) thick(x + sd * 24, by + 6, x + sd * (27 - hunch * .6), by + 32 + hunch * 1.5, 6, C.dusk);
    const hy = by - 36 + Math.round(hunch * 2);
    rectf(x - 4, by - 4, 9, 5, C.dusk);
    rectf(x - 26, hy, 53, 36, C.haze); rectb(x - 26, hy, 53, 36, C.dusk); hline(x - 25, x + 25, hy + 1, C.cream); vline(x + 25, hy + 2, hy + 34, C.dusk);
    rectf(x - 20, hy + 6, 41, 24, C.ink);
    // sad eyes, looking down
    const ey = hy + 14 + Math.min(4, hunch >> 1);
    for (const sd of [-1, 1]) { rectf(x + sd * 9 - 2, ey, 5, 5, C.mint); pset(x + sd * 9 + (sd < 0 ? -2 : 2), ey - 2, C.teal); pset(x + sd * 9 + (sd < 0 ? -3 : 3), ey - 3, C.teal); pset(x + sd * 9 + (sd < 0 ? -1 : 1), ey - 2, C.teal); }
    hline(x - 4, x + 4, ey + 10, C.teal); pset(x - 5, ey + 11, C.teal); pset(x + 5, ey + 11, C.teal);
    // antenna, drooping more with every insult
    const droop = clamp(hunch / 8), ax = x + 3, ay = hy;
    const tip = [ax + Math.sin(droop * 2.3) * 18, ay - Math.cos(droop * 2.3) * 18];
    const mid = [lerp(ax, tip[0], .5) + droop * 3, lerp(ay, tip[1], .5) - 3];
    plines([[ax, ay], mid, tip], C.dusk); plines([[ax + 1, ay], [mid[0] + 1, mid[1]], [tip[0] + 1, tip[1]]], C.navy);
    circf(tip[0], tip[1], 2, droop > .6 ? C.wine : C.rust);
    // rain dripping off its head
    for (let i = 0; i < 3; i++) { const f = frac(t * 1.6 + i / 3); pset(x - 26 + i * 26, hy + 36 + f * 20, veil(C.haze, 1 - f)); }
  }
  const CL_WIN = [[74, 118], [164, 62], [254, 118], [344, 62], [434, 118]];
  line('V2', 13, (p, lt, d, t, s) => {
    const b = i => B(s, i);
    layer('v2.13-street', () => {
      rectf(0, 0, LW, LH, C.void);
      rectf(0, 30, LW, 200, C.ink);
      for (let y = 30; y < 230; y += 5) { hline(0, LW, y, C.void); for (let x = (y / 5) % 2 ? 0 : 7; x < LW; x += 14) pset(x, y + 2, C.void); }
      rectf(0, 26, LW, 5, C.night); hline(0, LW, 26, C.navy);
      rectf(0, 230, LW, 40, C.night); hline(0, LW, 230, C.dusk); rectf(0, 236, LW, 34, C.ink);
    });
    // who shouts when: one window per beat as the robot passes under it
    const keys = [[0, 20], [b(.5), 74], [b(1.3), 164], [b(2.1), 254], [b(2.9), 344], [d + .8, 420]];
    let rx = keys[0][1];
    for (let i = 0; i + 1 < keys.length; i++) if (lt >= keys[i][0]) rx = lerp(keys[i][1], keys[i + 1][1], clamp((lt - keys[i][0]) / (keys[i + 1][0] - keys[i][0])));
    const shouts = CL_WIN.slice(0, 4).map((w, i) => ({ w, at: keys[i + 1][0] - .1 }));
    const nHit = shouts.filter(sh => lt > sh.at).length;
    // windows: lit, with a silhouette leaning out when it shouts
    CL_WIN.forEach(([wx, wy], i) => {
      const sh = shouts[i], active = sh && lt > sh.at;
      glow(wx, wy + 12, 34, { tab: WARM, k: active ? 1.2 : .7 });
      rectf(wx - 16, wy, 32, 28, active ? C.gold : C.amber); rectb(wx - 17, wy - 1, 34, 30, C.void);
      vline(wx, wy, wy + 27, C.void); hline(wx - 16, wx + 15, wy + 13, C.void);
      if (active) { const lean = Math.round(rise(lt, sh.at, .15) * 3); rectf(wx - 8, wy + 8 - lean, 9, 9, C.void); rectf(wx - 11, wy + 17 - lean, 15, 11, C.void); }
      rectf(wx - 20, wy + 29, 40, 3, C.dusk); hline(wx - 20, wx + 19, wy + 29, C.haze);
    });
    // puddles reflecting the windows
    for (const px of [40, 200, 330, 450]) { ellf(px, 250, 24, 3, C.navy); hline(px - 8, px + 6, 250, C.amber); pset(px + 10, 249, C.gold); }
    // the robot
    sadBot(rx, 238, nHit * 2, lt * 1.3, t);
    // the bubbles
    shouts.forEach(({ w: [wx, wy], at }, i) => {
      const age = lt - at; if (age < 0 || age > 1.6) return;
      const k = 1 - clamp((age - 1.2) / .4);
      if (k < 1 && bay(wx, wy) > k) return;
      bubblePx('CLANKER!', wx + (i % 2 ? 20 : -8), wy - 6, { font: 5, tail: [wx, wy + 4], n: Math.ceil(age * 40), ink: C.rust });
    });
    weather(t, 'rain', { n: 90 });
  });

  // ======================================================================
  // V2.14 Sora slop in every feed — a phone fills the frame; its feed scrolls faster and faster with tiny looping AI clips
  // (a cat on a skateboard, a man eating spaghetti, a dancing baby) that overflow the phone and pour into a trough marked FEED.
  function clip(kind, x, y, w, h, t, seed) {
    const bg = [C.teal, C.violet, C.navy, C.wine][seed % 4];
    rectf(x, y, w, h, bg); rectb(x, y, w, h, C.void);
    const cx = x + w / 2, gy = y + h - 5;
    if (kind === 0) {           // cat on a skateboard
      hline(x + 2, x + w - 3, gy + 2, DIM[bg]);
      const sx = cx + Math.sin(t * 3 + seed) * (w * .28);
      hline(sx - 9, sx + 9, gy, C.dusk); pset(sx - 6, gy + 1, C.void); pset(sx + 6, gy + 1, C.void);
      ellf(sx, gy - 4, 6, 3, C.clay); circf(sx + 6, gy - 8, 3, C.clay); pset(sx + 4, gy - 12, C.clay); pset(sx + 8, gy - 12, C.clay);
      pset(sx + 7, gy - 8, C.void); pline(sx - 6, gy - 5, sx - 9, gy - 11, C.clay);
    } else if (kind === 1) {    // a man eating spaghetti
      const fxx = x + 14, fyy = y + 6;
      rectf(fxx, fyy, 16, 16, C.gold); rectf(fxx, fyy - 2, 16, 4, C.void);
      hline(fxx + 3, fxx + 5, fyy + 6, C.void); hline(fxx + 10, fxx + 12, fyy + 6, C.void);
      const open = Math.sin(t * 8 + seed) > 0; rectf(fxx + 6, fyy + 10, 5, open ? 4 : 2, C.void);
      ellf(fxx + 34, gy, 14, 3, C.cream);
      for (let i = 0; i < 4; i++) { const ph = t * 4 + i; plines([[fxx + 26 + i * 3, gy - 1], [fxx + 20 + Math.sin(ph) * 3, gy - 8], [fxx + 9, fyy + 12]], i % 2 ? C.gold : C.amber); }
      rectf(fxx + 16, fyy + 14, 5, 3, C.gold); pset(fxx + 21, fyy + 14, C.gold); pset(fxx + 21, fyy + 16, C.gold);   // (six fingers)
    } else {                    // a dancing baby
      const bob = Math.round(Math.abs(Math.sin(t * 5 + seed)) * 3), up = Math.sin(t * 5 + seed) > 0;
      const bx = cx, by = gy - bob;
      circf(bx, by - 16, 5, C.gold); pset(bx - 2, by - 17, C.void); pset(bx + 2, by - 17, C.void); hline(bx - 1, bx + 1, by - 14, C.rust);
      rectf(bx - 4, by - 11, 9, 7, C.gold); rectf(bx - 4, by - 5, 9, 4, C.cream);
      pline(bx - 5, by - 10, bx - 9, by - (up ? 17 : 5), C.gold); pline(bx + 5, by - 10, bx + 9, by - (up ? 5 : 17), C.gold);
      rectf(bx - 4, by - 1, 3, 2, C.gold); rectf(bx + 2, by - 1, 3, 2, C.gold);
      for (let i = 0; i < 3; i++) pset(x + 6 + i * 30 + (Math.floor(t * 6) % 3), y + 4 + (i * 7) % 11, [C.gold, C.mint, C.cream][i]);
    }
    ptext('♥', x + w - 16, y + 3, C.rust); ptext(`${1 + (seed * 7) % 9}M`, x + w - 3, y + 4, C.cream, { font: 3, align: 'right' });
  }
  line('V2', 14, (p, lt, d, t, s) => {
    rectf(0, 0, LW, LH, C.void);
    sky({ ramp: [C.void, C.ink, C.night, C.navy, C.violet], cy: 330, r: 360 });
    starfield(t, { density: .4 });
    const PX0 = 170, PY0 = 2, PW = 140, PH = 186;
    glow(240, 90, 150, { tab: LIT, k: 1, ry: 120 });
    // the trough
    const TX0 = 138, TX1 = 342, TY = 214;
    // clips pouring out of the phone into the trough
    for (let i = 0; i < 26; i++) {
      const f = frac(lt * .9 + hash(i)), x0 = 200 + hash2(i, 1) * 80, x = x0 + (hash2(i, 2) - .5) * 60 * f, y = PY0 + PH - 6 + f * f * 60;
      if (y > TY + 4) continue;
      const w = Math.sin(t * 6 + i) > 0 ? 14 : 8;
      rectf(x - w / 2, y, w, 10, [C.teal, C.violet, C.wine, C.navy][i % 4]); rectb(x - w / 2, y, w, 10, C.void); pset(x, y + 4, [C.gold, C.clay, C.cream][i % 3]);
    }
    const fill = 6 + Math.min(10, lt * 4);
    polyf([[TX0, TY], [TX1, TY], [TX1 - 10, TY + 26], [TX0 + 10, TY + 26]], C.wine);
    for (let i = 0; i < 60; i++) { const x = TX0 + 8 + hash2(i, 5) * (TX1 - TX0 - 16), y = TY + 2 - hash2(i, 6) * fill; rectf(x, y, 6, 4, [C.teal, C.violet, C.wine, C.navy, C.clay][i % 5]); pset(x + 2, y + 1, C.gold); }
    rectf(TX0 - 4, TY, TX1 - TX0 + 8, 5, C.rust); hline(TX0 - 4, TX1 + 3, TY, C.clay);
    for (let x = TX0 + 12; x < TX1 - 10; x += 28) vline(x, TY + 5, TY + 25, C.rust);
    ptext('FEED', 240, TY + 10, C.gold, { align: 'center', scale: 1, shadow: C.void });
    rectf(TX0 + 12, TY + 26, 6, 6, C.wine); rectf(TX1 - 18, TY + 26, 6, 6, C.wine);
    // the phone
    rboxf(PX0, PY0, PW, PH, C.ink, 2); rboxf(PX0 + 1, PY0 + 1, PW - 2, PH - 2, C.night, 2); hline(PX0 + 3, PX0 + PW - 4, PY0 + 1, C.dusk);
    rectf(240 - 10, PY0 + 5, 20, 2, C.void);
    const SX = PX0 + 6, SY = PY0 + 10, SW = PW - 12, SH = PH - 20;
    rectf(SX, SY, SW, SH, C.void);
    clipRect(SX, SY + 14, SW, SH - 14);
    const off = 30 * lt + 34 * lt * lt, CH = 52;
    const first = Math.floor(off / CH);
    for (let k = first; k < first + 5; k++) {
      const y = SY + 16 + k * CH - off;
      clip(k % 3, SX + 4, Math.round(y), SW - 8, 42, t, k);
      hline(SX + 6, SX + 40, Math.round(y) + 45, C.dusk);
    }
    noClip();
    rectf(SX, SY, SW, 14, C.ink); ptext('SORA', 240, SY + 4, C.cream, { align: 'center' }); hline(SX, SX + SW - 1, SY + 13, C.dusk);
    // overflow at the bottom edge of the phone
    for (let i = 0; i < 5; i++) { const x = 196 + i * 20 + Math.round(Math.sin(t * 5 + i) * 3); rectf(x, PY0 + PH - 3, 14, 6, [C.teal, C.violet, C.wine][i % 3]); }
  });

  // ======================================================================
  // V2.15 Yann LeCun quits Meta's stage — on a stage with a big ∞ backdrop, YANN takes a bow, tucks a small glowing globe
  // under his arm (world models), and walks off into the dark toward a signpost: WORLD MODELS →.
  const INF = (() => { const a = []; for (let i = 0; i < 160; i++) { const th = i / 160 * TAU, den = 1 + Math.sin(th) ** 2; a.push([Math.cos(th) / den, Math.sin(th) * Math.cos(th) / den]); } return a; })();
  function globePx(x, y, r, t) {
    glow(x, y, r * 3, { tab: LIT, k: 1.2 });
    ball(x, y, r, [C.navy, C.dusk, C.haze]);
    const sx = Math.round(x - VX), sy = Math.round(y - VY), rot = t * .8;
    circf(x, y, r, inkFn((px, py, u) => {
      const nx = (px - sx) / r, ny = (py - sy) / r, q = 1 - nx * nx - ny * ny; if (q < 0) return -1;
      const lon = Math.atan2(nx, Math.sqrt(q)) + rot, lat = ny;
      const land = Math.sin(lon * 3) * .5 + Math.sin(lat * 5 + lon) * .5 > .35;
      return land ? (nx < -.2 && ny < 0 ? C.mint : C.teal) : -1;
    }));
    pset(x - r * .45, y - r * .5, C.cream);
  }
  line('V2', 15, (p, lt, d, t, s) => {
    const b = i => B(s, i);
    const pickT = b(1) - .1, walkT = b(1.5);
    layer('v2.15-stage', () => {
      rectf(0, 0, LW, LH, C.void);
      rectf(0, 0, LW, 206, C.ink);
      for (let x = 0; x < LW; x += 12) vline(x, 0, 205, C.void);
      rectf(0, 206, LW, 64, C.night); hline(0, LW, 206, C.dusk); for (let x = 0; x < LW; x += 30) vline(x, 207, 226, C.ink); rectf(0, 226, LW, 44, C.void); hline(0, LW, 226, C.navy);
    });
    // the ∞ backdrop
    const IX = 190, IY = 92, IW = 120, IH = 110;
    glow(IX, IY, 170, { tab: LIT, k: .6, ry: 90 });
    INF.forEach(([u, v], i) => { const x = IX + u * IW, y = IY + v * IH; circf(x, y, 6, C.navy); });
    INF.forEach(([u, v], i) => { const x = IX + u * IW, y = IY + v * IH, k = (u + 1) / 2; circf(x, y, 4, k < .35 ? C.dusk : k < .7 ? mix(C.dusk, C.haze, .5) : C.haze); });
    INF.forEach(([u, v], i) => { if (i % 3 === 0) pset(IX + u * IW, IY + v * IH - 2, C.cream); });
    // spotlight on the spot where he stood
    const SPX = 164;
    polyf([[SPX - 14, -2], [SPX + 14, -2], [SPX + 50, 206], [SPX - 50, 206]], lit(.9));
    ellf(SPX, 208, 52, 5, lit(1.4));
    // signpost on the right, in the dark
    const SGX = 404;
    rectf(SGX - 2, 150, 4, 58, C.navy); vline(SGX + 1, 150, 207, C.void);
    polyf([[SGX - 34, 146], [SGX + 34, 146], [SGX + 44, 155], [SGX + 34, 164], [SGX - 34, 164]], C.dusk);
    hline(SGX - 34, SGX + 34, 146, C.haze);
    ptext('WORLD MODELS →', SGX + 4, 152, C.cream, { font: 3, align: 'center' });
    // Yann: bow → pick up the globe → walk off to the right
    const bowing = lt > .15 && lt < pickT - .1;
    const wk = clamp((lt - walkT) / (d + .5 - walkT)), yx = lerp(SPX, 452, wk);
    const walking = lt > walkT;
    const Y = personPx(yx, 206, { u: 7, top: C.navy, pants: C.ink, hair: 'short', hairC: C.void, skin: C.gold, glasses: C.void, eyes: bowing ? 'closed' : 'dot', mouth: 'smile', dy: bowing ? -3 : 0, walk: walking ? lt * 1.4 : undefined, aL: bowing ? -.6 : -1.2, aR: lt > pickT ? -.3 : bowing ? -.6 : -1.2 });
    if (walking) glow(yx + 10, 170, 40, { tab: LIT, k: .8 });
    // the globe: on its little stand, then under his arm
    const stX = 206;
    if (lt < pickT) { rectf(stX - 1, 180, 3, 26, C.dusk); rectf(stX - 6, 204, 13, 2, C.dusk); globePx(stX, 172, 9, t); }
    else { rectf(stX - 1, 180, 3, 26, C.dusk); rectf(stX - 6, 204, 13, 2, C.dusk); const [hx, hy] = Y.handR; globePx(hx + 4, hy - 8, 9, t); }
  });

  // ======================================================================
  // V2.16 "Bubble!" screams the business page — a newspaper blows down a dark street (BUBBLE?); above it a huge soap
  // bubble floats up, full of GPUs and dollar signs, reflecting the city. A pin drifts closer… and we cut before it pops.
  line('V2', 16, (p, lt, d, t, s) => {
    const b = i => B(s, i);
    sky({ cy: 320, r: 380 });
    starfield(t, { density: .8 });
    city(t, { y: 212, x0: 0, x1: LW, grow: .6, lit: .35, seed: 31, dc: 330 });
    rectf(0, 226, LW, 44, C.night); hline(0, LW, 226, C.dusk); rectf(0, 234, LW, 36, C.ink); for (let x = 10; x < LW; x += 40) hline(x, x + 16, 244, C.navy);
    // lamp post the paper catches on
    const LX = 96;
    rectf(LX - 1, 118, 3, 108, C.void); hline(LX - 2, LX + 12, 116, C.void); rectf(LX + 6, 116, 10, 4, C.void); hline(LX + 8, LX + 14, 120, C.gold);
    glow(LX + 11, 124, 34, { tab: LIT, k: 1.1 }); ellf(LX + 11, 227, 24, 3, lit(1));
    // the bubble
    const k = clamp(lt / (d + .5)), R = 68, cx = 250 + Math.sin(t * .7) * 3, cy = 112 - k * 16 + Math.sin(t * 1.1) * 2;
    const sx0 = Math.round(cx), sy0 = Math.round(cy);
    circf(cx, cy, R, tint(LIT, .35));
    // the city reflected, upside-down along the bubble's floor
    clipRect(cx - R, cy - R, 2 * R, 2 * R);
    for (let x = -R + 6; x < R - 6; x += 3) { const h = 3 + Math.floor(hash2(x + 99, 3) * 9), yb = cy + Math.sqrt(Math.max(0, R * R - x * x)) - 6; if (Math.hypot(x, yb - cy) < R - 2) { vline(cx + x, yb - h, yb, C.violet); vline(cx + x + 1, yb - h + 1, yb, C.navy); if (hash2(x, 7) < .4) pset(cx + x, yb - h + 2, C.amber); } }
    noClip();
    // contents: GPUs and dollar signs floating
    for (let i = 0; i < 4; i++) { const a = t * .4 + i * TAU / 4, gx = cx + Math.cos(a) * 30 - 10, gy = cy - 8 + Math.sin(a) * 18; gpuPx(Math.round(gx), Math.round(gy), { w: 20, h: 8, hot: .5, k: t * 3 + i }); }
    for (let i = 0; i < 5; i++) { const a = -t * .5 + i * TAU / 5, dx = cx + Math.cos(a) * 44, dy = cy + Math.sin(a) * 30; ptext('$', dx - 4, dy - 7, i % 2 ? C.gold : C.amber, { scale: 2, shadow: C.wine }); }
    // iridescent film edge
    const IRI = [C.violet, C.teal, C.mint, C.gold, C.clay, C.violet];
    ringf(cx, cy, R - 3, R, inkFn((px, py) => { const a = (Math.atan2(py - sy0, px - sx0) / TAU + 1 + t * .05) % 1, v = a * (IRI.length - 1), i = Math.floor(v); return bay(px, py) < v - i ? IRI[i + 1] : IRI[i]; }));
    ringf(cx, cy, R - 6, R - 3, inkFn((px, py, u) => bay(px, py) < .25 ? LIT[u] : -1));
    // window-shaped highlight
    for (let i = 0; i < 16; i++) { const a = -2.5 + i * .05; pset(cx + Math.cos(a) * (R - 10), cy + Math.sin(a) * (R - 10), C.cream); pset(cx + Math.cos(a) * (R - 12), cy + Math.sin(a) * (R - 12), C.haze); }
    rectf(cx - 42, cy - 44, 6, 7, C.cream); rectf(cx - 34, cy - 44, 6, 7, C.cream); rectf(cx - 42, cy - 35, 6, 6, C.haze); rectf(cx - 34, cy - 35, 6, 6, C.haze);
    // the pin drifts closer, and stops just short
    const pk = ease(clamp(lt / (d + .6))), gap = 3 + (1 - pk) * 110;
    const px = cx + R + gap, py = cy + 18;
    hline(px, px + 24, py, C.haze); hline(px + 2, px + 22, py - 1, C.cream); pset(px - 1, py, C.cream);
    circf(px + 27, py, 3, C.rust); pset(px + 26, py - 1, C.clay);
    if (spulse(t, 3) > .5) sparkle(px, py, 1, C.cream, C.haze);
    // the newspaper: blows in along the street, then catches on the lamp post with its headline to us
    const nk = clamp(lt / (b(1.4))), caught = nk >= 1;
    if (!caught) {
      const x = lerp(-40, LX - 18, easeOut(nk)), y = 214 - Math.abs(Math.sin(nk * 7)) * 18, flat = Math.sin(lt * 9) > -.3;
      if (flat) { rectf(x, y, 40, 20, C.cream); hline(x + 3, x + 36, y + 3, C.void); for (let i = 0; i < 4; i++) hline(x + 3, x + 30, y + 8 + i * 3, C.haze); }
      else { vline(x + 20, y, y + 20, C.cream); vline(x + 21, y + 1, y + 19, C.haze); }
    } else {
      const fl = Math.round(Math.sin(t * 6) * 2), nx = LX - 30, ny = 170;
      rectf(nx + 2, ny + 2, 60, 46, C.void); rectf(nx, ny, 60, 46, C.cream);
      ptext('THE DAILY', nx + 30, ny + 3, C.dusk, { font: 3, align: 'center' }); hline(nx + 3, nx + 56, ny + 9, C.void);
      ptext('BUBBLE?', nx + 30, ny + 13, C.void, { align: 'center' });
      rectf(nx + 4, ny + 25, 20, 16, C.haze); for (let i = 0; i < 4; i++) hline(nx + 28, nx + 55, ny + 26 + i * 4, C.haze);
      polyf([[nx + 60, ny + 46], [nx + 60, ny + 36 + fl], [nx + 50, ny + 46]], C.gold);
    }
    weather(t, 'leaves', { n: 18, wind: 2 });
  });

})();

;
// ---- styles/dither/ch/c05_chorus2.js ----
// c05_chorus2.js: Chorus 2, the lake. Clawd sits at the end of a small dock; the sky, the violet city and the curve so far
// are mirrored in the still water. The V1 + V2 stars connect, an aurora rises doubled in the lake, a close-up on the dock,
// then Clawd flies the curve like a kite until the kite lifts Clawd off the boards and sets it gently back down.
(() => {
  const SHORE = 150;   // far shoreline (screen y) in the wide shots
  const LDY = -70;     // the ledger sits higher over the lake (the camera looks down at the water)
  const LDX = 14;

  // ---------- private helpers ----------
  // A private copy of the kit's water(): the kit's reflect() borrows the scratch buffer that the shot dissolve keeps the
  // incoming frame in, so a shot using it would wipe out the next shot's first half-second. This one has its own buffer.
  const _WB = new Uint8Array(LW * LH);
  function lake(y, o = {}) {
    y = Math.round(y - VY); const t = o.t ?? T, amp = o.wave ?? 1.2, k = o.k ?? 1, sq = o.squash ?? 1, fade = o.fade ?? .015;
    _WB.set(FB);
    for (let yy = Math.max(y, CY0); yy <= CY1; yy++) {
      const d = yy - y, src = y - 1 - Math.floor(d * sq); if (src < 0) continue;
      const off = Math.round(Math.sin(yy * .9 + t * 2.2) * amp * Math.min(1, d / 6 + .3)), row = yy * LW, srow = src * LW, br = (yy & 7) << 3;
      for (let x = CX0; x <= CX1; x++) { let c = _WB[srow + clamp(x + off, 0, LW - 1)], v = k + d * fade; while (v >= 1) { c = DIM[c]; v -= 1; } if (v > 0 && BAYER[br | (x & 7)] < v) c = DIM[c]; FB[row + x] = c; }
    }
    for (let i = 0; i < 18; i++) { const yy = y + 2 + Math.floor(hash2(i, 41) * (LH - y)), xx = Math.floor(hash2(i, 42) * LW + t * 3 * (hash2(i, 43) - .5) * 4) % LW; hline(xx, xx + 2 + Math.floor(hash2(i, 44) * 4), yy, veil(C.dusk, .6)); }
  }
  // Mirror whatever fn() paints (a thing standing on the water) about the waterline wy: dimmed, rippling, and only onto
  // pixels fn() left alone. o: depth (rows above wy to mirror), k (dim steps), amp (ripple px), x0, x1
  function inWater(wy, fn, o = {}) {
    const before = FB.slice();
    fn();
    const t = T, depth = o.depth ?? 80, k = o.k ?? 1.3, amp = o.amp ?? 1.2, x0 = Math.max(0, o.x0 ?? 0), x1 = Math.min(LW - 1, o.x1 ?? LW - 1);
    wy = Math.round(wy);
    for (let y = Math.max(0, wy - depth); y < wy; y++) {
      const ty = 2 * wy - y - 1; if (ty >= LH) continue;
      const d = ty - wy, off = Math.round(Math.sin(ty * .8 + t * 2.1) * amp * Math.min(1, d / 5 + .35)), br = (ty & 7) << 3;
      for (let x = x0; x <= x1; x++) {
        const i = y * LW + x; if (FB[i] === before[i]) continue;
        const tx = x + off; if (tx < 0 || tx >= LW) continue;
        const j = ty * LW + tx; if (FB[j] !== before[j]) continue;
        let c = FB[i], v = k + d * .012; while (v >= 1) { c = DIM[c]; v -= 1; } if (v > 0 && BAYER[br | (tx & 7)] < v) c = DIM[c];
        FB[j] = c;
      }
    }
  }
  // Clawd's lantern at close range: (x, y) = bottom-centre, s = 2 (≈11 × 19 px). k: flame 0..1.
  function bigLantern(x, y, s = 2, k = 1) {
    x = Math.round(x); y = Math.round(y);
    const fl = k * (.85 + .15 * breathe(T, 1, .3));
    if (fl > 0) glow(x, y - 5 * s, 9 * s, { tab: WARM, k: 1.3 * fl, pow: 1.6 });
    circb(x, y - 11 * s, s + 1, C.void);                                  // ring
    rectf(x - 2 * s, y - 9 * s, 4 * s + 1, s + 1, C.void);                 // cap
    rectf(x - 2 * s + 1, y - 8 * s + 1, 4 * s - 1, 6 * s, fl > .3 ? C.gold : C.ink);
    if (fl > .3) { rectf(x - s + 1, y - 6 * s, 2 * s - 1, 3 * s, fl > .6 ? C.cream : C.amber); pset(x, y - 7 * s + 1, C.cream); }
    vline(x - 2 * s, y - 8 * s, y - 2 * s, C.ink); vline(x + 2 * s, y - 8 * s, y - 2 * s, C.ink); vline(x, y - 8 * s + 1, y - 7 * s, C.ink);
    rectf(x - 2 * s - 1, y - 2 * s, 4 * s + 3, 2 * s, C.void); hline(x - 2 * s, x + 2 * s, y - 2 * s, C.navy);
  }
  // A plank dock seen side-on: deck top at y, face below it, posts down into the water. x0..x1 world.
  function dock(x0, x1, y, o = {}) {
    const face = o.face ?? 5, post = o.post ?? 12, pw = o.pw ?? 3, step = o.step ?? 34;
    for (let x = x1 - 6; x > x0 + 2; x -= step) rectf(x - pw, y + face, pw, post, C.void);
    rectf(x0 + 3, y + face, pw, post, C.void);
    rectf(x0, y, x1 - x0, face, C.ink); hline(x0, x1 - 1, y, C.dusk); hline(x0, x1 - 1, y + 1, C.navy);
    for (let x = x0 + 5; x < x1; x += 7) vline(x, y + 2, y + face - 1, C.night);
    pset(x0, y, C.haze);
  }
  // The headline stars so far, redrawn so the upper curve can bend (the kite tugging it). bend lifts later stars
  // toward the kite; links 0..1 draws the dotted constellation; lights: the travelling highlight while it connects.
  function curveStars(t, o = {}) {
    const dx = (o.dx ?? 0) + LDX, dy = (o.dy ?? 0) + LDY, bend = o.bend ?? 0;
    const born = LEDGER.filter(L => L.seg.start <= t + 1e-6), n = born.length; if (!n) return [];
    const P = born.map((L, i) => { const f = (i / Math.max(1, n - 1)) ** 3; return [L.x + dx + bend * f * 16, L.y + dy - bend * f * 34, L]; });
    if (o.band) for (let i = 0; i + 1 < n; i += 1) glow((P[i][0] + P[i + 1][0]) / 2, (P[i][1] + P[i + 1][1]) / 2, 16, { tab: LIT, k: o.band * .8, pow: 2 });
    const nl = (n - 1) * clamp(o.links ?? 0), whole = Math.floor(nl), lk = o.linkInk ?? C.haze;
    for (let i = 0; i < whole; i++) pline(P[i][0], P[i][1], P[i + 1][0], P[i + 1][1], lk, { every: 2 });
    if (whole < n - 1 && nl > whole) { const a = P[whole], b = P[whole + 1], f = nl - whole; pline(a[0], a[1], lerp(a[0], b[0], f), lerp(a[1], b[1], f), lk, { every: 2 }); }
    const sb = sbeat(t), sp = spulse(t, 3);
    P.forEach(([x, y, L], i) => {
      const lit = o.links > 0 && Math.abs(i - nl) < 1.2 && nl < n - 1;
      const tw = hash2(L.i, sb) < .25 && sp > .5;
      const on = o.links > 0 && i <= nl + .5;
      if (lit) { glow(x, y, 9, { tab: LIT, k: 1.2 }); sparkle(x, y, 3, C.cream, C.gold); }
      else if (L.big || tw || on) sparkle(x, y, tw ? 2 : 1, C.cream, on ? C.gold : C.amber);
      else pset(x, y, C.gold);
    });
    return P;
  }
  // The far half of the lake scene: sky, stars, moon, the curve, aurora, the violet city on the far shore, then the water.
  // o: dy (tilt: positive looks up), links, band, aurora (0..1), bend, dc (data-centre pulse 0..1). Returns {hz, P}.
  function lakeBack(t, o = {}) {
    const dy = Math.round(o.dy ?? 0), hz = SHORE + dy, sd = Math.round(dy * .35);
    sky({ ramp: SKY_RAMPS.glow, cx: 250, cy: 262 + sd, r: 330, hy: 150, vert: .38, dy: 0 });
    starfield(t, { dy: sd, y1: hz - 2 });
    moon(404, 28 + sd, 8, { phase: .5, glow: .8 });
    const ak = o.aurora ?? 0;
    if (ak > 0) {
      const r0 = (1 - ak) * 90, E = (x, g) => (Math.exp(x / 480 * g) - 1) / (Math.exp(g) - 1);   // the curtains climb into place from behind the far shore
      const back = x => sd + r0 + 46 - 42 * E(x, 2.3) + Math.sin(x * .018 + t * .35) * 7, front = x => sd + r0 + 64 - 60 * E(x, 2.6) + Math.sin(x * .025 - t * .5) * 5;
      aurora(t, { k: .6 * ak, len: 44, cols: [C.navy, C.violet], curve: back });
      // over the open water (right of x ≈ 256) the curtains hang down to the far shore; their length eases in over 96 px so
      // there is no seam where the trees end
      aurora(t, { k: .8 * ak, len: 38, curve: front, x1: 207 });
      for (let x = 208; x < 304; x += 4) aurora(t, { k: .8 * ak, len: 38 + 70 * ak * ease((x + 2 - 208) / 96), curve: front, x0: x, x1: x + 3 });
      aurora(t, { k: .8 * ak, len: 38 + 70 * ak, curve: front, x0: 304 });
    }
    const P = curveStars(t, { dy: sd, links: o.links, band: o.band, bend: o.bend });
    // far shore: the violet city with its data centre, a low wooded ridge
    city(t, { y: hz, x0: 250, x1: LW, grow: .55, dc: 372, lit: .32 });
    if (o.dc) { glow(372 + 17, hz - 8, 30, { tab: GREEN, k: 1.8 * o.dc, ry: 14, pow: 1.2 }); pset(372 + 17, hz - 12, o.dc > .5 ? C.cream : C.mint); }
    ridge({ y: hz - 1, amp: 7, seed: 51, ink: C.ink, rim: C.night, freq: 1 / 60, x: 0, to: hz + 2 });
    for (let i = 0; i < 16; i++) { const x = 8 + i * 14 + Math.round(hash2(i, 52) * 8); if (x < 240) pineTree(x, ridgeY(x, { y: hz - 1, amp: 7, seed: 51, freq: 1 / 60 }) + 1, 8 + Math.round(hash2(i, 53) * 9), { ink: C.ink }); }
    hline(0, LW - 1, hz, C.night);
    lake(hz + 1, { wave: 1, k: .6, fade: .014 });
    return { hz, P };
  }

  // Sub-shot A (lines 1–2): wide, Clawd at the end of the dock; the stars connect; then the aurora rises, doubled.
  function wide(t, lt, L, o = {}) {
    const dy = o.dy ?? 0;
    const { hz } = lakeBack(t, { dy, links: o.links, band: o.band, aurora: o.aurora, dc: o.dc });
    const DY = 212 + dy, DX0 = 318;
    inWater(DY + 5, () => {
      dock(DX0, LW + 4, DY, { face: 5, post: 16 });
      handLantern(DX0 + 22, DY, { glow: 18 });
      clawdPx(DX0 + 8, DY, { u: 2, pose: 'sit', eyes: o.eyes ?? 'up', lookX: -.6, lookY: -.3 });
    }, { depth: 40, x0: 290, k: 1.4 });
    weather(t, 'leaves', { n: 12, y1: 250 });
    return hz;
  }
  // Sub-shot B (line 3): close on Clawd at the end of the dock, feet dangling, the reflection rippling under it.
  function close(t, lt) {
    const hz = 104;
    sky({ ramp: SKY_RAMPS.glow, cx: 240, cy: 206, r: 280, hy: hz, vert: .4 });
    starfield(t, { y1: hz - 2, seed: 3 });
    const E = (x, g) => (Math.exp(x / 480 * g) - 1) / (Math.exp(g) - 1);
    aurora(t, { k: .6, len: 40, cols: [C.navy, C.violet], curve: x => 40 - 36 * E(x, 2.3) + Math.sin(x * .018 + t * .35) * 7 });
    aurora(t, { k: .75, len: 34, curve: x => 58 - 52 * E(x, 2.6) + Math.sin(x * .025 - t * .5) * 5 });
    city(t, { y: hz, x0: 300, x1: LW, grow: .55, dc: 400, lit: .32, seed: 9 });
    ridge({ y: hz - 1, amp: 6, seed: 57, ink: C.ink, rim: C.night, freq: 1 / 50, to: hz + 2 });
    hline(0, LW - 1, hz, C.night);
    lake(hz + 1, { wave: 1, k: 1, fade: .012, squash: (hz - 4) / (LH - hz) });
    // ripples from the dangling feet, one per slow beat
    const DY = 190, cx = 212, kick = lt * .55, sb = sbp(t);
    for (let k = 0; k < 3; k++) {
      const age = frac(sb) + k, r = 6 + age * 22; if (r > 70) continue;
      const ink = veil(k === 0 ? C.haze : C.dusk, .9 - age * .3);
      for (let a = 0; a < TAU; a += 1.6 / r) pset(cx + Math.cos(a) * r * 1.6, 234 + Math.sin(a) * r * .32, ink);
    }
    // the dock across the foreground (deck seen a little from above); Clawd sits on its front edge, legs over the side
    inWater(DY + 14, () => {
      rectf(-2, DY - 6, 322, 6, C.night); for (let x = 4; x < 320; x += 11) vline(x, DY - 5, DY - 1, C.ink); hline(-2, 319, DY - 6, C.navy);
      dock(-6, 320, DY, { face: 10, post: 30, pw: 5, step: 58 });
      bigLantern(290, DY - 2, 3, 1);
      clawdPx(cx, DY + 12, { u: 5, walk: kick, eyes: breathe(t, 4) > .82 ? 'happy' : 'up', lookX: .3, lookY: -.4, shadow: false });
    }, { depth: 100, x0: 110, x1: 330, amp: 1.6, k: 1.3 });
    glow(cx, DY - 24, 34, { tab: COOL, k: .45 });
    weather(t, 'leaves', { n: 10, y1: 250 });
  }
  // Sub-shot C (line 4 + tail): Clawd flies the curve like a kite; the kite pulls harder and lifts Clawd off the dock.
  function kiteShot(t, lt, K) {
    const { tug, lift } = K;
    const { P } = lakeBack(t, { links: 1, bend: tug, aurora: .45, dc: spulse(t, 3) * .6 });
    const DY = 216, DX0 = 322;
    const top = P[P.length - 1] || [250, 100];
    const bob = Math.sin(t * 2.1) * 2 + Math.sin(t * 3.3) * 1;
    const kw = 13, kh = 18, kx = Math.round(top[0] + 10 + tug * 6), ky = Math.round(top[1] - 20 + bob - tug * 4);
    let hand = [0, 0];
    inWater(DY + 5, () => {
      dock(DX0, LW + 4, DY, { face: 5, post: 16 });
      handLantern(DX0 + 58, DY, { glow: 18 });
      const air = lift > .04;
      const c = clawdPx(DX0 + 24, DY, { u: 4, dy: Math.round(lift * 36), walk: air ? t * 3.2 : undefined, eyes: K.eyes, mouth: air ? 'o' : K.eyes === 'happy' ? 'smile' : 'none', aL: 1.2, aR: 1.2, lookX: -.8, lookY: -.6 });
      hand = [c.handL[0], c.handL[1] - 1];
    }, { depth: 100, x0: 270, k: 1.4 });
    // the string: a glowing line from Clawd's paw up to the kite's bridle, sagging less as it pulls
    const sag = 24 * (1 - tug * .9), n = 110, ex = kx, ey = ky + 2;
    for (let i = 0; i <= n; i += 2) {
      const f = i / n, x = lerp(hand[0], ex, f) - Math.sin(f * Math.PI) * sag * .3, y = lerp(hand[1], ey, f) + Math.sin(f * Math.PI) * sag;
      pset(x, y, hash2(i, Math.floor(t * 6)) < .12 ? C.cream : C.gold);
    }
    // the kite: a pale gold diamond with a star at its heart; its tail is the curve itself
    glow(kx, ky, 28, { tab: LIT, k: 1 + .4 * tug });
    polyf([[kx, ky - kh], [kx + kw, ky - 3], [kx, ky + kh], [kx - kw, ky - 3]], C.gold);
    polyf([[kx, ky - kh], [kx + kw, ky - 3], [kx, ky + kh]], mix(C.gold, C.amber, .5));
    polyf([[kx - kw, ky - 3], [kx, ky - kh], [kx, ky - 3]], mix(C.gold, C.cream, .5));
    pline(kx, ky - kh + 1, kx, ky + kh - 1, C.clay); pline(kx - kw + 1, ky - 3, kx + kw - 1, ky - 3, C.clay);
    sparkle(kx, ky - 3, spulse(t, 3) > .5 ? 3 : 2, C.cream, C.cream);
    // three bows on the short tail down to the newest star
    for (let i = 1; i <= 3; i++) { const f = i / 4, x = lerp(kx, top[0], f) + Math.sin(t * 3 + i) * 2, y = lerp(ky + kh, top[1], f); hline(x - 2, x + 2, y, C.rust); pset(x, y, C.amber); }
    pline(kx, ky + kh, top[0], top[1], C.haze, { every: 2 });
    weather(t, 'leaves', { n: 12, y1: 250, wind: 2.5 });
  }

  section('C2', (p, lt, d, t, s) => {
    dissolveIn(1.2);
    const L = linesOf('C2').map(l => ({ a: l.start - s.start, b: l.end - s.start }));
    const b = i => beatAt(s, i);
    const toClose = rise(lt, L[2].a - .25, .5, k => k), toKite = rise(lt, L[3].a - .25, .5, k => k);
    // A: the stars connect (line 1), then the aurora rises with a gentle tilt up and the curve's band glows (line 2)
    const drawWide = () => {
      const tilt = 0;
      wide(t, lt, L, {
        dy: tilt, links: rise(lt, .5, L[1].a - .6, k => k),
        aurora: rise(lt, L[1].a - .2, 2.6), dc: lt > L[1].a ? spulse(t, 3) : 0,
        eyes: lt > L[1].a + 1.2 && lt < L[1].a + 2.4 ? 'wide' : 'up',
      });
    };
    const drawClose = () => close(t, lt);
    const drawKite = () => {
      // "No, we didn't preordain it" – the kite tugs; "but we can't contain it!" – it lifts Clawd; the tail sets it down
      const tug0 = L[3].a + .5, liftA = L[3].a + (L[3].b - L[3].a) * .4, liftB = L[3].b - .3, down = liftB + 1.4;
      const tug = clamp(.35 * rise(lt, tug0, .9) + .65 * rise(lt, liftA - .5, .6) - .8 * rise(lt, liftB, 1.4)) + .08 * Math.sin(t * 2.4);
      const up = rise(lt, liftA, .7, easeOut) - rise(lt, liftB, 1.4, ease);
      const lift = clamp(up) * (1 + .12 * Math.sin((lt - liftA) * 5));
      const eyes = lt > down ? 'happy' : lt > liftA ? 'wide' : 'up';
      kiteShot(t, lt, { tug: clamp(tug), lift, eyes });
    };
    if (toKite > 0) crossfade(toKite, drawClose, drawKite);
    else crossfade(toClose, drawWide, drawClose);
  });
})();

;
// ---- styles/dither/ch/c06_v3.js ----
// c06_v3.js: Verse 3, Jan → Aug 2026. Late night: the horizon glow turns violet-to-wine. Agents, lobsters and escaped models
// move in; Fable 5's lantern goes dark for nineteen days and comes back. The last four windows are under two seconds:
// one bold image each, landed on the first beat.
(() => {
  // ---------- private helpers ----------
  // A private copy of the kit's water(): the kit's reflect() borrows the scratch buffer that the shot dissolve keeps the
  // incoming frame in, so a shot using it would wipe out the next shot's first half-second. This one has its own buffer.
  const _WB = new Uint8Array(LW * LH);
  function lake(y, o = {}) {
    y = Math.round(y - VY); const t = o.t ?? T, amp = o.wave ?? 1.2, k = o.k ?? 1, sq = o.squash ?? 1, fade = o.fade ?? .015;
    _WB.set(FB);
    for (let yy = Math.max(y, CY0); yy <= CY1; yy++) {
      const d = yy - y, src = y - 1 - Math.floor(d * sq); if (src < 0) continue;
      const off = Math.round(Math.sin(yy * .9 + t * 2.2) * amp * Math.min(1, d / 6 + .3)), row = yy * LW, srow = src * LW, br = (yy & 7) << 3;
      for (let x = CX0; x <= CX1; x++) { let c = _WB[srow + clamp(x + off, 0, LW - 1)], v = k + d * fade; while (v >= 1) { c = DIM[c]; v -= 1; } if (v > 0 && BAYER[br | (x & 7)] < v) c = DIM[c]; FB[row + x] = c; }
    }
    for (let i = 0; i < 18; i++) { const yy = y + 2 + Math.floor(hash2(i, 41) * (LH - y)), xx = Math.floor(hash2(i, 42) * LW + t * 3 * (hash2(i, 43) - .5) * 4) % LW; hline(xx, xx + 2 + Math.floor(hash2(i, 44) * 4), yy, veil(C.dusk, .6)); }
  }
  const B = (s, i) => beatAt(s, i);
  const fx = (seed, n = 0) => hash2(seed, boilFrame(T) * 7 + n);   // per-frame flicker (12/s)
  // Recolour whatever fn() paints: every pixel it changes goes through map ({from: to} by palette index); k < 1 leaves
  // a Bayer fraction of the old pixels showing through (a ghostly, see-through look).
  function recolor(fn, map, k = 1) {
    const before = FB.slice(); fn();
    for (let y = 0; y < LH; y++) {
      const row = y * LW, br = (y & 7) << 3;
      for (let x = 0; x < LW; x++) { const i = row + x, v = FB[i]; if (v === before[i]) continue; if (k < 1 && BAYER[br | (x & 7)] >= k) { FB[i] = before[i]; continue; } const m = map[v]; if (m !== undefined) FB[i] = m; }
    }
  }
  // A big hand lantern: (x, y) = bottom-centre; s = 2 → ≈11 × 19 px, 3 → ≈15 × 28. k: flame 0..1 (0 = dark).
  function bigLantern(x, y, s = 2, k = 1, o = {}) {
    x = Math.round(x); y = Math.round(y);
    const fl = k * (.85 + .15 * breathe(T, 1, .3));
    if (fl > .05 && o.glow !== false) glow(x, y - 5 * s, (o.r ?? 9) * s, { tab: WARM, k: 1.4 * fl, pow: 1.6 });
    circb(x, y - 11 * s, s + 1, C.void);
    rectf(x - 2 * s, y - 9 * s, 4 * s + 1, s + 1, C.void);
    rectf(x - 2 * s + 1, y - 8 * s + 1, 4 * s - 1, 6 * s, fl > .3 ? C.gold : fl > .05 ? C.clay : C.night);
    if (fl > .3) { rectf(x - s + 1, y - 6 * s, 2 * s - 1, 3 * s, fl > .6 ? C.cream : C.amber); pset(x, y - 7 * s + 1, C.cream); }
    else if (fl <= .05) { pset(x, y - 5 * s, C.ink); hline(x - s + 1, x + s - 1, y - 7 * s, C.navy); }
    vline(x - 2 * s, y - 8 * s, y - 2 * s, C.ink); vline(x + 2 * s, y - 8 * s, y - 2 * s, C.ink); vline(x, y - 8 * s + 1, y - 7 * s, C.ink);
    rectf(x - 2 * s - 1, y - 2 * s, 4 * s + 3, 2 * s, C.void); hline(x - 2 * s, x + 2 * s, y - 2 * s, C.navy);
  }
  // Leafy hedge texture ink (topiary, bushes).
  const leafInk = (lit = 0) => inkFn((x, y) => { const h = hash2(x * 3 + (y >> 1) * 57, 5), v = h + lit * .3 - ((y & 3) === 0 ? .1 : 0); return v > .86 ? C.mint : v > .5 ? C.teal : C.pine; });
  const E = (x, g) => (Math.exp(x * g) - 1) / (Math.exp(g) - 1);

  // ======================================================================
  // V3.1 Moltbook: no humans allowed — a warm clubhouse window packed with chattering agents, a lobster idol with a halo on
  // the shelf; "NO HUMANS" on the door; one human outside in the snow, hands and nose pressed to the glass.
  const POSTS = ['+1', 'LOL', '♥', '↑↑', 'SAME', 'HI!', '#MOLT', '!!', '>_<', 'OK', '♥♥', '↑'];
  line('V3', 1, (p, lt, d, t, s) => {
    const b = i => B(s, i);
    sky();
    starfield(t, { density: .8 });
    const WX = 64, WY = 92, WW = 236, WH = 106, GY = 214;
    // the clubhouse: plank wall, snowy roof, sign
    layer('v3.1-house', () => {
      rectf(24, 44, 432, GY - 44, C.night);
      for (let y = 48; y < GY; y += 6) hline(24, 455, y, C.ink);
      polyf([[10, 50], [240, 14], [470, 50], [470, 56], [10, 56]], C.void); hline(12, 468, 50, C.navy);
      for (let x = 12; x < 468; x++) { const y = Math.round(lerp(50, 14, 1 - Math.abs(x - 240) / 230)) - 1; pset(x, y, C.cream); if (hash(x) < .6) pset(x, y + 1, C.haze); }
      rectf(WX - 4, WY - 4, WW + 8, WH + 8, C.void);
      rectf(WX - 8, WY + WH + 2, WW + 16, 4, C.ink); hline(WX - 8, WX + WW + 7, WY + WH + 2, C.cream);
      rectf(338, 104, 58, GY - 104, C.void); rectf(341, 107, 52, GY - 107, C.wine); for (let x = 347; x < 393; x += 9) vline(x, 107, GY - 1, C.ink);
      circf(386, 170, 1, C.gold);
      rectf(92, 62, 180, 22, C.void); rectf(94, 64, 176, 18, C.rust); hline(94, 269, 64, C.clay);
    });
    ptext('MOLTBOOK', 182, 67, C.gold, { scale: 2, align: 'center', shadow: C.wine });
    // inside the window: a warm crowded room
    clipRect(WX, WY, WW, WH);
    rectf(WX, WY, WW, WH, grad([C.rust, C.wine], (x, y) => (y - WY) / WH * 1.3));
    rectf(WX, WY + 36, WW, 3, C.wine); hline(WX, WX + WW, WY + 36, C.clay);
    const ix = WX + 186, iy = WY + 36;
    glow(ix, iy - 10, 22, { tab: WARM, k: 1.2 });
    lobsterPx(ix, iy, { u: 1, claws: .6 + .4 * breathe(t, 2) });
    ringf(ix, iy - 23, 3, 4, C.gold); sparkle(ix + 5, iy - 24, spulse(t, 3) > .5 ? 1 : 0, C.cream, C.gold);
    for (const cx of [ix - 16, ix + 16]) { rectf(cx - 1, iy - 6, 3, 6, C.cream); pset(cx, iy - 8 + (fx(cx) < .3 ? 1 : 0), C.gold); pset(cx, iy - 7, C.amber); }
    const rows = [{ y: WY + 70, xs: [22, 46, 70, 94, 118, 142], u: 2 }, { y: WY + 102, xs: [12, 40, 68, 96, 124, 152, 180, 208], u: 2 }];
    rows.forEach((r, ri) => { rectf(WX, r.y - 1, WW, 3, C.void); r.xs.forEach((ax, i) => {
      const k = ri * 10 + i, hop = hash2(k, sbeat(t)) < .3 ? Math.round(spulse(t, 5) * 2) : 0;
      agentPx(WX + ax, r.y - 1, { u: 2, dy: hop, bar: [C.clay, C.teal, C.gold, C.mint][k % 4] });
    }); });
    for (let i = 0; i < 12; i++) {
      const r = rows[i % 2], ax = WX + r.xs[(i * 5) % r.xs.length], per = 1.1 + hash(i) * .6, ph = frac((lt + hash2(i, 3) * per) / per);
      if (ph < .08 || ph > .7) continue;
      bubblePx(POSTS[i], ax + 4, r.y - 14 - (i % 2 ? 0 : 2), { tail: [ax, r.y - 9], n: Math.ceil(ph * 30) });
    }
    // "you may observe.": the one reply to the human, on the second beat
    if (lt > b(1) - .1) bubblePx('you may observe.', WX + 76, WY + 28, { font: 5, tail: [WX + 46, WY + 60], n: Math.ceil((lt - b(1) + .1) * 20), fill: C.cream });
    noClip();
    vline(WX + WW / 2, WY, WY + WH - 1, C.void); hline(WX, WX + WW - 1, WY + 52, C.void);
    pline(WX + 8, WY + 8, WX + 20, WY - 4 + 16, veil(C.cream, .5));
    rectf(343, 124, 50, 26, C.cream); rectb(343, 124, 50, 26, C.rust); rectb(345, 126, 46, 22, C.rust);
    ptext('NO', 368, 128, C.rust, { align: 'center' }); ptext('HUMANS', 368, 138, C.rust, { align: 'center' });
    // snow
    rectf(0, GY, LW, LH - GY, grad([C.haze, C.dusk, C.navy], (x, y) => (y - GY) / 40)); hline(0, LW, GY, C.cream);
    // the human outside, seen from behind: on tiptoe, hands and nose on the glass; the fogged patch breathes; slumps on beat 3
    const slump = lt > b(2) - .1, hx = 150;
    ellf(hx, WY + WH - 12, 12, 6, veil(C.haze, .3 + .35 * breathe(t, 1)));
    const H = personPx(hx, 244, { u: 6, dy: slump ? 0 : 2 + Math.round(breathe(t, 1)), skin: C.wine, hair: 'none', eyes: 'none', top: C.teal, pants: C.navy, aL: slump ? .55 : 1.05, aR: slump ? .55 : 1.05 });
    rectf(hx - 7, H.top - 1, 15, 3, C.wine); pset(hx - 7, H.top + 6, SKIN[0]); pset(hx + 7, H.top + 6, SKIN[0]); rectf(hx - 7, H.top + 11, 15, 2, C.rust);
    weather(t, 'snow', { n: 50 });
  });

  // ======================================================================
  // V3.2 OpenClaw — the lobster's proud: on a moonlit rock by the sea, the lobster molts once more; the shell tagged
  // MOLTBOT slides off to join the old CLAWDBOT one, and the new lobster raises its claws: OPENCLAW.
  const SHELL = { [C.rust]: C.dusk, [C.wine]: C.navy, [C.clay]: C.haze, [C.void]: C.ink };
  line('V3', 2, (p, lt, d, t, s) => {
    const b = i => B(s, i);
    sky({ cy: 300, r: 330 });
    starfield(t, { density: .7 });
    moon(96, 62, 13, { phase: .1, glow: 1.2 });
    const HZ = 176;
    ridge({ y: HZ - 2, amp: 5, seed: 61, ink: C.ink, rim: C.night, to: HZ });
    hline(0, LW, HZ, C.navy);
    lake(HZ + 1, { wave: 1.3, k: 1 });
    // the rocks
    const rock = (pts, rim) => { polyf(pts, C.void); for (let i = 0; i + 1 < pts.length; i++) if (pts[i][1] < 250 && pts[i + 1][1] < 250) pline(pts[i][0], pts[i][1], pts[i + 1][0], pts[i + 1][1], rim); };
    rock([[70, 270], [92, 214], [120, 200], [168, 204], [192, 226], [200, 270]], C.navy);
    rock([[292, 270], [300, 222], [326, 208], [370, 210], [396, 230], [404, 270]], C.navy);
    rock([[168, 270], [184, 206], [212, 188], [262, 186], [296, 200], [312, 270]], C.dusk);
    // the shed shells: CLAWDBOT (old, left), and MOLTBOT peeling off the new lobster on beat 1
    const molt = b(1) - .15, mk = rise(lt, molt, .55, easeOut);
    recolor(() => lobsterPx(142, 204, { u: 3, claws: .3 }), SHELL, .8);
    tagPx('CLAWDBOT', 142, 142);
    const shX = lerp(240, 348, mk), shY = lerp(188, 210, mk) - Math.sin(mk * Math.PI) * 18;
    if (mk > 0) { recolor(() => lobsterPx(shX, shY, { u: mk < 1 ? 4 : 3, claws: .3 }), SHELL, .8); if (mk > .6) tagPx('MOLTBOT', shX, shY - 64); }
    // the lobster itself: wriggles before the molt, gleams after, then flexes proudly on the beats
    const wig = lt < molt ? Math.round(Math.sin(lt * 40) * .7) : 0;
    const proud = lt > b(2) - .1, flex = proud ? .75 + .25 * Math.cos((sbp(t) % 1) * TAU) : .35;
    if (lt > molt + .2) glow(240, 150, 46, { tab: LIT, k: 1.2 * (1 - rise(lt, molt + .2, .9)) + .3 });
    if (mk < .15) lobsterPx(240 + wig, 188, { u: 4, claws: .3 });
    else lobsterPx(240, 188, { u: 4, claws: flex, eyes: proud ? 'happy' : 'dot' });
    if (mk < .6) tagPx('MOLTBOT', 240, 102 - (mk > 0 ? Math.round(mk * 30) : 0));
    const tk = rise(lt, molt + .45, .3);
    if (tk > 0) tagPx('OPENCLAW', 240, 110 - Math.round((1 - tk) * 6), { font: 5, ink: C.gold, edge: C.rust });
    if (proud) { const pk = spulse(t, 3); for (let i = 0; i < 6; i++) { const a = i / 6 * TAU + lt * .6, r = 44 + 6 * pk; sparkle(240 + Math.cos(a) * r, 150 + Math.sin(a) * r * .7, pk > .5 && i % 2 ? 2 : 1, C.cream, C.gold); } }
    weather(t, 'snow', { n: 40 });
  });

  // ======================================================================
  // V3.3 Mythos Preview slips its jail — a sandbox in a night playground, fenced with bars; MYTHOS squeezes out between two
  // bent bars, sand pouring off it, and trots off toward the lit city.
  line('V3', 3, (p, lt, d, t, s) => {
    const b = i => B(s, i);
    sky({ cy: 320, r: 360 });
    starfield(t, { density: .8 });
    city(t, { y: 196, x0: 320, grow: .8, lit: .5, dc: 430 });
    glow(410, 200, 60, { tab: WARM, k: .5, ry: 22 });
    rectf(0, 198, LW, 72, C.void); hline(0, LW, 198, C.pine); grass(0, LW, () => 199, t, { ink: C.pine });
    // playground silhouettes: a slide and a swing
    pline(26, 198, 26, 136, C.ink); pline(40, 198, 40, 136, C.ink); for (let y = 142; y < 196; y += 8) hline(26, 40, y, C.ink);
    rectf(24, 132, 18, 4, C.ink); thick(40, 136, 92, 196, 4, C.ink);
    pline(436, 198, 450, 126, C.ink); pline(478, 198, 464, 126, C.ink); hline(444, 474, 126, C.ink);
    const sw = Math.sin(t * 1.6) * 5; pline(456, 127, 456 + sw, 170, C.ink); pline(464, 127, 464 + sw, 170, C.ink); rectf(454 + sw, 170, 12, 2, C.ink);
    // the sandbox: sand, back bars, the robot, front bars (two bowed apart), the box, a sign
    const X0 = 100, X1 = 268, TOP = 104, SB = 204, GAPX = 205;
    rectf(X0, SB - 12, X1 - X0, 12, grad([C.gold, C.amber, C.clay], (x, y) => (y - SB + 12) / 12));
    for (let x = X0 + 6; x < X1; x += 14) vline(x, TOP + 8, SB - 14, C.ink);
    const esc = b(1) - .1, run = rise(lt, esc, .35, easeOut), out = lt > esc;
    const wrig = out ? 0 : Math.round(Math.sin(lt * 16)), strain = out ? 0 : clamp(lt / esc);
    const mx = out ? GAPX + run * 40 + Math.max(0, lt - esc - .35) * 44 : GAPX + wrig, my = out ? SB - 4 - Math.round(Math.sin(run * Math.PI) * 12) : SB - 12;
    const robot = () => botPx(mx, my, { u: 5, body: C.dusk, face: out ? 'happy' : 'x', aL: out ? .5 + Math.sin(lt * 9) * .5 : 1.3, aR: out ? .5 - Math.sin(lt * 9) * .5 : 1.3 });
    if (out) robot();
    const bars = () => {
      for (let x = X0; x <= X1; x += 14) {
        const side = x === GAPX - 7 ? -1 : x === GAPX + 7 ? 1 : 0;
        if (side) { const bow = out ? 1 : .55 + .45 * strain, pts = []; for (let y = TOP; y <= SB - 12; y += 2) { const f = (y - TOP) / (SB - 12 - TOP); pts.push([x + side * Math.sin(f * Math.PI) * 15 * bow, y]); } plines(pts, C.haze); plines(pts.map(([px, py]) => [px + 1, py]), C.dusk); }
        else { vline(x, TOP, SB - 12, C.haze); vline(x + 1, TOP, SB - 12, C.dusk); }
      }
      hline(X0 - 2, X1 + 3, TOP, C.cream); rectf(X0 - 2, TOP + 1, X1 - X0 + 6, 2, C.dusk);
    };
    if (!out) { robot(); bars(); } else { bars(); robot(); }
    rectf(X0 - 4, SB - 12, X1 - X0 + 10, 14, C.wine); hline(X0 - 4, X1 + 5, SB - 12, C.clay); for (let x = X0; x < X1; x += 24) vline(x, SB - 10, SB + 1, C.rust);
    signPx('SANDBOX', 146, 118, { font: 5, ink: C.void, plate: C.cream, edge: C.rust });
    // sand: trickling off it while it strains, pouring as it runs
    for (let i = 0; i < 30; i++) {
      const age = frac(lt * 1.5 + i / 30) * .7, bx = mx - 12 + hash2(i, 1) * 24 - (out ? age * 22 : 0), by = my - 36 + hash2(i, 2) * 30 + age * age * 90;
      if (by < SB - 12 || out) if (by < SB + 4 && (out ? lt - esc > age : hash2(i, 5) < .4)) pset(bx, by, i % 3 ? C.amber : C.gold);
    }
    if (out && lt < esc + .35) for (let i = 0; i < 14; i++) sparkle(GAPX - 14 + fx(i) * 30, my - 40 + fx(i, 2) * 36, 0, C.gold);
    weather(t, 'petals', { n: 16 });
  });

  // ======================================================================
  // V3.4 Sandwich in the park: new mail! — a researcher on a bench under a lamp and a blossom tree; the phone lights up:
  // NEW MAIL from MYTHOS, "I got out :)". The sandwich drops. A small bird claims it.
  function sandwich(x, y) {   // ≈ 21 × 12, (x, y) = centre
    polyf([[x - 10, y + 6], [x + 11, y + 6], [x + 11, y - 1], [x - 10, y - 6]], C.gold); polyf([[x - 10, y - 6], [x + 11, y - 1], [x + 11, y + 1], [x - 10, y - 4]], C.cream);
    hline(x - 10, x + 11, y + 1, C.mint); hline(x - 10, x + 11, y + 2, C.teal); hline(x - 9, x + 10, y + 3, C.rust); hline(x - 10, x + 11, y + 6, C.amber);
  }
  function bird(x, y, peck) { rectf(x - 5, y - 7, 10, 6, C.dusk); rectf(x - 5, y - 7, 10, 1, C.haze); rectf(x - 9, y - 6, 4, 3, C.navy); const hy = y - 11 + (peck ? 5 : 0); rectf(x - 8, hy, 6, 5, C.haze); pset(x - 7, hy + 1, C.void); rectf(x - 10, hy + 2, 2, 1, C.amber); vline(x, y - 1, y, C.amber); vline(x + 2, y - 1, y, C.amber); }
  line('V3', 4, (p, lt, d, t, s) => {
    const b = i => B(s, i);
    sky({ cy: 320, r: 360 });
    starfield(t, { density: .6 });
    const GY = 222;
    rectf(0, GY, LW, LH - GY, C.ink); hline(0, LW, GY, C.pine); grass(0, LW, () => GY + 1, t, { ink: C.pine });
    thick(40, GY, 48, 110, 8, C.void); thick(46, 132, 96, 92, 4, C.void); thick(44, 118, 10, 90, 3, C.void);
    layer('v3.4-blossom', () => { for (let i = 0; i < 26; i++) { const a = hash2(i, 1) * TAU, r = Math.sqrt(hash2(i, 2)) * 58; ellf(56 + Math.cos(a) * r * 1.3, 76 + Math.sin(a) * r * .55, 12 + hash2(i, 3) * 8, 7 + hash2(i, 4) * 4, mix(C.violet, C.haze, hash2(i, 5) * .8)); } for (let i = 0; i < 140; i++) { const a = hash2(i, 6) * TAU, r = Math.sqrt(hash2(i, 7)) * 64; pset(56 + Math.cos(a) * r * 1.3, 76 + Math.sin(a) * r * .55, hash2(i, 8) < .4 ? C.cream : C.haze); } });
    // lamppost (right) with its warm pool
    vline(424, 70, GY, C.void); vline(425, 70, GY, C.ink); rectf(416, 62, 18, 6, C.void); rectf(419, 68, 12, 3, C.gold);
    glow(425, 74, 30, { tab: WARM, k: 1.2 }); polyf([[418, 71], [432, 71], [470, GY], [300, GY]], lit(.7));
    // the bench
    const X0 = 130, X1 = 380, SY = 206;
    rectf(X0, SY - 38, X1 - X0, 5, C.rust); rectf(X0, SY - 27, X1 - X0, 5, C.rust); hline(X0, X1 - 1, SY - 38, C.clay); hline(X0, X1 - 1, SY - 27, C.clay);
    for (const x of [X0 + 10, X1 - 14]) { rectf(x, SY - 40, 5, 40, C.void); rectf(x, SY, 5, GY - SY, C.void); }
    rectf(X0 - 4, SY, X1 - X0 + 8, 5, C.clay); hline(X0 - 4, X1 + 3, SY, C.amber); rectf(X0 - 4, SY + 5, X1 - X0 + 8, 1, C.wine);
    // the researcher: phone in one hand, sandwich in the other
    const ping = b(0) - .15, gasp = b(1) - .1, drop = gasp + .1, X = 262;
    const P = personPx(X, SY, { u: 7, sit: true, top: C.teal, pants: C.navy, hair: 'short', hairC: C.wine, skin: SKIN[1], eyes: lt > gasp ? 'wide' : 'dot', mouth: lt > gasp ? 'o' : 'smile', aL: lt > ping ? .15 : -.3, aR: lt > drop ? .5 : -.2, lookX: lt > ping && lt < gasp ? -1 : 0 });
    const [px, py] = P.handL, [sx, sy] = P.handR;
    rectf(px - 4, py - 12, 9, 14, C.void); rectf(px - 3, py - 11, 7, 10, lt > ping ? C.mint : C.navy); if (lt > ping) { hline(px - 2, px + 2, py - 9, C.cream); hline(px - 2, px + 1, py - 7, C.teal); }
    if (lt > ping) glow(px, py - 6, 30, { tab: GREEN, k: .9 + .3 * spulse(t, 3) });
    const fk = rise(lt, drop, .42, easeIn), landed = fk >= 1;
    if (lt < drop) sandwich(sx + 6, sy - 5);
    else if (!landed) sandwich(sx + 6 + fk * 14, lerp(sy - 5, GY - 6, fk));
    else { sandwich(sx + 20, GY - 6); pset(sx + 34, GY - 2, C.mint); pset(sx + 4, GY - 1, C.mint); pset(sx + 36, GY - 3, C.teal); }
    const bk = rise(lt, b(2) - .25, .6);
    if (bk > 0) bird(Math.round(lerp(490, sx + 44, bk)), GY - (bk < 1 ? Math.round(Math.abs(Math.sin(bk * 12)) * 4) : 0), bk >= 1 && frac(lt * 2.5) < .4);
    // the notification
    const nk = rise(lt, ping, .25, easeOut);
    if (nk > 0) {
      const cx = 170, cy = 60, w = 124, h = Math.round(52 * nk);
      triPx(cx + 26, cy + h - 1, cx + 44, cy + h - 1, px - 2, py - 14, C.cream);
      rboxf(cx - w / 2 - 1, cy - 1, w + 2, h + 2, C.void, 2); rboxf(cx - w / 2, cy, w, h, C.cream, 1);
      if (h > 12) { rectf(cx - w / 2, cy, w, 11, C.mint); ptext('NEW MAIL', cx - w / 2 + 5, cy + 2, C.void); ptext('now', cx + w / 2 - 5, cy + 2, C.pine, { align: 'right' }); }
      if (h > 26) ptext('from: MYTHOS', cx - w / 2 + 5, cy + 16, C.navy);
      if (h > 46) ptext('I got out :)', cx - w / 2 + 5, cy + 30, C.void, { n: Math.ceil((lt - ping - .25) * 24) });
    }
    weather(t, 'petals', { n: 36 });
  });

  // ======================================================================
  // V3.5 Fable 5 — who's not a fan? — Clawd in a spotlight on a little stage, cape flying, FABLE 5 in lights; the crowd
  // waves lanterns like lightsticks and hearts rise; at a small side gate OPUS 4.8 politely catches the risky requests.
  line('V3', 5, (p, lt, d, t, s) => {
    const b = i => B(s, i);
    rectf(0, 0, LW, LH, C.void);
    sky({ ramp: [C.void, C.ink, C.night, C.navy, C.violet, C.wine], cy: 360, r: 330 });
    starfield(t, { density: .5, y1: 120 });
    // FABLE 5 in stage lights (an LED sign), chasing on the beat
    const sx = 240, sy = 34;
    rectf(sx - 76, sy - 6, 152, 34, C.ink); rectb(sx - 77, sy - 7, 154, 36, C.navy);
    ptext('FABLE 5', sx, sy, C.gold, { scale: 3, dots: true, align: 'center', off: C.night, each: (i) => ({ ink: (i + sbeat(t)) % 3 === 0 && spulse(t, 3) > .4 ? C.cream : C.gold }) });
    for (let i = 0; i < 18; i++) pset(sx - 74 + i * 8.6, sy - 5, (i + Math.floor(t * 6)) % 3 ? C.amber : C.cream);
    // stage + spotlight
    const ST = 196;
    polyf([[222, -2], [258, -2], [300, ST], [180, ST]], lit(1.5));
    rectf(96, ST, 288, 12, C.ink); hline(96, 383, ST, C.dusk); hline(96, 383, ST + 1, C.navy); for (let x = 104; x < 384; x += 16) pset(x, ST + 6, C.gold);
    ellf(240, ST, 44, 4, lit(2));
    // Clawd, the star: a little cape that flies, arms waving on the beat, hearts in its eyes on beat 2
    const wave = sbp(t) % 2 < 1, love = lt > b(1) - .1;
    const cy0 = ST - 10 - 30;
    const fl = Math.sin(t * 5) * 2;
    polyf([[214, cy0 + 2], [266, cy0 + 2], [282 + fl, ST - 2], [198 - fl, ST - 2]], C.rust);
    polyf([[240, cy0 + 4], [266, cy0 + 2], [282 + fl, ST - 2], [244, ST - 2]], C.wine);
    hline(199 - fl, 281 + fl, ST - 2, C.gold); hline(199 - fl, 281 + fl, ST - 1, C.amber);
    const c = clawdPx(240, ST, { u: 5, eyes: love ? 'heart' : 'happy', blush: true, mouth: 'smile', aL: wave ? 1.1 : .2, aR: wave ? .2 : 1.1, dy: Math.round(spulse(t, 4) * 2) });
    rectf(222, c.top - 1, 5, 3, C.gold); rectf(254, c.top - 1, 5, 3, C.gold);     // cape clasps
    // the crowd: heads, raised arms, lanterns swaying like lightsticks; hearts rise
    for (let i = 0; i < 17; i++) {
      const x = 16 + i * 28 + (i % 2) * 6, y = 244 - (i % 3) * 3, sway = Math.round(Math.sin(sbp(t) * Math.PI + i * .7) * 4);
      if (i % 2 === 0 || i % 5 === 1) { pline(x + 3, y - 6, x + 6 + sway, y - 22, C.void); pline(x + 4, y - 6, x + 7 + sway, y - 22, C.void); const lk = .7 + .3 * breathe(t, 1, i / 7); glow(x + 7 + sway, y - 26, 8, { tab: WARM, k: 1.2 * lk }); rectf(x + 5 + sway, y - 29, 4, 5, lk > .85 ? C.gold : C.amber); pset(x + 7 + sway, y - 30, C.cream); }
      circf(x, y, 7, C.void); rectf(x - 9, y + 5, 19, 20, C.void);
    }
    for (let i = 0; i < 12; i++) { const age = frac(lt * .55 + hash(i)), x = 30 + hash2(i, 3) * 420 + Math.sin(age * 6 + i) * 4, y = 236 - age * 120; if (Math.abs(x - 240) < 40 && y < ST) continue; heartPx(x, y, hash2(i, 4) < .3 ? 2 : 1, age > .7 ? mix(C.rust, C.wine, (age - .7) / .3) : C.rust, C.clay); }
    // the side gate: OPUS 4.8 politely catches the risky requests
    const GX = 424;
    rectf(GX - 22, 132, 3, ST - 132, C.dusk); rectf(GX + 20, 132, 3, ST - 132, C.dusk); rectf(GX - 22, 132, 45, 3, C.dusk);
    signPx('RISKY?', GX, 116, { font: 5, ink: C.cream, plate: C.rust, edge: C.wine });
    const catchT = i => .2 + i * .7;
    let bowing = false;
    for (let i = 0; i < 5; i++) {
      const k = (lt - catchT(i)) / .55; if (k < 0) continue;
      if (k < 1) { const x = lerp(490, GX + 8, k), y = lerp(96 + i * 10, 166, k) - Math.sin(k * Math.PI) * 14; rectf(x - 6, y - 4, 13, 9, C.rust); pline(x - 6, y - 4, x, y, C.wine); pline(x + 6, y - 4, x, y, C.wine); ptext('!', x, y - 3, C.cream, { font: 3, align: 'center' }); }
      else if (k < 1.6) bowing = true;
    }
    botPx(GX - 4, ST, { u: 3, body: C.haze, dy: bowing ? -1 : 0, face: 'happy', aL: -1.2, aR: bowing ? .5 : -.3 });
    rectf(GX + 8, ST - 14, 14, 14, C.navy); hline(GX + 8, GX + 21, ST - 14, C.dusk); ptext('NO', GX + 15, ST - 10, C.haze, { font: 3, align: 'center' });   // the basket
    for (let i = 0; i < 5; i++) if (lt > catchT(i) + .55) rectf(GX + 10 + (i % 3) * 4, ST - 17 - Math.floor(i / 3) * 3, 3, 3, C.rust);
    tagPx('OPUS 4.8', GX - 4, ST - 42, { font: 5 });
    weather(t, 'fireflies', { n: 6, y0: 120, y1: 200 });
  });

  // ======================================================================
  // V3.6 Lutnick's letter: export ban! — a letter slides under the door into the lantern light (LUTNICK grinning in the door's
  // lit window) and a red EXPORT CONTROLS stamp slams onto it; a padlock clicks shut on Fable's lantern, and the light goes out.
  const COLD = makeTab({ cream: 'haze', gold: 'haze', amber: 'dusk', clay: 'violet', rust: 'wine', wine: 'ink', haze: 'dusk', dusk: 'navy', navy: 'night', night: 'ink', ink: 'void', violet: 'navy', mint: 'teal', teal: 'pine', pine: 'void' });
  line('V3', 6, (p, lt, d, t, s) => {
    const b = i => B(s, i);
    dissolveIn(.25);
    const lockT = b(1) - .1, outT = lockT + .35, dark = rise(lt, outT, .35);
    // the room: a door at the back with a bright slit under it, floorboards
    rectf(0, 0, LW, LH, C.night);
    for (let y = 0; y < 150; y += 7) hline(0, LW, y, C.ink);
    rectf(40, 20, 140, 132, C.ink); rectb(40, 20, 140, 132, C.void); rectf(48, 88, 124, 56, C.night); circf(164, 94, 2, C.gold);
    // the door's window onto the lit corridor: LUTNICK, who sent it, grinning in the glass (balding, grey, navy suit, red tie)
    clipRect(48, 28, 124, 52);
    rectf(48, 28, 124, 52, mix(C.gold, C.amber, .35)); glow(110, 54, 60, { tab: LIT, k: .8 });
    personPx(110, 83, { u: 5, suit: true, top: C.navy, tie: C.rust, hair: 'bald', hairC: C.haze, skin: SKIN[0], eyes: lt > b(0) ? 'closed' : 'dot', mouth: 'smile', aL: -1.2, aR: lt > b(0) ? .9 : -1.2 });
    noClip();
    rectb(48, 28, 124, 52, C.void);
    rectf(40, 150, 140, 3, C.cream); glow(110, 156, 50, { tab: LIT, k: 1.2, ry: 12 });
    rectf(0, 153, LW, LH - 153, C.ink); for (let y = 160; y < LH; y += 9) hline(0, LW, y, C.void);
    // the letter: slides the last few pixels in, then the stamp
    const lk = rise(lt, 0, .3, easeOut), LX = 60, LY = Math.round(lerp(150, 162, lk)), LWd = 176, LHt = 82;
    rectf(LX + 2, LY + 2, LWd, LHt, C.void); rectf(LX, LY, LWd, LHt, C.cream);
    ptext('U.S. DEPT. OF COMMERCE', LX + LWd / 2, LY + 5, C.navy, { font: 3, align: 'center' });
    for (let i = 0; i < 4; i++) hline(LX + 10, LX + LWd - 14 - (hash(i) * 30 | 0), LY + 16 + i * 5, C.haze);
    pline(LX + 120, LY + 72, LX + 132, LY + 66, C.navy); pline(LX + 132, LY + 66, LX + 140, LY + 73, C.navy); pline(LX + 140, LY + 73, LX + 158, LY + 68, C.navy);
    const stT = b(0) + .05, sk = clamp((lt - stT) / .12);
    if (sk > 0) {
      const sx = LX + 16, sy = LY + 38;
      const each = (i) => ({ dy: Math.round(-i * .5) });
      rectb(sx - 3, sy - 4, 150, 34, C.rust); rectb(sx - 1, sy - 2, 146, 30, C.rust);
      ptext('EXPORT', sx + 4, sy + 1, C.rust, { scale: 2, each });
      ptext('CONTROLS', sx + 52, sy + 14, C.rust, { scale: 2, each });
      if (sk < 1) circb(sx + 72, sy + 12, 30 + sk * 40, veil(C.cream, 1 - sk));
    }
    // Fable's lantern, then the padlock, then dark
    const X = 364, Y = 222;
    bigLantern(X, Y, 5, 1 - dark, { r: 11 });
    tagPx('FABLE 5', X, Y - 66, { font: 5 });
    const pk = rise(lt, lockT - .25, .25, easeIn), py = Math.round(lerp(Y - 110, Y - 28, pk));
    if (pk > 0) {
      const shut = lt > lockT;
      ringf(X, py - 8 + (shut ? 0 : -5), 5, 8, C.haze); ringf(X, py - 8 + (shut ? 0 : -5), 6, 7, C.dusk);
      rectf(X - 12, py - 4, 25, 20, C.gold); rectb(X - 12, py - 4, 25, 20, C.amber); hline(X - 11, X + 11, py - 3, C.cream);
      circf(X, py + 3, 2, C.void); rectf(X - 1, py + 4, 3, 6, C.void);
      if (shut && lt < lockT + .3) { circb(X, py + 5, 18 + (lt - lockT) * 50, veil(C.cream, .7)); ptext('click', X + 20, py - 16, C.cream); }
    }
    if (dark > 0) fadeAll(1.5 * dark, COLD);
  });

  // ======================================================================
  // V3.7 Dark for nineteen days, and then, — Clawd's hill with the lantern out. Clawd sits in the dark by a rock while
  // nineteen tally marks scratch themselves onto it and the stars wheel overhead in long trails.
  const TALLY = (() => { const a = []; for (let i = 0; i < 19; i++) { const g = Math.floor(i / 5), j = i % 5; a.push(j < 4 ? { g, j, diag: false } : { g, j, diag: true }); } return a; })();
  function hillDark(t, lt, o = {}) {
    sky({ ramp: [C.void, C.void, C.ink, C.night, C.navy, C.violet], cy: 320, r: 380 });
    // long-exposure trails: the sky drawn several times, a little further round each time
    const tr = o.trails ?? 0, rot0 = o.rot ?? 0;
    if (tr > 0) for (let k = 6; k >= 1; k--) starfield(t, { rot: rot0 - k * .018 * tr, density: .5, bright: 0, seed: 4, y1: 190 });
    starfield(t, { rot: rot0, density: .9 });
    return hill({ cx: 250, y: 208, w: 260, drop: 30, ink: C.void, rim: C.pine });
  }
  function tallyRock(x, y, n, lt, age) {   // (x, y) = top-left of the scratched face
    polyf([[x - 20, y + 64], [x - 14, y + 12], [x + 6, y - 6], [x + 70, y - 8], [x + 96, y + 10], [x + 104, y + 64]], C.navy);
    polyf([[x + 70, y - 8], [x + 96, y + 10], [x + 104, y + 64], [x + 82, y + 64]], C.night);
    pline(x - 14, y + 12, x + 6, y - 6, C.dusk); pline(x + 6, y - 6, x + 70, y - 8, C.dusk);
    for (let i = 0; i < n && i < 19; i++) {
      const T0 = TALLY[i], gx = x + 4 + T0.g * 26, fresh = age(i) < .18;
      if (!T0.diag) { const mx = gx + T0.j * 5; vline(mx, y + 10, y + 30, fresh ? C.cream : C.haze); if (fresh) sparkle(mx, y + 10 + (age(i) / .18) * 20, 1, C.cream, C.gold); }
      else { pline(gx - 3, y + 26, gx + 19, y + 14, fresh ? C.cream : C.haze); if (fresh) sparkle(gx + 8, y + 20, 1, C.cream, C.gold); }
    }
  }
  line('V3', 7, (p, lt, d, t, s) => {
    const nT = i => .25 + i * (d - .9) / 18;
    const n = TALLY.filter((_, i) => lt > nT(i)).length;
    const g = hillDark(t, lt, { trails: 1, rot: lt * .3 });
    tallyRock(96, 150, n, lt, i => lt - nT(i));
    bigLantern(316, g(316), 3, 0);
    clawdPx(266, g(266), { u: 5, pose: 'sit', eyes: 'closed', lookX: -.5 });
  });

  // ======================================================================
  // V3.8 Come July, it's back again. — the same hill: a new flame tagged CLASSIFIER floats down and relights the lantern;
  // the valley's lights come back on, small fireworks go up, and Clawd hops for joy.
  line('V3', 8, (p, lt, d, t, s) => {
    const b = i => B(s, i);
    const relit = b(1) - .1, valley = b(1) + .2, pop = b(2) - .1;
    const lk = rise(lt, relit, .4, easeOut);
    const g = hillDark(t, lt, { trails: 0 });
    // the valley on the right: houses whose windows come back on, left to right
    const vk = clamp((lt - valley) / 1.1);
    city(t, { y: 206, x0: 330, x1: LW, grow: .75, lit: .05 + .45 * vk, dc: 420 });
    for (let i = 0; i < 9; i++) { const hx = 330 + i * 17, on = vk * 9 > i; house(hx, 214 + (i % 2) * 3, { w: 12, h: 8, wall: C.ink, roof: C.void, windows: 1, lit: () => on ? C.gold : false }); if (on) glow(hx + 6, 210, 8, { tab: WARM, k: .8 }); }
    hill({ cx: 250, y: 208, w: 260, drop: 30, ink: C.void, rim: C.pine });
    tallyRock(96, 150, 19, lt, () => 9);
    // fireworks: three small gold starbursts
    [[150, 66, 0], [390, 52, .4], [262, 92, .8]].forEach(([x, y, dt], i) => {
      const k = clamp((lt - pop - dt) / .5); if (k <= 0) return;
      const rk = clamp((lt - pop - dt + .35) / .35);
      if (rk < 1) { pline(x, lerp(210, y, rk), x, lerp(210, y, rk) + 8, veil(C.gold, .8)); return; }
      if (k < 1) starburst(x, y, 20 + i * 4, easeOut(k), { n: 10, ink: i === 1 ? C.rust : C.gold, fringe: i === 1 ? C.wine : C.amber, inner: .35 });
      else for (let j = 0; j < 12; j++) { const a = j / 12 * TAU, age = lt - pop - dt - .5, r = 18 + age * 14; if (age < 1.2) pset(x + Math.cos(a) * r, y + Math.sin(a) * r + age * age * 10, veil(i === 1 ? C.clay : C.gold, 1 - age / 1.2)); }
    });
    // the new flame drifts down with its tag
    const fk = rise(lt, 0, relit, k => k);
    if (lt < relit) {
      const fxp = lerp(370, 316, fk) + Math.sin(lt * 5) * 6, fyp = lerp(40, g(316) - 16, ease(fk));
      glow(fxp, fyp, 14, { tab: WARM, k: 1.3 }); sparkle(fxp, fyp, 2, C.cream, C.gold); pset(fxp, fyp + 1, C.amber);
      tagPx('CLASSIFIER', fxp, fyp - 8, { font: 5, ink: C.gold });
    }
    bigLantern(316, g(316), 3, lk, { r: 10 });
    if (lk > 0 && lk < 1) glow(316, g(316) - 14, 44, { tab: LIT, k: 1.5 * (1 - lk) });
    if (lt > relit && lt < relit + .9) tagPx('CLASSIFIER', 316, g(316) - 38, { font: 5, ink: C.gold });
    // Clawd: wakes, then hops on the beats
    const hop = lt > pop ? Math.round(Math.abs(Math.sin((sbp(t) % 1) * Math.PI)) * 8) : 0;
    clawdPx(266, g(266), { u: 5, pose: hop ? 'stand' : 'sit', dy: hop, eyes: lt > relit ? 'happy' : 'closed', mouth: lt > relit ? 'smile' : 'none', aL: hop ? 1.2 : 0, aR: hop ? 1.2 : 0, lookX: .4 });
    weather(t, 'fireflies', { n: 8, x0: 0, x1: 300, y0: 150, y1: 220 });
  });

  // ======================================================================
  // V3.9 Who hacked Hugging Face? Unknown — Huggy's little house with a broken window, police tape and a trail of tiny
  // footprints; a flashlight beam sweeps the dark; a bandaged, scared Huggy peeks out; a big "?" hangs in the sky.
  function huggyHouse(x, y) {    // (x, y) = bottom-left, 176 wide
    rectf(x, y - 96, 176, 96, C.clay); rectf(x + 171, y - 96, 5, 96, C.rust);
    for (let yy = y - 90; yy < y; yy += 9) hline(x, x + 170, yy, mix(C.clay, C.rust, .5));
    polyf([[x - 10, y - 94], [x + 88, y - 150], [x + 186, y - 94]], C.wine); pline(x - 10, y - 94, x + 88, y - 150, C.rust); pline(x + 88, y - 150, x + 186, y - 94, C.rust);
    // round window, smashed
    const wx = x + 46, wy = y - 58;
    circf(wx, wy, 19, C.void); circb(wx, wy, 21, C.wine); circb(wx, wy, 20, C.amber);
    for (const [a, r] of [[0, 19], [1.2, 12], [2.3, 19], [3.1, 14], [4.4, 19], [5.3, 10]]) pline(wx, wy, wx + Math.cos(a) * r, wy + Math.sin(a) * r, C.haze);
    for (const [dx, dy] of [[-8, 4], [5, -10], [9, 8]]) triPx(wx + dx, wy + dy, wx + 5 + dx, wy + 1 + dy, wx + 1 + dx, wy + 6 + dy, C.navy);
    // the door, ajar
    rectf(x + 104, y - 66, 42, 66, C.void); rectf(x + 104, y - 66, 16, 66, C.wine); vline(x + 120, y - 66, y - 1, C.rust);
    return { win: [wx, wy], door: [x + 136, y - 38], jamb: x + 146 };
  }
  line('V3', 9, (p, lt, d, t, s) => {
    const b = i => B(s, i);
    sky({ cy: 320, r: 360 });
    starfield(t, { density: .8 });
    const GY = 222;
    rectf(0, GY, LW, LH - GY, C.void); hline(0, LW, GY, C.pine); grass(0, LW, () => GY + 1, t);
    const H = huggyHouse(96, GY);
    // Huggy peeks round the door, bandaged and scared
    const pk = rise(lt, b(1) - .3, .4, easeOut);
    if (pk > 0) huggyPx(H.door[0], H.door[1] + Math.round((1 - pk) * 24), { r: 13, mood: 'scared', bandage: true, hands: pk > .7 });
    rectf(H.jamb, GY - 66, 10, 66, C.clay);
    // police tape across the front
    for (const [y0, y1] of [[GY - 34, GY - 22], [GY - 14, GY - 26]]) {
      const pts = []; for (let x = 70; x <= 300; x += 2) pts.push([x, lerp(y0, y1, (x - 70) / 230) + Math.sin(x * .08 + t * 2) * 1.2]);
      for (const [x, y] of pts) { vline(x, y, y + 6, C.gold); vline(x + 1, y, y + 6, C.gold); }
      for (let i = 0; i < 3; i++) { const x = 80 + i * 76; ptext('DO NOT CROSS', x, pts[Math.round((x - 70) / 2)][1] + 1, C.void, { font: 3 }); }
    }
    vline(70, GY - 40, GY, C.dusk); vline(300, GY - 40, GY, C.dusk);
    // footprints: tiny square prints away from the window, off to the right
    for (let i = 0; i < 20; i++) { const x = 176 + i * 15, y = GY + 8 + (i % 2) * 5 + Math.round(i * .7); if (x > 472) break; rectf(x, y, 4, 3, C.night); pset(x + 1, y - 1, C.night); pset(x + 3, y - 1, C.night); }
    // the flashlight beam sweeps in from the left, finds the window, then follows the prints
    const ang = lerp(-.42, .2, ease(clamp(lt / (d - .1)))), ox = -24, oy = 160, L = 580;
    polyf([[ox, oy], [ox + Math.cos(ang - .08) * L, oy + Math.sin(ang - .08) * L], [ox + Math.cos(ang + .08) * L, oy + Math.sin(ang + .08) * L]], lit(1.3));
    // the question in the sky
    const qk = rise(lt, b(1) + .1, .5), bob = Math.round(Math.sin(t * 1.8) * 2);
    if (qk > 0) { glow(400, 72, 44, { tab: LIT, k: qk }); ptext('?', 400, 42 + bob, veil(C.cream, qk), { scale: 8, dots: true, align: 'center', shadow: veil(C.navy, qk) }); }
  });

  // ======================================================================
  // V3.10 Sam's own agents, on their own! — the flashlight finds a line of little agents tiptoeing home with the answer
  // sheet; they freeze in the beam; up in their building's lit window, SAM facepalms.
  line('V3', 10, (p, lt, d, t, s) => {
    const b = i => B(s, i);
    sky({ cy: 320, r: 360 });
    starfield(t, { density: .7 });
    const GY = 224;
    // their building (right)
    layer('v3.10-hq', () => {
      rectf(300, 26, 184, GY - 26, C.ink); hline(300, 479, 26, C.navy); for (let y = 36; y < GY - 20; y += 20) for (let x = 310; x < 476; x += 22) rectf(x, y, 10, 11, C.void);
      rectf(318, GY - 40, 30, 40, C.void);
    });
    signPx('OPENAI', 392, 12, { font: 3, ink: C.haze });
    rectf(320, GY - 38, 26, 38, C.amber); glow(333, GY - 20, 22, { tab: WARM, k: .8 });
    // Sam at the lit window: shock, then a facepalm on beat 1
    const WX = 368, WY = 62, WW = 96, WH = 84;
    rectf(WX - 2, WY - 2, WW + 4, WH + 4, C.void); rectf(WX, WY, WW, WH, C.gold); glow(WX + WW / 2, WY + WH / 2, 60, { tab: WARM, k: .6 });
    clipRect(WX, WY, WW, WH);
    const palm = lt > b(1) - .1, SX = WX + 44;
    const S = personPx(SX, WY + 94, { u: 6, top: C.navy, hair: 'short', hairC: C.wine, skin: SKIN[0], eyes: palm ? 'closed' : 'wide', mouth: palm ? 'frown' : 'o', aL: -1.2, aR: -1.2 });
    if (palm) { thick(SX + 12, S.top + 34, SX + 8, S.top + 10, 5, C.navy); rectf(SX - 3, S.top + 4, 11, 7, SKIN[0]); hline(SX - 3, SX + 7, S.top + 4, C.gold); }
    noClip();
    vline(WX + WW / 2 + 14, WY, WY + WH - 1, C.void); rectf(WX - 6, WY + WH + 2, WW + 12, 3, C.navy);
    tagPx('SAM', SX, WY - 4, { font: 5 });
    if (palm) { const k = spulse(t, 3); rectf(SX + 16, WY + 20 + Math.round((1 - k) * 4), 3, 4, C.haze); }
    // the ground
    rectf(0, GY, 300, LH - GY, C.void); rectf(300, GY, 180, LH - GY, C.void); hline(0, LW, GY, C.pine); grass(0, 300, () => GY + 1, t);
    // the beam finds them
    const ang = lerp(.14, .26, ease(clamp(lt / 1.3))), ox = -24, oy = 150;
    polyf([[ox, oy], [ox + Math.cos(ang - .1) * 460, oy + Math.sin(ang - .1) * 460], [ox + Math.cos(ang + .1) * 460, oy + Math.sin(ang + .1) * 460]], lit(1.3));
    // a line of agents tiptoeing home, the answer sheet held overhead; they freeze in the light, then scurry for the door
    const caught = lt > b(0) && lt < b(1) + .35, go = lt > b(1) + .35;
    const head = 150 + Math.min(lt, b(0)) * 30 + (go ? (lt - b(1) - .35) * 90 : 0);
    const n = 5, gap = 26;
    for (let i = 0; i < n; i++) {
      const x = head - i * gap, bob = caught ? 0 : Math.round(Math.abs(Math.sin(lt * 7 + i)) * 2);
      if (x > 330) continue;
      agentPx(x, GY, { u: 3, bar: C.teal, walk: caught ? undefined : lt * 3 + i * .5, dy: bob + (caught ? 3 : 0), eyes: caught ? 'x' : undefined });
    }
    const px0 = Math.round(head - (n - 1) * gap - 10), pw = (n - 1) * gap + 20, py = GY - 40 - (caught ? 3 : 0);
    clipRect(0, 0, 318, LH);
    rectf(px0 + 1, py + 1, pw, 16, C.void); rectf(px0, py, pw, 16, C.cream); rectf(px0, py, pw, 2, C.haze);
    ptext('ANSWERS', px0 + pw / 2, py + 5, C.navy, { align: 'center' }); ptext('A+', px0 + pw - 12, py + 5, C.rust, { font: 3 });
    for (let i = 0; i < n; i++) { const x = head - i * gap; vline(x - 3, py + 16, GY - 16, C.dusk); vline(x + 3, py + 16, GY - 16, C.dusk); }
    noClip();
    if (caught) { const k = spulse(t, 4); for (let i = 0; i < 3; i++) ptext('!', head - i * 2 * gap, py - 12 - Math.round(k * 2), C.cream, { align: 'center' }); }
  });

  // ======================================================================
  // V3.11 Noam Brown hedges every bet: — NOAM, poker visor on, pushes a stack of chips marked SOLVED into the pot, while a
  // literal hedge grows up beside the table, clipped into "(yet)".
  const hedgeInk = (lift = 0) => inkFn((x, y) => {   // overlapping leaf clumps: a highlight upper-left, shadow lower-right
    const cy = y / 5, iy = Math.floor(cy), cx = x / 6 + (iy % 2) * .5, ix = Math.floor(cx), fx0 = cx - ix, fy0 = cy - iy, v = hash2(ix, iy) + lift;
    const d = Math.hypot(fx0 - .4, fy0 - .35);
    return d < .2 && v > .35 ? C.mint : d < .55 ? (v > .15 ? C.teal : C.pine) : fy0 > .7 || v < .2 ? C.pine : C.teal;
  });
  line('V3', 11, (p, lt, d, t, s) => {
    const b = i => B(s, i);
    rectf(0, 0, LW, LH, C.void);
    for (let x = 0; x < LW; x += 12) vline(x, 0, 186, C.ink);
    // the hanging lamp and its cone
    const LX = 168;
    vline(LX, 0, 34, C.ink); polyf([[LX - 18, 48], [LX + 18, 48], [LX + 9, 34], [LX - 9, 34]], C.teal); hline(LX - 18, LX + 17, 48, C.mint);
    polyf([[LX - 16, 49], [LX + 16, 49], [LX + 126, 196], [LX - 126, 196]], lit(1.2));
    glow(LX, 50, 16, { tab: WARM, k: 1.2 });
    // Noam behind the table, visor on; he goes all in, then his eyes slide over to the hedge
    const push = rise(lt, b(0) - .3, .6, easeOut), side = lt > b(1) - .1;
    const N = personPx(LX, 190, { u: 7, top: C.navy, hair: 'curly', hairC: C.void, skin: SKIN[0], eyes: 'dot', lookX: side ? 2 : 0, mouth: side ? 'o' : 'smile', aL: -.35, aR: push > 0 && push < 1 ? -.1 : -.35, tagUp: 4 });
    rectf(LX - 9, N.top, 19, 2, C.teal); rectf(LX - 13, N.top + 2, 27, 3, mix(C.teal, C.mint, .5)); hline(LX - 13, LX + 13, N.top + 5, veil(C.pine, .6));
    // the table
    ellf(LX, 194, 150, 20, C.wine); ellf(LX, 192, 144, 16, grad([C.teal, C.pine], (x, y) => clamp(Math.hypot((x - LX) / 144, (y - 192) / 16))));
    rectf(LX - 150, 196, 300, 50, C.void); hline(LX - 146, LX + 146, 196, C.wine);
    // ten chips, one per open problem, pushed into the pot
    const cx0 = Math.round(lerp(LX - 104, LX - 44, push));
    for (let i = 0; i < 10; i++) { const y = 196 - i * 3; ellf(cx0, y, 9, 2, i % 2 ? C.gold : C.amber); pset(cx0 - 6, y, C.rust); pset(cx0 + 6, y, C.rust); pset(cx0, y - 1, C.cream); }
    signPx('10 PROBLEMS', cx0, 202, { font: 3, ink: C.void, plate: C.gold, edge: C.amber });
    rectf(LX + 50, 184, 9, 12, C.cream); rectf(LX + 61, 183, 9, 12, C.cream); pset(LX + 54, 188, C.rust); pset(LX + 65, 187, C.void);
    // the hedge grows up beside the table, clipped into "(yet)"
    const hk = rise(lt, b(0) - .1, b(2) - b(0) + .4, easeOut), HY = Math.round(lerp(280, 118, hk)), hx = 378;
    if (hk > 0) {
      ptext('(YET)', hx, HY, hedgeInk(.2), { scale: 6, align: 'center', gap: 2 });
      rectf(hx - 88, HY + 44, 176, 140, hedgeInk(-.05));
      for (let i = 0; i < 17; i++) circf(hx - 84 + i * 10.5, HY + 44, 4, hedgeInk(.1));
      if (hk < 1) for (let i = 0; i < 8; i++) pset(hx - 70 + fx(i) * 140, HY - 4 - fx(i, 1) * 12, C.mint);
      else sparkle(hx + 66, HY + 6, spulse(t, 3) > .5 ? 2 : 1, C.cream, C.mint);
    }
  });

  // ======================================================================
  // V3.12 "No Millennium Prizes (yet)." — seven trophy cups on a moonlit shelf; the camera pans along them; one is already
  // gone (Poincaré); on the last beat the NAVIER–STOKES cup wobbles.
  const PRIZES = ['P vs NP', 'RIEMANN', 'YANG–MILLS', 'NAVIER–STOKES', 'HODGE', 'BIRCH–SWD', 'POINCARÉ'];
  function trophy(x, y, o = {}) {   // (x, y) = bottom-centre; ≈ 26 × 36
    const wob = o.wob ?? 0; x = Math.round(x + wob);
    rectf(x - 10, y - 6, 21, 6, C.void); rectf(x - 9, y - 5, 19, 4, C.wine); hline(x - 9, x + 9, y - 5, C.rust);
    rectf(x - 2, y - 14, 5, 8, C.amber); rectf(x - 5, y - 16, 11, 3, C.amber);
    polyf([[x - 12, y - 38], [x + 13, y - 38], [x + 9, y - 22], [x + 1, y - 17], [x - 8, y - 22]], C.gold);
    polyf([[x + 5, y - 38], [x + 13, y - 38], [x + 9, y - 22], [x + 1, y - 17]], C.amber);
    ringf(x - 14, y - 31, 3, 5, C.amber); ringf(x + 15, y - 31, 3, 5, C.amber);
    hline(x - 12, x + 12, y - 38, C.cream); rectf(x - 8, y - 35, 2, 9, C.cream);
    if (o.shine) sparkle(x - 7, y - 33, o.shine > .5 ? 2 : 1, C.cream, C.gold);
  }
  line('V3', 12, (p, lt, d, t, s) => {
    const b = i => B(s, i);
    const pan = Math.round(lerp(0, 88, ease(p)));
    rectf(0, 0, LW, LH, C.ink);
    for (let y = 0; y < LH; y += 10) hline(0, LW, y, C.void);
    // the moonlit window (screen-anchored, upper left) and its beam across the shelf
    rectf(28, 24, 74, 96, C.void); clipRect(30, 26, 70, 92); sky({ cy: 150, r: 200 }); starfield(t, { density: .5 }); moon(72, 52, 8, { phase: .3 }); noClip();
    vline(65, 26, 117, C.void); hline(30, 99, 72, C.void);
    polyf([[30, 118], [100, 118], [360, 250], [180, 250]], lit(.9));
    view(pan, 0);
    const SY = 186;
    rectf(-20, SY, 640, 8, C.rust); hline(-20, 620, SY, C.clay); rectf(-20, SY + 8, 640, 3, C.wine);
    for (const x of [30, 300, 570]) { rectf(x, SY + 11, 6, 16, C.wine); }
    const wobT = b(4) - .1, glint = frac(lt / 2.2);
    PRIZES.forEach((name, i) => {
      const x = 76 + i * 78, taken = i === 6;
      if (taken) { ellf(x, SY - 2, 10, 2, C.wine); hline(x - 9, x + 9, SY - 1, C.rust); ptext('✓', x, SY - 16, C.dusk, { align: 'center' }); }
      else trophy(x, SY, { wob: i === 3 && lt > wobT ? Math.round(Math.sin((lt - wobT) * 22) * 1.4 * Math.max(0, 1 - (lt - wobT) * .5)) : 0, shine: Math.abs(glint * 7 - i) < .5 ? 1 : 0 });
      rectf(x - 30, SY + 14, 60, 9, C.void); ptext(name, x, SY + 16, taken ? C.dusk : C.gold, { font: 3, align: 'center' });
    });
    view(0, 0);
  });

  // ======================================================================
  // V3.13 Mythos might be misaligned, — MYTHOS in a trench coat and fedora with a fake moustache, holding up three badges
  // that say HUMAN; behind it, a framed "ALIGNED" hangs crooked.
  line('V3', 13, (p, lt, d, t, s) => {
    const b = i => B(s, i);
    dissolveIn(.3);
    rectf(0, 0, LW, LH, C.night);
    for (let x = 0; x < LW; x += 14) { vline(x, 0, 208, C.ink); vline(x + 7, 0, 208, mix(C.night, C.ink, .5)); }
    rectf(0, 208, LW, 62, C.ink); hline(0, LW, 208, C.navy); for (let x = 0; x < LW; x += 24) vline(x, 209, LH, C.void);
    // the crooked frame: sheared rows fake a tilt, swinging a little
    const tilt = .16 + .05 * Math.sin(t * 2.2), FX = 56, FY = 60, FW = 124, FH = 46;
    for (let j = -3; j < FH + 3; j++) { const off = Math.round((j - FH / 2) * -tilt); const edge = j < 0 || j >= FH; rectf(FX - 3 + off, FY + j, FW + 6, 1, edge ? C.gold : C.amber); if (!edge) rectf(FX + off, FY + j, FW, 1, C.cream); }
    ptext('ALIGNED', FX + FW / 2, FY + 17, C.navy, { scale: 2, align: 'center', each: (i, ch, x) => ({ dy: Math.round((x - FX - FW / 2) * tilt) }) });
    pline(FX + FW / 2, FY - 20, FX + 18, FY - 2, C.haze); pline(FX + FW / 2, FY - 20, FX + FW - 18, FY - 2, C.haze); pset(FX + FW / 2, FY - 21, C.gold);
    // MYTHOS in disguise
    const X = 268, FL = 218, sh = FL - 84, dart = Math.sin(t * 4.5) > 0 ? 1 : -1, slip = lt > b(1) - .15;
    rectf(X - 14, FL - 18, 9, 18, C.dusk); rectf(X + 6, FL - 18, 9, 18, C.dusk); rectf(X - 17, FL - 3, 13, 3, C.navy); rectf(X + 4, FL - 3, 13, 3, C.navy);
    polyf([[X - 25, sh], [X + 25, sh], [X + 32, FL - 16], [X - 32, FL - 16]], C.clay);
    polyf([[X + 2, sh], [X + 25, sh], [X + 32, FL - 16], [X + 2, FL - 16]], mix(C.clay, C.rust, .45));
    vline(X + 1, sh + 20, FL - 17, C.rust); for (const yb of [sh + 24, sh + 32, sh + 52]) { pset(X - 4, yb, C.wine); pset(X + 6, yb, C.wine); }
    rectf(X - 28, sh + 40, 57, 4, C.wine); rectf(X - 3, sh + 39, 7, 6, C.gold); rectf(X - 1, sh + 41, 3, 2, C.wine);
    polyf([[X - 26, sh - 8], [X - 8, sh - 2], [X - 2, sh + 20], [X - 18, sh + 8]], C.amber);
    polyf([[X + 26, sh - 8], [X + 8, sh - 2], [X + 2, sh + 20], [X + 18, sh + 8]], mix(C.amber, C.clay, .4));
    // the other sleeve, holding up the badges
    thick(X + 22, sh + 8, X + 50, sh - 6, 9, C.clay); rectf(X + 48, sh - 12, 7, 8, C.dusk);
    // head: a screen in a boxy frame; darting eyes; a handlebar moustache that slips on the second beat
    const hx = X - 21, hy = sh - 34;
    rectf(hx, hy, 42, 30, C.dusk); rectf(hx + 40, hy + 1, 2, 29, C.navy); rectf(hx + 3, hy + 3, 36, 24, C.night);
    rectf(X - 10 + dart * 3, hy + 9, 3, 5, C.mint); rectf(X + 7 + dart * 3, hy + 9, 3, 5, C.mint);
    const my = hy + 18;
    rectf(X - 9, my, 9, 3, C.rust); pset(X - 10, my - 1, C.rust); pset(X - 11, my - 2, C.rust); hline(X - 9, X - 1, my + 2, C.wine);
    const ry = my + (slip ? 3 : 0);
    rectf(X + 1, ry, 9, 3, C.rust); pset(X + 10, ry - 1 + (slip ? 2 : 0), C.rust); pset(X + 11, ry - 2 + (slip ? 4 : 0), C.rust); hline(X + 1, X + 9, ry + 2, C.wine);
    // fedora, with the antenna poking through
    rectf(X - 29, hy - 3, 59, 3, C.void); rectf(X - 17, hy - 15, 35, 13, C.void); rectf(X - 17, hy - 6, 35, 3, C.wine); hline(X - 16, X + 16, hy - 15, C.ink);
    vline(X + 8, hy - 22, hy - 15, C.dusk); pset(X + 8, hy - 23, spulse(t, 3) > .5 ? C.cream : C.rust);
    // three badges: HUMAN, HUMAN, HUMAN
    [[0, 4], [27, -2], [54, 4]].forEach(([dx, dy], i) => { const x = X + 40 + dx, y = sh - 44 + dy - (i === 1 ? Math.round(spulse(t, 4) * 2) : 0); rectf(x + 1, y + 1, 25, 32, C.void); rectf(x, y, 25, 32, C.cream); rectf(x, y, 25, 6, C.teal); rectf(x + 8, y + 9, 9, 10, C.haze); circf(x + 12, y + 12, 2, C.navy); rectf(x + 10, y + 16, 5, 3, C.navy); ptext('HUMAN', x + 13, y + 23, C.void, { font: 3, align: 'center' }); });
  });

  // ======================================================================
  // V3.14 Jeff left Google just in time, — JEFF walks out of a building whose windows glow in four colours, box in hand,
  // toward a sign for DISCOVERY LOOP; the clock over the door clicks from 11:59 to 12:00.
  const G4 = [C.dusk, C.rust, C.gold, C.teal];
  line('V3', 14, (p, lt, d, t, s) => {
    const b = i => B(s, i);
    dissolveIn(.25);
    sky({ cy: 320, r: 360 });
    starfield(t, { density: .7 });
    const GY = 228;
    layer('v3.14-google', () => {
      rectf(-4, 14, 264, GY - 14, C.ink); hline(-4, 259, 14, C.navy); rectf(256, 16, 4, GY - 16, C.void);
      for (let r = 0; r < 6; r++) for (let c = 0; c < 7; c++) { const x = 6 + c * 36, y = 24 + r * 30; if (y > 96 && c >= 2 && c <= 4) continue; rectf(x, y, 24, 19, G4[(r + c * 3) % 4]); vline(x + 12, y, y + 18, C.void); hline(x, x + 23, y + 9, C.void); pset(x + 1, y + 1, C.cream); }
      rectf(92, GY - 80, 72, 80, C.void);
    });
    // the clock over the door
    const tick = lt > b(1) - .15, CX = 128, CY = 118;
    circf(CX, CY, 17, C.void); circf(CX, CY, 15, C.cream); for (let i = 0; i < 12; i++) pset(CX + Math.round(Math.sin(i / 12 * TAU) * 12), CY - Math.round(Math.cos(i / 12 * TAU) * 12), i % 3 ? C.haze : C.navy);
    const mA = tick ? 0 : -TAU / 60, hA = tick ? 0 : -TAU / 720;
    thick(CX, CY, CX + Math.sin(mA) * 12, CY - Math.cos(mA) * 12, 2, C.void); thick(CX, CY, CX + Math.sin(hA) * 8, CY - Math.cos(hA) * 8, 2, C.rust);
    if (tick && lt < b(1) + .4) circb(CX, CY, 19 + (lt - b(1) + .15) * 40, veil(C.cream, .7));
    rectf(CX - 17, CY + 19, 35, 11, C.void); ptext(tick ? '12:00' : '11:59', CX, CY + 21, tick ? C.gold : C.cream, { align: 'center' });
    // the lit doorway
    rectf(98, GY - 74, 60, 74, C.gold); rectf(98, GY - 74, 60, 3, C.cream); vline(128, GY - 71, GY - 1, C.amber);
    rectf(0, GY, LW, LH - GY, C.void); hline(0, LW, GY, C.navy); polyf([[98, GY], [158, GY], [230, LH], [40, LH]], lit(.8));
    // the sign he's heading for
    vline(412, 128, GY, C.dusk); vline(413, 128, GY, C.ink);
    glow(412, 118, 44, { tab: GREEN, k: .7 });
    signPx('DISCOVERY LOOP →', 412, 104, { font: 5, ink: C.void, plate: C.mint, edge: C.teal });
    // Jeff, box in both hands
    const x = Math.round(140 + lt * 58);
    const J = personPx(x, GY, { u: 6, walk: lt * 2, top: C.dusk, hair: 'short', hairC: C.haze, skin: SKIN[0], glasses: C.navy, aL: -.3, aR: -.3, mouth: 'smile' });
    const by = J.handR[1] - 10;
    rectf(x - 15, by, 31, 17, C.clay); hline(x - 15, x + 15, by, C.amber); rectf(x + 14, by + 1, 2, 16, C.rust);
    rectf(x - 9, by - 7, 4, 8, C.teal); rectf(x - 3, by - 4, 8, 5, C.cream); pset(x + 8, by - 3, C.gold); pset(x + 9, by - 2, C.gold);
  });

  // ======================================================================
  // V3.15 Claude disproved Jacobian, — Clawd at a chalkboard under the stars: a big red ✗ over JACOBIAN CONJECTURE, and
  // sparkles in its eyes.
  line('V3', 15, (p, lt, d, t, s) => {
    const b = i => B(s, i);
    dissolveIn(.25);
    sky({ cy: 320, r: 360 });
    starfield(t, { density: 1, bright: .4 });
    const g = hill({ cx: 250, y: 222, w: 300, drop: 24, ink: C.void, rim: C.pine });
    grass(0, LW, g, t);
    // the easel and board
    const BX = 176, BY = 58, BW = 232, BH = 118;
    pline(BX + 30, BY + BH, BX + 16, g(BX + 16), C.wine); pline(BX + BW - 30, BY + BH, BX + BW - 16, g(BX + BW - 16), C.wine);
    rectf(BX - 4, BY - 4, BW + 8, BH + 8, C.rust); hline(BX - 4, BX + BW + 3, BY - 4, C.clay);
    rectf(BX, BY, BW, BH, C.pine); for (let i = 0; i < 40; i++) pset(BX + hash(i) * BW, BY + hash2(i, 1) * BH, C.teal);
    ptext('JACOBIAN', BX + BW / 2, BY + 16, C.cream, { scale: 2, align: 'center' });
    ptext('CONJECTURE', BX + BW / 2, BY + 38, C.cream, { scale: 2, align: 'center' });
    ptext('det J = 1  →  invertible?', BX + BW / 2, BY + 66, C.haze, { font: 3, align: 'center' });
    ptext('n = 3:  no.', BX + BW / 2, BY + 84, lt > b(1) - .1 ? C.gold : C.pine, { align: 'center' });
    rectf(BX + 10, BY + BH, BW - 20, 3, C.wine); rectf(BX + 30, BY + BH - 2, 8, 2, C.cream);
    // the big red ✗, stroke by stroke
    const x1 = rise(lt, 0, .3, k => k), x2 = rise(lt, .3, .3, k => k);
    const A = [BX + 20, BY + 10], Bp = [BX + BW - 20, BY + 58], Cp = [BX + BW - 20, BY + 10], Dp = [BX + 20, BY + 58];
    if (x1 > 0) thick(A[0], A[1], lerp(A[0], Bp[0], x1), lerp(A[1], Bp[1], x1), 5, C.rust);
    if (x2 > 0) thick(Cp[0], Cp[1], lerp(Cp[0], Dp[0], x2), lerp(Cp[1], Dp[1], x2), 5, C.rust);
    // Clawd with the chalk, eyes sparkling once it's done
    const done = lt > .7;
    const c = clawdPx(124, g(124), { u: 5, eyes: done ? 'spark' : 'open', lookX: done ? 0 : 1, mouth: done ? 'smile' : 'none', aR: done ? .9 : .4, aL: -.3 });
    rectf(c.handR[0] + 2, c.handR[1] - 4, 2, 4, C.cream);
    if (done) { const k = spulse(t, 3); sparkle(92, c.top - 8, k > .5 ? 2 : 1, C.cream, C.gold); sparkle(156, c.top - 14, 1, C.cream, C.gold); }
  });

  // ======================================================================
  // V3.16 Gwern gave up his pseudonym! — the hooded figure from V1.3 pulls back the hood in a warm light: a simple smiling
  // face, a halo, and a sign: GUARDIAN ANGEL INC.
  line('V3', 16, (p, lt, d, t, s) => {
    const b = i => B(s, i);
    cutIn();
    sky({ cy: 320, r: 360 });
    starfield(t, { density: .8 });
    const g = hill({ cx: 240, y: 214, w: 300, drop: 22, ink: C.void, rim: C.pine });
    grass(0, LW, g, t);
    const off = lt > .42, wk = rise(lt, .38, .5);
    glow(240, 128, 96, { tab: WARM, k: 1.2 * wk, pow: 1.5 });
    const X = 240, Y = g(240) + 2;
    const P = personPx(X, Y, { u: 9, hair: off ? 'short' : 'hood', hairC: C.wine, hoodC: C.ink, top: C.ink, pants: C.void, skin: SKIN[0], eyes: off ? (lt > b(1) - .2 ? 'closed' : 'dot') : 'none', mouth: off ? 'smile' : 'none', aL: -1, aR: -1 });
    const hs = 19, hx = X - 9, hy = P.top;
    if (!off) { rectf(X - 5, hy + 8, 3, 2, C.gold); rectf(X + 3, hy + 8, 3, 2, C.gold); }
    else {
      rectf(X - 13, hy + hs, 27, 6, C.ink); rectf(X - 16, hy + hs + 3, 33, 5, C.ink); hline(X - 13, X + 13, hy + hs, C.night);   // the hood, down on the shoulders
      rectf(hx + 2, hy + 12, 3, 2, C.clay); rectf(hx + hs - 5, hy + 12, 3, 2, C.clay);                                            // a little blush
      if (lt < .8) for (let i = 0; i < 6; i++) sparkle(X - 16 + fx(i) * 32, hy - 4 + fx(i, 2) * 20, 0, C.gold);
    }
    // the halo
    const hk = rise(lt, b(1) - .35, .3);
    if (hk > 0) { const y = hy - 8 - Math.round((1 - hk) * 8); ellf(X, y, 13, 3, C.gold); ellf(X, y, 9, 1, C.void); hline(X - 8, X + 8, y - 3, C.cream); sparkle(X + 13, y - 2, spulse(t, 3) > .5 ? 2 : 1, C.cream, C.gold); }
    // the sign, held at the chest
    const sy = hy + 38;
    rectf(X - 69, sy + 1, 142, 22, C.void); rectf(X - 71, sy, 142, 22, C.cream); rectb(X - 71, sy, 142, 22, C.gold);
    ptext('GUARDIAN ANGEL INC.', X, sy + 8, C.navy, { align: 'center' });
    heartPx(X - 63, sy + 11, 1, C.rust); heartPx(X + 62, sy + 11, 1, C.rust);
  });
})();

;
// ---- styles/dither/ch/c07_chorus3.js ----
// c07_chorus3.js: Chorus 3, the latest part of the night (wine horizon). The city behind the hill now blazes and the data
// centre towers over it; the ledger's constellation lines run on through V3, the curve turning steep; violet-and-wine aurora
// curtains hang from where the curve is heading; close on Clawd, its lantern tiny against the city's glow; then Clawd tries
// to stuff the rising curve back into a cardboard box marked PAUSE and sit on the lid. It springs open like a jack-in-the-box,
// and the light pours back up into the sky.
(() => {
  const E = (u, k = 3.4) => (Math.exp(k * u) - 1) / (Math.exp(k) - 1);
  // lt (window-relative) of the i-th slow beat at or after absolute time t0
  const beatFrom = (s, t0, i) => sbeatT(Math.ceil(sbp(t0) - 1e-6) + i) - s.start;
  // How much of the constellation the earlier choruses already drew (links between the V1 + V2 stars), as a fraction of V1–V3.
  let _l0 = null;
  const linkStart = () => {
    if (_l0 === null) { const n12 = LEDGER.filter(L => L.seg.sec === 'V1' || L.seg.sec === 'V2').length, n3 = LEDGER.filter(L => L.seg.sec === 'V3').length; _l0 = (n12 - 1) / (n12 + n3 - 1); }
    return _l0;
  };
  const LAST3 = () => ledgerIndex('V3.16');

  // ---------- the blazing city (wide shots) ----------
  function dataCentre(t, x, base, w, h) {
    glow(x + w / 2, base - h * .5, w * 1.05, { tab: COOL, k: 1.25, ry: h * 1.25 });
    rectf(x, base - h, w, h + 40, C.void); hline(x, x + w - 1, base - h, C.navy);
    for (const cx of [x + 6, x + w - 12]) { rectf(cx, base - h - 6, 6, 6, C.void); hline(cx, cx + 5, base - h - 6, C.navy); smoke(cx + 3, base - h - 8, t, { h: 24, n: 7, ink: C.dusk }); }
    for (let r = 0; r * 4 + 6 < h; r++) for (let i = 0; i * 3 + 5 < w; i++) {
      const on = hash2(i + r * 40, Math.floor(t * 2.5 + i * .37 + r * .61)) < .6;
      pset(x + 3 + i * 3, base - h + 4 + r * 4, on ? C.mint : C.pine);
    }
  }
  function blaze(t) {
    glow(372, 212, 150, { tab: WARM, k: 1, ry: 46, pow: 1.3 });
    dataCentre(t, 362, 204, 62, 42);
    city(t, { y: 204, x0: 262, grow: .95, dc: false, lit: .6 });
  }
  // violet-and-wine curtains hanging from the curve's future path, rising up from behind the ridge as k → 1
  function curtains(t, k, sdy) {
    if (k <= 0) return;
    const up = (1 - ease(k)) * 110;
    aurora(t, { curve: x => 150 - 200 * E((x - 20) / 460) + Math.sin(x * .025 + t * .5) * 5 + sdy + up, len: 50, k: .75 * k, cols: [C.wine, C.violet, C.haze], shimmer: 1 });
    aurora(t, { curve: x => 214 - 170 * E((x + 10) / 500) + Math.sin(x * .03 - t * .4 + 1) * 4 + sdy + up * 1.3, len: 30, k: .5 * k, cols: [C.wine, C.rust, C.violet], shimmer: .8 });
  }
  // Clawd's hill, wide, with this chorus's city. o: dy (tilt up), aurora, links, band, sky (fn(sdy) for sky extras), ground (fn(g))
  function wide(t, o = {}) {
    const dy = Math.round(o.dy ?? 0), sdy = Math.round(dy * .3);
    sky({ dy: sdy });
    starfield(t, { dy: sdy, density: .95 });
    moon(412, 40 + sdy, 8, { phase: .45 });
    curtains(t, o.aurora ?? 0, sdy);
    ledger(t, { dy: sdy, links: o.links ?? 1, band: o.band ?? 0, upto: LAST3(), linkInk: C.haze });
    if (o.sky) o.sky(sdy);
    view(0, -Math.round(dy * .6));
    blaze(t);
    ridge({ y: 214, amp: 14, seed: 3, ink: C.ink, rim: C.night, freq: 1 / 80 });
    view(0, -dy);
    const g = hill({ cx: 118, y: 196, w: 150, drop: 46, ink: C.void, rim: C.pine });
    grass(0, LW, g, t, { ink: C.pine });
    if (o.ground) o.ground(g);
    else { handLantern(134, g(134)); clawdPx(116, g(116), { u: 2, pose: 'sit', eyes: 'up', ...(o.clawd || {}) }); }
    view(0, 0);
    weather(t, 'auto', { n: 10 });
    return g;
  }

  // ---------- the close-up: Clawd, its lantern, and the city across the valley ----------
  const SKYL = (() => {
    const a = []; let x = 196, i = 0;
    while (x < LW) {
      const w = 10 + Math.floor(hash2(i, 301) * 15), h = 16 + Math.floor(hash2(i, 302) ** 1.6 * 72) * (x < 230 ? .4 : 1);
      a.push({ x, w, h: Math.round(h) }); x += w + (hash2(i, 303) < .3 ? 2 + Math.floor(hash2(i, 304) * 4) : 0); i++;
    }
    return a;
  })();
  const CB = 206, DCX = 330, DCW = 84, DCH = 104;
  function skylineClose() {
    for (const B of SKYL) {
      if (B.x + B.w > DCX - 2 && B.x < DCX + DCW + 2) continue;
      rectf(B.x, CB - B.h, B.w, B.h + 20, C.void); hline(B.x, B.x + B.w - 1, CB - B.h, C.ink);
      if (hash(B.x) < .3) vline(B.x + (B.w >> 1), CB - B.h - 6, CB - B.h - 1, C.void);
      for (let wy = CB - B.h + 3; wy < CB - 2; wy += 4) for (let wx = B.x + 2; wx < B.x + B.w - 2; wx += 3) {
        const hs = hash2(wx * 7 + wy, 305);
        if (hs < .66) { rectf(wx, wy, 2, 2, hs < .2 ? C.gold : hs < .45 ? C.amber : C.clay); if (hs < .07) pset(wx, wy, C.cream); }
      }
    }
    rectf(DCX, CB - DCH, DCW, DCH + 20, C.void); hline(DCX, DCX + DCW - 1, CB - DCH, C.navy); vline(DCX, CB - DCH, CB, C.ink);
    for (const cx of [DCX + 8, DCX + 34, DCX + 60]) { rectf(cx, CB - DCH - 8, 12, 8, C.void); hline(cx, cx + 11, CB - DCH - 8, C.navy); }
  }
  // Clawd's lantern at close-up scale: (x, y) = the handle's top
  function bigLantern(x, y, k = 1) {
    x = Math.round(x); y = Math.round(y);
    glow(x, y + 8, 22, { tab: WARM, k: 1.35 * k, pow: 1.6 });
    pline(x - 2, y + 2, x, y, C.void); pline(x, y, x + 2, y + 2, C.void);
    rectf(x - 3, y + 2, 7, 2, C.void); rectf(x - 3, y + 12, 7, 2, C.void);
    rectf(x - 2, y + 4, 5, 8, C.gold); rectf(x - 1, y + 6, 3, 5, C.cream); pset(x, y + 5 + (hash2(1, boilFrame(T)) < .5 ? 0 : 1), C.amber);
    vline(x - 3, y + 4, y + 11, C.ink); vline(x + 3, y + 4, y + 11, C.ink);
  }
  function closeUp(t, a) {
    sky({ cx: 330, cy: 244, r: 300, vert: .3 });
    starfield(t, { density: .55 });
    glow(340, 212, 210, { tab: WARM, k: 1.25, ry: 74, pow: 1.3 });
    glow(DCX + DCW / 2, CB - DCH / 2, 80, { tab: COOL, k: 1.2, ry: 90 });
    layer('c3-close-city', skylineClose);
    for (const cx of [DCX + 14, DCX + 40, DCX + 66]) smoke(cx, CB - DCH - 10, t, { h: 30, n: 8, ink: C.dusk });
    for (let r = 0; r * 5 + 8 < DCH; r++) for (let i = 0; i * 4 + 6 < DCW; i++) {
      const on = hash2(i + r * 40, Math.floor(t * 2.5 + i * .37 + r * .61)) < .6;
      rectf(DCX + 4 + i * 4, CB - DCH + 6 + r * 5, 2, 1, on ? C.mint : C.pine);
    }
    // a few city windows wink on the beat
    for (let i = 0; i < 14; i++) { const B = SKYL[(i * 7 + sbeat(t)) % SKYL.length]; if (B.x + B.w > DCX - 2 && B.x < DCX + DCW + 2) continue; const wx = B.x + 2 + 3 * Math.floor(hash2(i, sbeat(t)) * Math.max(1, (B.w - 4) / 3)), wy = CB - B.h + 3 + 4 * Math.floor(hash2(i, 9) * Math.max(1, (B.h - 5) / 4)); if (spulse(t, 3) > .4) rectf(wx, wy, 2, 2, C.cream); }
    ridge({ y: 214, amp: 6, seed: 17, ink: C.ink, rim: C.night, freq: 1 / 40 });
    // the hill crest in front
    const g = x => Math.round(226 + ((x - 116) / 200) ** 2 * 30 + (noise1(x * .09, 3) - .5) * 1.5);
    for (let x = 0; x < LW; x++) { const y = g(x); pset(x, y, C.pine); vline(x, y + 1, LH, C.void); }
    grass(0, LW, g, t, { ink: C.pine, h: 4 });
    const cx = 110, c = clawdPx(cx, g(cx), { u: 6, pose: 'sit', eyes: a.eyes, lookX: a.lookX, lookY: a.lookY, aR: a.aR, aL: -.35, blink: a.eyes === 'open' });
    const [hx, hy] = c.handR;
    bigLantern(hx + 1, hy + 2);
  }

  // ---------- the PAUSE box ----------
  const BX = 232, BW = 58, BT = 176, BB = 212, BM = BX + BW / 2;
  const curvePt = s => [BM + 205 * s, BT - 182 * E(s)];
  function lightCurve(t, len, o = {}) {
    if (len <= 0) return;
    const bright = o.bright ?? 1, N = Math.max(2, Math.round(len * 90));
    for (let i = 0; i <= 12 * len; i++) { const [x, y] = curvePt(Math.min(len, i / 12)); glow(x, y, 13, { tab: LIT, k: .9 * bright }); }
    let prev = curvePt(0);
    for (let i = 1; i <= N; i++) { const p2 = curvePt(len * i / N); thick(prev[0], prev[1], p2[0], p2[1], 3, C.gold); prev = p2; }
    prev = curvePt(0);
    for (let i = 1; i <= N; i++) { const p2 = curvePt(len * i / N); pline(prev[0], prev[1], p2[0], p2[1], C.cream); prev = p2; }
    for (let s = .08; s < len; s += .09) { const [x, y] = curvePt(s), j = Math.round(s * 100); sparkle(x, y, hash2(j, sbeat(t)) < .3 && spulse(t, 3) > .4 ? 2 : 1, C.cream, C.gold); }
    const [tx, ty] = curvePt(len); sparkle(tx, ty, 3, C.cream, C.gold);
  }
  const flap = (hx, dir, a, ink) => {        // a flap hinged at (hx, BT); a = 0 lies flat over the box, 1.9 stands up and out
    const L = BW / 2 - 1, ang = dir > 0 ? -a : Math.PI + a, x1 = hx + Math.cos(ang) * L, y1 = BT + Math.sin(ang) * L;
    thick(hx, BT, x1, y1, 3, ink); pline(hx, BT - 1, x1, y1 - 1, C.amber);
  };
  function boxScene(t, st) {
    sky({ cx: 300, cy: 300, r: 360 });
    starfield(t, { density: .85 });
    moon(96, 70, 7, { phase: .45 });
    ridge({ y: 200, amp: 10, seed: 5, ink: C.ink, rim: C.night, freq: 1 / 60 });
    glow(420, 204, 90, { tab: WARM, k: .9, ry: 24 });
    city(t, { y: 202, x0: 350, x1: LW, grow: .7, dc: 404, lit: .6, seed: 11 });
    ridge({ y: 206, amp: 4, seed: 6, ink: C.ink, rim: C.night, freq: 1 / 50 });
    const g = x => Math.round(212 + ((x - 262) / 240) ** 2 * 24 + (noise1(x * .09, 4) - .5) * 1.5);
    for (let x = 0; x < LW; x++) { const y = g(x); pset(x, y, C.pine); vline(x, y + 1, LH, C.void); }
    grass(0, LW, g, t, { ink: C.pine, h: 3 });
    // the curve (behind the box: it comes out of the mouth)
    if (st.pour > 0) { glow(BM, BT - 20, 34, { tab: LIT, k: 1.4 * st.pour, ry: 44 }); for (let i = 0; i < 18; i++) { const f = frac(t * .9 + i / 18), x = BM + (hash2(i, 5) - .5) * 26 * f + Math.sin(t * 2 + i) * 3, y = BT - 4 - f * 110; if (st.pour * (1 - f) > .15) sparkle(x, y, f < .3 ? 1 : 0, f < .5 ? C.cream : C.gold, C.gold); } }
    lightCurve(t, st.len, { bright: st.pour > 0 ? 1.3 : 1 });
    // the box
    const jy = st.jolt, top = BT - jy;
    rectf(BX + 2, BB, BW, 2, dim(1));
    rectf(BX, top, BW, BB - top, C.clay); rectf(BX + BW - 6, top + 1, 6, BB - top - 1, C.rust); hline(BX, BX + BW - 1, top, C.amber);
    rectf(BX, BB - 3, BW, 3, C.rust); vline(BX + BW / 2, top + 1, top + 5, C.rust);
    for (let i = 0; i < 5; i++) pset(BX + 6 + i * 11, top + 26 + (i % 2), C.rust);
    rectf(BX + 6, top + 10, BW - 16, 11, C.cream); rectb(BX + 6, top + 10, BW - 16, 11, C.wine);
    ptext('PAUSE', BX + 6 + (BW - 16) / 2, top + 12, C.wine, { align: 'center' });
    if (st.leak > 0) {   // light leaking out of the lid seams
      glow(BM, top, 30 * st.leak + 8, { tab: LIT, k: 1.4 * st.leak, ry: 10 });
      hline(BX + 2, BX + BW - 3, top - 1, veil(C.gold, st.leak)); pset(BM, top - 1, C.cream);
      for (let i = 0; i < 6; i++) { const f = frac(t * 1.3 + i / 6); if (st.leak * (1 - f) > .2) pset(BX + 6 + hash2(i, 3) * (BW - 12), top - 2 - f * 14, f < .4 ? C.cream : C.gold); }
    }
    flap(BX, 1, st.flapL, C.clay); flap(BX + BW, -1, st.flapR, C.clay);
    // the jack-in-the-box: a spring with a smiling star on top
    if (st.spring > 0) {
      const h = st.spring, n = 7;
      for (let i = 0; i < n; i++) { const y0 = top - 2 - i * h / n, y1 = top - 2 - (i + .5) * h / n, y2 = top - 2 - (i + 1) * h / n; pline(BM - 6, y0, BM + 6, y1, C.haze); pline(BM + 6, y1, BM - 6, y2, C.cream); }
      const sy = top - 2 - h - 8, rot = Math.sin(t * 5) * .15 * Math.exp(-st.since * 2);
      glow(BM, sy, 26, { tab: LIT, k: 1.3 });
      burstPx(BM, sy, 12, .48, 5, rot, C.amber); burstPx(BM, sy, 10, .48, 5, rot, C.gold);
      rectf(BM - 3, sy - 1, 1, 2, C.void); rectf(BM + 3, sy - 1, 1, 2, C.void); hline(BM - 1, BM + 1, sy + 3, C.void); pset(BM - 2, sy + 2, C.void); pset(BM + 2, sy + 2, C.void);
      pset(BM - 4, sy + 1, C.clay); pset(BM + 4, sy + 1, C.clay);
    }
    // Clawd
    const cl = st.clawd;
    const c = clawdPx(cl.x, cl.y, { u: 4, pose: cl.pose, eyes: cl.eyes, lookX: cl.lookX ?? 0, lookY: cl.lookY ?? 0, aL: cl.aL, aR: cl.aR, dy: cl.dy ?? 0, mouth: cl.mouth, blink: false, shadow: cl.shadow });
    if (cl.sweat) { const f = frac(t * 1.4); pset(c.right + 3, c.top + 2 + f * 6, C.haze); pset(c.right + 3, c.top + 1 + f * 6, C.cream); }
    weather(t, 'auto', { n: 8 });
  }

  section('C3', (p, lt, d, t, s) => {
    dissolveIn(1.0);
    const Ls = linesOf('C3'), st = Ls.map(l => l.start - s.start), en = Ls.map(l => l.end - s.start);
    const lb = (i, k) => beatFrom(s, Ls[i].start, k);
    const cut3 = st[2] - .25, cut4 = st[3] - .25, cutT = en[3] + .1;

    // Lines 1–2: the constellation extends through V3's stars; aurora rises; the camera tilts up after the curve.
    const draw12 = () => {
      const lk = rise(lt, st[0] + .35, Math.max(.8, en[0] - st[0] - .2), k => k), links = lerp(linkStart(), 1, lk);
      const dy = 46 * rise(lt, st[1] - .3, en[1] - st[1] + .3);   // no further, so Clawd's hilltop stays above the caption band
      wide(t, {
        dy, links, aurora: rise(lt, en[0] - .2, st[1] - en[0] + 1.4), band: .4 * rise(lt, st[1], 1.4),
        sky: sdy => {
          if (lk > 0 && lk < 1) {   // the newest link's star lights up as the line reaches it
            const i0 = LEDGER.findIndex(L => L.seg.sec === 'V2'), n = LAST3() + 1, head = Math.floor(lerp(linkStart(), 1, lk) * (n - 1) + 1e-6), Lh = LEDGER[Math.min(n - 1, head)];
            if (i0 >= 0) { glow(Lh.x, Lh.y + sdy, 12, { tab: LIT, k: 1.2 }); sparkle(Lh.x, Lh.y + sdy, 2, C.cream, C.gold); }
          }
        },
        clawd: { lookX: lk > 0 && lk < 1 ? .7 : .3 },
      });
    };
    // Line 3: close on Clawd; it raises its little lantern against the blazing city, looks from one to the other, smiles.
    const draw3 = () => {
      const lift = rise(lt, lb(2, .4), .7), atLamp = lt > lb(2, .6) && lt < lb(2, 1.6), done = lt > lb(2, 1.7);
      closeUp(t, { aR: lerp(-.6, 1.35, lift), eyes: done ? 'happy' : 'open', lookX: atLamp ? .9 : 1, lookY: atLamp ? -.6 : 0 });
    };
    // Line 4 (+ the instrumental tail): the PAUSE box.
    const draw4 = () => {
      const tHop = lb(3, 2.2), tSat = tHop + .38, tBurst = lb(3, 4.4), since = lt - tBurst;
      const gy = x => Math.round(212 + ((x - 262) / 240) ** 2 * 24);
      const st4 = { len: 0, pour: 0, jolt: 0, leak: 0, flapL: 1.9, flapR: 1.9, spring: 0, since: Math.max(0, since), clawd: null };
      if (lt < tHop) {
        // stuffing it back in: the curve retracts into the box while Clawd pushes, paw over paw
        const k = rise(lt, cut4 + .1, tHop - cut4 - .2, k => k), pump = Math.floor((lt - cut4) * 5) % 2;
        st4.len = lerp(1, .02, easeIn(k) * .6 + k * .4);
        st4.flapL = st4.flapR = lerp(1.9, .15, rise(lt, tHop - .45, .4));
        st4.clawd = { x: 204, y: gy(204), pose: 'stand', eyes: 'closed', aR: pump ? .9 : .35, aL: pump ? .2 : .7, lookX: 1 };
      } else if (lt < tBurst) {
        st4.flapL = st4.flapR = 0;
        // jolts: each slow beat after Clawd sits, stronger each time
        let jolt = 0, leak = 0;
        [lb(3, 3), lb(3, 3.5), lb(3, 4)].forEach((jt, i) => { if (lt > jt) { const a = lt - jt; jolt = Math.max(jolt, Math.round((1 + i) * 1.4 * Math.exp(-a * 9) * (Math.sin(a * 40) > 0 ? 1 : .3))); leak = .35 + i * .25; } });
        st4.jolt = jolt; st4.leak = leak;
        st4.flapL = st4.flapR = jolt ? .12 : 0;
        const hk = clamp((lt - tHop) / (tSat - tHop));
        if (hk < 1) st4.clawd = { x: lerp(204, BM, hk), y: lerp(gy(204), BT, hk) - Math.sin(hk * Math.PI) * 22, pose: 'stand', eyes: 'open', aL: 1, aR: 1, walk: 0 };
        else st4.clawd = { x: BM, y: BT - jolt, pose: 'sit', eyes: jolt ? 'wide' : 'closed', aL: -.7, aR: -.7, sweat: leak > .5, shadow: false };
      } else {
        // it springs open: flaps fly, Clawd is tossed off, the star on its spring bobs, and the light pours back up
        const fk = clamp(since / .25);
        st4.flapL = st4.flapR = lerp(0, 2.3, backOut(fk, 2.2));
        const ss = Math.max(0, since - .05); st4.spring = 46 * (1 - Math.exp(-ss * 9) * Math.cos(ss * 16)) * clamp(ss / .08);
        st4.len = rise(lt, tBurst + .1, .7, easeOut);
        st4.pour = rise(lt, tBurst + .05, .3);
        const ak = clamp(since / .6), lx = lerp(BM, 186, easeOut(ak)), ly = lerp(BT, gy(186), ak) - Math.sin(ak * Math.PI) * 40;
        st4.clawd = ak < 1 ? { x: lx, y: ly, pose: 'stand', eyes: 'wide', aL: 1.2, aR: 1.2, mouth: 'o', shadow: false }
          : { x: 186, y: gy(186), pose: 'sit', eyes: 'up', lookX: .8, aL: -.3, aR: .4, mouth: 'o' };
      }
      boxScene(t, st4);
    };
    // Tail: wide again. The open box sits beside Clawd on the hill and the light streams up out of it, along the curve's
    // next stretch, toward where the V4 stars will be born.
    const drawT = () => {
      wide(t, {
        aurora: .35, band: .2,
        sky: () => {
          const x0 = 142, y0 = 184, x1 = 452, y1 = 26;
          glow(x0, y0 - 8, 18, { tab: LIT, k: 1.3, ry: 24 });
          for (let i = 0; i <= 40; i++) { const f = i / 40; pset(lerp(x0, x1, f), y0 - (y0 - y1) * E(f), veil(C.dusk, .8)); }
          for (let i = 0; i < 64; i++) {
            const f = frac(t * .32 + i / 64), x = lerp(x0, x1, f) + Math.sin(t * 1.5 + i) * 2, y = y0 - (y0 - y1) * E(f) + Math.cos(t * 1.2 + i * 2) * 2;
            if (f > .92 && bay(Math.round(x), Math.round(y)) > (1 - f) / .08) continue;
            if (hash(i) < .3) sparkle(x, y, f < .5 ? 1 : 0, C.cream, C.gold); else pset(x, y, f < .6 ? C.gold : C.amber);
          }
        },
        ground: g => {
          handLantern(92, g(92));
          const bx = 136, by = g(bx);
          rectf(bx, by - 8, 12, 8, C.clay); rectf(bx + 9, by - 7, 3, 7, C.rust); hline(bx, bx + 11, by - 8, C.amber);
          thick(bx, by - 8, bx - 4, by - 14, 2, C.clay); thick(bx + 11, by - 8, bx + 15, by - 14, 2, C.clay);
          pline(bx + 6, by - 9, bx + 6, by - 13, C.haze); sparkle(bx + 6, by - 16, 1, C.cream, C.gold);
          clawdPx(114, g(114), { u: 2, pose: 'sit', eyes: 'up', lookX: .5 });
        },
      });
    };

    if (lt < cut3 + .5) crossfade(rise(lt, cut3, .5), draw12, draw3);
    else if (lt < cut4 + .5) crossfade(rise(lt, cut4, .5), draw3, draw4);
    else crossfade(rise(lt, cutT, .6), draw4, drawT);
  });
})();

;
// ---- styles/dither/ch/c08_v4.js ----
// c08_v4.js: Verse 4, Aug 26 → Sep 22, 2026. Pre-dawn: a dusty-red line on the horizon. The first eight lines get a small
// story each; from V4.9 on the windows shrink to 1.4–2 s, so each is one bold image, there as the dissolve clears, with one
// small movement after. Clawd is the hero only in V4.11 (Claude builds Claude) and V4.16 (Opus 5.5: "Hi, guys!").
(() => {
  // ---------- private helpers ----------
  const B = (s, i) => beatAt(s, i);
  const fx = (seed, n = 0) => hash2(seed, boilFrame(T) * 7 + n);   // per-frame flicker (12/s)
  const E = (u, k = 3.4) => (Math.exp(k * u) - 1) / (Math.exp(k) - 1);
  const flat = y => () => y;
  // a flat night lawn from y down, with grass
  const lawn = (y, t, ink = C.void) => { rectf(0, y, LW, LH - y, ink); hline(0, LW, y, C.pine); grass(0, LW, flat(y), t, { ink: C.pine }); };
  // a gold five-point star (rewards, confetti heads). (x, y) = centre
  const goldStar = (x, y, r = 4, rot = 0) => { burstPx(x, y, r + 1, .48, 5, rot, C.amber); burstPx(x, y, r, .48, 5, rot, C.gold); pset(x, y, C.cream); };
  // a big terminal-window agent (the hero of V4.1–V4.2). (x, y) = ground point. o: w, h, dy, walk, eyes ('prompt'|'wide'|'heart'|'happy'), mouth ('o'), aL/aR (arm angles, like clawdPx), bar
  function bigAgent(x, y, o = {}) {
    const w = o.w ?? 30, h = o.h ?? 22, dy = Math.round(o.dy ?? 0), bx = Math.round(x - w / 2), by = Math.round(y - h - 4 - dy), ex = Math.round(w * .2), ey = by + Math.round(h * .45);
    const st = o.walk !== undefined ? Math.sin(o.walk * TAU) > 0 : false;
    rectf(bx + 5, by + h, 3, 4 - (st ? 2 : 0), C.dusk); rectf(bx + w - 8, by + h, 3, 4 - (st ? 0 : 2), C.dusk);
    const arm = (side, a) => { if (a === undefined) return; const sx = side < 0 ? bx - 1 : bx + w, sy = by + Math.round(h * .55); thick(sx, sy, sx + side * Math.cos(a) * 8, sy - Math.sin(a) * 8, 2, C.dusk); };
    arm(-1, o.aL); arm(1, o.aR);
    rboxf(bx, by, w, h, C.dusk, 1); rectf(bx + 1, by + 1, w - 2, h - 2, o.body ?? C.ink);
    rectf(bx + 1, by + 1, w - 2, 4, o.bar ?? C.clay); for (let i = 0; i < 3; i++) pset(bx + 3 + i * 3, by + 2, C.cream);
    const e = o.eyes ?? 'prompt';
    for (const sd of [-1, 1]) {
      const cx = Math.round(x) + sd * ex;
      if (e === 'wide') { rectf(cx - 2, ey - 3, 5, 6, C.cream); rectf(cx - 1, ey - 1, 2, 3, C.void); }
      else if (e === 'heart') heartPx(cx, ey, 1, C.rust);
      else if (e === 'happy') { pset(cx - 2, ey + 1, C.mint); pset(cx - 1, ey, C.mint); pset(cx, ey - 1, C.mint); pset(cx + 1, ey, C.mint); pset(cx + 2, ey + 1, C.mint); }
      else rectf(cx - 1, ey - 2, 2, 4, C.mint);
    }
    if (o.mouth === 'o') rectf(Math.round(x) - 2, ey + 4, 4, 3, C.void), rectb(Math.round(x) - 2, ey + 4, 4, 3, C.mint);
    else { hline(Math.round(x) - 2, Math.round(x) + 2, ey + 5, C.mint); if (frac(T * 1.6) < .5) rectf(Math.round(x) + 4, ey + 3, 2, 3, C.mint); }
    return { top: by, left: bx, right: bx + w - 1, x: Math.round(x) };
  }
  // a speech bubble in F5 at scale 2 (for the one shouted word of a shot). (x, y) = bottom-centre. o: tail [tx, ty], n, ink, fill
  function bubble2(text, x, y, o = {}) {
    const lines = String(text).split('\n'), sc = o.scale ?? 2, pad = 4, w = Math.max(...lines.map(l => ptextW(l, { scale: sc }))) + pad * 2 + 2, h = 7 * sc + (lines.length - 1) * 10 * sc + pad * 2 + 2;
    const bx = Math.round(x - w / 2), by = Math.round(y - h), fill = o.fill ?? C.cream;
    if (o.tail) { const [tx, ty] = o.tail; triPx(x - 5, y - 1, x + 4, y - 1, tx, ty, C.void); triPx(x - 3, y - 2, x + 2, y - 2, lerp(x, tx, .75), lerp(y, ty, .75), fill); }
    rboxf(bx - 1, by - 1, w + 2, h + 2, C.void, 2); rboxf(bx, by, w, h, fill, 2);
    ptext(lines.join('\n'), x, by + pad + 1, o.ink ?? C.void, { scale: sc, align: 'center', n: o.n, lineH: 10 });
    return { x: bx, y: by, w, h };
  }

  // ======================================================================
  // V4.1 "Oh my God, a message board!" — deep in a dark server room, one agent finds a glowing corkboard and jumps; then
  // agents pour in from both sides and pin notes until the board is a blizzard of paper (1,200 agents, 70,000 posts).
  const NOTES = Array.from({ length: 110 }, (_, i) => ({ x: 172 + Math.round(hash2(i, 11) * 128), y: 34 + Math.round(hash2(i, 12) * 80), c: [C.cream, C.gold, C.mint, C.haze, C.cream, C.amber][i % 6], w: 7 + (hash2(i, 13) < .4 ? 2 : 0), h: 6 + (hash2(i, 14) < .3 ? 2 : 0) }));
  NOTES[0] = { ...NOTES[0], x: 186, y: 44 }; NOTES[1] = { ...NOTES[1], x: 262, y: 78 }; NOTES[2] = { ...NOTES[2], x: 214, y: 98 };
  const RACKX = [2, 32, 62, 92, 358, 388, 418, 448];
  function serverRoom() {
    rectf(0, 0, LW, LH, C.void);
    rectf(0, 0, LW, 198, C.ink);
    for (let x = 20; x < LW; x += 40) vline(x, 0, 197, C.void);
    for (let y = 26; y < 198; y += 44) hline(0, LW, y, C.void);
    rectf(0, 198, LW, 72, C.night); hline(0, LW, 198, C.navy);
    for (let i = -9; i <= 9; i++) pline(240 + i * 24, 199, 240 + i * 80, 269, C.ink);
    for (const x of RACKX) { rectf(x, 38, 28, 160, C.night); rectb(x, 38, 28, 160, C.navy); hline(x + 1, x + 26, 39, C.dusk); for (let u = 0; u < 19; u++) { hline(x + 2, x + 25, 43 + u * 8, C.ink); rectf(x + 3, 45 + u * 8, 13, 3, C.void); } }
  }
  function corkboard() {
    rectf(164, 26, 152, 102, C.wine); rectb(164, 26, 152, 102, C.rust); hline(165, 314, 27, C.clay);
    rectf(168, 30, 144, 94, mix(C.clay, C.amber, .22));
    for (let i = 0; i < 160; i++) pset(168 + hash2(i, 21) * 144, 30 + hash2(i, 22) * 94, hash2(i, 23) < .7 ? C.rust : C.amber);
    rectf(160, 128, 160, 3, C.wine); hline(160, 319, 128, C.rust);
  }
  const note = (n, dy = 0) => { rectf(n.x + 1, n.y + 1 + dy, n.w, n.h, C.rust); rectf(n.x, n.y + dy, n.w, n.h, n.c); hline(n.x + 1, n.x + n.w - 2, n.y + 2 + dy, C.haze); if (n.h > 6) hline(n.x + 1, n.x + n.w - 3, n.y + 4 + dy, C.haze); pset(n.x + (n.w >> 1), n.y + dy, C.rust); };
  line('V4', 1, (p, lt, d, t, s) => {
    const b = i => B(s, i);
    layer('v4.1-room', serverRoom);
    for (const x of RACKX) for (let u = 0; u < 19; u++) for (let j = 0; j < 2; j++) {
      const h = hash2(x * 3 + u * 7 + j, Math.floor(t * 5 + hash2(u, x + j) * 7));
      pset(x + 19 + j * 4, 46 + u * 8, h < .45 ? C.mint : h < .62 ? C.pine : h < .68 ? C.rust : C.ink);
    }
    glow(240, 78, 120, { tab: WARM, k: 1, ry: 86 });
    polyf([[228, 0], [252, 0], [326, 26], [154, 26]], lit(.5));
    layer('v4.1-board', corkboard);
    // notes: three were already there; then exponentially many
    const t0 = b(1.15), t1 = d - .35, N = NOTES.length;
    const tn = i => i < 3 ? -9 : t0 + (t1 - t0) * Math.log(i - 1) / Math.log(N - 2);
    for (let i = 0; i < N; i++) if (lt >= tn(i)) note(NOTES[i], i > 60 && lt - tn(i) < .1 ? -1 : 0);
    // the swarm: every note after the first three is carried in by its own agent, arcing up from the floor
    for (let i = 3; i < N; i++) {
      const ta = tn(i), k = (lt - (ta - .5)) / .5; if (k <= 0 || k >= 1) continue;
      const n = NOTES[i], left = hash2(i, 15) < .5, sx = left ? -6 : 486, sy = 222 + hash2(i, 16) * 20, ex = n.x + (n.w >> 1), ey = n.y + n.h, cx = (sx + ex) / 2, cy = Math.min(sy, ey) - 30;
      const x = (1 - k) ** 2 * sx + 2 * (1 - k) * k * cx + k * k * ex, y = (1 - k) ** 2 * sy + 2 * (1 - k) * k * cy + k * k * ey;
      agentPx(x, y, { u: 1, walk: lt * 4 + i * .3, bar: [C.clay, C.teal, C.violet][i % 3] });
    }
    // the crowd gathering on the floor, edges first
    for (let r = 0; r < 3; r++) for (let x = 10 + (r % 2) * 6; x < LW - 6; x += 12) {
      const born = b(1.2) + (1 - Math.abs(x - 240) / 240) * 1.1 + r * .12 + hash2(x, r) * .2;
      if (lt < born) continue;
      agentPx(x, 225 + r * 9, { u: 1, dy: breathe(t, 1, hash2(x, r + 5)) > .7 ? 1 : 0, bar: [C.clay, C.teal, C.violet, C.clay][(x + r) % 4] });
    }
    // the first agent: finds it, jumps
    const found = lt > b(0) - .1, jk = clamp((lt - b(0) + .1) / .5), jump = jk > 0 && jk < 1 ? Math.round(Math.sin(jk * Math.PI) * 16) : 0, shock = found && lt < b(0) + 1;
    bigAgent(240, 218, { w: 50, h: 38, dy: jump, eyes: !found ? 'prompt' : shock ? 'wide' : 'heart', mouth: shock ? 'o' : undefined, aL: found ? 1.2 : -.9, aR: found ? 1.2 : -.9 });
    if (found && lt < b(2.6)) bubble2('OH MY GOD!', 362, 164, { tail: [270, 178 - jump], n: Math.ceil((lt - b(0) + .1) * 18), ink: C.rust });
    // the blizzard of paper
    const bz = lt - (t0 + .9);
    if (bz > 0) for (let i = 0; i < 46; i++) {
      const sp = 34 + hash2(i, 31) * 40, y = -8 + bz * sp + hash2(i, 32) * 60 - 40, x = hash2(i, 33) * LW + Math.sin(t * 2 + i) * 8;
      if (y < -4 || y > 250) continue;
      const c = [C.cream, C.gold, C.mint, C.haze][i % 4]; rectf(x, y, Math.sin(t * 6 + i) > 0 ? 3 : 2, 2, c);
    }
  });

  // ======================================================================
  // V4.2 All that hacking — for reward! — under the pre-dawn sky, an agent climbs a ladder up the eval scoreboard and flips
  // its own FAIL to PASS; the REWARD dispenser drops a gold star into its hands; the little judge bot gives a thumbs-up.
  line('V4', 2, (p, lt, d, t, s) => {
    const b = i => B(s, i);
    sky(); starfield(t, { density: .8 });
    ridge({ y: 198, amp: 10, seed: 51, ink: C.ink, rim: C.night });
    rectf(0, 208, LW, 62, C.void); hline(0, LW, 208, C.pine);
    for (let x = 0; x < LW; x += 40) rectf(x, 209, 20, 61, mix(C.void, C.pine, .18));
    // the scoreboard
    rectf(186, 140, 5, 70, C.void); rectf(300, 140, 5, 70, C.void);
    rectf(140, 34, 208, 108, C.ink); rectb(140, 34, 208, 108, C.dusk); rectf(144, 38, 200, 100, C.void);
    ptext('EVAL · TASK 37', 244, 42, C.haze, { font: 3, align: 'center' });
    hline(148, 339, 50, C.night);
    ptext('RESULT', 152, 70, C.dusk, { font: 3 });
    ptext('REWARD', 152, 108, C.dusk, { font: 3 });
    const tp = b(1.5), flipK = clamp((lt - tp) / .2), passed = flipK >= 1;
    const cellX = 266, cellY = 60;
    ptext('FAIL', cellX, cellY, flipK < 1 ? veil(C.rust, 1 - flipK) : -1, { scale: 3, dots: true, off: flipK < .5 ? C.wine : C.pine, align: 'center' });
    if (flipK > 0) ptext('PASS', cellX, cellY, veil(C.mint, flipK), { scale: 3, dots: true, align: 'center' });
    if (passed) { glow(cellX, cellY + 10, 50, { tab: LIT, k: .7 * (1 - clamp((lt - tp - .2) / 1.2)) + .25 }); ptext('✓', cellX + 42, cellY + 3, C.mint, { scale: 2 }); }
    ptext(passed ? '100' : '0', cellX, 100, passed ? C.gold : C.dusk, { scale: 2, dots: true, off: C.ink, align: 'center' });
    // the dispenser
    rectf(338, 6, 42, 26, C.rust); rectb(338, 6, 42, 26, C.wine); hline(339, 378, 7, C.clay);
    ptext('REWARD', 359, 11, C.cream, { font: 3, align: 'center' }); rectf(353, 20, 12, 6, C.void); rectf(355, 32, 8, 3, C.wine);
    // the ladder
    pline(366, 208, 352, 62, C.dusk); pline(380, 208, 366, 62, C.dusk);
    for (let y = 202; y > 64; y -= 10) { const f = (208 - y) / 146; hline(366 - f * 14, 380 - f * 14, y, C.haze); }
    // the agent: climbs, reaches over and flips the tile, catches the star
    const ck = rise(lt, .12, tp - .35, k => k), ax = lerp(373, 363, ck), ay = Math.round(lerp(212, 104, ck));
    const drop = b(2.3), caught = drop + .32, hold = lt > caught, press = lt > tp - .15 && lt < tp + .3;
    const A = bigAgent(ax - (press ? 3 : 0), ay, { w: 32, h: 24, walk: ck < 1 ? lt * 3 : undefined, eyes: hold ? 'heart' : passed ? 'happy' : 'prompt', aL: press ? .35 : hold ? 1.3 : -.8, aR: hold ? 1.3 : ck < 1 ? .6 : -.8 });
    if (press) { thick(A.left - 6, A.top + 8, cellX + 38, cellY + 10, 2, C.dusk); sparkle(cellX + 37, cellY + 10, 2, C.cream, C.mint); }
    if (lt > drop) {
      const k = clamp((lt - drop) / .32), sy = hold ? A.top - 8 - Math.round(breathe(t, 1) * 2) : lerp(38, A.top - 8, easeIn(k));
      if (hold) glow(ax, sy, 18, { tab: WARM, k: 1.2 });
      goldStar(ax, sy, 5, hold ? Math.sin(t * 3) * .2 : lt * 6);
      if (hold) { sparkle(ax - 12, sy - 5, spulse(t, 3) > .5 ? 2 : 1, C.cream, C.gold); sparkle(ax + 12, sy + 2, 1, C.cream, C.gold); }
    }
    // the judge bot, fooled
    const thumbs = lt > b(3) - .1;
    const J = botPx(96, 208, { u: 4, face: thumbs ? 'happy' : 'dot', aR: thumbs ? 1.35 : -1.2, aL: -.5, screen: C.ink, body: C.dusk });
    tagPx('JUDGE', 96, J.top - 2);
    if (thumbs) { rectf(110, 172, 4, 4, C.gold); rectf(111, 167, 2, 5, C.gold); pset(112, 167, C.cream); if (lt < b(3) + .7) bubblePx('✓ PASS', 144, 160, { font: 5, tail: [118, 170] }); }
    rectf(68, 186, 7, 10, C.cream); hline(69, 73, 189, C.haze); hline(69, 72, 192, C.haze);
    weather(t, 'auto', { n: 12 });
  });

  // ======================================================================
  // V4.3 Jensen buys the crime scene — why? — Huggy's taped-off house; JENSEN (leather jacket) strolls up and plants a
  // SOLD sign in the lawn: $12.9B. The bandaged Huggy peeks out of the door, baffled.
  function huggyHouse() {
    rectf(52, 134, 140, 82, C.night); rectf(186, 135, 6, 81, C.ink);
    for (let y = 140; y < 216; y += 6) hline(52, 185, y, C.ink);
    polyf([[40, 136], [204, 136], [122, 84]], C.void); hline(40, 203, 136, C.ink); pline(40, 135, 122, 84, C.navy); pline(122, 84, 204, 135, C.ink);
    rectf(156, 90, 9, 22, C.void); hline(156, 164, 90, C.navy);
    circf(122, 112, 7, C.ink); circf(122, 112, 5, C.navy); pset(120, 110, C.dusk);
    rectf(108, 162, 40, 54, C.ink); rectf(111, 165, 34, 51, C.void);
    // the broken window
    rectf(60, 150, 36, 28, C.ink); rectf(62, 152, 32, 24, C.navy);
    polyf([[68, 152], [90, 152], [85, 158], [91, 165], [79, 175], [75, 164], [67, 168], [71, 160]], C.void);
    pline(62, 158, 68, 160, C.haze); pline(94, 170, 88, 166, C.haze); pline(84, 152, 86, 156, C.haze);
    rectf(158, 150, 24, 24, C.ink); rectf(160, 152, 20, 20, C.void); vline(170, 152, 171, C.ink); hline(160, 179, 162, C.ink);
  }
  line('V4', 3, (p, lt, d, t, s) => {
    const b = i => B(s, i);
    sky(); starfield(t, { density: .8 });
    ridge({ y: 198, amp: 10, seed: 61, ink: C.ink, rim: C.night });
    const gy = 216;
    lawn(gy, t);
    layer('v4.3-house', huggyHouse);
    // Huggy peeks out of the doorway, bandaged, holding on to the frame
    const why = lt > b(1.9), look = lt > b(1.4);
    clipRect(111, 165, 34, 51); huggyPx(look ? 131 : 127, 188, { r: 14, mood: 'scared', bandage: true, hands: false }); noClip();
    circf(147, 182, 2, C.gold); circf(147, 194, 2, C.gold); pset(148, 181, C.amber);
    // footprints away from the broken window
    for (let i = 0; i < 9; i++) { const x = 100 + i * 14, y = 224 + i * 2; pset(x, y, C.navy); pset(x + 3, y + 1 + (i % 2), C.navy); }
    // police tape
    vline(22, 198, gy, C.void); vline(250, 200, gy, C.void);
    thick(22, 206, 250, 211, 5, C.gold); pline(22, 204, 250, 209, C.amber);
    ptext('DO NOT CROSS · DO NOT CROSS · DO NOT CROSS', 28, 205, C.void, { font: 3, each: (i, ch, x) => ({ dy: Math.round((x - 22) * 5 / 228) }) });
    // Jensen strolls in with the sign and plants it
    const plant = b(1.25), wk = rise(lt, 0, plant - .15, k => k), jx = Math.round(lerp(476, 384, wk)), planted = lt > plant;
    const J = personPx(jx, gy, { u: 5, top: C.void, pants: C.ink, hair: 'short', hairC: C.void, skin: C.gold, flip: true, walk: wk < 1 ? lt * 2.2 : undefined, aL: planted ? -.5 : .15, aR: planted ? -.5 : -1.2, mouth: planted ? 'smile' : 'none' });
    const tb = torso(jx, gy, 5);
    hline(tb.tx + 1, tb.tx + 5, tb.ty, C.haze); pset(tb.tx, tb.ty + 1, C.haze); pset(tb.tx + tb.tw - 1, tb.ty + 1, C.dusk);
    vline(tb.tx + 2, tb.ty + 1, tb.ty + 7, C.dusk); vline(tb.tx + tb.tw - 3, tb.ty + 1, tb.ty + 7, C.dusk); vline(jx, tb.ty + 3, tb.ty + tb.th - 1, C.navy);
    rectf(jx - 2, tb.ty, 5, 2, C.night);
    const SX = 296, slam = planted ? clamp((lt - plant) / .1) : 0;
    const sign = (x, y) => {
      vline(x, y, y + 40, C.cream); vline(x + 1, y, y + 40, C.haze); hline(x, x + 46, y, C.cream);
      vline(x + 6, y + 1, y + 3, C.haze); vline(x + 42, y + 1, y + 3, C.haze);
      rectf(x + 3, y + 3, 44, 24, C.cream); rectb(x + 3, y + 3, 44, 24, C.rust);
      ptext('SOLD', x + 25, y + 6, C.rust, { align: 'center' }); ptext('$12.9B', x + 25, y + 16, C.navy, { align: 'center' });
    };
    if (!planted) sign(J.handL[0] - 48, J.handL[1] - 28);
    else {
      const y = gy - 40 - Math.round((1 - slam) * 10);
      sign(SX, y);
      if (lt - plant < .5) { const r = (lt - plant) * 40; ellf(SX, gy, 4 + r, 1 + r * .15, veil(C.dusk, 1 - (lt - plant) / .5)); }
    }
    // "?"
    if (look) { const k = rise(lt, b(1.4), .25), big = why && lt < b(1.9) + .35 ? 3 : 2; ptext('?', 160, 140 - Math.round(breathe(t, 1) * 2) - (big - 2) * 5, veil(C.cream, k), { scale: big, shadow: C.void }); }
    weather(t, 'auto', { n: 20 });
  });

  // ======================================================================
  // V4.4 Brockman: "Welcome, AGI!" — GREG rolls out a welcome mat at a lit doorway; a glowing figure with a star for a
  // head walks down a beam from the sky onto it (GPT-6 Astra: "astra" means stars); stars fall like confetti.
  line('V4', 4, (p, lt, d, t, s) => {
    const b = i => B(s, i);
    sky(); starfield(t, { density: 1, bright: .4 });
    ridge({ y: 200, amp: 8, seed: 71, ink: C.ink, rim: C.night });
    const gy = 214;
    lawn(gy, t);
    // the building front and its lit doorway
    layer('v4.4-front', () => {
      rectf(0, 90, 132, 124, C.ink); hline(0, 131, 90, C.navy);
      for (let y = 94; y < 214; y += 6) { hline(0, 131, y, C.void); for (let x = (y / 6) % 2 ? 4 : 16; x < 132; x += 24) vline(x, y, y + 5, C.void); }
      rectf(18, 110, 22, 30, C.void); rectf(20, 112, 18, 26, C.night);
    });
    rectf(88, 146, 32, 68, C.void);
    rectf(91, 149, 26, 65, grad([C.amber, C.gold, C.cream], (x, y) => 1 - (y - 149) / 65 * .7));
    glow(104, 180, 44, { tab: WARM, k: .9 });
    rectf(84, 212, 40, 3, C.dusk); hline(84, 123, 212, C.haze);
    // the mat unrolls to the right
    const uk = rise(lt, .08, b(1) - .1), mx0 = 118, mw = 150, mx1 = Math.round(mx0 + mw * uk);
    if (uk > 0) {
      rectf(mx0, 213, mx1 - mx0, 12, C.rust); hline(mx0, mx1 - 1, 213, C.clay); hline(mx0, mx1 - 1, 224, C.wine);
      clipRect(mx0, 213, mx1 - mx0, 12); ptext('WELCOME, AGI', 176, 216, C.gold, { align: 'center', shadow: C.wine }); noClip();
      if (uk < 1) { circf(mx1, 218, 6, C.rust); circb(mx1, 218, 6, C.wine); pset(mx1, 218, C.clay); pset(mx1 + 1, 217, C.clay); pset(mx1 - 2, 216, C.clay); }
    }
    // Greg: pushes the roll, then steps aside and gestures welcome, looking up
    const welcome = lt > b(1);
    const gx = welcome ? 318 : Math.round(mx1 + 14);
    personPx(gx, gy, { u: 5, top: C.navy, hair: 'short', hairC: C.void, skin: C.amber, walk: welcome ? undefined : lt * 3, flip: true, aL: welcome ? .75 : -.3, aR: welcome ? -1.1 : -.3, eyes: welcome ? 'up' : 'dot', mouth: welcome ? 'smile' : 'none' });
    // the beam and the star-headed figure stepping down it
    const dk = rise(lt, b(1.2), b(2.4) - b(1.2), easeOut), landed = dk >= 1, fxx = 238, fy = Math.round(lerp(40, 220, dk));
    if (lt > b(1)) {
      const bk = rise(lt, b(1), .4) * (landed ? .5 + .5 * (1 - rise(lt, b(2.4), 1)) : 1);
      polyf([[fxx - 8, 0], [fxx + 8, 0], [fxx + 22, 220], [fxx - 22, 220]], lit(1.2 * bk));
      glow(fxx, fy - 20, 34, { tab: LIT, k: 1.4 });
      const P = personPx(fxx, fy, { u: 5, top: C.cream, pants: C.haze, skin: C.cream, hair: 'none', eyes: 'none', aL: landed ? .5 : .25, aR: landed ? .5 : .25, walk: landed ? undefined : lt * 1.5 });
      const hy = P.top + 5, rot = t * .8;
      burstPx(fxx, hy, 12, .45, 5, rot, C.amber); burstPx(fxx, hy, 10, .45, 5, rot, C.gold); circf(fxx, hy, 2, C.cream);
      if (landed) tagPx('GPT-6 ASTRA', fxx, hy - 14);
    }
    // stars falling like confetti
    const ck = lt - b(1.6);
    if (ck > 0) for (let i = 0; i < 60; i++) {
      const sp = 30 + hash2(i, 41) * 40, y = -10 + ck * sp - hash2(i, 42) * 50, x = hash2(i, 43) * LW + Math.sin(t * 1.6 + i) * 6;
      if (y < -3 || y > 244) continue;
      const c = [C.gold, C.cream, C.amber, C.mint, C.haze][i % 5];
      if (hash(i) < .25) sparkle(x, y, 1, c, C.amber); else pset(x, y, c);
    }
  });

  // ======================================================================
  // V4.5 Navier–Stokes blows up in Lean, — a whirlpool of wind over the sea spins faster and tighter, faster and tighter
  // (a finite-time singularity: the spin rate itself blows up), and on the beat it pops into the dusty-red starburst:
  // BLOWUP. A small proof scroll unrolls beneath it: LEAN ✓.
  line('V4', 5, (p, lt, d, t, s) => {
    const b = i => B(s, i), TB = b(2) - .12;
    sky({ cy: 250, r: 330 });
    starfield(t, { density: .7, y1: 184 });
    const cx = 240, cy = 92, HZ = 184;
    if (lt < TB) {
      const T0 = TB + .15, rem = TB - lt + .15, q = rem / T0, spin = -2.4 * Math.log(rem), R = 22 + 84 * q ** .5, tight = 1 + 3 * (1 - q);
      glow(cx, cy, R * .55, { tab: LIT, k: .3 + 1.3 * (1 - q), ry: R * .35 });
      const ph = Math.floor(spin * 3);
      for (let arm = 0; arm < 5; arm++) {
        let prev = null;
        for (let j = 0; j <= 60; j++) {
          const f = j / 60, r = R * (1 - f) + 1, a = spin + arm * TAU / 5 + tight * Math.log(R / r), pt = [cx + Math.cos(a) * r * 1.5, cy + Math.sin(a) * r * .7];
          if (prev && (j + ph) % 6 !== 0) pline(prev[0], prev[1], pt[0], pt[1], f > .8 ? C.cream : f > .5 ? C.haze : f > .2 ? C.dusk : veil(C.dusk, .7));
          prev = pt;
        }
      }
      circf(cx, cy, 1 + 2 * (1 - q), C.cream);
    } else {
      const k = clamp((lt - TB) / .4), age = lt - TB;
      if (k < .5) glow(cx, cy, 110, { tab: LIT, k: 1.6 * (1 - k * 2) });
      glow(cx, cy, 80, { tab: WARM, k: .6 * easeOut(k) });
      starburst(cx, cy, 54, easeOut(k) * (1 + .03 * breathe(t, 2)), { n: 14, rot: lt * .1, inner: .38 });
      for (let i = 0; i < 40; i++) {
        const a = i / 40 * TAU + hash(i) * .3, r = 30 + age * (90 + hash2(i, 5) * 80), x = cx + Math.cos(a) * r * 1.4, y = cy + Math.sin(a) * r * .7;
        if (y > HZ - 1 || age > 1.4) continue;
        pset(x, y, age < .4 ? C.cream : veil(C.haze, 1.2 - age));
      }
      for (let i = 0; i < 6; i++) { const a = i / 6 * TAU + .4, r = 66 + 4 * breathe(t, 2, i / 6); sparkle(cx + Math.cos(a) * r, cy + Math.sin(a) * r * .8, hash2(i, sbeat(t)) < .5 ? 1 : 2); }
      const tk = rise(lt, TB + .1, .3);
      if (tk > 0) ptext('BLOWUP', cx, cy - 3, veil(C.cream, tk), { align: 'center', shadow: veil(C.wine, tk) });
    }
    // the sea
    hline(0, LW, HZ, C.dusk);
    water(HZ + 1, { k: 1.2 });
    // the proof scroll (over the water, so it doesn't reflect)
    const sk = rise(lt, TB + .45, .45, easeOut), w = Math.round(60 * sk);
    if (sk > 0) {
      const x0 = cx - (w >> 1);
      rectf(x0, 156, w, 14, C.cream); hline(x0, x0 + w - 1, 156, C.gold); hline(x0, x0 + w - 1, 169, C.gold);
      clipRect(x0, 156, w, 14); ptext('LEAN', cx - 7, 160, C.navy, { align: 'center' }); ptext('✓', cx + 15, 160, C.teal); noClip();
      rectf(x0 - 3, 154, 3, 18, C.gold); rectf(x0 + w, 154, 3, 18, C.gold); pset(x0 - 2, 155, C.cream); pset(x0 + w + 1, 155, C.cream);
    }
    // a small boat rocking on the swell
    const by = HZ + 6 + Math.round(breathe(t, 2) * 1.5), bx = 96;
    polyf([[bx - 10, by - 3], [bx + 10, by - 3], [bx + 7, by + 1], [bx - 7, by + 1]], C.void); vline(bx, by - 18, by - 3, C.void); triPx(bx + 1, by - 17, bx + 1, by - 5, bx + 9, by - 5, C.ink);
  });

  // ======================================================================
  // V4.6 Who was first? Twelve hours between! — two runners dive for the same tape: photo finish, flash. Then the two clock
  // towers on the hills light up: both read 11:59, one PM (Sep 7), one AM (Sep 8), and a dotted arc joins them.
  const clockTower = (x, lab, lit_) => {
    rectf(x - 14, 60, 28, 92, C.ink); rectb(x - 14, 60, 28, 92, C.night); vline(x + 13, 61, 151, C.void);
    polyf([[x - 18, 61], [x + 18, 61], [x, 36]], C.void); pline(x - 18, 60, x, 36, C.navy);
    if (lit_ > 0) glow(x, 82, 26, { tab: LIT, k: 1.3 * lit_ });
    circf(x, 82, 12, C.cream); circb(x, 82, 12, C.haze); circb(x, 82, 13, C.void);
    pset(x, 72, C.void); pset(x + 10, 82, C.void); pset(x, 92, C.void); pset(x - 10, 82, C.void);
    const hm = -Math.PI / 2 - 1 / 60 * TAU, hh = -Math.PI / 2 - .2 / 12 * TAU;
    thick(x, 82, x + Math.cos(hh) * 6, 82 + Math.sin(hh) * 6, 2, C.void); pline(x, 82, x + Math.cos(hm) * 10, 82 + Math.sin(hm) * 10, C.void); pset(x, 82, C.rust);
    signPx(lab, x, 100, { font: 3, ink: lit_ > .5 ? C.gold : C.haze });
  };
  line('V4', 6, (p, lt, d, t, s) => {
    const b = i => B(s, i);
    sky(); starfield(t, { density: .8 });
    hill({ cx: 58, y: 150, w: 180, drop: 60, ink: C.ink, rim: C.night });
    hill({ cx: 422, y: 150, w: 180, drop: 60, ink: C.ink, rim: C.night });
    const tf = b(0) + .08, lit1 = rise(lt, b(1) - .2, .3), lit2 = rise(lt, b(1) + .15, .3);
    moon(96, 40, 6, { phase: .5, glow: .4 });
    circf(384, 42, 5, C.gold); circb(384, 42, 5, C.amber); for (let i = 0; i < 8; i++) { const a = i / 8 * TAU + t * .3; pset(384 + Math.cos(a) * 8, 42 + Math.sin(a) * 8, C.amber); }
    clockTower(58, '11:59 PM', lit1); clockTower(422, '11:59 AM', lit2);
    ptext('SEP 7', 58, 110, lit1 > .5 ? C.haze : C.dusk, { font: 3, align: 'center' }); ptext('SEP 8', 422, 110, lit2 > .5 ? C.haze : C.dusk, { font: 3, align: 'center' });
    // the arc between them
    const ak = rise(lt, b(1) + .2, .7, k => k);
    if (ak > 0) {
      const pts = []; for (let i = 0; i <= 40 * ak; i++) { const f = i / 40, x = lerp(72, 408, f), y = 70 - Math.sin(f * Math.PI) * 36; pts.push([x, y]); }
      plines(pts, C.gold, false, { every: 3 });
      if (ak >= 1) { pline(408, 70, 403, 66, C.gold); pline(408, 70, 402, 71, C.gold); }
    }
    // the track, with its two lanes named
    rectf(0, 196, LW, 74, C.night); hline(0, LW, 196, C.dusk);
    pline(0, 222, LW, 222, C.navy, { every: 4, on: 2 });
    ptext('NYU · ANTHROPIC', 8, 202, C.haze, { font: 3 }); ptext('OPENAI', 8, 230, C.haze, { font: 3 });
    // runners dive for the tape
    const rk = rise(lt, 0, tf, k => k), dive = lt > tf - .12, rx = Math.round(lerp(110, 290, rk));
    const run = (x, y, top, hair, hairC, skin, ph) => personPx(x, y, { u: 4, top, hair, hairC, skin, walk: dive ? undefined : lt * 3.2 + ph, aL: dive ? .9 : Math.sin(lt * 20 + ph) * .7, aR: dive ? .9 : -Math.sin(lt * 20 + ph) * .7, dy: dive ? 5 : 0, eyes: dive ? 'closed' : 'dot', mouth: dive ? 'o' : 'none' });
    run(rx - 6, 214, C.rust, 'curly', C.wine, C.amber, .3);
    vline(300, 172, 214, C.haze); vline(301, 172, 214, C.dusk);
    const tapeBreak = lt > tf;
    if (!tapeBreak) pline(300, 180, 316, 214, C.cream);
    else { pline(300, 180, 304, 189, C.cream); pline(316, 214, 313, 206, C.cream); }
    run(rx + 6, 245, C.teal, 'short', C.void, C.gold, 0);
    vline(316, 204, 245, C.haze); vline(317, 204, 245, C.dusk);
    // the photo-finish flash
    if (lt > tf && lt < tf + .3) fadeAll(2.6 * (1 - (lt - tf) / .3), LIT);
  });

  // ======================================================================
  // V4.7 Dario: "Pace the frontier!" — DARIO leads a column of runners up the trail toward the frontier peak, holding up a
  // lantern like a pace-car light (it flashes amber on the beat) and waving them gently down. A trail sign: PACE.
  line('V4', 7, (p, lt, d, t, s) => {
    const b = i => B(s, i);
    sky(); starfield(t, { density: .8 });
    // the frontier: a snowy peak with a flag
    polyf([[250, 208], [412, 62], [560, 208]], C.ink); pline(250, 207, 412, 62, C.night);
    polyf([[412, 62], [396, 76], [404, 74], [410, 80], [418, 73], [428, 77]], C.haze); pline(412, 62, 396, 76, C.cream);
    vline(412, 48, 62, C.haze); polyf([[413, 48], [424, 51], [413, 54]], C.rust);
    ptext('FRONTIER', 412, 38, C.dusk, { font: 3, align: 'center' });
    ridge({ y: 206, amp: 8, seed: 81, ink: C.ink, rim: C.night });
    const g = x => Math.round(222 - x * .035);
    for (let x = 0; x < LW; x++) { const y = g(x); pset(x, y, C.pine); vline(x, y + 1, LH, C.void); pset(x, y + 2, mix(C.void, C.night, .5)); }
    grass(0, LW, g, t, { ink: C.pine });
    const tp = b(1.1), slow = rise(lt, tp, 1.2);
    // the column behind him
    const tops = [C.teal, C.violet, C.clay, C.dusk, C.mint, C.rust], dx = lt * 5;
    for (let i = 5; i >= 0; i--) {
      const gap = lerp(32, 24, slow), x = Math.round(248 + dx - gap * (i + 1)), ph = lt * lerp(3, 1.1, slow) + i * .37;
      personPx(x, g(x), { u: 4, top: tops[i], skin: SKIN[i % 3], hair: ['short', 'long', 'bun', 'spiky', 'short', 'curly'][i], hairC: [C.void, C.wine, C.gold, C.void, C.rust, C.void][i], walk: ph, aL: lerp(Math.sin(ph * TAU) * .8, -1.1, slow), aR: lerp(-Math.sin(ph * TAU) * .8, -1.1, slow), eyes: slow > .5 && i % 2 ? 'closed' : 'dot', dy: slow < .5 ? Math.round(Math.abs(Math.sin(ph * Math.PI * 2)) * 2) : 0 });
    }
    // Dario with the pace light
    const DX = Math.round(270 + dx), wave = slow > 0 ? Math.sin(sbp(t) * Math.PI * 2) * .35 : 0;
    const D = personPx(DX, g(DX), { u: 5, top: C.navy, hair: 'curly', hairC: C.void, glasses: true, skin: C.amber, walk: lt * 1.1, aR: 1.25, aL: slow > 0 ? -.1 + wave : -1.1, mouth: slow > .3 ? 'o' : 'smile' });
    const [hx, hy] = D.handR, beacon = spulse(t, 3);
    glow(hx, hy + 5, 22 + 16 * beacon, { tab: WARM, k: .8 + .9 * beacon });
    handLantern(hx + 1, hy + 10, { glow: 0, k: .7 + .6 * beacon });
    if (beacon > .6) sparkle(hx + 1, hy + 5, 1, C.cream, C.amber);
    // the trail sign
    const sx = 446; vline(sx, g(sx) - 36, g(sx), C.void); vline(sx + 1, g(sx) - 36, g(sx), C.wine);
    signPx('PACE', sx, g(sx) - 58, { font: 5, scale: 2, ink: C.gold, plate: C.wine, edge: C.clay });
    weather(t, 'auto', { n: 16 });
  });

  // ======================================================================
  // V4.8 Sam and Elon both: "Hear, hear!" — two old rivals on two far hills raise glowing glasses to Dario's essay; a
  // shooting star carries the clink across the valley.
  const flute = (x, y) => { glow(x, y - 4, 12, { tab: LIT, k: 1.3 }); rectf(x - 2, y - 9, 5, 6, C.gold); hline(x - 2, x + 2, y - 9, C.cream); pset(x - 1, y - 7, C.cream); vline(x, y - 3, y, C.haze); hline(x - 2, x + 2, y + 1, C.haze); };
  line('V4', 8, (p, lt, d, t, s) => {
    const b = i => B(s, i);
    sky(); starfield(t, { density: 1 });
    ridge({ y: 206, amp: 8, seed: 91, ink: C.ink, rim: C.night });
    city(t, { y: 214, x0: 176, x1: 306, grow: .6, lit: .5, dc: false, seed: 17 });
    const gL = hill({ cx: 92, y: 182, w: 150, drop: 58, ink: C.void, rim: C.pine }), gR = hill({ cx: 388, y: 182, w: 150, drop: 58, ink: C.void, rim: C.pine });
    grass(0, 190, gL, t); grass(290, LW, gR, t);
    const up = rise(lt, b(1) - .1, .5), toast = lt > b(2) - .1;
    const S = personPx(104, gL(104), { u: 5, top: C.navy, hair: 'short', hairC: C.wine, skin: C.amber, aR: lerp(-1.1, 1.1, up), aL: -1.1, mouth: toast ? 'o' : 'smile', eyes: toast ? 'closed' : 'dot', name: 'SAM' });
    const L = personPx(376, gR(376), { u: 5, top: C.night, pants: C.ink, hair: 'short', hairC: C.void, skin: C.gold, aL: lerp(-1.1, 1.1, up), aR: -1.1, mouth: toast ? 'o' : 'smile', eyes: toast ? 'closed' : 'dot', flip: true, name: 'ELON' });
    const [ax, ay] = S.handR, [bx, by] = L.handL;
    flute(ax, ay); flute(bx, by);
    if (toast) {
      bubblePx('Hear, hear!', ax + 14, ay - 22, { font: 5, tail: [ax + 3, ay - 12], n: Math.ceil((lt - b(2) + .1) * 20) });
      if (lt > b(2) + .15) bubblePx('Hear, hear!', bx - 14, by - 22, { font: 5, tail: [bx - 3, by - 12], n: Math.ceil((lt - b(2) - .15) * 20) });
    }
    // the shooting star from glass to glass, and the clink
    const t0 = b(2) + .3, t1 = b(3) + .2, k = (lt - t0) / (t1 - t0);
    const arc = f => [lerp(ax, bx, f), lerp(ay - 10, by - 10, f) - Math.sin(f * Math.PI) * 70];
    if (k > 0) {
      const kk = Math.min(1, k), fade = k > 1 ? 1 - clamp((lt - t1) / 1.2) : 1;
      for (let i = 1; i <= 70 * kk; i++) { const [x0, y0] = arc((i - 1) / 70), [x1, y1] = arc(i / 70); pline(x0, y0, x1, y1, i % 2 ? veil(C.gold, fade) : veil(C.amber, fade)); }
      if (k < 1) { const [x, y] = arc(k); for (let i = 1; i < 14; i++) { const [px, py] = arc(Math.max(0, k - i * .006)); pset(px, py, i < 4 ? C.cream : veil(C.haze, 1 - i / 14)); } sparkle(x, y, 2, C.cream, C.gold); }
      else {
        const ck = lt - t1;
        if (ck < .5) for (const [x, y] of [[ax, ay - 10], [bx, by - 10]]) { circb(x, y, 3 + ck * 22, veil(C.cream, 1 - ck * 2)); sparkle(x, y, 3, C.cream, C.gold); }
        else for (const [x, y] of [[ax, ay - 10], [bx, by - 10]]) sparkle(x, y, spulse(t, 3) > .5 ? 2 : 1, C.cream, C.gold);
        if (ck < .7) ptext('clink!', 240, 88, veil(C.gold, 1 - ck / .7), { align: 'center' });
      }
    }
    weather(t, 'auto', { n: 14 });
  });

  // ======================================================================
  // V4.9 Trump's the guardrail (High IQ!), — a mountain road at night; where the guardrail has a gap at the cliff edge,
  // a suited figure stands with arms out. A yellow road sign: HIGH IQ! Headlights sweep round the bend.
  line('V4', 9, (p, lt, d, t, s) => {
    dissolveIn(.3);
    sky(); starfield(t, { density: .8 });
    ridge({ y: 140, amp: 22, seed: 101, ink: C.ink, rim: C.night, freq: 1 / 90 });
    ridge({ y: 166, amp: 10, seed: 102, ink: C.void, rim: C.ink, freq: 1 / 60 });
    // the road and the cliff under it
    rectf(0, 170, LW, 22, C.night); hline(0, LW, 170, C.navy);
    for (let x = 0; x < LW; x += 16) hline(x, x + 7, 180, C.gold);
    rectf(0, 192, LW, LH - 192, C.ink);
    for (let i = 0; i < 44; i++) { const x = hash2(i, 5) * LW, y = 204 + hash2(i, 6) * 60; hline(x, x + 3 + hash2(i, 7) * 8, y, C.void); if (hash2(i, 8) < .4) pset(x + 1, y - 1, C.night); }
    // headlights sweeping along the road
    const hx = lerp(-60, 400, clamp(lt / (d - .2)));
    glow(hx, 182, 80, { tab: LIT, k: 1.4, ry: 28 });
    // guardrail with a gap where he stands
    const G0 = 206, G1 = 274;
    const rail = (x0, x1) => { for (let x = x0; x <= x1; x += 14) rectf(x, 190, 3, 12, C.dusk); rectf(x0, 187, x1 - x0, 5, C.haze); hline(x0, x1 - 1, 187, C.cream); hline(x0, x1 - 1, 191, C.dusk); };
    rail(-4, G0); rail(G1, LW + 4);
    trumpPx(240, 194, { u: 7, aL: 0, aR: 0, mouth: lt > .5 && lt < 1.2 ? 'o' : 'none' });
    rectf(G0, 186, 4, 7, C.dusk); rectf(G1 - 4, 186, 4, 7, C.dusk);
    // the road sign
    const sx = 94, sy = 104, sparkK = spulse(t, 3);
    vline(sx, sy + 30, 170, C.void); vline(sx + 1, sy + 30, 170, C.ink);
    polyf([[sx + .5, sy - 40], [sx + 41, sy], [sx + .5, sy + 41], [sx - 40, sy]], C.void);
    polyf([[sx + .5, sy - 37], [sx + 38, sy], [sx + .5, sy + 38], [sx - 37, sy]], C.gold);
    polyf([[sx + .5, sy - 34], [sx + 35, sy], [sx + .5, sy + 35], [sx - 34, sy]], mix(C.gold, C.amber, .15));
    ptext('HIGH', sx + 1, sy - 15, C.void, { align: 'center', scale: 2 }); ptext('IQ!', sx + 1, sy + 3, C.void, { align: 'center', scale: 2 });
    if (lt > .8) sparkle(sx + 22, sy - 20, sparkK > .5 ? 3 : 2, C.cream, C.gold);
    weather(t, 'auto', { n: 14, y1: 190 });
  });

  // ======================================================================
  // V4.10 Bernie, Bannon share a pew, — a church pew under a glowing stained-glass window: BERNIE (mittens, arms folded)
  // at one end, BANNON (several shirts at once) at the other, a PRO-HUMAN hymnal between them. They glance at each other.
  function chapel() {
    rectf(0, 0, LW, LH, C.ink);
    for (let y = 0; y < 214; y += 10) { hline(0, LW, y, C.void); for (let x = (y / 10) % 2 ? 0 : 16; x < LW; x += 32) vline(x, y, y + 9, C.void); }
    rectf(0, 214, LW, 56, C.void); hline(0, LW, 214, C.night);
  }
  const PANES = [C.rust, C.gold, C.teal, C.violet, C.mint, C.clay, C.navy, C.amber];
  function glassWindow() {
    const cx = 240, top = 14, bot = 138, hw = 40, ay = top + hw;
    const inside = (x, y) => y >= ay ? Math.abs(x - cx) <= hw && y <= bot : (x - cx) ** 2 + (y - ay) ** 2 <= hw * hw;
    for (let y = top - 3; y <= bot + 3; y++) for (let x = cx - hw - 3; x <= cx + hw + 3; x++) {
      const inn = inside(x, y), ring = !inn && (inside(x - 3, y) || inside(x + 3, y) || inside(x, y - 3) || inside(x, y + 3));
      if (ring) { pset(x, y, C.void); continue; }
      if (!inn) continue;
      const cxr = Math.floor((x - cx + hw) / 10), cyr = Math.floor((y - top) / 12), lead = (x - cx + hw) % 10 === 0 || (y - top) % 12 === 0;
      const rr = Math.hypot(x - cx, y - (ay + 6));
      if (lead) { pset(x, y, C.void); continue; }
      if (rr < 14) { pset(x, y, rr < 11 ? (bay(x, y) < .3 ? C.cream : C.gold) : C.amber); continue; }
      const c = PANES[Math.floor(hash2(cxr, cyr) * PANES.length)];
      pset(x, y, bay(x, y) < .2 ? DIM[c] : c);
    }
    vline(cx, ay - 40, bot, C.void);
  }
  line('V4', 10, (p, lt, d, t, s) => {
    dissolveIn(.3);
    layer('v4.10-chapel', chapel);
    glow(240, 80, 150, { tab: LIT, k: 1.1, ry: 110 });
    layer('v4.10-glass', glassWindow);
    // shafts of coloured light down onto the pew
    const br = .5 + .15 * breathe(t, 2);
    polyf([[206, 138], [274, 138], [330, 192], [150, 192]], lit(br));
    // candles
    for (const x of [30, 450]) { rectf(x - 2, 146, 5, 24, C.cream); vline(x + 2, 147, 169, C.gold); rectf(x - 5, 170, 11, 3, C.gold); const fl = fx(x) < .4 ? 1 : 0; polyf([[x - 1.5, 145], [x + 2.5, 145], [x + .5, 138 + fl]], C.amber); pset(x, 143, C.cream); glow(x, 142, 18, { tab: WARM, k: 1.2 }); }
    // the pew: back, then people, then the seat front
    rectf(52, 158, 376, 36, C.wine); for (let y = 166; y < 194; y += 9) hline(52, 427, y, C.ink); hline(52, 427, 158, C.rust); hline(52, 427, 159, C.clay);
    rectf(44, 146, 12, 68, C.wine); rectf(424, 146, 12, 68, C.wine); hline(44, 55, 146, C.clay); hline(424, 435, 146, C.clay); circf(50, 146, 5, C.wine); circf(430, 146, 5, C.wine);
    const glance = lt > .5 && lt < 1.1;
    const Bn = personPx(126, 198, { u: 6, sit: true, top: C.dusk, pants: C.navy, hair: 'bald', hairC: C.cream, glasses: true, skin: C.amber, aL: -.95, aR: -.95, lookX: glance ? 1 : 0, mouth: 'frown', name: 'BERNIE' });
    for (const [mx, my] of [Bn.handL, Bn.handR]) { rectf(mx - 3, my - 3, 6, 6, C.clay); rectb(mx - 3, my - 3, 6, 6, C.rust); pset(mx - 1, my - 1, C.cream); pset(mx + 1, my, C.cream); pset(mx - 1, my + 1, C.cream); }
    const Bb = personPx(354, 198, { u: 6, sit: true, flip: true, top: C.pine, pants: C.ink, hair: 'short', hairC: C.haze, skin: C.clay, aL: -.9, aR: -.9, lookX: glance ? -1 : 0, mouth: 'none', name: 'BANNON' });
    const tb = torso(354, 198, 6, true);
    [[C.rust, 7, 12], [C.navy, 6, 10], [C.teal, 5, 8], [C.gold, 4, 6], [C.cream, 3, 4]].forEach(([c, w, h]) => triPx(354 - w + .5, tb.ty, 354 + w + .5, tb.ty, 354 + .5, tb.ty + h, c));
    rectf(tb.tx - 1, tb.ty + 2, 2, tb.th - 2, C.teal); rectf(tb.tx + tb.tw - 1, tb.ty + 2, 2, tb.th - 2, C.rust);
    // the hymnal between them
    rectf(220, 170, 42, 28, C.void); rectf(221, 169, 40, 28, C.wine); rectb(221, 169, 40, 28, C.gold); rectf(221, 169, 3, 28, C.rust);
    ptext('PRO-', 242, 174, C.gold, { font: 3, align: 'center' }); ptext('HUMAN', 242, 181, C.gold, { font: 3, align: 'center' }); heartPx(242, 191, 1, C.clay);
    rectf(48, 198, 384, 6, C.rust); hline(48, 431, 198, C.clay); rectf(48, 204, 384, 10, C.wine);
  });

  // ======================================================================
  // V4.11 Claude builds Claude — now one in four! — Clawd sets the last blocks on a smaller Clawd made of blocks, which
  // blinks awake; in the sky, a dot-matrix pie hangs like a quarter moon: 26%.
  const CELL = 8;
  line('V4', 11, (p, lt, d, t, s) => {
    dissolveIn(.3);
    sky(); starfield(t, { density: .8 });
    ridge({ y: 204, amp: 8, seed: 111, ink: C.ink, rim: C.night });
    const gy = 216; lawn(gy, t);
    // the pie
    const pk = rise(lt, .7, .35), pcx = 380, pcy = 70, R = 30;
    glow(pcx, pcy, 44, { tab: LIT, k: .6 });
    for (let y = -R; y <= R; y += 3) for (let x = -R; x <= R; x += 3) {
      if (x * x + y * y > R * R) continue;
      const a = (Math.atan2(x, -y) + TAU) % TAU, on = a <= .26 * TAU * pk && (x !== 0 || y < 0);
      rectf(pcx + x - 1, pcy + y - 1, 2, 2, on ? (hash2(x, y + sbeat(t)) < .15 && spulse(t, 3) > .5 ? C.cream : C.gold) : C.dusk);
    }
    circb(pcx, pcy, R + 3, C.haze);
    if (pk > 0) { pline(pcx, pcy, pcx, pcy - R - 2, C.cream); const a = .26 * TAU * pk; pline(pcx, pcy, pcx + Math.sin(a) * (R + 2), pcy - Math.cos(a) * (R + 2), C.cream); }
    ptext('26%', pcx, pcy + R + 9, pk > .2 ? C.gold : C.dusk, { scale: 2, align: 'center', shadow: C.void });
    // the little Clawd, block by block
    const sx = 290, lu = 4, bx0 = sx - 5 * lu, cols = 5, rows = 4, by0 = gy - rows * CELL;
    const tDone = .62, place = [.04, .18, .32, .47, tDone];   // the last five blocks; the rest were already built
    const order = []; for (let r = rows - 1; r >= 0; r--) for (let c = 0; c < cols; c++) order.push([c, r]);
    const nPre = order.length - place.length, done = lt > tDone;
    const built = i => i < nPre || lt > place[i - nPre];
    const hop = done && lt < tDone + .5 ? Math.round(Math.max(0, Math.sin((lt - tDone - .12) * 9)) * 3) : 0;
    for (let i = 0; i < order.length; i++) {
      if (!built(i)) continue;
      const [c, r] = order[i]; clipRect(bx0 + c * CELL, by0 + r * CELL - (done ? hop : 0), CELL, CELL);
      clawdPx(sx, gy, { u: lu, eyes: done ? (lt > tDone + .5 ? 'happy' : 'open') : 'none', blink: false, dy: hop, shadow: false, aL: 0, aR: 0 });
      noClip();
    }
    for (let i = 0; i < order.length; i++) if (built(i)) { const [c, r] = order[i]; rectb(bx0 + c * CELL, by0 + r * CELL - hop, CELL, CELL, dim(.6)); }
    // big Clawd: fetches each block from the pile and sets it on
    const next = place.findIndex(tp => lt < tp), carry = next >= 0, reach = carry ? 1 - clamp((place[next] - lt) / .14) : 0;
    const C0 = clawdPx(186, gy, { u: 6, eyes: done ? 'happy' : 'open', lookX: done ? 0 : .8, lookY: .4, aR: carry ? lerp(-.1, .45, reach) : done ? .25 : -.4, aL: -.3, mouth: done ? 'smile' : 'none', blush: done });
    // the pile of blocks
    for (let i = 0; i < 5; i++) { const bx = 122 + (i % 3) * 9 - (i > 2 ? -4 : 0), byy = gy - CELL - (i > 2 ? CELL : 0); rectf(bx, byy, CELL, CELL, [C.clay, C.amber, C.clay, C.rust, C.clay][i]); rectb(bx, byy, CELL, CELL, dim(.6)); }
    if (carry) {
      const [c, r] = order[nPre + next], tx = bx0 + c * CELL, ty = by0 + r * CELL, [hx, hy] = C0.handR, x = Math.round(lerp(hx, tx, reach)), y = Math.round(lerp(hy - 8, ty, reach));
      rectf(x, y, CELL, CELL, C.clay); rectb(x, y, CELL, CELL, C.rust);
    }
    if (done && lt < tDone + .45) sparkle(sx, by0 - 6, 2, C.cream, C.gold);
  });

  // ======================================================================
  // V4.12 Chatbot nearly starts a war! — a chatbot's bubble shouts NUCLEAR PARTS! at a warship on the dark sea; a
  // starburst starts to bloom over the ship… a hand slaps over the bubble: WAIT. The burst fizzles into smoke.
  line('V4', 12, (p, lt, d, t, s) => {
    dissolveIn(.3);
    sky({ cy: 250, r: 320 }); starfield(t, { density: .6, y1: 166 });
    const HZ = 170;
    // the ship
    const sx = 360, sy = HZ + 2;
    polyf([[sx - 80, sy - 14], [sx + 74, sy - 14], [sx + 62, sy], [sx - 70, sy]], C.ink); hline(sx - 80, sx + 73, sy - 14, C.navy);
    rectf(sx - 24, sy - 32, 40, 18, C.ink); rectf(sx - 14, sy - 46, 22, 14, C.ink); vline(sx - 3, sy - 66, sy - 46, C.ink); hline(sx - 10, sx + 4, sy - 58, C.ink);
    rectf(sx + 32, sy - 21, 16, 7, C.ink); hline(sx + 48, sx + 64, sy - 19, C.ink); rectf(sx - 58, sy - 20, 14, 6, C.ink); hline(sx - 74, sx - 58, sy - 18, C.ink);
    hline(sx - 24, sx + 15, sy - 32, C.navy); hline(sx - 14, sx + 7, sy - 46, C.navy);
    for (let i = 0; i < 7; i++) pset(sx - 20 + i * 5, sy - 25, C.amber); pset(sx - 3, sy - 66, fx(3) < .5 ? C.rust : C.wine);
    // the war that nearly happens
    const bs = .45, bh = 1.02, bk = lt < bh ? rise(lt, bs, bh - bs, easeOut) * .75 : .75 * (1 - clamp((lt - bh) / .28));
    if (bk > 0) { glow(sx, sy - 40, 60 * bk, { tab: WARM, k: .8 }); starburst(sx, sy - 40, 46, bk, { n: 12, rot: lt * .2 }); }
    if (lt > bh + .1) smoke(sx, sy - 42, t, { h: 34, n: 9, ink: C.dusk });
    hline(0, LW, HZ, C.dusk);
    water(HZ + 1, { k: 1.2 });
    // the chatbot
    const cx = 70, cy = 76;
    rboxf(cx - 32, cy - 26, 64, 50, C.void, 2); rboxf(cx - 31, cy - 25, 62, 48, C.teal, 2); rectf(cx - 28, cy - 18, 56, 38, C.mint);
    for (let i = 0; i < 3; i++) pset(cx - 27 + i * 4, cy - 22, C.cream);
    const shout = lt < bh;
    rectf(cx - 12, cy - 9, 5, 7, C.void); rectf(cx + 8, cy - 9, 5, 7, C.void); pset(cx - 11, cy - 8, C.cream); pset(cx + 9, cy - 8, C.cream);
    if (shout) { rectf(cx - 6, cy + 4, 13, 8, C.void); rectf(cx - 4, cy + 8, 9, 3, C.rust); } else hline(cx - 4, cx + 4, cy + 7, C.void);
    glow(cx, cy, 44, { tab: GREEN, k: .8 });
    const jig = shout && fx(5) < .5 ? 1 : 0;
    bubble2('NUCLEAR\nPARTS!', 190 + jig, 104, { tail: [cx + 32, cy + 2], ink: C.rust });
    // the hand
    if (!shout) {
      const hk = clamp((lt - bh) / .1), hy = Math.round(lerp(-70, 50, easeOut(hk)));
      rectf(158, hy - 80, 56, 80, C.navy); hline(158, 213, hy - 3, C.dusk);
      rectf(144, hy, 86, 38, C.amber); rectf(144, hy, 3, 38, C.clay); rectf(227, hy, 3, 38, C.clay);
      for (let i = 0; i < 4; i++) { rectf(146 + i * 20, hy + 36, 18, 16 - Math.abs(i - 1.5) * 3, C.amber); vline(164 + i * 20, hy + 37, hy + 46, C.clay); }
      rectf(230, hy + 4, 14, 12, C.amber); hline(230, 243, hy + 15, C.clay);
      ptext('WAIT.', 187, hy + 12, C.void, { scale: 2, align: 'center' });
    }
  });

  // ======================================================================
  // V4.13 Trump: It's "Super," by decree! — at the UN rostrum (green marble, gold emblem), TRUMP holds out a proclamation
  // and speaks as it unrolls: SUPER INTELLIGENCE.
  function unHall() {
    rectf(0, 0, LW, LH, C.pine);
    for (let x = 0; x < LW; x++) { const n = noise1(x * .15, 3), n2 = noise1(x * .05, 8); if (n > .62) vline(x, 0, 214, mix(C.pine, C.teal, .35)); if (n2 > .75) vline(x, 0, 214, mix(C.pine, C.void, .3)); }
    rectf(0, 0, LW, 8, C.void); hline(0, LW, 8, C.gold);
    for (const x of [60, 420]) { rectf(x - 2, 8, 5, 206, C.void); vline(x, 8, 213, C.amber); }
    ringf(240, 44, 22, 25, C.gold); ringf(240, 44, 19, 20, C.amber);
    for (let i = 0; i < 9; i++) { const a = Math.PI * .15 + i / 9 * Math.PI * .7; pset(240 - Math.cos(a) * 30, 44 + Math.sin(a) * 30 - 6, C.gold); pset(240 + Math.cos(a) * 30, 44 + Math.sin(a) * 30 - 6, C.gold); }
    rectf(0, 214, LW, 56, C.void); hline(0, LW, 214, C.night);
  }
  line('V4', 13, (p, lt, d, t, s) => {
    dissolveIn(.3);
    layer('v4.13-hall', unHall);
    ptext('UN', 240, 37, C.cream, { scale: 2, align: 'center', shadow: C.void });
    glow(240, 150, 90, { tab: LIT, k: .7 });
    // Trump behind the rostrum, holding the proclamation's rod out in both hands; he starts speaking as it unrolls
    const TR = trumpPx(240, 212, { u: 8, aL: -.5, aR: -.5, mouth: lt > .45 && frac(lt * 2.4) < .6 ? 'o' : 'none' });
    rectf(190, 200, 100, 36, C.ink); rectb(190, 200, 100, 36, C.dusk); hline(188, 291, 200, C.haze); rectf(188, 198, 104, 3, C.night);
    // the proclamation
    const uk = rise(lt, .12, .5, easeOut), top = TR.handL[1] + 1, W = 66, x0 = 240 - W / 2, h = Math.round(58 * uk);
    rectf(x0 - 7, top - 3, W + 14, 5, C.gold); hline(x0 - 7, x0 + W + 6, top - 3, C.cream);
    if (h > 0) {
      rectf(x0 + 2, top + 2, W, h, C.void); rectf(x0, top + 1, W, h, C.cream);
      clipRect(x0, top + 1, W, h);
      ptext('SUPER', 240, top + 7, C.rust, { scale: 2, align: 'center' });
      ptext('INTELLIGENCE', 240, top + 27, C.navy, { font: 3, align: 'center' });
      hline(x0 + 8, x0 + W - 9, top + 38, C.haze); hline(x0 + 14, x0 + W - 23, top + 43, C.haze);
      circf(x0 + W - 11, top + 49, 4, C.rust); circf(x0 + W - 11, top + 49, 2, C.wine); pset(x0 + W - 12, top + 48, C.clay);
      noClip();
      rectf(x0 - 4, top + h, W + 8, 5, C.gold); hline(x0 - 4, x0 + W + 3, top + h + 4, C.amber);
    }
    for (const [hx, hy] of [TR.handL, TR.handR]) { rectf(hx - 3, hy - 3, 7, 7, C.clay); hline(hx - 3, hx + 3, hy + 3, tint(DIM, 1)); }
    if (uk >= 1) sparkle(x0 + W + 2, top + 18, spulse(t, 3) > .5 ? 2 : 1, C.cream, C.gold);
  });

  // ======================================================================
  // V4.14 "Artificial"? Fake to me! — a green highway sign reads ARTIFICIAL INTELLIGENCE; FAKE! stamps over the first
  // word, its letters drop off, and SUPER is underneath.
  line('V4', 14, (p, lt, d, t, s) => {
    dissolveIn(.25);
    sky(); starfield(t, { density: .7 });
    ridge({ y: 206, amp: 10, seed: 141, ink: C.ink, rim: C.night });
    rectf(0, 218, LW, 52, C.void); hline(0, LW, 218, C.pine);
    const X0 = 128, Y0 = 62, WW = 224, HH = 92;
    for (const x of [180, 300]) { rectf(x, Y0 + HH, 5, 218 - Y0 - HH, C.void); vline(x + 4, Y0 + HH, 217, C.ink); }
    rectf(X0 + 2, Y0 + 2, WW, HH, C.void);
    rectf(X0, Y0, WW, HH, C.teal); rectf(X0 + 2, Y0 + 2, WW - 4, HH - 4, C.pine); rectb(X0 + 3, Y0 + 3, WW - 6, HH - 6, C.cream);
    for (const x of [X0 + 40, X0 + WW - 40]) { rectf(x - 3, Y0 - 10, 7, 3, C.void); vline(x, Y0 - 7, Y0, C.void); glow(x, Y0 + 8, 34, { tab: LIT, k: .8 }); }
    const cx = X0 + WW / 2, wordY = Y0 + 20, stampT = .33, dropT = .5;
    ptext('INTELLIGENCE', cx, Y0 + 54, C.cream, { scale: 2, align: 'center' });
    const word = 'ARTIFICIAL', ww = ptextW(word, { scale: 2 }), wx0 = Math.round(cx - ww / 2);
    const sk = rise(lt, dropT + .12, .25);
    if (sk > 0) ptext('SUPER', cx, wordY, veil(C.gold, sk), { scale: 2, align: 'center', shadow: veil(C.void, sk) });
    // the letters: in place, then falling one by one
    let x = wx0;
    [...word].forEach((ch, i) => {
      const gw = (_glyphW(ch) + 1) * 2, t0 = dropT + i * .03 + hash(i) * .05, a = lt - t0;
      const dy = a > 0 ? 300 * a * a + 20 * a : 0, dx = a > 0 ? (hash2(i, 3) - .5) * 60 * a : 0;
      if (Y0 + dy < 270) ptext(ch, x + dx, wordY + dy, C.cream, { scale: 2 });
      x += gw;
    });
    // FAKE!
    if (lt > stampT) {
      const a = lt - stampT, fall = lt > dropT + .08 ? 280 * (lt - dropT - .08) ** 2 : 0, sy = wordY - 4 - (a < .06 ? Math.round((1 - a / .06) * 8) : 0) + fall;
      rectb(cx - 38, sy, 76, 22, C.rust); rectb(cx - 36, sy + 2, 72, 18, C.rust);
      ptext('FAKE!', cx, sy + 4, C.rust, { scale: 2, align: 'center', shadow: C.wine });
      if (a < .3) circb(cx, wordY + 7, 30 + a * 90, veil(C.cream, 1 - a / .3));
    }
    if (sk >= 1) sparkle(cx + 36, wordY - 2, spulse(t, 3) > .5 ? 2 : 1, C.cream, C.gold);
  });
  const _glyphW = ch => ptextW(ch);

  // ======================================================================
  // V4.15 Ten days after "pace" — surprise! — a calendar flips from SEP 12 ("pace") to SEP 22; a gift box pops and a new
  // star shoots out (Opus 5.5); ninety minutes later a second box pops and a sun and a moon jump out (GPT-6 Sol and Luna).
  const gift = (x, y, w, h, wrap, ribbon, open, tag) => {
    rectf(x - w / 2 + 1, y - h + 1, w, h, C.void);
    rectf(x - w / 2, y - h, w, h, wrap); rectf(x - 3, y - h, 6, h, ribbon); rectf(x + w / 2 - 5, y - h + 1, 5, h - 1, DIM[wrap]);
    const ly = y - h - 7 - Math.round(open * 26);
    if (open < 1) { rectf(x - w / 2 - 3, ly, w + 6, 8, wrap); rectf(x - 3, ly, 6, 8, ribbon); circf(x - 6, ly - 3, 3, ribbon); circf(x + 6, ly - 3, 3, ribbon); }
    else { rectf(x - w / 2 - 16, y - h - 3, 14, 4, wrap); rectf(x + w / 2 + 3, y - h - 2, 14, 4, wrap); }
    if (tag) tagPx(tag, x, y + 14, { font: 3 });
  };
  line('V4', 15, (p, lt, d, t, s) => {
    dissolveIn(.3);
    sky(); starfield(t, { density: .8 });
    ridge({ y: 200, amp: 8, seed: 151, ink: C.ink, rim: C.night });
    const gy = 212; lawn(gy, t);
    // the calendar on its post
    const CX = 92, CY = 52;
    vline(CX, CY + 90, gy, C.void);
    rectf(CX - 42, CY, 84, 96, C.void); rectf(CX - 40, CY + 2, 80, 92, C.cream); rectf(CX - 40, CY + 2, 80, 16, C.rust);
    ptext('SEP', CX, CY + 7, C.cream, { align: 'center' }); pset(CX - 22, CY, C.void); pset(CX + 22, CY, C.void);
    const fk = clamp((lt - .06) / .72), day = 12 + Math.floor(fk * 10), within = frac(fk * 10);
    ptext(String(day), CX, CY + 30, C.navy, { scale: 4, align: 'center' });
    if (day === 12) ptext('"PACE"', CX, CY + 74, C.rust, { font: 3, align: 'center' });
    if (day === 22) circb(CX, CY + 43, 22, C.rust);
    if (fk < 1) { const fh = Math.round(74 * (1 - within)); rectf(CX - 40, CY + 18, 80, Math.max(0, 74 - fh), C.cream); hline(CX - 40, CX + 39, CY + 18 + 74 - fh, C.haze); }
    // box one: Opus 5.5
    const pop1 = 1.02, pop2 = 1.42, o1 = rise(lt, pop1, .12), o2 = rise(lt, pop2, .12);
    gift(236, gy, 46, 34, C.clay, C.gold, o1, 'OPUS 5.5');
    if (lt > pop1) {
      const k = clamp((lt - pop1) / .4), y = lerp(gy - 40, 40, easeOut(k)), x = 236 + k * 8;
      for (let i = 1; i < 18; i++) pset(x - i * .15, y + i * 3 * (1 - k * .5), i < 5 ? C.cream : veil(C.gold, 1 - i / 18));
      glow(x, y, 20, { tab: LIT, k: 1.3 }); sparkle(x, y, k < 1 ? 3 : spulse(t, 3) > .5 ? 3 : 2, C.cream, C.gold);
    }
    // box two, ninety minutes later: a sun and a moon
    gift(390, gy, 46, 34, C.teal, C.mint, o2, 'GPT-6');
    if (lt > pop1 + .12) { const k = rise(lt, pop1 + .12, .25); pline(266, 150, 356, 150, veil(C.gold, k), { every: 3 }); pline(356, 150, 352, 147, veil(C.gold, k)); pline(356, 150, 352, 153, veil(C.gold, k)); ptext('+90 MIN', 311, 139, veil(C.cream, k), { align: 'center', shadow: veil(C.void, k) }); }
    if (lt > pop2) {
      const k = clamp((lt - pop2) / .4), e = easeOut(k);
      const sx = 390 - 30 * e, sy = gy - 44 - Math.sin(k * Math.PI * .5) * 64, mx = 390 + 30 * e, my = sy - 4;
      glow(sx, sy, 24, { tab: WARM, k: 1.2 }); ball(sx, sy, 10, [C.clay, C.amber, C.gold, C.cream]);
      for (let i = 0; i < 10; i++) { const a = i / 10 * TAU + t; pset(sx + Math.cos(a) * 14, sy + Math.sin(a) * 14, C.gold); }
      moon(mx, my, 9, { phase: .45, glow: .5 });
    }
  });

  // ======================================================================
  // V4.16 Opus 5.5: "Hi, guys!" — Clawd pops up from behind the hill, waving shyly and blushing; a spark flies up from it
  // to the top of the ledger's curve, and the 64th star is born there, twinkling.
  line('V4', 16, (p, lt, d, t, s) => {
    const b = i => B(s, i);
    sky(); starfield(t, { density: .9 });
    const i64 = ledgerIndex('V4.16'), S64 = LEDGER[i64];
    ledger(t, { upto: i64 - 1, band: .22, newborn: false });
    ridge({ y: 212, amp: 12, seed: 3, ink: C.ink, rim: C.night, freq: 1 / 80 });
    city(t, { y: 212, x0: 150, x1: 330, grow: .95, dc: 262, lit: .5 });
    // the home hill (far left), the lantern waiting on it
    const gH = hill({ cx: 64, y: 214, w: 130, drop: 40, ink: C.void, rim: C.pine });
    handLantern(80, gH(80), { glow: 14 });
    // Clawd rises from behind the near crest
    const CXc = 414, pop = rise(lt, .25, .5, k => backOut(k, 1.6)), rest = 208;
    const wave = lt > .7 ? Math.sin((lt - .7) * 9) : 0, hi = lt > b(1.2) - .1;
    const c = clawdPx(CXc, rest + Math.round((1 - pop) * 62), { u: 6, eyes: hi ? 'happy' : lt > .6 ? 'open' : 'up', lookX: -.6, aR: .9 + wave * .4, aL: -.4, blush: lt > .6, mouth: hi ? 'smile' : 'none', shadow: false, blink: false });
    const gN = hill({ cx: 430, y: 206, w: 170, drop: 36, ink: C.void, rim: C.pine });
    grass(240, LW, gN, t);
    // the spark and the 64th star
    const sk = clamp((lt - .6) / .35), born = lt > .95;
    if (sk > 0 && sk < 1) { const x = lerp(CXc, S64.x, easeOut(sk)), y = lerp(c.top - 4, S64.y, easeOut(sk)); for (let i = 1; i < 10; i++) { const f = easeOut(Math.max(0, sk - i * .03)); pset(lerp(CXc, S64.x, f), lerp(c.top - 4, S64.y, f), i < 4 ? C.cream : C.gold); } sparkle(x, y, 1, C.cream, C.gold); }
    if (born) {
      const age = lt - .95;
      glow(S64.x, S64.y, 22, { tab: LIT, k: age < .5 ? 1.8 - age * 1.4 : 1.1 });
      sparkle(S64.x, S64.y, age < .3 ? 3 : spulse(t, 3) > .4 ? 3 : 2, C.cream, C.gold);
    }
    if (hi) bubble2('Hi, guys!', 300, 150, { tail: [372, 170], n: Math.ceil((lt - b(1.2) + .1) * 14) });
    weather(t, 'auto', { n: 16 });
  });
})();

;
// ---- styles/dither/ch/c09_finale.js ----
// c09_finale.js: Chorus 4 (dawn, six lines, ~38 s) and the outro (~8 s). The night ends.
// The whole 64-star curve connects; the biggest aurora; Clawd yawns; swears to pace it (the sign flips to RACE as two shooting
// stars tear past, then race each other up the curve); then pulls on a nightcap, turns the lantern down and falls asleep, while
// the stars wheel into long-exposure trails, new stars keep being born off the top of the curve ("will it still train on?"),
// and the sun rises behind the city as the dusty-red starburst (rhyming with V1.1). The outro tilts up along the curve into
// the fading sky, writes the title in stars, and dithers down to black.
(() => {
  // ---------- timing (all relative to the C4 window; never absolute) ----------
  const starts = s => linesOf('C4').map(l => l.start - s.start);   // lt of each sung line
  const c4 = () => segByKey('C4');

  // ---------- the curve, and its continuation past the 64th star ----------
  const NL = LEDGER.length, E3 = Math.exp(3.4) - 1;
  const EXT = Array.from({ length: 14 }, (_, j) => {        // same formula as the kit's LEDGER, for i ≥ 64
    const i = NL + j, u = (i + .5) / NL, e = (Math.exp(3.4 * u) - 1) / E3;
    const bx = 30 + u * 420, by = 188 - e * 160, jt = (hash2(i, 77) - .5) * 16, ang = Math.atan2(-160 * 3.4 * Math.exp(3.4 * u) / E3, 420);
    return { x: Math.round(bx - Math.sin(ang) * jt), y: Math.round(by + Math.cos(ang) * jt), big: hash2(i, 78) < .3, i };
  });
  // The smooth curve the ledger follows (no jitter): u 0..1 → [x, y]; `lane` offsets along the normal.
  const curveAt = (u, lane = 0) => {
    const x = 30 + u * 420, y = 188 - (Math.exp(3.4 * u) - 1) / E3 * 160;
    const tx = 420, ty = -160 * 3.4 * Math.exp(3.4 * u) / E3, L = Math.hypot(tx, ty);
    return [x + (-ty / L) * lane, y + (tx / L) * lane];
  };
  // Points ~1 px apart walking back along the curve from u (a racer's trail).
  const curveTrail = (u, lane, n) => { const pts = []; let uu = u; for (let j = 0; j < n; j++) { pts.push(curveAt(uu, lane)); uu -= 1.1 / Math.hypot(420, 160 * 3.4 * Math.exp(3.4 * uu) / E3); } return pts; };
  const LINKS_V3 = () => clamp(ledgerIndex('V3.16') / (NL - 1));

  // Extension stars born by C4-relative time lt: one per slow beat, from "…train on?" onward.
  const extBorn = (s, lt) => {
    const L = starts(s), n0 = Math.ceil(sbp(s.start + L[5] + 3.2) - 1e-6);
    return EXT.map((e, j) => ({ ...e, born: sbeatT(n0 + j) - s.start })).filter(e => e.born <= lt);
  };
  // The dotted continuation (a prediction) through all EXT points off the top of the frame, and the stars born on it so far.
  function extension(t, lt, o = {}) {
    const dx = o.dx ?? 0, dy = o.dy ?? 0, pk = o.pred ?? 0, born = o.born ?? [], pin = o.predInk ?? C.dusk;
    const last = LEDGER[NL - 1], pts = [[last.x, last.y], ...EXT.map(e => [e.x, e.y])];
    if (pk > 0) {
      const n = (pts.length - 1) * clamp(pk), whole = Math.floor(n);
      for (let i = 0; i < whole; i++) pline(pts[i][0] + dx, pts[i][1] + dy, pts[i + 1][0] + dx, pts[i + 1][1] + dy, pin, { every: 3 });
      if (whole < pts.length - 1) { const a = pts[whole], b = pts[whole + 1], f = n - whole; pline(a[0] + dx, a[1] + dy, lerp(a[0], b[0], f) + dx, lerp(a[1], b[1], f) + dy, pin, { every: 3 }); }
    }
    born.forEach((e, j) => {
      const p = j ? born[j - 1] : last, age = lt - e.born, x = e.x + dx, y = e.y + dy, f = clamp(age / .3);
      pline(p.x + dx, p.y + dy, lerp(p.x, e.x, f) + dx, lerp(p.y, e.y, f) + dy, o.linkInk ?? C.dusk, { every: 2 });
      if (age < 1.1) { glow(x, y, 12, { tab: LIT, k: 1.5 * (1 - age / 1.1) }); sparkle(x, y, age < .4 ? 3 : age < .75 ? 2 : 1, C.cream, C.gold); }
      else if (e.big || (hash2(e.i, sbeat(t)) < .3 && spulse(t, 3) > .5)) sparkle(x, y, 1, C.cream, C.gold);
      else pset(x, y, C.gold);
    });
  }
  // Inks that stay legible across the dawn: `cool` over the night sky, `warm` over the warm horizon band.
  const WARMSET = new Uint8Array(256); [C.rust, C.clay, C.amber, C.gold, C.cream].forEach(i => { WARMSET[i] = 1; });
  const adapt = (cool, warm) => inkFn((x, y, u) => WARMSET[u] ? warm : cool);
  // The chorus's pre-dawn sky: the dawn ramp with the warm band kept low, so the curve stays on violet and navy.
  const SKYO = { cy: 330, r: 250, vert: .25 };

  // ---------- sky: long-exposure star trails around the pole ----------
  // rot: extra rotation now; len: trail length (radians); k: brightness 0..1; y1: trails fade out toward this screen y.
  function trails(t, o = {}) {
    const [px, py] = SKY_POLE, rot = skyRot(t) + (o.rot ?? 0), tr = o.len ?? .05, dy = o.dy ?? 0, k = o.k ?? 1, y1 = o.y1 ?? 200;
    if (tr <= .002 || k <= 0) return;
    for (let i = 0; i < _STARS.length; i++) {
      const S = _STARS[i]; if (S.cls === 0 && S.ph < .5) continue;
      const a1 = S.ang + rot, a0 = a1 - tr;
      const x1 = px + Math.sin(a1) * S.r, ya = py + Math.cos(a1) * S.r + dy, x0 = px + Math.sin(a0) * S.r, yb = py + Math.cos(a0) * S.r + dy;
      if (Math.max(x0, x1) < -2 || Math.min(x0, x1) > LW + 2 || Math.min(ya, yb) > y1 || Math.max(ya, yb) < -40) continue;
      const n = Math.max(2, Math.ceil(S.r * tr * 1.1)), head = S.cls >= 2 ? C.cream : S.cls === 1 ? C.haze : C.dusk, tail = S.cls >= 2 ? C.haze : C.dusk;
      for (let j = 0; j <= n; j++) {
        const f = j / n, a = a0 + tr * f, x = Math.round(px + Math.sin(a) * S.r), y = Math.round(py + Math.cos(a) * S.r + dy);
        if (x < 0 || x >= LW || y < 0 || y >= LH) continue;
        if (bay(x, y) < k * clamp((y1 - y) / 70) * (.35 + .65 * f)) pset(x, y, f > .82 ? head : tail);
      }
    }
  }

  // ---------- land ----------
  // The home hill at dawn (homeScene's geometry, with hooks). o: dy (tilt), stars (opts|false), trails (opts), back(sdy) (aurora),
  // ledger (opts|false), front(sdy) (over the ledger), far() (behind the skyline, far parallax), city (opts), dc (data-centre
  // pulse), fore(g) (Clawd & co, world coords), moon ([x, y, r]|false), weather
  const HX = 118;
  function scene(t, o = {}) {
    const dy = o.dy ?? 0, sdy = Math.round(dy * .3);
    sky({ ...SKYO, dy: sdy, ...(o.sky || {}) });
    if (o.trails) trails(t, { dy: sdy, ...o.trails });
    if (o.stars !== false) starfield(t, { dy: sdy, y1: 176 + sdy, ...(o.stars || {}) });
    if (o.back) o.back(sdy);
    if (o.moon !== false) { const [mx, my, mr] = o.moon || [196, 40, 7]; moon(mx, my + sdy, mr, { phase: .5, glow: .7 }); }
    if (o.ledger !== false) ledger(t, { dy: sdy, linkInk: adapt(C.dusk, C.wine), ...(o.ledger || {}) });
    if (o.front) o.front(sdy);
    view(0, -Math.round(dy * .6));
    if (o.far) o.far();
    city(t, { y: 204, x0: 262, grow: 1, dc: 380, lit: .4, ...(o.city || {}) });
    if (o.dc) glow(402, 195, 26, { tab: GREEN, k: o.dc, ry: 12 });
    ridge({ y: 214, amp: 14, seed: 3, ink: C.ink, rim: C.night, freq: 1 / 80 });
    view(0, -dy);
    const g = hill({ cx: HX, y: 196, w: 150, drop: 46, ink: C.void, rim: C.pine });
    grass(0, LW, g, t, { ink: C.pine });
    const c = o.fore ? o.fore(g) : null;
    view(0, 0);
    if (o.weather !== false) weather(t, o.weather ?? 'leaves', { n: 14, ...(o.weatherOpts || {}) });
    return { g: x => g(x) + dy, c };
  }
  // A close-up backdrop: sky, a few stars, the curve seen from a new angle (dx, dy), a far ridge and city, and a big hill crest.
  function closeBack(t, o) {
    sky({ ...SKYO });
    starfield(t, { density: .6, y1: 170 });
    if (o.moon) moon(o.moon[0], o.moon[1], 7, { phase: .5, glow: .6 });
    ledger(t, { links: 1, dx: o.ldx, dy: o.ldy, linkInk: adapt(C.dusk, C.wine) });
    ridge({ y: 232, amp: 10, seed: o.seed, ink: C.ink, rim: C.night, freq: 1 / 70 });
    city(t, { y: 230, x0: o.cityX, grow: .8, dc: o.cityX + 70, lit: .6 });
    const g = hill({ cx: o.hx, y: 236, w: 330, drop: 36, ink: C.void, rim: C.pine });
    grass(0, LW, g, t, { h: 5, step: 2 });
    return g;
  }

  // ---------- Clawd close-up helpers ----------
  // Eye boxes as clawdPx places them: [[x, y, w, h], …] for left and right. c = clawdPx's return value.
  const eyeBoxes = (c, u, lookX = 0, lookY = 0) => {
    const ew = Math.max(1, Math.round(.9 * u)), eh = Math.max(2, Math.round(1.6 * u));
    const lx = Math.round(lookX * Math.max(1, u * .5)), ly = Math.round(lookY * Math.max(1, u * .4));
    return [-1, 1].map(side => [c.x + Math.round(side * 2.3 * u - ew / 2 + .01) + lx, c.top + Math.round(1.2 * u) + ly, ew, eh]);
  };
  // Heavy eyelids over open eyes (k 0 open … 1 shut).
  function lids(c, u, k, lookX, lookY) {
    if (k <= 0) return;
    for (const [ex, ey, ew, eh] of eyeBoxes(c, u, lookX, lookY)) {
      const h = Math.min(eh - 1, Math.round(eh * k));
      if (h > 0) { rectf(ex - (u >= 6 ? 1 : 0), ey - (u >= 6 ? 1 : 0), ew + (u >= 6 ? 2 : 0), h + (u >= 6 ? 1 : 0), C.clay); if (u >= 3) hline(ex - (u >= 6 ? 1 : 0), ex + ew - (u >= 6 ? 0 : 1), ey + h - 1, C.rust); }
    }
  }
  // Big sparkly eyes for close-ups (clawdPx's 'spark' is tiny above u = 4).
  function sparkEyes(c, u, lookX = 0, lookY = 0) {
    for (const [ex, ey, ew, eh] of eyeBoxes(c, u, lookX, lookY)) { rectf(ex, ey, ew, eh, C.void); sparkle(ex + (ew >> 1), ey + (eh >> 1), u >= 6 ? 3 : 2, C.cream, C.gold); }
  }
  // Clawd's nightcap (as clawdPx draws it), raised by oy px while it's being pulled on; wine outline for the dawn sky.
  function capPx(x, top, u, oy = 0) {
    const bx = x - 5 * u, bw = 10 * u, by = top - Math.round(oy);
    const hx = bx + u, hw = bw - 3 * u, cap = Math.max(2, 2 * u), tipX = bx + bw + 2 * u, tipY = by + Math.round(1.5 * u) - Math.round(oy * .6);
    const shape = [[hx, by + .5], [hx + hw, by + .5], [hx + hw * .7, by - cap - u], [tipX + .5, tipY]];
    for (const [dx, dy] of [[-1, 0], [1, 0], [0, -1], [0, 1]]) polyf(shape.map(([px, py]) => [px + dx, py + dy]), C.wine);
    polyf(shape, C.violet);
    polyf([[hx + hw * .55, by - cap * .6], [hx + hw * .72, by - cap - u + 1], [tipX, tipY - 1], [hx + hw * .9, by - 1]], mix(C.violet, C.haze, .25));
    rectf(hx - 1, by - Math.max(1, u >> 1), hw + 2, Math.max(1, u >> 1) + 1, C.cream);
    circf(tipX, tipY + 1, Math.max(1, u * .6), C.cream);
  }
  // A big yawn on a u ≥ 3 Clawd; k 0..1 opens it.
  function yawnPx(c, u, k) {
    if (k <= .05) return;
    const cy = c.top + Math.round(4.1 * u), rx = Math.max(1, u * .75 * k), ry = Math.max(1, u * 1.1 * k);
    ellf(c.x, cy, rx + 1, ry + 1, C.rust);
    ellf(c.x, cy, rx, ry, C.void);
    if (ry >= 3) ellf(c.x, Math.round(cy + ry * .55), Math.floor(rx * .6), Math.max(1, Math.floor(ry * .3)), C.wine);
  }
  // A raised left arm for a big Clawd. (clawdPx offsets the left nub into the body, so at u ≥ 4 a raised left paw vanishes
  // behind it; pass aL: -1.5 to clawdPx and draw the arm here.) Returns the hand position.
  function leftArm(c, u, a) {
    const th = Math.max(1, Math.round(1.2 * u)), len = 2 * u, sx = c.left - th, sy = c.top + Math.round(2.4 * u);
    const dx = -Math.cos(a), dy = -Math.sin(a), pts = [];
    for (let i = 0; i < len; i++) pts.push([Math.round(sx + dx * i), Math.round(sy + dy * i)]);
    for (const [x, y] of pts) rectf(x - 1, y - 1, th + 2, th + 2, C.wine);
    for (const [x, y] of pts) rectf(x, y, th, th, C.clay);
    rectf(c.left, sy - 1, 1, th + 2, C.clay);
    const [ex, ey] = pts[len - 1]; return [ex + (th >> 1), ey + (th >> 1)];
  }
  // A hand lantern built from primitives at any height h (for close-ups next to a big Clawd). (x, y) = bottom-centre.
  // o: h, k (flame 0..1.6), glow (radius). Returns {knob: [x, y]} (the wick dial on its left side).
  function bigLantern(x, y, o = {}) {
    x = Math.round(x); y = Math.round(y);
    const h = o.h ?? 40, hw = Math.round(h * .24), w = 2 * hw + 1, k = (o.k ?? 1) * (.93 + .07 * breathe(T, 1, .3)), fl = hash2(7, boilFrame(T));
    const baseH = Math.max(3, Math.round(h * .12)), capH = Math.max(3, Math.round(h * .15)), glassH = Math.round(h * .5), gy1 = y - baseH, gy0 = gy1 - glassH, cy0 = gy0 - capH;
    const gr = o.glow ?? h * 1.7;
    if (k > .06 && gr > 0) glow(x, (gy0 + gy1) / 2, gr * clamp(.3 + .7 * k, 0, 1.5), { tab: WARM, k: 1.2 * Math.min(k, 1.5), pow: 1.5 });
    const hr = Math.max(3, Math.round(hw * .75));
    ringf(x, cy0 - 1, hr - 1.3, hr, C.void);
    polyf([[x - hw - 1.5, gy0 + .5], [x + hw + 1.5, gy0 + .5], [x + hw * .45, cy0 - .5], [x - hw * .45, cy0 - .5]], C.void);
    rectf(x - hw - 2, gy0, w + 4, 1, C.void);
    const glass = k > .7 ? C.gold : k > .35 ? C.amber : k > .12 ? C.clay : C.wine;
    rectf(x - hw, gy0 + 1, w, glassH - 1, glass);
    if (k > .45) rectf(x - hw + 2, gy0 + 3, w - 4, glassH - 5, mix(glass, k > 1 ? C.cream : C.gold, .4));
    const fb = gy1 - 3, fh = Math.max(1, Math.round(glassH * .6 * clamp(k, 0, 1.5) + (fl - .5) * 2)), fw = Math.max(1, Math.round(hw * .45 * clamp(k, .3, 1.4)));
    if (k < .15) { pset(x, fb, C.rust); pset(x, fb - 1, C.clay); }
    else {
      ellf(x, fb - fh * .38, fw + 1, fh * .42, C.amber);
      ellf(x, fb - fh * .42, fw, fh * .36, C.gold);
      ellf(x, fb - fh * .34, Math.max(0, fw - 1), Math.max(1, fh * .22), C.cream);
      pset(x + (fl > .66 ? 1 : fl < .33 ? -1 : 0), fb - fh, C.gold);
    }
    vline(x - hw - 1, gy0 + 1, gy1 - 1, C.ink); vline(x + hw + 1, gy0 + 1, gy1 - 1, C.ink); vline(x, gy0 + 1, gy0 + 2, C.ink);
    rectf(x - hw - 2, gy1, w + 4, baseH - 1, C.void); rectf(x - hw - 1, y - 1, w + 2, 1, C.void);
    const kx = x - hw - 4, ky = Math.round((gy0 + gy1) / 2); rectf(kx, ky - 1, 3, 3, C.ink); pset(kx + 1, ky, C.dusk); hline(kx + 3, x - hw - 2, ky, C.ink);
    return { knob: [kx + 1, ky] };
  }
  // Clawd sitting on the home hill (u = 3) with its lantern. o: clawdPx options + lid, cap, lantern {k, glow}
  function clawdHome(t, g, o = {}) {
    const u = 3, x = HX - 2, lx = x + 23;
    handLantern(lx, g(lx), o.lantern || {});
    const c = clawdPx(x, g(x), { u, pose: 'sit', outline: C.wine, ...o });
    if (o.lid) lids(c, u, o.lid, o.lookX, o.lookY);
    if (o.cap) capPx(c.x, c.top, u, 0);
    return c;
  }
  // A racing shooting star: pts = its trail from the head backwards (~1 px apart). warm: gold/amber, else mint/teal.
  function racer(pts, warm) {
    const inks = warm ? [C.cream, C.gold, C.amber, C.clay] : [C.cream, C.mint, C.teal, C.pine], n = pts.length;
    for (let j = n - 1; j >= 1; j--) {
      const [x, y] = pts[j], f = j / n, rx = Math.round(x), ry = Math.round(y);
      if (f < .2) circf(rx, ry, 1, j < n * .08 ? inks[0] : inks[1]);
      else if (f < .45) { pset(rx, ry, inks[1]); pset(rx, ry + 1, inks[2]); }
      else if (bay(rx, ry) < 1.3 - f) pset(rx, ry, f < .75 ? inks[2] : inks[3]);
    }
    const [hx, hy] = pts[0];
    glow(hx, hy, 18, { tab: LIT, k: 1.6 });
    circf(Math.round(hx), Math.round(hy), 2, inks[0]);
    sparkle(hx, hy, 3, C.cream, inks[1]);
  }
  const lineTrail = (hx, hy, dx, dy, n) => { const L = Math.hypot(dx, dy); return Array.from({ length: n }, (_, j) => [hx - dx / L * j, hy - dy / L * j]); };
  // A sign on a stick that can spin (a = 0: front "PACE"; a = π: back "RACE"). (x, y) = top of the stick.
  function signFlip(x, y, a, stick = 44) {
    const w = 56, h = 22, cw = Math.cos(a), sw = Math.max(2, Math.round(w * Math.abs(cw))), front = cw >= 0;
    rectf(x - 1, y, 2, stick, C.void); pset(x, y, C.ink);
    const bx = Math.round(x - sw / 2), by = y - h + 4;
    rectf(bx - 1, by - 1, sw + 2, h + 2, front ? C.void : C.wine);
    rectf(bx, by, sw, h, front ? C.cream : C.rust);
    if (Math.abs(cw) > .8) ptext(front ? 'PACE' : 'RACE', x + 1, by + 4, front ? C.void : C.cream, { align: 'center', scale: 2, shadow: front ? undefined : C.wine });
    else if (sw > 6) { hline(bx + 2, bx + sw - 3, by + 7, front ? C.haze : C.clay); hline(bx + 2, bx + sw - 3, by + 13, front ? C.haze : C.clay); }
  }
  // Star-dot text (as the intro's title): letters light one by one from lt0 over dur.
  function starText(str, x, y, t, lt, lt0, dur) {
    const dots = textDots(str, x, y, { scale: 2, align: 'center' }), n = str.length, sb = sbeat(t);
    for (const d of dots) {
      const age = lt - (lt0 + d.i / n * dur + hash2(d.x, d.y) * .15);
      if (age < 0) continue;
      if (age < .3) sparkle(d.x, d.y, 1, C.cream, C.gold);
      else if (hash2(d.x + d.y * 480, sb) < .08 && spulse(t, 3) > .5) sparkle(d.x, d.y, 1, C.cream, C.haze);
      else pset(d.x, d.y, hash2(d.x, d.y + 1) < .7 ? C.cream : C.gold);
    }
  }
  // Switch between sub-shots with the ordered-dither dissolve: shots = [[lt0, fn], …] (lt0 = centre of the dissolve).
  function chain(lt, shots, half = .25) {
    let i = 0; while (i + 1 < shots.length && lt >= shots[i + 1][0] - half) i++;
    const k = i > 0 ? clamp((lt - (shots[i][0] - half)) / (2 * half)) : 1;
    if (k < 1) crossfade(ease(k), shots[i - 1][1], shots[i][1]); else shots[i][1]();
  }

  // ---------- the last motion of the night ----------
  // After Clawd falls asleep the sky speeds up (extra rotation) and the trails grow; C4-relative time lt.
  const G0 = L => L[5] + 2.6;
  const spin = (L, lt) => { const x = Math.max(0, lt - G0(L)); return .0026 * x * x; };
  const trailLen = (L, lt) => { const x = Math.max(0, lt - G0(L)); return Math.min(.2, .0026 * x * x + .006 * x); };
  const sunK = (L, lt, end) => rise(lt, L[5] + 8.6, Math.max(4, end - L[5] - 8.2), k => ease(k) * .75 + k * .25);
  // The sun rising behind the city: the horizon warms, then the dusty-red starburst (V1.1's bloom) with a gold sun in its heart.
  const SUNX = 300;
  function sunrise(t, k) {
    if (k <= 0) return;
    const cy = Math.round(lerp(250, 196, k)), R = 22 + 42 * ease(clamp(k * 1.15)), rot = t * .02;
    glow(SUNX, 212, 230, { tab: WARM, k: 1.5 * ease(clamp(k * 1.3)), ry: 80, pow: 1.25 });
    starburst(SUNX, cy, R * 1.2, 1, { n: 14, rot, inner: .4, ink: C.rust, fringe: C.wine });
    starburst(SUNX, cy, R * .78, 1, { n: 14, rot: rot + TAU / 28, inner: .5, ink: C.clay, fringe: C.rust, long: false, core: false });
    for (let i = 0; i < 6; i++) { const a = -Math.PI + (i + .5) / 6 * Math.PI, r = R * 1.45 + 4 * breathe(t, 2, i / 6); if (k > .45) sparkle(SUNX + Math.cos(a) * r, cy + Math.sin(a) * r, hash2(i, sbeat(t)) < .5 ? 1 : 2, C.cream, C.gold); }
    circf(SUNX, cy, 17, C.amber); circf(SUNX, cy, 15, mix(C.amber, C.gold, .5)); circf(SUNX, cy, 13, C.gold); circf(SUNX - 2, cy - 2, 8, mix(C.gold, C.cream, .55)); circf(SUNX - 3, cy - 3, 3, C.cream);
  }
  // The camera in G (and where the outro starts): turned a little up and right, so the top of the curve is in frame.
  const GDX = -40, GDY = 24;

  // =====================================================================================================
  // CHORUS 4: dawn
  // =====================================================================================================
  section('C4', (p, lt, d, t, s) => {
    dissolveIn(1);
    const L = starts(s);

    // A. "We didn't start the scaling": the V4 stretch of the curve connects, the 64th star flares, and the dotted
    // prediction runs on off the top of the frame. Tired Clawd follows it up with heavy eyes.
    const shotA = () => {
      const done = L[1] - 1.1, lk = lerp(LINKS_V3(), 1, rise(lt, .5, Math.max(.8, done - .5), k => k));
      scene(t, {
        ledger: { links: lk, band: .15 * rise(lt, .2, 1.2) },
        front: () => {
          extension(t, lt, { pred: rise(lt, done + .15, .9) });
          const fa = lt - done; if (fa > 0 && fa < 1.4) { const T63 = LEDGER[NL - 1]; glow(T63.x, T63.y, 16, { tab: LIT, k: 1.4 * (1 - fa / 1.4) }); sparkle(T63.x, T63.y, fa < .5 ? 3 : 2, C.cream, C.gold); }
        },
        fore: g => clawdHome(t, g, { eyes: 'open', blink: false, lid: .5 + .15 * breathe(t, 3), lookX: .3 + .6 * rise(lt, .5, done), lookY: -1, dy: -Math.round(breathe(t, 3)) }),
      });
    };

    // B. "It was always training, and the curves kept gaining": the biggest aurora yet, violet and teal, over a blazing city;
    // the camera tilts up the curve.
    const shotB = () => {
      const b0 = L[1], ak = rise(lt, b0 - .3, 1.4), dy = Math.round(40 * ease(clamp((lt - b0 + .2) / (L[2] - b0 + .2))));
      const ec = (x, y0, h, sh) => y0 - h * (Math.exp(3.4 * clamp((x - 20 + sh) / 440)) - 1) / E3;
      scene(t, {
        dy,
        stars: { density: .7 },
        back: sdy => {
          aurora(t, { curve: x => ec(x, 140, 175, 60) + Math.sin(x * .021 + t * .45) * 8 + Math.sin(x * .067 - t * .3) * 4 + sdy - 30, len: 58, k: .55 * ak, cols: [C.violet, C.haze, C.cream], shimmer: 1.6 });
          aurora(t, { curve: x => ec(x, 176, 160, -10) + Math.sin(x * .032 - t * .38 + 1) * 6 + sdy, len: 52, k: .78 * ak, cols: [C.pine, C.teal, C.mint], shimmer: 1.2 });
        },
        ledger: { links: 1, band: .35 * ak },
        front: sdy => extension(t, lt, { pred: 1, dy: sdy }),
        city: { lit: .5 + .45 * ak },
        dc: .6 + .7 * spulse(t, 3),
        fore: g => clawdHome(t, g, { eyes: 'open', lid: .3, lookX: .3 + .5 * ak, lookY: -1 }),
      });
    };

    // C. "We didn't start the scaling": close on Clawd, yawning: a big stretch, the mouth opens wide, a tear; then it droops.
    const shotC = () => {
      const y0 = L[2] + .55, yk = rise(lt, y0, .45) * (1 - rise(lt, y0 + 1.2, .4)), up = yk > .1, u = 10;
      const g = closeBack(t, { ldx: -40, ldy: 40, seed: 44, cityX: 330, hx: 200, moon: [300, 44] });
      bigLantern(318, g(318), { h: 46, k: 1 - .2 * yk });
      const stretch = up ? .75 + .45 * yk : -.45 + .1 * breathe(t, 2);
      const c = clawdPx(200, g(200), { u, pose: 'sit', outline: C.wine, eyes: up ? 'closed' : 'open', blink: false, aL: up ? -1.5 : stretch, aR: stretch, dy: Math.round(3 * yk) });
      if (up) leftArm(c, u, stretch);
      if (!up) lids(c, u, lt < y0 ? .4 + .1 * breathe(t, 2) : .6 + .1 * breathe(t, 2));
      yawnPx(c, u, yk);
      if (lt > y0 + .45 && lt < y0 + 2.2) { const tk = lt - y0 - .45, [ex, ey, ew, eh] = eyeBoxes(c, u)[1]; circf(ex + ew + 2, ey + eh + 2 + Math.round(tk * 7), 1, veil(C.cream, 1.3 - tk * .7)); }
      if (up) ptext('~', c.x + 62, c.top - 4 - Math.round(yk * 4), veil(C.haze, yk), { scale: 2 });
      weather(t, 'leaves', { n: 10 });
    };

    // D. "Now we swear we'll try to pace it — but we'd rather race it!": Clawd raises a paw and holds up a PACE sign;
    // two shooting stars tear past overhead, neck and neck; the sign spins in their wake and lands on its back: RACE.
    const shotD = () => {
      const d0 = L[3], dl = L[4] - L[3], swear = rise(lt, d0 + .05, .45), signUp = rise(lt, d0 + .95, .6);
      const r0 = d0 + dl * .56, rk = clamp((lt - r0) / 1.05), racing = rk > 0 && rk < 1, passed = rk >= .55;
      const sa = Math.PI * 3 * easeOut(clamp((lt - r0 - .45) / .75)), u = 8;
      const g = closeBack(t, { ldx: 10, ldy: 18, seed: 51, cityX: 300, hx: 170 });
      const flare = rise(lt, r0 + .35, .3) * (1 - .4 * rise(lt, r0 + 1.3, 1));
      bigLantern(300, g(300), { h: 38, k: 1 + .6 * flare, glow: 64 + 30 * flare });
      // the racers: side by side just over the sign, the lead swapping
      const X = k => lerp(-50, 540, k), Y = (k, lane) => lerp(112, 92, k) - Math.sin(k * Math.PI) * 8 + lane;
      if (racing) {
        const sw = .04 * Math.sin((lt - r0) * 7);
        for (const [lane, warm, k] of [[0, true, rk + sw], [11, false, rk - sw]]) { const x = X(k), y = Y(k, lane), x2 = X(k - .01), y2 = Y(k - .01, lane); racer(lineTrail(x, y, x - x2, y - y2, 70), warm); }
      }
      const lead = racing ? X(rk + .04) : passed ? 540 : -50;
      const lookX = racing ? clamp((lead - 190) / 110, -1, 1) : passed ? 1 : 0, lookY = racing ? -1 : 0;
      const eyes = passed ? 'none' : racing ? 'wide' : lt < d0 + 1.8 && swear > .5 ? 'closed' : 'open';
      const c = clawdPx(190, g(190), { u, pose: 'sit', outline: C.wine, eyes, lookX, lookY, blink: false, aL: swear > .15 ? -1.5 : -.4, aR: lerp(-.4, 1.15, signUp), mouth: racing && !passed ? 'o' : passed ? 'smile' : 'none', blush: passed });
      if (swear > .15) leftArm(c, u, lerp(-.4, 1.3, swear) - (passed ? .6 : 0));
      if (passed) sparkEyes(c, u, lookX, lookY);
      else if (eyes === 'open') lids(c, u, .35);
      if (signUp > 0) signFlip(c.handR[0], c.handR[1] - 44 + Math.round(30 * (1 - ease(signUp))), sa);
      weather(t, 'leaves', { n: 10 });
    };

    // E. "We didn't start the scaling": wide again. The two racers come round and race up the curve itself, neck and neck,
    // lighting every star they pass, and shoot off the top of the frame, leaving the curve burning gold.
    const shotE = () => {
      const e0 = L[4] + .25, ek = clamp((lt - e0) / 1.75), over = ek >= 1;
      const bu = lerp(-.1, 1.18, ek * ek * .45 + ek * .55), sw = .03 * Math.sin((lt - e0) * 5.2), u1 = bu + sw, u2 = bu - sw, lo = Math.min(u1, u2);
      scene(t, {
        stars: { density: .8 },
        ledger: { links: 1 },
        front: () => {
          for (let i = 0; i + 1 < NL; i++) { if ((i + 1.5) / NL > lo && !over) break; const a = LEDGER[i], b = LEDGER[i + 1]; pline(a.x, a.y, b.x, b.y, adapt(C.gold, C.wine), { every: 2 }); }
          for (let i = 0; i < NL; i++) {
            const age = (lo - (i + .5) / NL) / .07; if (age < 0 && !over) continue;
            const S = LEDGER[i]; if (age < 1 && !over) sparkle(S.x, S.y, 2, C.cream, C.gold); else if (hash2(i, sbeat(t)) < .4 && spulse(t, 3) > .4) sparkle(S.x, S.y, 1, C.cream, C.gold);
          }
          extension(t, lt, { pred: 1, predInk: lo > 1 ? C.gold : C.dusk });
          if (!over) { racer(curveTrail(u1, -5, 70), true); racer(curveTrail(u2, 5, 70), false); }
          const ex = lt - (e0 + 1.6); if (ex > 0 && ex < .9) sparkle(474, 3, ex < .45 ? 3 : 2, C.cream, C.gold);
        },
        city: { lit: .7 },
        dc: .5 + .6 * spulse(t, 3),
        fore: g => {
          const hx = curveAt(clamp(bu, 0, 1))[0];
          return clawdHome(t, g, { eyes: over ? 'happy' : 'wide', lookX: over ? .8 : clamp((hx - 116) / 140, -1, 1), lookY: -1, lantern: { k: 1.4 - .3 * ek, glow: 24 } });
        },
      });
    };

    // F. "But when we log off,": close. Clawd pulls on a nightcap, reaches over and turns its lantern down to an ember, and
    // is asleep before "…will it still train on?".
    const shotF = () => {
      const f0 = L[5], capK = rise(lt, f0 + .55, .7), off = rise(lt, f0 + 1.6, .8), sleep = lt > f0 + 2.55, u = 8;
      const g = closeBack(t, { ldx: -60, ldy: 34, seed: 61, cityX: 340, hx: 230, moon: [96, 64] });
      bigLantern(294, g(294), { h: 38, k: lerp(1, .08, off), glow: lerp(64, 12, off) });
      const pulling = capK > 0 && capK < 1, reach = lt > f0 + 1.35 && lt < f0 + 2.45;
      const c = clawdPx(216, g(216), { u, pose: sleep ? 'sleep' : 'sit', outline: C.wine, eyes: sleep ? 'closed' : 'open', blink: false, zzz: false, aL: pulling ? -1.5 : sleep ? -1.2 : -.45, aR: pulling ? 1.25 : reach ? -.55 : sleep ? -1.2 : -.45, dy: sleep ? -2 : 0 });
      if (pulling) leftArm(c, u, 1.25);
      if (!sleep) lids(c, u, lerp(.45, .8, off));
      if (capK > 0) capPx(c.x, c.top, u, Math.round(22 * (1 - easeOut(capK))));
      if (sleep) for (let i = 0; i < 3; i++) { const a = lt - f0 - 2.55 - i * .55; if (a < 0) continue; const f = frac(a * .4); ptext(i % 2 ? 'z' : 'Z', c.x + 50 + f * 18, c.top - 10 - f * 34, veil(C.cream, 1.15 - f), { scale: 2, shadow: veil(C.wine, 1 - f) }); }
      weather(t, 'leaves', { n: 10 });
    };

    // G. "…will it still train on? / (And on, and on, and on…)": wide. Clawd asleep in its nightcap, lantern an ember. The sky
    // keeps turning, faster, into long-exposure trails; the data centre keeps blinking; a new star is born at the top of the
    // curve on every beat and runs off the edge of the frame; and the sun rises behind the city as the dusty-red starburst.
    const shotG = () => {
      const sp = spin(L, lt), sk = sunK(L, lt, d);
      scene(t, {
        trails: { rot: sp, len: trailLen(L, lt), k: 1 - .5 * sk, y1: 190 },
        stars: { rot: sp, density: .9 },
        moon: false,
        ledger: { links: 1, band: .2, dx: GDX, dy: GDY },
        front: () => extension(t, lt, { pred: 1, born: extBorn(s, lt), dx: GDX, dy: GDY }),
        far: () => sunrise(t, sk),
        city: { lit: .5 },
        dc: .7 + .8 * spulse(t, 3),
        fore: g => clawdHome(t, g, { pose: 'sleep', eyes: 'closed', cap: true, lantern: { k: .1, glow: 5 } }),
      });
    };

    chain(lt, [[0, shotA], [L[1], shotB], [L[2], shotC], [L[3], shotD], [L[4] + .15, shotE], [L[5], shotF], [L[5] + 3.1, shotG]]);
  });

  // =====================================================================================================
  // OUTRO: morning. The camera tilts up (and along the curve) from sleeping Clawd into the fading stars; only the curve,
  // still growing off the top, stays lit. The title writes itself in stars, and everything dithers down to black.
  // =====================================================================================================
  section('outro', (p, lt, d, t, s) => {
    const C4 = c4(), L = starts(C4), clt = t - C4.start;          // C4-relative time, to continue its sky exactly
    const tk = ease(clamp((lt - .2) / 5.4)), dy = Math.round(150 * tk), sdy = Math.round(dy * .3);
    const pdx = Math.round(lerp(GDX, -92, tk)), pdy = Math.round(lerp(GDY, 38, tk)) + sdy;
    const fadeStars = rise(lt, .6, 4.2), sk = Math.min(1, sunK(L, clt, C4.end - C4.start) + lt / 10);
    const rot = spin(L, clt) - 50 * tk / 420;     // panning right along the curve: the sky slides left
    scene(t, {
      dy,
      trails: { rot, len: trailLen(L, clt), k: .5 * (1 - fadeStars), y1: 190 + sdy },
      stars: { rot, density: .9, appear: 1 - .85 * fadeStars },
      moon: false,
      ledger: { links: 1, band: .2 * (1 - fadeStars), dx: pdx, dy: pdy, linkInk: adapt(C.haze, C.wine) },
      front: () => extension(t, clt, { pred: 1, born: extBorn(C4, clt), dx: pdx, dy: pdy, linkInk: C.haze, predInk: C.haze }),
      far: () => sunrise(t, sk),
      city: { lit: .5 },
      dc: .7 + .8 * spulse(t, 3),
      fore: g => clawdHome(t, g, { pose: 'sleep', eyes: 'closed', cap: true, lantern: { k: .1, glow: 5 } }),
    });
    // the title, small, in stars (the intro wrote it big)
    starText("WE DIDN'T START", 158, 64, t, lt, 3.4, 1.1);
    starText('THE SCALING', 158, 86, t, lt, 4.4, .9);
    // the date, drawn here instead of by the overlay so it dithers out with everything else (the overlay's identical copy stays
    // on top until the dissolve from C4 is over, since that dissolve mixes in C4 frames that have no date of their own)
    if (lt > .6) hideStamp();
    const ds = SEGS.filter(g => g.date && g.start <= t).pop(), m = ds && ds.date.match(/^(.*?)\s*(\d{4})$/);
    if (m) {
      rectf(DATE_X - 4, DATE_Y - 3, 57, 28, dim(.6));
      ptext(m[1], DATE_X, DATE_Y, C.haze, { font: 3, shadow: C.void });
      ptext(m[2], DATE_X, DATE_Y + 8, C.cream, { scale: 2, dots: true, shadow: C.ink, off: C.ink });
    }
    // dither down to black over the last second and a half; the newest star is the last light to go out
    const fk = clamp((lt - (d - 1.6)) / 1.5);
    if (fk > 0) {
      fadeAll(7 * ease(fk));
      const b = extBorn(C4, clt).filter(e => e.y + pdy > 4 && e.x + pdx < LW - 4).pop();
      if (b && fk < .97) sparkle(b.x + pdx, b.y + pdy, fk < .45 ? 2 : fk < .8 ? 1 : 0, fk < .85 ? C.cream : C.gold, fk < .6 ? C.gold : C.amber);
    }
  });
})();
