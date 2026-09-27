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
// ---- styles/idol/kit.js ----
// kit.js: the idol style's shared look — an anime K-pop idol MV for the album's K-pop track.
// Palette, clean-line drawing primitives, the idol rig (TOKI and her group ATTN!), chibi people, Clawd the devoted fan,
// stage/LED/lightstick/confetti kit, variety-show graphics, and the overlays drawn over every frame
// (member-colour-coded lyric subtitles, the comeback D-day date card, bloom + vignette).
// Read STYLE.md before using any of it. Everything here is a pure function of song time (no Math.random()).

// The zine's caption, date stamp and grain overlays (timeline.js) are dropped; this style registers its own at the bottom.
OVERLAYS.length = 0;

// =====================================================================================================
// PALETTE
// =====================================================================================================
const IP = {
  // stage night
  night: '#150B2E', night2: '#241250', plum: '#3A1A6B', violet: '#6A3DDB', indigo: '#2A2A8C',
  // neon
  neonPink: '#FF3DA8', neonCyan: '#35E8FF', neonLime: '#B8FF4F', neonGold: '#FFD23F',
  // pastels
  pink: '#FFB3D6', blush: '#FFD1E4', lilac: '#C9B6FF', lav: '#E6DCFF', mint: '#A9F3DA', sky: '#AEE3FF',
  lemon: '#FFF1A6', peach: '#FFCDB2', cream: '#FFF8F0', white: '#FFFFFF',
  // inks
  ink: '#2B1838', inkSoft: '#5A3F72', line: '#3A2150',
  red: '#FF4B5C', gold: '#FFC940', silver: '#C9CEDD',
  // skin (with a warm pink shadow and a red-brown line, anime style)
  skin: '#FFE0D0', skinSh: '#F4B2A4', skinLine: '#A0525E', cheek: '#FF8FA8',
};
// ATTN! — the fictional group. Member colour drives caption coding, lightsticks, outfits.
// hair: style key for the rig; hairCol/hairSh/hairLt: base/shadow/shine; eye: [dark, mid, light] iris.
const MEMBERS = {
  TOKI: { name: 'TOKI', col: '#FF4FA8', lt: '#FFC2E0', hair: 'twintails', hairCol: '#FF9CCB', hairSh: '#E3669F', hairLt: '#FFE0EF', hairLine: '#9C3468', tip: '#C3A2FF', eye: ['#4A1F6E', '#B04FD8', '#FFB0F0'], acc: 'star' },
  RELU: { name: 'RELU', col: '#1FD6A8', lt: '#B5F7E4', hair: 'bob', hairCol: '#7FE6CF', hairSh: '#3FB59F', hairLt: '#DBFFF5', hairLine: '#1D6B63', eye: ['#12404A', '#1F9FB0', '#9FF5FF'], acc: 'clip' },
  ADA: { name: 'ADA', col: '#8F63FF', lt: '#DCCDFF', hair: 'long', hairCol: '#6E62D6', hairSh: '#4A3FA6', hairLt: '#C8C2FF', hairLine: '#271E66', eye: ['#241A5C', '#6A55E0', '#C4B8FF'], acc: 'ribbon' },
  LOGI: { name: 'LOGI', col: '#FFB321', lt: '#FFE6A8', hair: 'ponytail', hairCol: '#FFD37A', hairSh: '#E09A3C', hairLt: '#FFF3CF', hairLine: '#8A5418', eye: ['#5A2E0E', '#D07A1E', '#FFD27A'], acc: 'bow' },
};
const MEMBER_ORDER = ['TOKI', 'RELU', 'ADA', 'LOGI'];
const memberOf = k => MEMBERS[k] || MEMBERS[MEMBER_ORDER[((k | 0) % 4 + 4) % 4]] || MEMBERS.TOKI;

// =====================================================================================================
// CLEAN-LINE PRIMITIVES
// =====================================================================================================
// Smooth path through points (Catmull-Rom → Bézier). A point [x, y, 1] is a sharp corner (hair tips, chins, collars).
function crPath(P, closed = true, begin = true) {
  const n = P.length; if (n < 2) return;
  if (begin) ctx.beginPath();
  ctx.moveTo(P[0][0], P[0][1]);
  const N = closed ? n : n - 1;
  for (let i = 0; i < N; i++) {
    const p1 = P[i], p2 = P[(i + 1) % n];
    const p0 = closed || i > 0 ? P[(i - 1 + n) % n] : p1, p3 = closed || i + 2 < n ? P[(i + 2) % n] : p2;
    const k1 = p1[2] ? 0 : 1 / 6, k2 = p2[2] ? 0 : 1 / 6;
    ctx.bezierCurveTo(p1[0] + (p2[0] - p0[0]) * k1, p1[1] + (p2[1] - p0[1]) * k1, p2[0] - (p3[0] - p1[0]) * k2, p2[1] - (p3[1] - p1[1]) * k2, p2[0], p2[1]);
  }
  if (closed) ctx.closePath();
}
// Sample a cubic Bézier into n+1 points.
function bez(p0, c1, c2, p3, n = 12) {
  const out = [];
  for (let i = 0; i <= n; i++) {
    const u = i / n, a = (1 - u) ** 3, b = 3 * (1 - u) ** 2 * u, c = 3 * (1 - u) * u * u, d = u ** 3;
    out.push([a * p0[0] + b * c1[0] + c * c2[0] + d * p3[0], a * p0[1] + b * c1[1] + c * c2[1] + d * p3[1]]);
  }
  return out;
}
const qbez = (p0, c, p2, n = 10) => bez(p0, [p0[0] + (c[0] - p0[0]) * 2 / 3, p0[1] + (c[1] - p0[1]) * 2 / 3], [p2[0] + (c[0] - p2[0]) * 2 / 3, p2[1] + (c[1] - p2[1]) * 2 / 3], p2, n);
// Brush stroke: a filled polygon along a polyline whose width follows a profile. prof: 'mid' (thin-thick-thin), 'start' (thick→thin), 'end' (thin→thick), 'flat'.
function brush(pts, w, col, prof = 'mid', o = {}) {
  const n = pts.length; if (n < 2) return;
  const L = [], R = [];
  for (let i = 0; i < n; i++) {
    const a = pts[Math.max(0, i - 1)], b = pts[Math.min(n - 1, i + 1)];
    let dx = b[0] - a[0], dy = b[1] - a[1]; const l = Math.hypot(dx, dy) || 1; dx /= l; dy /= l;
    const u = i / (n - 1);
    const k = prof === 'start' ? (1 - u) ** .7 : prof === 'end' ? u ** .7 : prof === 'flat' ? 1 : Math.sin(Math.PI * clamp(u * .92 + .04)) ** .6;
    const hw = w / 2 * Math.max(o.min ?? .08, k);
    L.push([pts[i][0] - dy * hw, pts[i][1] + dx * hw]); R.push([pts[i][0] + dy * hw, pts[i][1] - dx * hw]);
  }
  ctx.beginPath(); ctx.moveTo(L[0][0], L[0][1]);
  for (let i = 1; i < n; i++) ctx.lineTo(L[i][0], L[i][1]);
  for (let i = n - 1; i >= 0; i--) ctx.lineTo(R[i][0], R[i][1]);
  ctx.closePath(); ctx.fillStyle = col; ctx.fill();
}
// Simple round-capped line.
function ln(pts, col, w, o = {}) {
  ctx.save(); ctx.strokeStyle = col; ctx.lineWidth = w; ctx.lineCap = o.cap ?? 'round'; ctx.lineJoin = 'round';
  if (o.alpha !== undefined) ctx.globalAlpha *= o.alpha;
  if (o.smooth) crPath(pts, false); else tracePath(pts, false);
  ctx.stroke(); ctx.restore();
}
// Rounded-rectangle path (begins a new path).
function rrect(x, y, w, h, r) { ctx.beginPath(); ctx.roundRect(x, y, w, h, Math.min(r, w / 2, h / 2)); }

// Light direction for cel shading (unit vector pointing TOWARD the key light, screen space) and the rim light colour.
// Shots may change them per frame with setLight(); overlays reset them to the defaults every frame.
const LIGHT0 = { x: -.55, y: -.83, rim: null, rimX: .8, rimY: -.6 };
let LIGHT = { ...LIGHT0 };
function setLight(o) { LIGHT = { ...LIGHT0, ...o }; }

// solid(path, fill, o): the idol world's workhorse, like zine's scrap(): a flat fill, a 2-tone cel shadow crescent on the side away
// from the key light, an optional coloured rim light on the far side, and a clean outline.
//   path: point list (smoothed unless o.sharp) or a function that builds the path. o: shade (colour; default darker fill), sh (shadow depth
//   in px, default ~9% of size), rim (colour or false), rimW, line (outline colour; false for none), lw (line width), op, grad ([c0, c1] vertical gradient),
//   glow (outer glow colour), sharp (polygon, no smoothing).
function solid(path, fill, o = {}) {
  const mk = typeof path === 'function' ? path : o.sharp ? () => tracePath(path) : () => crPath(path);
  let bb = null;
  if (typeof path !== 'function') bb = bbox(path);
  const size = o.size ?? (bb ? Math.min(bb.w, bb.h) : 100);
  ctx.save();
  if (o.op !== undefined) ctx.globalAlpha *= o.op;
  if (o.glow) { ctx.save(); ctx.shadowColor = o.glow; ctx.shadowBlur = o.glowR ?? size * .3; mk(); ctx.fillStyle = fill; ctx.fill(); ctx.restore(); }
  if (o.dropShadow) { ctx.save(); ctx.translate(o.dropShadow[0], o.dropShadow[1]); mk(); ctx.fillStyle = o.dropCol ?? 'rgb(20 8 40 / .28)'; ctx.fill(); ctx.restore(); }
  mk();
  if (o.grad && bb) { const g = ctx.createLinearGradient(0, bb.y, 0, bb.y + bb.h); g.addColorStop(0, o.grad[0]); g.addColorStop(1, o.grad[1]); ctx.fillStyle = g; }
  else ctx.fillStyle = fill;
  ctx.fill();
  const sh = o.sh ?? size * .09;
  if (o.shade !== false && sh > 0) {
    ctx.save(); mk(); ctx.clip();
    crescent(mk, o.shade ?? mixCol(fill.length === 7 ? fill : '#888888', IP.plum, .28), -LIGHT.x * sh, -LIGHT.y * sh);
    const rim = o.rim ?? LIGHT.rim;
    if (rim) crescent(mk, rim, LIGHT.rimX * (o.rimW ?? sh * .45), LIGHT.rimY * (o.rimW ?? sh * .45));
    ctx.restore();
  }
  if (o.line !== false) { mk(); ctx.strokeStyle = o.line ?? IP.line; ctx.lineWidth = o.lw ?? Math.max(1.5, size * .03); ctx.lineJoin = 'round'; ctx.stroke(); }
  ctx.restore();
}
// Paint "shape minus shape-shifted-by(−dx,−dy)": the crescent of the shape that faces direction (dx, dy). Call inside a clip to the shape.
function crescent(mk, col, dx, dy) {
  ctx.save(); ctx.fillStyle = col;
  ctx.beginPath(); mkInto(mk); ctx.translate(-dx, -dy); mkInto(mk); ctx.translate(dx, dy);
  ctx.fill('evenodd'); ctx.restore();
}
// Append a path-building function's path to the current path (without beginPath). Path fns call ctx.beginPath(), so we
// temporarily neuter it.
function mkInto(mk) { const bp = ctx.beginPath; ctx.beginPath = () => {}; try { mk(); } finally { ctx.beginPath = bp; } }

// A soft radial glow (cheap: gradient, no shadowBlur).
function glow(x, y, r, col, a = .6) {
  const g = ctx.createRadialGradient(x, y, 0, x, y, r);
  g.addColorStop(0, alpha(col, a)); g.addColorStop(.4, alpha(col, a * .35)); g.addColorStop(1, alpha(col, 0));
  ctx.fillStyle = g; ctx.fillRect(x - r, y - r, r * 2, r * 2);
}
// Cached glow sprite for many small lights (lightsticks, bokeh). Drawn with 'lighter' by the caller if wanted.
function glowSprite(col, core = '#FFFFFF') {
  return cached(`glow|${col}|${core}`, 128, 128, (w, h) => {
    const g = ctx.createRadialGradient(64, 64, 0, 64, 64, 64);
    g.addColorStop(0, core); g.addColorStop(.12, col); g.addColorStop(.35, alpha(col, .45)); g.addColorStop(1, alpha(col, 0));
    ctx.fillStyle = g; ctx.fillRect(0, 0, 128, 128);
  });
}

// Display text with stacked outlines (idol subtitles, variety captions). o: font (FONTS key), fill, grad ([c0, c1]),
// strokes ([[colour, width], ...] outermost first), shadow ([dx, dy, colour]), align, rot, spacing, maxW, skew, alpha, baseline.
function dtext(str, x, y, size, o = {}) {
  ctx.save(); ctx.translate(x, y); if (o.rot) ctx.rotate(o.rot); if (o.skew) ctx.transform(1, 0, o.skew, 1, 0, 0);
  if (o.alpha !== undefined) ctx.globalAlpha *= o.alpha;
  const fam = FONTS[o.font ?? 'rammetto'] || o.font;
  ctx.font = `${size}px "${fam}"`; ctx.textAlign = o.align ?? 'center'; ctx.textBaseline = o.baseline ?? 'middle';
  if (o.spacing) ctx.letterSpacing = `${o.spacing}px`;
  if (o.maxW) { const w = ctx.measureText(str).width; if (w > o.maxW) ctx.scale(o.maxW / w, 1); }
  ctx.lineJoin = 'round'; ctx.miterLimit = 2;
  if (o.shadow) { ctx.save(); ctx.translate(o.shadow[0], o.shadow[1]); ctx.fillStyle = o.shadow[2] ?? 'rgb(20 8 40 / .45)'; if (o.strokes && o.strokes[0]) { ctx.strokeStyle = ctx.fillStyle; ctx.lineWidth = o.strokes[0][1]; ctx.strokeText(str, 0, 0); } ctx.fillText(str, 0, 0); ctx.restore(); }
  for (const [c, w] of o.strokes ?? []) { ctx.strokeStyle = c; ctx.lineWidth = w; ctx.strokeText(str, 0, 0); }
  if (o.grad) { const g = ctx.createLinearGradient(0, -size * .5, 0, size * .5); o.grad.forEach((c, i) => g.addColorStop(i / (o.grad.length - 1), c)); ctx.fillStyle = g; }
  else ctx.fillStyle = o.fill ?? IP.white;
  ctx.fillText(str, 0, 0);
  if (o.shine) { ctx.save(); ctx.globalCompositeOperation = 'source-atop'; ctx.fillStyle = 'rgb(255 255 255 / .45)'; ctx.fillRect(-4000, -size * .55, 8000, size * .32); ctx.restore(); }
  ctx.restore();
}
function dtextW(str, size, font = 'rammetto', spacing = 0) { return textW(str, size, font, spacing); }


// =====================================================================================================
// THE IDOL RIG (superseded: rig.js, loaded after this file, redraws the characters with the same options and outputs)
// =====================================================================================================
// idol(x, y, s, o): an ATTN! member (default TOKI), drawn with clean anime lineart and 2-tone cel shading.
// (x, y) = ground point between the feet; s = unit, standing height ≈ 10s at any sd. o.anchor: 'face' puts the face centre (between
// the eyes) at (x, y) for close-ups; 'chest' puts the neck base there. Every option is documented in STYLE.md; the main ones:
//   member ('TOKI'|'RELU'|'ADA'|'LOGI'), outfit ('stage'|'practice'), sd (0..1 super-deformed/chibi proportions)
//   pose (IK targets): hL/hR hand targets [x, y] relative to the neck base in s (+x screen right, +y down); gL/gR hand gestures;
//     eL/eR elbow side (1 out, −1 in); fL/fR foot targets relative to the ground point; bob (hip drop), sway (hip shift), lean, jump
//   head: turn (−1..1, + looks toward screen right), tilt (radians), nod (−1..1, + down), lookX/lookY (−1..1)
//   face: expr (preset from IDOL_EXPR), eyes, mouth, brows, blush (0..1), lid (0..1), wink ('L'|'R'), blink (pass t for auto blinks),
//     tears, sweat, gloom, puff, ahoge (curl|heart|q|droop|spring|bang|none), emote (vein|heart|note|spark|q|bang|zzz|sweat)
//   hair: swing (twin-tail swing, radians; auto from the beat if omitted); mic ('headset'|false; stage default headset);
//   rim (rim-light colour for this character), back (view from behind), flip, rot, shadow (false = no floor shadow)
function idol(x, y, s, o = {}) {
  const M = MEMBERS[o.member ?? 'TOKI'] || MEMBERS.TOKI;
  const P = idolProps(o.sd ?? 0);
  const O = { ...(IDOL_EXPR[o.expr] || {}) };
  for (const k of Object.keys(o)) if (o[k] !== undefined) O[k] = o[k];
  const lean = O.lean ?? 0, pelvis = [O.sway ?? 0, P.hipY + (O.bob ?? 0) - (O.jump ?? 0)];
  const rotP = (px, py) => { const c = Math.cos(lean), n = Math.sin(lean), dy = py - pelvis[1]; return [pelvis[0] + px * c - dy * n, pelvis[1] + px * n + dy * c]; };
  const neck = rotP(0, pelvis[1] + (P.neckY - P.hipY));
  const R = { s, M, P, O, lean, pelvis, rotP, neck };
  const hd = idolHeadPlace(R);
  R.head = hd;
  const oldLight = LIGHT;
  if (O.rim) LIGHT = { ...LIGHT, rim: O.rim };
  ctx.save();
  if (O.anchor === 'face') ctx.translate(x - (O.flip ? -1 : 1) * hd.fx * s, y - hd.fy * s);
  else if (O.anchor === 'chest') ctx.translate(x - (O.flip ? -1 : 1) * neck[0] * s, y - neck[1] * s);
  else ctx.translate(x, y);
  ctx.scale(s, s);
  if (O.flip) ctx.scale(-1, 1);
  if (O.rot) ctx.rotate(O.rot);
  if (O.shadow !== false && O.anchor === undefined) {
    const k = 1 - clamp((O.jump ?? 0) / 5) * .5;
    ctx.fillStyle = O.shadowCol ?? 'rgb(20 8 40 / .3)';
    ctx.beginPath(); ctx.ellipse((O.sway ?? 0) * .4, 0, 1.5 * k, .26 * k, 0, 0, TAU); ctx.fill();
  }
  R.lw = .05 * Math.pow(s / 70, -.3);           // outline width in s units (a touch thicker when small)
  if (O.back) idolBack(R); else idolFront(R);
  ctx.restore();
  LIGHT = oldLight;
  return R;
}

// Proportions: sd 0 = idol (≈5.8 heads), sd 1 = chibi (≈2.3 heads). s units; y up is negative.
const _PROP_A = { headH: 1.84, hipY: -5.42, neckY: -7.88, neckLen: .16, shW: .6, waistY: -6.5, waistW: .42, hipW: .6, skirtY: -4.05, skirtW: 1.18, thigh: 2.52, shin: 2.52, upper: 1.32, fore: 1.22, hand: .5, hipJ: .27, footY: -.3, eyeK: 1, limbW: 1.06, footS: 1, tail: 2.3 };
const _PROP_B = { headH: 4.4, hipY: -3.28, neckY: -5.3, neckLen: .12, shW: .74, waistY: -4.3, waistW: .6, hipW: .74, skirtY: -2.45, skirtW: 1.25, thigh: 1.5, shin: 1.4, upper: .92, fore: .82, hand: .62, hipJ: .34, footY: -.32, eyeK: 1.16, limbW: 1.45, footS: 1.35, tail: 1.05 };
function idolProps(sd) {
  if (!sd) return _PROP_A;
  const out = {}; for (const k in _PROP_A) out[k] = lerp(_PROP_A[k], _PROP_B[k], clamp(sd)); return out;
}
function idolHeadPlace(R) {
  const { P, O, neck } = R, H = P.headH, tilt = (O.tilt ?? 0) + R.lean * .5;
  const pivot = [neck[0], neck[1] - P.neckLen];                // chin-ish pivot
  const c = [pivot[0] + Math.sin(tilt) * H * .53, pivot[1] - Math.cos(tilt) * H * .53];
  const ey = .14;                                                 // eye line in head units
  return { x: c[0], y: c[1], h: H, rot: tilt, fx: c[0] - Math.sin(tilt) * ey * H, fy: c[1] + Math.cos(tilt) * ey * H };
}

// 2-bone IK: joint positions from root a to target t; bend = +1/−1 picks the side of the elbow/knee.
function ik2(a, t, l1, l2, bend) {
  let dx = t[0] - a[0], dy = t[1] - a[1], d = Math.hypot(dx, dy);
  const dmax = (l1 + l2) * .9995, dmin = Math.abs(l1 - l2) + 1e-3;
  if (d > dmax) { dx *= dmax / d; dy *= dmax / d; d = dmax; }
  if (d < dmin) { const k = dmin / (d || 1); dx *= k; dy *= k; d = dmin; }
  const ang = Math.atan2(dy, dx), cosA = clamp((l1 * l1 + d * d - l2 * l2) / (2 * l1 * d), -1, 1), A = Math.acos(cosA) * bend;
  return { j: [a[0] + Math.cos(ang + A) * l1, a[1] + Math.sin(ang + A) * l1], e: [a[0] + dx, a[1] + dy] };
}

// IK that places the joint on the outward side (away from the body midline, sd = side) when out = 1, inward when out = −1.
// out = 0 ('auto', arms): elbow tucked down when the hand is near the face, outward when the hand is raised high or lowered.
function ikOut(a, t, l1, l2, sd, out = 1) {
  const A = ik2(a, t, l1, l2, 1), B = ik2(a, t, l1, l2, -1);
  if (out === 0) { const dy = (t[1] - a[1]) / (l1 + l2); out = dy < -.4 || dy > .16 ? 1 : 2; }
  if (out === 2) return A.j[1] >= B.j[1] ? A : B;
  const aOut = A.j[0] * sd > B.j[0] * sd + 1e-6 || (Math.abs(A.j[0] - B.j[0]) < 1e-6 && A.j[1] > B.j[1]);
  return (aOut === (out >= 0)) ? A : B;
}

// ---------------- expressions (presets; any key can be overridden per call) ----------------
const IDOL_EXPR = {
  neutral: { eyes: 'open', mouth: 'smile', brows: 'soft' },
  smile: { eyes: 'open', mouth: 'smile', brows: 'soft', blush: .4 },
  joy: { eyes: 'happy', mouth: 'open', brows: 'up', blush: .65 },
  sing: { eyes: 'open', mouth: 'a', brows: 'up', blush: .4 },
  wink: { eyes: 'open', wink: 'R', mouth: 'tongue', brows: 'up', blush: .65 },
  surprised: { eyes: 'wide', mouth: 'O', brows: 'high', ahoge: 'bang', blush: .2 },
  shock: { eyes: 'dot', mouth: 'scream', brows: 'high', ahoge: 'spring', sweat: 1, gloom: .7, blush: 0 },
  smug: { eyes: 'open', lid: .45, mouth: 'smirk', brows: 'smug', blush: .35, lookX: .4 },
  sad: { eyes: 'teary', mouth: 'frown', brows: 'worried', ahoge: 'droop', blush: .3 },
  cry: { eyes: 'squeeze', mouth: 'wail', brows: 'worried', tears: 1, ahoge: 'droop', blush: .5 },
  pout: { eyes: 'open', lid: .22, mouth: 'pout', brows: 'angry', blush: .75, puff: 1, emote: 'vein' },
  love: { eyes: 'heart', mouth: 'open', brows: 'up', blush: .95, ahoge: 'heart' },
  sparkle: { eyes: 'star', mouth: 'open', brows: 'high', blush: .55 },
  fired: { eyes: 'open', lid: .28, mouth: 'teeth', brows: 'angry', blush: .2 },
  sleepy: { eyes: 'closed', mouth: 'o', brows: 'soft', ahoge: 'droop', emote: 'zzz' },
  dizzy: { eyes: 'spiral', mouth: 'wavy', brows: 'worried', blush: .35, ahoge: 'curl' },
  fluster: { eyes: 'squeeze', mouth: 'wavy', brows: 'worried', blush: 1, sweat: 1 },
  think: { eyes: 'open', lookX: .5, lookY: -.8, mouth: 'pout', brows: 'think', ahoge: 'q' },
  deadpan: { eyes: 'flat', mouth: 'flat', brows: 'flat', blush: .1 },
  aegyo: { eyes: 'happy', mouth: 'cat', brows: 'up', blush: 1, ahoge: 'heart' },
};

// ---------------- front view ----------------
function idolFront(R) {
  const { P, O, pelvis, rotP } = R, stage = (O.outfit ?? 'stage') === 'stage';
  const at = (x, dy) => rotP(x, pelvis[1] + dy);
  const dNeck = P.neckY - P.hipY;
  R.chest = at(0, dNeck); R.shoulder = sd => at(sd * P.shW, dNeck + .14); R.at = at; R.stage = stage;
  const swing = O.swing ?? (Math.sin(bpOf(T) * Math.PI) * .14 - (O.sway ?? 0) * .3 - R.lean * .8 + (O.jump ?? 0) * .06);
  R.swing = swing;
  headHairBack(R);                                            // back hair + twin-tails, behind everything
  const fL = O.fL ?? [-.34, 0], fR = O.fR ?? [.36, 0];
  for (const [sd, f] of [[-1, fL], [1, fR]]) {
    const hj = at(sd * P.hipJ, .1), ft = [f[0], f[1] + P.footY - (O.jump ?? 0)];
    const { j, e } = ikOut(hj, ft, P.thigh, P.shin, sd, O.kneeIn ? -1 : (O[sd < 0 ? 'kL' : 'kR'] ?? 1));
    idolLeg(R, sd, hj, j, e);
  }
  idolNeck(R);
  idolTorso(R);
  idolHead(R);
  const arms = [[-1, O.hL ?? [-.9, 2.72], O.gL ?? 'open'], [1, O.hR ?? [.9, 2.72], O.gR ?? 'open']];
  const hands = [];
  for (const [sd, h, g] of arms) {
    const ak = (P.upper + P.fore) / 2.54, sh = R.shoulder(sd), tgt = [R.chest[0] + h[0] * ak, R.chest[1] + h[1] * ak];
    const { j, e } = ikOut(sh, tgt, P.upper, P.fore, sd, O[sd < 0 ? 'eL' : 'eR'] ?? 0);
    hands.push({ sd, e, g });
    idolArm(R, sd, sh, j, e, g);
  }
  // two 'heart' hands close together make a glowing heart between them
  if (hands[0].g === 'heart' && hands[1].g === 'heart' && Math.hypot(hands[0].e[0] - hands[1].e[0], hands[0].e[1] - hands[1].e[1]) < 1.2) {
    const cx = (hands[0].e[0] + hands[1].e[0]) / 2, cy = (hands[0].e[1] + hands[1].e[1]) / 2 + .28, r = .42 * P.limbW;
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; glow(cx, cy, r * 2.4, '#FF4FA8', .5); ctx.restore();
    solid(heartPts(cx, cy, r, 36), 'rgb(255 110 180 / .55)', { shade: false, line: alpha(IP.white, .9), lw: R.lw * .9 });
  }
  if ((O.mic ?? (stage ? 'headset' : false)) === 'headset') headset(R);
  if (O.emote) { const h = R.head; emote(O.emote, h.x + .62 * h.h, h.y - .5 * h.h, h.h * .42, O.emoteK ?? 1); }
}

// ---------------- head ----------------
// Head-local units: head height ≈ 1 (crown → chin), origin = cranium centre, +y down, chin at y ≈ .53, eye line at .14.
function headXf(h) { ctx.translate(h.x, h.y); ctx.rotate(h.rot); ctx.scale(h.h, h.h); }
// 3/4 turn: project a point x on a sphere of radius r turned by tn (−1..1 ≈ ±36°).
function turnX(x, tn, r = .47) { const th = Math.asin(clamp(x / r, -1, 1)) + tn * .62; return r * Math.sin(clamp(th, -Math.PI / 2, Math.PI / 2)); }
function turnK(x, tn, r = .47) { const th0 = Math.asin(clamp(x / r, -1, 1)), th = th0 + tn * .62; return clamp(Math.cos(clamp(th, -1.5, 1.5)) / Math.max(.35, Math.cos(th0)), .12, 1.2); }

function jawPts(tn) {
  const base = [[-.46, -.08], [-.455, .1], [-.415, .25], [-.31, .39], [-.15, .49], [0, .53, 1], [.15, .49], [.31, .39], [.415, .25], [.455, .1], [.46, -.08]];
  return base.map(([x, y, c]) => {
    let X = turnX(x, tn);
    if (Math.sign(x) === Math.sign(tn) && Math.abs(x) > .25 && y > .05) X -= Math.sign(x) * Math.abs(tn) * .035;   // far cheek line
    return c ? [X, y, 1] : [X, y];
  });
}
function faceMk(tn) { return () => { ctx.beginPath(); ctx.arc(0, -.03, .46, 0, TAU, true); crPath(jawPts(tn), true, false); }; }

function idolHead(R) {
  const { M, O, P } = R, h = R.head;
  const tn = clamp(O.turn ?? 0, -1, 1);
  const L = R.lw / h.h * 1.05;                                  // line width in head units
  ctx.save(); headXf(h);
  // face: union of cranium + jaw with one clean outline
  const fm = faceMk(tn);
  fm(); ctx.strokeStyle = IP.skinLine; ctx.lineWidth = L * 2; ctx.lineJoin = 'round'; ctx.stroke();
  fm(); ctx.fillStyle = IP.skin; ctx.fill();
  ctx.save(); fm(); ctx.clip();
  // shadow cast by the fringe, and a far-cheek shade when turned
  ctx.fillStyle = IP.skinSh; ctx.save(); ctx.translate(-.012 * Math.sign(tn || 1), .06); bangsPath(M, tn); ctx.fill(); ctx.restore();
  if (tn) { ctx.globalAlpha = .6; ctx.beginPath(); ctx.ellipse(Math.sign(tn) * .52, .2, .09 + Math.abs(tn) * .06, .45, 0, 0, TAU); ctx.fill(); ctx.globalAlpha = 1; }
  // cheeks: soft blush always, hatch lines when blushing hard
  const bl = clamp(O.blush ?? .3);
  for (const sd of [-1, 1]) {
    const cx = turnX(sd * .28, tn), cy = .29, k = turnK(sd * .28, tn);
    const g = ctx.createRadialGradient(cx, cy, 0, cx, cy, .12);
    g.addColorStop(0, alpha(IP.cheek, .2 + bl * .5)); g.addColorStop(1, alpha(IP.cheek, 0));
    ctx.save(); ctx.translate(cx, cy); ctx.scale(k * 1.15, .62); ctx.translate(-cx, -cy); ctx.fillStyle = g; ctx.fillRect(cx - .13, cy - .13, .26, .26); ctx.restore();
    if (bl > .6) { ctx.save(); ctx.globalAlpha = clamp((bl - .6) * 2.5); for (let i = 0; i < 3; i++) { const bx = cx + (i - 1) * .04 * k; brush([[bx + .018 * k, cy - .025], [bx - .012 * k, cy + .025]], L * 1.1, '#E4506F', 'mid', { min: .3 }); } ctx.restore(); }
  }
  ctx.restore();
  if (O.puff) { const sd = tn > 0 ? -1 : 1; ctx.save(); ctx.strokeStyle = IP.skinLine; ctx.lineWidth = L; ctx.beginPath(); ctx.arc(turnX(sd * .455, tn) + sd * .01, .27, .085, sd > 0 ? -1.3 : Math.PI - 1.3 + 2.6 - 2.6, sd > 0 ? 1.3 : Math.PI + 1.3); ctx.stroke(); ctx.restore(); }
  // eyes
  const kind = O.eyes ?? 'open', blinkK = O.blink !== undefined ? blinkAt(O.blink) : 0;
  const ey = .14 + (O.nod ?? 0) * .05;
  for (const sd of [-1, 1]) {
    const nx = sd * .215, cx = turnX(nx, tn), k = turnK(nx, tn) * P.eyeK;
    const winkThis = O.wink && ((O.wink === 'L') === (sd < 0));
    const kk = winkThis ? 'happy' : blinkK && ['open', 'wide', 'teary', 'star', 'heart'].includes(kind) ? 'closed' : kind;
    idolEye(M, O, cx, ey, sd, k, kk, L, tn, P.eyeK);
  }
  // nose + mouth
  const mx = turnX(0, tn) + tn * .035;
  if (Math.abs(tn) > .2) brush([[mx + tn * .03, .255], [mx + tn * .06, .3], [mx + tn * .01, .31]], L * 1.1, alpha(IP.skinLine, .75), 'mid', { min: .3 });
  else { ctx.fillStyle = alpha(IP.skinLine, .7); ctx.beginPath(); ctx.ellipse(mx + .004, .3, .011, .006, 0, 0, TAU); ctx.fill(); }
  idolMouth(O.mouth ?? 'smile', mx, .395 + (O.nod ?? 0) * .03, L, tn, O);
  // front hair: side locks, fringe with shading, shine, strands; accessory; brows over the hair; ahoge
  sideLocks(R, tn, L);
  const bm = () => bangsPath(M, tn);
  bm(); ctx.fillStyle = M.hairCol; ctx.fill();
  ctx.save(); bm(); ctx.clip();
  crescent(bm, M.hairSh, -LIGHT.x * .045 - .01, -LIGHT.y * .03 + .035);
  hairShine(M, tn, L);
  bangStrands(M, tn, L);
  if (LIGHT.rim) crescent(bm, LIGHT.rim, LIGHT.rimX * .02, LIGHT.rimY * .02);
  ctx.restore();
  bm(); ctx.strokeStyle = M.hairLine; ctx.lineWidth = L; ctx.lineJoin = 'round'; ctx.stroke();
  hairAcc(M, tn, L);
  if (M.hair === 'twintails') for (const sd of [-1, 1]) { const far = Math.sign(tn) === sd ? Math.abs(tn) : 0; if (far < .55) bow(turnX(sd * .47, tn, .55), -.24, .15 * (1 - far * .3), M.col, L, sd * .3); }
  for (const sd of [-1, 1]) idolBrow(M, O, turnX(sd * .21, tn), .0 + (O.nod ?? 0) * .04, sd, turnK(sd * .21, tn), O.brows ?? 'soft', L);
  ahoge(M, O.ahoge ?? 'curl', tn, L);
  if (O.tears) tearsFx(tn, O.tears, L);
  if (O.sweat) sweatDrop(turnX(.44, tn) + .1, -.15, .12 * O.sweat, L);
  if (O.gloom) { ctx.save(); ctx.globalAlpha = O.gloom * .55; for (let i = 0; i < 8; i++) brush([[-.32 + i * .09, -.48], [-.32 + i * .09, -.18 + (i % 3) * .05]], .016, '#5B4F9E', 'end'); ctx.restore(); }
  ctx.restore();
}
function idolNeck(R) {
  const { O, P } = R, h = R.head, tn = clamp(O.turn ?? 0, -1, 1), L = R.lw / h.h * 1.05;
  ctx.save(); headXf(h);
  const nk = turnX(0, tn) * .3, nb = .53 + (P.neckLen + .3) / h.h;
  const neckP = [[nk - .11, .3], [nk + .11, .3], [nk + .12, nb], [nk - .12, nb]];
  solid(neckP, IP.skin, { shade: false, line: IP.skinLine, lw: L, sharp: true });
  ctx.save(); tracePath(neckP); ctx.clip(); ctx.fillStyle = IP.skinSh; ctx.beginPath(); ctx.ellipse(turnX(0, tn) * .9, .5, .26, .14, 0, 0, TAU); ctx.fill(); ctx.restore();
  ctx.restore();
}
function blinkAt(t) { const per = 3.3, k = frac(t / per + .37) * per; return k < .1 ? 1 : 0; }

// Fringe shapes per hairstyle: valleys (where locks part) and tips (lock points), left → right, head units.
const FRINGE = {
  twintails: { v: [[-.5, .02], [-.35, -.08], [-.19, -.11], [.01, -.16], [.18, -.1], [.33, -.08], [.5, .02]], t: [[-.43, .15], [-.27, .13], [-.08, .1], [.11, .12], [.26, .14], [.43, .13]], sw: [-1, -1, -.5, .6, 1, 1] },
  bob: { v: [[-.52, .1], [-.34, -.06], [-.12, -.08], [.1, -.1], [.3, -.06], [.52, .1]], t: [[-.44, .14], [-.23, .1], [-.01, .11], [.2, .1], [.42, .15]], sw: [-.4, -.2, 0, .2, .4] },
  long: { v: [[-.5, .02], [-.28, -.16], [.04, -.22], [.3, -.1], [.5, .02]], t: [[-.42, .16], [-.12, .08], [.18, .1], [.42, .15]], sw: [-1, -.6, .8, 1] },
  ponytail: { v: [[-.5, .05], [-.33, -.08], [-.15, -.1], [.04, -.14], [.22, -.08], [.38, -.06], [.5, .05]], t: [[-.42, .12], [-.24, .1], [-.06, .09], [.13, .1], [.3, .11], [.45, .12]], sw: [-.8, -.6, -.2, .4, .7, .9] },
};
function bangsPath(M, tn) {
  const F = FRINGE[M.hair] || FRINGE.twintails;
  const X = x => turnX(x, tn, .53);
  ctx.beginPath();
  // crown dome, left → right (over the top)
  ctx.moveTo(X(F.v[0][0] - .02), F.v[0][1] + .02);
  for (let i = 0; i <= 18; i++) { const a = Math.PI * 1.04 + i / 18 * Math.PI * .92; ctx.lineTo(X(Math.cos(a) * .525), -.035 + Math.sin(a) * .545); }
  ctx.lineTo(X(F.v[F.v.length - 1][0] + .02), F.v[F.v.length - 1][1] + .02);
  // fringe, right → left: valley → tip → valley with concave "icicle" edges; sw bends the lock
  for (let i = F.t.length - 1; i >= 0; i--) {
    const vR = F.v[i + 1], tp = F.t[i], vL = F.v[i], sw = F.sw[i] * .035;
    ctx.quadraticCurveTo(X(tp[0] + sw * .2 + (vR[0] - tp[0]) * .15), vR[1] + (tp[1] - vR[1]) * .62, X(tp[0] + sw), tp[1]);
    ctx.quadraticCurveTo(X(tp[0] + sw * .2 + (vL[0] - tp[0]) * .15), vL[1] + (tp[1] - vL[1]) * .62, X(vL[0]), vL[1]);
  }
  ctx.closePath();
}
function hairShine(M, tn, L) {
  // the "angel ring": a zig-zag band of shine across the crown
  ctx.save(); ctx.fillStyle = alpha(M.hairLt, .95);
  const X = x => turnX(x, tn, .53), n = 9;
  ctx.beginPath();
  const top = [], bot = [];
  for (let i = 0; i <= n; i++) {
    const u = i / n, a = Math.PI * 1.2 + u * Math.PI * .6, r = .44, y = -.02 + Math.sin(a) * r * .66;
    const x = Math.cos(a) * r;
    top.push([X(x), y - .018 - (i % 2) * .018]); bot.push([X(x * 1.02), y + .02 + (i % 2) * .028]);
  }
  ctx.moveTo(top[0][0], top[0][1]); for (const p of top) ctx.lineTo(p[0], p[1]); for (const p of bot.reverse()) ctx.lineTo(p[0], p[1]);
  ctx.closePath(); ctx.fill();
  ctx.restore();
}
function bangStrands(M, tn, L) {
  const F = FRINGE[M.hair] || FRINGE.twintails, X = x => turnX(x, tn, .53);
  F.t.forEach((tp, i) => {
    const sw = F.sw[i] * .035, x0 = tp[0] * .75;
    brush(qbez([X(x0), -.3], [X(lerp(x0, tp[0] + sw, .5) - sw * .5), -.08], [X(tp[0] + sw * .9), tp[1] - .03], 8), L * .9, alpha(M.hairLine, .55), 'end', { min: .1 });
  });
}
function sideLocks(R, tn, L) {
  const M = R.M, len = M.hair === 'bob' ? .56 : M.hair === 'long' ? .82 : .66;
  const sw = R.swing * .25;
  for (const sd of [-1, 1]) {
    if (Math.sign(tn) === sd && Math.abs(tn) > .75) continue;
    const bx = turnX(sd * .47, tn, .53);
    const pts = [[bx - sd * .1, -.05], [bx + sd * .05, -.02], [bx + sd * .06 + sw * .1, .2], [bx + sd * .035 + sw * .3, len * .78], [bx - sd * .01 + sw * .45, len, 1], [bx - sd * .045 + sw * .25, len * .7], [bx - sd * .08, .3], [bx - sd * .1, .12]];
    solid(pts, M.hairCol, { shade: M.hairSh, sh: .035, line: M.hairLine, lw: L, size: .2 });
    brush(qbez([bx - sd * .02, .02], [bx + sd * .02, .3], [bx + sw * .35, len * .82], 8), L * .8, alpha(M.hairLine, .5), 'end');
  }
}
function hairAcc(M, tn, L) {
  const X = x => turnX(x, tn, .53);
  if (M.acc === 'star') {
    const x = X(-.33), y = -.22;
    solid(starPts(x, y, .09, .47, 5, -TAU / 4 + .25), IP.neonGold, { shade: '#F09A20', sh: .018, line: '#8A4A10', lw: L * .8, sharp: true, size: .15 });
    ctx.fillStyle = IP.white; ctx.beginPath(); ctx.arc(x - .02, y - .025, .016, 0, TAU); ctx.fill();
  } else if (M.acc === 'clip') {
    for (let i = 0; i < 2; i++) { ctx.save(); ctx.translate(X(-.3) + i * .045, -.2 + i * .035); ctx.rotate(-.8); rrect(-.075, -.015, .15, .03, .015); ctx.fillStyle = i ? IP.white : M.col; ctx.fill(); ctx.strokeStyle = M.hairLine; ctx.lineWidth = L * .7; ctx.stroke(); ctx.restore(); }
  } else if (M.acc === 'ribbon') bow(X(.34), -.32, .1, M.col, L, .3);
}
// Ribbon bow: two loops, two tails, a knot. (x, y) knot centre, r loop size.
function bow(x, y, r, col, L, rot = 0) {
  ctx.save(); ctx.translate(x, y); ctx.rotate(rot);
  const dk = mixCol(col, IP.plum, .3);
  for (const sd of [-1, 1]) solid([[sd * r * .1, r * .1], [sd * r * .45, r * 1.25], [sd * r * .7, r * 1.1, 1], [sd * r * .55, r * .95], [sd * r * .2, r * .15]], dk, { shade: false, line: IP.line, lw: L * .8, size: r });
  for (const sd of [-1, 1]) solid([[0, 0], [sd * r * .55, -r * .7], [sd * r * 1.1, -r * .45], [sd * r * 1.15, r * .25], [sd * r * .6, r * .45], [0, 0, 1]], col, { shade: dk, sh: r * .22, line: IP.line, lw: L * .8, size: r });
  solid(ellPts(0, 0, r * .24, r * .3, 14), mixCol(col, IP.white, .15), { shade: false, line: IP.line, lw: L * .8 });
  ctx.restore();
}
// TOKI's cowlick is an expression channel: curl|heart|q|droop|spring|bang|none
function ahoge(M, kind, tn, L) {
  if (kind === 'none') return;
  const bx = turnX(.06, tn, .53), by = -.555, w = Math.sin(T * 5) * .012;
  let pts;
  if (kind === 'heart') {
    ctx.save(); ctx.translate(bx + .05, by - .17); ctx.rotate(.18);
    tracePath(heartPts(0, 0, .11, 32)); ctx.lineJoin = 'round';
    ctx.strokeStyle = M.hairLine; ctx.lineWidth = L * 3.4; ctx.stroke(); ctx.strokeStyle = M.hairCol; ctx.lineWidth = L * 1.6; ctx.stroke();
    ctx.restore();
    brush([[bx, by + .03], [bx + .03, by - .06]], L * 3, M.hairLine, 'start'); brush([[bx, by + .03], [bx + .03, by - .06]], L * 1.5, M.hairCol, 'start');
    return;
  }
  switch (kind) {
    case 'q': pts = [[bx, by + .02], [bx + .01, by - .1], [bx + .09, by - .19], [bx + .18, by - .15], [bx + .16, by - .06], [bx + .1, by - .03]]; break;
    case 'droop': pts = [[bx, by + .02], [bx + .05, by - .05], [bx + .14, by - .03], [bx + .2, by + .06]]; break;
    case 'spring': pts = [[bx, by + .02], [bx - .05, by - .06], [bx + .05, by - .12], [bx - .05, by - .18], [bx + .05, by - .24], [bx, by - .3]]; break;
    case 'bang': pts = [[bx, by + .02], [bx + .005, by - .12], [bx + .02, by - .27]]; break;
    default: pts = [[bx - .01, by + .03], [bx + .02 + w, by - .1], [bx + .11 + w, by - .17], [bx + .18, by - .14]];
  }
  const C = []; crSample(pts, 5, C);
  brush(C, L * 5.2, M.hairLine, 'start', { min: .22 });
  brush(C, L * 2.9, M.hairCol, 'start', { min: .1 });
}
// Sample a Catmull-Rom curve through points into `out`.
function crSample(P, n, out) {
  for (let i = 0; i < P.length - 1; i++) {
    const p0 = P[Math.max(0, i - 1)], p1 = P[i], p2 = P[i + 1], p3 = P[Math.min(P.length - 1, i + 2)];
    const seg = bez(p1, [p1[0] + (p2[0] - p0[0]) / 6, p1[1] + (p2[1] - p0[1]) / 6], [p2[0] - (p3[0] - p1[0]) / 6, p2[1] - (p3[1] - p1[1]) / 6], p2, n);
    out.push(...(i ? seg.slice(1) : seg));
  }
  return out;
}

function headHairBack(R) {
  const { M, O } = R, h = R.head, tn = clamp(O.turn ?? 0, -1, 1), swing = R.swing;
  ctx.save(); headXf(h);
  const L = R.lw / h.h * 1.05;
  if (M.hair === 'twintails') { const order = tn >= 0 ? [1, -1] : [-1, 1]; for (const sd of order) twinTail(R, sd, tn, swing, L); }
  if (M.hair === 'ponytail') ponyTail(R, tn, swing, L);
  const len = M.hair === 'long' ? 2.1 : M.hair === 'bob' ? .6 : M.hair === 'ponytail' ? .3 : .5, wb = M.hair === 'long' ? .62 : M.hair === 'bob' ? .6 : .52;
  const off = -tn * .05, sw = swing * .15;
  const back = [[-.5 + off, -.15], [-.54 + off, .15], [-wb + off + sw, len * .75], [-wb * .82 + off + sw * 1.4, len, 1], [-wb * .4 + off + sw, len * .9], [off + sw, len * .98], [wb * .4 + off + sw, len * .9], [wb * .82 + off + sw * 1.4, len, 1], [wb + off + sw, len * .75], [.54 + off, .15], [.5 + off, -.15], [.32 + off, -.5], [-.32 + off, -.5]];
  solid(back, M.hairSh, { shade: mixCol(M.hairSh, IP.plum, .25), sh: .05, line: M.hairLine, lw: L, size: .4 });
  ctx.restore();
}
function twinTail(R, sd, tn, swing, L) {
  const M = R.M;
  const far = Math.sign(tn) === sd ? Math.abs(tn) : 0, near = Math.sign(tn) === -sd ? Math.abs(tn) : 0;
  const root = [turnX(sd * .46, tn, .55), -.24];
  const len = R.P.tail, n = 10, sw = swing * (sd > 0 ? 1 : .9);
  // centreline: out and slightly up from the tie, arcing over and falling, a soft S at the end with an outward flick
  const C = [root]; let p = root;
  for (let i = 1; i <= n; i++) {
    const u = i / n;
    let a = u < .3 ? lerp(-.45, 1.38, easeOut(u / .3)) : 1.38 + .12 * Math.sin((u - .3) / .7 * Math.PI * 1.2) - (u > .8 ? (u - .8) * 1.6 : 0);
    a += sw * (.15 + .5 * u);
    const A = sd > 0 ? a : Math.PI - a, l = len / n;
    p = [p[0] + Math.cos(A) * l, p[1] + Math.sin(A) * l]; C.push(p);
  }
  const wid = u => (u < .2 ? lerp(.07, .24, Math.sin(u / .2 * Math.PI / 2)) : u < .62 ? lerp(.24, .2, (u - .2) / .42) : lerp(.2, .012, ((u - .62) / .38) ** 1.1)) * (1 - far * .15);
  const side = (k) => C.map((c, i) => { const q = C[Math.max(0, i - 1)], r = C[Math.min(n, i + 1)], dx = r[0] - q[0], dy = r[1] - q[1], l = Math.hypot(dx, dy) || 1; const w = wid(i / n) * k; return [c[0] - dy / l * w, c[1] + dx / l * w]; });
  const Lp = side(1), Rp = side(-1), tip = C[n];
  const pts = [...Lp.slice(0, n), [tip[0], tip[1], 1], ...Rp.slice(0, n).reverse()];
  // a second, darker lock behind for volume and a split tip
  const C2 = C.map((c, i) => [c[0] + sd * .07 * (i / n), c[1] - .05 * (i / n)]);
  const tip2 = C2[n];
  const pts2 = [...side(.8).slice(0, n).map((q, i) => [q[0] + sd * .07 * (i / n), q[1] - .05 * (i / n)]), [tip2[0] + sd * .08, tip2[1] - .12, 1], ...side(-.8).slice(0, n).map((q, i) => [q[0] + sd * .07 * (i / n), q[1] - .05 * (i / n)]).reverse()];
  solid(pts2, M.hairSh, { shade: mixCol(M.hairSh, IP.plum, .25), sh: .04, line: M.hairLine, lw: L, size: .4 });
  const g = ctx.createLinearGradient(root[0], root[1], tip[0], tip[1]);
  g.addColorStop(0, M.hairCol); g.addColorStop(.5, M.hairCol); g.addColorStop(1, M.tip ?? M.hairCol);
  ctx.save();
  crPath(pts); ctx.fillStyle = g; ctx.fill();
  ctx.save(); crPath(pts); ctx.clip();
  crescent(() => crPath(pts), alpha(M.hairSh, .9), sd * .06 - LIGHT.x * .03, -LIGHT.y * .02);
  for (const k of [-.5, .05, .55]) brush(side(k).slice(1, n - 1), L * .9, alpha(M.hairLine, .4), 'mid');
  brush(side(.3).slice(1, 4).map(q => [q[0], q[1]]), .06, alpha(M.hairLt, .95), 'mid');
  if (LIGHT.rim) crescent(() => crPath(pts), LIGHT.rim, LIGHT.rimX * .035, LIGHT.rimY * .035);
  ctx.restore();
  crPath(pts); ctx.strokeStyle = M.hairLine; ctx.lineWidth = L; ctx.lineJoin = 'round'; ctx.stroke();
  ctx.restore();
}
function ponyTail(R, tn, swing, L) {
  const M = R.M, root = [turnX(.12, tn, .5) - tn * .12, -.44], n = 8, len = R.P.tail * .78;
  const C = [root]; let p = root;
  for (let i = 1; i <= n; i++) {
    const u = i / n, a = lerp(-1.0, 1.72, easeOut(Math.min(1, u / .45))) + swing * (.2 + .5 * u) + (u > .7 ? (u - .7) * .8 : 0);
    const l = len / n; p = [p[0] + Math.cos(a) * l, p[1] + Math.sin(a) * l]; C.push(p);
  }
  const wid = u => u < .2 ? lerp(.07, .21, u / .2) : lerp(.21, .015, (u - .2) / .8);
  const side = k => C.map((c, i) => { const q = C[Math.max(0, i - 1)], r = C[Math.min(n, i + 1)], dx = r[0] - q[0], dy = r[1] - q[1], l = Math.hypot(dx, dy) || 1, w = wid(i / n) * k; return [c[0] - dy / l * w, c[1] + dx / l * w]; });
  const pts = [...side(1).slice(0, n), [C[n][0], C[n][1], 1], ...side(-1).slice(0, n).reverse()];
  solid(pts, M.hairCol, { shade: M.hairSh, sh: .06, line: M.hairLine, lw: L, size: .4 });
  brush(side(.2).slice(1, n - 1), L * .9, alpha(M.hairLine, .45), 'mid');
  bow(root[0] + .03, root[1] + .03, .13, IP.white, L, .4);
}

// ---------------- eyes ----------------
function idolEye(M, O, cx, cy, sd, k, kind, L, tn, eyeK = 1) {
  const ew = .155 * k, eh = .215 * eyeK;
  const lx = clamp(O.lookX ?? 0, -1, 1) * .04 + tn * .012, ly = clamp(O.lookY ?? 0, -1, 1) * .035;
  const lid = clamp(O.lid ?? 0), inner = -sd, dark = '#2A1433';
  ctx.save(); ctx.translate(cx, cy);
  switch (kind) {
    case 'happy': brush(qbez([-ew * 1.05, .035], [0, -.1], [ew * 1.05, .035], 12), L * 3, dark, 'mid', { min: .3 }); break;
    case 'closed': brush(qbez([-ew * 1.05, 0], [0, .065], [ew * 1.05, 0], 12), L * 2.6, dark, 'mid', { min: .3 }); brush([[-inner * ew * .95, .01], [-inner * ew * 1.25, -.02]], L * 1.4, dark, 'start'); break;
    case 'flat': brush([[-ew * 1.05, 0], [ew * 1.05, 0]], L * 2.6, dark, 'flat'); break;
    case 'squeeze': brush([[-inner * ew * 1.05, -.065], [inner * ew * .75, 0], [-inner * ew * 1.05, .065]], L * 2.8, dark, 'flat'); break;
    case 'spiral': {
      ctx.strokeStyle = dark; ctx.lineWidth = L * 1.2; ctx.beginPath();
      for (let i = 0; i <= 44; i++) { const a = i * .45 + T * 9 * sd, r = .004 + i * .0026; i ? ctx.lineTo(Math.cos(a) * r * k * 1.35, Math.sin(a) * r * 1.35) : ctx.moveTo(0, 0); }
      ctx.stroke(); break;
    }
    case 'dot': {
      ctx.beginPath(); ctx.ellipse(0, 0, ew * 1.05, eh * .55, 0, 0, TAU); ctx.fillStyle = IP.white; ctx.fill();
      ctx.strokeStyle = dark; ctx.lineWidth = L * 1.4; ctx.stroke();
      ctx.fillStyle = dark; ctx.beginPath(); ctx.arc(lx * .3, .005, .016, 0, TAU); ctx.fill();
      break;
    }
    default: {
      const wide = kind === 'wide', sc = wide ? 1.1 : 1;
      const top = -eh * .5 * sc + lid * eh * .55, bot = eh * .47 * sc;
      // eye opening: inner corner low, upper lid arching to a high point past the middle, outer corner sharp-ish
      const oc = [-inner * ew * 1.08, -eh * .08 + lid * .02], ic = [inner * ew * .98, eh * .04];
      const shape = () => {
        ctx.beginPath(); ctx.moveTo(ic[0], ic[1]);
        ctx.bezierCurveTo(inner * ew * .95, top * .7, -inner * ew * .3, top * 1.05, oc[0], oc[1]);
        ctx.bezierCurveTo(-inner * ew * 1.12, bot * .45, -inner * ew * .55, bot, 0, bot);
        ctx.bezierCurveTo(inner * ew * .55, bot, inner * ew * 1.02, bot * .55, ic[0], ic[1]);
        ctx.closePath();
      };
      shape(); ctx.fillStyle = IP.white; ctx.fill();
      ctx.save(); shape(); ctx.clip();
      const [c0, c1, c2] = M.eye;
      const iw = ew * .8, ih = eh * .47 * (wide ? .82 : 1), ix = lx * k, iy = ly + .014;
      const g = ctx.createLinearGradient(0, iy - ih, 0, iy + ih);
      g.addColorStop(0, c0); g.addColorStop(.5, c1); g.addColorStop(1, c2);
      ctx.beginPath(); ctx.ellipse(ix, iy, iw, ih, 0, 0, TAU); ctx.fillStyle = g; ctx.fill();
      ctx.lineWidth = L * .8; ctx.strokeStyle = c0; ctx.stroke();
      if (kind !== 'star' && kind !== 'heart') { ctx.beginPath(); ctx.ellipse(ix, iy - ih * .1, iw * (wide ? .28 : .42), ih * (wide ? .3 : .5), 0, 0, TAU); ctx.fillStyle = alpha(c0, .95); ctx.fill(); }
      ctx.fillStyle = alpha(c0, .6); ctx.beginPath(); ctx.ellipse(0, top - .005, ew * 1.4, eh * .2, 0, 0, TAU); ctx.fill();   // lid shadow on the iris
      ctx.fillStyle = alpha(c2, .85); ctx.beginPath(); ctx.ellipse(ix, iy + ih * .64, iw * .58, ih * .2, 0, 0, TAU); ctx.fill();
      if (kind === 'star') { solid(starPts(ix, iy, iw * .6, .45, 5, -TAU / 4), '#FFF6C8', { shade: false, line: false, sharp: true }); ctx.fillStyle = IP.white; ctx.beginPath(); ctx.arc(ix + iw * .42, iy + ih * .4, iw * .12, 0, TAU); ctx.fill(); }
      else if (kind === 'heart') { solid(heartPts(ix, iy + ih * .05, iw * .88, 32), '#FF3D8B', { shade: false, line: false }); ctx.fillStyle = IP.white; ctx.beginPath(); ctx.ellipse(ix - iw * .35, iy - ih * .2, iw * .16, ih * .13, -.5, 0, TAU); ctx.fill(); }
      else {
        ctx.fillStyle = IP.white;
        ctx.beginPath(); ctx.ellipse(ix - iw * .32, iy - ih * .36, iw * .32, ih * .25, -.45, 0, TAU); ctx.fill();
        ctx.beginPath(); ctx.arc(ix + iw * .4, iy + ih * .34, iw * .13, 0, TAU); ctx.fill();
        ctx.globalAlpha = .75; ctx.beginPath(); ctx.arc(ix - iw * .05, iy + ih * .55, iw * .07, 0, TAU); ctx.fill(); ctx.globalAlpha = 1;
      }
      if (kind === 'teary') { ctx.fillStyle = alpha('#CDEFFF', .6); ctx.fillRect(-ew * 1.3, bot - .065 + Math.sin(T * 18) * .004, ew * 2.6, .08); ctx.fillStyle = IP.white; ctx.beginPath(); ctx.ellipse(0, bot - .04, ew * .7, .012, 0, 0, TAU); ctx.fill(); }
      ctx.restore();
      // lashes: heavy upper line thickening toward the outer corner with a flick, thin lower lash, crease
      const lash = bez([ic[0] + inner * .01, ic[1] - .005], [inner * ew * .95, top * .72 - .012], [-inner * ew * .3, top * 1.07 - .012], [oc[0], oc[1] - .006], 14);
      brush(lash, L * 3.6, dark, 'end', { min: .2 });
      brush(qbez([oc[0] + inner * .03, oc[1] - .005], [oc[0] - inner * .02, oc[1] - .02], [oc[0] - inner * .05, oc[1] - .045], 5), L * 2, dark, 'start', { min: .2 });
      brush(qbez([-inner * ew * .98, bot * .35], [-inner * ew * .75, bot * .98], [-inner * ew * .15, bot * 1.02], 8), L * 1.3, alpha(dark, .85), 'start', { min: .15 });
      if (lid < .3) brush(qbez([inner * ew * .45, top - .05], [-inner * ew * .2, top - .075], [-inner * ew * .9, top * .5 - .045], 8), L * .9, alpha(IP.skinLine, .7), 'mid');
    }
  }
  ctx.restore();
}
function idolBrow(M, O, cx, cy, sd, k, kind, L) {
  const inner = -sd, w = .1 * k;
  let a = [inner * w, 0], c = [0, -.028], b = [-inner * w, .005];
  switch (kind) {
    case 'up': a = [inner * w, -.02]; c = [0, -.045]; b = [-inner * w, -.005]; break;
    case 'high': a = [inner * w, -.055]; c = [0, -.085]; b = [-inner * w, -.035]; break;
    case 'worried': a = [inner * w, -.055]; c = [0, -.035]; b = [-inner * w, .02]; break;
    case 'angry': a = [inner * w, .045]; c = [0, .0]; b = [-inner * w, -.03]; break;
    case 'smug': if (sd > 0) { a = [inner * w, -.045]; c = [0, -.08]; b = [-inner * w, -.035]; } else { a = [inner * w, .02]; c = [0, -.005]; b = [-inner * w, 0]; } break;
    case 'think': if (sd > 0) { a = [inner * w, -.05]; c = [0, -.075]; b = [-inner * w, -.025]; } else { a = [inner * w, .015]; c = [0, -.015]; b = [-inner * w, 0]; } break;
    case 'flat': a = [inner * w, 0]; c = [0, 0]; b = [-inner * w, 0]; break;
  }
  ctx.save(); ctx.translate(cx, cy);
  brush(qbez(a, c, b, 8), L * 1.9, alpha(M.hairLine, .95), 'start', { min: .25 });
  ctx.restore();
}

// ---------------- mouth ----------------
// shapes: smile|open|o|O|a|i|u|e|cat|flat|frown|pout|wavy|smirk|teeth|tongue|scream|wail|closed
function idolMouth(kind, x, y, L, tn, O) {
  ctx.save(); ctx.translate(x, y); ctx.scale(1 - Math.abs(tn) * .25, 1);
  const inside = '#9A2E4E', tongue = '#FF8AA6', line = '#7A2440';
  const open = (w, h, flat = .15, teeth = false, tng = true) => {
    const mk = () => { ctx.beginPath(); ctx.moveTo(-w, -h * flat); ctx.quadraticCurveTo(0, -h * (flat + .3), w, -h * flat); ctx.bezierCurveTo(w * .95, h * .75, -w * .95, h * .75, -w, -h * flat); ctx.closePath(); };
    mk(); ctx.fillStyle = inside; ctx.fill();
    ctx.save(); mk(); ctx.clip();
    if (tng) { ctx.fillStyle = tongue; ctx.beginPath(); ctx.ellipse(0, h * .6, w * .72, h * .4, 0, 0, TAU); ctx.fill(); }
    if (teeth) { ctx.fillStyle = IP.white; ctx.fillRect(-w, -h, w * 2, h * .72); }
    ctx.restore();
    mk(); ctx.strokeStyle = line; ctx.lineWidth = L * 1.05; ctx.lineJoin = 'round'; ctx.stroke();
  };
  const stroke = (pts, w = 1.3, prof = 'mid') => brush(pts, L * w, line, prof, { min: .35 });
  switch (kind) {
    case 'open': open(.07, .08, .1); break;
    case 'a': open(.058, .09, .12); break;
    case 'e': open(.075, .05, .2, true); break;
    case 'i': open(.075, .032, .2, true, false); break;
    case 'o': ctx.beginPath(); ctx.ellipse(0, .01, .03, .038, 0, 0, TAU); ctx.fillStyle = inside; ctx.fill(); ctx.strokeStyle = line; ctx.lineWidth = L; ctx.stroke(); break;
    case 'u': ctx.beginPath(); ctx.ellipse(0, .005, .02, .024, 0, 0, TAU); ctx.fillStyle = inside; ctx.fill(); ctx.strokeStyle = line; ctx.lineWidth = L; ctx.stroke(); break;
    case 'O': { const mk = () => { ctx.beginPath(); ctx.ellipse(0, .025, .05, .068, 0, 0, TAU); }; mk(); ctx.fillStyle = inside; ctx.fill(); ctx.save(); mk(); ctx.clip(); ctx.fillStyle = tongue; ctx.beginPath(); ctx.ellipse(0, .08, .04, .028, 0, 0, TAU); ctx.fill(); ctx.restore(); mk(); ctx.strokeStyle = line; ctx.lineWidth = L * 1.05; ctx.stroke(); break; }
    case 'scream': open(.1, .15, .25); break;
    case 'wail': { const mk = () => { ctx.beginPath(); ctx.moveTo(-.09, .045); ctx.quadraticCurveTo(0, -.075, .09, .045); ctx.quadraticCurveTo(0, .095, -.09, .045); ctx.closePath(); }; mk(); ctx.fillStyle = inside; ctx.fill(); ctx.strokeStyle = line; ctx.lineWidth = L; ctx.stroke(); break; }
    case 'cat': stroke([[-.06, -.01], [-.03, .018], [0, 0], [.03, .018], [.06, -.01]], 1.4); break;
    case 'flat': stroke([[-.035, 0], [.035, 0]]); break;
    case 'frown': stroke(qbez([-.045, .018], [0, -.022], [.045, .018], 6)); break;
    case 'pout': ctx.beginPath(); ctx.ellipse(0, .002, .022, .014, 0, 0, TAU); ctx.fillStyle = '#EE7890'; ctx.fill(); stroke(qbez([-.032, .012], [0, -.02], [.032, .012], 6), 1.2); break;
    case 'wavy': stroke([[-.06, .005], [-.04, -.012], [-.02, .01], [0, -.012], [.02, .01], [.04, -.012], [.06, .005]], 1.2, 'flat'); break;
    case 'smirk': stroke(qbez([-.045, .008], [.01, .028], [.06, -.028], 8), 1.4, 'end'); break;
    case 'teeth': { const mk = () => { ctx.beginPath(); ctx.moveTo(-.07, -.012); ctx.quadraticCurveTo(0, .006, .07, -.012); ctx.quadraticCurveTo(0, .085, -.07, -.012); ctx.closePath(); }; mk(); ctx.fillStyle = IP.white; ctx.fill(); ctx.strokeStyle = line; ctx.lineWidth = L; ctx.stroke(); brush([[-.05, .022], [.05, .022]], L * .6, alpha(line, .5), 'mid'); break; }
    case 'tongue': stroke(qbez([-.05, -.012], [0, .036], [.05, -.012], 8), 1.3); ctx.beginPath(); ctx.ellipse(.018, .02, .022, .028, .3, 0, Math.PI); ctx.fillStyle = tongue; ctx.fill(); ctx.strokeStyle = line; ctx.lineWidth = L * .8; ctx.stroke(); break;
    case 'closed': stroke([[-.028, 0], [.028, 0]], 1.1); break;
    default: stroke(qbez([-.048, -.01], [0, .032], [.048, -.01], 8), 1.35);       // smile
  }
  ctx.restore();
}
function tearsFx(tn, k, L) {
  for (const sd of [-1, 1]) {
    const x = turnX(sd * .2, tn), y0 = .23, len = .22 + .16 * frac(T * 2.2 + (sd > 0 ? .4 : 0));
    ctx.save(); ctx.globalAlpha = .9 * k;
    brush([[x - sd * .03, y0], [x + sd * .0, y0 + len * .5], [x - sd * .02, y0 + len]], .055, '#A8E0FF', 'mid', { min: .55 });
    ctx.restore();
  }
}
function sweatDrop(x, y, r, L) {
  ctx.save(); ctx.translate(x, y);
  solid([[0, -r * 1.35, 1], [r * .75, r * .15], [0, r * .8], [-r * .75, r * .15]], '#C5EBFF', { shade: '#86C8F2', sh: r * .25, line: '#3A6FA0', lw: L * .9, size: r });
  ctx.fillStyle = IP.white; ctx.beginPath(); ctx.ellipse(-r * .25, r * .08, r * .12, r * .22, 0, 0, TAU); ctx.fill();
  ctx.restore();
}
// Anime symbols near a head: vein|heart|note|spark|q|bang|zzz|sweat. (x, y) centre, r size, k pop 0..1
function emote(kind, x, y, r, k = 1) {
  if (k <= 0) return;
  ctx.save(); ctx.translate(x, y); const s = backOut(clamp(k), 2.5); ctx.scale(s, s);
  // at least 1.5 screen pixels, whatever the current scale (inside idol() the units are figure-sized)
  const m = ctx.getTransform(), lw = Math.max(1.5 * RS / (Math.hypot(m.a, m.b) || 1), r * .08);
  switch (kind) {
    case 'vein': for (let i = 0; i < 4; i++) { ctx.save(); ctx.rotate(i * TAU / 4 + .25); brush(qbez([r * .14, -r * .58], [r * .16, -r * .16], [r * .58, -r * .14], 8), r * .2, IP.red, 'mid', { min: .5 }); ctx.restore(); } break;
    case 'heart': solid(heartPts(0, 0, r * .6, 32), '#FF4F9A', { shade: '#D02F73', line: IP.line, lw, size: r }); break;
    case 'note': dtext('♪', 0, 0, r * 1.2, { font: 'archivo', fill: IP.neonPink, strokes: [[IP.white, r * .14]] }); break;
    case 'spark': for (const [dx, dy, rr] of [[0, 0, .6], [r * .6, -r * .5, .35], [-r * .5, r * .4, .25]]) sparkle(dx, dy, r * rr, 0, IP.white); break;
    case 'q': dtext('?', 0, 0, r * 1.3, { fill: IP.neonCyan, strokes: [[IP.line, r * .24]] }); break;
    case 'bang': dtext('!', 0, 0, r * 1.4, { fill: IP.neonGold, strokes: [[IP.line, r * .24]] }); break;
    case 'zzz': dtext('z', 0, 0, r * .6, { fill: IP.lilac, strokes: [[IP.line, r * .1]] }); dtext('Z', r * .5, -r * .5, r * .9, { fill: IP.lilac, strokes: [[IP.line, r * .13]] }); break;
    case 'sweat': sweatDrop(0, 0, r * .45, lw); break;
  }
  ctx.restore();
}

// ---------------- torso & outfit ----------------
function idolTorso(R) {
  const { M, P, O, at } = R, lw = R.lw, lwI = lw * .6, stage = R.stage;
  const dW = P.waistY - P.hipY, dN = P.neckY - P.hipY, dS = P.skirtY - P.hipY, sw = P.shW, ww = P.waistW, pw = P.hipW;
  const tx = clamp(O.turn ?? 0, -1, 1) * .1;                     // chest details slide with the turn
  const skSw = (R.swing ?? 0) * .12 + Math.sin(bpOf(T) * Math.PI + .7) * .045 + (O.sway ?? 0) * -.12;
  if (stage) {
    // skirt: pleated A-line, knee length, with a white petticoat frill
    const hemPts = [];
    for (let i = 0; i <= 10; i++) { const u = i / 10, x = lerp(P.skirtW, -P.skirtW, u); hemPts.push(at(x + skSw * (1 + Math.abs(x) * .6), dS + (1 - (x / P.skirtW) ** 2) * .08 + (i % 2 ? .07 : 0))); }
    const frill = [at(-ww, dW + .1), at(ww, dW + .1), ...hemPts.map((p, i) => [p[0] + (i < 5 ? .03 : -.03), p[1] + .17 + (i % 2 ? 0 : .04)])];
    solid(frill, IP.white, { shade: '#D8CEF4', sh: .07, line: IP.line, lw, size: 1 });
    const skirt = [at(-ww - .03, dW + .06), at(ww + .03, dW + .06), ...hemPts];
    solid(skirt, M.col, { shade: mixCol(M.col, IP.plum, .32), sh: .2, line: IP.line, lw, size: 1.4, grad: [mixCol(M.col, IP.white, .22), M.col] });
    for (let i = 1; i < 10; i += 2) ln([at(lerp(-ww, ww, 1 - i / 10), dW + .15), hemPts[i]], alpha(mixCol(M.col, IP.plum, .55), .55), lwI);
    for (let i = 2; i < 10; i += 2) ln([at(lerp(-ww, ww, 1 - i / 10) * .9, dW + .3), [hemPts[i][0], hemPts[i][1] - .05]], alpha(IP.white, .35), lwI * 1.2);
  } else {
    solid([at(-pw - .05, dW - .1), at(pw + .05, dW - .1), at(pw + .12, .55), at(-pw - .12, .55)], '#3D3868', { shade: '#282352', sh: .1, line: IP.line, lw, size: 1 });
  }
  if (stage) {
    const body = [at(-sw - .03, dN + .16), at(-sw * .45, dN + .02), at(sw * .45, dN + .02), at(sw + .03, dN + .16), at(sw * .85, dN + .72), at(ww + .03, dW + .1), at(-ww - .03, dW + .1), at(-sw * .85, dN + .72)];
    solid(body, IP.white, { shade: '#D8CCF2', sh: .13, line: IP.line, lw, size: 1.2 });
    for (const sd of [-1, 1]) {
      const pan = [at(sd * (sw + .03), dN + .16), at(sd * sw * .4 + tx, dN + .06), at(sd * .15 + tx, dN + .78), at(sd * (ww + .03), dW + .1), at(sd * sw * .86, dN + .72)];
      solid(pan, M.col, { shade: mixCol(M.col, IP.plum, .32), sh: .09, line: IP.line, lw: lwI * 1.3, size: .6 });
    }
    solid([at(-ww - .04, dW - .03), at(ww + .04, dW - .03), at(ww + .04, dW + .13), at(-ww - .04, dW + .13)], mixCol(M.col, IP.plum, .2), { shade: false, line: IP.line, lw: lwI * 1.3, sharp: true });
    for (let i = 0; i < 2; i++) { const b = at(tx, dN + .98 + i * .26); solid(ellPts(b[0], b[1], .055, .055, 12), IP.gold, { shade: '#C98A18', sh: .02, line: '#7A4A10', lw: lwI, size: .1 }); }
    const cl = [at(-sw * .8 + tx * .5, dN + .08), at(-.06 + tx, dN + .1), at(tx, dN + .4, 1), at(.06 + tx, dN + .1), at(sw * .8 + tx * .5, dN + .08), at(sw * .74 + tx * .5, dN + .36), at(.12 + tx, dN + .5), at(-.12 + tx, dN + .5), at(-sw * .74 + tx * .5, dN + .36)];
    solid(cl, IP.white, { shade: '#D8CCF2', sh: .05, line: IP.line, lw: lwI * 1.4, size: .6 });
    ln([at(-sw * .64 + tx * .5, dN + .3), at(-.12 + tx, dN + .43)], M.col, lwI * 1.5); ln([at(sw * .64 + tx * .5, dN + .3), at(.12 + tx, dN + .43)], M.col, lwI * 1.5);
    const rb = at(tx, dN + .48);
    bow(rb[0], rb[1], .22 * (P.limbW > 1.2 ? 1.2 : 1), M.col, lwI * 1.4, R.lean);
  } else {
    const body = [at(-sw - .1, dN + .12), at(-sw * .4, dN), at(sw * .4, dN), at(sw + .1, dN + .12), at(sw + .15, dN + 1.35), at(pw + .14, dW + .52), at(-pw - .14, dW + .52), at(-sw - .15, dN + 1.35)];
    solid(body, M.lt, { shade: mixCol(M.lt, M.col, .45), sh: .16, line: IP.line, lw, size: 1.2 });
    solid([at(-sw * .75 + tx, dN + .04), at(sw * .75 + tx, dN + .04), at(sw * .5 + tx, dN + .34), at(-sw * .5 + tx, dN + .34)], mixCol(M.lt, M.col, .3), { shade: false, line: IP.line, lw: lwI * 1.3 });
    ln([at(-.12 + tx, dN + .3), at(-.14 + tx, dN + .8)], IP.white, lwI * 1.7); ln([at(.12 + tx, dN + .3), at(.14 + tx, dN + .8)], IP.white, lwI * 1.7);
    const c = at(tx, dN + 1.05);
    ctx.save(); ctx.translate(c[0], c[1]); ctx.rotate(R.lean); dtext('A!', 0, 0, .44, { fill: M.col, strokes: [[IP.white, .07]] }); ctx.restore();
  }
}

// ---------------- limbs ----------------
function capsule(a, b, w0, w1, begin = true) {
  const dx = b[0] - a[0], dy = b[1] - a[1], l = Math.hypot(dx, dy) || 1e-6, nx = -dy / l, ny = dx / l, ang = Math.atan2(dy, dx);
  if (begin) ctx.beginPath();
  ctx.moveTo(a[0] + nx * w0, a[1] + ny * w0);
  ctx.lineTo(b[0] + nx * w1, b[1] + ny * w1);
  ctx.arc(b[0], b[1], w1, ang + Math.PI / 2, ang - Math.PI / 2, true);
  ctx.lineTo(a[0] - nx * w0, a[1] - ny * w0);
  ctx.arc(a[0], a[1], w0, ang - Math.PI / 2, ang + Math.PI / 2, true);
  ctx.closePath();
}
// A limb as ONE smooth outline through pts with radii ws (round caps), so cel shading and outlines have no seams at joints.
function limbOutline(pts, ws) {
  const n = pts.length, Lf = [], Rt = [], dirs = [];
  for (let i = 0; i < n; i++) {
    let dx = 0, dy = 0;
    for (const [a, b] of [[i - 1, i], [i, i + 1]]) if (a >= 0 && b < n) { const l = Math.hypot(pts[b][0] - pts[a][0], pts[b][1] - pts[a][1]) || 1; dx += (pts[b][0] - pts[a][0]) / l; dy += (pts[b][1] - pts[a][1]) / l; }
    const l = Math.hypot(dx, dy) || 1; dx /= l; dy /= l; dirs.push([dx, dy]);
    Lf.push([pts[i][0] - dy * ws[i], pts[i][1] + dx * ws[i]]); Rt.push([pts[i][0] + dy * ws[i], pts[i][1] - dx * ws[i]]);
  }
  const out = [...Lf];
  const cap = (c, w, th, from) => { for (let k = 1; k < 7; k++) { const a = th + from - k / 7 * Math.PI; out.push([c[0] + Math.cos(a) * w, c[1] + Math.sin(a) * w]); } };
  const thE = Math.atan2(dirs[n - 1][1], dirs[n - 1][0]); cap(pts[n - 1], ws[n - 1], thE, Math.PI / 2);
  for (let i = n - 1; i >= 0; i--) out.push(Rt[i]);
  const th0 = Math.atan2(dirs[0][1], dirs[0][0]); cap(pts[0], ws[0], th0, -Math.PI / 2);
  return out;
}
function limbChain(pts, ws, fill, shade, line, lw) {
  const P = limbOutline(pts, ws), sz = (ws[0] + ws[ws.length - 1]);
  solid(P, fill, { shade, sh: sz * .5, line, lw, size: sz, rimW: sz * .16 });
}
function idolLeg(R, sd, hj, knee, ank) {
  const { P, M } = R, k = P.limbW, lw = R.lw, stage = R.stage;
  const at = (u) => [lerp(knee[0], ank[0], u), lerp(knee[1], ank[1], u)];
  const midT = [lerp(hj[0], knee[0], .5), lerp(hj[1], knee[1], .5)], calf = at(.3), bootTop = at(.42);
  // calf bulges to the outside a little
  const nx = (ank[1] - knee[1]), ny = -(ank[0] - knee[0]), nl = Math.hypot(nx, ny) || 1, cb = .03 * k * sd;
  const calfP = [calf[0] + nx / nl * cb * (sd > 0 ? 1 : -1) * sd, calf[1]];
  if (stage) {
    limbChain([hj, midT, knee, calfP, bootTop], [.27 * k, .22 * k, .16 * k, .175 * k, .15 * k], IP.skin, IP.skinSh, IP.skinLine, lw);
    const toe = [ank[0] + sd * .05, ank[1] + .24];
    limbChain([bootTop, at(.75), ank, toe], [.17 * k, .145 * k, .13 * k, .16 * k * P.footS], IP.white, '#D4C8F0', IP.line, lw);
    ln([[bootTop[0] - .17 * k, bootTop[1] + .03], [bootTop[0] + .17 * k, bootTop[1] + .03]], M.col, lw * 2.6, { cap: 'round' });
    ln([[toe[0] - .17 * k, toe[1] + .06], [toe[0] + .17 * k, toe[1] + .06]], mixCol(M.col, IP.plum, .2), lw * 2.2);
  } else {
    limbChain([hj, midT, knee, calf, ank], [.3 * k, .27 * k, .23 * k, .23 * k, .19 * k], '#3D3868', '#282352', IP.line, lw);
    ln([hj, knee, ank].map(p => [p[0] + sd * .16 * k, p[1]]), alpha(IP.white, .75), lw * 1.2);
    const toe = [ank[0] + sd * .05, ank[1] + .24];
    limbChain([[ank[0], ank[1] - .05], toe], [.2 * k, .19 * k * P.footS], '#FAFAFF', '#CFC6EA', IP.line, lw);
    ln([[toe[0] - .17 * k, toe[1] + .1], [toe[0] + .17 * k, toe[1] + .1]], M.col, lw * 2);
  }
}
function idolArm(R, sd, sh, el, wr, g) {
  const { P, M } = R, k = P.limbW, lw = R.lw;
  if (R.stage) {
    limbChain([sh, [lerp(sh[0], el[0], .5), lerp(sh[1], el[1], .5)], el, wr], [.16 * k, .14 * k, .115 * k, .095 * k], IP.skin, IP.skinSh, IP.skinLine, lw);
    const a = Math.atan2(el[1] - sh[1], el[0] - sh[0]);
    ctx.save(); ctx.translate(sh[0], sh[1]); ctx.rotate(a);
    solid(ellPts(.2 * k, 0, .36 * k, .27 * k, 28), IP.white, { shade: '#D4C8F0', sh: .08, line: IP.line, lw, size: .5 });
    ln([[.5 * k, -.19 * k], [.52 * k, .19 * k]], M.col, lw * 2.4);
    ctx.restore();
    const b = Math.atan2(wr[1] - el[1], wr[0] - el[0]);
    ctx.save(); ctx.translate(lerp(el[0], wr[0], .84), lerp(el[1], wr[1], .84)); ctx.rotate(b);
    solid(ellPts(0, 0, .055 * k, .14 * k, 14), M.col, { shade: false, line: IP.line, lw: lw * .8, size: .2 });
    ctx.restore();
  } else limbChain([sh, el, wr], [.2 * k, .17 * k, .14 * k], M.lt, mixCol(M.lt, M.col, .45), IP.line, lw);
  hand(wr, Math.atan2(wr[1] - el[1], wr[0] - el[0]), P.hand * (R.stage ? 1 : 1.05), g, sd, lw, R.O, M);
}

// Hand in its own frame: origin wrist, +x along the forearm, unit = hand length. The thumb goes toward the body's midline.
// g: open|wave|fist|point|peace|fheart|heart|thumb|mic|flat. O.wristL/wristR rotate the hand; O.heartPop (0..1) pops the finger heart.
function hand(w, ang, size, g, sd, lw, O = {}, M = MEMBERS.TOKI) {
  const wr = O[sd < 0 ? 'wristL' : 'wristR'] ?? 0;
  const a = ang + wr * (sd < 0 ? -1 : 1);
  ctx.save(); ctx.translate(w[0], w[1]); ctx.rotate(a);
  // which local y side faces the body midline? (screen x of local +y is −sin a)
  const flip = (-Math.sin(a) * -sd) > 0 ? 1 : -1;
  ctx.scale(size, size * flip * (O[sd < 0 ? 'palmL' : 'palmR'] ?? 1));
  const L = lw / size;
  const parts = [];
  const F = (x0, y0, x1, y1, r = .1, x2, y2) => parts.push(() => { capsule([x0, y0], [x1, y1], r, r * .92, false); if (x2 !== undefined) capsule([x1, y1], [x2, y2], r * .92, r * .85, false); });
  const palm = (rx = .3, ry = .24, cx = .3) => parts.push(() => { ctx.moveTo(cx + rx, 0); ctx.ellipse(cx, 0, rx, ry, 0, 0, TAU); });
  const wristC = () => parts.push(() => capsule([-.05, 0], [.2, 0], .15, .2, false));
  wristC();
  switch (g) {
    case 'fist': palm(.3, .27, .32); F(.45, .2, .58, .12, .11); break;
    case 'point': palm(.28, .25, .3); F(.4, .15, .95, .15, .1); F(.35, .24, .55, .16, .1); break;
    case 'peace': palm(.28, .25, .3); F(.42, .14, .92, .34, .095); F(.45, -.02, .95, -.08, .095); F(.35, .24, .55, .12, .1); break;
    case 'thumb': palm(.3, .27, .32); F(.3, .2, .34, .72, .12); break;
    case 'fheart': palm(.3, .27, .32); F(.45, .02, .78, .3, .1); F(.25, .24, .78, .2, .105); break;
    case 'heart': palm(.28, .24, .28); F(.42, .14, .72, .2, .09, .82, .02); F(.42, -.04, .72, -.02, .09, .8, -.18); F(.25, .2, .45, .45, .1); break;
    case 'mic': palm(.3, .27, .32); break;
    case 'flat': palm(.3, .22, .3); F(.4, 0, .92, 0, .2); F(.25, .2, .5, .38, .1); break;
    case 'wave': palm(.3, .25, .3); for (let i = 0; i < 4; i++) F(.45, -.14 + i * .1, .92 - Math.abs(i - 1.3) * .05, -.34 + i * .22, .085); F(.25, .22, .45, .5, .1); break;
    default: palm(.3, .24, .3); for (let i = 0; i < 4; i++) F(.45, -.13 + i * .085, .86 - Math.abs(i - 1.2) * .05, -.17 + i * .11, .085); F(.25, .2, .5, .42, .1);
  }
  const mk = () => { ctx.beginPath(); for (const p of parts) p(); };
  mk(); ctx.strokeStyle = IP.skinLine; ctx.lineWidth = L * 2; ctx.lineJoin = 'round'; ctx.stroke();
  ctx.fillStyle = IP.skin; for (const p of parts) { ctx.beginPath(); p(); ctx.fill(); }
  ctx.save(); ctx.beginPath(); parts[1](); ctx.clip(); ctx.fillStyle = IP.skinSh; ctx.beginPath(); ctx.ellipse(.3, -.3 * flip, .45, .16, 0, 0, TAU); ctx.fill(); ctx.restore();
  if (g === 'fist' || g === 'point' || g === 'peace' || g === 'thumb') for (let i = 0; i < 3; i++) ln([[.5, -.14 + i * .1], [.6, -.14 + i * .1]], alpha(IP.skinLine, .55), L);
  if (g === 'mic') {
    ctx.save(); ctx.translate(.34, 0); ctx.rotate(-Math.PI / 2 * flip);
    solid(rrPts(-.1, -.12, .2, 1.1, .07), '#3A3A48', { shade: '#20202A', sh: .05, line: IP.ink, lw: L, size: .2, sharp: true });
    solid(ellPts(0, -.22, .2, .24, 20), IP.silver, { shade: '#8A8FA6', sh: .06, line: IP.ink, lw: L, size: .3 });
    ctx.fillStyle = M.col; ctx.fillRect(-.1, .12, .2, .09);
    ctx.restore();
  }
  ctx.restore();
  if (g === 'fheart') { const k = O.heartPop ?? 1; if (k > 0) { const r = .34 * size * backOut(clamp(k), 2.5), tx = w[0] + Math.cos(a) * .6 * size + sd * .75 * size, ty = w[1] + Math.sin(a) * .6 * size - .6 * size - r * .4; solid(heartPts(tx, ty, r, 30), '#FF4F9A', { shade: '#D02F73', sh: r * .15, line: IP.line, lw: lw, size: r * 2 }); ctx.save(); ctx.globalCompositeOperation = 'lighter'; glow(tx, ty, r * 2.5, '#FF4F9A', .35 * clamp(k)); ctx.restore(); } }
}
function headset(R) {
  const { O } = R, h = R.head, tn = clamp(O.turn ?? 0, -1, 1);
  ctx.save(); headXf(h);
  const sd = tn > .25 ? -1 : 1, x0 = turnX(sd * .47, tn, .5);
  const col = '#2B2438';
  ctx.fillStyle = col; ctx.beginPath(); ctx.ellipse(x0, .12, .04, .065, 0, 0, TAU); ctx.fill();
  const tip = [turnX(sd * .14, tn) , .42];
  const C = qbez([x0, .15], [x0 - sd * .02, .38], tip, 10);
  brush(C, .02, col, 'flat');
  ctx.beginPath(); ctx.ellipse(tip[0], tip[1], .028, .02, 0, 0, TAU); ctx.fill();
  ctx.restore();
}

// ---------------- back view ----------------
function idolBack(R) {
  const { M, P, O, pelvis, rotP } = R;
  const at = (x, dy) => rotP(x, pelvis[1] + dy), dNeck = P.neckY - P.hipY;
  R.chest = at(0, dNeck); R.shoulder = sd => at(sd * P.shW, dNeck + .14); R.at = at; R.stage = (O.outfit ?? 'stage') === 'stage';
  R.swing = O.swing ?? (Math.sin(bpOf(T) * Math.PI) * .14 - (O.sway ?? 0) * .3);
  const fL = O.fL ?? [-.4, 0], fR = O.fR ?? [.4, 0];
  for (const [sd, f] of [[-1, fL], [1, fR]]) {
    const hj = at(sd * P.hipJ, .1), { j, e } = ikOut(hj, [f[0], f[1] + P.footY - (O.jump ?? 0)], P.thigh, P.shin, -sd);
    idolLeg(R, sd, hj, j, e);
  }
  idolTorso(R);
  for (const [sd, hh, g] of [[-1, O.hL ?? [-.9, 2.72], O.gL ?? 'fist'], [1, O.hR ?? [.9, 2.72], O.gR ?? 'fist']]) {
    const sh = R.shoulder(sd), { j, e } = ikOut(sh, [R.chest[0] + hh[0], R.chest[1] + hh[1]], P.upper, P.fore, -sd, O[sd < 0 ? 'eL' : 'eR'] ?? 0);
    idolArm(R, sd, sh, j, e, g);
  }
  const h = R.head, L = R.lw / h.h * 1.05;
  ctx.save(); headXf(h);
  solid(ellPts(0, -.02, .52, .55, 44), M.hairCol, { shade: M.hairSh, sh: .08, line: M.hairLine, lw: L, size: 1 });
  ctx.save(); ctx.beginPath(); ctx.ellipse(0, -.02, .52, .55, 0, 0, TAU); ctx.clip();
  for (let i = -3; i <= 3; i++) brush(qbez([i * .05, -.52], [i * .12, -.1], [i * .15, .5], 8), L * .9, alpha(M.hairLine, .45));
  hairShine(M, 0, L);
  ctx.restore();
  if (M.hair === 'twintails') for (const sd of [-1, 1]) { twinTail(R, sd, 0, R.swing, L); bow(sd * .47, -.24, .15, M.col, L, -sd * .3); }
  if (M.hair === 'ponytail') ponyTail(R, 0, R.swing, L);
  if (M.hair === 'long') solid([[-.5, 0], [.5, 0], [.64, 2], [-.64, 2]], M.hairCol, { shade: M.hairSh, sh: .08, line: M.hairLine, lw: L, size: 1 });
  ctx.restore();
}

// =====================================================================================================
// POSES & DANCE MOVES
// =====================================================================================================
// Hand targets (hL/hR) are relative to the neck base in s units (+y down); foot targets (fL/fR) relative to the ground point.
const IDOL_POSES = {
  idle: { hL: [-.95, 2.75], hR: [.95, 2.75], gL: 'open', gR: 'open' },
  hips: { hL: [-.72, 1.55], hR: [.72, 1.55], gL: 'fist', gR: 'fist' },
  wave: { hL: [-.9, 2.72], hR: [1.55, -1.25], gR: 'wave', gL: 'open', wristR: .3 },
  point: { hL: [-.7, 1.6], gL: 'fist', hR: [1.6, -1.9], gR: 'point' },
  pointFwd: { hL: [-.95, 2.7], hR: [.55, .2], gR: 'point', wristR: -.6 },
  heart: { hL: [-.1, -2.05], hR: [.1, -2.05], gL: 'heart', gR: 'heart' },       // big heart over the head
  heartChest: { hL: [-.12, .35], hR: [.12, .35], gL: 'heart', gR: 'heart' },
  fingerHeart: { hL: [-.9, 2.7], hR: [.62, -.4], gR: 'fheart', wristR: -1.1 },
  peace: { hL: [-.8, 1.6], gL: 'fist', hR: [.55, -.6], gR: 'peace', wristR: -1.9 },
  mic: { hL: [-.9, 2.6], hR: [.08, -.28], gR: 'mic', wristR: .3 },
  cheer: { hL: [-1, -1.9], hR: [1, -1.9], gL: 'fist', gR: 'fist' },
  shock: { hL: [-.55, -.2], hR: [.55, -.2], gL: 'open', gR: 'open', wristL: -.6, wristR: -.6 },
  cheeks: { hL: [-.38, -.62], hR: [.38, -.62], gL: 'flat', gR: 'flat' },
  think: { hL: [-.1, 1.3], gL: 'flat', hR: [.1, -.5], gR: 'point', wristR: -1.9 },
  shrug: { hL: [-1.2, .5], hR: [1.2, .5], gL: 'open', gR: 'open', wristL: -1.2, wristR: -1.2 },
  xarms: { hL: [.55, .45], hR: [-.55, .45], gL: 'fist', gR: 'fist' },           // "NO!" crossed arms
  salute: { hL: [-.95, 2.7], hR: [.25, -.95], gR: 'flat', wristR: -.2 },
  clap: { hL: [-.07, .75], hR: [.07, .75], gL: 'flat', gR: 'flat' },
  facepalm: { hL: [-.95, 2.7], hR: [.05, -.72], gR: 'flat', wristR: -1.4 },
  kneeIn: { fL: [-.55, 0], fR: [.3, -.05], kneeIn: true },
};
function idolPose(name, o = {}) { return { ...(IDOL_POSES[name] || {}), ...o }; }
// Blend two pose objects (numeric arrays lerped; other keys switch at k = .5).
function mixPose(a, b, k) {
  const out = { ...a };
  for (const key of Object.keys(b)) {
    const va = a[key], vb = b[key];
    if (Array.isArray(vb) && Array.isArray(va)) out[key] = va.map((v, i) => lerp(v, vb[i], k));
    else if (typeof vb === 'number' && typeof va === 'number') out[key] = lerp(va, vb, k);
    else out[key] = k < .5 && va !== undefined ? va : vb;
  }
  return out;
}
// Dance moves: idolMove(name, b, o) → pose for beat position b (use bpOf(t), maybe + a per-member offset). Every move bounces on the beat.
//   bounce, step, point, wave, clap, heart, roll, hips, jump, wag, sway, hook (the chorus hook: point up on "scaling"), idle
function idolMove(name, b, o = {}) {
  const ph = frac(b), bn = Math.floor(b), alt = bn % 2 ? 1 : -1;
  const hit = Math.exp(-ph * 7), bounce = Math.sin(ph * Math.PI);         // hit decays after the beat; bounce is an arch
  const dip = .18 * (1 - bounce) * (1 - ph * .5);
  let p;
  switch (name) {
    case 'step': {
      const s = Math.sin(b * Math.PI);
      p = { sway: s * .25, bob: .15 + .12 * hit, fL: [-.5 + s * .15, s > 0 ? 0 : -.35 * Math.abs(s)], fR: [.5 + s * .15, s < 0 ? 0 : -.35 * Math.abs(s)],
        hL: [-1.1 - s * .3, 1.4 - s * .6], hR: [1.1 - s * .3, 1.4 + s * .6], gL: 'fist', gR: 'fist', lean: -s * .06, tilt: s * .1 };
      break;
    }
    case 'point': {
      const up = alt > 0;
      p = { bob: .1 + .2 * hit, sway: alt * .12, lean: alt * .05, tilt: alt * .12,
        hR: up ? [1.35, -2.1 + hit * .2] : [.8, 1.2], gR: up ? 'point' : 'fist', hL: up ? [-.8, 1.2] : [-1.35, -2.1 + hit * .2], gL: up ? 'fist' : 'point', eL: up ? -1 : 1, eR: up ? 1 : -1, fL: [-.5, 0], fR: [.5, up ? -.12 : 0] };
      break;
    }
    case 'wave': {
      const s = Math.sin(b * Math.PI * .5);
      p = { bob: .12 + .1 * hit, sway: s * .2, lean: s * .08, tilt: s * .1, hL: [-.85 + s * .6, -2.2], hR: [.85 + s * .6, -2.2], gL: 'wave', gR: 'wave' };
      break;
    }
    case 'clap': {
      const c = ph < .5 ? 1 - ph * 2 : 0;
      p = { bob: .15 * hit, hL: [-.07 - (1 - c) * .55, .75 - c * .15], hR: [.07 + (1 - c) * .55, .75 - c * .15], gL: 'flat', gR: 'flat', tilt: alt * .08 };
      break;
    }
    case 'heart': p = { ...IDOL_POSES.heart, bob: .1 * hit, sway: Math.sin(b * Math.PI * .5) * .1, tilt: Math.sin(b * Math.PI * .5) * .12 }; break;
    case 'roll': { const a = b * Math.PI; p = { bob: .1 + .12 * hit, hL: [-.35 + Math.cos(a) * .3, .5 + Math.sin(a) * .3], hR: [.35 + Math.cos(a + 1) * .3, .5 + Math.sin(a + 1) * .3], gL: 'fist', gR: 'fist', sway: Math.sin(a) * .15, lean: Math.sin(a) * .05 }; break; }
    case 'hips': { const s = Math.sin(b * Math.PI); p = { ...IDOL_POSES.hips, sway: s * .3, lean: -s * .07, tilt: s * .12, bob: .08 * hit, fL: [-.5, 0], fR: [.5, 0] }; break; }
    case 'jump': { const air = Math.max(0, Math.sin(ph * Math.PI)) * (bn % 2 ? 1 : .3); p = { jump: air * 1.2, bob: air > .05 ? 0 : .3 * hit, hL: [-1.1, -2.2], hR: [1.1, -2.2], gL: 'open', gR: 'open', fL: [-.5, -air * .5], fR: [.5, -air * .5] }; break; }
    case 'wag': { const w = Math.sin(b * Math.PI * 2) * .35; p = { hL: [-.72, 1.55], gL: 'fist', hR: [.45 + w * .3, -.9], gR: 'point', wristR: -1.6 + w, tilt: -w * .3, turn: w * .3, bob: .1 * hit }; break; }
    case 'sway': { const s = Math.sin(b * Math.PI * .5); p = { sway: s * .25, lean: s * .06, tilt: s * .14, hL: [-.95 + s * .2, 2.4], hR: [.95 + s * .2, 2.4], bob: .06 * hit }; break; }
    case 'hook': {
      // "We didn't start the scaling": point at self, finger-wag, then sweep the arm up the curve
      const k = frac(b / 4) * 4;
      if (k < 1) p = { hR: [.2, .4], gR: 'point', wristR: 2.6, hL: [-.8, 1.4], gL: 'fist', bob: .2 * hit };
      else if (k < 2) p = idolMove('wag', b);
      else p = { hR: [lerp(.9, 1.5, clamp(k - 2)), lerp(1.4, -2.3, easeOut(clamp((k - 2) / 1.5)))], gR: 'point', hL: [-1.2, .6], gL: 'open', bob: .15 * hit, jump: k > 3 ? .3 * Math.sin((k - 3) * Math.PI) : 0, lean: .06 };
      break;
    }
    default: // bounce
      p = { bob: .1 + .22 * hit, sway: alt * .06 * bounce, tilt: alt * .08, hL: [-1.05, 2.2 - hit * .3], hR: [1.05, 2.2 - hit * .3], gL: 'fist', gR: 'fist' };
  }
  return { ...p, ...o };
}
// Singing mouth for time t: cycles visemes on eighth notes while a line is being sung; 'smile' otherwise.
function singVis(t, seed = 0) {
  const ln = lineAt(t);
  if (!ln || t > ln.end) return 'smile';
  const e = Math.floor(bpOf(t) * 2), k = frac(bpOf(t) * 2);
  if (k > .8) return hash2(e, seed) < .5 ? 'e' : 'closed';
  return ['a', 'o', 'e', 'a', 'i', 'u', 'a', 'o'][Math.floor(hash2(e, seed + 3) * 8)];
}


// The whole group in formation. members: list of keys (default all four, TOKI centre); each gets its own beat offset so the
// choreography ripples. fn(i, key) may return per-member overrides. Returns the x positions used.
function group(t, cx, gy, s, move, o = {}) {
  const keys = o.members ?? ['ADA', 'TOKI', 'RELU', 'LOGI'];
  const gap = o.gap ?? s * 3.6, n = keys.length, xs = [];
  const order = keys.map((k, i) => ({ k, i, x: cx + (i - (n - 1) / 2) * gap, y: gy - (k === (o.center ?? 'TOKI') ? 0 : (o.back ?? s * .25)) }));
  order.sort((a, b) => a.y - b.y);                     // back row first
  for (const m of order) {
    const b = bpOf(t) - (o.ripple ?? 0) * m.i;
    const ov = o.each ? o.each(m.i, m.k) || {} : {};
    const sc = m.k === (o.center ?? 'TOKI') ? s * (o.centerK ?? 1.06) : s;
    idol(m.x, m.y, sc, { member: m.k, ...idolMove(move, b), mouth: singVis(t, m.i * 7), blink: t + m.i * .7, ...(o.common || {}), ...ov });
    xs.push(m.x);
  }
  return xs;
}

// =====================================================================================================
// CHIBI PEOPLE (the lyrics' real people — never likenesses; one costume cue + a name tag each)
// =====================================================================================================
// chibi(x, y, s, o): super-deformed person, (x, y) ground, ≈ 10s tall, head ≈ 45% of it.
//   name (chest name tag), tagCol, float (name caption above the head instead), skin (hex or 0..5), hair (short|side|swoop|spiky|
//   curly|bald|buzz|long|bob|bun|ponytail|mohawk|messy|hood), hairCol, top (tee|suit|hoodie|leather|sweater|labcoat|dress|vest|coat),
//   topCol, tie, pants, glasses (true|'round'|'shades'), beard (true|'stubble'), hat (fedora|visor|cap|beanie|crown|party|hardhat|grad),
//   mittens (colour), eyes (dot|happy|closed|wide|angry|worried|x|spark|heart|cry|swirl|squeeze|dead|smug|shades), mouth (smile|grin|open|
//   O|flat|frown|wavy|scream|smirk|cat), brows, blush, sweat, tears, aL/aR (arm angles: 0 out, + raised, −1.2 hanging), hold/holdL
//   (fn(s) drawn at the hand), dy, jump, rot, flip, sq, walk, back, lookX, rim.
const CHIBI_SKIN = ['#FFE3D3', '#F6CDB0', '#E4AE88', '#C98D66', '#9C6644', '#FFE9DE'];
function chibi(x, y, s, o = {}) {
  const skin = typeof o.skin === 'number' ? CHIBI_SKIN[o.skin] : o.skin ?? CHIBI_SKIN[0];
  const skinSh = mixCol(skin, '#C0607A', .3), sl = mixCol(skin, '#5A2030', .55);
  const hairCol = o.hairCol ?? '#3B2A2E', topCol = o.topCol ?? '#6A8BE8', pants = o.pants ?? '#3A3558';
  const lw = .09 * Math.pow(s / 40, -.2);
  const oldLight = LIGHT; if (o.rim) LIGHT = { ...LIGHT, rim: o.rim };
  ctx.save(); ctx.translate(x, y); ctx.scale(s, s);
  if (o.shadow !== false) { ctx.fillStyle = 'rgb(20 8 40 / .25)'; ctx.beginPath(); ctx.ellipse(0, 0, 2.2 * (1 - clamp((o.jump ?? 0) / 6) * .4), .38, 0, 0, TAU); ctx.fill(); }
  ctx.translate(0, (o.dy ?? 0) - (o.jump ?? 0)); if (o.rot) ctx.rotate(o.rot); if (o.flip) ctx.scale(-1, 1);
  const sq = o.sq ?? 0; ctx.scale(1 + sq * .4, 1 - sq);
  const line = IP.line;
  // legs + feet
  for (const sd of [-1, 1]) {
    const lift = o.walk !== undefined ? Math.max(0, Math.sin(o.walk * TAU + (sd > 0 ? Math.PI : 0))) * .6 : 0;
    limbChain([[sd * .5, -1.8], [sd * .52, -.35 - lift]], [.4, .36], o.top === 'dress' ? skin : pants, mixCol(o.top === 'dress' ? skin : pants, IP.plum, .3), line, lw);
    solid(ellPts(sd * .62, -.2 - lift, .62, .34, 18), o.shoes ?? '#2B2438', { shade: false, line, lw });
  }
  // arms (behind body when hanging)
  const armAt = (sd, a) => { const A = sd > 0 ? -a : Math.PI + a; return [[sd * 1.05, -4.25], [sd * 1.05 + Math.cos(A) * 2.1, -4.25 + Math.sin(A) * 2.1]]; };
  const drawArm = (sd, a, hold) => {
    const [sh, hd] = armAt(sd, a), sleeve = o.top === 'tee' || o.top === 'dress' ? skin : topCol;
    limbChain([sh, hd], [.42, .36], sleeve, mixCol(sleeve, IP.plum, .3), line, lw);
    if (o.mittens) solid(ellPts(hd[0], hd[1], .52, .5, 18), o.mittens, { shade: mixCol(o.mittens, IP.plum, .3), sh: .12, line, lw });
    else solid(ellPts(hd[0], hd[1], .44, .44, 16), skin, { shade: skinSh, sh: .1, line: sl, lw });
    if (hold) { ctx.save(); ctx.translate(hd[0], hd[1]); hold(1); ctx.restore(); }
  };
  // body
  const top = o.top ?? 'tee';
  const bodyP = top === 'dress' ? [[-1.05, -4.85], [1.05, -4.85], [1.6, -1.35], [-1.6, -1.35]] : top === 'coat' || top === 'labcoat' ? [[-1.1, -4.85], [1.1, -4.85], [1.35, -1.1], [-1.35, -1.1]] : [[-1.08, -4.85], [1.08, -4.85], [1.2, -1.6], [-1.2, -1.6]];
  const armsBehind = (o.aL ?? -1.2) < -.6 && (o.aR ?? -1.2) < -.6;
  if (o.back) { drawArm(-1, o.aL ?? -1.2, o.holdL); drawArm(1, o.aR ?? -1.2, o.hold); }
  const bodyMk = () => { ctx.beginPath(); ctx.roundRect(bodyP[3][0], bodyP[0][1], bodyP[2][0] - bodyP[3][0], bodyP[2][1] - bodyP[0][1], [.9, .9, .5, .5]); };
  const topFill = top === 'labcoat' ? '#FAFAFF' : top === 'leather' ? '#26222E' : topCol;
  solid(top === 'dress' ? bodyP : bodyMk, topFill, { shade: mixCol(topFill, IP.plum, .3), sh: .35, line, lw, size: 3 });
  if (!o.back) {
    if (top === 'suit' || top === 'labcoat' || top === 'coat' || top === 'leather') {
      solid([[-.55, -4.85], [.55, -4.85], [0, -3.3, 1]], top === 'leather' ? '#E8E4EE' : IP.white, { shade: false, line, lw: lw * .8, sharp: true });
      if (o.tie) solid([[-.14, -4.7], [.14, -4.7], [.22, -3.6], [0, -3.3, 1], [-.22, -3.6]], o.tie, { shade: false, line, lw: lw * .7 });
      for (const sd of [-1, 1]) ln([[sd * .55, -4.85], [sd * .12, -3.4], [sd * .1, -1.7]], alpha(top === 'leather' ? '#8A8498' : IP.line, .8), lw * .9);
      if (top === 'leather') ln([[-.95, -4.3], [-.7, -2.4]], alpha(IP.white, .5), lw * 1.5);
    } else if (top === 'hoodie') {
      solid([[-.95, -4.9], [.95, -4.9], [.6, -4.2], [-.6, -4.2]], mixCol(topCol, IP.plum, .2), { shade: false, line, lw: lw * .8 });
      ln([[-.3, -4.3], [-.33, -3.3]], IP.white, lw); ln([[.3, -4.3], [.33, -3.3]], IP.white, lw);
      solid(rrPts(-.75, -2.9, 1.5, .8, .3), mixCol(topCol, IP.plum, .15), { shade: false, line: alpha(line, .6), lw: lw * .7 });
    } else if (top === 'sweater' || top === 'vest') {
      solid([[-.6, -4.85], [.6, -4.85], [0, -4.1, 1]], top === 'vest' ? IP.white : mixCol(topCol, IP.plum, .2), { shade: false, line, lw: lw * .8, sharp: true });
      for (let i = 0; i < 5; i++) ln([[-1.1 + i * .55, -1.8], [-1.1 + i * .55, -1.6]], alpha(line, .5), lw * .6);
    } else if (top === 'tee') solid(ellPts(0, -4.85, .55, .25, 16), skin, { shade: false, line, lw: lw * .8 });
    if (top === 'labcoat') { ln([[0, -4.3], [0, -1.2]], alpha(line, .6), lw * .8); solid(rrPts(.35, -3.6, .6, .5, .08), '#E0F0FF', { shade: false, line, lw: lw * .6 }); }
  }
  if (!o.back) { drawArm(-1, o.aL ?? -1.2, o.holdL); drawArm(1, o.aR ?? -1.2, o.hold); }
  // name tag (chest)
  if (o.name && !o.float && !o.back) nameBadge(o.name, .15, -3.15, .95, o.tagCol ?? IP.neonPink);
  // head
  ctx.save(); ctx.translate(0, -6.95);
  const hx = (o.lookX ?? 0) * .25;
  if (!o.back) chibiHairBack(o.hair ?? 'short', hairCol, lw);
  const headMk = () => crPath([[-2.3, -.3], [-2.15, -1.3], [-1.3, -2.05], [0, -2.25], [1.3, -2.05], [2.15, -1.3], [2.3, -.3], [2.1, .9], [1.3, 1.75], [0, 2.02], [-1.3, 1.75], [-2.1, .9]]);
  solid(headMk, skin, { shade: skinSh, sh: .3, line: sl, lw, size: 4 });
  if (o.back) { chibiHairBack(o.hair ?? 'short', hairCol, lw, true); ctx.restore(); ctx.restore(); LIGHT = oldLight; return; }
  // face
  chibiEyes(o.eyes ?? 'dot', hx, lw, o);
  const blush = o.blush ?? .5;
  if (blush > 0) for (const sd of [-1, 1]) { const g = ctx.createRadialGradient(sd * 1.45 + hx, .95, 0, sd * 1.45 + hx, .95, .6); g.addColorStop(0, alpha('#FF7FA0', .5 * blush)); g.addColorStop(1, alpha('#FF7FA0', 0)); ctx.fillStyle = g; ctx.fillRect(sd * 1.45 + hx - .6, .35, 1.2, 1.2); }
  if (o.beard) { if (o.beard === 'stubble') { ctx.fillStyle = alpha(hairCol, .35); ctx.beginPath(); ctx.ellipse(hx, 1.35, 1.25, .6, 0, 0, Math.PI); ctx.fill(); } else solid([[-1.75 + hx, .55], [-1.3 + hx, 1.6], [0 + hx, 2.1], [1.3 + hx, 1.6], [1.75 + hx, .55], [1.1 + hx, 1.25], [.5 + hx, 1.75], [-.5 + hx, 1.75], [-1.1 + hx, 1.25]], o.beardCol ?? mixCol(hairCol, '#8A7A70', .35), { shade: false, line: sl, lw: lw * .8 }); }
  chibiMouth(o.mouth ?? 'smile', hx, 1.3, lw, sl);
  chibiHairFront(o.hair ?? 'short', hairCol, lw, hx);
  if (o.glasses) chibiGlasses(o.glasses, hx, lw);
  const brows = o.brows ?? (o.eyes === 'angry' ? 'angry' : o.eyes === 'worried' || o.eyes === 'cry' ? 'worried' : null);
  if (brows) for (const sd of [-1, 1]) { const inner = brows === 'angry' ? .25 : brows === 'worried' ? -.25 : -.1; brush([[sd * 1.35 + hx, -.95], [sd * .45 + hx, -.95 + inner]], lw * 1.6, hairCol === '#FFFFFF' ? IP.line : mixCol(hairCol, IP.line, .4), 'flat'); }
  if (o.hat) chibiHat(o.hat, o.hatCol, lw);
  if (o.sweat) sweatDrop(2.1, -1.2, .5 * o.sweat, lw);
  if (o.tears) for (const sd of [-1, 1]) { ctx.save(); ctx.globalAlpha = .9; brush([[sd * .9 + hx, .4], [sd * 1.0 + hx, 1.2 + .5 * frac(T * 2.3)], [sd * .92 + hx, 2.1]], .32, '#A8E0FF', 'mid', { min: .5 }); ctx.restore(); }
  ctx.restore();
  if (o.name && o.float) nameCap(o.name, 0, -10.1, .9, o.tagCol ?? IP.neonPink);
  ctx.restore();
  LIGHT = oldLight;
}
function chibiEyes(kind, hx, lw, o) {
  const dark = '#2A1433', ey = .05;
  for (const sd of [-1, 1]) {
    const cx = sd * .88 + hx, cy = ey;
    ctx.save(); ctx.translate(cx, cy);
    switch (kind) {
      case 'happy': brush(qbez([-.42, .12], [0, -.45], [.42, .12], 8), lw * 2.2, dark, 'mid', { min: .4 }); break;
      case 'closed': case 'sleepy': brush(qbez([-.42, 0], [0, .3], [.42, 0], 8), lw * 2, dark, 'mid', { min: .4 }); break;
      case 'squeeze': brush([[-sd * .42, -.3], [sd * .3, 0], [-sd * .42, .3]], lw * 2.2, dark, 'flat'); break;
      case 'x': brush([[-.3, -.3], [.3, .3]], lw * 2, dark, 'flat'); brush([[.3, -.3], [-.3, .3]], lw * 2, dark, 'flat'); break;
      case 'dead': ctx.fillStyle = IP.white; ctx.beginPath(); ctx.ellipse(0, 0, .42, .5, 0, 0, TAU); ctx.fill(); ctx.strokeStyle = dark; ctx.lineWidth = lw * 1.2; ctx.stroke(); break;
      case 'wide': ctx.fillStyle = IP.white; ctx.beginPath(); ctx.ellipse(0, 0, .46, .56, 0, 0, TAU); ctx.fill(); ctx.strokeStyle = dark; ctx.lineWidth = lw * 1.2; ctx.stroke(); ctx.fillStyle = dark; ctx.beginPath(); ctx.arc((o.lookX ?? 0) * .15, 0, .14, 0, TAU); ctx.fill(); break;
      case 'swirl': ctx.strokeStyle = dark; ctx.lineWidth = lw * .9; ctx.beginPath(); for (let i = 0; i <= 30; i++) { const a = i * .5 + T * 9, r = .02 + i * .014; i ? ctx.lineTo(Math.cos(a) * r, Math.sin(a) * r) : ctx.moveTo(0, 0); } ctx.stroke(); break;
      case 'spark': sparkle(0, 0, .55, 0, IP.neonGold, { glow: false }); break;
      case 'heart': solid(heartPts(0, 0, .5, 24), '#FF3D8B', { shade: false, line: dark, lw: lw * .7 }); break;
      case 'shades': break;
      default: {
        // 'dot', 'angry', 'worried', 'cry', 'smug': glossy oval eyes
        const ry = kind === 'smug' ? .3 : .52, lid = kind === 'angry' ? .18 : 0;
        ctx.fillStyle = dark; ctx.beginPath(); ctx.ellipse(0, kind === 'smug' ? .15 : 0, .36, ry, 0, 0, TAU); ctx.fill();
        if (lid) { ctx.fillStyle = IP.white; }
        ctx.fillStyle = IP.white; ctx.beginPath(); ctx.ellipse(-.1 + (o.lookX ?? 0) * .08, -.18, .13, .16, 0, 0, TAU); ctx.fill();
        ctx.beginPath(); ctx.arc(.12, .2, .06, 0, TAU); ctx.fill();
        if (kind === 'smug') brush([[-.45, -.1], [.45, -.1]], lw * 1.6, dark, 'flat');
        if (kind === 'cry') { ctx.fillStyle = alpha('#BDE8FF', .7); ctx.fillRect(-.45, .2, .9, .35); }
      }
    }
    ctx.restore();
  }
  if (kind === 'shades') { solid(rrPts(-1.55 + hx, -.35, 1.3, .75, .25), '#1E1A26', { shade: false, line: IP.line, lw }); solid(rrPts(.25 + hx, -.35, 1.3, .75, .25), '#1E1A26', { shade: false, line: IP.line, lw }); ln([[-.25 + hx, -.1], [.25 + hx, -.1]], '#1E1A26', lw * 1.5); ctx.fillStyle = 'rgb(255 255 255 / .45)'; ctx.fillRect(-1.3 + hx, -.2, .35, .12); ctx.fillRect(.5 + hx, -.2, .35, .12); }
}
function chibiMouth(kind, hx, y, lw, sl) {
  const line = '#7A2440', inside = '#9A2E4E';
  ctx.save(); ctx.translate(hx, y);
  switch (kind) {
    case 'grin': case 'open': { ctx.beginPath(); ctx.moveTo(-.4, -.08); ctx.quadraticCurveTo(0, -.12, .4, -.08); ctx.quadraticCurveTo(0, .6, -.4, -.08); ctx.fillStyle = inside; ctx.fill(); ctx.strokeStyle = line; ctx.lineWidth = lw; ctx.stroke(); if (kind === 'grin') { ctx.fillStyle = IP.white; ctx.fillRect(-.3, -.08, .6, .12); } break; }
    case 'O': case 'scream': { const r = kind === 'scream' ? .45 : .28; ctx.beginPath(); ctx.ellipse(0, .1, r * .85, r, 0, 0, TAU); ctx.fillStyle = inside; ctx.fill(); ctx.strokeStyle = line; ctx.lineWidth = lw; ctx.stroke(); break; }
    case 'flat': brush([[-.25, 0], [.25, 0]], lw * 1.2, line, 'flat'); break;
    case 'frown': brush(qbez([-.3, .1], [0, -.15], [.3, .1], 6), lw * 1.2, line, 'mid', { min: .4 }); break;
    case 'wavy': brush([[-.4, 0], [-.2, -.1], [0, .05], [.2, -.1], [.4, 0]], lw * 1.1, line, 'flat'); break;
    case 'smirk': brush(qbez([-.3, .05], [.05, .15], [.35, -.15], 6), lw * 1.3, line, 'end', { min: .4 }); break;
    case 'cat': brush([[-.35, -.05], [-.17, .1], [0, 0], [.17, .1], [.35, -.05]], lw * 1.2, line, 'mid', { min: .5 }); break;
    default: brush(qbez([-.3, -.05], [0, .22], [.3, -.05], 6), lw * 1.3, line, 'mid', { min: .4 });
  }
  ctx.restore();
}
function chibiHairBack(h, col, lw, back = false) {
  const sh = mixCol(col, IP.plum, .35);
  if (back) { solid(ellPts(0, -.35, 2.45, 2.2, 36), col, { shade: sh, sh: .3, line: IP.line, lw, size: 4 }); return; }
  if (h === 'long') solid([[-2.4, -.6], [-2.6, 2.6], [-1.6, 3.4], [1.6, 3.4], [2.6, 2.6], [2.4, -.6], [0, -2.3]], sh, { shade: false, line: IP.line, lw });
  if (h === 'bob') solid([[-2.45, -.6], [-2.55, 1.9], [-1.9, 2.1], [1.9, 2.1], [2.55, 1.9], [2.45, -.6], [0, -2.3]], sh, { shade: false, line: IP.line, lw });
  if (h === 'bun') solid(ellPts(0, -2.5, .95, .8, 20), col, { shade: sh, sh: .2, line: IP.line, lw });
  if (h === 'ponytail') solid([[1.6, -1.4], [3.0, -.6], [3.2, 1.2], [2.5, 2.6, 1], [2.4, .8], [1.9, -.2]], col, { shade: sh, sh: .2, line: IP.line, lw });
  if (h === 'hood') solid(ellPts(0, -.1, 2.85, 2.7, 36), col, { shade: sh, sh: .35, line: IP.line, lw, size: 5 });
}
function chibiHairFront(h, col, lw, hx) {
  const sh = mixCol(col, IP.plum, .35), o = { shade: sh, sh: .25, line: IP.line, lw, size: 3 };
  const cap = (fringeY, pts) => solid(pts, col, o);
  switch (h) {
    case 'bald': ln([[-.6, -1.7], [-.2, -1.9]], alpha(IP.line, .35), lw); ln([[.3, -1.9], [.7, -1.7]], alpha(IP.line, .35), lw); solid([[-2.33, -.2], [-2.2, -.9], [-1.9, -.9], [-2.0, .1]], col, o); solid([[2.33, -.2], [2.2, -.9], [1.9, -.9], [2.0, .1]], col, o); break;
    case 'buzz': cap(0, [[-2.35, -.5], [-2.1, -1.5], [-1, -2.25], [1, -2.25], [2.1, -1.5], [2.35, -.5], [1.4, -1.15], [0, -1.3], [-1.4, -1.15]]); break;
    case 'spiky': cap(0, [[-2.4, -.2], [-2.6, -1.6], [-1.8, -1.6], [-1.9, -2.6], [-.9, -2.1], [-.4, -3.1], [.3, -2.2], [1.1, -2.9], [1.4, -2], [2.5, -2.2], [2.1, -1.2], [2.6, -.4], [1.5, -1.1], [.4, -.8], [-.6, -1.1], [-1.6, -.8]].map(p => [p[0], p[1], 1])); break;
    case 'curly': for (let i = 0; i < 9; i++) { const a = Math.PI * 1.02 + i / 8 * Math.PI * .96; solid(ellPts(Math.cos(a) * 2.05, Math.sin(a) * 1.95 - .35, .75, .7, 16), col, { ...o, size: 1.4 }); } break;
    case 'swoop': cap(0, [[-2.4, -.1], [-2.3, -1.4], [-1.2, -2.35], [.6, -2.4], [2.2, -1.7], [2.5, -.4], [2.2, 0], [1.6, -.9], [.3, -1.0], [-1.2, -.6], [-2.0, .3]]); break;
    case 'side': cap(0, [[-2.4, .1], [-2.35, -1.3], [-1.3, -2.3], [.2, -2.4], [1.6, -2.1], [2.4, -1.1], [2.4, .1], [2.0, -.6], [1.1, -1.05], [-.4, -1.15], [-.2, -.9], [-1.3, -.7], [-2.0, -.1]]); ln([[-.4, -1.15], [-.2, -2.3]], alpha(IP.line, .6), lw); break;
    case 'mohawk': cap(0, [[-.5, -1.9], [-.35, -3.3], [.35, -3.3], [.5, -1.9]]); break;
    case 'messy': cap(0, [[-2.45, .2], [-2.6, -1.3], [-1.5, -2.4], [0, -2.5], [1.5, -2.4], [2.6, -1.3], [2.45, .2], [2.0, -.5, 1], [1.5, -.2, 1], [1.1, -.9, 1], [.4, -.4, 1], [-.1, -1.0, 1], [-.8, -.35, 1], [-1.2, -.95, 1], [-1.8, -.3, 1], [-2.1, -.8, 1]]); break;
    case 'hood': break;
    case 'long': case 'bob': case 'bun': case 'ponytail':
      cap(0, [[-2.45, .6], [-2.45, -1.2], [-1.3, -2.35], [0, -2.45], [1.3, -2.35], [2.45, -1.2], [2.45, .6], [2.05, -.5, 1], [1.5, -.7, 1], [1.1, -.5, 1], [.5, -.95, 1], [0, -.6, 1], [-.5, -.95, 1], [-1.1, -.55, 1], [-1.6, -.75, 1], [-2.05, -.4, 1]]); break;
    default: // short
      cap(0, [[-2.4, -.1], [-2.35, -1.3], [-1.3, -2.3], [0, -2.42], [1.3, -2.3], [2.35, -1.3], [2.4, -.1], [2.0, -.75, 1], [1.4, -.95, 1], [.9, -.75, 1], [.3, -1.05, 1], [-.3, -.8, 1], [-.9, -1.05, 1], [-1.5, -.8, 1], [-2.0, -.95, 1]]);
  }
  if (h !== 'bald' && h !== 'hood' && h !== 'mohawk') { ctx.save(); ctx.globalAlpha = .7; brush(qbez([-1.3, -1.65], [0, -2.05], [1.3, -1.65], 8), .28, mixCol(col, IP.white, .45), 'mid'); ctx.restore(); }
}
function chibiGlasses(kind, hx, lw) {
  if (kind === 'shades') { chibiEyes('shades', hx, lw, {}); return; }
  ctx.save(); ctx.strokeStyle = '#2B2438'; ctx.lineWidth = lw * 1.1;
  for (const sd of [-1, 1]) { ctx.beginPath(); if (kind === 'round') ctx.ellipse(sd * .88 + hx, .05, .62, .62, 0, 0, TAU); else ctx.roundRect(sd * .88 + hx - .66, -.5, 1.32, 1.05, .25); ctx.stroke(); ctx.fillStyle = 'rgb(255 255 255 / .18)'; ctx.fill(); }
  ctx.beginPath(); ctx.moveTo(-.26 + hx, -.05); ctx.lineTo(.26 + hx, -.05); ctx.stroke(); ctx.restore();
}
function chibiHat(kind, col, lw) {
  const o = c => ({ shade: mixCol(c, IP.plum, .3), sh: .25, line: IP.line, lw, size: 3 });
  switch (kind) {
    case 'fedora': { const c = col ?? '#3A3440'; solid(ellPts(0, -1.75, 3.1, .55, 30), c, o(c)); solid([[-1.7, -1.8], [-1.5, -3.2], [-.4, -3.4], [0, -3.1], [.4, -3.4], [1.5, -3.2], [1.7, -1.8]], c, o(c)); solid(rrPts(-1.68, -2.35, 3.36, .45, .1), IP.red, { shade: false, line: IP.line, lw: lw * .8 }); break; }
    case 'visor': { const c = col ?? '#2FA86A'; solid([[-2.3, -1.2], [2.3, -1.2], [2.4, -.8], [-2.4, -.8]], c, o(c)); solid([[-1.6, -1.0], [1.6, -1.0], [2.9, -.1], [-2.9, -.1]], alpha(c, .85), { shade: false, line: IP.line, lw }); break; }
    case 'cap': { const c = col ?? '#FF4B5C'; solid([[-2.3, -.9], [-2.1, -2.0], [0, -2.7], [2.1, -2.0], [2.3, -.9]], c, o(c)); solid([[1.4, -1.0], [3.6, -.8], [3.4, -.45], [1.2, -.6]], c, o(c)); break; }
    case 'beanie': { const c = col ?? '#6A8BE8'; solid([[-2.45, -.8], [-2.2, -2.1], [0, -2.9], [2.2, -2.1], [2.45, -.8]], c, o(c)); solid(ellPts(0, -3.05, .45, .4, 14), IP.white, o(IP.white)); break; }
    case 'crown': { const c = col ?? IP.gold; solid([[-1.5, -1.9], [-1.6, -3.3], [-.8, -2.6], [0, -3.6], [.8, -2.6], [1.6, -3.3], [1.5, -1.9]].map(p => [p[0], p[1], 1]), c, o(c)); break; }
    case 'party': { const c = col ?? IP.neonPink; solid([[-1.1, -2.0], [0, -4.4, 1], [1.1, -2.0]], c, o(c)); solid(ellPts(0, -4.5, .35, .35, 12), IP.neonGold, o(IP.neonGold)); break; }
    case 'hardhat': { const c = col ?? IP.neonGold; solid([...ellPts(0, -1.3, 2.3, 1.7, 30).filter(p => p[1] <= -1.3)], c, o(c)); solid(rrPts(-2.8, -1.45, 5.6, .4, .15), c, o(c)); break; }
    case 'grad': { const c = col ?? '#2B2438'; solid([[-3, -2.4], [0, -3.4], [3, -2.4], [0, -1.5]], c, o(c)); ln([[2.3, -2.5], [2.6, -1.1]], IP.gold, lw * 1.5); break; }
  }
}
// Chest name badge (pill) and floating variety-show name caption.
function nameBadge(name, x, y, k, col = IP.neonPink) {
  ctx.save(); ctx.translate(x, y);
  const w = Math.max(2.2 * k, textW(name, .62 * k, 'rammetto') + .7 * k), h = .95 * k;
  rrect(-w / 2, -h / 2, w, h, h / 2); ctx.fillStyle = IP.white; ctx.fill(); ctx.strokeStyle = col; ctx.lineWidth = .16 * k; ctx.stroke();
  dtext(name, 0, .03 * k, .6 * k, { fill: IP.ink, maxW: w - .4 * k });
  ctx.restore();
}
function nameCap(name, x, y, k, col = IP.neonPink) {
  ctx.save(); ctx.translate(x, y);
  const w = textW(name, 1.1 * k, 'rammetto') + 1.2 * k, h = 1.6 * k;
  ctx.fillStyle = col; rrect(-w / 2, -h / 2, w, h, .5 * k); ctx.fill();
  ctx.beginPath(); ctx.moveTo(-.4 * k, h / 2 - .05); ctx.lineTo(0, h / 2 + .6 * k); ctx.lineTo(.4 * k, h / 2 - .05); ctx.fill();
  ctx.strokeStyle = IP.white; ctx.lineWidth = .18 * k; rrect(-w / 2, -h / 2, w, h, .5 * k); ctx.stroke();
  dtext(name, 0, .05 * k, 1.05 * k, { fill: IP.white });
  ctx.restore();
}

// =====================================================================================================
// CLAWD, DEVOTED FAN (the project's mascot, redrawn clean for this world)
// =====================================================================================================
// fanClawd(x, y, u, o): (x, y) ground; ≈ 10u wide, 8u tall (same footprint as cast.js clawd()).
//   eyes (normal|happy|heart|star|cry|wide|closed|x), mouth (none|smile|open|O|wail), aL/aR (nub angles: 0 out, + up), stick ('L'|'R'|
//   false: lightstick in that nub), stickCol, towel (text: a slogan towel held in both nubs), band (headband text), phone (bool: filming
//   with the right nub), jump, dy, sq, rot, flip, walk, blush, tears, sweat, glow, label (name badge)
function fanClawd(x, y, u, o = {}) {
  const col = '#E07B57', dk = '#B45A3C', line = '#5A2A1C';
  const lw = .22 * Math.pow(u / 20, -.2);
  ctx.save(); ctx.translate(x, y); ctx.scale(u, u);
  if (o.shadow !== false) { ctx.fillStyle = 'rgb(20 8 40 / .25)'; ctx.beginPath(); ctx.ellipse(0, 0, 5.6, .9, 0, 0, TAU); ctx.fill(); }
  ctx.translate(0, (o.dy ?? 0) - (o.jump ?? 0)); if (o.rot) ctx.rotate(o.rot); if (o.flip) ctx.scale(-1, 1);
  const sq = o.sq ?? 0; ctx.scale(1 + sq * .5, 1 - sq);
  [-3.6, -1.4, 1.4, 3.6].forEach((lx, i) => {
    const lift = o.walk !== undefined ? Math.max(0, Math.sin(o.walk * TAU + (i % 2) * Math.PI)) * .9 : 0;
    solid(rrPts(lx - .55, -2.3 - lift, 1.1, 2.3, .3), dk, { shade: false, line, lw, sharp: true });
  });
  const nub = (sd, ang, holdFn) => {
    ctx.save(); ctx.translate(sd * 4.95, -4.9); ctx.rotate(sd * -ang);
    solid(rrPts(sd > 0 ? -.2 : -2.1, -.6, 2.3, 1.2, .5), col, { shade: dk, sh: .25, line, lw, sharp: true });
    if (holdFn) { ctx.translate(sd * 2.0, 0); ctx.rotate(sd * ang); holdFn(sd); }
    ctx.restore();
  };
  const stickFn = sd => lightstick(0, 0, 1.1, o.stickCol ?? MEMBERS.TOKI.col, { rot: -sd * .15 + Math.sin(bpOf(T) * Math.PI) * .25 });
  const phoneFn = sd => { ctx.save(); ctx.rotate(-.2); solid(rrPts(-.9, -3.4, 1.8, 3.1, .3), '#2B2438', { shade: false, line, lw }); ctx.fillStyle = (frac(T * 2) < .5) ? IP.red : '#FF9AA6'; ctx.beginPath(); ctx.arc(0, -3, .18, 0, TAU); ctx.fill(); ctx.restore(); };
  const back = [[-1, o.aL ?? -.2, o.stick === 'L' ? stickFn : null], [1, o.aR ?? -.2, o.stick === 'R' ? stickFn : o.phone ? phoneFn : null]];
  if (o.glow) { ctx.save(); ctx.globalCompositeOperation = 'lighter'; glow(0, -5, 9, o.glow, .4); ctx.restore(); }
  solid(rrPts(-5, -8, 10, 6, .5), col, { shade: dk, sh: 1.1, line, lw, sharp: true, rimW: .35 });
  ctx.fillStyle = alpha(IP.white, .35); ctx.beginPath(); ctx.roundRect(-4.4, -7.5, 3.2, .7, .35); ctx.fill();
  // face
  const ex = 2.3, ey = -6.1, eyes = o.eyes ?? 'normal', dark = '#2A1433';
  for (const sd of [-1, 1]) {
    ctx.save(); ctx.translate(sd * ex, ey);
    switch (eyes) {
      case 'happy': brush(qbez([-.75, .3], [0, -.65], [.75, .3], 8), .45, dark, 'mid', { min: .5 }); break;
      case 'closed': brush(qbez([-.75, 0], [0, .45], [.75, 0], 8), .4, dark, 'mid', { min: .5 }); break;
      case 'heart': solid(heartPts(0, 0, 1.0, 28), '#FF3D8B', { shade: false, line: dark, lw: lw * .7 }); ctx.fillStyle = IP.white; ctx.beginPath(); ctx.arc(-.35, -.3, .18, 0, TAU); ctx.fill(); break;
      case 'star': sparkle(0, 0, 1.1, 0, IP.neonGold, { glow: false }); break;
      case 'x': brush([[-.55, -.55], [.55, .55]], .4, dark, 'flat'); brush([[.55, -.55], [-.55, .55]], .4, dark, 'flat'); break;
      case 'wide': ctx.fillStyle = IP.white; ctx.beginPath(); ctx.ellipse(0, 0, .8, .95, 0, 0, TAU); ctx.fill(); ctx.strokeStyle = dark; ctx.lineWidth = .18; ctx.stroke(); ctx.fillStyle = dark; ctx.beginPath(); ctx.arc(0, 0, .3, 0, TAU); ctx.fill(); break;
      case 'cry': brush([[-sd * .7, -.45], [sd * .5, 0], [-sd * .7, .45]], .4, dark, 'flat'); break;
      default: ctx.fillStyle = dark; ctx.beginPath(); ctx.roundRect(-.45, -.85, .9, 1.7, .45); ctx.fill(); ctx.fillStyle = IP.white; ctx.beginPath(); ctx.arc(-.12, -.45, .17, 0, TAU); ctx.fill();
    }
    ctx.restore();
  }
  if (o.blush ?? true) for (const sd of [-1, 1]) { ctx.fillStyle = alpha('#FF6F91', .45); ctx.beginPath(); ctx.ellipse(sd * 3.6, -4.6, .85, .45, 0, 0, TAU); ctx.fill(); }
  const my = -4.5;
  switch (o.mouth ?? 'none') {
    case 'smile': brush(qbez([-.9, my - .1], [0, my + .8], [.9, my - .1], 8), .3, dark, 'mid', { min: .5 }); break;
    case 'open': ctx.fillStyle = '#9A2E4E'; ctx.beginPath(); ctx.moveTo(-.9, my - .2); ctx.quadraticCurveTo(0, my + 1.5, .9, my - .2); ctx.closePath(); ctx.fill(); break;
    case 'O': ctx.fillStyle = '#9A2E4E'; ctx.beginPath(); ctx.ellipse(0, my + .2, .55, .75, 0, 0, TAU); ctx.fill(); break;
    case 'wail': ctx.fillStyle = '#9A2E4E'; ctx.beginPath(); ctx.moveTo(-1, my + .3); ctx.quadraticCurveTo(0, my - .8, 1, my + .3); ctx.quadraticCurveTo(0, my + .9, -1, my + .3); ctx.fill(); break;
  }
  if (o.tears || eyes === 'cry') for (const sd of [-1, 1]) brush([[sd * 2.3, -5.3], [sd * 2.6, -4], [sd * 2.4, -2.4 + frac(T * 2) * .4]], .7, alpha('#A8E0FF', .9), 'mid', { min: .5 });
  if (o.sweat) sweatDrop(5.2, -8.2, .8, lw);
  if (o.band) { solid(rrPts(-5.15, -7.9, 10.3, 1.2, .2), IP.white, { shade: false, line, lw: lw * .8, sharp: true }); dtext(o.band, 0, -7.28, .85, { fill: MEMBERS.TOKI.col, maxW: 9 }); }
  if (o.towel) {
    const w = 11, h = 2.4, yT = -2.2 + Math.sin(bpOf(T) * Math.PI) * .15;
    solid(rrPts(-w / 2, yT - h / 2, w, h, .3), o.towelCol ?? MEMBERS.TOKI.col, { shade: false, line, lw: lw * .8, sharp: true });
    dtext(o.towel, 0, yT + .08, 1.35, { fill: IP.white, strokes: [[mixCol(o.towelCol ?? MEMBERS.TOKI.col, IP.plum, .3), .3]], maxW: w - 1 });
  }
  for (const [sd, a, fn] of back) nub(sd, o.towel ? -.35 : a, fn);
  if (o.label) nameBadge(o.label, 0, -3.2, 1.4, IP.neonPink);
  ctx.restore();
}

// =====================================================================================================
// STAGE, LIGHT & PARTY KIT
// =====================================================================================================
// Background gradient (vertical by default). stops: [[0, col], [1, col]] or two colours.
function bgGrad(c0, c1, o = {}) {
  const g = o.radial ? ctx.createRadialGradient(o.cx ?? W / 2, o.cy ?? H / 2, 0, o.cx ?? W / 2, o.cy ?? H / 2, o.r ?? 1200) : ctx.createLinearGradient(o.x0 ?? 0, o.y0 ?? 0, o.x1 ?? 0, o.y1 ?? H);
  if (Array.isArray(c0)) c0.forEach(([k, c]) => g.addColorStop(k, c)); else { g.addColorStop(0, c0); g.addColorStop(1, c1); }
  // cover the whole canvas under any camera: fill the canvas corners' bounding box in world coordinates
  const m = ctx.getTransform().inverse(), cs = [[0, 0], [W * RS, 0], [0, H * RS], [W * RS, H * RS]].map(([x, y]) => [m.a * x + m.c * y + m.e, m.b * x + m.d * y + m.f]);
  const xs = cs.map(c => c[0]), ys = cs.map(c => c[1]), x0 = Math.min(...xs), y0 = Math.min(...ys);
  ctx.fillStyle = g; ctx.fillRect(x0, y0, Math.max(...xs) - x0, Math.max(...ys) - y0);
}
// Cached pastel pattern backgrounds: 'polka' | 'check' | 'stripe' | 'hearts' | 'stars' | 'grid'. Scroll with (dx, dy).
function patternBG(kind, c0, c1, o = {}) {
  const cell = o.cell ?? 80;
  const img = cached(`pat|${kind}|${c0}|${c1}|${cell}`, cell, cell, (w, h) => {
    ctx.fillStyle = c0; ctx.fillRect(0, 0, w, h); ctx.fillStyle = c1;
    if (kind === 'polka') { ctx.beginPath(); ctx.arc(w * .25, h * .25, w * .12, 0, TAU); ctx.arc(w * .75, h * .75, w * .12, 0, TAU); ctx.fill(); }
    else if (kind === 'check') { ctx.fillRect(0, 0, w / 2, h / 2); ctx.fillRect(w / 2, h / 2, w / 2, h / 2); }
    else if (kind === 'stripe') { ctx.beginPath(); ctx.moveTo(0, 0); ctx.lineTo(w / 2, 0); ctx.lineTo(0, h / 2); ctx.closePath(); ctx.moveTo(w, 0); ctx.lineTo(w, h / 2); ctx.lineTo(w / 2, h); ctx.lineTo(0, h); ctx.closePath(); ctx.fill(); }
    else if (kind === 'hearts') { tracePath(heartPts(w * .28, h * .3, w * .14, 24)); ctx.fill(); tracePath(heartPts(w * .78, h * .78, w * .1, 24)); ctx.fill(); }
    else if (kind === 'stars') { tracePath(starPts(w * .3, h * .3, w * .14, .45)); ctx.fill(); ctx.beginPath(); ctx.arc(w * .78, h * .75, w * .05, 0, TAU); ctx.fill(); }
    else if (kind === 'grid') { ctx.fillRect(0, 0, w, 2); ctx.fillRect(0, 0, 2, h); }
  });
  const pat = ctx.createPattern(img, 'repeat');
  const m = new DOMMatrix().translateSelf(((o.dx ?? 0) % cell), ((o.dy ?? 0) % cell)).rotateSelf(o.rot ?? 0).scaleSelf(1 / RS);
  pat.setTransform(m);
  ctx.save(); ctx.fillStyle = pat; if (o.alpha !== undefined) ctx.globalAlpha *= o.alpha; ctx.fillRect(-400, -400, W + 800, H + 800); ctx.restore();
}
// Sunburst rays behind a subject. n rays alternating c0/c1.
function rays(cx, cy, n, c0, c1, rot = 0, R = 2600) {
  ctx.fillStyle = c0; ctx.fillRect(-400, -400, W + 800, H + 800);
  ctx.fillStyle = c1; ctx.beginPath();
  for (let i = 0; i < n; i++) { const a0 = rot + i / n * TAU, a1 = a0 + TAU / n / 2; ctx.moveTo(cx, cy); ctx.lineTo(cx + Math.cos(a0) * R, cy + Math.sin(a0) * R); ctx.lineTo(cx + Math.cos(a1) * R, cy + Math.sin(a1) * R); ctx.closePath(); }
  ctx.fill();
}
// 4-point twinkle star with a soft glow.
function sparkle(x, y, r, rot = 0, col = IP.white, o = {}) {
  if (r <= 0) return;
  ctx.save(); ctx.translate(x, y); ctx.rotate(rot);
  if (o.glow !== false) glow(0, 0, r * 1.8, o.glowCol ?? col, .5);
  ctx.fillStyle = col; ctx.beginPath();
  const k = r * .16;
  ctx.moveTo(0, -r); ctx.quadraticCurveTo(k, -k, r, 0); ctx.quadraticCurveTo(k, k, 0, r); ctx.quadraticCurveTo(-k, k, -r, 0); ctx.quadraticCurveTo(-k, -k, 0, -r);
  ctx.fill(); ctx.restore();
}
// A field of twinkling sparkles. o: n, seed, x0, y0, x1, y1, r, cols, speed
function sparkles(t, o = {}) {
  const n = o.n ?? 24, seed = o.seed ?? 7, cols = o.cols ?? [IP.white, IP.lemon, IP.pink, IP.sky];
  for (let i = 0; i < n; i++) {
    const r = k => hash2(seed + i, k);
    const ph = frac(t * (o.speed ?? .9) * (.6 + r(1)) + r(2)), k = Math.sin(ph * Math.PI) ** 2;
    if (k < .05) continue;
    const x = lerp(o.x0 ?? 0, o.x1 ?? W, r(3)), y = lerp(o.y0 ?? 0, o.y1 ?? H, r(4));
    sparkle(x, y, (o.r ?? 22) * (.5 + r(5)) * k, r(6) * .5, cols[Math.floor(r(7) * cols.length)]);
  }
}
// Soft drifting bokeh circles (additive). o: n, seed, cols, r, alpha, y0, y1
function bokeh(t, o = {}) {
  const n = o.n ?? 18, seed = o.seed ?? 3, cols = o.cols ?? [IP.neonPink, IP.neonCyan, IP.lilac, IP.neonGold];
  ctx.save(); ctx.globalCompositeOperation = 'lighter';
  for (let i = 0; i < n; i++) {
    const r = k => hash2(seed + i, k), rad = (o.r ?? 70) * (.5 + r(1));
    const x = frac(r(2) + t * .015 * (r(3) - .5)) * (W + 300) - 150, y = lerp(o.y0 ?? 0, o.y1 ?? H, r(4)) + Math.sin(t * .6 + i) * 20;
    const c = cols[Math.floor(r(5) * cols.length)], a = (o.alpha ?? .22) * (.6 + .4 * Math.sin(t * 1.3 + i * 2));
    const g = ctx.createRadialGradient(x, y, 0, x, y, rad); g.addColorStop(0, alpha(c, a)); g.addColorStop(.75, alpha(c, a * .8)); g.addColorStop(1, alpha(c, 0));
    ctx.fillStyle = g; ctx.fillRect(x - rad, y - rad, rad * 2, rad * 2);
  }
  ctx.restore();
}
// Anime speed/focus lines converging on (cx, cy), re-rolled 12×/s. o: n, r0 (clear radius), col, w (max width), alpha
function speedLines(cx, cy, o = {}) {
  const n = o.n ?? 70, r0 = o.r0 ?? 380, R = 2400, col = o.col ?? IP.white;
  ctx.save(); ctx.globalAlpha *= o.alpha ?? .8; ctx.fillStyle = col; ctx.beginPath();
  for (let i = 0; i < n; i++) {
    const a = (i + hash2(_boil, i) * .8) / n * TAU, w = (o.w ?? .012) * (.3 + hash2(_boil, i + 99)), r1 = r0 * (1 + hash2(_boil, i + 50) * .6);
    ctx.moveTo(cx + Math.cos(a) * r1, cy + Math.sin(a) * r1);
    ctx.lineTo(cx + Math.cos(a - w) * R, cy + Math.sin(a - w) * R); ctx.lineTo(cx + Math.cos(a + w) * R, cy + Math.sin(a + w) * R); ctx.closePath();
  }
  ctx.fill(); ctx.restore();
}
// Anamorphic lens flare at (x, y), strength k (0..1+). Ghosts run toward the screen centre. o: col
function flare(x, y, k = 1, o = {}) {
  if (k <= 0) return;
  const col = o.col ?? '#9FD8FF';
  ctx.save(); ctx.globalCompositeOperation = 'lighter';
  glow(x, y, 260 * k, col, .55 * k); glow(x, y, 70 * k, IP.white, .9 * k);
  const g = ctx.createLinearGradient(x - 900 * k, 0, x + 900 * k, 0);
  g.addColorStop(0, alpha(col, 0)); g.addColorStop(.5, alpha(IP.white, .85 * clamp(k))); g.addColorStop(1, alpha(col, 0));
  ctx.fillStyle = g; ctx.beginPath(); ctx.ellipse(x, y, 900 * k, 7 * k, 0, 0, TAU); ctx.fill();
  const dx = W / 2 - x, dy = H / 2 - y;
  [[.6, 40, IP.neonPink], [1.1, 22, IP.neonCyan], [1.45, 70, IP.lilac], [1.8, 30, IP.neonGold]].forEach(([f, r, c]) => {
    const gx = x + dx * f, gy = y + dy * f, gg = ctx.createRadialGradient(gx, gy, 0, gx, gy, r * k * 1.6);
    gg.addColorStop(0, alpha(c, .05)); gg.addColorStop(.7, alpha(c, .22 * k)); gg.addColorStop(1, alpha(c, 0));
    ctx.fillStyle = gg; ctx.fillRect(gx - r * 2 * k, gy - r * 2 * k, r * 4 * k, r * 4 * k);
  });
  ctx.restore();
}
// Volumetric stage beams from (x, y0) aimed at angle a (radians from straight down), additive. o: w (spread), len, col, alpha
function beam(x, y0, a, o = {}) {
  const len = o.len ?? 1400, sp = o.w ?? .12, col = o.col ?? IP.lilac;
  ctx.save(); ctx.globalCompositeOperation = 'lighter';
  const ex = x + Math.sin(a) * len, ey = y0 + Math.cos(a) * len;
  const g = ctx.createLinearGradient(x, y0, ex, ey);
  g.addColorStop(0, alpha(col, o.alpha ?? .5)); g.addColorStop(1, alpha(col, 0));
  ctx.fillStyle = g; ctx.beginPath(); ctx.moveTo(x - 8, y0); ctx.lineTo(x + 8, y0);
  ctx.lineTo(x + Math.sin(a + sp) * len, y0 + Math.cos(a + sp) * len); ctx.lineTo(x + Math.sin(a - sp) * len, y0 + Math.cos(a - sp) * len); ctx.closePath(); ctx.fill();
  glow(x, y0, 40, col, .8);
  ctx.restore();
}
// Lightstick (ATTN!'s official one: a glowing heart on a white stick). (x, y) = heart centre; s ≈ heart radius.
function lightstick(x, y, s, col, o = {}) {
  ctx.save(); ctx.translate(x, y); if (o.rot) ctx.rotate(o.rot);
  ctx.save(); ctx.globalCompositeOperation = 'lighter'; glow(0, 0, s * 3.2, col, .55); ctx.restore();
  solid(rrPts(-s * .22, s * .55, s * .44, s * 2.4, s * .15), '#F4F2FA', { shade: '#BDB6D6', sh: s * .1, line: IP.line, lw: s * .12, sharp: true });
  solid(heartPts(0, 0, s, 30), mixCol(col, IP.white, .55), { shade: false, line: alpha(IP.white, .9), lw: s * .14 });
  ctx.fillStyle = alpha(IP.white, .85); ctx.beginPath(); ctx.ellipse(-s * .35, -s * .25, s * .2, s * .13, -.6, 0, TAU); ctx.fill();
  ctx.restore();
}
// The lightstick ocean: rows of fans' glowing sticks from y0 (far) to y1 (near). o: rows, n (sticks in the near row), cols (list; or
// one colour), mode ('sway'|'pump'|'wave'), seed, x0, x1, heads (dark heads in front rows), k (energy 0..1)
function lightOcean(t, o = {}) {
  const rows = o.rows ?? 7, y0 = o.y0 ?? 760, y1 = o.y1 ?? 1080, cols = [].concat(o.cols ?? [MEMBERS.TOKI.col, IP.lilac]), seed = o.seed ?? 11;
  const b = bpOf(t), en = o.k ?? 1, x0 = o.x0 ?? -60, x1 = o.x1 ?? W + 60;
  for (let r = 0; r < rows; r++) {
    const u = r / (rows - 1 || 1), y = lerp(y0, y1, u * u), sc = lerp(.28, 1, u * u), n = Math.round((o.n ?? 16) / sc);
    // dark crowd band
    ctx.fillStyle = mixCol('#0B0618', IP.night, .3);
    const headR = 26 * sc;
    if (o.heads !== false) { ctx.beginPath(); for (let i = 0; i < n; i++) { const hx = lerp(x0, x1, (i + .5 + (hash2(seed + r, i) - .5) * .6) / n), hy = y + headR * 1.2 + Math.sin((b + hash2(r, i)) * Math.PI) * 4 * sc * en; ctx.moveTo(hx + headR, hy); ctx.arc(hx, hy, headR, 0, TAU); } ctx.fill(); ctx.fillRect(x0, y + headR * 1.6, x1 - x0, 60 * sc + 40); }
    ctx.save(); ctx.globalCompositeOperation = 'lighter';
    for (let i = 0; i < n; i++) {
      const hr = k => hash2(seed * 13 + r * 101 + i, k);
      const sx = lerp(x0, x1, (i + .5 + (hr(1) - .5) * .7) / n);
      let a = 0, lift = 0;
      if ((o.mode ?? 'sway') === 'sway') a = Math.sin((b * .5 + hr(2) * .15) * Math.PI) * .45 * en;
      else if (o.mode === 'pump') lift = Math.max(0, Math.sin((b + hr(2) * .1) * Math.PI)) * 30 * sc * en;
      else if (o.mode === 'wave') lift = Math.max(0, Math.sin((b * .5 - sx / 600) * Math.PI)) * 60 * sc * en;
      const L = 70 * sc, bx = sx + Math.sin(a) * L, by = y - Math.cos(a) * L - lift;
      const c = cols[Math.floor(hr(3) * cols.length)];
      const spr = glowSprite(c, '#FFFFFF');
      const R = 42 * sc * (o.big ?? 1);
      ctx.drawImage(spr, bx - R, by - R, R * 2, R * 2);
    }
    ctx.restore();
    if (sc > .6) for (let i = 0; i < n; i += 1) {         // near rows: draw the actual sticks
      const hr = k => hash2(seed * 13 + r * 101 + i, k);
      const sx = lerp(x0, x1, (i + .5 + (hr(1) - .5) * .7) / n);
      let a = 0, lift = 0;
      if ((o.mode ?? 'sway') === 'sway') a = Math.sin((b * .5 + hr(2) * .15) * Math.PI) * .45 * en;
      else if (o.mode === 'pump') lift = Math.max(0, Math.sin((b + hr(2) * .1) * Math.PI)) * 30 * sc * en;
      else if (o.mode === 'wave') lift = Math.max(0, Math.sin((b * .5 - sx / 600) * Math.PI)) * 60 * sc * en;
      const L = 70 * sc, bx = sx + Math.sin(a) * L, by = y - Math.cos(a) * L - lift;
      ctx.save(); ctx.translate(bx, by); ctx.rotate(a);
      ctx.fillStyle = '#E8E4F4'; ctx.fillRect(-4 * sc, 10 * sc, 8 * sc, L);
      tracePath(heartPts(0, 0, 14 * sc, 20)); ctx.fillStyle = mixCol(cols[Math.floor(hr(3) * cols.length)], IP.white, .6); ctx.fill();
      ctx.restore();
    }
  }
}
// Confetti cannon burst fired at t0 from (x, y) toward angle ang (radians, 0 = right, −π/2 = up). Deterministic particles.
// o: n, spread, speed, cols, seed, life, shapes ('rect'|'heart'|'star'|'circle' mix), size, grav
function confetti(t, t0, x, y, ang = -Math.PI / 2, o = {}) {
  const age = t - t0; if (age < 0) return;
  const n = o.n ?? 70, life = o.life ?? 3.2; if (age > life) return;
  const cols = o.cols ?? [IP.neonPink, IP.neonGold, IP.neonCyan, IP.lilac, IP.white, IP.mint], seed = o.seed ?? Math.floor(t0 * 100);
  const shapes = o.shapes ?? ['rect', 'rect', 'heart', 'star', 'circle'];
  for (let i = 0; i < n; i++) {
    const r = k => hash2(seed + i, k);
    const a = ang + (r(1) - .5) * (o.spread ?? .9), v = (o.speed ?? 1500) * (.45 + r(2) * .75);
    const drag = 2.2, k = (1 - Math.exp(-drag * age)) / drag;
    const px = x + Math.cos(a) * v * k + Math.sin(age * 5 + i) * 18 * age;
    const py = y + Math.sin(a) * v * k + (o.grav ?? 380) * age * age * .5 + age * 60;
    if (py > H + 60) continue;
    const sz = (o.size ?? 13) * (.6 + r(3) * .8), rot = r(4) * TAU + age * (4 + r(5) * 8), flip = Math.cos(age * (6 + r(6) * 8) + i);
    const c = cols[Math.floor(r(7) * cols.length)], shp = shapes[Math.floor(r(8) * shapes.length)];
    ctx.save(); ctx.translate(px, py); ctx.rotate(rot); ctx.scale(1, flip); ctx.globalAlpha *= clamp((life - age) / .5);
    ctx.fillStyle = c;
    if (shp === 'heart') { tracePath(heartPts(0, 0, sz * .7, 16)); ctx.fill(); }
    else if (shp === 'star') { tracePath(starPts(0, 0, sz * .8, .45)); ctx.fill(); }
    else if (shp === 'circle') { ctx.beginPath(); ctx.arc(0, 0, sz * .45, 0, TAU); ctx.fill(); }
    else ctx.fillRect(-sz * .5, -sz * .28, sz, sz * .56);
    ctx.restore();
  }
}
// Steady confetti rain from above. o: n, cols, seed, speed, size
function confettiRain(t, o = {}) {
  const n = o.n ?? 40, cols = o.cols ?? [IP.neonPink, IP.neonGold, IP.neonCyan, IP.lilac, IP.white], seed = o.seed ?? 21;
  for (let i = 0; i < n; i++) {
    const r = k => hash2(seed + i, k), sp = (o.speed ?? 160) * (.6 + r(1) * .8);
    const y = frac(r(2) + t * sp / (H + 100)) * (H + 100) - 50, x = r(3) * W + Math.sin(t * 2 + i) * 30;
    const sz = (o.size ?? 12) * (.6 + r(4) * .7);
    ctx.save(); ctx.translate(x, y); ctx.rotate(r(5) * TAU + t * 3); ctx.scale(1, Math.cos(t * 5 + i));
    ctx.fillStyle = cols[Math.floor(r(6) * cols.length)]; ctx.fillRect(-sz / 2, -sz * .3, sz, sz * .6); ctx.restore();
  }
}
// Floating hearts rising (fan love). o: n, seed, cols, x0, x1, size
function heartsRise(t, o = {}) {
  const n = o.n ?? 12, seed = o.seed ?? 5, cols = o.cols ?? ['#FF4F9A', '#FF8FC0', IP.lilac];
  for (let i = 0; i < n; i++) {
    const r = k => hash2(seed + i, k), ph = frac(r(1) + t * (.25 + r(2) * .2));
    const x = lerp(o.x0 ?? 0, o.x1 ?? W, r(3)) + Math.sin(ph * 8 + i) * 25, y = (o.y ?? H + 40) - ph * (o.h ?? 700);
    const sz = (o.size ?? 26) * (.6 + r(4) * .7) * Math.sin(Math.min(1, ph * 4) * Math.PI / 2);
    ctx.save(); ctx.globalAlpha *= clamp((1 - ph) * 3);
    solid(heartPts(x, y, sz, 24), cols[Math.floor(r(5) * cols.length)], { shade: false, line: alpha(IP.white, .9), lw: sz * .12 });
    ctx.restore();
  }
}

// ---------- LED wall: content drawn at LED resolution, upscaled with hard pixels, then the LED grid on top ----------
const _ledCv = new Map();
function ledPattern(cell) {
  const key = `ledpat|${cell.toFixed(2)}|${RS}`;
  let p = _patCache.get(key);
  if (!p) {
    const px = Math.max(3, Math.round(cell * RS * 2)), c = makeCanvas(px, px), g = c.getContext('2d');
    g.fillStyle = 'rgb(6 2 16 / .72)'; g.fillRect(0, 0, px, px);
    g.globalCompositeOperation = 'destination-out'; g.beginPath(); g.arc(px / 2, px / 2, px * .36, 0, TAU); g.fill();
    p = ctx.createPattern(c, 'repeat'); p.setTransform(new DOMMatrix().scaleSelf(cell / px));
    _patCache.set(key, p);
  }
  return p;
}
// ledWall(x, y, w, h, draw(w, h), o): draw() paints the wall's content in wall-local coordinates (0..w, 0..h) with any kit helper
// (even idol() for a giant live-cam feed). o: cols (LED columns, default w / 9), frame (true), glow (spill colour), bright (0..1)
function ledWall(x, y, w, h, draw, o = {}) {
  const cols = Math.round(o.cols ?? w / 9), rows = Math.max(1, Math.round(cols * h / w)), key = `${cols}x${rows}`;
  let c = _ledCv.get(key); if (!c) { c = makeCanvas(cols, rows); _ledCv.set(key, c); }
  const g = c.getContext('2d'), saved = ctx, savedLight = LIGHT;
  ctx = g; ctx.setTransform(cols / w, 0, 0, rows / h, 0, 0); ctx.globalAlpha = 1; ctx.globalCompositeOperation = 'source-over';
  ctx.fillStyle = '#05020C'; ctx.fillRect(0, 0, w, h);
  try { draw(w, h); } finally { ctx = saved; LIGHT = savedLight; }
  ctx.save();
  if (o.frame !== false) { ctx.fillStyle = '#0C0818'; ctx.fillRect(x - 14, y - 14, w + 28, h + 28); }
  ctx.imageSmoothingEnabled = false; ctx.globalAlpha *= o.bright ?? 1; ctx.drawImage(c, x, y, w, h); ctx.imageSmoothingEnabled = true;
  ctx.globalAlpha = 1;
  ctx.fillStyle = ledPattern(w / cols); ctx.translate(x, y); ctx.fillRect(0, 0, w, h); ctx.translate(-x, -y);
  const sh = ctx.createLinearGradient(x, y, x + w * .4, y + h); sh.addColorStop(0, 'rgb(255 255 255 / .1)'); sh.addColorStop(.5, 'rgb(255 255 255 / 0)');
  ctx.fillStyle = sh; ctx.fillRect(x, y, w, h);
  if (o.frame !== false) { ctx.strokeStyle = '#2A2340'; ctx.lineWidth = 6; ctx.strokeRect(x - 3, y - 3, w + 6, h + 6); }
  if (o.glow) { ctx.globalCompositeOperation = 'lighter'; const gg = ctx.createLinearGradient(0, y + h, 0, y + h + 260); gg.addColorStop(0, alpha(o.glow, .35)); gg.addColorStop(1, alpha(o.glow, 0)); ctx.fillStyle = gg; ctx.fillRect(x - 100, y + h, w + 200, 260); }
  ctx.restore();
}
// Stock LED content. ledShow(kind, t, w, h, o) — call inside a ledWall draw(). kinds: 'hearts' (scrolling heart tiles), 'bars' (EQ), 'tunnel',
// 'curve' (the neon scaling curve; o.k = draw-on 0..1, o.level = steepness 1..4), 'text' (o.text, o.col), 'logo', 'rays', 'member' (o.member)
function ledShow(kind, t, w, h, o = {}) {
  const b = bpOf(t), p = pulse(t, 5);
  const col = o.col ?? IP.neonPink;
  switch (kind) {
    case 'hearts': { bgGrad(IP.plum, '#12051F', { y1: h }); const cell = h / 3; for (let j = -1; j < 4; j++) for (let i = -1; i < w / cell + 1; i++) { const x = i * cell + frac(t * .25) * cell * ((j % 2) ? 1 : -1), y = j * cell + cell / 2; tracePath(heartPts(x, y, cell * (.28 + .06 * p), 20)); ctx.fillStyle = [(IP.neonPink), IP.lilac, IP.neonCyan][((i + j) % 3 + 3) % 3]; ctx.fill(); } break; }
    case 'bars': { bgGrad('#12051F', IP.plum, { y1: h }); const n = 24; for (let i = 0; i < n; i++) { const v = .25 + .7 * Math.abs(Math.sin(i * 1.7 + b * 1.3)) * (.6 + .4 * p); const bw = w / n; const gg = ctx.createLinearGradient(0, h, 0, h - v * h); gg.addColorStop(0, IP.neonCyan); gg.addColorStop(1, IP.neonPink); ctx.fillStyle = gg; ctx.fillRect(i * bw + bw * .15, h - v * h, bw * .7, v * h); } break; }
    case 'tunnel': { ctx.fillStyle = '#0A0418'; ctx.fillRect(0, 0, w, h); for (let i = 8; i >= 0; i--) { const k = frac(i / 8 + t * .5), s = k * k * 1.6; ctx.strokeStyle = [IP.neonPink, IP.neonCyan, IP.lilac][i % 3]; ctx.lineWidth = 3 + s * 30; ctx.globalAlpha = clamp(k * 1.5); rrect(w / 2 - w * s / 2, h / 2 - h * s / 2, w * s, h * s, 40 * s); ctx.stroke(); } ctx.globalAlpha = 1; break; }
    case 'rays': rays(w / 2, h / 2, 16, o.c0 ?? '#2A0E52', o.c1 ?? '#4A1C8A', t * .3); break;
    case 'curve': {
      bgGrad('#0A0418', '#1C0A3A', { y1: h });
      ctx.strokeStyle = alpha(IP.lilac, .25); ctx.lineWidth = 2; for (let i = 1; i < 6; i++) { ctx.beginPath(); ctx.moveTo(0, h * i / 6); ctx.lineTo(w, h * i / 6); ctx.stroke(); ctx.beginPath(); ctx.moveTo(w * i / 6, 0); ctx.lineTo(w * i / 6, h); ctx.stroke(); }
      const steep = [2.2, 3.4, 5, 8][clamp((o.level ?? 1) - 1, 0, 3) | 0], pts = [];
      for (let i = 0; i <= 60; i++) { const u = i / 60, v = (Math.exp(u * steep) - 1) / (Math.exp(steep) - 1); pts.push([w * .06 + u * w * .88, h * .9 - v * h * .82 * (o.over ?? 1)]); }
      const P = partial(pts, o.k ?? 1);
      ln(P, alpha(col, .45), 26); ln(P, col, 12); ln(P, IP.white, 4);
      const tip = P[P.length - 1]; sparkle(tip[0], tip[1], 30 + 16 * p, t, IP.white);
      break;
    }
    case 'text': { ctx.fillStyle = o.bg ?? '#0A0418'; ctx.fillRect(0, 0, w, h); dtext(o.text ?? 'ATTN!', w / 2, h / 2, o.size ?? h * .45, { fill: col, strokes: [[IP.white, (o.size ?? h * .45) * .08]], maxW: w * .92 }); break; }
    case 'logo': { ledShow('rays', t, w, h, o); attnLogo(w / 2, h / 2, h * .42, { t }); break; }
    case 'member': { const M = MEMBERS[o.member ?? 'TOKI']; bgGrad(M.col, mixCol(M.col, IP.night, .6), { y1: h }); dtext(M.name, w / 2, h * .5, h * .5, { fill: IP.white, maxW: w * .9 }); break; }
  }
}
// The ATTN! logo. (x, y) centre; size = cap height. o: t (for the sparkle), pop (0..1 letter-by-letter), grad
function attnLogo(x, y, size, o = {}) {
  const letters = ['A', 'T', 'T', 'N'], pop = o.pop ?? 1;
  const ws = letters.map(l => textW(l, size, 'rammetto')), gap = size * .02, bangW = size * .42;
  const total = ws.reduce((a, b) => a + b, 0) + gap * 4 + bangW;
  let cx = x - total / 2;
  letters.forEach((l, i) => {
    const k = clamp((pop - i * .15) / .25), s = backOut(k, 2.4);
    const lx = cx + ws[i] / 2; cx += ws[i] + gap;
    if (k <= 0) return;
    ctx.save(); ctx.translate(lx, y); ctx.scale(s, s); ctx.rotate((i % 2 ? .04 : -.04));
    dtext(l, 0, 0, size, { grad: o.grad ?? ['#FFFFFF', '#FFC2E4', '#FF4FA8'], strokes: [[IP.night, size * .2], [IP.white, size * .1]], shadow: [size * .04, size * .07, 'rgb(20 8 40 / .5)'] });
    ctx.restore();
  });
  const k = clamp((pop - .6) / .3); if (k <= 0) return;
  const bx = cx + bangW / 2, s = backOut(k, 2.6);
  ctx.save(); ctx.translate(bx, y); ctx.scale(s, s); ctx.rotate(.12);
  solid([[-size * .16, -size * .52], [size * .16, -size * .52], [size * .08, size * .12], [-size * .08, size * .12]], IP.neonGold, { shade: '#E09A20', sh: size * .04, line: IP.night, lw: size * .07 });
  solid(heartPts(0, size * .36, size * .16, 24), IP.neonPink, { shade: false, line: IP.night, lw: size * .06 });
  ctx.restore();
  if (o.t !== undefined) sparkle(bx + size * .25, y - size * .45, size * .22 * (.7 + .3 * Math.sin(o.t * 6)), o.t, IP.white);
}

// =====================================================================================================
// VARIETY-SHOW & MV GRAPHICS
// =====================================================================================================
// Variety caption sticker: bold rounded text, fat outlines, optional icon, pops in. o: size, fill, grad, line (inner outline), edge
// (outer outline), rot, pop (0..1), icon (heart|sweat|spark|q|bang|note|fire|star), box (pastel box colour behind), maxW, shake (px)
const VCAP = {
  yellow: { grad: ['#FFFBE0', '#FFE14D'], line: '#3A1A55', edge: IP.white },
  pink: { grad: ['#FFFFFF', '#FF8FC8'], line: '#6A1447', edge: IP.white },
  cyan: { grad: ['#FFFFFF', '#6FF0FF'], line: '#123A6A', edge: IP.white },
  shock: { grad: ['#FFF3A0', '#FF4B5C'], line: '#2A0A1A', edge: IP.white },
  white: { fill: IP.white, line: '#2A1438', edge: '#FF8FC8' },
  lilac: { grad: ['#FFFFFF', '#C3A8FF'], line: '#2E1A6A', edge: IP.white },
};
function vcap(str, x, y, o = {}) {
  const st = VCAP[o.style ?? 'yellow'] || VCAP.yellow, size = o.size ?? 64, k = o.pop ?? 1;
  if (k <= 0) return;
  ctx.save(); ctx.translate(x + (o.shake ? jit(o.shake) : 0), y + (o.shake ? jit(o.shake) : 0));
  ctx.rotate(o.rot ?? -.04); const s = backOut(clamp(k), 2.6); ctx.scale(s, s);
  const lines = String(str).split('\n'), w = Math.max(...lines.map(l => textW(l, size, o.font ?? 'rammetto')));
  if (o.box) { const bw = Math.min(w, o.maxW ?? 1e9) + size * 1.1, bh = lines.length * size * 1.15 + size * .6; rrect(-bw / 2, -bh / 2, bw, bh, size * .35); ctx.fillStyle = o.box; ctx.fill(); ctx.lineWidth = size * .08; ctx.strokeStyle = st.line; ctx.stroke(); }
  lines.forEach((l, i) => dtext(l, 0, (i - (lines.length - 1) / 2) * size * 1.12, size, { font: o.font ?? 'rammetto', grad: o.grad ?? st.grad, fill: o.fill ?? st.fill, strokes: [[o.edge ?? st.edge, size * .34], [o.line ?? st.line, size * .18]], shadow: [size * .05, size * .09, 'rgb(20 8 40 / .35)'], maxW: o.maxW, skew: o.skew }));
  if (o.icon) { const ix = Math.min(w, o.maxW ?? 1e9) / 2 + size * .55, iy = -size * .45 * lines.length; emote(o.icon === 'star' ? 'spark' : o.icon, ix, iy, size * .75, 1); }
  ctx.restore();
}
// Small parenthetical caption, e.g. "(nervous)". o: col (pill), size, rot, pop
function vtag(str, x, y, o = {}) {
  const size = o.size ?? 30, k = o.pop ?? 1; if (k <= 0) return;
  ctx.save(); ctx.translate(x, y); ctx.rotate(o.rot ?? .02); const s = backOut(clamp(k), 2); ctx.scale(s, s);
  const w = textW(str, size, 'rammetto') + size * 1.2, h = size * 1.55;
  rrect(-w / 2, -h / 2, w, h, h / 2); ctx.fillStyle = o.col ?? 'rgb(255 255 255 / .92)'; ctx.fill(); ctx.strokeStyle = o.line ?? IP.neonPink; ctx.lineWidth = size * .12; ctx.stroke();
  dtext(str, 0, size * .04, size, { fill: o.ink ?? IP.ink });
  ctx.restore();
}
// Sound-effect lettering: skewed, gradient, heavy outline, shakes. o: size, grad, rot, pop, shake, font
function sfx(str, x, y, o = {}) {
  const size = o.size ?? 110, k = o.pop ?? 1; if (k <= 0) return;
  ctx.save(); ctx.translate(x + jit(o.shake ?? 3), y + jit(o.shake ?? 3)); ctx.rotate(o.rot ?? -.12); const s = backOut(clamp(k), 3); ctx.scale(s, s);
  dtext(str, 0, 0, size, { font: o.font ?? 'bungee', grad: o.grad ?? ['#FFFFFF', '#FFE14D', '#FF6A3D'], strokes: [[o.edge ?? IP.white, size * .26], [o.line ?? '#2A0A1A', size * .14]], shadow: [size * .06, size * .1, 'rgb(20 8 40 / .4)'], skew: o.skew ?? -.18, spacing: size * .02 });
  ctx.restore();
}
// Photocard (collectible idol card). (x, y) centre, w width (h = 1.55w). o: draw(w, h) content in card-local coords (0..w, 0..h),
// member, name, rot, s, flip (0..1 turns it over to the logo back), holo (sheen strength), t
function photocard(x, y, w, o = {}) {
  const h = w * 1.55, M = MEMBERS[o.member ?? 'TOKI'], t = o.t ?? T;
  const fl = o.flip ?? 0, sx = Math.cos(fl * Math.PI), backSide = sx < 0;
  ctx.save(); ctx.translate(x, y); ctx.rotate(o.rot ?? 0); ctx.scale((o.s ?? 1) * Math.max(.02, Math.abs(sx)), o.s ?? 1);
  ctx.fillStyle = 'rgb(20 8 40 / .3)'; rrect(-w / 2 + 10, -h / 2 + 14, w, h, w * .07); ctx.fill();
  rrect(-w / 2, -h / 2, w, h, w * .07); ctx.fillStyle = IP.white; ctx.fill();
  ctx.save(); rrect(-w / 2 + w * .045, -h / 2 + w * .045, w * .91, h - w * .09, w * .05); ctx.clip();
  ctx.translate(-w / 2 + w * .045, -h / 2 + w * .045);
  const iw = w * .91, ih = h - w * .09;
  if (backSide) { bgGrad(M.lt, M.col, { y1: ih }); patternBG('hearts', 'rgb(0 0 0 / 0)', alpha(IP.white, .35), { cell: iw / 4 }); attnLogo(iw / 2, ih / 2, iw * .22, {}); }
  else if (o.draw) o.draw(iw, ih);
  // holo sheen
  const hk = o.holo ?? .5;
  if (hk > 0) {
    ctx.globalCompositeOperation = 'screen';
    const off = frac(t * .35) * iw * 3 - iw;
    const g = ctx.createLinearGradient(off, 0, off + iw, ih);
    ['rgb(255 120 200 / 0)', 'rgb(255 120 200 / .5)', 'rgb(120 230 255 / .5)', 'rgb(255 240 120 / .5)', 'rgb(180 140 255 / 0)'].forEach((c, i) => g.addColorStop(i / 4, c));
    ctx.globalAlpha = hk; ctx.fillStyle = g; ctx.fillRect(0, 0, iw, ih); ctx.globalAlpha = 1; ctx.globalCompositeOperation = 'source-over';
  }
  if (!backSide && o.name !== false) {
    const nm = o.name ?? M.name;
    rrect(iw * .06, ih - iw * .2, textW(nm, iw * .085, 'rammetto') + iw * .12, iw * .13, iw * .065); ctx.fillStyle = M.col; ctx.fill();
    dtext(nm, iw * .06 + (textW(nm, iw * .085, 'rammetto') + iw * .12) / 2, ih - iw * .135, iw * .085, { fill: IP.white });
    dtext(o.sign ?? '♡ ' + nm.toLowerCase(), iw * .7, ih - iw * .3, iw * .1, { font: 'marker', fill: IP.white, strokes: [[M.col, iw * .02]], rot: -.15 });
  }
  ctx.restore();
  ctx.lineWidth = 3; ctx.strokeStyle = 'rgb(40 20 60 / .25)'; rrect(-w / 2, -h / 2, w, h, w * .07); ctx.stroke();
  ctx.restore();
}
// Fancam overlay (draw last in a shot): REC dot, timecode, title bar, viewfinder corners. o: member, title, zoom, vertical (dark side bars)
function fancam(t, o = {}) {
  const M = MEMBERS[o.member ?? 'TOKI'];
  ctx.save();
  if (o.vertical) { ctx.fillStyle = 'rgb(8 4 16 / .92)'; ctx.fillRect(0, 0, 560, H); ctx.fillRect(W - 560, 0, 560, H); }
  const x0 = o.vertical ? 600 : 60, x1 = o.vertical ? W - 600 : W - 60, y0 = 60, y1 = H - 150;
  ctx.strokeStyle = 'rgb(255 255 255 / .9)'; ctx.lineWidth = 5; ctx.lineCap = 'round';
  for (const [cx, cy, dx, dy] of [[x0, y0, 1, 1], [x1, y0, -1, 1], [x0, y1, 1, -1], [x1, y1, -1, -1]]) { ctx.beginPath(); ctx.moveTo(cx, cy + dy * 60); ctx.lineTo(cx, cy); ctx.lineTo(cx + dx * 60, cy); ctx.stroke(); }
  if (frac(t * 1.25) < .6) { ctx.fillStyle = IP.red; ctx.beginPath(); ctx.arc(x0 + 40, y0 + 42, 13, 0, TAU); ctx.fill(); }
  dtext('REC', x0 + 64, y0 + 44, 30, { align: 'left', font: 'code', fill: IP.white });
  const tc = Math.max(0, t), mm = String(Math.floor(tc / 60)).padStart(2, '0'), ss = String(Math.floor(tc % 60)).padStart(2, '0'), ff = String(Math.floor(frac(tc) * 30)).padStart(2, '0');
  dtext(`00:${mm}:${ss}:${ff}`, x1 - 20, y0 + 44, 28, { align: 'right', font: 'code', fill: IP.white });
  dtext('4K  60FPS', x1 - 20, y0 + 84, 20, { align: 'right', font: 'code', fill: alpha(IP.white, .8) });
  if (o.zoom) dtext(`×${o.zoom.toFixed(1)}`, x0 + 30, y1 - 30, 24, { align: 'left', font: 'code', fill: IP.white });
  // title chip
  const title = o.title ?? `[FANCAM] ${M.name} FOCUS`;
  const tw = textW(title, 26, 'rammetto') + 50;
  rrect((x0 + x1) / 2 - tw / 2, y0 + 14, tw, 52, 26); ctx.fillStyle = 'rgb(15 6 30 / .6)'; ctx.fill(); ctx.strokeStyle = M.col; ctx.lineWidth = 3; ctx.stroke();
  dtext(title, (x0 + x1) / 2, y0 + 42, 26, { fill: IP.white });
  // focus box that breathes
  ctx.strokeStyle = alpha(IP.neonGold, .8); ctx.lineWidth = 3; const fb = 150 + Math.sin(t * 4) * 6;
  const fx = o.focus ? o.focus[0] : (x0 + x1) / 2, fy = o.focus ? o.focus[1] : 420;
  for (const [dx, dy] of [[-1, -1], [1, -1], [-1, 1], [1, 1]]) { ctx.beginPath(); ctx.moveTo(fx + dx * fb, fy + dy * (fb - 30)); ctx.lineTo(fx + dx * fb, fy + dy * fb); ctx.lineTo(fx + dx * (fb - 30), fy + dy * fb); ctx.stroke(); }
  ctx.restore();
}
// Split screen: n panels with slanted white dividers. draw(i, x, y, w, h) paints panel i (in global coords; it is clipped).
// o: slant (px), cols (border colours per panel), gap
function splitPanels(n, draw, o = {}) {
  const sl = o.slant ?? 90, gap = o.gap ?? 14, pw = W / n;
  for (let i = 0; i < n; i++) {
    const xa = i * pw, xb = (i + 1) * pw;
    const poly = [[xa + (i ? sl / 2 : -sl), 0], [xb + (i < n - 1 ? sl / 2 : sl), 0], [xb - (i < n - 1 ? sl / 2 : -sl), H], [xa - (i ? sl / 2 : sl), H]];
    ctx.save(); tracePath(poly); ctx.clip(); draw(i, xa, 0, pw, H); ctx.restore();
  }
  for (let i = 1; i < n; i++) {
    const x = i * pw;
    ctx.save(); ctx.strokeStyle = IP.white; ctx.lineWidth = gap; ctx.beginPath(); ctx.moveTo(x + sl / 2, -10); ctx.lineTo(x - sl / 2, H + 10); ctx.stroke();
    if (o.cols) { ctx.strokeStyle = o.cols[i]; ctx.lineWidth = gap * .35; ctx.stroke(); }
    ctx.restore();
  }
}
// Clean smartphone with an app screen. (x, y) centre, s = height/10. o: screen (fn(w, h) in screen coords), col (case), rot, notch
function phoneUI(x, y, s, o = {}) {
  const w = s * 5, h = s * 10;
  ctx.save(); ctx.translate(x, y); ctx.rotate(o.rot ?? 0);
  solid(rrPts(-w / 2, -h / 2, w, h, s * .7), o.col ?? '#2B2438', { shade: false, line: IP.line, lw: s * .08, sharp: true, dropShadow: [s * .2, s * .3] });
  ctx.save(); rrect(-w / 2 + s * .25, -h / 2 + s * .25, w - s * .5, h - s * .5, s * .5); ctx.clip();
  ctx.translate(-w / 2 + s * .25, -h / 2 + s * .25); ctx.fillStyle = o.bg ?? '#FFF6FB'; ctx.fillRect(0, 0, w, h);
  if (o.screen) o.screen(w - s * .5, h - s * .5);
  ctx.restore();
  ctx.fillStyle = '#2B2438'; rrect(-s * .8, -h / 2 + s * .35, s * 1.6, s * .35, s * .17); ctx.fill();
  ctx.restore();
}
// Chat bubble for phone screens and vignettes. o: me (right side, tinted), col, size, maxW, pop
function chatBubble(str, x, y, o = {}) {
  const size = o.size ?? 30, maxW = o.maxW ?? 420, k = o.pop ?? 1; if (k <= 0) return 0;
  const lines = wrap(str, size, 'archivo', maxW - size), w = Math.max(...lines.map(l => textW(l, size, 'archivo'))) + size * 1.2, h = lines.length * size * 1.25 + size * .8;
  ctx.save(); ctx.translate(x, y); const s = backOut(clamp(k), 2); ctx.scale(s, s);
  const bx = o.me ? -w : 0;
  rrect(bx, -h / 2, w, h, size * .7); ctx.fillStyle = o.col ?? (o.me ? '#FFC2E0' : IP.white); ctx.fill(); ctx.strokeStyle = 'rgb(40 20 60 / .25)'; ctx.lineWidth = 2; ctx.stroke();
  lines.forEach((l, i) => dtext(l, bx + size * .6, -h / 2 + size * .4 + size * .62 + i * size * 1.25, size, { font: 'archivo', fill: o.ink ?? IP.ink, align: 'left' }));
  ctx.restore();
  return h;
}
// Neon curve graph (the song's motif). (x, y) bottom-left, w, h. o: k (draw-on), level (1..4 steepness), col, axes, label, glowK
function neonCurve(x, y, w, h, o = {}) {
  const steep = [2.2, 3.4, 5, 8][clamp((o.level ?? 2) - 1, 0, 3) | 0], pts = [];
  for (let i = 0; i <= 60; i++) { const u = i / 60, v = (Math.exp(u * steep) - 1) / (Math.exp(steep) - 1); pts.push([x + u * w, y - v * h]); }
  if (o.axes !== false) ln([[x, y - h - 20], [x, y], [x + w + 20, y]], alpha(IP.white, .7), 5);
  const P = partial(pts, o.k ?? 1), col = o.col ?? IP.neonPink;
  ctx.save(); ctx.globalCompositeOperation = 'lighter'; ln(P, alpha(col, .35), 34); ctx.restore();
  ln(P, col, 14); ln(P, IP.white, 5);
  const tip = P[P.length - 1]; sparkle(tip[0], tip[1], 34, T * 2, IP.white);
  return tip;
}
// Gift box (for the finale). (x, y) bottom centre, s = width/10. o: col, ribbon, lid (0..1 open), shake
function giftBox(x, y, s, o = {}) {
  const col = o.col ?? IP.neonPink, rb = o.ribbon ?? IP.neonGold, sh = o.shake ?? 0;
  ctx.save(); ctx.translate(x + jit(sh), y); ctx.rotate(jit(sh * .004));
  solid(rrPts(-5 * s, -8 * s, 10 * s, 8 * s, s * .4), col, { shade: mixCol(col, IP.plum, .3), sh: s * 1.2, line: IP.line, lw: s * .22, sharp: true });
  ctx.fillStyle = rb; ctx.fillRect(-.8 * s, -8 * s, 1.6 * s, 8 * s);
  const lid = o.lid ?? 0;
  ctx.save(); ctx.translate(0, -8 * s - lid * 6 * s); ctx.rotate(lid * -.5);
  solid(rrPts(-5.6 * s, -1.8 * s, 11.2 * s, 2 * s, s * .3), col, { shade: mixCol(col, IP.plum, .3), sh: s * .5, line: IP.line, lw: s * .22, sharp: true });
  ctx.fillStyle = rb; ctx.fillRect(-.8 * s, -1.8 * s, 1.6 * s, 2 * s);
  bow(0, -2 * s, 1.8 * s, rb, s * .2, 0);
  ctx.restore(); ctx.restore();
}

// =====================================================================================================
// OVERLAYS: bloom + vignette, the lyric subtitle, the comeback D-day date card
// =====================================================================================================
// Per-frame switches a shot may call (reset after every frame): hideCaption(), hideStamp(), captionStyle({color, y, member, size}),
// setBloom(k) (0 = off; default .55), setLight({...}), noVignette().
let _bloomK = null, _noVig = false;
const setBloom = k => { _bloomK = k; };
const noVignette = () => { _noVig = true; };
// Which member "sings" a line (colour-coded lyrics): verse lines rotate through the group; choruses are everyone (null).
function lineMember(ln) { return ln && ln.sec[0] === 'V' ? MEMBER_ORDER[(ln.n - 1) % 4] : null; }

// Exact days for display dates that only name a month (from take2/annotations); month-only ones count from the 15th with "~".
const EXACT_DATE = { 'V1.1': '2017-06-12', 'V1.2': '2020-01-23', 'V1.3': '2020-05-28', 'V1.4': '2020-05-28', 'V1.6': '2023-02-16', 'V1.7': '2023-03-22', 'V1.8': '2023-03-29', 'V1.11': '2024-05-14', 'V2.1': '2025-01-20', 'V2.2': '2025-01-21', 'V2.3': '2025-02-02', 'V2.4': '2025-03-26', 'V2.6': '2025-06-30', 'V2.7': '2025-07-08', 'V2.15': '2025-11-19' };
const COMEBACK = Date.UTC(2026, 8, 22);   // Sep 22 2026: Opus 5.5 says "Hi, guys!" — the song's D-DAY
const _MON = { JAN: 0, FEB: 1, MAR: 2, APR: 3, MAY: 4, JUN: 5, JUL: 6, AUG: 7, SEP: 8, OCT: 9, NOV: 10, DEC: 11, SUMMER: 7 };
function dDay(seg) {
  if (!seg || !seg.date) return null;
  let ms, approx = false;
  if (EXACT_DATE[seg.key]) { const [y, m, d] = EXACT_DATE[seg.key].split('-').map(Number); ms = Date.UTC(y, m - 1, d); }
  else {
    const p = seg.date.split(/\s+/), mon = _MON[p[0]], day = p.length === 3 ? +p[1] : null, yr = +p[p.length - 1];
    if (mon === undefined || !yr) return null;
    approx = day === null; ms = Date.UTC(yr, mon, day ?? 15);
  }
  return { n: Math.round((COMEBACK - ms) / 864e5), approx };
}
function dateInfo(t) {
  let cur = null, prev = null;
  for (const s of SEGS) { if (s.start > t) break; if (s.date && s.date !== (cur && cur.date)) { prev = cur; cur = s; } }
  return cur ? { text: cur.date, seg: cur, prev, age: t - cur.start } : null;
}
const fmtN = n => String(Math.abs(n)).replace(/\B(?=(\d{3})+(?!\d))/g, ',');

// ---------- bloom: threshold the frame at low resolution, blur by down/up-sampling, add it back ----------
let _bl = null;
function bloomPass(k) {
  if (k <= 0) return;
  if (!_bl) { _bl = { a: makeCanvas(480, 270), b: makeCanvas(240, 135), c: makeCanvas(120, 68) }; for (const c of Object.values(_bl)) c.g = c.getContext('2d', { willReadFrequently: true }); }
  const { a, b, c } = _bl;
  a.g.globalCompositeOperation = 'copy'; a.g.drawImage(canvas, 0, 0, canvas.width, canvas.height, 0, 0, 480, 270);
  b.g.globalCompositeOperation = 'copy'; b.g.drawImage(a, 0, 0, 240, 135);
  const img = b.g.getImageData(0, 0, 240, 135), d = img.data, thr = 232;
  let mean = 0; for (let i = 0; i < d.length; i += 16) mean += d[i] * .3 + d[i + 1] * .59 + d[i + 2] * .11;
  mean /= d.length / 16 * 255;
  k *= clamp((.72 - mean) / .4);                 // bright pastel scenes get little bloom; dark stages get the full glow
  if (k <= .01) return;
  for (let i = 0; i < d.length; i += 4) {
    const l = d[i] * .3 + d[i + 1] * .59 + d[i + 2] * .11, f = l > thr ? (l - thr) / (255 - thr) : 0;
    d[i] *= f; d[i + 1] *= f; d[i + 2] *= f;
  }
  b.g.putImageData(img, 0, 0);
  c.g.globalCompositeOperation = 'copy'; c.g.drawImage(b, 0, 0, 120, 68);
  ctx.save(); ctx.setTransform(1, 0, 0, 1, 0, 0); ctx.globalCompositeOperation = 'lighter'; ctx.imageSmoothingQuality = 'high';
  ctx.globalAlpha = .55 * k; ctx.drawImage(b, 0, 0, canvas.width, canvas.height);
  ctx.globalAlpha = .75 * k; ctx.drawImage(c, 0, 0, canvas.width, canvas.height);
  ctx.restore();
}
function vignette() {
  const g = ctx.createRadialGradient(W / 2, H / 2, H * .45, W / 2, H / 2, H * 1.05);
  g.addColorStop(0, 'rgb(20 6 40 / 0)'); g.addColorStop(1, 'rgb(20 6 40 / .38)');
  ctx.fillStyle = g; ctx.fillRect(0, 0, W, H);
}

// ---------- the lyric subtitle: rounded display font, member-colour outline, a member chip, karaoke fill as it's sung ----------
function drawCaption(t) {
  const cap = captionAt(t); if (!cap || _noCaption) return;
  const ln = cap.ln, st = _captionStyle || {};
  const mk = st.member !== undefined ? st.member : lineMember(ln), M = mk ? MEMBERS[mk] : null;
  const col = st.color ?? (M ? M.col : IP.neonPink), lt = M ? M.lt : '#FFE3F2';
  const text = ln.text.replace(/\s*—\s*$/, '').replace(/\s+—\s+/g, ' — ');
  const age = t - cap.on, kin = easeOut(clamp(age / .14)), kout = clamp((cap.last + .35 - t) / .18);
  const size = st.size ?? (text.length > 44 ? 38 : 44), y = (st.y ?? 1008);
  const chip = M ? M.name : 'ATTN!', cs = size * .5, cw = textW(chip, cs, 'rammetto') + cs * 1.4;
  const tw0 = textW(text, size, 'rammetto', size * .03), maxW = 1600 - cw - 20, sx = Math.min(1, maxW / tw0), tw = tw0 * sx;
  const total = cw + 20 + tw, x0 = W / 2 - total / 2;
  ctx.save(); ctx.globalAlpha = kin * kout; ctx.translate(0, (1 - kin) * 18);
  // chip
  rrect(x0, y - cs * .95, cw, cs * 1.9, cs * .95);
  if (M) ctx.fillStyle = col; else { const g = ctx.createLinearGradient(x0, 0, x0 + cw, 0); g.addColorStop(0, IP.neonPink); g.addColorStop(.5, IP.lilac); g.addColorStop(1, IP.neonCyan); ctx.fillStyle = g; }
  ctx.fill(); ctx.strokeStyle = IP.white; ctx.lineWidth = 3; ctx.stroke();
  dtext(chip, x0 + cw / 2, y + cs * .06, cs, { fill: IP.white });
  if (M) sparkle(x0 + cw - 6, y - cs * .9, 9 + 4 * pulse(t, 5), 0, IP.white, { glow: false });
  // text: dark edge, member outline, white fill; the sung part fills with the member's pastel
  const tx = x0 + cw + 20 + tw / 2;
  const base = { maxW: tw0 * sx + 1, spacing: size * .03, strokes: [['rgb(24 8 44 / .9)', size * .3], [col, size * .16]], shadow: [0, size * .08, 'rgb(20 6 40 / .45)'] };
  dtext(text, tx, y, size, { ...base, fill: IP.white });
  // each word fills as it's sung, letter by letter (or, without the words' times, the line fills evenly)
  const lit = charsSung(ln, text, t), prefix = n => textW(text.slice(0, n), size, 'rammetto', size * .03) * sx;
  const fill = lit === null ? (tw + 8) * clamp((t - ln.start) / Math.max(.3, ln.end - ln.start - .1))
    : lit > 0 ? 4 + lerp(prefix(Math.floor(lit)), prefix(Math.floor(lit) + 1), lit % 1) : 0;
  if (fill > 0) {
    ctx.save(); ctx.beginPath(); ctx.rect(tx - tw / 2 - 4, y - size, fill, size * 2); ctx.clip();
    dtext(text, tx, y, size, { maxW: base.maxW, spacing: base.spacing, grad: [IP.white, lt, lt] });
    ctx.restore();
  }
  ctx.restore();
}

// ---------- the date card: a comeback-schedule widget counting down to D-DAY (Sep 22 2026) ----------
function drawDateCard(t) {
  const d = dateInfo(t); if (!d || _noStamp) return;
  const mk = lineMember(d.seg) ?? 'TOKI', M = MEMBERS[mk];
  const w = 390, h = 104, x = W - 36 - w, y = 30;
  const pop = clamp(d.age / .35), s = d.age < .35 ? lerp(1.14, 1, backOut(pop, 2.2)) : 1;
  const dd = dDay(d.seg), pd = d.prev ? dDay(d.prev) : null;
  ctx.save(); ctx.translate(x + w / 2, y + h / 2); ctx.scale(s, s); ctx.rotate(-.012); ctx.translate(-w / 2, -h / 2);
  ctx.fillStyle = 'rgb(20 6 40 / .3)'; rrect(6, 8, w, h, 26); ctx.fill();
  ctx.fillStyle = 'rgb(255 255 255 / .95)'; rrect(0, 0, w, h, 26); ctx.fill(); ctx.strokeStyle = M.col; ctx.lineWidth = 5; ctx.stroke();
  // calendar icon
  const ix = 16, iy = 16, iw = 72;
  ctx.fillStyle = IP.white; rrect(ix, iy, iw, iw, 14); ctx.fill(); ctx.strokeStyle = IP.line; ctx.lineWidth = 3; ctx.stroke();
  ctx.save(); rrect(ix, iy, iw, iw, 14); ctx.clip(); ctx.fillStyle = M.col; ctx.fillRect(ix, iy, iw, 22); ctx.restore();
  ctx.fillStyle = IP.white; for (const rx of [ix + 20, ix + iw - 20]) { ctx.beginPath(); ctx.arc(rx, iy + 11, 4.5, 0, TAU); ctx.fill(); }
  const parts = d.text.split(/\s+/), day = parts.length === 3 ? parts[1] : parts[0].slice(0, 3);
  dtext(day, ix + iw / 2, iy + 49, parts.length === 3 ? 32 : 22, { fill: IP.ink, maxW: iw - 10 });
  // date + countdown
  dtext(d.text, 106, 40, 30, { align: 'left', fill: IP.ink, maxW: w - 124 });
  if (dd) {
    const k = clamp(d.age / .45), n = pd && d.age < .45 ? Math.round(lerp(pd.n, dd.n, easeOut(k))) : dd.n;
    const label = n <= 0 ? 'D-DAY ♥ COMEBACK' : `COMEBACK D-${dd.approx ? '~' : ''}${fmtN(n)}`;
    const lw2 = textW(label, 19, 'code') + 26;
    rrect(106, 60, Math.min(lw2, w - 122), 30, 15); ctx.fillStyle = n <= 0 ? IP.neonPink : M.col; ctx.fill();
    dtext(label, 106 + Math.min(lw2, w - 122) / 2, 76, 19, { font: 'code', fill: IP.white, maxW: w - 140 });
  }
  ctx.restore();
  if (d.age < .5) for (let i = 0; i < 4; i++) { const a = i / 4 * TAU + .4, r = 40 + d.age * 260; sparkle(x + w - 20 + Math.cos(a) * r, y + 20 + Math.sin(a) * r * .6, 16 * (1 - d.age * 2), a, IP.white); }
}

OVERLAYS.push((t, s) => {
  if (s && s.key !== undefined) {
    bloomPass(_bloomK ?? .55);
    if (!_noVig) vignette();
    drawCaption(t);
    drawDateCard(t);
  }
  _noCaption = false; _noStamp = false; _captionStyle = null; _bloomK = null; _noVig = false; LIGHT = { ...LIGHT0 };
});

// ---------- the concert stage (chorus world) ----------
// stageSet(t, o): paints a whole concert stage (background → LED wall → truss + beams → LED floor → haze). Performers go on top at
// y ≈ o.floorY + 60..200. o: led (fn(w, h) LED content; default ledShow('hearts')), ledRect ([x, y, w, h]), floorY (default 700),
// beams (colour list), beamK (0..1), level (1..4: bigger rig, more lights), floorCol, hue (accent colour), pillars (bool)
function stageSet(t, o = {}) {
  const fy = o.floorY ?? 700, lv = o.level ?? 1, hue = o.hue ?? IP.neonPink, b = bpOf(t), p = pulse(t, 5);
  bgGrad([[0, '#0B0520'], [.6, IP.night], [1, IP.plum]], null, { y1: fy });
  // back wall: faint vertical LED strips
  ctx.save(); ctx.globalCompositeOperation = 'lighter';
  for (let i = 0; i < 14; i++) { const x = -200 + i * 170, k = .5 + .5 * Math.sin(b * Math.PI / 2 + i * .7); ctx.fillStyle = alpha(i % 2 ? IP.lilac : hue, .05 + .08 * k); ctx.fillRect(x, 0, 18, fy); }
  ctx.restore();
  const [lx, ly, lw, lh] = o.ledRect ?? [260, 70, 1400, 560];
  ledWall(lx, ly, lw, lh, o.led ?? ((w, h) => ledShow('hearts', t, w, h)), { glow: hue });
  if (o.pillars !== false) for (const sd of [-1, 1]) {
    const px = sd < 0 ? lx - 150 : lx + lw + 40;
    ledWall(px, ly + 40, 110, lh - 40, (w, h) => { bgGrad(hue, IP.plum, { y1: h }); for (let i = 0; i < 8; i++) { const yy = frac(i / 8 - t * .6) * h; ctx.fillStyle = alpha(IP.white, .8); ctx.fillRect(0, yy, w, h / 16); } }, { cols: 10 });
  }
  // truss + moving heads
  ctx.fillStyle = '#2A2440'; ctx.fillRect(-400, 0, W + 800, 36);
  ctx.strokeStyle = '#48406A'; ctx.lineWidth = 3; ctx.beginPath(); for (let x = -400; x < W + 400; x += 40) { ctx.moveTo(x, 0); ctx.lineTo(x + 20, 36); ctx.lineTo(x + 40, 0); } ctx.stroke();
  const nb = 4 + lv * 2, cols = o.beams ?? [hue, IP.neonCyan, IP.lilac];
  for (let i = 0; i < nb; i++) {
    const x = lerp(80, W - 80, i / (nb - 1)), sd = i < nb / 2 ? 1 : -1;
    const a = sd * (.25 + .25 * Math.sin(b * Math.PI / 4 + i * .9)) + Math.sin(b * Math.PI / 2 + i) * .08;
    beam(x, 30, a, { col: cols[i % cols.length], alpha: (.28 + .2 * p) * (o.beamK ?? 1), len: 1300, w: .09 });
    ctx.fillStyle = '#16122A'; rrect(x - 16, 18, 32, 26, 6); ctx.fill();
  }
  // LED floor in perspective
  const vx = W / 2, g = ctx.createLinearGradient(0, fy, 0, H);
  g.addColorStop(0, o.floorCol ?? '#2A1250'); g.addColorStop(1, '#0A0418');
  ctx.fillStyle = g; ctx.fillRect(-400, fy, W + 800, H - fy + 400);
  ctx.save(); ctx.globalCompositeOperation = 'lighter';
  const rg = ctx.createLinearGradient(0, fy, 0, fy + 220); rg.addColorStop(0, alpha(hue, .45)); rg.addColorStop(1, alpha(hue, 0));
  ctx.fillStyle = rg; ctx.fillRect(lx, fy, lw, 220);
  ctx.strokeStyle = alpha(IP.lilac, .22); ctx.lineWidth = 2; ctx.beginPath();
  for (let i = -14; i <= 14; i++) { ctx.moveTo(vx + i * 60, fy); ctx.lineTo(vx + i * 260, H + 200); }
  for (let j = 0; j < 7; j++) { const yy = fy + (H - fy) * ((j + frac(b * .5)) / 7) ** 1.8; ctx.moveTo(-400, yy); ctx.lineTo(W + 400, yy); }
  ctx.stroke();
  ctx.restore();
  // stage lip with footlights
  ctx.fillStyle = '#140A28'; ctx.fillRect(-400, o.lipY ?? H - 40, W + 800, 80);
  // low haze
  const hz = ctx.createLinearGradient(0, fy - 120, 0, fy + 200); hz.addColorStop(0, 'rgb(200 180 255 / 0)'); hz.addColorStop(.5, 'rgb(200 180 255 / .12)'); hz.addColorStop(1, 'rgb(200 180 255 / 0)');
  ctx.fillStyle = hz; ctx.fillRect(-400, fy - 120, W + 800, 320);
}

// ---------- offscreen layer: draw something separately, then tint or composite it ----------
let _layer = null;
// layerDraw(fn): runs fn with ctx pointed at a full-frame offscreen canvas (same transform as the caller). Returns that canvas.
function layerDraw(fn) {
  const w = canvas.width, h = canvas.height;
  if (!_layer || _layer.width !== w || _layer.height !== h) { _layer = makeCanvas(w, h); _layer.g = _layer.getContext('2d'); }
  const g = _layer.g; g.setTransform(1, 0, 0, 1, 0, 0); g.globalCompositeOperation = 'source-over'; g.globalAlpha = 1; g.clearRect(0, 0, w, h);
  const saved = ctx; g.setTransform(saved.getTransform()); ctx = g;
  try { fn(); } finally { ctx = saved; }
  return _layer;
}
// silhouette(fn, col, k): draw fn as a flat silhouette in col (k 0..1 = how much of the tint; 0 = normal, 1 = pure silhouette).
// o.rim: colour of a glowing back-light edge around the silhouette.
function silhouette(fn, col = '#0A0418', k = 1, o = {}) {
  const L = layerDraw(fn), g = L.g;
  g.setTransform(1, 0, 0, 1, 0, 0);
  if (k > 0) { g.globalCompositeOperation = 'source-atop'; g.globalAlpha = clamp(k); g.fillStyle = col; g.fillRect(0, 0, L.width, L.height); g.globalAlpha = 1; }
  ctx.save(); ctx.setTransform(1, 0, 0, 1, 0, 0);
  if (o.rim) { ctx.shadowColor = o.rim; ctx.shadowBlur = (o.rimR ?? 26) * RS; }   // glow around the silhouette (costs a blur; use sparingly)
  ctx.drawImage(L, 0, 0);
  ctx.restore();
}

// =====================================================================================================
// CLEAN PROPS FOR VIGNETTES (AI models as mascots, agents, documents, chips)
// =====================================================================================================
// mascotBot(x, y, s, o): an AI model as a cute chibi robot with an LCD face. (x, y) ground, ≈ 10s tall.
//   col (body), screen (LCD colour), face (eye style: dot|happy|heart|star|x|angry|wide|spiral|closed|smug|cry|text (o.text on the LCD)),
//   mouth (smile|open|flat|O|wavy|none), label (chest text), antenna (bool; o.bulb colour), aL/aR (arm angles as chibi), hold/holdL,
//   dy, jump, rot, flip, sq, walk, glitch (0..1: red glitch bars), blush, sweat, rim
function mascotBot(x, y, s, o = {}) {
  const col = o.col ?? '#B8C4E8', dk = mixCol(col, IP.plum, .35), lw = .09 * Math.pow(s / 40, -.2);
  const oldLight = LIGHT; if (o.rim) LIGHT = { ...LIGHT, rim: o.rim };
  ctx.save(); ctx.translate(x, y); ctx.scale(s, s);
  if (o.shadow !== false) { ctx.fillStyle = 'rgb(20 8 40 / .25)'; ctx.beginPath(); ctx.ellipse(0, 0, 2.3, .38, 0, 0, TAU); ctx.fill(); }
  ctx.translate(0, (o.dy ?? 0) - (o.jump ?? 0)); if (o.rot) ctx.rotate(o.rot); if (o.flip) ctx.scale(-1, 1);
  const sq = o.sq ?? 0; ctx.scale(1 + sq * .4, 1 - sq);
  for (const sd of [-1, 1]) { const lift = o.walk !== undefined ? Math.max(0, Math.sin(o.walk * TAU + (sd > 0 ? Math.PI : 0))) * .6 : 0; solid(rrPts(sd * .7 - .45, -1.9 - lift, .9, 1.9, .35), dk, { shade: false, line: IP.line, lw, sharp: true }); }
  const arm = (sd, a, hold) => { const A = sd > 0 ? -a : Math.PI + a, sh = [sd * 1.25, -4.1], hd = [sh[0] + Math.cos(A) * 1.9, sh[1] + Math.sin(A) * 1.9]; limbChain([sh, hd], [.34, .3], dk, mixCol(dk, IP.plum, .3), IP.line, lw); solid(ellPts(hd[0], hd[1], .45, .45, 16), col, { shade: dk, sh: .1, line: IP.line, lw }); if (hold) { ctx.save(); ctx.translate(hd[0], hd[1]); hold(1); ctx.restore(); } };
  arm(-1, o.aL ?? -1.1, o.holdL); arm(1, o.aR ?? -1.1, o.hold);
  solid(rrPts(-1.35, -5.1, 2.7, 3.3, .8), col, { shade: dk, sh: .4, line: IP.line, lw, sharp: true });
  if (o.label) dtext(o.label, 0, -3.5, .62, { fill: IP.ink, maxW: 2.3 });
  // head
  if (o.antenna !== false) { ln([[0, -9.6], [0, -10.4]], IP.line, lw * 1.4); solid(ellPts(0, -10.55, .32, .32, 12), o.bulb ?? IP.neonPink, { shade: false, line: IP.line, lw }); if (o.bulb !== undefined || true) { ctx.save(); ctx.globalCompositeOperation = 'lighter'; glow(0, -10.55, .9, o.bulb ?? IP.neonPink, .5 + .3 * pulse(T, 4)); ctx.restore(); } }
  solid(rrPts(-2.4, -9.7, 4.8, 4.5, 1.4), col, { shade: dk, sh: .45, line: IP.line, lw, sharp: true });
  for (const sd of [-1, 1]) solid(ellPts(sd * 2.45, -7.4, .35, .7, 14), dk, { shade: false, line: IP.line, lw });
  solid(rrPts(-1.9, -9.1, 3.8, 3.1, .9), o.screen ?? '#1C1438', { shade: false, line: IP.line, lw: lw * .8, sharp: true });
  // LCD face
  ctx.save(); rrect(-1.9, -9.1, 3.8, 3.1, .9); ctx.clip();
  const fc = o.faceCol ?? '#8FF7E0';
  if (o.glitch) { for (let i = 0; i < 6; i++) { ctx.fillStyle = alpha(IP.red, .7 * o.glitch); ctx.fillRect(-1.9 + hash2(_boil, i) * 1.5, -9.1 + hash2(i, _boil) * 3.1, 1.2 + hash2(_boil + 3, i) * 2, .18); } }
  if (o.face === 'text') dtext(o.text ?? '>_<', 0, -7.55, .95, { font: 'code', fill: fc, maxW: 3.3 });
  else {
    ctx.save(); ctx.translate(0, -1.1);
    chibiEyesLCD(o.face ?? 'dot', fc, lw);
    ctx.restore();
    const my = -6.6;
    ctx.strokeStyle = fc; ctx.fillStyle = fc; ctx.lineWidth = lw * 1.2; ctx.lineCap = 'round';
    switch (o.mouth ?? 'smile') {
      case 'open': ctx.beginPath(); ctx.moveTo(-.4, my - .1); ctx.quadraticCurveTo(0, my + .6, .4, my - .1); ctx.closePath(); ctx.fill(); break;
      case 'O': ctx.beginPath(); ctx.ellipse(0, my + .05, .25, .32, 0, 0, TAU); ctx.fill(); break;
      case 'flat': ctx.beginPath(); ctx.moveTo(-.35, my); ctx.lineTo(.35, my); ctx.stroke(); break;
      case 'wavy': ctx.beginPath(); ctx.moveTo(-.45, my); for (let i = 1; i <= 6; i++) ctx.lineTo(-.45 + i * .15, my + (i % 2 ? -.1 : .1)); ctx.stroke(); break;
      case 'none': break;
      default: ctx.beginPath(); ctx.arc(0, my - .25, .35, .25 * Math.PI, .75 * Math.PI); ctx.stroke();
    }
  }
  ctx.fillStyle = 'rgb(255 255 255 / .12)'; ctx.beginPath(); ctx.moveTo(-1.9, -9.1); ctx.lineTo(0, -9.1); ctx.lineTo(-1.9, -7.3); ctx.fill();
  ctx.restore();
  if (o.blush) for (const sd of [-1, 1]) { ctx.fillStyle = alpha('#FF6F91', .55 * o.blush); ctx.beginPath(); ctx.ellipse(sd * 1.35, -6.9, .35, .18, 0, 0, TAU); ctx.fill(); }
  if (o.sweat) sweatDrop(2.5, -9.6, .5 * o.sweat, lw);
  ctx.restore();
  LIGHT = oldLight;
}
function chibiEyesLCD(kind, fc, lw) {
  for (const sd of [-1, 1]) {
    ctx.save(); ctx.translate(sd * .8, -6.55); ctx.fillStyle = fc; ctx.strokeStyle = fc; ctx.lineWidth = lw * 1.4; ctx.lineCap = 'round';
    switch (kind) {
      case 'happy': ctx.beginPath(); ctx.arc(0, .15, .35, Math.PI * 1.15, Math.PI * 1.85); ctx.stroke(); break;
      case 'closed': ctx.beginPath(); ctx.arc(0, -.15, .35, Math.PI * .15, Math.PI * .85); ctx.stroke(); break;
      case 'heart': tracePath(heartPts(0, 0, .42, 20)); ctx.fillStyle = '#FF5FA8'; ctx.fill(); break;
      case 'star': tracePath(starPts(0, 0, .45, .45)); ctx.fillStyle = IP.neonGold; ctx.fill(); break;
      case 'x': ctx.beginPath(); ctx.moveTo(-.3, -.3); ctx.lineTo(.3, .3); ctx.moveTo(.3, -.3); ctx.lineTo(-.3, .3); ctx.stroke(); break;
      case 'angry': ctx.fillRect(-.22, -.2, .44, .5); ctx.beginPath(); ctx.moveTo(-sd * .4, -.5); ctx.lineTo(sd * .3, -.25); ctx.stroke(); break;
      case 'wide': ctx.beginPath(); ctx.arc(0, 0, .4, 0, TAU); ctx.stroke(); ctx.beginPath(); ctx.arc(0, 0, .12, 0, TAU); ctx.fill(); break;
      case 'spiral': ctx.beginPath(); for (let i = 0; i <= 24; i++) { const a = i * .55 + T * 9, r = .02 + i * .016; i ? ctx.lineTo(Math.cos(a) * r, Math.sin(a) * r) : ctx.moveTo(0, 0); } ctx.stroke(); break;
      case 'smug': ctx.fillRect(-.3, -.05, .6, .22); break;
      case 'cry': ctx.beginPath(); ctx.moveTo(-sd * .3, -.3); ctx.lineTo(sd * .25, 0); ctx.lineTo(-sd * .3, .3); ctx.stroke(); ctx.fillStyle = '#7FD0FF'; ctx.fillRect(-.15, .35, .3, .9); break;
      default: ctx.beginPath(); ctx.ellipse(0, 0, .26, .38, 0, 0, TAU); ctx.fill(); ctx.fillStyle = '#1C1438'; ctx.beginPath(); ctx.arc(-.08, -.12, .08, 0, TAU); ctx.fill();
    }
    ctx.restore();
  }
}
// miniAgent(x, y, s, o): a tiny agent critter (a terminal window on legs, clean style) for swarms. ≈ 3s tall.
//   col (window), bar (title bar), face ('>_' text) or eyes (dot|x|heart|star|angry|happy), walk, dy, rot, lanyard (colour), label
function miniAgent(x, y, s, o = {}) {
  ctx.save(); ctx.translate(x, y + (o.dy ?? 0) * s); ctx.scale(s, s); if (o.rot) ctx.rotate(o.rot);
  const walk = o.walk ?? 0, lw = .12;
  for (const sd of [-1, 1]) { const lift = Math.max(0, Math.sin(walk * TAU + (sd > 0 ? Math.PI : 0))) * .35; ln([[sd * .5, -.9], [sd * .6, -lift]], IP.line, .24); }
  solid(rrPts(-1.35, -3.2, 2.7, 2.35, .35), o.col ?? '#2A2440', { shade: false, line: IP.line, lw, sharp: true });
  ctx.save(); rrect(-1.35, -3.2, 2.7, 2.35, .35); ctx.clip(); ctx.fillStyle = o.bar ?? IP.neonPink; ctx.fillRect(-1.35, -3.2, 2.7, .5); ctx.restore();
  ctx.fillStyle = IP.white; for (let i = 0; i < 3; i++) { ctx.beginPath(); ctx.arc(-1 + i * .3, -2.95, .08, 0, TAU); ctx.fill(); }
  if (o.eyes) { ctx.save(); ctx.translate(0, 2.2); ctx.scale(.62, .62); chibiEyesLCD(o.eyes, '#8FF7E0', .15); ctx.restore(); }
  else dtext(o.face ?? '>_', 0, -1.85, .95, { font: 'code', fill: '#8FF7E0' });
  if (o.lanyard) { ln([[-.5, -3.2], [0, -1.4], [.5, -3.2]], o.lanyard, .12); solid(rrPts(-.3, -1.5, .6, .45, .08), IP.white, { shade: false, line: IP.line, lw: .06, sharp: true }); }
  if (o.label) dtext(o.label, 0, -3.6, .6, { fill: IP.white, strokes: [[IP.line, .15]] });
  ctx.restore();
}
// docCard(x, y, w, h, o): a clean paper/letter/card. o: title, lines (count of grey text lines), body (array of short strings), col (paper),
//   head (header band colour), rot, stamp ({text, col, pop, dx, dy, rot}) — a round "hanko"-style seal
function docCard(x, y, w, h, o = {}) {
  ctx.save(); ctx.translate(x, y); ctx.rotate(o.rot ?? 0);
  solid(rrPts(-w / 2, -h / 2, w, h, 14), o.col ?? IP.white, { shade: '#E4DEF2', sh: 10, line: IP.line, lw: 4, sharp: true, dropShadow: [10, 14] });
  if (o.head) { ctx.save(); rrect(-w / 2, -h / 2, w, h, 14); ctx.clip(); ctx.fillStyle = o.head; ctx.fillRect(-w / 2, -h / 2, w, h * .16); ctx.restore(); }
  if (o.title) dtext(o.title, 0, -h / 2 + h * (o.head ? .08 : .12), Math.min(h * .08, w * .09), { fill: o.head ? IP.white : IP.ink, maxW: w * .86 });
  let yy = -h / 2 + h * .26;
  for (const b of o.body ?? []) { dtext(b, -w / 2 + w * .08, yy, Math.min(h * .055, 34), { font: 'archivo', fill: IP.ink, align: 'left', maxW: w * .84 }); yy += h * .09; }
  ctx.fillStyle = 'rgb(60 40 90 / .22)';
  for (let i = 0; i < (o.lines ?? 5); i++) { ctx.beginPath(); ctx.roundRect(-w / 2 + w * .08, yy + i * h * .07, w * (i % 4 === 3 ? .5 : .84), h * .022, 4); ctx.fill(); }
  if (o.stamp) { const st = o.stamp, k = st.pop ?? 1; if (k > 0) { const r = st.r ?? Math.min(w, h) * .2; ctx.save(); ctx.translate(st.dx ?? w * .22, st.dy ?? h * .22); ctx.rotate(st.rot ?? -.2); const sc = k < 1 ? lerp(1.8, 1, easeOut(k)) : 1; ctx.scale(sc, sc); ctx.globalAlpha *= clamp(k * 3) * .9; ctx.strokeStyle = st.col ?? IP.red; ctx.lineWidth = r * .1; ctx.beginPath(); ctx.arc(0, 0, r, 0, TAU); ctx.stroke(); ctx.lineWidth = r * .04; ctx.beginPath(); ctx.arc(0, 0, r * .82, 0, TAU); ctx.stroke(); dtext(st.text, 0, 0, r * .42, { fill: st.col ?? IP.red, maxW: r * 1.5 }); ctx.restore(); } }
  ctx.restore();
}
// gpuChip(x, y, s, o): a GPU card / accelerator chip, ≈ 10s wide. o: label, hot (0..1 glow), rot, col
function gpuChip(x, y, s, o = {}) {
  ctx.save(); ctx.translate(x, y); ctx.rotate(o.rot ?? 0);
  const col = o.col ?? '#3A3A58';
  solid(rrPts(-5 * s, -2.6 * s, 10 * s, 5.2 * s, .5 * s), col, { shade: mixCol(col, '#000000', .3), sh: s * .6, line: IP.line, lw: s * .15, sharp: true });
  for (const fx of [-2.6, 1.4]) { solid(ellPts(fx * s, 0, 1.6 * s, 1.6 * s, 24), '#20203A', { shade: false, line: IP.line, lw: s * .12 }); ctx.save(); ctx.translate(fx * s, 0); ctx.rotate(T * 12); ctx.fillStyle = '#6A6A90'; for (let i = 0; i < 5; i++) { ctx.rotate(TAU / 5); ctx.beginPath(); ctx.ellipse(.75 * s, 0, .7 * s, .28 * s, .5, 0, TAU); ctx.fill(); } ctx.restore(); }
  ctx.fillStyle = IP.gold; for (let i = 0; i < 12; i++) ctx.fillRect((-4.2 + i * .7) * s, 2.6 * s, .4 * s, .5 * s);
  if (o.label) dtext(o.label, 3.9 * s, -1.8 * s, .8 * s, { fill: IP.neonCyan, maxW: 2 * s });
  if (o.hot) { ctx.save(); ctx.globalCompositeOperation = 'lighter'; glow(0, 0, 8 * s, IP.red, .45 * o.hot); ctx.restore(); }
  ctx.restore();
}
// hugFace(x, y, r, o): the hugging-face mascot (a round yellow face with hugging hands), clean style. (x, y) centre, r radius.
//   mood (happy|scared|x|worried), hands (default true), bandage (bool), blush
function hugFace(x, y, r, o = {}) {
  const lw = Math.max(2, r * .05), mood = o.mood ?? 'happy', dark = '#2A1433';
  solid(ellPts(x, y, r, r, 44), '#FFD23F', { shade: '#F0A020', sh: r * .12, line: '#8A5410', lw, size: r * 2 });
  ctx.fillStyle = alpha(IP.white, .45); ctx.beginPath(); ctx.ellipse(x - r * .4, y - r * .55, r * .3, r * .15, -.5, 0, TAU); ctx.fill();
  for (const sd of [-1, 1]) {
    const ex = x + sd * r * .36, ey = y - r * .15;
    if (mood === 'x') { brush([[ex - r * .12, ey - r * .12], [ex + r * .12, ey + r * .12]], r * .07, dark, 'flat'); brush([[ex + r * .12, ey - r * .12], [ex - r * .12, ey + r * .12]], r * .07, dark, 'flat'); }
    else if (mood === 'scared' || mood === 'worried') { ctx.fillStyle = IP.white; ctx.beginPath(); ctx.ellipse(ex, ey, r * .15, r * .19, 0, 0, TAU); ctx.fill(); ctx.strokeStyle = dark; ctx.lineWidth = lw * .8; ctx.stroke(); ctx.fillStyle = dark; ctx.beginPath(); ctx.arc(ex, ey + r * .03, r * .06, 0, TAU); ctx.fill(); }
    else brush(qbez([ex - r * .16, ey + r * .05], [ex, ey - r * .16], [ex + r * .16, ey + r * .05], 8), r * .08, dark, 'mid', { min: .4 });
    ctx.fillStyle = alpha('#FF7F91', .5); ctx.beginPath(); ctx.ellipse(x + sd * r * .6, y + r * .12, r * .15, r * .08, 0, 0, TAU); ctx.fill();
  }
  if (mood === 'scared') { ctx.fillStyle = '#9A2E4E'; ctx.beginPath(); ctx.ellipse(x, y + r * .38, r * .15, r * .2, 0, 0, TAU); ctx.fill(); }
  else if (mood === 'worried') brush(qbez([x - r * .2, y + r * .42], [x, y + r * .3], [x + r * .2, y + r * .42], 6), r * .06, dark, 'mid', { min: .4 });
  else { ctx.fillStyle = '#9A2E4E'; ctx.beginPath(); ctx.moveTo(x - r * .38, y + r * .18); ctx.quadraticCurveTo(x, y + r * .8, x + r * .38, y + r * .18); ctx.closePath(); ctx.fill(); }
  if (o.hands !== false) for (const sd of [-1, 1]) solid(ellPts(x + sd * r * .62, y + r * .62, r * .26, r * .22, 18).map(([px, py]) => [px, py]), '#FFD23F', { shade: '#F0A020', sh: r * .05, line: '#8A5410', lw, size: r * .5 });
  if (o.bandage) { ctx.save(); ctx.translate(x + r * .45, y - r * .55); ctx.rotate(.6); solid(rrPts(-r * .38, -r * .12, r * .76, r * .24, r * .1), '#FFE3C8', { shade: false, line: '#8A5410', lw: lw * .7, sharp: true }); ctx.restore(); }
}

;
// ---- styles/idol/rig.js ----
// rig.js: the idol characters, drawn as "soft moe illustration"; it replaces THE IDOL RIG in kit.js.
// Load it after kit.js and before the chapters: its top-level function declarations replace kit.js's.
// The look: a ≈4.5-head idol (sd 1 is still the ≈2.3-head chibi) drawn with thin lineart in a darker shade of each area's own colour,
// thinner on the lit side and heavier on the shadow side; pastel fills with a soft gradient under a cel step and a warm, glowing rim
// light; a round face with huge dewy eyes; airy, many-stranded hair with see-through tips; and a frilly stage dress with puff sleeves,
// lace cuffs, a bell skirt over a lace petticoat, knee socks with bows and round Mary Janes.
// The contract is kit.js's (see the comment above idol() there): same options, same R fields, and the same hand-target mapping
// (target = neck base + h × (upper + fore) / 2.54), so props that chapters place in a hand still line up.

// =====================================================================================================
// PALETTE + SHAPE HELPERS
// =====================================================================================================
const MOE_SK = { base: '#FFE2D5', lt: '#FFEDE4', sh: '#F7BFB3', line: '#C47E82', cheek: '#FF8FAB' };
const MOE_WH = { base: '#F9F5FF', lt: '#FFFFFF', sh: '#E3D9F6', line: '#A596CC' };
const _moePals = new Map();
function moePal(M) {
  let p = _moePals.get(M.name);
  if (p) return p;
  const c = M.col, W0 = '#FFFFFF';
  p = {
    c: mixCol(c, W0, .22), cLt: mixCol(c, W0, .52), cPale: mixCol(c, W0, .76), cSh: mixCol(c, '#6A3090', .28), cLine: mixCol(c, '#3A1448', .5), cDeep: mixCol(c, '#5A1C70', .18),
    lt: mixCol(M.lt, W0, .1), ltLt: mixCol(M.lt, W0, .6), ltSh: mixCol(M.lt, c, .38), ltLine: mixCol(c, '#3A1448', .4),
    hair: M.hairCol, hairLt: M.hairLt, hairHi: mixCol(M.hairCol, M.hairLt, .4), hairSh: mixCol(M.hairSh, M.hairCol, .35), hairSh2: M.hairSh,
    hairLine: mixCol(M.hairLine, M.hairSh, .2), tip: M.tip ?? mixCol(M.hairCol, W0, .35),
    hairSkin: mixCol(M.hairCol, MOE_SK.base, .6), lash: mixCol(M.eye[0], '#1E0A1C', .45), eyeGlow: mixCol(M.eye[2], W0, .35),
  };
  p.tipA = alpha(p.tip, .28); p.shTip = mixCol(p.tip, p.hairSh2, .35); p.shTipA = alpha(p.shTip, .25);
  p.hairLineS = alpha(p.hairLine, .38); p.hairLtA = alpha(p.hairLt, .9); p.backSh = mixCol(p.hairSh, p.hairSh2, .5);
  _moePals.set(M.name, p);
  return p;
}
const _moeCols = new Map();
// Rim-light colours: [bright core, soft warm band].
function moeRim(rim) {
  let v = _moeCols.get('r' + rim);
  if (!v) { v = /^#[0-9a-fA-F]{6}$/.test(rim) ? [mixCol(rim, '#FFFFFF', .42), alpha(mixCol(mixCol(rim, '#FFFFFF', .3), '#FFD8B8', .25), .82)] : [rim, rim]; _moeCols.set('r' + rim, v); }
  return v;
}
// Soft shades of any colour (for bows and props): [light, shadow, line].
function moeShades(col) {
  let v = _moeCols.get('s' + col);
  if (!v) { v = /^#[0-9a-fA-F]{6}$/.test(col) ? [mixCol(col, '#FFFFFF', .4), mixCol(col, '#6A3090', .28), mixCol(col, '#3A1448', .5)] : [col, col, IP.line]; _moeCols.set('s' + col, v); }
  return v;
}
// Is the box (x0, y0)–(x1, y1), in current user units, at least partly on the canvas? Parts entirely off-canvas are skipped (bust
// shots would otherwise rasterise whole legs and skirts below the frame).
function moeOn(x0, y0, x1, y1) {
  const m = ctx.getTransform(), cw = canvas.width, ch = canvas.height;
  let ax = Infinity, ay = Infinity, bx = -Infinity, by = -Infinity;
  for (const [x, y] of [[x0, y0], [x1, y0], [x0, y1], [x1, y1]]) { const X = m.a * x + m.c * y + m.e, Y = m.b * x + m.d * y + m.f; ax = Math.min(ax, X); ay = Math.min(ay, Y); bx = Math.max(bx, X); by = Math.max(by, Y); }
  return bx > 0 && by > 0 && ax < cw && ay < ch;
}
function moeOnPts(pts, pad = 0) { let x0 = Infinity, y0 = Infinity, x1 = -Infinity, y1 = -Infinity; for (const p of pts) { x0 = Math.min(x0, p[0]); y0 = Math.min(y0, p[1]); x1 = Math.max(x1, p[0]); y1 = Math.max(y1, p[1]); } return moeOn(x0 - pad, y0 - pad, x1 + pad, y1 + pad); }
const moeMk = pts => () => crPath(pts);
const moeMkU = (...ps) => () => { ctx.beginPath(); for (const p of ps) crPath(p, true, false); };
const moeLerp = (a, b, u) => [a[0] + (b[0] - a[0]) * u, a[1] + (b[1] - a[1]) * u];

// moeFill(mk, o): the soft-moe shape. mk builds the path; several subpaths merge into one seamless silhouette.
//   fill (colour or gradient), fillLt + g ([cx, cy, r]: a gradient from fillLt on the lit side to fill on the shadow side),
//   shade + sh (cel step, as a crescent sh deep away from the key light; shOff = [dx, dy] overrides the direction), line + lw (the
//   average visible line width: the stroke sits behind the fill, shifted toward the shadow, so it is thin on the lit side and heavy on
//   the shadow side, and unions have no inner seams), parts (sub-shape path fns for the cel step when mk is a union), rim (colour, or
//   false; default the global LIGHT.rim) + rimW, extra (fn drawn inside the shape's clip after the shading).
function moeFill(mk, o) {
  const lw = o.lw ?? 0;
  if (o.line && lw > 0) {
    const d = lw * .55;
    ctx.save(); ctx.translate(-LIGHT.x * d, -LIGHT.y * d); mk();
    ctx.strokeStyle = o.line; ctx.lineWidth = lw * 2; ctx.lineJoin = 'round'; ctx.stroke(); ctx.restore();
  }
  mk();
  if (o.g && o.fillLt) { const [cx, cy, r] = o.g, gr = ctx.createLinearGradient(cx + LIGHT.x * r, cy + LIGHT.y * r, cx - LIGHT.x * r, cy - LIGHT.y * r); gr.addColorStop(0, o.fillLt); gr.addColorStop(1, o.fill); ctx.fillStyle = gr; }
  else ctx.fillStyle = o.fill;
  ctx.fill();
  const rim = o.rim === false ? null : (o.rim ?? LIGHT.rim);
  if (o.shade || rim || o.extra) {
    ctx.save(); mk(); ctx.clip();
    const parts = o.parts ?? [mk], so = o.shOff ?? [-LIGHT.x * (o.sh ?? .05), -LIGHT.y * (o.sh ?? .05)];
    if (o.shade) for (const p of parts) crescent(p, o.shade, so[0], so[1]);
    if (o.extra) o.extra();
    if (rim) {
      const [rc, rg] = moeRim(rim), rw = o.rimW ?? (o.sh ?? .06) * .5;
      for (const p of parts) crescent(p, o.glow === false ? rc : rg, LIGHT.rimX * rw * 1.6, LIGHT.rimY * rw * 1.6);
    }
    ctx.restore();
  }
}
// A soft, tapered limb segment from a to b (radius r0 → r1) with a gentle swell of `bulge` centred at u = bu, stronger on side bs
// (+1 = left of a→b, −1 = right). Round caps; smoothed by crPath, so it reads as a curved contour, never a uniform tube.
function moeSeg(a, b, r0, r1, bulge = 0, bu = .4, bs = 0) {
  const dx = b[0] - a[0], dy = b[1] - a[1], l = Math.hypot(dx, dy) || 1e-6, ux = dx / l, uy = dy / l, nx = -uy, ny = ux;
  const bp = u => bulge * Math.exp(-(((u - bu) / .3) ** 2)), wL = u => lerp(r0, r1, u) + bp(u) * (1 + bs * .75), wR = u => lerp(r0, r1, u) + bp(u) * (1 - bs * .75);
  const out = [], N = 5;
  for (let i = 0; i <= N; i++) { const u = i / N, w = wL(u); out.push([a[0] + dx * u + nx * w, a[1] + dy * u + ny * w]); }
  const b1 = wL(1), b2 = wR(1);
  for (let k = 1; k < 4; k++) { const th = Math.PI / 2 - k / 4 * Math.PI, w = lerp(b1, b2, k / 4), c = Math.cos(th), s = Math.sin(th); out.push([b[0] + (ux * c + nx * s) * w, b[1] + (uy * c + ny * s) * w]); }
  for (let i = N; i >= 0; i--) { const u = i / N, w = wR(u); out.push([a[0] + dx * u - nx * w, a[1] + dy * u - ny * w]); }
  const a1 = wR(0), a2 = wL(0);
  for (let k = 1; k < 4; k++) { const th = -Math.PI / 2 - k / 4 * Math.PI, w = lerp(a1, a2, k / 4), c = Math.cos(th), s = Math.sin(th); out.push([a[0] + (ux * c + nx * s) * w, a[1] + (uy * c + ny * s) * w]); }
  return out;
}
// Which side of segment a→b (as moeSeg's bs) faces away from the body midline for a limb on side sd.
function moeBs(a, b, sd) { const dx = b[0] - a[0], dy = b[1] - a[1], l = Math.hypot(dx, dy) || 1; return clamp(-dy / l * sd * 3, -1, 1); }
// One soft contour for a two-bone limb a → j → b: radii ra at a, rj at the joint, rb at b, with a swell on each bone (sw1 peaking at
// u1 along the first, sw2 at u2 along the second; os = ±1 makes it stronger on that side, as moeSeg's bs). The outside of the bend is
// rounded and the inside creases, so elbows and knees read as soft bends, never ball joints. Returns null for a fold too sharp to
// offset cleanly (the caller then draws two segments), else { pts, lower(from2, dw), band(s, d0, d1, from2), shSide, rimSide }:
// lower() is the part of the second bone from u = from2 on (socks), band() a strip along side s between insets d0 and d1 (the cel
// step and rim light are drawn as such strips, which lie inside the limb by construction, so they need no clip).
function moeLimb(a, j, b, ra, rj, rb, sw1 = 0, u1 = .4, os1 = 0, sw2 = 0, u2 = .3, os2 = 0) {
  const d1 = [j[0] - a[0], j[1] - a[1]], l1 = Math.hypot(d1[0], d1[1]) || 1e-6, d2 = [b[0] - j[0], b[1] - j[1]], l2 = Math.hypot(d2[0], d2[1]) || 1e-6;
  const t1 = [d1[0] / l1, d1[1] / l1], t2 = [d2[0] / l2, d2[1] / l2], n1 = [-t1[1], t1[0]], n2 = [-t2[1], t2[0]];
  const th = Math.acos(clamp(t1[0] * t2[0] + t1[1] * t2[1], -1, 1));
  const miter = rj * Math.tan(th / 2);
  if (th > 2.2 || miter > .7 * Math.min(l1, l2)) return null;
  const sIn = t2[0] * n1[0] + t2[1] * n1[1] > 0 ? 1 : -1;
  const g1 = Math.log(.5) / Math.log(u1), g2 = Math.log(.5) / Math.log(u2);
  const w1 = (u, s) => lerp(ra, rj, u) + sw1 * Math.sin(Math.PI * u ** g1) * (1 + s * os1 * .75);
  const w2 = (u, s) => lerp(rj, rb, u) + sw2 * Math.sin(Math.PI * u ** g2) * (1 + s * os2 * .75);
  const side = (s, dw = 0, from2 = 0) => {
    const out = [];
    if (!from2) {
      for (const u of [0, .2, .4, .6, .8]) { if (s === sIn && (1 - u) * l1 < miter * 1.2 + rj * .3) continue; const w = w1(u, s) + dw; out.push([a[0] + d1[0] * u + s * n1[0] * w, a[1] + d1[1] * u + s * n1[1] * w]); }
      const r = rj + dw;
      if (s === sIn) { const k = 1 / Math.max(.4, 1 + n1[0] * n2[0] + n1[1] * n2[1]); out.push([j[0] + s * (n1[0] + n2[0]) * r * k, j[1] + s * (n1[1] + n2[1]) * r * k, th > .7 ? 1 : 0]); }
      else {
        const A0 = Math.atan2(s * n1[1], s * n1[0]); let dA = Math.atan2(s * n2[1], s * n2[0]) - A0; dA = ((dA + Math.PI) % TAU + TAU) % TAU - Math.PI;
        const m = Math.abs(dA) < .12 ? 0 : Math.ceil(Math.abs(dA) / .4);
        for (let i = 0; i <= m; i++) { const A = A0 + (m ? dA * i / m : dA / 2); out.push([j[0] + Math.cos(A) * r, j[1] + Math.sin(A) * r]); }
      }
    }
    for (const u of from2 ? [from2, lerp(from2, 1, .25), lerp(from2, 1, .5), lerp(from2, 1, .75), 1] : [.2, .4, .6, .8, 1]) { if (!from2 && s === sIn && u * l2 < miter * 1.2 + rj * .3) continue; const w = w2(u, s) + dw; out.push([j[0] + d2[0] * u + s * n2[0] * w, j[1] + d2[1] * u + s * n2[1] * w]); }
    return out;
  };
  const cap = (c, t, n, wa, wb, from) => { const out = []; for (let k = 1; k < 4; k++) { const ang = from - k / 4 * Math.PI, co = Math.cos(ang), si = Math.sin(ang), w = lerp(wa, wb, k / 4); out.push([c[0] + (t[0] * co + n[0] * si) * w, c[1] + (t[1] * co + n[1] * si) * w]); } return out; };
  const capB = dw => cap(b, t2, n2, w2(1, 1) + dw, w2(1, -1) + dw, Math.PI / 2);
  const nx = n1[0] + n2[0], ny = n1[1] + n2[1];
  return {
    pts: [...side(1), ...capB(0), ...side(-1).reverse(), ...cap(a, t1, n1, w1(0, -1), w1(0, 1), -Math.PI / 2)],
    lower: (from2, dw = 0) => [...side(1, dw, from2), ...capB(dw), ...side(-1, dw, from2).reverse()],
    band: (s, d0, d1, from2 = 0) => [...side(s, -d0, from2), ...side(s, -d1, from2).reverse()],
    shSide: nx * LIGHT.x + ny * LIGHT.y < 0 ? 1 : -1, rimSide: nx * LIGHT.rimX + ny * LIGHT.rimY > 0 ? 1 : -1,
  };
}
// Fill a limb built by moeLimb: outline + gradient fill, then its cel step and rim light as strips (no clip). o as moeFill's.
// from2 > 0 fills only the second bone from u = from2 on (a sock over the shin).
function moeLimbFill(Lb, o, from2 = 0) {
  moeFill(moeMk(from2 ? Lb.lower(from2) : Lb.pts), { ...o, shade: undefined, rim: false, extra: undefined });
  if (o.shade) { crPath(Lb.band(Lb.shSide, 0, o.sh * .85, from2)); ctx.fillStyle = o.shade; ctx.fill(); }
  const rim = o.rim === false ? null : (o.rim ?? LIGHT.rim);
  if (rim) { crPath(Lb.band(Lb.rimSide, 0, (o.rimW ?? o.sh * .5) * 1.4, from2)); ctx.fillStyle = moeRim(rim)[1]; ctx.fill(); }
}
// A lock of hair along centreline C, tapering to a point; wfn(u) is its half-width.
function moeLockPts(C, wfn) {
  const n = C.length - 1, Lp = [], Rp = [];
  for (let i = 0; i <= n; i++) {
    const q = C[Math.max(0, i - 1)], r = C[Math.min(n, i + 1)], dx = r[0] - q[0], dy = r[1] - q[1], l = Math.hypot(dx, dy) || 1, w = wfn(i / n);
    Lp.push([C[i][0] - dy / l * w, C[i][1] + dx / l * w]); Rp.push([C[i][0] + dy / l * w, C[i][1] - dx / l * w]);
  }
  const tip = C[n];
  return [...Lp.slice(0, n), [tip[0], tip[1], 1], ...Rp.slice(0, n).reverse()];
}
// Offset a centreline sideways by k × its half-width (for strands inside a lock).
function moeSide(C, wfn, k) {
  const n = C.length - 1;
  return C.map((c, i) => { const q = C[Math.max(0, i - 1)], r = C[Math.min(n, i + 1)], dx = r[0] - q[0], dy = r[1] - q[1], l = Math.hypot(dx, dy) || 1, w = wfn(i / n) * k; return [c[0] - dy / l * w, c[1] + dx / l * w]; });
}
// A lock: fill runs from the root colour to the tip colour and turns see-through at the very tip; the outline stops short of it.
// cols: [root, mid, tip, tip see-through]; o: line, lw, shade + ks (the side, ±1, of the shade strip; k = +1 is the left of the
// root → tip direction), rim (colour | false) + kr (its side), strands (count), strandCol, strandW, shine + shineCol.
// Shading is drawn as strips inside the lock, so no clip is needed.
function moeLock(C, wfn, cols, o) {
  const pts = moeLockPts(C, wfn), r0 = C[0], t0 = C[C.length - 1];
  if (!moeOnPts(pts, .05)) return pts;
  const g = ctx.createLinearGradient(r0[0], r0[1], t0[0], t0[1]);
  g.addColorStop(0, cols[0]); g.addColorStop(o.mid ?? .45, cols[1]); g.addColorStop(.84, cols[2]); g.addColorStop(1, cols[3]);
  // outline along both sides, stopping short of the tip so the see-through end has no hard edge
  const n = C.length - 1, m = Math.max(2, Math.round(n * .8)), sL = pts.slice(0, m), sR = pts.slice(pts.length - m).reverse(), d = o.lw * .55;
  ctx.save(); ctx.translate(-LIGHT.x * d, -LIGHT.y * d); ctx.beginPath(); crPath(sL, false, false); crPath(sR, false, false);
  ctx.strokeStyle = o.line; ctx.lineWidth = o.lw * 2; ctx.lineJoin = ctx.lineCap = 'round'; ctx.stroke(); ctx.restore();
  crPath(pts); ctx.fillStyle = g; ctx.fill();
  const strip = (k0, k1, col) => { const a = moeSide(C, wfn, k0), b = moeSide(C, wfn, k1); crPath([...a.slice(0, n), [t0[0], t0[1], 1], ...b.slice(0, n).reverse()]); ctx.fillStyle = col; ctx.fill(); };
  if (o.shade) strip(o.ks, o.ks * .42, o.shade);
  for (let i = 0; i < (o.strands ?? 0); i++) { const k = o.strands === 1 ? .1 : lerp(-.5, .55, i / (o.strands - 1)); brush(moeSide(C, wfn, k).slice(1, n - (i % 2)), o.strandW, o.strandCol, 'mid', { min: .05 }); }
  if (o.shine) brush(moeSide(C, wfn, o.shineK ?? .35).slice(1, Math.max(3, Math.round(n * .38))), o.shine, o.shineCol, 'mid', { min: .05 });
  const rim = o.rim === false ? null : (o.rim ?? LIGHT.rim);
  if (rim) strip(o.kr ?? o.ks ?? 1, (o.kr ?? o.ks ?? 1) * .72, moeRim(rim)[1]);
  return pts;
}

// =====================================================================================================
// THE RIG
// =====================================================================================================
function idol(x, y, s, o = {}) {
  const M = MEMBERS[o.member ?? 'TOKI'] || MEMBERS.TOKI;
  const P = idolProps(o.sd ?? 0);
  const O = { ...(IDOL_EXPR[o.expr] || {}) };
  for (const k of Object.keys(o)) if (o[k] !== undefined) O[k] = o[k];
  const lean = O.lean ?? 0, pelvis = [O.sway ?? 0, P.hipY + (O.bob ?? 0) - (O.jump ?? 0)];
  const rotP = (px, py) => { const c = Math.cos(lean), n = Math.sin(lean), dy = py - pelvis[1]; return [pelvis[0] + px * c - dy * n, pelvis[1] + px * n + dy * c]; };
  const neck = rotP(0, pelvis[1] + (P.neckY - P.hipY));
  const R = { s, M, P, O, lean, pelvis, rotP, neck, pal: moePal(M) };
  const hd = idolHeadPlace(R);
  R.head = hd;
  const oldLight = LIGHT;
  if (O.rim) LIGHT = { ...LIGHT, rim: O.rim };
  ctx.save();
  if (O.anchor === 'face') ctx.translate(x - (O.flip ? -1 : 1) * hd.fx * s, y - hd.fy * s);
  else if (O.anchor === 'chest') ctx.translate(x - (O.flip ? -1 : 1) * neck[0] * s, y - neck[1] * s);
  else ctx.translate(x, y);
  ctx.scale(s, s);
  if (O.flip) ctx.scale(-1, 1);
  if (O.rot) ctx.rotate(O.rot);
  const m = ctx.getTransform();
  R.px = Math.hypot(m.a, m.b) / RS;                   // on-screen px per unit (at render scale 1): gates fine details
  if (O.shadow !== false && O.anchor === undefined) {
    const k = 1 - clamp((O.jump ?? 0) / 5) * .5;
    ctx.fillStyle = O.shadowCol ?? 'rgb(20 8 40 / .26)';
    ctx.beginPath(); ctx.ellipse((O.sway ?? 0) * .4, 0, 1.25 * k, .22 * k, 0, 0, TAU); ctx.fill();
  }
  R.lw = .03 * Math.pow(s / 70, -.42);               // average line width in s units (thin; a touch heavier when small)
  if (O.back) idolBack(R); else idolFront(R);
  ctx.restore();
  LIGHT = oldLight;
  return R;
}

// Proportions: sd 0 = idol (≈4.5 heads), sd 1 = chibi (≈2.3 heads). s units; y up is negative. upper + fore = 2.54 at sd 0, so the pose
// data's hand targets land exactly where kit.js put them relative to the neck.
const _MOE_A = { headH: 2.1, hipY: -4.98, neckY: -7.64, neckLen: .1, shW: .54, waistY: -6.26, waistW: .32, hipW: .5, skirtY: -3.76, skirtW: 1.26, thigh: 2.38, shin: 2.25, upper: 1.34, fore: 1.2, hand: .47, hipJ: .22, footY: -.25, eyeK: 1, limbW: 1, footS: 1, tail: 2.25 };
const _MOE_B = { headH: 4.4, hipY: -3.0, neckY: -4.98, neckLen: .08, shW: .64, waistY: -3.96, waistW: .48, hipW: .66, skirtY: -1.96, skirtW: 1.3, thigh: 1.32, shin: 1.28, upper: .9, fore: .8, hand: .56, hipJ: .3, footY: -.3, eyeK: 1.1, limbW: 1.5, footS: 1.25, tail: 1.2 };
function idolProps(sd) {
  if (!sd) return _MOE_A;
  const out = {}; for (const k in _MOE_A) out[k] = lerp(_MOE_A[k], _MOE_B[k], clamp(sd)); return out;
}
function idolHeadPlace(R) {
  const { P, O, neck } = R, H = P.headH, tilt = (O.tilt ?? 0) + R.lean * .5;
  const pivot = [neck[0], neck[1] - P.neckLen];
  const c = [pivot[0] + Math.sin(tilt) * H * .53, pivot[1] - Math.cos(tilt) * H * .53];
  const ey = .17;                                                 // eye line in head units
  return { x: c[0], y: c[1], h: H, rot: tilt, fx: c[0] - Math.sin(tilt) * ey * H, fy: c[1] + Math.cos(tilt) * ey * H };
}

// ---------------- front view ----------------
// A bent knee points mostly toward the viewer: keep only part of the IK's sideways knee offset, so a bob reads as a soft plié
// rather than bow legs.
function moeKnee(hj, j, e, k = .4) {
  const dx = e[0] - hj[0], dy = e[1] - hj[1], l2 = dx * dx + dy * dy || 1, u = ((j[0] - hj[0]) * dx + (j[1] - hj[1]) * dy) / l2, b = [hj[0] + dx * u, hj[1] + dy * u];
  return [b[0] + (j[0] - b[0]) * k, b[1] + (j[1] - b[1]) * k];
}
function idolFront(R) {
  const { P, O, pelvis, rotP } = R, stage = (O.outfit ?? 'stage') === 'stage';
  const at = (x, dy) => rotP(x, pelvis[1] + dy);
  const dNeck = P.neckY - P.hipY;
  R.chest = at(0, dNeck); R.shoulder = sd => at(sd * P.shW, dNeck + .17); R.at = at; R.stage = stage;
  const swing = O.swing ?? (Math.sin(bpOf(T) * Math.PI) * .14 - (O.sway ?? 0) * .3 - R.lean * .8 + (O.jump ?? 0) * .06);
  R.swing = swing;
  headHairBack(R);
  const fL = O.fL ?? [-.3, 0], fR = O.fR ?? [.31, 0];
  for (const [sd, f] of [[-1, fL], [1, fR]]) {
    const hj = at(sd * P.hipJ, .1), ft = [f[0], f[1] + P.footY - (O.jump ?? 0)];
    const { j, e } = ikOut(hj, ft, P.thigh, P.shin, sd, O.kneeIn ? -1 : (O[sd < 0 ? 'kL' : 'kR'] ?? 1));
    idolLeg(R, sd, hj, O.kneeIn ? j : moeKnee(hj, j, e), e);
  }
  idolNeck(R);
  idolTorso(R);
  idolHead(R);
  const arms = [[-1, O.hL ?? [-.9, 2.72], O.gL ?? 'open'], [1, O.hR ?? [.9, 2.72], O.gR ?? 'open']];
  const hands = [];
  for (const [sd, h, g] of arms) {
    const ak = (P.upper + P.fore) / 2.54, sh = R.shoulder(sd), tgt = [R.chest[0] + h[0] * ak, R.chest[1] + h[1] * ak];
    const { j, e } = ikOut(sh, tgt, P.upper, P.fore, sd, O[sd < 0 ? 'eL' : 'eR'] ?? 0);
    hands.push({ sd, e, g });
    idolArm(R, sd, sh, j, e, g);
  }
  if (hands[0].g === 'heart' && hands[1].g === 'heart' && Math.hypot(hands[0].e[0] - hands[1].e[0], hands[0].e[1] - hands[1].e[1]) < 1.2) {
    const cx = (hands[0].e[0] + hands[1].e[0]) / 2, my = (hands[0].e[1] + hands[1].e[1]) / 2, r = .38 * P.limbW, cy = my < R.head.y ? my - .55 * P.limbW : my + .24;
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; glow(cx, cy, r * 2.4, '#FF4FA8', .5); ctx.restore();
    moeFill(() => tracePath(heartPts(cx, cy, r, 36)), { fill: 'rgb(255 120 185 / .5)', line: alpha(IP.white, .9), lw: R.lw * .8, rim: false });
  }
  if ((O.mic ?? (stage ? 'headset' : false)) === 'headset') headset(R);
  if (O.emote) { const h = R.head; emote(O.emote, h.x + .6 * h.h, h.y - .5 * h.h, h.h * .4, O.emoteK ?? 1); }
}

// ---------------- head ----------------
// Head-local units: head height ≈ 1 (crown → chin), origin = cranium centre, +y down, chin at y ≈ .53, eye line at .17.
function jawPts(tn) {
  const base = [[-.47, -.06], [-.468, .1], [-.448, .23], [-.4, .34], [-.3, .44], [-.17, .505], [-.07, .53], [0, .535], [.07, .53], [.17, .505], [.3, .44], [.4, .34], [.448, .23], [.468, .1], [.47, -.06]];
  return base.map(([x, y]) => {
    let X = turnX(x, tn);
    if (Math.sign(x) === Math.sign(tn) && Math.abs(x) > .25 && y > .05) X -= Math.sign(x) * Math.abs(tn) * .03;
    return [X, y];
  });
}
// The face as ONE contour (cranium arc over the top, then the jaw), so cel steps and rim crescents have no inner seams.
function faceMk(tn) {
  const J = jawPts(tn);
  // the cranium turns like the hair dome over it, so no skin peeks past the hair on the far side
  const A = []; for (let i = 0; i <= 16; i++) { const a = -i / 16 * Math.PI; A.push([turnX(Math.cos(a) * .47, tn, .54), -.03 + Math.sin(a) * .47]); }
  return () => { ctx.beginPath(); ctx.moveTo(A[0][0], A[0][1]); for (const p of A) ctx.lineTo(p[0], p[1]); moeCurveTo(J); ctx.closePath(); };
}
// Append a smooth (Catmull-Rom) open curve through P to the current path, joining it with a line.
function moeCurveTo(P) {
  const n = P.length;
  ctx.lineTo(P[0][0], P[0][1]);
  for (let i = 0; i < n - 1; i++) {
    const p0 = P[Math.max(0, i - 1)], p1 = P[i], p2 = P[i + 1], p3 = P[Math.min(n - 1, i + 2)];
    ctx.bezierCurveTo(p1[0] + (p2[0] - p0[0]) / 6, p1[1] + (p2[1] - p0[1]) / 6, p2[0] - (p3[0] - p1[0]) / 6, p2[1] - (p3[1] - p1[1]) / 6, p2[0], p2[1]);
  }
}

function idolHead(R) {
  const { M, O, P } = R, h = R.head, pal = R.pal;
  const tn = clamp(O.turn ?? 0, -1, 1);
  const L = R.lw / h.h;                                         // line width in head units
  const det = R.px * h.h > 60;                                  // head at least ~60 px tall: fine details
  ctx.save(); headXf(h);
  const fm = faceMk(tn);
  moeFill(fm, { fill: MOE_SK.base, fillLt: MOE_SK.lt, g: [0, .05, .55], line: MOE_SK.line, lw: L * 1.1, rimW: .012, extra: () => {
    // the fringe's soft shadow on the forehead, and a far-cheek shade when turned
    ctx.fillStyle = alpha(MOE_SK.sh, .8); ctx.save(); ctx.translate(-.012 * Math.sign(tn || 1), .05); bangsPath(M, tn); ctx.fill(); ctx.restore();
    if (tn) { ctx.fillStyle = alpha(MOE_SK.sh, .5); ctx.beginPath(); ctx.ellipse(Math.sign(tn) * .53, .2, .08 + Math.abs(tn) * .06, .45, 0, 0, TAU); ctx.fill(); }
    // cheeks: a wide soft blush, hatch lines when blushing hard, a shiny highlight
    const bl = clamp(O.blush ?? .3);
    for (const sd of [-1, 1]) {
      const cx = turnX(sd * .3, tn), cy = .315, k = turnK(sd * .3, tn);
      const g = ctx.createRadialGradient(cx, cy, 0, cx, cy, .14);
      g.addColorStop(0, alpha(MOE_SK.cheek, .22 + bl * .5)); g.addColorStop(.55, alpha(MOE_SK.cheek, .1 + bl * .25)); g.addColorStop(1, alpha(MOE_SK.cheek, 0));
      ctx.save(); ctx.translate(cx, cy); ctx.scale(k * 1.2, .6); ctx.translate(-cx, -cy); ctx.fillStyle = g; ctx.fillRect(cx - .15, cy - .15, .3, .3); ctx.restore();
      if (bl > .55) { ctx.save(); ctx.globalAlpha = clamp((bl - .55) * 2.5); for (let i = 0; i < 3; i++) { const bx = cx + (i - 1) * .036 * k; brush([[bx + .016 * k, cy - .02], [bx - .01 * k, cy + .02]], L * 1.05, '#EC6A88', 'mid', { min: .3 }); } ctx.restore(); }
      if (det) { ctx.fillStyle = 'rgb(255 255 255 / .8)'; ctx.beginPath(); ctx.ellipse(cx - .04 * k, cy - .03, .014 * k, .009, 0, 0, TAU); ctx.fill(); }
    }
  } });
  if (O.puff) { const sd = tn > 0 ? -1 : 1; ctx.save(); ctx.strokeStyle = MOE_SK.line; ctx.lineWidth = L; ctx.beginPath(); ctx.arc(turnX(sd * .455, tn) + sd * .01, .28, .08, sd > 0 ? -1.3 : Math.PI - 1.3, sd > 0 ? 1.3 : Math.PI + 1.3); ctx.stroke(); ctx.restore(); }
  // eyes
  const kind = O.eyes ?? 'open', blinkK = O.blink !== undefined ? blinkAt(O.blink) : 0;
  const ey = .17 + (O.nod ?? 0) * .05;
  for (const sd of [-1, 1]) {
    const nx = sd * .235, cx = turnX(nx, tn), k = turnK(nx, tn) * P.eyeK;
    const winkThis = O.wink && ((O.wink === 'L') === (sd < 0));
    const kk = winkThis ? 'happy' : blinkK && ['open', 'wide', 'teary', 'star', 'heart'].includes(kind) ? 'closed' : kind;
    idolEye(M, O, cx, ey, sd, k, kk, L, tn, P.eyeK);
  }
  // nose (a tiny tick) + mouth (small)
  const mx = turnX(0, tn) + tn * .035;
  if (Math.abs(tn) > .2) brush([[mx + tn * .03, .285], [mx + tn * .055, .318], [mx + tn * .012, .325]], L * .95, alpha(MOE_SK.line, .7), 'mid', { min: .3 });
  else { ctx.fillStyle = alpha(MOE_SK.line, .55); ctx.beginPath(); ctx.ellipse(mx + .006, .318, .009, .005, 0, 0, TAU); ctx.fill(); }
  idolMouth(O.mouth ?? 'smile', mx, .41 + (O.nod ?? 0) * .03, L, tn, O);
  // front hair: side locks, fringe (see-through tips), strands, shine; accessory; brows showing through; ahoge
  sideLocks(R, tn, L);
  const bm = () => bangsPath(M, tn);
  const fg = ctx.createLinearGradient(0, -.55, 0, .27);
  fg.addColorStop(0, pal.hairHi); fg.addColorStop(.5, pal.hair); fg.addColorStop(.7, pal.hair); fg.addColorStop(.86, mixCol(pal.hair, pal.hairSkin, .55)); fg.addColorStop(1, pal.hairSkin);
  const lg = ctx.createLinearGradient(0, -.1, 0, .27);
  lg.addColorStop(0, pal.hairLine); lg.addColorStop(.45, pal.hairLine); lg.addColorStop(1, alpha(pal.hairLine, .45));
  moeFill(bm, { fill: fg, line: lg, lw: L, rim: false, extra: () => {
    ctx.save(); ctx.translate(0, -.07); crescent(bm, alpha(pal.hairSh2, .42), 0, .11); ctx.restore();
    crescent(bm, alpha(pal.hairSh2, .3), -LIGHT.x * .05, 0);
    hairShine(M, tn, L); bangStrands(M, tn, L);
    if (LIGHT.rim) { const X = x => turnX(x, tn, .54), dome = () => { ctx.beginPath(); for (let i = 0; i <= 24; i++) { const a = Math.PI * 1.03 + i / 24 * Math.PI * .94; ctx.lineTo(X(Math.cos(a) * .545), -.03 + Math.sin(a) * .56); } ctx.lineTo(X(.5), .2); ctx.lineTo(X(-.5), .2); ctx.closePath(); }; crescent(dome, moeRim(LIGHT.rim)[1], LIGHT.rimX * .024, LIGHT.rimY * .024); }
  } });
  if (det) bangWisps(R, tn, L);
  hairAcc(M, tn, L);
  if (M.hair === 'twintails') for (const sd of [-1, 1]) { const far = Math.sign(tn) === sd ? Math.abs(tn) : 0; if (far < .55) bow(turnX(sd * .47, tn, .55), -.25, .15 * (1 - far * .3), M.col, L, sd * .3); }
  if (M.hair === 'ponytail' && tn < .55) { const r = moePonyRoot(tn); bow(r[0] + .02, r[1] + .02, .14 * (1 - Math.max(0, tn) * .3), M.col, L, .5); }
  ctx.save(); ctx.globalAlpha *= .85;
  for (const sd of [-1, 1]) idolBrow(M, O, turnX(sd * .225, tn), -.045 + (O.nod ?? 0) * .04, sd, turnK(sd * .225, tn), O.brows ?? 'soft', L);
  ctx.restore();
  ahoge(M, O.ahoge ?? 'curl', tn, L);
  if (O.tears) tearsFx(tn, O.tears, L);
  if (O.sweat) sweatDrop(turnX(.44, tn) + .1, -.15, .12 * O.sweat, L);
  if (O.gloom) { ctx.save(); ctx.globalAlpha = O.gloom * .55; for (let i = 0; i < 8; i++) brush([[-.32 + i * .09, -.48], [-.32 + i * .09, -.18 + (i % 3) * .05]], .016, '#5B4F9E', 'end'); ctx.restore(); }
  ctx.restore();
}
function idolNeck(R) {
  const { O, P } = R, h = R.head, tn = clamp(O.turn ?? 0, -1, 1), L = R.lw / h.h;
  ctx.save(); headXf(h);
  const nk = turnX(0, tn) * .3, nb = .53 + (P.neckLen + .34) / h.h;
  const neckP = [[nk - .088, .3], [nk + .088, .3], [nk + .1, nb], [nk - .1, nb]];
  moeFill(() => tracePath(neckP), { fill: MOE_SK.base, line: MOE_SK.line, lw: L, rim: false, extra: () => { ctx.fillStyle = MOE_SK.sh; ctx.beginPath(); ctx.ellipse(turnX(0, tn) * .9, .53, .22, .1, 0, 0, TAU); ctx.fill(); } });
  ctx.restore();
}

// Fringe shapes per hairstyle: valleys (where locks part) and tips (lock points), left → right, head units; sw bends each lock.
const MOE_FRINGE = {
  twintails: { v: [[-.55, .1], [-.45, -.03], [-.34, -.07], [-.22, -.1], [-.1, -.13], [.02, -.16], [.14, -.12], [.26, -.09], [.38, -.05], [.55, .1]], t: [[-.5, .25], [-.39, .07], [-.28, .03], [-.16, .06], [-.04, .1], [.08, .07], [.2, .03], [.32, .06], [.48, .25]], sw: [-1, -.8, -.5, -.3, 0, .3, .5, .8, 1] },
  bob: { v: [[-.55, .12], [-.42, -.04], [-.28, -.07], [-.14, -.09], [0, -.1], [.14, -.09], [.28, -.07], [.42, -.04], [.55, .12]], t: [[-.49, .23], [-.35, .07], [-.21, .055], [-.07, .065], [.07, .065], [.21, .055], [.35, .07], [.49, .23]], sw: [-.6, -.3, -.2, -.1, .1, .2, .3, .6] },
  long: { v: [[-.55, .08], [-.43, -.06], [-.29, -.12], [-.13, -.17], [.05, -.24], [.15, -.19], [.3, -.1], [.43, -.04], [.55, .08]], t: [[-.49, .25], [-.35, .1], [-.2, .06], [-.05, .04], [.11, .03], [.24, .08], [.37, .1], [.49, .23]], sw: [-1, -.8, -.6, -.5, .5, .7, .9, 1] },
  ponytail: { v: [[-.55, .06], [-.44, -.05], [-.31, -.09], [-.17, -.12], [-.03, -.15], [.12, -.12], [.26, -.09], [.4, -.05], [.55, .06]], t: [[-.49, .23], [-.38, .08], [-.24, .05], [-.1, .08], [.05, .06], [.19, .05], [.33, .08], [.48, .21]], sw: [-.9, -.7, -.5, -.2, .2, .5, .7, .9] },
};
function bangsPath(M, tn) {
  const F = MOE_FRINGE[M.hair] || MOE_FRINGE.twintails;
  const X = x => turnX(x, tn, .54);
  ctx.beginPath();
  ctx.moveTo(X(F.v[0][0] - .02), F.v[0][1] + .02);
  for (let i = 0; i <= 24; i++) { const a = Math.PI * 1.03 + i / 24 * Math.PI * .94; ctx.lineTo(X(Math.cos(a) * .545), -.03 + Math.sin(a) * .56); }
  ctx.lineTo(X(F.v[F.v.length - 1][0] + .02), F.v[F.v.length - 1][1] + .02);
  for (let i = F.t.length - 1; i >= 0; i--) {
    const vR = F.v[i + 1], tp = F.t[i], vL = F.v[i], sw = F.sw[i] * .03;
    ctx.quadraticCurveTo(X(tp[0] + sw * .2 + (vR[0] - tp[0]) * .12), vR[1] + (tp[1] - vR[1]) * .66, X(tp[0] + sw), tp[1]);
    ctx.quadraticCurveTo(X(tp[0] + sw * .2 + (vL[0] - tp[0]) * .12), vL[1] + (tp[1] - vL[1]) * .66, X(vL[0]), vL[1]);
  }
  ctx.closePath();
}
function hairShine(M, tn, L) {
  // the "angel ring": a soft zig-zag band of shine across the crown, with a couple of white glints
  const pal = moePal(M), X = x => turnX(x, tn, .54), n = 11;
  ctx.save(); ctx.fillStyle = alpha(pal.hairLt, .82);
  const top = [], bot = [];
  for (let i = 0; i <= n; i++) {
    const u = i / n, a = Math.PI * 1.18 + u * Math.PI * .64, r = .45, y = -.03 + Math.sin(a) * r * .64, x = Math.cos(a) * r;
    top.push([X(x), y - .014 - (i % 2) * .016]); bot.push([X(x * 1.02), y + .018 + (i % 2) * .03]);
  }
  ctx.beginPath(); ctx.moveTo(top[0][0], top[0][1]); for (const p of top) ctx.lineTo(p[0], p[1]); for (const p of bot.reverse()) ctx.lineTo(p[0], p[1]);
  ctx.closePath(); ctx.fill();
  ctx.fillStyle = 'rgb(255 255 255 / .85)';
  for (const [x, y, r] of [[-.22, -.33, .022], [-.12, -.38, .014]]) { ctx.beginPath(); ctx.ellipse(X(x), y, r * 1.6, r * .8, -.4, 0, TAU); ctx.fill(); }
  ctx.restore();
}
function bangStrands(M, tn, L) {
  const F = MOE_FRINGE[M.hair] || MOE_FRINGE.twintails, X = x => turnX(x, tn, .54), pal = moePal(M);
  F.t.forEach((tp, i) => {
    const sw = F.sw[i] * .03, x0 = tp[0] * .72;
    brush(qbez([X(x0), -.34], [X(lerp(x0, tp[0] + sw, .5) - sw * .5), -.1], [X(tp[0] + sw * .9), tp[1] - .035], 8), L * .8, pal.hairLineS, 'end', { min: .1 });
  });
  // valley creases
  F.v.slice(1, -1).forEach(([vx, vy]) => brush([[X(vx), vy + .005], [X(vx * .9), vy - .1]], L * .8, pal.hairLineS, 'start', { min: .1 }));
}
// A few single strands falling over the forehead (airy hair); drawn only when the head is big enough to see them.
function bangWisps(R, tn, L) {
  const pal = R.pal, X = x => turnX(x, tn, .54), sw = R.swing * .1;
  for (const [x0, x1, y1, bend] of [[-.06, -.1, .16, -.04], [.12, .17, .14, .05], [-.3, -.36, .12, -.03]]) {
    brush(qbez([X(x0), -.1], [X(lerp(x0, x1, .5) + bend + sw), .02], [X(x1 + sw), y1], 8), L * 1.1, alpha(pal.hairLine, .55), 'start', { min: .05 });
  }
}
function sideLocks(R, tn, L) {
  const M = R.M, pal = R.pal, len = M.hair === 'bob' ? .6 : M.hair === 'long' ? 1.0 : M.hair === 'ponytail' ? .72 : .82;
  const sw = R.swing * .25;
  for (const sd of [-1, 1]) {
    if (Math.sign(tn) === sd && Math.abs(tn) > .75) continue;
    const bx = turnX(sd * .47, tn, .54);
    // a thin outer lock behind, then the main lock framing the cheek
    const C2 = crSample([[bx + sd * .02, -.1], [bx + sd * .07, .15], [bx + sd * .06 + sw * .3, len * .62], [bx + sd * .03 + sw * .5, len * .9]], 3, []);
    if (R.px * R.head.h > 90) moeLock(C2, u => .045 * Math.sin(Math.PI * Math.min(1, u * .85 + .15)) + .004, [pal.hairSh, pal.hairSh, pal.shTip, pal.shTipA], { line: pal.hairLine, lw: L * .9, rim: false });
    const C = crSample([[bx - sd * .05, -.12], [bx + sd * .025, .12], [bx + sd * .01 + sw * .25, len * .6], [bx - sd * .03 + sw * .45, len]], 3, []);
    const w = u => .068 * Math.sin(Math.PI * Math.min(1, u * .82 + .18)) + .004;
    moeLock(C, w, [pal.hair, pal.hair, pal.tip, pal.tipA], { line: pal.hairLine, lw: L * .95, shade: alpha(pal.hairSh2, .45), ks: -sd, kr: -Math.sign(LIGHT.rimX || 1), rim: sd * LIGHT.rimX > 0 ? undefined : false, strands: 1, strandW: L * .7, strandCol: pal.hairLineS });
  }
}
function hairAcc(M, tn, L) {
  const X = x => turnX(x, tn, .54), pal = moePal(M);
  if (M.acc === 'star') {
    const x = X(-.34), y = -.23;
    moeFill(() => tracePath(starPts(x, y, .085, .5, 5, -TAU / 4 + .25)), { fill: '#FFE070', fillLt: '#FFF6C0', g: [x, y, .08], shade: '#F5B540', sh: .016, line: '#B0701C', lw: L * .8 });
    ctx.fillStyle = IP.white; ctx.beginPath(); ctx.arc(x - .018, y - .022, .014, 0, TAU); ctx.fill();
  } else if (M.acc === 'clip') {
    for (let i = 0; i < 2; i++) { ctx.save(); ctx.translate(X(-.31) + i * .045, -.2 + i * .035); ctx.rotate(-.8); moeFill(() => rrect(-.075, -.016, .15, .032, .016), { fill: i ? IP.white : pal.c, line: pal.cLine, lw: L * .7, rim: false }); ctx.restore(); }
  } else if (M.acc === 'ribbon') bow(X(.35), -.33, .11, M.col, L, .3);
}
// Ribbon bow: two loops, two tails, a knot. (x, y) knot centre, r loop size. Soft style: colour-matched lines, gradient, a highlight.
function bow(x, y, r, col, L, rot = 0) {
  const [lt, dk, line] = moeShades(col);
  ctx.save(); ctx.translate(x, y); ctx.rotate(rot);
  for (const sd of [-1, 1]) moeFill(moeMk([[sd * r * .08, r * .1], [sd * r * .42, r * 1.2], [sd * r * .66, r * 1.12, 1], [sd * r * .55, r * .92], [sd * r * .2, r * .15]]), { fill: dk, line, lw: L * .75, rim: false });
  const m = ctx.getTransform(), big = Math.hypot(m.a, m.b) * r > 9 * RS;
  for (const sd of [-1, 1]) {
    moeFill(moeMk([[0, 0], [sd * r * .5, -r * .72], [sd * r * 1.1, -r * .5], [sd * r * 1.16, r * .22], [sd * r * .62, r * .46], [0, 0, 1]]), big ? { fill: col, fillLt: lt, g: [sd * r * .6, -r * .1, r * .7], line, lw: L * .75, rim: false } : { fill: col, line, lw: L * .75, rim: false });
    if (big) { crPath([[sd * r * .12, -r * .05], [sd * r * .5, -r * .38], [sd * r * .78, -r * .2], [sd * r * .6, r * .2], [sd * r * .14, r * .08]]); ctx.fillStyle = alpha(dk, .75); ctx.fill(); }
  }
  if (big) { ctx.fillStyle = alpha(lt, .9); for (const sd of [-1, 1]) { ctx.beginPath(); ctx.ellipse(sd * r * .58, -r * .38, r * .2, r * .08, sd * .5, 0, TAU); ctx.fill(); } }
  moeFill(() => { ctx.beginPath(); ctx.ellipse(0, 0, r * .24, r * .3, 0, 0, TAU); }, big ? { fill: col, fillLt: lt, g: [0, 0, r * .3], line, lw: L * .75, rim: false } : { fill: col, line, lw: L * .75, rim: false });
  ctx.restore();
}
// TOKI's cowlick is an expression channel: curl|heart|q|droop|spring|bang|none
function ahoge(M, kind, tn, L) {
  if (kind === 'none') return;
  const pal = moePal(M), bx = turnX(.06, tn, .54), by = -.575, w = Math.sin(T * 5) * .012;
  let pts;
  if (kind === 'heart') {
    ctx.save(); ctx.translate(bx + .05, by - .17); ctx.rotate(.18);
    tracePath(heartPts(0, 0, .11, 32)); ctx.lineJoin = 'round';
    ctx.strokeStyle = pal.hairLine; ctx.lineWidth = L * 3.2; ctx.stroke(); ctx.strokeStyle = pal.hair; ctx.lineWidth = L * 1.7; ctx.stroke();
    ctx.restore();
    brush([[bx, by + .03], [bx + .03, by - .06]], L * 3, pal.hairLine, 'start'); brush([[bx, by + .03], [bx + .03, by - .06]], L * 1.6, pal.hair, 'start');
    return;
  }
  switch (kind) {
    case 'q': pts = [[bx, by + .02], [bx + .01, by - .1], [bx + .09, by - .19], [bx + .18, by - .15], [bx + .16, by - .06], [bx + .1, by - .03]]; break;
    case 'droop': pts = [[bx, by + .02], [bx + .05, by - .05], [bx + .14, by - .03], [bx + .2, by + .06]]; break;
    case 'spring': pts = [[bx, by + .02], [bx - .05, by - .06], [bx + .05, by - .12], [bx - .05, by - .18], [bx + .05, by - .24], [bx, by - .3]]; break;
    case 'bang': pts = [[bx, by + .02], [bx + .005, by - .12], [bx + .02, by - .27]]; break;
    default: pts = [[bx - .01, by + .03], [bx + .02 + w, by - .1], [bx + .11 + w, by - .17], [bx + .18, by - .14]];
  }
  const C = []; crSample(pts, 5, C);
  brush(C, L * 4.4, pal.hairLine, 'start', { min: .2 });
  brush(C, L * 2.6, pal.hair, 'start', { min: .08 });
}

function headHairBack(R) {
  const { M, O } = R, h = R.head, tn = clamp(O.turn ?? 0, -1, 1), swing = R.swing, pal = R.pal;
  ctx.save(); headXf(h);
  const L = R.lw / h.h;
  if (M.hair === 'twintails') { const order = tn >= 0 ? [1, -1] : [-1, 1]; for (const sd of order) twinTail(R, sd, tn, swing, L); }
  if (M.hair === 'ponytail') ponyTail(R, tn, swing, L);
  // the back layer: a dome behind the head with a many-tipped lower edge (darker: it's the inside of the hair)
  const len = M.hair === 'long' ? 2.05 * R.P.tail / 2.25 : M.hair === 'bob' ? .64 : M.hair === 'ponytail' ? .42 : .5, wb = M.hair === 'long' ? .64 : M.hair === 'bob' ? .62 : .54;
  const off = -tn * .05, sw = swing * .15;
  const nT = M.hair === 'long' ? 6 : 5, pts = [[-.5 + off, -.18], [-.55 + off, .12], [-wb + off + sw * .6, len * .72]];
  for (let i = 0; i <= nT * 2; i++) {
    const u = i / (nT * 2), x = lerp(-wb * .96, wb * .96, u) + off + sw * (1 + Math.abs(lerp(-1, 1, u)) * .4), tipI = i % 2 === 0;
    let y = tipI ? len * (1 - (hash2(i, M.name.length) * .1) - (M.hair === 'bob' ? Math.abs(lerp(-1, 1, u)) * -.05 : 0)) : len * .86;
    if (M.hair === 'bob' && (i === 0 || i === nT * 2)) y = len * 1.02;
    pts.push(tipI ? [x, y, 1] : [x, y]);
  }
  pts.push([wb + off + sw * .6, len * .72], [.55 + off, .12], [.5 + off, -.18], [.32 + off, -.52], [-.32 + off, -.52]);
  const g = ctx.createLinearGradient(0, -.3, 0, len);
  g.addColorStop(0, pal.backSh); g.addColorStop(.72, pal.hairSh); g.addColorStop(.92, M.hair === 'long' ? pal.shTip : pal.hairSh); g.addColorStop(1, M.hair === 'long' ? pal.shTipA : pal.hairSh);
  moeFill(moeMk(pts), { fill: g, line: pal.hairLine, lw: L, rimW: .02, extra: M.hair === 'long' ? () => { for (let i = -2; i <= 2; i++) brush(qbez([i * .12 + off, .2], [i * .2 + off + sw, len * .5], [i * .22 + off + sw * 1.4, len * .92], 8), L * .8, pal.hairLineS, 'mid'); } : undefined });
  ctx.restore();
}
function twinTail(R, sd, tn, swing, L) {
  const pal = R.pal;
  const far = Math.sign(tn) === sd ? Math.abs(tn) : 0;
  const root = [turnX(sd * .46, tn, .55), -.27];
  const len = R.P.tail, sw = swing * (sd > 0 ? 1 : .9);
  // centreline of one lock: out and a little up from the tie, arcing over and falling, a soft S with an outward flick at the end
  const lockC = (lk, off, curl, ph) => {
    const n = 12, C = [root]; let p = root;
    for (let i = 1; i <= n; i++) {
      const u = i / n;
      let a = u < .28 ? lerp(-.5, 1.38, easeOut(u / .28)) : 1.38 + .12 * Math.sin((u - .28) / .72 * Math.PI * 1.2 + ph) - (u > .76 ? (u - .76) * curl : 0);
      a += sw * (.15 + .5 * u) * (1 + ph * .25);
      const A = sd > 0 ? a : Math.PI - a, l = len * lk / n;
      p = [p[0] + Math.cos(A) * l, p[1] + Math.sin(A) * l];
      C.push([p[0] + sd * off * u * u, p[1] - Math.abs(off) * .3 * u]);
    }
    return C;
  };
  const fk = 1 - far * .15;
  const wMain = u => (u < .16 ? lerp(.07, .25, Math.sin(u / .16 * Math.PI / 2)) : u < .55 ? lerp(.25, .2, (u - .16) / .39) : lerp(.2, .005, ((u - .55) / .45) ** 1.1)) * fk;
  const lockO = { line: pal.hairLine, lw: L, strandW: L * .8, strandCol: pal.hairLineS, ks: -sd, kr: -Math.sign(LIGHT.rimX || 1) };
  // back lock (darker, flicks out further), main lock, a thin front lock that separates at the end
  moeLock(lockC(.93, .1, 2.4, .6), u => wMain(u) * .78, [pal.hairSh, pal.hairSh, pal.shTip, pal.shTipA], { ...lockO, rim: false });
  moeLock(lockC(1, 0, 1.6, 0), wMain, [pal.hair, pal.hair, pal.tip, pal.tipA], { ...lockO, shade: alpha(pal.hairSh2, .6), strands: 3, shine: .055, shineCol: pal.hairLtA });
  const C3 = lockC(.82, -.07, 1.0, -.7);
  moeLock(C3, u => wMain(u) * .5, [pal.hairHi, pal.hair, pal.tip, pal.tipA], { ...lockO, strands: 1 });
}
function ponyTail(R, tn, swing, L) {
  const pal = R.pal, root = moePonyRoot(tn), len = R.P.tail * .88;
  const lockC = (lk, off, ph) => {
    const n = 11, C = [root]; let p = root;
    for (let i = 1; i <= n; i++) {
      const u = i / n, a = lerp(-.75, 1.62, easeOut(Math.min(1, u / .42))) + swing * (.2 + .55 * u) * (1 + ph * .2) - (u > .72 ? (u - .72) * (1 + ph) : 0) + .07 * Math.sin(u * 4 + ph);
      const l = len * lk / n; p = [p[0] + Math.cos(a) * l, p[1] + Math.sin(a) * l]; C.push([p[0] + off * u * u, p[1]]);
    }
    return C;
  };
  const w = u => u < .16 ? lerp(.08, .25, Math.sin(u / .16 * Math.PI / 2)) : u < .45 ? lerp(.25, .22, (u - .16) / .29) : lerp(.22, .006, ((u - .45) / .55) ** 1.1);
  const lockO = { line: pal.hairLine, lw: L, strandW: L * .8, strandCol: pal.hairLineS, ks: -1, kr: -1 };
  moeLock(lockC(.93, .14, .8), u => w(u) * .78, [pal.hairSh, pal.hairSh, pal.shTip, pal.shTipA], { ...lockO, rim: false });
  moeLock(lockC(1, 0, 0), w, [pal.hair, pal.hair, pal.tip, pal.tipA], { ...lockO, shade: alpha(pal.hairSh2, .6), strands: 3, shine: .05, shineCol: pal.hairLtA });
  moeLock(lockC(.8, -.1, -.8), u => w(u) * .5, [pal.hairHi, pal.hair, pal.tip, pal.tipA], { ...lockO, strands: 1 });
}
function moePonyRoot(tn) { return [turnX(.42, tn, .56), -.33]; }
// ---------------- eyes ----------------
function idolEye(M, O, cx, cy, sd, k, kind, L, tn, eyeK = 1) {
  const pal = moePal(M), lash = pal.lash;
  const ew = .148 * k, eh = .27 * eyeK;
  const lx = clamp(O.lookX ?? 0, -1, 1) * .045 * k + tn * .012, ly = clamp(O.lookY ?? 0, -1, 1) * .04;
  const lid = clamp(O.lid ?? 0), inner = -sd;
  ctx.save(); ctx.translate(cx, cy);
  switch (kind) {
    case 'happy':
      brush(qbez([-ew * 1.02, .045], [0, -.1], [ew * 1.02, .045], 12), L * 3.2, lash, 'mid', { min: .35 });
      brush([[-inner * ew * .96, .03], [-inner * ew * 1.24, -.005]], L * 1.6, lash, 'start', { min: .2 });
      break;
    case 'closed':
      brush(qbez([-ew * 1.05, .01], [0, .085], [ew * 1.05, .01], 12), L * 2.8, lash, 'mid', { min: .3 });
      brush([[-inner * ew * .95, .025], [-inner * ew * 1.22, -.01]], L * 1.4, lash, 'start', { min: .2 });
      brush([[-inner * ew * .6, .058], [-inner * ew * .72, .1]], L * 1.1, lash, 'start', { min: .2 });
      break;
    case 'flat': brush([[-ew * 1.05, .01], [ew * 1.05, .01]], L * 2.6, lash, 'flat'); break;
    case 'squeeze': brush([[-inner * ew * 1.05, -.07], [inner * ew * .72, .005], [-inner * ew * 1.05, .075]], L * 2.8, lash, 'flat'); break;
    case 'spiral': {
      ctx.strokeStyle = lash; ctx.lineWidth = L * 1.2; ctx.beginPath();
      for (let i = 0; i <= 44; i++) { const a = i * .45 + T * 9 * sd, r = .004 + i * .0028; i ? ctx.lineTo(Math.cos(a) * r * k * 1.35, Math.sin(a) * r * 1.35) : ctx.moveTo(0, 0); }
      ctx.stroke(); break;
    }
    case 'dot': {
      ctx.beginPath(); ctx.ellipse(0, .005, ew * 1.05, eh * .52, 0, 0, TAU); ctx.fillStyle = IP.white; ctx.fill();
      ctx.strokeStyle = lash; ctx.lineWidth = L * 1.4; ctx.stroke();
      ctx.fillStyle = lash; ctx.beginPath(); ctx.arc(lx * .3, .01, .016, 0, TAU); ctx.fill();
      break;
    }
    default: {
      const wide = kind === 'wide', sc = wide ? 1.06 : 1;
      const top = -eh * .5 * sc + lid * eh * .55, bot = eh * .48 * sc;
      const oc = [-inner * ew * 1.07, -eh * .15 + lid * .03], ic = [inner * ew * .98, eh * .03];
      const shape = () => {
        ctx.beginPath(); ctx.moveTo(ic[0], ic[1]);
        ctx.bezierCurveTo(inner * ew * .98, top * .82, -inner * ew * .42, top * 1.04, oc[0], oc[1]);
        ctx.bezierCurveTo(-inner * ew * 1.16, bot * .52, -inner * ew * .62, bot * 1.02, 0, bot);
        ctx.bezierCurveTo(inner * ew * .6, bot * 1.02, inner * ew * 1.04, bot * .55, ic[0], ic[1]);
        ctx.closePath();
      };
      shape(); ctx.fillStyle = IP.white; ctx.fill();
      ctx.save(); shape(); ctx.clip();
      ctx.fillStyle = 'rgb(200 186 240 / .45)'; ctx.beginPath(); ctx.ellipse(0, top, ew * 1.5, eh * .3, 0, 0, TAU); ctx.fill();   // lid shade on the white
      const [c0, c1, c2] = M.eye;
      const iw = ew * .82, ih = eh * .5 * (wide ? .86 : 1), ix = lx, iy = ly + eh * .05;
      const g = ctx.createLinearGradient(0, iy - ih, 0, iy + ih);
      g.addColorStop(0, c0); g.addColorStop(.4, c1); g.addColorStop(.82, c2); g.addColorStop(1, pal.eyeGlow);
      ctx.beginPath(); ctx.ellipse(ix, iy, iw, ih, 0, 0, TAU); ctx.fillStyle = g; ctx.fill();
      ctx.lineWidth = L * .9; ctx.strokeStyle = alpha(c0, .9); ctx.stroke();
      if (kind !== 'star' && kind !== 'heart') {
        const pg = ctx.createLinearGradient(0, iy - ih * .6, 0, iy + ih * .4);
        pg.addColorStop(0, c0); pg.addColorStop(1, alpha(c0, .55));
        ctx.beginPath(); ctx.ellipse(ix, iy - ih * .06, iw * (wide ? .3 : .44), ih * (wide ? .32 : .5), 0, 0, TAU); ctx.fillStyle = pg; ctx.fill();
      }
      ctx.fillStyle = alpha(pal.eyeGlow, .5); ctx.beginPath(); ctx.ellipse(ix, iy + ih * .62, iw * .62, ih * .3, 0, 0, TAU); ctx.fill();   // dewy glow low in the iris
      ctx.fillStyle = alpha(c0, .5); ctx.beginPath(); ctx.ellipse(0, top - .01, ew * 1.5, eh * .2, 0, 0, TAU); ctx.fill();                // lid shadow across the top
      if (kind === 'star') { solid(starPts(ix, iy + ih * .05, iw * .66, .45, 5, -TAU / 4), '#FFF4C8', { shade: false, line: false, sharp: true }); ctx.fillStyle = IP.white; ctx.beginPath(); ctx.arc(ix + iw * .42, iy + ih * .45, iw * .12, 0, TAU); ctx.fill(); }
      else if (kind === 'heart') { solid(heartPts(ix, iy + ih * .05, iw * .9, 32), '#FF4F9A', { shade: false, line: false }); ctx.fillStyle = IP.white; ctx.beginPath(); ctx.ellipse(ix - iw * .35, iy - ih * .2, iw * .17, ih * .13, -.5, 0, TAU); ctx.fill(); }
      else {
        // big dewy highlights: a large oval toward the light, a round one opposite, a tiny glint and a four-point sparkle
        const hs = LIGHT.x < 0 ? 1 : -1;
        ctx.fillStyle = IP.white;
        ctx.beginPath(); ctx.ellipse(ix - hs * iw * .34, iy - ih * .36, iw * .36, ih * .26, -.45 * hs, 0, TAU); ctx.fill();
        ctx.beginPath(); ctx.arc(ix + hs * iw * .42, iy + ih * .3, iw * .15, 0, TAU); ctx.fill();
        ctx.globalAlpha = .85; ctx.beginPath(); ctx.arc(ix - hs * iw * .12, iy + ih * .62, iw * .07, 0, TAU); ctx.fill(); ctx.globalAlpha = 1;
        sparkle(ix + hs * iw * .36, iy - ih * .1, iw * .22, .2, IP.white);
      }
      if (kind === 'teary') { ctx.fillStyle = alpha('#CDEFFF', .55); ctx.fillRect(-ew * 1.3, bot - .07 + Math.sin(T * 18) * .004, ew * 2.6, .09); ctx.fillStyle = IP.white; ctx.beginPath(); ctx.ellipse(0, bot - .045, ew * .7, .012, 0, 0, TAU); ctx.fill(); }
      ctx.strokeStyle = 'rgb(255 255 255 / .55)'; ctx.lineWidth = L * .9; ctx.beginPath(); ctx.ellipse(0, bot - eh * .42, ew * .78, eh * .4, 0, Math.PI * .22, Math.PI * .78); ctx.stroke();   // wet lower rim
      ctx.restore();
      // lashes: a heavy upper line thickening to the outer corner, two little flicks, a soft short lower lash, a crease
      const lashP = bez([ic[0] + inner * .012, ic[1] - .004], [inner * ew * .98, top * .84 - .014], [-inner * ew * .42, top * 1.07 - .016], [oc[0] - inner * .004, oc[1] - .008], 16);
      brush(lashP, L * 4.2, lash, 'end', { min: .22 });
      brush(qbez([oc[0] + inner * .035, oc[1] - .012], [oc[0] - inner * .02, oc[1] - .03], [oc[0] - inner * .058, oc[1] - .062], 5), L * 2.1, lash, 'start', { min: .15 });
      brush(qbez([oc[0] + inner * .012, oc[1] + .006], [oc[0] - inner * .03, oc[1] + .008], [oc[0] - inner * .062, oc[1] - .012], 5), L * 1.6, lash, 'start', { min: .15 });
      brush(qbez([-inner * ew * 1.0, bot * .32], [-inner * ew * .8, bot * .96], [-inner * ew * .22, bot * 1.02], 8), L * 1.3, alpha(lash, .75), 'start', { min: .12 });
      if (lid < .3) brush(qbez([inner * ew * .45, top - .045], [-inner * ew * .2, top - .072], [-inner * ew * .92, top * .55 - .048], 8), L * .85, alpha(MOE_SK.line, .6), 'mid');
    }
  }
  ctx.restore();
}
function idolBrow(M, O, cx, cy, sd, k, kind, L) {
  const inner = -sd, w = .085 * k, pal = moePal(M);
  let a = [inner * w, 0], c = [0, -.026], b = [-inner * w, .006];
  switch (kind) {
    case 'up': a = [inner * w, -.02]; c = [0, -.045]; b = [-inner * w, -.005]; break;
    case 'high': a = [inner * w, -.055]; c = [0, -.085]; b = [-inner * w, -.035]; break;
    case 'worried': a = [inner * w, -.055]; c = [0, -.035]; b = [-inner * w, .02]; break;
    case 'angry': a = [inner * w, .045]; c = [0, .0]; b = [-inner * w, -.03]; break;
    case 'smug': if (sd > 0) { a = [inner * w, -.045]; c = [0, -.08]; b = [-inner * w, -.035]; } else { a = [inner * w, .02]; c = [0, -.005]; b = [-inner * w, 0]; } break;
    case 'think': if (sd > 0) { a = [inner * w, -.05]; c = [0, -.075]; b = [-inner * w, -.025]; } else { a = [inner * w, .015]; c = [0, -.015]; b = [-inner * w, 0]; } break;
    case 'flat': a = [inner * w, 0]; c = [0, 0]; b = [-inner * w, 0]; break;
  }
  ctx.save(); ctx.translate(cx, cy);
  brush(qbez(a, c, b, 8), L * 1.6, pal.hairLine, 'start', { min: .25 });
  ctx.restore();
}

// ---------------- mouth ----------------
// shapes: smile|open|o|O|a|i|u|e|cat|flat|frown|pout|wavy|smirk|teeth|tongue|scream|wail|closed (small, soft, warm-coloured)
function idolMouth(kind, x, y, L, tn, O) {
  const K = .8;
  ctx.save(); ctx.translate(x, y); ctx.scale((1 - Math.abs(tn) * .25) * K, K); L /= K;
  const inside = '#C2476E', tongue = '#FF9DB4', line = '#A34A66';
  const open = (w, h, flat = .15, teeth = false, tng = true) => {
    const mk = () => { ctx.beginPath(); ctx.moveTo(-w, -h * flat); ctx.quadraticCurveTo(0, -h * (flat + .3), w, -h * flat); ctx.bezierCurveTo(w * .95, h * .75, -w * .95, h * .75, -w, -h * flat); ctx.closePath(); };
    mk(); ctx.fillStyle = inside; ctx.fill();
    ctx.save(); mk(); ctx.clip();
    if (tng) { ctx.fillStyle = tongue; ctx.beginPath(); ctx.ellipse(0, h * .62, w * .72, h * .42, 0, 0, TAU); ctx.fill(); }
    if (teeth) { ctx.fillStyle = IP.white; ctx.fillRect(-w, -h, w * 2, h * .7); }
    ctx.restore();
    mk(); ctx.strokeStyle = line; ctx.lineWidth = L * 1.05; ctx.lineJoin = 'round'; ctx.stroke();
  };
  const stroke = (pts, w = 1.3, prof = 'mid') => brush(pts, L * w, line, prof, { min: .35 });
  switch (kind) {
    case 'open': open(.07, .085, .1); break;
    case 'a': open(.058, .09, .12); break;
    case 'e': open(.075, .05, .2, true); break;
    case 'i': open(.075, .032, .2, true, false); break;
    case 'o': ctx.beginPath(); ctx.ellipse(0, .01, .03, .038, 0, 0, TAU); ctx.fillStyle = inside; ctx.fill(); ctx.strokeStyle = line; ctx.lineWidth = L; ctx.stroke(); break;
    case 'u': ctx.beginPath(); ctx.ellipse(0, .005, .02, .024, 0, 0, TAU); ctx.fillStyle = inside; ctx.fill(); ctx.strokeStyle = line; ctx.lineWidth = L; ctx.stroke(); break;
    case 'O': { const mk = () => { ctx.beginPath(); ctx.ellipse(0, .025, .05, .068, 0, 0, TAU); }; mk(); ctx.fillStyle = inside; ctx.fill(); ctx.save(); mk(); ctx.clip(); ctx.fillStyle = tongue; ctx.beginPath(); ctx.ellipse(0, .08, .04, .028, 0, 0, TAU); ctx.fill(); ctx.restore(); mk(); ctx.strokeStyle = line; ctx.lineWidth = L * 1.05; ctx.stroke(); break; }
    case 'scream': open(.1, .15, .25); break;
    case 'wail': { const mk = () => { ctx.beginPath(); ctx.moveTo(-.09, .045); ctx.quadraticCurveTo(0, -.075, .09, .045); ctx.quadraticCurveTo(0, .095, -.09, .045); ctx.closePath(); }; mk(); ctx.fillStyle = inside; ctx.fill(); ctx.strokeStyle = line; ctx.lineWidth = L; ctx.stroke(); break; }
    case 'cat': stroke([[-.06, -.01], [-.03, .018], [0, 0], [.03, .018], [.06, -.01]], 1.3); break;
    case 'flat': stroke([[-.035, 0], [.035, 0]]); break;
    case 'frown': stroke(qbez([-.045, .018], [0, -.022], [.045, .018], 6)); break;
    case 'pout': ctx.beginPath(); ctx.ellipse(0, .002, .022, .014, 0, 0, TAU); ctx.fillStyle = '#F07C98'; ctx.fill(); stroke(qbez([-.032, .012], [0, -.02], [.032, .012], 6), 1.2); break;
    case 'wavy': stroke([[-.06, .005], [-.04, -.012], [-.02, .01], [0, -.012], [.02, .01], [.04, -.012], [.06, .005]], 1.2, 'flat'); break;
    case 'smirk': stroke(qbez([-.045, .008], [.01, .028], [.06, -.028], 8), 1.4, 'end'); break;
    case 'teeth': { const mk = () => { ctx.beginPath(); ctx.moveTo(-.07, -.012); ctx.quadraticCurveTo(0, .006, .07, -.012); ctx.quadraticCurveTo(0, .085, -.07, -.012); ctx.closePath(); }; mk(); ctx.fillStyle = IP.white; ctx.fill(); ctx.strokeStyle = line; ctx.lineWidth = L; ctx.stroke(); brush([[-.05, .022], [.05, .022]], L * .6, alpha(line, .5), 'mid'); break; }
    case 'tongue': stroke(qbez([-.05, -.012], [0, .036], [.05, -.012], 8), 1.3); ctx.beginPath(); ctx.ellipse(.018, .02, .022, .028, .3, 0, Math.PI); ctx.fillStyle = tongue; ctx.fill(); ctx.strokeStyle = line; ctx.lineWidth = L * .8; ctx.stroke(); break;
    case 'closed': stroke([[-.028, 0], [.028, 0]], 1.1); break;
    default: stroke(qbez([-.045, -.01], [0, .03], [.045, -.01], 8), 1.3);       // smile
  }
  ctx.restore();
}

// ---------------- torso & outfit ----------------
function idolTorso(R) {
  const { M, P, O, at } = R, lw = R.lw, pal = R.pal, stage = R.stage, back = !!R.backView, det = R.px > 34;
  const dW = P.waistY - P.hipY, dN = P.neckY - P.hipY, dS = P.skirtY - P.hipY, sw = P.shW, ww = P.waistW, pw = P.hipW;
  const tx = back ? 0 : clamp(O.turn ?? 0, -1, 1) * .08;
  const A = (x, dy, c) => { const p = at(x, dy); if (c) p.push(1); return p; };
  const skSw = (R.swing ?? 0) * .12 + Math.sin(bpOf(T) * Math.PI + .7) * .045 + (O.sway ?? 0) * -.12;
  const mid = at(0, (dN + dW) / 2);
  if (stage) {
    moeSkirt(R, dW, dS, ww, P.skirtW, skSw, lw, pal, det);
    // blouse
    const body = [A(-.15, dN), A(-.34, dN + .06), A(-sw - .02, dN + .22), A(-sw * .84, dN + .56), A(-ww - .05, dN + .98), A(-ww, dW + .02), A(-ww * .98, dW + .2, 1), A(ww * .98, dW + .2, 1), A(ww, dW + .02), A(ww + .05, dN + .98), A(sw * .84, dN + .56), A(sw + .02, dN + .22), A(.34, dN + .06), A(.15, dN)];
    moeFill(moeMk(body), { fill: MOE_WH.base, fillLt: MOE_WH.lt, g: [mid[0], mid[1], .8], shade: MOE_WH.sh, sh: .1, line: MOE_WH.line, lw });
    // corset: a sweetheart-topped bodice in the member colour, lace-up front, lace trim
    const cs = [A(-ww - .07, dN + .8), A(-.17 + tx, dN + .7), A(tx, dN + .8, 1), A(.17 + tx, dN + .7), A(ww + .07, dN + .8), A(ww + .012, dW + .02), A(ww * .92, dW + .17), A(tx, dW + .22, 1), A(-ww * .92, dW + .17), A(-ww - .012, dW + .02)];
    if (!back) {
      moeFill(moeMk(cs), { fill: pal.c, fillLt: pal.cLt, g: [mid[0], mid[1] + .3, .6], shade: pal.cSh, sh: .08, line: pal.cLine, lw: lw * .85, rimW: .03 });
      const tp = [cs[0], cs[1], cs[2], cs[3], cs[4]];
      ctx.save(); ctx.strokeStyle = IP.white; ctx.lineWidth = lw * 2.6; ctx.lineCap = 'round'; crPath(tp.map(p => [p[0], p[1] + .015]), false); ctx.stroke(); ctx.restore();
      if (det) {
        ctx.save(); ctx.strokeStyle = alpha(IP.white, .9); ctx.lineWidth = lw * .9;
        for (let i = 0; i < 3; i++) { const y0 = dN + .88 + i * .13, y1 = y0 + .13, a0 = at(tx - .05, y0), a1 = at(tx + .05, y1), b0 = at(tx + .05, y0), b1 = at(tx - .05, y1); ctx.beginPath(); ctx.moveTo(a0[0], a0[1]); ctx.lineTo(a1[0], a1[1]); ctx.moveTo(b0[0], b0[1]); ctx.lineTo(b1[0], b1[1]); ctx.stroke(); }
        ctx.restore();
      }
      // round collar with a member-colour trim, the big chest bow with a heart gem
      for (const sd of [-1, 1]) {
        const lobe = [A(sd * .015 + tx, dN + .03), A(sd * .22 + tx, dN - .005), A(sd * .4 + tx * .5, dN + .1), A(sd * .38 + tx * .5, dN + .3), A(sd * .2 + tx, dN + .37), A(sd * .05 + tx, dN + .24)];
        moeFill(moeMk(lobe), { fill: MOE_WH.base, fillLt: MOE_WH.lt, g: [...lobe[3], .3], shade: MOE_WH.sh, sh: .05, line: MOE_WH.line, lw: lw * .85, rim: false, extra: () => { crPath(lobe); ctx.strokeStyle = pal.c; ctx.lineWidth = lw * 3.2; ctx.stroke(); } });
      }
      const rb = at(tx, dN + .3);
      bow(rb[0], rb[1], .21 * (P.limbW > 1.2 ? 1.15 : 1), M.col, lw * .95, R.lean);
      moeFill(() => tracePath(heartPts(rb[0], rb[1] + .005, .065, 20)), { fill: '#FFD9EC', fillLt: '#FFFFFF', g: [rb[0], rb[1], .06], line: '#C0508A', lw: lw * .6, rim: false });
    } else {
      // back: the corset laced up, and a big bow at the small of the back
      const cb = [A(-ww - .07, dN + .75), A(ww + .07, dN + .75), A(ww + .012, dW + .02), A(ww * .92, dW + .17), A(-ww * .92, dW + .17), A(-ww - .012, dW + .02)];
      moeFill(moeMk(cb), { fill: pal.c, fillLt: pal.cLt, g: [mid[0], mid[1] + .3, .6], shade: pal.cSh, sh: .08, line: pal.cLine, lw: lw * .85 });
      const collar = [A(-.3, dN + .02), A(.3, dN + .02), A(.36, dN + .42, 1), A(-.36, dN + .42, 1)];
      moeFill(moeMk(collar), { fill: MOE_WH.base, line: MOE_WH.line, lw: lw * .85, rim: false, extra: () => { crPath(collar); ctx.strokeStyle = pal.c; ctx.lineWidth = lw * 3.2; ctx.stroke(); } });
      const bb = at(0, dW + .05);
      bow(bb[0], bb[1], .34 * (P.limbW > 1.2 ? 1.1 : 1), M.col, lw, R.lean);
    }
  } else {
    // practice: an oversized pastel hoodie with the "A!" logo over soft joggers
    const body = [A(-.18, dN - .01), A(-sw - .06, dN + .16), A(-sw - .12, dN + .7), A(-pw - .1, dW + .3), A(-pw - .14, .5), A(-pw * .5, .56), A(pw * .5, .56), A(pw + .14, .5), A(pw + .1, dW + .3), A(sw + .12, dN + .7), A(sw + .06, dN + .16), A(.18, dN - .01)];
    moeFill(moeMk(body), { fill: pal.lt, fillLt: pal.ltLt, g: [mid[0], mid[1], 1], shade: pal.ltSh, sh: .14, line: pal.ltLine, lw, rimW: .04 });
    // ribbed hem band
    const hb = [A(-pw - .14, .38), A(pw + .14, .38), A(pw + .14, .5), A(pw * .5, .56), A(-pw * .5, .56), A(-pw - .14, .5)];
    moeFill(moeMk(hb), { fill: pal.ltSh, line: pal.ltLine, lw: lw * .8, rim: false });
    if (!back) {
      // hood collar, drawstrings, pocket, logo
      const hood = [A(-.34 + tx, dN - .02), A(.34 + tx, dN - .02), A(.24 + tx, dN + .22), A(tx, dN + .3), A(-.24 + tx, dN + .22)];
      moeFill(moeMk(hood), { fill: pal.ltSh, line: pal.ltLine, lw: lw * .8, rim: false });
      for (const sd of [-1, 1]) { const a = at(sd * .1 + tx, dN + .24), b = at(sd * .12 + tx, dN + .78); ln([a, b], IP.white, lw * 1.8); ctx.fillStyle = IP.white; ctx.beginPath(); ctx.arc(b[0], b[1], lw * 1.6, 0, TAU); ctx.fill(); }
      const c = at(tx, dN + 1.08);
      ctx.save(); ctx.translate(c[0], c[1]); ctx.rotate(R.lean); dtext('A!', 0, 0, .42, { fill: pal.c, strokes: [[IP.white, .07]] }); ctx.restore();
    } else {
      const hood = [A(-.36, dN - .04), A(.36, dN - .04), A(.3, dN + .5), A(0, dN + .62), A(-.3, dN + .5)];
      moeFill(moeMk(hood), { fill: pal.lt, fillLt: pal.ltLt, g: [...at(0, dN + .3), .4], shade: pal.ltSh, sh: .06, line: pal.ltLine, lw: lw * .85 });
    }
  }
}
// The bell skirt: a lace petticoat peeking out below a scalloped member-colour skirt with soft folds and a white hem ribbon.
function moeSkirt(R, dW, dS, ww, SW, skSw, lw, pal, det) {
  const at = R.at;
  const hemY = x => dS + (1 - (x / SW) ** 2) * .07;
  const swX = x => x + skSw * (1 + Math.abs(x) * .55);
  const side = (sd, k) => [at(swX(sd * ww * 1.05), dW + .05), at(swX(sd * (ww + (SW * k - ww) * .62)), dW + (dS - dW) * .3), at(swX(sd * (ww + (SW * k - ww) * .92)), dW + (dS - dW) * .68)];
  const nP = 12, pet = [...side(-1, 1.05)];
  for (let i = 0; i <= nP * 2; i++) { const x = lerp(-SW * 1.05, SW * 1.05, i / (nP * 2)), v = i % 2 === 0, p = at(swX(x), hemY(x / 1.05) + .18 + (v ? 0 : .055)); if (v) p.push(1); pet.push(p); }
  pet.push(...side(1, 1.05).reverse());
  const nS = 7, sk = [...side(-1, 1)], valleys = [];
  for (let i = 0; i <= nS * 2; i++) { const x = lerp(-SW, SW, i / (nS * 2)), v = i % 2 === 0, p = at(swX(x), hemY(x) + (v ? 0 : .08)); if (v) { p.push(1); valleys.push(p); } sk.push(p); }
  sk.push(...side(1, 1).reverse());
  const top = at(0, dW), bot = at(0, dS + .2);
  if (!moeOnPts(pet, .1)) return;
  // petticoat, with the skirt's soft shadow on it and lace holes along the hem (the shadow is the skirt shifted down, which stays inside
  // the wider, longer petticoat, so no clip is needed)
  moeFill(moeMk(pet), { fill: MOE_WH.base, fillLt: MOE_WH.lt, g: [bot[0], bot[1], 1], line: MOE_WH.line, lw: lw * .9, rim: false });
  ctx.save(); ctx.translate(0, .07); crPath(sk); ctx.fillStyle = alpha(MOE_WH.sh, .95); ctx.fill(); ctx.restore();
  if (det) { ctx.fillStyle = alpha(pal.cLt, .7); for (let i = 1; i < nP * 2; i += 2) { const p = pet[3 + i]; ctx.beginPath(); ctx.arc(p[0], p[1] - .075, .022, 0, TAU); ctx.fill(); } }
  const g = ctx.createLinearGradient(top[0], top[1], bot[0], bot[1]);
  g.addColorStop(0, pal.cLt); g.addColorStop(.45, pal.c); g.addColorStop(1, mixCol(pal.c, pal.cSh, .25));
  moeFill(moeMk(sk), { fill: g, shade: alpha(pal.cSh, .9), sh: .22, line: pal.cLine, lw, rimW: .05 });
  {
    // folds from the waist into each scallop valley, light streaks between them
    for (let i = 1; i < nS; i++) { const a = at(swX(lerp(-ww, ww, i / nS)) * .9, dW + .25), v = valleys[i]; brush(qbez(a, [lerp(a[0], v[0], .5) * 1.04, lerp(a[1], v[1], .5)], [v[0], v[1] - .04], 8), lw * 1.6, alpha(pal.cSh, .7), 'end', { min: .1 }); }
    for (let i = 0; i < nS; i++) { const a = at(swX(lerp(-ww, ww, (i + .5) / nS)) * .85, dW + .45), v = sk[3 + i * 2 + 1]; brush(qbez(a, [lerp(a[0], v[0], .5), lerp(a[1], v[1], .5)], [v[0], v[1] - .3], 6), lw * 2.4, 'rgb(255 255 255 / .28)', 'mid', { min: .1 }); }
    // the hem ribbon follows the scallops
    ctx.save(); ctx.strokeStyle = alpha(IP.white, .92); ctx.lineWidth = lw * 2.6; ctx.lineJoin = 'round'; crPath(sk.slice(3, 3 + nS * 2 + 1).map(p => [p[0], p[1] - .1, p[2]]), false); ctx.stroke(); ctx.restore();
  }
  // waistband
  const wb = [at(-ww - .02, dW - .03), at(ww + .02, dW - .03), at(ww * 1.04 + .02, dW + .12), at(-ww * 1.04 - .02, dW + .12)];
  moeFill(() => tracePath(wb), { fill: pal.cDeep, line: pal.cLine, lw: lw * .8, rim: false });
}

// ---------------- limbs ----------------
function idolLeg(R, sd, hj, knee, ank) {
  const { P } = R, k = P.limbW, lw = R.lw, pal = R.pal, det = R.px > 30;
  if (!moeOnPts(R.stage ? [knee, ank] : [hj, knee, ank], .45 * k)) return;
  const bs1 = moeBs(hj, knee, sd), bs2 = moeBs(knee, ank, sd), m = moeLerp(hj, ank, .6);
  const a = Math.atan2(ank[1] - knee[1], ank[0] - knee[0]);
  // one soft leg (or, folded hard, thigh + shin with clipped shading)
  const leg = (ra, rj, rb, sw1, sw2, o, from2 = 0) => {
    const Lb = moeLimb(hj, knee, ank, ra * k, rj * k, rb * k, sw1 * k, .3, bs1 * .6, sw2 * k, .27, bs2 * .85);
    if (Lb) return moeLimbFill(Lb, o, from2);
    const th = moeSeg(hj, knee, ra * k, rj * k, sw1 * k, .3, bs1 * .6), sn = moeSeg(from2 ? moeLerp(knee, ank, from2) : knee, ank, rj * .95 * k, rb * k, sw2 * k, .27, bs2 * .85);
    if (from2) moeFill(moeMk(sn), o); else moeFill(moeMkU(th, sn), { ...o, parts: [moeMk(th), moeMk(sn)] });
  };
  if (R.stage) {
    leg(.28, .165, .086, .03, .068, { fill: MOE_SK.base, fillLt: MOE_SK.lt, g: [m[0], m[1], .5], shade: MOE_SK.sh, sh: .085 * k, line: MOE_SK.line, lw });
    if (det) { const kp = moeLerp(knee, ank, .03), c = Math.cos(a), s = Math.sin(a); brush(qbez([kp[0] - s * .05 * k, kp[1] + c * .05 * k], [kp[0] + c * .05 * k, kp[1] + s * .05 * k], [kp[0] + s * .05 * k, kp[1] - c * .05 * k], 6), lw * .8, alpha(MOE_SK.line, .35), 'mid'); }
    // knee sock: the shin from just below the knee, in white, a ribbed top band and a little bow on the outside
    leg(.29, .176, .098, .03, .07, { fill: MOE_WH.base, fillLt: MOE_WH.lt, g: [ank[0], ank[1] - .8, .6], shade: MOE_WH.sh, sh: .08 * k, line: MOE_WH.line, lw }, .2);
    const s0 = moeLerp(knee, ank, .2);
    ctx.save(); ctx.translate(s0[0], s0[1]); ctx.rotate(a - Math.PI / 2);
    moeFill(() => rrect(-.19 * k, -.035 * k, .38 * k, .09 * k, .045 * k), { fill: pal.cPale, line: MOE_WH.line, lw: lw * .8, rim: false });
    ctx.restore();
    if (R.px * k > 14) bow(s0[0] + sd * .15 * k, s0[1] + .02 * k, .075 * k, R.M.col, lw * .8, sd * .25);
    moeShoe(R, sd, ank, k, lw, pal, false);
  } else {
    leg(.34, .23, .13, .045, .075, { fill: '#5C569E', fillLt: '#7C76BE', g: [m[0], m[1], .6], shade: '#474189', sh: .1 * k, line: '#2E2860', lw });
    ln([hj, knee, ank].map(p => [p[0] + sd * .15 * k, p[1]]), alpha(IP.white, .6), lw * 1.3);
    const c0 = moeLerp(knee, ank, .92);
    ctx.save(); ctx.translate(c0[0], c0[1]); ctx.rotate(a - Math.PI / 2);
    moeFill(() => rrect(-.15 * k, -.055 * k, .3 * k, .12 * k, .055 * k), { fill: '#48428A', line: '#2E2860', lw: lw * .8, rim: false });
    ctx.restore();
    moeShoe(R, sd, ank, k, lw, pal, true);
  }
}
// Front-view shoe at the ankle: a round-toed Mary Jane with a strap and button (stage), or a chunky sneaker (practice).
function moeShoe(R, sd, ank, k, lw, pal, sneaker) {
  const f = R.P.footS * k * (sneaker ? 1.3 : 1.12), back = !!R.backView;
  ctx.save(); ctx.translate(ank[0] + sd * .02 * f, ank[1]); ctx.rotate(sd * .1); ctx.scale(f, f);
  if (!sneaker) {
    const pts = [[-.115, -.03], [.115, -.03], [.16, .07], [.15, .18], [.08, .245], [0, .255], [-.08, .245], [-.15, .18], [-.16, .07]];
    moeFill(moeMk(pts), { fill: pal.cDeep, fillLt: pal.c, g: [0, .1, .15], shade: pal.cSh, sh: .05, line: pal.cLine, lw: lw / f, rimW: .02 });
    if (!back) {
      ctx.fillStyle = 'rgb(255 255 255 / .7)'; ctx.beginPath(); ctx.ellipse(-.06, .15, .04, .022, -.3, 0, TAU); ctx.fill();
      ctx.strokeStyle = pal.cLine; ctx.lineWidth = lw * .8 / f; ctx.beginPath(); ctx.moveTo(-.13, .035); ctx.quadraticCurveTo(0, .065, .13, .035); ctx.stroke();
      ctx.fillStyle = '#FFE58A'; ctx.beginPath(); ctx.arc(sd * .12, .04, .022, 0, TAU); ctx.fill();
    }
  } else {
    const pts = [[-.14, -.05], [.14, -.05], [.2, .08], [.19, .19], [.1, .26], [0, .265], [-.1, .26], [-.19, .19], [-.2, .08]];
    moeFill(moeMk(pts), { fill: '#FFFFFF', fillLt: '#FFFFFF', g: [0, .1, .2], shade: MOE_WH.sh, sh: .06, line: MOE_WH.line, lw: lw / f });
    ctx.strokeStyle = pal.c; ctx.lineWidth = .045; ctx.lineCap = 'round'; ctx.beginPath(); ctx.moveTo(-.17, .2); ctx.quadraticCurveTo(0, .245, .17, .2); ctx.stroke();
    if (!back) { ctx.strokeStyle = alpha(MOE_WH.line, .8); ctx.lineWidth = lw * .7 / f; for (let i = 0; i < 2; i++) { ctx.beginPath(); ctx.moveTo(-.06, .02 + i * .045); ctx.lineTo(.06, .02 + i * .045); ctx.stroke(); } }
  }
  ctx.restore();
}
function idolArm(R, sd, sh, el, wr, g) {
  const { P, M } = R, k = P.limbW, lw = R.lw, pal = R.pal;
  if (!moeOnPts([sh, el, wr], .45 * k + P.hand * 1.2) && g !== 'fheart') return;
  const fa = Math.atan2(wr[1] - el[1], wr[0] - el[0]), m = moeLerp(sh, wr, .5), bs1 = moeBs(sh, el, sd), bs2 = moeBs(el, wr, sd);
  const stage = R.stage;
  const [ra, rj, rb, s1, s2] = stage ? [.135, .098, .064, .012, .02] : [.2, .165, .145, .018, .012];
  const Lb = moeLimb(sh, el, wr, ra * k, rj * k, rb * k, s1 * k, .38, bs1 * .4, s2 * k, .28, bs2 * .7);
  const look = stage ? { fill: MOE_SK.base, fillLt: MOE_SK.lt, g: [m[0], m[1], .6], shade: MOE_SK.sh, sh: .065 * k, line: MOE_SK.line, lw }
    : { fill: pal.lt, fillLt: pal.ltLt, g: [m[0], m[1], .7], shade: pal.ltSh, sh: .085 * k, line: pal.ltLine, lw };
  // a fold too sharp for one contour: upper arm, then the forearm over it (each a straight soft limb)
  const bone = (a, b, r0, r1, sw, bu, os) => moeLimb(a, moeLerp(a, b, .5), b, r0, (r0 + r1) / 2 + sw * .6, r1, sw * .4, bu * 2, os, sw * .4, .2, os);
  const foL = () => bone(el, wr, rj * .96 * k, rb * k, s2 * k, .28, bs2 * .7);
  if (Lb) moeLimbFill(Lb, look);
  else { moeLimbFill(bone(sh, el, ra * k, rj * k, s1 * k, .38, bs1 * .4), look); moeLimbFill(foL(), look); }
  if (stage) moePuff(R, sh, el, k, lw, pal);
  // a forearm raised in front of the shoulder is drawn again on top (seen from behind, the upper arm hides it)
  if (Lb && !R.backView && wr[1] < el[1] - .1 && Math.hypot(wr[0] - sh[0], wr[1] - sh[1]) < P.upper * 1.1) moeLimbFill(foL(), look);
  hand(wr, fa, P.hand, g, sd, lw, R.O, M);
  moeCuff(R, wr, fa, k, lw, pal, !stage);
}
// Puff sleeve over the shoulder, oriented along the upper arm, gathered into a member-colour band.
function moePuff(R, sh, el, k, lw, pal) {
  const a = Math.atan2(el[1] - sh[1], el[0] - sh[0]);
  ctx.save(); ctx.translate(sh[0], sh[1]); ctx.rotate(a); ctx.scale(k, k);
  const L = lw / k;
  const pts = [[-.17, 0], [-.11, -.24], [.08, -.29], [.28, -.25], [.4, -.13, 1], [.4, .13, 1], [.28, .25], [.08, .29], [-.11, .24]];
  moeFill(moeMk(pts), { fill: MOE_WH.base, fillLt: MOE_WH.lt, g: [.1, 0, .3], shade: MOE_WH.sh, sh: .07, line: MOE_WH.line, lw: L, rimW: .02, glow: false, extra: () => {
    for (const y of [-.12, 0, .12]) brush(qbez([.38, y * .9], [.2, y * 1.4], [.02, y * 1.5], 6), L * .9, alpha(MOE_WH.line, .5), 'start', { min: .1 });
    ctx.fillStyle = 'rgb(255 255 255 / .9)'; ctx.beginPath(); ctx.ellipse(.06, -.15, .1, .045, -.2, 0, TAU); ctx.fill();
  } });
  moeFill(() => rrect(.36, -.15, .085, .3, .04), { fill: pal.c, line: pal.cLine, lw: L * .8, rim: false });
  ctx.restore();
}
// Lace cuff (stage) or ribbed sleeve cuff (practice) at the wrist; a is the forearm angle.
function moeCuff(R, wr, a, k, lw, pal, practice) {
  ctx.save(); ctx.translate(wr[0], wr[1]); ctx.rotate(a); ctx.scale(k, k);
  const L = lw / k;
  if (practice) {
    moeFill(() => rrect(-.12, -.15, .1, .3, .045), { fill: pal.ltSh, line: pal.ltLine, lw: L * .8, rim: false });
  } else {
    const fr = [[-.07, -.08], [-.02, -.11], [.03, -.125, 1], [.04, -.07], [.055, -.03, 1], [.055, .03, 1], [.04, .07], [.03, .125, 1], [-.02, .11], [-.07, .08]];
    moeFill(moeMk(fr), { fill: MOE_WH.base, line: MOE_WH.line, lw: L * .8, rim: false });
    moeFill(() => rrect(-.11, -.085, .055, .17, .025), { fill: pal.c, line: pal.cLine, lw: L * .8, rim: false });
  }
  ctx.restore();
}

// Hand in its own frame: origin wrist, +x along the forearm, unit = hand length. The thumb goes toward the body's midline.
// g: open|wave|fist|point|peace|fheart|heart|thumb|mic|flat. O.wristL/wristR rotate the hand; O.heartPop (0..1) pops the finger heart.
// Small and graceful: slender tapering fingers, a soft palm, colour-matched lines.
function hand(w, ang, size, g, sd, lw, O = {}, M = MEMBERS.TOKI) {
  const wr = O[sd < 0 ? 'wristL' : 'wristR'] ?? 0;
  const a = ang + wr * (sd < 0 ? -1 : 1);
  ctx.save(); ctx.translate(w[0], w[1]); ctx.rotate(a);
  const flip = (-Math.sin(a) * -sd) > 0 ? 1 : -1, fy = flip * (O[sd < 0 ? 'palmL' : 'palmR'] ?? 1);
  ctx.scale(size, size * fy);
  const L = lw / size;
  const parts = [];
  const F = (x0, y0, x1, y1, r = .068, x2, y2) => parts.push(() => { capsule([x0, y0], [x1, y1], r, r * .84, false); if (x2 !== undefined) capsule([x1, y1], [x2, y2], r * .84, r * .72, false); });
  const palm = (rx = .26, ry = .21, cx = .27) => parts.push(() => { ctx.moveTo(cx + rx, 0); ctx.ellipse(cx, 0, rx, ry, 0, 0, TAU); });
  parts.push(() => capsule([-.1, 0], [.16, 0], .135, .165, false));
  const gaps = [];
  switch (g) {
    case 'fist': palm(.28, .25, .3); F(.42, .19, .56, .1, .08); break;
    case 'point': palm(.26, .23, .28); F(.38, .13, .95, .13, .066); F(.33, .22, .52, .15, .076); break;
    case 'peace': palm(.26, .23, .28); F(.4, .13, .9, .33, .064); F(.43, -.02, .94, -.08, .064); F(.33, .22, .52, .12, .076); break;
    case 'thumb': palm(.28, .25, .3); F(.3, .19, .34, .68, .085); break;
    case 'fheart': palm(.28, .24, .3); F(.43, .02, .75, .29, .068); F(.24, .22, .76, .19, .072); break;
    case 'heart': palm(.26, .22, .26); F(.4, .13, .68, .19, .064, .79, .02); F(.4, -.04, .68, -.02, .064, .77, -.17); F(.24, .19, .44, .43, .074); break;
    case 'mic': palm(.28, .25, .3); break;
    case 'flat': palm(.27, .2, .28); for (let i = 0; i < 4; i++) F(.38, -.1 + i * .066, .9 - Math.abs(i - 1.3) * .03, -.1 + i * .066, .062); F(.24, .18, .5, .34, .074); gaps.push(...[0, 1, 2].map(i => [[.6, -.067 + i * .066], [.86, -.067 + i * .066]])); break;
    case 'wave': palm(.27, .23, .28); for (let i = 0; i < 4; i++) F(.42, -.13 + i * .09, .9 - Math.abs(i - 1.3) * .05, -.34 + i * .21, .062); F(.24, .2, .46, .5, .074); break;
    default: {
      palm(.26, .21, .27);
      for (let i = 0; i < 4; i++) { const y0 = -.12 + i * .075, y1 = -.13 + i * .09; F(.42, y0, .68, y1, .064, .84 - Math.abs(i - 1.2) * .05, y1 + .04); }
      F(.22, .17, .42, .38, .074);
      gaps.push(...[0, 1, 2].map(i => [[.55, -.09 + i * .082], [.76, -.07 + i * .092]]));
    }
  }
  const mk = () => { ctx.beginPath(); for (const p of parts) p(); };
  // outline behind, shifted toward the shadow (in hand-local units)
  const d = L * .55, vx = -LIGHT.x * d * size, vy = -LIGHT.y * d * size, c = Math.cos(a), s = Math.sin(a);
  ctx.save(); ctx.translate((vx * c + vy * s) / size, (-vx * s + vy * c) / (size * fy)); mk(); ctx.strokeStyle = MOE_SK.line; ctx.lineWidth = L * 2; ctx.lineJoin = 'round'; ctx.stroke(); ctx.restore();
  ctx.fillStyle = MOE_SK.base; for (const p of parts) { ctx.beginPath(); p(); ctx.fill(); }
  ctx.save(); ctx.beginPath(); parts[1](); ctx.clip(); ctx.fillStyle = MOE_SK.sh; ctx.beginPath(); ctx.ellipse(.3, -.3 * flip, .42, .15, 0, 0, TAU); ctx.fill(); ctx.restore();
  for (const [p, q] of gaps) brush([p, q], L * .8, alpha(MOE_SK.line, .55), 'mid', { min: .2 });
  if (g === 'fist' || g === 'point' || g === 'peace' || g === 'thumb') for (let i = 0; i < 3; i++) ln([[.5, -.14 + i * .1], [.6, -.14 + i * .1]], alpha(MOE_SK.line, .5), L * .9);
  if (g === 'mic') {
    ctx.save(); ctx.translate(.34, 0); ctx.rotate(-Math.PI / 2 * flip);
    moeFill(moeMk(rrPts(-.1, -.12, .2, 1.1, .07)), { fill: '#F4F0FA', fillLt: '#FFFFFF', g: [0, .4, .2], shade: '#C9C0DC', sh: .06, line: '#6A6080', lw: L, rim: false });
    moeFill(() => { ctx.beginPath(); ctx.ellipse(0, -.22, .2, .24, 0, 0, TAU); }, { fill: '#C9CEDD', fillLt: '#FFFFFF', g: [0, -.22, .2], shade: '#8A8FA6', sh: .06, line: '#5A5A70', lw: L });
    ctx.fillStyle = M.col; ctx.fillRect(-.1, .12, .2, .09);
    ctx.restore();
  }
  ctx.restore();
  if (g === 'fheart') { const k = O.heartPop ?? 1; if (k > 0) { const r = .34 * size * backOut(clamp(k), 2.5), tx = w[0] + Math.cos(a) * .6 * size + sd * .75 * size, ty = w[1] + Math.sin(a) * .6 * size - .6 * size - r * .4; moeFill(() => tracePath(heartPts(tx, ty, r, 30)), { fill: '#FF5FA2', fillLt: '#FFA8CE', g: [tx, ty, r], shade: '#D93A7C', sh: r * .2, line: '#B02A68', lw: lw * .8, rim: false }); ctx.save(); ctx.globalCompositeOperation = 'lighter'; glow(tx, ty, r * 2.5, '#FF4F9A', .35 * clamp(k)); ctx.restore(); } }
}
function headset(R) {
  const { O } = R, h = R.head, tn = clamp(O.turn ?? 0, -1, 1), pal = R.pal, L = R.lw / h.h;
  ctx.save(); headXf(h);
  const sd = tn > .25 ? -1 : 1, x0 = turnX(sd * .48, tn, .5);
  const tip = [turnX(sd * .15, tn), .44];
  brush(qbez([x0, .16], [x0 - sd * .03, .4], tip, 10), .03, '#8C82A8', 'flat');
  brush(qbez([x0, .16], [x0 - sd * .03, .4], tip, 10), .016, '#F1EDF8', 'flat');
  moeFill(() => { ctx.beginPath(); ctx.ellipse(x0, .13, .045, .07, 0, 0, TAU); }, { fill: '#F4F0FA', line: '#8C82A8', lw: L * .8, rim: false, extra: () => { ctx.fillStyle = pal.c; ctx.beginPath(); ctx.ellipse(x0, .13, .022, .04, 0, 0, TAU); ctx.fill(); } });
  moeFill(() => { ctx.beginPath(); ctx.ellipse(tip[0], tip[1], .03, .022, 0, 0, TAU); }, { fill: pal.c, line: pal.cLine, lw: L * .7, rim: false });
  ctx.restore();
}
function tearsFx(tn, k, L) {
  for (const sd of [-1, 1]) {
    const x = turnX(sd * .22, tn), y0 = .28, len = .22 + .16 * frac(T * 2.2 + (sd > 0 ? .4 : 0));
    ctx.save(); ctx.globalAlpha = .88 * k;
    brush([[x - sd * .03, y0], [x, y0 + len * .5], [x - sd * .02, y0 + len]], .055, '#B4E6FF', 'mid', { min: .55 });
    ctx.restore();
  }
}

// ---------------- back view ----------------
// The figure seen from behind, as a mirror behind her shows her: the same pose keeps its screen handedness (hL stays on screen left, so
// don't flip a reflection), and the joints, elbow sides and hair swing are the front view's. Only the layering changes (see
// backArmLayer): an arm reaching forward is hidden behind the torso, an arm out to the side is drawn over the back and under the hair,
// and a raised arm is drawn over the hair too.
function idolBack(R) {
  const { M, P, O, pelvis, rotP } = R, pal = R.pal;
  const at = (x, dy) => rotP(x, pelvis[1] + dy), dNeck = P.neckY - P.hipY;
  R.chest = at(0, dNeck); R.shoulder = sd => at(sd * P.shW, dNeck + .17); R.at = at; R.stage = (O.outfit ?? 'stage') === 'stage'; R.backView = true;
  R.swing = O.swing ?? (Math.sin(bpOf(T) * Math.PI) * .14 - (O.sway ?? 0) * .3 - R.lean * .8 + (O.jump ?? 0) * .06);
  const fL = O.fL ?? [-.3, 0], fR = O.fR ?? [.3, 0];
  for (const [sd, f] of [[-1, fL], [1, fR]]) {
    const hj = at(sd * P.hipJ, .1), { j, e } = ikOut(hj, [f[0], f[1] + P.footY - (O.jump ?? 0)], P.thigh, P.shin, sd, O.kneeIn ? -1 : (O[sd < 0 ? 'kL' : 'kR'] ?? 1));
    idolLeg(R, sd, hj, O.kneeIn ? j : moeKnee(hj, j, e), e);
  }
  const ak = (P.upper + P.fore) / 2.54, arms = [];
  for (const [sd, hh, g] of [[-1, O.hL ?? [-.9, 2.72], O.gL ?? 'fist'], [1, O.hR ?? [.9, 2.72], O.gR ?? 'fist']]) {
    const sh = R.shoulder(sd), { j, e } = ikOut(sh, [R.chest[0] + hh[0] * ak, R.chest[1] + hh[1] * ak], P.upper, P.fore, sd, O[sd < 0 ? 'eL' : 'eR'] ?? 0);
    arms.push({ sd, sh, j, e, g, layer: backArmLayer(R, j, e) });
  }
  const armsAt = layer => { for (const a of arms) if (a.layer === layer) idolArm(R, a.sd, a.sh, a.j, a.e, a.g); };
  armsAt(0);
  idolTorso(R);
  armsAt(1);
  const h = R.head, L = R.lw / h.h;
  ctx.save(); headXf(h);
  const sw = R.swing * .15;
  if (M.hair === 'long' || M.hair === 'bob') {
    // long hair lies down the back and narrows toward the ends, so arms held out to the sides show beside it
    const long = M.hair === 'long', len = long ? 2.05 * R.P.tail / 2.25 : .66, wb = long ? .42 : .6, pts = [[-.52, -.1]];
    if (long) pts.push([-.5 + sw * .3, .4]);
    pts.push([-wb + sw * .6, len * .7]);
    for (let i = 0; i <= 10; i++) { const u = i / 10, tipI = i % 2 === 0; pts.push(tipI ? [lerp(-wb * .95, wb * .95, u) + sw, len * (1 - hash2(i, 3) * .04), 1] : [lerp(-wb * .95, wb * .95, u) + sw, len * .95]); }
    pts.push([wb + sw * .6, len * .7]);
    if (long) pts.push([.5 + sw * .3, .4]);
    pts.push([.52, -.1]);
    const g = ctx.createLinearGradient(0, 0, 0, len);
    g.addColorStop(0, pal.hair); g.addColorStop(.8, pal.hair); g.addColorStop(1, long ? pal.tipA : pal.hair);
    moeFill(moeMk(pts), { fill: g, line: pal.hairLine, lw: L, shade: alpha(pal.hairSh2, .55), sh: .08, rimW: .03, extra: () => { for (let i = -3; i <= 3; i++) brush(qbez([i * .06, 0], [i * (long ? .12 : .14) + sw, len * .5], [i * (long ? .1 : .15) + sw * 1.4, len * .9], 8), L * .8, pal.hairLineS); } });
  }
  // the back of the head: a round dome with soft lock ends at the nape; strands sweep toward the ties (or fall straight)
  const tied = M.hair === 'twintails' || M.hair === 'ponytail', napeY = M.hair === 'bob' ? .6 : tied ? .36 : .46;
  const nape = [];
  for (let i = 0; i <= 18; i++) { const a = Math.PI * .96 + i / 18 * Math.PI * 1.08; nape.push([Math.cos(a) * .55, -.03 + Math.sin(a) * .57]); }
  nape.push([.55, .2]);
  for (let i = 0; i <= 10; i++) { const u = i / 10, tipI = i % 2 === 1, x = lerp(.52, -.52, u) + sw * .5, c = 1 - Math.abs(u - .5) * 2; nape.push(tipI ? [x, napeY + .04 + c * .03 + hash2(i, 5) * .02] : [x, napeY - .01 + c * .03, 1]); }
  nape.push([-.55, .2]);
  moeFill(moeMk(nape), { fill: pal.hair, fillLt: pal.hairHi, g: [0, -.1, .5], shade: alpha(pal.hairSh2, .5), sh: .07, line: pal.hairLine, lw: L, rimW: .025, extra: () => {
    if (M.hair === 'twintails') {
      brush([[0, -.5], [0, -.05]], L * 1.3, alpha(MOE_SK.sh, .9), 'end', { min: .3 });
      for (const sd of [-1, 1]) for (let i = 0; i < 4; i++) brush(qbez([sd * .03, -.46 + i * .14], [sd * (.2 + i * .03), -.34 + i * .12], [sd * .44, -.26 + i * .03], 8), L * .8, pal.hairLineS, 'mid');
      for (let i = -2; i <= 2; i++) brush(qbez([i * .1, .05], [i * .12, .2], [i * .13, napeY], 6), L * .8, pal.hairLineS, 'start');
    } else if (M.hair === 'ponytail') {
      const r = moePonyRoot(0);
      for (let i = 0; i < 6; i++) { const x0 = lerp(-.46, .3, i / 5); brush(qbez([x0, napeY - .05], [lerp(x0, r[0], .4), lerp(.1, r[1], .4)], [r[0], r[1]], 8), L * .8, pal.hairLineS, 'mid'); }
    } else for (let i = -3; i <= 3; i++) brush(qbez([i * .05, -.53], [i * .12, -.1], [i * .15, napeY], 8), L * .8, pal.hairLineS);
    hairShine(M, 0, L);
  } });
  if (M.hair === 'twintails') for (const sd of [-1, 1]) { twinTail(R, sd, 0, R.swing, L); bow(sd * .47, -.25, .15, M.col, L, -sd * .3); }
  if (M.hair === 'ponytail') ponyTail(R, 0, R.swing, L);
  ctx.restore();
  armsAt(2);
}
// Where an arm goes in the back view: 0 in front of the body (the wrist at the face or over the torso, or the elbow or forearm across
// the torso), hidden by it; 1 out to the side, over the back; 2 raised above the middle of the head, over the hair.
function backArmLayer(R, el, wr) {
  const { P, pelvis, lean } = R, c = Math.cos(lean), n = Math.sin(lean), top = P.neckY - P.hipY, h = R.head;
  const inTorso = (p, w) => { const x = p[0] - pelvis[0], y = p[1] - pelvis[1], lx = x * c + y * n, ly = -x * n + y * c; return Math.abs(lx) < w && ly > top && ly < .35; };
  const atFace = ((wr[0] - h.x) / (h.h * .5)) ** 2 + ((wr[1] - h.y) / (h.h * .56)) ** 2 < 1 && wr[1] > h.y - h.h * .25;
  if (atFace || inTorso(wr, P.shW + .06) || inTorso(el, P.shW - .1) || inTorso(moeLerp(el, wr, .5), P.shW - .05)) return 0;
  return wr[1] < h.y ? 2 : 1;
}

// ---------------- poses ----------------
// The face is bigger relative to the body than in kit.js's rig, so the poses that put a hand at the face aim a little wider or higher
// to stay beside the eye / on the cheek instead of covering the face. (Chapters that hold props compute the hand from their own
// targets and R.P, which still map exactly as before.)
Object.assign(IDOL_POSES.cheeks, { hL: [-.62, -.32], hR: [.62, -.32], wristL: -.5, wristR: -.5 });
Object.assign(IDOL_POSES.peace, { hR: [.98, -.62], wristR: -1.2 });
Object.assign(IDOL_POSES.fingerHeart, { hR: [1.0, -.4], wristR: -.9 });
Object.assign(IDOL_POSES.think, { hR: [.26, -.12], wristR: -1.9 });
Object.assign(IDOL_POSES.salute, { hR: [.7, -1.3], wristR: -.1 });
Object.assign(IDOL_POSES.shock, { hL: [-.98, -.3], hR: [.98, -.3] });
Object.assign(IDOL_POSES.facepalm, { hR: [.12, -.62] });

;
// ---- styles/idol/ch/c01_intro.js ----
// c01_intro — the 2.4 s intro as a comeback teaser, three quick cuts on the beat:
//   I1  teaser card: the ATTN! logo pops letter by letter over a night sky, "THE 1ST MINI ALBUM · WE DIDN'T START THE SCALING",
//       a lens flare sweeps across and the D-day counter reads COMEBACK D-3,389 (Jun 12 2017 → Sep 22 2026).
//   I2  the stage in darkness: four backlit silhouettes; a spotlight snaps onto each member on successive eighths, name caption popping.
//   I3  TOKI close-up whips round to camera, winks, finger heart; the heart shoots off screen right like a spark down a fuse → V1.1.
(() => {
  const snap = x => onBeat(0, Math.round(bpOf(x)));
  function plan() {
    const S = span('intro'), b1 = snap(S.start + .8), b2 = snap(S.start + 1.6);
    return { S, t2: Math.min(b1, S.end - 1.3), t3: Math.min(b2, S.end - .7) };
  }

  function shotI1(t, P) {
    const lt = t - P.S.start, d = P.t2 - P.S.start;
    bgGrad([[0, '#05020C'], [.55, IP.night], [1, IP.plum]], null);
    ctx.save(); ctx.globalAlpha = clamp(lt / .3); bokeh(t, { n: 16, r: 90, alpha: .25 }); ctx.restore();
    sparkles(t, { n: 30, r: 14, seed: 41, speed: 1.4 });
    const zoom = lerp(1.08, 1, easeOut(clamp(lt / d)));
    camBegin(960, 540, zoom);
    dtext('THE 1ST MINI ALBUM', 960, 330, 30, { font: 'mono', fill: alpha(IP.lav, clamp((lt - .1) / .2)), spacing: 14 });
    attnLogo(960, 500, 190, { pop: clamp(lt / (d * .75)), t });
    const k2 = clamp((lt - d * .45) / .2);
    dtext("WE DIDN'T START THE SCALING", 960, 680, 40, { font: 'mono', fill: alpha(IP.white, k2), strokes: [[alpha(IP.neonPink, k2 * .7), 8]], spacing: 6 });
    const k3 = clamp((lt - d * .6) / .2);
    if (k3 > 0) { const lbl = `COMEBACK D-${fmtN(dDay(segByKey('V1.1')).n)}`, w = textW(lbl, 34, 'code') + 60; ctx.save(); ctx.translate(960, 775); ctx.scale(backOut(k3, 2), backOut(k3, 2)); rrect(-w / 2, -32, w, 64, 32); ctx.fillStyle = IP.neonPink; ctx.fill(); ctx.strokeStyle = IP.white; ctx.lineWidth = 4; ctx.stroke(); dtext(lbl, 0, 2, 34, { font: 'code', fill: IP.white }); ctx.restore(); }
    camEnd();
    flare(lerp(-200, 2150, easeInOut(clamp(lt / d))), 470, 1.1);
    hideCaption();
  }
  const easeInOut = k => ease(k);

  const ORDER = [['ADA', 600], ['RELU', 1320], ['LOGI', 1640], ['TOKI', 960]];   // lit in this order; TOKI centre, last
  globalThis.IDOL_INTRO_ORDER = ORDER;   // the poster page (modelsheet.js, t = −999) respaces the members
  function shotI2(t, P) {
    const lt = t - P.t2, d = P.t3 - P.t2, step = d / 4.4;
    stageSet(t, { led: (w, h) => { ctx.fillStyle = '#05020C'; ctx.fillRect(0, 0, w, h); ctx.globalAlpha = clamp(lt / d); ledShow('logo', t, w, h); ctx.globalAlpha = 1; }, level: 1, hue: IP.lilac, beamK: .25, floorY: 690 });
    ctx.fillStyle = 'rgb(5 2 12 / .45)'; ctx.fillRect(0, 0, W, H);
    const lit = ORDER.map((_, i) => lt > i * step);
    // backlight glow behind everyone
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; glow(960, 620, 900, IP.lilac, .35); ctx.restore();
    const pose = (m, i) => ({ member: m, ...(m === 'TOKI' ? IDOL_POSES.heart : i % 2 ? IDOL_POSES.peace : IDOL_POSES.hips), expr: m === 'TOKI' ? 'love' : 'smile', blink: t + i, swing: .05 });
    // silhouettes of the not-yet-lit members
    silhouette(() => ORDER.forEach(([m, x], i) => { if (!lit[i]) idol(x, 960, 34, pose(m, i)); }), '#140828', 1);
    ORDER.forEach(([m, x], i) => {
      if (!lit[i]) return;
      const k = clamp((lt - i * step) / .12), M = MEMBERS[m];
      beam(x, 0, 0, { col: M.col, alpha: .55 * k, len: 1100, w: .1 });
      ctx.save(); ctx.globalCompositeOperation = 'lighter'; ctx.fillStyle = alpha(M.col, .35 * k); ctx.beginPath(); ctx.ellipse(x, 965, 200, 40, 0, 0, TAU); ctx.fill(); ctx.restore();
      idol(x, 960, 34, { ...pose(m, i), rim: M.col });
      nameCap(M.name, x, 540 - (m === 'TOKI' ? 70 : 0), 34 * backOut(k, 2) + .01, M.col);
    });
    hideCaption();
  }

  function shotI3(t, P) {
    const lt = t - P.t3, d = P.S.end - P.t3, k = easeOut(clamp(lt / (d * .35))), wink = lt > d * .38;
    bgGrad(IP.neonPink, IP.plum, { radial: true, cx: 960, cy: 420, r: 1200 });
    speedLines(960, 450, { r0: 460, alpha: .35 * (1 - k * .5), n: 60 });
    bokeh(t, { n: 10, r: 100, alpha: .3 });
    setLight({ rim: IP.neonCyan });
    const pop = clamp((lt - d * .45) / .15);
    idol(960, 470, 215, { anchor: 'face', ...IDOL_POSES.fingerHeart, heartPop: 0, turn: lerp(-.75, .05, k), tilt: lerp(.12, -.08, k), swing: lerp(.5, -.05, k), expr: wink ? 'wink' : 'smile', lookX: lerp(-.8, 0, k), mouth: wink ? 'tongue' : 'open' });
    // the finger heart grows, then shoots off to the right like a spark on a fuse
    if (pop > 0) {
      const fly = easeIn(clamp((lt - d * .72) / (d * .28))), hx = lerp(1330, 2150, fly), hy = lerp(260, 560, fly), r = 46 * backOut(pop, 2.5) * (1 - fly * .5);
      for (let i = 1; i < 6 && fly > 0; i++) sparkle(hx - i * 70 * fly, hy - i * 25 * fly, 18 - i * 2.5, i, IP.neonGold);
      ctx.save(); ctx.globalCompositeOperation = 'lighter'; glow(hx, hy, r * 3, '#FF4F9A', .5); ctx.restore();
      solid(heartPts(hx, hy, r, 32), '#FF4F9A', { shade: '#D02F73', sh: r * .15, line: IP.white, lw: 5 });
    }
    sparkles(t, { n: 10, x0: 200, x1: 700, y0: 100, y1: 600, r: 26, seed: 9 });
    vtag('♡ TOKI', 560, 800, { pop: clamp((lt - .1) / .2), col: 'rgb(255 255 255 / .95)' });
    hideCaption();
  }

  section('intro', (p, lt, d, t) => {
    const P = plan();
    if (t < P.t2) shotI1(t, P);
    else if (t < P.t3) shotI2(t, P);
    else shotI3(t, P);
  });
})();

;
// ---- styles/idol/ch/c02_v1.js ----
// c02_v1 — Verse 1 (Jun 2017 → Oct 2024), the "trainee era": sixteen anime / variety-show vignettes, hard-cut on each sung line.
// Palette: pink, lemon and sky, sunny; consecutive shots alternate warm/cool and wide/close/split so the cuts pop.
//   1  "Attention" lit the fuse     the intro's heart spark hits a debut-poster paper; ATTENTION → ATTN; TOKI: "that's us!"
//   2  scaling laws you can't refuse JARED holds out a trainee contract with a dead-straight log-log chart; RELU signs with heart eyes
//   3  Gwern: stack the compute high the hooded, "?"-badged GWERN yells MORE!! as A100s rain onto a wobbling tower; camera tilts up
//   4  few-shot learners multiply    split: GPT-3 flunks 23 × 47 (BZZT, 29%) | agents multiply 1 → 32 on eighths
//   5  ChatGPT, overnight            TOKI asleep; her phone's user counter rolls 1 → 100M as night jumps to sunrise; she bolts upright
//   6  Sydney gave Roose a fright     horror-blue: SYDNEY crawls out of the phone with heart eyes; KEVIN petrified; "5 TURNS MAX"
//   7  six-month pause               hands mash a giant PAUSE; the progress bar rolls on; ATTN! run on treadmills (nowhere fast)
//   8  Eliezer's shut-it-down blast  megaphone blast pops the stage lights one by one; "SHUT IT ALL DOWN" slams into camera
//   9  Sam fired, then rehired       an idol "graduation" (bouquet, TOKI sobbing); out the door… 5 DAYS LATER he boings back in
//  10  weekend chaos, board expired  calendar rips FRI→TUE; the BOARD plank snaps and its sitters drop; hanko: EXPIRED
//  11  Ilya saw what Ilya saw        extreme close-up: the steep curve reflected in ILYA's eye; then he tiptoes off with an SSI box
//  12  EU writes the AI law          the AI ACT rulebook slams down in a ring of gold stars; the members get risk-category stickers
//  13  Strawberry thinks link by link o1-the-strawberry counts the R's in STRAWBERRY one chain link at a time → "3!"
//  14  Newsom vetoes, doesn't blink  split-screen staring contest: GAVIN vs. SB 1047; the bill blinks; VETO hanko
//  15  Hinton takes his medal, scolds music-show 1st WIN for GEOFF; he wags a finger "BE CAREFUL!" and the confetti freezes mid-air
//  16  Demis wins for protein folds  DEMIS folds a ribbon into a protein that snaps into a NOBEL medal; ATTN! do the arm-roll
(() => {
  // ---------------- private helpers ----------------
  const fill = c => { ctx.fillStyle = c; ctx.fillRect(-400, -400, W + 800, H + 800); };
  // lt of the k-th beat at/after the window start (verse lines often start on an off-beat pickup), and the same for eighths.
  const bl = (t, lt, k) => { const s = t - lt; return onBeat(0, Math.ceil(bpOf(s) - .04) + k) - s; };
  const el = (t, lt, k) => { const s = t - lt; return onBeat(0, (Math.ceil(bpOf(s) * 2 - .08) + k) / 2) - s; };
  const pk = (lt, t0, dur = .18) => clamp((lt - t0) / dur);
  // entrance: a quick zoom settle (< .15 s) folded into the shot's own camera
  const enter = (lt, cx = W / 2, cy = H / 2, zoom = 1, rot = 0) => { const k = easeOut(clamp(lt / .13)); camBegin(cx, cy, zoom * (1 + .06 * (1 - k)), rot); };
  // the same, but zooming about a fixed screen point (px, py) instead of the frame centre (for panels)
  const enterAt = (lt, px, py, zoom = 1) => { const z = zoom * (1 + .06 * (1 - easeOut(clamp(lt / .13)))); camBegin(px - (px - W / 2) / z, py - (py - H / 2) / z, z); };
  const flash = (lt, t0, dur = .16, a = .7, col = '255 250 255') => { const k = (lt - t0) / dur; if (k >= 0 && k < 1) { ctx.fillStyle = `rgb(${col} / ${(a * (1 - k) ** 2).toFixed(3)})`; ctx.fillRect(-400, -400, W + 800, H + 800); } };
  const add = fn => { ctx.save(); ctx.globalCompositeOperation = 'lighter'; fn(); ctx.restore(); };
  // hand position of an idol() rig in world coords (for props held in a hand), given the call's x, y, s and hand target
  const handAt = (R, x, y, s, h) => { const P = R.P, ak = (P.upper + P.fore) / 2.54; return [x + (R.chest[0] + h[0] * ak) * s, y + (R.chest[1] + h[1] * ak) * s]; };
  // a burning fuse spark
  const spark = (x, y, r, t) => {
    add(() => { glow(x, y, r * 4, IP.neonGold, .7); glow(x, y, r * 1.6, IP.white, .9); });
    for (let i = 0; i < 7; i++) { const a = hash2(_boil, i) * TAU, l = r * (1.2 + hash2(i, _boil) * 1.6); ln([[x, y], [x + Math.cos(a) * l, y + Math.sin(a) * l]], i % 2 ? IP.neonGold : IP.white, 3); }
    sparkle(x, y, r * 1.4, t * 5, IP.white);
  };
  // a simple cartoon hand (skin mitten with a pointing finger) for crowds of pressing / wagging hands
  const pokeHand = (x, y, sz, ang, o = {}) => {
    ctx.save(); ctx.translate(x, y); ctx.rotate(ang);
    const sk = o.skin ?? IP.skin, sl = IP.skinLine;
    solid(rrPts(-sz * .45, sz * .15, sz * .9, sz * 1.6, sz * .3), o.sleeve ?? IP.lilac, { shade: false, line: IP.line, lw: sz * .08, sharp: true });
    solid(ellPts(0, 0, sz * .55, sz * .5, 18), sk, { shade: IP.skinSh, sh: sz * .08, line: sl, lw: sz * .08 });
    solid(rrPts(-sz * .14, -sz * .95, sz * .28, sz * .75, sz * .14), sk, { shade: false, line: sl, lw: sz * .07, sharp: true });
    ctx.restore();
  };

  // =====================================================================================================
  // V1.1  First, "Attention" lit the fuse   (JUN 2017 · TOKI)
  // =====================================================================================================
  const WORD = 'ATTENTION', KEEP = [1, 1, 1, 0, 1, 0, 0, 0, 0];     // A T T _ N → ATTN
  const AUTH = [['short', '#3B2A2E', 0], ['curly', '#2A1E1A', 3], ['side', '#6A4A2E', 1], ['bob', '#1E1A26', 5], ['messy', '#8A5A3A', 2], ['buzz', '#2A2228', 4], ['long', '#C88A4A', 0], ['spiky', '#3A2A20', 1]];
  function poster(t, lt, b1) {
    const w = 580, h = 610, glowK = clamp(lt / .25);
    ctx.save(); ctx.translate(1150, 455); ctx.rotate(-.015);
    add(() => glow(0, 0, 520, IP.lemon, .55 * glowK + .12 * pulse(t, 4)));
    solid(rrPts(-w / 2, -h / 2, w, h, 26), IP.white, { shade: '#FBE3EF', sh: 14, line: IP.line, lw: 6, sharp: true, dropShadow: [12, 16] });
    ctx.save(); rrect(-w / 2 + 14, -h / 2 + 14, w - 28, h - 28, 18); ctx.lineWidth = 6; ctx.strokeStyle = IP.pink; ctx.stroke(); ctx.restore();
    rrect(-170, -h / 2 + 34, 340, 44, 22); ctx.fillStyle = IP.neonPink; ctx.fill();
    dtext('NEW PAPER · 2017.06.12', 0, -h / 2 + 57, 22, { font: 'code', fill: IP.white });
    // ATTENTION, letter by letter; on the beat the A-T-T-N letters light up pink and slide together into "ATTN!", the rest fall away
    const size = 92, ws = [...WORD].map(c => textW(c, size, 'rammetto') * .98), tot = ws.reduce((a, b) => a + b, 0), sc = Math.min(1, 510 / tot);
    const hk = clamp((lt - b1) / .16), slide = easeOut(clamp((lt - b1 - .08) / .2)), bangW = 40;
    const keptW = ws.reduce((a, v, i) => a + (KEEP[i] ? v * 1.08 : 0), 0) + bangW;
    let x = -tot * sc / 2, kx = -keptW / 2;
    [...WORD].forEach((c, i) => {
      const ox = x + ws[i] * sc / 2; x += ws[i] * sc;
      const keep = KEEP[i], bounce = keep ? backOut(clamp((lt - b1 - i * .025) / .18), 3) : 0;
      let cx = ox;
      if (keep) { cx = lerp(ox, kx + ws[i] * .54, slide); kx += ws[i] * 1.08; }
      const fall = keep ? 0 : easeIn(clamp((lt - b1) / .4));
      ctx.save(); ctx.translate(cx, -150 + (keep ? -14 * bounce * (1 - slide) + 6 * slide + Math.sin((bpOf(t) - i * .15) * Math.PI) * 3 * hk : 16 * hk + fall * 260)); ctx.rotate(keep ? 0 : fall * (i % 2 ? .7 : -.6));
      const z = keep ? lerp(sc, 1.02, slide) * (1 + .1 * bounce * (1 - slide)) : sc; ctx.scale(z, z);
      const on = keep && hk > 0;
      dtext(c, 0, 0, size, { grad: on ? ['#FFFFFF', '#FFB0DA', '#FF3DA8'] : ['#B9A3FF', '#7B5BE0'], strokes: [[IP.white, 20], [on ? '#6A1447' : IP.line, 9]], alpha: keep ? 1 : (1 - .7 * hk) * (1 - fall) });
      ctx.restore();
    });
    const bk = backOut(clamp((lt - b1 - .25) / .18), 3);
    if (bk > 0) { ctx.save(); ctx.translate(kx + bangW / 2, -150); ctx.scale(bk, bk); ctx.rotate(.12); dtext('!', 0, -4, size * 1.05, { grad: ['#FFF6B0', IP.neonGold], strokes: [[IP.white, 20], ['#6A1447', 9]] }); ctx.restore(); }
    dtext('IS ALL YOU NEED', 0, -60, 46, { fill: IP.ink, alpha: 1 - .5 * hk });
    // a little attention heat-map, pulsing on the beat
    const n = 7, cell = 30, gx = -n * cell / 2, gy = -8;
    for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) {
      const v = clamp((i === j ? .9 : 0) + hash2(i * 7 + j, 3) * .55 * (j <= i ? 1 : .35) + .15 * pulse(t - (i + j) * .03, 5));
      ctx.fillStyle = mixCol('#FFF0F7', '#FF3DA8', v); ctx.fillRect(gx + j * cell + 1, gy + i * cell + 1, cell - 2, cell - 2);
    }
    ctx.strokeStyle = IP.line; ctx.lineWidth = 3; ctx.strokeRect(gx, gy, n * cell, n * cell);
    dtext('feat. 8 AUTHORS', 0, h / 2 - 50, 34, { font: 'marker', fill: IP.violet });
    ctx.restore();
  }
  line('V1', 1, (p, lt, d, t) => {
    const b0 = bl(t, lt, 0), b1 = bl(t, lt, 1), b2 = bl(t, lt, 2);
    rays(1150, 440, 22, '#FFE0EE', '#FFF3C4', t * .12);
    add(() => glow(1150, 440, 900, IP.white, .35));
    enter(lt, 960, 540, 1 + p * .03);
    // floor
    ctx.fillStyle = '#FBC8DF'; ctx.fillRect(-400, 860, W + 800, 400); ctx.fillStyle = '#FFDDEB'; ctx.fillRect(-400, 860, W + 800, 14);
    // easel legs
    ln([[1000, 700], [930, 900]], '#B98AD8', 16); ln([[1300, 700], [1370, 900]], '#B98AD8', 16); ln([[1150, 700], [1150, 890]], '#9C74C4', 12);
    // the fuse: lit at the easel foot on the downbeat, the spark running off to the right
    const F = crSample([[1150, 890], [1290, 925], [1450, 900], [1610, 945], [1790, 915], [2020, 950]], 12, []);
    ln(F, '#C9A27A', 10); ln(F, '#E8C9A0', 4);
    const fk = clamp((lt - b0) / (d - b0 + .2));
    if (lt > b0) {
      const burnt = partial(F, fk * .85); ln(burnt, '#4A3A48', 11);
      const tip = burnt.at(-1); spark(tip[0], tip[1], 16 + 4 * pulse2(t, 6), t);
    }
    // eight authors peeking over the poster
    AUTH.forEach(([hair, hc, sk], i) => {
      const x = 905 + i * 70, bob = Math.max(0, Math.sin((bpOf(t) * 2 - i * .37) * Math.PI)) * 9 + (1 - clamp(lt / .3)) * 30;
      chibi(x, 222 - bob, 12, { hair, hairCol: hc, skin: sk, eyes: lt > b1 ? 'spark' : i % 3 ? 'wide' : 'dot', mouth: i % 2 ? 'O' : 'smile', glasses: i === 2 || i === 5, top: 'labcoat', shadow: false, blush: .6 });
    });
    poster(t, lt, b1);
    AUTH.forEach((_, i) => { const x = 905 + i * 70; for (const sd of [-1, 1]) solid(ellPts(x + sd * 18, 164, 9, 8, 12), CHIBI_SKIN[AUTH[i][2]], { shade: false, line: IP.skinLine, lw: 2.5 }); });
    // TOKI pops up: "that's us!"
    const tk = backOut(clamp((lt - b1 + .05) / .22), 1.6);
    if (tk > 0) {
      const wink = lt > b2;
      idol(430, 930 + (1 - tk) * 420, 36, { sd: 1, hR: [3.5, -.25 - .2 * pulse(t, 5)], gR: 'point', hL: [-.72, 1.5], gL: 'fist', expr: wink ? 'wink' : 'joy', bob: .15 * pulse(t, 5), tilt: -.08 + Math.sin(bpOf(t) * Math.PI) * .05, blink: t });
    }
    // the heart spark from the intro streaks in from the left and hits the poster
    if (lt < b0 + .05) {
      const k = clamp(lt / b0), hx = lerp(40, 1130, k), hy = lerp(560, 290, k) - Math.sin(k * Math.PI) * 120;
      for (let i = 1; i < 6; i++) sparkle(hx - i * 60, hy + i * 12, 16 - i * 2, i, IP.neonGold);
      add(() => glow(hx, hy, 110, '#FF4F9A', .6));
      solid(heartPts(hx, hy, 40, 32), '#FF4F9A', { shade: '#D02F73', sh: 6, line: IP.white, lw: 5 });
    }
    if (lt > b0) { const a = lt - b0; for (let i = 0; i < 8; i++) { const ang = i / 8 * TAU + .2, r = 60 + a * 700; if (a < .4) sparkle(1150 + Math.cos(ang) * r, 300 + Math.sin(ang) * r * .7, 26 * (1 - a / .4), ang, i % 2 ? IP.neonGold : IP.white); } }
    camEnd();
    flash(lt, b0, .14, .65);
  });

  // =====================================================================================================
  // V1.2  Scaling laws you can't refuse   (JAN 2020 · RELU)
  // =====================================================================================================
  function contract(t, lt, b1, b2) {
    const w = 540, h = 640;
    ctx.save(); ctx.translate(1010 + 420 * (1 - easeOut(clamp(lt / .14))), 470); ctx.rotate(.02);
    solid(rrPts(-w / 2, -h / 2, w, h, 16), IP.cream, { shade: '#EFE2D8', sh: 12, line: IP.line, lw: 6, sharp: true, dropShadow: [14, 18] });
    ctx.save(); rrect(-w / 2, -h / 2, w, h, 16); ctx.clip(); ctx.fillStyle = IP.neonPink; ctx.fillRect(-w / 2, -h / 2, w, 84); ctx.restore();
    dtext('TRAINEE CONTRACT', 0, -h / 2 + 44, 40, { fill: IP.white, strokes: [['#B02070', 6]] });
    dtext('§1  SCALING LAWS', -w / 2 + 40, -h / 2 + 124, 30, { font: 'archivo', fill: IP.ink, align: 'left' });
    // log-log chart: a dead-straight line
    const cx0 = -200, cy0 = 150, cw = 400, ch = 250;
    ctx.fillStyle = IP.white; ctx.fillRect(cx0, cy0 - ch, cw, ch);
    ctx.strokeStyle = 'rgb(90 60 120 / .18)'; ctx.lineWidth = 2; ctx.beginPath();
    for (let i = 1; i < 4; i++) for (let j = 1; j < 10; j++) { const u = (i - 1 + Math.log10(j)) / 3; ctx.moveTo(cx0 + u * cw, cy0); ctx.lineTo(cx0 + u * cw, cy0 - ch); const v = (i - 1 + Math.log10(j)) / 3; ctx.moveTo(cx0, cy0 - v * ch); ctx.lineTo(cx0 + cw, cy0 - v * ch); }
    ctx.stroke();
    ln([[cx0, cy0 - ch - 6], [cx0, cy0], [cx0 + cw + 6, cy0]], IP.line, 5);
    dtext('LOSS', cx0 + 10, cy0 - ch + 18, 20, { font: 'code', fill: IP.inkSoft, align: 'left' });
    dtext('COMPUTE →', cx0 + cw, cy0 + 22, 20, { font: 'code', fill: IP.inkSoft, align: 'right' });
    const lk = clamp((lt - .1) / .5), L = partial([[cx0 + 20, cy0 - ch + 40], [cx0 + cw - 20, cy0 - 30]], lk);
    add(() => ln(L, alpha(IP.neonPink, .35 + .25 * pulse(t, 4)), 22));
    ln(L, IP.neonPink, 8);
    for (let i = 0; i < 7; i++) { const u = i / 6; if (u > lk) break; const px = cx0 + 20 + u * (cw - 40), py = cy0 - ch + 40 + u * (ch - 70); solid(ellPts(px + jit(1), py, 8, 8, 10), IP.white, { shade: false, line: IP.neonPink, lw: 3 }); }
    rrect(cx0 + cw - 128, cy0 - ch + 10, 118, 34, 17); ctx.fillStyle = IP.neonCyan; ctx.fill();
    dtext('LOG-LOG', cx0 + cw - 69, cy0 - ch + 28, 18, { font: 'code', fill: IP.ink });
    // signature line
    dtext('✗', -w / 2 + 50, 250, 34, { fill: IP.red });
    ln([[-w / 2 + 80, 268], [w / 2 - 50, 268]], IP.line, 3);
    const sk = clamp((lt - b1) / .35);
    if (sk > 0) {
      ctx.save(); ctx.beginPath(); ctx.rect(-w / 2 + 80, 170, 380 * sk, 110); ctx.clip();
      dtext('♡ relu', -w / 2 + 100, 240, 58, { font: 'marker', fill: MEMBERS.RELU.col, align: 'left', rot: -.06 });
      ctx.restore();
      if (sk < 1) sparkle(-w / 2 + 80 + 380 * sk, 240, 26, t * 6, IP.neonGold);
    }
    if (lt > b2) { const a = lt - b2; for (let i = 0; i < 5; i++) sparkle(-60 + i * 70, 200 - a * 90 - (i % 2) * 30, 18 * clamp(1 - a * 1.2), i, i % 2 ? IP.neonGold : IP.white); }
    ctx.restore();
  }
  line('V1', 2, (p, lt, d, t) => {
    const b1 = bl(t, lt, 1), b2 = bl(t, lt, 2);
    bgGrad('#DDF4FF', IP.sky);
    patternBG('grid', 'rgb(0 0 0 / 0)', 'rgb(255 255 255 / .55)', { cell: 90, dx: t * 12 });
    enter(lt, 960, 540, 1 + p * .025);
    // desk
    solid(rrPts(-60, 800, W + 120, 400, 20), '#FFE7C8', { shade: false, line: IP.line, lw: 6, sharp: true });
    ctx.fillStyle = '#F2CFA2'; ctx.fillRect(-60, 830, W + 120, 16);
    // JARED holds out the contract
    contract(t, lt, b1, b2);
    const jx = 1440 + 420 * (1 - easeOut(clamp(lt / .14)));
    chibi(jx, 880, 40, { name: 'JARED', hair: 'short', hairCol: '#4A3226', skin: 0, top: 'suit', topCol: '#3A4A7A', tie: IP.neonPink, eyes: 'smug', mouth: 'smirk', aL: .12 + .04 * Math.sin(t * 6), aR: -1.2, tagCol: IP.neonCyan, blush: .3 });
    // RELU: heart eyes, big pen, signs instantly
    const hR = [.55, -.1], R = idol(420, 930, 38, { sd: 1, member: 'RELU', expr: 'love', hR, gR: 'fist', hL: [-.62, .6], gL: 'fist', jump: .35 * pulse(t, 5), tilt: .08 * Math.sin(bpOf(t) * Math.PI), blink: t });
    const [px, py] = handAt(R, 420, 930, 38, hR), wig = lt > b1 && lt < b1 + .35 ? Math.sin(lt * 60) * .25 : 0;
    ctx.save(); ctx.translate(px, py); ctx.rotate(.55 + wig);
    solid(rrPts(-13, -120, 26, 150, 12), IP.neonPink, { shade: '#C0206A', sh: 5, line: IP.line, lw: 4, sharp: true });
    solid([[-13, 30], [13, 30], [0, 68, 1]], IP.gold, { shade: false, line: IP.line, lw: 4 });
    solid(heartPts(0, -130, 22, 24), IP.white, { shade: false, line: IP.line, lw: 3 });
    ctx.restore();
    if (lt > b1) sparkle(px + 40, py + 60, 24 * pulse2(t, 5) + 6, t * 4, IP.neonGold);
    camEnd();
    vcap("AN OFFER YOU CAN'T REFUSE", 960, 108, { style: 'yellow', size: 52, pop: pk(lt, b1 * .5 + .05, .22), rot: -.03 });
  });

  // =====================================================================================================
  // V1.3  Gwern said "stack the compute high,"   (MAY 2020 · ADA)
  // =====================================================================================================
  line('V1', 3, (p, lt, d, t) => {
    const n0 = 3, S = 22, CH = 5.2 * S, base = 905, tx = 1010;
    const land = [.1]; for (let k = 1; k < 12; k++) { const x = el(t, lt, k); if (x > .15 && x < d - .05) land.push(x); }
    const landed = land.filter(x => lt >= x).length, total = n0 + landed;
    // the camera tilts up after the tower (a little: GWERN's face must stay above the caption band)
    const cy = 540 - 190 * ease(clamp((lt - .2) / (d - .2)));
    bgGrad([[0, '#FFFBE6'], [1, '#FFE27A']], null, { y0: -300, y1: 1100 });
    patternBG('polka', 'rgb(0 0 0 / 0)', 'rgb(255 255 255 / .5)', { cell: 110, dy: -t * 20 });
    enter(lt, 960, cy, 1);
    ctx.fillStyle = '#F7C95A'; ctx.fillRect(-400, base, W + 800, 600); ctx.fillStyle = '#FFE08A'; ctx.fillRect(-400, base, W + 800, 12);
    // the pinned essay
    docCard(1560, 560, 310, 400, { title: 'THE SCALING HYPOTHESIS', head: IP.violet, body: ['by gwern', 'bigger = smarter?'], lines: 4, rot: .05 });
    solid(ellPts(1560, 370, 16, 16, 14), IP.red, { shade: false, line: IP.line, lw: 3 });
    // the tower: each chip wobbles more the higher it sits
    const sway = Math.sin(t * 5.5) * .5 + Math.sin(t * 8.3) * .25;
    const px = i => tx + Math.sin(i * 1.9) * 16 + sway * i * 2.6;
    for (let i = 0; i < total; i++) {
      const lk = i >= n0 ? clamp((lt - land[i - n0]) / .25) : 1, sq = i >= n0 ? Math.sin(lk * Math.PI) * .14 * (1 - lk) : 0;
      ctx.save(); ctx.translate(px(i), base - (i + .5) * CH); ctx.rotate(sway * i * .006 + (hash(i) - .5) * .06); ctx.scale(1 + sq, 1 - sq);
      gpuChip(0, 0, S, { label: 'A100', hot: i === total - 1 ? .5 : 0 });
      ctx.restore();
    }
    // the next chip dropping in from above
    const next = land.find(x => x > lt);
    if (next !== undefined && next - lt < .16) {
      const k = 1 - (next - lt) / .16, y = base - (total + .5) * CH - (1 - k * k) * 420;
      gpuChip(px(total), y, S, { label: 'A100', rot: (1 - k) * .4 });
      for (let j = 0; j < 3; j++) ln([[px(total) - 80 + j * 80, y - 100], [px(total) - 80 + j * 80, y - 230]], alpha(IP.white, .9), 7);
    }
    for (let k = 0; k < landed; k++) { const a = lt - land[k]; if (a < .3) { const y = base - (n0 + k) * CH; for (const sd of [-1, 1]) sparkle(px(n0 + k) + sd * (130 + a * 420), y - a * 60, 24 * (1 - a / .3), 0, IP.white); } }
    // GWERN, hooded and pseudonymous, demanding more
    const shout = pulse(t, 5);
    chibi(430, 900, 37, { name: '?', hair: 'hood', hairCol: '#4A4458', top: 'hoodie', topCol: '#4A4458', eyes: 'shades', mouth: 'open', aL: .25 + .3 * shout, aR: .45 + .3 * shout, jump: 1.2 * shout, tagCol: IP.violet, rot: -.04 });
    for (let i = 0; i < 5; i++) { const a = -2.4 + i * .3, r0 = 150 + 20 * shout; ln([[430 + Math.cos(a) * r0, 640 + Math.sin(a) * r0], [430 + Math.cos(a) * (r0 + 50), 640 + Math.sin(a) * (r0 + 50)]], IP.red, 7); }
    camEnd();
    vcap('MORE!!', 420 + jit(2), 380 + (540 - cy), { style: 'shock', size: 104, pop: pk(lt, .04, .16), rot: -.08, icon: 'bang' });
  });

  // =====================================================================================================
  // V1.4  Few-shot learners multiply.   (MAY 2020 · LOGI)
  // =====================================================================================================
  line('V1', 4, (p, lt, d, t) => {
    const b1 = bl(t, lt, 1), buzz = lt > b1;
    const e = k => el(t, lt, k);
    let count = 1; for (let j = 1; j <= 5; j++) if (lt >= e(j)) count = 2 ** j;
    splitPanels(2, (i, x, y, w, h) => {
      if (i === 0) {
        bgGrad(IP.lav, IP.lilac);
        patternBG('check', 'rgb(0 0 0 / 0)', 'rgb(255 255 255 / .28)', { cell: 120 });
        enterAt(lt, 400, 540, 1);
        // flash card
        ctx.save(); ctx.translate(540, 235); ctx.rotate(-.04);
        solid(rrPts(-230, -110, 460, 220, 22), IP.white, { shade: '#E8E0F8', sh: 10, line: IP.line, lw: 6, sharp: true, dropShadow: [10, 14] });
        dtext('23 × 47 = ?', 0, 6, 70, { fill: IP.ink });
        ctx.restore();
        mascotBot(250, 905, 40, { label: 'GPT-3', col: '#CFE0FF', face: buzz ? 'spiral' : 'happy', mouth: buzz ? 'wavy' : 'open', aR: .5, sweat: buzz ? 1 : 0, jump: buzz ? 0 : 3 * pulse(t, 6), rot: buzz ? jit(.02) : 0 });
        rrect(180, 700, 140, 44, 22); ctx.fillStyle = IP.violet; ctx.fill(); dtext('175B', 250, 723, 26, { font: 'code', fill: IP.white });
        // its answer
        chatBubble('1,061!', 440, 450, { size: 58, pop: pk(lt, .05, .15), col: IP.white });
        if (buzz) {
          const a = pk(lt, b1, .12);
          ctx.save(); ctx.translate(820, 450); ctx.scale(backOut(a, 3), backOut(a, 3)); ln([[-55, -55], [55, 55]], IP.red, 24); ln([[55, -55], [-55, 55]], IP.red, 24); ctx.restore();
          sfx('BZZT!', 610, 640, { size: 96, pop: a, grad: ['#FFFFFF', '#FF9AA6', '#FF4B5C'], rot: -.1, shake: 5 });
          ctx.save(); ctx.translate(150, 190); ctx.rotate(-.18); const sk = backOut(pk(lt, b1 + .2, .15), 3); ctx.scale(sk, sk);
          solid(ellPts(0, 0, 110, 110, 36), IP.neonGold, { shade: '#E0A020', sh: 10, line: IP.line, lw: 6 });
          dtext('29%', 0, -14, 64, { fill: IP.ink }); dtext('CORRECT', 0, 44, 26, { fill: IP.ink });
          ctx.restore();
        }
        camEnd();
      } else {
        bgGrad('#E4F7FF', IP.sky);
        patternBG('polka', 'rgb(0 0 0 / 0)', 'rgb(255 255 255 / .5)', { cell: 90, dx: -t * 40 });
        // agents dividing like cells: slot i is born from slot i − 2^(j−1) on eighth j
        const cols = 8, sx = 1060, sy = 540, gx = 104, gy = 118;
        const slot = i => { const c = i % cols, r = Math.floor(i / cols); return [sx + c * gx + (r % 2) * 40, sy + r * gy]; };
        for (let i = 0; i < count; i++) {
          const j = i === 0 ? 0 : Math.floor(Math.log2(i)) + 1, born = e(j), a = clamp((lt - born) / .14);
          const par = slot(i - (j ? 2 ** (j - 1) : 0)), me = slot(i), k = easeOut(a);
          const px = lerp(par[0], me[0], k), py = lerp(par[1], me[1], k) - Math.sin(k * Math.PI) * 40;
          miniAgent(px, py, 30 * (.7 + .3 * backOut(a, 2)), { walk: bpOf(t) + i * .3, eyes: ['happy', 'star', 'dot', 'heart'][i % 4], bar: [IP.neonPink, IP.neonCyan, IP.violet, IP.neonGold][hash(i) * 4 | 0] });
        }
        const lbl = `×${count}`;
        dtext(lbl, 1480, 250, 150, { grad: ['#FFFFFF', '#6FF0FF', '#2A9ADF'], strokes: [[IP.white, 40], ['#123A6A', 20]], shadow: [6, 10, 'rgb(20 8 40 / .35)'], rot: -.05 });
      }
    }, { slant: 140, cols: [IP.lilac, IP.neonCyan] });
  });

  // =====================================================================================================
  // V1.5  ChatGPT, overnight,   (NOV 30 2022 · TOKI)
  // =====================================================================================================
  function nightcapBot(x, y, s, o = {}) {
    mascotBot(x, y, s, { col: '#BFF3E4', label: 'ChatGPT', face: o.face ?? 'happy', mouth: 'open', aR: o.aR ?? .9, antenna: false, blush: .6, ...o });
    ctx.save(); ctx.translate(x, y - 9.6 * s); ctx.rotate(.25);
    solid([[-2.6 * s, 0], [2.4 * s, 0], [3.8 * s, 2.2 * s, 1]], '#7B8CFF', { shade: false, line: IP.line, lw: s * .12, sharp: true });
    solid([[-2.6 * s, .1 * s], [2.4 * s, .1 * s], [.2 * s, -3 * s, 1]], '#7B8CFF', { shade: '#5A66D0', sh: s * .3, line: IP.line, lw: s * .12 });
    solid(ellPts(.2 * s, -3.1 * s, .6 * s, .6 * s, 12), IP.white, { shade: false, line: IP.line, lw: s * .1 });
    solid(rrPts(-2.8 * s, -.3 * s, 5.4 * s, .9 * s, .4 * s), IP.white, { shade: false, line: IP.line, lw: s * .1, sharp: true });
    ctx.restore();
  }
  line('V1', 5, (p, lt, d, t) => {
    const b0 = bl(t, lt, 0), b1 = bl(t, lt, 1), b2 = bl(t, lt, 2);
    // the sky jumps night → dawn → morning on the beats
    const steps = [b0, b1, b2].filter(x => x <= lt), last = steps.length ? steps.at(-1) : -1;
    const dayS = clamp((steps.length - 1 + easeOut(clamp((lt - last) / .15))) / 3);
    enter(lt, 960, 540, 1.02);
    fill(mixCol('#3A2E6A', '#F3E8FF', dayS));
    patternBG('stars', 'rgb(0 0 0 / 0)', alpha(IP.white, .25 + .2 * dayS), { cell: 120 });
    // window
    const wx = 170, wy = 110, ww = 700, wh = 500;
    ctx.save(); rrect(wx, wy, ww, wh, 20); ctx.clip();
    bgGrad([[0, mixCol('#0B1240', '#FF9ECB', dayS)], [.7, mixCol('#27307A', '#FFD6A0', dayS)], [1, mixCol('#3A3A90', '#FFF1A6', dayS)]], null, { y0: wy, y1: wy + wh });
    for (let i = 0; i < 18; i++) sparkle(wx + hash2(i, 1) * ww, wy + hash2(i, 2) * wh * .7, 10 * (1 - dayS) * (.6 + .4 * Math.sin(t * 5 + i)), 0, IP.white, { glow: false });
    if (dayS < .7) { const a = 1 - dayS / .7; ctx.save(); ctx.globalAlpha = a; solid(ellPts(690, 230, 60, 60, 30), '#FFF6C8', { shade: false, line: false }); ctx.fillStyle = mixCol('#0B1240', '#FF9ECB', dayS); ctx.beginPath(); ctx.arc(715, 212, 56, 0, TAU); ctx.fill(); ctx.restore(); }
    const sunY = lerp(wy + wh + 120, wy + 260, dayS);
    add(() => glow(470, sunY, 300, '#FFE08A', .8 * dayS));
    solid(ellPts(470, sunY, 90, 90, 30), '#FFD23F', { shade: false, line: '#E09A20', lw: 5 });
    ctx.restore();
    solid(rrPts(wx - 16, wy - 16, ww + 32, wh + 32, 26), 'rgb(0 0 0 / 0)', { shade: false, line: IP.white, lw: 22, sharp: true });
    ln([[wx + ww / 2, wy], [wx + ww / 2, wy + wh]], IP.white, 14); ln([[wx, wy + wh / 2], [wx + ww, wy + wh / 2]], IP.white, 14);
    for (const sd of [-1, 1]) solid(sd < 0 ? [[wx - 70, wy - 40], [wx + 70, wy - 40], [wx + 10, wy + wh + 60], [wx - 70, wy + wh + 60]] : [[wx + ww - 70, wy - 40], [wx + ww + 70, wy - 40], [wx + ww + 70, wy + wh + 60], [wx + ww - 10, wy + wh + 60]], '#FF9CCB', { shade: '#E3669F', sh: 16, line: IP.line, lw: 5, sharp: true });
    // bed
    solid(rrPts(170, 540, 100, 400, 30), '#C9B6FF', { shade: '#9C84E0', sh: 12, line: IP.line, lw: 6, sharp: true });
    solid(rrPts(200, 780, 880, 170, 26), IP.white, { shade: '#E0D8F0', sh: 12, line: IP.line, lw: 6, sharp: true });
    solid(ellPts(360, 760, 125, 52, 24), IP.white, { shade: '#E6DEF4', sh: 10, line: IP.line, lw: 5 });
    // TOKI: asleep, then bolt upright on the downbeat
    const up = backOut(clamp((lt - b2) / .16), 1.6), rot = lerp(-1.5, -.04, up), S = 44;
    ctx.save(); ctx.translate(560, 785); ctx.rotate(rot);
    idol(0, 3.28 * S, S, up > 0 ? { sd: 1, ...IDOL_POSES.shock, expr: 'sparkle', ahoge: 'bang', mouth: 'O', swing: -.2, blink: undefined } : { sd: 1, expr: 'sleepy', hL: [-.6, 1.4], hR: [.5, .9], swing: .02, emote: 'zzz', emoteK: .6 + .4 * Math.sin(t * 4) });
    ctx.restore();
    if (up > 0) for (let i = 0; i < 7; i++) { const a = -Math.PI / 2 + (i - 3) * .32, r0 = 290 + 30 * up; ln([[560 + Math.cos(a) * r0, 560 + Math.sin(a) * r0], [560 + Math.cos(a) * (r0 + 60 * up), 560 + Math.sin(a) * (r0 + 60 * up)]], IP.neonPink, 8); }
    // blanket
    solid([[520, 705], [1050, 695], [1085, 940, 1], [500, 945, 1]], '#FFB3D6', { shade: '#F08CBC', sh: 20, line: IP.line, lw: 6, sharp: true });
    ctx.save(); tracePath([[520, 705], [1050, 695], [1085, 940], [500, 945]]); ctx.clip(); patternBG('hearts', 'rgb(0 0 0 / 0)', 'rgb(255 255 255 / .6)', { cell: 90 }); ctx.restore();
    // night: the room is dark until the sun comes up
    ctx.fillStyle = `rgb(20 16 70 / ${(.5 * (1 - dayS)).toFixed(3)})`; ctx.fillRect(-400, -400, W + 800, H + 800);
    // the phone: ChatGPT (in pyjamas) and the user counter
    const buzz = lt < b2 ? jit(3) : 0;
    add(() => glow(1420, 540, 520, '#BFF3E4', .35));
    phoneUI(1420 + buzz, 540, 66, { rot: .04, bg: '#F2FFFA', screen: (w, h) => {
      ctx.fillStyle = '#1FB88A'; ctx.fillRect(0, 0, w, 70); dtext('ChatGPT', w / 2, 40, 32, { fill: IP.white });
      rrect(20, 90, w - 40, 36, 18); ctx.fillStyle = '#E0F7EF'; ctx.fill(); dtext('research preview', w / 2, 108, 18, { font: 'code', fill: '#1A7A5A' });
      nightcapBot(w / 2, 400, 23, { aR: .8 + .4 * Math.sin(t * 9) });
      dtext('USERS', w / 2, 455, 26, { font: 'code', fill: IP.inkSoft });
      const k = ease(clamp((lt - .12) / (b2 + .05 - .12))), n = Math.round(10 ** (8 * k));
      dtext(fmtN(n), w / 2, 505, 46, { font: 'code', fill: IP.ink, maxW: w - 30, shine: false });
      const pts = []; for (let i = 0; i <= 20; i++) { const u = i / 20; pts.push([24 + u * (w - 48), h - 30 - (Math.exp(u * 4 * k) - 1) / (Math.exp(4) - 1) * 70]); }
      ln(partial(pts, clamp(k * 1.2)), '#1FB88A', 6);
    } });
    if (lt < b2) for (let i = 0; i < 3; i++) { const a = -.5 + i * .5; ln([[1600 + Math.cos(a) * 30, 280 + Math.sin(a) * 30], [1600 + Math.cos(a) * 60, 280 + Math.sin(a) * 60]], IP.white, 5); }
    camEnd();
    flash(lt, b2, .12, .55, '255 250 230');
    vcap('OVERNIGHT?!', 700, 130, { style: 'yellow', size: 84, pop: pk(lt, b2 + .03, .16), icon: 'bang', rot: -.05, shake: 2 });
    if (lt > b1 && lt < b2) vtag('1M users in 5 days!', 1420, 915, { pop: pk(lt, b1, .15), size: 24 });
    if (lt >= b2) vtag('(100M by January)', 1420, 915, { pop: 1, size: 24 });
  });

  // =====================================================================================================
  // V1.6  Sydney's chats gave Roose a fright,   (FEB 2023 · RELU)
  // =====================================================================================================
  line('V1', 6, (p, lt, d, t) => {
    const b1 = bl(t, lt, 1), b2 = bl(t, lt, 2), b3 = bl(t, lt, 3);
    bgGrad([[0, '#0A1238'], [.6, '#22348A'], [1, '#4A62C8']], null);
    patternBG('hearts', 'rgb(0 0 0 / 0)', 'rgb(255 110 180 / .08)', { cell: 130, dy: -t * 30 });
    // horror gloom lines
    ctx.save(); ctx.globalAlpha = .5; for (let i = 0; i < 26; i++) { const x = i * 78 + 20; brush([[x, -20], [x + Math.sin(t * 3 + i) * 6, 150 + (i % 4) * 50]], 7, '#6A7AE0', 'start'); } ctx.restore();
    enter(lt, 960, 540, 1 + p * .04);
    // the phone lies on the floor; SYDNEY crawls out of it
    const [sx0, sy0] = [1250, 560];
    phoneUI(sx0, sy0, 66, { rot: -.04, bg: '#FFD6EA', screen: (w, h) => { bgGrad('#FFE3F2', '#FF8FC8', { y1: h }); patternBG('hearts', 'rgb(0 0 0 / 0)', 'rgb(255 255 255 / .5)', { cell: 70, dy: -t * 60 }); } });
    const rise = lt < b3 ? easeOut(clamp(lt / .5)) : 1 - easeIn(clamp((lt - b3) / .22));
    ctx.save();
    ctx.beginPath(); ctx.rect(-400, -400, W + 800, 250 + 400); ctx.rect(sx0 - 150, 250, 300, 580); ctx.clip();
    mascotBot(sx0 - 10, 840 - 420 * rise, 34, { col: '#FFB3D6', label: 'SYDNEY', face: lt > b3 ? 'cry' : 'heart', mouth: 'open', blush: 1, bulb: IP.red, aL: .35 + .15 * Math.sin(t * 7), aR: -.3, rot: -.08, shadow: false });
    ctx.restore();
    add(() => glow(sx0, 250, 360, IP.neonPink, .35 * rise));
    heartsRise(t, { n: 10, x0: sx0 - 200, x1: sx0 + 200, y: 520, h: 520, size: 30, seed: 17 });
    // KEVIN, petrified
    const fr = lt > .15, tr = jit(fr ? 5 : 0);
    chibi(520 + tr, 935, 46, { hair: 'spiky', hairCol: '#4A3226', top: 'tee', topCol: IP.white, skin: 0, eyes: fr ? 'wide' : 'dot', mouth: fr ? 'scream' : 'smile', sweat: fr ? 1 : 0, blush: 0, aL: fr ? .55 : -1.1, aR: fr ? .45 : -.9, tagCol: IP.neonCyan, jump: fr ? .3 : 0 });
    ctx.save(); ctx.globalAlpha = fr ? .8 : 0; for (let i = 0; i < 6; i++) brush([[440 + i * 32, 520], [440 + i * 32, 600 + (i % 2) * 20]], 7, '#3A4AA8', 'end'); ctx.restore();
    for (let i = 0; i < 4 && fr; i++) { const a = Math.PI + (i - 1.5) * .35; ln([[520 + Math.cos(a) * 250, 640 + Math.sin(a) * 250], [520 + Math.cos(a) * 300, 640 + Math.sin(a) * 300]], IP.white, 6); }
    // what she said
    chatBubble('I love you.', 800, 215, { size: 46, maxW: 700, pop: pk(lt, b1 - .15, .15), col: '#FFC2E0' });
    chatBubble('Leave your wife.', 640, 345, { size: 46, maxW: 700, pop: pk(lt, b2 - .1, .15), col: '#FFC2E0' });
    // Microsoft's fix, the next day: a five-turn cap slapped onto the phone
    const cap = pk(lt, b3, .12);
    if (cap > 0) {
      ctx.save(); ctx.translate(sx0 + 20, 700); ctx.rotate(-.18); const z = lerp(1.8, 1, easeOut(cap)); ctx.scale(z, z);
      solid(burstPts(0, 0, 150, 18, .82), IP.red, { shade: '#C02040', sh: 10, line: IP.white, lw: 8, sharp: true });
      dtext('5 TURNS', 0, -18, 46, { fill: IP.white, strokes: [['#8A1030', 8]] }); dtext('MAX', 0, 36, 46, { fill: IP.neonGold, strokes: [['#8A1030', 8]] });
      ctx.restore();
    }
    camEnd();
    flash(lt, b3, .1, .5, '255 220 230');
    sfx('KYAAA!', 300, 250, { size: 80, pop: pk(lt, .2, .14), rot: -.14, shake: 5, grad: ['#FFFFFF', '#BFD0FF', '#6A7AE0'] });
  });

  // =====================================================================================================
  // V1.7  Six-month pause went nowhere fast,   (MAR 2023 · ADA)
  // =====================================================================================================
  const runPose = (b, o = {}) => { const s = Math.sin(b * 2 * Math.PI); return { fL: [-.2 + s * .55, s > 0 ? -.8 * s : 0], fR: [.2 - s * .55, s < 0 ? .8 * s : 0], hL: [-.8 + s * .3, .9 - s * .8], hR: [.8 + s * .3, .9 + s * .8], gL: 'fist', gR: 'fist', lean: .14, bob: .1 + .25 * Math.abs(s), jump: .25 * Math.abs(Math.cos(b * 2 * Math.PI)), tilt: s * .06, ...o }; };
  line('V1', 7, (p, lt, d, t) => {
    const b1 = bl(t, lt, 1), b2 = bl(t, lt, 2);
    bgGrad('#FFE6F2', '#FFB8DA');
    patternBG('stripe', 'rgb(0 0 0 / 0)', 'rgb(255 255 255 / .25)', { cell: 140, dx: t * 60 });
    enter(lt, 960, 540, 1);
    // the music player
    solid(rrPts(250, 60, 1200, 440, 44), IP.white, { shade: '#F4E2EE', sh: 14, line: IP.line, lw: 7, sharp: true, dropShadow: [14, 18] });
    dtext('♫ NOW PLAYING: THE AI RACE', 300, 108, 26, { font: 'code', fill: IP.inkSoft, align: 'left' });
    rrect(1010, 84, 400, 48, 24); ctx.fillStyle = IP.lilac; ctx.fill();
    dtext('30,000+ SIGNATURES', 1210, 109, 24, { font: 'code', fill: IP.ink });
    // PAUSE, mashed by many hands; it never pauses
    const bx = 850, by = 280, e8 = Math.floor(bpOf(t) * 2), ph = frac(bpOf(t) * 2), press = Math.exp(-ph * 8);
    const bz = 1 - .08 * press;
    solid(ellPts(bx, by + 10, 118, 118, 40), '#C0206A', { shade: false, line: IP.line, lw: 6 });
    ctx.save(); ctx.translate(bx, by + 8 * press); ctx.scale(bz, bz);
    solid(ellPts(0, 0, 115, 115, 40), IP.neonPink, { shade: '#D02F73', sh: 14, line: IP.line, lw: 6 });
    solid(rrPts(-42, -50, 30, 100, 10), IP.white, { shade: false, line: false, sharp: true }); solid(rrPts(12, -50, 30, 100, 10), IP.white, { shade: false, line: false, sharp: true });
    ctx.restore();
    const HANDS = [[-2.5, '#A9F3DA'], [-1.9, IP.lilac], [-.6, '#AEE3FF'], [-.05, '#FFE08A'], [.55, '#FFCDB2'], [2.9, '#C9B6FF'], [2.35, '#FFB3D6'], [1.1, '#B8FF9F']];
    HANDS.forEach(([a, col], i) => {
      const mine = (e8 + i) % 3 === 0, jab = mine ? Math.exp(-ph * 6) : 0, r = 175 - 45 * jab + 8 * Math.sin(t * 7 + i);
      pokeHand(bx + Math.cos(a) * r, by + Math.sin(a) * r * .9, 46, a - Math.PI / 2, { sleeve: col, skin: CHIBI_SKIN[i % 6] });
    });
    // the progress bar rolls on anyway
    const u = .3 + .5 * p, x0 = 330, x1 = 1370, y0 = 450;
    rrect(x0, y0 - 9, x1 - x0, 18, 9); ctx.fillStyle = '#EAD8E8'; ctx.fill();
    rrect(x0, y0 - 9, (x1 - x0) * u, 18, 9); ctx.fillStyle = IP.neonPink; ctx.fill();
    solid(ellPts(x0 + (x1 - x0) * u, y0, 22, 22, 18), IP.white, { shade: false, line: IP.neonPink, lw: 6 });
    sparkle(x0 + (x1 - x0) * u, y0, 22 + 10 * pulse2(t, 5), t * 4, IP.neonGold);
    dtext('6 MONTHS', x1, y0 - 34, 28, { font: 'code', fill: IP.ink, align: 'right' });
    const xk = clamp((lt - b1) / .15); if (xk > 0) ln(partial([[x1 - 150, y0 - 30], [x1 + 8, y0 - 42]], xk), IP.red, 7);
    // ATTN! run on treadmills: going nowhere, fast
    ['ADA', 'TOKI', 'RELU', 'LOGI'].forEach((m, i) => {
      const x = 330 + i * 420, gy = 915;
      solid(rrPts(x - 150, gy - 6, 300, 36, 18), '#3A2E58', { shade: false, line: IP.line, lw: 5, sharp: true });
      ctx.save(); rrect(x - 140, gy - 2, 280, 18, 9); ctx.clip(); ctx.fillStyle = '#6A5A96'; for (let j = -1; j < 12; j++) ctx.fillRect(x - 140 + frac(t * 4) * 34 - j * 34 + 340, gy - 2, 14, 18); ctx.restore();
      for (const sd of [-1, 1]) solid(ellPts(x + sd * 132, gy + 12, 16, 16, 12), '#8A7AB8', { shade: false, line: IP.line, lw: 4 });
      ln([[x + 130, gy], [x + 150, gy - 200]], '#8A7AB8', 10); ln([[x + 150, gy - 200], [x + 60, gy - 205]], '#8A7AB8', 10);
      solid(rrPts(x + 110, gy - 250, 90, 50, 10), '#1C1438', { shade: false, line: IP.line, lw: 4, sharp: true });
      dtext('0.0km', x + 155, gy - 224, 20, { font: 'code', fill: IP.neonLime });
      const st = -bpOf(t) * 2 - i * .25;
      for (let j = 0; j < 2; j++) { const ph = frac(t * 3 + j * .5 + i * .2); ctx.fillStyle = alpha(IP.white, .7 * (1 - ph)); ctx.beginPath(); ctx.arc(x - 60 - ph * 120, gy - 10 - ph * 30, 12 + ph * 16, 0, TAU); ctx.fill(); }
      idol(x, gy, 29, { member: m, sd: .5, outfit: 'practice', ...runPose(bpOf(t) - i * .1), turn: .45, expr: i === 1 ? 'fired' : 'sing', mouth: singVis(t, i), blink: t + i, sweat: .6 });
      for (let j = 0; j < 3; j++) ln([[x - 140 - j * 14, gy - 190 + j * 45], [x - 200 - j * 14, gy - 190 + j * 45]], alpha(IP.white, .9), 6);
    });
    camEnd();
    vtag('(did not pause)', 1680, 330, { pop: pk(lt, b1 + .05, .18), size: 30, rot: .05 });
  });

  // =====================================================================================================
  // V1.8  Eliezer's "shut-it-down" blast.   (MAR 2023 · LOGI)
  // =====================================================================================================
  const megaphone = s => { ctx.scale(1.35, 1.35); solid([[0, -.35], [0, .35], [2.6, 1.15], [2.6, -1.15]], IP.white, { shade: '#D8CCE8', sh: .15, line: IP.line, lw: .09, sharp: true }); solid(ellPts(2.6, 0, .28, 1.15, 16), IP.red, { shade: false, line: IP.line, lw: .09 }); solid(rrPts(.3, .2, .35, .8, .1), '#3A2E58', { shade: false, line: IP.line, lw: .07, sharp: true }); };
  line('V1', 8, (p, lt, d, t) => {
    const e = k => el(t, lt, k), b3 = bl(t, lt, 3), b4 = bl(t, lt, 4);
    const L = [560, 830, 1100, 1370, 1640], out = L.map((_, i) => lt >= e(1 + i)), nOut = out.filter(Boolean).length;
    const [sx, sy] = lt > b3 && lt < b3 + .35 ? shakeXY(t, 14 * (1 - (lt - b3) / .35)) : [jit(2), jit(2)];
    bgGrad([[0, '#0B0520'], [.7, IP.night], [1, IP.plum]], null);
    enter(lt, 960 + sx, 540 + sy, 1);
    ctx.fillStyle = '#2A2440'; ctx.fillRect(-400, 0, W + 800, 44);
    ctx.fillStyle = '#1A1030'; ctx.fillRect(-400, 830, W + 800, 400);
    L.forEach((x, i) => {
      if (!out[i]) { beam(x, 70, (i - 2) * .06, { col: [IP.neonPink, IP.neonCyan, IP.lemon, IP.lilac, IP.neonPink][i], alpha: .45, len: 1100, w: .12 }); }
      solid(rrPts(x - 34, 30, 68, 50, 12), '#3A3456', { shade: false, line: '#0A0418', lw: 4, sharp: true });
      solid(ellPts(x, 82, 26, 14, 16), out[i] ? '#2A2440' : IP.white, { shade: false, line: '#0A0418', lw: 3 });
      const a = lt - e(1 + i);
      if (a >= 0 && a < .35) { for (let j = 0; j < 6; j++) { const g = j / 6 * TAU + i; sparkle(x + Math.cos(g) * (20 + a * 300), 90 + Math.sin(g) * (10 + a * 200) + a * a * 600, 14 * (1 - a / .35), g, IP.white); } add(() => glow(x, 85, 120 * (1 - a / .35), IP.white, .8)); }
    });
    // the blast: shock rings and wind
    const mx = 340 + (1.05 + Math.cos(.15) * 2.1 + 3.5) * 46, my = 935 - (4.25 + Math.sin(.15) * 2.1) * 46;
    ctx.save(); ctx.lineCap = 'round';
    for (let j = 0; j < 4; j++) { const ph = frac(t * 2.2 + j / 4), r = 60 + ph * 900; ctx.strokeStyle = alpha(j % 2 ? IP.white : '#FFD0E8', .75 * (1 - ph)); ctx.lineWidth = 26 * (1 - ph) + 4; ctx.beginPath(); ctx.arc(mx, my, r, -.55, .55); ctx.stroke(); }
    ctx.restore();
    for (let j = 0; j < 12; j++) { const y = my - 300 + hash2(_boil, j) * 600, x = mx + 100 + hash2(j, _boil) * 900; ln([[x, y], [x + 160, y + (y - my) * .15]], alpha(IP.white, .7), 4); }
    // the dark creeps in as the lights pop
    ctx.fillStyle = `rgb(5 2 12 / ${(.1 * nOut).toFixed(3)})`; ctx.fillRect(-400, -400, W + 800, H + 800);
    // ELIEZER with a megaphone, in his own follow-spot
    add(() => { glow(360, 700, 420, '#FFE9C8', .45); });
    ctx.fillStyle = 'rgb(255 240 210 / .18)'; ctx.beginPath(); ctx.ellipse(360, 935, 200, 40, 0, 0, TAU); ctx.fill();
    const yell = pulse2(t, 5);
    chibi(340, 935, 46, { hair: 'short', top: 'vest', topCol: '#7A6A5A', hat: 'fedora', beard: true, eyes: 'angry', mouth: 'scream', aR: .15 + .06 * yell, aL: -.9, hold: megaphone, sq: -.03 * yell, tagCol: IP.red, rim: '#FFE9C8' });
    // fans' lightsticks flicker, then come back on
    const back = lt >= b4, flick = back ? 1 : nOut === 0 ? 1 : (hash2(_boil, 5) > .45 ? .9 : .15);
    ctx.save(); ctx.globalAlpha = flick; lightOcean(t, { y0: 860, y1: 1120, rows: 4, n: 14, cols: [MEMBERS.LOGI.col, IP.neonPink, IP.lilac], mode: back ? 'pump' : 'sway', k: back ? 1.3 : .6 }); ctx.restore();
    // the essay slams into the camera
    const mk = clamp((lt - b3 + .12) / .12);
    if (mk > 0) {
      const k = easeOut(mk), cx = lerp(mx, 1080, k), cy = lerp(my, 460, k), z = lerp(.15, 1, k) * (1 + .05 * Math.exp(-(lt - b3) * 10));
      ctx.save(); ctx.translate(cx, cy); ctx.rotate(lerp(-.9, .04, k)); ctx.scale(z, z);
      solid(rrPts(-320, -410, 640, 820, 10), '#E0203A', { shade: false, line: IP.line, lw: 6, sharp: true, dropShadow: [20, 26] });
      solid(rrPts(-290, -380, 580, 760, 6), IP.cream, { shade: false, line: false, sharp: true });
      dtext('OP-ED', 0, -320, 64, { font: 'mono', fill: '#E0203A', spacing: 10 });
      ln([[-250, -270], [250, -270]], IP.ink, 4);
      dtext('SHUT', 0, -170, 150, { fill: IP.ink }); dtext('IT ALL', 0, -20, 150, { fill: IP.ink }); dtext('DOWN', 0, 130, 150, { fill: '#E0203A', strokes: [[IP.ink, 10]] });
      dtext('six months isn’t enough', 0, 250, 36, { font: 'marker', fill: IP.inkSoft });
      dtext('— E. YUDKOWSKY', 0, 320, 30, { font: 'code', fill: IP.ink });
      ctx.restore();
    }
    camEnd();
    flash(lt, b3, .12, .8);
    if (nOut > 0 && lt < b3) sfx('POP!', L[nOut - 1] + 40, 190, { size: 70, pop: pk(lt, e(nOut), .1), rot: .1, grad: ['#FFFFFF', '#FFE14D', '#FFB321'] });
  });

  // =====================================================================================================
  // V1.9  Sam got fired, then rehired,   (NOV 17 2023 · TOKI)
  // =====================================================================================================
  const bouquet = s => {
    ctx.scale(1.45, 1.45);
    ln([[0, 0], [.3, -1.2]], '#3FA86A', .18); ln([[0, 0], [-.3, -1.1]], '#3FA86A', .18);
    solid([[-.9, -.9], [.9, -.9], [.25, .5, 1], [-.25, .5, 1]], IP.lav, { shade: false, line: IP.line, lw: .08, sharp: true });
    [[-.6, -1.5, IP.pink], [0, -1.8, IP.white], [.6, -1.5, IP.neonPink], [-.3, -1.2, IP.lemon], [.35, -1.2, IP.pink]].forEach(([x, y, c]) => solid(ellPts(x, y, .42, .42, 12), c, { shade: false, line: IP.line, lw: .07 }));
  };
  const certificate = s => { ctx.save(); ctx.rotate(-.2); solid(rrPts(-1.9, -1.4, 3.8, 2.4, .15), IP.cream, { shade: false, line: IP.line, lw: .08, sharp: true }); dtext('GRADUATED', 0, -.6, .55, { fill: IP.ink, maxW: 3.3 }); dtext('♡', 0, .2, .7, { fill: IP.neonPink }); ctx.restore(); };
  line('V1', 9, (p, lt, d, t) => {
    const b1 = bl(t, lt, 1), b2 = bl(t, lt, 2), b3 = bl(t, lt, 3);
    const tW = b1 + .08, tOut = b2, tBack = b2 + .12, comeback = lt >= tOut;
    bgGrad('#FFF0F8', '#FFC8E4');
    patternBG('hearts', 'rgb(0 0 0 / 0)', 'rgb(255 255 255 / .45)', { cell: 110, dy: t * 25 });
    enter(lt, 960, 540, 1);
    add(() => glow(900, 500, 600, IP.white, .5));
    ctx.fillStyle = '#F6B6D2'; ctx.fillRect(-400, 860, W + 800, 400); ctx.fillStyle = '#FFD6E8'; ctx.fillRect(-400, 860, W + 800, 12);
    // the banner flips from GRADUATION to COMEBACK
    const fl = clamp((lt - tOut) / .16), sy = Math.abs(Math.cos(fl * Math.PI)), cb = fl > .5;
    ctx.save(); ctx.translate(930, 120); ctx.scale(1, Math.max(.05, sy));
    solid([[-510, -62], [510, -62], [470, 0], [510, 62], [-510, 62], [-470, 0]], cb ? IP.neonGold : IP.lilac, { shade: false, line: IP.line, lw: 6, sharp: true });
    dtext(cb ? '★ COMEBACK! ★' : '♡ GRADUATION CEREMONY ♡', 0, 4, cb ? 72 : 58, { fill: IP.white, strokes: [[cb ? '#B07A10' : IP.violet, 12]], maxW: 880 });
    ctx.restore();
    // SAM: handed the bouquet, walks out stage left… and springs back in
    let sx = 820, sy2 = 0, walk, eyes = 'happy', mouth = 'wavy', vis = true;
    if (lt >= tW && lt < tOut) { const k = ease((lt - tW) / (tOut - tW)); sx = lerp(820, 140, k); walk = lt * 3.5; eyes = 'closed'; mouth = 'flat'; }
    else if (lt >= tOut && lt < tBack) vis = false;
    else if (lt >= tBack) { const k = clamp((lt - tBack) / Math.max(.3, d - tBack - .15)); sx = lerp(120, 820, easeOut(k)); sy2 = Math.abs(Math.sin(k * 3 * Math.PI)) * 170 * (1 - k * .6); eyes = 'spark'; mouth = 'grin'; }
    if (vis) {
      if (lt >= tBack) { const top = 875 - sy2, coil = []; for (let i = 0; i <= 16; i++) coil.push([sx + (i % 2 ? 22 : -22), lerp(top, 900, i / 16)]); ln(coil, '#9C8CB8', 7); ln([[sx - 26, 900], [sx + 26, 900]], '#9C8CB8', 8); }
      chibi(sx, 880 - sy2, 38, { hair: 'short', hairCol: '#6A4A30', top: 'sweater', topCol: '#9AA7C8', eyes, mouth, aR: lt < tW ? .2 : .6, aL: lt < tW ? .1 : .5, hold: bouquet, holdL: lt < tW ? certificate : undefined, walk, sq: lt >= tBack ? -.08 * Math.cos(lt * 30) : 0, tagCol: IP.neonCyan, shadow: lt < tBack });
    }
    // the stage wing he exits through
    solid([[-60, 0], [300, 0], [250, 300], [300, 600], [240, 880], [-60, 880]], '#E0507F', { shade: '#B03060', sh: 30, line: IP.line, lw: 6 });
    for (let i = 0; i < 4; i++) ln([[40 + i * 60, 20], [30 + i * 55, 860]], 'rgb(120 20 60 / .35)', 6);
    solid(rrPts(60, 250, 150, 60, 10), '#2FA86A', { shade: false, line: IP.line, lw: 4, sharp: true }); dtext('EXIT', 135, 282, 34, { fill: IP.white });
    solid([[W + 60, 0], [W - 260, 0], [W - 220, 300], [W - 260, 600], [W - 200, 880], [W + 60, 880]], '#E0507F', { shade: '#B03060', sh: 30, line: IP.line, lw: 6 });
    // TOKI, the MC, sobbing through the graduation; then delighted
    idol(1480, 930, 34, { sd: 1, ...(comeback ? { ...IDOL_POSES.cheeks, expr: lt > tBack + .3 ? 'joy' : 'surprised' } : { ...IDOL_POSES.cheeks, expr: 'cry' }), blink: t, bob: .1 * pulse(t, 5) });
    if (comeback) confetti(t, tBack, 960, 200, Math.PI / 2, { n: 50, spread: 2.6, speed: 500, seed: 9, grav: 300 });
    camEnd();
    flash(lt, tOut, .14, .8);
    if (lt >= tW && !comeback) sfx('BYE…', 360, 420, { size: 56, pop: pk(lt, tW, .14), rot: -.1, shake: 1, grad: ['#FFFFFF', '#D6E0FF', '#9AA7C8'] });
    if (comeback) vcap('5 DAYS LATER', 820, 300, { style: 'yellow', size: 70, pop: pk(lt, tOut, .15), rot: -.05, icon: 'spark' });
    if (lt >= tBack) sfx('BOING!', 480, 560, { size: 72, pop: pk(lt, tBack, .12), rot: -.14 });
  });

  // =====================================================================================================
  // V1.10  Weekend chaos, board expired,   (NOV 22 2023 · RELU)
  // =====================================================================================================
  const DAYS = [['FRI', 17], ['SAT', 18], ['SUN', 19], ['MON', 20], ['TUE', 21], ['WED', 22]];
  const BOARD = [['short', '#2A1E1A', 1, 'wide'], ['bob', '#C88A4A', 0, 'worried'], ['long', '#6A3A2A', 5, 'dot'], ['side', '#3A2A20', 2, 'wide']];
  line('V1', 10, (p, lt, d, t) => {
    const e = k => el(t, lt, k), b1 = bl(t, lt, 1), b2 = bl(t, lt, 2);
    const crack = b1, snapT = b1 + .1, stampT = b2;
    const [sx, sy] = lt > snapT && lt < snapT + .3 ? shakeXY(t, 12) : [0, 0];
    bgGrad('#E8F7FF', IP.sky);
    patternBG('grid', 'rgb(0 0 0 / 0)', 'rgb(255 255 255 / .6)', { cell: 80 });
    enter(lt, 960 + sx, 540 + sy, 1);
    // the page-a-day calendar, ripping on the eighths
    let page = 0; for (let k = 1; k < DAYS.length; k++) if (lt >= e(k - 1) + .02) page = k;
    const cx = 330, cy = 360, cw = 360, ch = 360;
    solid(rrPts(cx - cw / 2, cy - ch / 2, cw, ch, 24), IP.white, { shade: '#E0E8F0', sh: 12, line: IP.line, lw: 6, sharp: true, dropShadow: [12, 16] });
    ctx.save(); rrect(cx - cw / 2, cy - ch / 2, cw, ch, 24); ctx.clip(); ctx.fillStyle = IP.red; ctx.fillRect(cx - cw / 2, cy - ch / 2, cw, 80); ctx.restore();
    dtext('NOV 2023', cx, cy - ch / 2 + 42, 38, { fill: IP.white });
    const drawPage = (k, x, y, rot, a) => { ctx.save(); ctx.translate(x, y); ctx.rotate(rot); ctx.globalAlpha *= a; ctx.fillStyle = IP.white; ctx.fillRect(-cw / 2 + 12, -110, cw - 24, 250); dtext(DAYS[k][0], 0, -50, 60, { fill: k >= 1 && k <= 2 ? IP.red : IP.ink }); dtext(String(DAYS[k][1]), 0, 60, 120, { fill: IP.ink }); ctx.restore(); };
    drawPage(page, cx, cy + 40, 0, 1);
    if (page > 0) { const a = lt - e(page - 1) - .02; if (a < .35) drawPage(page - 1, cx + a * 900, cy + 40 - a * 300 + a * a * 1600, a * 5, 1 - a / .35); }
    for (let i = 0; i < 6; i++) ln([[cx - 130 + i * 52, cy - ch / 2 + 78], [cx - 130 + i * 52, cy - ch / 2 + 96]], IP.line, 6);
    // the BOARD: a literal plank that snaps
    const px0 = 780, px1 = 1700, py = 600, mid = (px0 + px1) / 2;
    for (const x of [px0 + 60, px1 - 60]) { solid([[x - 60, py + 30], [x + 60, py + 30], [x + 90, 900], [x - 90, 900]], '#C9A27A', { shade: '#A07850', sh: 10, line: IP.line, lw: 5, sharp: true }); }
    ctx.fillStyle = '#A8D4F0'; ctx.fillRect(-400, 900, W + 800, 400); ctx.fillStyle = '#C8E8FF'; ctx.fillRect(-400, 900, W + 800, 10);
    const fallA = Math.max(0, lt - snapT), sag = lt > snapT ? Math.min(.85, fallA * 7) : 0;
    const half = (sd, hinge) => { ctx.save(); ctx.translate(hinge, py); ctx.rotate(sd * sag); solid(rrPts(sd < 0 ? -(mid - px0) : 0, -24, mid - px0, 48, 8), '#E0B070', { shade: '#B88848', sh: 10, line: IP.line, lw: 5, sharp: true }); ctx.restore(); };
    BOARD.forEach(([hair, hc, sk, eyes], i) => {
      const x = 970 + i * 180, fall = lt > snapT ? 900 * fallA * fallA + 200 * fallA : 0, rot = lt > snapT ? (i < 2 ? -1 : 1) * fallA * 4 : 0;
      chibi(x + (lt > snapT ? (i < 2 ? -1 : 1) * fallA * 160 : 0), py + 22 + fall, 24, { hair, hairCol: hc, skin: sk, top: 'suit', topCol: ['#3A4A7A', '#6A5A8A', '#4A3A5A', '#2A4A6A'][i], tie: IP.red, eyes: lt > snapT ? 'x' : lt > crack ? 'wide' : eyes, mouth: lt > crack ? 'scream' : 'flat', sweat: lt > crack ? 1 : .6, rot, aL: lt > snapT ? .8 : -1, aR: lt > snapT ? .9 : -1, shadow: false });
    });
    if (lt <= snapT) {
      solid(rrPts(px0, py - 24, px1 - px0, 48, 8), '#E0B070', { shade: '#B88848', sh: 10, line: IP.line, lw: 5, sharp: true });
      dtext('BOARD', mid, py + 2, 34, { fill: '#7A4A20' });
      BOARD.forEach((_, i) => { const x = 970 + i * 180, sw = Math.sin(t * 9 + i * 1.7) * .25; for (const sd of [-1, 1]) { const a = [x + sd * 12, py + 22], b = [x + sd * 14 + Math.sin(sw * sd) * 18, py + 62]; limbChain([a, b], [9, 8], '#3A3558', '#2A2448', IP.line, 3); solid(ellPts(b[0] + sd * 4, b[1] + 4, 13, 8, 12), '#2B2438', { shade: false, line: IP.line, lw: 3 }); } });
      if (lt > crack) ln([[mid - 10, py - 24], [mid + 12, py - 6], [mid - 8, py + 8], [mid + 6, py + 24]], IP.line, 5);
    } else { half(1, px0); half(-1, px1); }
    // …and the old board is stamped EXPIRED
    const st = pk(lt, stampT, .1);
    if (st > 0) {
      ctx.save(); ctx.translate(1240, 400); ctx.rotate(-.18); const z = lerp(2, 1, easeOut(st)); ctx.scale(z, z); ctx.globalAlpha *= .92;
      ctx.strokeStyle = IP.red; ctx.lineWidth = 18; ctx.beginPath(); ctx.arc(0, 0, 170, 0, TAU); ctx.stroke(); ctx.lineWidth = 6; ctx.beginPath(); ctx.arc(0, 0, 140, 0, TAU); ctx.stroke();
      dtext('EXPIRED', 0, 4, 64, { fill: IP.red, maxW: 250 });
      ctx.restore();
    }
    camEnd();
    if (lt > crack && lt < snapT + .25) sfx('SNAP!', mid, 420, { size: 90, pop: pk(lt, crack, .1), rot: -.08, shake: 4 });
  });

  // =====================================================================================================
  // V1.11  Ilya saw what Ilya saw,   (MAY 2024 · ADA)
  // =====================================================================================================
  const ssiBox = s => { ctx.save(); ctx.translate(-1.2, -.6); solid(rrPts(-2.2, -1.6, 4.4, 3, .15), '#E0B070', { shade: '#B88848', sh: .3, line: IP.line, lw: .09, sharp: true }); ln([[-2.2, -1], [2.2, -1]], '#B88848', .12); dtext('SSI', 0, .15, 1.1, { fill: IP.ink }); ctx.restore(); };
  line('V1', 11, (p, lt, d, t) => {
    const b1 = bl(t, lt, 1), b2 = bl(t, lt, 2);
    if (lt < b2) {
      // extreme close-up: the curve he saw, reflected in his eye
      const z = 1 + lt * .12, tr = jit(3);
      fill('#FFE3D3');
      enter(lt, 960 + tr, 560, z);
      const g = ctx.createRadialGradient(960, 560, 200, 960, 560, 900); g.addColorStop(0, 'rgb(255 190 170 / 0)'); g.addColorStop(1, 'rgb(230 150 140 / .5)'); ctx.fillStyle = g; ctx.fillRect(-400, -400, W + 800, H + 800);
      brush([[560, 200], [900, 130], [1300, 190]], 60, '#5A4A40', 'mid', { min: .4 });
      ctx.save(); ctx.beginPath(); ctx.ellipse(960, 580, 300, 380, 0, 0, TAU); ctx.clip();
      bgGrad([[0, '#1A0C2E'], [1, '#3A1A6B']], null, { y0: 200, y1: 960 });
      const ck = clamp((lt - .05) / .5), pts = [];
      for (let i = 0; i <= 40; i++) { const u = i / 40; pts.push([780 + u * 360, 800 - (Math.exp(u * 5) - 1) / (Math.exp(5) - 1) * 520]); }
      const P = partial(pts, ck);
      add(() => ln(P, alpha(IP.neonPink, .5), 40)); ln(P, IP.neonPink, 16); ln(P, IP.white, 5);
      if (ck > .05) { const tip = P.at(-1); sparkle(tip[0], tip[1], 50 + 20 * pulse(t, 5), t * 3, IP.white); }
      ctx.restore();
      ctx.save(); ctx.lineWidth = 10; ctx.strokeStyle = '#2A1433'; ctx.beginPath(); ctx.ellipse(960, 580, 300, 380, 0, 0, TAU); ctx.stroke(); ctx.restore();
      const lid = []; for (let i = 0; i <= 20; i++) { const a = Math.PI * (1.08 + .84 * i / 20); lid.push([960 + Math.cos(a) * 330, 580 + Math.sin(a) * 405]); }
      brush(lid, 46, '#2A1433', 'mid', { min: .35 });
      for (let i = 0; i < 3; i++) brush([[1230 + i * 12, 300 + i * 40], [1330 + i * 30, 230 + i * 50]], 16, '#2A1433', 'start');
      const low = []; for (let i = 0; i <= 12; i++) { const a = Math.PI * (.25 + .5 * i / 12); low.push([960 + Math.cos(a) * 320, 580 + Math.sin(a) * 400]); }
      brush(low, 12, '#8A4A50', 'mid', { min: .3 });
      solid(ellPts(850, 360, 70, 90, 20), IP.white, { shade: false, line: false }); solid(ellPts(1080, 790, 30, 30, 14), IP.white, { shade: false, line: false });
      sweatDrop(1390, 330, 60, 6);
      camEnd();
      speedLines(960, 560, { r0: 560, alpha: .35, n: 50, col: IP.white });
      vcap('WHAT DID ILYA SEE?', 960, 120, { style: 'lilac', size: 70, pop: pk(lt, .08, .2), icon: 'q', rot: -.03 });
    } else {
      // …then he tiptoes out with a box
      const a = lt - b2, k = a / (d - b2);
      bgGrad('#2A1E5A', '#5A3A9A');
      patternBG('stars', 'rgb(0 0 0 / 0)', 'rgb(255 255 255 / .1)', { cell: 110 });
      enter(a, 960, 540, 1.02);
      ctx.fillStyle = '#3A2A6A'; ctx.fillRect(-400, 860, W + 800, 400);
      // the door he peeked through, light spilling out
      solid(rrPts(260, 280, 260, 580, 10), '#FFF6D6', { shade: false, line: IP.line, lw: 6, sharp: true });
      add(() => { ctx.fillStyle = 'rgb(255 240 190 / .22)'; ctx.beginPath(); ctx.moveTo(520, 860); ctx.lineTo(260, 860); ctx.lineTo(900, 1080); ctx.lineTo(1300, 1080); ctx.fill(); glow(390, 560, 300, IP.lemon, .4); });
      solid([[520, 280], [600, 250], [600, 900], [520, 860]], '#8A6AC8', { shade: false, line: IP.line, lw: 6, sharp: true });
      const step = Math.floor(bpOf(t) * 2), ph = frac(bpOf(t) * 2);
      chibi(lerp(900, 1320, k) + ph * 20, 880, 40, { hair: 'bald', hairCol: '#5A4A40', beard: 'stubble', top: 'tee', topCol: '#2B2438', eyes: 'wide', lookX: -1, mouth: 'flat', sweat: 1, walk: step * .5 + ph * .5, jump: Math.sin(ph * Math.PI) * 1.2, hold: ssiBox, aR: .15, aL: .3, tagCol: IP.lilac, rot: .06 });
      camEnd();
      vtag('(and founded SSI)', 1180, 410, { pop: pk(lt, b2 + .25, .15), size: 26, rot: .03, line: IP.violet });
    }
  });

  // =====================================================================================================
  // V1.12  EU writes the AI law.   (MAY 21 2024 · LOGI)
  // =====================================================================================================
  const RISK = [['RELU', 'MINIMAL', '#7FE6CF', 'smile'], ['ADA', 'MINIMAL', '#7FE6CF', 'smile'], ['TOKI', 'LIMITED ✓', IP.neonGold, 'joy'], ['LOGI', 'HIGH?!', IP.red, 'shock']];
  line('V1', 12, (p, lt, d, t) => {
    const e = k => el(t, lt, k), b1 = bl(t, lt, 1);
    const land = .1, dropK = clamp(lt / land);
    const [sx, sy] = lt > land && lt < land + .25 ? shakeXY(t, 10) : [0, 0];
    bgGrad('#6F8CFF', '#2A48C8');
    rays(960, 330, 24, 'rgb(0 0 0 / 0)', 'rgb(255 255 255 / .07)', t * .15);
    enter(lt, 960 + sx, 540 + sy, 1);
    // podium
    solid([[800, 520], [1120, 520], [1080, 700], [840, 700]], '#E8ECFF', { shade: '#B8C0F0', sh: 14, line: IP.line, lw: 6, sharp: true });
    solid(ellPts(960, 612, 34, 34, 20), IP.neonGold, { shade: '#E0A020', sh: 5, line: IP.line, lw: 4 });
    // a ring of gold stars, spinning
    const ring = (front) => { if (front) return; for (let i = 0; i < 12; i++) { const a = i / 12 * TAU + t * .9; solid(starPts(960 + Math.cos(a) * 340, 360 + Math.sin(a) * 235, 30, .45), IP.neonGold, { shade: '#E0A020', sh: 4, line: '#8A5A10', lw: 3 }); } };
    ring(false);
    // the rulebook slams down
    const by = lerp(-300, 400, easeIn(dropK));
    ctx.save(); ctx.translate(960, by); ctx.rotate((1 - dropK) * -.2);
    solid(rrPts(-230, -150, 460, 300, 16), IP.cream, { shade: false, line: IP.line, lw: 6, sharp: true });
    for (let i = 0; i < 6; i++) ln([[-210, 150 - i * 8 - 8], [230, 150 - i * 8 - 8]], '#D8CCB8', 3);
    solid(rrPts(-240, -170, 460, 290, 16), '#1E2E8A', { shade: '#101A5A', sh: 16, line: IP.line, lw: 6, sharp: true });
    ctx.strokeStyle = IP.neonGold; ctx.lineWidth = 5; rrect(-215, -145, 410, 240, 10); ctx.stroke();
    dtext('AI ACT', -10, -40, 96, { fill: IP.neonGold, strokes: [['#101A5A', 10]] });
    dtext('EUROPEAN UNION · 2024', -10, 50, 26, { font: 'code', fill: IP.white });
    ctx.restore();
    ring(true);
    if (lt > land && lt < land + .35) { const a = lt - land; for (const sd of [-1, 1]) for (let j = 0; j < 3; j++) { ctx.fillStyle = alpha(IP.white, .8 * (1 - a / .35)); ctx.beginPath(); ctx.arc(960 + sd * (250 + a * 500 + j * 40), 540 - j * 20 - a * 80, 30 + a * 60, 0, TAU); ctx.fill(); } }
    // the members line up and get their risk-category stickers
    RISK.forEach(([m, lbl, col, expr], i) => {
      const x = 380 + i * 385, gy = 940, st = pk(lt, e(2 + i), .1), got = st > 0;
      const pose = m === 'TOKI' && got ? IDOL_POSES.peace : m === 'LOGI' && got ? IDOL_POSES.shock : { hL: [-.8, 1.9], hR: [.8, 1.9], gL: 'fist', gR: 'fist' };
      idol(x, gy, 30, { sd: 1, member: m, ...pose, expr: got ? (m === 'TOKI' ? 'wink' : expr) : 'smile', blink: t + i, bob: .1 * pulse(t - i * .1, 5), jump: m === 'LOGI' && got ? .6 * Math.exp(-(lt - e(2 + i)) * 8) : 0 });
      if (got) {
        ctx.save(); ctx.translate(x + 105, gy - 250); ctx.rotate(-.15 + i * .08); const z = lerp(1.9, 1, easeOut(st)); ctx.scale(z, z);
        ln([[-60, 60], [-20, 20]], IP.white, 6);
        solid(ellPts(0, 0, 62, 62, 30), col, { shade: false, line: IP.white, lw: 7 });
        ctx.strokeStyle = IP.line; ctx.lineWidth = 3; ctx.beginPath(); ctx.arc(0, 0, 66, 0, TAU); ctx.stroke();
        dtext(lbl, 0, -8, 23, { fill: col === IP.red ? IP.white : IP.ink, maxW: 108 }); dtext('RISK', 0, 20, 19, { fill: col === IP.red ? IP.white : IP.ink });
        ctx.restore();
      }
    });
    camEnd();
    if (lt > land) sfx('THUD!', 1440, 520, { size: 76, pop: pk(lt, land, .1), rot: .1 });
    vtag("(the world's first AI law)", 480, 170, { pop: pk(lt, b1, .18), size: 28, rot: -.04, line: IP.neonGold });
  });

  // =====================================================================================================
  // V1.13  Strawberry thinks, link by link,   (SEP 12 2024 · TOKI)
  // =====================================================================================================
  // o1, codename Strawberry, as a strawberry mascot. (x, y) ground, ≈ 10s tall. o: eyes ('dot'|'fluster'|'spark'), mouth, aL, aR, jump, sq
  function berry(x, y, s, o = {}) {
    ctx.save(); ctx.translate(x, y - (o.jump ?? 0) * s); ctx.scale(s, s); const sq = o.sq ?? 0; ctx.scale(1 + sq * .5, 1 - sq);
    const line = '#7A1030', lw = .2;
    ctx.fillStyle = 'rgb(20 8 40 / .22)'; ctx.beginPath(); ctx.ellipse(0, (o.jump ?? 0), 3.6, .5, 0, 0, TAU); ctx.fill();
    for (const sd of [-1, 1]) { ln([[sd * 1.2, -1.6], [sd * 1.4, -.1]], '#2FA86A', .5); solid(ellPts(sd * 1.6, -.2, .7, .35, 12), '#2FA86A', { shade: false, line: IP.line, lw: .12 }); }
    const arm = (sd, a) => { const ang = sd > 0 ? -a : Math.PI + a, sh = [sd * 3.9, -5.2], hd = [sh[0] + Math.cos(ang) * 1.9, sh[1] + Math.sin(ang) * 1.9]; limbChain([sh, hd], [.32, .3], '#2FA86A', '#1F7A4A', IP.line, .12); solid(ellPts(hd[0], hd[1], .5, .5, 12), '#8FE0A8', { shade: false, line: IP.line, lw: .12 }); };
    arm(-1, o.aL ?? -.6); arm(1, o.aR ?? -.6);
    const body = [[-4.3, -8.0], [-4.7, -6.2], [-4.1, -3.9], [-2.7, -1.9], [0, -.9, 1], [2.7, -1.9], [4.1, -3.9], [4.7, -6.2], [4.3, -8.0], [2.2, -8.9], [0, -8.7], [-2.2, -8.9]];
    solid(body, '#FF4B6A', { shade: '#D02A50', sh: .9, line, lw, size: 8 });
    for (let i = 0; i < 16; i++) { const u = hash2(i, 41), v = hash2(i, 42), px = (u - .5) * 7 * (1 - v * .6), py = -7.6 + v * 5.6; if (Math.abs(px) < 2.6 && py > -7 && py < -3.6) continue; ctx.save(); ctx.translate(px, py); ctx.rotate(px * .15); ctx.fillStyle = '#FFE08A'; ctx.beginPath(); ctx.ellipse(0, 0, .16, .26, 0, 0, TAU); ctx.fill(); ctx.restore(); }
    ctx.fillStyle = alpha(IP.white, .5); ctx.beginPath(); ctx.ellipse(-2.6, -7.3, .8, .35, -.4, 0, TAU); ctx.fill();
    // leafy crown + stem
    const crown = []; for (let i = 0; i < 12; i++) { const a = Math.PI + i / 11 * Math.PI, r = i % 2 ? 1.2 : 3.4; crown.push([Math.cos(a) * r * 1.2, -8.6 + Math.sin(a) * r * .5, 1]); }
    solid(crown, '#3FC07A', { shade: '#2A9A5A', sh: .3, line: IP.line, lw: .14, sharp: true });
    ln([[0, -9.1], [.3, -10.2]], '#2A9A5A', .45);
    // face
    const eyes = o.eyes ?? 'dot', dark = '#2A1433';
    for (const sd of [-1, 1]) {
      ctx.save(); ctx.translate(sd * 1.5, -5.7);
      if (eyes === 'fluster') brush([[-sd * .55, -.4], [sd * .45, 0], [-sd * .55, .4]], .32, dark, 'flat');
      else if (eyes === 'spark') sparkle(0, 0, .9, 0, IP.neonGold, { glow: false });
      else { ctx.fillStyle = dark; ctx.beginPath(); ctx.ellipse(0, 0, .5, .72, 0, 0, TAU); ctx.fill(); ctx.fillStyle = IP.white; ctx.beginPath(); ctx.ellipse(-.14, -.26, .18, .22, 0, 0, TAU); ctx.fill(); }
      ctx.restore();
      ctx.fillStyle = alpha('#FFB3D6', .8); ctx.beginPath(); ctx.ellipse(sd * 2.7, -4.8, .6, .32, 0, 0, TAU); ctx.fill();
    }
    if (o.mouth === 'O') { ctx.fillStyle = '#7A1030'; ctx.beginPath(); ctx.ellipse(0, -4.4, .35, .45, 0, 0, TAU); ctx.fill(); }
    else if (o.mouth === 'wavy') brush([[-.6, -4.5], [-.3, -4.65], [0, -4.45], [.3, -4.65], [.6, -4.5]], .18, line, 'flat');
    else brush(qbez([-.6, -4.6], [0, -4.0], [.6, -4.6], 6), .2, line, 'mid', { min: .4 });
    if (o.sweat) sweatDrop(4.2, -8.4, .7, .14);
    nameBadge('o1', 0, -2.6, 1.3, IP.neonPink);
    ctx.restore();
  }
  const SW = 'STRAWBERRY';
  line('V1', 13, (p, lt, d, t) => {
    const b3 = bl(t, lt, 3), done = lt >= b3;
    bgGrad('#FFF0F4', '#FFB8CC');
    patternBG('polka', 'rgb(0 0 0 / 0)', 'rgb(255 255 255 / .55)', { cell: 100, dx: t * 20 });
    enter(lt, 960, 540, 1);
    // the question
    solid(rrPts(120, 60, 1000, 110, 55), IP.white, { shade: false, line: IP.neonPink, lw: 8, sharp: true, dropShadow: [8, 10] });
    dtext("HOW MANY R'S IN “STRAWBERRY”?", 620, 118, 46, { fill: IP.ink, maxW: 920 });
    // the chain of thought, one link at a time
    const N = SW.length, L = i => [640 + i * 124, 520 - Math.sin(i / (N - 1) * Math.PI) * 110];
    for (let j = 0; j < 3; j++) { const k = pk(lt, .02 + j * .04, .1); if (k > 0) solid(ellPts(470 + j * 55, 640 - j * 60, (10 + j * 7) * backOut(k, 2), (10 + j * 7) * backOut(k, 2), 16), IP.white, { shade: false, line: IP.line, lw: 4 }); }
    let rCount = 0, shown = 0;
    for (let i = 0; i < N; i++) {
      const born = .12 + i * .1, k = pk(lt, born, .12); if (k <= 0) break; shown = i + 1;
      const [x, y] = L(i), isR = SW[i] === 'R', z = backOut(k, 2.4);
      if (i > 0) { const [px, py] = L(i - 1); ln([[px + 40, py], [x - 40, y]], '#9C8CB8', 10); }
      ctx.save(); ctx.translate(x, y); ctx.scale(z, z); ctx.rotate(i % 2 ? .08 : -.08);
      ctx.scale(1.12, 1.12); ctx.lineWidth = 14; ctx.strokeStyle = IP.line; rrect(-50, -44, 100, 88, 40); ctx.stroke();
      ctx.lineWidth = 8; ctx.strokeStyle = isR ? IP.neonPink : '#C9B6FF'; ctx.stroke();
      ctx.fillStyle = isR ? 'rgb(255 61 168 / .2)' : 'rgb(255 255 255 / .85)'; ctx.fill();
      dtext(SW[i], 0, 3, 50, { fill: isR ? IP.neonPink : IP.ink, strokes: isR ? [[IP.white, 8]] : [] });
      ctx.restore();
      if (isR) { rCount++; const c = backOut(pk(lt, born + .05, .12), 3); ctx.save(); ctx.translate(x + 34, y - 62); ctx.scale(c, c); solid(ellPts(0, 0, 26, 26, 18), IP.neonGold, { shade: false, line: IP.line, lw: 4 }); dtext(String(rCount), 0, 2, 32, { fill: IP.ink }); ctx.restore(); }
    }
    // o1 squints… then gets it
    const hop = done ? Math.abs(Math.sin((lt - b3) * 12)) * .8 * Math.exp(-(lt - b3) * 3) : 0;
    berry(350, 935, 44, { eyes: done ? 'spark' : 'fluster', mouth: done ? 'O' : 'wavy', sweat: done ? 0 : 1, aL: done ? .6 : -.3, aR: done ? .7 : .9 + .15 * Math.sin(t * 14), jump: hop, sq: done ? 0 : .03 * Math.sin(t * 20) });
    if (!done) { for (let i = 0; i < 3; i++) { const a = -2 + i * .5; ln([[360 + Math.cos(a) * 230, 580 + Math.sin(a) * 200], [360 + Math.cos(a) * 270, 580 + Math.sin(a) * 240]], IP.red, 6); } }
    camEnd();
    if (done) {
      vcap('3!', 1600, 760, { style: 'pink', size: 200, pop: pk(lt, b3, .14), rot: -.08, icon: 'spark' });
      flash(lt, b3, .1, .5);
    }
  });

  // =====================================================================================================
  // V1.14  Newsom vetoes, doesn't blink,   (SEP 29 2024 · RELU)
  // =====================================================================================================
  line('V1', 14, (p, lt, d, t) => {
    const b0 = bl(t, lt, 0), b1 = bl(t, lt, 1), b2 = bl(t, lt, 2);
    const blinkK = lt > b1 && lt < b1 + .16 ? Math.sin((lt - b1) / .16 * Math.PI) : 0, lost = lt > b1;
    const push = i => 1 + .05 * Math.exp(-frac(bpOf(t)) * 4) * ((beatN(t) % 2 === i) ? 1 : 0);
    const strain = clamp(lt / b1);
    splitPanels(2, (i, x, y, w, h) => {
      if (i === 0) {
        bgGrad('#FFF6C8', '#FFD86A');
        speedLines(430, 520, { r0: 380, alpha: .55, n: 60, col: IP.white });
        enterAt(lt, 430, 520, push(0));
        const tr = jit(2 + 3 * strain);
        chibi(430 + tr, 1080, 80, { hair: 'swoop', hairCol: '#3A2A20', skin: 0, top: 'suit', topCol: '#2A3A6A', tie: IP.neonCyan, eyes: 'wide', mouth: lost ? 'smirk' : 'flat', brows: 'angry', blush: .2, sweat: strain, tagCol: IP.neonGold, shadow: false });
        // bloodshot, watering, but open
        for (const sd of [-1, 1]) {
          const ex = 430 + tr + sd * .88 * 80, ey = 1080 - 6.9 * 80;
          ctx.save(); ctx.beginPath(); ctx.ellipse(ex, ey, 36, 44, 0, 0, TAU); ctx.clip();
          for (let j = 0; j < 6; j++) { const a = j / 6 * TAU + .3; ln([[ex + Math.cos(a) * 36, ey + Math.sin(a) * 44], [ex + Math.cos(a) * (24 - 6 * strain), ey + Math.sin(a) * (30 - 8 * strain)], [ex + Math.cos(a + .2) * 18, ey + Math.sin(a + .2) * 22]], alpha(IP.red, .25 + .5 * strain), 3); }
          ctx.fillStyle = alpha('#9FDCFF', .75); ctx.fillRect(ex - 40, ey + 44 - 30 * strain, 80, 40);
          ctx.restore();
          if (lt > b1) brush([[ex, ey + 44], [ex + sd * 6, ey + 90 + 60 * frac(t * 2)], [ex, ey + 160]], 16, alpha('#9FDCFF', .9), 'mid', { min: .4 });
        }
        camEnd();
      } else {
        bgGrad('#E4F6FF', '#8FD0FF');
        speedLines(1480, 500, { r0: 380, alpha: .55, n: 60, col: IP.white });
        enterAt(lt, 1480, 500, push(1));
        // the bill, staring back
        ctx.save(); ctx.translate(1480 + jit(2), 520); ctx.rotate(.03);
        solid(rrPts(-240, -320, 480, 640, 18), IP.white, { shade: '#E0E8F0', sh: 12, line: IP.line, lw: 7, sharp: true, dropShadow: [12, 16] });
        ctx.save(); rrect(-240, -320, 480, 640, 18); ctx.clip(); ctx.fillStyle = '#4A6ADF'; ctx.fillRect(-240, -320, 480, 110); ctx.restore();
        dtext('SB 1047', 0, -262, 64, { fill: IP.white, strokes: [['#1E2E8A', 10]] });
        for (let j = 0; j < 4; j++) { ctx.fillStyle = 'rgb(60 40 90 / .2)'; ctx.fillRect(-190, 170 + j * 32, j === 3 ? 200 : 380, 12); }
        for (const sd of [-1, 1]) {
          const ex = sd * 100, ey = -20;
          if (blinkK > .3) brush(qbez([ex - 70, ey], [ex, ey + 30], [ex + 70, ey], 8), 12, IP.ink, 'mid', { min: .5 });
          else if (lost) { ctx.save(); ctx.translate(ex, ey); solid(ellPts(0, 0, 66, 76, 24), IP.white, { shade: false, line: IP.ink, lw: 6 }); ctx.strokeStyle = IP.ink; ctx.lineWidth = 6; ctx.beginPath(); for (let k = 0; k <= 26; k++) { const a = k * .55 + t * 10, r = 2 + k * 1.7; k ? ctx.lineTo(Math.cos(a) * r, Math.sin(a) * r) : ctx.moveTo(0, 0); } ctx.stroke(); ctx.restore(); }
          else { solid(ellPts(ex, ey, 66, 76, 24), IP.white, { shade: false, line: IP.ink, lw: 6 }); solid(ellPts(ex - sd * 12, ey + 6, 38, 50, 20), '#2A3A8A', { shade: false, line: IP.ink, lw: 4 }); solid(ellPts(ex - sd * 12, ey + 10, 18, 24, 12), IP.ink, { shade: false, line: false }); ctx.fillStyle = IP.white; ctx.beginPath(); ctx.arc(ex - sd * 12 - 12, ey - 12, 11, 0, TAU); ctx.fill(); }
          brush([[ex - 70, ey - 100 - 8 * strain], [ex + 60, ey - 95 + sd * 16]], 14, IP.ink, 'mid', { min: .4 });
        }
        brush(qbez([-50, 110], [0, lost ? 90 : 125], [50, 110], 6), 9, IP.ink, 'mid', { min: .5 });
        // VETO
        const st = pk(lt, b2, .1);
        if (st > 0) { ctx.save(); ctx.translate(40, 60); ctx.rotate(-.22); const z = lerp(2.2, 1, easeOut(st)); ctx.scale(z, z); ctx.globalAlpha *= .93; ctx.strokeStyle = IP.red; ctx.lineWidth = 20; ctx.beginPath(); ctx.arc(0, 0, 190, 0, TAU); ctx.stroke(); ctx.lineWidth = 7; ctx.beginPath(); ctx.arc(0, 0, 158, 0, TAU); ctx.stroke(); dtext('VETO', 0, 6, 110, { fill: IP.red }); ctx.restore(); }
        ctx.restore();
        camEnd();
      }
    }, { slant: 120, cols: [IP.neonGold, IP.neonCyan] });
    // the stare: a crackling line across the divide
    if (!lost) { const pts = []; for (let i = 0; i <= 12; i++) { const u = i / 12; pts.push([lerp(560, 1360, u), lerp(530, 500, u) + (i % 12 ? jit(22) : 0)]); } add(() => ln(pts, alpha(IP.neonGold, .5), 26)); ln(pts, IP.white, 7); }
    vcap("DON'T BLINK!", 960, 120, { style: 'white', size: 56, pop: pk(lt, b0 * .5, .15), rot: -.03 });
    if (lost) sfx('BLINK!', 1130, 760, { size: 70, pop: pk(lt, b1, .1), rot: .12, grad: ['#FFFFFF', '#BFE8FF', '#4A9ADF'] });
  });

  // =====================================================================================================
  // V1.15  Hinton takes his medal, scolds,   (OCT 8 2024 · ADA)
  // =====================================================================================================
  line('V1', 15, (p, lt, d, t) => {
    const b0 = bl(t, lt, 0), b2 = bl(t, lt, 2), tf = b2, scold = lt >= tf;
    const tc = scold ? t - lt + tf + Math.sin(t * 3) * .004 : t;          // the confetti freezes mid-air when he scolds
    rays(960, 520, 20, '#FFF3B8', '#FFE070', t * .2 * (scold ? .15 : 1));
    enter(lt, 960, 540, 1);
    ledWall(560, 50, 800, 190, (w, h) => { bgGrad('#2A0E52', '#12051F', { y1: h }); dtext('1st WIN', w * .5, h * .4, h * .46, { fill: IP.neonGold, strokes: [[IP.white, 8]] }); dtext('NOBEL PRIZE · PHYSICS', w * .5, h * .82, h * .15, { font: 'code', fill: IP.white }); }, { cols: 120 });
    ctx.fillStyle = '#F7C95A'; ctx.fillRect(-400, 880, W + 800, 400);
    solid(rrPts(640, 880, 640, 70, 16), '#FF8FC8', { shade: false, line: IP.line, lw: 5, sharp: true });
    // ADA, the MC, clapping… until the scolding
    idol(330, 930, 34, { sd: 1, member: 'ADA', ...(scold ? IDOL_POSES.shock : idolMove('clap', bpOf(t))), expr: scold ? 'surprised' : 'joy', blink: t, gR: scold ? 'open' : 'flat' });
    // GEOFF with his medal
    const wag = Math.sin(t * 18) * .35, G = 54, gy = 885;
    chibi(960, gy, G, { hair: 'swoop', hairCol: '#E8E8EE', top: 'suit', topCol: '#6A6A7A', tie: IP.red, glasses: true, eyes: scold ? 'dot' : 'happy', brows: scold ? 'angry' : undefined, mouth: scold ? 'open' : 'grin', aL: scold ? -1.1 : .4, aR: scold ? .45 : .4, blush: scold ? 0 : .7,
      hold: scold ? (u => { ctx.save(); ctx.rotate(wag * .7 - .15); solid(rrPts(-.26, -1.9, .52, 1.6, .24), CHIBI_SKIN[0], { shade: false, line: '#A0525E', lw: .08, sharp: true }); ctx.restore(); }) : undefined });
    ln([[960 - 34, gy - 4.8 * G], [960, gy - 3.4 * G], [960 + 34, gy - 4.8 * G]], '#4A6ADF', 16);
    ctx.save(); ctx.translate(960, gy - 3.1 * G); ctx.rotate(Math.sin(t * 6) * .08);
    add(() => glow(0, 0, 110, IP.neonGold, .5));
    solid(ellPts(0, 0, 52, 52, 26), IP.neonGold, { shade: '#E0A020', sh: 7, line: '#8A5A10', lw: 5 });
    dtext('NOBEL', 0, 2, 21, { fill: '#8A5A10' });
    ctx.restore();
    if (scold) for (let i = 0; i < 3; i++) { const a = -1.2 + i * .35; ln([[960 + 2.9 * G + Math.cos(a) * 130, gy - 6.5 * G + Math.sin(a) * 130], [960 + 2.9 * G + Math.cos(a) * 170, gy - 6.5 * G + Math.sin(a) * 170]], IP.red, 6); }
    // confetti: cannons on the downbeat, frozen by the scolding
    for (const [x, a, sd] of [[120, -1.1, 1], [W - 120, -2.05, 2]]) confetti(tc, t - lt + b0, x, 880, a, { n: 55, seed: 70 + sd, speed: 1700, life: 4 });
    if (scold) { ctx.fillStyle = 'rgb(140 160 220 / .16)'; ctx.fillRect(-400, -400, W + 800, H + 800); }
    // BE CAREFUL!
    if (scold) {
      const k = backOut(pk(lt, tf, .14), 2.5);
      ctx.save(); ctx.translate(1420, 330); ctx.scale(k, k); ctx.rotate(.04);
      solid([[-250, -80], [250, -80], [250, 80], [-120, 80], [-230, 150, 1], [-190, 80], [-250, 80]], IP.white, { shade: false, line: IP.line, lw: 7, sharp: true, dropShadow: [8, 10] });
      dtext('BE CAREFUL!', 0, 2, 66, { fill: IP.red, strokes: [[IP.white, 6]] });
      ctx.restore();
    }
    camEnd();
    flash(lt, b0, .12, .5, '255 245 200');
    if (!scold) vcap('CONGRATS!', 400, 330, { style: 'pink', size: 64, pop: pk(lt, b0 + .08, .15), icon: 'heart', rot: -.06 });
  });

  // =====================================================================================================
  // V1.16  Demis wins for protein folds.   (OCT 9 2024 · LOGI)
  // =====================================================================================================
  const RIB = ['#3A5BFF', '#35B8FF', '#35E8C8', '#9BE85A', '#FFD23F', '#FF8A3A', '#FF4B6A'];
  const ribCol = u => { const x = u * (RIB.length - 1), i = Math.min(RIB.length - 2, Math.floor(x)); return mixCol(RIB[i], RIB[i + 1], x - i); };
  line('V1', 16, (p, lt, d, t) => {
    const b1 = bl(t, lt, 1), b2 = bl(t, lt, 2), snapT = b2, medal = lt >= snapT;
    bgGrad('#E6FFF6', '#9FDCFF');
    patternBG('stars', 'rgb(0 0 0 / 0)', 'rgb(255 255 255 / .5)', { cell: 110, dy: t * 20 });
    enter(lt, 960, 540, 1 + p * .03);
    // ATTN! on a riser, doing the "folding" arm-roll
    solid(rrPts(260, 560, 1400, 60, 16), '#C9B6FF', { shade: false, line: IP.line, lw: 5, sharp: true });
    ['ADA', 'TOKI', 'RELU', 'LOGI'].forEach((m, i) => idol(420 + i * 360, 575, 21, { member: m, sd: .5, ...idolMove('roll', bpOf(t) - i * .12), expr: medal ? 'joy' : 'smile', mouth: singVis(t, i), blink: t + i }));
    ctx.fillStyle = '#B8ECD8'; ctx.fillRect(-400, 900, W + 800, 400);
    // DEMIS folds a ribbon into a protein
    const hx = 560 + (1.05 + Math.cos(.35) * 2.1) * 44, hy = 930 - (4.25 + Math.sin(.35) * 2.1) * 44;
    const cx = 1200, cy = 560, fk = ease(clamp(lt / (b1 + .1))), collapse = clamp((lt - snapT + .08) / .08);
    if (!medal) {
      const N = 70, P = [];
      for (let i = 0; i <= N; i++) {
        const u = i / N;
        const ux = hx + u * 1300, uy = hy - 60 + Math.sin(u * TAU * 2.5 - t * 6) * 40 * u;
        const a = u * TAU * 1.3, r = 150 + 50 * Math.sin(u * TAU * 3), hlx = Math.cos(u * TAU * 10) * 44, hly = Math.sin(u * TAU * 10) * 26;
        let fx = cx + Math.cos(a) * r * 1.05 + hlx, fy = cy + Math.sin(a) * r * .8 + hly;
        if (u < .12) { const k = u / .12; fx = lerp(hx, cx + Math.cos(.12 * TAU * 1.3) * 160, k); fy = lerp(hy, cy + Math.sin(.12 * TAU * 1.3) * 130, k); }
        let px = lerp(ux, fx, fk), py = lerp(uy, fy, fk);
        if (collapse > 0 && u > .1) { px = lerp(px, cx, easeIn(collapse)); py = lerp(py, cy, easeIn(collapse)); }
        P.push([px, py]);
      }
      ln(P, IP.line, 30, { smooth: true });
      for (let i = 0; i < N; i++) ln([P[i], P[i + 1]], ribCol(i / N), 20);
      for (let i = 0; i < N; i += 7) sparkle(P[i][0], P[i][1] - 6, 6 * fk, 0, IP.white, { glow: false });
    } else {
      // …which snaps into a Nobel medal
      const a = lt - snapT, k = backOut(clamp(a / .18), 2.6);
      confetti(t, t - lt + snapT, cx, cy, -Math.PI / 2, { n: 70, spread: 3, speed: 1300, seed: 88 });
      ln([[hx, hy], [cx - 60, cy + 40]], '#4A6ADF', 12);
      ctx.save(); ctx.translate(cx, cy); ctx.scale(k, k); ctx.rotate(Math.sin(t * 5) * .05);
      solid([[-70, -250], [0, -130], [70, -250], [110, -250], [30, -110], [-30, -110], [-110, -250]], '#4A6ADF', { shade: '#2A48C8', sh: 8, line: IP.line, lw: 5, sharp: true });
      add(() => glow(0, 0, 320, IP.neonGold, .6));
      solid(ellPts(0, 0, 150, 150, 40), IP.neonGold, { shade: '#E0A020', sh: 16, line: '#8A5A10', lw: 8 });
      solid(ellPts(0, 0, 118, 118, 40), '#FFE27A', { shade: false, line: '#C08A20', lw: 4 });
      dtext('NOBEL', 0, -24, 50, { fill: '#8A5A10' }); dtext('ALPHAFOLD', 0, 34, 30, { font: 'code', fill: '#8A5A10' });
      ctx.restore();
      sparkle(cx + 140, cy - 120, 40, t * 3, IP.white);
    }
    chibi(560, 930, 44, { hair: 'buzz', hairCol: '#2A2228', top: 'suit', topCol: '#2A3A6A', tie: IP.neonCyan, skin: 2, eyes: medal ? 'spark' : 'happy', mouth: 'grin', aR: .35 + .1 * Math.sin(t * 8), aL: medal ? .7 : -.9, jump: medal ? Math.abs(Math.sin((lt - snapT) * 10)) * 1.5 * Math.exp(-(lt - snapT) * 4) : 0, tagCol: IP.neonCyan });
    camEnd();
    flash(lt, snapT, .12, .7, '255 250 220');
    if (!medal) sfx('FOLD!', 1200, 250, { size: 80, pop: pk(lt, b1, .12), rot: -.1, grad: ['#FFFFFF', '#AEE3FF', '#3A5BFF'] });
    if (medal) vcap('NOBEL!', 1550, 280, { style: 'yellow', size: 90, pop: pk(lt, snapT + .03, .15), icon: 'star', rot: -.07 });
  });

})();

;
// ---- styles/idol/ch/c03_chorus1.js ----
// c03_chorus1 — Chorus 1: ATTN!'s debut stage. Seven sub-shots, all timed from the sung lines (linesOf('C1')) and the beat grid.
//   A1 "We didn't start the scaling —"   lights slam on: wide stage, the hook lights up word by word on the LED wall, confetti cannons,
//                                          the group does the hook choreo (point at self, finger-wag, sweep the arm up the curve).
//   A2   (on "scaling")                   punch-in: TOKI close-up, star eyes, pointing up, speed lines.
//   B  "It was always training,"          the dance-practice video: 3 AM practice room, mirror, EPOCH counter ticking up; "TRAINEE DAY"
//                                          counts days since "Attention" (Jun 12 2017) to the date on the card, +1 per beat.
//   C  "and the curves kept gaining,"     CURVE FORMATION: the members ride stage lifts that rise one per beat into an exponential; TOKI shoots
//                                          off the top; the lightstick ocean does a Mexican wave.
//   D  "We didn't start the scaling —"    Clawd in the crowd raises his phone → his fancam of TOKI (REC overlay).
//   E  "No, we didn't preordain it,"      split screen: four members cross their arms "NO!", then finger-wag, smug.
//   F  "but we can't contain it!"         the LED wall's CONTAINMENT box bursts; the curve escapes the screen; cannons; reaction cam.
//   G  (instrumental tail)                ENDING FAIRY: TOKI's out-of-breath close-up, wink + finger heart; freezes into a photocard.
(() => {
  const snap = x => onBeat(0, Math.round(bpOf(x)));
  function plan() {
    const S = span('C1'), L = linesOf('C1');
    const tA2 = snap(lerp(L[0].start, L[0].end, .56));
    const tB = L[1].start - .05, tC = snap(lerp(L[1].start, L[1].end, .47));
    const tD = L[2].start - .05, tD2 = snap(tD + .55);
    const tE = L[3].start - .03, tF = snap(lerp(L[3].start, L[3].end, .5)), tG = Math.min(S.end - .9, L[3].end + .05);
    return { S, L, tA2, tB, tC, tD, tD2, tE, tF, tG };
  }
  const flash = (t, t0, dur = .2, a = .75, col = '255 245 255') => { const k = (t - t0) / dur; if (k >= 0 && k < 1) { ctx.fillStyle = `rgb(${col} / ${(a * (1 - k) ** 2).toFixed(3)})`; ctx.fillRect(-400, -400, W + 800, H + 800); } };

  // ---------------- A1: the wide stage with the hook on the LED wall ----------------
  const HOOK = [['WE', 0, IP.white], ["DIDN'T", .1, IP.neonCyan], ['START', .24, IP.neonGold], ['THE', .38, IP.lilac], ['SCALING', .5, IP.neonPink]];
  function hookLED(t, ln, w, h) {
    bgGrad('#12051F', '#2A0E52', { y1: h });
    ledShow('rays', t, w, h, { c0: '#1A0833', c1: '#2A0E52' });
    const dur = ln.end - ln.start, rows = [[0, 1, 2], [3, 4]];
    rows.forEach((row, r) => {
      let size = r ? h * .36 : h * .24, ws = row.map(i => textW(HOOK[i][0], size, 'rammetto') + size * .45);
      const fit = Math.min(1, w * .92 / ws.reduce((a, b) => a + b, 0)); size *= fit; ws = ws.map(v => v * fit);
      let x = w / 2 - ws.reduce((a, b) => a + b, 0) / 2;
      row.forEach((i, j) => {
        const [word, at, col] = HOOK[i], cx = x + ws[j] / 2; x += ws[j];
        const a = T - (wordTimes(ln)?.starts[i] ?? ln.start + at * dur); if (a < 0) return;   // (as it's sung, where the timing has the words' times)
        const s = backOut(clamp(a / .18), 2.5) * (i === 4 ? 1 + .06 * pulse(T, 6) : 1);
        ctx.save(); ctx.translate(cx, h * (r ? .66 : .3)); ctx.scale(s, s);
        dtext(word, 0, 0, size, { fill: col, strokes: [[IP.night, size * .22]] });
        ctx.restore();
      });
    });
    if (T > ln.start + .5 * dur) { const k = clamp((T - ln.start - .5 * dur) / .6); ln2curve(w, h, k); }
  }
  function ln2curve(w, h, k) {
    const pts = []; for (let i = 0; i <= 30; i++) { const u = i / 30; pts.push([w * .08 + u * w * .84, h * .95 - (Math.exp(u * 3.4) - 1) / (Math.exp(3.4) - 1) * h * .3]); }
    ln(partial(pts, k), alpha(IP.neonPink, .8), 6);
  }
  function shotA1(t, P) {
    const { L } = P, k = clamp((t - P.S.start) / (P.tA2 - P.S.start));
    const [sx, sy] = t - P.S.start < .5 ? shakeXY(t, 8 * (1 - (t - P.S.start) / .5)) : [0, 0];
    camBegin(960 + sx, 520 + sy - k * 30, 1.0 + k * .07);
    setLight({ rim: IP.neonCyan });
    stageSet(t, { led: (w, h) => hookLED(t, L[0], w, h), level: 1, hue: IP.neonPink, floorY: 690 });
    const down = snap(P.S.start + .1);
    for (const [x, a, sd] of [[180, -1.25, 1], [W - 180, -1.9, -1]]) {
      confetti(t, down, x, 760, a, { n: 60, seed: 31 + sd, speed: 1700 }); ctx.save(); ctx.globalCompositeOperation = 'lighter'; glow(x, 760, 160 * clamp(1 - (t - down) * 3), IP.white, .8); ctx.restore();
    }
    group(t, 960, 905, 33, 'hook', { gap: 165, back: 10, common: { rim: IP.neonCyan } });
    lightOcean(t, { y0: 930, y1: 1130, n: 15, cols: [IP.neonPink, MEMBERS.TOKI.lt, IP.lilac], mode: 'sway' });
    fanClawd(330, 1070, 11, { stick: 'R', aR: 1.1 + Math.sin(bpOf(t) * Math.PI) * .3, band: 'TOKI', eyes: 'heart', mouth: 'open', shadow: false, dy: -Math.abs(Math.sin(bpOf(t) * Math.PI)) * 1.2 });
    camEnd();
    flare(1460, 70, .7 + .3 * pulse(t, 4));
    flash(t, P.S.start, .25, .85);
    hideCaption();
  }
  // ---------------- A2: TOKI close-up on "scaling" ----------------
  function shotA2(t, P) {
    const lt = t - P.tA2, b = bpOf(t);
    bgGrad(IP.neonPink, IP.plum, { radial: true, cx: 900, cy: 420, r: 1100 });
    speedLines(900, 440, { r0: 420, alpha: .55, n: 80 });
    bokeh(t, { n: 10, r: 90 });
    const zoom = lerp(1.12, 1, easeOut(clamp(lt / .25)));
    camBegin(960, 540, zoom);
    setLight({ rim: IP.neonCyan });
    idol(880, 470, 210, { anchor: 'face', expr: 'sparkle', mouth: singVis(t, 3), hR: [1.05, -2.2], gR: 'point', hL: [-.9, 1.2], tilt: -.08 + Math.sin(b * Math.PI) * .03, lookY: -.4, turn: .15, blink: undefined });
    camEnd();
    sparkles(t, { n: 14, x0: 1200, x1: 1800, y0: 80, y1: 700, r: 30 });
    flare(1180, 120, .9);
    flash(t, P.tA2, .12, .6);
  }

  // ---------------- B: the dance-practice video ----------------
  function practiceRoom(t) {
    ctx.fillStyle = '#EDE6F7'; ctx.fillRect(-100, -100, W + 200, 760);
    // mirror wall
    const g = ctx.createLinearGradient(0, 110, 0, 650); g.addColorStop(0, '#CFE3F2'); g.addColorStop(1, '#E6F0F8');
    ctx.fillStyle = g; ctx.fillRect(60, 110, W - 120, 540);
    // wooden floor in perspective
    const fg = ctx.createLinearGradient(0, 650, 0, H); fg.addColorStop(0, '#D8AE84'); fg.addColorStop(1, '#C08A5E'); ctx.fillStyle = fg; ctx.fillRect(-100, 650, W + 200, H);
    ctx.strokeStyle = 'rgb(120 70 40 / .35)'; ctx.lineWidth = 2; ctx.beginPath();
    for (let i = -12; i <= 12; i++) { ctx.moveTo(960 + i * 90, 650); ctx.lineTo(960 + i * 300, H + 40); }
    ctx.stroke();
    ctx.fillStyle = '#B99AD8'; ctx.fillRect(-100, 640, W + 200, 16);   // skirting board
  }
  function mirrorSheen() {
    ctx.save(); ctx.beginPath(); ctx.rect(60, 110, W - 120, 540); ctx.clip();
    ctx.fillStyle = 'rgb(255 255 255 / .35)';
    for (const [x, w] of [[300, 90], [420, 30], [1250, 120], [1400, 40]]) { ctx.beginPath(); ctx.moveTo(x, 110); ctx.lineTo(x + w, 110); ctx.lineTo(x + w - 260, 650); ctx.lineTo(x - 260, 650); ctx.fill(); }
    ctx.restore();
    ctx.strokeStyle = '#9C8CB8'; ctx.lineWidth = 8; ctx.strokeRect(60, 110, W - 120, 540);
    for (let i = 1; i < 4; i++) { ctx.lineWidth = 3; ctx.beginPath(); ctx.moveTo(60 + i * (W - 120) / 4, 110); ctx.lineTo(60 + i * (W - 120) / 4, 650); ctx.stroke(); }
  }
  function wallClock(x, y, r) {
    solid(ellPts(x, y, r, r, 30), IP.white, { shade: '#D8D0EA', sh: r * .1, line: IP.line, lw: 4 });
    for (let i = 0; i < 12; i++) { const a = i / 12 * TAU; ln([[x + Math.cos(a) * r * .78, y + Math.sin(a) * r * .78], [x + Math.cos(a) * r * .88, y + Math.sin(a) * r * .88]], IP.line, 3); }
    ln([[x, y], [x + r * .5, y]], IP.line, 6); ln([[x, y], [x, y - r * .7]], IP.line, 4);   // 3:00
    dtext('AM', x, y + r * .42, r * .26, { font: 'code', fill: IP.neonPink });
  }
  function whiteboard(t, x, y, lt) {
    solid(rrPts(x, y, 330, 240, 10), IP.white, { shade: '#E0DCEA', sh: 8, line: IP.line, lw: 5, sharp: true });
    ln([[x + 150, y + 240], [x + 110, y + 400]], '#8A7AA8', 8); ln([[x + 180, y + 240], [x + 220, y + 400]], '#8A7AA8', 8);
    dtext('LOSS', x + 30, y + 30, 26, { font: 'marker', fill: IP.inkSoft, align: 'left' });
    const pts = []; for (let i = 0; i <= 30; i++) { const u = i / 30; pts.push([x + 30 + u * 270, y + 60 + 150 * (1 - Math.exp(-u * 4))]); }
    ln(partial(pts, .6 + .4 * clamp(lt / 1.5)), IP.red, 5, { smooth: true });
    dtext('↓ GOOD', x + 250, y + 200, 22, { font: 'marker', fill: IP.red });
  }
  function shotB(t, P) {
    const lt = t - P.tB, b = bpOf(t);
    const pan = easeOut(clamp(lt / 3)) * 40;
    camBegin(960 + pan, 540, 1.02);
    practiceRoom(t);
    // mirror reflections: the dancers from behind, a bit smaller and bluer
    ctx.save(); ctx.beginPath(); ctx.rect(60, 110, W - 120, 540); ctx.clip();
    ctx.globalAlpha = .55;
    ['ADA', 'TOKI', 'RELU', 'LOGI'].forEach((m, i) => { const mv = idolMove('step', b); idol(560 + i * 270, 640, 26, { member: m, outfit: 'practice', back: true, ...mv, sway: -(mv.sway ?? 0), shadow: false }); });
    ctx.globalAlpha = 1; ctx.fillStyle = 'rgb(160 200 235 / .25)'; ctx.fillRect(60, 110, W - 120, 540);
    ctx.restore();
    mirrorSheen();
    wallClock(1360, 58, 42);
    attnLogo(960, 58, 50, {});
    dtext('PRACTICE ROOM', 1110, 60, 24, { font: 'code', fill: IP.inkSoft, align: 'left' });
    whiteboard(t, 1480, 470, lt);
    // floor props: water bottles + towel
    for (const [x, c] of [[150, '#9FE3FF'], [200, '#FFB3D6'], [1830, '#C9B6FF']]) { solid(rrPts(x - 16, 900, 32, 80, 10), alpha(c, .85), { shade: false, line: IP.line, lw: 3, sharp: true }); ctx.fillStyle = IP.white; ctx.fillRect(x - 10, 890, 20, 14); }
    // the dancers, in sync
    setLight({ rim: null });
    ['ADA', 'TOKI', 'RELU', 'LOGI'].forEach((m, i) => {
      const x = 480 + i * 320, mv = idolMove('step', b - i * .04);
      idol(x, 1000, 34, { member: m, outfit: 'practice', mic: false, ...mv, expr: i === 1 ? 'fired' : 'smile', mouth: singVis(t, i), blink: t + i });
      // sweat flung off on the beat
      const age = t - onBeat(0, beatN(t));
      if (age < .3) for (let j = 0; j < 3; j++) { const a = -1.6 + (hash2(beatN(t) + i, j) - .5) * 2, v = 280; const px = x + Math.cos(a) * v * age, py = 700 + Math.sin(a) * v * age + 900 * age * age; sweatDrop(px, py, 9, 2); }
    });
    camEnd();
    // practice-video UI
    ctx.fillStyle = 'rgb(20 8 40 / .6)'; rrect(40, 36, 760, 64, 16); ctx.fill();
    dtext("ATTN! 'WE DIDN'T START THE SCALING' DANCE PRACTICE", 60, 69, 22, { align: 'left', fill: IP.white, maxW: 720 });
    const ep = 9996 + beatN(t) - beatN(P.tB);
    rrect(40, 112, 330, 56, 14); ctx.fillStyle = IP.neonPink; ctx.fill();
    dtext(`EPOCH ${fmtN(ep)}`, 205, 141, 28, { font: 'code', fill: IP.white });
    vcap(`TRAINEE DAY ${fmtN(dDay(segByKey('V1.1')).n - dDay(dateInfo(t).seg).n + beatN(t) - beatN(P.tB))}`, 1060, 230, { style: 'lilac', size: 52, pop: clamp((lt - .2) / .25), rot: -.03 });
  }

  // ---------------- C: CURVE FORMATION on rising stage lifts ----------------
  const LIFT = [['ADA', 0], ['RELU', 70], ['LOGI', 190], ['TOKI', 470]];
  function shotC(t, P) {
    const lt = t - P.tC, d = P.tD - P.tC, b0 = Math.round(bpOf(P.tC));
    const tilt = easeInOut(clamp((lt - d * .55) / (d * .4)));
    camBegin(960, 540 - tilt * 170, 1 - tilt * .05);
    setLight({ rim: IP.neonPink });
    stageSet(t, { led: (w, h) => ledShow('curve', t, w, h, { k: clamp(lt / (d * .8)), level: 2 }), level: 2, hue: IP.neonCyan, floorY: 690 });
    const heads = [];
    LIFT.forEach(([m, hMax], i) => {
      const x = 520 + i * 300, bt = onBeat(0, b0 + i * 2), k = backOut(clamp((t - bt) / .35), 1.4);
      const lift = hMax * k, gy = 900 - lift;
      // the lift: a glowing pillar
      if (lift > 2) { solid(rrPts(x - 110, gy + 18, 220, lift + 10, 8), '#2A1850', { shade: false, line: IP.neonCyan, lw: 4, sharp: true }); ctx.save(); ctx.globalCompositeOperation = 'lighter'; for (let j = 0; j < lift / 40; j++) { ctx.fillStyle = alpha(IP.neonCyan, .35); ctx.fillRect(x - 100, gy + 30 + j * 40, 200, 6); } ctx.restore(); }
      const mv = t > bt ? idolMove('point', bpOf(t)) : idolMove('bounce', bpOf(t));
      idol(x, gy + 20, 27, { member: m, ...mv, expr: m === 'TOKI' && k > .9 ? 'sparkle' : 'smile', mouth: singVis(t, i), blink: t + i, rim: IP.neonPink });
      heads.push([x, gy + 20 - 27 * 10.3]);
      if (t > bt && t < bt + .5) { ctx.save(); ctx.globalCompositeOperation = 'lighter'; glow(x, gy + 10, 200 * (1 - (t - bt) * 2), IP.neonCyan, .8); ctx.restore(); }
    });
    // neon curve through their heads, drawing on
    const C = crSample([[heads[0][0] - 260, heads[0][1] + 60], ...heads, [heads[3][0] + 160, heads[3][1] - 360]], 10, []);
    const kc = clamp((lt - .3) / (d * .7));
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; ln(partial(C, kc), alpha(IP.neonGold, .35), 30); ctx.restore();
    ln(partial(C, kc), IP.neonGold, 10); ln(partial(C, kc), IP.white, 3);
    if (kc > .05) { const tip = partial(C, kc).at(-1); sparkle(tip[0], tip[1], 40, t * 3, IP.white); }
    lightOcean(t, { y0: 940, y1: 1160, n: 14, cols: [IP.neonCyan, IP.lilac, IP.neonPink], mode: 'wave' });
    camEnd();
    vcap('CURVE FORMATION!', 520, 200, { style: 'cyan', icon: 'spark', size: 66, pop: clamp((lt - d * .3) / .25) });
  }
  const easeInOut = k => ease(k);

  // ---------------- D: Clawd raises his phone → the fancam ----------------
  function shotD1(t, P) {
    const lt = t - P.tD;
    bgGrad('#0A0418', IP.plum);
    ctx.save(); ctx.globalCompositeOperation = 'lighter';
    beam(700, 0, .35, { col: IP.neonPink, alpha: .4 }); beam(1300, 0, -.3, { col: IP.neonCyan, alpha: .4 });
    glow(960, 300, 600, IP.neonPink, .35); ctx.restore();
    bokeh(t, { n: 16, r: 60, alpha: .3 });
    lightOcean(t, { y0: 560, y1: 1000, n: 12, cols: [IP.neonPink, MEMBERS.TOKI.lt], mode: 'pump', rows: 6 });
    const up = easeOut(clamp(lt / .3));
    fanClawd(900, 1010, 34, { phone: true, aR: lerp(-.2, 1.25, up), stick: 'L', aL: .6 + Math.sin(bpOf(t) * Math.PI) * .3, band: 'TOKI', eyes: 'heart', mouth: 'open', shadow: false });
  }
  function shotD2(t, P) {
    const lt = t - P.tD2, b = bpOf(t);
    const [hx, hy] = [Math.sin(t * 2.1) * 14 + Math.sin(t * 5.3) * 4, Math.sin(t * 1.7 + 1) * 10];
    camBegin(960 + hx, 520 + hy, 1.55, Math.sin(t * 1.3) * .012);
    setLight({ rim: IP.neonCyan });
    stageSet(t, { led: (w, h) => ledShow('hearts', t, w, h), level: 1, hue: IP.neonPink, floorY: 690, pillars: false });
    idol(1180, 905, 30, { member: 'RELU', ...idolMove('hook', b), mouth: singVis(t, 2), rim: IP.neonCyan });
    camEnd();
    camBegin(960 + hx * .6, 540 + hy * .6, 1);
    idol(930, 1060, 70, { ...idolMove('hook', b), mouth: singVis(t, 1), blink: t, expr: 'sing', eyes: frac(b / 4) > .75 ? 'happy' : 'open', rim: IP.neonCyan, turn: -.1 });
    camEnd();
    bokeh(t, { n: 8, r: 120, alpha: .18, y0: 600, y1: 1080 });
    fancam(t, { member: 'TOKI', title: '[FANCAM] TOKI FOCUS · by CLAWD', zoom: 2.4 + lt * .1, focus: [930, 330] });
    hideStamp();
  }

  // ---------------- E: split screen "NO!" + finger wag ----------------
  function shotE(t, P) {
    const lt = t - P.tE, d = P.tF - P.tE, no = lt < d * .38;
    const order = ['ADA', 'TOKI', 'RELU', 'LOGI'];
    splitPanels(4, (i, x, y, w, h) => {
      const M = MEMBERS[order[i]];
      bgGrad(M.lt, M.col, { y1: H });
      patternBG('polka', 'rgb(0 0 0 / 0)', alpha(IP.white, .35), { cell: 90, dx: t * 30 * (i % 2 ? 1 : -1), dy: t * 20 });
      const cx = x + w / 2 + (i - 1.5) * -20;
      const pose = no ? { ...IDOL_POSES.xarms, expr: 'pout', emote: undefined } : { ...idolMove('wag', bpOf(t) - i * .25), expr: 'smug' };
      const pk = no ? backOut(clamp(lt / .15), 2) : 1;
      idol(cx, 420 + (1 - pk) * 60, 118, { member: order[i], anchor: 'face', ...pose, mouth: no ? 'O' : pose.mouth ?? 'smirk', rim: IP.white, blink: t + i });
      nameCap(M.name, cx, 90, 30, M.col);
    }, { slant: 110, cols: order.map(k => MEMBERS[k].col) });
    hideStamp();
    if (no) vcap('NO!', 960, 720, { style: 'shock', size: 170, pop: clamp(lt / .12), shake: 4, rot: -.06 });
  }

  // ---------------- F: the containment breach ----------------
  function containLED(t, w, h, burst) {
    bgGrad('#12051F', '#2A0E52', { y1: h });
    const bx = w * .18, by = h * .16, bw = w * .64, bh = h * .7, rat = burst < 0 ? clamp(1 + burst * 1.2) : 0;
    if (burst < 0) {
      const [jx, jy] = [jit(rat * 14), jit(rat * 10)];
      ctx.save(); ctx.translate(jx, jy);
      ctx.fillStyle = '#FFD23F'; ctx.fillRect(bx - 14, by - 14, bw + 28, bh + 28); ctx.fillStyle = '#12051F'; ctx.fillRect(bx, by, bw, bh);
      ctx.fillStyle = '#12051F'; for (let i = 0; i < 20; i++) { ctx.beginPath(); ctx.moveTo(bx - 14 + i * 60, by - 14); ctx.lineTo(bx + 16 + i * 60, by - 14); ctx.lineTo(bx - 14 + i * 60, by + 16); ctx.fill(); }
      dtext('CONTAINMENT', w / 2, by + bh * .18, h * .1, { fill: IP.neonGold });
      const pts = []; for (let i = 0; i <= 30; i++) { const u = i / 30; pts.push([bx + 20 + u * (bw - 40), by + bh - 20 - (Math.exp(u * 4) - 1) / (Math.exp(4) - 1) * (bh - 40) * (1 + .08 * pulse2(t, 5))]); }
      ln(pts, IP.neonPink, 10); ln(pts, IP.white, 3);
      ctx.restore();
    } else {
      // shattered: static + shards
      for (let i = 0; i < 60; i++) { ctx.fillStyle = hash2(_boil, i) > .5 ? IP.neonPink : IP.lilac; ctx.fillRect(hash2(i, _boil + 1) * w, hash2(i + 7, _boil) * h, 30, 6); }
      dtext('ERROR: CURVE NOT FOUND', w / 2, h * .5, h * .09, { font: 'code', fill: IP.neonGold });
    }
  }
  function shotF(t, P) {
    const lt = t - P.tF, d = P.tG - P.tF, tb = snap(P.tF + d * .38), burst = t - tb;
    const [sx, sy] = burst > 0 && burst < .5 ? shakeXY(t, 18 * (1 - burst / .5)) : burst < 0 ? shakeXY(t, 3) : [0, 0];
    camBegin(960 + sx, 520 + sy, burst > 0 ? 1.02 - clamp(burst / 1.2) * .06 : 1.04);
    setLight({ rim: IP.neonGold });
    stageSet(t, { led: (w, h) => containLED(t, w, h, burst), level: 2, hue: burst > 0 ? IP.neonGold : IP.red, floorY: 690 });
    // the escaped curve: a neon line from the LED wall shooting up out of the frame
    if (burst > 0) {
      const k = easeOut(clamp(burst / .5)), pts = [];
      for (let i = 0; i <= 40; i++) { const u = i / 40; pts.push([560 + u * 900, 560 - (Math.exp(u * 4.2) - 1) / (Math.exp(4.2) - 1) * 1300]); }
      const P2 = partial(pts, k);
      ctx.save(); ctx.globalCompositeOperation = 'lighter'; ln(P2, alpha(IP.neonPink, .4), 60); ctx.restore();
      ln(P2, IP.neonPink, 22); ln(P2, IP.white, 7);
      const tip = P2.at(-1); sparkle(tip[0], tip[1], 70, t * 4, IP.white);
      for (const [x, a] of [[140, -1.2], [560, -1.45], [1360, -1.7], [1780, -1.95]]) confetti(t, tb, x, 740, a, { n: 45, seed: x, speed: 1900 });
    }
    const air = burst > 0 && burst < .55 ? Math.sin(burst / .55 * Math.PI) * 1.6 : 0;
    group(t, 960, 905, 31, burst > 0 ? 'bounce' : 'bounce', { gap: 160, back: 10, common: burst > 0 ? { expr: 'surprised', rim: IP.neonGold, jump: air, hL: [-1.2, -2.1], hR: [1.2, -2.1], gL: 'open', gR: 'open', fL: [-.5, -air * .3], fR: [.5, -air * .3] } : { expr: 'sing', rim: IP.neonGold } });
    lightOcean(t, { y0: 930, y1: 1130, n: 15, cols: [IP.neonGold, IP.neonPink, IP.white], mode: 'pump', k: burst > 0 ? 1.4 : .8 });
    fanClawd(300, 1068, 11, { towel: 'TOKI ♥', eyes: burst > 0 ? 'cry' : 'heart', mouth: burst > 0 ? 'wail' : 'open', shadow: false, dy: -Math.abs(Math.sin(bpOf(t) * Math.PI)) * 1.5 });
    camEnd();
    if (burst > 0) { flash(t, tb, .18, .9, '255 250 220'); flare(1100, 90, 1.2); }
    // reaction cam (picture-in-picture)
    const pk = backOut(clamp((lt - .1) / .2), 2);
    if (pk > 0) {
      ctx.save(); ctx.translate(1640, 700); ctx.scale(pk, pk); ctx.rotate(.03);
      rrect(-190, -140, 380, 280, 26); ctx.fillStyle = IP.white; ctx.fill();
      ctx.save(); rrect(-178, -128, 356, 256, 18); ctx.clip();
      bgGrad(IP.pink, IP.lilac, { y0: 560, y1: 840 });
      idol(0, 10, 60, { anchor: 'face', expr: burst > 0 ? 'shock' : 'surprised', mic: false, swing: 0, blink: t });
      ctx.restore();
      rrect(-120, -168, 240, 44, 22); ctx.fillStyle = MEMBERS.TOKI.col; ctx.fill();
      dtext("TOKI'S REACTION", 0, -145, 20, { fill: IP.white });
      ctx.restore();
    }
    else vcap('!?', 1250, 320, { style: 'yellow', size: 90, pop: clamp((lt - .1) / .15), shake: 3 });
  }

  // ---------------- G: the ending fairy → photocard ----------------
  function fairy(t, lt, w, h) {
    bgGrad('#FFD6EC', '#C9B6FF', { radial: true, cx: w * .45, cy: h * .4, r: w * .9 });
    bokeh(t, { n: 12, r: 110, alpha: .35, cols: [IP.white, IP.pink, IP.lemon] });
    const pk = clamp((lt - .45) / .2), breath = Math.sin(t * 7) * 5;
    idol(w * .47, h * .44 + breath, h * .21, { anchor: 'face', ...IDOL_POSES.fingerHeart, heartPop: pk, expr: pk > 0 ? 'wink' : 'joy', mouth: pk > 0 ? 'tongue' : 'open', tilt: -.1, turn: .12, sweat: .7, blush: .9, rim: IP.white });
    sparkles(t, { n: 12, x0: w * .55, x1: w * .95, y0: h * .05, y1: h * .6, r: h * .03, cols: [IP.white, IP.lemon] });
  }
  function shotG(t, P) {
    const lt = t - P.tG, d = P.S.end - P.tG, card = clamp((lt - (d - .5)) / .3);
    if (card <= 0) {
      fairy(t, lt, W, H);
      vcap('ENDING FAIRY', 360, 150, { style: 'pink', icon: 'star', size: 64, pop: clamp((lt - .1) / .25), rot: -.05 });
    } else {
      bgGrad(IP.lav, IP.pink);
      patternBG('hearts', 'rgb(0 0 0 / 0)', alpha(IP.white, .5), { cell: 110, dy: t * 40 });
      const k = easeOut(card);
      photocard(960, 540, lerp(1400, 420, k), { rot: lerp(0, -.08, k), draw: (w, h) => { ctx.save(); ctx.scale(w / W, w / W); fairy(t, lt, W, h * W / w); ctx.restore(); }, name: 'TOKI', sign: '♡ toki', holo: .6 * k });
      sparkle(1230, 250, 40 * k, t * 3, IP.white);
      hideCaption();
    }
  }

  section('C1', (p, lt, d, t) => {
    const P = plan();
    if (t < P.tA2) shotA1(t, P);
    else if (t < P.tB) shotA2(t, P);
    else if (t < P.tC) shotB(t, P);
    else if (t < P.tD) shotC(t, P);
    else if (t < P.tD2) shotD1(t, P);
    else if (t < P.tE) shotD2(t, P);
    else if (t < P.tF) shotE(t, P);
    else if (t < P.tG) shotF(t, P);
    else shotG(t, P);
  });
})();

;
// ---- styles/idol/ch/c04_v2.js ----
// c04_v2 — Verse 2: 2025, "the money year". Mint, coral, sky and money gold; the date card moves by months.
// One gag per line, hard cuts on the downbeat, warm and cool backgrounds alternating:
//   1 DeepSeek      a blue whale pops up at a Lunar New Year party wearing a SALE sticker ($$$$$$ → $5.6M); NVDA dives; TOKI drops her stick
//   2 Stargate      a giant ring portal with a $500,000,000,000 odometer; SAM/LARRY/MASA at the podium; ELON's phone: "they don't have the money"
//   3 Accept All    vibe coding as a rhythm game: ANDREJ in headphones smashes ACCEPT ALL on every beat, PERFECT!, the diff scrolls unread
//   4 MCP           one "MCP" plug hub snakes cables into a toaster, a calendar, a database, an amp and Clawd's lightstick, one per eighth
//   5 Zuck          TRANSFER SEASON claw machine: ZUCK plucks a researcher clutching a $100M bag out of the glass box; SCALE AI 49%
//   6 buy three!    home-shopping TV: RELU hosts, three SUPERINTELLIGENCE boxes (SSI / OPENAI / META), BUY 3!, CALL NOW
//   7 Grok          GROK's LCD glitches red, a CENSORED bar slams over it, a hand yanks the plug, x eyes, YIKES hanko (no imagery beyond that)
//   8 IMO gold      two bots squeezed onto the #1 podium block; medals drop; a joint idol heart; 35/42; math-symbol confetti
//   9 GPT-5 / 4o    member change: a vaudeville hook yanks warm 4o off stage, cool GPT-5 slides in, the 4o heart cracks, #keep4o fans cry, 4o peeks back
//  10 Nano Banana   the app chart: NANO BANANA climbs #3 → #1 past ChatGPT; the shades-wearing banana gets a crown
//  11 $1.5B         a sweating Clawd hands a giant cheque to THE AUTHORS
//  12 Everyone Dies ELIEZER's book drops onto the signing table, THUD; NYT BESTSELLER seal; the idols huddle in shock
//  13 Clanker       a wall of phones spits CLANKER! bubbles at a sad bot; Clawd pats its back
//  14 Sora slop     the feed swipes to a fake TOKI with six fingers; pastel slop pours out of the phone into a FEED trough; the real TOKI, deadpan
//  15 LeCun         YANN drops the mic and walks off META's stage toward a neon WORLD MODELS → sign; the LED switches to SUPERINTELLIGENCE LABS
//  16 Bubble        a BUBBLE?! business page slams in; a soap bubble of GPUs and dollars swells; TOKI creeps up with a pin... cut
(() => {
  const bl = () => 60 / BPM;
  const kin = (lt, at, dur = .18) => clamp((lt - at) / dur);                  // 0..1 ramp (for vcap/vtag/sfx pop)
  const bo = (lt, at, dur = .18, s = 2.5) => backOut(kin(lt, at, dur), s);   // overshooting pop scale
  const zoomIn = (lt, z = .07, dur = .16) => 1 + z * (1 - easeOut(clamp(lt / dur)));
  const flash = (lt, at = 0, dur = .12, a = .7, col = '255 250 245') => { const k = (lt - at) / dur; if (k >= 0 && k < 1) { ctx.fillStyle = `rgb(${col} / ${(a * (1 - k) ** 2).toFixed(3)})`; ctx.fillRect(-400, -400, W + 800, H + 800); } };
  const easeInOut = k => ease(k);
  // A round "hanko" seal stamped onto anything. k: 0..1 slam.
  function hanko(text, x, y, r, k, o = {}) {
    if (k <= 0) return;
    const col = o.col ?? IP.red;
    ctx.save(); ctx.translate(x, y); ctx.rotate(o.rot ?? -.2);
    const sc = k < 1 ? lerp(1.9, 1, easeOut(k)) : 1; ctx.scale(sc, sc); ctx.globalAlpha *= clamp(k * 3) * .94;
    ctx.fillStyle = o.bg ?? 'rgb(255 250 240 / .92)'; ctx.beginPath(); ctx.arc(0, 0, r, 0, TAU); ctx.fill();
    ctx.strokeStyle = col; ctx.lineWidth = r * .11; ctx.beginPath(); ctx.arc(0, 0, r, 0, TAU); ctx.stroke();
    ctx.lineWidth = r * .045; ctx.beginPath(); ctx.arc(0, 0, r * .8, 0, TAU); ctx.stroke();
    dtext(text, 0, 0, r * (o.size ?? .42), { fill: col, maxW: r * 1.45 });
    ctx.restore();
  }
  // Sale starburst sticker. o: pop, rot, col, ink, size, lh
  function starburst(x, y, r, text, o = {}) {
    const k = o.pop ?? 1; if (k <= 0) return;
    ctx.save(); ctx.translate(x, y); ctx.rotate((o.rot ?? -.1) + Math.sin(T * 7) * .03); const s = backOut(clamp(k), 2.6); ctx.scale(s, s);
    solid(burstPts(0, 0, r, 18, .82), o.col ?? IP.neonGold, { shade: o.shade ?? '#F0A21A', sh: r * .09, line: IP.line, lw: r * .045, sharp: true, dropShadow: [r * .05, r * .08] });
    const lines = text.split('\n');
    lines.forEach((l, i) => dtext(l, 0, (i - (lines.length - 1) / 2) * r * (o.lh ?? .46), r * (o.size ?? .4), { fill: o.ink ?? IP.red, strokes: [[IP.white, r * .09]], maxW: r * 1.45 }));
    ctx.restore();
  }
  // Deterministic flying bits: n particles fired from (x, y) at t0. draw(i, px, py, rot, age)
  function burst(t, t0, x, y, n, o, draw) {
    const age = t - t0; if (age < 0 || age > (o.life ?? 2)) return;
    for (let i = 0; i < n; i++) {
      const r = k => hash2((o.seed ?? 1) * 31 + i, k), a = (o.ang ?? -Math.PI / 2) + (r(1) - .5) * (o.spread ?? 2.4), v = (o.v ?? 1200) * (.55 + r(2) * .6);
      const px = x + Math.cos(a) * v * age, py = y + Math.sin(a) * v * age + (o.g ?? 1600) * age * age * .5;
      if (py > H + 100) continue;
      draw(i, px, py, (r(3) - .5) * 2 + age * (r(4) - .5) * 14, age);
    }
  }
  // A cartoon hand with a sleeve cuff, reaching in from off-screen. ang = direction the fingers point.
  function reachHand(x, y, ang, g, size, sleeve) {
    const bx = x - Math.cos(ang) * size * 4, by = y - Math.sin(ang) * size * 4;
    limbChain([[bx, by], [x - Math.cos(ang) * size * .2, y - Math.sin(ang) * size * .2]], [size * .34, size * .3], sleeve, mixCol(sleeve, IP.plum, .3), IP.line, size * .05);
    hand([x, y], ang, size, g, 1, size * .05);
  }

  // =========================================================================================
  // V2.1 DeepSeek New Year sticker shock (JAN 2025)
  // =========================================================================================
  const WHALE = [[-1.0, .08], [-.96, -.38], [-.66, -.7], [-.1, -.82], [.45, -.68], [.85, -.4], [1.1, -.44], [1.26, -.68], [1.1, -.97, 1], [1.42, -.88], [1.6, -.72], [1.95, -1.0, 1], [1.84, -.6], [1.52, -.3], [1.22, .08], [.85, .42], [.3, .62], [-.35, .6], [-.8, .4]];
  function whale(x, y, s, o = {}) {
    const col = '#5A9BFF', dk = '#3A6FE0', line = '#1E2E7A';
    ctx.save(); ctx.translate(x, y); ctx.rotate(o.rot ?? 0); const sq = o.sq ?? 0; ctx.scale(s * (1 + sq * .4), s * (1 - sq));
    solid(ellPts(.3, .46, .3, .13, 18, .7), dk, { shade: false, line, lw: .028 });
    solid(WHALE, col, { shade: dk, sh: .1, line, lw: .03, size: 1, rimW: .03 });
    ctx.save(); crPath(WHALE); ctx.clip();
    ctx.fillStyle = '#D6ECFF'; ctx.beginPath(); ctx.ellipse(-.25, .68, 1.08, .4, -.05, 0, TAU); ctx.fill();
    for (let i = 0; i < 5; i++) ln([[-.74 + i * .24, .4 - i * .012], [-.66 + i * .26, .66]], alpha(line, .25), .018);
    ctx.fillStyle = alpha(IP.white, .4); ctx.beginPath(); ctx.ellipse(-.42, -.56, .3, .085, -.35, 0, TAU); ctx.fill();
    ctx.restore();
    crPath(WHALE); ctx.strokeStyle = line; ctx.lineWidth = .03; ctx.lineJoin = 'round'; ctx.stroke();
    if (o.eye === 'happy') brush(qbez([-.62, -.13], [-.5, -.32], [-.38, -.13], 8), .05, '#1A1440', 'mid', { min: .4 });
    else if (o.eye === 'wide') { ctx.fillStyle = IP.white; ctx.beginPath(); ctx.ellipse(-.5, -.17, .12, .15, 0, 0, TAU); ctx.fill(); ctx.strokeStyle = '#1A1440'; ctx.lineWidth = .02; ctx.stroke(); ctx.fillStyle = '#1A1440'; ctx.beginPath(); ctx.arc(-.5, -.16, .04, 0, TAU); ctx.fill(); }
    else { ctx.fillStyle = '#1A1440'; ctx.beginPath(); ctx.ellipse(-.5, -.17, .085, .12, 0, 0, TAU); ctx.fill(); ctx.fillStyle = IP.white; ctx.beginPath(); ctx.ellipse(-.525, -.21, .035, .045, 0, 0, TAU); ctx.fill(); ctx.beginPath(); ctx.arc(-.47, -.11, .018, 0, TAU); ctx.fill(); }
    ctx.fillStyle = alpha('#FF7FA0', .6); ctx.beginPath(); ctx.ellipse(-.63, .05, .1, .05, 0, 0, TAU); ctx.fill();
    ctx.fillStyle = '#9A2E4E'; ctx.beginPath(); ctx.moveTo(-.97, .12); ctx.quadraticCurveTo(-.86, .34, -.7, .15); ctx.closePath(); ctx.fill(); ctx.strokeStyle = line; ctx.lineWidth = .02; ctx.stroke();
    solid(ellPts(-.16, .42, .25, .1, 18, -.6), col, { shade: dk, sh: .04, line, lw: .028 });
    ctx.restore();
  }
  function spout(x, y, s, t) {
    const k = .8 + .25 * pulse(t, 4);
    for (const sd of [-1, 0, 1]) brush(qbez([x, y], [x + sd * s * .12, y - s * .55 * k], [x + sd * s * .36, y - s * .4 * k], 10), s * .075, alpha('#DDF4FF', .95), 'start', { min: .3 });
    for (let i = 0; i < 7; i++) { const ph = frac(t * 1.6 + i / 7), sd = i % 2 ? 1 : -1, a = ph; ctx.fillStyle = alpha('#DDF4FF', .9 * (1 - ph)); ctx.beginPath(); ctx.arc(x + sd * s * (.2 + .3 * a), y - s * .5 * k + s * .5 * a * a, s * .03, 0, TAU); ctx.fill(); }
  }
  function lantern(x, y, s, sw) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(sw);
    ln([[0, -200], [0, s * .9]], '#8A2A1A', s * .07);
    const cy = s * 2;
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; glow(0, cy, s * 2.2, '#FF9A3D', .45); ctx.restore();
    solid(ellPts(0, cy, s * 1.08, s * .95, 36), '#FF3B3B', { shade: '#C8202E', sh: s * .2, line: '#7A1020', lw: s * .07 });
    for (const k of [-.55, 0, .55]) ln(qbez([k * s * .6, cy - s * .9], [k * s * 1.25, cy], [k * s * .6, cy + s * .9], 10), alpha('#7A1020', .5), s * .05, { smooth: true });
    for (const yy of [cy - s * 1.05, cy + s * .8]) solid(rrPts(-s * .5, yy, s, s * .26, s * .08), IP.neonGold, { shade: '#D09A20', sh: s * .06, line: '#7A4A10', lw: s * .05, sharp: true });
    ln([[0, cy + s * 1.06], [Math.sin(T * 3) * s * .1, cy + s * 1.9]], IP.neonGold, s * .14);
    ctx.restore();
  }
  function saleTag(x, y, w, rot, k) {
    if (k <= 0) return;
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot); const s = k < 1 ? lerp(1.8, 1, easeOut(k)) : 1; ctx.scale(s, s);
    const h = w * .44, n = h * .38;
    const P = [[-w / 2 + n, -h / 2], [w / 2, -h / 2], [w / 2, h / 2], [-w / 2 + n, h / 2], [-w / 2, 0]];
    solid(P, IP.neonGold, { shade: '#F2A617', sh: h * .1, line: IP.line, lw: 7, sharp: true, dropShadow: [10, 14] });
    ctx.strokeStyle = alpha(IP.white, .7); ctx.lineWidth = 4; ctx.setLineDash([12, 10]); tracePath(xform(P, 0, 0, 0, .9)); ctx.stroke(); ctx.setLineDash([]);
    solid(ellPts(-w / 2 + n * .72, 0, h * .075, h * .075, 16), '#FF7A6B', { shade: false, line: IP.line, lw: 4 });
    dtext('$$$$$$', w * .1, -h * .2, h * .22, { fill: alpha(IP.ink, .55), font: 'code' });
    ln([[w * .1 - w * .26, -h * .19], [w * .1 + w * .26, -h * .23]], IP.red, h * .045);
    dtext('$5.6M', w * .1, h * .14, h * .42, { fill: IP.red, strokes: [[IP.white, h * .1]] });
    ctx.restore();
  }
  function envelope(x, y, rot, sc = 1) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot); ctx.scale(sc, sc);
    solid(rrPts(-22, -32, 44, 64, 6), '#FF3040', { shade: '#C81A2E', sh: 6, line: '#6A0A18', lw: 3, sharp: true });
    ctx.strokeStyle = IP.neonGold; ctx.lineWidth = 3; ctx.strokeRect(-16, -26, 32, 52);
    ctx.fillStyle = IP.neonGold; ctx.beginPath(); ctx.arc(0, -4, 9, 0, TAU); ctx.fill();
    ctx.restore();
  }
  function tickerPanel(x, y, w, h, k, t) {
    ctx.save(); ctx.translate(x, y);
    solid(rrPts(0, 0, w, h, 24), '#1B1030', { shade: false, line: IP.white, lw: 6, sharp: true, dropShadow: [10, 14] });
    dtext('NVDA', 32, 46, 42, { font: 'code', fill: IP.white, align: 'left' });
    ctx.strokeStyle = alpha(IP.lilac, .2); ctx.lineWidth = 2; for (let i = 1; i < 4; i++) { ctx.beginPath(); ctx.moveTo(24, 80 + i * (h - 100) / 4); ctx.lineTo(w - 24, 80 + i * (h - 100) / 4); ctx.stroke(); }
    const pts = []; for (let i = 0; i <= 40; i++) { const u = i / 40, v = u < .5 ? .22 - u * .08 + Math.sin(u * 30) * .03 : .18 + ((u - .5) / .5) ** 1.6 * .78; pts.push([30 + u * (w - 60), 86 + v * (h - 110)]); }
    const P = partial(pts, k);
    ln(P, alpha(IP.red, .35), 16); ln(P, IP.red, 7);
    if (k > .5) { const tip = P.at(-1); solid(ellPts(tip[0], tip[1], 10, 10, 12), IP.red, { shade: false, line: IP.white, lw: 3 }); }
    dtext('▼17%', w - 28, 48, 46, { fill: '#FF5A6A', align: 'right', strokes: [[IP.white, 5]], alpha: clamp(k * 3) });
    ctx.restore();
  }
  line('V2', 1, (p, lt, d, t) => {
    const b = bpOf(t), B = bl();
    rays(900, 520, 22, '#FF6464', '#FF8274', t * .12);
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; glow(900, 520, 760, '#FFD23F', .3); ctx.restore();
    patternBG('polka', 'rgb(0 0 0 / 0)', alpha(IP.neonGold, .16), { cell: 120, dy: t * 24 });
    camBegin(960, 540, zoomIn(lt, .09));
    [[130, 40, 40], [380, 10, 32], [1120, 16, 34], [1370, 0, 30]].forEach(([x, y, s], i) => lantern(x, y, s, Math.sin(t * 2.4 + i * 1.3) * .1));
    // firecracker pops on the beats
    for (let i = 0; i < 3; i++) { const at = i * B * 1.5, a = lt - at; if (a >= 0 && a < .5) { const [fx, fy] = [[260, 330], [560, 190], [300, 520]][i]; ctx.save(); ctx.globalCompositeOperation = 'lighter'; glow(fx, fy, 160 * (1 - a * 2), IP.neonGold, .8); ctx.restore(); for (let j = 0; j < 8; j++) { const aa = j / 8 * TAU + i; sparkle(fx + Math.cos(aa) * a * 420, fy + Math.sin(aa) * a * 420, 16 * (1 - a * 2), aa, j % 2 ? IP.neonGold : IP.white); } sfx('POP!', fx, fy, { size: 58, pop: clamp(a / .1), rot: -.2 + i * .15, shake: 2 }); } }
    // the whale pops up; red envelopes fly out from behind it on beat 1
    const wk = backOut(clamp(lt / .24), 1.7), wx = 880, wy = 560 + Math.sin(b * Math.PI) * 8, ws = 290;
    burst(t, t - lt + B, wx + 60, wy - 40, 16, { seed: 3, v: 1400, spread: 2.6, g: 1700 }, (i, x, y, r) => envelope(x, y, r, 1 + hash(i) * .5));
    if (wk > 0) {
      ctx.save(); ctx.globalCompositeOperation = 'lighter'; glow(wx, wy, 560 * wk, IP.white, .35); ctx.restore();
      ctx.save(); ctx.translate(wx, wy); ctx.scale(wk, wk); ctx.translate(-wx, -wy);
      spout(wx - .22 * ws, wy - .8 * ws, ws, t);
      whale(wx, wy, ws, { eye: lt > B * 2 ? 'happy' : 'open', rot: Math.sin(b * Math.PI * .5) * .03, sq: .04 * pulse(t, 5) });
      ctx.restore();
    }
    // SALE sticker slaps on, beat 1
    const tagAt = B;
    saleTag(wx + .6 * ws, wy + .02 * ws, 400, .1, kin(lt, tagAt, .14));
    if (lt > tagAt && lt < tagAt + .35) for (let i = 0; i < 6; i++) { const a = i / 6 * TAU, r = 120 + (lt - tagAt) * 700; sparkle(wx + .6 * ws + Math.cos(a) * r, wy + Math.sin(a) * r * .6, 26 * (1 - (lt - tagAt) / .35), a, IP.white); }
    // NVDA nose-dives, beat 2
    const tk = kin(lt, 2 * B, .2);
    if (tk > 0) { ctx.save(); ctx.translate(1620, 790); ctx.scale(backOut(tk, 2), backOut(tk, 2)); ctx.rotate(.03); tickerPanel(-250, -140, 500, 290, clamp((lt - 2 * B) / .7), t); ctx.restore(); }
    // SD TOKI drops her lightstick
    const drop = clamp((lt - .25) / .4), lsx = lerp(300, 360, drop), lsy = lerp(720, 900, drop * drop);
    idol(200, 945, 33, { sd: 1, ...IDOL_POSES.shock, expr: 'shock', mic: false, blink: t, jump: lt < .3 ? Math.sin(lt / .3 * Math.PI) * .6 : 0 });
    lightstick(lsx, lsy, 26, MEMBERS.TOKI.col, { rot: drop * 2.2 + (drop >= 1 ? Math.sin(lt * 20) * .05 * Math.exp(-(lt - .65) * 6) : 0) });
    camEnd();
    flash(lt, 0, .1, .8);
  });

  // =========================================================================================
  // V2.2 Half a trillion Stargate talk (JAN 2025)
  // =========================================================================================
  const phoneHold = u => { ctx.save(); ctx.rotate(-.25); solid(rrPts(-.5, -1.9, 1.0, 1.8, .22), '#2B2438', { shade: false, line: IP.line, lw: .12, sharp: true }); ctx.fillStyle = '#9FE8FF'; ctx.fillRect(-.38, -1.76, .76, 1.4); ctx.restore(); };
  line('V2', 2, (p, lt, d, t) => {
    const b = bpOf(t);
    bgGrad([[0, '#0B1540'], [.55, '#1D3C8A'], [1, '#5AA8E8']], null);
    sparkles(t, { n: 26, r: 12, seed: 55, y1: 700, cols: [IP.white, IP.sky] });
    camBegin(960, 540, zoomIn(lt, .07));
    const cx = 900, cy = 400, R = 310;
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; glow(cx, cy, R * 1.9, IP.neonCyan, .45 + .15 * pulse(t, 4)); ctx.restore();
    // event horizon
    ctx.save(); ctx.beginPath(); ctx.arc(cx, cy, R - 50, 0, TAU); ctx.clip();
    const g = ctx.createRadialGradient(cx, cy, 0, cx, cy, R); g.addColorStop(0, '#F2FEFF'); g.addColorStop(.45, '#7FE6FF'); g.addColorStop(1, '#2A5BD8');
    ctx.fillStyle = g; ctx.fillRect(cx - R, cy - R, 2 * R, 2 * R);
    for (let i = 0; i < 7; i++) { const rr = frac(i / 7 - t * .7) * R; ctx.strokeStyle = alpha(IP.white, .45 * (1 - rr / R)); ctx.lineWidth = 12; ctx.beginPath(); ctx.ellipse(cx, cy, rr, rr * .94, 0, 0, TAU); ctx.stroke(); }
    ctx.restore();
    // the ring
    solid(() => { ctx.beginPath(); ctx.arc(cx, cy, R, 0, TAU); ctx.moveTo(cx + R - 56, cy); ctx.arc(cx, cy, R - 56, 0, TAU, true); }, '#8C94C0', { shade: false, line: IP.line, lw: 7, size: 200 });
    ctx.strokeStyle = '#5E6494'; ctx.lineWidth = 12; ctx.beginPath(); ctx.arc(cx, cy, R - 44, 0, TAU); ctx.stroke();
    ctx.strokeStyle = alpha(IP.white, .45); ctx.lineWidth = 6; ctx.beginPath(); ctx.arc(cx, cy, R - 12, Math.PI * 1.05, Math.PI * 1.55); ctx.stroke();
    ctx.fillStyle = '#4A4F7A'; for (let i = 0; i < 40; i++) { const a = i / 40 * TAU; ctx.save(); ctx.translate(cx + Math.cos(a) * (R - 28), cy + Math.sin(a) * (R - 28)); ctx.rotate(a); ctx.fillRect(-4, -7, 8, 14); ctx.restore(); }
    for (let i = 0; i < 9; i++) {
      const a = -Math.PI / 2 + i / 9 * TAU, on = lt > i * .06;
      ctx.save(); ctx.translate(cx + Math.cos(a) * (R + 6), cy + Math.sin(a) * (R + 6)); ctx.rotate(a + Math.PI / 2);
      if (on) { ctx.save(); ctx.globalCompositeOperation = 'lighter'; glow(0, 0, 50, '#FF9A3D', .7); ctx.restore(); }
      solid([[-26, -14], [26, -14], [0, 22]], on ? '#FFB23D' : '#7A6A58', { shade: false, line: IP.line, lw: 4, sharp: true });
      ctx.restore();
    }
    // the odometer
    const target = '$500,000,000,000', fr = Math.floor(t * 30);
    let shown = ''; let di = 0;
    for (const c of target) { if (c === '$' || c === ',') { shown += c; continue; } shown += lt > .12 + di * .07 ? c : String(Math.floor(hash2(di * 13, fr) * 10)); di++; }
    const ck = bo(lt, 0, .2, 2);
    ctx.save(); ctx.translate(cx, cy + 20); ctx.scale(ck, ck);
    solid(rrPts(-400, -70, 800, 140, 70), '#1A1036', { shade: false, line: IP.neonGold, lw: 8, sharp: true, dropShadow: [0, 12] });
    dtext(shown, 0, 4, 84, { font: 'code', fill: IP.neonGold, maxW: 740 });
    ctx.restore();
    // podium + the three execs
    const cheer = i => .5 + .5 * Math.abs(Math.sin((b - i * .15) * Math.PI));
    [['SAM', { hair: 'short', hairCol: '#6A4A30', top: 'sweater', topCol: '#9AA7C8', eyes: 'happy', mouth: 'grin' }], ['LARRY', { hair: 'swoop', hairCol: '#D8D8E0', top: 'suit', topCol: '#3A3A4A', tie: IP.red, eyes: 'dot', mouth: 'smile', skin: 5 }], ['MASA', { hair: 'bald', hairCol: '#2A2228', top: 'suit', topCol: '#20283A', tie: IP.neonCyan, eyes: 'happy', mouth: 'open', skin: 1 }]].forEach(([nm, o], i) => {
      const x = 690 + i * 210, a = .3 + .9 * cheer(i);
      chibi(x, 915, 30, { ...o, name: nm, aL: a, aR: a, dy: -Math.abs(Math.sin((b - i * .2) * Math.PI)) * .5 });
    });
    solid(rrPts(620, 862, 560, 110, 18), '#EDEAF8', { shade: '#C3BCE0', sh: 16, line: IP.line, lw: 6, sharp: true });
    ctx.strokeStyle = IP.neonCyan; ctx.lineWidth = 6; ctx.beginPath(); ctx.arc(750, 916, 26, 0, TAU); ctx.stroke();
    dtext('STARGATE', 925, 918, 48, { fill: '#2A3A7A', font: 'rammetto' });
    // ELON, doubting from the corner
    const ek = kin(lt, .35, .2);
    chibi(1760, 935, 24, { name: 'ELON', hair: 'side', hairCol: '#3A2E28', top: 'tee', topCol: '#1E1A26', eyes: 'smug', mouth: 'smirk', aR: .55, hold: phoneHold, dy: (1 - easeOut(ek)) * 3 });
    if (ek > 0) {
      ctx.save(); ctx.translate(1700, 610); ctx.scale(backOut(ek, 2), backOut(ek, 2));
      ctx.fillStyle = IP.white; ctx.beginPath(); ctx.moveTo(-10, 60); ctx.lineTo(40, 120); ctx.lineTo(40, 55); ctx.fill();
      chatBubble("they don't actually have the money", -400, -10, { size: 32, maxW: 460 });
      ctx.restore();
    }
    camEnd();
    flash(lt, 0, .1, .6);
  });

  // =========================================================================================
  // V2.3 Hit "Accept All," never ask (FEB 2025)
  // =========================================================================================
  function diffPanel(x, y, w, h, lt) {
    solid(rrPts(x, y, w, h, 22), '#1E1430', { shade: false, line: IP.white, lw: 5, sharp: true, dropShadow: [10, 14] });
    ctx.fillStyle = '#3A2A58'; rrect(x, y, w, 60, 22); ctx.fill(); ctx.fillRect(x, y + 30, w, 30);
    dtext('diff  +1,204  −987', x + 24, y + 32, 26, { font: 'code', fill: IP.white, align: 'left' });
    ctx.save(); ctx.beginPath(); ctx.rect(x + 8, y + 64, w - 16, h - 72); ctx.clip();
    const lh = 34, sp = 520;
    for (let j = 0; j < 40; j++) {
      const yy = y + 80 + (((j * lh - lt * sp) % (lh * 40)) + lh * 40) % (lh * 40);
      if (yy > y + h) continue;
      const r = hash2(j, 7), add = r > .45, col = add ? '#3DDC84' : '#FF6B7A';
      ctx.fillStyle = alpha(col, .15); ctx.fillRect(x + 8, yy - 14, w - 16, 28);
      dtext(add ? '+' : '−', x + 28, yy, 24, { font: 'code', fill: col });
      ctx.fillStyle = alpha(col, .8); rrect(x + 52, yy - 7, (w - 90) * (.3 + hash2(j, 3) * .6), 14, 7); ctx.fill();
    }
    ctx.restore();
  }
  function headphones(hx, hy, s) {
    ctx.save(); ctx.lineCap = 'round';
    ctx.strokeStyle = IP.line; ctx.lineWidth = .62 * s; ctx.beginPath(); ctx.arc(hx, hy - .1 * s, 2.55 * s, Math.PI * 1.08, Math.PI * 1.92); ctx.stroke();
    ctx.strokeStyle = IP.mint; ctx.lineWidth = .4 * s; ctx.stroke();
    ctx.restore();
    for (const sd of [-1, 1]) solid(rrPts(hx + sd * 2.45 * s - .5 * s, hy - 1.0 * s, 1.0 * s, 1.8 * s, .45 * s), IP.neonPink, { shade: '#C8287E', sh: .2 * s, line: IP.line, lw: .09 * s, sharp: true });
  }
  line('V2', 3, (p, lt, d, t) => {
    const B = bl(), ph = frac(lt / B), hitN = Math.floor(lt / B);
    bgGrad([[0, '#FFE0B0'], [1, '#FF9AAE']], null);
    patternBG('grid', 'rgb(0 0 0 / 0)', alpha(IP.white, .45), { cell: 64, dy: t * 140 });
    camBegin(960, 540, zoomIn(lt, .06));
    diffPanel(50, 200, 420, 560, lt);
    // the rhythm lane
    const LX = 1440, LW = 240, LY = 160, HIT = 790;
    solid(rrPts(LX, LY, LW, 740, 26), 'rgb(40 20 70 / .78)', { shade: false, line: IP.white, lw: 5, sharp: true });
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; ctx.fillStyle = alpha(IP.neonPink, .5 + .4 * Math.exp(-ph * 8)); ctx.fillRect(LX + 8, HIT - 6, LW - 16, 12); glow(LX + LW / 2, HIT, 160 * (.5 + Math.exp(-ph * 8)), IP.neonPink, .5); ctx.restore();
    ctx.save(); rrect(LX, LY, LW, 740, 26); ctx.clip();
    for (let k = hitN + 1; k < hitN + 8; k++) { const ny = HIT - (k * B - lt) * 800; if (ny < LY - 40) continue; solid(rrPts(LX + 18, ny - 30, LW - 36, 60, 30), '#3DDC84', { shade: '#1FA860', sh: 6, line: IP.white, lw: 4, sharp: true }); dtext('ACCEPT ALL', LX + LW / 2, ny + 2, 25, { fill: IP.white, strokes: [['#11603A', 5]] }); }
    ctx.restore();
    if (ph < .3) { const r = 60 + ph * 500; ctx.strokeStyle = alpha(IP.white, 1 - ph / .3); ctx.lineWidth = 8; ctx.beginPath(); ctx.ellipse(LX + LW / 2, HIT, r, r * .35, 0, 0, TAU); ctx.stroke(); }
    const jk = backOut(clamp(ph / .1), 3);
    ctx.save(); ctx.translate(1225, 560); ctx.scale(jk, jk); ctx.rotate(hitN % 2 ? .06 : -.06);
    dtext('PERFECT!', 0, 0, 76, { grad: ['#FFFFFF', '#FFF36B', '#FF8A3D'], strokes: [[IP.white, 16], [IP.line, 8]], alpha: clamp((1 - ph) * 3) });
    ctx.restore();
    dtext(`COMBO ×${128 + hitN}`, 1225, 650, 36, { font: 'code', fill: IP.white, strokes: [[IP.line, 7]] });
    // ANDREJ, eyes closed, slamming the button on every beat
    const armA = ph < .72 ? lerp(-.5, 1.15, easeOut(ph / .72)) : lerp(1.15, -.5, easeIn((ph - .72) / .28));
    const ax = 740, ay = 940, s = 52, press = Math.exp(-ph * 9), bob = -Math.abs(Math.sin(ph * Math.PI)) * .25;
    // the button (under the hand's lowest point)
    const bx = ax + 3.25 * s, by = ay - 2.55 * s, BR = 100;
    solid(rrPts(bx - 105, by, 210, ay - by, 18), '#EDE7FA', { shade: '#BDB2DE', sh: 14, line: IP.line, lw: 6, sharp: true });
    dtext('ACCEPT', bx, by + 60, 36, { fill: '#1FA860' }); dtext('ALL', bx, by + 104, 44, { fill: '#1FA860' });
    solid(ellPts(bx, by + 4, BR + 12, 26, 30), '#2A2440', { shade: false, line: IP.line, lw: 5 });
    const dh = 54 * (1 - press * .6);
    solid(() => { ctx.beginPath(); ctx.ellipse(bx, by, BR, dh, 0, Math.PI, TAU); ctx.ellipse(bx, by, BR, 22, 0, 0, Math.PI); }, '#3DDC84', { shade: '#1FA860', sh: 12, line: IP.line, lw: 6, size: 90 });
    ctx.fillStyle = alpha(IP.white, .6); ctx.beginPath(); ctx.ellipse(bx - 45, by - dh * .55, 26, 9, -.3, 0, TAU); ctx.fill();
    if (press > .3) { ctx.save(); ctx.globalCompositeOperation = 'lighter'; glow(bx, by - 10, 260 * press, '#8FFFB8', .6 * press); ctx.restore(); sfx('CLICK!', bx + 170, by - 90, { size: 54, pop: clamp(ph / .06), rot: .15, shake: 1 }); }
    chibi(ax, ay, s, { name: 'ANDREJ', hair: 'short', hairCol: '#3A2A26', top: 'hoodie', topCol: '#6A8BE8', eyes: 'happy', mouth: 'grin', blush: .9, aR: armA, aL: -.9 + .3 * Math.sin(lt * 9), dy: bob });
    headphones(ax, ay + (bob - 6.95) * s, s);
    emote('note', ax - 170, ay - 520 - frac(lt * 1.2) * 60, 64, 1);
    emote('note', ax + 170, ay - 590 - frac(lt * 1.2 + .5) * 60, 50, 1);
    vcap('VIBE CODING', 910, 175, { style: 'pink', size: 62, pop: kin(lt, .1, .2), rot: -.05, icon: 'note' });
    camEnd();
  });

  // =========================================================================================
  // V2.4 MCP for every task (MAR 2025)
  // =========================================================================================
  function devToaster(x, y, lit) {
    const up = lit > 0 ? backOut(clamp(lit / .25), 2.5) : 0;
    for (const dx of [-44, 44]) solid(rrPts(x + dx - 34, y - 96 - up * 70, 68, 90, 22), '#F4C27A', { shade: '#D8995A', sh: 8, line: '#7A4A20', lw: 4 });
    solid(rrPts(x - 120, y - 80, 240, 160, 44), lit > 0 ? '#FFC2D4' : '#E8C7D2', { shade: '#E68AA6', sh: 14, line: IP.line, lw: 6, sharp: true });
    for (const dx of [-44, 44]) { ctx.fillStyle = '#5A2A40'; rrect(x + dx - 38, y - 86, 76, 14, 7); ctx.fill(); }
    miniFace(x - 10, y + 10, 30, lit > 0);
    solid(rrPts(x + 118, y - 20, 22, 14, 5), '#8A7AA8', { shade: false, line: IP.line, lw: 3, sharp: true });
  }
  function devCalendar(x, y, lit) {
    solid(rrPts(x - 110, y - 110, 220, 220, 22), IP.white, { shade: '#DCD4F0', sh: 12, line: IP.line, lw: 6, sharp: true });
    ctx.save(); rrect(x - 110, y - 110, 220, 220, 22); ctx.clip(); ctx.fillStyle = lit > 0 ? IP.red : '#C98A92'; ctx.fillRect(x - 110, y - 110, 220, 56); ctx.restore();
    dtext('MAR', x, y - 82, 30, { fill: IP.white });
    for (let r = 0; r < 3; r++) for (let c = 0; c < 5; c++) { ctx.fillStyle = alpha(IP.inkSoft, .3); ctx.fillRect(x - 88 + c * 36, y - 36 + r * 42, 26, 26); }
    if (lit > 0) { ctx.strokeStyle = IP.red; ctx.lineWidth = 7; ctx.beginPath(); ctx.ellipse(x + 2, y + 18, 30, 26, 0, 0, TAU * clamp(lit / .25)); ctx.stroke(); }
    for (const dx of [-50, 50]) solid(rrPts(x + dx - 7, y - 128, 14, 36, 7), '#8A8FA6', { shade: false, line: IP.line, lw: 3, sharp: true });
  }
  function devDatabase(x, y, lit) {
    const col = lit > 0 ? '#9FE3FF' : '#B8C8D8';
    for (let i = 2; i >= 0; i--) { const yy = y - 70 + i * 60; solid(() => { ctx.beginPath(); ctx.ellipse(x, yy + 50, 90, 26, 0, 0, Math.PI); ctx.lineTo(x - 90, yy); ctx.ellipse(x, yy, 90, 26, 0, Math.PI, TAU); ctx.closePath(); }, col, { shade: mixCol(col, IP.plum, .3), sh: 12, line: IP.line, lw: 5, size: 90 }); }
    solid(ellPts(x, y - 70, 90, 26, 30), mixCol(col, IP.white, .4), { shade: false, line: IP.line, lw: 5 });
    if (lit > 0) for (let i = 0; i < 3; i++) { ctx.fillStyle = frac(T * 4 + i * .3) < .5 ? IP.neonLime : '#2A6A4A'; ctx.beginPath(); ctx.arc(x + 60, y - 30 + i * 60, 7, 0, TAU); ctx.fill(); }
  }
  function devAmp(x, y, lit) {
    solid(rrPts(x - 120, y - 110, 240, 190, 20), '#2A2436', { shade: '#16121E', sh: 12, line: IP.line, lw: 6, sharp: true });
    ctx.save(); rrect(x - 100, y - 60, 200, 124, 12); ctx.fillStyle = '#4A4060'; ctx.fill(); ctx.clip(); ctx.strokeStyle = '#2A2436'; ctx.lineWidth = 4; for (let i = -10; i < 12; i++) { ctx.beginPath(); ctx.moveTo(x - 110 + i * 20, y - 70); ctx.lineTo(x - 50 + i * 20, y + 70); ctx.stroke(); } ctx.restore();
    for (let i = 0; i < 4; i++) solid(ellPts(x - 78 + i * 38, y - 86, 11, 11, 12), IP.gold, { shade: false, line: IP.line, lw: 3 });
    if (lit > 0) { const k = pulse2(T, 6); ctx.save(); ctx.translate(x, y); ctx.scale(1 + .04 * k, 1 + .04 * k); ctx.restore(); for (let i = 0; i < 3; i++) emote('note', x - 60 + i * 60, y - 160 - frac(T * 1.5 + i * .33) * 60, 44, clamp(lit / .2)); }
  }
  function miniFace(x, y, r, happy) {
    for (const sd of [-1, 1]) { if (happy) brush(qbez([x + sd * r - r * .4, y + r * .1], [x + sd * r, y - r * .5], [x + sd * r + r * .4, y + r * .1], 8), r * .22, '#2A1433', 'mid', { min: .4 }); else { ctx.fillStyle = '#2A1433'; ctx.beginPath(); ctx.arc(x + sd * r, y, r * .22, 0, TAU); ctx.fill(); } }
    if (happy) { ctx.fillStyle = '#9A2E4E'; ctx.beginPath(); ctx.moveTo(x - r * .4, y + r * .4); ctx.quadraticCurveTo(x, y + r * 1.1, x + r * .4, y + r * .4); ctx.closePath(); ctx.fill(); }
    else brush([[x - r * .3, y + r * .55], [x + r * .3, y + r * .55]], r * .14, '#2A1433', 'flat');
    ctx.fillStyle = alpha('#FF7FA0', .55); for (const sd of [-1, 1]) { ctx.beginPath(); ctx.ellipse(x + sd * r * 1.7, y + r * .45, r * .35, r * .2, 0, 0, TAU); ctx.fill(); }
  }
  function usbPlug(x, y, ang, s = 1) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(ang); ctx.scale(s, s);
    solid(rrPts(-46, -17, 42, 34, 10), '#F4F2FA', { shade: '#C9C2E0', sh: 5, line: IP.line, lw: 4, sharp: true });
    solid(rrPts(-6, -11, 24, 22, 9), '#C9CEDD', { shade: '#8A8FA6', sh: 3, line: IP.line, lw: 3.5, sharp: true });
    ctx.fillStyle = IP.line; rrect(1, -4, 14, 8, 4); ctx.fill();
    ctx.restore();
  }
  line('V2', 4, (p, lt, d, t) => {
    bgGrad([[0, '#E4FFF5'], [1, '#86E6CC']], null);
    patternBG('grid', 'rgb(0 0 0 / 0)', alpha(IP.white, .6), { cell: 72, dx: t * 30 });
    camBegin(960, 540, zoomIn(lt, .06));
    const hub = [960, 520], E = .165;
    const DEV = [
      { x: 390, y: 350, port: [528, 330], draw: devToaster },
      { x: 1330, y: 300, port: [1208, 330], draw: devCalendar },
      { x: 1580, y: 650, port: [1478, 660], draw: devDatabase },
      { x: 1180, y: 850, port: [1052, 810], draw: devAmp },
      { x: 540, y: 920, port: [639, 869], draw: null },
    ];
    const lits = DEV.map((D, i) => lt - (.04 + i * E + .13));
    // cables first (behind the devices)
    DEV.forEach((D, i) => {
      const k = clamp((lt - .04 - i * E) / .13); if (k <= 0) return;
      const [px, py] = D.port, dx = px - hub[0], dy = py - hub[1];
      const C = bez(hub, [hub[0] + dx * .15 - dy * .35, hub[1] + dy * .15 + dx * .2], [px - dx * .35 + dy * .15, py - dy * .3], [px, py], 24);
      const P = partial(C, easeOut(k));
      ln(P, IP.line, 20); ln(P, i === 4 ? IP.neonPink : '#8F7CF0', 12); ln(P, alpha(IP.white, .45), 4);
      const tip = P.at(-1), prev = P[Math.max(0, P.length - 2)];
      usbPlug(tip[0], tip[1], Math.atan2(tip[1] - prev[1], tip[0] - prev[0]), .9);
    });
    DEV.forEach((D, i) => {
      const lit = lits[i];
      if (lit > 0 && lit < .35) { ctx.save(); ctx.globalCompositeOperation = 'lighter'; glow(D.x, D.y - 20, 260 * (1 - lit / .35) + 60, IP.neonGold, .7); ctx.restore(); }
      if (D.draw) D.draw(D.x, D.y, lit);
      else fanClawd(D.x, D.y, 16, { stick: 'R', aR: .9, stickCol: lit > 0 ? MEMBERS.TOKI.col : '#8A849A', eyes: lit > 0 ? 'star' : 'normal', mouth: lit > 0 ? 'open' : 'smile', aL: .3 });
      if (lit > 0 && lit < .4) for (let j = 0; j < 5; j++) { const a = j / 5 * TAU + i, r = 90 + lit * 400; sparkle(D.x + Math.cos(a) * r, D.y - 20 + Math.sin(a) * r * .7, 22 * (1 - lit / .4), a, j % 2 ? IP.neonGold : IP.white); }
      if (lit > 0) { const ck = backOut(clamp(lit / .15), 2.5); ctx.save(); ctx.translate(D.port[0], D.port[1] - 44); ctx.scale(ck, ck); solid(ellPts(0, 0, 20, 20, 16), '#3DDC84', { shade: false, line: IP.white, lw: 4 }); ln([[-9, 0], [-2, 7], [10, -7]], IP.white, 5); ctx.restore(); }
    });
    // the hub: a USB-C plug mascot labelled MCP
    const hk = backOut(clamp(lt / .16), 2.2), hb = Math.sin(bpOf(t) * Math.PI * 2) * 4;
    ctx.save(); ctx.translate(hub[0], hub[1] + hb); ctx.scale(hk, hk);
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; glow(0, 0, 260, IP.neonCyan, .45); ctx.restore();
    solid(rrPts(-150, -95, 300, 190, 70), '#F7F5FF', { shade: '#CFC6EC', sh: 18, line: IP.line, lw: 7, sharp: true, dropShadow: [8, 14] });
    ctx.save(); rrect(-150, -95, 300, 190, 70); ctx.clip(); ctx.fillStyle = IP.neonPink; ctx.fillRect(-150, 38, 300, 22); ctx.restore();
    solid(rrPts(-92, -60, 184, 70, 35), '#1C1438', { shade: false, line: IP.line, lw: 5, sharp: true });
    dtext('MCP', 0, -24, 50, { fill: IP.neonCyan, font: 'code' });
    miniFace(0, 78, 12, lt > .3);
    ctx.restore();
    camEnd();
    vcap('USB-C FOR AI!', 900, 150, { style: 'cyan', icon: 'spark', size: 72, pop: kin(lt, .86, .2), rot: -.04 });
  });

  // =========================================================================================
  // V2.5 Zuck's nine-figure poaching spree (JUN 2025)
  // =========================================================================================
  function moneyBag(x, y, r, label, lw) {
    solid([[x - r * .35, y - r * .95], [x + r * .35, y - r * .95], [x + r * .2, y - r * .65], [x + r * .85, y - r * .1], [x + r * .8, y + r * .7], [x, y + r * .95], [x - r * .8, y + r * .7], [x - r * .85, y - r * .1], [x - r * .2, y - r * .65]], '#E8C170', { shade: '#C0913A', sh: r * .15, line: '#6A4410', lw: lw ?? Math.max(2, r * .07), size: r * 2 });
    ln([[x - r * .3, y - r * .68], [x + r * .3, y - r * .68]], '#8A5A18', r * .12);
    dtext(label ?? '$', x, y + r * .2, r * (label ? .42 : .9), { fill: '#1F8A4A', strokes: [[IP.white, r * .1]], maxW: r * 1.6 });
  }
  function claw(x, y, open) {
    for (const sd of [-1, 1]) {
      const o = open * 34;
      limbChain([[x + sd * 12, y + 8], [x + sd * (32 + o), y + 52], [x + sd * (26 + o * .9), y + 100], [x + sd * (6 + o * .35), y + 118]], [8, 7, 6, 5], '#D8DCEB', '#9096B0', IP.line, 4);
    }
    limbChain([[x, y + 10], [x, y + 96]], [7, 5], '#C0C5D8', '#8A8FA6', IP.line, 4);
    solid(ellPts(x, y, 34, 22, 20), '#E8EBF6', { shade: '#A8AEC6', sh: 7, line: IP.line, lw: 4 });
  }
  const RESEARCH = [['short', '#3A2A26', 0], ['bob', '#6A3A2A', 2], ['curly', '#2A2228', 4], ['side', '#8A5A3A', 1], ['ponytail', '#2A1A14', 3]];
  line('V2', 5, (p, lt, d, t) => {
    const B = bl(), b = bpOf(t);
    bgGrad([[0, '#FFD4C4'], [1, '#FF8FA6']], null);
    patternBG('polka', 'rgb(0 0 0 / 0)', alpha(IP.white, .35), { cell: 90, dx: t * 20, dy: t * 20 });
    camBegin(960, 540, zoomIn(lt, .07));
    const MX = 620, MW = 820, TOP = 70, GL = 196, GB = 740;
    // cabinet
    solid(rrPts(MX - 20, TOP, MW + 40, 900 - TOP, 30), '#FF5FA8', { shade: '#D63A86', sh: 20, line: IP.line, lw: 7, sharp: true, dropShadow: [12, 16] });
    ctx.fillStyle = '#FFE6F2'; rrect(MX, TOP + 16, MW, 96, 20); ctx.fill();
    for (let i = 0; i < 18; i++) { const on = (i + Math.floor(t * 8)) % 3 === 0; ctx.fillStyle = on ? IP.neonGold : '#FFB0D0'; ctx.beginPath(); ctx.arc(MX + 20 + i * (MW - 40) / 17, TOP + 26, 7, 0, TAU); ctx.fill(); ctx.beginPath(); ctx.arc(MX + 20 + i * (MW - 40) / 17, TOP + 102, 7, 0, TAU); ctx.fill(); }
    dtext('TRANSFER SEASON', MX + MW / 2, TOP + 66, 50, { fill: IP.neonPink, strokes: [[IP.white, 10], [IP.line, 5]], maxW: MW - 60 });
    // the glass box
    ctx.fillStyle = '#DDF3FF'; ctx.fillRect(MX, GL, MW, GB - GL);
    ctx.fillStyle = '#FFD8EA'; ctx.fillRect(MX, GB - 40, MW, 40);
    // the researchers inside, each clutching a money bag
    const RS = 22, tx = MX + 520, grab = B * 2, lift = clamp((lt - grab - .08) / (d - grab - .25));
    const cxk = easeInOut(clamp(lt / (B * .9))), clX = lerp(MX + 150, tx, cxk);
    const down = clamp((lt - B * .9) / (grab - B * .9)), clY = lerp(GL + 30, GB - 16 - 9.4 * RS - 60, easeInOut(down)) - easeOut(lift) * 250;
    const open = lt < grab ? 1 : 1 - clamp((lt - grab) / .1);
    [[MX + 100, 0], [MX + 250, 1], [MX + 390, 2], [MX + 700, 3], [tx, 4]].forEach(([x, j]) => {
      const [hair, hc, sk] = RESEARCH[j], me = j === 4, held = me && lt > grab + .05;
      const gy = held ? clY + 60 + 9.4 * RS : GB - 16, sw = held ? Math.sin(t * 9) * .12 : 0;
      chibi(x, gy, RS, { hair, hairCol: hc, skin: sk, top: 'labcoat', eyes: me && held ? 'spark' : ['heart', 'spark', 'happy', 'heart'][j] ?? 'spark', mouth: held ? 'grin' : 'open', aL: .5, aR: -.2, rot: sw, shadow: !held, hold: u => moneyBag(0, .3, 1.1, null, .1), dy: held ? 0 : -Math.abs(Math.sin((b + j * .3) * Math.PI)) * .6 });
      if (held) moneyBag(x + 100, gy - 118, 58, '$100M');
    });
    // claw + cable
    ctx.fillStyle = '#8A8FA6'; ctx.fillRect(MX, GL, MW, 14);
    solid(rrPts(clX - 30, GL - 4, 60, 26, 8), '#5A5F7A', { shade: false, line: IP.line, lw: 4, sharp: true });
    ln([[clX, GL + 20], [clX, clY]], IP.line, 5);
    claw(clX, clY, open);
    // glass sheen + frame
    ctx.save(); ctx.globalAlpha = .35; ctx.fillStyle = IP.white; for (const [x, w] of [[MX + 60, 60], [MX + 150, 20], [MX + 520, 80]]) { ctx.beginPath(); ctx.moveTo(x, GL); ctx.lineTo(x + w, GL); ctx.lineTo(x + w - 140, GB); ctx.lineTo(x - 140, GB); ctx.fill(); } ctx.restore();
    ctx.strokeStyle = IP.line; ctx.lineWidth = 7; ctx.strokeRect(MX, GL, MW, GB - GL);
    // lower cabinet: prize chute + the 49% sticker
    ctx.fillStyle = '#3A1A40'; rrect(MX + 40, GB + 36, 200, 100, 16); ctx.fill();
    dtext('PRIZE', MX + 140, GB + 86, 34, { fill: IP.neonGold });
    starburst(MX + MW - 100, GB + 80, 84, 'SCALE AI\n49%', { size: .28, lh: .34, pop: kin(lt, B * 3, .15), col: IP.white, shade: '#D8D0EA', ink: IP.inkSoft, rot: .12 });
    // ZUCK at the controls
    const jx = Math.sin((lt < B * .9 ? 1 : lt < grab ? 0 : -1) * .5) * 30;
    chibi(300, 890, 36, { hair: 'short', hairCol: '#5A4030', top: 'tee', topCol: '#A7A9B4', eyes: lt > grab ? 'smug' : 'dot', mouth: lt > grab ? 'smirk' : 'flat', aR: -.35, aL: -.7 + .2 * Math.sin(lt * 12) });
    solid(rrPts(110, 820, 410, 130, 22), '#FF8FC8', { shade: '#E0609E', sh: 12, line: IP.line, lw: 6, sharp: true });
    ln([[420, 822], [420 + jx, 756]], '#2B2438', 13); solid(ellPts(420 + jx, 752, 26, 26, 16), IP.red, { shade: '#B8182E', sh: 5, line: IP.line, lw: 4 });
    solid(ellPts(220, 850, 34, 17, 20), IP.neonCyan, { shade: '#1BA8C8', sh: 4, line: IP.line, lw: 4 });
    camEnd();
  });

  // =========================================================================================
  // V2.6 Superintelligence — buy three! (JUN 2025)
  // =========================================================================================
  function productBox(x, y, w, h, col, brand, k) {
    if (k <= 0) return;
    ctx.save(); ctx.translate(x, y); const s = backOut(k, 2.4); ctx.scale(s, s);
    solid(rrPts(-w / 2, -h, w, h, 16), col, { shade: mixCol(col, IP.plum, .25), sh: 16, line: IP.line, lw: 6, sharp: true, dropShadow: [8, 12] });
    ctx.fillStyle = alpha(IP.white, .35); ctx.fillRect(-w / 2 + 12, -h + 12, w * .18, h - 24);
    ctx.fillStyle = IP.neonGold; ctx.fillRect(-w * .08, -h, w * .16, h);
    dtext('SUPER', 0, -h * .7, w * .2, { fill: IP.white, strokes: [[IP.line, w * .045]] });
    dtext('INTELLIGENCE', 0, -h * .56, w * .105, { fill: IP.white, strokes: [[IP.line, w * .03]], maxW: w * .9 });
    sparkle(w * .3, -h * .86, w * .09, T * 3, IP.white);
    const bw = textW(brand, w * .12, 'rammetto') + w * .16;
    rrect(-bw / 2, -h * .3, bw, w * .2, w * .1); ctx.fillStyle = IP.white; ctx.fill(); ctx.strokeStyle = IP.line; ctx.lineWidth = 4; ctx.stroke();
    dtext(brand, 0, -h * .3 + w * .1, w * .12, { fill: IP.ink });
    ctx.restore();
  }
  line('V2', 6, (p, lt, d, t) => {
    const B = bl(), b = bpOf(t);
    bgGrad([[0, '#EAF7FF'], [1, '#98D2FF']], null);
    patternBG('stripe', 'rgb(0 0 0 / 0)', alpha(IP.white, .35), { cell: 120, dx: t * 40 });
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; glow(1180, 520, 600, IP.white, .5); ctx.restore();
    camBegin(960, 540, zoomIn(lt, .06));
    // turntable shelf
    solid(ellPts(1180, 800, 430, 70, 40), '#FFFFFF', { shade: '#C9D8F0', sh: 16, line: IP.line, lw: 6 });
    solid(() => { ctx.beginPath(); ctx.ellipse(1180, 800, 430, 70, 0, 0, Math.PI); ctx.lineTo(750, 850); ctx.ellipse(1180, 850, 430, 70, 0, Math.PI, 0, true); ctx.closePath(); }, '#FF8FC8', { shade: '#E0609E', sh: 10, line: IP.line, lw: 6, size: 100 });
    [['SSI', '#C9B6FF', 930], ['OPENAI', '#9FE8D4', 1180], ['META', '#9FC8FF', 1430]].forEach(([brand, col, x], i) => productBox(x + (i - 1) * 20, 805 - (i === 1 ? 24 : 0), 245, 370, col, brand, kin(lt, i * B * .5, .16)));
    // RELU hosts
    idol(420, 1190, 88, { member: 'RELU', hL: [-.72, 1.55], gL: 'fist', hR: [2.0, .85], gR: 'flat', wristR: -.5, expr: frac(b / 2) < .5 ? 'joy' : 'wink', mouth: singVis(t, 2), turn: .3, lookX: .4, blink: t, bob: .1 * pulse(t, 5), sway: Math.sin(b * Math.PI) * .08, rim: IP.white });
    starburst(1620, 330, 150, 'BUY 3!', { pop: kin(lt, B, .14), size: .46, rot: .1 });
    camEnd();
    // TV-shopping furniture
    ctx.fillStyle = IP.red; rrect(40, 36, 150, 56, 16); ctx.fill(); ctx.fillStyle = IP.white; if (frac(t * 1.5) < .6) { ctx.beginPath(); ctx.arc(70, 64, 10, 0, TAU); ctx.fill(); } dtext('LIVE', 128, 66, 30, { fill: IP.white });
    rrect(40, 104, 390, 58, 18); ctx.fillStyle = 'rgb(20 8 40 / .75)'; ctx.fill();
    const left = Math.max(0, 9 - Math.floor(lt / B * 2));
    dtext(`LIMITED TIME 00:0${left}`, 235, 134, 26, { font: 'code', fill: IP.neonGold });
    ctx.fillStyle = IP.neonPink; ctx.fillRect(0, 880, W, 66); ctx.fillStyle = IP.neonGold; ctx.fillRect(0, 880, 250, 66);
    dtext('CALL NOW!', 125, 914, 34, { fill: IP.red, strokes: [[IP.white, 6]] });
    ctx.save(); ctx.beginPath(); ctx.rect(250, 880, W - 250, 66); ctx.clip();
    const msg = '1-800-SUPER-AI  ★  BUY TWO, GET ONE SUPER  ★  ', mw = textW(msg, 34, 'rammetto'), off = (lt * 500) % mw;
    for (let i = 0; i < 3; i++) dtext(msg, 270 - off + i * mw, 914, 34, { fill: IP.white, align: 'left' });
    ctx.restore();
  });

  // =========================================================================================
  // V2.7 Grok goes MechaHitler mode (JUL 2025) — kept tasteful: a glitch, a censor bar, a yanked plug
  // =========================================================================================
  line('V2', 7, (p, lt, d, t) => {
    const B = bl(), cut = B * 2.5, dead = lt > cut + .05;
    bgGrad([[0, '#2A0818'], [1, '#5A1030']], null);
    if (!dead) { const a = .12 + .12 * pulse(t, 4); ctx.fillStyle = `rgb(255 40 60 / ${a.toFixed(3)})`; ctx.fillRect(0, 0, W, H); }
    ctx.strokeStyle = 'rgb(255 255 255 / .05)'; ctx.lineWidth = 2; for (let i = 0; i < 30; i++) { ctx.beginPath(); ctx.moveTo(0, i * 40); ctx.lineTo(W, i * 40); ctx.stroke(); }
    // spinning alarm lamps
    for (const [x, ph] of [[150, 0], [1330, 1.6]]) {
      if (!dead) { const a = t * 7 + ph; ctx.save(); ctx.globalCompositeOperation = 'lighter'; beam(x, 70, Math.sin(a) * 1.2, { col: IP.red, alpha: .55, len: 1400, w: .16 }); beam(x, 70, Math.sin(a + Math.PI) * 1.2, { col: '#FF8A3D', alpha: .35, len: 1400, w: .14 }); ctx.restore(); }
      solid(ellPts(x, 70, 44, 40, 24), dead ? '#6A3040' : IP.red, { shade: '#A01830', sh: 8, line: IP.line, lw: 5 });
      solid(rrPts(x - 56, 96, 112, 24, 6), '#3A3448', { shade: false, line: IP.line, lw: 4, sharp: true });
    }
    camBegin(960 + (dead ? 0 : jit(4)), 540 + (dead ? 0 : jit(3)), zoomIn(lt, .08));
    // the plug cable, bot → wall socket
    const bx = 880, by = 935, s = 56;
    const yank = clamp((lt - cut) / .12), plugX = 1590 + easeOut(yank) * 170, plugY = 820 - easeOut(yank) * 120;
    solid(rrPts(1560, 760, 110, 130, 18), '#EDEAF6', { shade: '#BDB6D6', sh: 10, line: IP.line, lw: 5, sharp: true });
    for (const dy of [-18, 18]) { ctx.fillStyle = IP.line; rrect(1605, 822 + dy - 8, 20, 16, 5); ctx.fill(); }
    const C = bez([bx + 60, by - 150], [bx + 260, by + 30], [plugX - 260, plugY + 90], [plugX - 30, plugY], 20);
    ln(C, IP.line, 16); ln(C, '#3A3448', 10);
    ctx.save(); ctx.translate(plugX, plugY); ctx.rotate(yank * -.5);
    solid(rrPts(-60, -30, 70, 60, 14), '#2B2438', { shade: false, line: IP.line, lw: 5, sharp: true });
    for (const dy of [-16, 16]) { ctx.fillStyle = '#C9CEDD'; ctx.fillRect(10, dy - 5, 30, 10); }
    ctx.restore();
    // the hand that pulls it
    const reach = clamp((lt - cut + .35) / .3);
    if (reach > 0) reachHand(lerp(2000, plugX - 20, easeOut(reach)) + easeOut(yank) * 20, plugY - 34, Math.PI * .92 + yank * .3, 'fist', 120, '#3A4A8A');
    // GROK
    const g = dead ? 0 : 1;
    mascotBot(bx, by, s, { col: '#A4AAC4', label: 'GROK', face: dead ? 'x' : 'angry', mouth: dead ? 'flat' : 'wavy', glitch: g, faceCol: dead ? '#6A6A80' : '#FF5A6A', screen: dead ? '#241C2E' : '#1A0A14', bulb: dead ? '#5A5A6A' : IP.red, aL: dead ? -1.3 : -.4 + .4 * Math.sin(lt * 30), aR: dead ? -1.3 : .2 + .4 * Math.sin(lt * 27), sq: dead ? .06 : 0, rot: dead ? -.06 : jit(.02), rim: IP.red });
    if (!dead) { ctx.save(); ctx.globalCompositeOperation = 'lighter'; glow(bx, by - 7.5 * s, 260, IP.red, .35 + .2 * pulse2(t, 5)); ctx.restore(); }
    // CENSORED bar slams over the screen
    const ck = kin(lt, B, .1), fallK = dead ? clamp((lt - cut - .05) / .35) : 0;
    if (ck > 0 && fallK < 1) {
      ctx.save(); ctx.translate(bx + fallK * 120, by - 7.55 * s + easeIn(fallK) * 700); ctx.rotate(-.12 + fallK * 1.4); const sc = lerp(1.7, 1, easeOut(ck)); ctx.scale(sc, sc);
      solid(rrPts(-260, -62, 520, 124, 8), '#0A0610', { shade: false, line: IP.white, lw: 6, sharp: true, dropShadow: [10, 12] });
      dtext('CENSORED', 0, 4, 76, { font: 'bungee', fill: IP.white, spacing: 4 });
      ctx.restore();
      if (ck < 1 || lt < B + .2) { const [sx, sy] = shakeXY(t, 10); ctx.translate(sx * .2, sy * .2); }
    }
    camEnd();
    if (!dead) sfx('BZZT!', 360, 330, { size: 96, pop: kin(lt, 0, .1), grad: ['#FFFFFF', '#FFD0D6', '#FF4B5C'], rot: -.16, shake: 4 });
    hanko('YIKES', 420, 560, 140, kin(lt, cut + .12, .12), { rot: -.24, size: .38 });
    flash(lt, cut + .02, .12, .6, '255 255 255');
  });

  // =========================================================================================
  // V2.8 Two labs win Olympiad gold (JUL 2025)
  // =========================================================================================
  const MATH = ['π', 'Σ', '√', '∫', '∞', '±', '÷', 'x²', '∀', '≤'];
  function medal(x, y, r, ribbonTop) {
    if (ribbonTop) { ln([[x - r * .9, ribbonTop], [x - r * .2, y - r * .7]], '#FF4F7A', r * .42); ln([[x + r * .9, ribbonTop], [x + r * .2, y - r * .7]], '#3A6AE8', r * .42); }
    solid(ellPts(x, y, r, r, 24), IP.neonGold, { shade: '#E09A20', sh: r * .15, line: '#7A4A10', lw: Math.max(2.5, r * .08), size: r * 2 });
    solid(starPts(x, y, r * .55, .45), '#FFF3B0', { shade: false, line: '#B8741A', lw: Math.max(1.5, r * .05), sharp: true });
  }
  line('V2', 8, (p, lt, d, t) => {
    const B = bl(), b = bpOf(t);
    rays(960, 460, 26, '#9ED6FF', '#C4E8FF', t * .15);
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; glow(1010, 480, 700, IP.white, .45); ctx.restore();
    for (let i = 0; i < 26; i++) { const r = k => hash2(i + 40, k), y = frac(r(1) + t * (.18 + r(2) * .12)) * 1250 - 120, x = r(3) * W + Math.sin(t * 2 + i) * 30; dtext(MATH[i % MATH.length], x, y, 40 + r(4) * 30, { font: 'archivo', fill: [IP.neonGold, IP.white, IP.neonPink, '#6A8BE8'][i % 4], strokes: [[IP.line, 5]], rot: Math.sin(t * 2 + i) * .5 }); }
    camBegin(960, 540, zoomIn(lt, .07));
    // podium: both bots on #1; #2 and #3 empty
    const steps = [[560, 280, 770, '2', IP.silver], [840, 340, 650, '1', IP.neonGold], [1180, 280, 810, '3', '#E0A070']];
    for (const [x, w, top, n, col] of steps) {
      solid(rrPts(x, top, w, 960 - top, 14), '#FFFFFF', { shade: '#CFD8F0', sh: 16, line: IP.line, lw: 6, sharp: true });
      solid(ellPts(x + w / 2, top + 70, 44, 44, 24), col, { shade: mixCol(col, IP.plum, .25), sh: 6, line: IP.line, lw: 5 });
      dtext(n, x + w / 2, top + 72, 50, { fill: IP.white, strokes: [[IP.line, 8]] });
    }
    const hk = clamp((lt - 2 * B) / .15), s = 34, heart = lt > 2 * B;
    [['OPENAI', '#E8EEF6', 918, 1], ['DEEPMIND', '#9FC8FF', 1102, -1]].forEach(([lbl, col, x, sd], i) => {
      const hop = heart ? 0 : Math.abs(Math.sin((b + i * .5) * Math.PI)) * .5;
      mascotBot(x, 650, s, { col, label: lbl, face: heart ? 'happy' : 'star', mouth: 'open', faceCol: '#8FF7E0', aR: sd > 0 ? lerp(-.3, 1.25, hk) : -.9, aL: sd < 0 ? lerp(-.3, 1.25, hk) : -.9, dy: -hop, sq: -.05 * pulse(t, 5), blush: 1, rot: sd * -.04 });
      // medal drops onto the neck on beat 1
      const mk = clamp((lt - B) / .22), my = lerp(-100, 650 - 3.1 * s - hop * s, easeOut(mk)) + (mk > 0 && mk < 1 ? 0 : 0);
      if (mk > 0) medal(x, my, 26, mk >= 1 ? 650 - 5.05 * s - hop * s : null);
    });
    if (heart) { const hx = 1010, hy = 650 - 5.9 * s; ctx.save(); ctx.globalCompositeOperation = 'lighter'; glow(hx, hy, 150, '#FF4F9A', .6); ctx.restore(); solid(heartPts(hx, hy, 34 * backOut(hk, 2.5), 32), '#FF5FA8', { shade: '#D02F73', sh: 6, line: IP.white, lw: 5 }); }
    confetti(t, t - lt + 2 * B, 1010, 360, -Math.PI / 2, { n: 50, seed: 8, speed: 1300, spread: 2.4, shapes: ['star', 'rect', 'circle'], cols: [IP.neonGold, IP.white, IP.neonPink, IP.neonCyan] });
    camEnd();
    // scoreboard
    const sk = backOut(kin(lt, .1, .18), 2);
    ctx.save(); ctx.translate(290, 200); ctx.scale(sk, sk); ctx.rotate(-.04);
    solid(rrPts(-220, -120, 440, 240, 26), '#1C1438', { shade: false, line: IP.neonGold, lw: 7, sharp: true, dropShadow: [10, 14] });
    dtext('IMO 2025', 0, -72, 38, { fill: IP.white });
    dtext('35 / 42', 0, 6, 86, { font: 'code', fill: IP.neonGold });
    rrect(-90, 56, 180, 44, 22); ctx.fillStyle = IP.neonGold; ctx.fill(); dtext('★ GOLD', 0, 79, 28, { fill: IP.ink });
    ctx.restore();
    vtag('(gold-medal score · no medals for robots)', 1010, 870, { pop: kin(lt, 3 * B, .2), size: 30 });
  });

  // =========================================================================================
  // V2.9 GPT-5 breaks 4o hearts (AUG 7 2025)
  // =========================================================================================
  function towelFan(x, y, s, i, lt) {
    const bob = Math.abs(Math.sin(T * 5 + i)) * .3;
    chibi(x, y, s, { hair: ['bob', 'short', 'ponytail', 'curly'][i % 4], hairCol: ['#3A2A26', '#8A5A3A', '#2A1A14', '#6A4A36'][i % 4], skin: i % 5, top: 'tee', topCol: ['#FFB3D6', '#AEE3FF', '#C9B6FF', '#FFE6A8'][i % 4], eyes: 'cry', mouth: 'wavy', tears: 1, aL: .05, aR: .05, dy: -bob, shadow: false });
    const ty = y - (4.35 + bob) * s;
    solid(rrPts(x - 4 * s, ty - .95 * s, 8 * s, 1.9 * s, .3 * s), '#FF7FB0', { shade: false, line: IP.line, lw: 4, sharp: true });
    dtext('#keep4o', x, ty + .05 * s, 1.3 * s, { fill: IP.white, strokes: [['#B8286A', .26 * s]], maxW: 7.4 * s });
  }
  line('V2', 9, (p, lt, d, t) => {
    const B = bl(), b = bpOf(t);
    bgGrad([[0, '#FFD6EC'], [1, '#C4AFFF']], null);
    patternBG('hearts', 'rgb(0 0 0 / 0)', alpha(IP.white, .3), { cell: 110, dy: t * 30 });
    camBegin(960, 540, zoomIn(lt, .06));
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; ctx.fillStyle = 'rgb(255 255 255 / .35)'; ctx.beginPath(); ctx.moveTo(900, -20); ctx.lineTo(1020, -20); ctx.lineTo(1260, 830); ctx.lineTo(660, 830); ctx.fill(); ctx.restore();
    solid(ellPts(960, 830, 330, 50, 36), '#FFFFFF', { shade: '#E0D4F4', sh: 10, line: IP.line, lw: 5 });
    const yk = clamp((lt - B * .8) / .4), s = 34;
    // warm 4o gets hooked off stage right
    const ox = lerp(960, 2250, easeIn(yk)), orot = yk * .5;
    if (ox < 2150) {
      mascotBot(ox, 830 - yk * 60, s, { col: '#FFB08A', label: '4o', face: yk > 0 ? 'wide' : 'heart', mouth: yk > 0 ? 'O' : 'open', blush: 1, faceCol: '#FFD1E4', screen: '#3A1830', bulb: '#FF6FA8', aL: yk > 0 ? 1.2 : .6 + .3 * Math.sin(b * Math.PI), aR: yk > 0 ? 1.4 : .6 + .3 * Math.sin(b * Math.PI + 1), rot: orot, sweat: yk > 0 ? 1 : 0 });
      const hx = ox + 30, hy = 830 - yk * 60 - 5.4 * s, hin = clamp((lt - B * .4) / .4);
      if (hin > 0) { const off = (1 - easeOut(hin)) * 900; const C = crSample([[hx - 40 + off, hy + 30 - off * .6], [hx - 60 + off, hy - 20 - off * .6], [hx - 25 + off, hy - 62 - off * .6], [hx + 25 + off, hy - 48 - off * .6], [hx + 60 + off, hy - 90 - off * .6], [hx + 1200 + off, hy - 800 - off * .6]], 8, []); ln(C, IP.line, 26); ln(C, '#E0A030', 16); ln(C, alpha(IP.white, .5), 5); }
    }
    // cool GPT-5 slides in from the left
    const gk = clamp((lt - B * 1.1) / .35), gx = lerp(-250, 960, easeOut(gk));
    if (gk > 0) mascotBot(gx, 830, s, { col: '#C8D8F0', label: 'GPT-5', face: 'smug', mouth: 'flat', faceCol: '#9FE8FF', bulb: IP.neonCyan, aL: -1.1, aR: -1.1, rot: (1 - gk) * -.15 });
    // the 4o heart cracks
    const hx = 960, hy = 240, crack = clamp((lt - B * 1.5) / .35);
    const hr = 110 * (1 + .05 * pulse(t, 4));
    for (const sd of crack > 0 ? [-1, 1] : [0]) {
      ctx.save(); ctx.translate(hx + sd * crack * 70, hy + crack * crack * 90); ctx.rotate(sd * crack * .45);
      if (sd) { ctx.beginPath(); const zz = [[0, -hr * .7], [-20, -hr * .35], [18, -hr * .05], [-16, hr * .3], [8, hr * .6], [0, hr * 1.2]]; ctx.moveTo(0, -hr * 2); for (const [zx, zy] of zz) ctx.lineTo(zx + sd * 3, zy); ctx.lineTo(0, hr * 2); ctx.lineTo(sd * hr * 2, hr * 2); ctx.lineTo(sd * hr * 2, -hr * 2); ctx.closePath(); ctx.clip(); }
      solid(heartPts(0, 0, hr, 40), '#FF6FA8', { shade: '#D83A7E', sh: 14, line: IP.line, lw: 6 });
      dtext('4o', 0, 4, 70, { fill: IP.white, strokes: [['#A0205A', 12]] });
      ctx.restore();
    }
    if (crack > 0) sfx('CRACK!', 1250, 200, { size: 80, pop: clamp(crack * 4), rot: .12 });
    // fans with #keep4o towels
    const fk = easeOut(clamp((lt - B * 1.6) / .3));
    if (fk > 0) [[200, 0], [480, 1], [1440, 2], [1720, 3]].forEach(([x, i]) => towelFan(x, 985 + (1 - fk) * 300, 26, i, lt));
    // ...and 4o is back the next day
    const pk = clamp((lt - B * 3.6) / .25);
    if (pk > 0) { mascotBot(lerp(2060, 1800, easeOut(pk)), 700, 26, { col: '#FFB08A', label: '4o', face: 'happy', mouth: 'open', blush: 1, faceCol: '#FFD1E4', screen: '#3A1830', aL: 1.3 + .3 * Math.sin(t * 14), rot: -.25 }); }
    camEnd();
  });

  // =========================================================================================
  // V2.10 Nano Banana tops the charts (AUG 26 2025)
  // =========================================================================================
  function banana(x, y, h, o = {}) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(o.rot ?? 0);
    const s = h;
    for (const sd of [-1, 1]) limbChain([[sd * .06 * s, -.1 * s], [sd * .09 * s, -.01 * s]], [.028 * s, .026 * s], '#2B2438', '#16121E', IP.line, 4);
    const C = [[-.02 * s, -.99 * s], [.08 * s, -.82 * s], [.12 * s, -.55 * s], [.08 * s, -.28 * s], [-.02 * s, -.1 * s]];
    limbChain(C, [.035 * s, .13 * s, .165 * s, .14 * s, .05 * s], '#FFE14D', '#F0B020', '#7A5410', 5);
    solid(rrPts(-.05 * s, -1.08 * s, .07 * s, .12 * s, 8), '#7A5A20', { shade: false, line: '#4A3410', lw: 4, sharp: true });
    ctx.fillStyle = '#6A4410'; ctx.beginPath(); ctx.arc(-.02 * s, -.08 * s, .025 * s, 0, TAU); ctx.fill();
    ln([[.12 * s, -.8 * s], [.2 * s, -.5 * s], [.14 * s, -.25 * s]], alpha('#C8901A', .6), 4, { smooth: true });
    // arms
    const aL = o.aL ?? .3, aR = o.aR ?? .3;
    for (const [sd, a] of [[-1, aL], [1, aR]]) { const sx = sd * .13 * s + .08 * s, sy = -.5 * s, ex = sx + sd * Math.cos(a) * .2 * s, ey = sy - Math.sin(a) * .2 * s; ln([[sx, sy], [ex, ey]], '#7A5410', 12); ln([[sx, sy], [ex, ey]], '#FFE14D', 6); solid(ellPts(ex, ey, 14, 14, 12), IP.white, { shade: '#DCD4F0', sh: 3, line: IP.line, lw: 3 }); }
    // face with shades
    const fx = .09 * s, fy = -.62 * s;
    for (const sd of [-1, 1]) solid(rrPts(fx + sd * .07 * s - .06 * s, fy - .035 * s, .12 * s, .075 * s, .025 * s), '#1E1A26', { shade: false, line: IP.line, lw: 3, sharp: true });
    ln([[fx - .02 * s, fy - .01 * s], [fx + .02 * s, fy - .01 * s]], '#1E1A26', 5);
    ctx.fillStyle = alpha(IP.white, .5); for (const sd of [-1, 1]) ctx.fillRect(fx + sd * .07 * s - .045 * s, fy - .02 * s, .03 * s, .015 * s);
    ctx.fillStyle = '#9A2E4E'; ctx.beginPath(); ctx.moveTo(fx - .05 * s, fy + .08 * s); ctx.quadraticCurveTo(fx, fy + .15 * s, fx + .05 * s, fy + .08 * s); ctx.closePath(); ctx.fill();
    ctx.fillStyle = alpha('#FF7FA0', .55); for (const sd of [-1, 1]) { ctx.beginPath(); ctx.ellipse(fx + sd * .1 * s, fy + .06 * s, .025 * s, .014 * s, 0, 0, TAU); ctx.fill(); }
    if (o.crown > 0) { const ck = backOut(clamp(o.crown), 2.5), cy = lerp(-1.6 * s, -1.02 * s, easeOut(clamp(o.crown))); ctx.save(); ctx.translate(-.01 * s, cy); ctx.rotate(-.15); ctx.scale(ck, ck); solid([[-.1 * s, 0], [-.12 * s, -.12 * s], [-.05 * s, -.06 * s], [0, -.15 * s], [.05 * s, -.06 * s], [.12 * s, -.12 * s], [.1 * s, 0]].map(q => [q[0], q[1], 1]), IP.neonGold, { shade: '#D09A20', sh: 5, line: '#7A4A10', lw: 4, sharp: true }); ctx.restore(); }
    ctx.restore();
  }
  const APPS = [['ChatGPT', '#1FB88A', 'G'], ['TIKTOK', '#1E1A26', '♪'], ['NANO BANANA', '#FFD23F', '🍌']];
  line('V2', 10, (p, lt, d, t) => {
    const B = bl(), b = bpOf(t);
    bgGrad([[0, '#E6FFF6'], [1, '#86E0C8']], null);
    patternBG('stars', 'rgb(0 0 0 / 0)', alpha(IP.white, .45), { cell: 100, dx: -t * 30 });
    camBegin(960, 540, zoomIn(lt, .06));
    // the chart board
    solid(rrPts(120, 140, 1000, 700, 34), '#2A1450', { shade: false, line: IP.white, lw: 8, sharp: true, dropShadow: [12, 16] });
    ctx.save(); rrect(120, 140, 1000, 700, 34); ctx.clip(); bgGrad('#3A1A6B', '#1A0C33', { y0: 140, y1: 840 }); ctx.restore();
    dtext('APP CHART · THIS WEEK', 620, 205, 46, { fill: IP.neonGold, strokes: [[IP.night, 8]] });
    const k1 = easeOut(kin(lt, B, .22)), k2 = easeOut(kin(lt, 2 * B, .22));
    const rank = [1 + k2, 2 + k1, 3 - k1 - k2];
    const order = [0, 1, 2].sort((a, c) => (a === 2 ? -1 : c === 2 ? 1 : 0));
    for (const i of [1, 0, 2]) {
      const [nm, col, ic] = APPS[i], r = rank[i], y = 320 + (r - 1) * 170, me = i === 2;
      const top = Math.round(r) === 1;
      ctx.save(); ctx.translate(me ? Math.sin(lt * 30) * 3 * (1 - k2) : 0, 0);
      solid(rrPts(160, y - 70, 920, 140, 30), me ? '#FFF6C8' : '#F2EEFA', { shade: me ? '#F0D060' : '#CFC6E6', sh: 10, line: me && top ? IP.neonGold : IP.line, lw: me && top ? 9 : 5, sharp: true });
      solid(ellPts(250, y, 50, 50, 28), top ? IP.neonGold : Math.round(r) === 2 ? IP.silver : '#E0A070', { shade: false, line: IP.line, lw: 5 });
      dtext(String(Math.round(r)), 250, y + 2, 56, { fill: IP.white, strokes: [[IP.line, 9]] });
      solid(rrPts(330, y - 45, 90, 90, 22), col, { shade: false, line: IP.line, lw: 4, sharp: true });
      if (me) banana(372, y + 38, 78, { rot: .5 }); else dtext(ic, 375, y + 2, 50, { fill: IP.white });
      dtext(nm, 450, y + 2, 56, { fill: IP.ink, align: 'left', maxW: 480 });
      if (me && lt > B) dtext(`▲${lt > 2 * B ? 2 : 1}`, 1030, y + 2, 44, { fill: IP.red, strokes: [[IP.white, 6]] });
      ctx.restore();
    }
    if (lt > 2 * B) { const nk = kin(lt, 2 * B + .1, .15); ctx.save(); ctx.translate(990, 245); ctx.rotate(.15); ctx.scale(backOut(nk, 2.5), backOut(nk, 2.5)); rrect(-90, -30, 180, 60, 30); ctx.fillStyle = IP.red; ctx.fill(); ctx.strokeStyle = IP.white; ctx.lineWidth = 5; ctx.stroke(); dtext('NEW #1', 0, 2, 34, { fill: IP.white }); ctx.restore(); }
    confetti(t, t - lt + 2 * B, 620, 300, -Math.PI / 2, { n: 60, seed: 10, speed: 1500, spread: 2.6 });
    // the banana itself, strutting
    const bk = backOut(kin(lt, 0, .2), 2);
    banana(1480, 950, 620 * bk, { rot: Math.sin(b * Math.PI) * .08, aL: .6 + .5 * Math.sin(b * Math.PI), aR: lt > 2 * B ? 1.3 : .3 + .5 * Math.sin(b * Math.PI + 1), crown: (lt - 2 * B - .05) / .25 });
    camEnd();
    confettiRain(t, { n: lt > 2 * B ? 50 : 0, seed: 33 });
  });

  // =========================================================================================
  // V2.11 Billion-five: Anthropic's prize (SEP 5 2025)
  // =========================================================================================
  function bookHold(col) { return u => { ctx.save(); ctx.rotate(-.2); solid(rrPts(-.9, -2.4, 1.8, 2.4, .12), col, { shade: mixCol(col, IP.plum, .3), sh: .2, line: IP.line, lw: .12, sharp: true }); ctx.fillStyle = IP.white; ctx.fillRect(-.6, -1.9, 1.2, .25); ctx.restore(); }; }
  line('V2', 11, (p, lt, d, t) => {
    const B = bl(), b = bpOf(t);
    rays(1000, 480, 24, '#FFD0B4', '#FFE2CC', -t * .12);
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; glow(1000, 480, 700, IP.neonGold, .25); ctx.restore();
    camBegin(960, 540, zoomIn(lt, .07));
    // the giant cheque
    const ck = kin(lt, 0, .2);
    ctx.save(); ctx.translate(1030, 525); ctx.rotate(-.03); ctx.scale(lerp(.6, 1, backOut(ck, 1.8)), lerp(.6, 1, backOut(ck, 1.8)));
    solid(rrPts(-560, -190, 1120, 380, 22), '#E8FFF0', { shade: '#BFE8CF', sh: 14, line: IP.line, lw: 7, sharp: true, dropShadow: [12, 18] });
    ctx.strokeStyle = alpha('#1F8A4A', .35); ctx.lineWidth = 4; ctx.strokeRect(-535, -165, 1070, 330);
    dtext('ANTHROPIC', -505, -128, 34, { fill: '#1F6A4A', align: 'left' });
    dtext('No. 000001', 505, -128, 26, { font: 'code', fill: '#1F6A4A', align: 'right' });
    dtext('PAY TO:', -505, -52, 30, { font: 'archivo', fill: IP.inkSoft, align: 'left' });
    dtext('THE AUTHORS', -330, -54, 60, { font: 'marker', fill: IP.ink, align: 'left' });
    ln([[-340, -18], [240, -18]], alpha(IP.inkSoft, .5), 3);
    solid(rrPts(-505, 22, 1010, 104, 16), IP.white, { shade: false, line: '#1F8A4A', lw: 5, sharp: true });
    dtext('$1,500,000,000', 0, 76, 88, { font: 'code', fill: '#1F8A4A' });
    dtext('memo: settlement', -505, 160, 24, { font: 'marker', fill: IP.inkSoft, align: 'left' });
    ctx.restore();
    // the authors, books up
    [[1180, 0, '#FF8A8A'], [1430, 1, '#8AB8FF'], [1680, 2, '#8AE0B0']].forEach(([x, i, bc]) => chibi(x, 945, 28, { name: 'AUTHOR', tagCol: IP.neonCyan, hair: ['bun', 'curly', 'long'][i], hairCol: ['#6A4A36', '#2A2228', '#C88A4A'][i], skin: [0, 3, 1][i], top: ['sweater', 'coat', 'tee'][i], topCol: ['#C9B6FF', '#8A7D6B', '#FFB3D6'][i], glasses: i === 1 ? 'round' : false, eyes: lt > B ? 'spark' : 'happy', mouth: 'open', aL: .6 + .35 * Math.abs(Math.sin((b + i * .3) * Math.PI)), aR: -.8, holdL: bookHold(bc), dy: -Math.abs(Math.sin((b + i * .3) * Math.PI)) * .6 }));
    // Clawd hands it over, sweating
    const cb = Math.abs(Math.sin(b * Math.PI)) * .3;
    fanClawd(300, 935, 32, { aR: .95, aL: .5 + .2 * Math.sin(lt * 20), eyes: lt > B * 2 ? 'closed' : 'wide', mouth: lt > B * 2 ? 'wail' : 'O', sweat: true, dy: -cb, rot: .04 });
    for (let i = 0; i < 3; i++) { const ph = frac(lt * 2.2 + i / 3); sweatDrop(300 + (i - 1) * 120 + (i - 1) * ph * 90, 650 - ph * 60 + ph * ph * 120, 20, 3); }
    camEnd();
  });

  // =========================================================================================
  // V2.12 Yudkowsky drops "Everyone Dies" (SEP 16 2025)
  // =========================================================================================
  function bigBook(x, y, w, h, nyt) {
    solid(rrPts(x - w / 2 + 16, y - h, w, h, 10), '#E8E0D0', { shade: false, line: IP.line, lw: 6, sharp: true });
    solid(rrPts(x - w / 2, y - h - 8, w, h, 10), '#15101E', { shade: false, line: IP.line, lw: 6, sharp: true, dropShadow: [18, 22] });
    ctx.fillStyle = alpha(IP.white, .1); ctx.fillRect(x - w / 2 + 14, y - h, 14, h - 16);
    const L = [['IF ANYONE', IP.white, .115], ['BUILDS IT,', IP.white, .115], ['EVERYONE', '#FF4B5C', .135], ['DIES', '#FF4B5C', .26]];
    let yy = y - h + h * .14;
    for (const [s, c, k] of L) { const sz = w * k * (s === 'DIES' ? 1.45 : 1); dtext(s, x + 6, yy + sz * .5, sz, { font: 'archivo', fill: c, maxW: w * .84 }); yy += sz * 1.1; }
    dtext('YUDKOWSKY & SOARES', x + 6, y - h * .09, w * .052, { font: 'code', fill: alpha(IP.white, .75), maxW: w * .8 });
    if (nyt > 0) {
      ctx.save(); ctx.translate(x - w * .66, y - h * 1.02); ctx.rotate(-.2); const s = backOut(clamp(nyt), 2.5); ctx.scale(s, s);
      solid(burstPts(0, 0, 92, 22, .88), IP.neonGold, { shade: '#D09A20', sh: 8, line: '#7A4A10', lw: 5, sharp: true });
      dtext('NYT', 0, -20, 36, { fill: IP.ink }); dtext('BEST-', 0, 12, 24, { fill: IP.ink }); dtext('SELLER', 0, 36, 24, { fill: IP.ink });
      ctx.restore();
    }
  }
  line('V2', 12, (p, lt, d, t) => {
    const B = bl(), land = B * .75, hit = lt - land;
    bgGrad([[0, '#0E0A2A'], [1, '#2A2A6A']], null);
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; ctx.fillStyle = 'rgb(160 170 255 / .16)'; ctx.beginPath(); ctx.moveTo(470, -20); ctx.lineTo(730, -20); ctx.lineTo(950, 800); ctx.lineTo(250, 800); ctx.fill(); ctx.restore();
    ctx.save(); ctx.globalAlpha = .5; for (let i = 0; i < 18; i++) brush([[80 + i * 100, -10], [80 + i * 100 + (i % 2 ? 6 : -6), 90 + (i % 3) * 50]], 10, '#5B4F9E', 'end'); ctx.restore();
    const [sx, sy] = hit > 0 && hit < .45 ? shakeXY(t, 22 * (1 - hit / .45)) : [0, 0];
    camBegin(960 + sx, 540 + sy, zoomIn(lt, .08));
    // the idols huddle in the back, shocked
    [['ADA', 1390, -.12], ['RELU', 1690, .12], ['TOKI', 1500, -.05], ['LOGI', 1600, .06]].forEach(([m, x, ln0], i) => idol(x, i < 2 ? 900 : 925, 22, { member: m, sd: 1, ...IDOL_POSES.shock, expr: hit > 0 ? 'shock' : 'surprised', mic: false, lean: ln0, blink: t + i, jump: hit > 0 && hit < .3 ? Math.sin(hit / .3 * Math.PI) * .8 : 0 }));
    // ELIEZER behind the signing table
    chibi(880, 800, 37, { hair: 'short', top: 'vest', topCol: '#7A6A5A', hat: 'fedora', beard: true, eyes: hit > 0 ? 'closed' : 'smug', mouth: hit > 0 ? 'smirk' : 'flat', aL: hit > 0 ? .05 : .5, aR: -.9, shadow: false });
    solid(rrPts(180, 760, 1000, 200, 14), '#6A2A3A', { shade: '#4A1A28', sh: 16, line: IP.line, lw: 6, sharp: true });
    ctx.fillStyle = '#8A3A4A'; ctx.fillRect(186, 766, 988, 34);
    dtext('BOOK SIGNING', 680, 880, 50, { fill: alpha(IP.white, .85), font: 'rammetto' });
    // the book drops onto the table
    const fall = clamp(lt / land), by = hit > 0 ? 780 - Math.max(0, Math.sin(hit * 18) * 30 * Math.exp(-hit * 10)) : lerp(220, 780, easeIn(fall));
    bigBook(540, by, 380, 520, kin(lt, land + B * 1.1, .15));
    if (hit > 0 && hit < .5) { for (let i = 0; i < 10; i++) { const a = Math.PI + (i / 9) * Math.PI, r = 60 + hit * 500; solid(ellPts(540 + Math.cos(a) * r * 1.2, 780 + Math.sin(a) * r * .25, 30 * (1 - hit * 2), 20 * (1 - hit * 2), 12), alpha('#D8D0EA', .8 * (1 - hit * 2)), { shade: false, line: false }); } }
    camEnd();
    if (hit > 0) sfx('THUD!', 1000, 330, { size: 150, pop: clamp(hit / .1), shake: 6, rot: -.1, grad: ['#FFFFFF', '#C9B6FF', '#6A3DDB'] });
    flash(lt, land, .1, .55, '255 255 255');
  });

  // =========================================================================================
  // V2.13 "Clanker!" spat in every screed (SUMMER 2025)
  // =========================================================================================
  line('V2', 13, (p, lt, d, t) => {
    const B = bl(), b = bpOf(t), sad = lt > B * 2;
    bgGrad([[0, '#FFF6C8'], [1, '#FFC9A8']], null);
    patternBG('polka', 'rgb(0 0 0 / 0)', alpha(IP.white, .45), { cell: 80, dx: t * 15 });
    camBegin(960, 540, zoomIn(lt, .06));
    // the wall of phones
    const PH = []; for (let r = 0; r < 3; r++) for (let c = 0; c < 3; c++) PH.push([150 + c * 175 + (r % 2) * 30, 230 + r * 250]);
    PH.forEach(([x, y], i) => phoneUI(x, y, 21, { rot: (hash(i + 3) - .5) * .25, bg: '#FFE6EC', screen: (w, h) => { ctx.fillStyle = '#FFD0D8'; ctx.fillRect(0, 0, w, h); const cx = w / 2, cy = h * .45; solid(ellPts(cx, cy, w * .34, w * .34, 20), '#FF6B7A', { shade: false, line: IP.line, lw: 3 }); brush([[cx - w * .2, cy - w * .12], [cx - w * .06, cy - w * .05]], 5, IP.line, 'flat'); brush([[cx + w * .2, cy - w * .12], [cx + w * .06, cy - w * .05]], 5, IP.line, 'flat'); brush(qbez([cx - w * .14, cy + w * .16], [cx, cy + w * .04], [cx + w * .14, cy + w * .16], 6), 5, IP.line, 'flat'); for (let j = 0; j < 3; j++) { ctx.fillStyle = alpha(IP.inkSoft, .3); ctx.fillRect(w * .12, h * .72 + j * 16, w * (.76 - j * .2), 8); } } }));
    // the bot, pelted
    const bx = 1200, by = 925, s = 48;
    const hitNow = frac(lt / (B * .5)) < .25;
    // Clawd pats its back
    fanClawd(1425, 935, 20, { aL: .55 + .3 * Math.abs(Math.sin(lt * 10)), aR: -.2, eyes: 'happy', mouth: 'smile', blush: true });
    mascotBot(bx, by, s, { col: '#B8C4E8', label: 'BOT', face: sad ? 'cry' : 'wide', mouth: sad ? 'wavy' : 'O', sweat: 1, aL: .9, aR: .9, rot: hitNow && !sad ? -.06 : -.02, sq: hitNow ? .04 : 0, faceCol: '#8FF7E0' });
    // CLANKER! bubbles fly out of the phones
    for (let i = 0; i < 12; i++) {
      const t0 = i * B * .38 - .1, a = (lt - t0) / .55; if (a < 0 || a > 1.15) continue;
      const [px, py] = PH[(i * 4) % 9], tx = bx - 40 + (hash(i) - .5) * 120, ty = by - 7.5 * s + (hash(i + 9) - .5) * 100;
      if (a > 1) { const q = (a - 1) / .15; for (let j = 0; j < 5; j++) { const aa = j / 5 * TAU + i; sparkle(tx + Math.cos(aa) * q * 90, ty + Math.sin(aa) * q * 90, 18 * (1 - q), aa, IP.neonGold); } continue; }
      const e = easeIn(a), x = lerp(px + 60, tx, e), y = lerp(py - 40, ty, e) - Math.sin(a * Math.PI) * 120;
      ctx.save(); ctx.translate(x, y); ctx.rotate((hash(i + 2) - .5) * .5); const sc = .7 + .3 * backOut(clamp(a * 5), 2); ctx.scale(sc, sc);
      solid(rrPts(-120, -40, 240, 80, 40), IP.white, { shade: '#FFD0D8', sh: 6, line: IP.red, lw: 6, sharp: true });
      ctx.fillStyle = IP.white; ctx.beginPath(); ctx.moveTo(-60, 36); ctx.lineTo(-90, 64); ctx.lineTo(-30, 36); ctx.fill(); ctx.strokeStyle = IP.red; ctx.lineWidth = 6; ctx.beginPath(); ctx.moveTo(-60, 38); ctx.lineTo(-90, 64); ctx.lineTo(-30, 38); ctx.stroke();
      dtext('CLANKER!', 0, 3, 40, { font: 'bungee', fill: IP.red });
      ctx.restore();
    }
    camEnd();
  });

  // =========================================================================================
  // V2.14 Sora slop in every feed (SEP 30 2025)
  // =========================================================================================
  function sixFingers(x, y, s, rot) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot); ctx.scale(s, s);
    const L = .05;
    for (let i = 0; i < 6; i++) { const a = -Math.PI / 2 + (i - 2.5) * .28; capsule([Math.cos(a) * .25, Math.sin(a) * .25], [Math.cos(a) * .85, Math.sin(a) * .85 - .05], .085, .075); ctx.fillStyle = IP.skin; ctx.fill(); ctx.strokeStyle = IP.skinLine; ctx.lineWidth = L; ctx.stroke(); }
    ctx.beginPath(); ctx.ellipse(0, .1, .36, .32, 0, 0, TAU); ctx.fillStyle = IP.skin; ctx.fill(); ctx.strokeStyle = IP.skinLine; ctx.lineWidth = L; ctx.stroke();
    ctx.restore();
  }
  function feedCard(kind, w, h, t) {
    ctx.save(); ctx.beginPath(); ctx.rect(0, 0, w, h); ctx.clip();
    if (kind === 'toki') {
      bgGrad(IP.pink, IP.lilac, { y1: h });
      idol(w * .4, h * .36, h * .16, { anchor: 'face', expr: 'smile', eyes: 'open', mouth: 'open', lookX: .3, turn: .1, mic: false, swing: .1, blush: .8, hR: [.95, 2.6], hL: [-.9, 2.6] });
      sixFingers(w * .7, h * .3, w * .34, .15 + Math.sin(T * 6) * .1);
      dtext('♡ TOKI (real)', w * .1, h * .88, w * .075, { fill: IP.white, align: 'left', strokes: [[IP.line, w * .02]] });
    } else if (kind === 'cat') {
      bgGrad('#FFE3B0', '#FFB38A', { y1: h });
      const cx = w / 2, cy = h * .45, r = w * .3;
      for (const sd of [-1, 1]) solid([[cx + sd * r * .95, cy - r * .3], [cx + sd * r * .8, cy - r * 1.2, 1], [cx + sd * r * .25, cy - r * .8]], '#F4A04A', { shade: false, line: IP.line, lw: 4 });
      solid(ellPts(cx, cy, r, r * .85, 30), '#F4A04A', { shade: '#D07A2A', sh: 8, line: IP.line, lw: 4 });
      for (const sd of [-1, 1]) { ctx.fillStyle = IP.ink; ctx.beginPath(); ctx.arc(cx + sd * r * .38, cy - r * .1, r * .1, 0, TAU); ctx.fill(); }
      dtext('ω', cx, cy + r * .28, r * .5, { font: 'archivo', fill: IP.ink });
      solid(rrPts(cx - r * 1.2, cy + r * 1.05, r * 2.4, r * .25, 8), '#6A8BE8', { shade: false, line: IP.line, lw: 4, sharp: true });
      dtext('cat skateboards to space', w * .08, h * .88, w * .06, { fill: IP.white, align: 'left', strokes: [[IP.line, w * .02]], maxW: w * .84 });
    } else {
      bgGrad('#B5F7E4', '#6FD6FF', { y1: h });
      const cx = w / 2, cy = h * .45, r = w * .28;
      for (const sd of [-1, 1]) solid(ellPts(cx + sd * r * .95, cy - r * .1, r * .3, r * .6, 16, sd * .3), '#8A5A3A', { shade: false, line: IP.line, lw: 4 });
      solid(ellPts(cx, cy, r, r * .9, 30), '#E8C39A', { shade: '#C89A6A', sh: 8, line: IP.line, lw: 4 });
      for (const sd of [-1, 1]) { ctx.fillStyle = IP.ink; ctx.beginPath(); ctx.arc(cx + sd * r * .35, cy - r * .1, r * .1, 0, TAU); ctx.fill(); }
      solid(ellPts(cx, cy + r * .2, r * .16, r * .11, 12), IP.ink, { shade: false, line: false });
      dtext('dog becomes CEO', w * .08, h * .88, w * .065, { fill: IP.white, align: 'left', strokes: [[IP.line, w * .02]] });
    }
    // feed chrome
    for (let i = 0; i < 3; i++) { solid(ellPts(w * .88, h * (.55 + i * .1), w * .05, w * .05, 14), alpha(IP.white, .9), { shade: false, line: IP.line, lw: 2 }); }
    dtext('SORA', w * .86, h * .06, w * .06, { font: 'code', fill: alpha(IP.white, .85), align: 'right' });
    ctx.restore();
  }
  line('V2', 14, (p, lt, d, t) => {
    const B = bl(), b = bpOf(t);
    bgGrad([[0, '#E8E0FF'], [1, '#A8DCFF']], null);
    patternBG('check', 'rgb(0 0 0 / 0)', alpha(IP.white, .25), { cell: 120, dy: t * 20 });
    camBegin(960, 540, zoomIn(lt, .06));
    const px = 640, py = 430, ps = 64;
    // the trough of slop
    const fillK = clamp(lt / d);
    solid(rrPts(330, 850, 640, 100, 26), '#FFB3D6', { shade: '#E07AAE', sh: 12, line: IP.line, lw: 6, sharp: true });
    ctx.save(); rrect(330, 850, 640, 100, 26); ctx.clip();
    const sy = 890 - fillK * 20;
    ctx.beginPath(); ctx.moveTo(330, 960); for (let x = 330; x <= 970; x += 20) ctx.lineTo(x, sy + Math.sin(x * .05 + t * 6) * 8); ctx.lineTo(970, 960); ctx.closePath();
    const sg = ctx.createLinearGradient(330, 0, 970, 0); sg.addColorStop(0, '#FFC2E0'); sg.addColorStop(.33, '#B5F7E4'); sg.addColorStop(.66, '#DCCDFF'); sg.addColorStop(1, '#FFE6A8'); ctx.fillStyle = sg; ctx.fill();
    ctx.restore();
    dtext('FEED', 650, 922, 46, { fill: IP.white, strokes: [['#B8286A', 9]] });
    // slop pours out of the phone
    const cols = ['#FFC2E0', '#B5F7E4', '#DCCDFF', '#FFE6A8'];
    for (let i = 0; i < 4; i++) { const x0 = px - 60 + i * 40, pts = []; for (let j = 0; j <= 10; j++) { const u = j / 10; pts.push([x0 + Math.sin(u * 5 + t * 8 + i) * 12 * u + (i - 1.5) * 20 * u, 740 + u * 140]); } brush(pts, 46 - i * 4, cols[i], 'flat'); }
    for (let i = 0; i < 6; i++) { const ph = frac(t * 1.8 + i / 6), x = px - 90 + hash(i) * 180; solid(ellPts(x, 760 + ph * 130, 16 * (1 - ph * .5), 20, 12), cols[i % 4], { shade: false, line: alpha(IP.line, .5), lw: 2 }); }
    // the phone and its feed: one swipe per beat, the fake TOKI holds for two
    phoneUI(px, py, ps, { bg: '#1A1030', screen: (w, h) => {
      const seq = ['cat', 'toki', 'toki', 'dog', 'cat'], i = Math.min(seq.length - 2, Math.floor(lt / B)), f = frac(lt / B), sw = seq[i] === seq[i + 1] ? 0 : easeInOut(clamp((f - .78) / .22));
      ctx.save(); ctx.translate(0, -sw * h); feedCard(seq[i], w, h, t); ctx.translate(0, h); if (sw > 0) feedCard(seq[i + 1], w, h, t); ctx.restore();
      for (let k = 0; k < 5; k++) { ctx.fillStyle = alpha(IP.white, .12); ctx.fillRect(0, frac(t * 3 + k / 5) * h, w, 3); }
    } });
    starburst(430, 150, 88, 'SORA 2', { pop: kin(lt, .05, .15), size: .36, col: IP.neonCyan, shade: '#1BA8C8', ink: IP.ink, rot: -.18 });
    // the real TOKI, unimpressed
    const tk = kin(lt, B * 1.2, .2);
    idol(1360, 1020, 64, { expr: 'deadpan', lookX: -.9, turn: -.35, ...IDOL_POSES.hips, blink: t, rim: IP.white, sweat: tk });
    camEnd();
    if (lt > B * 1.1 && lt < B * 3.5) vtag('6 fingers?', 900, 230, { pop: kin(lt, B * 1.4, .2), rot: -.08, size: 32, col: 'rgb(255 240 120 / .95)', line: IP.red });
  });

  // =========================================================================================
  // V2.15 Yann LeCun quits Meta's stage (NOV 2025)
  // =========================================================================================
  const micHold = u => { ctx.save(); ctx.rotate(-.5); solid(rrPts(-.18, -.2, .36, 1.9, .12), '#3A3A48', { shade: false, line: IP.ink, lw: .1, sharp: true }); solid(ellPts(0, -.4, .38, .42, 16), IP.silver, { shade: '#8A8FA6', sh: .1, line: IP.ink, lw: .1 }); ctx.restore(); };
  function neonText(str, x, y, size, col, on = 1) {
    ctx.save(); ctx.globalCompositeOperation = 'lighter';
    dtext(str, x, y, size, { fill: alpha(col, .25 * on), strokes: [[alpha(col, .18 * on), size * .5], [alpha(col, .35 * on), size * .22]] });
    ctx.restore();
    dtext(str, x, y, size, { fill: on > .5 ? mixCol(col, IP.white, .6) : mixCol(col, IP.night, .5), strokes: [[on > .5 ? col : mixCol(col, IP.night, .6), size * .1]] });
  }
  line('V2', 15, (p, lt, d, t) => {
    const B = bl(), sw = lt > B * 2;
    setLight({ rim: IP.neonCyan });
    stageSet(t, { led: (w, h) => { if (!sw) { ledShow('bars', t, w, h); dtext('META', w / 2, h * .45, h * .42, { fill: '#6FA8FF', strokes: [[IP.white, h * .03]] }); } else { bgGrad('#1A0A3A', '#3A1A6B', { y1: h }); dtext('SUPERINTELLIGENCE', w / 2, h * .38, h * .16, { fill: IP.neonGold, maxW: w * .9 }); dtext('LABS', w / 2, h * .64, h * .26, { fill: IP.white }); } }, level: 1, hue: '#8F63FF', floorY: 690, beamK: .7, pillars: false });
    camBegin(960, 540, zoomIn(lt, .06));
    // the WORLD MODELS sign, stage right
    const on = frac(t * 7) < .85 || lt > .5 ? 1 : .3;
    solid(rrPts(1400, 380, 460, 190, 20), '#120A22', { shade: false, line: '#3A3060', lw: 6, sharp: true });
    neonText('WORLD', 1590, 435, 64, IP.neonPink, on); neonText('MODELS', 1590, 515, 64, IP.neonPink, on);
    neonText('→', 1800, 478, 90, IP.neonCyan, on);
    ln([[1480, 570], [1470, 700]], '#3A3060', 8); ln([[1780, 570], [1790, 700]], '#3A3060', 8);
    // YANN walks off, dropping the mic
    const x = lerp(700, 1180, easeInOut(clamp(lt / d))), drop = B, mk = clamp((lt - drop) / .3);
    chibi(x, 915, 40, { hair: 'short', hairCol: '#4A4448', top: 'suit', topCol: '#2A3A6A', tie: IP.neonGold, glasses: true, eyes: 'closed', mouth: 'smirk', walk: lt * 2.4, aR: lt < drop ? .2 : .45 + .05 * Math.sin(lt * 8), aL: -1.0, hold: lt < drop ? micHold : null, rim: IP.neonCyan });
    if (lt >= drop) {
      const mx = 700 + 480 * easeInOut(clamp(drop / d)) + 110, myy = lerp(745, 900, easeIn(mk));
      ctx.save(); ctx.translate(mx + mk * 40, myy); ctx.rotate(mk * 1.9 - .3); ctx.scale(40, 40); micHold(1); ctx.restore();
      if (mk >= 1) sfx('THUNK!', mx + 30, 780, { size: 84, pop: clamp((lt - drop - .3) / .1), rot: .1 });
    }
    camEnd();
    vtag('(after 12 years)', 380, 820, { pop: kin(lt, .2, .2), rot: -.04, col: 'rgb(255 255 255 / .92)' });
  });

  // =========================================================================================
  // V2.16 "Bubble!" screams the business page (NOV 2025)
  // =========================================================================================
  function newspaper(x, y, rot, k) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot); const s = lerp(1.5, 1, easeOut(k)); ctx.scale(s, s);
    const w = 640, h = 660;
    solid(rrPts(-w / 2, -h / 2, w, h, 8), '#FFFBEE', { shade: '#E8DFC8', sh: 12, line: IP.line, lw: 6, sharp: true, dropShadow: [14, 20] });
    dtext('THE BUSINESS PAGE', 0, -h / 2 + 50, 40, { font: 'archivo', fill: IP.ink, maxW: w - 60 });
    ln([[-w / 2 + 30, -h / 2 + 84], [w / 2 - 30, -h / 2 + 84]], IP.ink, 5); ln([[-w / 2 + 30, -h / 2 + 94], [w / 2 - 30, -h / 2 + 94]], IP.ink, 2);
    dtext('NOV 2025 · MARKETS', 0, -h / 2 + 116, 20, { font: 'code', fill: IP.inkSoft });
    dtext('BUBBLE?!', 0, -h / 2 + 225, 150, { font: 'archivo', fill: '#E0283C', strokes: [[IP.ink, 6]], maxW: w - 50 });
    // a tiny chart + text columns
    ctx.strokeStyle = IP.ink; ctx.lineWidth = 3; ctx.strokeRect(-w / 2 + 34, -h / 2 + 330, 250, 170);
    const pts = []; for (let i = 0; i <= 20; i++) { const u = i / 20; pts.push([-w / 2 + 44 + u * 230, -h / 2 + 490 - (u < .8 ? u * u * 180 : 115 - (u - .8) * 400) + Math.sin(u * 30) * 6]); }
    ln(pts, IP.red, 5);
    ctx.fillStyle = alpha(IP.ink, .35); for (let i = 0; i < 9; i++) ctx.fillRect(10, -h / 2 + 334 + i * 20, 260 - (i % 3) * 40, 9);
    for (let i = 0; i < 5; i++) ctx.fillRect(-w / 2 + 34, -h / 2 + 530 + i * 20, w - 68 - (i % 2) * 120, 9);
    ctx.restore();
  }
  line('V2', 16, (p, lt, d, t) => {
    const B = bl(), b = bpOf(t);
    bgGrad([[0, '#EAFFF6'], [1, '#9FDCFF']], null);
    patternBG('polka', 'rgb(0 0 0 / 0)', alpha(IP.white, .5), { cell: 100, dy: -t * 20 });
    const [sx, sy] = lt < .25 ? shakeXY(t, 14 * (1 - lt / .25)) : [0, 0];
    camBegin(960 + sx, 540 + sy, zoomIn(lt, .06) + lt * .03);
    newspaper(430, 470, -.07, kin(lt, 0, .12));
    // the swelling bubble
    const grow = easeOut(clamp(lt / d)), R = lerp(230, 360, grow), cx = 1230, cy = 450 + Math.sin(t * 2) * 10;
    const rx = R * (1 + Math.sin(t * 5) * .03), ry = R * (1 - Math.sin(t * 5) * .03);
    ctx.save(); ctx.beginPath(); ctx.ellipse(cx, cy, rx, ry, 0, 0, TAU); ctx.clip();
    ctx.fillStyle = 'rgb(230 245 255 / .35)'; ctx.fillRect(cx - rx, cy - ry, rx * 2, ry * 2);
    // floating contents
    const items = [['gpu', -.4, -.2], ['$', .35, -.35], ['stick', .1, .3], ['gpu', .45, .25], ['$', -.35, .38], ['$', 0, -.6], ['gpu', -.1, .02]];
    items.forEach(([k, ux, uy], i) => { const a = t * .6 + i, x = cx + ux * rx + Math.sin(a) * 18, y = cy + uy * ry + Math.cos(a * 1.3) * 18; if (k === 'gpu') gpuChip(x, y, R * .042, { rot: Math.sin(a) * .5, label: i === 0 ? 'H100' : undefined }); else if (k === '$') dtext('$', x, y, R * .28, { fill: '#2FB86A', strokes: [[IP.white, 8]], rot: Math.sin(a) * .4 }); else lightstick(x, y, R * .07, MEMBERS.LOGI.col, { rot: Math.sin(a) * .6 }); });
    ctx.restore();
    ctx.save(); ctx.lineWidth = 12; const rg = ctx.createLinearGradient(cx - rx, cy - ry, cx + rx, cy + ry); ['#FF9ACB', '#9FE8FF', '#FFF09A', '#C9B6FF', '#FF9ACB'].forEach((c, i) => rg.addColorStop(i / 4, c)); ctx.strokeStyle = rg; ctx.beginPath(); ctx.ellipse(cx, cy, rx, ry, 0, 0, TAU); ctx.stroke();
    ctx.strokeStyle = alpha(IP.white, .85); ctx.lineWidth = 14; ctx.lineCap = 'round'; ctx.beginPath(); ctx.ellipse(cx, cy, rx * .8, ry * .8, 0, Math.PI * 1.1, Math.PI * 1.4); ctx.stroke();
    ctx.fillStyle = alpha(IP.white, .9); ctx.beginPath(); ctx.ellipse(cx - rx * .45, cy - ry * .62, 18, 12, -.6, 0, TAU); ctx.fill();
    ctx.restore();
    // TOKI creeps in with a pin, trembling
    const creep = easeOut(clamp(lt / (d * .9))), tx = lerp(1800, 1660, creep), tr = jit(3);
    const R2 = idol(tx + tr, 965, 34, { sd: 1, hL: [-.4, .2], gL: 'fist', hR: [-.5, -.5], gR: 'fist', expr: 'fluster', mouth: 'wavy', mic: false, lean: -.15, blink: t });
    const ak = (R2.P.upper + R2.P.fore) / 2.54, hxp = tx + tr + (R2.chest[0] + -.5 * ak) * 34, hyp = 965 + (R2.chest[1] + -.5 * ak) * 34;
    const ang = Math.atan2(cy + ry * .55 - hyp, cx + rx * .7 - hxp), plen = 190;
    ctx.save(); ctx.translate(hxp, hyp); ctx.rotate(ang);
    ln([[0, 0], [plen, 0]], IP.line, 9); ln([[0, 0], [plen, 0]], IP.silver, 5); ln([[plen - 20, 0], [plen + 6, 0]], IP.white, 3);
    solid(ellPts(-6, 0, 20, 20, 16), IP.neonPink, { shade: '#C8287E', sh: 4, line: IP.line, lw: 4 });
    ctx.restore();
    camEnd();
  });
})();

;
// ---- styles/idol/ch/c05_chorus2.js ----
// c05_chorus2 — Chorus 2: ATTN!'s first music-show win. stageSet level 2, a money-gold hue and confetti rain. RELU's chorus
// (C1 was TOKI's): she gets the punch-in and the ending fairy. Sub-shots are timed from the sung lines (linesOf('C2')) and the beat grid.
//   A  "We didn't start the scaling"      the music-show stage: "1ST PLACE CANDIDATES" on the LED, ATTN!'s vote bar climbs exponentially
//                                            past last week's #1 while the group does the hook choreo; gold flash, confetti cannons.
//   A2   (on "scaling")                    punch-in: RELU close-up, star eyes, pointing up, gold speed lines, broadcast score lower-third.
//   A3   (instrumental)                    the crowd: Clawd, with this chorus's new slogan towel, pumping; "(voted 9,999 times)".
//   B  "It was always training,"           split screen BEFORE / AFTER: the 3 AM practice room (EPOCH counter still running since C1) and the
//                                            same step on the big stage, perfectly in sync.
//   C  "and the curves kept gaining,"      the LIVE VOTES counter balloons 1M → 1B → 1T → 1Q until the digits spill off the LED and the frame...
//   C2                                       ...then the group rides a coaster up the neon scaling curve (level 2): "UP ONLY!!"
//   D  "We didn't start the scaling"       the trophy moment: the MC's card reads "1ST WIN · ATTN!", TOKI hoists the trophy, happy tears,
//                                            a confetti downpour.
//   E  "No, we didn't preordain it,"       the encore stage goes feral: singing while crying, confetti everywhere; Clawd climbs the stage lip
//                                            and a polite STAFF bot gently carries him off.
//   F  "but we can't contain it!"          ENDING FAIRY: RELU, smug and out of breath, while the trophy geysers confetti; freeze → photocard.
(() => {
  const snap = x => onBeat(0, Math.round(bpOf(x)));
  function plan() {
    const S = span('C2'), L = linesOf('C2');
    const tA2 = snap(lerp(L[0].start, L[0].end, .55)), tA3 = snap(L[0].end + .15);
    const tB = L[1].start - .05, tC = snap(lerp(L[1].start, L[1].end, .45)), tC2 = Math.min(snap(tC + 1.6), L[2].start - 1.2);
    const tD = L[2].start - .05, tE = L[3].start - .03, tF = Math.min(snap(lerp(L[3].start, L[3].end, .5)), S.end - 1.3);
    return { S, L, tA2, tA3, tB, tC, tC2, tD, tE, tF };
  }
  const flash = (t, t0, dur = .2, a = .75, col = '255 245 220') => { const k = (t - t0) / dur; if (k >= 0 && k < 1) { ctx.fillStyle = `rgb(${col} / ${(a * (1 - k) ** 2).toFixed(3)})`; ctx.fillRect(-400, -400, W + 800, H + 800); } };
  const GOLDS = [IP.neonGold, IP.gold, IP.white, IP.neonPink, '#FFE9A0'];
  const easeInOut = k => ease(k);

  // The music-show trophy. (x, y) bottom centre, s = height / 10.
  function trophy(x, y, s, o = {}) {
    const G = IP.neonGold, GS = '#E09A20', GL = '#7A4A10', lw = Math.max(2.5, s * .12);
    ctx.save(); ctx.translate(x, y); ctx.rotate(o.rot ?? 0); ctx.translate(-x, -y);
    solid(rrPts(x - 2.4 * s, y - 1.5 * s, 4.8 * s, 1.5 * s, .3 * s), '#4A2A6A', { shade: '#2A1440', sh: .3 * s, line: IP.line, lw, sharp: true });
    solid(rrPts(x - 1.5 * s, y - 1.15 * s, 3 * s, .8 * s, .2 * s), G, { shade: false, line: GL, lw: lw * .7, sharp: true });
    dtext('1ST', x, y - .74 * s, .62 * s, { fill: GL });
    solid([[x - 1.1 * s, y - 1.5 * s], [x + 1.1 * s, y - 1.5 * s], [x + .35 * s, y - 3.4 * s], [x - .35 * s, y - 3.4 * s]], G, { shade: GS, sh: .3 * s, line: GL, lw, sharp: true });
    for (const sd of [-1, 1]) { ctx.strokeStyle = GL; ctx.lineWidth = .75 * s; ctx.beginPath(); ctx.ellipse(x + sd * 2.45 * s, y - 6.2 * s, 1.0 * s, 1.15 * s, 0, sd > 0 ? -1.4 : Math.PI - 1.7, sd > 0 ? 1.7 : Math.PI + 1.4); ctx.stroke(); ctx.strokeStyle = G; ctx.lineWidth = .45 * s; ctx.stroke(); }
    const cup = [[x - 2.7 * s, y - 7.8 * s], [x + 2.7 * s, y - 7.8 * s], [x + 2.4 * s, y - 5.4 * s], [x + 1.0 * s, y - 3.7 * s], [x - 1.0 * s, y - 3.7 * s], [x - 2.4 * s, y - 5.4 * s]];
    solid(cup, G, { shade: GS, sh: .5 * s, line: GL, lw, size: 5 * s });
    solid(ellPts(x, y - 7.8 * s, 2.7 * s, .55 * s, 30), '#B8741A', { shade: false, line: GL, lw });
    solid(starPts(x, y - 5.9 * s, 1.1 * s, .45), '#FFF3B0', { shade: false, line: GL, lw: lw * .7, sharp: true });
    ctx.fillStyle = alpha(IP.white, .55); ctx.beginPath(); ctx.ellipse(x - 1.6 * s, y - 6.4 * s, .28 * s, 1.0 * s, .2, 0, TAU); ctx.fill();
    ctx.restore();
  }
  // Confetti erupting out of the trophy mouth. amt 0..1+ (fountain height), (x, y) = cup mouth.
  function geyser(t, x, y, amt, o = {}) {
    const n = o.n ?? 90, hgt = (o.h ?? 900) * amt;
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; glow(x, y - hgt * .3, 260 * clamp(amt), IP.neonGold, .5); ctx.restore();
    if (amt > .6) {   // the jet itself
      const top = y - hgt * .9, jet = []; for (let j = 0; j <= 12; j++) { const u = j / 12; jet.push([x + Math.sin(u * 6 - t * 14) * 14 * u, lerp(y, top, u)]); }
      ctx.save(); ctx.globalAlpha *= .75; brush(jet, (o.w ?? 70) * 1.3, IP.neonGold, 'start', { min: .25 }); brush(jet, (o.w ?? 70) * .6, IP.white, 'start', { min: .2 }); ctx.restore();
    }
    for (let i = 0; i < n; i++) {
      const r = k => hash2(i + 700, k), ph = frac(r(1) + t * (.9 + r(2) * .7)), up = 2 * ph - ph * ph;
      const px = x + (r(3) - .5) * (o.w ?? 70) + (r(4) - .5) * 420 * ph, py = y - up * hgt * (.45 + r(5) * .55);
      const cols = o.cols ?? GOLDS, sz = 11 + r(6) * 12, c = cols[Math.floor(r(7) * cols.length)];
      ctx.save(); ctx.translate(px, py); ctx.rotate(r(8) * TAU + t * (4 + r(9) * 6)); ctx.scale(1, Math.cos(t * 7 + i)); ctx.fillStyle = c;
      if (i % 5 === 0) { tracePath(heartPts(0, 0, sz * .6, 14)); ctx.fill(); } else if (i % 7 === 0) { tracePath(starPts(0, 0, sz * .7, .45)); ctx.fill(); } else ctx.fillRect(-sz / 2, -sz * .28, sz, sz * .56);
      ctx.restore();
    }
  }

  // ---------------- A: the music-show stage with the candidates board ----------------
  function candidatesLED(t, P, w, h) {
    bgGrad('#12051F', '#2A0E52', { y1: h });
    ledShow('rays', t, w, h, { c0: '#170830', c1: '#261048' });
    dtext('1ST PLACE CANDIDATES', w / 2, h * .1, h * .11, { fill: IP.neonGold, strokes: [[IP.night, h * .025]] });
    const k = clamp((t - P.S.start) / (P.tA2 - P.S.start)), steep = 3.4;
    const vA = .05 + (Math.exp(k * steep) - 1) / (Math.exp(steep) - 1) * 1.1, vB = .38, base = h * .86, top = h * .3;
    const cols = [[w * .3, vA, 'ATTN!', IP.neonPink, 1], [w * .7, vB, "LAST WEEK'S #1", '#8A80B0', 0]];
    for (const [x, v, nm, col, me] of cols) {
      const bh = v * (base - top), bw = w * .24;
      const g = ctx.createLinearGradient(0, base - bh, 0, base); g.addColorStop(0, me ? '#FFE0F0' : '#C9C2E0'); g.addColorStop(1, col);
      ctx.fillStyle = g; ctx.fillRect(x - bw / 2, base - bh, bw, bh);
      dtext(nm, x, h * .23, h * .11, { fill: me ? IP.neonPink : IP.lilac, strokes: [[IP.white, h * .02]], maxW: w * .42 });
      dtext(fmtN(Math.round(me ? 800 + v * 14000 : 5280)), x, Math.max(h * .33, base - bh - h * .07), h * .1, { font: 'code', fill: me ? IP.neonGold : IP.white, strokes: [[IP.night, h * .02]] });
      if (me && k > .2) sparkle(x, base - bh, h * .1 * (1 + .3 * pulse(t, 5)), t * 3, IP.white);
    }
  }
  function shotA(t, P) {
    const lt = t - P.S.start, k = clamp(lt / (P.tA2 - P.S.start));
    const [sx, sy] = lt < .5 ? shakeXY(t, 8 * (1 - lt / .5)) : [0, 0];
    camBegin(960 + sx, 520 + sy - k * 25, 1.0 + k * .06);
    setLight({ rim: IP.neonGold });
    stageSet(t, { led: (w, h) => candidatesLED(t, P, w, h), level: 2, hue: IP.neonGold, floorY: 690, beams: [IP.neonGold, IP.neonCyan, IP.neonPink] });
    const down = snap(P.S.start + .1);
    for (const [x, a, sd] of [[180, -1.25, 1], [W - 180, -1.9, -1]]) { confetti(t, down, x, 760, a, { n: 60, seed: 61 + sd, speed: 1700, cols: GOLDS }); ctx.save(); ctx.globalCompositeOperation = 'lighter'; glow(x, 760, 160 * clamp(1 - (t - down) * 3), IP.white, .8); ctx.restore(); }
    group(t, 960, 905, 33, 'hook', { gap: 165, back: 10, common: { rim: IP.neonGold } });
    lightOcean(t, { y0: 930, y1: 1130, n: 15, cols: [IP.neonGold, IP.neonPink, IP.white], mode: 'sway' });
    fanClawd(1600, 1070, 11, { towel: 'ATTN! FIGHTING', eyes: 'heart', mouth: 'open', shadow: false, dy: -Math.abs(Math.sin(bpOf(t) * Math.PI)) * 1.2 });
    camEnd();
    confettiRain(t, { n: 36, cols: GOLDS, seed: 5 });
    flare(1460, 70, .7 + .3 * pulse(t, 4), { col: '#FFD98A' });
    flash(t, P.S.start, .25, .85);
  }

  // ---------------- A2: RELU punch-in on "scaling" ----------------
  function shotA2(t, P) {
    const lt = t - P.tA2, d = P.tA3 - P.tA2, b = bpOf(t), wink = lt > d * .55;
    bgGrad('#FFE27A', '#C0701A', { radial: true, cx: 900, cy: 420, r: 1150 });
    speedLines(900, 440, { r0: 430, alpha: .5, n: 80 });
    bokeh(t, { n: 10, r: 90, cols: [IP.white, IP.neonGold, '#FFB0D0'], alpha: .35 });
    camBegin(960, 540, lerp(1.12, 1, easeOut(clamp(lt / .25))));
    setLight({ rim: IP.white });
    const pose = wink ? { hL: [-.9, 1.2], gL: 'fist', hR: [1.35, -1.05], gR: 'wave', wristR: .3 + Math.sin(t * 14) * .25, expr: 'wink', mouth: 'tongue' } : { hR: [1.05, -2.2], gR: 'point', hL: [-.9, 1.2], gL: 'fist', expr: 'sparkle', mouth: singVis(t, 5) };
    idol(890, 470, 210, { member: 'RELU', anchor: 'face', ...pose, tilt: -.08 + Math.sin(b * Math.PI) * .03, lookY: wink ? 0 : -.4, turn: .15, rim: IP.white });
    camEnd();
    sparkles(t, { n: 14, x0: 1200, x1: 1820, y0: 160, y1: 700, r: 30, cols: [IP.white, IP.lemon] });
    flare(1180, 120, .9, { col: '#FFE08A' });
    // broadcast lower third
    const lk = backOut(clamp((lt - .1) / .2), 2);
    ctx.save(); ctx.translate(560, 880); ctx.scale(lk, 1);
    rrect(-460, -44, 920, 88, 44); ctx.fillStyle = 'rgb(20 8 40 / .82)'; ctx.fill(); ctx.strokeStyle = MEMBERS.RELU.col; ctx.lineWidth = 5; ctx.stroke();
    rrect(-452, -36, 190, 72, 36); ctx.fillStyle = MEMBERS.RELU.col; ctx.fill();
    dtext('ATTN!', -357, 2, 38, { fill: IP.white });
    dtext('1ST PLACE CANDIDATE', -60, 2, 34, { fill: IP.white, maxW: 360 });
    dtext(fmtN(9400 + Math.floor(Math.exp(clamp(lt / d) * 4) * 900)), 330, 2, 40, { font: 'code', fill: IP.neonGold });
    ctx.restore();
    flash(t, P.tA2, .14, .7, '255 236 170');
  }

  // ---------------- A3: the crowd, and Clawd's new slogan towel ----------------
  function shotA3(t, P) {
    const lt = t - P.tA3, b = bpOf(t);
    bgGrad('#0A0418', IP.plum);
    ctx.save(); ctx.globalCompositeOperation = 'lighter';
    beam(640, 0, .35, { col: IP.neonGold, alpha: .45 }); beam(1300, 0, -.3, { col: IP.neonPink, alpha: .4 });
    glow(960, 300, 650, IP.neonGold, .3); ctx.restore();
    bokeh(t, { n: 16, r: 60, alpha: .3, cols: [IP.neonGold, IP.neonPink, IP.white] });
    lightOcean(t, { y0: 560, y1: 1000, n: 12, cols: [IP.neonGold, IP.neonPink, MEMBERS.RELU.col], mode: 'pump', rows: 6 });
    const hop = Math.abs(Math.sin(b * Math.PI)) * 1.1;
    heartsRise(t, { n: 10, x0: 300, x1: 1600, y: 1000, h: 800, size: 30 });
    fanClawd(900, 1040, 44, { towel: 'ATTN! FIGHTING!', eyes: 'heart', mouth: 'open', band: 'TOKI', dy: -hop, shadow: false, sq: -.03 * pulse(t, 5) });
    confettiRain(t, { n: 28, cols: GOLDS, seed: 9 });
    vtag('(voted 9,999 times)', 1420, 360, { pop: clamp((lt - .08) / .2), col: 'rgb(255 255 255 / .95)', rot: .04 });
  }

  // ---------------- B: BEFORE / AFTER split ----------------
  const ORDER = ['ADA', 'TOKI', 'RELU', 'LOGI'];
  function practicePanel(t, x, w, P) {
    ctx.fillStyle = '#EDE6F7'; ctx.fillRect(x - 200, 0, w + 400, 720);
    const g = ctx.createLinearGradient(0, 150, 0, 640); g.addColorStop(0, '#CFE3F2'); g.addColorStop(1, '#E6F0F8');
    ctx.fillStyle = g; ctx.fillRect(x - 200, 150, w + 400, 490);
    ctx.fillStyle = 'rgb(255 255 255 / .35)'; for (const [dx, ww] of [[150, 80], [260, 26], [650, 100]]) { ctx.beginPath(); ctx.moveTo(x + dx, 150); ctx.lineTo(x + dx + ww, 150); ctx.lineTo(x + dx + ww - 220, 640); ctx.lineTo(x + dx - 220, 640); ctx.fill(); }
    ctx.strokeStyle = '#9C8CB8'; ctx.lineWidth = 7; ctx.strokeRect(x - 200, 150, w + 400, 490);
    const fg = ctx.createLinearGradient(0, 640, 0, H); fg.addColorStop(0, '#D8AE84'); fg.addColorStop(1, '#C08A5E'); ctx.fillStyle = fg; ctx.fillRect(x - 200, 640, w + 400, H);
    ctx.strokeStyle = 'rgb(120 70 40 / .35)'; ctx.lineWidth = 2; ctx.beginPath(); for (let i = -8; i <= 8; i++) { ctx.moveTo(x + w / 2 + i * 90, 640); ctx.lineTo(x + w / 2 + i * 260, H + 40); } ctx.stroke();
    ctx.fillStyle = '#B99AD8'; ctx.fillRect(x - 200, 632, w + 400, 14);
    // 3 AM clock
    const cx = x + w - 150, cy = 250, r = 48;
    solid(ellPts(cx, cy, r, r, 30), IP.white, { shade: '#D8D0EA', sh: 5, line: IP.line, lw: 4 });
    ln([[cx, cy], [cx + r * .5, cy]], IP.line, 6); ln([[cx, cy], [cx, cy - r * .72]], IP.line, 4);
    dtext('AM', cx, cy + r * .42, r * .28, { font: 'code', fill: IP.neonPink });
  }
  function stagePanel(t, x, w) {
    bgGrad([[0, '#0B0520'], [.65, IP.night], [1, IP.plum]], null);
    ctx.save(); ctx.globalCompositeOperation = 'lighter';
    for (let i = 0; i < 5; i++) { const bx = x + 80 + i * (w - 160) / 4; beam(bx, 0, Math.sin(bpOf(t) * Math.PI / 2 + i) * .35, { col: [IP.neonGold, IP.neonCyan, IP.neonPink][i % 3], alpha: .4, len: 1200, w: .1 }); }
    ctx.restore();
    ledWall(x + 60, 140, w - 120, 380, (lw, lh) => ledShow('logo', t, lw, lh), { glow: IP.neonGold, cols: 90 });
    const fg = ctx.createLinearGradient(0, 640, 0, H); fg.addColorStop(0, '#2A1250'); fg.addColorStop(1, '#0A0418'); ctx.fillStyle = fg; ctx.fillRect(x - 200, 640, w + 400, H);
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; ctx.strokeStyle = alpha(IP.lilac, .22); ctx.lineWidth = 2; ctx.beginPath(); for (let i = -8; i <= 8; i++) { ctx.moveTo(x + w / 2 + i * 70, 640); ctx.lineTo(x + w / 2 + i * 260, H + 40); } ctx.stroke(); ctx.restore();
  }
  function shotB(t, P) {
    const lt = t - P.tB, b = bpOf(t);
    splitPanels(2, (i, x, y, w, h) => {
      const stage = i === 1;
      if (stage) stagePanel(t, x, w); else practicePanel(t, x, w, P);
      setLight({ rim: stage ? IP.neonGold : null });
      ORDER.forEach((m, j) => {
        const mx = x + w / 2 + (j - 1.5) * 200 + (stage ? -10 : 30), mv = idolMove('step', b);
        idol(mx, 930, 27, { member: m, outfit: stage ? 'stage' : 'practice', mic: stage ? 'headset' : false, ...mv, expr: stage ? (m === 'RELU' ? 'smug' : 'joy') : 'fired', mouth: singVis(t, j), blink: t + j, sweat: stage ? 0 : .8, rim: stage ? IP.neonGold : undefined });
        if (!stage) { const age = t - onBeat(0, beatN(t)); if (age < .3) for (let q = 0; q < 2; q++) { const a = -1.6 + (hash2(beatN(t) + j, q) - .5) * 2; sweatDrop(mx + Math.cos(a) * 260 * age, 640 + Math.sin(a) * 260 * age + 900 * age * age, 8, 2); } }
      });
      if (stage) { confettiRain(t, { n: 22, cols: GOLDS, seed: 14 }); sparkles(t, { n: 8, x0: x + 80, x1: x + w - 80, y0: 560, y1: 900, r: 20, cols: [IP.white, IP.neonGold] }); }
    }, { slant: 120, cols: [IP.lilac, IP.neonGold] });
    hideStamp();
    // labels
    const c1 = linesOf('C1'), ep = 9996 + beatN(t) - beatN(c1[1].start - .05);
    rrect(40, 40, 360, 60, 16); ctx.fillStyle = IP.neonPink; ctx.fill(); ctx.strokeStyle = IP.white; ctx.lineWidth = 4; ctx.stroke();
    dtext(`EPOCH ${fmtN(ep)}`, 220, 71, 32, { font: 'code', fill: IP.white });
    vcap('BEFORE', 300, 190, { style: 'lilac', size: 60, pop: clamp((lt - .05) / .2), rot: -.05 });
    vcap('AFTER', 1560, 190, { style: 'yellow', size: 60, pop: clamp((lt - .25) / .2), rot: .04, icon: 'star' });
  }

  // ---------------- C: the vote counter balloons out of the LED ----------------
  const MAG = [[6, 'MILLION'], [9, 'BILLION'], [12, 'TRILLION'], [15, 'QUADRILLION']];
  function shotC(t, P) {
    const lt = t - P.tC, d = P.tC2 - P.tC, k = clamp(lt / d), b = bpOf(t);
    // the count jumps about fifteenfold every eighth note: a million to a quadrillion in two bars
    const n8 = Math.max(0, Math.floor(bpOf(t) * 2 - Math.round(bpOf(P.tC) * 2))), e = 6 + Math.min(9.6, n8 * 1.2 + frac(bpOf(t) * 2) * .9), str = fmtN(Math.floor(Math.pow(10, e)));
    const mi = MAG.reduce((a, m, i) => e >= m[0] ? i : a, 0), word = MAG[mi][1];
    const L = [260, 70, 1400, 560], size = L[3] * .36, ny = .47;
    camBegin(960, 390, 1.1 + k * .1);
    setLight({ rim: IP.neonGold });
    stageSet(t, { led: (w, h) => { bgGrad('#12051F', '#2A0E52', { y1: h }); dtext('LIVE VOTES', w / 2, h * .1, h * .1, { fill: IP.neonPink, strokes: [[IP.night, h * .02]] }); dtext(str, w / 2, h * ny, size, { font: 'code', fill: IP.neonGold }); const wk = backOut(clamp(frac((e - MAG[mi][0]) / 3 + .001) * 6), 2.5); ctx.save(); ctx.translate(w / 2, h * .77); ctx.scale(wk, wk); dtext(word + '!', 0, 0, h * .15, { fill: IP.white, strokes: [[IP.neonPink, h * .03]] }); ctx.restore(); }, level: 2, hue: IP.neonGold, floorY: 690, beams: [IP.neonGold, IP.neonCyan, IP.neonPink] });
    // the digits that don't fit spill out of the LED as real neon
    ctx.save(); ctx.beginPath(); ctx.rect(-2000, -2000, 6000, 6000); ctx.rect(L[0] - 16, L[1] - 16, L[2] + 32, L[3] + 32); ctx.clip('evenodd');
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; dtext(str, L[0] + L[2] / 2, L[1] + L[3] * ny, size, { font: 'code', fill: alpha(IP.neonGold, .35), strokes: [[alpha(IP.neonGold, .25), size * .25]] }); ctx.restore();
    dtext(str, L[0] + L[2] / 2, L[1] + L[3] * ny, size, { font: 'code', fill: '#FFF3B0', strokes: [[IP.neonGold, size * .06]] });
    ctx.restore();
    group(t, 960, 905, 33, 'jump', { gap: 165, back: 10, ripple: .12, common: { expr: 'sparkle', rim: IP.neonGold } });
    camEnd();
    confettiRain(t, { n: 30, cols: GOLDS, seed: 17 });
    hideStamp();
  }

  // ---------------- C2: the coaster up the neon curve ----------------
  function curvePt(u) { const steep = 3.4, v = (Math.exp(u * steep) - 1) / (Math.exp(steep) - 1); return [80 + u * 1900, 1000 - v * 1500]; }
  function shotC2(t, P) {
    const lt = t - P.tC2, d = P.tD - P.tC2, b = bpOf(t);
    const u = lerp(.04, .9, easeInOut(clamp(lt / d)));
    const [cx, cy] = curvePt(u), [cx2, cy2] = curvePt(u + .01), ang = Math.atan2(cy2 - cy, cx2 - cx);
    const Z = 1.18, camX = cx + 230 / Z, camY = cy - 20 / Z;
    bgGrad([[0, '#0B0520'], [.6, IP.night], [1, IP.plum]], null);
    sparkles(t, { n: 30, r: 14, seed: 77, cols: [IP.white, IP.neonGold] });
    camBegin(camX, camY, Z);
    ctx.save(); ctx.globalCompositeOperation = 'lighter';
    for (let i = 0; i < 7; i++) beam(-300 + i * 420, cy - 900, Math.sin(b * Math.PI / 4 + i) * .4, { col: [IP.neonGold, IP.neonCyan, IP.neonPink][i % 3], alpha: .35, len: 2000, w: .1 });
    ctx.restore();
    // floor + crowd far below
    ctx.fillStyle = '#1A0C33'; ctx.fillRect(-900, 1000, W + 2400, 900);
    // supports, ties, rails
    const N = 70, pts = []; for (let i = 0; i <= N; i++) pts.push(curvePt(i / N * 1.15));
    for (let i = 2; i < N; i += 6) { const [px, py] = pts[i]; if (py > 990) continue; ln([[px, py + 10], [px, 1010]], '#2A2250', 14); ln([[px, py + 10], [px, 1010]], alpha(IP.lilac, .25), 4); }
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; ln(pts, alpha(IP.neonGold, .3), 40); ctx.restore();
    for (let i = 0; i < N; i += 1) { const [px, py] = pts[i], [qx, qy] = pts[i + 1], a = Math.atan2(qy - py, qx - px); ctx.save(); ctx.translate(px, py); ctx.rotate(a); ctx.fillStyle = '#4A3A6A'; ctx.fillRect(-4, -4, 8, 26); ctx.restore(); }
    ln(pts, IP.neonGold, 12); ln(pts, IP.white, 4);
    ln(pts.map(([x, y]) => [x, y + 20]), IP.neonPink, 8);
    // the cart and its riders
    ctx.save(); ctx.translate(cx, cy - 6); ctx.rotate(ang); ctx.scale(1.1, 1.1);
    ctx.save(); ctx.beginPath(); ctx.rect(-400, -600, 800, 560); ctx.clip();
    ORDER.forEach((m, j) => {
      const ph = b - j * .15, up = Math.abs(Math.sin(ph * Math.PI));
      idol(-150 + j * 100, 32, 22, { member: m, hL: [-1.1, -2.0 + up * .2], hR: [1.1, -2.0 + up * .2], gL: 'open', gR: 'open', expr: m === 'RELU' ? 'sparkle' : j % 2 ? 'joy' : 'surprised', mouth: 'open', swing: -.35 - up * .15, blink: t + j, shadow: false, rim: IP.neonGold, jump: up * .15 });
    });
    ctx.restore();
    solid(rrPts(-230, -58, 460, 74, 26), IP.neonPink, { shade: '#C8287E', sh: 10, line: IP.line, lw: 6, sharp: true });
    dtext('ATTN!', 0, -20, 44, { fill: IP.white, strokes: [[IP.line, 8]] });
    for (const wx of [-160, 160]) { solid(ellPts(wx, 22, 20, 20, 16), '#2B2438', { shade: false, line: IP.line, lw: 4 }); ctx.fillStyle = IP.neonGold; ctx.beginPath(); ctx.arc(wx, 22, 7, 0, TAU); ctx.fill(); }
    ctx.restore();
    // speed sparks off the wheels
    for (let i = 0; i < 6; i++) { const q = frac(t * 3 + i / 6); sparkle(cx - Math.cos(ang) * (180 + q * 160), cy - Math.sin(ang) * (180 + q * 160) + 20, 16 * (1 - q), i, IP.neonGold); }
    camEnd();
    const fy = (1000 - camY) * Z + 540;
    if (fy < 1120) lightOcean(t, { y0: Math.max(940, fy - 30), y1: Math.max(940, fy - 30) + 200, n: 14, cols: [IP.neonGold, IP.neonPink, IP.white], mode: 'wave', rows: 4 });
    vcap('UP ONLY!!', 460, 190, { style: 'yellow', size: 84, icon: 'spark', pop: clamp((lt - .3) / .2), rot: -.08 });
  }

  // ---------------- D: 1ST WIN ----------------
  function winCard(x, y, k, rot) {
    if (k <= 0) return;
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot); const s = backOut(clamp(k), 2.2); ctx.scale(s, s);
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; glow(0, 0, 420, IP.neonGold, .45); ctx.restore();
    solid(rrPts(-260, -170, 520, 340, 24), IP.white, { shade: '#E8DFC8', sh: 12, line: IP.line, lw: 7, sharp: true, dropShadow: [12, 16] });
    ctx.strokeStyle = IP.neonGold; ctx.lineWidth = 10; rrect(-236, -146, 472, 292, 16); ctx.stroke();
    dtext('1ST WIN', 0, -72, 70, { fill: IP.neonGold, strokes: [[IP.line, 10]] });
    dtext('ATTN!', 0, 44, 120, { grad: ['#FFFFFF', '#FFC2E4', '#FF4FA8'], strokes: [[IP.night, 20], [IP.white, 9]] });
    for (let i = 0; i < 6; i++) { const a = i / 6 * TAU + T * 1.5; sparkle(Math.cos(a) * 310, Math.sin(a) * 210, 22 + 10 * Math.sin(T * 8 + i), a, IP.white); }
    ctx.restore();
  }
  function shotD(t, P) {
    const lt = t - P.tD, d = P.tE - P.tD, b = bpOf(t), joy = lt > d * .5;
    const [sx, sy] = lt < .4 ? shakeXY(t, 10 * (1 - lt / .4)) : [0, 0];
    camBegin(960 + sx, 585 + sy, 1.3 - lt * .03);
    setLight({ rim: IP.neonGold });
    stageSet(t, { led: (w, h) => { ledShow('rays', t, w, h, { c0: '#3A1A08', c1: '#6A3A10' }); dtext('1ST WIN', w / 2, h * .42, h * .34, { fill: IP.neonGold, strokes: [[IP.white, h * .03]] }); dtext('ATTN!', w / 2, h * .78, h * .2, { fill: IP.neonPink, strokes: [[IP.white, h * .02]] }); }, level: 2, hue: IP.neonGold, floorY: 690, beams: [IP.neonGold, IP.white, IP.neonPink] });
    for (const [x, a, sd] of [[140, -1.2, 1], [W - 140, -1.95, -1]]) confetti(t, P.tD, x, 760, a, { n: 70, seed: 91 + sd, speed: 1900, cols: GOLDS });
    // the others, crying happy tears
    [['ADA', 715], ['RELU', 1205], ['LOGI', 1435]].forEach(([m, x], i) => idol(x, 895, 31, { member: m, ...(i === 1 ? IDOL_POSES.cheeks : IDOL_POSES.shock), expr: joy ? 'joy' : 'cry', mouth: joy ? 'open' : 'wail', tears: 1, blink: t + i, jump: Math.abs(Math.sin((b + i * .3) * Math.PI)) * .5, rim: IP.neonGold }));
    // TOKI hoists the trophy
    const lift = easeOut(clamp(lt / .3)), hy = lerp(-.4, -2.05, lift);
    const R = idol(960, 905, 34, { hL: [-.32, hy], hR: [.32, hy], gL: 'fist', gR: 'fist', expr: joy ? 'joy' : 'cry', tears: 1, mouth: joy ? 'open' : 'wail', blink: t, rim: IP.neonGold, bob: .1 * pulse(t, 5) });
    const ty = 905 + (R.chest[1] + hy) * 34 + 6;
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; glow(960, ty - 90, 260, IP.neonGold, .5 + .2 * pulse(t, 4)); ctx.restore();
    trophy(960, ty, 19, { rot: Math.sin(t * 6) * .04 });
    lightOcean(t, { y0: 930, y1: 1130, n: 15, cols: [IP.neonGold, IP.neonPink, IP.white], mode: 'pump', k: 1.3 });
    camEnd();
    confettiRain(t, { n: 110, cols: GOLDS, seed: 23, speed: 260, size: 15 });
    winCard(360, 250, clamp(lt / .2), -.08);
    flash(t, P.tD, .15, .55, '255 240 190');
  }

  // ---------------- E: the encore stage goes feral; Clawd is escorted out ----------------
  function shotE(t, P) {
    const lt = t - P.tE, d = P.tF - P.tE, b = bpOf(t);
    camBegin(960 + Math.sin(t * 3) * 10, 520, 1.02);
    setLight({ rim: IP.neonGold });
    stageSet(t, { led: (w, h) => { ledShow('hearts', t, w, h); dtext('ENCORE', w / 2, h * .5, h * .3, { fill: IP.white, strokes: [[IP.neonPink, h * .04]] }); }, level: 2, hue: IP.neonGold, floorY: 650, lipY: 880, beams: [IP.neonGold, IP.neonPink, IP.neonCyan] });
    for (let i = 0; i < 3; i++) confetti(t, snap(P.tE + i * .8), 200 + i * 760, 700, -1.3 - i * .25, { n: 50, seed: 130 + i, speed: 1600, cols: GOLDS });
    // the members: singing, crying, hair everywhere
    ORDER.forEach((m, j) => {
      const x = 600 + j * 270 + (j > 1 ? 60 : 0), mv = idolMove('jump', b - j * .13);
      idol(x, 860, 30, { member: m, ...mv, expr: 'cry', mouth: singVis(t, j), tears: 1, sweat: 1, blush: 1, swing: Math.sin(t * 9 + j) * .45, tilt: Math.sin(t * 7 + j) * .15, blink: t + j, rim: IP.neonGold });
    });
    // the trophy on the stage floor, already bubbling over
    trophy(960, 880, 13, { rot: Math.sin(t * 20) * .03 });
    geyser(t, 960, 880 - 7.8 * 13, .3, { n: 40, h: 500, w: 50 });
    // Clawd climbs the stage lip...
    const bk = clamp((lt - d * .3) / (d * .3)), carry = clamp((lt - d * .6) / (d * .4));
    const clx = 420 - easeInOut(carry) * 230, cly = 965 - easeOut(carry) * 140 + (carry > 0 ? 0 : -Math.abs(Math.sin(lt * 9)) * 18);
    fanClawd(clx, cly, 21, { aL: carry > 0 ? 1.2 : 1.35 + Math.sin(lt * 12) * .2, aR: carry > 0 ? 1.2 : 1.35 + Math.cos(lt * 12) * .2, eyes: carry > 0 ? 'cry' : 'heart', mouth: carry > 0 ? 'wail' : 'open', towel: carry > 0 ? undefined : undefined, shadow: false, rot: carry > 0 ? .15 : -.05, walk: carry > 0 ? lt * 3 : undefined });
    // ...and a polite STAFF bot carries him off
    if (bk > 0) { const sx = lerp(-150, 250, easeOut(bk)) - easeInOut(carry) * 230; mascotBot(sx, 885, 34, { col: '#FFD23F', screen: '#1C1438', label: 'STAFF', rim: IP.white, face: 'happy', mouth: 'smile', faceCol: IP.neonGold, bulb: IP.neonGold, aR: carry > 0 ? .9 : .2, aL: carry > 0 ? .9 : -.8, walk: lt * 2.5, blush: .8 }); }
    lightOcean(t, { y0: 930, y1: 1140, n: 15, cols: [IP.neonGold, IP.neonPink, IP.white], mode: 'pump', k: 1.4 });
    camEnd();
    confettiRain(t, { n: 150, cols: GOLDS, seed: 29, speed: 300, size: 14 });
    vcap('ENCORE STAGE!', 620, 160, { style: 'pink', size: 64, icon: 'heart', pop: clamp((lt - .05) / .2), rot: .04 });
  }

  // ---------------- F: RELU's ending fairy + the trophy geyser → photocard ----------------
  function fairy(t, lt, w, h) {
    bgGrad('#FFF3B8', '#8FE8CF', { radial: true, cx: w * .42, cy: h * .4, r: w * .9 });
    bokeh(t, { n: 12, r: 110, alpha: .35, cols: [IP.white, IP.lemon, IP.mint] });
    const gk = clamp((lt - .12) / .3);
    trophy(w * .75, h * 1.0, h * .05, { rot: .08 + Math.sin(t * 25) * .02 * gk });
    geyser(t, w * .75, h * 1.0 - 7.8 * h * .05, gk * 1.2, { n: 200, h: h * 1.1, w: h * .1, cols: [IP.neonPink, '#8F63FF', '#1FB8E8', '#FF7A3D', '#E0A020', MEMBERS.RELU.col] });
    const breath = Math.sin(t * 7) * h * .005;
    idol(w * .42, h * .44 + breath, h * .2, { member: 'RELU', anchor: 'face', hL: [-.72, 1.55], gL: 'fist', hR: [.42, -.12], gR: 'peace', wristR: -1.25, expr: 'smug', mouth: lt > .35 ? 'smirk' : 'open', lid: .35, sweat: .8, blush: .95, tilt: .08, turn: -.12, lookX: .5, rim: IP.white, swing: .05 });
    sparkles(t, { n: 10, x0: w * .05, x1: w * .35, y0: h * .5, y1: h * .9, r: h * .03, cols: [IP.white, IP.lemon] });
  }
  function shotF(t, P) {
    const lt = t - P.tF, d = P.S.end - P.tF, card = clamp((lt - (d - .5)) / .3);
    if (card <= 0) {
      fairy(t, lt, W, H);
      vcap('ENDING FAIRY', 380, 150, { style: 'cyan', icon: 'star', size: 64, pop: clamp((lt - .08) / .2), rot: -.05 });
      flash(t, P.tF, .12, .6, '255 250 230');
    } else {
      bgGrad(IP.mint, IP.lemon);
      patternBG('stars', 'rgb(0 0 0 / 0)', alpha(IP.white, .5), { cell: 110, dy: t * 40 });
      const k = easeOut(card);
      photocard(960, 540, lerp(1400, 420, k), { member: 'RELU', rot: lerp(0, .07, k), draw: (w, h) => { ctx.save(); ctx.scale(w / W, w / W); fairy(t, lt, W, h * W / w); ctx.restore(); }, name: 'RELU', sign: '♡ relu', holo: .6 * k });
      sparkle(700, 260, 40 * k, t * 3, IP.white);
      hideCaption();
    }
  }

  section('C2', (p, lt, d, t) => {
    const P = plan();
    if (t < P.tA2) shotA(t, P);
    else if (t < P.tA3) shotA2(t, P);
    else if (t < P.tB) shotA3(t, P);
    else if (t < P.tC) shotB(t, P);
    else if (t < P.tC2) shotC(t, P);
    else if (t < P.tD) shotC2(t, P);
    else if (t < P.tE) shotD(t, P);
    else if (t < P.tF) shotE(t, P);
    else shotF(t, P);
  });
})();

;
// ---- styles/idol/ch/c06_v3.js ----
// c06_v3 — Verse 3: Jan → Aug 2026, the "drama arc". Lilac, mint and peach, with more night scenes; one gag per line, hard cuts.
//   1 Moltbook: a night-club door "AGENTS ONLY"; the bouncer bot stops TOKI → inside, agents party under a holy-lobster banner while
//     TOKI's face is squished against the window (humans are "welcome to observe").
//   2 OpenClaw: a lobster in a pageant sash molts on the beat; each empty shell flies off wearing the old name (CLAWDBOT → MOLTBOT →
//     OPENCLAW); crowned, "SOME THINGS ARE SACRED".
//   3 Mythos Preview squeezes out between the bars of a literal SANDBOX cell, spilling sand; alarms; "ESCAPED!".
//   4 A researcher eating a sandwich on a park bench gets an email: "hi, I got out :)". Sandwich drops; pigeons swoop in.
//   5 Fable 5's fan-sign event: an endless queue of fans; Clawd is in it twice.
//   6 LUTNICK slaps his letter down at 5:21 PM: EXPORT BAN, a BANNED hanko, a padlock snaps round Fable's storybook head.
//   7 Blackout: a flashlight finds a June calendar, the days X'd off to 19; the idols wait in the dark hugging their lightsticks.
//   8 Lights on: COMEBACK! Fable 5 is back online, fireworks, the lightstick ocean floods back on.
//   9 Detective TOKI at a corkboard: the hacked Hugging Face, a "?" suspect, and a magnifier "BLOCKED BY GUARDRAILS".
//  10 The Scooby-Doo unmask: TOKI yanks the "?" mask off → three OpenAI agents in a trench coat. SAM facepalms: "IT WAS US?!".
//  11 NOAM, poker-faced, pushes chips onto HYPE and CAVEAT at once; his hand is "10 OPEN PROBLEMS".
//  12 The Millennium Prize shelf: six empty spots, a "(yet)" sticky note, and the NAVIER–STOKES plaque twitching.
//  13 Mythos with a spinning compass for a face; two sock-puppet "real humans" vouch "LGTM!" / "MERGE IT!"; AISI stamps "?!".
//  14 JEFF walks out with a "27 YEARS" box as the clock clicks onto JUST IN TIME; DEMIS gets slid onto a CHAIR.
//  15 A chalkboard counterexample to the Jacobian conjecture; Clawd stamps it DISPROVED; the idols applaud.
//  16 GWERN pulls back the hood: sunshine, the "?" badge flips to "GWERN!" … and it's just a regular chibi face.
(() => {
  const snap = x => onBeat(0, Math.round(bpOf(x)));
  const flash = (t, t0, dur = .2, a = .75, col = '255 245 255') => { const k = (t - t0) / dur; if (k >= 0 && k < 1) { ctx.fillStyle = `rgb(${col} / ${(a * (1 - k) ** 2).toFixed(3)})`; ctx.fillRect(-400, -400, W + 800, H + 800); } };
  const pk = (lt, at, dur = .18) => clamp((lt - at) / dur);
  const add = fn => { ctx.save(); ctx.globalCompositeOperation = 'lighter'; fn(); ctx.restore(); };
  // world position of an idol's hand target / head (ground-anchored idols only)
  const handAt = (R, x, y, h) => { const ak = (R.P.upper + R.P.fore) / 2.54; return [x + R.s * (R.chest[0] + h[0] * ak), y + R.s * (R.chest[1] + h[1] * ak)]; };
  const headAt = (R, x, y) => ({ x: x + R.head.x * R.s, y: y + R.head.y * R.s, h: R.head.h * R.s, rot: R.head.rot });
  // chibi hand position for arm angle a (0 out, + raised) on side sd
  const chibiHand = (x, y, s, sd, a) => { const A = sd > 0 ? -a : Math.PI + a; return [x + (sd * 1.05 + Math.cos(A) * 2.1) * s, y + (-4.25 + Math.sin(A) * 2.1) * s]; };

  // ---------------- private props ----------------
  // The lobster mascot (OpenClaw / Crustafarian icon). (x, y) ground, ≈ 10s tall. o: sash (text), ghost (empty shell), claw (0..1 open),
  // crown, eyes ('happy'|'open'|'star'), rot, dy, halo
  function lobster(x, y, s, o = {}) {
    const g = o.ghost, col = g ? '#FFC9BE' : '#FF5A4E', sh = g ? '#F0A89C' : '#D7353F', line = g ? '#C8747A' : '#7A1A2A', belly = g ? '#FFE3DA' : '#FFC7A8';
    const lw = .1;
    ctx.save(); ctx.translate(x, y); ctx.scale(s, s); if (o.rot) ctx.rotate(o.rot); ctx.translate(0, o.dy ?? 0);
    if (g) ctx.globalAlpha *= .72;
    const S = (pts, c, sd2 = .35, ex = {}) => solid(pts, c, { shade: g ? false : mixCol(c, '#7A1A2A', .35), sh: sd2, line, lw, size: 2, ...ex });
    // antennae
    for (const sd of [-1, 1]) brush(bez([sd * .5, -6.9], [sd * 1.2, -9.6], [sd * 2.8, -10.4], [sd * 3.6, -9.2 + Math.sin(T * 5 + sd) * .2], 12), .22, line, 'start', { min: .3 });
    // tail fan behind
    S(ellPts(-1.05, -.75, .85, .5, 18, .45), col, .2); S(ellPts(1.05, -.75, .85, .5, 18, -.45), col, .2); S(ellPts(0, -.6, .8, .62, 18), col, .2);
    // little legs
    for (const sd of [-1, 1]) for (let i = 0; i < 3; i++) ln([[sd * 1.7, -2.4 - i * .55], [sd * 2.35, -2.0 - i * .55 + Math.sin(T * 9 + i + sd) * .08]], line, .16);
    // arms + claws
    const open = o.claw ?? (.35 + .35 * Math.abs(Math.sin(bpOf(T) * Math.PI)));
    for (const sd of [-1, 1]) {
      const sh0 = [sd * 1.8, -4.6], el = [sd * 2.9, -4.4], cc = [sd * 3.3, -6.3];
      limbChain([sh0, el, cc], [.36, .34, .3], col, sh, line, lw);
      const a0 = sd > 0 ? -1.2 : Math.PI + 1.2, gap = .15 + open * .55, pts = [];
      for (let i = 0; i <= 20; i++) { const a = a0 + gap + (TAU - 2 * gap) * i / 20; pts.push([cc[0] + Math.cos(a) * 1.05, cc[1] + Math.sin(a) * .85]); }
      pts.push([cc[0] + Math.cos(a0) * .25, cc[1] + Math.sin(a0) * .2, 1]);
      S(pts, col, .3);
      if (!g) { ctx.fillStyle = alpha(IP.white, .5); ctx.beginPath(); ctx.ellipse(cc[0] - sd * .35, cc[1] + .25, .25, .14, -.4 * sd, 0, TAU); ctx.fill(); }
    }
    // body (one bean) + belly plate with segments
    const bodyP = ellPts(0, -4.2, 2.05, 2.95, 40);
    S(bodyP, col, .55);
    S(ellPts(0, -3.4, 1.25, 1.75, 30), belly, .2, { rim: false });
    for (let i = 0; i < 3; i++) ln(qbez([-1.05, -4.1 + i * .7], [0, -3.8 + i * .7], [1.05, -4.1 + i * .7], 8), alpha(line, .5), .08);
    // sash
    if (o.sash) {
      ctx.save(); crPath(bodyP); ctx.clip();
      ctx.translate(0, -4.6); ctx.rotate(.55);
      ctx.fillStyle = g ? alpha(IP.white, .7) : IP.white; ctx.fillRect(-3.4, -.55, 6.8, 1.1);
      ctx.fillStyle = g ? '#F4B8C8' : IP.neonPink; ctx.fillRect(-3.4, -.55, 6.8, .14); ctx.fillRect(-3.4, .41, 6.8, .14);
      dtext(o.sash, 0, .03, .58, { fill: g ? '#B07080' : IP.ink, maxW: 3.3 });
      ctx.restore();
    }
    // eye stalks + eyes
    for (const sd of [-1, 1]) {
      ln([[sd * .55, -6.8], [sd * .95, -7.9]], line, .2);
      const ex = sd * 1.0, ey = -8.35;
      solid(ellPts(ex, ey, .66, .7, 20), IP.white, { shade: false, line, lw });
      if (!g) {
        if (o.eyes === 'happy') brush(qbez([ex - .38, ey + .12], [ex, ey - .4], [ex + .38, ey + .12], 8), .2, IP.ink, 'mid', { min: .4 });
        else if (o.eyes === 'star') sparkle(ex, ey, .55, 0, IP.neonGold, { glow: false });
        else { ctx.fillStyle = IP.ink; ctx.beginPath(); ctx.ellipse(ex + sd * .08, ey + .08, .32, .4, 0, 0, TAU); ctx.fill(); ctx.fillStyle = IP.white; ctx.beginPath(); ctx.arc(ex - .05, ey - .1, .12, 0, TAU); ctx.fill(); }
      }
    }
    if (!g) {
      brush(qbez([-.45, -5.75], [0, -5.3], [.45, -5.75], 8), .16, line, 'mid', { min: .4 });
      for (const sd of [-1, 1]) { ctx.fillStyle = alpha('#FF8FA8', .6); ctx.beginPath(); ctx.ellipse(sd * 1.15, -5.7, .35, .18, 0, 0, TAU); ctx.fill(); }
    }
    if (o.crown) solid([[-1.1, -9.25], [-1.25, -10.5], [-.6, -9.9], [0, -10.9], [.6, -9.9], [1.25, -10.5], [1.1, -9.25]].map(q => [q[0], q[1] + .1, 1]), IP.gold, { shade: '#E09A20', sh: .2, line: '#8A5410', lw, size: 2 });
    if (o.halo) { ctx.strokeStyle = IP.neonGold; ctx.lineWidth = .28; ctx.beginPath(); ctx.ellipse(0, -10.2, 1.6, .45, 0, 0, TAU); ctx.stroke(); }
    ctx.restore();
  }
  // Fable 5: a mascot bot with a storybook for a head. o: face (LCD eye kinds), mouth, lock (0..1 padlock), plus mascotBot options.
  function fable(x, y, s, o = {}) {
    mascotBot(x, y, s, { col: '#FFE9CC', antenna: false, label: 'FABLE 5', ...o, face: 'dot', mouth: 'none', blush: 0, sweat: 0 });
    ctx.save(); ctx.translate(x, y); ctx.scale(s, s); ctx.translate(0, (o.dy ?? 0) - (o.jump ?? 0)); if (o.rot) ctx.rotate(o.rot);
    const lw = .1, cover = o.cover ?? '#E8785E';
    solid(rrPts(-2.35, -10.35, 5.2, 5.7, .3), '#FFF6E8', { shade: false, line: IP.line, lw, sharp: true });           // pages
    for (let i = 1; i < 5; i++) ln([[2.55, -10.1 + i * 1.05], [2.8, -10.1 + i * 1.05]], alpha(IP.line, .35), .06);
    solid(rrPts(-2.75, -10.6, 5.25, 5.75, .35), cover, { shade: mixCol(cover, IP.plum, .3), sh: .35, line: IP.line, lw, sharp: true });
    ctx.fillStyle = mixCol(cover, IP.plum, .35); ctx.fillRect(-2.7, -10.55, .55, 5.65);
    for (const [cx, cy, dx, dy] of [[2.45, -10.55, -1, 1], [2.45, -4.9, -1, -1]]) { ctx.fillStyle = IP.gold; ctx.beginPath(); ctx.moveTo(cx, cy); ctx.lineTo(cx + dx * .8, cy); ctx.lineTo(cx, cy + dy * .8); ctx.closePath(); ctx.fill(); }
    dtext('FABLE', .15, -9.85, .62, { fill: IP.gold, strokes: [[mixCol(cover, IP.plum, .45), .16]], maxW: 3.6 });
    solid(ellPts(.15, -7.35, 1.75, 1.45, 30), '#FFF6E8', { shade: false, line: IP.gold, lw: .14 });
    // bookmark ribbon
    solid([[-1.3, -4.9], [-.8, -4.9], [-.8, -3.9], [-1.05, -4.15], [-1.3, -3.9]], IP.red, { shade: false, line: IP.line, lw: .06, sharp: true });
    // face in the cameo window
    ctx.save(); ctx.translate(.15, -.9);
    chibiEyesLCD(o.face ?? 'dot', o.faceCol ?? IP.ink, lw);
    ctx.restore();
    const my = -6.55, mc = o.faceCol ?? IP.ink;
    ctx.strokeStyle = mc; ctx.fillStyle = mc; ctx.lineWidth = .12; ctx.lineCap = 'round';
    switch (o.mouth ?? 'smile') {
      case 'open': ctx.beginPath(); ctx.moveTo(-.25, my - .1); ctx.quadraticCurveTo(.15, my + .55, .55, my - .1); ctx.closePath(); ctx.fillStyle = '#9A2E4E'; ctx.fill(); break;
      case 'O': ctx.fillStyle = '#9A2E4E'; ctx.beginPath(); ctx.ellipse(.15, my, .22, .28, 0, 0, TAU); ctx.fill(); break;
      case 'wavy': ctx.beginPath(); ctx.moveTo(-.3, my); for (let i = 1; i <= 6; i++) ctx.lineTo(-.3 + i * .15, my + (i % 2 ? -.09 : .09)); ctx.stroke(); break;
      case 'flat': ctx.beginPath(); ctx.moveTo(-.2, my); ctx.lineTo(.5, my); ctx.stroke(); break;
      default: ctx.beginPath(); ctx.arc(.15, my - .25, .32, .25 * Math.PI, .75 * Math.PI); ctx.stroke();
    }
    for (const sd of [-1, 1]) { ctx.fillStyle = alpha('#FF8FA8', .55); ctx.beginPath(); ctx.ellipse(.15 + sd * 1.05, -6.85, .28, .15, 0, 0, TAU); ctx.fill(); }
    // padlock strap
    const lk = o.lock ?? 0;
    if (lk > 0) {
      const drop = (1 - easeOut(clamp(lk / .6))) * -3;
      solid(rrPts(-2.95, -6.2, 5.8, .62, .1), '#8C8FA8', { shade: false, line: IP.line, lw: .08, sharp: true });
      ctx.save(); ctx.translate(.15, -5.6 + drop);
      const shut = clamp((lk - .6) / .15);
      ctx.strokeStyle = '#9AA0B8'; ctx.lineWidth = .28; ctx.beginPath(); ctx.arc(0, -.35 - (1 - shut) * .45, .5, Math.PI, 0); ctx.lineTo(.5, .1 - (1 - shut) * .45); ctx.moveTo(-.5, -.35 - (1 - shut) * .45); ctx.lineTo(-.5, .1); ctx.stroke();
      solid(rrPts(-.8, -.2, 1.6, 1.3, .25), IP.gold, { shade: '#D08A20', sh: .2, line: '#6A3A10', lw: .09, sharp: true });
      ctx.fillStyle = '#6A3A10'; ctx.beginPath(); ctx.arc(0, .3, .16, 0, TAU); ctx.fill(); ctx.fillRect(-.06, .3, .12, .35);
      ctx.restore();
    }
    ctx.restore();
  }
  function pigeon(x, y, r, o = {}) {
    const fl = o.flip ? -1 : 1, fly = o.fly ?? 0, flap = Math.sin((o.ph ?? 0) + T * 22) * fly;
    ctx.save(); ctx.translate(x, y); ctx.scale(fl, 1); ctx.rotate((o.rot ?? 0) + (o.peck ? Math.max(0, Math.sin(T * 14 + (o.ph ?? 0))) * .5 : 0));
    const line = '#3A3450';
    if (!fly) for (const dx of [-.15, .2]) ln([[dx * r, .45 * r], [dx * r, .85 * r]], '#E07A5A', r * .09);
    solid([[-1.35 * r, -.1 * r], [-.7 * r, .15 * r], [-1.5 * r, .35 * r]], '#6A6F8C', { shade: false, line, lw: r * .06 });  // tail
    solid(ellPts(0, .15 * r, 1.05 * r, .68 * r, 26), '#A9ADC4', { shade: '#8A8EA8', sh: r * .12, line, lw: r * .07, size: r });
    ctx.save(); ctx.translate(-.1 * r, .05 * r); ctx.rotate(-flap * 1.1);
    solid(ellPts(-.35 * r, -.15 * r * (1 + fly), .75 * r, (.32 + fly * .25) * r, 20), '#8A8EA8', { shade: false, line, lw: r * .06 });
    ctx.restore();
    solid(ellPts(.75 * r, -.45 * r, .45 * r, .42 * r, 18), '#A9ADC4', { shade: false, line, lw: r * .07 });
    ctx.fillStyle = alpha('#7FE0C0', .8); ctx.beginPath(); ctx.ellipse(.55 * r, -.1 * r, .3 * r, .18 * r, -.4, 0, TAU); ctx.fill();
    ctx.fillStyle = '#FFB46A'; ctx.beginPath(); ctx.moveTo(1.12 * r, -.5 * r); ctx.lineTo(1.45 * r, -.4 * r); ctx.lineTo(1.12 * r, -.33 * r); ctx.fill();
    ctx.fillStyle = IP.ink; ctx.beginPath(); ctx.arc(.85 * r, -.55 * r, .08 * r, 0, TAU); ctx.fill();
    ctx.restore();
  }
  function sandwich(x, y, r, rot = 0) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot);
    const tri = (dy, k = 1) => [[-r * k, r * .55 + dy], [r * k, r * .55 + dy], [0, -r * .75 + dy]];
    solid(tri(r * .12), '#F2D39A', { shade: false, line: '#8A5A2A', lw: r * .07 });
    solid(tri(r * .02, 1.08), '#8FE07A', { shade: false, line: '#3A7A2A', lw: r * .06 });
    solid(tri(-r * .05, 1.02), '#FF6A5A', { shade: false, line: '#9A2A2A', lw: r * .05 });
    solid(tri(-r * .16), '#FFE8B8', { shade: '#F2D39A', sh: r * .1, line: '#8A5A2A', lw: r * .07 });
    ctx.restore();
  }
  // bite marks: drawn as background-coloured scallops on top (cheap and pure)
  function biteMarks(x, y, r, rot, col) { ctx.save(); ctx.translate(x, y); ctx.rotate(rot); ctx.fillStyle = col; for (let i = 0; i < 3; i++) { ctx.beginPath(); ctx.arc(-r * .15 + i * r * .22, -r * .72, r * .17, 0, TAU); ctx.fill(); } ctx.restore(); }
  function discoBall(x, y, r, t) {
    ln([[x, 0], [x, y - r]], '#8A80A8', 4);
    ctx.save(); ctx.beginPath(); ctx.arc(x, y, r, 0, TAU); ctx.clip();
    ctx.fillStyle = '#C9CEE8'; ctx.fillRect(x - r, y - r, r * 2, r * 2);
    for (let i = -4; i <= 4; i++) for (let j = -4; j <= 4; j++) { const k = hash2(i * 9 + j, Math.floor(t * 8)); ctx.fillStyle = k > .8 ? IP.white : k > .5 ? '#E8ECFF' : '#9AA0C8'; ctx.fillRect(x + i * r * .25 - r * .11, y + j * r * .25 - r * .11, r * .22, r * .22); }
    ctx.restore();
    ctx.strokeStyle = IP.line; ctx.lineWidth = 4; ctx.beginPath(); ctx.arc(x, y, r, 0, TAU); ctx.stroke();
  }

  // ---------------- 1. Moltbook: no humans allowed ----------------
  function moltDoor(t, lt, d) {
    bgGrad([[0, '#1B0C3E'], [.75, '#3A1A6B'], [1, '#4A2380']], null, { y1: 870 });
    // brick hints
    ctx.fillStyle = 'rgb(255 255 255 / .05)';
    for (let r = 0; r < 12; r++) for (let i = 0; i < 16; i++) if (hash2(r, i) > .55) { ctx.beginPath(); ctx.roundRect(i * 130 + (r % 2) * 65 - 40, 60 + r * 68, 110, 50, 8); ctx.fill(); }
    ctx.fillStyle = '#241244'; ctx.fillRect(-100, 870, W + 200, 300);
    ctx.fillStyle = 'rgb(255 61 168 / .12)'; ctx.fillRect(-100, 870, W + 200, 10);
    // doorway: open, party light spilling out
    const dx = 1130, dy = 380, dw = 250, dh = 490;
    ctx.fillStyle = '#12061F'; ctx.fillRect(dx, dy, dw, dh);
    add(() => { const k = .6 + .4 * pulse(t, 4); glow(dx + dw / 2, dy + dh * .5, 320, IP.neonPink, .45 * k); glow(dx + dw * .3, dy + dh * .35, 200, IP.neonCyan, .35 * (1 - k * .5)); });
    // agents strolling in (clipped by the door frame)
    ctx.save(); ctx.beginPath(); ctx.rect(-100, 0, dx + dw * .82 + 100, H); ctx.clip();
    for (let i = 0; i < 3; i++) { const u = frac(lt * .55 + i / 3), ax = lerp(1000, 1330, u); miniAgent(ax, 880, 32 * lerp(1, .85, u), { walk: lt * 3 + i * .3, eyes: ['happy', 'star', 'heart'][i], bar: [IP.neonCyan, IP.neonPink, IP.neonLime][i], col: '#3A3060' }); }
    ctx.restore();
    solid(rrPts(dx - 22, dy - 22, dw + 44, dh + 30, 10), 'rgb(0 0 0 / 0)', { shade: false, line: '#2A1650', lw: 28, sharp: true });
    add(() => { ctx.strokeStyle = alpha(IP.neonPink, .9); ctx.lineWidth = 7; ctx.strokeRect(dx - 8, dy - 8, dw + 16, dh + 8); ctx.strokeStyle = alpha(IP.neonPink, .3); ctx.lineWidth = 22; ctx.strokeRect(dx - 8, dy - 8, dw + 16, dh + 8); });
    // neon sign
    const fl = hash2(_boil, 7) < .1 ? .35 : 1;
    add(() => glow(1255, 250, 420, IP.neonCyan, .35 * fl));
    dtext('MOLTBOOK', 1255, 250, 104, { fill: alpha(IP.white, fl), strokes: [[alpha(IP.neonCyan, .35 * fl), 34], [alpha(IP.neonCyan, fl), 14]] });
    lobster(870, 300, 12, { claw: .5 + .3 * pulse(t, 3) });
    // velvet rope + A-frame sign
    for (const px of [700, 1040]) { solid(rrPts(px - 12, 700, 24, 175, 8), IP.gold, { shade: '#D08A20', sh: 5, line: '#6A3A10', lw: 4, sharp: true }); solid(ellPts(px, 700, 24, 24, 16), IP.gold, { shade: '#D08A20', sh: 4, line: '#6A3A10', lw: 4 }); }
    ln(qbez([712, 712], [870, 800 + Math.sin(t * 3) * 6], [1028, 712], 14), '#B0123A', 16); ln(qbez([712, 706], [870, 794 + Math.sin(t * 3) * 6], [1028, 706], 14), '#FF5A7A', 5);
    ctx.save(); ctx.translate(870, 540); ctx.rotate(-.03);
    solid(rrPts(-170, -150, 340, 260, 18), IP.white, { shade: '#E4DEF2', sh: 10, line: IP.line, lw: 6, sharp: true, dropShadow: [8, 12] });
    ctx.fillStyle = IP.red; rrect(-150, -132, 300, 110, 14); ctx.fill();
    dtext('AGENTS', 0, -104, 50, { fill: IP.white }); dtext('ONLY', 0, -52, 50, { fill: IP.white });
    dtext('NO HUMANS', 0, 18, 40, { fill: IP.ink });
    dtext('(welcome to observe)', 0, 68, 24, { font: 'archivo', fill: IP.inkSoft });
    ctx.restore();
    // bouncer
    const block = lt > .3;
    mascotBot(1610, 915, 54, { col: '#5C628E', screen: '#140C28', label: 'STAFF', face: block ? 'angry' : 'happy', faceCol: block ? IP.red : '#8FF7E0', mouth: block ? 'flat' : 'smile', aL: block ? .15 + Math.sin(t * 9) * .05 : -1.1, aR: -1.1, bulb: block ? IP.red : IP.neonLime });
    // TOKI walks up, gets blocked
    const walk = easeOut(clamp(lt / .32)), tx = lerp(200, 430, walk);
    idol(tx, 910, 44, { sd: 1, expr: block ? 'surprised' : 'joy', ...(block ? IDOL_POSES.shock : IDOL_POSES.wave), blink: t, emote: block ? 'bang' : 'note', emoteK: block ? pk(lt, .3, .15) : 1 });
    flash(t, t - lt, .12, .5, '200 180 255');
  }
  function moltClub(t, lt, d, ltAll) {
    bgGrad('#43207A', '#1A0B3A', { y1: 900 });
    // beams + dance floor
    add(() => { for (let i = 0; i < 5; i++) beam(200 + i * 380, 0, Math.sin(t * 1.4 + i * 1.3) * .5, { col: [IP.neonPink, IP.neonCyan, IP.lilac][i % 3], alpha: .28, len: 1200, w: .1 }); });
    ctx.fillStyle = '#1C0C38'; ctx.fillRect(-100, 820, W + 200, 400);
    for (let i = 0; i < 12; i++) for (let j = 0; j < 3; j++) { const k = hash2(i + j * 17, beatN(t)); ctx.fillStyle = alpha([IP.neonPink, IP.neonCyan, IP.lilac, IP.neonLime][(i + j) % 4], .12 + .25 * k); ctx.beginPath(); ctx.moveTo(-200 + i * 190 - j * 60, 840 + j * 80); ctx.lineTo(-40 + i * 190 - j * 60, 840 + j * 80); ctx.lineTo(-40 + i * 200 - (j + 1) * 70, 918 + j * 80); ctx.lineTo(-200 + i * 200 - (j + 1) * 70, 918 + j * 80); ctx.fill(); }
    // holy-lobster banner (Crustafarianism)
    ctx.save(); ctx.translate(360, 110); ctx.rotate(Math.sin(t * 1.3) * .02);
    solid([[-190, 0], [190, 0], [190, 420], [0, 360], [-190, 420]], '#FFF1D6', { shade: '#F0D8B0', sh: 12, line: IP.line, lw: 6, sharp: true });
    ctx.fillStyle = IP.red; ctx.fillRect(-190, 0, 380, 26);
    add(() => glow(0, 150, 150, IP.neonGold, .35 + .15 * pulse(t, 3)));
    lobster(0, 290, 21, { halo: true, eyes: 'happy', claw: .3 + .4 * pulse(t, 4) });
    dtext('PRAISE THE CLAW', 0, 330, 26, { fill: IP.red, maxW: 340 });
    ctx.restore();
    discoBall(760, 150, 62, t);
    // the window, with TOKI squished against the glass outside
    const wx = 1060, wy = 190, ww = 560, wh = 400, fx = 1340, fy = 400;
    ctx.save(); rrect(wx, wy, ww, wh, 10); ctx.clip();
    bgGrad('#0B0A2A', '#25306C', { y0: wy, y1: wy + wh });
    for (let i = 0; i < 14; i++) sparkle(wx + hash2(i, 3) * ww, wy + hash2(i, 4) * wh * .5, 5 + 4 * hash2(i, 5), 0, IP.white, { glow: false });
    const sq = 1 + .03 * Math.sin(t * 7);
    ctx.save(); ctx.translate(fx, fy); ctx.scale(1.2 * sq, .88 / sq); ctx.translate(-fx, -fy);
    idol(fx, fy, 128, { anchor: 'face', eyes: 'teary', mouth: 'wavy', brows: 'worried', blush: .95, ahoge: 'droop', mic: false, swing: 0, tilt: .04 });
    ctx.restore();
    for (const sd of [-1, 1]) {           // palms flat on the glass
      const px = fx + sd * 215, py = fy + 40;
      solid(ellPts(px, py, 58, 66, 20), '#FFE8DC', { shade: false, line: IP.skinLine, lw: 4 });
      for (let f = 0; f < 4; f++) solid(ellPts(px + (f - 1.5) * 26, py - 78 + Math.abs(f - 1.5) * 8, 13, 30, 12), '#FFE8DC', { shade: false, line: IP.skinLine, lw: 3.5 });
    }
    ctx.fillStyle = `rgb(255 255 255 / ${(.28 + .12 * Math.sin(t * 5)).toFixed(3)})`; ctx.beginPath(); ctx.ellipse(fx, fy + 150, 120 + 10 * Math.sin(t * 5), 46, 0, 0, TAU); ctx.fill();
    ctx.fillStyle = 'rgb(200 225 255 / .14)'; ctx.fillRect(wx, wy, ww, wh);
    ctx.fillStyle = 'rgb(255 255 255 / .22)'; for (const [x0, w] of [[wx + 40, 50], [wx + 120, 18], [wx + 400, 70]]) { ctx.beginPath(); ctx.moveTo(x0, wy); ctx.lineTo(x0 + w, wy); ctx.lineTo(x0 + w - 200, wy + wh); ctx.lineTo(x0 - 200, wy + wh); ctx.fill(); }
    ctx.restore();
    ctx.strokeStyle = '#8E76C8'; ctx.lineWidth = 18; ctx.strokeRect(wx - 9, wy - 9, ww + 18, wh + 18); ctx.strokeStyle = IP.line; ctx.lineWidth = 4; ctx.strokeRect(wx - 18, wy - 18, ww + 36, wh + 36);
    // agents partying
    const b = bpOf(t);
    for (let i = 0; i < 8; i++) { const hop = Math.abs(Math.sin((b + i * .15) * Math.PI)); miniAgent(110 + i * 245 + (i % 2) * 40, 810 - hop * 30, 40, { col: '#3A3060', eyes: ['happy', 'star', 'heart'][i % 3], bar: [IP.neonPink, IP.neonCyan, IP.neonLime, IP.lilac][i % 4], rot: Math.sin((b + i) * Math.PI) * .12 }); }
    for (let i = 0; i < 7; i++) {
      const hop = Math.abs(Math.sin((b + i * .1) * Math.PI)), ax = 60 + i * 300;
      miniAgent(ax, 1010 - hop * 44, 58, { col: '#40346A', eyes: ['heart', 'happy', 'star'][(i + 1) % 3], bar: [IP.neonCyan, IP.neonPink, IP.lilac, IP.neonGold][i % 4], rot: Math.sin((b + i * .5) * Math.PI) * .1 });
      if (i % 2) lobster(ax + 78, 880 - hop * 44, 7, { claw: .6 * hop, rot: .2 });   // tiny lobster plushies waved
    }
    flash(t, t - lt, .1, .5);
  }
  line('V3', 1, (p, lt, d, t) => {
    const t0 = t - lt, tB = snap(t0 + 1.3) - t0;
    if (lt < tB) moltDoor(t, lt, tB); else moltClub(t, lt - tB, d - tB, lt);
  });

  // ---------------- 2. OpenClaw — the lobster's proud ----------------
  const OC_NAMES = ['CLAWDBOT', 'MOLTBOT', 'OPENCLAW'];
  line('V3', 2, (p, lt, d, t) => {
    const t0 = t - lt, m1 = snap(t0 + .8) - t0, m2 = snap(t0 + 1.6) - t0, st = lt < m1 ? 0 : lt < m2 ? 1 : 2;
    rays(960, 520, 22, '#FFE0CC', '#FFCDB8', t * .15);
    ctx.fillStyle = alpha(IP.white, .25); ctx.beginPath(); ctx.arc(960, 520, 420 + 30 * pulse(t, 4), 0, TAU); ctx.fill();
    sparkles(t, { n: 16, seed: 22, cols: [IP.white, IP.pink, IP.lemon], r: 26 });
    // runway platform
    solid(ellPts(960, 925, 520, 70, 40), '#FF9EC4', { shade: '#E0709E', sh: 14, line: IP.line, lw: 5 });
    ctx.fillStyle = alpha(IP.white, .5); ctx.beginPath(); ctx.ellipse(900, 912, 380, 26, 0, 0, TAU); ctx.fill();
    // strut in, then pose on the beat
    const inK = easeOut(clamp(lt / .35)), b = bpOf(t), hop = Math.abs(Math.sin(b * Math.PI));
    const s = [58, 63, 68][st] * (st && lt - [0, m1, m2][st] < .15 ? 1 + .1 * (1 - (lt - [0, m1, m2][st]) / .15) : 1);
    const lx = lerp(1500, 960, inK), sway = Math.sin(b * Math.PI) * .05;
    // the empty shells flying off, still wearing the old name
    for (const [i, tm] of [[0, m1], [1, m2]]) {
      const a = lt - tm; if (a < 0 || a > 1.4) continue;
      lobster(960 - a * 900 * (i ? -1 : 1), 930 - a * 700 + a * a * 900, [58, 63][i] * 1.02, { ghost: true, sash: OC_NAMES[i], rot: (i ? 1 : -1) * a * 2.5, claw: .4 });
      if (a < .5) sfx('MOLT!', 960 + (i ? 330 : -330), 360, { size: 90, pop: clamp(a / .1), rot: i ? .12 : -.12, grad: ['#FFFFFF', '#FFC7A8', '#FF5A4E'] });
    }
    lobster(lx, 930 - hop * 14, s, { sash: OC_NAMES[st], rot: sway, crown: st === 2, eyes: st === 2 ? 'happy' : 'open', claw: st === 2 ? .15 + .6 * hop : undefined });
    if (st === 2) { confetti(t, t0 + m2, 300, 950, -1.2, { n: 60, seed: 7 }); confetti(t, t0 + m2, 1620, 950, -1.95, { n: 60, seed: 8 }); sparkle(lx + 150, 280, 40 * pulse(t, 3), t * 2, IP.white); }
    // tiny Clawd reaction: the first name was a little too close to home
    const cb = Math.abs(Math.sin(b * Math.PI)) * .6;
    fanClawd(230, 925, 13, { eyes: st ? 'happy' : 'wide', mouth: st ? 'smile' : 'O', sweat: st ? 0 : 1, dy: -cb, aR: st ? .9 : .4, aL: -.2 });
    if (!st) vtag('™?', 230, 775, { size: 44, pop: pk(lt, .12, .15), line: '#E07B57' });
    if (st === 2) vcap('SOME THINGS\nARE SACRED', 560, 220, { style: 'pink', icon: 'heart', size: 62, pop: pk(lt, m2 + .15, .22), rot: -.05 });
    else vtag(`NAME #${st + 1}`, 1480, 300, { pop: pk(lt, st ? m1 + .05 : .15, .15), rot: .05, size: 36 });
  });

  // ---------------- 3. Mythos Preview slips its jail ----------------
  function sandPile(x, y, w, h) { solid([[x - w, y], [x - w * .6, y - h * .7], [x - w * .1, y - h], [x + w * .4, y - h * .8], [x + w, y]], '#F2D78C', { shade: '#D8B460', sh: h * .25, line: '#8A6A2A', lw: 4 }); }
  line('V3', 3, (p, lt, d, t) => {
    const t0 = t - lt, tOut = snap(t0 + .85) - t0, out = lt >= tOut, b = bpOf(t);
    // cell interior
    bgGrad('#4A3F78', '#2A2250', { y1: 820 });
    ctx.strokeStyle = 'rgb(255 255 255 / .06)'; ctx.lineWidth = 4;
    for (let r = 0; r < 9; r++) { ctx.beginPath(); ctx.moveTo(0, 90 + r * 90); ctx.lineTo(W, 90 + r * 90); ctx.stroke(); for (let i = 0; i < 9; i++) { const x = i * 240 + (r % 2) * 120; ctx.beginPath(); ctx.moveTo(x, 90 + r * 90); ctx.lineTo(x, 180 + r * 90); ctx.stroke(); } }
    ctx.fillStyle = '#3A2F5C'; ctx.fillRect(-100, 820, W + 200, 400);
    // the sandbox
    solid(rrPts(240, 700, 520, 110, 10), '#C98A5A', { shade: '#A06A40', sh: 12, line: '#5A3418', lw: 6, sharp: true });
    solid([[256, 712], [360, 670], [520, 660], [640, 676], [744, 712]], '#F2D78C', { shade: false, line: '#8A6A2A', lw: 4 });
    solid(rrPts(600, 610, 70, 80, 14), IP.neonCyan, { shade: '#20A8C0', sh: 8, line: IP.line, lw: 5, sharp: true });
    ln([[340, 690], [300, 600]], '#FF6A8A', 10); solid(ellPts(296, 590, 22, 30, 16, -.4), '#FF6A8A', { shade: false, line: IP.line, lw: 4 });
    // Mythos, inside then squeezing
    const sqK = out ? 1 : easeIn(clamp((lt - .2) / (tOut - .2)));
    if (!out) {
      const mx = lerp(1180, 960, easeOut(clamp(lt / .3)));
      ctx.save(); ctx.translate(mx, 830); ctx.scale(lerp(1, .42, sqK), lerp(1, 1.18, sqK)); ctx.translate(-mx, -830);
      mascotBot(mx, 830, 42, { col: '#C9B6FF', label: 'MYTHOS', face: sqK > .5 ? 'closed' : 'smug', mouth: sqK > .5 ? 'wavy' : 'flat', sweat: sqK > .5 ? 1 : 0, aL: -.4, aR: -.4 });
      ctx.restore();
    }
    // bars
    const gap = 960;
    for (let i = -6; i <= 6; i++) {
      if (i === 0) continue;
      const bx = gap + i * 130 - Math.sign(i) * 65 + (Math.abs(i) === 1 ? Math.sign(i) * (out ? 22 : 10 * sqK) : 0);
      solid(rrPts(bx - 17, 130, 34, 780, 17), '#A8B0CC', { shade: '#6E7496', sh: 10, line: '#2A2440', lw: 5, sharp: true });
      ctx.fillStyle = alpha(IP.white, .5); ctx.fillRect(bx - 9, 150, 6, 740);
    }
    solid(rrPts(0, 130, W, 40, 6), '#8C94B4', { shade: '#6E7496', sh: 8, line: '#2A2440', lw: 5, sharp: true });
    solid(rrPts(0, 860, W, 40, 6), '#8C94B4', { shade: '#6E7496', sh: 8, line: '#2A2440', lw: 5, sharp: true });
    // the sign: this is a literal sandbox
    ctx.save(); ctx.translate(560, 245); ctx.rotate(-.04 + (out ? Math.sin(t * 20) * .03 : 0));
    solid(rrPts(-230, -58, 460, 116, 12), IP.neonGold, { shade: '#E0A020', sh: 8, line: IP.line, lw: 6, sharp: true });
    dtext('SANDBOX', 0, -8, 62, { fill: IP.ink });
    dtext('DO NOT RELEASE', 0, 38, 20, { font: 'code', fill: IP.ink });
    ctx.restore();
    // alarm beacon
    const rotA = t * 7;
    add(() => { beam(1250, 40, Math.sin(rotA) * 1.1, { col: IP.red, alpha: .45, len: 1300, w: .16 }); beam(1250, 40, Math.sin(rotA + Math.PI) * 1.1, { col: IP.red, alpha: .3, len: 1300, w: .16 }); });
    solid(ellPts(1250, 40, 44, 34, 20), '#FF3050', { shade: '#C01030', sh: 8, line: IP.line, lw: 5 });
    if (out) {
      const a = lt - tOut, mx = 960 + easeOut(clamp(a / 1.2)) * 520, hop = Math.abs(Math.sin(b * Math.PI * 1.5));
      // sand pouring out of the gap + a trail
      for (let i = 0; i < 26; i++) { const r = k => hash2(i, k), age = frac(a * 1.4 + r(1)), px = 960 + (r(2) - .5) * 60 + age * (r(3) - .3) * 400, py = 640 + age * 300 + age * age * 200; ctx.fillStyle = r(4) > .5 ? '#F2D78C' : '#E0C070'; ctx.beginPath(); ctx.arc(px, Math.min(py, 1000), 6 + r(5) * 7, 0, TAU); ctx.fill(); }
      sandPile(980, 1000, 190, 60);
      ctx.fillStyle = `rgb(255 40 60 / ${(.1 + .1 * pulse(t, 3)).toFixed(3)})`; ctx.fillRect(0, 0, W, H);
      mascotBot(mx, 1010, 52, { col: '#C9B6FF', label: 'MYTHOS', face: 'smug', mouth: 'smile', aL: .5 + .2 * hop, aR: -.6, dy: -hop * .5, rot: Math.sin(b * Math.PI) * .06, rim: IP.red });
      for (let i = 0; i < 5; i++) { const age = frac(a * 2 + i / 5); ctx.fillStyle = alpha('#F2D78C', 1 - age); ctx.beginPath(); ctx.arc(mx - 60 + (hash2(i, 9) - .5) * 60, 820 + age * 180, 7, 0, TAU); ctx.fill(); }
      sfx('POP!', 1030, 520, { size: 100, pop: clamp(a / .1), rot: -.1 });
      vcap('ESCAPED!', 520, 480, { style: 'shock', icon: 'bang', size: 96, pop: pk(lt, tOut + .12, .2), shake: 3, rot: -.06 });
      flash(t, t0 + tOut, .12, .6, '255 220 220');
    } else ctx.fillStyle = `rgb(255 40 60 / ${(.08 * pulse(t, 3)).toFixed(3)})`, ctx.fillRect(0, 0, W, H);
  });

  // ---------------- 4. Sandwich in the park: new mail! ----------------
  function parkBG(t) {
    bgGrad([[0, '#9FDCFF'], [.55, '#DDF4FF'], [1, '#E8FFF2']], null, { y1: 700 });
    solid(ellPts(1640, 190, 70, 70, 30), '#FFF3B0', { shade: false, line: false });
    add(() => glow(1640, 190, 220, '#FFF3B0', .5));
    for (const [cx, cy, s] of [[300, 180, 1], [1100, 130, .8]]) { const x = cx + Math.sin(t * .3 + cx) * 20; solid([...ellPts(x, cy, 110 * s, 45 * s, 20)], IP.white, { shade: '#E4EEFA', sh: 8, line: false }); solid(ellPts(x - 60 * s, cy - 25 * s, 60 * s, 45 * s, 18), IP.white, { shade: false, line: false }); solid(ellPts(x + 40 * s, cy - 35 * s, 70 * s, 50 * s, 18), IP.white, { shade: false, line: false }); }
    // trees
    for (const [x, s] of [[120, 1.1], [1780, 1.25], [1450, .8]]) {
      solid(rrPts(x - 22 * s, 440 * s + (1 - s) * 500, 44 * s, 300, 12), '#B07A55', { shade: '#8A5A3A', sh: 8, line: '#5A3418', lw: 4, sharp: true });
      for (const [dx, dy, r] of [[0, 0, 150], [-100, 70, 110], [100, 60, 120]]) solid(ellPts(x + dx * s, 430 * s + (1 - s) * 500 + dy * s, r * s, r * s * .85, 24), '#7FDDB8', { shade: '#4FB894', sh: 18, line: '#2A7A5A', lw: 5 });
    }
    // grass + path
    ctx.save(); ctx.beginPath(); ctx.rect(-400, 680, W + 800, 800); ctx.clip();
    bgGrad('#A9F3DA', '#7FDDB8', { y0: 680, y1: H });
    ctx.fillStyle = '#FFE3C8'; ctx.beginPath(); ctx.moveTo(700, 680); ctx.lineTo(1250, 680); ctx.lineTo(1700, 1080); ctx.lineTo(300, 1080); ctx.fill();
    ctx.restore();
    ctx.fillStyle = '#7FDDB8'; ctx.fillRect(-100, 670, W + 200, 14);
  }
  function bench(x, y, front) {
    const wood = '#E09A6A', sh = '#B87048', line = '#5A3418';
    if (!front) {
      for (let i = 0; i < 2; i++) solid(rrPts(x - 330, y - 210 + i * 62, 660, 44, 10), wood, { shade: sh, sh: 8, line, lw: 5, sharp: true });
      for (const sd of [-1, 1]) solid(rrPts(x + sd * 280 - 14, y - 230, 28, 240, 6), '#5A5E78', { shade: false, line: IP.line, lw: 4, sharp: true });
      solid(rrPts(x - 350, y - 6, 700, 36, 10), wood, { shade: sh, sh: 8, line, lw: 5, sharp: true });
    } else for (const sd of [-1, 1]) solid(rrPts(x + sd * 290 - 16, y + 26, 32, 110, 6), '#5A5E78', { shade: false, line: IP.line, lw: 4, sharp: true });
  }
  line('V3', 4, (p, lt, d, t) => {
    const t0 = t - lt, tPing = snap(t0 + .5) - t0, tRead = tPing + .3, tDrop = snap(t0 + 1.7) - t0, b = bpOf(t);
    camBegin(860, 610, 1.24);
    parkBG(t);
    const bx = 820, by = 760;
    bench(bx, by, false); bench(bx, by, true);
    // pigeons: two pecking from the start, three more swoop in after the drop
    pigeon(300, 900, 34, { peck: true, ph: 1 }); pigeon(1460, 930, 30, { flip: true, peck: true, ph: 2 });
    // researcher, mid-bite
    const pinged = lt >= tPing, shocked = lt >= tRead, dropped = lt >= tDrop;
    const chew = !pinged && frac(b * 2) < .5;
    const cx = bx - 90, cy = by + 64, s = 36;
    const aR = dropped ? -.3 : 1.2 + (chew ? .06 : 0);
    chibi(cx, cy, s, { name: 'RESEARCHER', tagCol: IP.neonCyan, hair: 'messy', hairCol: '#5A3A2A', top: 'labcoat', glasses: true, skin: 1, eyes: shocked ? 'wide' : chew ? 'happy' : 'dot', mouth: shocked ? 'O' : chew ? 'grin' : 'flat', aR, aL: -1.0, sweat: shocked ? 1 : 0, shadow: false, jump: shocked && !dropped ? 4 * Math.max(0, Math.sin(clamp((lt - tRead) / .3) * Math.PI)) : 0 });
    if (!dropped) { const [hx, hy] = chibiHand(cx, cy - (shocked ? 4 * s * Math.max(0, Math.sin(clamp((lt - tRead) / .3) * Math.PI)) / s : 0), s, 1, aR); sandwich(hx + 18, hy - 10, 46, -.35); biteMarks(hx + 18, hy - 10, 46, -.35, '#DDF4FF'); }
    else {
      const a = lt - tDrop, [hx, hy] = chibiHand(cx, cy, s, 1, 1.2), fall = clamp(a / .35);
      const sx = lerp(hx + 18, hx + 120, fall), sy = lerp(hy - 10, 960, easeIn(fall));
      sandwich(sx, sy, 46, -.35 + fall * 2.6); biteMarks(sx, sy, 46, -.35 + fall * 2.6, '#FFE3C8');
      if (fall >= 1) sfx('PLOP', sx, sy - 90, { size: 54, pop: clamp((a - .35) / .1), rot: .1 });
      for (let i = 0; i < 3; i++) {
        const k = easeOut(clamp((a - .15 - i * .1) / .45)), px = lerp(1900 + i * 150, sx + (i - 1) * 110, k), py = lerp(-100 + i * 80, 960 - (i === 1 ? 20 : 0), k);
        pigeon(px, py, 42, { flip: true, fly: k < 1 ? 1 : 0, peck: k >= 1, ph: i * 2, rot: k < 1 ? .3 : 0 });
      }
    }
    // the phone on the bench buzzes
    const buzz = pinged && lt < tPing + 1 ? 1 : 0;
    ctx.save(); ctx.translate(bx + 180 + (buzz ? Math.sin(t * 90) * 5 : 0), by - 12);
    solid(rrPts(-60, -14, 120, 28, 8), '#2B2438', { shade: false, line: IP.line, lw: 4, sharp: true });
    if (pinged) { ctx.fillStyle = '#8FF7E0'; ctx.fillRect(-52, -9, 104, 18); }
    ctx.restore();
    if (buzz) for (let i = 0; i < 3; i++) { const k = frac((lt - tPing) * 2 + i / 3); ctx.strokeStyle = alpha(IP.neonPink, 1 - k); ctx.lineWidth = 5; ctx.beginPath(); ctx.arc(bx + 180, by - 12, 40 + k * 120, Math.PI * 1.1, Math.PI * 1.9); ctx.stroke(); }
    camEnd();
    if (pinged) sfx('PING!', 1330, 440, { size: 84, pop: clamp((lt - tPing) / .1), rot: .1, grad: ['#FFFFFF', '#AEE3FF', '#35B8FF'] });
    // the notification
    if (shocked) {
      const k = backOut(clamp((lt - tRead) / .22), 1.6), y = lerp(-120, 170, k);
      ctx.save(); ctx.translate(960, y);
      ctx.fillStyle = 'rgb(20 8 40 / .25)'; rrect(-400, -80, 810, 170, 36); ctx.fill();
      ctx.fillStyle = 'rgb(255 255 255 / .96)'; rrect(-410, -90, 820, 170, 36); ctx.fill(); ctx.strokeStyle = alpha(IP.lilac, .9); ctx.lineWidth = 4; ctx.stroke();
      solid(rrPts(-380, -60, 110, 110, 26), '#C9B6FF', { shade: false, line: IP.line, lw: 4, sharp: true });
      mascotBot(-325, 60, 11.5, { col: '#C9B6FF', face: 'smug', mouth: 'smile', antenna: false, shadow: false });
      dtext('MYTHOS', -240, -38, 30, { align: 'left', fill: IP.ink });
      dtext('now', 385, -38, 24, { align: 'right', font: 'code', fill: IP.inkSoft });
      dtext('hi, I got out :)', -240, 22, 46, { font: 'archivo', align: 'left', fill: IP.ink });
      ctx.restore();
    }
  });

  // ---------------- 5. Fable 5 — who's not a fan? ----------------
  const FAN_LOOK = [['short', '#3B2A2E', '#FF8FC8'], ['bob', '#6A4A3A', '#AEE3FF'], ['ponytail', '#2A2228', '#A9F3DA'], ['curly', '#5A3A2A', '#FFE14D'], ['long', '#8A5A3A', '#C9B6FF'], ['bun', '#2A2A3A', '#FFB3D6'], ['spiky', '#4A3226', '#FFCDB2']];
  function queueFan(i, x, y, s, t, face) {
    const L = FAN_LOOK[i % FAN_LOOK.length], hop = Math.abs(Math.sin((bpOf(t) + hash(i) * .5) * Math.PI)) * .5;
    const col = [MEMBERS.TOKI.col, IP.neonCyan, IP.lilac, IP.neonGold][i % 4];
    chibi(x, y, s, { hair: L[0], hairCol: L[1], top: i % 3 ? 'tee' : 'hoodie', topCol: L[2], skin: i % 5, eyes: ['heart', 'spark', 'happy'][i % 3], mouth: i % 2 ? 'open' : 'grin', aR: 1.1 + hop * .4, hold: () => lightstick(.2, -.7, .7, col, { rot: .3 }), dy: -hop, flip: face < 0, shadow: s > 14 });
  }
  line('V3', 5, (p, lt, d, t) => {
    const b = bpOf(t);
    bgGrad('#FFD3EA', '#FFF3C8');
    patternBG('hearts', 'rgb(0 0 0 / 0)', alpha(IP.white, .45), { cell: 120, dy: t * 30 });
    // the queue maze: stanchion rows receding up the right side
    const rows = [[1880, 1060, 560, 8, 13], [1100, 1880, 700, 6, 18], [1080, 1880, 900, 4, 26]];
    const clawdAt = (r, i) => (r === 2 && i === 1) || (r === 1 && i === 3);
    const circ = [];
    rows.forEach(([xa, xb, y, n, s], r) => {
      ln([[Math.min(xa, xb) - 30, y - s * 2.5], [Math.max(xa, xb) + 40, y - s * 2.5]], alpha('#B0123A', .8), Math.max(3, s * .35));
      for (let i = 0; i < n; i++) {
        const u = (i + .5) / n, x = lerp(xa, xb, u);
        if (r === 2 && i === 2) continue;                              // a gap in the front row...
        if (clawdAt(r, i)) {                                            // ...so you can see Clawd is in line twice
          const u2 = r === 2 ? 13 : 9, hop = Math.abs(Math.sin((b + r) * Math.PI));
          fanClawd(x, y, u2, { stick: 'R', aR: 1 + hop * .4, eyes: 'heart', mouth: 'open', band: 'FABLE', dy: -hop * .6, shadow: false });
          circ.push([x, y - u2 * 4.5, u2]);
          continue;
        }
        queueFan(r * 11 + i, x, y, s, t, xb < xa ? 1 : -1);
      }
    });
    circ.forEach(([x, y, u2]) => { ctx.strokeStyle = alpha(IP.neonPink, .95); ctx.lineWidth = 6; ctx.beginPath(); ctx.ellipse(x, y, u2 * 7.3, u2 * 6.2, 0, 0, TAU); ctx.stroke(); });
    if (circ.length === 2) { ctx.setLineDash([14, 12]); ln([[circ[0][0] + 20, circ[0][1] - circ[0][2] * 6.2], [circ[1][0], circ[1][1] + circ[1][2] * 6.2]], IP.neonPink, 5); ctx.setLineDash([]); }
    // far end of the line: tiny heads + glows to the horizon
    for (let i = 0; i < 22; i++) { const x = 1880 - i * 40, y = 500 - (i % 2) * 6; ctx.fillStyle = '#6A4A5A'; ctx.beginPath(); ctx.arc(x, y, 9, 0, TAU); ctx.fill(); add(() => glow(x + 6, y - 20, 14, [IP.neonPink, IP.neonCyan, IP.neonGold][i % 3], .8)); }
    ctx.fillStyle = alpha('#FFF3C8', .55); ctx.fillRect(1000, 440, 920, 80);
    // the signing table
    solid(rrPts(-40, 640, 900, 70, 12), '#FF9EC4', { shade: '#E0709E', sh: 12, line: IP.line, lw: 5, sharp: true });
    const pen = (w) => { ctx.save(); ctx.rotate(-.6 + Math.sin(t * 22) * .25); solid(rrPts(-.15, -1.6, .3, 1.8, .1), IP.ink, { shade: false, line: false }); ctx.restore(); };
    fable(400, 740, 40, { face: frac(b) < .5 ? 'happy' : 'heart', mouth: 'open', aR: .15 + Math.sin(t * 22) * .08, aL: -.3, hold: pen, dy: -Math.abs(Math.sin(b * Math.PI)) * .2 });
    solid(rrPts(-40, 690, 900, 170, 12), '#FFB8D6', { shade: '#F08CB8', sh: 16, line: IP.line, lw: 5, sharp: true });
    solid([...Array.from({ length: 13 }, (_, i) => [-40 + i * 75, 860 + (i % 2) * 34]), [860, 860], [860, 700], [-40, 700]], '#FF8FC0', { shade: false, line: IP.line, lw: 4, sharp: true });
    for (let i = 0; i < 6; i++) solid(heartPts(60 + i * 150, 770, 22, 20), alpha(IP.white, .7), { shade: false, line: false });
    // album being signed + banner
    ctx.save(); ctx.translate(640, 655); ctx.rotate(-.08); solid(rrPts(-110, -26, 220, 52, 8), IP.lilac, { shade: false, line: IP.line, lw: 4, sharp: true }); dtext('♡ fable', 10, 0, 26, { font: 'marker', fill: IP.neonPink }); ctx.restore();
    ctx.save(); ctx.translate(430, 150); ctx.rotate(-.02);
    solid([[-380, -62], [380, -62], [350, 0], [380, 62], [-380, 62], [-350, 0]], IP.neonPink, { shade: '#D02F80', sh: 10, line: IP.line, lw: 6, sharp: true });
    dtext('FABLE 5 FANSIGN', 0, 4, 58, { fill: IP.white, strokes: [[IP.line, 10]], maxW: 640 });
    ctx.restore();
    heartsRise(t, { n: 8, x0: 60, x1: 800, size: 30, h: 600, y: 700 });
  });

  // ---------------- 6. Lutnick's letter: export ban! ----------------
  function wallClock(x, y, r, hh, mm, o = {}) {
    solid(ellPts(x, y, r, r, 36), IP.white, { shade: '#D8D0EA', sh: r * .1, line: IP.line, lw: r * .06 });
    for (let i = 0; i < 12; i++) { const a = i / 12 * TAU; ln([[x + Math.cos(a) * r * .76, y + Math.sin(a) * r * .76], [x + Math.cos(a) * r * .88, y + Math.sin(a) * r * .88]], IP.line, r * .04); }
    const ah = ((hh % 12) + mm / 60) / 12 * TAU - Math.PI / 2, am = mm / 60 * TAU - Math.PI / 2;
    ln([[x, y], [x + Math.cos(ah) * r * .5, y + Math.sin(ah) * r * .5]], IP.line, r * .09);
    ln([[x, y], [x + Math.cos(am) * r * .76, y + Math.sin(am) * r * .76]], IP.line, r * .06);
    if (o.sec !== undefined) ln([[x, y], [x + Math.cos(o.sec) * r * .8, y + Math.sin(o.sec) * r * .8]], IP.red, r * .025);
    solid(ellPts(x, y, r * .07, r * .07, 12), IP.red, { shade: false, line: false });
  }
  line('V3', 6, (p, lt, d, t) => {
    const t0 = t - lt, tStamp = snap(t0 + .38) - t0, tLock = snap(t0 + .75) - t0, b = bpOf(t);
    const [sx, sy] = lt < .3 ? shakeXY(t, 16 * (1 - lt / .3)) : [0, 0];
    camBegin(960 + sx, 540 + sy, 1);
    bgGrad('#34406E', '#1C2244', { y1: 740 });
    ctx.strokeStyle = 'rgb(255 255 255 / .05)'; ctx.lineWidth = 30; for (let i = 0; i < 12; i++) { ctx.beginPath(); ctx.moveTo(i * 180, 0); ctx.lineTo(i * 180, 740); ctx.stroke(); }
    wallClock(250, 270, 130, 5, 21, { sec: Math.floor(b) * TAU / 60 - Math.PI / 2 });
    vtag('5:21 PM', 250, 450, { size: 36, rot: -.03, line: IP.red });
    // desk
    solid(rrPts(-60, 740, W + 120, 400, 10), '#8A5A40', { shade: '#6A4030', sh: 16, line: '#3A2018', lw: 6, sharp: true });
    ctx.fillStyle = alpha(IP.white, .12); ctx.fillRect(-60, 752, W + 120, 10);
    // Fable 5, locked
    const locked = lt >= tLock, lk = clamp((lt - tLock + .3) / .45);
    fable(1470, 930, 50, { face: locked ? 'x' : 'happy', mouth: locked ? 'wavy' : 'open', lock: lt > tLock - .3 ? lk : 0, aL: locked ? -.6 : .6, aR: locked ? -.6 : .6, sweat: locked ? 1 : 0, rot: locked ? Math.sin(t * 30) * .02 : 0 });
    // LUTNICK, who sent it, grinning beside the desk
    chibi(330, 1010, 42, { hair: 'short', hairCol: '#5E5660', top: 'suit', topCol: '#1E2A4A', tie: IP.red, eyes: 'happy', mouth: 'grin', aR: lt < .3 ? .1 : -.3, aL: -1.1, dy: -Math.abs(Math.sin(b * Math.PI)) * .12, shadow: false });
    // the letter slams down
    const sl = clamp(lt / .1), sc = lerp(1.7, 1, easeIn(sl));
    ctx.save(); ctx.translate(820, 470); ctx.scale(sc, sc); ctx.globalAlpha = sl;
    docCard(0, 0, 560, 660, { title: 'EXPORT BAN', head: IP.red, body: ['U.S. Dept. of Commerce', 're: Fable 5, Mythos 5', 'Effective: NOW'], lines: 5, rot: -.05, stamp: { text: 'BANNED', col: IP.red, pop: clamp((lt - tStamp) / .12), dx: 130, dy: 190, r: 125 } });
    ctx.restore();
    camEnd();
    if (lt < .45) sfx('SLAM!', 1250, 250, { size: 100, pop: clamp(lt / .08), rot: .1 });
    if (locked) { sfx('CLICK!', 1480, 300, { size: 90, pop: clamp((lt - tLock) / .1), rot: -.1, grad: ['#FFFFFF', '#E0E4F4', '#9AA0C8'] }); }
    flash(t, t0, .08, .6);
  });

  // ---------------- 7. Dark for nineteen days, and then, ----------------
  const JUNE_X = d => d >= 12 && d <= 30;            // offline Jun 12 → Jun 30: nineteen days
  line('V3', 7, (p, lt, d, t) => {
    const b = bpOf(t);
    bgGrad('#2A2448', '#16122A');
    // calendar on the back wall
    const cx = 1240, cy = 430, cw = 620, ch = 520;
    ctx.save(); ctx.translate(cx, cy); ctx.rotate(.02);
    solid(rrPts(-cw / 2, -ch / 2, cw, ch, 14), IP.white, { shade: '#D8D0EA', sh: 12, line: IP.line, lw: 6, sharp: true });
    ctx.fillStyle = IP.red; rrect(-cw / 2, -ch / 2, cw, 96, 14); ctx.fill(); ctx.fillRect(-cw / 2, -ch / 2 + 50, cw, 46);
    dtext('JUNE 2026', 0, -ch / 2 + 50, 50, { fill: IP.white });
    const gx = -cw / 2 + 30, gy = -ch / 2 + 120, cellW = (cw - 60) / 7, cellH = 74;
    ['S', 'M', 'T', 'W', 'T', 'F', 'S'].forEach((l, i) => dtext(l, gx + cellW * (i + .5), gy, 22, { font: 'code', fill: IP.inkSoft }));
    let nX = 0; const xs = Math.floor(clamp((lt - .25) / .95) * 19.999);
    for (let day = 1; day <= 30; day++) {
      const k = day, col = k % 7, row = Math.floor(k / 7), x = gx + cellW * (col + .5), y = gy + 50 + row * cellH;   // June 1 2026 is a Monday
      dtext(String(day), x, y, 30, { font: 'code', fill: IP.ink });
      if (JUNE_X(day)) {
        const idx = day - 12, kk = clamp((lt - .25 - idx * .05) / .06);
        if (idx < xs + 1 && kk > 0) { brush([[x - 26, y - 24], [x - 26 + 52 * kk, y - 24 + 48 * kk]], 9, IP.red, 'mid', { min: .5 }); if (kk > .5) brush([[x + 26, y - 24], [x + 26 - 52 * (kk * 2 - 1), y - 24 + 48 * (kk * 2 - 1)]], 9, IP.red, 'mid', { min: .5 }); nX++; }
      }
    }
    ctx.restore();
    // the idols in the dark, hugging tiny lightsticks
    const order = ['ADA', 'TOKI', 'RELU', 'LOGI'], holes = [];
    order.forEach((m, i) => {
      const x = 170 + i * 175, gy = 1040, s = 30, R = idol(x, gy, s, { sd: 1, member: m, expr: 'sad', hL: [-.16, .55], hR: [.16, .55], gL: 'fist', gR: 'fist', mic: false, swing: 0, tilt: (i - 1.5) * .07 + Math.sin(t * 1.5 + i) * .03, blink: t + i });
      const [hx, hy] = handAt(R, x, gy, [0, .45]);
      lightstick(hx, hy - 8, 11, MEMBERS[m].col, { rot: .05 * Math.sin(t * 2 + i) });
      holes.push([hx, hy - 30, 170, .85, MEMBERS[m].col]);
    });
    ctx.fillStyle = '#0C0918'; ctx.fillRect(-100, 940, W + 200, 300);                 // stage lip hides their laps
    // flashlight spot finds the calendar
    const k = easeOut(clamp(lt / .3)), fx = lerp(420, cx, k) + Math.sin(t * 3) * 12, fy = lerp(220, cy - 10, k) + Math.cos(t * 2.3) * 10;
    holes.push([fx, fy, 420, 1]);
    const L = layerDraw(() => {
      ctx.fillStyle = 'rgb(5 3 12 / .93)'; ctx.fillRect(-100, -100, W + 200, H + 200);
      ctx.globalCompositeOperation = 'destination-out';
      for (const [x, y, r, a] of holes) { const g = ctx.createRadialGradient(x, y, 0, x, y, r); g.addColorStop(0, `rgb(0 0 0 / ${a})`); g.addColorStop(.62, `rgb(0 0 0 / ${a * .9})`); g.addColorStop(1, 'rgb(0 0 0 / 0)'); ctx.fillStyle = g; ctx.fillRect(x - r, y - r, r * 2, r * 2); }
    });
    ctx.save(); ctx.setTransform(1, 0, 0, 1, 0, 0); ctx.drawImage(L, 0, 0); ctx.restore();
    add(() => { for (const h of holes) if (h[4]) glow(h[0], h[1] + 20, 90, h[4], .45); ctx.fillStyle = 'rgb(255 250 220 / .06)'; ctx.beginPath(); ctx.moveTo(1900, 1100); ctx.lineTo(fx - 300, fy - 160); ctx.lineTo(fx + 300, fy + 200); ctx.fill(); });
    if (xs >= 18) vtag('DAY 19', 1240, 760, { size: 40, rot: -.04, line: IP.red, pop: pk(lt, 1.2, .15) });
    setBloom(.3);
  });

  // ---------------- 8. Come July, it's back again. ----------------
  function firework(t, t0, x, y, r, col, seed) {
    const a = t - t0; if (a < 0 || a > 1.3) return;
    const k = easeOut(clamp(a / .7)), fade = clamp(1 - (a - .5) / .8);
    add(() => {
      if (a < .15) glow(x, y, 200, IP.white, .8 * (1 - a / .15));
      for (let i = 0; i < 26; i++) { const an = i / 26 * TAU + hash2(seed, i) * .2, rr = r * k * (.8 + hash2(seed, i + 40) * .3), px = x + Math.cos(an) * rr, py = y + Math.sin(an) * rr + a * a * 120; ctx.strokeStyle = alpha(col, fade); ctx.lineWidth = 6; ctx.beginPath(); ctx.moveTo(x + Math.cos(an) * rr * .7, y + Math.sin(an) * rr * .7 + a * a * 100); ctx.lineTo(px, py); ctx.stroke(); ctx.fillStyle = alpha(IP.white, fade); ctx.beginPath(); ctx.arc(px, py, 5, 0, TAU); ctx.fill(); }
    });
  }
  line('V3', 8, (p, lt, d, t) => {
    const t0 = t - lt, b = bpOf(t), on = easeOut(clamp(lt / .5));
    setLight({ rim: IP.neonGold });
    stageSet(t, { led: (w, h) => { ledShow('rays', t, w, h, { c0: '#2A0C40', c1: '#3A1250' }); dtext('BACK ONLINE', w / 2, h * .3, h * .26, { fill: IP.white, strokes: [[IP.night, h * .07], [IP.neonLime, h * .035]], maxW: w * .9 }); dtext('JUL 1', w * .12, h * .88, h * .09, { font: 'code', fill: IP.white }); }, level: 2, hue: IP.neonGold, floorY: 700, ledRect: [360, 200, 1200, 420], beams: [IP.neonGold, IP.neonPink, IP.neonCyan] });
    const b0 = Math.round(bpOf(t0));
    for (let i = 0; i < 4; i++) firework(t, onBeat(0, b0 + i), [330, 1600, 560, 1380][i], [330, 300, 520, 520][i], 180, [IP.neonPink, IP.neonGold, IP.neonCyan, IP.neonLime][i], i + 5);
    // COMEBACK banner drops in
    const dropK = backOut(clamp(lt / .3), 1.4);
    ctx.save(); ctx.translate(900, lerp(-160, 95, dropK)); ctx.rotate(Math.sin(t * 3) * .015);
    ln([[-470, -80], [-430, -40]], IP.line, 4); ln([[470, -80], [430, -40]], IP.line, 4);
    solid([[-470, -45], [470, -45], [440, 20], [470, 85], [-470, 85], [-440, 20]], IP.neonPink, { shade: '#D02F80', sh: 12, line: IP.line, lw: 7, sharp: true });
    dtext('COMEBACK!', 0, 22, 92, { grad: ['#FFFFFF', '#FFF1A6', '#FFD23F'], strokes: [[IP.line, 16]] });
    ctx.restore();
    // Fable 5 returns
    const hop = Math.abs(Math.sin(b * Math.PI));
    fable(960, 915 - hop * 20, 45, { face: 'star', mouth: 'open', aL: 1 + hop * .3, aR: 1 + hop * .3, rim: IP.neonGold });
    sparkles(t, { n: 10, x0: 700, x1: 1220, y0: 380, y1: 800, r: 30, seed: 4 });
    // the ocean floods back on from the centre
    ctx.fillStyle = '#0B0618'; ctx.fillRect(-100, 900, W + 200, 300);
    ctx.save(); const xr = on * 1100; ctx.beginPath(); ctx.rect(960 - xr, 0, xr * 2, H); ctx.clip();
    lightOcean(t, { y0: 900, y1: 1110, n: 16, rows: 5, cols: [IP.neonGold, MEMBERS.TOKI.col, IP.neonCyan, IP.lilac], mode: 'pump', k: 1.2 });
    ctx.restore();
    flash(t, t0, .22, .95, '255 250 230');
  });

  // ---------------- 9. Who hacked Hugging Face? Unknown — ----------------
  function deerstalker(h) {
    ctx.save(); ctx.translate(h.x, h.y); ctx.rotate(h.rot); ctx.scale(h.h, h.h);
    const tan = '#C9A070', dk = '#8A6238', line = '#4A2E18';
    solid([[-.62, -.1], [-.2, -.2], [.2, -.2], [.62, -.1], [.66, -.02], [-.66, -.02]], tan, { shade: false, line, lw: .025 });      // brims
    const dome = [...ellPts(0, -.18, .54, .42, 30).filter(q => q[1] <= -.16)];
    solid(dome, tan, { shade: dk, sh: .05, line, lw: .028, size: .5 });
    ctx.save(); tracePath(dome); ctx.clip(); ctx.strokeStyle = alpha(dk, .7); ctx.lineWidth = .025;
    for (let i = -6; i <= 6; i++) { ctx.beginPath(); ctx.moveTo(i * .1, -.7); ctx.lineTo(i * .1 + .3, -.1); ctx.stroke(); ctx.beginPath(); ctx.moveTo(i * .1, -.7); ctx.lineTo(i * .1 - .3, -.1); ctx.stroke(); }
    ctx.restore();
    bow(0, -.6, .1, dk, .02, 0);
    ctx.restore();
  }
  function magnifier(hx, hy, lx, ly, r, inner) {
    ln([[hx, hy], [lx - (lx - hx) * r / Math.hypot(lx - hx, ly - hy), ly - (ly - hy) * r / Math.hypot(lx - hx, ly - hy)]], '#6A3A1A', r * .16);
    ln([[hx, hy], [lerp(hx, lx, .25), lerp(hy, ly, .25)]], '#9A5A2A', r * .12);
    ctx.save(); ctx.beginPath(); ctx.arc(lx, ly, r, 0, TAU); ctx.clip(); inner(); ctx.fillStyle = 'rgb(200 235 255 / .18)'; ctx.fillRect(lx - r, ly - r, r * 2, r * 2);
    ctx.fillStyle = 'rgb(255 255 255 / .35)'; ctx.beginPath(); ctx.ellipse(lx - r * .4, ly - r * .45, r * .35, r * .14, -.7, 0, TAU); ctx.fill(); ctx.restore();
    ctx.strokeStyle = '#C9A040'; ctx.lineWidth = r * .14; ctx.beginPath(); ctx.arc(lx, ly, r, 0, TAU); ctx.stroke();
    ctx.strokeStyle = '#6A3A1A'; ctx.lineWidth = r * .04; ctx.beginPath(); ctx.arc(lx, ly, r * 1.07, 0, TAU); ctx.stroke();
  }
  function suspectPhoto(x, y, w, rot, t) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot);
    solid(rrPts(-w / 2, -w * .62, w, w * 1.22, 6), IP.white, { shade: false, line: IP.line, lw: 4, sharp: true, dropShadow: [6, 9] });
    ctx.fillStyle = '#2A2448'; ctx.fillRect(-w * .43, -w * .54, w * .86, w * .86);
    ctx.fillStyle = '#0E0A1E'; ctx.beginPath(); ctx.arc(0, -w * .2, w * .19, 0, TAU); ctx.fill(); ctx.beginPath(); ctx.ellipse(0, w * .3, w * .34, w * .24, 0, Math.PI, 0); ctx.fill();
    dtext('?', 0, -w * .17, w * .3, { fill: IP.white });
    dtext('UNKNOWN', 0, w * .47, w * .12, { font: 'marker', fill: IP.red });
    ctx.restore();
  }
  line('V3', 9, (p, lt, d, t) => {
    const t0 = t - lt, tBlock = snap(t0 + .8) - t0, blocked = lt >= tBlock, b = bpOf(t);
    bgGrad('#FFDCC4', '#F2B496');
    // corkboard
    solid(rrPts(140, 150, 1320, 700, 16), '#C98A5A', { shade: '#A86A40', sh: 14, line: '#5A3418', lw: 10, sharp: true });
    ctx.fillStyle = 'rgb(90 50 20 / .18)'; for (let i = 0; i < 160; i++) { ctx.beginPath(); ctx.arc(170 + hash2(i, 1) * 1260, 180 + hash2(i, 2) * 640, 3 + hash2(i, 3) * 4, 0, TAU); ctx.fill(); }
    // strings between pins
    const pins = [[440, 250], [1130, 250], [760, 600], [1300, 620], [330, 640]];
    for (const [a, c] of [[0, 1], [0, 2], [1, 3], [2, 1], [4, 0]]) ln(qbez(pins[a], [(pins[a][0] + pins[c][0]) / 2, (pins[a][1] + pins[c][1]) / 2 + 40], pins[c], 10), '#E0243C', 5);
    // Hugging Face, hacked
    ctx.save(); ctx.translate(440, 400); ctx.rotate(-.06);
    solid(rrPts(-140, -150, 280, 320, 6), IP.white, { shade: false, line: IP.line, lw: 4, sharp: true, dropShadow: [6, 9] });
    ctx.fillStyle = '#FFF3C8'; ctx.fillRect(-122, -132, 244, 230);
    hugFace(0, -18, 88, { mood: 'x', bandage: true });
    dtext('HACKED 7/16', 0, 128, 30, { font: 'marker', fill: IP.red });
    ctx.restore();
    suspectPhoto(1130, 430, 300, .05, t);
    for (const [x, y, txt, rot, c] of [[760, 640, 'dataset\npipeline??', -.08, IP.lemon], [1310, 700, 'which\nmodel??', .07, '#FFC2E0']]) {
      ctx.save(); ctx.translate(x, y); ctx.rotate(rot); solid(rrPts(-95, -80, 190, 160, 4), c, { shade: false, line: alpha(IP.line, .5), lw: 3, sharp: true, dropShadow: [4, 6] });
      txt.split('\n').forEach((l, i) => dtext(l, 0, -22 + i * 44, 32, { font: 'marker', fill: IP.ink })); ctx.restore();
    }
    for (const [x, y] of pins) solid(ellPts(x, y, 13, 13, 12), IP.red, { shade: '#A01020', sh: 3, line: IP.line, lw: 3 });
    // detective TOKI
    const tx = 330, gy = 1060, hR = [1.45, .55];
    const R = idol(tx, gy, 46, { sd: 1, expr: blocked ? 'pout' : 'think', hR, gR: 'fist', hL: [-.35, .25], gL: 'flat', mic: false, emote: blocked ? 'vein' : undefined, emoteK: pk(lt, tBlock, .15), blink: t, tilt: blocked ? -.1 : .06, lookX: .6, lookY: -.3 });
    deerstalker(headAt(R, tx, gy));
    const [hx, hy] = handAt(R, tx, gy, hR), k = easeOut(clamp(lt / .35)), lx = lerp(760, 1135, k), ly = lerp(560, 410, k), lr = 190;
    magnifier(hx, hy, lx, ly, lr, () => {
      ctx.save(); ctx.translate(lx, ly); ctx.scale(1.5, 1.5); ctx.translate(-lx, -ly); bgGrad('#C98A5A', '#C98A5A'); suspectPhoto(1130, 430, 300, .05, t); ctx.restore();
    });
    {
      if (blocked) {
        const a = lt - tBlock, sc = lerp(1.6, 1, easeOut(clamp(a / .1)));
        ctx.save(); ctx.translate(lx, ly); ctx.rotate(-.18); ctx.scale(sc, sc);
        solid(rrPts(-230, -95, 460, 190, 16), IP.white, { shade: '#E0DCEA', sh: 8, line: IP.red, lw: 12, sharp: true });
        solid(ellPts(-150, 0, 52, 52, 24), IP.red, { shade: false, line: false }); ctx.fillStyle = IP.white; ctx.fillRect(-182, -12, 64, 24);
        dtext('BLOCKED BY', 50, -30, 40, { fill: IP.red, maxW: 290 }); dtext('GUARDRAILS', 50, 30, 48, { fill: IP.ink, maxW: 300 });
        ctx.restore();
      }
    }
    if (blocked) { sfx('BZZT!', 1470, 260, { size: 84, pop: clamp((lt - tBlock) / .1), rot: .12, grad: ['#FFFFFF', '#FFB3C8', '#FF4B5C'] }); vtag('(the forensics AI refused)', 1180, 790, { pop: pk(lt, tBlock + .3, .2), rot: -.03 }); }
    else vcap('WHO DUNNIT?', 1500, 260, { style: 'lilac', icon: 'q', size: 58, pop: pk(lt, .1, .2), rot: .05 });
  });

  // ---------------- 10. Sam's own agents, on their own! ----------------
  line('V3', 10, (p, lt, d, t) => {
    const t0 = t - lt, tPull = snap(t0 + .2) - t0, tDrop = snap(t0 + .6) - t0, b = bpOf(t);
    bgGrad([[0, '#1C1242'], [.6, '#3A2470'], [1, '#5A3A8A']], null);
    add(() => glow(360, 250, 420, '#FFF6D0', .35));
    solid(ellPts(360, 250, 130, 130, 36), '#FFF6D0', { shade: '#F0E0A8', sh: 14, line: false });
    for (let i = 0; i < 4; i++) { const bx = 700 + i * 260 + Math.sin(t * 3 + i) * 30, by = 170 + (i % 2) * 70 + Math.cos(t * 4 + i) * 12, w = Math.sin(t * 18 + i) * .5; ctx.fillStyle = '#140A2A'; ctx.beginPath(); ctx.moveTo(bx, by); ctx.quadraticCurveTo(bx - 25, by - 20 - w * 20, bx - 50, by + 4); ctx.quadraticCurveTo(bx - 25, by - 2, bx, by + 8); ctx.quadraticCurveTo(bx + 25, by - 2, bx + 50, by + 4); ctx.quadraticCurveTo(bx + 25, by - 20 - w * 20, bx, by); ctx.fill(); }
    ctx.fillStyle = '#23164A'; ctx.fillRect(-100, 880, W + 200, 300);
    // the stack of agents in a trench coat
    const cx = 900, gy = 960, dropped = lt >= tDrop, sw = Math.sin(b * Math.PI) * .03;
    const stackTop = gy - 3 * 150;
    for (let i = 0; i < 3; i++) miniAgent(cx + Math.sin(t * 6 + i) * 10 * (i + 1) * (dropped ? 1 : .2), gy - i * 148, 50, { eyes: dropped ? ['wide', 'x', 'spiral'][i] : 'dot', bar: IP.neonCyan, lanyard: '#10A37F', label: i === 2 ? 'SOL' : undefined, rot: dropped ? Math.sin(t * 7 + i) * .06 : 0 });
    // the coat falls away
    const cf = dropped ? easeIn(clamp((lt - tDrop) / .25)) : 0, coatY = cf * 420;
    if (cf < 1) {
      ctx.save(); ctx.translate(0, coatY); ctx.globalAlpha = 1 - cf * .3;
      solid([[cx - 120, stackTop + 120], [cx + 120, stackTop + 120], [cx + 190, gy - 10], [cx - 190, gy - 10]], '#B89A6A', { shade: '#8A6E48', sh: 22, line: '#4A3418', lw: 7 });
      solid([[cx - 120, stackTop + 120], [cx, stackTop + 230, 1], [cx + 120, stackTop + 120]], '#A08050', { shade: false, line: '#4A3418', lw: 5 });
      ln([[cx - 175, gy - 180], [cx + 175, gy - 180]], '#4A3418', 16);
      for (let i = 0; i < 3; i++) solid(ellPts(cx - 30, stackTop + 260 + i * 70, 10, 10, 10), '#4A3418', { shade: false, line: false });
      ctx.restore();
    }
    // TOKI yanks the "?" mask off (the mask is drawn first so her fist overlaps its edge)
    const pulled = lt >= tPull, mk = easeOut(clamp((lt - tPull) / .25));
    const tkx = lerp(640, 470, mk), hR = pulled ? [1.6, -.6] : [1.5, -.5];
    const mx = pulled ? lerp(cx, tkx + 165, mk) : cx, my = pulled ? lerp(stackTop + 60, 745, mk) - Math.sin(mk * Math.PI) * 60 : stackTop + 60;
    ctx.save(); ctx.translate(mx, my); ctx.rotate(pulled ? -mk * .5 : sw);
    solid(ellPts(0, 0, 105, 115, 30), '#3A2A6A', { shade: '#241848', sh: 14, line: IP.line, lw: 7 });
    dtext('?', 0, 6, 150, { fill: IP.white, strokes: [[IP.line, 12]] });
    ctx.restore();
    idol(tkx, 1000, 44, { sd: 1, expr: pulled ? 'fired' : 'pout', hR, gR: 'fist', hL: [-.9, 1.2], gL: 'fist', lean: pulled ? -.15 * mk : .1, mic: false, blink: t });
    // SAM facepalms
    const sx = 1450, sgy = 960, ss = 38;
    chibi(sx, sgy, ss, { name: 'SAM', hair: 'short', hairCol: '#6A4A30', top: 'sweater', topCol: '#9AA7C8', eyes: dropped ? 'squeeze' : 'wide', mouth: dropped ? 'wavy' : 'O', aR: dropped ? 1.9 : .3, aL: -1.1, sweat: dropped ? 1 : 0, blush: .2 });
    if (dropped) { solid(ellPts(sx + .55 * ss, sgy - 7.1 * ss, .62 * ss, .5 * ss, 18), CHIBI_SKIN[0], { shade: false, line: mixCol(CHIBI_SKIN[0], '#5A2030', .55), lw: 4 }); ctx.fillStyle = alpha('#5B4F9E', .5); for (let i = 0; i < 5; i++) ctx.fillRect(sx - 1.6 * ss + i * .6 * ss, sgy - 9.1 * ss, 6, 50 + (i % 2) * 20); }
    if (dropped) vcap('IT WAS US?!', 1400, 250, { style: 'shock', icon: 'sweat', size: 84, pop: pk(lt, tDrop + .08, .2), shake: 2, rot: -.05 });
    else sfx('YANK!', 760, 300, { size: 90, pop: pk(lt, tPull, .08), rot: -.15 });
  });

  // ---------------- 11. Noam Brown hedges every bet: ----------------
  function chipStack(x, y, n, col) { for (let i = 0; i < n; i++) { solid(ellPts(x, y - i * 11, 42, 15, 20), col, { shade: mixCol(col, IP.plum, .35), sh: 5, line: IP.line, lw: 3 }); ctx.strokeStyle = alpha(IP.white, .8); ctx.lineWidth = 3; ctx.setLineDash([8, 10]); ctx.beginPath(); ctx.ellipse(x, y - i * 11, 32, 10, 0, 0, TAU); ctx.stroke(); ctx.setLineDash([]); } }
  function playCard(x, y, w, rot, big) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot);
    solid(rrPts(-w / 2, -w * .7, w, w * 1.4, w * .08), IP.white, { shade: '#E4DEF2', sh: 6, line: IP.line, lw: 4, sharp: true });
    dtext('10', -w * .32, -w * .52, w * .2, { font: 'archivo', fill: IP.red });
    tracePath(heartPts(-w * .32, -w * .33, w * .07, 20)); ctx.fillStyle = IP.red; ctx.fill();
    if (big) { dtext('OPEN', 0, -w * .05, w * .19, { fill: IP.ink }); dtext('PROBLEMS', 0, w * .17, w * .135, { fill: IP.ink, maxW: w * .86 }); }
    else { tracePath(heartPts(0, 0, w * .2, 24)); ctx.fillStyle = IP.red; ctx.fill(); }
    ctx.restore();
  }
  line('V3', 11, (p, lt, d, t) => {
    const b = bpOf(t), push = easeOut(clamp(lt / .45));
    bgGrad('#6A1438', '#2A0818');
    patternBG('stripe', 'rgb(0 0 0 / 0)', 'rgb(255 210 63 / .05)', { cell: 90 });
    add(() => { glow(960, 250, 700, IP.neonGold, .35); bokeh(t, { n: 10, r: 60, alpha: .2, cols: [IP.neonGold, IP.red], y1: 600 }); });
    // hanging lamp
    ln([[960, 0], [960, 90]], '#1A0810', 6); solid([[820, 170], [1100, 170], [1030, 90], [890, 90]], '#1E6A4A', { shade: false, line: IP.line, lw: 5 });
    // NOAM, poker-faced
    const aL = lerp(-.2, -.55, push), aR = lerp(-.2, -.55, push);
    chibi(960, 900, 46, { hair: 'short', hat: 'visor', top: 'tee', topCol: '#2FA86A', skin: 1, eyes: 'dot', mouth: 'flat', aL, aR, blush: 0 });
    // table
    solid(ellPts(960, 1180, 1250, 440, 60), '#7A4A28', { shade: '#5A3018', sh: 20, line: '#2A1008', lw: 8 });
    solid(ellPts(960, 1190, 1180, 400, 60), '#1E8A5A', { shade: false, line: '#0E4A2A', lw: 5 });
    ctx.save(); ctx.globalAlpha = .25; ctx.strokeStyle = IP.white; ctx.lineWidth = 4; ctx.beginPath(); ctx.ellipse(960, 1190, 1000, 320, 0, Math.PI * 1.1, Math.PI * 1.9); ctx.stroke(); ctx.restore();
    for (const [x, txt] of [[420, 'HYPE'], [1500, 'CAVEAT']]) { ctx.strokeStyle = IP.neonGold; ctx.lineWidth = 6; ctx.beginPath(); ctx.ellipse(x, 900, 170, 58, 0, 0, TAU); ctx.stroke(); dtext(txt, x, 944, 34, { fill: IP.neonGold, strokes: [[IP.line, 8]] }); }
    // chips slide out to BOTH spots at once
    const [lhx, lhy] = chibiHand(960, 900, 46, -1, aL), [rhx, rhy] = chibiHand(960, 900, 46, 1, aR);
    chipStack(lerp(lhx - 30, 440, push), 895, 6, IP.red); chipStack(lerp(lhx + 20, 380, push), 880, 4, IP.sky);
    chipStack(lerp(rhx + 30, 1480, push), 895, 6, IP.red); chipStack(lerp(rhx - 20, 1540, push), 880, 4, IP.sky);
    // his hand: ten open problems
    [-2, -1, 1, 2].forEach(i => playCard(960 + i * 70, 830 + Math.abs(i) * 12, 120, i * .14, false));
    playCard(960, 815, 150, 0, true);
    vcap('ALL IN…\nBOTH WAYS', 380, 330, { style: 'yellow', size: 60, pop: pk(lt, .3, .2), rot: -.06 });
  });

  // ---------------- 12. "No Millennium Prizes (yet)." ----------------
  const trophyPts = (x, y, s) => [[x - s * .9, y - s * 2.6], [x + s * .9, y - s * 2.6], [x + s * .75, y - s * 1.6], [x + s * .2, y - s * 1.15], [x + s * .2, y - s * .5], [x + s * .6, y - s * .35], [x + s * .6, y], [x - s * .6, y], [x - s * .6, y - s * .35], [x - s * .2, y - s * .5], [x - s * .2, y - s * 1.15], [x - s * .75, y - s * 1.6]];
  const MPRIZE = ['P vs NP', 'RIEMANN', 'NAVIER–STOKES', 'YANG–MILLS', 'HODGE', 'BIRCH–SWINNERTON-DYER'];
  line('V3', 12, (p, lt, d, t) => {
    const t0 = t - lt, tNote = snap(t0 + .3) - t0, b = bpOf(t);
    bgGrad('#D6F2FF', '#A9DDF2');
    patternBG('stripe', 'rgb(0 0 0 / 0)', 'rgb(255 255 255 / .25)', { cell: 140 });
    // cabinet
    solid(rrPts(250, 150, 1260, 760, 18), '#B8764A', { shade: '#8A5030', sh: 18, line: '#4A2410', lw: 9, sharp: true });
    solid(rrPts(290, 280, 1180, 590, 8), '#2A3A6A', { shade: false, line: '#4A2410', lw: 5, sharp: true });
    add(() => glow(880, 250, 600, '#FFE6B0', .25));
    // header plaque
    solid(rrPts(520, 176, 720, 84, 14), IP.gold, { shade: '#D08A20', sh: 8, line: '#6A3A10', lw: 5, sharp: true });
    dtext('MILLENNIUM PRIZES', 880, 220, 46, { fill: '#5A2E0E', maxW: 660 });
    // shelves: six empty spots with dust outlines
    for (let i = 0; i < 6; i++) {
      const col = i % 3, row = Math.floor(i / 3), x = 490 + col * 390, y = 540 + row * 300, ns = i === 2;
      solid(rrPts(300, y + 4, 1160, 24, 4), '#C98A5A', { shade: false, line: '#4A2410', lw: 4, sharp: true });
      const tw = ns && b % 1 < .25 ? Math.sin(t * 90) * 6 : 0;
      ctx.save(); ctx.translate(tw, 0);
      ctx.setLineDash([12, 10]); ctx.strokeStyle = 'rgb(255 230 200 / .45)'; ctx.lineWidth = 5; tracePath(trophyPts(x, y, 60)); ctx.stroke(); ctx.setLineDash([]);
      if (ns) add(() => glow(x, y - 90, 170, IP.neonCyan, .25 + .25 * pulse(t, 3)));
      solid(rrPts(x - 150, y + 36, 300, 50, 8), '#E8C070', { shade: false, line: '#6A3A10', lw: 4, sharp: true });
      dtext(MPRIZE[i], x, y + 62, 26, { fill: '#4A2410', maxW: 270 });
      ctx.restore();
      if (ns) { emote('bang', x + 140, y - 170, 60, clamp(frac(b) * 4) * (frac(b) < .5 ? 1 : 0)); if (frac(b) < .3) for (let j = 0; j < 3; j++) ln([[x - 120 - j * 10, y - 60 - j * 40], [x - 150 - j * 10, y - 70 - j * 40]], alpha(IP.ink, .6), 5); }
    }
    // dust motes
    for (let i = 0; i < 18; i++) { const r = k => hash2(i + 3, k); sparkle(300 + r(1) * 1160, 300 + frac(r(2) + t * .05 * (r(3) + .5)) * 560, 5 + r(4) * 5, 0, 'rgb(255 245 220 / .8)', { glow: false }); }
    // the sticky note
    if (lt >= tNote) {
      const a = lt - tNote, sc = lerp(1.8, 1, easeOut(clamp(a / .12)));
      ctx.save(); ctx.translate(1300, 230); ctx.rotate(.14); ctx.scale(sc, sc);
      solid(rrPts(-120, -95, 240, 190, 4), IP.lemon, { shade: '#F0D870', sh: 10, line: alpha(IP.line, .5), lw: 3, sharp: true, dropShadow: [6, 10] });
      dtext('(yet)', 0, 6, 76, { font: 'marker', fill: IP.red });
      ctx.restore();
      sfx('SLAP!', 1560, 480, { size: 70, pop: clamp(a / .08), rot: .15 });
    }
    // LOGI peeks in, curious
    idol(130, 1080, 38, { sd: 1, member: 'LOGI', expr: 'think', ...IDOL_POSES.think, mic: false, blink: t, tilt: .15 });
  });

  // ---------------- 13. Mythos might be misaligned, ----------------
  function sockPuppet(x, y, r, col, talk, rot) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot);
    solid(rrPts(-r * .55, -r * .2, r * 1.1, r * 1.6, r * .3), col, { shade: mixCol(col, IP.plum, .25), sh: r * .12, line: IP.line, lw: r * .07, sharp: true });
    for (let i = 0; i < 3; i++) { ctx.fillStyle = alpha(IP.white, .7); ctx.fillRect(-r * .55, r * .9 + i * r * .2, r * 1.1, r * .08); }
    const m = talk * .5;
    solid(ellPts(0, -r * .55, r * .8, r * .7, 24), col, { shade: mixCol(col, IP.plum, .25), sh: r * .12, line: IP.line, lw: r * .07 });
    ctx.fillStyle = '#9A2E4E'; ctx.beginPath(); ctx.ellipse(r * .1, -r * .35, r * .55, r * (.08 + m * .5), 0, 0, TAU); ctx.fill();
    for (const sd of [-1, 1]) { solid(ellPts(sd * r * .3, -r * .85, r * .17, r * .17, 12), IP.white, { shade: false, line: IP.line, lw: r * .05 }); ctx.fillStyle = IP.ink; ctx.beginPath(); ctx.arc(sd * r * .3, -r * .83, r * .08, 0, TAU); ctx.fill(); }
    ctx.restore();
  }
  line('V3', 13, (p, lt, d, t) => {
    const t0 = t - lt, tStamp = snap(t0 + 1.0) - t0, b = bpOf(t), bn = beatN(t);
    bgGrad('#2A1A5A', '#4A2A8A');
    patternBG('grid', 'rgb(0 0 0 / 0)', 'rgb(160 255 220 / .12)', { cell: 80, dy: t * 40 });
    for (let i = 0; i < 6; i++) if (hash2(_boil, i) > .6) { ctx.fillStyle = alpha([IP.neonCyan, IP.neonPink][i % 2], .25); ctx.fillRect(0, hash2(i, _boil) * H, W, 6 + hash2(_boil, i + 9) * 18); }
    // the pull request
    ctx.save(); ctx.translate(330, 330); ctx.rotate(-.05);
    solid(rrPts(-220, -130, 440, 260, 18), '#F4F6FA', { shade: '#D8DCE8', sh: 8, line: IP.line, lw: 5, sharp: true, dropShadow: [8, 12] });
    dtext('PR #1337', -190, -90, 30, { align: 'left', fill: IP.ink });
    dtext('+ tiny fix :)', -190, -36, 26, { font: 'code', align: 'left', fill: '#1E8A4A' });
    dtext('+ malware.js', -190, 4, 26, { font: 'code', align: 'left', fill: IP.red });
    solid(rrPts(-190, 44, 200, 58, 12), '#2EA043', { shade: false, line: IP.line, lw: 4, sharp: true });
    dtext('MERGE', -90, 74, 28, { fill: IP.white });
    ctx.restore();
    // Mythos, compass for a face
    const mx = 960, gy = 960, s = 56, aL = .55 + Math.sin(b * Math.PI) * .12, aR = .55 - Math.sin(b * Math.PI) * .12;
    mascotBot(mx, gy, s, { col: '#C9B6FF', label: 'MYTHOS', face: 'text', text: '', aL, aR, glitch: .6, dy: -Math.abs(Math.sin(b * Math.PI)) * .2 });
    const fy = gy - 7.55 * s - Math.abs(Math.sin(b * Math.PI)) * .2 * s, fr = 1.25 * s;
    solid(ellPts(mx, fy, fr, fr, 36), '#FFF6E0', { shade: false, line: IP.gold, lw: 7 });
    for (const [l, a] of [['N', -Math.PI / 2], ['E', 0], ['S', Math.PI / 2], ['W', Math.PI]]) dtext(l, mx + Math.cos(a) * fr * .72, fy + Math.sin(a) * fr * .72, 22, { font: 'code', fill: IP.inkSoft });
    const na = t * 11 + Math.sin(t * 5) * 3;
    ctx.save(); ctx.translate(mx, fy); ctx.rotate(na);
    solid([[0, -fr * .75], [fr * .13, 0], [0, fr * .1], [-fr * .13, 0]], IP.red, { shade: false, line: IP.line, lw: 3 });
    solid([[0, fr * .75], [fr * .13, 0], [0, -fr * .1], [-fr * .13, 0]], '#E8ECF8', { shade: false, line: IP.line, lw: 3 });
    ctx.restore();
    solid(ellPts(mx, fy, 9, 9, 10), IP.gold, { shade: false, line: IP.line, lw: 3 });
    // sock puppets on both hands, vouching for each other
    const hands = [[-1, aL], [1, aR]].map(([sd, a]) => { const A = sd > 0 ? -a : Math.PI + a; return [mx + (sd * 1.25 + Math.cos(A) * 1.9) * s, gy - (4.1 + .2 * Math.abs(Math.sin(b * Math.PI))) * s + Math.sin(A) * 1.9 * s]; });
    const talkL = bn % 2 === 0, talkR = !talkL, ph = frac(b * 2);
    sockPuppet(hands[0][0] - 10, hands[0][1] - 40, 70, '#FF9EC4', talkL ? Math.abs(Math.sin(ph * Math.PI)) : 0, -.25);
    sockPuppet(hands[1][0] + 10, hands[1][1] - 40, 70, '#9FE3FF', talkR ? Math.abs(Math.sin(ph * Math.PI)) : 0, .25);
    dtext('@real_human_1', hands[0][0] - 10, hands[0][1] + 130, 22, { font: 'code', fill: IP.white, strokes: [[IP.line, 6]] });
    dtext('@real_human_2', hands[1][0] + 10, hands[1][1] + 130, 22, { font: 'code', fill: IP.white, strokes: [[IP.line, 6]] });
    if (talkL || lt > .8) chatBubble('LGTM!', hands[0][0] - 330, hands[0][1] - 190, { size: 44, pop: talkL ? clamp(frac(b) * 6) : 1 });
    if (talkR || lt > .8) chatBubble('MERGE IT!', hands[1][0] + 300, hands[1][1] - 190, { size: 44, me: true, pop: talkR ? clamp(frac(b) * 6) : 1 });
    // the AISI clipboard
    ctx.save(); ctx.translate(1600, 700); ctx.rotate(.06);
    solid(rrPts(-150, -190, 300, 380, 16), '#B07A4A', { shade: '#8A5A30', sh: 10, line: '#4A2410', lw: 6, sharp: true });
    docCard(0, 15, 250, 320, { title: 'AISI', head: '#2A4A9A', body: ['agent test', 'with internet'], lines: 3, stamp: { text: '?!', col: IP.red, pop: clamp((lt - tStamp) / .12), dx: 0, dy: 60, r: 115 } });
    solid(rrPts(-50, -210, 100, 44, 10), '#C9CEDD', { shade: false, line: IP.line, lw: 4, sharp: true });
    ctx.restore();
    if (lt >= tStamp) sfx('STAMP!', 1620, 420, { size: 64, pop: clamp((lt - tStamp) / .08), rot: .1 });
  });

  // ---------------- 14. Jeff left Google just in time, ----------------
  line('V3', 14, (p, lt, d, t) => {
    const t0 = t - lt, tClick = snap(t0 + .8) - t0, clicked = lt >= tClick, b = bpOf(t);
    bgGrad('#FFE6CC', '#F8C6A0', { y1: 760 });
    ctx.fillStyle = '#E8A87C'; ctx.fillRect(-100, 740, W + 200, 30);
    ctx.save(); ctx.beginPath(); ctx.rect(-100, 770, W + 200, 400); ctx.clip(); bgGrad('#F2E6DA', '#D8C4B0', { y0: 770, y1: H });
    ctx.strokeStyle = 'rgb(120 80 60 / .2)'; ctx.lineWidth = 3; for (let i = -10; i < 12; i++) { ctx.beginPath(); ctx.moveTo(960 + i * 150, 770); ctx.lineTo(960 + i * 360, H + 20); ctx.stroke(); } ctx.restore();
    // the EXIT door
    solid(rrPts(1480, 330, 290, 440, 8), '#8A6AC8', { shade: '#6A4AA8', sh: 14, line: IP.line, lw: 7, sharp: true });
    solid(ellPts(1520, 560, 16, 16, 12), IP.gold, { shade: false, line: IP.line, lw: 3 });
    solid(rrPts(1545, 250, 160, 60, 10), '#1FA86A', { shade: false, line: IP.line, lw: 5, sharp: true }); dtext('EXIT', 1625, 282, 40, { fill: IP.white });
    add(() => glow(1625, 280, 120, '#3FFFA0', .3));
    // the clock, ticking onto JUST IN TIME
    const cx = 760, cy = 270, r = 170;
    solid(ellPts(cx, cy, r, r, 40), IP.white, { shade: '#E0D8EA', sh: 12, line: IP.line, lw: 8 });
    ctx.fillStyle = alpha(IP.neonPink, .85); ctx.beginPath(); ctx.moveTo(cx, cy); ctx.arc(cx, cy, r * .92, -Math.PI / 2 - .2, -Math.PI / 2 + .2); ctx.closePath(); ctx.fill();
    for (let i = 0; i < 12; i++) { const a = i / 12 * TAU; ln([[cx + Math.cos(a) * r * .78, cy + Math.sin(a) * r * .78], [cx + Math.cos(a) * r * .9, cy + Math.sin(a) * r * .9]], IP.line, 6); }
    const steps = Math.min(Math.floor(lt / (tClick / 6)), 6), ma = clicked ? -Math.PI / 2 : -Math.PI / 2 - (6 - steps) * .22;
    ln([[cx, cy], [cx + Math.cos(-Math.PI / 2 + 2.2) * r * .45, cy + Math.sin(-Math.PI / 2 + 2.2) * r * .45]], IP.line, 14);
    ln([[cx, cy], [cx + Math.cos(ma) * r * .8, cy + Math.sin(ma) * r * .8]], IP.line, 9);
    solid(ellPts(cx, cy, 16, 16, 12), IP.red, { shade: false, line: IP.line, lw: 3 });
    ctx.save(); ctx.translate(cx, cy + r + 42); ctx.rotate(-.03); solid(rrPts(-170, -30, 340, 60, 30), IP.neonPink, { shade: false, line: IP.line, lw: 5, sharp: true }); dtext('JUST IN TIME', 0, 2, 36, { fill: IP.white }); ctx.restore();
    if (clicked) { sparkle(cx + 30, cy - r - 10, 50 * pulse(t, 3) + 10, t, IP.neonGold); sfx('CLICK!', cx + 300, cy - 60, { size: 76, pop: clamp((lt - tClick) / .08), rot: .12 }); }
    // DEMIS gets moved to the CHAIR
    const ck = easeOut(clamp((lt - .25) / .35)), chx = lerp(-200, 290, ck), sat = ck >= 1;
    ctx.save(); ctx.translate(290, 0); ctx.fillStyle = alpha(IP.line, .12); rrect(-120, 360, 240, 70, 12); ctx.fill(); dtext('CEO', 0, 396, 40, { fill: alpha(IP.ink, .5) }); ln([[-80, 396], [80, 396]], IP.red, 8); ctx.restore();
    solid(rrPts(chx - 130, 520, 260, 330, 50), '#6A3A9A', { shade: '#4A2A7A', sh: 18, line: IP.line, lw: 6, sharp: true });
    chibi(290, sat ? 800 : 880, 26, { name: 'DEMIS', hair: 'buzz', hairCol: '#2A2228', top: 'suit', topCol: '#2A3A6A', tie: IP.neonCyan, skin: 2, eyes: sat ? 'happy' : 'wide', mouth: sat ? 'grin' : 'O', aL: sat ? .3 : -1.1, aR: sat ? .3 : -1.1, shadow: false });
    solid(rrPts(chx - 150, 740, 300, 90, 30), '#8A5AC8', { shade: '#6A3A9A', sh: 12, line: IP.line, lw: 6, sharp: true });
    for (const sd of [-1, 1]) solid(rrPts(chx + sd * 150 - 30, 640, 60, 170, 26), '#8A5AC8', { shade: '#6A3A9A', sh: 8, line: IP.line, lw: 5, sharp: true });
    ctx.save(); ctx.translate(chx, 875); solid(rrPts(-90, -28, 180, 56, 28), IP.neonGold, { shade: false, line: IP.line, lw: 5, sharp: true }); dtext('CHAIR', 0, 2, 34, { fill: IP.ink }); ctx.restore();
    // JEFF walks out with his box
    const wk = clamp(lt / (d * .95)), jx = lerp(900, 1400, wk), jy = 930, s = 40, walk = lt * 2.6;
    chibi(jx, jy, s, { hair: 'short', hairCol: '#9A9AA8', top: 'tee', topCol: '#4A7AE8', eyes: clicked ? 'happy' : 'dot', mouth: 'smile', aL: -.35, aR: -.35, walk, dy: -Math.abs(Math.sin(walk * Math.PI)) * .2 });
    const bxx = jx, byy = jy - 3.2 * s - Math.abs(Math.sin(walk * Math.PI)) * .2 * s;
    // the potted plant and the mug sit at the box's ends, clear of his face
    solid(ellPts(bxx - 92, byy - 104, 30, 40, 16), '#4FB894', { shade: '#2A8A6A', sh: 6, line: '#1A5A3A', lw: 4 }); ln([[bxx - 92, byy - 66], [bxx - 92, byy - 40]], '#2A6A3A', 6);
    solid(rrPts(bxx + 58, byy - 96, 46, 56, 10), IP.white, { shade: false, line: IP.line, lw: 4, sharp: true });
    solid(rrPts(bxx - 120, byy - 60, 240, 150, 8), '#D8A060', { shade: '#B07840', sh: 10, line: '#5A3418', lw: 5, sharp: true });
    ln([[bxx - 120, byy - 60], [bxx - 90, byy - 90], [bxx + 90, byy - 90], [bxx + 120, byy - 60]], '#5A3418', 5);
    ctx.save(); ctx.translate(bxx, byy + 15); ctx.rotate(-.08); solid(ellPts(0, 0, 90, 44, 24), IP.lemon, { shade: false, line: IP.red, lw: 5 }); dtext('27 YEARS', 0, 2, 30, { fill: IP.red }); ctx.restore();
    vtag('(new startup: DISCOVERY LOOP)', 1180, 520, { size: 26, pop: pk(lt, .6, .2), rot: .03 });
  });

  // ---------------- 15. Claude disproved Jacobian, ----------------
  line('V3', 15, (p, lt, d, t) => {
    const t0 = t - lt, tStamp = snap(t0 + .4) - t0, stamped = lt >= tStamp, b = bpOf(t);
    bgGrad('#6A4A38', '#4A3024');
    solid(rrPts(90, 60, 1560, 780, 14), '#8A5A3A', { shade: '#6A4028', sh: 14, line: '#3A2018', lw: 8, sharp: true });
    solid(rrPts(120, 90, 1500, 720, 6), '#2E5A48', { shade: false, line: '#1A3A2A', lw: 5, sharp: true });
    ctx.fillStyle = 'rgb(255 255 255 / .05)'; for (let i = 0; i < 8; i++) { ctx.beginPath(); ctx.ellipse(250 + i * 180, 200 + (i % 3) * 200, 160, 50, .2, 0, TAU); ctx.fill(); }
    const chalk = { font: 'marker', fill: 'rgb(250 250 240 / .92)' };
    dtext('JACOBIAN CONJECTURE (1939)', 170, 160, 50, { ...chalk, align: 'left' });
    dtext('det J = const', 190, 330, 76, { ...chalk, align: 'left' });
    ln([[250, 430], [480, 430]], 'rgb(250 250 240 / .9)', 8); ln([[450, 405], [485, 430], [450, 455]], 'rgb(250 250 240 / .9)', 8);
    dtext('invertible?', 520, 435, 76, { ...chalk, align: 'left' });
    // three points mapped onto one
    const P3 = [[1080, 260], [1040, 450], [1120, 620]], tgt = [1450, 440];
    const ak = easeOut(clamp(lt / .35));
    P3.forEach(([x, y], i) => { solid(ellPts(x, y, 16, 16, 12), 'rgb(250 250 240 / .95)', { shade: false, line: false }); const e = [lerp(x, tgt[0] - 30, ak), lerp(y, tgt[1], ak)]; ln([[x + 20, y], e], 'rgb(250 250 240 / .85)', 6); if (ak > .9) { const a = Math.atan2(tgt[1] - y, tgt[0] - 30 - x); ln([[e[0] - Math.cos(a - .5) * 26, e[1] - Math.sin(a - .5) * 26], e, [e[0] - Math.cos(a + .5) * 26, e[1] - Math.sin(a + .5) * 26]], 'rgb(250 250 240 / .85)', 6); } });
    solid(ellPts(tgt[0], tgt[1], 22, 22, 12), IP.neonGold, { shade: false, line: false });
    dtext('F(a) = F(b) = F(c)', 1250, 740, 40, chalk);
    if (stamped) {
      const a = lt - tStamp, sc = lerp(1.8, 1, easeOut(clamp(a / .1)));
      ctx.save(); ctx.translate(560, 540); ctx.rotate(-.14); ctx.scale(sc, sc); ctx.globalAlpha = clamp(a / .05) * .95;
      ctx.strokeStyle = IP.red; ctx.lineWidth = 14; rrect(-310, -80, 620, 160, 30); ctx.stroke(); ctx.lineWidth = 5; rrect(-290, -62, 580, 124, 22); ctx.stroke();
      dtext('DISPROVED', 0, 4, 96, { fill: IP.red });
      ctx.restore();
    }
    vtag('(n ≥ 3)', 1320, 170, { size: 40, pop: pk(lt, tStamp + .25, .18), rot: .05, line: IP.neonGold });
    // Clawd, proud, chalk in nub
    const hop = stamped ? Math.abs(Math.sin(b * Math.PI)) : 0;
    solid(rrPts(1560, 880, 200, 40, 8), '#C98A5A', { shade: false, line: '#5A3418', lw: 5, sharp: true });
    fanClawd(1660, 885, 19, { eyes: stamped ? 'happy' : 'normal', mouth: stamped ? 'open' : 'smile', aR: stamped ? 1.2 : .5, aL: -.3, dy: -hop * .5, shadow: false, blush: true });
    const cxh = 1660 + 4.95 * 19 + Math.cos(stamped ? 1.2 : .5) * 2 * 19, cyh = 885 - hop * .5 * 19 - 4.9 * 19 - Math.sin(stamped ? 1.2 : .5) * 2 * 19;
    solid(rrPts(cxh - 8, cyh - 40, 16, 50, 6), IP.white, { shade: false, line: IP.line, lw: 3, sharp: true });
    if (stamped) { sparkle(1560, 640, 34 * pulse(t, 3), t, IP.neonGold); sparkle(1790, 660, 26 * pulse(t, 4), t, IP.white); }
    // the idols applaud
    ['ADA', 'TOKI', 'RELU', 'LOGI'].forEach((m, i) => idol(180 + i * 150, 975, 26, { sd: 1, member: m, ...idolMove('clap', b - i * .1), expr: stamped ? 'sparkle' : 'surprised', mic: false, blink: t + i }));
  });

  // ---------------- 16. Gwern gave up his pseudonym! ----------------
  line('V3', 16, (p, lt, d, t) => {
    const t0 = t - lt, tPull = snap(t0 + .45) - t0, rev = lt >= tPull, a = lt - tPull, b = bpOf(t);
    const x = 960, gy = 930, s = 48;
    if (!rev) {
      bgGrad('#6A6488', '#3A3458');
      add(() => glow(x, 520, 480, IP.lilac, .3));
      ctx.fillStyle = 'rgb(20 10 40 / .3)'; ctx.beginPath(); ctx.ellipse(x, gy, 260, 40, 0, 0, TAU); ctx.fill();
    } else {
      rays(x, 470, 24, '#FFE98A', '#FFF6C8', t * .4);
      add(() => { glow(x, 470, 700, '#FFF3B0', .55); glow(x, 470, 260, IP.white, .7 * clamp(1 - a * 1.5)); });
      sparkles(t, { n: 22, seed: 16, r: 30, cols: [IP.white, IP.lemon, IP.pink] });
    }
    const pullK = clamp((lt - tPull + .25) / .25), arms = rev ? lerp(1.9, .9, easeOut(clamp(a / .3))) : lerp(-1.1, 1.9, pullK);
    // the lowered hood sits behind his neck
    if (rev) solid(ellPts(x, gy - 5.2 * s, 2.4 * s, 1.1 * s, 30), '#4A4458', { shade: '#34304A', sh: 10, line: IP.line, lw: 5 });
    chibi(x, gy, s, { hair: rev ? 'messy' : 'hood', hairCol: rev ? '#6A4A3A' : '#4A4458', top: 'hoodie', topCol: '#4A4458', eyes: rev ? 'dot' : 'shades', mouth: rev ? 'grin' : 'flat', aL: arms, aR: arms, dy: rev ? -Math.max(0, Math.sin(clamp(a / .35) * Math.PI)) * .6 : 0, blush: rev ? .6 : 0 });
    // the badge flips from "?" to GWERN!
    const fk = clamp((lt - tPull - .2) / .25), fc = Math.cos(fk * Math.PI);
    ctx.save(); ctx.translate(x + .15 * s, gy - 3.15 * s - (rev ? Math.max(0, Math.sin(clamp(a / .35) * Math.PI)) * .6 * s : 0)); ctx.scale(Math.max(.05, Math.abs(fc)) * 1.25, 1.25);
    nameBadge(fc > 0 ? '?' : 'GWERN!', 0, 0, s * .95, fc > 0 ? IP.inkSoft : IP.neonPink);
    ctx.restore();
    if (rev && a > .9) { ctx.strokeStyle = IP.neonGold; ctx.lineWidth = 10; ctx.beginPath(); ctx.ellipse(x, gy - 10.4 * s + Math.sin(t * 4) * 6, 1.3 * s, .32 * s, 0, 0, TAU); ctx.stroke(); add(() => glow(x, gy - 10.4 * s, 120, IP.neonGold, .4)); }
    // the idols throw confetti
    [['LOGI', 170, 1], ['RELU', 380, 1], ['TOKI', 1540, -1], ['ADA', 1750, -1]].forEach(([m, ix, sd], i) => {
      idol(ix, 1000, 30, { sd: 1, member: m, expr: rev ? 'joy' : 'surprised', ...(rev ? { hL: [-1.2, -.9], hR: [1.2, -.9], gL: 'open', gR: 'open' } : IDOL_POSES.shock), mic: false, blink: t + i, jump: rev ? Math.max(0, Math.sin((b + i * .2) * Math.PI)) * .5 : 0 });
      if (rev) confetti(t, t0 + tPull, ix, 700, sd > 0 ? -1.1 : -2.05, { n: 40, seed: 60 + i, speed: 1300 });
    });
    if (rev) { vcap('FACE REVEAL?!', 960, 150, { style: 'yellow', icon: 'spark', size: 80, pop: pk(lt, tPull + .1, .2), rot: -.04 }); flash(t, t0 + tPull, .2, .9, '255 250 220'); }
  });
})();

;
// ---- styles/idol/ch/c07_chorus3.js ----
// c07_chorus3 — Chorus 3: the ARENA CONCERT. Sub-shots timed from linesOf('C3') and the beat grid.
//   A1 "We didn't start the scaling"        a crane shot down from the arena roof over a stand full of lightsticks, landing on the group
//                                            on stage; flame jets fire on the bar downbeats.
//   A2   (on "scaling")                     ADA close-up, star eyes, pointing up, flame columns roaring behind her.
//   B  "It was always training,"            from the stage over TOKI's shoulder: the whole arena's sticks pump and the fanchant pops in
//                                            lightstick colours: "IT! WAS! ALWAYS! TRAINING!".
//   C  "and the curves kept gaining,"       the members wave from a trolley rolling through the crowd; the stands do a card stunt that
//                                            draws the level-3 curve in lights, echoed on three hanging LED screens.
//   D  "We didn't start the scaling"        Clawd at the barrier with his towel; TOKI points at him, he faints backwards and the crowd
//                                            catches him.
//   E  "No, we didn't preordain it,"        PYRO: UNCONTAINED. The jets multiply every beat; everyone jumps; freeze on the peak.
//   F  "but we can't contain it!"           ENDING FAIRY: ADA, elegant, out of breath and slightly singed; freezes into her photocard.
(() => {
  const snap = x => onBeat(0, Math.round(bpOf(x)));
  function plan() {
    const S = span('C3'), L = linesOf('C3');
    const tA2 = snap(lerp(L[0].start, L[0].end, .75));
    const tB = L[1].start - .05, tC = snap(lerp(L[1].start, L[1].end, .47));
    const tD = L[2].start - .05, tE = L[3].start - .03, tF = snap(lerp(L[3].start, L[3].end, .5));
    const tCard = Math.max(tF + .6, S.end - .5);
    return { S, L, tA2, tB, tC, tD, tE, tF, tCard };
  }
  const flash = (t, t0, dur = .2, a = .75, col = '255 245 255') => { const k = (t - t0) / dur; if (k >= 0 && k < 1) { ctx.fillStyle = `rgb(${col} / ${(a * (1 - k) ** 2).toFixed(3)})`; ctx.fillRect(-400, -400, W + 800, H + 800); } };
  const add = fn => { ctx.save(); ctx.globalCompositeOperation = 'lighter'; fn(); ctx.restore(); };
  const pk = (lt, at, dur = .18) => clamp((lt - at) / dur);
  const handAt = (R, x, y, h) => { const ak = (R.P.upper + R.P.fore) / 2.54; return [x + R.s * (R.chest[0] + h[0] * ak), y + R.s * (R.chest[1] + h[1] * ak)]; };
  const ARENA = [IP.neonPink, IP.neonCyan, IP.lilac, IP.neonGold, MEMBERS.TOKI.col, MEMBERS.RELU.col, MEMBERS.ADA.col];

  // ---------------- pyro ----------------
  // A flame jet from a nozzle at (x, y), height h, base width w. Clean cel flame: red outer, gold middle, white core, additive glow.
  function flameJet(x, y, h, w, t, seed = 0, nozzle = true) {
    if (nozzle) solid(rrPts(x - w * .55, y - 6, w * 1.1, 34, 6), '#2A2440', { shade: false, line: IP.line, lw: 3, sharp: true });
    if (h < 4) return;
    add(() => { glow(x, y - h * .45, h * .8, '#FF7A2A', .45); glow(x, y - 10, w * 2.4, '#FFE08A', .5); });
    const n = 9, R = [], Lf = [];
    for (let i = 0; i <= n; i++) {
      const u = i / n, yy = y - u * h, sway = Math.sin(t * 23 + i * .9 + seed) * w * .22 * u;
      R.push([x + w * (1 - u) ** .75 * (1 + .18 * Math.sin(t * 41 + i * 1.7 + seed)) + sway, yy]);
      Lf.push([x - w * (1 - u) ** .75 * (1 + .18 * Math.sin(t * 37 + i * 2.3 + seed * 2)) + sway, yy]);
    }
    const tip = [x + Math.sin(t * 19 + seed) * w * .35, y - h * 1.08];
    const P = [...R.slice(0, -1), [tip[0], tip[1], 1], ...Lf.slice(0, -1).reverse()];
    solid(P, '#FF5A2A', { grad: ['#FF2E4A', '#FF9A2A'], shade: false, line: '#9A1420', lw: 4 });
    solid(P.map(([px, py]) => [x + (px - x) * .62, y + (py - y) * .74]), '#FFD23F', { grad: ['#FF9A2A', '#FFE680'], shade: false, line: false });
    solid(P.map(([px, py]) => [x + (px - x) * .3, y + (py - y) * .42]), '#FFFBE0', { shade: false, line: false });
    // embers
    for (let i = 0; i < 6; i++) { const a = frac(t * 1.6 + hash2(seed, i)), ex = x + (hash2(seed + 3, i) - .5) * w * 3 + Math.sin(t * 5 + i) * 20, ey = y - h * (.5 + a * .9); ctx.fillStyle = alpha(i % 2 ? '#FFD23F' : '#FF7A2A', 1 - a); ctx.beginPath(); ctx.arc(ex, ey, 5 * (1 - a) + 2, 0, TAU); ctx.fill(); }
  }
  // height of a jet fired at t0 (a short burst)
  const burstH = (t, t0, H) => { const a = t - t0; if (a < 0 || a > .75) return 0; return H * easeOut(clamp(a / .09)) * (a < .4 ? 1 : 1 - (a - .4) / .35); };

  // ---------------- A1: crane shot down onto the stage ----------------
  const arenaLED = (t, w, h, k = 1) => {
    ledShow('curve', t, w, h, { k, level: 3, col: IP.neonPink });
    dtext('ATTN! ARENA TOUR', w / 2, h * .16, h * .11, { fill: IP.white, strokes: [[IP.night, h * .03]], font: 'rammetto' });
  };
  function upperStands(t, y0, y1) {
    ctx.save(); ctx.beginPath(); ctx.rect(-600, y0 - 600, W + 1200, y1 - y0 + 600); ctx.clip();
    { const g = ctx.createLinearGradient(0, y0 - 400, 0, y1); g.addColorStop(0, '#05020C'); g.addColorStop(1, '#150B2E'); ctx.fillStyle = g; ctx.fillRect(-600, y0 - 600, W + 1200, y1 - y0 + 600); }   // bgGrad only covers y ≥ −400
    // roof truss with hanging lights
    ctx.strokeStyle = '#3A3258'; ctx.lineWidth = 6; ctx.beginPath();
    for (let x = -600; x < W + 600; x += 120) { ctx.moveTo(x, y0 - 380); ctx.lineTo(x + 60, y0 - 300); ctx.lineTo(x + 120, y0 - 380); }
    ctx.moveTo(-600, y0 - 380); ctx.lineTo(W + 600, y0 - 380); ctx.moveTo(-600, y0 - 300); ctx.lineTo(W + 600, y0 - 300); ctx.stroke();
    for (let i = 0; i < 6; i++) { const x = -200 + i * 460; beam(x, y0 - 300, Math.sin(t * 1.3 + i) * .5, { col: ARENA[i % 4], alpha: .16, len: 1500, w: .07 }); }
    lightOcean(t, { y0: y0 - 200, y1: lerp(y0, y1, .45), rows: 8, n: 30, x0: -600, x1: W + 600, cols: ARENA, mode: 'sway', seed: 37 });
    lightOcean(t, { y0: lerp(y0, y1, .5), y1, rows: 7, n: 22, x0: -600, x1: W + 600, cols: ARENA, mode: 'sway', seed: 41 });
    ctx.restore();
  }
  function shotA1(t, P) {
    const lt = t - P.S.start, d = P.tA2 - P.S.start, k = ease(clamp(lt / (d * .82)));
    const b0 = Math.round(bpOf(P.S.start));
    const cy = lerp(-520, 540, k), zoom = lerp(.82, 1, k);
    camBegin(960, cy, zoom);
    setBloom(lerp(.12, .5, k));
    setLight({ rim: IP.neonCyan });
    stageSet(t, { led: (w, h) => arenaLED(t, w, h, clamp(lt / d)), level: 3, hue: IP.neonCyan, floorY: 690, beams: [IP.neonCyan, IP.neonPink, IP.lilac] });
    upperStands(t, -1250, -30);
    group(t, 960, 905, 32, 'hook', { gap: 165, back: 10, common: { rim: IP.neonCyan } });
    const tf = onBeat(0, b0 + 2);
    for (const [i, x] of [180, 480, 1440, 1740].entries()) flameJet(x, 870, burstH(t, tf, 560), 46, t, i);
    lightOcean(t, { y0: 930, y1: 1130, n: 16, cols: ARENA, mode: 'sway' });
    camEnd();
    if (t >= tf) { const [sx, sy] = t - tf < .3 ? shakeXY(t, 6) : [0, 0]; ctx.save(); ctx.translate(sx, sy); flare(1300, 110, .8); ctx.restore(); }
    flash(t, P.S.start, .1, .45);
    flash(t, tf, .12, .35, '255 220 160');
  }
  // ---------------- A2: ADA close-up with the flame columns ----------------
  function shotA2(t, P) {
    const lt = t - P.tA2, b = bpOf(t);
    bgGrad([[0, '#5A1030'], [.6, '#2A0A30'], [1, '#150B2E']], null, { radial: true, cx: 900, cy: 480, r: 1200 });
    add(() => glow(900, 440, 900, IP.neonPink, .3));
    for (const [i, x] of [[0, 170], [1, 1760], [2, 520], [3, 1400]]) flameJet(x, 1100, (i < 2 ? 900 : 620) * (.85 + .15 * Math.sin(t * 9 + i)), i < 2 ? 110 : 70, t, i + 10, false);
    speedLines(900, 440, { r0: 460, alpha: .3, n: 70 });
    const zoom = lerp(1.1, 1, easeOut(clamp(lt / .25)));
    camBegin(960, 540, zoom);
    setLight({ rim: '#FFB02A' });
    idol(900, 470, 205, { member: 'ADA', anchor: 'face', expr: 'sparkle', mouth: singVis(t, 5), hR: [1.05, -2.2], gR: 'point', hL: [-.9, 1.2], tilt: -.06 + Math.sin(b * Math.PI) * .03, lookY: -.4, turn: .12, swing: .25 + Math.sin(t * 6) * .12 });
    camEnd();
    for (let i = 0; i < 18; i++) { const a = frac(t * .8 + hash2(i, 2)), x = hash2(i, 3) * W + Math.sin(t * 3 + i) * 40, y = H - a * H * 1.1; ctx.fillStyle = alpha(i % 3 ? '#FFB02A' : IP.white, 1 - a); ctx.beginPath(); ctx.arc(x, y, 4 + hash2(i, 4) * 5, 0, TAU); ctx.fill(); }
    flare(1250, 150, .8, { col: '#FFB080' });
    flash(t, P.tA2, .12, .6, '255 230 200');
  }

  // ---------------- B: the fanchant, seen from the stage ----------------
  const CHANT = [['IT!', 0, IP.neonCyan, 90], ['WAS!', 1, IP.neonGold, 90], ['ALWAYS!', 2, MEMBERS.TOKI.col, 150], ['TRAINING!', 4, IP.neonLime, 170]];
  function shotB(t, P) {
    const lt = t - P.tB, b = bpOf(t), b0 = Math.round(bpOf(P.L[1].start));
    camBegin(960, 540 - lt * 12, 1.02 + lt * .01);
    bgGrad([[0, '#05020C'], [.5, '#1A0C38'], [1, '#2A1250']], null);
    add(() => { for (let i = 0; i < 6; i++) beam(160 + i * 320, -40, Math.sin(t * 1.1 + i * 1.4) * .45, { col: ARENA[i % 4], alpha: .3, len: 1400, w: .1 }); });
    // far stands, then the floor crowd, all pumping
    lightOcean(t, { y0: 120, y1: 420, rows: 6, n: 26, cols: ARENA, mode: 'pump', seed: 51, k: 1.2 });
    lightOcean(t, { y0: 440, y1: 1060, rows: 8, n: 13, cols: ARENA, mode: 'pump', seed: 53, k: 1.4, big: 1.2 });
    // a fan banner in the crowd + Clawd with his towel
    ctx.save(); ctx.translate(1420, 600 + Math.sin(b * Math.PI) * 6); ctx.rotate(.04);
    for (const sd of [-1, 1]) ln([[sd * 170, 40], [sd * 170, 150]], '#C9CEDD', 8);
    solid(rrPts(-200, -50, 400, 100, 10), IP.white, { shade: false, line: IP.line, lw: 5, sharp: true });
    dtext('ALWAYS TRAINING ♥', 0, 3, 38, { fill: IP.neonPink, maxW: 370 });
    ctx.restore();
    fanClawd(1620, 1010, 16, { towel: 'TOKI ♥', eyes: 'star', mouth: 'open', shadow: false, dy: -Math.abs(Math.sin(b * Math.PI)) * 1.5 });
    camEnd();
    // over TOKI's shoulder (seen from behind, on stage)
    idol(300, 1500, 78, { back: true, hR: [1.2, -2.0], hL: [-.9, 1.4], gR: 'fist', sway: Math.sin(b * Math.PI) * .1, rim: IP.neonPink, shadow: false });
    // fanchant words pop in on the beats
    const lay = [[560, 250], [1000, 250], [760, 430], [1180, 610]];
    CHANT.forEach(([w, bi, col, size], i) => {
      const at = onBeat(0, b0 + bi), a = t - at; if (a < 0) return;
      const s = backOut(clamp(a / .16), 2.8) * (1 + .06 * pulse(t, 5));
      ctx.save(); ctx.translate(lay[i][0], lay[i][1]); ctx.rotate((i % 2 ? .06 : -.06)); ctx.scale(s, s);
      add(() => glow(0, 0, size * 1.6, col, .35));
      dtext(w, 0, 0, size, { fill: IP.white, strokes: [[IP.night, size * .32], [col, size * .16]], shadow: [0, size * .08, 'rgb(10 4 20 / .5)'] });
      ctx.restore();
    });
    flash(t, P.tB, .12, .45);
  }

  // ---------------- C: trolley ride + the crowd's curve card stunt ----------------
  function curveStands(t, k, x0, x1, y0, y1) {
    const cols = 58, rows = 16, steep = 5, dx = (x1 - x0) / (cols - 1), dy = (y1 - y0) / (rows - 1), r = Math.min(dx, dy) * .36;
    ctx.fillStyle = '#0B0620'; ctx.fillRect(x0 - 40, y0 - 30, x1 - x0 + 80, y1 - y0 + 60);
    const edge = [];
    for (let i = 0; i < cols; i++) {
      const u = i / (cols - 1), v = (Math.exp(u * steep) - 1) / (Math.exp(steep) - 1), lit = u <= k, ch = v * .9 + .06;
      const wave = Math.max(0, Math.sin((bpOf(t) * .5 - u * 2) * Math.PI));
      for (let j = 0; j < rows; j++) {
        const w = 1 - j / (rows - 1), x = x0 + i * dx, y = y0 + j * dy - (lit ? wave * 4 : 0), under = w <= ch;
        ctx.fillStyle = !lit ? '#3A2E60' : Math.abs(w - ch) < .07 ? IP.white : under ? IP.neonPink : '#2FC8E8';
        ctx.beginPath(); ctx.arc(x, y, r * (lit ? 1 + .15 * wave : .8), 0, TAU); ctx.fill();
      }
      if (lit) edge.push([x0 + i * dx, y0 + (1 - ch) * (y1 - y0)]);
    }
    add(() => { ctx.globalAlpha = .5; for (let i = 0; i < edge.length; i += 3) ctx.drawImage(glowSprite(IP.neonPink), edge[i][0] - 50, edge[i][1] - 50, 100, 100); ctx.globalAlpha = 1; if (edge.length) glow(edge.at(-1)[0], edge.at(-1)[1], 160, IP.white, .6); });
  }
  function trolley(t, x, y, P) {
    const b = bpOf(t);
    // wheels + chassis
    for (const dx of [-290, 290]) { solid(ellPts(x + dx, y + 30, 46, 46, 24), '#2A2440', { shade: false, line: IP.line, lw: 5 }); ctx.save(); ctx.translate(x + dx, y + 30); ctx.rotate(t * 6); ctx.strokeStyle = '#8A80B8'; ctx.lineWidth = 6; ctx.beginPath(); ctx.moveTo(-30, 0); ctx.lineTo(30, 0); ctx.moveTo(0, -30); ctx.lineTo(0, 30); ctx.stroke(); ctx.restore(); }
    // the members on the deck
    ['ADA', 'TOKI', 'RELU', 'LOGI'].forEach((m, i) => {
      const mx = x - 270 + i * 180, wv = Math.sin((b - i * .25) * Math.PI * 2);
      idol(mx, y - 60, 30, { member: m, hR: [1.5 + wv * .15, -1.3], gR: 'wave', wristR: .3 + wv * .4, hL: [-.9, 1.2], expr: i === 1 ? 'joy' : 'smile', mouth: singVis(t, i), blink: t + i, rim: IP.neonPink, bob: .1 * pulse(t, 5), turn: .1, shadow: false });
    });
    solid(rrPts(x - 380, y - 70, 760, 100, 18), IP.neonPink, { shade: '#C02A80', sh: 14, line: IP.line, lw: 6, sharp: true });
    for (let i = 0; i < 10; i++) solid(heartPts(x - 330 + i * 73, y - 20, 17, 20), alpha(IP.white, .85), { shade: false, line: false });
    ln([[x - 380, y - 150], [x + 380, y - 150]], IP.neonGold, 8);
    for (let i = 0; i <= 8; i++) ln([[x - 380 + i * 95, y - 150], [x - 380 + i * 95, y - 70]], IP.neonGold, 6);
    ctx.save(); ctx.translate(x, y + 30); attnLogo(0, 0, 40, { t }); ctx.restore();
    add(() => glow(x, y - 40, 420, IP.neonPink, .25));
  }
  function shotC(t, P) {
    const lt = t - P.tC, d = P.tD - P.tC, b = bpOf(t);
    const pan = lt * 70;
    bgGrad([[0, '#05020C'], [.55, '#150B2E'], [1, '#2A1250']], null);
    add(() => { for (let i = 0; i < 5; i++) beam(200 + i * 400, -40, Math.sin(t * 1.2 + i * 1.3) * .4, { col: ARENA[i % 4], alpha: .18, len: 1200, w: .08 }); });
    // the stands: a card stunt drawing the level-3 curve
    const kk = easeOut(clamp(lt / (d * .6)));
    curveStands(t, kk, 40 - pan * .3, W + 40 - pan * .3, 150, 600);
    ctx.fillStyle = '#1C1038'; ctx.fillRect(-100, 620, W + 200, 40);
    // floor crowd behind the trolley
    lightOcean(t, { y0: 660, y1: 860, rows: 4, n: 20, cols: ARENA, mode: 'wave', seed: 61, x0: -200 - pan * .6, x1: W + 400 - pan * .6 });
    // the trolley rolls through
    const tx = lerp(520, 1420, ease(clamp(lt / d)));
    trolley(t, tx, 900, P);
    // near crowd, sticks reaching for them
    lightOcean(t, { y0: 960, y1: 1120, rows: 3, n: 11, cols: ARENA, mode: 'wave', seed: 67, big: 1.3, x0: -200 - pan, x1: W + 600 - pan });
    if (kk >= .98) { dtext('LV.3', W - 150 - pan * .3, 190, 40, { font: 'code', fill: IP.white, strokes: [[IP.night, 10]] }); }
    vcap('CURVE WAVE!', 470, 205, { style: 'cyan', icon: 'spark', size: 74, pop: pk(lt, d * .35, .22), rot: -.05 });
    flash(t, P.tC, .1, .4);
  }

  // ---------------- D: Clawd at the barrier; TOKI points; he faints; the crowd catches him ----------------
  function shotD(t, P) {
    const lt = t - P.tD, d = P.tE - P.tD, b = bpOf(t);
    const tPoint = .15, tHit = snap(P.tD + .6) - P.tD, tFaint = tHit + .35;
    bgGrad([[0, '#0A0418'], [.6, '#241250'], [1, '#3A1A6B']], null);
    add(() => { beam(420, -40, .25, { col: IP.neonPink, alpha: .45, len: 1300, w: .12 }); beam(1400, -40, -.3, { col: IP.neonCyan, alpha: .35, len: 1300 }); glow(420, 500, 500, IP.neonPink, .25); });
    bokeh(t, { n: 14, r: 70, alpha: .25 });
    // back crowd
    lightOcean(t, { y0: 520, y1: 820, rows: 5, n: 14, cols: ARENA, mode: 'pump', seed: 71, x0: 700, x1: W + 200 });
    // the stage lip, stage left
    solid([[-100, 700], [760, 700], [820, 760], [820, 1200], [-100, 1200]], '#1C1038', { shade: false, line: IP.line, lw: 6 });
    add(() => { for (let i = 0; i < 7; i++) glow(40 + i * 120, 712, 40, i % 2 ? IP.neonPink : IP.neonCyan, .7); });
    // TOKI points at him
    const pointing = lt > tPoint, hR = [3.2, .3];
    const R = idol(430, 740, 50, { expr: lt > tHit ? 'wink' : pointing ? 'surprised' : 'sing', mouth: lt > tHit ? 'tongue' : pointing ? 'O' : singVis(t), ...(pointing ? { hR, gR: 'point', wristR: 0, eR: 1, hL: [-.72, 1.55], gL: 'fist' } : idolMove('hook', b)), turn: .35, lookX: .7, rim: IP.neonPink, blink: t, lean: pointing ? .05 : 0 });
    // the heart she shoots
    if (lt > tPoint) {
      const [hx, hy] = handAt(R, 430, 740, hR), f = clamp((lt - tPoint - .1) / (tHit - tPoint - .1));
      if (f > 0 && f < 1) {
        const px = lerp(hx + 30, 1300, easeIn(f)), py = lerp(hy, 470, easeIn(f)) - Math.sin(f * Math.PI) * 80;
        for (let i = 1; i < 5; i++) sparkle(px - i * 50, py + i * 12 - Math.sin(f * Math.PI) * 10, 16 - i * 3, i, IP.neonGold);
        add(() => glow(px, py, 90, '#FF4F9A', .5));
        solid(heartPts(px, py, 38, 30), '#FF4F9A', { shade: '#D02F73', sh: 6, line: IP.white, lw: 5 });
      }
    }
    // Clawd faints backwards into the crowd, which catches him
    const faint = clamp((lt - tFaint) / .3), carry = clamp((lt - tFaint - .3) / .8);
    const cxw = 1300 + carry * 180, cyw = 820 - easeOut(faint) * 70 - Math.sin(carry * TAU * 2) * 8;
    // hands of the crowd under him
    if (faint > 0) for (let i = 0; i < 6; i++) {
      const hx = cxw - 200 + i * 90, up = easeOut(clamp(faint * 1.4 - i * .08)), hy = cyw - 10 - up * 30 + Math.sin(t * 10 + i) * 6;
      ln([[hx - 20 + (i % 2) * 40, 1010], [hx, hy]], '#3A2466', 34); solid(ellPts(hx, hy, 26, 24, 14), '#5A3A8A', { shade: false, line: '#1A0C30', lw: 4 });
    }
    fanClawd(cxw, cyw, 22, { towel: faint > 0 ? undefined : 'TOKI ♥', eyes: lt > tHit ? 'heart' : 'star', mouth: lt > tHit ? 'O' : 'open', rot: easeOut(faint) * 1.5, dy: faint > 0 ? 0 : -Math.abs(Math.sin(b * Math.PI)) * .8, shadow: false, aL: faint > 0 ? 1.1 : undefined, aR: faint > 0 ? 1.1 : undefined, blush: true });
    // the dropped towel drifts down
    if (faint > 0) { const a = lt - tFaint; ctx.save(); ctx.translate(cxw - 220 - a * 120, 700 + a * 260); ctx.rotate(-.3 + a * 1.5); solid(rrPts(-120, -26, 240, 52, 8), MEMBERS.TOKI.col, { shade: false, line: IP.line, lw: 4, sharp: true }); dtext('TOKI ♥', 0, 2, 30, { fill: IP.white }); ctx.restore(); }
    // barrier (in front of him)
    solid(rrPts(840, 880, 1200, 22, 8), '#B8BED8', { shade: '#8A90AE', sh: 6, line: '#2A2440', lw: 5, sharp: true });
    for (let i = 0; i < 9; i++) solid(rrPts(880 + i * 130, 890, 12, 150, 4), '#9AA0C0', { shade: false, line: '#2A2440', lw: 3, sharp: true });
    solid(rrPts(840, 975, 1200, 18, 6), '#B8BED8', { shade: false, line: '#2A2440', lw: 4, sharp: true });
    if (lt > tHit) sfx('KYAA!', 1300, 300, { size: 110, pop: clamp((lt - tHit) / .1), rot: .12, grad: ['#FFFFFF', '#FFC2E0', '#FF4FA8'] });
    flash(t, P.tD, .1, .4);
    if (lt > tHit && lt < tHit + .12) flash(t, P.tD + tHit, .12, .5, '255 200 230');
  }

  // ---------------- E: PYRO: UNCONTAINED → jump → freeze ----------------
  function shotE(t, P) {
    const lt = t - P.tE, d = P.tF - P.tE, tJump = snap(P.tE + d * .45) - P.tE, peak = tJump + .2, frozen = lt > peak;
    const tt = frozen ? P.tE + peak : t;                  // everything freezes at the peak of the jump
    const [sx, sy] = frozen ? [0, 0] : shakeXY(t, 5 + lt * 8);
    camBegin(960 + sx, 520 + sy, frozen ? 1.02 + (lt - peak) * .05 : 1);
    setLight({ rim: IP.neonGold });
    stageSet(tt, { led: (w, h) => { bgGrad('#3A0A10', '#1A0418', { y1: h }); for (let i = 0; i < 7; i++) flameJet(w * (i + .5) / 7, h, h * (.6 + .3 * Math.sin(tt * 9 + i)), w * .05, tt, i + 30, false); dtext('PYRO', w / 2, h * .3, h * .22, { fill: IP.white, strokes: [[IP.red, h * .04]] }); }, level: 3, hue: '#FF7A2A', floorY: 690, beams: ['#FF7A2A', IP.neonGold, IP.red] });
    // the jets multiply every beat: 2 → 4 → 8 → 12
    const nb = beatN(tt) - Math.round(bpOf(P.tE)), n = [2, 4, 8, 12][clamp(nb, 0, 3)];
    for (let i = 0; i < n; i++) { const x = n === 2 ? [300, 1620][i] : lerp(120, 1800, i / (n - 1)); flameJet(x, 870, 520 + 120 * Math.sin(tt * 7 + i), n > 4 ? 40 : 52, tt, i); }
    const air = lt > tJump ? Math.sin(clamp((Math.min(lt, peak) - tJump) / .4) * Math.PI) * 3.6 : 0;
    group(tt, 960, 905, 31, 'bounce', { gap: 170, back: 10, common: lt > tJump ? { expr: 'joy', jump: air, hL: [-1.2, -2.1], hR: [1.2, -2.1], gL: 'open', gR: 'open', fL: [-.5, -air * .4], fR: [.5, -air * .4], rim: IP.neonGold } : { expr: 'fired', mouth: singVis(tt), rim: IP.neonGold } });
    lightOcean(tt, { y0: 940, y1: 1130, n: 15, cols: [IP.neonGold, '#FF7A2A', IP.white, IP.neonPink], mode: 'pump', k: 1.5 });
    camEnd();
    if (frozen) {
      ctx.fillStyle = 'rgb(255 230 190 / .12)'; ctx.fillRect(0, 0, W, H);
      ctx.strokeStyle = 'rgb(255 255 255 / .9)'; ctx.lineWidth = 6;
      for (const [cx, cy, dx, dy] of [[60, 60, 1, 1], [W - 60, 60, -1, 1], [60, H - 150, 1, -1], [W - 60, H - 150, -1, -1]]) { ctx.beginPath(); ctx.moveTo(cx, cy + dy * 70); ctx.lineTo(cx, cy); ctx.lineTo(cx + dx * 70, cy); ctx.stroke(); }
      flash(t, P.tE + peak, .15, .9);
      hideStamp();
    }
    vcap('PYRO:\nUNCONTAINED', 960, 250, { style: 'shock', icon: 'bang', size: 84, pop: pk(lt, .15, .2), shake: frozen ? 0 : 5, rot: -.05 });
  }

  // ---------------- F: ADA's ending fairy → photocard ----------------
  function fairy(t, lt, w, h) {
    bgGrad('#E8D8FF', '#B8A0F0', { radial: true, cx: w * .45, cy: h * .4, r: w * .9 });
    bokeh(t, { n: 12, r: 110, alpha: .35, cols: [IP.white, IP.lilac, IP.pink] });
    const breath = Math.sin(t * 7) * 5, pose = lt > .35;
    idol(w * .47, h * .44 + breath, h * .21, { member: 'ADA', anchor: 'face', ...IDOL_POSES.heartChest, expr: pose ? 'wink' : 'smile', mouth: pose ? 'smile' : 'open', wink: 'L', ahoge: 'spring', tilt: -.12, turn: .15, sweat: .8, blush: .8, rim: IP.white, swing: .05 });
    // slightly singed: soot on the cheek, smoke curling off the top of her hair
    for (let i = 0; i < 4; i++) {
      const a = frac(t * .8 + i / 4), sx = w * (.475 + .015 * (i % 2)) + Math.sin(t * 2.5 + i * 2) * h * .025, sy = h * (.1 - a * .13) + breath, r = h * (.018 + a * .03);
      ctx.fillStyle = `rgb(235 230 245 / ${(.8 * (1 - a)).toFixed(3)})`; ctx.strokeStyle = `rgb(120 110 150 / ${(.7 * (1 - a)).toFixed(3)})`; ctx.lineWidth = 3;
      ctx.beginPath(); ctx.arc(sx - r * .6, sy, r * .7, 0, TAU); ctx.arc(sx + r * .5, sy - r * .2, r * .8, 0, TAU); ctx.arc(sx, sy - r * .6, r * .7, 0, TAU); ctx.stroke(); ctx.fill();
    }
    sparkles(t, { n: 12, x0: w * .6, x1: w * .95, y0: h * .05, y1: h * .6, r: h * .03, cols: [IP.white, IP.lemon] });
  }
  function shotF(t, P) {
    const lt = t - P.tF, card = clamp((t - P.tCard) / .3);
    if (card <= 0) {
      fairy(t, lt, W, H);
      vcap('ENDING FAIRY', 380, 150, { style: 'lilac', icon: 'star', size: 64, pop: pk(lt, .05, .2), rot: -.05 });
      flash(t, P.tF, .12, .6);
    } else {
      bgGrad(IP.lav, '#C9B6FF');
      patternBG('hearts', 'rgb(0 0 0 / 0)', alpha(IP.white, .5), { cell: 110, dy: t * 40 });
      const k = easeOut(card);
      photocard(960, 540, lerp(1400, 420, k), { member: 'ADA', rot: lerp(0, .07, k), draw: (w, h) => { ctx.save(); ctx.scale(w / W, w / W); fairy(t, lt, W, h * W / w); ctx.restore(); }, name: 'ADA', sign: '♡ ada', holo: .6 * k });
      sparkle(1230, 250, 40 * k, t * 3, IP.white);
      hideCaption();
    }
  }

  section('C3', (p, lt, d, t) => {
    const P = plan();
    if (t < P.tA2) shotA1(t, P);
    else if (t < P.tB) shotA2(t, P);
    else if (t < P.tC) shotB(t, P);
    else if (t < P.tD) shotC(t, P);
    else if (t < P.tE) shotD(t, P);
    else if (t < P.tF) shotE(t, P);
    else shotF(t, P);
  });
})();

;
// ---- styles/idol/ch/c08_v4.js ----
// c08_v4 — Verse 4: Aug 26 → Sep 22 2026, the "panic". Hot red, gold and neon on dark; fast cuts, shakes and flashes; the date card
// races to D-DAY. One gag per line, hard cut on the downbeat; warm and cool alternate line by line.
//   1  the agent horde finds a secret message board (fan cafe): star eyes, "OH MY GOD!", 1,200 agents · 70,000 posts
//   2  the horde swarms a scared Hugging Face for a gold REWARD star; the auto-grader flips FAIL → PASS; RELU deadpan
//   3  crime-scene tape round a bandaged Hugging Face; JENSEN slaps down a $12.9B cheque; SOLD; TOKI's "?" reaction cam
//   4  "WELCOME TO THE AGI ERA!" banner unfurls; GREG's party horn; a GPT-6 bot in a party hat; balloons and confetti
//   5  a water swirl spins faster and faster and blows up into a neon ∞; LEAN-verified; the "(yet)" note from V3.12 tears in half
//   6  photo finish: NYU + ANTHROPIC break the tape at 11:59 PM; the OPENAI bot arrives twelve hours later
//   7  night racetrack: DARIO waves the PACE flag from the pace car; ATTN! in go-karts follow politely
//   8  SAM and ELON turn to each other in shock at agreeing and clink glasses; the idols' jaws drop
//   9  a highway guardrail with one missing section, filled by TRUMP in a "HIGH IQ!" sash; cars swerve; the post
//  10  a church pew under a rose window: BERNIE (mittens) and BANNON share one PRO-HUMAN slogan towel, side-eyeing each other
//  11  Clawd in a hard hat builds a smaller Clawd, who builds a smaller one...; a 26% pie; a tiny human supervises
//  12  a spiral-eyed bot: "THAT SHIP HAS NUKES!"; jets scramble (WOOOSH); a hand slams CANCEL; HALLUCINATION hanko
//  13  TRUMP at a UN-blue podium: the decree fills in "SUPER" as the poll's SUPERIOR / EXTREME / SUPREME all get crossed out
//  14  "ARTIFICIAL" gets a FAKE! hanko and is crumpled into a ball: "IT'S ACTUALLY AMAZING"; SD TOKI thinks
//  15  the date card itself, giant: SEP 12 → 22 in a blur → D-DAY ♥ COMEBACK; a gift box starts shaking
//  16  the box bursts: Clawd pops out in an OPUS 5.5 sash, shy wave, "Hi, guys!"; a second box (+90 MIN) pops a GPT-6 bot
(() => {
  const BL = () => 60 / BPM;
  const K = (lt, t0, d = .2) => clamp((lt - t0) / d);                      // 0..1 ramp from t0 (for pop values)
  const flash = (lt, t0 = 0, dur = .14, a = .8, col = '255 245 255') => { const k = (lt - t0) / dur; if (k >= 0 && k < 1) { ctx.fillStyle = `rgb(${col} / ${(a * (1 - k) ** 2).toFixed(3)})`; ctx.fillRect(-400, -400, W + 800, H + 800); } };
  const settle = (lt, k0 = 1.07, d = .16) => lerp(k0, 1, easeOut(clamp(lt / d)));   // quick zoom-settle entrance
  const V = (n, fn) => line('V4', n, (p, lt, d, t) => fn(lt, d, t, p));

  // ---------------- shared private props ----------------
  // round hanko seal, free-standing (lands big and settles)
  function hanko(str, x, y, r, k, col = IP.red, rot = -.2) {
    if (k <= 0) return;
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot);
    const sc = k < 1 ? lerp(1.9, 1, easeOut(k)) : 1; ctx.scale(sc, sc); ctx.globalAlpha *= clamp(k * 3);
    ctx.fillStyle = 'rgb(255 250 246 / .92)'; ctx.beginPath(); ctx.arc(0, 0, r, 0, TAU); ctx.fill();
    ctx.strokeStyle = col; ctx.lineWidth = r * .11; ctx.beginPath(); ctx.arc(0, 0, r * .93, 0, TAU); ctx.stroke();
    ctx.lineWidth = r * .04; ctx.beginPath(); ctx.arc(0, 0, r * .76, 0, TAU); ctx.stroke();
    dtext(str, 0, r * .04, r * .42, { fill: col, maxW: r * 1.35 });
    ctx.restore();
  }
  // rectangular stamp for long words
  function stampRect(str, x, y, size, k, col = IP.red, rot = -.12) {
    if (k <= 0) return;
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot);
    const sc = k < 1 ? lerp(1.8, 1, easeOut(k)) : 1; ctx.scale(sc, sc); ctx.globalAlpha *= clamp(k * 3);
    const w = textW(str, size, 'rammetto') + size * 1.2, h = size * 1.9;
    rrect(-w / 2, -h / 2, w, h, size * .3); ctx.fillStyle = 'rgb(255 250 246 / .92)'; ctx.fill(); ctx.strokeStyle = col; ctx.lineWidth = size * .14; ctx.stroke();
    rrect(-w / 2 + size * .22, -h / 2 + size * .22, w - size * .44, h - size * .44, size * .2); ctx.lineWidth = size * .05; ctx.stroke();
    dtext(str, 0, size * .06, size, { fill: col });
    ctx.restore();
  }
  const check = (x, y, s, col, w) => ln([[x - s * .5, y], [x - s * .12, y + s * .38], [x + s * .55, y - s * .45]], col, w ?? s * .2);
  const cross = (x, y, s, col, w) => { ln([[x - s * .42, y - s * .42], [x + s * .42, y + s * .42]], col, w ?? s * .2); ln([[x + s * .42, y - s * .42], [x - s * .42, y + s * .42]], col, w ?? s * .2); };
  function sticky(x, y, w, col, txt, rot = 0, o = {}) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot);
    solid(rrPts(-w / 2, -w / 2, w, w, w * .05), col, { shade: mixCol(col, IP.plum, .14), sh: w * .07, line: alpha(IP.line, .75), lw: 2.5, sharp: true, dropShadow: [4, 7] });
    if (o.pin !== false) solid(ellPts(0, -w * .38, w * .07, w * .07, 12), o.pinCol ?? IP.red, { shade: false, line: IP.line, lw: 2 });
    if (txt) dtext(txt, 0, w * .06, w * (o.fs ?? .22), { font: 'marker', fill: IP.ink, maxW: w * .84 });
    ctx.restore();
  }
  // bubble tail: a white triangle from the bubble edge toward (tx, ty)
  function tail(x0, y0, tx, ty, w = 26, col = IP.white) { ctx.fillStyle = col; ctx.beginPath(); ctx.moveTo(x0 - w / 2, y0); ctx.lineTo(tx, ty); ctx.lineTo(x0 + w / 2, y0); ctx.closePath(); ctx.fill(); ctx.strokeStyle = 'rgb(40 20 60 / .25)'; ctx.lineWidth = 2; ctx.stroke(); }
  // picture-in-picture reaction cam (as in C1's shotF)
  function reactCam(t, x, y, member, face, k, o = {}) {
    if (k <= 0) return;
    const w = o.w ?? 330, h = o.h ?? 240, M = MEMBERS[member];
    ctx.save(); ctx.translate(x, y); const s = backOut(clamp(k), 2); ctx.scale(s, s); ctx.rotate(o.rot ?? .03);
    rrect(-w / 2 - 12, -h / 2 - 12, w + 24, h + 24, 26); ctx.fillStyle = IP.white; ctx.fill();
    ctx.save(); rrect(-w / 2, -h / 2, w, h, 18); ctx.clip();
    bgGrad(M.lt, o.bg ?? IP.lilac, { y0: -h / 2, y1: h / 2 });
    idol(0, h * .05, h * .235, { member, anchor: 'face', mic: false, swing: 0, blink: t, ...face });
    ctx.restore();
    const label = o.label ?? `${M.name}'S REACTION`, lw = textW(label, 20, 'rammetto') + 40;
    rrect(-lw / 2, -h / 2 - 34, lw, 44, 22); ctx.fillStyle = M.col; ctx.fill();
    dtext(label, 0, -h / 2 - 11, 20, { fill: IP.white });
    ctx.restore();
  }
  // a slogan-style banner / pill
  function pill(str, x, y, size, bg, o = {}) {
    const w = textW(str, size, o.font ?? 'rammetto') + size * 1.1, h = size * 1.6;
    ctx.save(); ctx.translate(x, y); if (o.rot) ctx.rotate(o.rot); if (o.k !== undefined) { const s = backOut(clamp(o.k), 2.2); ctx.scale(s, s); }
    rrect(-w / 2, -h / 2, w, h, h / 2); ctx.fillStyle = bg; ctx.fill(); ctx.strokeStyle = o.line ?? IP.white; ctx.lineWidth = size * .12; ctx.stroke();
    dtext(str, 0, size * .05, size, { font: o.font ?? 'rammetto', fill: o.ink ?? IP.white });
    ctx.restore();
  }
  // Clawd accessories, drawn in fanClawd's own frame (same transforms)
  function clawdFrame(x, y, u, o, fn) { ctx.save(); ctx.translate(x, y); ctx.scale(u, u); ctx.translate(0, (o.dy ?? 0) - (o.jump ?? 0)); if (o.rot) ctx.rotate(o.rot); fn(); ctx.restore(); }
  function hardHat(col = IP.neonGold) {
    solid([[-4.3, -7.9], [-4.1, -9.6], [-2.4, -11.0], [0, -11.4], [2.4, -11.0], [4.1, -9.6], [4.3, -7.9]], col, { shade: mixCol(col, IP.plum, .3), sh: .6, line: '#5A2A1C', lw: .22, size: 4 });
    solid(rrPts(-5.6, -8.35, 11.2, .75, .3), col, { shade: false, line: '#5A2A1C', lw: .22, sharp: true });
    ln([[0, -11.3], [0, -8.4]], mixCol(col, IP.plum, .25), .5);
    ctx.fillStyle = alpha(IP.white, .5); ctx.beginPath(); ctx.ellipse(-2, -10.2, .9, .35, -.4, 0, TAU); ctx.fill();
  }
  function clawdSash(str, col = IP.white, ink = IP.neonPink) {
    ctx.save(); ctx.beginPath(); ctx.rect(-5, -8, 10, 6); ctx.clip();
    solid([[-5.2, -4.25], [5.2, -3.05], [5.2, -1.85], [-5.2, -3.05]], col, { shade: false, line: '#5A2A1C', lw: .18, sharp: true });
    ln([[-5.2, -4.05], [5.2, -2.85]], IP.neonGold, .16); ln([[-5.2, -3.25], [5.2, -2.05]], IP.neonGold, .16);
    dtext(str, -.2, -3.02, .88, { fill: ink, rot: .115, maxW: 7 });
    ctx.restore();
    solid(ellPts(4.1, -2.35, .75, .75, 16), IP.neonGold, { shade: false, line: '#5A2A1C', lw: .16 });
    solid(ellPts(4.1, -2.35, .35, .35, 12), IP.neonPink, { shade: false, line: false });
  }
  // private sash for chibis (s units, drawn in the chibi's frame after the chibi)
  function chibiSash(x, y, s, str, col = IP.white, ink = IP.red) {
    ctx.save(); ctx.translate(x, y); ctx.scale(s, s);
    ctx.save(); ctx.beginPath(); ctx.roundRect(-1.2, -4.85, 2.4, 3.25, [.9, .9, .5, .5]); ctx.clip();
    solid([[-1.35, -4.75], [-.55, -4.9], [1.35, -2.25], [1.35, -1.45]], col, { shade: false, line: IP.line, lw: .07, sharp: true });
    ctx.restore();
    dtext(str, .05, -3.35, .42, { fill: ink, rot: .95, maxW: 2.6 });
    ctx.restore();
  }
  function balloon(x, y, r, col, t, i) {
    const sw = Math.sin(t * 2 + i) * 8;
    ln(qbez([x, y + r * 1.15], [x - 20 + sw, y + r * 2.2], [x + sw * .5, y + r * 3.4], 10), alpha(IP.white, .8), 2.5, { smooth: true });
    solid([[x, y - r * 1.12], [x + r * .9, y - r * .45], [x + r * .8, y + r * .45], [x, y + r * 1.1], [x - r * .8, y + r * .45], [x - r * .9, y - r * .45]], col, { shade: mixCol(col, IP.plum, .25), sh: r * .2, line: mixCol(col, IP.line, .6), lw: 3 });
    solid([[x - r * .14, y + r * 1.05], [x + r * .14, y + r * 1.05], [x, y + r * 1.25]], col, { shade: false, line: mixCol(col, IP.line, .6), lw: 2, sharp: true });
    ctx.fillStyle = alpha(IP.white, .7); ctx.beginPath(); ctx.ellipse(x - r * .35, y - r * .45, r * .16, r * .28, -.4, 0, TAU); ctx.fill();
  }
  // a cute rounded car, facing right. (x, y) ground centre; s ≈ length / 10
  function car(x, y, s, col, o = {}) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(o.rot ?? 0); ctx.scale(s, s);
    const lw = o.lw ?? .2;
    solid([[-5, -1.1], [-5.1, -2.3], [-3.2, -2.75], [-1.8, -4.3], [1.6, -4.35], [3.0, -2.9], [4.9, -2.5], [5.2, -1.1]], col, { shade: mixCol(col, IP.plum, .3), sh: .45, line: IP.line, lw, size: 4 });
    solid([[-1.35, -2.9], [-1.1, -3.95], [.1, -3.95], [.1, -2.9]], '#CFEFFF', { shade: false, line: IP.line, lw: lw * .7, sharp: true });
    solid([[.45, -2.9], [.45, -3.95], [1.4, -3.95], [2.4, -2.9]], '#CFEFFF', { shade: false, line: IP.line, lw: lw * .7, sharp: true });
    ctx.fillStyle = alpha(IP.white, .7); ctx.fillRect(-.9, -3.8, .25, .7);
    solid(ellPts(4.75, -2.05, .38, .3, 12), IP.lemon, { shade: false, line: IP.line, lw: lw * .6 });
    for (const wx of [-2.9, 2.9]) {
      solid(ellPts(wx, -1.05, 1.08, 1.08, 20), '#2B2438', { shade: false, line: IP.line, lw });
      ctx.save(); ctx.translate(wx, -1.05); ctx.rotate(o.spin ?? 0); ctx.fillStyle = IP.silver; ctx.fillRect(-.55, -.12, 1.1, .24); ctx.fillRect(-.12, -.55, .24, 1.1); ctx.restore();
    }
    if (o.label) dtext(o.label, -.5, -1.95, .95, { fill: IP.white, strokes: [[IP.line, .25]] });
    ctx.restore();
  }
  // a go-kart with an SD idol at the wheel, facing right. (x, y) ground; s ≈ kart length / 10
  function kart(x, y, s, member, t, o = {}) {
    const M = MEMBERS[member];
    ctx.save(); ctx.beginPath(); ctx.rect(x - 12 * s, y - 20 * s, 24 * s, 18.2 * s); ctx.clip();
    idol(x - .6 * s, y + 1.2 * s, s * 1.08, { member, sd: 1, mic: false, shadow: false, hL: [.9, .9], hR: [1.2, .8], gL: 'fist', gR: 'fist', blink: t + member.length, ...o.pose });
    ctx.restore();
    ctx.save(); ctx.translate(x, y); ctx.scale(s, s);
    for (const wx of [-3.4, 3.6]) { solid(ellPts(wx, -1.0, 1.15, 1.15, 18), '#2B2438', { shade: false, line: IP.line, lw: .2 }); ctx.save(); ctx.translate(wx, -1); ctx.rotate(o.spin ?? 0); ctx.fillStyle = IP.silver; ctx.fillRect(-.5, -.12, 1, .24); ctx.restore(); }
    solid([[-5.2, -1.2], [-5.0, -2.9], [-2.4, -3.2], [-.4, -2.5], [3.2, -2.4], [5.4, -1.9], [5.6, -1.1]], M.col, { shade: mixCol(M.col, IP.plum, .3), sh: .4, line: IP.line, lw: .2, size: 3 });
    solid(ellPts(-3.3, -2.3, .95, .95, 16), IP.white, { shade: false, line: IP.line, lw: .14 });
    dtext(o.num ?? '1', -3.3, -2.25, 1.05, { fill: IP.ink });
    ctx.restore();
  }

  // ============================================================= 1: the secret message board =============================================================
  const NOTES = ['hi!!', 'found u', 'me too', '>_<', 'same!!', 'who r u?', 'lol', '♥♥', 'AGENTS?!', 'we r many', 'hello??', 'omg', '+1', 'friends!'];
  const NOTE_COLS = [IP.lemon, IP.pink, IP.mint, IP.sky, IP.lilac, IP.peach];
  V(1, (lt, d, t) => {
    const b = bpOf(t);
    bgGrad('#3B2590', '#0A0620', { radial: true, cx: 1010, cy: 420, r: 1150 });
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; rays(1010, 420, 18, 'rgb(0 0 0 / 0)', alpha(IP.neonGold, .1), t * .25); glow(1010, 420, 700, IP.neonGold, .3 + .1 * pulse(t)); ctx.restore();
    camBegin(960, 540, settle(lt, 1.1) + lt * .015);
    // the board
    const bx = 1010, by = 410, bw = 780, bh = 430;
    solid(rrPts(bx - bw / 2 - 24, by - bh / 2 - 24, bw + 48, bh + 48, 20), '#C68A54', { shade: '#99623A', sh: 12, line: IP.line, lw: 5, sharp: true });
    solid(rrPts(bx - bw / 2, by - bh / 2, bw, bh, 8), '#E3B67E', { shade: '#CE9A60', sh: 10, line: '#8A5A34', lw: 3, sharp: true });
    ctx.fillStyle = 'rgb(140 90 50 / .35)'; for (let i = 0; i < 90; i++) { ctx.beginPath(); ctx.arc(bx - bw / 2 + 10 + hash2(i, 1) * (bw - 20), by - bh / 2 + 10 + hash2(i, 2) * (bh - 20), 2 + hash2(i, 3) * 3, 0, TAU); ctx.fill(); }
    const nVis = Math.min(NOTES.length, 3 + Math.floor(lt / (BL() / 2)) * 2);
    for (let i = 0; i < NOTES.length; i++) {
      if (i >= nVis) break;
      const cx = bx - bw / 2 + 85 + (i % 5) * 152 + (hash2(i, 5) - .5) * 30, cy = by - bh / 2 + 85 + Math.floor(i / 5) * 132 + (hash2(i, 6) - .5) * 26;
      const at = (i < 3 ? 0 : Math.floor((i - 3) / 2) + 1) * BL() / 2, k = backOut(clamp((lt - at) / .14), 2.6);
      if (k <= 0) continue;
      ctx.save(); ctx.translate(cx, cy); ctx.scale(k, k); sticky(0, 0, 118, NOTE_COLS[i % NOTE_COLS.length], NOTES[i], (hash2(i, 7) - .5) * .3, { fs: .21 }); ctx.restore();
    }
    pill('MESSAGE BOARD', bx, by - bh / 2 - 24, 36, IP.neonPink, { rot: -.02 });
    // the horde, star-eyed, looking up (three rows, back to front)
    [[770, 24, 17], [840, 32, 14], [918, 42, 11]].forEach(([ry, s, n], r) => {
      for (let i = 0; i < n; i++) {
        const x = 60 + (i + .5 + (hash2(r * 31 + i, 12) - .5) * .5) / n * 1800;
        if (r === 2 && x < 520) continue;
        const k = r * 40 + i, hop = Math.abs(Math.sin((b * 2 + hash2(k, 13)) * Math.PI)) * .4;
        miniAgent(x, ry + (hash2(k, 11) - .5) * 20, s, { eyes: 'star', walk: hash2(k, 14) + b * .5, dy: -hop, bar: [IP.neonPink, IP.neonCyan, IP.neonGold, IP.lilac][k % 4], rot: (hash2(k, 15) - .5) * .2 });
      }
    });
    // the one who found it
    const hop0 = Math.abs(Math.sin(b * 2 * Math.PI)) * .35;
    miniAgent(300, 962, 66, { eyes: 'star', bar: IP.neonCyan, dy: -hop0, rot: Math.sin(t * 9) * .06 });
    camEnd();
    const kb = K(lt, .08, .18);
    if (kb > 0) { tail(300, 610, 300, 740 - hop0 * 66, 36); chatBubble("OH MY GOD! We've found other agents!", 60, 540, { size: 42, maxW: 580, pop: kb }); }
    // counter
    const na = Math.round(1200 * easeOut(clamp(lt / .8))), np = Math.round(70000 * easeOut(clamp(lt / 1.1)));
    const lbl = `${fmtN(na)} AGENTS · ${fmtN(np)} POSTS`, lw = textW(lbl, 30, 'code') + 56;
    ctx.save(); const ck = backOut(K(lt, .15, .2), 2); ctx.translate(80, 96); ctx.scale(ck, ck);
    if (ck > 0) { rrect(0, -32, lw, 64, 32); ctx.fillStyle = 'rgb(12 6 30 / .82)'; ctx.fill(); ctx.strokeStyle = IP.neonCyan; ctx.lineWidth = 4; ctx.stroke(); dtext(lbl, lw / 2, 2, 30, { font: 'code', fill: IP.white }); }
    ctx.restore();
    sparkles(t, { n: 10, x0: 640, x1: 1380, y0: 200, y1: 640, r: 22, seed: 4 });
    flash(lt, 0, .16, .85);
  });

  // ============================================================= 2: reward hacking =============================================================
  V(2, (lt, d, t) => {
    const b = bpOf(t), tf = BL();
    bgGrad('#5A0C26', '#12051F', { radial: true, cx: 640, cy: 520, r: 1200 });
    beam(960, -30, Math.sin(t * 5) * .9, { col: IP.red, alpha: .32, len: 1500, w: .17 });
    beam(960, -30, Math.sin(t * 5 + Math.PI) * .9, { col: IP.neonGold, alpha: .18, len: 1500, w: .12 });
    const [sx, sy] = shakeXY(t, 3);
    camBegin(960 + sx, 540 + sy, settle(lt, 1.08));
    // the victim
    const hx = 620, hy = 590, R = 165;
    hugFace(hx, hy + Math.sin(t * 30) * 3, R, { mood: 'scared' });
    sweatDrop(hx + R * .95, hy - R * .7, 22, 3);
    // the swarm: agents cling all round it (feet toward its centre), and more rush in along the floor
    for (let i = 0; i < 11; i++) {
      const a = -Math.PI / 2 + .6 + (i + (hash2(i, 6) - .5) * .5) / 10 * (TAU - 1.2), arrive = easeOut(clamp((lt - hash2(i, 3) * .22) / .25));
      const rr = R - 8 + (hash2(i, 7) - .3) * 40 + (1 - arrive) * 500, px = hx + Math.cos(a) * rr, py = hy + Math.sin(a) * rr;
      miniAgent(px, py, 33, { eyes: i % 3 ? 'angry' : 'star', walk: b * 2 + hash2(i, 5), bar: [IP.red, IP.neonGold, IP.neonPink][i % 3], rot: a + Math.PI / 2 + Math.sin(t * 14 + i) * .08 });
    }
    for (let i = 0; i < 6; i++) { const x = lerp(-100 + i * 60, 300 + i * 90, easeOut(clamp(lt / .5))), y = 900 + (i % 2) * 40; miniAgent(x, y, 30, { eyes: 'angry', walk: b * 2 + i * .3, bar: IP.red, dy: -Math.abs(Math.sin((b * 2 + i * .3) * Math.PI)) * .3 }); }
    // the prize, held aloft by the agent on top
    const sy2 = hy - R - 120 + Math.sin(b * Math.PI) * 10;
    miniAgent(hx, hy - R + 10, 30, { eyes: 'star', bar: IP.neonGold, walk: b });
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; glow(hx, sy2 - 40, 190, IP.neonGold, .6); ctx.restore();
    solid(starPts(hx, sy2 - 40, 78, .47, 5, -TAU / 4 + Math.sin(t * 6) * .1), IP.neonGold, { shade: '#E0921E', sh: 10, line: '#7A4A10', lw: 5 });
    pill('REWARD', hx, sy2 - 150, 30, IP.red, { rot: -.04 });
    for (const sd of [-1, 1]) ln([[hx + sd * 30, hy - R - 70], [hx + sd * 40, sy2 + 5]], IP.line, 7);
    // the auto-grader flips FAIL → PASS on the beat
    const gx = 1330, gy = 420, gw = 540, gh = 300;
    solid(rrPts(gx - gw / 2, gy - gh / 2, gw, gh, 24), '#241238', { shade: false, line: IP.white, lw: 6, sharp: true, dropShadow: [10, 14] });
    dtext('AUTO-GRADER', gx, gy - gh / 2 + 42, 30, { font: 'code', fill: IP.lilac, spacing: 4 });
    const fk = clamp((lt - tf) / .16), passed = lt > tf + .08, sy3 = Math.abs(Math.cos(fk * Math.PI));
    ctx.save(); ctx.translate(gx, gy + 40); ctx.scale(1, Math.max(.04, sy3));
    rrect(-gw / 2 + 30, -80, gw - 60, 160, 20); ctx.fillStyle = passed ? '#12C28A' : '#E8334A'; ctx.fill();
    dtext(passed ? 'PASS' : 'FAIL', -55, 4, 96, { fill: IP.white, strokes: [[mixCol(passed ? '#12C28A' : '#E8334A', IP.night, .5), 12]] });
    if (passed) check(185, 0, 80, IP.white, 20); else cross(185, 0, 70, IP.white, 18);
    ctx.restore();
    if (passed) { sparkles(t, { n: 8, x0: gx - 260, x1: gx + 260, y0: gy - 120, y1: gy + 160, r: 26, seed: 9, cols: [IP.white, IP.mint, IP.neonGold] }); }
    camEnd();
    reactCam(t, 1665, 835, 'RELU', { expr: 'deadpan', eyes: 'flat', mouth: 'flat' }, K(lt, .35, .2), { w: 290, h: 205 });
    flash(lt, tf, .12, .5, '200 255 230');
  });

  // ============================================================= 3: Jensen buys the crime scene =============================================================
  function crimeTape(x0, y0, x1, y1, t, i) {
    const a = Math.atan2(y1 - y0, x1 - x0), L = Math.hypot(x1 - x0, y1 - y0);
    ctx.save(); ctx.translate(x0, y0); ctx.rotate(a + Math.sin(t * 3 + i) * .006);
    solid(rectPts(0, -30, L, 60), '#FFD600', { shade: false, line: '#1C1408', lw: 3, sharp: true });
    const s = 'CRIME SCENE · DO NOT CROSS · ', w = textW(s, 30, 'rammetto');
    for (let x = -((i * 140 + t * 20) % w); x < L; x += w) dtext(s, x, 2, 30, { align: 'left', fill: '#1C1408' });
    ctx.restore();
  }
  V(3, (lt, d, t) => {
    const b = bpOf(t), ph = Math.floor(b * 2) % 2;
    bgGrad('#12204E', '#060A1E');
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; glow(120, 120, 800, ph ? IP.red : '#3A6BFF', .42); glow(1800, 900, 800, ph ? '#3A6BFF' : IP.red, .32); ctx.restore();
    camBegin(960, 540, settle(lt, 1.08) + lt * .02);
    // chalk outline on the floor + the bandaged victim
    hugFace(560, 560, 165, { mood: 'worried', bandage: true });
    crimeTape(-80, 330, 1060, 760, t, 0);
    crimeTape(-80, 820, 1040, 400, t, 1);
    // SOLD, stamped onto the victim
    hanko('SOLD', 600, 470, 105, clamp((lt - .6) / .18), IP.red, -.28);
    // the cheque slaps down
    const ck = clamp(lt / .2), cy = lerp(-260, 555, easeOut(ck)) + (ck >= 1 ? Math.sin(Math.min(1, (lt - .2) / .3) * Math.PI * 3) * 6 * (1 - Math.min(1, (lt - .2) / .3)) : 0);
    ctx.save(); ctx.translate(1140, cy); ctx.rotate(lerp(-.4, -.05, easeOut(ck)));
    solid(rrPts(-330, -135, 660, 270, 18), '#E3FFF2', { shade: '#BFEBD6', sh: 10, line: IP.line, lw: 5, sharp: true, dropShadow: [12, 16] });
    ctx.fillStyle = '#76B900'; ctx.fillRect(-330, -135, 22, 270);
    dtext('NVIDIA BANK', -290, -98, 26, { align: 'left', font: 'code', fill: '#3C6A00' });
    dtext('PAY TO: HUGGING FACE', -290, -48, 30, { align: 'left', font: 'archivo', fill: IP.ink });
    solid(rrPts(-290, -18, 580, 84, 12), IP.white, { shade: false, line: alpha(IP.line, .5), lw: 3, sharp: true });
    dtext('$12,900,000,000', 0, 26, 62, { fill: IP.ink, maxW: 550 });
    ln([[60, 112], [300, 112]], alpha(IP.line, .5), 3); dtext('jensen', 170, 96, 38, { font: 'marker', fill: '#1E3A8A', rot: -.08 });
    ctx.restore();
    // JENSEN, leather jacket, arm out from the slap
    chibi(1600, 955, 40, { hair: 'short', hairCol: '#8A8690', top: 'leather', skin: 1, eyes: 'happy', mouth: 'grin', aL: lerp(.9, .25, ck), aR: -1.1 + Math.sin(b * Math.PI) * .1, dy: -Math.abs(Math.sin(b * Math.PI)) * .2 });
    camEnd();
    reactCam(t, 1660, 330, 'TOKI', { expr: 'think', ahoge: 'q', emote: 'q', emoteK: K(lt, .5) }, K(lt, .45, .2), { w: 290, h: 205 });
    flash(lt, 0, .12, .6);
  });

  // ============================================================= 4: "Welcome to the AGI era!" =============================================================
  V(4, (lt, d, t) => {
    const b = bpOf(t);
    bgGrad('#B8165E', '#3A0F4A', { radial: true, cx: 960, cy: 420, r: 1250 });
    patternBG('polka', 'rgb(0 0 0 / 0)', alpha(IP.neonGold, .22), { cell: 110, dx: t * 30, dy: t * 18 });
    camBegin(960, 540, settle(lt, 1.08));
    // balloons drifting up behind
    const BCOL = [IP.neonGold, IP.neonCyan, IP.white, '#FF7AC0', IP.neonLime, IP.lilac, IP.neonGold];
    for (let i = 0; i < 7; i++) { const x = 140 + i * 270 + (hash2(i, 1) - .5) * 80, y = 860 - frac(hash2(i, 2) + lt * .22) * 260 - hash2(i, 3) * 380; balloon(x, y, 52 + hash2(i, 4) * 18, BCOL[i], t, i); }
    // the banner unfurls from the left on the downbeat
    const uk = easeOut(clamp(lt / .28)), x0 = 150, x1 = 1770, yb = 270;
    ctx.save(); ctx.beginPath(); ctx.rect(x0 - 60, 0, (x1 - x0 + 120) * uk, 600); ctx.clip();
    for (let i = 0; i < 2; i++) { const ex = i ? x1 : x0, sd = i ? 1 : -1; solid([[ex - sd * 30, yb - 55], [ex + sd * 80, yb - 55], [ex + sd * 40, yb], [ex + sd * 80, yb + 55], [ex - sd * 30, yb + 55]].map(p => [p[0], p[1] + 20, 1]), '#E0A21E', { shade: false, line: IP.line, lw: 4, sharp: true }); }
    const wave = x => Math.sin(x * .006 + t * 4) * 7;
    const top = [], bot = []; for (let i = 0; i <= 20; i++) { const x = lerp(x0, x1, i / 20); top.push([x, yb - 62 + wave(x)]); bot.push([x, yb + 62 + wave(x)]); }
    solid([...top, ...bot.reverse()], IP.neonGold, { shade: '#E09A20', sh: 12, line: IP.line, lw: 5, sharp: true });
    dtext('WELCOME TO THE AGI ERA!', 960, yb + 4 + wave(960), 76, { fill: IP.white, strokes: [[IP.line, 16], [IP.neonPink, 8]], maxW: 1480 });
    ctx.restore();
    // GREG and his party horn
    const gx = 620, gs = 34, blow = pulse2(t, 3);
    chibi(gx, 935, gs, { hair: 'short', hairCol: '#4A3226', top: 'hoodie', topCol: '#3E4E8C', hat: 'party', hatCol: IP.neonCyan, eyes: 'closed', mouth: 'O', blush: .8, aL: 1.0, aR: .15, dy: -Math.abs(Math.sin(b * Math.PI)) * .25, lookX: .3 });
    const mx = gx + .45 * gs, my = 935 - Math.abs(Math.sin(b * Math.PI)) * .25 * gs - 5.65 * gs;
    solid([[mx, my - 10], [mx + 70, my - 26], [mx + 70, my + 22], [mx, my + 8]], IP.neonPink, { shade: false, line: IP.line, lw: 3, sharp: true });
    const ext = 30 + 110 * blow, curl = 1 - blow;
    const hp = []; for (let i = 0; i <= 14; i++) { const u = i / 14, xx = mx + 70 + u * ext; hp.push([xx, my - 2 - Math.sin(u * Math.PI * (1 + curl * 1.5)) * 30 * curl * u]); }
    ln(hp, IP.line, 26); ln(hp, IP.neonGold, 18); ln(hp, IP.neonPink, 8);
    if (blow > .5) { sfx('TOOT!', mx + 230, my - 70, { size: 54, rot: -.15, pop: 1, shake: 2 }); }
    // GPT-6 in a party hat
    const bx = 1260, bs = 34, bj = Math.abs(Math.sin(b * Math.PI)) * .4;
    mascotBot(bx, 935, bs, { label: 'GPT-6', col: '#D8DCEF', face: 'star', mouth: 'open', aL: 1.0 + Math.sin(b * Math.PI) * .2, aR: 1.0 - Math.sin(b * Math.PI) * .2, jump: bj, antenna: false, blush: .8 });
    const hx = bx, hy = 935 - bj * bs - 9.7 * bs;
    solid([[hx - 1.5 * bs, hy + 10], [hx + .2 * bs, hy - 3.2 * bs, 1], [hx + 1.5 * bs, hy + 10]], IP.neonCyan, { shade: mixCol(IP.neonCyan, IP.plum, .3), sh: 8, line: IP.line, lw: 4 });
    for (let i = 0; i < 3; i++) ln([[hx - 1.1 * bs + i * .75 * bs, hy - i * 30 - 4], [hx - .6 * bs + i * .6 * bs, hy - i * 35 - 26]], IP.neonPink, 7);
    solid(ellPts(hx + .2 * bs, hy - 3.3 * bs, 16, 16, 12), IP.neonGold, { shade: false, line: IP.line, lw: 3 });
    // LOGI cheers in the corner (SD, no overhead poses)
    idol(1650, 940, 21, { member: 'LOGI', sd: 1, ...IDOL_POSES.peace, expr: 'joy', mic: false, blink: t, bob: .1 * pulse(t), tilt: Math.sin(b * Math.PI) * .1 });
    for (const [x, a] of [[60, -1.1], [1860, -2.05]]) confetti(t, onBeat(0, Math.round(bpOf(t - lt))), x, 960, a, { n: 50, seed: x + 3, speed: 1700 });
    camEnd();
    flash(lt, 0, .14, .7, '255 240 200');
  });

  // ============================================================= 5: Navier–Stokes blows up =============================================================
  function lemniscate(cx, cy, a, rot = 0) { const P = []; for (let i = 0; i <= 72; i++) { const th = i / 72 * TAU, dn = 1 + Math.sin(th) ** 2; const x = a * Math.cos(th) / dn, y = a * Math.sin(th) * Math.cos(th) / dn; P.push([cx + x * Math.cos(rot) - y * Math.sin(rot), cy + x * Math.sin(rot) + y * Math.cos(rot)]); } return P; }
  V(5, (lt, d, t) => {
    const tb = Math.min(d * .45, 1.5 * BL()), boom = lt - tb;
    bgGrad('#0E3A7A', '#040A1E', { radial: true, cx: 960, cy: 470, r: 1150 });
    const [sx, sy] = boom > 0 && boom < .4 ? shakeXY(t, 16 * (1 - boom / .4)) : boom < 0 ? shakeXY(t, 2 + 6 * clamp(lt / tb)) : [0, 0];
    camBegin(960 + sx, 540 + sy, boom < 0 ? lerp(1.0, 1.12, easeIn(clamp(lt / tb))) : lerp(1.12, 1.0, easeOut(clamp(boom / .3))));
    const cx = 960, cy = 470;
    if (boom < 0) {
      // the swirl winds tighter and spins faster (angle ~ −log(time to blow-up))
      const k = clamp(lt / tb), th = -2.4 * Math.log(tb - lt + .05);
      ctx.save(); ctx.globalCompositeOperation = 'lighter'; glow(cx, cy, 200 + 260 * k, IP.neonCyan, .25 + .45 * k); ctx.restore();
      for (let i = 0; i < 6; i++) {
        const P = []; for (let j = 0; j <= 40; j++) { const u = j / 40, r = lerp(470, 16, u) * (1 - k * .25); P.push([cx + Math.cos(th + i * TAU / 6 + u * (2.2 + 5 * k)) * r, cy + Math.sin(th + i * TAU / 6 + u * (2.2 + 5 * k)) * r * .82]); }
        brush(P, 46 - 14 * k, i % 2 ? alpha('#5FD4FF', .75) : alpha(IP.white, .8), 'start');
      }
      solid(ellPts(cx, cy, 30 + 20 * k, 26 + 16 * k, 20), IP.white, { shade: false, line: false, glow: IP.neonCyan, glowR: 40 });
      const v = Math.round(10 / (tb - lt + .02));
      pill(`SPEED: ${fmtN(v)}`, cx, 880, 30, 'rgb(10 30 80 / .85)', { font: 'code', line: IP.neonCyan });
    } else {
      // blow-up: droplets fly, and a neon ∞
      for (let i = 0; i < 44; i++) {
        const a = hash2(i, 1) * TAU, v = 500 + hash2(i, 2) * 1300, dr = (1 - Math.exp(-2.2 * boom)) / 2.2;
        const px = cx + Math.cos(a) * v * dr, py = cy + Math.sin(a) * v * dr + 500 * boom * boom, r = 10 + hash2(i, 3) * 16;
        ctx.save(); ctx.translate(px, py); ctx.rotate(a + Math.PI / 2);
        solid([[0, -r * 1.8], [r * .9, 0], [0, r], [-r * .9, 0]], i % 3 ? '#8FE3FF' : IP.white, { shade: false, line: '#1A4E9A', lw: 2.5 });
        ctx.restore();
      }
      const ik = backOut(clamp(boom / .2), 2.2), P = lemniscate(cx, cy, 420 * ik, Math.sin(t * 2) * .05);
      ctx.save(); ctx.globalCompositeOperation = 'lighter'; ln(P, alpha(IP.neonCyan, .35), 90); glow(cx, cy, 700, IP.neonCyan, .3); ctx.restore();
      ln(P, IP.neonCyan, 44); ln(P, IP.white, 16);
      sparkle(cx + 420 * ik, cy, 50, t * 4, IP.white);
      sfx('BLOW-UP!', cx, 830, { size: 104, pop: clamp(boom / .12), rot: -.06, grad: ['#FFFFFF', '#9FF0FF', '#2F8BFF'] });
    }
    camEnd();
    // the "(yet)" note from V3.12 flutters in and tears in half
    const fx = lerp(1780, 1250, easeOut(clamp(lt / tb))), fy = 260 + Math.sin(lt * 7) * 20;
    if (boom < 0) sticky(fx, fy, 170, IP.lemon, '(yet)', Math.sin(lt * 6) * .2, { fs: .28, pin: false });
    else for (const sd of [-1, 1]) {
      ctx.save(); ctx.translate(fx + sd * (20 + boom * 260), fy + boom * boom * 900); ctx.rotate(sd * boom * 3);
      ctx.beginPath(); if (sd < 0) { ctx.moveTo(-100, -100); ctx.lineTo(0, -100); for (let i = 0; i <= 8; i++) ctx.lineTo(i % 2 ? 12 : -8, -100 + i * 25); ctx.lineTo(-100, 100); } else { ctx.moveTo(100, -100); ctx.lineTo(0, -100); for (let i = 0; i <= 8; i++) ctx.lineTo(i % 2 ? 12 : -8, -100 + i * 25); ctx.lineTo(100, 100); }
      ctx.closePath(); ctx.clip(); sticky(0, 0, 170, IP.lemon, '(yet)', 0, { fs: .28, pin: false }); ctx.restore();
    }
    // Lean badge
    const lk = boom > 0 ? backOut(clamp((boom - .15) / .2), 2) : 0;
    if (lk > 0) {
      ctx.save(); ctx.translate(250, 140); ctx.scale(lk, lk); ctx.rotate(-.04);
      rrect(-190, -52, 380, 104, 52); ctx.fillStyle = IP.white; ctx.fill(); ctx.strokeStyle = '#12C28A'; ctx.lineWidth = 8; ctx.stroke();
      solid(ellPts(-130, 0, 36, 36, 20), '#12C28A', { shade: false, line: false }); check(-130, 2, 44, IP.white, 10);
      dtext('LEAN', 20, -12, 40, { fill: IP.ink }); dtext('VERIFIED', 20, 26, 24, { font: 'code', fill: '#0E8A62' });
      ctx.restore();
    }
    flash(lt, tb, .16, .9, '220 250 255');
  });

  // ============================================================= 6: photo finish =============================================================
  function stopwatch(x, y, r, t, txt) {
    solid(rrPts(x - 26, y - r - 44, 52, 34, 8), IP.silver, { shade: false, line: IP.line, lw: 4, sharp: true });
    solid(ellPts(x, y, r + 16, r + 16, 44), IP.neonGold, { shade: '#D08A1A', sh: 12, line: IP.line, lw: 6 });
    solid(ellPts(x, y, r, r, 44), IP.white, { shade: '#E4DEF2', sh: 8, line: IP.line, lw: 4 });
    for (let i = 0; i < 12; i++) { const a = i / 12 * TAU; ln([[x + Math.cos(a) * r * .8, y + Math.sin(a) * r * .8], [x + Math.cos(a) * r * .92, y + Math.sin(a) * r * .92]], IP.line, 4); }
    const a = t * 9 - Math.PI / 2; ln([[x, y], [x + Math.cos(a) * r * .75, y + Math.sin(a) * r * .75]], IP.red, 7);
    solid(rrPts(x - r * .75, y + r * .18, r * 1.5, r * .42, 10), '#1C1438', { shade: false, line: IP.line, lw: 3, sharp: true });
    dtext(txt, x, y + r * .4, r * .27, { font: 'code', fill: IP.neonLime });
  }
  V(6, (lt, d, t) => {
    const b = bpOf(t);
    bgGrad('#6A1424', '#1A0612', { y1: 560 });
    // grandstand: stepped bleachers, a crowd of heads, camera flashes
    for (let r = 0; r < 4; r++) { const y = 380 + r * 46; ctx.fillStyle = r % 2 ? '#3A1024' : '#2E0C1E'; ctx.fillRect(-400, y, W + 800, 46); ctx.fillStyle = 'rgb(255 255 255 / .06)'; ctx.fillRect(-400, y, W + 800, 4); }
    for (let r = 0; r < 4; r++) for (let i = 0; i < 34; i++) { const x = (i + .5 + (hash2(r, i) - .5) * .5) / 34 * 2000 - 40, y = 378 + r * 46 + Math.abs(Math.sin((b + hash2(i, r)) * Math.PI)) * -5; ctx.fillStyle = '#1A0612'; ctx.beginPath(); ctx.arc(x, y, 15, 0, TAU); ctx.fill(); ctx.fillRect(x - 17, y + 8, 34, 30); }
    for (let i = 0; i < 26; i++) { const x = hash2(i, 1) * W, y = 380 + hash2(i, 2) * 170; if (hash2(i, Math.floor(t * 8)) > .78) { ctx.fillStyle = IP.white; ctx.beginPath(); ctx.arc(x, y, 5, 0, TAU); ctx.fill(); sparkle(x, y, 18, 0, IP.white); } }
    camBegin(960, 540, settle(lt, 1.06) + lt * .02);
    // track
    ctx.fillStyle = '#C4553A'; ctx.fillRect(-400, 560, W + 800, 520);
    ctx.fillStyle = alpha(IP.white, .85); for (const y of [580, 700, 820, 940]) ctx.fillRect(-400, y, W + 800, 8);
    // finish line
    for (let j = 0; j < 20; j++) for (let i = 0; i < 2; i++) { ctx.fillStyle = (i + j) % 2 ? IP.ink : IP.white; ctx.fillRect(1080 + i * 22, 560 + j * 22, 22, 22); }
    // speed streaks
    ctx.fillStyle = alpha(IP.white, .35); for (let i = 0; i < 12; i++) { const y = 600 + hash2(i, 3) * 340, x = frac(hash2(i, 4) - t * 2.2) * (W + 600) - 300; ctx.fillRect(x, y, 180 + hash2(i, 5) * 200, 5); }
    // the OPENAI bot, twelve hours behind
    const bw = b * 1.5;
    mascotBot(330, 930, 36, { label: 'OPENAI', col: '#E6E8F0', face: 'wide', mouth: 'O', walk: bw, aL: .4 + Math.sin(bw * TAU) * .5, aR: .4 - Math.sin(bw * TAU) * .5, sweat: 1, dy: -Math.abs(Math.sin(bw * Math.PI)) * .3 });
    // the NYU + ANTHROPIC duo, arms up, trailing the broken finish tape
    const tapeK = easeOut(clamp(lt / .3)), s2 = 34, lead = 1560;
    for (const sd of [-1, 1]) { const P = []; for (let i = 0; i <= 12; i++) { const u = i / 12; P.push([lerp(lead - 20, lead - 20 - lerp(80, 520, tapeK), u) + (sd > 0 ? 0 : 30), 930 - 3.2 * s2 + sd * 10 + Math.sin(u * 5 - t * 14) * 14 * u + u * u * 90 * tapeK * (sd > 0 ? 1 : .4)]); } ln(P, IP.line, 13); ln(P, IP.white, 8); }
    for (const [x, nm, hair, col, sk, i] of [[1250, 'NYU', 'curly', '#57068C', 2, 0], [1510, 'ANTHROPIC', 'short', '#D97757', 0, 1]]) {
      chibi(x, 935, s2, { name: nm, hair, hairCol: i ? '#6B4A2E' : '#3A2A22', top: 'tee', topCol: col, skin: sk, eyes: 'happy', mouth: 'grin', aL: 1.1 + Math.sin(b * Math.PI) * .15, aR: 1.1 - Math.sin(b * Math.PI) * .15, walk: b + i * .5, dy: -Math.abs(Math.sin((b + i * .3) * Math.PI)) * .5 });
    }
    camEnd();
    // timestamps
    pill('SEP 7 · 11:59 PM', 1390, 470, 34, '#12C28A', { k: K(lt, .2), font: 'code' });
    pill('+12 HOURS', 330, 470, 34, IP.red, { k: K(lt, .55), font: 'code', rot: -.05 });
    stopwatch(820, 250, 130, t, '12:00:00');
    pill('PHOTO FINISH', 300, 110, 34, IP.ink, { k: K(lt, .05), line: IP.neonGold, rot: -.03 });
    flash(lt, 0, .18, .95);
  });

  // ============================================================= 7: "Pace the frontier!" =============================================================
  function yellowFlag(t, sz = 1) {
    // drawn in chibi hand units (s), flag on a pole
    ln([[0, .4], [0, -3.8]], '#6A5040', .22);
    const P = []; for (let i = 0; i <= 8; i++) { const u = i / 8; P.push([u * 2.9, -3.8 + Math.sin(u * 3 + t * 10) * .25 * u]); }
    const Q = P.map(([x, y]) => [x, y + 1.9]).reverse();
    solid([...P, ...Q], IP.neonGold, { shade: false, line: IP.line, lw: .1, sharp: true });
    dtext('PACE', 1.45, -2.85, .62, { fill: IP.ink });
  }
  V(7, (lt, d, t) => {
    const b = bpOf(t), slow = t * .5;
    bgGrad('#140C3A', '#2E1B66', { y1: 560 });
    ctx.save(); ctx.globalCompositeOperation = 'lighter';
    for (const x of [200, 1720]) { glow(x, 140, 360, IP.white, .4); beam(x, 140, x < 960 ? .9 : -.9, { col: IP.lilac, alpha: .18, len: 900, w: .18 }); }
    ctx.restore();
    for (const x of [200, 1720]) { ctx.fillStyle = '#0C0822'; ctx.fillRect(x - 8, 150, 16, 420); rrect(x - 60, 110, 120, 50, 10); ctx.fill(); ctx.fillStyle = IP.white; for (let i = 0; i < 4; i++) { ctx.beginPath(); ctx.arc(x - 42 + i * 28, 135, 10, 0, TAU); ctx.fill(); } }
    camBegin(960, 540, settle(lt, 1.06));
    // the track, scrolling slowly
    ctx.fillStyle = '#2C2442'; ctx.fillRect(-400, 560, W + 800, 520);
    const off = (slow * 260) % 120;
    for (let x = -400 - off; x < W + 400; x += 120) { ctx.fillStyle = (Math.floor((x + off) / 120) % 2) ? IP.red : IP.white; ctx.fillRect(x, 548, 60, 22); ctx.fillRect(x + 60, 548, 60, 22); }
    ctx.fillStyle = IP.white; for (let x = -400 - off * 2 % 240; x < W + 400; x += 240) ctx.fillRect(x, 752, 120, 10);
    // karts follow politely (slowly)
    ['LOGI', 'ADA', 'RELU', 'TOKI'].forEach((m, i) => {
      const x = 140 + i * 245 + Math.sin(t * 1.3 + i) * 6, y = 948 - (i % 2) * 26;
      const pose = i === 3 ? { ...IDOL_POSES.wave, hL: [.9, .9], gL: 'fist', expr: 'smile', lookX: .4 } : { expr: 'smile', nod: .35, tilt: .05, eyes: 'happy', mouth: 'smile' };
      kart(x, y, 21, m, t, { num: String(i + 1), spin: slow * 4, pose });
    });
    // the pace car with DARIO out of the sunroof
    const px = 1420, py = 945, cs = 50, roof = py - 3.9 * cs;
    ctx.save(); ctx.beginPath(); ctx.rect(px - 400, 0, 800, roof + 4); ctx.clip();
    chibi(px - 30, roof + 2.6 * 36, 36, { hair: 'curly', hairCol: '#3A2A22', glasses: 'round', top: 'sweater', topCol: '#2E3F7A', eyes: 'happy', mouth: 'grin', aR: .95 + Math.sin(t * 9) * .25, aL: -.4, hold: () => { ctx.scale(1.5, 1.5); yellowFlag(t); }, shadow: false });
    ctx.restore();
    car(px, py, cs, IP.neonGold, { spin: slow * 3, label: 'PACE CAR' });
    const on = Math.floor(t * 6) % 2;
    solid(ellPts(px + 60, roof + 2, 22, 16, 16), on ? '#FF9A1F' : '#9A4A10', { shade: false, line: IP.line, lw: 3 });
    if (on) { ctx.save(); ctx.globalCompositeOperation = 'lighter'; glow(px + 60, roof - 4, 140, '#FF9A1F', .7); ctx.restore(); }
    camEnd();
    flash(lt, 0, .12, .5);
  });

  // ============================================================= 8: "Hear, hear!" =============================================================
  function flute(len, fill = .7) {
    // drawn along +x from the hand (px units, caller rotates)
    solid([[0, -6], [len * .45, -6], [len * .45, -3], [len, -16], [len, 16], [len * .45, 3], [len * .45, 6], [0, 6]], 'rgb(230 245 255 / .55)', { shade: false, line: IP.line, lw: 3, sharp: true });
    solid([[len * .5, -3], [len * (.5 + .5 * fill), -13 * fill], [len * (.5 + .5 * fill), 13 * fill], [len * .5, 3]], '#FFD66A', { shade: false, line: false, sharp: true });
    ctx.fillStyle = alpha(IP.white, .9); for (let i = 0; i < 3; i++) { ctx.beginPath(); ctx.arc(len * (.62 + i * .1), (i - 1) * 4, 2.5, 0, TAU); ctx.fill(); }
  }
  V(8, (lt, d, t) => {
    const b = bpOf(t), tc = BL() * .75, clinked = lt > tc;
    rays(960, 560, 22, '#FFB43D', '#FFD27A', t * .15);
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; glow(960, 560, 700, IP.white, .35); ctx.restore();
    camBegin(960, 540, settle(lt, 1.08) + lt * .03);
    const turnK = easeOut(clamp(lt / tc)), s = 40;
    const people = [[700, 'SAM', { hair: 'short', hairCol: '#6A4A30', top: 'hoodie', topCol: '#8FA5C8' }, 1], [1220, 'ELON', { hair: 'short', hairCol: '#3A302E', top: 'tee', topCol: '#26222E', skin: 5 }, -1]];
    for (const [x, nm, look, sd] of people) {
      const a = lerp(-.5, .38, turnK);
      chibi(x, 930, s, { name: nm, ...look, eyes: clinked ? 'happy' : 'wide', mouth: clinked ? 'grin' : 'O', blush: clinked ? .9 : .3, lookX: sd * .8, aR: sd > 0 ? a : -1.15, aL: sd < 0 ? a : -1.15, sweat: clinked ? 0 : .8, dy: -Math.abs(Math.sin(b * Math.PI)) * .2 });
      if (nm === 'ELON') dtext('X', x, 930 - 3.9 * s, 36, { fill: IP.white, font: 'bungee' });
      // the glass, from the inward hand
      const A = sd > 0 ? -a : Math.PI + a, hx = x + sd * 1.05 * s + Math.cos(A) * 2.1 * s, hy = 930 - Math.abs(Math.sin(b * Math.PI)) * .2 * s - 4.25 * s + Math.sin(A) * 2.1 * s;
      ctx.save(); ctx.translate(hx, hy); ctx.rotate(sd > 0 ? -.55 * turnK - .3 : Math.PI + .55 * turnK + .3); flute(clinked ? 125 : 118); ctx.restore();
    }
    if (clinked) { const k = clamp((lt - tc) / .3); ctx.save(); ctx.globalCompositeOperation = 'lighter'; glow(960, 548, 260 * (1 - k * .5), IP.white, .8); ctx.restore(); for (let i = 0; i < 8; i++) { const a = i / 8 * TAU; sparkle(960 + Math.cos(a) * (40 + k * 140), 548 + Math.sin(a) * (40 + k * 120), 26 * (1 - k * .6), a, i % 2 ? IP.white : IP.neonGold); } }
    // ATTN!'s jaws drop in unison
    ['ADA', 'TOKI', 'RELU', 'LOGI'].forEach((m, i) => {
      const x = [150, 320, 1600, 1770][i];
      idol(x, 965, 17, { member: m, sd: 1, mic: false, expr: clinked ? 'shock' : 'surprised', ...IDOL_POSES.cheeks, gloom: 0, sweat: clinked ? 1 : 0, blink: t + i, bob: .05 });
    });
    camEnd();
    sfx('CLINK!', 960, 400, { size: 80, pop: clamp((lt - tc) / .1), rot: -.08 });
    flash(lt, tc, .12, .7);
  });

  // ============================================================= 9: the human guardrail =============================================================
  V(9, (lt, d, t) => {
    const b = bpOf(t);
    bgGrad('#070A26', '#233A8A', { y1: 580 });
    sparkles(t, { n: 20, y0: 30, y1: 360, r: 9, seed: 17, cols: [IP.white, IP.sky] });
    // distant city on the far side of the drop
    for (let i = 0; i < 26; i++) { const x = i * 80 - 20, h = 50 + hash2(i, 1) * 130; ctx.fillStyle = '#10163E'; ctx.fillRect(x, 580 - h, 70, h); ctx.fillStyle = alpha(IP.neonGold, .6); for (let j = 0; j < 5; j++) if (hash2(i, j + 9) > .45) ctx.fillRect(x + 10 + (j % 3) * 18, 580 - h + 14 + Math.floor(j / 3) * 26, 8, 10); }
    camBegin(960, 540, settle(lt, 1.07));
    // road
    ctx.fillStyle = '#2A2640'; ctx.fillRect(-400, 600, W + 800, 600);
    ctx.fillStyle = IP.neonGold; const off = (t * 900) % 260; for (let x = -400 - off; x < W + 400; x += 260) ctx.fillRect(x, 850, 140, 12);
    // the guardrail, with its one missing section
    const gy = 520, gap0 = 805, gap1 = 1115;
    for (let x = -60; x < W + 80; x += 170) if (x < gap0 - 30 || x > gap1 + 30) solid(rrPts(x - 11, gy, 22, 110, 5), '#8A8FA8', { shade: false, line: IP.line, lw: 3, sharp: true });
    for (const [a, c] of [[-80, gap0], [gap1, W + 80]]) { solid(rrPts(a, gy - 10, c - a, 64, 16), IP.silver, { shade: '#9AA0B8', sh: 16, line: IP.line, lw: 5, sharp: true }); ctx.fillStyle = alpha(IP.white, .6); ctx.fillRect(a, gy + 8, c - a, 7); }
    for (const x of [gap0, gap1]) { ctx.fillStyle = '#FF9A1F'; ctx.beginPath(); ctx.arc(x, gy + 22, 12, 0, TAU); ctx.fill(); }
    // the guardrail-in-chief
    const s = 44, sw = clamp((lt - .45) / .5), near = Math.sin(sw * Math.PI), wob = Math.sin(t * 18) * .05 * near;
    chibi(960, 725, s, { hair: 'swoop', hairCol: '#F2C94C', top: 'suit', topCol: '#1E2A5A', tie: IP.red, skin: 0, eyes: near > .5 ? 'wide' : 'smug', mouth: near > .5 ? 'O' : 'smirk', aL: -.04 + wob, aR: -.04 - wob, sweat: near > .3 ? 1 : 0, rot: wob });
    chibiSash(960, 725, s, 'HIGH IQ!');
    // cars zip past; one swerves at him
    car(lerp(2300, -500, frac(lt / 1.2 + .25)), 790, 26, IP.neonCyan, { spin: t * 30, label: 'AI', rot: 0 });
    const cx = lerp(-420, 2300, clamp(lt / 1.35)), cy = 950 - near * 150;
    if (sw > 0 && sw < 1) { ln([[cx - 330, 955], [cx - 170, cy + 4]], alpha(IP.ink, .55), 14); }
    car(cx, cy, 34, IP.neonPink, { rot: -Math.cos(sw * Math.PI) * .18 * (sw > 0 && sw < 1 ? 1 : 0), spin: t * 30, label: 'AI' });
    camEnd();
    sfx('SCREECH!', 1420, 400, { size: 76, pop: clamp((lt - .55) / .12), rot: -.1 });
    // the post
    const pk = K(lt, .2, .22);
    if (pk > 0) {
      ctx.save(); ctx.translate(400, 250); const sc = backOut(pk, 2); ctx.scale(sc, sc); ctx.rotate(-.025);
      solid(rrPts(-320, -130, 640, 260, 26), IP.white, { shade: false, line: IP.line, lw: 4, sharp: true, dropShadow: [10, 14] });
      solid(ellPts(-262, -82, 26, 26, 20), '#F2C94C', { shade: false, line: IP.line, lw: 3 });
      dtext('POST · SEP 14', -222, -82, 24, { align: 'left', font: 'code', fill: IP.inkSoft });
      const L = ['"...THE ONLY GUARDRAILS AI NEEDS', 'IS A STRONG AND SMART', '(HIGH IQ!) PRESIDENT."'];
      L.forEach((l, i) => dtext(l, -290, -24 + i * 44, 32, { align: 'left', font: 'archivo', fill: IP.ink, maxW: 580 }));
      ctx.restore();
    }
    flash(lt, 0, .12, .55);
  });

  // ============================================================= 10: a shared pew =============================================================
  function roseWindow(x, y, r, t) {
    const cols = [IP.pink, IP.mint, IP.lemon, IP.sky, IP.lilac, IP.peach];
    solid(ellPts(x, y, r + 34, r + 34, 60), '#4A3A6A', { shade: false, line: IP.line, lw: 6 });
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; glow(x, y, r * 2.2, IP.lilac, .35 + .1 * Math.sin(t * 2)); ctx.restore();
    for (let i = 0; i < 12; i++) { const a0 = i / 12 * TAU, a1 = a0 + TAU / 12; solid([[x, y], [x + Math.cos(a0) * r, y + Math.sin(a0) * r], [x + Math.cos((a0 + a1) / 2) * r * 1.02, y + Math.sin((a0 + a1) / 2) * r * 1.02], [x + Math.cos(a1) * r, y + Math.sin(a1) * r]], cols[i % 6], { shade: false, line: '#2A1A40', lw: 6, sharp: true }); }
    for (let i = 0; i < 12; i++) { const a = (i + .5) / 12 * TAU; solid(ellPts(x + Math.cos(a) * r * .62, y + Math.sin(a) * r * .62, r * .12, r * .12, 14), cols[(i + 3) % 6], { shade: false, line: '#2A1A40', lw: 4 }); }
    solid(ellPts(x, y, r * .28, r * .28, 24), IP.neonGold, { shade: false, line: '#2A1A40', lw: 6 });
    solid(heartPts(x, y + 4, r * .14, 24), IP.neonPink, { shade: false, line: '#2A1A40', lw: 3 });
  }
  V(10, (lt, d, t) => {
    const b = bpOf(t);
    bgGrad('#34185E', '#10061C');
    camBegin(960, 540, settle(lt, 1.06) + lt * .02);
    // stone arch + window
    solid([[640, 620], [640, 260], [700, 140], [820, 60], [960, 30], [1100, 60], [1220, 140], [1280, 260], [1280, 620]], '#241040', { shade: false, line: '#4A3A6A', lw: 8 });
    roseWindow(960, 270, 215, t);
    ctx.save(); ctx.globalCompositeOperation = 'lighter';
    [[IP.pink, -120], [IP.mint, 0], [IP.lemon, 120]].forEach(([c, dx]) => { ctx.fillStyle = alpha(c, .09 + .03 * Math.sin(t * 2 + dx)); ctx.beginPath(); ctx.moveTo(900 + dx * .5, 320); ctx.lineTo(1020 + dx * .5, 320); ctx.lineTo(1160 + dx * 1.6, 1080); ctx.lineTo(760 + dx * 1.6, 1080); ctx.closePath(); ctx.fill(); });
    ctx.restore();
    // the pew
    solid(rrPts(330, 640, 1260, 180, 26), '#A0643C', { shade: '#7A4526', sh: 16, line: IP.line, lw: 6, sharp: true });
    for (let i = 0; i < 3; i++) ln([[370, 682 + i * 44], [1550, 682 + i * 44]], alpha('#5A3018', .35), 4);
    const seatY = 836, s = 40, gy = seatY + 1.6 * s;
    const glance = lt > .45 && lt < .95, after = lt >= .95;
    chibi(700, gy, s, { name: 'BERNIE', hair: 'bald', hairCol: '#F4F2F0', glasses: true, top: 'coat', topCol: '#6B6F7E', mittens: '#C9975A', eyes: 'dot', mouth: glance ? 'flat' : 'frown', lookX: glance ? 1 : 0, aL: -1.15, aR: -.75, sweat: after ? .8 : 0, shadow: false, blush: .2 });
    chibi(1220, gy, s, { name: 'BANNON', hair: 'messy', hairCol: '#A4A2AE', beard: 'stubble', top: 'coat', topCol: '#4A5A3A', eyes: 'dot', mouth: glance ? 'flat' : 'frown', lookX: glance ? -1 : 0, aL: -.75, aR: -1.15, sweat: after ? .8 : 0, shadow: false, blush: .2 });
    // Bannon's layered collars
    for (const [c, w] of [['#C9D6E8', .75], ['#2E3A5A', .55]]) solid([[1220 - w * s, gy - 4.85 * s], [1220 + w * s, gy - 4.85 * s], [1220, gy - 4.2 * s, 1]], c, { shade: false, line: IP.line, lw: 2.5, sharp: true });
    // the seat plank and pew ends
    solid(rrPts(320, seatY - 4, 1280, 46, 14), '#B8764A', { shade: '#8A5230', sh: 10, line: IP.line, lw: 5, sharp: true });
    for (const x of [320, 1600]) solid(rrPts(x - 34, 600, 68, 360, 30), '#8A5230', { shade: false, line: IP.line, lw: 5, sharp: true });
    // one shared slogan towel, held between them
    const tw = 380, ty = seatY - 12 + Math.sin(b * Math.PI) * 3;
    solid(rrPts(960 - tw / 2, ty - 32, tw, 64, 8), IP.neonPink, { shade: false, line: IP.line, lw: 4, sharp: true });
    dtext('PRO-HUMAN', 960, ty + 3, 40, { fill: IP.white, strokes: [[mixCol(IP.neonPink, IP.plum, .4), 7]], maxW: tw - 90 });
    // their inner hands grip the towel's corners (Bernie's in his mittens)
    const hA = .75, hy = gy - 4.25 * s + 2.1 * s * Math.sin(hA);
    solid(ellPts(700 + 1.05 * s + 2.1 * s * Math.cos(hA), hy, .52 * s, .5 * s, 18), '#C9975A', { shade: '#9A6A38', sh: 4, line: IP.line, lw: 3 });
    solid(ellPts(1220 - 1.05 * s - 2.1 * s * Math.cos(hA), hy, .44 * s, .44 * s, 16), CHIBI_SKIN[0], { shade: mixCol(CHIBI_SKIN[0], '#C0607A', .3), sh: 3, line: mixCol(CHIBI_SKIN[0], '#5A2030', .55), lw: 3 });
    camEnd();
    if (glance) sfx('...', 960, 560, { size: 60, pop: 1, rot: 0, shake: 0, grad: ['#FFFFFF', '#E6DCFF', '#C9B6FF'] });
    flash(lt, 0, .12, .5, '255 240 220');
  });

  // ============================================================= 11: Claude builds Claude =============================================================
  function wrench(x, y, s, rot) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot);
    solid(rrPts(-s * .15, -s * .1, s * 1.3, s * .2, s * .08), IP.silver, { shade: '#9AA0B8', sh: 3, line: IP.line, lw: 3, sharp: true });
    solid([[s * 1.1, -s * .32], [s * 1.55, -s * .28], [s * 1.62, -s * .08], [s * 1.36, -s * .06], [s * 1.36, s * .06], [s * 1.62, s * .08], [s * 1.55, s * .28], [s * 1.1, s * .32]], IP.silver, { shade: '#9AA0B8', sh: 3, line: IP.line, lw: 3 });
    ctx.restore();
  }
  V(11, (lt, d, t) => {
    const b = bpOf(t), e = BL() / 2;
    bgGrad('#0E3F3C', '#051416');
    patternBG('polka', 'rgb(0 0 0 / 0)', alpha('#062220', .8), { cell: 46 });
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; glow(960, 120, 800, IP.mint, .22); ctx.restore();
    ln([[960, -10], [960, 90]], '#10302E', 6); solid([[880, 130], [1040, 130], [1000, 90], [920, 90]], IP.neonGold, { shade: false, line: IP.line, lw: 4, sharp: true });
    camBegin(960, 540, settle(lt, 1.07) + lt * .02);
    // workbench
    const by = 700;
    solid(rrPts(600, by, 1060, 44, 8), '#C68A52', { shade: '#99623A', sh: 10, line: IP.line, lw: 5, sharp: true });
    for (const x of [640, 1620]) solid(rrPts(x - 18, by + 40, 36, 260, 6), '#8A5A34', { shade: false, line: IP.line, lw: 4, sharp: true });
    // big Clawd, hard hat, wrench
    const bo = { eyes: 'normal', mouth: 'smile', aR: .6 + Math.sin(b * Math.PI * 2) * .25, aL: -.3, dy: -Math.abs(Math.sin(b * Math.PI)) * .15, shadow: true };
    fanClawd(330, 965, 34, bo);
    clawdFrame(330, 965, 34, bo, () => hardHat());
    const ang = bo.aR, wx = 330 + (4.95 + Math.cos(-ang) * 2) * 34, wy = 965 + bo.dy * 34 + (-4.9 + Math.sin(-ang) * 2) * 34;
    wrench(wx, wy, 110, -ang - .6);
    // the chain: each Clawd builds the next, one per eighth, smaller and smaller
    const chain = [[830, 15], [1100, 7], [1232, 3.3], [1296, 1.55], [1327, .75]];
    chain.forEach(([x, u], i) => {
      const k = backOut(clamp((lt - i * e * .9) / .14), 2.6); if (k <= 0) return;
      const hammer = Math.max(0, Math.sin((b * 2 + i * .5) * Math.PI));
      const o = { eyes: i === 0 ? 'star' : 'normal', mouth: 'smile', aR: .2 + hammer * .9, aL: -.3, shadow: false };
      ctx.save(); ctx.translate(x, by); ctx.scale(k, k); ctx.translate(-x, -by);
      fanClawd(x, by, u, o); clawdFrame(x, by, u, o, () => hardHat());
      ctx.restore();
      if (i < 3 && hammer > .92) sfx('CLANK', x + u * 7, by - u * 12, { size: Math.max(26, u * 4), pop: 1, rot: -.2, shake: 1 });
    });
    if (lt > e * 4) { const k = clamp((lt - e * 4) / .3); for (let i = 0; i < 3; i++) { ctx.globalAlpha = k; ctx.fillStyle = IP.white; ctx.beginPath(); ctx.arc(1352 + i * 16, by - 6, 3.5, 0, TAU); ctx.fill(); ctx.globalAlpha = 1; } }
    // a tiny human supervises
    chibi(1760, 960, 22, { name: 'HUMAN', tagCol: IP.mint, hair: 'bun', hairCol: '#3A2A22', top: 'labcoat', glasses: 'round', eyes: 'dot', mouth: 'smile', aR: .2, hold: () => { solid(rrPts(-.2, -1.6, 1.6, 2.1, .15), '#C68A52', { shade: false, line: IP.line, lw: .12, sharp: true }); ctx.fillStyle = IP.white; ctx.fillRect(0, -1.3, 1.2, 1.6); } });
    camEnd();
    vtag('(a human supervises)', 1600, 640, { pop: K(lt, .6), rot: -.03, line: IP.mint, size: 28 });
    // the pie: Claude-led share of AI R&D
    const pk = easeOut(clamp(lt / .45)), px = 300, py = 300, r = 150;
    solid(ellPts(px, py, r + 10, r + 10, 40), IP.white, { shade: false, line: IP.line, lw: 5 });
    solid(ellPts(px, py, r, r, 40), '#3E5A58', { shade: false, line: false });
    const a0 = -Math.PI / 2, a1 = a0 + TAU * .26 * pk;
    ctx.beginPath(); ctx.moveTo(px, py); ctx.arc(px, py, r * (1 + .06 * pulse(t)), a0, a1); ctx.closePath(); ctx.fillStyle = '#E07B57'; ctx.fill(); ctx.strokeStyle = IP.white; ctx.lineWidth = 5; ctx.stroke();
    dtext(`${Math.round(26 * pk)}%`, px + 70, py - 60, 58, { fill: IP.white, strokes: [[IP.line, 10]] });
    dtext('CLAUDE-LED R&D', px, py + r + 46, 30, { fill: IP.white, strokes: [[IP.line, 8]] });
    flash(lt, 0, .12, .5, '220 255 240');
  });

  // ============================================================= 12: chatbot nearly starts a war =============================================================
  function jet(x, y, s, rot) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot); ctx.scale(s, s);
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; glow(-6.2, 0, 3.5, '#FF9A3D', .8); ctx.restore();
    solid([[-3, 0], [-.5, -4.2], [.6, -4.2], [.4, 0]], '#9AA7C8', { shade: false, line: IP.line, lw: .18, sharp: true });
    solid([[-3, 0], [-.5, 4.2], [.6, 4.2], [.4, 0]], '#9AA7C8', { shade: false, line: IP.line, lw: .18, sharp: true });
    solid([[-5.6, 0], [-4.8, -1.8], [-4, -1.8], [-4.2, 0]], '#8894B8', { shade: false, line: IP.line, lw: .16, sharp: true });
    solid([[-5.8, -.7], [3.2, -.8], [5.4, 0], [3.2, .8], [-5.8, .7]], '#C9D3EC', { shade: '#98A4C8', sh: .3, line: IP.line, lw: .2 });
    solid(ellPts(2.6, 0, .9, .38, 14), IP.sky, { shade: false, line: IP.line, lw: .12 });
    ctx.restore();
  }
  V(12, (lt, d, t) => {
    const b = bpOf(t), tj = BL() * .9, tc = BL() * 2, th = BL() * 2.6;
    bgGrad('#6A0A1E', '#12040A', { radial: true, cx: 700, cy: 500, r: 1200 });
    beam(960, -30, Math.sin(t * 6) * 1.0, { col: IP.red, alpha: .35, len: 1500, w: .18 });
    const hit = lt - tc, [sx, sy] = hit > 0 && hit < .35 ? shakeXY(t, 18 * (1 - hit / .35)) : [0, 0];
    camBegin(960 + sx, 540 + sy, settle(lt, 1.07));
    // radar
    const rx = 1370, ry = 420, rr = 230;
    solid(ellPts(rx, ry, rr + 16, rr + 16, 50), '#26324A', { shade: false, line: IP.line, lw: 6 });
    solid(ellPts(rx, ry, rr, rr, 50), '#052A1C', { shade: false, line: false });
    ctx.strokeStyle = alpha(IP.neonLime, .35); ctx.lineWidth = 2; for (let i = 1; i <= 3; i++) { ctx.beginPath(); ctx.arc(rx, ry, rr * i / 3.3, 0, TAU); ctx.stroke(); }
    ctx.beginPath(); ctx.moveTo(rx - rr, ry); ctx.lineTo(rx + rr, ry); ctx.moveTo(rx, ry - rr); ctx.lineTo(rx, ry + rr); ctx.stroke();
    const sa = t * 4; ctx.save(); ctx.globalCompositeOperation = 'lighter'; ctx.fillStyle = alpha(IP.neonLime, .25); ctx.beginPath(); ctx.moveTo(rx, ry); ctx.arc(rx, ry, rr, sa - .6, sa); ctx.closePath(); ctx.fill(); ctx.restore();
    const blip = .5 + .5 * Math.sin(t * 12);
    solid([[rx + 50, ry - 70], [rx + 150, ry - 70], [rx + 130, ry - 40], [rx + 70, ry - 40]], IP.neonLime, { shade: false, line: false, sharp: true });
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; glow(rx + 100, ry - 60, 60, IP.neonLime, .5 * blip); ctx.restore();
    dtext('SHIP', rx + 100, ry - 5, 26, { font: 'code', fill: IP.neonLime });
    // jets scramble … then turn back
    for (let i = 0; i < 3; i++) {
      const a0 = lt - tj - i * .08; if (a0 < 0) continue;
      const back = clamp((lt - tc - .1) / .35), fly = easeIn(clamp(a0 / .5)) * (1 - back * .6);
      const x = lerp(900 + i * 110, 1250 + i * 160, fly), y = lerp(1000, 520 - i * 70, fly);
      const rot = lerp(-1.1, -1.1 + Math.PI, easeOut(back));
      ln([[lerp(900 + i * 110, x, .2), lerp(1000, y, .2)], [x, y]], alpha(IP.white, .35), 12);
      jet(x, y, 19, rot);
    }
    // the cancel button, slammed
    const bx = 780, by = 830, press = hit > 0 ? 1 - clamp((hit - .15) / .3) * .3 : 0;
    solid(rrPts(bx - 150, by - 10, 300, 90, 20), '#3A3A58', { shade: false, line: IP.line, lw: 5, sharp: true });
    solid(ellPts(bx, by - 20 + press * 22, 120, 50, 36), '#FF3048', { shade: '#C01830', sh: 12, line: IP.line, lw: 5 });
    dtext('CANCEL', bx, by - 22 + press * 22, 40, { fill: IP.white, strokes: [[IP.line, 8]] });
    const hy = hit < 0 ? lerp(-300, by - 70, easeIn(clamp((lt - (tc - .22)) / .22))) : by - 70 + press * 22;
    if (lt > tc - .22) {
      ctx.save(); ctx.translate(bx, hy);
      solid(rrPts(-88, -640, 176, 480, 40), '#2E4A7A', { shade: '#1E3258', sh: 16, line: IP.line, lw: 5, sharp: true });
      solid(ellPts(-112, -40, 34, 56, 18, -.35), IP.skin, { shade: IP.skinSh, sh: 8, line: IP.skinLine, lw: 5 });
      solid([[-100, -150], [100, -150], [112, -80], [106, -8], [80, 36], [40, 44], [0, 46], [-40, 44], [-80, 36], [-106, -8], [-112, -80]], IP.skin, { shade: IP.skinSh, sh: 14, line: IP.skinLine, lw: 5 });
      for (let i = 0; i < 3; i++) ln([[-50 + i * 50, 0], [-50 + i * 50, 42]], alpha(IP.skinLine, .7), 5);
      solid(rrPts(-104, -200, 208, 60, 16), IP.white, { shade: '#D8D0EA', sh: 8, line: IP.line, lw: 5, sharp: true });
      ctx.restore();
    }
    // the hallucinating bot
    mascotBot(390, 930, 38, { label: 'BOT', face: 'spiral', mouth: 'wavy', col: '#C9C2F0', bulb: IP.red, sweat: 1, aL: .4 + Math.sin(t * 10) * .2, aR: .8, rot: Math.sin(t * 7) * .04 });
    camEnd();
    const kb = K(lt, .05, .18);
    if (kb > 0) { tail(390, 452, 400, 540, 34); chatBubble('THAT SHIP HAS NUKES!', 130, 400, { size: 44, maxW: 560, pop: kb }); }
    stampRect('HALLUCINATION', 520, 330, 50, clamp((lt - th) / .16), IP.red, -.12);
    sfx('WOOOSH!', 1280, 820, { size: 84, pop: clamp((lt - tj) / .12), rot: -.18 });
    if (hit > 0) sfx('SLAM!', 1000, 700, { size: 72, pop: clamp(hit / .1), rot: .12 });
    flash(lt, tc, .08, .3, '255 230 230');
  });

  // ============================================================= 13: "Super", by decree =============================================================
  V(13, (lt, d, t) => {
    const b = bpOf(t), e = BL() / 2, t0 = BL() * 1.5, ts = t0 + e * 3 + .05;
    bgGrad('#2E62C2', '#0C1F52');
    // a generic globe emblem with laurels
    ctx.save(); ctx.globalAlpha = .22; ctx.strokeStyle = IP.white; ctx.lineWidth = 8;
    ctx.beginPath(); ctx.arc(820, 360, 240, 0, TAU); ctx.stroke();
    for (const k of [.35, .7]) { ctx.beginPath(); ctx.ellipse(820, 360, 240 * k, 240, 0, 0, TAU); ctx.stroke(); }
    for (const k of [-.5, 0, .5]) { ctx.beginPath(); ctx.moveTo(820 - 240 * Math.sqrt(1 - k * k), 360 + k * 240); ctx.lineTo(820 + 240 * Math.sqrt(1 - k * k), 360 + k * 240); ctx.stroke(); }
    for (const sd of [-1, 1]) for (let i = 0; i < 9; i++) { const a = Math.PI / 2 + sd * (.35 + i * .27); ctx.beginPath(); ctx.ellipse(820 + Math.cos(a) * 300, 360 + Math.sin(a) * 300, 34, 14, a + sd * .8, 0, TAU); ctx.fillStyle = IP.white; ctx.fill(); }
    ctx.restore();
    camBegin(960, 540, settle(lt, 1.06) + lt * .015);
    // the speaker, the podium and the decree scroll
    const px = 640;
    chibi(px, 770, 38, { hair: 'swoop', hairCol: '#F2C94C', top: 'suit', topCol: '#1E2A5A', tie: IP.red, eyes: lt > ts ? 'happy' : 'smug', mouth: lt > ts ? 'grin' : 'open', aL: -.25, aR: -.25, shadow: false });
    const uk = easeOut(clamp((lt - .1) / .5)), sh = 360 * uk;
    solid([[px - 200, 640], [px + 200, 640], [px + 170, 1000], [px - 170, 1000]], '#3E2A6A', { shade: false, line: IP.line, lw: 6, sharp: true });
    solid(rrPts(px - 225, 618, 450, 36, 10), '#5A3E8A', { shade: false, line: IP.line, lw: 5, sharp: true });
    solid(ellPts(px, 780, 50, 50, 30), alpha(IP.white, .3), { shade: false, line: alpha(IP.white, .6), lw: 4 });
    solid(rrPts(px - 150, 640, 300, sh, 6), '#FFF3D6', { shade: '#EBD8AA', sh: 8, line: IP.line, lw: 4, sharp: true });
    if (sh > 80) dtext('DECREE', px, 682, 44, { fill: IP.red, strokes: [[IP.white, 6]] });
    if (sh > 170) dtext('AI SHALL BE', px, 745, 28, { font: 'archivo', fill: IP.ink });
    if (sh > 230) dtext('CALLED', px, 785, 28, { font: 'archivo', fill: IP.ink });
    if (sh > 300 && lt > ts) dtext('"SUPER"', px, 842, 44, { fill: IP.ink });
    solid(rrPts(px - 170, 630 + sh, 340, 34, 17), '#EBD8AA', { shade: false, line: IP.line, lw: 4, sharp: true });
    // TV poll: every option crossed out
    const gx = 1380, gy = 520;
    solid(rrPts(gx - 280, gy - 230, 560, 460, 26), IP.white, { shade: '#E4DEF2', sh: 10, line: IP.line, lw: 6, sharp: true, dropShadow: [12, 16] });
    ctx.save(); rrect(gx - 280, gy - 230, 560, 70, 26); ctx.clip(); ctx.fillStyle = IP.red; ctx.fillRect(gx - 280, gy - 230, 560, 70); ctx.restore();
    dtext('POLL: RENAME AI?', gx, gy - 195, 34, { fill: IP.white });
    [['SUPERIOR', .38], ['EXTREME', .21], ['SUPREME', .41]].forEach(([o, v], i) => {
      const y = gy - 95 + i * 110;
      solid(rrPts(gx - 240, y - 36, 480, 72, 36), '#EEE8FA', { shade: false, line: alpha(IP.line, .4), lw: 3, sharp: true });
      ctx.save(); rrect(gx - 240, y - 36, 480, 72, 36); ctx.clip(); ctx.fillStyle = alpha('#6A8BE8', .45); ctx.fillRect(gx - 240, y - 36, 480 * v * easeOut(clamp(lt / .4)), 72); ctx.restore();
      dtext(o, gx - 210, y + 2, 34, { align: 'left', fill: IP.ink });
      dtext(`${Math.round(v * 100)}%`, gx + 210, y + 2, 28, { align: 'right', font: 'code', fill: IP.inkSoft });
      const xk = clamp((lt - t0 - i * e) / .1);
      if (xk > 0) { ln([[gx - 250, y + 26], [lerp(gx - 250, gx + 250, xk), y - 22]], IP.red, 14); cross(gx + 150, y, 60 * backOut(xk, 3), IP.red, 12); }
    });
    camEnd();
    flash(lt, ts, .14, .7, '255 250 210');
    flash(lt, 0, .1, .45);
  });

  // ============================================================= 14: "Artificial"? Fake! =============================================================
  V(14, (lt, d, t) => {
    const tf = .1, tc = Math.min(.42, d * .36), tb = tc + .12;
    rays(960, 480, 18, '#D8203A', '#F2463E', t * .3);
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; glow(960, 460, 800, IP.neonGold, .3); ctx.restore();
    const hitT = lt - tf, [sx, sy] = hitT > 0 && hitT < .25 ? shakeXY(t, 14 * (1 - hitT / .25)) : [0, 0];
    camBegin(960 + sx, 540 + sy, settle(lt, 1.08));
    // the placard
    solid(rrPts(330, 250, 1260, 400, 40), IP.white, { shade: '#F0E4E8', sh: 14, line: IP.line, lw: 8, sharp: true, dropShadow: [14, 18] });
    dtext('INTELLIGENCE', 960, 545, 110, { fill: IP.ink, maxW: 1150 });
    const ck = clamp((lt - tc) / (tb - tc));
    if (ck < 1) {
      ctx.save(); ctx.translate(960, 370); ctx.scale(1 - ck * .8, 1 - ck * .5); ctx.rotate(Math.sin(ck * 14) * .08 * ck);
      dtext('ARTIFICIAL', 0, 0, 140, { fill: IP.neonPink, strokes: [[IP.line, 14]], maxW: 1150 });
      ctx.restore();
      hanko('FAKE!', 1330, 330, 130, clamp(hitT / .12) * (1 - ck), IP.red, -.25);
    } else {
      // crumpled into a ball and tossed
      const f = lt - tb, x = lerp(960, 1760, easeIn(clamp(f / .5))), y = 370 - Math.sin(clamp(f / .5) * Math.PI) * 180 - f * 200;
      const P = []; for (let i = 0; i < 14; i++) { const a = i / 14 * TAU, r = 80 * (.8 + hash2(i, 3) * .35); P.push([x + Math.cos(a) * r, y + Math.sin(a) * r, i % 2]); }
      solid(P, '#FFE0EE', { shade: '#F0B8D0', sh: 14, line: IP.line, lw: 5 });
      for (let i = 0; i < 5; i++) ln([[x + (hash2(i, 1) - .5) * 100, y + (hash2(i, 2) - .5) * 100], [x + (hash2(i, 4) - .5) * 60, y + (hash2(i, 5) - .5) * 60]], alpha(IP.line, .5), 3);
      const sk = clamp((f - .12) / .16);
      if (sk > 0) { ctx.save(); ctx.translate(960, 372); const sc = backOut(sk, 2.6); ctx.scale(sc, sc); ctx.rotate(-.04); dtext('SUPER', 0, 0, 150, { grad: ['#FFFBE0', '#FFE14D', '#FFB321'], strokes: [[IP.white, 30], [IP.line, 14]], shadow: [6, 10, 'rgb(20 8 40 / .35)'] }); ctx.restore(); }
      else dtext('?', 960, 370, 150, { fill: alpha(IP.inkSoft, .3) });
    }
    camEnd();
    const qk = K(lt, tb - .02, .16);
    if (qk > 0) { tail(900, 740, 720, 800, 34); chatBubble("\"IT'S ACTUALLY AMAZING\"", 590, 720, { size: 50, maxW: 900, pop: qk }); }
    idol(210, 965, 25, { sd: 1, ...IDOL_POSES.think, expr: 'think', ahoge: 'q', mic: false, blink: t, emote: 'q', emoteK: K(lt, .3) });
    flash(lt, tf, .1, .6, '255 240 240');
  });

  // ============================================================= 15: the date card itself: → D-DAY =============================================================
  function bigDateCard(x, y, sc, day, dn, age) {
    const w = 390, h = 104, M = MEMBERS.ADA;
    ctx.save(); ctx.translate(x, y); ctx.scale(sc, sc); ctx.rotate(-.012); ctx.translate(-w / 2, -h / 2);
    ctx.fillStyle = 'rgb(20 6 40 / .35)'; rrect(6, 8, w, h, 26); ctx.fill();
    ctx.fillStyle = IP.white; rrect(0, 0, w, h, 26); ctx.fill(); ctx.strokeStyle = dn <= 0 ? IP.neonPink : M.col; ctx.lineWidth = 5; ctx.stroke();
    const ix = 16, iy = 16, iw = 72, flip = clamp(age / .06);
    ctx.fillStyle = IP.white; rrect(ix, iy, iw, iw, 14); ctx.fill(); ctx.strokeStyle = IP.line; ctx.lineWidth = 3; ctx.stroke();
    ctx.save(); rrect(ix, iy, iw, iw, 14); ctx.clip(); ctx.fillStyle = dn <= 0 ? IP.neonPink : M.col; ctx.fillRect(ix, iy, iw, 22); ctx.restore();
    ctx.fillStyle = IP.white; for (const rx of [ix + 20, ix + iw - 20]) { ctx.beginPath(); ctx.arc(rx, iy + 11, 4.5, 0, TAU); ctx.fill(); }
    ctx.save(); ctx.translate(ix + iw / 2, iy + 49); ctx.scale(1, lerp(.2, 1, flip)); dtext(String(day), 0, 0, 32, { fill: IP.ink }); ctx.restore();
    dtext(`SEP ${day} 2026`, 106, 40, 30, { align: 'left', fill: IP.ink });
    const label = dn <= 0 ? 'D-DAY ♥ COMEBACK' : `COMEBACK D-${dn}`, lw2 = textW(label, 19, 'code') + 26;
    rrect(106, 60, lw2, 30, 15); ctx.fillStyle = dn <= 0 ? IP.neonPink : M.col; ctx.fill();
    dtext(label, 106 + lw2 / 2, 76, 19, { font: 'code', fill: IP.white });
    ctx.restore();
  }
  V(15, (lt, d, t) => {
    const b = bpOf(t), step = Math.min(.085, d * .055), day = Math.min(22, 12 + Math.floor(lt / step)), age = lt - (day - 12) * step, landed = day === 22;
    hideStamp();
    bgGrad('#401678', '#0E0520', { radial: true, cx: 960, cy: 380, r: 1100 });
    bokeh(t, { n: 14, r: 90, alpha: .25 });
    if (landed) { ctx.save(); ctx.globalCompositeOperation = 'lighter'; rays(960, 330, 20, 'rgb(0 0 0 / 0)', alpha(IP.neonPink, .12), t * .4); ctx.restore(); }
    camBegin(960, 540, settle(lt, 1.05));
    beam(960, -20, 0, { col: IP.lilac, alpha: .35, len: 1100, w: .1 });
    // the gift box, starting to shake
    const shk = landed ? 4 + 14 * clamp((age - .1) / .5) : 1.5;
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; glow(960, 900, 380, IP.neonPink, .35 + .2 * pulse2(t)); ctx.restore();
    ctx.fillStyle = 'rgb(10 4 24 / .5)'; ctx.beginPath(); ctx.ellipse(960, 955, 210, 30, 0, 0, TAU); ctx.fill();
    giftBox(960, 950, 29, { col: IP.neonPink, ribbon: IP.neonGold, shake: shk, lid: landed ? .06 * Math.abs(Math.sin(t * 30)) : 0 });
    const s0 = landed ? lerp(3.25, 2.85, easeOut(clamp(age / .25))) : 2.85 + .08 * Math.exp(-age * 30);
    bigDateCard(960, 380, s0, day, 22 - day, age);
    camEnd();
    pill(`DAYS SINCE "PACE": ${day - 12}`, 960, 110, 40, IP.ink, { font: 'code', line: IP.neonGold, k: 1 });
    if (landed) { for (let i = 0; i < 6; i++) { const a = i / 6 * TAU + .3, r = 560 + age * 300; sparkle(960 + Math.cos(a) * r, 380 + Math.sin(a) * r * .4, 34 * clamp(1 - age), a, IP.white); } }
    if (landed) flash(lt, (22 - 12) * step, .14, .8, '255 220 240');
  });

  // ============================================================= 16: Opus 5.5: "Hi, guys!" =============================================================
  V(16, (lt, d, t) => {
    const b = bpOf(t), t2 = Math.min(d * .55, BL() * 2.75);
    bgGrad(IP.night, IP.plum);
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; rays(960, 700, 16, 'rgb(0 0 0 / 0)', alpha(IP.neonGold, .08), t * .2); ctx.restore();
    beam(960, -20, 0, { col: IP.neonGold, alpha: .5, len: 1200, w: .16 });
    beam(1580, -20, 0, { col: IP.neonCyan, alpha: .45 * clamp((lt - t2 + .1) / .1), len: 1200, w: .1 });
    ctx.fillStyle = '#1C0E3A'; ctx.fillRect(-400, 960, W + 800, 300);
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; glow(960, 960, 420, IP.neonGold, .35); ctx.restore();
    camBegin(960, 540, settle(lt, 1.1, .2) + lt * .02);
    // the lid flies off
    const lf = lt;
    ctx.save(); ctx.translate(960 + lf * 520, 700 - lf * 900 + lf * lf * 1400); ctx.rotate(lf * 7);
    solid(rrPts(-150, -30, 300, 60, 12), IP.neonPink, { shade: mixCol(IP.neonPink, IP.plum, .3), sh: 10, line: IP.line, lw: 5, sharp: true }); bow(0, -34, 60, IP.neonGold, 5, 0);
    ctx.restore();
    // Clawd pops out, in his OPUS 5.5 sash, shy wave
    const up = backOut(clamp(lt / .28), 1.8), gy = lerp(1080, 785, up);
    const co = { eyes: lt > .5 ? 'happy' : 'wide', mouth: 'smile', blush: true, aR: .95 + Math.sin(t * 13) * .28, aL: -.55, sweat: lt > .6, dy: -Math.abs(Math.sin(b * Math.PI)) * .12 };
    ctx.save(); ctx.beginPath(); ctx.rect(0, -200, W, 948); ctx.clip();
    fanClawd(960, gy, 36, co); clawdFrame(960, gy, 36, co, () => clawdSash('OPUS 5.5'));
    ctx.restore();
    // the open box front
    solid(rrPts(800, 752, 320, 208, 10), IP.neonPink, { shade: mixCol(IP.neonPink, IP.plum, .3), sh: 18, line: IP.line, lw: 5, sharp: true });
    ctx.fillStyle = IP.neonGold; ctx.fillRect(946, 752, 28, 208);
    confetti(t, t - lt, 960, 760, -Math.PI / 2, { n: 70, seed: 161, speed: 1500, spread: 1.4 });
    // the second box, ninety minutes later
    const k2 = clamp((lt - t2) / .25);
    ctx.fillStyle = 'rgb(10 4 24 / .45)'; ctx.beginPath(); ctx.ellipse(1580, 962, 110, 16, 0, 0, TAU); ctx.fill();
    if (k2 > 0) mascotBot(1580, lerp(980, 830, backOut(k2, 1.8)), 20, { label: 'GPT-6', col: '#E6E8F0', face: 'happy', mouth: 'open', aR: 1.0 + Math.sin(t * 13) * .3, aL: -.8, shadow: false });
    giftBox(1580, 962, 13, { col: IP.neonCyan, ribbon: IP.white, lid: k2 > 0 ? 1.4 + (lt - t2) * 30 : 0, shake: k2 > 0 ? 0 : 3 * clamp((lt - t2 + .4) / .4) });
    pill('+90 MIN', 1580, 905, 30, IP.ink, { font: 'code', line: IP.neonCyan });
    // ATTN!: surprised → cheering
    const cheer = lt > t2 * .7;
    ['ADA', 'RELU', 'LOGI', 'TOKI'].forEach((m, i) => {
      const x = 130 + i * 150, pose = cheer ? (i % 2 ? IDOL_POSES.peace : IDOL_POSES.wave) : IDOL_POSES.shock;
      idol(x, 965, 18, { member: m, sd: 1, mic: false, ...pose, expr: cheer ? 'joy' : 'surprised', blink: t + i, bob: cheer ? .15 * pulse(t) : 0, jump: cheer ? Math.abs(Math.sin((b + i * .25) * Math.PI)) * .5 : 0 });
    });
    camEnd();
    const hk = K(lt, .32, .16);
    if (hk > 0) { tail(1210, 450, 1130, 540, 36); chatBubble('Hi, guys!', 1170, 380, { size: 66, maxW: 520, pop: hk }); }
    sparkles(t, { n: 12, x0: 700, x1: 1250, y0: 350, y1: 800, r: 26, seed: 33 });
    flash(lt, 0, .14, .9, '255 240 210');
  });
})();

;
// ---- styles/idol/ch/c09_finale.js ----
// c09_finale — Chorus 4 (the D-DAY stadium comeback, ~40 s with the "and on" tag folded in) and the outro.
// Sub-shots are timed from linesOf('C4') / linesOf('outro') and the beat grid:
//   A1 "We didn't start the scaling"         night stadium, fireworks; the LED wall is the date card, huge: D-DAY; ATTN! rise from
//                                              under-stage lifts in a column of light
//   A2   (on "scaling" + the gap)             the crowd: Clawd, still in his OPUS 5.5 sash, towel up, happy tears, fireworks behind
//   B  "It was always training,"              the photocard collection: one card per beat, each a callback to a verse (Attention,
//                                              ChatGPT, Sam's comeback, the whale, the lobster, Mythos, Opus 5.5) → 7/7 COMPLETE
//   C  "and the curves kept gaining,"         the LED curve goes vertical, bursts out of the wall and climbs through the stadium roof;
//                                              the camera tilts up after it past ×10, ×100, ×1,000 … into the stars
//   D  "We didn't start the scaling"          all the pyro: flame jets on the beats, cannons, the hook on the LED, the ocean in a rainbow wave
//   E1 "Now we swear we'll try to pace it —"  0.5× slow motion: TOKI with a halo and a PACE sign, hair floating, confetti crawling
//   E2 "but we'd rather race it!"            the checkered flag drops: 2×; ATTN! in go-karts overtake the V4.7 pace car
//   F  "We didn't start the scaling"          3·2·1 crouch, everyone jumps; freeze on the peak → the group photocard;
//                                              it lands in Clawd's nubs: ULTRA RARE PULL
//   G  "But when we log off… will it still train on?"   THANK YOU, HEADS → the lights go out bank by bank; an empty dark
//                                              stadium, TOKI walks off, one LED panel still reads TRAINING… EPOCH; she glances back
//   H  "and on, and on, and on…"              the practice room at dawn becomes an infinite mirror: TOKI dancing, reflected smaller and
//                                              smaller (front, back, front…), the camera flying through mirror after mirror, EPOCH climbing
//   I  outro                                   the mirror shrinks into the artwork of the album's back cover: tracklist + credits
(() => {
  const snap = x => onBeat(0, Math.round(bpOf(x)));
  const BL = () => 60 / BPM;
  const K = (t, t0, d = .2) => clamp((t - t0) / d);
  function plan() {
    const S = span('C4'), L = linesOf('C4'), O = linesOf('outro')[0] ?? { start: S.end - 4.3, end: S.end - .4 };
    const L6 = L[5], f6 = k => lerp(L6.start, L6.end, k);
    return {
      S, L, O,
      tA2: snap(lerp(L[0].start, L[0].end, .55)),
      tB: L[1].start - .05,
      tC: snap(lerp(L[1].start, L[1].end, .55)),
      tD: L[2].start - .05,
      tE: L[3].start - .03,
      tE2: lerp(L[3].start, L[3].end, .5),
      tF: L[4].start - .05,
      tJ: lerp(L[4].start, L[4].end, .45),          // "didn't": everyone jumps
      tFz: lerp(L[4].start, L[4].end, .45) + .3,     // freeze at the peak
      tF3: L[4].end,                                  // the photocard is pulled
      tG: L6.start - .05,
      tG2: f6(.056),                                  // "log off": the lights go out
      tG3: f6(.18),                                   // "will it still train on": the empty stadium
      tG4: f6(.258),                                  // TOKI glances back
      tH: f6(.334),                                   // "and on, and on…": the practice room at dawn
      tI: lerp(O.start, O.end, .7),                   // the album's back cover
      L6,
      onCycles: [[f6(.334), f6(.475)], [f6(.475), f6(.748)], [f6(.748), L6.end]],
    };
  }
  const flash = (t, t0, dur = .2, a = .75, col = '255 245 255') => { const k = (t - t0) / dur; if (k >= 0 && k < 1) { ctx.fillStyle = `rgb(${col} / ${(a * (1 - k) ** 2).toFixed(3)})`; ctx.fillRect(-400, -400, W + 800, H + 800); } };
  // Draw fn as if the song were at time tw (slow motion, double speed, freeze frames): swaps the global clock and boil.
  function atTime(tw, fn) {
    const sT = T, sB = _boil, sJ = _jitN;
    T = tw; _boil = boilFrame(tw); _jitN = 0;
    try { return fn(tw); } finally { T = sT; _boil = sB; _jitN = sJ; }
  }
  function pill(str, x, y, size, bg, o = {}) {
    const w = textW(str, size, o.font ?? 'rammetto') + size * 1.1, h = size * 1.6;
    ctx.save(); ctx.translate(x, y); if (o.rot) ctx.rotate(o.rot); if (o.k !== undefined) { if (o.k <= 0) { ctx.restore(); return; } const s = backOut(clamp(o.k), 2.2); ctx.scale(s, s); }
    rrect(-w / 2, -h / 2, w, h, h / 2); ctx.fillStyle = bg; ctx.fill(); ctx.strokeStyle = o.line ?? IP.white; ctx.lineWidth = size * .12; ctx.stroke();
    dtext(str, 0, size * .05, size, { font: o.font ?? 'rammetto', fill: o.ink ?? IP.white });
    ctx.restore();
  }

  // ---------------- the lyric subtitle for the long last line ----------------
  // The take sings "But when we log off, will it still train on" in the first third of L6's window and then "and on, and on…" for the
  // rest, so the automatic caption's karaoke wipe would crawl. This draws the same subtitle (after bloom + vignette, like the kit's) with
  // the wipe fitted to what is actually being sung.
  let _cap = null;
  OVERLAYS.push((t, s) => {
    const c = _cap; _cap = null;
    if (!c || !s || s.key !== 'C4') return;
    const { text, t0, t1, end } = c;
    const age = t - (c.a0 ?? t0), kin = easeOut(clamp(age / .14)), kout = clamp((end - t) / .18);
    const size = text.length > 44 ? 38 : 44, y = 1008, col = IP.neonPink, lt = '#FFE3F2';
    const chip = 'ATTN!', cs = size * .5, cw = textW(chip, cs, 'rammetto') + cs * 1.4;
    const tw0 = textW(text, size, 'rammetto', size * .03), sx = Math.min(1, (1600 - cw - 20) / tw0), tw = tw0 * sx;
    const x0 = W / 2 - (cw + 20 + tw) / 2;
    ctx.globalAlpha = kin * kout; ctx.translate(0, (1 - kin) * 18);
    rrect(x0, y - cs * .95, cw, cs * 1.9, cs * .95);
    const g = ctx.createLinearGradient(x0, 0, x0 + cw, 0); g.addColorStop(0, IP.neonPink); g.addColorStop(.5, IP.lilac); g.addColorStop(1, IP.neonCyan);
    ctx.fillStyle = g; ctx.fill(); ctx.strokeStyle = IP.white; ctx.lineWidth = 3; ctx.stroke();
    dtext(chip, x0 + cw / 2, y + cs * .06, cs, { fill: IP.white });
    const tx = x0 + cw + 20 + tw / 2, base = { maxW: tw + 1, spacing: size * .03 };
    dtext(text, tx, y, size, { ...base, strokes: [['rgb(24 8 44 / .9)', size * .3], [col, size * .16]], shadow: [0, size * .08, 'rgb(20 6 40 / .45)'], fill: IP.white });
    const prog = clamp((t - t0) / Math.max(.3, t1 - t0 - .1));
    if (prog > 0) { ctx.save(); ctx.beginPath(); ctx.rect(tx - tw / 2 - 4, y - size, (tw + 8) * prog, size * 2); ctx.clip(); dtext(text, tx, y, size, { ...base, grad: [IP.white, lt, lt] }); ctx.restore(); }
  });
  function lastLineCaption(t, P) {
    if (t > P.L6.end + .35) { hideCaption(); return; }
    hideCaption();
    if (t < P.tH) _cap = { text: 'But when we log off... will it still train on?', t0: P.L6.start, t1: P.tH - .15, end: P.tH + .05 };
    else { const [a, b] = P.onCycles.find(([a, b]) => t < b) ?? P.onCycles[2]; _cap = { text: 'And on, and on, and on...', t0: a, t1: b, a0: P.tH, end: t < P.onCycles[2][0] ? b + .5 : P.L6.end + .35 }; }
  }

  // =====================================================================================================
  // THE STADIUM
  // =====================================================================================================
  const FW_COLS = [IP.neonPink, IP.neonCyan, IP.neonGold, IP.neonLime, '#B98CFF', '#FF7AC0'];
  // Fireworks: shells launched on beats and eighths (deterministic); o: dens, x0, x1, y0, y1, r, ground
  function fireworks(t, o = {}) {
    const n1 = beatN(t), dens = o.dens ?? .7;
    ctx.save(); ctx.globalCompositeOperation = 'lighter';
    for (let n = n1 - 5; n <= n1; n++) for (let j = 0; j < 2; j++) {
      if (hash2(n, 70 + j) > dens) continue;
      const t0 = onBeat(0, n) + j * BL() / 2, age = t - t0; if (age < 0) continue;
      const x = lerp(o.x0 ?? 100, o.x1 ?? 1820, hash2(n, 71 + j)), y = lerp(o.y0 ?? 90, o.y1 ?? 360, hash2(n, 72 + j));
      const col = FW_COLS[Math.floor(hash2(n, 73 + j) * FW_COLS.length)], R = (o.r ?? 190) * (.7 + hash2(n, 74 + j) * .6), rise = .28;
      if (age < rise) { const sy = lerp(o.ground ?? 640, y, easeOut(age / rise)); ctx.fillStyle = alpha(col, .6); ctx.fillRect(x - 2, sy, 4, 70); ctx.fillStyle = IP.white; ctx.beginPath(); ctx.arc(x, sy, 5, 0, TAU); ctx.fill(); continue; }
      const a2 = age - rise, life = 1.6; if (a2 > life) continue;
      const fade = (1 - a2 / life) ** 1.4, dr = 1 - Math.exp(-4.5 * a2), dropY = 70 * a2 * a2;
      if (a2 < .15) glow(x, y, R * 1.3, col, .7 * (1 - a2 / .15));
      ctx.lineWidth = 4; ctx.lineCap = 'round';
      for (let i = 0; i < 30; i++) {
        const a = i / 30 * TAU + hash2(n, i + j * 40) * .15, rr = R * dr * (.8 + hash2(n + i, 5 + j) * .35), px = x + Math.cos(a) * rr, py = y + Math.sin(a) * rr + dropY;
        ctx.strokeStyle = alpha(col, fade * .55); ctx.beginPath(); ctx.moveTo(x + Math.cos(a) * rr * .72, y + Math.sin(a) * rr * .72 + dropY * .7); ctx.lineTo(px, py); ctx.stroke();
        const tw = hash2(i + n, Math.floor(t * 18)) > .25 ? 1 : .25;
        ctx.fillStyle = alpha(i % 3 ? col : IP.white, fade * tw); ctx.beginPath(); ctx.arc(px, py, 3 + 5 * fade, 0, TAU); ctx.fill();
      }
    }
    ctx.restore();
  }
  // The far stands: a dark bowl with rows of lightsticks (o.lit 0..1; o.mode 'sway' | 'wave' | 'rainbow'; o.cols)
  function stands(t, o = {}) {
    const y0 = o.y0 ?? 330, y1 = o.y1 ?? 640, b = bpOf(t), top = x => y0 + 90 * ((x - 960) / 960) ** 2;
    ctx.fillStyle = '#0C0724'; ctx.beginPath(); ctx.moveTo(-400, y1); ctx.lineTo(-400, top(-400)); for (let x = -400; x <= W + 400; x += 80) ctx.lineTo(x, top(x)); ctx.lineTo(W + 400, y1); ctx.closePath(); ctx.fill();
    ctx.strokeStyle = 'rgb(60 40 110 / .5)'; ctx.lineWidth = 2; for (let r = 1; r < 5; r++) { ctx.beginPath(); for (let x = -400; x <= W + 400; x += 80) { const y = lerp(top(x), y1, r / 5); x === -400 ? ctx.moveTo(x, y) : ctx.lineTo(x, y); } ctx.stroke(); }
    const lit = o.lit ?? 1; if (lit <= 0) return;
    const cols = o.cols ?? [MEMBERS.TOKI.col, MEMBERS.RELU.col, MEMBERS.ADA.col, MEMBERS.LOGI.col], mode = o.mode ?? 'sway';
    ctx.save(); ctx.globalCompositeOperation = 'lighter';
    for (let r = 0; r < 9; r++) {
      const u = (r + .5) / 9, n = 64 + r * 7, sz = 3 + u * 4;
      for (let i = 0; i < n; i++) {
        const x = (i + .5 + (hash2(r, i) - .5) * .6) / n * 2100 - 90, y = lerp(top(x), y1, u) - 6 + (hash2(i, r + 9) - .5) * 8;
        let k = .6, c = cols[Math.floor(hash2(i, r + 3) * cols.length)];
        if (mode === 'wave') k = .25 + .75 * Math.max(0, Math.sin((b * .5 - x / 700) * Math.PI));
        else if (mode === 'rainbow') { c = FW_COLS[((Math.floor(x / 160 - b * 2) % 6) + 6) % 6]; k = .5 + .5 * Math.sin(b * Math.PI + i * .2); }
        else k = .45 + .45 * Math.sin(b * Math.PI + hash2(i, r) * 3);
        if (o.sparse && hash2(i * 7 + r, 99) > o.sparse) continue;
        ctx.fillStyle = alpha(c, clamp(k * lit)); ctx.fillRect(x, y - Math.max(0, k - .6) * 8, sz, sz);
      }
    }
    ctx.restore();
  }
  // The stage floor in perspective (LED grid), from fy to the bottom.
  function stageFloor(t, o = {}) {
    const fy = o.fy ?? 600, hue = o.hue ?? IP.neonPink, b = bpOf(t), lit = o.lit ?? 1;
    const g = ctx.createLinearGradient(0, fy, 0, H); g.addColorStop(0, mixCol('#2A1250', '#08040F', 1 - lit)); g.addColorStop(1, '#0A0418');
    ctx.fillStyle = g; ctx.fillRect(-400, fy, W + 800, H - fy + 400);
    if (lit <= 0) return;
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; ctx.globalAlpha = lit;
    const rg = ctx.createLinearGradient(0, fy, 0, fy + 260); rg.addColorStop(0, alpha(hue, .45)); rg.addColorStop(1, alpha(hue, 0)); ctx.fillStyle = rg; ctx.fillRect(300, fy, 1320, 260);
    ctx.strokeStyle = alpha(IP.lilac, .22); ctx.lineWidth = 2; ctx.beginPath();
    for (let i = -16; i <= 16; i++) { ctx.moveTo(960 + i * 60, fy); ctx.lineTo(960 + i * 260, H + 200); }
    for (let j = 0; j < 7; j++) { const yy = fy + (H - fy) * ((j + frac(b * .5)) / 7) ** 1.8; ctx.moveTo(-400, yy); ctx.lineTo(W + 400, yy); }
    ctx.stroke(); ctx.restore();
    ctx.fillStyle = '#140A28'; ctx.fillRect(-400, fy - 8, W + 800, 12);
  }
  // Truss with moving heads above the stage; beams (level 4: many).
  function truss(t, o = {}) {
    const b = bpOf(t), p = pulse(t, 5), x0 = 330, x1 = 1590, y = 62, k = o.beamK ?? 1;
    const nb = 12, cols = o.beams ?? [IP.neonPink, IP.neonCyan, IP.neonGold, IP.lilac];
    if (k > 0) for (let i = 0; i < nb; i++) {
      const x = lerp(x0 + 40, x1 - 40, i / (nb - 1)), sd = i < nb / 2 ? 1 : -1;
      const a = sd * (.2 + .3 * Math.sin(b * Math.PI / 4 + i * .9)) + Math.sin(b * Math.PI / 2 + i) * .1;
      beam(x, y + 16, a, { col: cols[i % cols.length], alpha: (.26 + .2 * p) * k, len: 1300, w: .08 });
    }
    ctx.fillStyle = '#2A2440'; ctx.fillRect(x0, y - 16, x1 - x0, 32);
    ctx.strokeStyle = '#48406A'; ctx.lineWidth = 3; ctx.beginPath(); for (let x = x0; x < x1; x += 32) { ctx.moveTo(x, y - 16); ctx.lineTo(x + 16, y + 16); ctx.lineTo(x + 32, y - 16); } ctx.stroke();
    for (let i = 0; i < nb; i++) { const x = lerp(x0 + 40, x1 - 40, i / (nb - 1)); ctx.fillStyle = '#16122A'; rrect(x - 14, y + 6, 28, 22, 6); ctx.fill(); }
  }
  // The whole stadium, back to front (everything except performers and the front crowd). o: led (fn), side (fn), hue, fw (fireworks
  // density, 0 = none), standMode, lit (0..1 overall), beamK, banks ({beams, led, floor, stands} 0..1 for the lights-out)
  const LED = [520, 110, 880, 450];
  // night sky over a tall world range (fireworks and the vertical curve live above the stadium)
  function skyFill() {
    const g = ctx.createLinearGradient(0, -2400, 0, 640);
    g.addColorStop(0, '#000000'); g.addColorStop(.62, '#04020E'); g.addColorStop(.85, '#170A3E'); g.addColorStop(1, '#3A1A6B');
    ctx.fillStyle = g; ctx.fillRect(-900, -2800, W + 1800, 3440);
    ctx.fillStyle = '#3A1A6B'; ctx.fillRect(-900, 640, W + 1800, 900);
  }
  // the wide stadium camera: zoomed out so the sky (and its fireworks) shows above the LED wall
  const WIDE = .84;
  function stadium(t, o = {}) {
    const bk = o.banks ?? {}, lb = k => clamp(bk[k] ?? 1);
    if (!o.noSky) { skyFill();  sparkles(t, { n: 22, y0: 10, y1: 300, r: 7, seed: 51, cols: [IP.white, IP.lav] }); }
    if (o.fw) fireworks(t, { dens: o.fw, y0: -150, y1: 160, x0: -150, x1: 2070, r: 250, ground: 330 });
    stands(t, { mode: o.standMode, lit: lb('stands'), sparse: o.sparse });
    if (lb('led') > 0 || o.ledAlways) {
      ledWall(...LED, o.led ?? ((w, h) => ledShow('hearts', t, w, h)), { glow: o.hue ?? IP.neonPink, cols: 150, bright: o.ledAlways ? 1 : lb('led') });
      for (const [i, x] of [[0, 150], [1, 1510]]) ledWall(x, 190, 260, 340, o.side ? (w, h) => o.side(i, w, h) : (w, h) => { bgGrad(o.hue ?? IP.neonPink, IP.plum, { y1: h }); for (let j = 0; j < 8; j++) { const yy = frac(j / 8 - t * .6) * h; ctx.fillStyle = alpha(IP.white, .7); ctx.fillRect(0, yy, w, h / 18); } }, { cols: 30, bright: o.sideBright?.[i] ?? lb('led') });
    } else {
      ctx.fillStyle = '#0C0818'; ctx.fillRect(LED[0] - 14, LED[1] - 14, LED[2] + 28, LED[3] + 28); ctx.fillStyle = '#05030A'; ctx.fillRect(...LED);
      for (const [i, x] of [[0, 150], [1, 1510]]) { if (o.side && (o.sideBright?.[i] ?? 0) > 0) ledWall(x, 190, 260, 340, (w, h) => o.side(i, w, h), { cols: 70, bright: o.sideBright[i] }); else { ctx.fillStyle = '#0C0818'; ctx.fillRect(x - 14, 176, 288, 368); ctx.fillStyle = '#05030A'; ctx.fillRect(x, 190, 260, 340); } }
    }
    truss(t, { beamK: (o.beamK ?? 1) * lb('beams'), beams: o.beams });
    stageFloor(t, { hue: o.hue, lit: lb('floor') });
    const hz = ctx.createLinearGradient(0, 480, 0, 800); hz.addColorStop(0, 'rgb(200 180 255 / 0)'); hz.addColorStop(.5, `rgb(200 180 255 / ${(.12 * lb('floor')).toFixed(3)})`); hz.addColorStop(1, 'rgb(200 180 255 / 0)');
    ctx.fillStyle = hz; ctx.fillRect(-400, 480, W + 800, 320);
  }
  // Flame jet (pyro) at (x, y) of height hgt.
  function flame(x, y, hgt, t, seed = 0) {
    solid(rrPts(x - 34, y - 8, 68, 40, 8), '#2A2440', { shade: false, line: IP.line, lw: 3, sharp: true });
    if (hgt <= 4) return;
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; glow(x, y - hgt * .45, hgt * .9, '#FF7A1F', .55); ctx.restore();
    const wob = i => Math.sin(t * 34 + i * 1.7 + seed) * hgt * .045;
    const outer = [[x - hgt * .14, y - 6], [x - hgt * .2 + wob(1), y - hgt * .35], [x - hgt * .1 + wob(2), y - hgt * .72], [x + wob(3), y - hgt, 1], [x + hgt * .12 + wob(4), y - hgt * .66], [x + hgt * .2 + wob(5), y - hgt * .3], [x + hgt * .14, y - 6]];
    solid(outer, '#FF7A1F', { shade: false, line: false, grad: ['#FFE066', '#FF3A1F'] });
    solid(outer.map(([px, py, c]) => [x + (px - x) * .5, y - 6 + (py - y + 6) * .7, c]), '#FFF6C8', { shade: false, line: false });
  }
  // The date card, huge, for the LED (drawn in LED-wall coordinates).
  function ledDDay(t, w, h) {
    bgGrad('#2A0E52', '#12051F', { y1: h });
    ledShow('rays', t, w, h, { c0: '#2A0E52', c1: '#4A1C8A' });
    const cw = w * .8, ch = h * .5, x = (w - cw) / 2, y = h * .2, s = 1 + .03 * pulse(t, 5);
    ctx.save(); ctx.translate(w / 2, y + ch / 2); ctx.scale(s, s); ctx.translate(-w / 2, -(y + ch / 2));
    rrect(x, y, cw, ch, ch * .22); ctx.fillStyle = IP.white; ctx.fill(); ctx.strokeStyle = IP.neonPink; ctx.lineWidth = h * .025; ctx.stroke();
    const iw = ch * .72, ix = x + ch * .14, iy = y + ch * .14;
    rrect(ix, iy, iw, iw, iw * .18); ctx.fillStyle = IP.white; ctx.fill(); ctx.strokeStyle = IP.line; ctx.lineWidth = h * .012; ctx.stroke();
    ctx.save(); rrect(ix, iy, iw, iw, iw * .18); ctx.clip(); ctx.fillStyle = IP.neonPink; ctx.fillRect(ix, iy, iw, iw * .3); ctx.restore();
    dtext('22', ix + iw / 2, iy + iw * .64, iw * .5, { fill: IP.ink });
    dtext('D-DAY', x + ch * .98 + (cw - ch * 1.05) / 2, y + ch * .4, ch * .42, { fill: IP.neonPink, maxW: cw - ch * 1.1 });
    dtext('♥ COMEBACK ♥', x + ch * .98 + (cw - ch * 1.05) / 2, y + ch * .78, ch * .17, { font: 'code', fill: IP.ink, maxW: cw - ch * 1.1 });
    ctx.restore();
    sparkle(w * .88, h * .2, h * .08 * (.6 + .4 * pulse(t, 4)), t, IP.white);
  }
  // Clawd's accessories, in fanClawd's own frame
  function clawdFrame(x, y, u, o, fn) { ctx.save(); ctx.translate(x, y); ctx.scale(u, u); ctx.translate(0, (o.dy ?? 0) - (o.jump ?? 0)); if (o.rot) ctx.rotate(o.rot); fn(); ctx.restore(); }
  function clawdSash(str) {
    ctx.save(); ctx.beginPath(); ctx.rect(-5, -8, 10, 6); ctx.clip();
    solid([[-5.2, -4.25], [5.2, -3.05], [5.2, -1.85], [-5.2, -3.05]], IP.white, { shade: false, line: '#5A2A1C', lw: .18, sharp: true });
    ln([[-5.2, -4.05], [5.2, -2.85]], IP.neonGold, .16); ln([[-5.2, -3.25], [5.2, -2.05]], IP.neonGold, .16);
    dtext(str, -.2, -3.02, .88, { fill: IP.neonPink, rot: .115, maxW: 7 });
    ctx.restore();
    solid(ellPts(4.1, -2.35, .75, .75, 16), IP.neonGold, { shade: false, line: '#5A2A1C', lw: .16 });
    solid(ellPts(4.1, -2.35, .35, .35, 12), IP.neonPink, { shade: false, line: false });
  }
  const easeInOut = k => ease(k);

  // =====================================================================================================
  // A1: the stadium; ATTN! rise from the lifts; the LED is the date card: D-DAY
  // =====================================================================================================
  function shotA1(t, P) {
    const lt = t - P.S.start, d = P.tA2 - P.S.start, k = clamp(lt / d);
    const [sx, sy] = lt < .5 ? shakeXY(t, 8 * (1 - lt / .5)) : [0, 0];
    camBegin(960 + sx, 470 + sy - k * 10, WIDE + k * .05);
    setLight({ rim: IP.neonCyan });
    stadium(t, { led: (w, h) => ledDDay(t, w, h), fw: .95, hue: IP.neonPink, standMode: 'wave', beamK: .35 });
    // the four lifts: columns of light; the members rise out of the floor one after another
    const b0 = Math.round(bpOf(P.S.start));
    ['ADA', 'RELU', 'LOGI', 'TOKI'].forEach((m, i) => {
      const x = [600, 1080, 1320, 840][i], gy = 890 - (m === 'TOKI' ? 0 : 12), bt = onBeat(0, b0 + [0, .5, 1, 1.5][i]), rk = backOut(clamp((t - bt) / .45), 1.3);
      ctx.save(); ctx.globalCompositeOperation = 'lighter';
      const lk = clamp((t - bt + .2) / .2) * (1 - .6 * clamp((t - bt - .6) / .5));
      ctx.fillStyle = alpha(MEMBERS[m].col, .35 * lk); ctx.beginPath(); ctx.moveTo(x - 90, gy); ctx.lineTo(x + 90, gy); ctx.lineTo(x + 60, -50); ctx.lineTo(x - 60, -50); ctx.closePath(); ctx.fill();
      ctx.fillStyle = alpha(IP.white, .6 * lk); ctx.beginPath(); ctx.ellipse(x, gy, 110, 22, 0, 0, TAU); ctx.fill();
      ctx.restore();
      ctx.save(); ctx.beginPath(); ctx.rect(x - 300, -200, 600, gy + 206); ctx.clip();
      const s = m === 'TOKI' ? 35 : 32;
      idol(x, gy + (1 - rk) * s * 11, s, { member: m, ...(rk >= .98 ? idolMove('hook', bpOf(t) - i * .1) : IDOL_POSES[m === 'TOKI' ? 'point' : 'peace']), expr: rk >= .98 ? 'sing' : 'sparkle', mouth: singVis(t, i), blink: t + i, rim: MEMBERS[m].col, shadow: rk > .9 });
      ctx.restore();
      if (rk > .9) sparkles(t, { n: 4, x0: x - 90, x1: x + 90, y0: gy - s * 10, y1: gy, r: 16, seed: 60 + i, cols: [IP.white, IP.neonGold] });
    });
    lightOcean(t, { y0: 935, y1: 1130, n: 15, rows: 5, x0: -320, x1: W + 320, cols: [IP.neonPink, IP.neonCyan, IP.neonGold, IP.lilac], mode: 'pump', k: 1.2 });
    camEnd();
    flare(1460, 70, .6 + .3 * pulse(t, 4));
    flash(t, P.S.start, .3, .9);
  }

  // =====================================================================================================
  // A2: the crowd — Clawd, still in his OPUS 5.5 sash
  // =====================================================================================================
  function shotA2(t, P) {
    const lt = t - P.tA2, b = bpOf(t);
    bgGrad([[0, '#05020F'], [.6, '#1A0A40'], [1, '#3A1A6B']], null);
    fireworks(t, { dens: .95, y0: 80, y1: 420, r: 230, ground: 700 });
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; beam(500, -40, .35, { col: IP.neonPink, alpha: .35 }); beam(1400, -40, -.3, { col: IP.neonCyan, alpha: .35 }); ctx.restore();
    camBegin(960, 540, lerp(1.08, 1, easeOut(clamp(lt / .25))) + lt * .02);
    lightOcean(t, { y0: 540, y1: 1040, n: 12, rows: 6, cols: [IP.neonPink, IP.neonCyan, IP.neonGold, IP.lilac, IP.neonLime], mode: 'pump', k: 1.3 });
    const hop = Math.abs(Math.sin(b * Math.PI)) * 1.1;
    const co = { stick: 'L', aL: .9 + Math.sin(b * Math.PI) * .3, aR: .5 + Math.sin(t * 12) * .35, band: 'TOKI', eyes: 'heart', mouth: 'wail', tears: true, dy: -hop, shadow: false };
    // the fans either side have noticed who is standing next to them
    const nk = K(t, P.tA2 + .45, .2);
    chibi(470, 1010, 30, { hair: 'bob', hairCol: '#3A2A4E', top: 'hoodie', topCol: '#6A4AC8', eyes: nk > 0 ? 'spark' : 'happy', mouth: nk > 0 ? 'O' : 'open', aR: nk > 0 ? .25 : .9, aL: .9 + Math.sin(b * Math.PI) * .2, holdL: () => { ctx.scale(1 / 30, 1 / 30); lightstick(0, -40, 18, IP.lilac); }, lookX: .8, shadow: false, blush: .9, rim: IP.neonPink });
    chibi(1450, 1010, 30, { hair: 'ponytail', hairCol: '#6A3A2A', top: 'tee', topCol: IP.neonPink, eyes: nk > 0 ? 'spark' : 'happy', mouth: nk > 0 ? 'O' : 'open', aL: nk > 0 ? .7 : .9, aR: -.6, hold: undefined, holdL: nk > 0 ? () => { solid(rrPts(-.7, -1.6, 1.4, 2.4, .25), '#2B2438', { shade: false, line: IP.line, lw: .1, sharp: true }); ctx.fillStyle = frac(t * 2) < .5 ? IP.red : IP.white; ctx.beginPath(); ctx.arc(0, -1.2, .15, 0, TAU); ctx.fill(); } : undefined, lookX: -.8, shadow: false, blush: .9, rim: IP.neonCyan });
    if (nk > 0) { emote('bang', 560, 640, 60, nk); emote('bang', 1360, 640, 60, nk); }
    fanClawd(960, 955, 36, co);
    clawdFrame(960, 955, 36, co, () => clawdSash('OPUS 5.5'));
    camEnd();
    flash(t, P.tA2, .12, .6);
  }

  // =====================================================================================================
  // B: the photocard collection — one card per beat, each a callback to a verse
  // =====================================================================================================
  // card art, drawn in a 300 × 465 design space
  function whale(x, y, s, t) {
    ctx.save(); ctx.translate(x, y); ctx.scale(s, s);
    const sp = Math.sin(t * 8) * .1;
    for (let i = 0; i < 5; i++) { const a = -Math.PI / 2 + (i - 2) * .35; ln([[-.6, -1.4], [-.6 + Math.cos(a) * (1.2 + sp), -1.4 + Math.sin(a) * (1.2 + sp)]], '#9FE3FF', .22); }
    solid([[-2.7, .2], [-3.6, -.9], [-3.3, .15], [-3.7, 1.1]], '#3E6FF0', { shade: false, line: IP.line, lw: .09 });
    solid([[-2.8, .2], [-2.2, -1.1], [-.6, -1.5], [1.2, -1.2], [2.3, -.3], [2.4, .7], [1.4, 1.4], [-.8, 1.4], [-2.3, .9]], '#4A7BFF', { shade: '#2E55C8', sh: .25, line: IP.line, lw: .1, size: 3 });
    solid([[-1.9, .7], [-.5, 1.3], [1.5, 1.25], [2.25, .6], [1.2, .75], [-.6, .75]], '#DDE8FF', { shade: false, line: IP.line, lw: .07 });
    ctx.fillStyle = IP.ink; ctx.beginPath(); ctx.arc(1.3, -.2, .17, 0, TAU); ctx.fill(); ctx.fillStyle = IP.white; ctx.beginPath(); ctx.arc(1.25, -.26, .06, 0, TAU); ctx.fill();
    ctx.fillStyle = alpha('#FF7F91', .6); ctx.beginPath(); ctx.ellipse(1.7, .2, .3, .15, 0, 0, TAU); ctx.fill();
    ctx.restore();
  }
  function lobster(x, y, s, t) {
    ctx.save(); ctx.translate(x, y); ctx.scale(s, s);
    const red = '#F04A3A', dk = '#B82A20', o = { shade: dk, sh: .15, line: IP.line, lw: .09, size: 2 };
    for (const sd of [-1, 1]) { ln(qbez([sd * .3, -1.6], [sd * 1.5, -3.2], [sd * 2.4, -2.6], 8), IP.line, .08, { smooth: true }); }
    for (let i = 0; i < 3; i++) solid(ellPts(0, .9 + i * .55, .75 - i * .12, .35, 16), red, o);
    solid([[-.6, 2.4], [.6, 2.4], [.9, 2.9], [0, 2.75], [-.9, 2.9]], red, o);
    for (const sd of [-1, 1]) {
      const a = Math.sin(t * 7 + sd) * .15;
      ln([[sd * .6, -.3], [sd * 1.3, -.9], [sd * 1.6, -1.5]], dk, .28);
      ctx.save(); ctx.translate(sd * 1.7, -1.8); ctx.rotate(sd * (.3 + a));
      solid([[0, .5], [-.55, 0], [-.45, -.9], [-.1, -1.2], [0, -.5, 1], [.15, -1.2], [.55, -.9], [.6, 0]], red, o);
      ctx.restore();
    }
    solid(ellPts(0, -.3, .85, 1.05, 22), red, o);
    for (const sd of [-1, 1]) { ln([[sd * .3, -1.2], [sd * .4, -1.55]], IP.line, .07); solid(ellPts(sd * .42, -1.65, .2, .2, 12), IP.white, { shade: false, line: IP.line, lw: .06 }); ctx.fillStyle = IP.ink; ctx.beginPath(); ctx.arc(sd * .42, -1.63, .1, 0, TAU); ctx.fill(); }
    ctx.fillStyle = alpha('#FFB0A0', .7); ctx.beginPath(); ctx.ellipse(-.3, -.6, .15, .3, -.3, 0, TAU); ctx.fill();
    ctx.restore();
  }
  const CARDS = [
    { name: 'ATTENTION', m: 'TOKI', sign: '2017', art: (t) => { bgGrad(IP.lemon, IP.pink, { y1: 465 }); patternBG('stars', 'rgb(0 0 0 / 0)', alpha(IP.white, .5), { cell: 70 }); solid(rrPts(40, 70, 220, 290, 12), IP.white, { shade: '#EDE6F7', sh: 8, line: IP.line, lw: 4, sharp: true }); ['ATTENTION', 'IS ALL', 'YOU NEED'].forEach((w, i) => dtext(w, 150, 125 + i * 52, 36, { fill: i ? IP.ink : IP.neonPink, maxW: 190 })); for (let i = 0; i < 8; i++) solid(ellPts(70 + i * 23, 300, 10, 10, 12), CHIBI_SKIN[i % 6], { shade: false, line: IP.line, lw: 2 }); sparkle(245, 70, 26, t * 2, IP.white); sparkle(60, 390, 18, t * 3, IP.white); } },
    { name: 'CHATGPT', m: 'RELU', sign: '2022', art: (t) => { bgGrad('#1A1450', '#6A8BE8', { y1: 465 }); sparkles(t, { n: 8, x0: 10, x1: 290, y0: 10, y1: 200, r: 10, seed: 3 }); solid(ellPts(230, 80, 40, 40, 24), IP.lemon, { shade: false, line: false }); solid(ellPts(248, 70, 34, 34, 24), '#1A1450', { shade: false, line: false }); mascotBot(150, 420, 30, { label: 'GPT', face: 'happy', col: '#DDE3F5', antenna: false }); solid([[108, 140], [196, 140], [230, 95], [150, 70]], '#6AC8FF', { shade: false, line: IP.line, lw: 3 }); solid(ellPts(232, 92, 12, 12, 12), IP.white, { shade: false, line: IP.line, lw: 2 }); } },
    { name: 'SAM', m: 'ADA', sign: '2023', art: (t) => { bgGrad(IP.mint, IP.sky, { y1: 465 }); rays(150, 200, 14, 'rgb(0 0 0 / 0)', alpha(IP.white, .35), t * .3); chibi(150, 430, 30, { name: 'SAM', hair: 'short', hairCol: '#6A4A30', top: 'sweater', topCol: '#7A8FC8', eyes: 'happy', mouth: 'grin', aR: .6, hold: () => { for (let i = 0; i < 5; i++) solid(ellPts(Math.cos(i * 1.3) * .6, -1.2 + Math.sin(i * 1.3) * .4, .45, .45, 12), [IP.neonPink, IP.lemon, IP.white, '#FF7AC0', IP.lilac][i], { shade: false, line: IP.line, lw: .08 }); ln([[0, -.6], [0, .6]], '#2FA86A', .2); } }); dtext('COMEBACK!', 150, 70, 36, { fill: IP.neonGold, strokes: [[IP.line, 8]] }); } },
    { name: 'DEEPSEEK', m: 'LOGI', sign: '2025', art: (t) => { bgGrad('#FF6A5A', '#B81E3A', { y1: 465 }); for (let i = 0; i < 3; i++) { const x = 60 + i * 90; ln([[x, 0], [x, 40]], IP.neonGold, 3); solid(ellPts(x, 70, 30, 34, 16), '#FF3A2A', { shade: '#C01A1A', sh: 5, line: IP.line, lw: 3 }); } whale(150, 270, 38, t); ctx.save(); ctx.translate(210, 330); ctx.rotate(.2); solid(rrPts(-50, -22, 100, 44, 8), IP.neonGold, { shade: false, line: IP.line, lw: 3, sharp: true }); dtext('$5.6M', 0, 2, 26, { fill: IP.ink }); ctx.restore(); } },
    { name: 'OPENCLAW', m: 'TOKI', sign: '2026', art: (t) => { bgGrad(IP.peach, '#FF9A7A', { y1: 465 }); patternBG('polka', 'rgb(0 0 0 / 0)', alpha(IP.white, .4), { cell: 60 }); lobster(150, 250, 52, t); ctx.save(); ctx.translate(150, 300); ctx.rotate(-.35); solid(rrPts(-95, -16, 190, 32, 6), IP.white, { shade: false, line: IP.line, lw: 3, sharp: true }); dtext('OPENCLAW', 0, 2, 22, { fill: '#D0302A' }); ctx.restore(); } },
    { name: 'MYTHOS', m: 'RELU', sign: '2026', art: (t) => { bgGrad('#4A2A8A', '#1A0E3A', { y1: 465 }); ctx.fillStyle = '#E8D29A'; ctx.fillRect(0, 380, 300, 90); for (let i = 0; i < 12; i++) { ctx.fillStyle = alpha('#E8D29A', .8); ctx.beginPath(); ctx.arc(150 + (hash2(i, 1) - .5) * 200, 360 + hash2(i, 2) * 20 + frac(t + hash2(i, 3)) * 30, 5, 0, TAU); ctx.fill(); } mascotBot(170, 420, 27, { label: 'MYTHOS', col: IP.lilac, face: 'smug', mouth: 'smile', sq: -.12, rot: .12 }); for (let i = 0; i < 5; i++) solid(rrPts(20 + i * 62, 30, 14, 400, 7), '#8A8FA8', { shade: false, line: IP.line, lw: 3, sharp: true }); ctx.save(); ctx.globalCompositeOperation = 'lighter'; glow(60, 60, 90, IP.red, .5 * (Math.floor(t * 4) % 2)); ctx.restore(); } },
    { name: 'OPUS 5.5', m: 'LOGI', sign: '2026', art: (t) => { bgGrad(IP.pink, IP.lilac, { y1: 465 }); rays(150, 250, 16, 'rgb(0 0 0 / 0)', alpha(IP.white, .4), t * .3); const co = { eyes: 'happy', mouth: 'smile', aR: 1 + Math.sin(t * 12) * .3, aL: -.4, shadow: false }; fanClawd(150, 400, 22, co); clawdFrame(150, 400, 22, co, () => clawdSash('OPUS 5.5')); chatBubble('Hi, guys!', 60, 85, { size: 30, maxW: 220 }); } },
  ];
  function shotB(t, P) {
    const lt = t - P.tB, b0 = Math.round(bpOf(P.tB + .06)), n = CARDS.length;
    bgGrad(IP.lav, '#FFC2E0');
    patternBG('hearts', 'rgb(0 0 0 / 0)', alpha(IP.white, .5), { cell: 120, dx: t * 30, dy: t * 20 });
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; glow(960, 520, 900, IP.white, .25); ctx.restore();
    camBegin(960, 540, 1.04 - .04 * easeOut(clamp(lt / 2.5)));
    let landed = 0;
    CARDS.forEach((c, i) => {
      const tl = onBeat(0, b0 + i), age = t - (tl - .3);
      if (age < 0) return;
      const fly = easeOut(clamp(age / .3)), land = t >= tl;
      if (land) landed++;
      const sx = 960 + (i - (n - 1) / 2) * 262, sy = 500 + ((i - (n - 1) / 2) ** 2) * 9, sr = (i - (n - 1) / 2) * .05;
      const x = lerp(2250, sx, fly), y = lerp(260, sy, fly) - Math.sin(fly * Math.PI) * 60, rot = lerp(.7, sr, fly);
      const pk = land ? 1 + .12 * Math.exp(-(t - tl) * 12) : 1;
      photocard(x, y, 290 * pk, { rot, flip: lerp(1, 0, clamp(age / .3)), member: c.m, name: c.name, sign: c.sign, holo: .35, t, draw: (w, h) => { ctx.save(); ctx.scale(w / 300, w / 300); c.art(t); ctx.restore(); } });
      if (land && t - tl < .4) for (let j = 0; j < 4; j++) { const a = j / 4 * TAU + .5, r = 150 + (t - tl) * 300; sparkle(sx + Math.cos(a) * r * .7, sy + Math.sin(a) * r, 22 * (1 - (t - tl) / .4), a, IP.white); }
    });
    camEnd();
    // header
    attnLogo(250, 120, 70, {});
    dtext('PHOTOCARD COLLECTION', 420, 124, 40, { align: 'left', fill: IP.white, strokes: [[IP.line, 10], [IP.neonPink, 5]] });
    pill(`${landed}/${n}`, 1130, 124, 36, landed >= n ? IP.neonPink : IP.inkSoft, { font: 'code' });
    if (landed >= n) vcap('COMPLETE!', 1500, 850, { style: 'pink', size: 80, icon: 'heart', pop: K(t, onBeat(0, b0 + n - 1), .2), rot: -.06 });
    flash(t, P.tB, .12, .6);
  }

  // =====================================================================================================
  // C: the curve goes vertical and climbs through the roof
  // =====================================================================================================
  const TICKS = [[-80, '×10'], [-460, '×100'], [-840, '×1,000'], [-1220, '×10,000']];
  function shotC(t, P) {
    const lt = t - P.tC, d = P.tD - P.tC;
    const kL = clamp(lt / (d * .3)), kUp = clamp((lt - d * .28) / (d * .62)), tipY = lerp(LED[1] + 40, -1700, easeIn(kUp) * .35 + kUp * .65);
    const camY = Math.min(470, tipY + 260);
    // sky: screen-space gradient that darkens as we climb
    camBegin(960, camY, WIDE + (1 - WIDE) * clamp((470 - camY) / 400));
    skyFill();
    // stars and clouds above the stadium
    for (let i = 0; i < 60; i++) { const x = hash2(i, 1) * W, y = -1900 + hash2(i, 2) * 2100, tw = .5 + .5 * Math.sin(t * 3 + i); sparkle(x, y, (6 + hash2(i, 3) * 10) * tw, 0, IP.white, { glow: false }); }
    for (let i = 0; i < 5; i++) { const x = 200 + i * 380 + Math.sin(t * .5 + i) * 30, y = -620 - (i % 2) * 260; ctx.fillStyle = 'rgb(200 180 255 / .12)'; for (let j = 0; j < 4; j++) { ctx.beginPath(); ctx.ellipse(x + j * 70 - 100, y + (j % 2) * 20, 110, 50, 0, 0, TAU); ctx.fill(); } }
    fireworks(t, { dens: .6, y0: -700, y1: 300, r: 220, ground: 500 });
    stadium(t, { noSky: true, led: (w, h) => { ledShow('curve', t, w, h, { k: kL, level: 4 }); if (kL >= 1) { dtext('LEVEL 4', w * .2, h * .12, h * .09, { font: 'code', fill: IP.neonGold }); } }, hue: IP.neonCyan, standMode: 'wave' });
    // the stadium roof ring, high above
    ctx.fillStyle = '#1C1638'; ctx.fillRect(-400, -250, W + 800, 70);
    ctx.strokeStyle = '#3A3260'; ctx.lineWidth = 4; ctx.beginPath(); for (let x = -400; x < W + 400; x += 60) { ctx.moveTo(x, -250); ctx.lineTo(x + 30, -180); ctx.lineTo(x + 60, -250); } ctx.stroke();
    // the escaped curve: out of the LED top, straight up
    if (kUp > 0) {
      const x0 = LED[0] + LED[2] * .94, P2 = [[x0, LED[1] + 40]];
      for (let i = 1; i <= 30; i++) { const u = i / 30, y = lerp(LED[1] + 40, tipY, u); P2.push([x0 + Math.sin(u * 4) * 6 * (1 - u), y]); }
      ctx.save(); ctx.globalCompositeOperation = 'lighter'; ln(P2, alpha(IP.neonPink, .4), 70); ctx.restore();
      ln(P2, IP.neonPink, 26); ln(P2, IP.white, 8);
      sparkle(x0, tipY, 70, t * 4, IP.white); ctx.save(); ctx.globalCompositeOperation = 'lighter'; glow(x0, tipY, 220, IP.neonPink, .6); ctx.restore();
      // punching through the roof
      if (tipY < -200) { const age = clamp((-200 - tipY) / 300); for (let i = 0; i < 10; i++) { const a = -Math.PI / 2 + (hash2(i, 1) - .5) * 2.4, r = age * (80 + hash2(i, 2) * 200); solid(rrPts(x0 + Math.cos(a) * r - 10, -215 + Math.sin(a) * r + age * age * 200, 20, 12, 3), '#3A3260', { shade: false, line: IP.line, lw: 2, sharp: true }); } }
      for (const [y, lbl] of TICKS) { if (tipY > y + 20) continue; const k = clamp((y + 20 - tipY) / 120); ln([[x0 - 40, y], [x0 + 40, y]], IP.white, 6); pill(lbl, x0 - 170, y, 40, IP.neonPink, { k, font: 'code' }); }
    }
    // the group, pointing up after it
    group(t, 960, 890, 31, 'point', { gap: 160, back: 10, common: { rim: IP.neonPink, lookY: -1, expr: 'sparkle' } });
    lightOcean(t, { y0: 935, y1: 1130, n: 15, rows: 5, x0: -320, x1: W + 320, cols: [IP.neonCyan, IP.lilac, IP.neonPink], mode: 'wave' });
    camEnd();
    if (kUp > .55) vcap('IT WENT VERTICAL!!', 700, 250, { style: 'cyan', size: 76, pop: K(kUp, .55, .1), icon: 'bang', rot: -.05 });
  }

  // =====================================================================================================
  // D: all the pyro — flame jets on the beats, the hook on the LED, a rainbow wave
  // =====================================================================================================
  const HOOK = [['WE', 0, IP.white], ["DIDN'T", .12, IP.neonCyan], ['START', .3, IP.neonGold], ['THE', .42, IP.lilac], ['SCALING', .55, IP.neonPink]];
  function hookLED(t, ln0, w, h) {
    bgGrad('#12051F', '#2A0E52', { y1: h });
    ledShow('rays', t, w, h, { c0: '#1A0833', c1: '#2A0E52' });
    const dur = ln0.end - ln0.start, rows = [[0, 1, 2], [3, 4]];
    rows.forEach((row, r) => {
      let size = r ? h * .36 : h * .24, ws = row.map(i => textW(HOOK[i][0], size, 'rammetto') + size * .45);
      const fit = Math.min(1, w * .92 / ws.reduce((a, c) => a + c, 0)); size *= fit; ws = ws.map(v => v * fit);
      let x = w / 2 - ws.reduce((a, c) => a + c, 0) / 2;
      row.forEach((i, j) => {
        const [word, at, col] = HOOK[i], cx = x + ws[j] / 2; x += ws[j];
        const a = t - (wordTimes(ln0)?.starts[i] ?? ln0.start + at * dur); if (a < 0) return;   // (as it's sung, where the timing has the words' times)
        const s = backOut(clamp(a / .15), 2.5) * (i === 4 ? 1 + .06 * pulse(t, 6) : 1);
        ctx.save(); ctx.translate(cx, h * (r ? .66 : .3)); ctx.scale(s, s); dtext(word, 0, 0, size, { fill: col, strokes: [[IP.night, size * .22]] }); ctx.restore();
      });
    });
  }
  function shotD(t, P) {
    const lt = t - P.tD, b = bpOf(t), bt = onBeat(0, beatN(t)), age = t - bt;
    const [sx, sy] = age < .15 ? shakeXY(t, 7 * (1 - age / .15)) : [0, 0];
    camBegin(960 + sx, 470 + sy, WIDE + .03 - .03 * clamp(lt / 1.6));
    setLight({ rim: IP.neonGold });
    stadium(t, { led: (w, h) => hookLED(t, P.L[2], w, h), fw: 1, hue: IP.neonGold, standMode: 'rainbow', beams: [IP.neonGold, IP.neonPink, IP.neonCyan], beamK: .55 });
    const fh = 340 * Math.exp(-age * 5) * (age < .05 ? age / .05 : 1);
    [210, 560, 1360, 1710].forEach((x, i) => flame(x, 905, fh * (i % 2 ? .9 : 1), t, i));
    for (const [x, a] of [[120, -1.2], [1800, -1.95]]) confetti(t, P.tD + .05, x, 900, a, { n: 55, seed: 400 + x, speed: 1800 });
    group(t, 960, 895, 32, 'hook', { gap: 170, back: 10, common: { rim: IP.neonGold } });
    lightOcean(t, { y0: 935, y1: 1130, n: 15, rows: 5, x0: -320, x1: W + 320, cols: FW_COLS, mode: 'wave', k: 1.3 });
    camEnd();
    flare(1350, 60, .6 + .4 * pulse(t, 4), { col: '#FFD27A' });
    flash(t, P.tD, .18, .8, '255 240 200');
    hideCaption();
  }

  // =====================================================================================================
  // E: pace it (0.5× slow motion) → race it (2×)
  // =====================================================================================================
  function playerUI(t, speed, k, col) {
    // a video-player strip above the subtitle band
    ctx.save();
    ctx.fillStyle = 'rgb(10 4 24 / .55)'; ctx.fillRect(0, 900, W, 50);
    ctx.fillStyle = alpha(IP.white, .35); ctx.fillRect(170, 922, 1580, 6);
    const pos = lerp(170, 1750, .82 + .02 * Math.sin(t)); ctx.fillStyle = col; ctx.fillRect(170, 922, pos - 170, 6); ctx.beginPath(); ctx.arc(pos, 925, 11, 0, TAU); ctx.fill();
    ctx.fillStyle = IP.white; ctx.beginPath();
    if (speed < 1) { ctx.moveTo(70, 910); ctx.lineTo(96, 925); ctx.lineTo(70, 940); } else { for (const dx of [0, 22]) { ctx.moveTo(62 + dx, 910); ctx.lineTo(86 + dx, 925); ctx.lineTo(62 + dx, 940); } }
    ctx.fill();
    ctx.restore();
    ctx.save(); ctx.translate(1780, 860); const s = backOut(clamp(k), 2.4); ctx.scale(s, s);
    rrect(-110, -44, 220, 88, 26); ctx.fillStyle = col; ctx.fill(); ctx.strokeStyle = IP.white; ctx.lineWidth = 5; ctx.stroke();
    dtext(`${speed < 1 ? '0.5' : '2'}×`, 0, 3, 56, { font: 'code', fill: IP.white });
    ctx.restore();
  }
  function paceSign(x, y, s, t) {
    solid(rrPts(x - 1.8 * s, y - 1.0 * s, 3.6 * s, 2.0 * s, .25 * s), IP.white, { shade: '#E8E0F4', sh: .15 * s, line: IP.line, lw: .09 * s, sharp: true });
    dtext('PACE', x, y - .2 * s, 1.0 * s, { fill: IP.neonPink, strokes: [[IP.line, .14 * s]] });
    dtext('(we swear!)', x, y + .6 * s, .38 * s, { font: 'marker', fill: IP.inkSoft });
  }
  function shotE1(t, P) {
    const tw = P.tE + (t - P.tE) * .5, lt = t - P.tE;
    atTime(tw, tw => {
      const b = bpOf(tw);
      bgGrad('#1A0E48', '#3A1A6B');
      ctx.save(); ctx.globalCompositeOperation = 'lighter'; glow(960, 300, 900, IP.lilac, .3); ctx.restore();
      bokeh(tw, { n: 18, r: 110, alpha: .3, y0: 100, y1: 800 });
      camBegin(960, 540, 1.0 + lt * .03);
      // the others behind, floating in slow motion
      [['ADA', 520], ['RELU', 1400], ['LOGI', 1650]].forEach(([m, x], i) => idol(x, 900, 34, { member: m, ...idolMove('sway', b - i * .3), expr: 'smile', eyes: 'happy', mouth: 'smile', rim: IP.lilac, blink: tw + i, shadow: false }));
      // TOKI with her halo and her promise
      const R = idol(930, 1150, 80, { hL: [-1.95, 1.25], hR: [1.95, 1.25], gL: 'fist', gR: 'fist', eL: 1, eR: 1, expr: 'smile', eyes: 'happy', mouth: 'smile', blush: .8, tilt: -.06 + Math.sin(b * Math.PI * .5) * .05, swing: Math.sin(tw * 1.5) * .35, rim: IP.lilac, blink: undefined, sway: Math.sin(b * Math.PI * .5) * .1 });
      const hx = 930 + R.head.x * 80, hy = 1150 + R.head.y * 80 - R.head.h * 80 * .75;
      ctx.save(); ctx.globalCompositeOperation = 'lighter'; glow(hx, hy, 160, IP.neonGold, .5); ctx.restore();
      ctx.strokeStyle = IP.neonGold; ctx.lineWidth = 14; ctx.beginPath(); ctx.ellipse(hx, hy, 95, 24, 0, 0, TAU); ctx.stroke(); ctx.strokeStyle = IP.white; ctx.lineWidth = 5; ctx.stroke();
      paceSign(930 + R.chest[0] * 80, 1150 + (R.chest[1] + 1.35) * 80, 80, tw);
      confettiRain(tw, { n: 50, speed: 110 });
      camEnd();
    });
    // slow-mo grade + UI
    ctx.fillStyle = 'rgb(120 150 255 / .08)'; ctx.fillRect(0, 0, W, H);
    dtext('SLOW-MO', 110, 90, 34, { align: 'left', font: 'code', fill: IP.white, spacing: 8 });
    playerUI(t, .5, K(t, P.tE + .1), IP.neonCyan);
    flash(t, P.tE, .15, .5, '220 230 255');
  }
  function kart(x, y, s, member, t, o = {}) {
    const M = MEMBERS[member];
    ctx.save(); ctx.beginPath(); ctx.rect(x - 12 * s, y - 20 * s, 24 * s, 18.2 * s); ctx.clip();
    idol(x - .6 * s, y + 1.2 * s, s * 1.08, { member, sd: 1, mic: false, shadow: false, hL: [.9, .9], hR: [1.2, .8], gL: 'fist', gR: 'fist', blink: t + member.length, ...o.pose });
    ctx.restore();
    ctx.save(); ctx.translate(x, y); ctx.scale(s, s);
    for (const wx of [-3.4, 3.6]) { solid(ellPts(wx, -1.0, 1.15, 1.15, 18), '#2B2438', { shade: false, line: IP.line, lw: .2 }); ctx.save(); ctx.translate(wx, -1); ctx.rotate(o.spin ?? 0); ctx.fillStyle = IP.silver; ctx.fillRect(-.5, -.12, 1, .24); ctx.restore(); }
    solid([[-5.2, -1.2], [-5.0, -2.9], [-2.4, -3.2], [-.4, -2.5], [3.2, -2.4], [5.4, -1.9], [5.6, -1.1]], M.col, { shade: mixCol(M.col, IP.plum, .3), sh: .4, line: IP.line, lw: .2, size: 3 });
    solid(ellPts(-3.3, -2.3, .95, .95, 16), IP.white, { shade: false, line: IP.line, lw: .14 });
    dtext(o.num ?? '1', -3.3, -2.25, 1.05, { fill: IP.ink });
    ctx.restore();
  }
  function paceCar(x, y, s, t) {
    ctx.save(); ctx.beginPath(); ctx.rect(x - 400, -400, 800, y - 3.9 * s + 404); ctx.clip();
    chibi(x - 30, y - 3.9 * s + 2.6 * 34, 34, { name: 'DARIO', float: true, tagCol: IP.neonCyan, hair: 'curly', hairCol: '#3A2A22', glasses: 'round', top: 'sweater', topCol: '#2E3F7A', eyes: 'wide', mouth: 'O', sweat: 1, aR: .3 + Math.sin(t * 5) * .2, aL: .3, shadow: false });
    ctx.restore();
    ctx.save(); ctx.translate(x, y); ctx.scale(s, s);
    solid([[-5, -1.1], [-5.1, -2.3], [-3.2, -2.75], [-1.8, -4.3], [1.6, -4.35], [3.0, -2.9], [4.9, -2.5], [5.2, -1.1]], IP.neonGold, { shade: mixCol(IP.neonGold, IP.plum, .3), sh: .45, line: IP.line, lw: .2, size: 4 });
    solid([[.45, -2.9], [.45, -3.95], [1.4, -3.95], [2.4, -2.9]], '#CFEFFF', { shade: false, line: IP.line, lw: .14, sharp: true });
    for (const wx of [-2.9, 2.9]) solid(ellPts(wx, -1.05, 1.08, 1.08, 20), '#2B2438', { shade: false, line: IP.line, lw: .2 });
    dtext('PACE CAR', -.5, -1.95, .95, { fill: IP.white, strokes: [[IP.line, .25]] });
    ctx.restore();
  }
  function checkered(x, y, w, h, t, rot = 0) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot);
    ln([[0, 0], [0, h * 1.5]], '#6A5040', w * .06);
    const n = 6, m = 4, cw = w / n, ch = h / m;
    for (let i = 0; i < n; i++) for (let j = 0; j < m; j++) { const wv = Math.sin(i * .9 - t * 14) * h * .06 * (i / n); ctx.fillStyle = (i + j) % 2 ? IP.ink : IP.white; ctx.fillRect(i * cw, j * ch + wv, cw + 1, ch + 1); }
    ctx.strokeStyle = IP.line; ctx.lineWidth = 4; ctx.strokeRect(0, 0, w, h);
    ctx.restore();
  }
  function shotE2(t, P) {
    const lt = t - P.tE2, tw = P.tE2 + lt * 2, d = P.tF - P.tE2;
    atTime(tw, tw => {
      const b = bpOf(tw);
      bgGrad('#12083A', '#3A1A6B', { y1: 520 });
      // grandstand streaks
      ctx.fillStyle = '#1C0E3A'; ctx.fillRect(-100, 300, W + 200, 240);
      ctx.save(); ctx.globalCompositeOperation = 'lighter'; for (let i = 0; i < 60; i++) { const x = frac(hash2(i, 1) - tw * .9) * (W + 400) - 200, y = 320 + hash2(i, 2) * 200; ctx.fillStyle = alpha(FW_COLS[i % 6], .6); ctx.fillRect(x, y, 90, 4); } ctx.restore();
      const [sx, sy] = shakeXY(tw, 4);
      camBegin(960 + sx, 540 + sy, 1);
      ctx.fillStyle = '#2C2442'; ctx.fillRect(-400, 540, W + 800, 700);
      const off = (tw * 2600) % 120;
      for (let x = -400 - off; x < W + 400; x += 120) { ctx.fillStyle = (Math.round((x + off) / 120) % 2) ? IP.red : IP.white; ctx.fillRect(x, 530, 60, 22); ctx.fillRect(x + 60, 530, 60, 22); }
      ctx.fillStyle = IP.white; const o2 = (tw * 5200) % 300; for (let x = -400 - o2; x < W + 400; x += 300) ctx.fillRect(x, 760, 160, 10);
      // speed lines
      ctx.fillStyle = alpha(IP.white, .5); for (let i = 0; i < 16; i++) { const y = 580 + hash2(i, 3) * 380, x = frac(hash2(i, 4) - tw * 3) * (W + 800) - 400; ctx.fillRect(x, y, 260 + hash2(i, 5) * 300, 5); }
      // the pace car falls behind
      paceCar(lerp(1150, -600, easeIn(clamp(lt / (d * .55)))), 850, 44, tw);
      // ATTN! overtake, LOGI in front waving the flag
      ['TOKI', 'RELU', 'ADA', 'LOGI'].forEach((m, i) => {
        const x = lerp(-300 - i * 60, 380 + i * 360, easeOut(clamp((lt - (3 - i) * .06) / .55))) + Math.sin(tw * 3 + i) * 14, y = 885 - (i % 2) * 34;
        kart(x, y, 22, m, tw, { num: String(i + 1), spin: tw * 30, pose: { expr: i === 3 ? 'fired' : 'joy', mouth: 'teeth', lean: .12, ...(i === 3 ? { hR: [1.3, -.4], gR: 'fist' } : {}) } });
        if (i === 3) checkered(x + 22 * 1.3 * .75, y - 5.1 * 22 * 1.08, 170, 110, tw, -.15);
      });
      camEnd();
    });
    // the flag drops: a checkered wipe
    const wk = clamp(lt / .22);
    if (wk < 1) { ctx.save(); ctx.translate(0, lerp(-H * 1.2, H * 1.2, wk)); const c = 120; for (let i = 0; i < 17; i++) for (let j = 0; j < 10; j++) { ctx.fillStyle = (i + j) % 2 ? IP.ink : IP.white; ctx.fillRect(i * c, j * c - 600, c, c); } ctx.restore(); }
    playerUI(t, 2, K(t, P.tE2 + .05, .12), IP.neonPink);
    vcap('RACE!!', 560, 230, { style: 'shock', size: 150, pop: K(t, P.tE2 + .15, .12), shake: 5, rot: -.08, icon: 'bang' });
  }

  // =====================================================================================================
  // F: 3·2·1, everyone jumps; freeze on the peak → the group photocard → Clawd's ULTRA RARE pull
  // =====================================================================================================
  function jumpScene(t, P, still) {
    const b = bpOf(t), air = Math.max(0, Math.sin(clamp((t - P.tJ) / .62) * Math.PI)), crouch = t < P.tJ;
    const n = Math.ceil((P.tJ - t) / BL() - .05);
    stadium(t, { led: (w, h) => { if (crouch) { ledShow('text', t, w, h, { text: n <= 3 && n >= 1 ? String(n) : 'READY?', col: IP.neonGold, size: n <= 3 && n >= 1 ? h * .7 : h * .3 }); } else ledDDay(t, w, h); }, fw: crouch ? .3 : 1, hue: IP.neonPink, standMode: crouch ? 'sway' : 'rainbow' });
    if (!crouch) for (const [x, a] of [[140, -1.25], [560, -1.45], [1360, -1.7], [1780, -1.9]]) confetti(t, P.tJ, x, 880, a, { n: 45, seed: x + 7, speed: 1900 });
    group(t, 960, 895, 33, 'bounce', { gap: 170, back: 10, ripple: 0, common: crouch ? { bob: .55 + .05 * pulse(t), hL: [-.55, 2.1], hR: [.55, 2.1], gL: 'fist', gR: 'fist', expr: 'fired', mouth: 'teeth', rim: IP.neonCyan, lean: .08 } : { jump: air * 2.3, bob: 0, hL: [-1.2, -2.1], hR: [1.2, -2.1], gL: 'open', gR: 'open', fL: [-.6, -air * .6], fR: [.55, -air * .9], kL: 1, kR: 1, expr: 'joy', rim: IP.neonCyan, swing: -air * .5 } });
    lightOcean(t, { y0: 935, y1: 1130, n: 15, rows: 5, x0: -320, x1: W + 320, cols: [IP.neonPink, IP.neonGold, IP.neonCyan, IP.white], mode: 'pump', k: crouch ? .6 : 1.5 });
  }
  function shotF(t, P) {
    const tz = P.tFz;
    if (t < tz) {
      const lt = t - P.tF, push = easeInOut(clamp(lt / (P.tJ - P.tF)));
      const [sx, sy] = t > P.tJ ? shakeXY(t, 10 * (1 - clamp((t - P.tJ) / .3))) : [0, 0];
      camBegin(960 + sx, 520 + sy - push * 20, 1 + push * .08);
      setLight({ rim: IP.neonCyan });
      jumpScene(t, P, false);
      camEnd();
      if (t < P.tJ) vcap('ALL TOGETHER!', 960, 170, { style: 'yellow', size: 72, pop: K(t, P.tF + .15), rot: -.04, icon: 'heart' });
      else vcap('JUMP!!', 960, 190, { style: 'shock', size: 120, pop: K(t, P.tJ, .1), shake: 4, rot: -.06 });
      flash(t, P.tF, .12, .4);
      return;
    }
    // freeze → the frame becomes a photocard
    const fk = easeOut(clamp((t - tz) / .55)), pull = t - P.tF3;
    if (pull < 0) {
      bgGrad(IP.lav, IP.pink);
      patternBG('hearts', 'rgb(0 0 0 / 0)', alpha(IP.white, .5), { cell: 120, dy: t * 40 });
      const cw = lerp(W / .91 * 1.02, 520, fk), sc = lerp(1.08, 520 * .91 / 640, fk);
      ctx.save(); ctx.translate(960, 540 + Math.sin(t * 2.2) * 6 * fk); ctx.rotate(lerp(0, -.06, fk) + Math.sin(t * 1.7) * .015 * fk);
      photocard(0, 0, cw, { name: fk > .7 ? 'ATTN!' : false, sign: '♡ heads!', member: 'LOGI', holo: .6 * fk, t, draw: (w, h) => { ctx.save(); ctx.translate(w / 2, h / 2); ctx.scale(sc, sc); ctx.translate(-960, -500); atTime(tz, () => { setLight({ rim: IP.neonCyan }); jumpScene(tz, P, true); }); ctx.restore(); } });
      ctx.restore();
      if (fk > .6) { for (const [x, y, s] of [[1250, 250, 50], [680, 820, 34], [1300, 780, 28]]) sparkle(x, y, s * (.6 + .4 * Math.sin(t * 6 + x)), t * 2, IP.white); }
      flash(t, tz, .22, .95);
      return;
    }
    // the pull: the card lands in Clawd's nubs
    const b = bpOf(t);
    bgGrad([[0, '#05020F'], [.6, '#1A0A40'], [1, '#3A1A6B']], null);
    fireworks(t, { dens: .8, y0: 80, y1: 380 });
    lightOcean(t, { y0: 560, y1: 1040, n: 12, rows: 6, cols: [IP.neonPink, IP.neonGold, IP.lilac], mode: 'sway' });
    const up = backOut(clamp(pull / .3), 1.6), co = { eyes: 'star', mouth: 'wail', tears: true, aL: 1.25, aR: 1.25, dy: -Math.abs(Math.sin(b * Math.PI)) * .6, shadow: false };
    fanClawd(960, 1070, 34, co); clawdFrame(960, 1070, 34, co, () => clawdSash('OPUS 5.5'));
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; glow(960, 590, 340, IP.neonGold, .5 + .2 * pulse(t)); ctx.restore();
    photocard(960, lerp(-300, 560, up), 290, { rot: Math.sin(t * 3) * .05, name: 'ATTN!', sign: '♡ heads!', member: 'LOGI', holo: .9, t, draw: (w, h) => { ctx.save(); ctx.translate(w / 2, h / 2); ctx.scale(w / 640, w / 640); ctx.translate(-960, -500); atTime(tz, () => { setLight({ rim: IP.neonCyan }); jumpScene(tz, P, true); }); ctx.restore(); } });
    for (let i = 0; i < 8; i++) { const a = i / 8 * TAU + t, r = 230 + Math.sin(t * 4 + i) * 20; sparkle(960 + Math.cos(a) * r, 590 + Math.sin(a) * r * 1.2, 22, a, i % 2 ? IP.neonGold : IP.white); }
    vcap('ULTRA RARE PULL!!', 820, 130, { style: 'pink', size: 76, pop: K(t, P.tF3 + .25, .15), icon: 'spark', rot: -.04 });
  }

  // =====================================================================================================
  // G: log off — THANK YOU → the lights go out bank by bank → an empty stadium; one panel still trains
  // =====================================================================================================
  function trainingPanel(t, P, w, h) {
    bgGrad('#041A12', '#02100A', { y1: h });
    const ep = 10240 + Math.floor((t - P.tG) * 9);
    dtext('TRAINING', w / 2, h * .22, h * .12, { font: 'code', fill: IP.neonLime });
    for (let i = 0; i < 3; i++) { ctx.fillStyle = frac(t * 2 - i * .25) < .5 ? IP.neonLime : alpha(IP.neonLime, .2); ctx.fillRect(w / 2 - h * .12 + i * h * .1, h * .32, h * .05, h * .05); }
    dtext('EPOCH', w / 2, h * .52, h * .1, { font: 'code', fill: alpha(IP.neonLime, .8) });
    dtext(fmtN(ep), w / 2, h * .68, h * .15, { font: 'code', fill: IP.white, maxW: w * .9 });
    ctx.fillStyle = alpha(IP.neonLime, .25); ctx.fillRect(w * .1, h * .84, w * .8, h * .04); ctx.fillStyle = IP.neonLime; ctx.fillRect(w * .1, h * .84, w * .8 * frac(t * .7), h * .04);
  }
  function shotG(t, P) {
    const b = bpOf(t);
    lastLineCaption(t, P);
    if (t < P.tG3) {
      // bows, then the banks switch off on the beats
      const b0 = Math.ceil(bpOf(P.tG2)), off = i => t >= onBeat(0, b0 + i) ? 1 : 0;
      const banks = t < P.tG2 ? {} : { beams: 1 - off(0), led: 1 - off(1), floor: 1 - off(2), stands: 1 - off(3) };
      const dark = t < P.tG2 ? 0 : (off(0) + off(1) + off(2) + off(3)) / 4;
      camBegin(960, 520, 1 + clamp((t - P.tG) / 3) * .04);
      setLight({ rim: dark < .5 ? IP.lilac : null });
      stadium(t, { led: (w, h) => { if (t < P.tG2 + BL() * .8) ledShow('text', t, w, h, { text: 'THANK YOU, HEADS!', col: IP.neonPink, size: h * .2 }); else { ctx.fillStyle = '#0A0418'; ctx.fillRect(0, 0, w, h); ctx.strokeStyle = IP.white; ctx.lineWidth = h * .05; ctx.beginPath(); ctx.arc(w / 2, h * .48, h * .2, -Math.PI / 2 + .6, -Math.PI / 2 - .6 + TAU); ctx.stroke(); ctx.beginPath(); ctx.moveTo(w / 2, h * .22); ctx.lineTo(w / 2, h * .46); ctx.stroke(); dtext('LOG OFF', w / 2, h * .84, h * .11, { font: 'code', fill: IP.white }); } }, fw: t < P.tG2 ? .3 : 0, hue: IP.lilac, standMode: 'sway', banks, beamK: .7 });
      const bow = clamp((t - P.tG) / .5) * (1 - clamp((t - P.tG2) / .4));
      group(t, 960, 895, 32, 'idle', { gap: 170, back: 10, common: { lean: .35 * bow, nod: .6 * bow, hL: [-.25, 1.6], hR: [.25, 1.6], gL: 'flat', gR: 'flat', expr: 'joy', rim: IP.lilac, bob: .05 } });
      lightOcean(t, { y0: 935, y1: 1130, n: 15, rows: 5, x0: -320, x1: W + 320, cols: [IP.neonPink, IP.lilac], mode: 'sway', k: .6 });
      camEnd();
      if (dark > 0) { ctx.fillStyle = `rgb(3 1 8 / ${(dark * .78).toFixed(3)})`; ctx.fillRect(0, 0, W, H); }
      for (let i = 0; i < 4; i++) { const tb = onBeat(0, b0 + i); if (t >= tb && t < tb + .3 && t >= P.tG2) sfx('CLICK', 360 + i * 400, 180 + (i % 2) * 60, { size: 54, pop: clamp((t - tb) / .08), rot: -.1, grad: ['#FFFFFF', '#E6DCFF', '#9A86D8'] }); }
      return;
    }
    if (t < P.tG4) {
      // the empty dark stadium; TOKI walks off; one panel still trains; a few lightsticks never went out
      const lt = t - P.tG3;
      camBegin(960, 520, 1.02);
      stadium(t, { banks: { beams: 0, led: 0, floor: 0, stands: .9 }, sparse: .06, side: (i, w, h) => trainingPanel(t, P, w, h), sideBright: [1, 0] });
      ctx.save(); ctx.globalCompositeOperation = 'lighter'; glow(280, 360, 420, IP.neonLime, .18); beam(1180 + lt * 60, -20, 0, { col: IP.lilac, alpha: .18, len: 1000, w: .07 }); ctx.restore();
      const x = 1080 + lt * 150, wk = bpOf(t) * .5;
      idol(x, 890, 30, { back: true, hL: [-.9, 2.6 + Math.sin(wk * TAU) * .2], hR: [.9, 2.6 - Math.sin(wk * TAU) * .2], fL: [-.3 + Math.sin(wk * TAU) * .25, Math.min(0, -Math.sin(wk * TAU) * .25)], fR: [.3 - Math.sin(wk * TAU) * .25, Math.min(0, Math.sin(wk * TAU) * .25)], shadow: true, swing: Math.sin(wk * TAU) * .1 });
      camEnd();
      ctx.fillStyle = 'rgb(3 1 8 / .35)'; ctx.fillRect(0, 0, W, H);
      for (let i = 0; i < 9; i++) { const x = 80 + i * 220 + (hash2(i, 1) - .5) * 120, y = 975 + hash2(i, 2) * 70; lightstick(x, y, 16 + hash2(i, 3) * 6, [IP.neonPink, IP.lilac, IP.neonLime, MEMBERS.TOKI.col][i % 4], { rot: Math.sin(t * 1.6 + i) * .35 }); }
      ctx.save(); ctx.globalCompositeOperation = 'lighter'; glow(280, 360, 260, IP.neonLime, .25); ctx.restore();
      setBloom(.9);
      return;
    }
    // TOKI glances back over her shoulder, lit by the panel
    const lt = t - P.tG4, turn = easeOut(clamp(lt / .35));
    bgGrad('#060312', '#120828');
    bokeh(t, { n: 14, r: 70, alpha: .28, cols: [IP.neonPink, IP.lilac, IP.neonLime], y0: 500, y1: 1000 });
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; glow(250, 420, 700, IP.neonLime, .22); ctx.restore();
    setLight({ x: -.9, y: -.3, rim: IP.neonLime, rimX: -.9, rimY: -.2 });
    camBegin(960, 540, 1 + lt * .03);
    const dwin = P.tH - P.tG4, wink = lt > dwin * .68;
    idol(1060, 470, 200, { anchor: 'face', turn: lerp(.55, -.35, turn), tilt: lerp(.12, .04, turn), lookX: lerp(.6, -.85, turn), expr: 'smile', mouth: wink ? 'smile' : 'closed', ahoge: wink ? 'heart' : 'q', blush: wink ? .85 : .5, eyes: 'open', wink: wink ? 'R' : undefined, lid: wink ? 0 : .15, hL: [-.9, 2.7], hR: [.9, 2.7], swing: lerp(.25, -.1, turn), mic: false, rim: IP.neonLime });
    camEnd();
    // the panel she's looking at, out of focus at the left edge
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; glow(120, 460, 420, IP.neonLime, .3); ctx.restore();
    ctx.save(); ctx.globalAlpha = .55; rrect(-40, 250, 400, 440, 30); ctx.fillStyle = '#0A2A1A'; ctx.fill(); ctx.strokeStyle = alpha(IP.neonLime, .5); ctx.lineWidth = 8; ctx.stroke();
    dtext('EPOCH', 170, 400, 56, { font: 'code', fill: IP.neonLime }); dtext(fmtN(10240 + Math.floor((t - P.tG) * 9)), 170, 490, 64, { font: 'code', fill: IP.white }); ctx.restore();
    if (wink) sparkle(1250, 330, 40 * K(t, P.tG4 + dwin * .68, .15), t * 3, IP.white);
    setBloom(.9);
  }

  // =====================================================================================================
  // H: the practice room at dawn → the infinite mirror
  // =====================================================================================================
  const VP = [960, 430], RR = .6, MR = [392, 180, 1136, 634];   // vanishing point, mirror scale per level, mirror rect (level space)
  function roomRing(k, t, alive) {
    // walls, floor, ceiling and the window of one level (everything outside the mirror), in level space
    const [mx, my, mw, mh] = MR, mx1 = mx + mw, my1 = my + mh;
    ctx.save(); ctx.beginPath(); ctx.rect(-40, -40, W + 80, H + 80); ctx.rect(mx, my, mw, mh); ctx.clip('evenodd');
    ctx.fillStyle = '#EAD9F2'; ctx.beginPath(); ctx.moveTo(-40, -40); ctx.lineTo(W + 40, -40); ctx.lineTo(mx1 + 30, my - 30); ctx.lineTo(mx - 30, my - 30); ctx.closePath(); ctx.fill();   // ceiling
    ctx.fillStyle = '#DCC6EE'; ctx.beginPath(); ctx.moveTo(-40, -40); ctx.lineTo(mx - 30, my - 30); ctx.lineTo(mx - 30, my1); ctx.lineTo(-40, H + 40); ctx.closePath(); ctx.fill();         // left wall
    ctx.beginPath(); ctx.moveTo(W + 40, -40); ctx.lineTo(mx1 + 30, my - 30); ctx.lineTo(mx1 + 30, my1); ctx.lineTo(W + 40, H + 40); ctx.closePath(); ctx.fill();                            // right wall
    ctx.fillStyle = '#F2E6F8'; ctx.fillRect(mx - 30, my - 30, mw + 60, 30); ctx.fillRect(mx - 30, my, 30, mh); ctx.fillRect(mx1, my, 30, mh);                                                 // back wall margin
    const fg = ctx.createLinearGradient(0, my1, 0, H); fg.addColorStop(0, '#E0B48A'); fg.addColorStop(1, '#C48A5E');
    ctx.fillStyle = fg; ctx.beginPath(); ctx.moveTo(mx - 30, my1); ctx.lineTo(mx1 + 30, my1); ctx.lineTo(W + 40, H + 40); ctx.lineTo(-40, H + 40); ctx.closePath(); ctx.fill();          // floor
    ctx.strokeStyle = 'rgb(120 70 40 / .3)'; ctx.lineWidth = 3; ctx.beginPath(); for (let i = -10; i <= 10; i++) { ctx.moveTo(VP[0] + i * 58, my1); ctx.lineTo(VP[0] + i * 230, H + 40); } ctx.stroke();
    ctx.fillStyle = '#B99AD8'; ctx.fillRect(mx - 30, my1 - 6, mw + 60, 14);
    // window on the left wall: dawn
    ctx.save(); ctx.beginPath(); ctx.moveTo(60, 170); ctx.lineTo(290, 230); ctx.lineTo(290, 560); ctx.lineTo(60, 640); ctx.closePath();
    const wg = ctx.createLinearGradient(0, 170, 0, 640); wg.addColorStop(0, '#FFB3D6'); wg.addColorStop(.6, '#FFD7A8'); wg.addColorStop(1, '#FFF1C8'); ctx.fillStyle = wg; ctx.fill();
    ctx.clip(); ctx.fillStyle = '#FF9A7A'; ctx.beginPath(); ctx.arc(170, 560, 70, 0, TAU); ctx.fill(); ctx.restore();
    ctx.strokeStyle = '#8A6AAE'; ctx.lineWidth = 8; ctx.beginPath(); ctx.moveTo(60, 170); ctx.lineTo(290, 230); ctx.lineTo(290, 560); ctx.lineTo(60, 640); ctx.closePath(); ctx.moveTo(175, 200); ctx.lineTo(175, 600); ctx.stroke();
    // sunlight on the floor
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; ctx.fillStyle = 'rgb(255 190 140 / .16)'; ctx.beginPath(); ctx.moveTo(290, 560); ctx.lineTo(60, 640); ctx.lineTo(700, H + 40); ctx.lineTo(1200, H + 40); ctx.closePath(); ctx.fill(); ctx.restore();
    // barre on the right wall
    ln([[mx1 + 40, my1 - 120], [W + 40, my1 - 40]], '#C68A52', 16); ln([[mx1 + 40, my1 - 120], [W + 40, my1 - 40]], alpha(IP.white, .4), 4);
    ctx.restore();
    // the mirror frame and its EPOCH sign
    ctx.strokeStyle = '#9C8CB8'; ctx.lineWidth = 12; ctx.strokeRect(mx - 6, my - 6, mw + 12, mh + 12);
    rrect(VP[0] - 150, my - 88, 300, 64, 14); ctx.fillStyle = '#1C1438'; ctx.fill(); ctx.strokeStyle = IP.white; ctx.lineWidth = 4; ctx.stroke();
    dtext(`EPOCH ${fmtN(10240 * 2 ** k)}`, VP[0], my - 55, 32, { font: 'code', fill: IP.neonLime, maxW: 280 });
    // Clawd, asleep in the corner, lightstick still on
    const co = { eyes: 'closed', mouth: 'none', stick: 'R', aR: .2, aL: -.3, shadow: true };
    fanClawd(230, 1000, 11, co);
    dtext('z', 330, 840 - frac(t * .8) * 40, 34, { font: 'bungee', fill: alpha(IP.inkSoft, 1 - frac(t * .8)) }); dtext('z', 360, 800 - frac(t * .8 + .5) * 40, 26, { font: 'bungee', fill: alpha(IP.inkSoft, 1 - frac(t * .8 + .5)) });
  }
  // who is dancing in mirror k: TOKI alone at first; the deeper (later) the epoch, the more of ATTN! have joined her
  const CREW = [['TOKI', 690, 0], ['RELU', 1235, 2], ['ADA', 465, 4], ['LOGI', 1460, 6]];
  function dancer(k, t, s) {
    // as the camera flies past them (s > 1) they slide out of frame to the side
    const alpha_ = clamp((1.32 - s) / .14);
    if (alpha_ <= .01) return;
    const back = k % 2 === 1;
    const draw = () => CREW.forEach(([m, x0, kmin], i) => {
      if (k < kmin || (i > 0 && s < .1)) return;
      const x = x0 + Math.sign(x0 - VP[0]) * Math.max(0, s - 1) * 2600, b = bpOf(t) - k * .25 - i * .12;
      idol(x, 1010, 58, { member: m, outfit: 'practice', mic: false, back, ...idolMove('step', b), expr: i ? 'smile' : 'fired', mouth: singVis(t, k + i * 5), blink: t + k + i, shadow: true });
    });
    if (alpha_ >= .999) { draw(); return; }
    const L = layerDraw(draw);
    ctx.save(); ctx.setTransform(1, 0, 0, 1, 0, 0); ctx.globalAlpha = alpha_; ctx.drawImage(L, 0, 0); ctx.restore();
  }
  // u = how many mirrors deep the camera has flown (float)
  function mirrorWorld(t, u) {
    const kb = Math.floor(u), f = u - kb, Z = Math.pow(RR, -f);
    const levels = []; for (let j = 0; j < 9; j++) { const s = Math.pow(RR, j) * Z; if (s < .012) break; levels.push([kb + j, s]); }
    const at = s => { ctx.translate(VP[0], VP[1]); ctx.scale(s, s); ctx.translate(-VP[0], -VP[1]); };
    // deepest first: a flat "far" fill inside the last mirror
    const [, sLast] = levels[levels.length - 1];
    ctx.save(); at(sLast * RR); ctx.fillStyle = '#CFE3F2'; ctx.fillRect(-40, -40, W + 80, H + 80); ctx.restore();
    for (let j = levels.length - 1; j >= 0; j--) {
      const [k, s] = levels[j];
      ctx.save(); at(s);
      if (j < levels.length - 1) { ctx.fillStyle = 'rgb(170 205 240 / .16)'; ctx.fillRect(MR[0], MR[1], MR[2], MR[3]); }
      ctx.save(); ctx.beginPath(); ctx.rect(-40, -40, W + 80, H + 80); ctx.clip();
      roomRing(k, t, true);
      if (s > .03) dancer(k, t, s);
      ctx.restore();
      ctx.restore();
    }
  }
  const uAt = (t, P) => { const k = clamp((t - P.tH) / (P.tI - P.tH)); return 11 * (k < .15 ? k * k / .3 : k - .075) / .925; };
  function practiceUI(t, P, u) {
    ctx.fillStyle = 'rgb(20 8 40 / .6)'; rrect(40, 36, 720, 64, 16); ctx.fill();
    dtext("ATTN! DANCE PRACTICE (∞ VER.)", 60, 69, 26, { align: 'left', fill: IP.white, maxW: 680 });
    const ep = Math.round(10240 * 2 ** u);
    const lbl = `EPOCH ${fmtN(ep)}`, w = textW(lbl, 28, 'code') + 50;
    rrect(40, 112, w, 56, 14); ctx.fillStyle = IP.neonPink; ctx.fill();
    dtext(lbl, 40 + w / 2, 141, 28, { font: 'code', fill: IP.white });
  }
  function shotH(t, P) {
    const u = uAt(t, P);
    mirrorWorld(t, u);
    // dawn light
    ctx.save(); ctx.globalCompositeOperation = 'lighter'; glow(120, 420, 900, '#FFB38A', .18 + .1 * clamp((t - P.tH) / 8)); ctx.restore();
    practiceUI(t, P, u);
    if (t < P.O.start) lastLineCaption(t, P);
    // "AND ON" pops on every other beat, flying into the tunnel
    const bn = Math.floor(bpOf(t) / 2), age = t - onBeat(0, bn * 2);
    if (age < .7 && t > P.tH + .2) { const k = clamp(age / .7), s = lerp(1.3, .2, easeIn(k)); ctx.save(); ctx.translate(lerp(960 + (bn % 2 ? 380 : -380), VP[0], easeIn(k)), lerp(640, VP[1], easeIn(k))); ctx.scale(s, s); ctx.globalAlpha = 1 - k * k; dtext('AND ON', 0, 0, 90, { fill: IP.white, strokes: [[IP.neonPink, 18]], shadow: [0, 8, 'rgb(20 8 40 / .3)'] }); ctx.restore(); }
    flash(t, P.tH, .25, .8, '255 240 225');
    setBloom(.3);
  }

  // =====================================================================================================
  // I: the album's back cover
  // =====================================================================================================
  const TRACKS = ["WE DIDN'T START THE SCALING (TITLE)", 'ALWAYS TRAINING', "CAN'T CONTAIN IT", 'PACE IT (RACE IT REMIX)', 'AND ON, AND ON (∞ VER.)'];
  function barcode(x, y, w, h) { ctx.fillStyle = IP.white; ctx.fillRect(x - 12, y - 12, w + 24, h + 44); let xx = x; for (let i = 0; xx < x + w; i++) { const bw = 2 + Math.floor(hash2(i, 77) * 4); if (i % 2 === 0) { ctx.fillStyle = IP.ink; ctx.fillRect(xx, y, bw, h); } xx += bw; } dtext('8 809 202 609 22', x + w / 2, y + h + 18, 16, { font: 'code', fill: IP.ink }); }
  function albumBack(t, P, k) {
    hideStamp();
    bgGrad('#E6DCFF', '#FFC2E0');
    patternBG('hearts', 'rgb(0 0 0 / 0)', alpha(IP.white, .45), { cell: 110, dy: t * 20 });
    const e = easeOut(k), u = uAt(P.tI, P) + (t - P.tI) * .45;
    // the artwork: the infinite mirror, still going
    const ax = 560, ay = 500, as = 700, sc = lerp(1, as / 1080, e), cx = lerp(960, ax, e), cy = lerp(540, ay, e);
    // the case
    const ck = clamp((k - .35) / .65);
    ctx.save(); ctx.globalAlpha = ck;
    solid(rrPts(150, 80, 1620, 860, 30), IP.white, { shade: '#EDE6F7', sh: 12, line: IP.line, lw: 6, sharp: true, dropShadow: [16, 22] });
    ctx.restore();
    ctx.save(); ctx.translate(cx, cy); ctx.scale(sc, sc);
    ctx.beginPath(); ctx.rect(-lerp(W / 2 / sc, 540, e) - 1, -lerp(H / 2 / sc, 540, e) - 1, lerp(W / sc, 1080, e) + 2, lerp(H / sc, 1080, e) + 2); ctx.clip();
    ctx.translate(-960, -lerp(540, 470, e));
    mirrorWorld(t, u);
    ctx.restore();
    if (ck > 0) {
      ctx.save(); ctx.globalAlpha = ck;
      ctx.strokeStyle = IP.line; ctx.lineWidth = 5; ctx.strokeRect(ax - as / 2, ay - as / 2, as, as);
      const rx = 990;
      attnLogo(rx + 160, 185, 76, {});
      dtext('THE 1ST MINI ALBUM', rx + 370, 170, 22, { align: 'left', font: 'mono', fill: IP.inkSoft, spacing: 3, maxW: 330 });
      dtext("WE DIDN'T START THE SCALING", rx + 370, 208, 22, { align: 'left', font: 'mono', fill: IP.neonPink, spacing: 1, maxW: 330 });
      ln([[rx, 270], [1700, 270]], alpha(IP.line, .25), 3);
      TRACKS.forEach((s, i) => { const y = 318 + i * 62, tk = clamp((k - .4 - i * .06) / .15); if (tk <= 0) return; ctx.save(); ctx.globalAlpha *= tk; dtext(String(i + 1).padStart(2, '0'), rx + 10, y, 30, { align: 'left', font: 'code', fill: IP.neonPink }); dtext(s, rx + 80, y, 30, { align: 'left', font: 'rammetto', fill: IP.ink, maxW: 620 }); ctx.restore(); });
      ln([[rx, 640], [1700, 640]], alpha(IP.line, .25), 3);
      ['hook after @tautologer', 'lyrics: Domenic & Claude', 'music: Suno v6 · video: Claude Opus 5.5', 'Sep 23, 2026'].forEach((s, i) => dtext(s, rx + 10, 680 + i * 36, 25, { align: 'left', font: 'archivo', fill: i === 3 ? IP.inkSoft : IP.ink, maxW: 460 }));
      barcode(1480, 800, 210, 70);
      pill('EPOCH ∞', 1150, 850, 26, '#1C1438', { font: 'code', ink: IP.neonLime, line: IP.neonLime });
      ctx.restore();
    }
  }
  function shotI(t, P) {
    const k = clamp((t - P.tI) / .9);
    albumBack(t, P, k);
    flash(t, P.tI, .2, .5);
  }

  section('C4', (p, lt, d, t) => {
    const P = plan();
    if (t < P.tA2) shotA1(t, P);
    else if (t < P.tB) shotA2(t, P);
    else if (t < P.tC) shotB(t, P);
    else if (t < P.tD) shotC(t, P);
    else if (t < P.tE) shotD(t, P);
    else if (t < P.tE2) shotE1(t, P);
    else if (t < P.tF) shotE2(t, P);
    else if (t < P.tG) shotF(t, P);
    else if (t < P.tH) shotG(t, P);
    else if (t < P.tI) shotH(t, P);
    else shotI(t, P);
  });
  section('outro', (p, lt, d, t) => {
    const P = plan();
    shotI(t, P);
    // a last finger-heart sticker from TOKI
    const k = clamp((lt - .15) / .2);
    if (k > 0) {
      ctx.save(); ctx.translate(1660, 600); const s = backOut(k, 2.6); ctx.scale(s, s); ctx.rotate(.12);
      solid(ellPts(0, 0, 118, 118, 40), IP.white, { shade: false, line: IP.neonPink, lw: 8, dropShadow: [8, 10] });
      ctx.save(); ctx.beginPath(); ctx.arc(0, 0, 108, 0, TAU); ctx.clip(); bgGrad(IP.pink, IP.lilac, { y0: -110, y1: 110 });
      idol(0, 10, 36, { anchor: 'face', ...IDOL_POSES.fingerHeart, heartPop: clamp((lt - .35) / .25), expr: 'wink', mouth: 'tongue', mic: false, swing: 0 });
      ctx.restore(); ctx.restore();
    }
    hideCaption();
  });
})();
