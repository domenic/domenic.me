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
// ---- styles/newscast/kit.js ----
// kit.js: the newscast style's shared look — palette, characters, props, and the overlays drawn over every frame.
// "CHANNEL 89 ACTION NEWS": a 1989 local TV newscast, played back from a worn VHS tape on a curved CRT.
// Read STYLE.md before painting a chapter. Everything here is a pure function of time: no Math.random(), no state between frames.
// The zine's caption, date stamp and grain overlays (timeline.js) are dropped; this style registers its own (bottom of this file).
OVERLAYS.length = 0;

// =====================================================================================================
// PALETTE — late-80s broadcast: deep studio blues, chrome, gold rules, red for LIVE/BREAKING.
// =====================================================================================================
const NP = {
  ink: '#15121C', black: '#050508', white: '#F7F6F1', paper: '#EFE8D6', cream: '#FFF3D2',
  night: '#060A20', navy: '#0B1545', royal: '#17328A', blue: '#2554CC', sky: '#6FA7FF', ice: '#D4E6FF',
  slate: '#2A3148', steel: '#5B6784', grey: '#8D95A8', silver: '#C9CFDB',
  red: '#D8262F', redDk: '#8A1219', gold: '#F4B62A', goldDk: '#B07A12', amber: '#FF9B2F',
  magenta: '#E2379B', cyan: '#2AD4F0', teal: '#15A897', green: '#2EBD5B', lime: '#A6F04A', purple: '#6B3FC4',
  phosphor: '#6CFF8E', crtAmber: '#FFB23B', beige: '#DCD2B6', beigeDk: '#A99E80', wood: '#6D482E', woodLt: '#9A6A45',
  clawd: '#D97757', clawdDk: '#A5533A', clawdLt: '#EDA07F',
  ccText: '#F2F2F2', ccYellow: '#F5E04A',
};
// Skin tones for toon() (index or explicit colour). Hair colours.
const NSKIN = ['#F6CFB0', '#E8B48C', '#C98B5E', '#8E5A3A', '#FAD9C2', '#B97A57'];
const NHAIR = { black: '#1E1A1D', brown: '#5A3A24', blond: '#E8C46A', auburn: '#A5462A', grey: '#B9B6B0', white: '#ECEAE4', red: '#C2462A' };

// =====================================================================================================
// LOW-LEVEL DRAWING (clean vector, no torn edges)
// =====================================================================================================
function ell(cx, cy, rx, ry = rx, rot = 0) { ctx.beginPath(); ctx.ellipse(cx, cy, Math.abs(rx), Math.abs(ry), rot, 0, TAU); }
function rrect(x, y, w, h, r = 0) { ctx.beginPath(); ctx.roundRect(x, y, w, h, Math.max(0, Math.min(r, Math.abs(w) / 2, Math.abs(h) / 2))); }
function poly(pts, close = true) { tracePath(pts, close); }
// Fill and/or stroke the current path. In sketch mode (courtroom), fills become pastel hatching and strokes charcoal.
let _sketch = 0;
function paint(fill, stroke, lw = 3) {
  if (_sketch) return _sketchPaint(fill, stroke, lw);
  if (fill) { ctx.fillStyle = fill; ctx.fill(); }
  if (stroke) { ctx.strokeStyle = stroke; ctx.lineWidth = lw; ctx.lineJoin = 'round'; ctx.lineCap = 'round'; ctx.stroke(); }
}
const lg = (x0, y0, x1, y1, stops) => { const g = ctx.createLinearGradient(x0, y0, x1, y1); for (const [k, c] of stops) g.addColorStop(k, c); return g; };
const rg = (x, y, r0, r1, stops, x1 = x, y1 = y) => { const g = ctx.createRadialGradient(x, y, r0, x1, y1, r1); for (const [k, c] of stops) g.addColorStop(k, c); return g; };
function fillAll(c) { ctx.fillStyle = c; ctx.fillRect(-600, -600, W + 1200, H + 1200); }
function vFill(top, bottom, x = -600, y = -600, w = W + 1200, h = H + 1200) { ctx.fillStyle = lg(0, Math.max(y, 0), 0, Math.min(y + h, H), [[0, top], [1, bottom]]); ctx.fillRect(x, y, w, h); }
const shade = (c, k = .25) => mixCol(c, '#000000', k);
const tint = (c, k = .25) => mixCol(c, '#ffffff', k);
// Talking mouth openness (0..1) that chatters ~9×/s; phase lets two people differ.
const talk = (t, ph = 0) => Math.max(0, Math.sin(t * 19 + ph) * .6 + Math.sin(t * 31 + ph * 2) * .4);
// Entrance helper: 0→1 over `dur` s starting at `t0` s into the window.
const inK = (lt, t0 = 0, dur = .2) => clamp((lt - t0) / dur);
// The hard-cut beat of a window: seconds from window start to the first beat at/after it (never > .2 s).
const firstBeat = (t, lt) => { const b = Math.ceil(bpOf(t - lt) - .05); return Math.min(.2, Math.max(0, onBeat(0, b) - (t - lt))); };
// Draw a fn into an offscreen canvas `key` that holds a whole 1920×1080 frame at `scale`; returns the canvas.
const _rtBufs = new Map();
function renderTo(key, scale, draw) {
  const w = Math.max(2, Math.round(W * scale * RS)), h = Math.max(2, Math.round(H * scale * RS));
  let c = _rtBufs.get(key);
  if (!c || c.width !== w || c.height !== h) { c = makeCanvas(w, h); _rtBufs.set(key, c); }
  const saved = ctx, savedDepth = _camDepth;
  ctx = c.getContext('2d'); ctx.setTransform(w / W, 0, 0, h / H, 0, 0); ctx.globalAlpha = 1; ctx.globalCompositeOperation = 'source-over';
  ctx.imageSmoothingEnabled = true; ctx.fillStyle = '#000'; ctx.fillRect(0, 0, W, H);
  ctx.save();
  try { draw(); } finally { while (_camDepth > savedDepth) camEnd(); ctx.restore(); ctx = saved; }
  return c;
}
// Blit a renderTo() canvas into a logical rect.
function blitFrame(c, x, y, w, h, o = {}) {
  ctx.save(); if (o.alpha !== undefined) ctx.globalAlpha *= o.alpha; if (o.pixel) ctx.imageSmoothingEnabled = false;
  ctx.drawImage(c, x, y, w, h); ctx.restore();
}
// Pixelate whatever `draw` paints inside the rect (x, y, w, h) into `block`-px mosaic tiles (80s DVE mosaic / identity-hidden face).
function mosaic(x, y, w, h, block, draw) {
  const sc = 1 / block, c = renderTo('mosaic', sc, draw);
  ctx.save(); ctx.imageSmoothingEnabled = false; rrect(x, y, w, h, 0); ctx.clip();
  ctx.drawImage(c, 0, 0, W, H); ctx.restore();
}

// =====================================================================================================
// PIXEL FONT — the VCR on-screen display (5×7 glyphs). pixelText(str, x, y, px, col, o)
// =====================================================================================================
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
  "■": '.....#########################.....', "!": '..#....#....#....#....#.........#..', "?": '.###.#...#....#...#...#.........#..', "'": '..#....#...#.......................',
  ",": '.....................##....#...#...', "(": '...#...#...#....#....#.....#.....#.', ")": '.#.....#.....#....#....#...#...#...', "#": '.#.#..#.#.#####.#.#.#####.#.#..#.#.',
  "%": '##...##..#...#...#...#...#..##...##', "+": '.......#....#..#####..#....#.......', "\"": '.#.#..#.#..#.#.....................', "*": '.....#.#.#.###.#####.###.#.#.#.....',
  "$": '..#...#####.#...###...#.#####...#..', "&": '.##..#..#.#.#...#...#.#.##..#..##.#', "=": '..........#####.....#####..........', "_": '..............................#####',
};
function pixelW(str, px) { return [...String(str)].length * 6 * px - px; }
// pixelText(str, x, y, px, col, o): blocky VCR/character-generator text. (x, y) = top-left (align 'left'), top-centre or top-right.
// o.align ('left'|'center'|'right'), o.edge (outline colour, default black; null for none), o.shadow ([dx,dy] in px units).
function pixelText(str, x, y, px, col = NP.white, o = {}) {
  str = String(str).toUpperCase();
  const w = pixelW(str, px), x0 = o.align === 'right' ? x - w : o.align === 'center' ? x - w / 2 : x;
  const chars = [...str], edge = o.edge === undefined ? '#000' : o.edge;
  const pass = (c, grow, dx, dy) => {
    ctx.fillStyle = c;
    chars.forEach((ch, i) => {
      const g = PIXFONT[ch] || PIXFONT['?'];
      for (let r = 0; r < 7; r++) for (let q = 0; q < 5; q++) if (g[r * 5 + q] === '#')
        ctx.fillRect(x0 + (i * 6 + q) * px - grow + dx, y + r * px - grow + dy, px + grow * 2, px + grow * 2);
    });
  };
  ctx.save(); if (o.alpha !== undefined) ctx.globalAlpha *= o.alpha;
  if (o.shadow) pass('rgb(0 0 0 / .6)', 0, o.shadow[0] * px, o.shadow[1] * px);
  if (edge) pass(edge, px * .34, 0, 0);
  pass(col, 0, 0, 0);
  ctx.restore();
  return w;
}

// =====================================================================================================
// CHROME TYPE, GLINTS, THE STATION LOGO
// =====================================================================================================
const CHROME = {
  chrome: { stops: [[0, '#1B2A78'], [.18, '#5E86E0'], [.44, '#E6F1FF'], [.5, '#FFFFFF'], [.52, '#2A1830'], [.6, '#7A3E28'], [.8, '#EE9E4A'], [1, '#FFE9B8']], ext: ['#070B26', '#2B3B86'], line: '#0A0F2E' },
  gold: { stops: [[0, '#5A3300'], [.3, '#E8B840'], [.46, '#FFF2B8'], [.5, '#FFFFFF'], [.53, '#6B3E00'], [.7, '#D9961C'], [1, '#FFF0B0']], ext: ['#2A1600', '#8A5A10'], line: '#2A1600' },
  red: { stops: [[0, '#4A0008'], [.3, '#E0303A'], [.46, '#FFB0B0'], [.5, '#FFFFFF'], [.53, '#5A0010'], [.75, '#E3262F'], [1, '#FFB8A8']], ext: ['#260004', '#8A1020'], line: '#200004' },
  blue: { stops: [[0, '#06124A'], [.4, '#4F8BFF'], [.5, '#E8F4FF'], [.53, '#0A1A5A'], [.8, '#2F74FF'], [1, '#A9D2FF']], ext: ['#020824', '#10267A'], line: '#020824' },
  white: { stops: [[0, '#FFFFFF'], [.5, '#EEF3FF'], [1, '#B9C6E6']], ext: ['#10183F', '#44527E'], line: '#0A0F2E' },
};
// chrome(str, x, y, size, o): 80s chrome/extruded logo lettering, centred on (x, y) unless o.align.
// o.font (FONTS key, default 'archivo'), o.style ('chrome'|'gold'|'red'|'blue'|'white'), o.depth (extrusion px), o.spacing,
// o.italic (slant, e.g. .2), o.align, o.s / o.sx / o.sy (scale), o.rot, o.alpha. Returns the drawn width. Cached per string.
function chrome(str, x, y, size, o = {}) {
  const font = o.font ?? 'archivo', st = o.style ?? 'chrome', depth = Math.round(o.depth ?? size * .09), sp = o.spacing ?? 0, it = o.italic ?? 0;
  const S = CHROME[st] || CHROME.chrome;
  const tw = textW(str, size, font, sp), w = tw + depth + size * .5 + Math.abs(it) * size, h = size * 1.5 + depth;
  const img = cached(`chr|${str}|${size}|${font}|${st}|${depth}|${sp}|${it}`, w, h, () => {
    ctx.translate(size * .25 + Math.max(0, it) * size * .6, 0); ctx.transform(1, 0, -it, 1, it * size * 1.05, 0);
    ctx.font = `${size}px "${FONTS[font] || font}"`; ctx.letterSpacing = `${sp}px`; ctx.textAlign = 'left'; ctx.textBaseline = 'alphabetic';
    const by = size * 1.1;
    for (let i = depth; i >= 1; i--) { ctx.fillStyle = mixCol(S.ext[0], S.ext[1], 1 - i / depth); ctx.fillText(str, i * .55, by + i); }
    ctx.lineWidth = Math.max(2, size * .07); ctx.strokeStyle = S.line; ctx.lineJoin = 'round'; ctx.strokeText(str, 0, by);
    ctx.fillStyle = lg(0, by - size * .74, 0, by + size * .02, S.stops); ctx.fillText(str, 0, by);
    ctx.lineWidth = Math.max(1, size * .018); ctx.strokeStyle = 'rgb(255 255 255 / .55)'; ctx.strokeText(str, -size * .01, by - size * .012);
  });
  const s = o.s ?? 1, ax = o.align === 'left' ? img.lw / 2 * s - size * .25 * s : o.align === 'right' ? -img.lw / 2 * s + size * .25 * s : 0;
  blit(img, x + ax, y + (depth / 2 - size * .08) * s, { rot: o.rot, s, sx: o.sx, sy: o.sy, alpha: o.alpha });
  return tw * s;
}
// A four-point star glint (lens sparkle). a = 0..1 intensity; r = ray length.
function glint(x, y, r, a = 1, col = '#FFFFFF') {
  if (a <= 0) return;
  ctx.save(); ctx.translate(x, y); ctx.globalAlpha *= clamp(a); ctx.globalCompositeOperation = 'lighter';
  ctx.fillStyle = rg(0, 0, 0, r * .5, [[0, 'rgb(255 255 255 / .9)'], [.4, 'rgb(190 220 255 / .35)'], [1, 'rgb(120 170 255 / 0)']]);
  ctx.fillRect(-r * .5, -r * .5, r, r);
  ctx.fillStyle = col;
  for (const [rx, ry] of [[r, r * .06], [r * .06, r], [r * .42, r * .04]]) { poly([[-rx, 0], [0, -ry], [rx, 0], [0, ry]]); ctx.fill(); }
  ctx.rotate(Math.PI / 4); poly([[-r * .35, 0], [0, -r * .03], [r * .35, 0], [0, r * .03]]); ctx.fill(); poly([[0, -r * .35], [r * .03, 0], [0, r * .35], [-r * .03, 0]]); ctx.fill();
  ctx.restore();
}
// Glint that sweeps across a word: k = 0..1 position along [x0, x1].
const sweepGlint = (x0, x1, y, k, r = 60) => { if (k > 0 && k < 1) glint(lerp(x0, x1, k), y, r * Math.sin(k * Math.PI), Math.sin(k * Math.PI)); };

// The station roundel: a blue disc with a chrome ring, a slanted chrome "89" and a red swoosh. (x, y) centre, r radius.
// o.words: draw "ACTION NEWS" under it; o.spin: rotation about the vertical axis (radians) for flying logos.
function logo89(x, y, r, o = {}) {
  const img = cached('logo89', 440, 440, () => {
    ctx.translate(220, 220); const R = 200;
    ctx.fillStyle = 'rgb(0 0 0 / .35)'; ell(8, 12, R, R); ctx.fill();
    ctx.fillStyle = lg(0, -R, 0, R, [[0, '#9CC4FF'], [.08, '#E8F2FF'], [.2, '#5C7FD8'], [.5, '#1A2C8A'], [.52, '#0A1240'], [.75, '#C47A38'], [1, '#FFE4A8']]); ell(0, 0, R, R); ctx.fill();
    ctx.fillStyle = rg(-40, -60, 10, R * .92, [[0, '#3B78FF'], [.7, '#12308F'], [1, '#081650']]); ell(0, 0, R * .86, R * .86); ctx.fill();
    ctx.strokeStyle = 'rgb(255 255 255 / .35)'; ctx.lineWidth = 2; for (let i = -4; i <= 4; i++) { ctx.beginPath(); ctx.moveTo(-R * .86, i * 34); ctx.lineTo(R * .86, i * 34); ctx.stroke(); }
    // swoosh
    ctx.save(); ell(0, 0, R * .86, R * .86); ctx.clip();
    ctx.fillStyle = lg(-R, 0, R, 0, [[0, '#7A0010'], [.5, '#FF3A3A'], [1, '#FFD0B0']]);
    ctx.beginPath(); ctx.moveTo(-R, R * .55); ctx.quadraticCurveTo(0, R * .05, R, -R * .25); ctx.lineTo(R, -R * .05); ctx.quadraticCurveTo(0, R * .35, -R, R * .8); ctx.closePath(); ctx.fill();
    ctx.restore();
    chrome('89', 4, -6, 190, { font: 'anton', italic: .18, depth: 14 });
  });
  const img2 = o.words ? cached('logo89w', 760, 150, () => { chrome('ACTION NEWS', 380, 70, 96, { font: 'archivo', italic: .12, depth: 9, spacing: 2 }); }) : null;
  const s = r / 200, sx = o.spin !== undefined ? Math.cos(o.spin) : 1;
  blit(img, x, y, { s, sx, alpha: o.alpha });
  if (img2) blit(img2, x, y + r * 1.22, { s: s * (o.wordScale ?? .9), sx, alpha: o.alpha });
}

// =====================================================================================================
// BROADCAST GRAPHICS: bugs, chyrons, over-the-shoulder boxes, full-screen graphic frames, bumpers
// =====================================================================================================
// liveBug(x, y, o): top-left corner bug. o.label ('LIVE'|'FILE'|'SKY 89'|'EXCLUSIVE'|'VIA SATELLITE'…), o.col, o.logo (show the mini 89 roundel), o.blink.
function liveBug(x = 96, y = 70, o = {}) {
  const label = o.label ?? 'LIVE', col = o.col ?? NP.red, size = o.size ?? 46, k = o.k ?? 1;
  if (k <= 0) return;
  const tw = textW(label, size, 'archivo', 2), w = tw + 50 + (o.logo !== false ? 84 : 0), h = size * 1.45;
  ctx.save(); ctx.translate(x, y); ctx.scale(1, easeOut(k));
  ctx.fillStyle = 'rgb(0 0 0 / .45)'; rrect(6, 8, w, h, 8); ctx.fill();
  let lx = 0;
  if (o.logo !== false) { ctx.fillStyle = lg(0, 0, 0, h, [[0, '#2F5BD8'], [1, '#0B1A66']]); rrect(0, 0, 84, h, [8, 0, 0, 8]); ctx.fill(); logo89(42, h / 2, h * .42); lx = 84; }
  ctx.fillStyle = lg(0, 0, 0, h, [[0, tint(col, .25)], [.5, col], [1, shade(col, .35)]]); rrect(lx, 0, w - lx, h, o.logo !== false ? [0, 8, 8, 0] : 8); ctx.fill();
  ctx.fillStyle = 'rgb(255 255 255 / .22)'; ctx.fillRect(lx + 4, 4, w - lx - 8, h * .38);
  const blink = o.blink === false ? 1 : (frac(T * 1.1) < .75 ? 1 : .35);
  if (label === 'LIVE') { ctx.fillStyle = `rgb(255 255 255 / ${blink})`; ell(lx + 26, h / 2, 9); ctx.fill(); }
  txt(label, lx + (label === 'LIVE' ? 44 : 25), h / 2 + 2, size, NP.white, { font: 'archivo', align: 'left', spacing: 2, shadow: [2, 3], shadowCol: 'rgb(0 0 0 / .5)' });
  ctx.restore();
}
// Station ID bug for a corner (the roundel with a soft glow). Mostly for bumpers and full-screen graphics.
function stationBug(x = 1790, y = 950, r = 48, a = .85) { ctx.save(); ctx.globalAlpha *= a; logo89(x, y, r); ctx.restore(); }

const CHY = {
  news: { bar: ['#2A5AE0', '#10247A'], sub: ['#FFE08A', '#F0B429'], subText: NP.navy, tab: NP.red },
  breaking: { bar: ['#F03A40', '#8A0E16'], sub: ['#FFFFFF', '#D9DEE8'], subText: NP.redDk, tab: '#1A1A1A' },
  live: { bar: ['#2A5AE0', '#10247A'], sub: ['#FF5A5A', '#C8141E'], subText: NP.white, tab: NP.red },
  sports: { bar: ['#1FA85A', '#0A5A2A'], sub: ['#FFE08A', '#F0B429'], subText: '#0A3A1A', tab: '#0B1545' },
  money: { bar: ['#1E7A4A', '#0A3A22'], sub: ['#E8F0C0', '#B8D080'], subText: '#0A3A22', tab: NP.gold },
  weather: { bar: ['#18B0C8', '#0A5A7A'], sub: ['#FFFFFF', '#CFE8F0'], subText: '#0A4A6A', tab: NP.amber },
  purple: { bar: ['#8A4AE0', '#3A1680'], sub: ['#FFD0F0', '#F090D0'], subText: '#3A1060', tab: NP.gold },
};
// chyron(title, sub, o): lower-third super. Top-left of the title bar at (o.x ?? 150, o.y ?? 812).
// o.k: entrance 0..1 (tab flips in, bar wipes on); o.out: exit 0..1; o.style: key of CHY; o.tab: tab text (default: the 89 roundel);
// o.size (title px, default 54), o.w (force width), o.subW. Returns the bar width.
function chyron(title, sub, o = {}) {
  const k = o.k ?? 1, out = o.out ?? 0; if (k <= 0 || out >= 1) return 0;
  const S = CHY[o.style ?? 'news'], x = o.x ?? 150, y = o.y ?? 812, size = o.size ?? 54, ss = o.subSize ?? 34;
  const tabW = 104, th = size * 1.3, sh = ss * 1.3;
  const tw = textW(title, size, 'archivo', 1.5), sw = sub ? textW(sub, ss, 'archivo', 1) : 0;
  const bw = o.w ?? Math.max(tw + 64, 380), subW = o.subW ?? Math.max(sw + 56, 200);
  const kt = easeOut(clamp(k / .45)), kb = easeOut(clamp((k - .2) / .8)), ko = 1 - easeIn(out);
  ctx.save();
  // shadow
  ctx.fillStyle = 'rgb(0 0 0 / .38)'; ctx.fillRect(x + 8, y + 9, (tabW + bw) * kb * ko, th); if (sub) ctx.fillRect(x + tabW + 8, y + th + 9, subW * kb * ko, sh);
  // bar (wipes on left→right)
  ctx.save(); ctx.beginPath(); ctx.rect(x + tabW - 2, y - 10, (Math.max(bw, sub ? subW : 0) + 4) * kb * ko, th + sh + 30); ctx.clip();
  ctx.fillStyle = lg(0, y, 0, y + th, [[0, tint(S.bar[0], .15)], [.48, S.bar[0]], [.52, S.bar[1]], [1, shade(S.bar[1], .1)]]); ctx.fillRect(x + tabW, y, bw, th);
  ctx.fillStyle = 'rgb(255 255 255 / .16)'; ctx.fillRect(x + tabW, y + 3, bw, th * .35);
  ctx.fillStyle = NP.gold; ctx.fillRect(x + tabW, y, bw, 4);
  txt(title, x + tabW + 30 - (1 - kb) * 60, y + th / 2 + 3, size, NP.white, { font: 'archivo', align: 'left', spacing: 1.5, shadow: [3, 4], shadowCol: 'rgb(0 0 0 / .55)', maxW: bw - 50 });
  if (sub) {
    ctx.fillStyle = lg(0, y + th, 0, y + th + sh, [[0, S.sub[0]], [1, S.sub[1]]]); ctx.fillRect(x + tabW, y + th, subW, sh);
    txt(sub, x + tabW + 26 - (1 - kb) * 90, y + th + sh / 2 + 2, ss, S.subText, { font: 'archivo', align: 'left', spacing: 1, maxW: subW - 40 });
  }
  ctx.restore();
  // tab (flips in)
  ctx.save(); ctx.translate(x + tabW / 2, y + th / 2); ctx.scale(kt * ko, 1);
  ctx.fillStyle = lg(0, -th / 2, 0, th / 2, [[0, tint(S.tab, .3)], [.5, S.tab], [1, shade(S.tab, .35)]]); ctx.fillRect(-tabW / 2, -th / 2, tabW, th);
  ctx.fillStyle = 'rgb(255 255 255 / .2)'; ctx.fillRect(-tabW / 2, -th / 2 + 3, tabW, th * .35);
  if (o.tab) txt(o.tab, 0, 3, Math.min(size * .6, 34 * 5 / Math.max(3, o.tab.length)), NP.white, { font: 'archivo', maxW: tabW - 14, shadow: [2, 3], shadowCol: 'rgb(0 0 0 / .5)' });
  else logo89(0, 0, th * .42);
  ctx.restore();
  ctx.restore();
  return tabW + bw;
}
// Standard chyron timing for a verse window: wipes on from 0.08 s to 0.38 s.
const chyK = lt => clamp((lt - .08) / .3);
// A two-line name super for a person: NAME / title. Same options as chyron().
const nameSuper = (name, title, o = {}) => chyron(name, title, o);

// otsBox(x, y, w, h, draw, o): the over-the-shoulder picture box. draw(w, h) paints its content in local coords (0,0)–(w,h), clipped.
// o.k: DVE zoom-in 0..1; o.label: caption strip along the bottom; o.labelCol; o.tilt (−.2..2 fake 3D yaw); o.border (colour).
function otsBox(x, y, w, h, draw, o = {}) {
  const k = o.k ?? 1; if (k <= 0) return;
  const sk = backOut(clamp(k), 1.2), tilt = o.tilt ?? 0;
  ctx.save(); ctx.translate(x + w / 2, y + h / 2); ctx.scale(lerp(.15, 1, sk), lerp(.15, 1, sk));
  if (tilt) ctx.transform(1, tilt * .08, 0, 1, 0, 0);
  ctx.translate(-w / 2, -h / 2);
  ctx.fillStyle = 'rgb(0 0 0 / .45)'; ctx.fillRect(12, 14, w, h);
  ctx.save(); ctx.beginPath(); ctx.rect(0, 0, w, h); ctx.clip();
  ctx.fillStyle = NP.navy; ctx.fillRect(0, 0, w, h);
  draw(w, h);
  ctx.fillStyle = lg(0, 0, 0, h * .5, [[0, 'rgb(255 255 255 / .16)'], [1, 'rgb(255 255 255 / 0)']]); ctx.fillRect(0, 0, w, h * .5);
  if (o.label) {
    const lh = o.labelH ?? 58;
    ctx.fillStyle = lg(0, h - lh, 0, h, [[0, tint(o.labelCol ?? NP.red, .2)], [.5, o.labelCol ?? NP.red], [1, shade(o.labelCol ?? NP.red, .35)]]); ctx.fillRect(0, h - lh, w, lh);
    ctx.fillStyle = NP.gold; ctx.fillRect(0, h - lh, w, 3);
    txt(o.label, w / 2, h - lh / 2 + 2, o.labelSize ?? 38, NP.white, { font: 'archivo', spacing: 1.5, maxW: w - 30, shadow: [2, 3], shadowCol: 'rgb(0 0 0 / .5)' });
  }
  ctx.restore();
  ctx.lineWidth = 7; ctx.strokeStyle = o.border ?? '#F2F4FA'; ctx.strokeRect(0, 0, w, h);
  ctx.lineWidth = 2; ctx.strokeStyle = 'rgb(0 0 0 / .6)'; ctx.strokeRect(-4.5, -4.5, w + 9, h + 9); ctx.strokeRect(3.5, 3.5, w - 7, h - 7);
  ctx.restore();
}
// speech(str, x, y, o): a clean cartoon speech bubble centred on (x, y). o.tail ([x, y] it points at), o.size, o.font ('archivo'),
// o.pop (0..1 scale-in), o.fill, o.color, o.maxW, o.rot, o.think (thought-bubble dots instead of a tail).
function speech(str, x, y, o = {}) {
  const k = o.pop ?? 1; if (k <= 0) return;
  const size = o.size ?? 48, font = o.font ?? 'archivo', lines = wrap(str, size, font, o.maxW ?? 560);
  const w = Math.max(...lines.map(l => textW(l, size, font))) + size * 1.1, h = lines.length * size * 1.15 + size * .8;
  ctx.save(); ctx.translate(x, y); const s = backOut(clamp(k), 2); ctx.scale(s, s); if (o.rot) ctx.rotate(o.rot);
  const fill = o.fill ?? '#FFFFFF';
  if (o.tail && !o.think) { const tx = (o.tail[0] - x) / s, ty = (o.tail[1] - y) / s, a = Math.atan2(ty, tx), bx = Math.cos(a) * w * .25, by = Math.sin(a) * h * .25;
    poly([[bx - Math.sin(a) * 26, by + Math.cos(a) * 26], [tx * .85, ty * .85], [bx + Math.sin(a) * 26, by - Math.cos(a) * 26]]); paint(fill, NP.ink, 5); }
  if (o.tail && o.think) { const tx = (o.tail[0] - x) / s, ty = (o.tail[1] - y) / s; for (let i = 1; i <= 3; i++) { ell(tx * (.35 + i * .17), ty * (.35 + i * .17), 22 - i * 5); paint(fill, NP.ink, 4); } }
  ctx.fillStyle = 'rgb(0 0 0 / .3)'; rrect(-w / 2 + 8, -h / 2 + 10, w, h, Math.min(h / 2, 34)); ctx.fill();
  rrect(-w / 2, -h / 2, w, h, Math.min(h / 2, 34)); paint(fill, NP.ink, 5);
  if (o.tail && !o.think) { const tx = (o.tail[0] - x) / s, ty = (o.tail[1] - y) / s, a = Math.atan2(ty, tx), bx = Math.cos(a) * w * .25, by = Math.sin(a) * h * .25;
    poly([[bx - Math.sin(a) * 20, by + Math.cos(a) * 20], [bx + Math.cos(a) * 12, by + Math.sin(a) * 12], [bx + Math.sin(a) * 20, by - Math.cos(a) * 20]]); paint(fill); }
  lines.forEach((l, i) => txt(l, 0, -h / 2 + size * .4 + size * .58 + i * size * 1.15, size, o.color ?? NP.ink, { font }));
  ctx.restore();
}
// Full-screen graphic ("Paintbox" card): gradient background, venetian scan stripes, a header band with a segment name, the roundel.
// o.top / o.bottom colours, o.head (segment name), o.headCol, o.sub (small right-aligned text in the header).
function gfxCard(o = {}) {
  vFill(o.top ?? '#1D3FB0', o.bottom ?? '#060D38');
  ctx.fillStyle = 'rgb(255 255 255 / .045)'; for (let y = 0; y < H; y += 12) ctx.fillRect(0, y, W, 5);
  ctx.fillStyle = rg(W * .3, H * .25, 50, 1100, [[0, 'rgb(120 170 255 / .22)'], [1, 'rgb(0 0 0 / 0)']]); ctx.fillRect(0, 0, W, H);
  if (o.head) {
    const hy = o.headY ?? 84, hh = 96, x1 = o.headW ?? 1250;
    const tab = (dx, dy) => poly([[-10 + dx, hy + dy], [x1 + dx, hy + dy], [x1 - 60 + dx, hy + hh + dy], [-10 + dx, hy + hh + dy]]);
    ctx.fillStyle = 'rgb(0 0 0 / .4)'; tab(10, 10); ctx.fill();
    ctx.fillStyle = lg(0, hy, 0, hy + hh, [[0, tint(o.headCol ?? NP.red, .25)], [.5, o.headCol ?? NP.red], [1, shade(o.headCol ?? NP.red, .4)]]); tab(0, 0); ctx.fill();
    ctx.save(); tab(0, 0); ctx.clip(); ctx.fillStyle = NP.gold; ctx.fillRect(0, hy, W, 5); ctx.fillRect(0, hy + hh - 4, W, 4); ctx.fillStyle = 'rgb(255 255 255 / .15)'; ctx.fillRect(0, hy + 6, W, hh * .32); ctx.restore();
    logo89(190, hy + hh / 2, 62);
    const hw = chrome(o.head, 280, hy + hh / 2 + 4, 64, { font: 'archivo', style: 'white', depth: 5, align: 'left', italic: .1, spacing: 2 });
    if (o.sub && 280 + hw + 60 + textW(o.sub, 34, 'archivo', 2) < x1 - 60) txt(o.sub, x1 - 90, hy + hh / 2 + 2, 34, NP.white, { font: 'archivo', align: 'right', spacing: 2 });
  }
}
// Horizontal "swoosh" ribbons (the 80s motion-graphics staple). k = 0..1 sweep; y centre; col.
function swoosh(k, y, col = NP.red, o = {}) {
  if (k <= 0) return;
  const len = o.len ?? 1400, th = o.th ?? 46, x1 = lerp(-len, W + len * .2, easeOut(k)), x0 = x1 - len;
  ctx.save(); ctx.globalAlpha *= o.alpha ?? 1;
  ctx.fillStyle = lg(x0, 0, x1, 0, [[0, alpha(col, 0)], [.7, alpha(col, .9)], [1, tint(col, .6)]]);
  ctx.beginPath(); ctx.moveTo(x0, y + th * .6); ctx.quadraticCurveTo((x0 + x1) / 2, y - th * 1.2, x1, y - th * .1); ctx.lineTo(x1, y + th * .3); ctx.quadraticCurveTo((x0 + x1) / 2, y - th * .2, x0, y + th); ctx.closePath(); ctx.fill();
  ctx.restore();
}
// Perspective laser grid floor + starfield sky (the station open / bumpers). o.horizon (y), o.col (grid), o.sky ([top, horizon]), o.speed.
function laserGrid(t, o = {}) {
  const hz = o.horizon ?? 620, col = o.col ?? NP.magenta, sp = o.speed ?? 1.2;
  fillAll(o.sky?.[0] ?? '#02041A'); vFill(o.sky?.[0] ?? '#02041A', o.sky?.[1] ?? '#2A0E5A', -600, 0, W + 1200, hz);
  ctx.fillStyle = lg(0, hz - 160, 0, hz, [[0, 'rgb(255 60 180 / 0)'], [1, 'rgb(255 80 190 / .45)']]); ctx.fillRect(0, hz - 160, W, 160);
  for (let i = 0; i < 90; i++) { const sx = hash2(i, 1) * W, sy = hash2(i, 2) * (hz - 20), tw = .4 + .6 * Math.abs(Math.sin(t * (2 + hash2(i, 3) * 4) + i)); ctx.fillStyle = `rgb(255 255 255 / ${(.25 + .6 * hash2(i, 4)) * tw})`; ctx.fillRect(sx, sy, 2.5, 2.5); }
  vFill('#0A0220', '#1A0438', -600, hz, W + 1200, H - hz + 600);
  ctx.save(); ctx.beginPath(); ctx.rect(-600, hz, W + 1200, H - hz + 600); ctx.clip();
  const vx = W / 2, draw = (lw, a) => {
    ctx.strokeStyle = alpha(col, a); ctx.lineWidth = lw; ctx.beginPath();
    for (let i = -40; i <= 40; i++) { ctx.moveTo(vx + i * 30, hz); ctx.lineTo(vx + i * 30 * 12, H + 700); }
    const ph = frac(t * sp);
    for (let j = 0; j < 14; j++) { const z = (j + 1 - ph), yy = hz + 900 / (z * 1.6 + .4) - 900 / (14 * 1.6 + .4); if (yy > hz && yy < H + 600) { ctx.moveTo(-600, yy); ctx.lineTo(W + 600, yy); } }
    ctx.stroke();
  };
  draw(9, .18); draw(3, .95);
  ctx.restore();
  ctx.fillStyle = alpha(tint(col, .5), .9); ctx.fillRect(-600, hz - 1.5, W + 1200, 3);
}
// Wireframe globe (news-open staple). (x, y) centre, r radius, spin (radians). o.col, o.fill.
function globe(x, y, r, spin, o = {}) {
  const col = o.col ?? NP.cyan;
  ctx.save(); ctx.translate(x, y);
  ctx.fillStyle = o.fill ?? rg(-r * .35, -r * .35, r * .1, r * 1.05, [[0, '#2F66FF'], [.7, '#0B2380'], [1, '#040C3A']]); ell(0, 0, r, r); ctx.fill();
  ctx.strokeStyle = alpha(col, .85); ctx.lineWidth = Math.max(1.5, r * .012);
  for (let i = 0; i < 12; i++) { const a = spin + i / 12 * Math.PI, c = Math.cos(a); if (Math.sin(a) < 0) continue; ctx.beginPath(); ctx.ellipse(0, 0, Math.abs(c) * r, r, 0, 0, TAU); ctx.stroke(); }
  for (let j = -2; j <= 2; j++) { const la = j * .5, yy = Math.sin(la) * r, rr = Math.cos(la) * r; ctx.beginPath(); ctx.ellipse(0, yy, rr, rr * .18, 0, 0, TAU); ctx.stroke(); }
  // continents as chunky blobs on the front face
  ctx.save(); ell(0, 0, r, r); ctx.clip(); ctx.fillStyle = alpha(o.land ?? '#3FD6A0', .75);
  for (const cont of WORLD) {
    ctx.beginPath(); let first = true, vis = 0;
    for (const [lo, la] of cont) {
      const L = lo * Math.PI / 180 + spin, A = la * Math.PI / 180, z = Math.cos(A) * Math.cos(L);
      const px = Math.cos(A) * Math.sin(L) * r, py = -Math.sin(A) * r; if (z > 0) vis++;
      first ? ctx.moveTo(px, py) : ctx.lineTo(px, py); first = false;
    }
    if (vis > cont.length * .6) ctx.fill();
  }
  ctx.restore();
  ctx.fillStyle = rg(-r * .4, -r * .45, 0, r * .6, [[0, 'rgb(255 255 255 / .35)'], [1, 'rgb(255 255 255 / 0)']]); ell(0, 0, r, r); ctx.fill();
  ctx.lineWidth = r * .03; ctx.strokeStyle = alpha(col, .9); ell(0, 0, r, r); ctx.stroke();
  ctx.restore();
}
// Coarse continents (lon, lat) for globe() and worldMap().
const WORLD = [
  [[-168, 66], [-160, 71], [-140, 70], [-125, 71], [-110, 73], [-95, 72], [-85, 70], [-80, 64], [-94, 59], [-92, 56], [-82, 55], [-78, 52], [-66, 60], [-60, 55], [-56, 50], [-66, 45], [-70, 42], [-76, 38], [-76, 35], [-81, 31], [-80, 26], [-83, 29], [-90, 30], [-97, 27], [-97, 21], [-92, 18], [-88, 15], [-83, 10], [-78, 8], [-86, 12], [-95, 16], [-105, 20], [-110, 24], [-114, 30], [-117, 33], [-121, 36], [-124, 40], [-124, 46], [-128, 51], [-134, 56], [-142, 60], [-152, 60], [-158, 57], [-165, 60]],
  [[-55, 60], [-45, 60], [-22, 70], [-20, 78], [-40, 83], [-65, 80], [-58, 76], [-55, 70]],
  [[-80, 8], [-72, 12], [-62, 10], [-50, 2], [-35, -6], [-39, -15], [-48, -26], [-58, -38], [-65, -42], [-68, -54], [-75, -50], [-73, -40], [-71, -30], [-70, -18], [-76, -12], [-81, -5], [-80, 0], [-78, 5]],
  [[-10, 36], [-9, 43], [-1, 46], [-4, 48], [2, 51], [8, 54], [8, 57], [5, 59], [10, 63], [15, 68], [25, 71], [40, 68], [60, 70], [80, 73], [100, 77], [120, 73], [140, 72], [160, 70], [180, 68], [178, 62], [165, 60], [160, 54], [142, 52], [140, 45], [135, 35], [127, 38], [122, 31], [120, 22], [108, 18], [106, 10], [100, 6], [98, 15], [92, 22], [88, 21], [80, 15], [77, 8], [72, 20], [66, 25], [57, 25], [52, 28], [48, 30], [56, 24], [58, 20], [52, 16], [44, 12], [40, 15], [35, 28], [34, 31], [36, 36], [28, 36], [26, 40], [23, 38], [20, 40], [15, 38], [18, 42], [13, 45], [12, 42], [8, 44], [3, 43], [-1, 37], [-6, 36]],
  [[-17, 21], [-17, 15], [-12, 8], [-5, 5], [5, 5], [9, 4], [10, -2], [13, -10], [12, -18], [15, -27], [18, -34], [25, -34], [32, -28], [35, -22], [40, -15], [40, -5], [44, 0], [51, 11], [44, 11], [38, 18], [33, 27], [30, 31], [20, 32], [10, 37], [0, 36], [-6, 35], [-10, 30]],
  [[114, -22], [122, -18], [130, -12], [137, -12], [142, -11], [146, -19], [153, -25], [151, -34], [146, -39], [138, -35], [130, -32], [115, -34]],
  [[130, 31], [135, 34], [140, 36], [142, 40], [141, 45], [139, 40], [135, 35], [130, 33]],
  [[-5, 50], [1, 51], [0, 53], [-3, 56], [-5, 58], [-6, 55], [-4, 53]],
  [[95, 5], [105, -6], [115, -8], [120, -9], [110, -2], [100, 2]],
  [[44, -25], [50, -15], [49, -12], [44, -17]],
];

// =====================================================================================================
// PEOPLE — toon(): a clean 80s-cartoon person (flat fills, ink outline, one cel-shade tone). Never a likeness:
// real people get a generic face, one costume cue, and a name super / HELLO tag.
// =====================================================================================================
// toon(x, y, s, o): (x, y) = ground point between the feet; ≈ 11s tall (head top ≈ y − 11s, eyes ≈ y − 9.6s, shoulders ≈ y − 8s,
// waist ≈ y − 4s). Options:
//   skin (colour or NSKIN index), hair: short|side|slick|swoop|pompadour|balding|bald|curly|bob|long|big80s|buzz|spiky|bun|none,
//   hairCol, top: suit|blazer (80s shoulder pads)|sweater|hoodie|tee|leather|trench|labcoat|turtleneck|layers|dress|robe,
//   topCol, shirtCol, tie (colour), pocket (pocket-square colour), pin (lapel-pin colour), pants, shoes,
//   hat: fedora|visor|cap|hardhat|headset|beret, hatCol, glasses: round|square|shades|aviator, beard, mustache, stubble, beardCol,
//   eyes: open|dot|wide|closed|happy|half|angry|worried|x|spark|heart, blink (0..1), lookX / lookY (−1..1), brows: up|angry|worried|flat|raised,
//   mouth: smile|grin|flat|o|O|frown|smirk|scream|none, talk (0..1 openness; overrides mouth), blush, sweat, earrings, pearls,
//   aL / aR (upper-arm angle: 0 = out sideways, +1.2 ≈ raised, −1.35 = hanging), eL / eR (elbow bend, + bends up),
//   reachL / reachR ([x, y] hand target in s-units from the ground point; IK solves the arm), hand / handL: fist|open|point|thumb|wave,
//   hold / holdL (fn(s) drawn at the hand in pixels, upright; s is passed for sizing), legs (false = skip), walk (phase), dy (lift, in s), rot, flip, sq,
//   hood (hood up), faceless (face in shadow), sil (colour: flat silhouette, no face), line (outline colour), shadow (false = no floor shadow),
//   tag (HELLO-my-name-is sticker text on the chest).
function toon(x, y, s, o = {}) {
  const sil = o.sil, OL = sil ? null : (o.line ?? NP.ink), LW = .09;
  const C = c => sil ?? c;
  const skin = C(typeof o.skin === 'number' ? NSKIN[o.skin] : (o.skin ?? NSKIN[0]));
  const topCol = C(o.topCol ?? NP.blue), shirt = C(o.shirtCol ?? NP.white), pants = C(o.pants ?? '#2B3150'), hairCol = C(o.hairCol ?? NHAIR.brown);
  const top = o.top ?? 'suit', hair = o.hair ?? 'short';
  const pad = top === 'blazer' ? 1.95 : top === 'trench' || top === 'leather' ? 1.62 : 1.5;
  ctx.save(); ctx.translate(x, y);
  if (o.shadow !== false && o.legs !== false) { ctx.fillStyle = 'rgb(0 0 0 / .22)'; ell(0, 0, 2.4 * s, .42 * s); ctx.fill(); }
  ctx.translate(0, (o.dy ?? 0) * s); if (o.rot) ctx.rotate(o.rot);
  ctx.scale(o.flip ? -s : s, s); if (o.sq) ctx.scale(1 + o.sq * .4, 1 - o.sq);
  ctx.lineJoin = 'round'; ctx.lineCap = 'round';
  const HX = 0, HY = -9.55, RX = 1.28 * (o.headW ?? 1), RY = 1.42;
  // ---- back hair / hood ----
  const backHair = () => {
    if (hair === 'big80s') { ell(0, -10.05, 2.25, 1.95); paint(hairCol, OL, LW); ell(-1.55, -8.9, .95, 1.25); paint(hairCol, OL, LW); ell(1.55, -8.9, .95, 1.25); paint(hairCol, OL, LW); ell(0, -10.05, 2.1, 1.8); paint(hairCol); }
    else if (hair === 'bob' || hair === 'bun') { rrect(-RX - .38, -11.1, (RX + .38) * 2, 2.55, 1.1); paint(hairCol, OL, LW); }
    else if (hair === 'long') { rrect(-RX - .3, -11.05, (RX + .3) * 2, 4.3, 1.1); paint(hairCol, OL, LW); }
  };
  const hoodBack = () => { ell(0, -9.75, RX + .62, RY + .55); paint(topCol, OL, LW); };
  if (o.hood) hoodBack(); else backHair();
  // ---- legs ----
  if (o.legs !== false) {
    for (const side of [-1, 1]) {
      const sw = o.walk !== undefined ? Math.sin(o.walk * TAU + (side > 0 ? Math.PI : 0)) * .38 : 0;
      ctx.save(); ctx.translate(side * .55, -4.1); ctx.rotate(sw);
      ctx.beginPath(); ctx.moveTo(0, 0); ctx.lineTo(0, 3.65);
      if (OL) { ctx.strokeStyle = OL; ctx.lineWidth = .78 + LW * 2; ctx.stroke(); }
      ctx.strokeStyle = top === 'dress' || top === 'robe' ? skin : pants; ctx.lineWidth = .78; ctx.stroke();
      ell(side * .18, 3.85, .55, .26); paint(C(o.shoes ?? '#1E1A22'), OL, LW);
      ctx.restore();
    }
  }
  // ---- neck ----
  rrect(-.36, -8.55, .72, .7, .1); paint(skin, OL, LW);
  // ---- torso ----
  const torso = () => {
    ctx.beginPath();
    if (top === 'dress' || top === 'robe') { ctx.moveTo(-1.95, top === 'robe' ? -.3 : -2.5); ctx.lineTo(-pad, -7.2); ctx.quadraticCurveTo(-pad, -8.02, -pad + .55, -8.05); ctx.lineTo(pad - .55, -8.05); ctx.quadraticCurveTo(pad, -8.02, pad, -7.2); ctx.lineTo(1.95, top === 'robe' ? -.3 : -2.5); }
    else { ctx.moveTo(-1.32, -3.95); ctx.lineTo(-pad, -7.2); ctx.quadraticCurveTo(-pad, -8.02, -pad + .55, -8.05); ctx.lineTo(pad - .55, -8.05); ctx.quadraticCurveTo(pad, -8.02, pad, -7.2); ctx.lineTo(1.32, -3.95); }
    ctx.closePath();
  };
  torso(); paint(topCol);
  if (!sil) { ctx.save(); torso(); ctx.clip(); ctx.fillStyle = shade(topCol, .2); poly([[.8, -8.3], [3, -8.3], [3, 0], [1.05, 0]]); ctx.fill(); ctx.restore(); }
  if (!sil) {
    const lap = shade(topCol, .16);
    if (top === 'suit' || top === 'blazer' || top === 'labcoat' || top === 'trench') {
      poly([[-.52, -8.05], [.52, -8.05], [0, -6.1]]); paint(top === 'blazer' ? (o.shirtCol ?? NP.white) : shirt, OL, LW * .8);
      if (o.tie) { poly([[-.15, -7.86], [.15, -7.86], [.27, -6.15], [0, -5.55], [-.27, -6.15]]); paint(o.tie, OL, LW * .7); rrect(-.2, -8.0, .4, .32, .08); paint(shade(o.tie, .15), OL, LW * .7); }
      for (const sd of [-1, 1]) { poly([[sd * .52, -8.05], [sd * (top === 'trench' ? 1.35 : .98), -7.9], [sd * .72, -7.05], [sd * .36, -6.85], [0, -6.1]].map(([a, b]) => [a, b])); paint(top === 'labcoat' ? '#E6E9EF' : lap, OL, LW * .8); }
      ctx.beginPath(); ctx.moveTo(0, -6.1); ctx.lineTo(0, -3.95); paint(null, OL, LW * .8);
      if (top !== 'labcoat') for (const by of [-5.35, -4.7]) { ell(.14, by, .09); paint(shade(topCol, .45)); }
      if (o.pocket) { poly([[-1.15, -6.75], [-.7, -6.75], [-.8, -7.05], [-.95, -6.95], [-1.05, -7.1]]); paint(o.pocket, OL, LW * .6); }
      if (o.pin) { ell(.85, -7.15, .13); paint(o.pin, OL, LW * .5); }
      if (top === 'trench') { rrect(-1.34, -5.1, 2.68, .36, .05); paint(shade(topCol, .25), OL, LW * .7); rrect(-.18, -5.14, .36, .44, .05); paint(NP.gold, OL, LW * .5); }
    } else if (top === 'sweater' || top === 'tee') {
      ctx.beginPath(); ctx.ellipse(0, -8.05, .62, .32, 0, 0, Math.PI); paint(shade(topCol, .25), OL, LW * .8);
      if (top === 'sweater') for (let i = -3; i <= 3; i++) { ctx.beginPath(); ctx.moveTo(i * .36, -4.35); ctx.lineTo(i * .36, -3.98); paint(null, shade(topCol, .35), .06); }
    } else if (top === 'hoodie') {
      if (!o.hood) { ctx.beginPath(); ctx.ellipse(0, -8.05, 1.05, .45, 0, 0, Math.PI); paint(shade(topCol, .22), OL, LW * .8); }
      for (const sd of [-1, 1]) { ctx.beginPath(); ctx.moveTo(sd * .3, -7.8); ctx.lineTo(sd * .34, -6.6); paint(null, NP.white, .08); }
      rrect(-.95, -5.45, 1.9, .95, .3); paint(shade(topCol, .1), OL, LW * .7);
    } else if (top === 'leather') {
      for (const sd of [-1, 1]) { poly([[sd * .45, -8.05], [sd * 1.3, -7.95], [sd * .95, -7.1], [sd * .25, -6.7]]); paint(shade(topCol, .3), OL, LW * .8); }
      poly([[-.45, -8.05], [.45, -8.05], [.2, -6.7], [-.2, -6.7]]); paint(C(o.shirtCol ?? '#22222A'));
      ctx.beginPath(); ctx.moveTo(.25, -6.7); ctx.lineTo(.3, -3.95); paint(null, '#C9CFDB', .07);
      ctx.beginPath(); ctx.moveTo(-1.1, -7.3); ctx.quadraticCurveTo(-.9, -6, -1.05, -4.6); paint(null, 'rgb(255 255 255 / .25)', .14);
    } else if (top === 'turtleneck') {
      rrect(-.55, -8.5, 1.1, .6, .2); paint(shade(topCol, .15), OL, LW * .8);
    } else if (top === 'layers') {
      const cs = [o.shirtCol ?? '#E8E0CC', o.midCol ?? '#6B7A5A', topCol];
      poly([[-.9, -8.05], [.9, -8.05], [0, -5.6]]); paint(cs[0], OL, LW * .7);
      for (const sd of [-1, 1]) { poly([[sd * .55, -8.05], [sd * 1.1, -7.9], [sd * .5, -6.2], [0, -5.9]]); paint(cs[1], OL, LW * .7); }
      for (const sd of [-1, 1]) { poly([[sd * 1.0, -8.0], [sd * 1.5, -7.6], [sd * 1.0, -5.0], [sd * .55, -6.0]]); paint(shade(cs[2], .1), OL, LW * .7); }
    } else if (top === 'dress' || top === 'robe') {
      ctx.beginPath(); ctx.ellipse(0, -8.05, .7, .45, 0, 0, Math.PI); paint(skin, OL, LW * .7);
    }
    if (o.pearls) for (let i = -4; i <= 4; i++) { ell(i * .15, -7.95 + Math.abs(i) * -.02 + (1 - (i / 4) ** 2) * .28, .09); paint('#F4F0E6', OL, .03); }
  }
  torso(); paint(null, OL, LW);
  if (o.tag && !sil) nameTag(o.tag, .75, -6.35, .36, -.08);
  // ---- arms ----
  const L1 = 1.72, L2 = 1.62, AW = .64;
  const arm = (side, a, e, reach, hand, hold) => {
    const sx = side * 1.3, sy = -7.55;
    if (reach) {
      let tx = (reach[0] - sx) * side, ty = reach[1] - sy;
      const d = clamp(Math.hypot(tx, ty), .2, L1 + L2 - .02), th = Math.atan2(-ty, tx);
      const b = Math.acos(clamp((L1 * L1 + d * d - L2 * L2) / (2 * L1 * d), -1, 1));
      a = th + b * (o.elbowIn ? -1 : 1);
      const ex = Math.cos(a) * L1, ey = -Math.sin(a) * L1, k = d / Math.hypot(tx, ty);
      e = Math.atan2(-(ty * k - ey), tx * k - ex) - a;
    }
    const ex = side * Math.cos(a) * L1, ey = -Math.sin(a) * L1, a2 = a + e, hx = ex + side * Math.cos(a2) * L2, hy = ey - Math.sin(a2) * L2;
    ctx.save(); ctx.translate(sx, sy);
    const sleeve = top === 'tee' ? skin : topCol;
    ctx.beginPath(); ctx.moveTo(0, 0); ctx.lineTo(ex, ey); ctx.lineTo(hx, hy);
    if (OL) { ctx.strokeStyle = OL; ctx.lineWidth = AW + LW * 2; ctx.stroke(); }
    ctx.strokeStyle = sleeve; ctx.lineWidth = AW; ctx.stroke();
    if (top === 'tee') { ctx.beginPath(); ctx.moveTo(0, 0); ctx.lineTo(ex * .55, ey * .55); ctx.strokeStyle = topCol; ctx.lineWidth = AW + .08; ctx.stroke(); }
    else if (!sil && (top === 'suit' || top === 'blazer' || top === 'labcoat')) { ell(hx - side * Math.cos(a2) * .38, hy + Math.sin(a2) * .38, .3, .3); paint(shirt); }
    // hand
    const hd = hand ?? 'fist', dx = side * Math.cos(a2), dy = -Math.sin(a2);
    if (hd === 'point') { ctx.beginPath(); ctx.moveTo(hx, hy); ctx.lineTo(hx + dx * .62, hy + dy * .62); if (OL) { ctx.strokeStyle = OL; ctx.lineWidth = .24 + LW * 2; ctx.stroke(); } ctx.strokeStyle = skin; ctx.lineWidth = .24; ctx.stroke(); }
    if (hd === 'open' || hd === 'wave') for (let f = -2; f <= 2; f++) { const fa = Math.atan2(dy, dx) + f * .38; ctx.beginPath(); ctx.moveTo(hx, hy); ctx.lineTo(hx + Math.cos(fa) * .55, hy + Math.sin(fa) * .55); if (OL) { ctx.strokeStyle = OL; ctx.lineWidth = .2 + LW * 2; ctx.stroke(); } ctx.strokeStyle = skin; ctx.lineWidth = .2; ctx.stroke(); }
    if (hd === 'thumb') { ctx.beginPath(); ctx.moveTo(hx, hy); ctx.lineTo(hx, hy - .55); if (OL) { ctx.strokeStyle = OL; ctx.lineWidth = .24 + LW * 2; ctx.stroke(); } ctx.strokeStyle = skin; ctx.lineWidth = .24; ctx.stroke(); }
    ell(hx, hy, .34); paint(skin, OL, LW);
    if (hold) { ctx.save(); ctx.translate(hx, hy); ctx.scale(1 / s, 1 / s); hold(s); ctx.restore(); }
    ctx.restore();
  };
  arm(-1, o.aL ?? -1.35, o.eL ?? .12, o.reachL, o.handL, o.holdL);
  arm(1, o.aR ?? -1.35, o.eR ?? .12, o.reachR, o.hand, o.hold);
  // ---- head ----
  if (!o.hood) for (const sd of [-1, 1]) { ell(sd * (RX - .02), -9.5, .24, .34); paint(skin, OL, LW); }
  ell(HX, HY, RX, RY); paint(skin, OL, LW);
  if (!sil) { ctx.save(); ell(HX, HY, RX, RY); ctx.clip(); ctx.fillStyle = shade(skin, .1); ctx.beginPath(); ctx.rect(-3, -12, 6, 5); ctx.ellipse(HX - .32, HY - .12, RX, RY + .1, 0, 0, TAU); ctx.fill('evenodd'); ctx.restore(); }
  const faceless = o.faceless || sil;
  if (o.hood) {
    ctx.save(); ell(HX, HY, RX, RY); ctx.clip(); ctx.fillStyle = sil ?? '#16121E'; ctx.fillRect(-3, -12, 6, 5); ctx.restore();
    ctx.beginPath(); ctx.ellipse(HX, HY - .1, RX + .62, RY + .55, 0, 0, TAU); ctx.ellipse(HX, HY + .05, RX - .05, RY - .02, 0, 0, TAU);
    ctx.fillStyle = topCol; ctx.fill('evenodd'); if (OL) { ctx.strokeStyle = OL; ctx.lineWidth = LW; ctx.stroke(); }
    if (!sil) { ctx.fillStyle = shade(topCol, .22); ctx.beginPath(); ctx.ellipse(HX, HY + .05, RX + .12, RY + .1, 0, 0, TAU); ctx.ellipse(HX, HY + .05, RX - .05, RY - .02, 0, 0, TAU); ctx.fill('evenodd'); }
  } else if (faceless) {
    if (!sil) { ctx.save(); ell(HX, HY, RX, RY); ctx.clip(); ctx.fillStyle = 'rgb(10 8 20 / .85)'; ctx.fillRect(-3, -12, 6, 5); ctx.restore(); }
  }
  if (!faceless && !o.hood) {
    // eyes
    const eyes = o.eyes ?? 'open', blink = o.blink ?? 0, lx = (o.lookX ?? 0) * .12, ly = (o.lookY ?? 0) * .12;
    for (const sd of [-1, 1]) {
      const ex = sd * .47, ey = -9.62;
      ctx.save(); ctx.translate(ex, ey);
      if (eyes === 'open' || eyes === 'wide' || eyes === 'half' || eyes === 'angry' || eyes === 'worried') {
        const wr = eyes === 'wide' ? 1.25 : 1, lid = eyes === 'half' ? .5 : blink;
        ell(0, 0, .29 * wr, .35 * wr); paint('#FFFFFF', OL, LW * .7);
        ell(lx, ly, (eyes === 'wide' ? .11 : .15), (eyes === 'wide' ? .12 : .17)); paint(NP.ink);
        ell(lx + .05, ly - .06, .045); paint('#FFFFFF');
        if (lid > 0 || eyes === 'angry' || eyes === 'worried') {
          ctx.save(); ell(0, 0, .29 * wr, .35 * wr); ctx.clip(); ctx.fillStyle = skin;
          if (lid > 0) ctx.fillRect(-.5, -.5, 1, .15 + lid * .72);
          if (eyes === 'angry') poly([[-.5 * sd, -.5], [.5 * sd, -.5], [.5 * sd, -.02], [-.5 * sd, -.28]].map(([a, b]) => [a * -1, b])), ctx.fill();
          if (eyes === 'worried') poly([[-.5 * sd, -.5], [.5 * sd, -.5], [.5 * sd, -.3], [-.5 * sd, -.02]].map(([a, b]) => [a * -1, b])), ctx.fill();
          ctx.restore(); ell(0, 0, .29 * wr, .35 * wr); paint(null, OL, LW * .7);
        }
      } else if (eyes === 'dot') { ell(lx * .5, ly * .5, .12, .15); paint(NP.ink); }
      else if (eyes === 'closed') { ctx.beginPath(); ctx.arc(0, -.08, .24, .15 * Math.PI, .85 * Math.PI); paint(null, NP.ink, .09); }
      else if (eyes === 'happy') { ctx.beginPath(); ctx.arc(0, .1, .24, 1.15 * Math.PI, 1.85 * Math.PI); paint(null, NP.ink, .1); }
      else if (eyes === 'x') { ctx.beginPath(); ctx.moveTo(-.18, -.18); ctx.lineTo(.18, .18); ctx.moveTo(.18, -.18); ctx.lineTo(-.18, .18); paint(null, NP.ink, .1); }
      else if (eyes === 'spark') { poly(starPts(0, 0, .34, .35, 4, 0)); paint(NP.gold, OL, .04); }
      else if (eyes === 'heart') { poly(heartPts(0, 0, .3, 20)); paint(NP.red, OL, .04); }
      ctx.restore();
    }
    if (o.glasses) {
      const g = o.glasses; ctx.lineWidth = .08;
      for (const sd of [-1, 1]) {
        if (g === 'round') ell(sd * .47, -9.62, .38, .38);
        else if (g === 'aviator') { ctx.beginPath(); ctx.moveTo(sd * .08, -9.95); ctx.lineTo(sd * .9, -9.95); ctx.quadraticCurveTo(sd * .95, -9.2, sd * .5, -9.15); ctx.quadraticCurveTo(sd * .1, -9.2, sd * .08, -9.95); }
        else rrect(sd * .47 - .38, -9.95, .76, .62, .12);
        paint(g === 'shades' ? '#15121C' : g === 'aviator' ? 'rgb(120 80 40 / .45)' : 'rgb(200 230 255 / .18)', NP.ink, .08);
      }
      ctx.beginPath(); ctx.moveTo(-.1, -9.75); ctx.lineTo(.1, -9.75); paint(null, NP.ink, .08);
    }
    // nose
    ctx.beginPath(); ctx.moveTo(.02, -9.42); ctx.quadraticCurveTo(.2, -9.08, -.05, -9.06); paint(null, shade(skin, .35), .08);
    if (o.blush) { ctx.fillStyle = 'rgb(255 110 140 / .4)'; ell(-.78, -9.1, .24, .13); ctx.fill(); ell(.78, -9.1, .24, .13); ctx.fill(); }
    // facial hair (under the mouth)
    const bc = C(o.beardCol ?? hairCol);
    if (o.beard) { ctx.beginPath(); ctx.moveTo(-1.22, -9.35); ctx.quadraticCurveTo(-1.1, -8.05, 0, -7.85); ctx.quadraticCurveTo(1.1, -8.05, 1.22, -9.35); ctx.quadraticCurveTo(.8, -8.55, 0, -8.5); ctx.quadraticCurveTo(-.8, -8.55, -1.22, -9.35); paint(bc, OL, LW * .7); }
    if (o.stubble) { ctx.fillStyle = 'rgb(40 30 30 / .25)'; ctx.beginPath(); ctx.ellipse(0, -8.75, .95, .55, 0, 0, Math.PI); ctx.fill(); }
    // mouth
    const my = -8.78, m = o.talk !== undefined ? 'talk' : (o.mouth ?? 'smile');
    if (m === 'talk') { const k = clamp(o.talk); rrect(-.28, my - .08, .56, .14 + k * .36, .12); paint('#5A1A20', OL, LW * .6); }
    else if (m === 'smile') { ctx.beginPath(); ctx.arc(0, my - .3, .36, .22 * Math.PI, .78 * Math.PI); paint(null, NP.ink, .09); }
    else if (m === 'grin') { ctx.beginPath(); ctx.moveTo(-.45, my - .12); ctx.quadraticCurveTo(0, my + .55, .45, my - .12); ctx.closePath(); paint('#5A1A20', OL, LW * .6); ctx.fillStyle = '#FFF'; ctx.fillRect(-.33, my - .1, .66, .12); }
    else if (m === 'flat') { ctx.beginPath(); ctx.moveTo(-.28, my); ctx.lineTo(.28, my); paint(null, NP.ink, .09); }
    else if (m === 'frown') { ctx.beginPath(); ctx.arc(0, my + .3, .32, 1.22 * Math.PI, 1.78 * Math.PI); paint(null, NP.ink, .09); }
    else if (m === 'smirk') { ctx.beginPath(); ctx.moveTo(-.25, my); ctx.quadraticCurveTo(.15, my + .1, .35, my - .15); paint(null, NP.ink, .09); }
    else if (m === 'o') { ell(0, my, .14, .18); paint('#5A1A20', OL, LW * .6); }
    else if (m === 'O' || m === 'scream') { ell(0, my + .05, .3, m === 'scream' ? .45 : .38); paint('#5A1A20', OL, LW * .6); ell(0, my + .22, .17, .1); paint('#E0606A'); }
    if (o.mustache) { ctx.beginPath(); ctx.moveTo(0, -9.0); ctx.quadraticCurveTo(-.5, -9.12, -.62, -8.8); ctx.quadraticCurveTo(-.3, -8.9, 0, -8.88); ctx.quadraticCurveTo(.3, -8.9, .62, -8.8); ctx.quadraticCurveTo(.5, -9.12, 0, -9.0); paint(bc, OL, LW * .6); }
    if (o.earrings) for (const sd of [-1, 1]) { ell(sd * 1.3, -9.1, .13); paint(o.earrings === true ? NP.gold : o.earrings, OL, .04); }
    if (o.sweat) { poly([[1.15, -10.4], [1.35, -9.95], [1.15, -9.8], [.97, -9.95]]); paint('#9FD3F2', OL, .04); }
  }
  // ---- front hair ----
  const cap = (ex, mid, side = .95, hl = -9.4) => {
    ctx.beginPath(); ctx.ellipse(HX, HY, RX + ex, RY + ex, 0, Math.PI * 1.0, Math.PI * 2.0);
    ctx.lineTo(RX * side, hl); ctx.quadraticCurveTo(0, 2 * mid - hl, -RX * side, hl); ctx.closePath();
  };
  if (!o.hood && !sil) {
    if (hair === 'short' || hair === 'side' || hair === 'swoop' || hair === 'pompadour' || hair === 'buzz' || hair === 'bob' || hair === 'long' || hair === 'bun' || hair === 'big80s') {
      const mid = hair === 'buzz' ? -10.45 : hair === 'bob' || hair === 'long' ? -10.25 : hair === 'big80s' ? -10.35 : -10.35;
      cap(hair === 'buzz' ? .03 : .1, mid, hair === 'big80s' ? 1 : .95, hair === 'bob' || hair === 'long' ? -9.1 : -9.4); paint(hairCol, OL, LW);
      if (hair === 'side' || hair === 'swoop') { ctx.beginPath(); ctx.moveTo(-.55, -10.95); ctx.quadraticCurveTo(-.1, -10.2, 1.2, -10.1); ctx.quadraticCurveTo(.4, -10.7, -.55, -10.95); paint(shade(hairCol, .2), OL, LW * .6); }
      if (hair === 'swoop') { ctx.beginPath(); ctx.moveTo(-1.3, -10.2); ctx.quadraticCurveTo(-.9, -11.6, .8, -11.3); ctx.quadraticCurveTo(1.5, -11.0, 1.35, -10.2); ctx.quadraticCurveTo(.4, -10.9, -1.3, -10.2); paint(hairCol, OL, LW); }
      if (hair === 'pompadour') { ell(.1, -11.05, 1.05, .55, -.1); paint(hairCol, OL, LW); ctx.beginPath(); ctx.moveTo(-.6, -11.2); ctx.quadraticCurveTo(.2, -11.5, .9, -11.1); paint(null, tint(hairCol, .3), .08); }
      if (hair === 'big80s') { ctx.beginPath(); ctx.moveTo(-1.45, -9.7); ctx.quadraticCurveTo(-1.6, -11.6, .3, -11.5); ctx.quadraticCurveTo(1.7, -11.3, 1.45, -9.9); ctx.quadraticCurveTo(.9, -10.9, -.2, -10.55); ctx.quadraticCurveTo(-1.0, -10.5, -1.45, -9.7); paint(hairCol, OL, LW); ctx.beginPath(); ctx.moveTo(-.9, -11.1); ctx.quadraticCurveTo(0, -11.45, .9, -11.0); paint(null, tint(hairCol, .35), .1); }
      if (hair === 'bun') { ell(0, -11.25, .6, .48); paint(hairCol, OL, LW); }
      if (hair === 'buzz') { ctx.fillStyle = 'rgb(255 255 255 / .12)'; ell(-.3, -10.6, .5, .15); ctx.fill(); }
    } else if (hair === 'slick') {
      cap(.08, -10.7, .95, -9.55); paint(hairCol, OL, LW);
      for (const k of [-.5, 0, .5]) { ctx.beginPath(); ctx.moveTo(k - .3, -10.55); ctx.quadraticCurveTo(k, -10.95, k + .45, -10.85); paint(null, tint(hairCol, .35), .07); }
    } else if (hair === 'curly') {
      for (let i = 0; i <= 8; i++) { const a = Math.PI * (1.02 + i / 8 * .96); ell(Math.cos(a) * (RX + .05), HY + Math.sin(a) * (RY + .02), .42, .42); paint(hairCol, OL, LW * .8); }
      ell(0, -10.5, 1.05, .6); paint(hairCol);
    } else if (hair === 'spiky') {
      ctx.beginPath(); ctx.moveTo(-1.3, -9.6); for (let i = 0; i <= 6; i++) { const u = i / 6, bx = lerp(-1.3, 1.3, u); ctx.lineTo(bx - .1, -10.6 - (i % 2 ? .1 : .75) - Math.sin(u * Math.PI) * .45); } ctx.lineTo(1.3, -9.6); ctx.quadraticCurveTo(0, -10.5, -1.3, -9.6); paint(hairCol, OL, LW);
    } else if (hair === 'balding') {
      for (const sd of [-1, 1]) { ctx.beginPath(); ctx.ellipse(sd * 1.12, -9.85, .34, .62, sd * .2, 0, TAU); paint(hairCol, OL, LW * .8); }
      ctx.beginPath(); ctx.moveTo(-.4, -10.9); ctx.quadraticCurveTo(0, -11.2, .5, -10.95); paint(null, hairCol, .08);
    } else if (hair === 'bald') {
      ctx.fillStyle = 'rgb(255 255 255 / .25)'; ell(-.35, -10.55, .45, .18, -.2); ctx.fill();
    }
    // brows
    if (!faceless) {
      const br = o.brows ?? (o.eyes === 'angry' ? 'angry' : o.eyes === 'worried' ? 'worried' : o.eyes === 'wide' ? 'up' : 'flat');
      const bcol = hair === 'bald' ? shade(skin, .5) : shade(hairCol, .25);
      for (const sd of [-1, 1]) {
        const lift = br === 'up' || br === 'raised' ? -.2 : 0, inner = br === 'angry' ? .16 : br === 'worried' ? -.16 : 0;
        ctx.beginPath(); ctx.moveTo(sd * .2, -10.1 + lift + inner); ctx.lineTo(sd * .78, -10.12 + lift - inner * .4); paint(null, bcol, .14);
      }
    }
  }
  // ---- hats ----
  const hat = o.hat, hc = C(o.hatCol ?? '#2E2B33');
  if (hat === 'fedora') { ell(0, -10.55, 2.05, .38); paint(hc, OL, LW); ctx.beginPath(); ctx.moveTo(-1.1, -10.6); ctx.lineTo(-.95, -11.85); ctx.quadraticCurveTo(0, -12.2, .95, -11.85); ctx.lineTo(1.1, -10.6); ctx.closePath(); paint(hc, OL, LW); rrect(-1.08, -11.0, 2.16, .36, .05); paint(C(o.hatBand ?? '#8A1219')); }
  else if (hat === 'visor') { ctx.beginPath(); ctx.ellipse(0, -10.3, RX + .08, .5, 0, Math.PI, TAU); paint(C('#2E8B57'), OL, LW); ctx.beginPath(); ctx.moveTo(-1.2, -10.3); ctx.quadraticCurveTo(0, -9.4, 1.2, -10.3); ctx.quadraticCurveTo(0, -9.85, -1.2, -10.3); paint(C('rgb(40 200 120 / .7)'), OL, LW * .7); }
  else if (hat === 'cap') { ctx.beginPath(); ctx.ellipse(0, -10.25, RX + .1, 1.05, 0, Math.PI, TAU); paint(hc, OL, LW); ctx.beginPath(); ctx.ellipse(.7, -10.25, 1.1, .28, 0, 0, TAU); paint(shade(hc, .2), OL, LW); }
  else if (hat === 'hardhat') { ctx.beginPath(); ctx.ellipse(0, -10.35, RX + .15, 1.05, 0, Math.PI, TAU); paint(C(NP.gold), OL, LW); rrect(-RX - .45, -10.5, (RX + .45) * 2, .3, .1); paint(C(NP.gold), OL, LW); }
  else if (hat === 'beret') { ell(.25, -10.75, 1.35, .5, -.12); paint(hc, OL, LW); }
  else if (hat === 'headset') { ctx.beginPath(); ctx.arc(0, -9.6, RX + .12, Math.PI * 1.1, Math.PI * 1.9); paint(null, '#222', .14); rrect(RX - .1, -9.9, .3, .6, .12); paint('#333', OL, LW * .6); ctx.beginPath(); ctx.moveTo(RX + .05, -9.4); ctx.quadraticCurveTo(.9, -8.6, .35, -8.75); paint(null, '#333', .07); }
  ctx.restore();
}

// nameTag(name, x, y, k, rot): a clean "HELLO my name is" sticker, ≈ 5.4k wide, centred on (x, y). Works inside scaled contexts.
function nameTag(name, x, y, k, rot = -.06) {
  ctx.save(); ctx.translate(x, y); ctx.rotate(rot);
  const w = Math.max(5.4 * k, textW(name, 1.5 * k, 'marker') + 1.2 * k), h = 3.4 * k;
  ctx.fillStyle = 'rgb(0 0 0 / .25)'; rrect(-w / 2 + .12 * k, -h / 2 + .16 * k, w, h, .45 * k); ctx.fill();
  rrect(-w / 2, -h / 2, w, h, .45 * k); paint(NP.red, NP.ink, .1 * k);
  ctx.fillStyle = '#FFFFFF'; ctx.fillRect(-w / 2 + .25 * k, -h / 2 + 1.25 * k, w - .5 * k, h - 1.6 * k);
  txt('HELLO', 0, -h / 2 + .5 * k, .72 * k, '#FFFFFF', { font: 'archivo' });
  txt('my name is', 0, -h / 2 + 1 * k, .32 * k, '#FFFFFF', { font: 'archivo' });
  txt(name, 0, .45 * k, 1.4 * k, NP.ink, { font: 'marker', maxW: w - .8 * k });
  ctx.restore();
}
// Anchor/reporter presets (the station's own on-air talent; fictional).
const CAST = {
  val: { name: 'VAL LOSS', role: 'CO-ANCHOR', o: { hair: 'big80s', hairCol: '#E2B95A', top: 'blazer', topCol: '#C8286E', shirtCol: '#FFF4F0', skin: 4, earrings: true, pearls: true, eyes: 'open' } },
  sunny: { name: 'SUNNY DESCENT', role: 'CHIEF METEOROLOGIST', o: { hair: 'pompadour', hairCol: '#3A2A1E', top: 'suit', topCol: '#2F8FB0', tie: '#FFB23B', skin: 2, mustache: true } },
  batch: { name: 'BATCH NORMAN', role: 'SPORTS', o: { hair: 'side', hairCol: '#5A3A24', top: 'blazer', topCol: '#1E7A4A', tie: NP.gold, skin: 1, mustache: true } },
  randi: { name: 'RANDI SEED', role: 'LIVE ON THE SCENE', o: { hair: 'bob', hairCol: '#2A1A14', top: 'trench', topCol: '#C9A46A', skin: 3, earrings: true } },
  chip: { name: 'CHIP STACKS', role: 'MONEY WATCH', o: { hair: 'slick', hairCol: '#1E1A1D', top: 'suit', topCol: '#3A3F58', tie: NP.red, pocket: NP.gold, skin: 0, glasses: 'square' } },
};

// =====================================================================================================
// CLAWD, THE ANCHOR — newsClawd(x, y, u, o): Clawd in a navy suit and red tie. (x, y) = ground between the feet; body 10u × 6u, ≈ 8u tall.
// o: suit (false = bare Clawd), suitCol, tie, eyes: normal|happy|closed|wide|x|heart|worried|angry|shades|spark, lookX/lookY (−1..1),
//    talk (0..1 mouth), mouth: none|smile|o|O|grin|flat, blush, sweat, hair ('anchor' = sprayed news-anchor helmet), aL/aR (angles like
//    clawd()), reachL/reachR ([x, y] in u from the ground point; IK), hold/holdL (fn(u) at the nub), legs (false), walk, dy, rot, flip, sq, col, glow.
// =====================================================================================================
function newsClawd(x, y, u, o = {}) {
  const col = o.col ?? NP.clawd, dk = shade(col, .28), OL = NP.ink, LW = .16, suit = o.suit !== false, sc = o.suitCol ?? '#1C2A5E';
  ctx.save(); ctx.translate(x, y);
  if (o.shadow !== false && o.legs !== false) { ctx.fillStyle = 'rgb(0 0 0 / .22)'; ell(0, 0, 6 * u, .9 * u); ctx.fill(); }
  ctx.translate(0, (o.dy ?? 0) * u); if (o.rot) ctx.rotate(o.rot); ctx.scale(o.flip ? -u : u, u); if (o.sq) ctx.scale(1 + o.sq * .5, 1 - o.sq);
  ctx.lineJoin = 'round'; ctx.lineCap = 'round';
  if (o.glow) { ctx.fillStyle = alpha(o.glow, .3); ell(0, -5, 8, 6); ctx.fill(); }
  if (o.legs !== false) [-3.6, -1.4, 1.4, 3.6].forEach((lx, i) => {
    const lift = o.walk !== undefined ? Math.max(0, Math.sin(o.walk * TAU + (i % 2) * Math.PI)) * .9 : 0;
    rrect(lx - .55, -2.2 - lift, 1.1, 2.2, .2); paint(suit && i % 3 === 0 ? dk : dk, OL, LW);
  });
  // arms: two-segment sleeves ending in orange nubs
  const L1 = 1.7, L2 = 1.6;
  const arm = (side, a, reach, hold) => {
    const sx = side * 4.7, sy = -4.5; let e = 0;
    if (reach) {
      const tx = (reach[0] - sx) * side, ty = reach[1] - sy, d = clamp(Math.hypot(tx, ty), .2, L1 + L2 - .02), th = Math.atan2(-ty, tx);
      const b = Math.acos(clamp((L1 * L1 + d * d - L2 * L2) / (2 * L1 * d), -1, 1)); a = th + b;
      const ex = Math.cos(a) * L1, ey = -Math.sin(a) * L1, k = d / Math.hypot(tx, ty); e = Math.atan2(-(ty * k - ey), tx * k - ex) - a;
    }
    const ex = side * Math.cos(a) * L1, ey = -Math.sin(a) * L1, hx = ex + side * Math.cos(a + e) * L2, hy = ey - Math.sin(a + e) * L2;
    ctx.save(); ctx.translate(sx, sy);
    ctx.beginPath(); ctx.moveTo(0, 0); ctx.lineTo(ex, ey); ctx.lineTo(hx, hy);
    ctx.strokeStyle = OL; ctx.lineWidth = 1.25 + LW * 2; ctx.stroke(); ctx.strokeStyle = suit ? sc : col; ctx.lineWidth = 1.25; ctx.stroke();
    if (suit) { ell(hx - side * Math.cos(a + e) * .5, hy + Math.sin(a + e) * .5, .55, .55); paint('#F4F2EC'); }
    rrect(hx - .62, hy - .62, 1.24, 1.24, .35); paint(col, OL, LW);
    if (hold) { ctx.save(); ctx.translate(hx, hy); ctx.scale(1 / u, 1 / u); hold(u); ctx.restore(); }
    ctx.restore();
  };
  // body
  rrect(-5, -8, 10, 6, .35); paint(col, OL, LW);
  ctx.save(); rrect(-5, -8, 10, 6, .35); ctx.clip(); ctx.fillStyle = dk; ctx.globalAlpha = .35; poly([[3.4, -8.5], [6, -8.5], [6, -1], [3.9, -1]]); ctx.fill(); ctx.restore();
  if (suit) {
    ctx.save(); rrect(-5, -8, 10, 6, .35); ctx.clip();
    for (const sd of [-1, 1]) { poly([[sd * 5.2, -4.75], [sd * 1.05, -4.75], [0, -2.85], [0, -1.8], [sd * 5.2, -1.8]]); paint(sc); }
    ctx.fillStyle = shade(sc, .3); poly([[3.3, -4.8], [5.2, -4.8], [5.2, -1.8], [3.6, -1.8]]); ctx.fill();
    ctx.restore();
    poly([[-1.05, -4.75], [1.05, -4.75], [0, -2.85]]); paint('#F4F2EC', OL, LW * .8);
    const tie = o.tie ?? NP.red; poly([[-.26, -4.55], [.26, -4.55], [.42, -3.45], [0, -2.95], [-.42, -3.45]]); paint(tie, OL, LW * .7); rrect(-.33, -4.78, .66, .42, .1); paint(shade(tie, .2), OL, LW * .6);
    for (const sd of [-1, 1]) { poly([[sd * 1.05, -4.75], [sd * 2.1, -4.75], [sd * .5, -3.3], [0, -2.85]]); paint(shade(sc, .25), OL, LW * .7); poly([[sd * .25, -4.75], [sd * 1.05, -4.75], [sd * .75, -4.25]]); paint('#FFFFFF', OL, LW * .5); }
    poly([[-3.9, -4.1], [-3.0, -4.1], [-3.2, -4.55], [-3.45, -4.35], [-3.65, -4.6]]); paint(o.pocket ?? NP.gold, OL, LW * .5);
    ell(3.0, -3.95, .28); paint(NP.gold, OL, LW * .5);
    ctx.beginPath(); ctx.moveTo(-5, -4.75); ctx.lineTo(5, -4.75); paint(null, OL, LW * .6);
  }
  arm(-1, o.aL ?? -.2, o.reachL, o.holdL); arm(1, o.aR ?? -.2, o.reachR, o.hold);
  // hair: the sprayed anchor helmet
  if (o.hair === 'anchor') { ctx.beginPath(); ctx.moveTo(-5.2, -7.2); ctx.quadraticCurveTo(-5.6, -9.9, -1.5, -9.9); ctx.quadraticCurveTo(2.8, -10.3, 4.6, -9.1); ctx.quadraticCurveTo(5.5, -8.4, 5.2, -7.3); ctx.quadraticCurveTo(3, -8.6, .2, -8.1); ctx.quadraticCurveTo(-3.2, -8.9, -5.2, -7.2); paint('#4A2E1C', OL, LW); ctx.beginPath(); ctx.moveTo(-3.8, -9.1); ctx.quadraticCurveTo(-.5, -9.8, 3.2, -9.3); paint(null, 'rgb(255 255 255 / .35)', .22); }
  // face
  const eyes = o.eyes ?? 'normal', lx = (o.lookX ?? 0) * .5, ly = (o.lookY ?? 0) * .4, ey = -6.2;
  for (const sd of [-1, 1]) {
    ctx.save(); ctx.translate(sd * 2.3 + lx, ey + ly);
    switch (eyes) {
      case 'happy': ctx.beginPath(); ctx.arc(0, .4, .7, Math.PI * 1.1, Math.PI * 1.9); paint(null, NP.ink, .45); break;
      case 'closed': ctx.beginPath(); ctx.moveTo(-.7, 0); ctx.lineTo(.7, 0); paint(null, NP.ink, .4); break;
      case 'x': ctx.beginPath(); ctx.moveTo(-.6, -.6); ctx.lineTo(.6, .6); ctx.moveTo(.6, -.6); ctx.lineTo(-.6, .6); paint(null, NP.ink, .4); break;
      case 'heart': poly(heartPts(0, 0, .95, 24)); paint(NP.red, OL, .12); break;
      case 'spark': poly(starPts(0, 0, 1.05, .4, 4, 0)); paint(NP.gold, OL, .12); break;
      case 'wide': ell(0, 0, .85, 1.0); paint('#FFFFFF', OL, .15); ell(lx * .3, ly * .3, .38, .48); paint(NP.ink); break;
      case 'angry': rrect(-.45, -.55, .9, 1.35, .15); paint(NP.ink); ctx.beginPath(); ctx.moveTo(-sd * .9, -1.3); ctx.lineTo(sd * .7, -.75); paint(null, NP.ink, .35); break;
      case 'worried': rrect(-.45, -.5, .9, 1.25, .15); paint(NP.ink); ctx.beginPath(); ctx.moveTo(-sd * .8, -1.0); ctx.lineTo(sd * .7, -1.45); paint(null, NP.ink, .35); break;
      case 'shades': break;
      default: { const bl = o.blink ?? 0; rrect(-.45, -.8 + bl * .7, .9, 1.6 * (1 - bl * .85), .15); paint(NP.ink); }
    }
    ctx.restore();
  }
  if (eyes === 'shades') { ctx.fillStyle = NP.ink; ctx.fillRect(-4, ey - .8, 8, .45); for (const sd of [-1, 1]) { rrect(sd * 2.3 - 1.3, ey - .8, 2.6, 1.7, .6); paint(NP.ink); } ctx.fillStyle = 'rgb(255 255 255 / .5)'; ctx.fillRect(-3.1, ey - .5, .7, .3); ctx.fillRect(1.5, ey - .5, .7, .3); }
  if (o.blush) { ctx.fillStyle = 'rgb(255 110 150 / .45)'; ell(-3.6, -4.9, .9, .45); ctx.fill(); ell(3.6, -4.9, .9, .45); ctx.fill(); }
  const my = -5.25, mouth = o.talk !== undefined ? 'talk' : (o.mouth ?? 'none');
  if (mouth === 'talk') { const k = clamp(o.talk); rrect(-.75, my - .2 - k * .25, 1.5, .35 + k * .75, .3); paint('#4A1418', OL, .12); }
  else if (mouth === 'smile') { ctx.beginPath(); ctx.arc(0, my - .8, 1.1, .25 * Math.PI, .75 * Math.PI); paint(null, NP.ink, .32); }
  else if (mouth === 'grin') { ctx.beginPath(); ctx.moveTo(-1.3, my - .35); ctx.quadraticCurveTo(0, my + 1.1, 1.3, my - .35); ctx.closePath(); paint('#4A1418', OL, .12); }
  else if (mouth === 'o') { ell(0, my, .5, .6); paint('#4A1418', OL, .12); }
  else if (mouth === 'O') { ell(0, my + .1, .85, 1.05); paint('#4A1418', OL, .12); }
  else if (mouth === 'flat') { ctx.beginPath(); ctx.moveTo(-.8, my); ctx.lineTo(.8, my); paint(null, NP.ink, .3); }
  if (o.sweat) { poly([[4.4, -8], [5, -6.8], [4.4, -6.4], [3.8, -6.8]]); paint('#9FD3F2', OL, .1); }
  ctx.restore();
}

// =====================================================================================================
// AI CHARACTERS — every AI model is an 80s personal computer with a face on its screen.
// computer(x, y, s, o): (x, y) = ground point; ≈ 10s tall, 6s wide. o: case (colour), screen (bg colour), glow (phosphor colour),
//   face: smile|grin|o|O|heart|x|angry|sly|sleep|happy|dizzy|think|wide|blank|sad, text (screen text instead of a face, \n for lines),
//   label (on the base unit), arms (true), aL/aR/eL/eR/reachL/reachR/hand/hold like toon(), legs (true), walk, dy, rot, flip, sq, blink.
// =====================================================================================================
function computer(x, y, s, o = {}) {
  const cs = o.case ?? NP.beige, OL = NP.ink, LW = .09, glow = o.glow ?? NP.phosphor, scr = o.screen ?? '#0C1A12';
  ctx.save(); ctx.translate(x, y);
  if (o.shadow !== false) { ctx.fillStyle = 'rgb(0 0 0 / .22)'; ell(0, 0, 3.2 * s, .5 * s); ctx.fill(); }
  ctx.translate(0, (o.dy ?? 0) * s); if (o.rot) ctx.rotate(o.rot); ctx.scale(o.flip ? -s : s, s); if (o.sq) ctx.scale(1 + o.sq * .4, 1 - o.sq);
  ctx.lineJoin = 'round'; ctx.lineCap = 'round';
  const legs = o.legs !== false;
  if (legs) for (const sd of [-1, 1]) {
    const sw = o.walk !== undefined ? Math.sin(o.walk * TAU + (sd > 0 ? Math.PI : 0)) * .4 : 0;
    ctx.save(); ctx.translate(sd * 1.1, -2.1); ctx.rotate(sw);
    ctx.beginPath(); ctx.moveTo(0, 0); ctx.lineTo(0, 1.8); ctx.strokeStyle = OL; ctx.lineWidth = .5 + LW * 2; ctx.stroke(); ctx.strokeStyle = shade(cs, .35); ctx.lineWidth = .5; ctx.stroke();
    ell(sd * .2, 1.95, .6, .28); paint('#E8E8EC', OL, LW); ctx.restore();
  }
  const baseY = legs ? -2.1 : 0;
  // base unit
  rrect(-3, baseY - 1.7, 6, 1.7, .15); paint(cs, OL, LW);
  ctx.fillStyle = shade(cs, .15); ctx.fillRect(-3, baseY - .45, 6, .3);
  rrect(-2.5, baseY - 1.25, 2.1, .32, .05); paint(shade(cs, .4));
  ell(2.35, baseY - 1.05, .12); paint(frac(T * 1.7 + (o.seed ?? 0)) < .5 ? '#FF3030' : '#601010');
  if (o.label) txt(o.label, .9, baseY - .95, .62, NP.ink, { font: 'archivo', maxW: 2.6 });
  // monitor
  const my0 = baseY - 1.75 - 5.3;
  rrect(-.9, baseY - 2.05, 1.8, .45, .1); paint(shade(cs, .1), OL, LW);
  rrect(-2.7, my0, 5.4, 5.0, .45); paint(cs, OL, LW);
  ctx.save(); rrect(-2.7, my0, 5.4, 5.0, .45); ctx.clip(); ctx.fillStyle = shade(cs, .16); poly([[1.9, my0 - 1], [4, my0 - 1], [4, my0 + 6], [2.3, my0 + 6]]); ctx.fill(); ctx.restore();
  const sx = -2.15, sy = my0 + .45, sw = 4.3, sh = 3.55;
  rrect(sx, sy, sw, sh, .55); paint(scr, OL, LW);
  ctx.save(); rrect(sx, sy, sw, sh, .55); ctx.clip();
  ctx.fillStyle = rg(0, sy + sh / 2, .2, 3, [[0, alpha(glow, .22)], [1, alpha(glow, 0)]]); ctx.fillRect(sx, sy, sw, sh);
  const fcx = 0, fcy = sy + sh / 2;
  ctx.strokeStyle = glow; ctx.fillStyle = glow; ctx.lineWidth = .2;
  if (o.text !== undefined) {
    const L = String(o.text).split('\n'), fs = o.textSize ?? Math.min(.9, 3.3 / Math.max(3, ...L.map(l => l.length)) * 1.6);
    L.forEach((l, i) => txt(l, fcx, fcy + (i - (L.length - 1) / 2) * fs * 1.15, fs, glow, { font: 'code', maxW: sw - .4 }));
  } else {
    const f = o.face ?? 'smile', bl = o.blink ?? 0;
    const eye = (sd) => {
      const ex = sd * .85, ey = fcy - .45;
      if (f === 'heart') { poly(heartPts(ex, ey, .42, 16)); ctx.fill(); }
      else if (f === 'x' || f === 'dizzy') { ctx.beginPath(); ctx.moveTo(ex - .3, ey - .3); ctx.lineTo(ex + .3, ey + .3); ctx.moveTo(ex + .3, ey - .3); ctx.lineTo(ex - .3, ey + .3); ctx.stroke(); }
      else if (f === 'happy' || f === 'grin') { ctx.beginPath(); ctx.arc(ex, ey + .15, .3, Math.PI * 1.1, Math.PI * 1.9); ctx.stroke(); }
      else if (f === 'sleep' || f === 'blank') { ctx.beginPath(); ctx.moveTo(ex - .3, ey); ctx.lineTo(ex + .3, ey); ctx.stroke(); }
      else if (f === 'angry') { ctx.fillRect(ex - .22, ey - .1, .44, .4); ctx.beginPath(); ctx.moveTo(ex - sd * .4, ey - .45); ctx.lineTo(ex + sd * .3, ey - .15); ctx.stroke(); }
      else if (f === 'sly') { ctx.fillRect(ex - .25, ey, .5, .18); }
      else if (f === 'wide' || f === 'O') { ctx.beginPath(); ctx.arc(ex, ey, .33, 0, TAU); ctx.stroke(); ctx.fillRect(ex - .08, ey - .08, .16, .16); }
      else if (f === 'think') { ctx.fillRect(ex - .18 + .15, ey - .5 - .1, .36, .5); }
      else if (f === 'sad') { ctx.fillRect(ex - .18, ey - .25, .36, .5); ctx.beginPath(); ctx.moveTo(ex - sd * .35, ey - .45); ctx.lineTo(ex + sd * .3, ey - .6); ctx.stroke(); }
      else { const h = .6 * (1 - bl * .85); ctx.fillRect(ex - .18, ey - h / 2, .36, h); }
    };
    eye(-1); eye(1);
    const my = fcy + .55;
    if (f === 'smile' || f === 'happy' || f === 'heart' || f === 'sly') { ctx.beginPath(); ctx.arc(fcx, my - .45, .6, .2 * Math.PI, .8 * Math.PI); ctx.stroke(); }
    else if (f === 'grin') { ctx.beginPath(); ctx.moveTo(fcx - .75, my - .15); ctx.quadraticCurveTo(fcx, my + .7, fcx + .75, my - .15); ctx.closePath(); ctx.fill(); }
    else if (f === 'o' || f === 'O' || f === 'wide') { ctx.beginPath(); ctx.ellipse(fcx, my, f === 'o' ? .2 : .32, f === 'o' ? .25 : .42, 0, 0, TAU); ctx.fill(); }
    else if (f === 'angry' || f === 'sad') { ctx.beginPath(); ctx.arc(fcx, my + .45, .55, 1.2 * Math.PI, 1.8 * Math.PI); ctx.stroke(); }
    else if (f === 'x' || f === 'dizzy') { ctx.beginPath(); for (let i = 0; i <= 6; i++) ctx.lineTo(fcx - .7 + i * .23, my + (i % 2 ? .15 : -.1)); ctx.stroke(); }
    else if (f === 'think') { ctx.beginPath(); ctx.moveTo(fcx - .4, my); ctx.lineTo(fcx + .4, my - .1); ctx.stroke(); }
    else if (f === 'sleep') { txt('z', fcx + 1.2, fcy - 1.1, .7, glow, { font: 'code' }); }
    else if (f !== 'blank') { ctx.beginPath(); ctx.moveTo(fcx - .45, my); ctx.lineTo(fcx + .45, my); ctx.stroke(); }
  }
  // scanlines + glass
  ctx.fillStyle = 'rgb(0 0 0 / .22)'; for (let yy = sy; yy < sy + sh; yy += .18) ctx.fillRect(sx, yy, sw, .07);
  ctx.fillStyle = 'rgb(255 255 255 / .1)'; ell(sx + 1, sy + .7, 1.3, .45, -.3); ctx.fill();
  ctx.restore();
  // arms (gloved 80s-mascot hands)
  if (o.arms !== false) {
    const L1 = 1.5, L2 = 1.45;
    const arm = (side, a, e, reach, hand, hold) => {
      const ax = side * 2.65, ay = my0 + 3.1;
      if (reach) {
        const tx = (reach[0] - ax) * side, ty = reach[1] - ay, d = clamp(Math.hypot(tx, ty), .2, L1 + L2 - .02), th = Math.atan2(-ty, tx);
        const b = Math.acos(clamp((L1 * L1 + d * d - L2 * L2) / (2 * L1 * d), -1, 1)); a = th + b;
        const ex = Math.cos(a) * L1, ey = -Math.sin(a) * L1, k = d / Math.hypot(tx, ty); e = Math.atan2(-(ty * k - ey), tx * k - ex) - a;
      }
      const ex = side * Math.cos(a) * L1, ey = -Math.sin(a) * L1, hx = ex + side * Math.cos(a + e) * L2, hy = ey - Math.sin(a + e) * L2;
      ctx.save(); ctx.translate(ax, ay);
      ctx.beginPath(); ctx.moveTo(0, 0); ctx.lineTo(ex, ey); ctx.lineTo(hx, hy);
      ctx.strokeStyle = OL; ctx.lineWidth = .36 + LW * 2; ctx.stroke(); ctx.strokeStyle = '#7A7F8C'; ctx.lineWidth = .36; ctx.stroke();
      const hd = hand ?? 'open', dx = side * Math.cos(a + e), dy = -Math.sin(a + e);
      if (hd === 'point') { ctx.beginPath(); ctx.moveTo(hx, hy); ctx.lineTo(hx + dx * .7, hy + dy * .7); ctx.strokeStyle = OL; ctx.lineWidth = .28 + LW * 2; ctx.stroke(); ctx.strokeStyle = '#FFFFFF'; ctx.lineWidth = .28; ctx.stroke(); }
      if (hd === 'open' || hd === 'wave') for (let f = -1; f <= 1; f++) { const fa = Math.atan2(dy, dx) + f * .5; ell(hx + Math.cos(fa) * .42, hy + Math.sin(fa) * .42, .2, .2); paint('#FFFFFF', OL, LW * .8); }
      ell(hx, hy, .45, .42); paint('#FFFFFF', OL, LW);
      if (hold) { ctx.save(); ctx.translate(hx, hy); ctx.scale(1 / s, 1 / s); hold(s); ctx.restore(); }
      ctx.restore();
    };
    arm(-1, o.aL ?? -1.1, o.eL ?? .2, o.reachL, o.handL, o.holdL);
    arm(1, o.aR ?? -1.1, o.eR ?? .2, o.reachR, o.hand, o.hold);
  }
  ctx.restore();
}
// miniBot(x, y, s, o): a tiny walking terminal (for agent swarms). ≈ 3s tall. o.col (case), o.glow, o.face ('>_' text or an eyes style like computer()), o.walk, o.dy, o.rot, o.label.
function miniBot(x, y, s, o = {}) {
  ctx.save(); ctx.translate(x, y + (o.dy ?? 0) * s); if (o.rot) ctx.rotate(o.rot); ctx.scale(o.flip ? -s : s, s);
  const OL = NP.ink, cs = o.col ?? '#2A2E3A', glow = o.glow ?? NP.phosphor, w = o.walk ?? 0;
  for (const sd of [-1, 1]) { const lift = Math.max(0, Math.sin(w * TAU + (sd > 0 ? Math.PI : 0))) * .35; ctx.beginPath(); ctx.moveTo(sd * .45, -.8); ctx.lineTo(sd * .55, -lift); paint(null, OL, .22); }
  rrect(-1.25, -3.05, 2.5, 2.2, .3); paint(cs, OL, .1);
  rrect(-.95, -2.8, 1.9, 1.45, .25); paint('#0A140E');
  const f = o.face ?? '>_';
  if (f.length <= 3 && /[^a-z]/.test(f)) txt(f, 0, -2.07, .8, glow, { font: 'code' });
  else { ctx.fillStyle = glow; if (f === 'heart') { poly(heartPts(-.4, -2.15, .25, 12)); ctx.fill(); poly(heartPts(.4, -2.15, .25, 12)); ctx.fill(); } else if (f === 'spark') { poly(starPts(-.4, -2.1, .3, .4, 4, 0)); ctx.fill(); poly(starPts(.4, -2.1, .3, .4, 4, 0)); ctx.fill(); } else { ctx.fillRect(-.52, -2.35, .22, .4); ctx.fillRect(.3, -2.35, .22, .4); } }
  if (o.label) { rrect(-1.1, -1.25, 2.2, .45, .1); paint(o.labelCol ?? NP.gold); txt(o.label, 0, -1.02, .34, NP.ink, { font: 'archivo', maxW: 2 }); }
  ctx.restore();
}

// =====================================================================================================
// FIELD GEAR & PRESS PROPS
// =====================================================================================================
// bigMic(x, y, s, o): the huge 80s reporter microphone. (x, y) = centre of the foam ball; ≈ 2.4s ball, handle below.
// o.rot (tilt, radians; 0 = upright), o.flag (true: the "89" flag cube), o.col (foam colour).
function bigMic(x, y, s, o = {}) {
  ctx.save(); ctx.translate(x, y); ctx.rotate(o.rot ?? 0); ctx.scale(s, s);
  ctx.beginPath(); ctx.moveTo(0, 1.2); ctx.quadraticCurveTo(.6, 6.5, -1.5, 8.5); paint(null, '#111', .18);
  rrect(-.32, .6, .64, 4.4, .18); paint('#2A2A30', NP.ink, .08); ctx.fillStyle = 'rgb(255 255 255 / .25)'; ctx.fillRect(-.2, .8, .1, 4);
  if (o.flag !== false) {
    rrect(-1.05, 1.35, 2.1, 1.75, .12); paint(NP.red, NP.ink, .08); ctx.fillStyle = 'rgb(255 255 255 / .2)'; ctx.fillRect(-1, 1.4, 2, .5);
    txt('89', 0, 2.25, 1.2, NP.white, { font: 'anton', shadow: [.06, .08], shadowCol: 'rgb(0 0 0 / .5)' });
  }
  ell(0, 0, 1.2, 1.25); paint(o.col ?? '#34343C', NP.ink, .09);
  ctx.save(); ell(0, 0, 1.2, 1.25); ctx.clip(); ctx.fillStyle = 'rgb(255 255 255 / .08)';
  for (let i = 0; i < 40; i++) { ell((hash2(i, 7) - .5) * 2.2, (hash2(i, 8) - .5) * 2.3, .09); ctx.fill(); }
  ctx.fillStyle = 'rgb(255 255 255 / .16)'; ell(-.4, -.45, .5, .35, -.5); ctx.fill(); ctx.restore();
  ctx.restore();
}
// A hold fn for toon()/newsClawd(): the big mic, held upright. Pass { hold: micHold() }; o.rot tilts it toward a face.
const micHold = (rot = 0, k = 1) => s => bigMic(0, -2.1 * s * k, s * .9 * k, { rot });
// podium(x, y, s, o): a lectern with a mic cluster (every station's flag on it). (x, y) = floor centre; ≈ 6s wide, 7s tall.
// o.seal (text on the front medallion), o.col, o.mics (number of mic flags).
function podium(x, y, s, o = {}) {
  ctx.save(); ctx.translate(x, y); ctx.scale(s, s);
  const col = o.col ?? '#5A3A26';
  poly([[-2.6, 0], [2.6, 0], [2.2, -6.2], [-2.2, -6.2]]); paint(col, NP.ink, .08);
  ctx.fillStyle = 'rgb(0 0 0 / .18)'; poly([[1.2, 0], [2.6, 0], [2.2, -6.2], [1.0, -6.2]]); ctx.fill();
  rrect(-3.0, -7.0, 6.0, .9, .15); paint(shade(col, .15), NP.ink, .08);
  ell(0, -3.4, 1.35, 1.35); paint(NP.gold, NP.ink, .07); ell(0, -3.4, 1.1, 1.1); paint(o.sealCol ?? NP.navy);
  if (o.seal) txt(o.seal, 0, -3.35, .55, NP.gold, { font: 'archivo', maxW: 1.9 });
  const n = o.mics ?? 6, cols = [NP.red, NP.blue, '#F4F4F4', NP.gold, NP.green, '#222'];
  for (let i = 0; i < n; i++) {
    const a = (i - (n - 1) / 2) * .2, mx = Math.sin(a) * 3.6, my = -7.2 - Math.cos(a) * 1.15 + Math.abs(i - (n - 1) / 2) * .08;
    ctx.beginPath(); ctx.moveTo(Math.sin(a) * .6, -7); ctx.lineTo(mx, my); paint(null, '#1A1A1A', .16);
    ell(mx, my - .2, .32, .38); paint('#2A2A30', NP.ink, .05);
    rrect(mx - .42, my + .35, .84, .62, .06); paint(cols[i % cols.length], NP.ink, .05);
    txt(i % 3 === 0 ? '89' : ['4', '7', '2', '11', '5'][i % 5], mx, my + .67, .38, i % cols.length === 2 ? NP.ink : NP.white, { font: 'anton' });
  }
  ctx.restore();
}
// Press-camera flashbulbs popping (on beats + offbeats). n flashes scattered; t song time. Draw last (over the scene).
function flashbulbs(t, n = 5, o = {}) {
  const b = Math.floor(bpOf(t) * 2);
  for (let k = 0; k < 2; k++) {
    const bn = b - k, age = t - onBeat(0, bn / 2); if (age < 0 || age > .18) continue;
    for (let i = 0; i < n; i++) {
      if (hash2(bn, i) < .45) continue;
      const fx = (o.x0 ?? 0) + hash2(bn, i + 30) * ((o.x1 ?? W) - (o.x0 ?? 0)), fy = (o.y0 ?? 300) + hash2(bn, i + 60) * ((o.y1 ?? 900) - (o.y0 ?? 300)), a = 1 - age / .18;
      glint(fx, fy, 170 * a + 40, a);
    }
    if (age < .06 && o.wash !== false) { ctx.fillStyle = `rgb(255 255 255 / ${.22 * (1 - age / .06)})`; ctx.fillRect(0, 0, W, H); }
  }
}
// crtTV(x, y, w, h, draw, o): a CRT set (the prop, not the whole frame). (x, y, w, h) = screen rect; draw(w, h) paints the screen.
// o.style: 'wood' (living-room console) | 'grey' (studio monitor) | 'black'; o.knobs; o.on (0 = off/dark); o.glow.
function crtTV(x, y, w, h, draw, o = {}) {
  const st = o.style ?? 'grey', b = Math.min(w, h) * (st === 'wood' ? .16 : .09);
  const caseCol = st === 'wood' ? NP.wood : st === 'black' ? '#1C1C22' : '#8E93A0';
  ctx.save();
  ctx.fillStyle = 'rgb(0 0 0 / .35)'; rrect(x - b + 8, y - b + 10, w + b * 2 + (st === 'wood' ? b * 1.6 : 0), h + b * 2, b * .5); ctx.fill();
  rrect(x - b, y - b, w + b * 2 + (st === 'wood' ? b * 1.6 : 0), h + b * 2, b * .5); paint(st === 'wood' ? lg(0, y - b, 0, y + h + b, [[0, NP.woodLt], [1, NP.wood]]) : lg(0, y - b, 0, y + h + b, [[0, tint(caseCol, .25)], [1, shade(caseCol, .2)]]), NP.ink, 3);
  if (st === 'wood') { const kx = x + w + b * 1.3; for (let i = 0; i < 2; i++) { ell(kx, y + h * (.25 + i * .3), b * .4); paint('#C9C2B0', NP.ink, 2); } ctx.fillStyle = '#2A2A2A'; for (let i = 0; i < 5; i++) ctx.fillRect(kx - b * .45, y + h * .75 + i * 8, b * .9, 4); }
  ctx.save(); rrect(x, y, w, h, Math.min(w, h) * .08); ctx.clip();
  ctx.fillStyle = '#0A0C10'; ctx.fillRect(x, y, w, h);
  if (o.on !== 0 && draw) { ctx.save(); ctx.translate(x, y); draw(w, h); ctx.restore(); }
  ctx.fillStyle = 'rgb(0 0 0 / .18)'; for (let yy = y; yy < y + h; yy += 4) ctx.fillRect(x, yy, w, 1.6);
  ctx.fillStyle = rg(x + w / 2, y + h / 2, Math.min(w, h) * .3, Math.max(w, h) * .75, [[0, 'rgb(0 0 0 / 0)'], [1, 'rgb(0 0 0 / .55)']]); ctx.fillRect(x, y, w, h);
  ctx.fillStyle = 'rgb(255 255 255 / .08)'; ell(x + w * .3, y + h * .22, w * .35, h * .14, -.25); ctx.fill();
  ctx.restore();
  rrect(x, y, w, h, Math.min(w, h) * .08); paint(null, '#000', 3);
  ctx.restore();
}

// =====================================================================================================
// THE STUDIO — set coordinates are screen coordinates of the canonical two-shot (camera 'two').
// Anchors: Clawd at x 600 (desk left), Val Loss at x 1320 (desk right). Desk top y ≈ 700.
// =====================================================================================================
const SET = { deskTop: 700, clawdX: 600, valX: 1320, clawdY: 782, clawdU: 36, valY: 905, valS: 38 };
function _newsroom(t) {
  // left panel: a window into the working newsroom (staff walk back and forth; terminals glow)
  ctx.save(); rrect(40, 96, 620, 520, 10); ctx.clip();
  vFill('#1B2B66', '#0A1236', 40, 96, 620, 520);
  ctx.fillStyle = 'rgb(255 255 255 / .06)'; for (let i = 0; i < 6; i++) ctx.fillRect(40, 130 + i * 26, 620, 8);
  for (let i = 0; i < 4; i++) { ctx.fillStyle = 'rgb(255 250 220 / .25)'; ctx.fillRect(70 + i * 150, 104, 90, 10); }
  // staff walking (silhouettes)
  for (let i = 0; i < 4; i++) {
    const sp = 60 + hash(i + 3) * 70, ph = hash(i + 9) * 900, px = 20 + ((t * sp * (i % 2 ? 1 : -1) + ph) % 700 + 700) % 700;
    toon(px, 575, 13 + i % 2 * 2, { sil: '#233876', legs: true, walk: t * 1.6 + i, shadow: false, hair: ['short', 'bob', 'curly', 'side'][i], flip: i % 2 === 0 });
  }
  // desks with terminals
  for (let i = 0; i < 4; i++) {
    const dx = 70 + i * 150;
    rrect(dx, 520, 120, 70, 4); paint('#2C3552');
    rrect(dx + 20, 468, 70, 54, 5); paint('#C9C2AE', NP.ink, 2);
    ctx.fillStyle = hash2(i, Math.floor(t * 3)) > .3 ? '#1B5E30' : '#237A3E'; ctx.fillRect(dx + 28, 475, 54, 36);
    ctx.fillStyle = 'rgb(140 255 170 / .7)'; for (let r = 0; r < 4; r++) ctx.fillRect(dx + 32, 480 + r * 8, 14 + hash2(i, r + Math.floor(t * 2)) * 32, 3);
  }
  ctx.fillStyle = 'rgb(140 190 255 / .08)'; poly([[40, 96], [300, 96], [120, 616], [40, 616]]); ctx.fill();
  ctx.restore();
  rrect(40, 96, 620, 520, 10); paint(null, '#8FA6E0', 5);
}
function _mapWall(t) {
  const x = 1260, y = 96, w = 620, h = 520;
  ctx.save(); rrect(x, y, w, h, 10); ctx.clip();
  vFill('#0E2A7A', '#07153E', x, y, w, h);
  worldMap(x + 20, y + 30, w - 40, 330, { land: '#2E6FD8', edge: '#7FB2FF', grid: 'rgb(120 170 255 / .18)' });
  const cities = [['S.F.', -8], ['D.C.', -5], ['LONDON', 0], ['BEIJING', 8]];
  cities.forEach(([nm, off], i) => {
    const cx = x + 90 + i * 147, cy = y + h - 110;
    ell(cx, cy, 44); paint('#F2F2EE', NP.ink, 3);
    const hr = ((t / 3600 + 18 + off) % 12) / 12 * TAU, mn = ((t / 60 + 42) % 60) / 60 * TAU, sc = (Math.floor(t) % 60) / 60 * TAU;
    ctx.lineCap = 'round';
    for (const [a, L, lw, c] of [[hr, 22, 5, NP.ink], [mn, 32, 3.5, NP.ink], [sc, 36, 1.5, NP.red]]) { ctx.beginPath(); ctx.moveTo(cx, cy); ctx.lineTo(cx + Math.sin(a) * L, cy - Math.cos(a) * L); ctx.strokeStyle = c; ctx.lineWidth = lw; ctx.stroke(); }
    txt(nm, cx, cy + 62, 22, NP.white, { font: 'archivo', spacing: 1 });
  });
  ctx.restore();
  rrect(x, y, w, h, 10); paint(null, '#8FA6E0', 5);
}
// studio(t, o): the set's back wall (draw first, then anchors, then newsDesk()). o.wall: fn(w, h) to put a picture on the centre
// logo panel instead of the logo (e.g. a big graphic behind the anchors); o.dim (0..1 lights down).
function studio(t, o = {}) {
  vFill('#0C1850', '#040820');
  // lighting truss
  ctx.fillStyle = '#0A0D1C'; ctx.fillRect(-600, -40, W + 1200, 70);
  for (let i = -3; i < 16; i++) { const lx = i * 150 + 40; ctx.fillStyle = rg(lx, 30, 2, 120, [[0, 'rgb(255 240 200 / .55)'], [1, 'rgb(255 240 200 / 0)']]); ctx.fillRect(lx - 120, 0, 240, 150); ell(lx, 26, 16); paint('#FFF6DA', '#222', 3); }
  _newsroom(t); _mapWall(t);
  // centre logo panel
  const px = 700, py = 80, pw = 520, ph = 540;
  ctx.fillStyle = 'rgb(0 0 0 / .4)'; rrect(px + 10, py + 12, pw, ph, 14); ctx.fill();
  ctx.save(); rrect(px, py, pw, ph, 14); ctx.clip();
  if (o.wall) { ctx.save(); ctx.translate(px, py); o.wall(pw, ph); ctx.restore(); }
  else {
    ctx.fillStyle = rg(px + pw / 2, py + 220, 20, 420, [[0, '#3E7CFF'], [.6, '#1330A0'], [1, '#081A60']]); ctx.fillRect(px, py, pw, ph);
    ctx.save(); ctx.translate(px + pw / 2, py + 220); ctx.rotate(t * .15); ctx.fillStyle = 'rgb(255 255 255 / .07)';
    for (let i = 0; i < 12; i++) { ctx.rotate(TAU / 12); poly([[0, 0], [700, -60], [700, 60]]); ctx.fill(); } ctx.restore();
    ctx.fillStyle = 'rgb(255 255 255 / .06)'; for (let yy = py; yy < py + ph; yy += 14) ctx.fillRect(px, yy, pw, 6);
    logo89(px + pw / 2, py + 210, 150, { words: true, wordScale: .8 });
    sweepGlint(px + 90, px + pw - 90, py + 395, frac(t * .35) * 1.6, 70);
  }
  ctx.restore();
  rrect(px, py, pw, ph, 14); paint(null, '#C9D8FF', 6);
  // riser behind the desk with a neon stripe
  vFill('#141C44', '#0A0F28', -600, 610, W + 1200, 200);
  ctx.fillStyle = alpha(NP.cyan, .85); ctx.fillRect(-600, 622, W + 1200, 4); ctx.fillStyle = alpha(NP.cyan, .18); ctx.fillRect(-600, 612, W + 1200, 24);
  if (o.dim) { ctx.fillStyle = `rgb(0 0 10 / ${o.dim * .75})`; ctx.fillRect(-600, -600, W + 1200, H + 1200); }
}
// newsDesk(o): the anchor desk (draw after the anchors). o.top (y), o.mugs (count of coffee mugs, V4 panic), o.x0/o.x1.
function newsDesk(o = {}) {
  const top = o.top ?? SET.deskTop, x0 = o.x0 ?? 120, x1 = o.x1 ?? 1800;
  // top surface
  ctx.beginPath(); ctx.moveTo(x0, top + 30); ctx.quadraticCurveTo(960, top - 38, x1, top + 30); ctx.lineTo(x1 + 30, top + 62); ctx.quadraticCurveTo(960, top - 6, x0 - 30, top + 62); ctx.closePath();
  paint(lg(0, top - 20, 0, top + 62, [[0, '#DDE6F5'], [1, '#8C9BBB']]), NP.ink, 3);
  // front panel
  ctx.beginPath(); ctx.moveTo(x0 - 30, top + 62); ctx.quadraticCurveTo(960, top - 6, x1 + 30, top + 62); ctx.lineTo(x1 + 60, H + 400); ctx.lineTo(x0 - 60, H + 400); ctx.closePath();
  paint(lg(0, top, 0, H, [[0, '#3B57A8'], [.35, '#243A80'], [1, '#101A45']]), NP.ink, 3);
  ctx.save(); ctx.clip();
  ctx.strokeStyle = 'rgb(220 235 255 / .8)'; ctx.lineWidth = 5; ctx.beginPath(); ctx.moveTo(x0 - 40, top + 100); ctx.quadraticCurveTo(960, top + 32, x1 + 40, top + 100); ctx.stroke();
  ctx.strokeStyle = alpha(NP.gold, .9); ctx.lineWidth = 3; ctx.beginPath(); ctx.moveTo(x0 - 40, top + 116); ctx.quadraticCurveTo(960, top + 48, x1 + 40, top + 116); ctx.stroke();
  ctx.fillStyle = 'rgb(0 0 0 / .25)'; for (const sx of [480, 1440]) ctx.fillRect(sx, top, 6, 600);
  ctx.fillStyle = 'rgb(255 255 255 / .06)'; ctx.fillRect(x0, top + 140, x1 - x0, 60);
  logo89(960, top + 205, 78);
  ctx.restore();
  // props on the top
  const mugs = o.mugs ?? 1;
  for (let i = 0; i < mugs; i++) { const mx = 1010 + i * 58 - (i % 2) * 20, my = top + 18 - (i % 3) * 6; rrect(mx - 20, my - 44, 40, 46, 6); paint('#F4F2EC', NP.ink, 3); ctx.beginPath(); ctx.arc(mx + 22, my - 22, 12, -1.2, 1.2); paint(null, NP.ink, 5); txt('89', mx, my - 22, 20, NP.red, { font: 'anton' }); }
}
// papers(x, y, s, t, o): the anchor's script on the desk surface. (x, y) = bottom-centre where the stack sits.
// o.up: 0 = lying flat, 1 = held upright and tapped square on the beat (the classic shuffle); o.tap (tap height 0..1). Returns the lift (px).
function papers(x, y, s, t, o = {}) {
  const up = clamp(o.up ?? 0), tap = (o.tap ?? 1) * up, lift = -16 * s * tap * Math.sin(frac(bpOf(t)) * Math.PI) ** .6;
  const nudge = (1 - up) * Math.sin(bpOf(t) * Math.PI) * 3 * s;
  const hgt = lerp(26, 128, up) * s, wb = 150 * s, wt = lerp(128, 150, up) * s;
  ctx.save(); ctx.translate(x + nudge, y + lift);
  for (let i = 2; i >= 0; i--) {
    const dx = i * 4 * s, dy = -i * lerp(2, 3, up) * s;
    poly([[-wb / 2 + dx, dy], [wb / 2 + dx, dy], [wt / 2 + dx, dy - hgt], [-wt / 2 + dx, dy - hgt]]); paint(i ? '#E4E2DA' : '#FBFAF4', NP.ink, 2.5);
  }
  ctx.fillStyle = 'rgb(20 20 30 / .45)';
  for (let r = 0; r < 6; r++) { const v = (r + 1) / 7, yy = -hgt * v, ww = lerp(wb, wt, v) * .72; ctx.fillRect(-ww / 2, yy - 2 * s, ww * (r % 3 === 2 ? .55 : 1), lerp(2, 5, up) * s); }
  ctx.restore();
  return lift;
}
// deskEdge(x): y of the desk top's back edge at x (anchors' forearms disappear behind it; hands sit just in front).
const deskEdge = x => { const u = clamp((x - 120) / 1680); return (1 - u) ** 2 * (SET.deskTop + 30) + 2 * u * (1 - u) * (SET.deskTop - 38) + u * u * (SET.deskTop + 30); };
// deskHands(x, y, kind, cuff): a pair of hands resting on the desk at (x ± spread, y); kind 'clawd' (orange nubs) | skin colour.
function deskHand(x, y, kind, cuff) {
  const top = deskEdge(x) - 6;
  ctx.beginPath(); ctx.moveTo(x, top); ctx.lineTo(x, y); ctx.strokeStyle = NP.ink; ctx.lineWidth = (kind === 'clawd' ? 44 : 26) + 6; ctx.lineCap = 'round'; ctx.stroke(); ctx.strokeStyle = cuff; ctx.lineWidth = kind === 'clawd' ? 44 : 26; ctx.stroke();
  if (kind === 'clawd') { rrect(x - 23, y - 14, 46, 36, 12); paint(NP.clawd, NP.ink, 5); }
  else { ell(x, y + 4, 15, 13); paint(kind, NP.ink, 3.5); }
}
// anchorShot(t, o): the whole desk shot, camera included. Paint it, then add your chyron.
//   o.who: 'clawd' (Clawd single, OTS box upper right) | 'val' (Val single, OTS upper left) | 'two' (two-shot) | 'wide' (establishing)
//   o.ots: { draw(w, h), label, k, labelCol } — the over-the-shoulder box for singles; o.clawd / o.val: pose overrides (newsClawd/toon options);
//   o.cam: { x, y, zoom, rot } to override the camera; o.push (0..1 slow push-in); o.shuffle (0..1 papers upright + tapping on the beat;
//   default 0 = papers flat); o.hands (false = the anchors' hands are free: pass your own reachL/reachR/aL/aR in o.clawd / o.val);
//   o.talk ('auto' = the on-camera anchor lip-syncs whenever a line is sung; or a number); o.wall (centre-panel picture fn(w, h)); o.mugs.
function anchorShot(t, o = {}) {
  const who = o.who ?? 'clawd', ln = lineAt(t), singing = ln && t < ln.end;
  const tk = o.talk === undefined || o.talk === 'auto' ? (singing ? talk(t) : 0) : o.talk;
  const cams = { clawd: [SET.clawdX + 330, 470, 1.5], val: [SET.valX - 330, 470, 1.5], two: [960, 540, 1], wide: [960, 700, .66] };
  const [cx, cy, cz] = o.cam ? [o.cam.x, o.cam.y, o.cam.zoom] : cams[who];
  camBegin(cx, cy, cz * (1 + (o.push ?? 0) * .08), o.cam?.rot ?? 0);
  if (who === 'wide') vFill('#10131C', '#05060A', -1200, 800, W + 2400, 1400);
  studio(t, { wall: o.wall, dim: o.dim });
  const b = bpOf(t), bob = Math.sin(b * Math.PI) * .05, up = o.shuffle ?? 0, hands = o.hands !== false;
  const blink = ph => (frac(t * .37 + ph) < .045 ? 1 : 0);
  const showC = who !== 'val', showV = who !== 'clawd';
  const hy = SET.deskTop + 14, spread = lerp(58, 82, up);
  const pl = -16 * (o.tap ?? 1) * up * Math.sin(frac(b) * Math.PI) ** .6;
  const cU = SET.clawdU, cX = SET.clawdX, cY = SET.clawdY, vS = SET.valS, vX = SET.valX, vY = SET.valY;
  if (showC) newsClawd(cX, cY, cU, { legs: false, shadow: false, talk: who === 'val' ? 0 : tk, lookX: who === 'two' ? .25 : 0, dy: bob, blink: blink(.1),
    ...(hands ? { reachL: [-spread / cU, (deskEdge(cX) + 4 - cY) / cU], reachR: [spread / cU, (deskEdge(cX) + 4 - cY) / cU] } : {}), ...(o.clawd || {}) });
  if (showV) toon(vX, vY, vS, { ...CAST.val.o, legs: false, shadow: false, talk: who === 'clawd' ? undefined : (who === 'two' ? undefined : tk), mouth: 'smile', lookX: who === 'two' ? -.6 : 0, blink: blink(.6), dy: -bob * .5,
    ...(hands ? { reachL: [-spread / vS, (deskEdge(vX) + 4 - vY) / vS], reachR: [spread / vS, (deskEdge(vX) + 4 - vY) / vS] } : {}), ...(o.val || {}) });
  newsDesk({ mugs: o.mugs });
  if (showC) { papers(cX, hy + 12, .95, t, { up }); if (hands) for (const sd of [-1, 1]) deskHand(cX + sd * spread, hy - 6 + pl - up * 50, 'clawd', '#1C2A5E'); }
  if (showV) { papers(vX, hy + 12, .95, t, { up }); if (hands) for (const sd of [-1, 1]) deskHand(vX + sd * spread, hy - 4 + pl - up * 50, NSKIN[4], CAST.val.o.topCol); }
  if (who === 'wide') _studioFloor(t);
  camEnd();
  if (o.ots && (who === 'clawd' || who === 'val')) {
    const ox = who === 'clawd' ? 1010 : 210, k = o.ots.k ?? 1;
    otsBox(ox, 175, 700, 470, o.ots.draw, { k, label: o.ots.label, labelCol: o.ots.labelCol, tilt: who === 'clawd' ? -1 : 1 });
  }
}
// The studio floor and pedestal cameras for the wide establishing shot (drawn in set coordinates, below the desk).
function _studioFloor(t) {
  vFill('#3A3F4E', '#12141C', -1200, 1000, W + 2400, 900);
  for (const lx of [300, 960, 1620]) { ctx.fillStyle = rg(lx, 1150, 10, 420, [[0, 'rgb(255 245 220 / .22)'], [1, 'rgb(255 245 220 / 0)']]); ctx.fillRect(lx - 500, 1000, 1000, 400); }
  ctx.strokeStyle = 'rgb(255 255 255 / .07)'; ctx.lineWidth = 3; for (let i = -20; i < 20; i++) { ctx.beginPath(); ctx.moveTo(960 + i * 60, 1000); ctx.lineTo(960 + i * 260, 1900); ctx.stroke(); }
  ctx.strokeStyle = '#08090C'; ctx.lineWidth = 12; ctx.beginPath(); ctx.moveTo(-300, 1500); ctx.bezierCurveTo(300, 1380, 700, 1640, 1100, 1480); ctx.bezierCurveTo(1400, 1380, 1800, 1560, 2300, 1420); ctx.stroke();
  for (const [x, fl] of [[120, 1], [1800, -1]]) {
    ctx.save(); ctx.translate(x, 1640); ctx.scale(fl * 1.25, 1.25);
    toon(fl > 0 ? 250 : 250, 60, 34, { sil: '#07080C', legs: true, shadow: false, hat: 'headset', hair: 'short', aL: .3, eL: .6, aR: .2, eR: .9 });
    ctx.fillStyle = '#0A0B10'; poly([[-60, 0], [60, 0], [30, -260], [-30, -260]]); ctx.fill();
    rrect(-150, -430, 300, 170, 14); paint('#1E212B', '#000', 4); rrect(120, -400, 100, 120, 10); paint('#14161C', '#000', 3);
    ctx.fillStyle = '#2E3240'; ctx.fillRect(-130, -410, 110, 60);
    ell(-230, -345, 84, 84); paint('#181A20', '#000', 4); ell(-230, -345, 54, 54); paint(rg(-245, -360, 4, 54, [[0, '#7B9CFF'], [1, '#0A0C20']]));
    ell(100, -420, 11); paint(frac(t * 1.5) < .5 ? '#FF2020' : '#500');
    ctx.save(); ctx.scale(fl, 1); txt('89', fl * 30, -300, 44, NP.white, { font: 'anton' }); ctx.restore();
    ctx.restore();
  }
}

// =====================================================================================================
// WEATHER CENTER — worldMap, wxIcon, forecastStrip, front, hurricane (for "Dark for nineteen days", Navier–Stokes…)
// =====================================================================================================
// worldMap(x, y, w, h, o): equirectangular world in the rect (lon −180..180, lat 84..−60). o.land, o.edge, o.sea (fill the rect first), o.grid.
function worldMap(x, y, w, h, o = {}) {
  const P = ([lo, la]) => [x + (lo + 180) / 360 * w, y + (84 - la) / 144 * h];
  if (o.sea) { ctx.fillStyle = o.sea; ctx.fillRect(x, y, w, h); }
  if (o.grid !== null) { ctx.strokeStyle = o.grid ?? 'rgb(255 255 255 / .15)'; ctx.lineWidth = 1.5; ctx.beginPath(); for (let lo = -150; lo <= 150; lo += 30) { const [gx] = P([lo, 0]); ctx.moveTo(gx, y); ctx.lineTo(gx, y + h); } for (let la = -45; la <= 75; la += 30) { const [, gy] = P([0, la]); ctx.moveTo(x, gy); ctx.lineTo(x + w, gy); } ctx.stroke(); }
  for (const c of WORLD) { poly(c.map(P)); paint(o.land ?? '#3E9A55', o.edge ?? '#CFE8C0', o.lw ?? 2.5); }
  return P;
}
// wxIcon(type, x, y, s, t): 'sun' | 'cloud' | 'rain' | 'storm' | 'snow' | 'moon' | 'dark' (a black cloud) | 'fog'. s ≈ radius.
function wxIcon(type, x, y, s, t = T) {
  ctx.save(); ctx.translate(x, y);
  const cloud = (c, dx = 0, dy = 0, k = 1) => { ctx.beginPath(); for (const [cx, cy, r] of [[-.45, .15, .42], [0, -.15, .55], [.48, .1, .42], [.1, .28, .45]]) ctx.ellipse((cx + dx) * s * k, (cy + dy) * s * k, r * s * k, r * s * k, 0, 0, TAU); ctx.fillStyle = c; ctx.fill(); ctx.lineWidth = s * .06; ctx.strokeStyle = NP.ink; ctx.stroke(); ctx.fill(); };
  if (type === 'sun') {
    ctx.rotate(t * .8); ctx.fillStyle = NP.amber; for (let i = 0; i < 10; i++) { ctx.rotate(TAU / 10); poly([[s * .55, -s * .13], [s * 1.05, 0], [s * .55, s * .13]]); ctx.fill(); }
    ell(0, 0, s * .6); paint(lg(0, -s * .6, 0, s * .6, [[0, '#FFF27A'], [1, '#FFB21E']]), NP.ink, s * .05);
  } else if (type === 'moon') { ctx.beginPath(); ctx.arc(0, 0, s * .6, .5, TAU - .5 + Math.PI, false); ctx.arc(s * .3, -s * .1, s * .5, TAU - .6 + Math.PI, .6, true); ctx.closePath(); paint('#F3EBC0', NP.ink, s * .05); }
  else if (type === 'fog') { for (let i = 0; i < 3; i++) { rrect(-s * .8 + i * s * .1, -s * .3 + i * s * .3, s * 1.5, s * .16, s * .08); paint('#C9D2DD'); } }
  else {
    if (type === 'rain' || type === 'storm' || type === 'snow') {
      for (let i = 0; i < 4; i++) { const ph = frac(t * 2.2 + i * .27), dx = (-.45 + i * .3) * s, dy = (.35 + ph * .7) * s; if (type === 'snow') { ell(dx, dy, s * .08); paint('#FFF'); } else { ctx.beginPath(); ctx.moveTo(dx, dy); ctx.lineTo(dx - s * .06, dy + s * .18); paint(null, '#5AB0FF', s * .07); } }
      if (type === 'storm') { poly([[.05 * s, .2 * s], [-.2 * s, .65 * s], [0, .62 * s], [-.12 * s, 1.0 * s], [.25 * s, .5 * s], [.05 * s, .52 * s], [.18 * s, .2 * s]]); paint(NP.gold, NP.ink, s * .03); }
    }
    cloud(type === 'dark' ? '#1C1C26' : type === 'storm' ? '#6B7384' : '#F2F4F8');
    if (type === 'dark') { ctx.fillStyle = 'rgb(255 255 255 / .12)'; ell(-.1 * s, -.3 * s, .3 * s, .1 * s); ctx.fill(); }
  }
  ctx.restore();
}
// forecastStrip(days, x, y, w, o): a row of forecast tiles. days: [{ day: 'MON', icon: 'sun', hi: 88, lo: 70 }], o.k (tiles flip in left→right), o.h.
function forecastStrip(days, x, y, w, o = {}) {
  const n = days.length, gap = o.gap ?? 10, tw = (w - gap * (n - 1)) / n, th = o.h ?? tw * 1.4, k = o.k ?? 1;
  days.forEach((d, i) => {
    const kk = clamp(k * n * 1.2 - i * 1.2 * (n > 1 ? 1 : 0)); if (kk <= 0) return;
    const tx = x + i * (tw + gap);
    ctx.save(); ctx.translate(tx + tw / 2, y + th / 2); ctx.scale(easeOut(kk), 1);
    rrect(-tw / 2, -th / 2, tw, th, 8); paint(lg(0, -th / 2, 0, th / 2, [[0, d.col ?? '#2B5FD9'], [1, shade(d.col ?? '#2B5FD9', .45)]]), NP.ink, 3);
    ctx.fillStyle = 'rgb(255 255 255 / .15)'; ctx.fillRect(-tw / 2 + 4, -th / 2 + 4, tw - 8, th * .18);
    txt(d.day, 0, -th / 2 + th * .13, Math.min(34, tw * .3), NP.white, { font: 'archivo', maxW: tw - 10 });
    wxIcon(d.icon, 0, -th * .02, Math.min(tw * .34, th * .22));
    if (d.hi !== undefined) txt(String(d.hi), 0, th * .32, Math.min(46, tw * .38), d.hiCol ?? NP.gold, { font: 'anton', maxW: tw - 10 });
    if (d.note) txt(d.note, 0, th * .32, Math.min(30, tw * .26), NP.white, { font: 'archivo', maxW: tw - 10 });
    ctx.restore();
  });
}
// front(pts, type, o): weather front along a polyline. type 'cold' (blue triangles) | 'warm' (red half-discs). o.k (draw-on 0..1).
function front(pts, type = 'cold', o = {}) {
  const P = partial(pts, o.k ?? 1), col = type === 'cold' ? '#2F7BFF' : NP.red;
  ctx.beginPath(); P.forEach(([px, py], i) => i ? ctx.lineTo(px, py) : ctx.moveTo(px, py)); paint(null, col, 7);
  let acc = 0; const step = o.step ?? 60;
  for (let i = 1; i < P.length; i++) {
    const [ax, ay] = P[i - 1], [bx, by] = P[i], L = Math.hypot(bx - ax, by - ay), a = Math.atan2(by - ay, bx - ax);
    for (let d = step / 2 - acc; d < L; d += step) {
      const px = ax + Math.cos(a) * d, py = ay + Math.sin(a) * d;
      ctx.save(); ctx.translate(px, py); ctx.rotate(a); ctx.fillStyle = col;
      if (type === 'cold') poly([[-14, 0], [14, 0], [0, -22]]); else { ctx.beginPath(); ctx.arc(0, 0, 14, Math.PI, TAU); ctx.closePath(); }
      ctx.fill(); ctx.restore();
    }
    acc = (acc + L) % step;
  }
}
// hurricane(x, y, r, t, o): the spinning storm glyph + radar rings. o.col, o.k (intensity 0..1), o.blowup (0..1: spins up and explodes).
function hurricane(x, y, r, t, o = {}) {
  const bu = o.blowup ?? 0, spin = t * (3 + bu * 30), rr = r * (1 + bu * 1.8);
  ctx.save(); ctx.translate(x, y);
  for (let i = 3; i >= 1; i--) { ctx.fillStyle = [null, 'rgb(255 60 60 / .55)', 'rgb(255 200 40 / .45)', 'rgb(60 220 90 / .35)'][i]; ell(0, 0, rr * (.5 + i * .35), rr * (.5 + i * .35)); ctx.fill(); }
  ctx.rotate(spin);
  for (const sd of [0, Math.PI]) { ctx.save(); ctx.rotate(sd); ctx.beginPath(); ctx.moveTo(0, 0); ctx.quadraticCurveTo(rr * .9, -rr * .1, rr * .7, -rr * .9); ctx.quadraticCurveTo(rr * .5, -rr * .2, 0, 0); paint(o.col ?? '#FFFFFF', NP.ink, 4); ctx.restore(); }
  ell(0, 0, rr * .28); paint(o.col ?? '#FFFFFF', NP.ink, 4); ell(0, 0, rr * .1); paint(NP.ink);
  ctx.restore();
}

// weatherSet(t, o): the whole weather-wall shot. The map fills the frame; SUNNY DESCENT stands chroma-keyed at the left with a pointer.
// o.draw(P, t) adds your symbols (P([lon, lat]) → [x, y] on the map); o.point ([x, y] the pointer hand aims at); o.head (tab text,
// default '89 WEATHER'); o.presenter (false to hide him); o.dark (0..1 dims the land — for outages); o.talk.
function weatherSet(t, o = {}) {
  vFill('#0A2A7A', '#04113A');
  const P = worldMap(150, 180, 1700, 700, { sea: '#0B3A9A', land: mixCol('#3E9A55', '#1A2230', o.dark ?? 0), edge: mixCol('#CFE8C0', '#5A6A7A', o.dark ?? 0), grid: 'rgb(255 255 255 / .12)' });
  if (o.draw) o.draw(P, t);
  rrect(90, 70, 560, 90, 10); paint(lg(0, 70, 0, 160, [[0, '#2FC8E0'], [1, '#0A6A8A']]), '#FFF', 4);
  logo89(150, 115, 38); chrome(o.head ?? '89 WEATHER', 200, 120, 54, { font: 'archivo', style: 'white', depth: 4, align: 'left', italic: .1, spacing: 2 });
  if (o.presenter !== false) {
    const X = 330, Y = 1210, S = 64, pt = o.point ?? [760, 420];
    const r = [(pt[0] - X) / S, (pt[1] - Y) / S];
    // chroma-key fringe: a faint cyan halo around the presenter
    ctx.save(); ctx.globalAlpha = .5; toon(X + 4, Y + 2, S * 1.01, { ...CAST.sunny.o, sil: '#6FF0FF', legs: false, shadow: false, reachR: r, hand: 'point' }); ctx.restore();
    toon(X, Y, S, { ...CAST.sunny.o, legs: false, shadow: false, reachR: r, hand: 'point', talk: o.talk ?? talk(t), lookX: .4 });
  }
  return P;
}
// bumper(t, k, o): the SPECIAL REPORT bumper (laser grid, spinning globe, chrome title slam, swooshes). k = 0..1 progress through it
// (≈ 1.5–2.5 s reads well). o.title (default 'SPECIAL REPORT'), o.sub (line under it), o.style ('red'|'chrome'|'gold'), o.col (grid colour).
function bumper(t, k, o = {}) {
  laserGrid(t, { horizon: 700, col: o.col ?? NP.magenta, speed: 2.4 });
  globe(W / 2, 430, lerp(120, 330, easeOut(clamp(k * 2))), t * 1.4, { col: NP.cyan });
  swoosh(clamp(k * 3), 640, NP.red, { len: 1700, th: 70 }); swoosh(clamp(k * 3 - .5), 700, NP.gold, { len: 1500, th: 36 });
  const tk = clamp((k - .12) / .18), s = tk < 1 ? lerp(2.6, 1, easeOut(tk)) : 1 + pulse(t, 6) * .02;
  if (tk > 0) chrome(o.title ?? 'SPECIAL REPORT', W / 2, 560, 150, { font: 'archivo', style: o.style ?? 'red', italic: .14, depth: 16, spacing: 4, s, alpha: clamp(tk * 3) });
  if (o.sub && k > .35) { const sk = clamp((k - .35) / .15); rrect(W / 2 - 560, 690, 1120, 84, 8); paint(`rgb(0 0 30 / ${.7 * sk})`, alpha(NP.cyan, sk), 3); txt(o.sub, W / 2, 733, 52, NP.white, { font: 'archivo', spacing: 5, alpha: sk, maxW: 1060 }); }
  sweepGlint(W / 2 - 620, W / 2 + 620, 520, (k - .3) / .4, 160);
}
// testCard(o): the station's sign-off test card (roundel, gratings, grey steps, "CHANNEL 89"). o.caption (bottom text), o.t (slow drift).
function testCard(o = {}) {
  fillAll('#8A8A8A');
  ctx.fillStyle = '#6E6E6E'; for (let x = 0; x < W; x += 120) for (let y = 0; y < H; y += 120) if (((x + y) / 120) % 2 === 0) ctx.fillRect(x, y, 120, 120);
  ell(W / 2, H / 2, 470, 470); paint('#D8D8D8', '#111', 8);
  ctx.save(); ell(W / 2, H / 2, 470, 470); ctx.clip();
  ['#B8B8B8', '#C0C000', '#00C0C0', '#00C000', '#C000C0', '#C00000', '#0000C0'].forEach((c, i) => { ctx.fillStyle = c; ctx.fillRect(W / 2 - 470 + i * 134, H / 2 - 330, 136, 170); });
  for (let i = 0; i < 6; i++) { const f = 6 + i * 4; for (let x = 0; x < 150; x += f) { ctx.fillStyle = (x / f) % 2 < 1 ? '#FFF' : '#000'; ctx.fillRect(W / 2 - 470 + i * 157 + x, H / 2 + 160, f / 2, 120); } }
  for (let i = 0; i < 8; i++) { ctx.fillStyle = mixCol('#000000', '#FFFFFF', i / 7); ctx.fillRect(W / 2 - 470 + i * 118, H / 2 + 290, 120, 120); }
  ctx.restore();
  ctx.strokeStyle = '#111'; ctx.lineWidth = 4; ctx.beginPath(); ctx.moveTo(W / 2 - 470, H / 2); ctx.lineTo(W / 2 + 470, H / 2); ctx.moveTo(W / 2, H / 2 - 470); ctx.lineTo(W / 2, H / 2 + 470); ctx.stroke();
  logo89(W / 2, H / 2 - 10, 150);
  const cw2 = pixelW(o.caption ?? 'CHANNEL 89', 6) + 60; rrect(W / 2 - cw2 / 2, H / 2 + 150, cw2, 70, 6); paint('#000'); pixelText(o.caption ?? 'CHANNEL 89', W / 2, H / 2 + 164, 6, NP.white, { align: 'center', edge: null });
}
// hugFace(x, y, r, o): the hugging-face emoji, clean. o.mood: 'happy' | 'scared' | 'x' | 'sad'; o.hands (0..1 raised); o.bandage (true).
function hugFace(x, y, r, o = {}) {
  ctx.save(); ctx.translate(x, y); if (o.rot) ctx.rotate(o.rot);
  ell(0, 0, r, r); paint(rg(-r * .3, -r * .35, r * .1, r * 1.05, [[0, '#FFE56A'], [.7, '#FFCC1E'], [1, '#E8A400']]), NP.ink, r * .05);
  const m = o.mood ?? 'happy'; ctx.lineCap = 'round';
  for (const sd of [-1, 1]) {
    const ex = sd * r * .35, ey = -r * .18;
    if (m === 'happy') { ctx.beginPath(); ctx.arc(ex, ey + r * .08, r * .14, Math.PI * 1.1, Math.PI * 1.9); paint(null, NP.ink, r * .07); }
    else if (m === 'x') { ctx.beginPath(); ctx.moveTo(ex - r * .1, ey - r * .1); ctx.lineTo(ex + r * .1, ey + r * .1); ctx.moveTo(ex + r * .1, ey - r * .1); ctx.lineTo(ex - r * .1, ey + r * .1); paint(null, NP.ink, r * .07); }
    else { ell(ex, ey, r * .15, r * .18); paint('#FFF', NP.ink, r * .03); ell(ex, ey + r * .03, r * .06, r * .07); paint(NP.ink); if (m === 'sad') { ctx.beginPath(); ctx.moveTo(ex - sd * r * .18, ey - r * .28); ctx.lineTo(ex + sd * r * .1, ey - r * .2); paint(null, NP.ink, r * .05); } }
  }
  if (m === 'happy') { ctx.beginPath(); ctx.moveTo(-r * .38, r * .12); ctx.quadraticCurveTo(0, r * .62, r * .38, r * .12); ctx.closePath(); paint('#6B2A1A', NP.ink, r * .03); }
  else if (m === 'sad') { ctx.beginPath(); ctx.arc(0, r * .5, r * .22, 1.2 * Math.PI, 1.8 * Math.PI); paint(null, NP.ink, r * .06); }
  else { ell(0, r * .3, r * .15, r * .19); paint('#6B2A1A', NP.ink, r * .03); }
  const hr = o.hands ?? 0;
  for (const sd of [-1, 1]) { ctx.save(); ctx.translate(sd * r * .62, r * (.55 - hr * .55)); ctx.rotate(sd * (.3 + hr * .6)); rrect(-r * .26, -r * .3, r * .52, r * .6, r * .2); paint('#FFC21A', NP.ink, r * .035); ctx.restore(); }
  if (o.bandage) { ctx.save(); ctx.rotate(-.5); rrect(-r * .5, -r * .72, r * 1.0, r * .26, r * .08); paint('#F2E2C8', NP.ink, r * .03); ctx.fillStyle = 'rgb(180 150 110 / .6)'; for (let i = 0; i < 5; i++) ell(-r * .3 + i * r * .15, -r * .59, r * .025); ctx.fill(); ctx.restore(); }
  ctx.restore();
}

// =====================================================================================================
// MONEY, SPORTS, POLLS — cgiChart, ticker, quoteBoard, scoreboard, pollBoard, tallyBoard
// =====================================================================================================
// cgiChart(x, y, w, h, o): early-CGI neon line chart on a glowing grid. o.fn(u) → 0..1 (default exponential), o.k (draw-on),
// o.col, o.grid, o.log (log-paper grid), o.fill (area under the line), o.label / o.xlabel / o.ylabel. Returns the tip [x, y].
function cgiChart(x, y, w, h, o = {}) {
  const fn = o.fn ?? (u => (Math.exp(u * 4) - 1) / (Math.exp(4) - 1)), k = clamp(o.k ?? 1), col = o.col ?? NP.lime;
  ctx.save();
  if (o.bg !== null) { rrect(x - 20, y - 20, w + 40, h + 40, 10); paint(o.bg ?? 'rgb(4 10 40 / .85)', 'rgb(120 170 255 / .6)', 3); }
  ctx.strokeStyle = o.grid ?? 'rgb(80 160 255 / .35)'; ctx.lineWidth = 2; ctx.beginPath();
  if (o.log) { for (let d = 0; d < 4; d++) for (let m = 1; m < 10; m++) { const u = (d + Math.log10(m)) / 4; ctx.moveTo(x + u * w, y); ctx.lineTo(x + u * w, y + h); ctx.moveTo(x, y + h - u * h); ctx.lineTo(x + w, y + h - u * h); } }
  else for (let i = 0; i <= 8; i++) { ctx.moveTo(x + i * w / 8, y); ctx.lineTo(x + i * w / 8, y + h); ctx.moveTo(x, y + i * h / 8); ctx.lineTo(x + w, y + i * h / 8); }
  ctx.stroke();
  ctx.strokeStyle = 'rgb(200 225 255 / .9)'; ctx.lineWidth = 4; ctx.beginPath(); ctx.moveTo(x, y); ctx.lineTo(x, y + h); ctx.lineTo(x + w, y + h); ctx.stroke();
  const pts = []; for (let i = 0; i <= 80; i++) { const u = i / 80; pts.push([x + u * w, y + h - clamp(fn(u), -.2, 1.3) * h]); }
  const P = partial(pts, k);
  if (o.fill && P.length > 1) { ctx.beginPath(); ctx.moveTo(P[0][0], y + h); P.forEach(([a, b]) => ctx.lineTo(a, b)); ctx.lineTo(P.at(-1)[0], y + h); ctx.closePath(); ctx.fillStyle = lg(0, y, 0, y + h, [[0, alpha(col, .45)], [1, alpha(col, .05)]]); ctx.fill(); }
  ctx.beginPath(); P.forEach(([a, b], i) => i ? ctx.lineTo(a, b) : ctx.moveTo(a, b));
  ctx.lineJoin = 'round'; ctx.lineCap = 'round'; ctx.strokeStyle = alpha(col, .25); ctx.lineWidth = 22; ctx.stroke(); ctx.strokeStyle = col; ctx.lineWidth = 8; ctx.stroke(); ctx.strokeStyle = 'rgb(255 255 255 / .8)'; ctx.lineWidth = 2.5; ctx.stroke();
  const tip = P.at(-1); if (k > 0 && k < 1) glint(tip[0], tip[1], 60, 1);
  if (o.label) txt(o.label, x + w / 2, y - 48, o.labelSize ?? 44, NP.white, { font: 'archivo', spacing: 2 });
  if (o.xlabel) txt(o.xlabel, x + w / 2, y + h + 44, 30, NP.ice, { font: 'archivo', spacing: 1 });
  if (o.ylabel) txt(o.ylabel, x - 46, y + h / 2, 30, NP.ice, { font: 'archivo', rot: -TAU / 4, spacing: 1 });
  ctx.restore();
  return tip;
}
// ticker(y, items, t, o): the stock-ticker crawl band. items: ['NVDA ▼17%', …] or [{ sym, val, dir }] (dir > 0 green ▲, < 0 red ▼).
// o.speed (px/s), o.h, o.bg, o.label (left tab text, default 'MARKETS').
function ticker(y, items, t, o = {}) {
  const h = o.h ?? 64, sp = o.speed ?? 320, size = h * .6;
  ctx.save();
  ctx.fillStyle = o.bg ?? '#050A1E'; ctx.fillRect(0, y, W, h); ctx.fillStyle = NP.gold; ctx.fillRect(0, y, W, 3); ctx.fillRect(0, y + h - 3, W, 3);
  const cells = items.map(it => typeof it === 'string' ? { s: it, c: /▼|−|-\d/.test(it) ? '#FF5050' : /▲|\+/.test(it) ? '#4CFF7A' : NP.white } : { s: `${it.sym} ${it.dir > 0 ? '▲' : it.dir < 0 ? '▼' : ''}${it.val}`, c: it.dir > 0 ? '#4CFF7A' : it.dir < 0 ? '#FF5050' : NP.white });
  const ws = cells.map(c => textW(c.s, size, 'archivo', 1) + 70), tot = ws.reduce((a, b) => a + b, 0);
  let x = -((t * sp) % tot);
  ctx.beginPath(); ctx.rect(0, y, W, h); ctx.clip();
  const aw = size * .62;
  const drawCell = (c, cx) => { let px = cx; for (const part of c.s.split(/([▲▼])/)) { if (!part) continue; if (part === '▲' || part === '▼') { const up = part === '▲'; poly(up ? [[px, y + h * .72], [px + size * .5, y + h * .72], [px + size * .25, y + h * .3]] : [[px, y + h * .3], [px + size * .5, y + h * .3], [px + size * .25, y + h * .72]]); ctx.fillStyle = c.c; ctx.fill(); px += aw; } else { txt(part, px, y + h / 2 + 2, size, c.c, { font: 'archivo', align: 'left', spacing: 1 }); px += textW(part, size, 'archivo', 1); } } };
  let guard = 0;
  while (x < W && guard++ < 50) { cells.forEach((c, i) => { if (x > -ws[i] && x < W) drawCell(c, x); x += ws[i]; }); }
  if (o.label !== null) { const lw = textW(o.label ?? 'MARKETS', size * .8, 'archivo', 1) + 50; ctx.fillStyle = NP.red; ctx.fillRect(0, y, lw, h); txt(o.label ?? 'MARKETS', lw / 2, y + h / 2 + 2, size * .8, NP.white, { font: 'archivo', spacing: 1 }); }
  ctx.restore();
}
// ticker items use ▲/▼ markers in strings: the glyph is drawn as a triangle (fonts lack it). Example: 'NVDA ▼17%'.
// quoteBoard(x, y, w, rows, o): big-board stock quotes. rows: [{ sym, price, chg }] (chg number: colour + arrow). o.rowH, o.flash (row index flashing).
function quoteBoard(x, y, w, rows, o = {}) {
  const rh = o.rowH ?? 86;
  rrect(x - 14, y - 14, w + 28, rows.length * rh + 28, 10); paint('#050812', '#3A4A7A', 4);
  rows.forEach((r, i) => {
    const ry = y + i * rh, fl = o.flash === i && frac(T * 4) < .5;
    ctx.fillStyle = fl ? 'rgb(255 255 255 / .12)' : i % 2 ? 'rgb(255 255 255 / .03)' : 'rgb(0 0 0 / 0)'; ctx.fillRect(x, ry, w, rh);
    const c = r.chg > 0 ? '#4CFF7A' : r.chg < 0 ? '#FF4A4A' : NP.white;
    pixelText(r.sym, x + 20, ry + rh / 2 - 17, 5, NP.crtAmber, { edge: null });
    pixelText(r.price, x + w * .62, ry + rh / 2 - 17, 5, NP.white, { align: 'right', edge: null });
    if (r.chg !== undefined) { const ax = x + w * .7, up = r.chg > 0; poly(up ? [[ax, ry + rh * .68], [ax + 30, ry + rh * .68], [ax + 15, ry + rh * .32]] : [[ax, ry + rh * .32], [ax + 30, ry + rh * .32], [ax + 15, ry + rh * .68]]); ctx.fillStyle = c; ctx.fill(); pixelText((r.chg > 0 ? '+' : '') + r.chg + (r.pct === false ? '' : '%'), x + w - 20, ry + rh / 2 - 17, 5, c, { align: 'right', edge: null }); }
  });
}
// scoreboard(x, y, w, h, o): stadium-style scoreboard with light-bulb digits. o.title, o.rows: [{ name, score, col }], o.foot (bottom line), o.flash.
function scoreboard(x, y, w, h, o = {}) {
  ctx.save();
  rrect(x, y, w, h, 14); paint(lg(0, y, 0, y + h, [[0, '#1B1E28'], [1, '#07080C']]), '#C9A43A', 8);
  if (o.title) { rrect(x + 30, y + 22, w - 60, 78, 8); paint('#8A1219'); txt(o.title, x + w / 2, y + 62, 54, NP.gold, { font: 'bungee', maxW: w - 100 }); }
  const rows = o.rows ?? [], top = y + (o.title ? 128 : 30), rh = (h - (top - y) - (o.foot ? 90 : 30)) / Math.max(1, rows.length);
  rows.forEach((r, i) => {
    const ry = top + i * rh;
    txt(r.name, x + 46, ry + rh / 2, Math.min(64, rh * .55), r.col ?? NP.white, { font: 'bungee', align: 'left', maxW: w * .6 });
    const bulbs = String(r.score);
    rrect(x + w - 60 - bulbs.length * 70, ry + rh * .12, bulbs.length * 70 + 30, rh * .76, 6); paint('#000');
    pixelText(bulbs, x + w - 45, ry + rh / 2 - Math.min(9, rh * .1) * 3.5, Math.min(10, rh * .1), (o.flash === i && frac(T * 5) < .5) ? '#FFFFFF' : '#FFC83A', { align: 'right', edge: null });
  });
  if (o.foot) txt(o.foot, x + w / 2, y + h - 48, 44, NP.white, { font: 'bungee', maxW: w - 60 });
  // bulb dots on the frame
  for (let i = 0; i < 30; i++) { const on = (i + Math.floor(T * 8)) % 3 === 0; ell(x + 20 + i * (w - 40) / 29, y + h - 12, 5); paint(on ? '#FFE27A' : '#5A4A1A'); }
  ctx.restore();
}
// pollBoard(o): full-screen phone-in poll. o.q (question), o.opts: [{ label, num (phone number), votes (0..1 share), col }], o.k (bars 0..1),
// o.head (default 'TONIGHT\'S POLL'), o.stamp ({ text, k }) a verdict slammed on top.
function pollBoard(t, o = {}) {
  gfxCard({ top: '#2A1470', bottom: '#080420', head: o.head ?? "TONIGHT'S POLL", headCol: NP.magenta, sub: o.sub ?? '50¢ PER CALL' });
  if (o.q) chrome(o.q, W / 2, 285, 78, { font: 'archivo', style: 'white', depth: 6, spacing: 1 });
  const opts = o.opts ?? [], n = opts.length, bw = 1500, x0 = (W - bw) / 2, rh = Math.min(170, 520 / Math.max(1, n));
  opts.forEach((op, i) => {
    const ry = 380 + i * rh, k = clamp((o.k ?? 1) * 1.3 - i * .15), share = (op.votes ?? 0) * easeOut(k), col = op.col ?? [NP.cyan, NP.gold, NP.magenta, NP.lime][i % 4];
    rrect(x0, ry, bw, rh - 24, 12); paint('rgb(0 0 0 / .45)', alpha(col, .8), 3);
    rrect(x0 + 6, ry + 6, (bw - 12) * share, rh - 36, 9); paint(lg(0, ry, 0, ry + rh, [[0, tint(col, .3)], [1, shade(col, .3)]]));
    txt(op.label, x0 + 40, ry + (rh - 24) / 2 + 2, Math.min(66, rh * .42), NP.white, { font: 'archivo', align: 'left', shadow: [3, 4], shadowCol: 'rgb(0 0 0 / .6)' });
    if (op.num) pixelText(op.num, x0 + bw - 330, ry + (rh - 24) / 2 - 14, 4, NP.white, { align: 'right' });
    txt(Math.round(share * 100) + '%', x0 + bw - 40, ry + (rh - 24) / 2 + 2, Math.min(70, rh * .45), NP.white, { font: 'anton', align: 'right', shadow: [3, 4], shadowCol: 'rgb(0 0 0 / .6)' });
  });
  if (o.stamp && (o.stamp.k ?? 1) > 0) stamp(o.stamp.text, W / 2, 620, o.stamp.size ?? 120, o.stamp.col ?? NP.red, -.12, { pop: o.stamp.k ?? 1, font: 'archivo', blend: 'source-over', alpha: 1 });
}
// tallyBoard(x, y, w, o): election-night results. o.title, o.rows: [{ label, n, col, win }], o.k (count-up 0..1), o.total.
function tallyBoard(x, y, w, o = {}) {
  const rows = o.rows ?? [], rh = 120, h = 110 + rows.length * rh;
  rrect(x, y, w, h, 12); paint(lg(0, y, 0, y + h, [[0, '#15307E'], [1, '#081440']]), '#C9D8FF', 5);
  if (o.title) txt(o.title, x + w / 2, y + 56, 52, NP.white, { font: 'archivo', maxW: w - 60, spacing: 1 });
  const tot = o.total ?? rows.reduce((a, r) => a + r.n, 0), k = clamp(o.k ?? 1);
  rows.forEach((r, i) => {
    const ry = y + 100 + i * rh, v = Math.round(r.n * easeOut(k));
    rrect(x + 24, ry, w - 48, rh - 18, 8); paint(alpha(r.col ?? NP.blue, .35), alpha(r.col ?? NP.blue, .9), 3);
    rrect(x + 30, ry + 6, (w - 60) * (v / Math.max(1, tot)), rh - 30, 6); paint(alpha(r.col ?? NP.blue, .9));
    txt(r.label, x + 56, ry + (rh - 18) / 2 + 2, 54, NP.white, { font: 'archivo', align: 'left', shadow: [3, 3], shadowCol: 'rgb(0 0 0 / .5)' });
    pixelText(String(v), x + w - 60, ry + (rh - 18) / 2 - 21, 6, NP.white, { align: 'right' });
    if (r.win && k >= 1) { const wx = x + w - 60 - pixelW(String(v), 6) - 70; ell(wx, ry + (rh - 18) / 2, 30); paint(NP.gold, NP.ink, 3); ctx.beginPath(); ctx.moveTo(wx - 14, ry + (rh - 18) / 2); ctx.lineTo(wx - 3, ry + (rh - 18) / 2 + 12); ctx.lineTo(wx + 16, ry + (rh - 18) / 2 - 12); paint(null, NP.ink, 6); }
  });
  return h;
}

// =====================================================================================================
// COURTROOM SKETCH MODE — sketchMode(true) makes toon()/computer()/paint() draw as pastel-on-paper; sketchPaper() is the backdrop.
// =====================================================================================================
const _hatchCache = new Map();
function _hatch(col) {
  let p = _hatchCache.get(col);
  if (!p) {
    const c = makeCanvas(14, 14), g = c.getContext('2d');
    g.strokeStyle = col; g.lineWidth = 2.4; g.lineCap = 'round';
    for (const o of [-14, 0, 14]) { g.beginPath(); g.moveTo(o, 14); g.lineTo(o + 14, 0); g.stroke(); }
    p = ctx.createPattern(c, 'repeat'); _hatchCache.set(col, p);
  }
  p.setTransform(ctx.getTransform().invertSelf());
  return p;
}
function _sketchPaint(fill, stroke, lw) {
  ctx.save();
  if (fill && typeof fill === 'string' && !fill.startsWith('rgb')) { ctx.globalAlpha *= .42; ctx.fillStyle = fill; ctx.fill(); ctx.globalAlpha /= .42; ctx.globalAlpha *= .85; ctx.fillStyle = _hatch(fill); ctx.fill(); }
  else if (fill) { ctx.fillStyle = fill; ctx.globalAlpha *= .5; ctx.fill(); }
  if (stroke || fill) {
    const m = ctx.getTransform(), sc = Math.hypot(m.a, m.b) / RS || 1, L = stroke ? lw : 2.4 / sc;
    ctx.strokeStyle = 'rgb(45 36 40 / .85)'; ctx.lineWidth = L * 1.15; ctx.lineJoin = 'round'; ctx.lineCap = 'round';
    ctx.setLineDash([L * 7, L * 1.6, L * 3, L * 1.2]); ctx.stroke(); ctx.setLineDash([]); ctx.globalAlpha *= .45; ctx.lineWidth = L * .55; ctx.stroke();
  }
  ctx.restore();
}
function sketchMode(on) { _sketch = on ? 1 : 0; }
// sketchPaper(o): the sketch artist's pad on an easel-ish board: cream paper with tooth, a signature scrawl. o.sig (initials).
function sketchPaper(o = {}) {
  fillAll('#3A2E28');
  rrect(70, 50, W - 140, H - 100, 6); paint('#EFE6D0', NP.ink, 4);
  ctx.save(); rrect(70, 50, W - 140, H - 100, 6); ctx.clip();
  ctx.fillStyle = 'rgb(120 100 70 / .05)'; for (let i = 0; i < 260; i++) ctx.fillRect(70 + hash2(i, 1) * (W - 140), 50 + hash2(i, 2) * (H - 100), 2 + hash2(i, 3) * 40, 1.5);
  ctx.restore();
  if (o.sig !== null) txt(o.sig ?? '— M.K. ’89', W - 230, H - 110, 34, 'rgb(60 40 40 / .7)', { font: 'scrawl', rot: -.05 });
}

// =====================================================================================================
// TEST SIGNALS & TAPE — colour bars, countdown leader, snow, the VCR blue screen
// =====================================================================================================
// colorBars(o): SMPTE colour bars (75%). o.slate: text lines for a station ID box over the bars; o.k (slate pop 0..1).
function colorBars(o = {}) {
  const top = [['#C0C0C0'], ['#C0C000'], ['#00C0C0'], ['#00C000'], ['#C000C0'], ['#C00000'], ['#0000C0']], bw = W / 7;
  top.forEach(([c], i) => { ctx.fillStyle = c; ctx.fillRect(i * bw, 0, bw + 1, H * .67); });
  ['#0000C0', '#131313', '#C000C0', '#131313', '#00C0C0', '#131313', '#C0C0C0'].forEach((c, i) => { ctx.fillStyle = c; ctx.fillRect(i * bw, H * .67, bw + 1, H * .08); });
  const b = [['#00214C', 1.25], ['#FFFFFF', 1.25], ['#32006A', 1.25], ['#131313', 1.25], ['#090909', bw / 3 / (bw)], ['#131313', bw / 3 / bw], ['#1D1D1D', bw / 3 / bw], ['#131313', 1]];
  let x = 0; for (const [c, f] of b) { const w = f * bw; ctx.fillStyle = c; ctx.fillRect(x, H * .75, w + 1, H * .25); x += w; }
  if (o.slate) {
    const k = o.k ?? 1; if (k <= 0) return;
    const L = o.slate, bwid = 1240, bh = 70 + L.length * 64;
    ctx.save(); ctx.translate(W / 2, 360); ctx.scale(1, easeOut(k));
    rrect(-bwid / 2, -bh / 2, bwid, bh, 6); paint('rgb(0 0 0 / .85)', '#FFFFFF', 4);
    L.forEach((l, i) => pixelText(l, 0, -bh / 2 + 40 + i * 64, 6, NP.white, { align: 'center', edge: null }));
    ctx.restore();
  }
}
// countdown(n, k, o): the film/video countdown leader showing number n; k = 0..1 sweep through this number's second.
function countdown(n, k, o = {}) {
  fillAll(o.bg ?? '#9A9A94');
  ctx.save(); ctx.translate(W / 2, H / 2);
  ctx.fillStyle = '#6A6A64'; ctx.beginPath(); ctx.moveTo(0, 0); ctx.arc(0, 0, 900, -Math.PI / 2, -Math.PI / 2 + k * TAU); ctx.closePath(); ctx.fill();
  ctx.strokeStyle = '#111'; ctx.lineWidth = 6; ctx.beginPath(); ctx.moveTo(-W, 0); ctx.lineTo(W, 0); ctx.moveTo(0, -H); ctx.lineTo(0, H); ctx.stroke();
  for (const r of [330, 400]) { ell(0, 0, r); paint(null, '#F4F4F0', 10); }
  txt(String(n), 0, 18, 520, '#111', { font: 'anton' });
  ctx.restore();
}
// Noise textures (VHS snow): horizontally streaky grey noise, built once.
let _snow = null;
function _buildSnow() {
  _snow = [];
  for (let v = 0; v < 4; v++) {
    const w = 320, h = 270, c = makeCanvas(w, h), g = c.getContext('2d'), img = g.createImageData(w, h), d = img.data;
    for (let i = 0; i < w * h; i++) { const n = hash2(v * 7 + 3, i), m = n * n * 255; d[i * 4] = m; d[i * 4 + 1] = m; d[i * 4 + 2] = m + 8; d[i * 4 + 3] = 255; }
    g.putImageData(img, 0, 0); _snow.push(c);
  }
}
// snow(a, o): full-frame VHS static at alpha a (0..1). o.x/y/w/h to confine it.
function snow(a = 1, o = {}) {
  if (!_snow) _buildSnow();
  const f = Math.floor(T * 30), c = _snow[f % 4], x = o.x ?? 0, y = o.y ?? 0, w = o.w ?? W, h = o.h ?? H;
  ctx.save(); ctx.globalAlpha *= a; ctx.imageSmoothingEnabled = false;
  const ox = hash(f) * 300, oy = hash(f + 9) * 200;
  ctx.beginPath(); ctx.rect(x, y, w, h); ctx.clip();
  ctx.drawImage(c, 0, 0, 320, 270, x - ox, y - oy, w * 2.2, h * 1.9);
  ctx.restore();
}
// blueScreen(): the VCR's blue "no signal" screen.
function blueScreen() { fillAll('#1034C8'); }

// =====================================================================================================
// DVE — 80s digital video effects for chorus sub-shots (each draw fn paints a whole 1920×1080 frame)
// =====================================================================================================
// dveFlip(k, drawA, drawB): A squeezes to a sliver and B flips out of it (k 0..1). o.axis 'x'|'y'.
function dveFlip(k, drawA, drawB, o = {}) {
  fillAll('#000'); const a = k < .5, sc = Math.abs(Math.cos(k * Math.PI)), fn = a ? drawA : drawB;
  const c = renderTo('dveA', .5, fn);
  ctx.save(); ctx.translate(W / 2, H / 2); o.axis === 'y' ? ctx.scale(1, sc) : ctx.scale(sc, 1); ctx.drawImage(c, -W / 2, -H / 2, W, H); ctx.restore();
}
// dveStar(k, drawA, drawB): B is revealed through a growing five-point star (the most 80s wipe there is).
function dveStar(k, drawA, drawB, o = {}) {
  drawA(); if (k <= 0) return;
  ctx.save(); poly(starPts(o.x ?? W / 2, o.y ?? H / 2, easeIn(k) * 2600 + 1, .45, 5, -TAU / 4 + k)); ctx.clip(); drawB(); ctx.restore();
}
// dveBox(k, x, y, w, h, draw): a picture flying in from the centre to the rect (with a white keyline).
function dveBox(k, x, y, w, h, draw, o = {}) {
  if (k <= 0) return;
  const c = renderTo(o.key ?? 'dveBox', o.res ?? .5, draw), e = backOut(k, 1.1);
  const cx = lerp(W / 2, x + w / 2, e), cy = lerp(H / 2, y + h / 2, e), ww = lerp(40, w, e), hh = lerp(22, h, e);
  ctx.save(); ctx.translate(cx, cy); if (o.rot) ctx.rotate(o.rot * (1 - e));
  ctx.fillStyle = 'rgb(0 0 0 / .4)'; ctx.fillRect(-ww / 2 + 10, -hh / 2 + 12, ww, hh);
  ctx.drawImage(c, -ww / 2, -hh / 2, ww, hh); ctx.lineWidth = 6; ctx.strokeStyle = '#FFF'; ctx.strokeRect(-ww / 2, -hh / 2, ww, hh);
  ctx.restore();
}
// dveTiles(n, draw, o): the multi-image effect — the whole picture repeated in an n×n grid (n may be fractional mid-split).
function dveTiles(n, draw, o = {}) {
  const c = renderTo('tiles', o.res ?? .5, draw), N = Math.max(1, Math.ceil(n - 1e-6)), gap = o.gap ?? 8;
  fillAll(o.bg ?? '#050510');
  const tw = (W - gap * (N + 1)) / N, th = (H - gap * (N + 1)) / N;
  for (let r = 0; r < N; r++) for (let q = 0; q < N; q++) ctx.drawImage(c, gap + q * (tw + gap), gap + r * (th + gap), tw, th);
}
// tvOff(k, draw): the CRT switching off — the picture (a whole frame painted by draw) squeezes to a bright line, then to a dot, then
// black. k 0..1 (≈ 0.5 s reads well). Draw it as the whole frame.
function tvOff(k, draw) {
  fillAll('#000'); if (k >= 1) return;
  const c = renderTo('tvoff', .5, draw), a = clamp(k / .55), b = clamp((k - .55) / .3);
  const sy = lerp(1, .004, easeIn(a)), sx = lerp(1, .004, easeIn(b));
  ctx.save(); ctx.translate(W / 2, H / 2); ctx.scale(sx, sy); ctx.drawImage(c, -W / 2, -H / 2, W, H);
  ctx.globalCompositeOperation = 'lighter'; ctx.fillStyle = `rgb(255 255 255 / ${a * .9})`; ctx.fillRect(-W / 2, -H / 2, W, H); ctx.restore();
  if (k > .5) glint(W / 2, H / 2, 160 * (1 - clamp((k - .7) / .3)), 1 - clamp((k - .8) / .2));
}
// paintShot(key, p): paint another segment's shot at progress p (for rewinds/recaps). Overlay switches it sets are discarded.
function paintShot(key, p) {
  const s = segByKey(key), fn = s && SHOTS[key]; if (!fn) return;
  const d = s.end - s.start, t = s.start + clamp(p) * d, saved = [T, _noCaption, _noStamp, _captionStyle, _fx, _vcrMode], depth = _camDepth;
  T = t; ctx.save();
  try { fn(clamp(p), clamp(p) * d, d, t, s); } finally { while (_camDepth > depth) camEnd(); ctx.restore(); [T, _noCaption, _noStamp, _captionStyle, _fx, _vcrMode] = saved; }
}

// =====================================================================================================
// PER-FRAME SWITCHES (a shot may call these every frame; they reset after each frame)
//   hideCaption()            no closed caption this frame          captionStyle({ color, y, size, rows })
//   hideStamp() / hideOSD()  no VCR on-screen display this frame   vcrMode('PAUSE'|'FF'|'REW'|'STOP'|'PLAY')
//   tapeFX({ … })            tape/CRT pass tweaks (see _FX0 below)  glitch(kind, k)  force a tape glitch now
// =====================================================================================================
let _fx = null, _vcrMode = null;
function tapeFX(o) { _fx = Object.assign(_fx || {}, o); }
function vcrMode(m) { _vcrMode = m; }
const hideOSD = () => hideStamp();
// kind: 'track' (tracking bands + noise bar) | 'roll' (vertical roll) | 'tear' (horizontal-hold skew) | 'snow' (static burst); k = 0..1 strength.
function glitch(kind, k = 1) { tapeFX({ glitch: kind, glitchK: k }); }
const _FX0 = {
  cut: undefined,   // auto glitch at this frame's cut: undefined = automatic, 'none' | 'track' | 'roll' | 'tear' to override
  glitch: null, glitchK: 0,
  chroma: 1,        // chroma bleed strength (0 = off)
  noise: 1,         // grain
  dropouts: 1,      // tape-wear white streaks (0 = off, 3 = worn tape)
  jitter: 1,        // occasional line jitter + top flagging + head-switching noise at the bottom
  pauseBar: 0,      // 0..1: the paused-VHS noise band (use with vcrMode('PAUSE'))
  pauseY: .74,      // where that band sits, as a fraction of the frame height (the default crosses the chyron's top)
  scan: 1, curve: 1, vignette: 1, // CRT pass
  crt: 1,           // 0 = skip the whole CRT pass
};

// ---------- scratch buffers (device pixels) ----------
const _fxBufs = new Map();
function _fxBuf(key, w = canvas.width, h = canvas.height) {
  let c = _fxBufs.get(key);
  if (!c || c.width !== w || c.height !== h) { c = makeCanvas(w, h); _fxBufs.set(key, c); }
  return c;
}
function _grab(key = 'grab') { const c = _fxBuf(key), g = c.getContext('2d'); g.globalCompositeOperation = 'copy'; g.drawImage(canvas, 0, 0); g.globalCompositeOperation = 'source-over'; return c; }

// ---------- automatic tape glitch at cuts ----------
function _cutKind(s) { const h = hstr(s.key + '/cut'); return h < .42 ? 'track' : h < .62 ? 'roll' : h < .8 ? 'tear' : 'none'; }
function _autoCut(t, s) {
  if (!s) return null;
  const i = SEGS.indexOf(s), age = t - s.start;
  if (s.kind !== 'intro' && age < .1) return { kind: _cutKind(s), k: 1 - age / .1 };
  const nx = SEGS[i + 1]; if (nx && nx.start - t < .035) return { kind: _cutKind(nx), k: .6 * (1 - (nx.start - t) / .035) + .2 };
  return null;
}
function _applyGlitch(kind, k, t) {
  if (!kind || kind === 'none' || k <= 0) return;
  const cw = canvas.width, ch = canvas.height, R = cw / W, B = _grab(), f = Math.floor(t * 30);
  if (kind === 'track') {
    for (let i = 0; i < 6; i++) { const y = hash2(f, i) * ch, h = (8 + hash2(f, i + 9) * 60) * R, dx = (hash2(f, i + 19) - .5) * 300 * R * k; ctx.drawImage(B, 0, y, cw, h, dx, y, cw, h); }
    const by = (hash(f + 3) * .75 + .1) * ch, bh = (30 + 70 * k) * R;
    ctx.save(); ctx.setTransform(RS, 0, 0, RS, 0, 0); ctx.globalCompositeOperation = 'screen'; snow(.85 * k, { y: by / R, h: bh / R }); ctx.restore();
    ctx.fillStyle = `rgb(255 255 255 / ${.5 * k})`; ctx.fillRect(0, by + bh * .4, cw, 2 * R);
  } else if (kind === 'roll') {
    const bar = 30 * R, v = Math.round(easeIn(k) * .5 * ch);
    ctx.fillStyle = '#000'; ctx.fillRect(0, 0, cw, ch);
    ctx.drawImage(B, 0, -v); ctx.drawImage(B, 0, ch - v + bar);
    ctx.fillStyle = '#0A0A0A'; ctx.fillRect(0, ch - v, cw, bar); ctx.fillStyle = 'rgb(255 255 255 / .4)'; ctx.fillRect(0, ch - v + bar * .45, cw * .3, 2 * R);
  } else if (kind === 'tear') {
    const n = 30;
    for (let i = 0; i < n; i++) { const y0 = Math.floor(i * ch / n), y1 = Math.floor((i + 1) * ch / n), u = 1 - i / n, dx = k * 240 * R * u * u * (1 + .25 * Math.sin(i * 1.7 + t * 50)); ctx.drawImage(B, 0, y0, cw, y1 - y0, dx, y0, cw, y1 - y0); ctx.drawImage(B, 0, y0, cw, y1 - y0, dx - cw, y0, cw, y1 - y0); }
  } else if (kind === 'snow') {
    ctx.save(); ctx.setTransform(RS, 0, 0, RS, 0, 0); snow(k); ctx.restore();
  }
}

// ---------- the tape pass: glitches, flagging, jitter, head-switching, dropouts, chroma bleed, grain ----------
function _tapePass(t, s, fx) {
  const cw = canvas.width, ch = canvas.height, R = cw / W, f = Math.floor(t * 30);
  ctx.setTransform(1, 0, 0, 1, 0, 0); ctx.globalAlpha = 1; ctx.globalCompositeOperation = 'source-over';
  const cut = fx.cut === 'none' ? null : fx.cut ? { kind: fx.cut, k: (_autoCut(t, s) || { k: 0 }).k } : _autoCut(t, s);
  if (cut) _applyGlitch(cut.kind, cut.k, t);
  if (fx.glitch) _applyGlitch(fx.glitch, fx.glitchK, t);
  if (fx.jitter > 0) {
    const B = _grab();
    // top-edge flagging (skew), head-switching noise at the bottom, and an occasional jittery line band
    for (let i = 0; i < 5; i++) { const y = i * 4 * R, dx = (5 - i) * 2.2 * R * fx.jitter; ctx.drawImage(B, 0, y, cw, 4 * R, dx, y, cw, 4 * R); }
    const hs = 12 * R, hy = ch - hs, hd = (14 + hash(f) * 16) * R * fx.jitter;
    ctx.drawImage(B, 0, hy, cw, hs, hd, hy, cw, hs); ctx.fillStyle = 'rgb(0 0 0 / .8)'; ctx.fillRect(0, hy, hd, hs);
    ctx.fillStyle = 'rgb(255 255 255 / .35)'; ctx.fillRect(hd, hy + hs * .3, cw * (.2 + hash(f + 1) * .5), 1.5 * R);
    if (hash(f * 13 + 5) < .18 * fx.jitter) { const y = hash(f + 77) * ch, h = (3 + hash(f + 78) * 10) * R, dx = (hash(f + 79) - .5) * 26 * R; ctx.drawImage(B, 0, y, cw, h, dx, y, cw, h); }
  }
  if (fx.pauseBar > 0) {
    const by = (fx.pauseY + (hash(f) - .5) * .01) * ch, bh = 46 * R;
    ctx.save(); ctx.setTransform(RS, 0, 0, RS, 0, 0); snow(.9 * fx.pauseBar, { y: by / RS, h: bh / RS }); ctx.restore();
    ctx.fillStyle = `rgb(255 255 255 / ${.6 * fx.pauseBar})`; ctx.fillRect(0, by - 2 * R, cw, 2 * R);
  }
  if (fx.dropouts > 0) {
    const n = hash(f * 3 + 1) < .32 * fx.dropouts ? 1 + Math.floor(hash(f * 3 + 2) * 3 * fx.dropouts) : 0;
    for (let i = 0; i < n; i++) {
      const x = hash2(f, i + 40) * cw, y = hash2(f, i + 50) * ch, L = (30 + hash2(f, i + 60) ** 2 * 420) * R, h = (1.5 + hash2(f, i + 70) * 2) * R;
      ctx.fillStyle = lg(x, 0, x + L, 0, [[0, 'rgb(255 255 255 / .9)'], [.6, 'rgb(230 230 240 / .7)'], [1, 'rgb(255 255 255 / 0)']]); ctx.fillRect(x, y, L, h);
      ctx.fillStyle = 'rgb(0 0 0 / .5)'; ctx.fillRect(x + L, y, L * .4, h);
    }
  }
  if (fx.chroma > 0) {
    const sw = Math.round(cw / 6), sh = Math.round(ch / 2), S = _fxBuf('chroma', sw, sh), g = S.getContext('2d');
    g.imageSmoothingEnabled = true; g.imageSmoothingQuality = 'medium'; g.globalCompositeOperation = 'copy'; g.drawImage(canvas, 0, 0, sw, sh);
    ctx.globalCompositeOperation = 'color'; ctx.globalAlpha = .8 * clamp(fx.chroma); ctx.imageSmoothingEnabled = true;
    ctx.drawImage(S, 4 * R, 0, cw, ch);
    ctx.globalCompositeOperation = 'source-over'; ctx.globalAlpha = 1;
  }
  if (fx.noise > 0) {
    if (!_snow) _buildSnow();
    ctx.globalCompositeOperation = 'overlay'; ctx.globalAlpha = .13 * fx.noise; ctx.imageSmoothingEnabled = false;
    ctx.drawImage(_snow[f % 4], hash(f) * 100, hash(f + 1) * 60, 200, 160, 0, 0, cw, ch);
    ctx.globalCompositeOperation = 'source-over'; ctx.globalAlpha = 1; ctx.imageSmoothingEnabled = true;
  }
}

// ---------- closed captions (Line 21 roll-up style: white caps on black boxes, ♪ around sung lines) ----------
function _ccText(s) {
  return String(s).toUpperCase().replace(/\b4O\b/g, '4o').replace(/[“”]/g, '"').replace(/[‘’]/g, "'").replace(/…/g, '...')
    .replace(/\s*—\s*$/, ' --').replace(/\s*—\s*/g, ' -- ').replace(/–/g, '-').trim();
}
function _ccRows(text, max) {
  const words = text.split(' '), rows = []; let cur = '';
  for (const w of words) { const t2 = cur ? cur + ' ' + w : w; if (t2.length > max && cur) { rows.push(cur); cur = w; } else cur = t2; }
  if (cur) rows.push(cur);
  rows[0] = '♪ ' + rows[0]; rows[rows.length - 1] += ' ♪';
  return rows;
}
function _ccNote(x, y, sz, col) { // a drawn ♪ (no bundled font has it)
  ctx.fillStyle = col; ctx.beginPath(); ctx.ellipse(x - sz * .1, y + sz * .22, sz * .17, sz * .12, -.4, 0, TAU); ctx.fill();
  ctx.fillRect(x + sz * .04, y - sz * .38, sz * .06, sz * .6);
  ctx.beginPath(); ctx.moveTo(x + sz * .1, y - sz * .38); ctx.quadraticCurveTo(x + sz * .32, y - sz * .22, x + sz * .24, y - sz * .02); ctx.quadraticCurveTo(x + sz * .22, y - sz * .2, x + sz * .1, y - sz * .22); ctx.fill();
}
function _ccDraw(rows, cy, sz, col, reveal, a = 1) {
  const cw = textW('M', sz, 'code'), rh = Math.round(sz * 1.42), total = rows.reduce((n, r) => n + r.length, 0);
  let shown = Math.round(total * reveal);
  ctx.save(); ctx.globalAlpha *= a; ctx.font = `${sz}px "${FONTS.code}"`; ctx.textBaseline = 'middle'; ctx.textAlign = 'left';
  rows.forEach((r, i) => {
    const y = cy - (rows.length - 1 - i) * rh, n = Math.min(r.length, shown); shown -= n; if (n <= 0) return;
    const x0 = Math.round(W / 2 - r.length * cw / 2);
    ctx.fillStyle = '#000'; ctx.fillRect(x0 - cw * .6, y - rh / 2, n * cw + cw * 1.2, rh);
    const vis = r.slice(0, n);
    for (let j = 0; j < vis.length; j++) { const c = vis[j]; if (c === '♪') _ccNote(x0 + j * cw + cw * .45, y, sz, col); }
    ctx.fillStyle = col; ctx.fillText(vis.replace(/♪/g, ' '), x0, y + sz * .04);
  });
  ctx.restore();
  return rows.length * rh;
}
// ccText(str, o): draw your own closed caption in the same style, e.g. ccText('[ THEME MUSIC ]'). o.y (bottom row centre, default 1004),
// o.color, o.reveal (0..1 characters shown), o.notes (wrap in ♪), o.size, o.maxChars. Call hideCaption() too if a lyric would collide.
function ccText(str, o = {}) {
  let rows = _ccRows(_ccText(str), o.maxChars ?? 36);
  if (!o.notes) rows = rows.map(r => r.replace(/^♪ /, '').replace(/ ♪$/, ''));
  _ccDraw(rows, o.y ?? 1004, o.size ?? 42, o.color ?? NP.ccText, o.reveal ?? 1);
}
function _caption(t) {
  if (_noCaption) return;
  const st = _captionStyle || {}, sz = st.size ?? 42, maxc = st.maxChars ?? 36, cy = st.y ?? 1004, rh = Math.round(sz * 1.42);
  const ln = lineAt(t); if (!ln) return;
  const i = LINES.indexOf(ln), age = t - ln.start, dur = ln.end - ln.start;
  const col = st.color ?? (ln.sec[0] === 'C' ? NP.ccYellow : NP.ccText);
  const rows = _ccRows(_ccText(ln.text), maxc);
  const rev = clamp(age / clamp(dur * .28, .16, .42));
  // roll-up: the previous line slides up out of the way, then is erased
  const prev = LINES[i - 1];
  if (prev && age < .26 && ln.start - prev.end < .6 && st.rows !== 1) {
    const e = easeOut(clamp(age / .12)), prows = _ccRows(_ccText(prev.text), maxc);
    const pcol = st.color ?? (prev.sec[0] === 'C' ? NP.ccYellow : NP.ccText);
    _ccDraw(prows, cy - rows.length * rh * e, sz, pcol, 1);
  }
  _ccDraw(rows, cy, sz, col, rev);
}

// ---------- VCR on-screen display: mode + the line's date (rolls FF/REW through the calendar when it changes) ----------
const _MONTHS = ['JAN', 'FEB', 'MAR', 'APR', 'MAY', 'JUN', 'JUL', 'AUG', 'SEP', 'OCT', 'NOV', 'DEC'];
function _pDate(s) { const p = s.split(' '); let m = _MONTHS.indexOf(p[0]); if (m < 0) m = 6; const d = p.length === 3 ? +p[1] : null, y = +p[p.length - 1]; return { m, d, y, v: y * 372 + m * 31 + (d ?? 15) }; }
function _fDate(v, day) { const y = Math.floor(v / 372), r = v - y * 372, m = clamp(Math.floor(r / 31), 0, 11), d = clamp(Math.floor(r - m * 31) + 1, 1, 30); return day ? `${_MONTHS[m]} ${String(d).padStart(2, ' ')} ${y}` : `${_MONTHS[m]} ${y}`; }
function _dateInfo(t) {
  let cur = null, prev = null;
  for (const s of SEGS) { if (s.start > t) break; if (s.date && s.date !== cur?.date) { prev = cur; cur = s; } }
  return cur ? { text: cur.date, prev: prev?.date ?? null, age: t - cur.start } : null;
}
const OSD_SYM = { PLAY: '▶', PAUSE: '❚', FF: '▶▶', REW: '◀◀', STOP: '■', REC: '', SLOW: '❚▶' };
function _osd(t) {
  if (_noStamp) return;
  const d = _dateInfo(t), ROLL = .3, xr = 1796;
  let mode = _vcrMode, dateStr = d?.text;
  if (d && d.prev && d.age < ROLL) {
    const a = _pDate(d.prev), b = _pDate(d.text), u = ease(d.age / ROLL);
    if (!mode) mode = b.v < a.v ? 'REW' : 'FF';
    dateStr = _fDate(lerp(a.v, b.v, u), true);
  }
  if (!mode && !d) return;
  mode = mode ?? 'PLAY';
  const blinkMode = (mode === 'FF' || mode === 'REW' || mode === 'PAUSE') && frac(t * 3) > .6;
  if (!blinkMode) pixelText(`${mode} ${OSD_SYM[mode] ?? ''}`.trim(), xr, 58, 5, NP.white, { align: 'right', shadow: [.6, .6] });
  if (mode === 'REC') { ell(xr - pixelW('REC', 5) - 30, 75, 13); paint(frac(t * 1.5) < .6 ? '#FF2020' : '#601010', '#000', 3); }
  if (dateStr) {
    const firstBlink = d && !d.prev && d.age < .25 && frac(d.age * 8) > .5;
    if (!firstBlink) pixelText(dateStr, xr, 108, 7, NP.white, { align: 'right', shadow: [.5, .5] });
  }
}

// ---------- the CRT pass: scanlines, black-level lift, tube curvature, vignette + bezel ----------
let _scanPat = null, _vig = null;
function _crtPass(fx) {
  const cw = canvas.width, ch = canvas.height, R = cw / W;
  ctx.setTransform(1, 0, 0, 1, 0, 0); ctx.globalAlpha = 1; ctx.globalCompositeOperation = 'source-over';
  if (fx.curve > 0) {
    // barrel distortion, separable: rows pinch toward the top/bottom, then columns toward the left/right
    const k = .026 * fx.curve, B = _grab('curve'), n = 40;
    ctx.fillStyle = '#000'; ctx.fillRect(0, 0, cw, ch);
    for (let i = 0; i < n; i++) { const y0 = Math.floor(i * ch / n), y1 = Math.floor((i + 1) * ch / n), dy = ((y0 + y1) / 2 - ch / 2) / (ch / 2), sc = 1 - k * dy * dy, w = cw * sc; ctx.drawImage(B, 0, y0, cw, y1 - y0, (cw - w) / 2, y0, w, y1 - y0); }
    const B2 = _grab('curve2'), kv = k * 1.25;
    ctx.fillRect(0, 0, cw, ch);
    for (let i = 0; i < n; i++) { const x0 = Math.floor(i * cw / n), x1 = Math.floor((i + 1) * cw / n), dx = ((x0 + x1) / 2 - cw / 2) / (cw / 2), sc = 1 - kv * dx * dx, h = ch * sc; ctx.drawImage(B2, x0, 0, x1 - x0, ch, x0, (ch - h) / 2, x1 - x0, h); }
  }
  if (fx.scan > 0) {
    const P = Math.max(2, Math.round(3 * R));
    if (!_scanPat || _scanPat.P !== P) { const c = makeCanvas(4, P), g = c.getContext('2d'); g.fillStyle = 'rgb(0 0 0 / .3)'; g.fillRect(0, 0, 4, Math.max(1, Math.round(R))); _scanPat = ctx.createPattern(c, 'repeat'); _scanPat.P = P; }
    ctx.globalAlpha = fx.scan; ctx.fillStyle = _scanPat; ctx.fillRect(0, 0, cw, ch); ctx.globalAlpha = 1;
  }
  ctx.globalCompositeOperation = 'lighten'; ctx.fillStyle = '#0B0B12'; ctx.fillRect(0, 0, cw, ch); ctx.globalCompositeOperation = 'source-over';
  if (fx.vignette > 0) {
    if (!_vig) {
      const vw = 480, vh = 270; _vig = makeCanvas(vw, vh); const g = _vig.getContext('2d');
      const gr = g.createRadialGradient(vw / 2, vh / 2, vh * .35, vw / 2, vh / 2, vw * .62); gr.addColorStop(0, 'rgb(0 0 0 / 0)'); gr.addColorStop(.7, 'rgb(0 0 0 / .22)'); gr.addColorStop(1, 'rgb(0 0 0 / .7)');
      g.fillStyle = gr; g.fillRect(0, 0, vw, vh);
      // bezel: black outside a pillow-shaped tube face
      g.fillStyle = '#000'; g.beginPath(); g.rect(-10, -10, vw + 20, vh + 20);
      const m = 3, bow = 3.2, r = 16;
      g.moveTo(m + r, m); g.quadraticCurveTo(vw / 2, m - bow, vw - m - r, m); g.quadraticCurveTo(vw - m, m, vw - m, m + r);
      g.quadraticCurveTo(vw - m + bow, vh / 2, vw - m, vh - m - r); g.quadraticCurveTo(vw - m, vh - m, vw - m - r, vh - m);
      g.quadraticCurveTo(vw / 2, vh - m + bow, m + r, vh - m); g.quadraticCurveTo(m, vh - m, m, vh - m - r);
      g.quadraticCurveTo(m - bow, vh / 2, m, m + r); g.quadraticCurveTo(m, m, m + r, m); g.fill('evenodd');
      // glass reflection
      const hl = g.createLinearGradient(0, 0, vw * .5, vh * .6); hl.addColorStop(0, 'rgb(255 255 255 / .07)'); hl.addColorStop(.5, 'rgb(255 255 255 / .02)'); hl.addColorStop(1, 'rgb(255 255 255 / 0)');
      g.fillStyle = hl; g.beginPath(); g.ellipse(vw * .28, vh * .18, vw * .32, vh * .16, -.25, 0, TAU); g.fill();
    }
    ctx.globalAlpha = fx.vignette; ctx.imageSmoothingEnabled = true; ctx.drawImage(_vig, 0, 0, cw, ch); ctx.globalAlpha = 1;
  }
}

OVERLAYS.push((t, s) => {
  const fx = { ..._FX0, ...(_fx || {}) };
  try {
    ctx.save(); _tapePass(t, s, fx); ctx.restore();
    ctx.save(); ctx.setTransform(RS, 0, 0, RS, 0, 0); _caption(t); ctx.restore();
    ctx.save(); ctx.setTransform(RS, 0, 0, RS, 0, 0); _osd(t); ctx.restore();
    if (fx.crt) { ctx.save(); _crtPass(fx); ctx.restore(); }
  } finally {
    _noCaption = false; _noStamp = false; _captionStyle = null; _fx = null; _vcrMode = null;
  }
});

;
// ---- styles/newscast/ch/c01_intro.js ----
// c01_intro — Intro (0 → V1.1): somebody presses PLAY on a 1989 VHS tape of the Channel 89 special.
// Sub-shots follow the song's own beat grid (bpOf), because the arrangement does:
//   b0–b4    TV warms up → VCR blue screen "PLAY ▶" / CH 03 → the tape starts: snow and rolling bars (the piano pickup)
//   b4       the big hit: SMPTE colour bars slam in; station slate pops on b6; VU meters bounce; a tracking wobble on b8
//   b12–b18  countdown leader 6·5·4·3·2 on the beats, then black with the 2-pop, then a burst of snow
//   b18      the band kicks in: the CHANNEL 89 ACTION NEWS open — laser grid, flying chrome 89, globe, swooshes on the hits
//   b24      the special's title: WE DIDN'T START / THE SCALING, "A CHANNEL 89 SPECIAL REPORT · 2017–2026"; zoom-through on b27.5
//   b28      the studio, wide: crane push-in, anchors tapping their scripts square on every beat
//   b32      two-shot with name supers for CLAWD and VAL LOSS; scripts down on b34, eyes to camera → cut to V1.1 on the sung pickup
(() => {
  const B = n => onBeat(0, n);
  const hitFlash = (t, t0, dur = .12, a = .7) => { const k = (t - t0) / dur; if (k >= 0 && k < 1) { ctx.fillStyle = `rgb(255 255 255 / ${a * (1 - k)})`; ctx.fillRect(-100, -100, W + 200, H + 200); } };
  const theme = (t, t0) => ccText('[ DRAMATIC NEWS THEME ]', { reveal: clamp((t - t0) / .35) });

  // ---------- b0–b4: power-on, blue screen, tape start ----------
  function tapeStart(t, b) {
    fillAll('#000');
    if (t < .32) { // CRT warm-up: a dot, a line, then the raster opens
      const k = t / .32, w = lerp(20, W, easeOut(clamp(k * 2.2))), h = lerp(3, H, easeIn(clamp((k - .35) / .65)));
      ctx.fillStyle = rg(W / 2, H / 2, 2, Math.max(w, h) * .6, [[0, '#FFFFFF'], [.5, '#BFD4FF'], [1, 'rgb(40 60 200 / 0)']]);
      ctx.fillRect(W / 2 - w / 2, H / 2 - h / 2, w, h);
      tapeFX({ chroma: 0, dropouts: 0, jitter: 0 }); hideOSD(); return;
    }
    const kSnow = clamp((b - 2) / 1.6);
    blueScreen();
    vcrMode('PLAY');
    if (b < 2.6) pixelText('CH 03', 130, 96, 9, NP.phosphor, { shadow: [.5, .5] });
    if (b >= 2) {
      // tape heads find the signal: bars roll into place under snow
      ctx.save(); ctx.globalAlpha = clamp((b - 2.2) / 1.6);
      const roll = (1 - easeOut(clamp((b - 2.2) / 1.7))) * H * 1.3;
      ctx.translate(0, -(roll % (H + 40)));
      colorBars(); ctx.translate(0, H + 40); colorBars();
      ctx.restore();
      snow(kSnow * (1 - clamp((b - 3.5) / .5)) * .9);
      if (hash(Math.floor(t * 30)) < .6) glitch('track', .5 + kSnow * .5);
    }
    hitFlash(t, .32, .15, .5);
  }

  // ---------- b4–b12: colour bars + station slate ----------
  function vu(x, y, t, ph) {
    rrect(x, y, 46, 250, 6); paint('#0A0A0A', '#555', 3);
    const lvl = clamp(.55 + pulse(t, 5) * .35 + Math.sin(t * 23 + ph) * .08);
    for (let i = 0; i < 14; i++) { const on = i / 14 < lvl; ctx.fillStyle = on ? (i > 11 ? '#FF3030' : i > 8 ? '#FFD030' : '#40E060') : '#1A1A1A'; ctx.fillRect(x + 8, y + 232 - i * 16.5, 30, 12); }
  }
  function bars(t, b) {
    const sh = b < 4.5 ? shakeXY(t, 12 * (1 - (b - 4) / .5)) : [0, 0];
    ctx.save(); ctx.translate(sh[0], sh[1]);
    colorBars({ slate: ['CHANNEL 89 ACTION NEWS', '"WE DIDN\'T START THE SCALING"', 'SPECIAL REPORT - TRT 3:02', 'TONE 1KHZ -20DB'], k: (t - B(6)) / .22 });
    ctx.restore();
    // VU meters and a tape label, bottom right
    rrect(1440, 740, 390, 290, 10); paint('rgb(0 0 0 / .8)', '#888', 3);
    vu(1470, 760, t, 0); vu(1530, 760, t, 1.7);
    pixelText('L', 1484, 1016 - 6, 3, NP.white, { edge: null }); pixelText('R', 1544, 1016 - 6, 3, NP.white, { edge: null });
    pixelText('TAPE 1', 1605, 770, 4, NP.crtAmber, { edge: null });
    pixelText('SP', 1605, 815, 4, NP.crtAmber, { edge: null });
    pixelText('0:0' + Math.floor(t / 60) + ':' + String(Math.floor(t) % 60).padStart(2, '0'), 1605, 860, 4, NP.white, { edge: null });
    pixelText('REC 1989', 1605, 905, 4, frac(t * 1.5) < .6 ? '#FF4040' : '#702020', { edge: null });
    vcrMode('PLAY');
    hitFlash(t, B(4), .14, .8);
    if (Math.abs(b - 8) < .12) glitch('track', .7);
    if (Math.abs(b - 10.5) < .08) glitch('tear', .5);
  }

  // ---------- b12–b18: countdown leader ----------
  function leader(t, b) {
    if (b < 17) {
      const n = 6 - Math.floor(b - 12), k = frac(b - 12);
      const fl = .92 + .08 * hash(Math.floor(t * 24));
      countdown(n, k, { bg: mixCol('#9A9A94', '#6A6A66', 1 - fl) });
      // leader dirt: scratches and specks
      ctx.fillStyle = 'rgb(20 20 20 / .6)'; for (let i = 0; i < 6; i++) { const f = Math.floor(t * 24); ell(hash2(f, i) * W, hash2(f, i + 9) * H, 2 + hash2(f, i + 3) * 5); ctx.fill(); }
      ctx.fillStyle = 'rgb(255 255 255 / .35)'; ctx.fillRect(300 + hash(Math.floor(t * 8)) * 1300, 0, 2, H);
      hitFlash(t, B(Math.floor(b)), .08, .35);
      vcrMode('PLAY'); tapeFX({ dropouts: 2 });
      ccText('[ BEEP ]', { reveal: frac(b) < .25 ? 1 : 0, y: 1004 });
      return;
    }
    fillAll('#000');
    if (b < 17.25) { ell(W / 2, H / 2, 30, 30); paint('#FFF'); }
    if (b > 17.55) { snow(clamp((b - 17.55) / .45) * .8); glitch('track', clamp((b - 17.55) / .45)); }
    vcrMode('PLAY');
  }

  // ---------- b18–b24: the news open ----------
  function newsOpen(t, b) {
    const zoom = 1 + (b - 18) * .012;
    camBegin(W / 2, H / 2, zoom);
    laserGrid(t, { horizon: 640, speed: 1.6 });
    // globe rises behind on the right
    const gk = easeOut(clamp((b - 20.5) / 1.5));
    globe(1470, lerp(900, 360, gk), 250, t * .9, { col: NP.cyan });
    // the chrome 89 flies in spinning from the vanishing point
    const lk = clamp((b - 18) / 1.6), le = easeOut(lk);
    const lx = lerp(W / 2, 560, le), ly = lerp(560, 360, le), lr = lerp(12, 230, easeIn(lk) * .4 + le * .6);
    logo89(lx, ly, lr, { spin: (1 - le) * 5 * Math.PI + Math.sin(t * 2) * .15 });
    glint(lx + lr * .7, ly - lr * .7, 140 * pulse(t, 5), pulse(t, 5));
    swoosh(clamp((b - 18.3) / 1.2), 820, NP.red, { len: 1600, th: 60 });
    swoosh(clamp((b - 20) / 1.2), 870, NP.blue, { len: 1400, th: 40, alpha: .9 });
    swoosh(clamp((b - 22) / 1.2), 790, NP.gold, { len: 1500, th: 30, alpha: .9 });
    // ACTION NEWS wipes on at b20
    const ak = clamp((b - 20) / .6);
    if (ak > 0) {
      ctx.save(); ctx.beginPath(); ctx.rect(0, 0, 260 + ak * 1500, H); ctx.clip();
      const w = chrome('ACTION NEWS', 980, 760 - pulse(t, 7) * 8, 150, { font: 'archivo', italic: .14, depth: 14, spacing: 4 });
      ctx.restore();
      sweepGlint(980 - w / 2, 980 + w / 2, 720, (b - 21) / 1.2, 110);
      sweepGlint(980 - w / 2, 980 + w / 2, 720, (b - 23) / 1.0, 110);
    }
    camEnd();
    hitFlash(t, B(18), .16, .9); hitFlash(t, B(20), .1, .35); hitFlash(t, B(22), .1, .35);
    hideOSD(); theme(t, B(18));
  }

  // ---------- b24–b28: the special's title ----------
  function title(t, b) {
    const zt = clamp((b - 27.4) / .6), zoom = 1 + easeIn(zt) * 5;
    camBegin(W / 2, 470, zoom);
    laserGrid(t, { horizon: 720, speed: 2, col: NP.cyan, sky: ['#020416', '#3A0A4A'] });
    // sunburst behind the title
    ctx.save(); ctx.translate(W / 2, 470); ctx.rotate(t * .25); ctx.fillStyle = 'rgb(255 180 80 / .09)';
    for (let i = 0; i < 16; i++) { ctx.rotate(TAU / 16); poly([[0, 0], [1400, -90], [1400, 90]]); ctx.fill(); } ctx.restore();
    const k1 = easeOut(clamp((b - 24) / .5)), k2 = backOut(clamp((b - 25) / .45), 1.4), k3 = clamp((b - 26) / .4);
    chrome("WE DIDN'T START", lerp(-900, W / 2, k1), 330, 150, { font: 'archivo', italic: .14, depth: 14, spacing: 2 });
    if (k2 > 0) chrome('THE SCALING', lerp(W + 900, W / 2, clamp(k2)), 520 - pulse(t, 7) * 10, 200, { font: 'archivo', style: 'gold', italic: .14, depth: 18, spacing: 3, s: 1 + (1 - clamp((b - 25) / .2)) * .3 });
    if (k3 > 0) {
      ctx.save(); ctx.globalAlpha = k3;
      rrect(W / 2 - 520, 660, 1040, 76, 8); paint('rgb(0 0 30 / .6)', alpha(NP.cyan, .8), 3);
      txt('A CHANNEL 89 SPECIAL REPORT', W / 2, 700, 50, NP.white, { font: 'archivo', spacing: 6 });
      ctx.restore();
      pixelText('2017 - 2026', W / 2, 770, 7, NP.crtAmber, { align: 'center', alpha: clamp((b - 26.5) / .3) });
    }
    sweepGlint(W / 2 - 600, W / 2 + 620, 470, (b - 26) / 1.1, 150);
    glint(W / 2 + 560, 300, 120 * pulse(t, 4), pulse(t, 4));
    camEnd();
    if (zt > 0) { ctx.fillStyle = `rgb(255 255 255 / ${easeIn(zt) * .95})`; ctx.fillRect(0, 0, W, H); }
    hitFlash(t, B(25), .12, .5);
    hideOSD(); theme(t, B(18));
  }

  // ---------- b28–b32: the studio, wide ----------
  function wide(t, b) {
    const k = ease((b - 28) / 4);
    anchorShot(t, { who: 'wide', shuffle: 1, talk: 0, cam: { x: 960, y: lerp(760, 600, k), zoom: lerp(.6, .82, k) } });
    // floor director's countdown hand, lower left
    hitFlash(t, B(28), .2, 1);
    chyron('CHANNEL 89 ACTION NEWS', 'A SPECIAL REPORT', { k: clamp((b - 29) / .8), style: 'news', size: 50 });
    theme(t, B(18));
  }

  // ---------- b32–: two-shot, name supers ----------
  function two(t, b) {
    const k = ease((b - 32) / 3.5), down = clamp((b - 34) / .4);
    anchorShot(t, {
      who: 'two', shuffle: 1 - down, talk: 0, cam: { x: 960, y: lerp(520, 500, k), zoom: lerp(1, 1.08, k) },
      clawd: { lookX: b < 34 ? -.2 : 0, lookY: b < 34 ? .7 : 0, mouth: b > 34.4 ? 'smile' : 'none' },
      val: { lookX: b < 34 ? .3 : 0, lookY: b < 34 ? .6 : 0, mouth: 'smile', eyes: 'open' },
    });
    liveBug(96, 70, { k: clamp((b - 32) / .3) });
    chyron('CLAWD', 'ANCHOR', { k: clamp((b - 32.3) / .5), size: 56, x: 170 });
    chyron('VAL LOSS', 'CO-ANCHOR', { k: clamp((b - 32.8) / .5), size: 56, x: 1080, w: 420 });
    hitFlash(t, B(32), .1, .4);
    if (b < 34.6) theme(t, B(18));
  }

  section('intro', (p, lt, d, t) => {
    hideCaption();
    const b = bpOf(t);
    if (b < 4) return tapeStart(t, b);
    if (b < 12) return bars(t, b);
    if (b < 18) return leader(t, b);
    if (b < 24) return newsOpen(t, b);
    if (b < 28) return title(t, b);
    if (b < 32) return wide(t, b);
    return two(t, b);
  });
})();

;
// ---- styles/newscast/ch/c02_v1.js ----
// c02_v1 — Verse 1: 2017 → Oct 2024, the first seven years in sixteen headlines. Every line is a different kind of news segment,
// and consecutive shots flip dominant colour: blue set / amber / dusk / chalkboard green / night / pink / field green / alert red /
// blue set / grey board / street teal / EU blue-gold / stand-by red / drape blue / Nobel gold / CGI black.
(() => {
  // lt of the k-th beat at/after the window start (lines start on the beat or on the "and" before it)
  const bt = (t, lt, k = 0) => onBeat(0, Math.ceil(bpOf(t - lt) - .02) + k) - (t - lt);
  const flash = (lt, t0, dur = .1, a = .6, col = '255 255 255') => { const k = (lt - t0) / dur; if (k >= 0 && k < 1) { ctx.fillStyle = `rgb(${col} / ${a * (1 - k)})`; ctx.fillRect(-200, -200, W + 400, H + 400); } };
  const shake = (t, lt, t0, dur = .25, amt = 16) => { const k = (lt - t0) / dur; return k >= 0 && k < 1 ? shakeXY(t, amt * (1 - k)) : [0, 0]; };
  const rays = (cx, cy, n, col, rot = 0, R = 2600) => { ctx.fillStyle = col; ctx.beginPath(); for (let i = 0; i < n; i++) { const a0 = rot + i / n * TAU, a1 = a0 + TAU / n / 2; ctx.moveTo(cx, cy); ctx.lineTo(cx + Math.cos(a0) * R, cy + Math.sin(a0) * R); ctx.lineTo(cx + Math.cos(a1) * R, cy + Math.sin(a1) * R); ctx.closePath(); } ctx.fill(); };
  const eyeAt = (x, y, s, sd, o = {}) => [x + sd * .47 * s + (o.lookX ?? 0) * .12 * s, y - 9.62 * s + (o.lookY ?? 0) * .12 * s];
  // a clean gold medal on a ribbon; (x, y) = medal centre, r radius
  function goldMedal(x, y, r, o = {}) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(o.rot ?? 0);
    if (o.ribbon !== false) { poly([[-r * .7, -r * 3.2], [-r * .25, -r * .8], [r * .25, -r * .8], [r * .7, -r * 3.2], [r * .25, -r * 3.2], [0, -r * 1.6], [-r * .25, -r * 3.2]]); paint(o.ribbonCol ?? NP.blue, NP.ink, 3); }
    ell(0, 0, r, r); paint(lg(0, -r, 0, r, [[0, '#FFF1A8'], [.45, '#F4B62A'], [1, '#9A6408']]), NP.ink, 4);
    ell(0, 0, r * .72, r * .72); paint(null, 'rgb(120 70 0 / .6)', 3);
    if (o.text) txt(o.text, 0, 2, r * .55, '#6A4200', { font: 'archivo', maxW: r * 1.3 });
    ctx.restore();
    glint(x - r * .45, y - r * .5, r * 1.1 * (o.glint ?? 1), o.glint ?? 1);
  }

  // =====================================================================================
  // V1.1 First, "Attention" lit the fuse — Clawd reads the story; the OTS box is the paper strapped to dynamite, fuse fizzing.
  function dynamiteOTS(w, h, t, lt, d) {
    vFill('#7A0E18', '#1C0206'); rays(w / 2, h * .45, 14, 'rgb(255 190 90 / .08)', t * .3);
    const sy = h * .56;
    // three sticks, taped
    for (let i = 0; i < 3; i++) {
      const y = sy + i * 40;
      rrect(w / 2 - 190, y, 380, 38, 19); paint(lg(0, y, 0, y + 38, [[0, '#FF6A5A'], [.4, '#D8262F'], [1, '#7A0A10']]), NP.ink, 3);
      txt('TNT', w / 2 + 120, y + 20, 22, 'rgb(255 255 255 / .75)', { font: 'archivo' });
    }
    for (const bx of [-110, 60]) { ctx.fillStyle = '#1A1A1A'; ctx.fillRect(w / 2 + bx, sy - 4, 26, 128); }
    // the paper, taped on
    ctx.save(); ctx.translate(w / 2 - 10, h * .31); ctx.rotate(-.045 + Math.sin(t * 3) * .006); ctx.scale(1.22, 1.22);
    rrect(-170, -112, 340, 214, 3); paint('#FBFAF2', NP.ink, 3);
    txt('Attention Is All', -8, -76, 34, NP.ink, { font: 'abril' }); txt('You Need', -8, -40, 34, NP.ink, { font: 'abril' });
    txt('Vaswani et al.  ·  2017', -8, -10, 16, '#555', { font: 'courier' });
    ctx.fillStyle = 'rgb(20 20 30 / .45)'; for (let r = 0; r < 5; r++) ctx.fillRect(-148, 12 + r * 16, r % 3 === 2 ? 120 : 200, 5);
    for (let k = 0; k < 3; k++) { rrect(78, 70 - k * 26, 70, 18, 3); paint(['#F7D6A0', '#C9E4F7', '#D8F0C8'][k], NP.ink, 1.5); }
    ctx.restore();
    tape(w / 2 - 205, h * .31 - 128, 90, -.5, { seed: 71, h: 26 }); tape(w / 2 + 185, h * .31 - 126, 90, .45, { seed: 72, h: 26 });
    // the fuse, burning back toward the sticks
    const fuse = []; for (let i = 0; i <= 24; i++) { const u = i / 24; fuse.push([w / 2 + 190 + u * 110 + Math.sin(u * 7) * 18, sy + 58 - u * 300 - Math.sin(u * 3) * 40]); }
    const left = 1 - .75 * clamp(lt / d), P = partial(fuse, left);
    ctx.beginPath(); P.forEach(([a, b], i) => i ? ctx.lineTo(a, b) : ctx.moveTo(a, b)); paint(null, '#E8D7A0', 7);
    const [fx, fy] = P.at(-1), f = Math.floor(t * 24);
    for (let i = 0; i < 9; i++) { const a = hash2(f, i) * TAU, L = 18 + hash2(f, i + 20) * 46; ctx.beginPath(); ctx.moveTo(fx, fy); ctx.lineTo(fx + Math.cos(a) * L, fy + Math.sin(a) * L); paint(null, i % 2 ? NP.gold : '#FFF6C0', 3); }
    glint(fx, fy, 70 + 20 * Math.sin(t * 40), 1, '#FFE9A0');
  }
  line('V1', 1, (p, lt, d, t) => {
    const look = clamp((lt - .72) / .15);
    anchorShot(t, {
      who: 'clawd', push: p,
      ots: { draw: (w, h) => dynamiteOTS(w, h, t, lt, d), label: 'TRANSFORMER', k: inK(lt, .02, .22) },
      clawd: { lookX: look * .9, lookY: -look * .15, eyes: look > .5 ? 'worried' : 'normal', sweat: look > .5 },
    });
    chyron('TRANSFORMER UNVEILED', 'GOOGLE RESEARCHERS · JUNE 2017', { k: chyK(lt) });
  });

  // =====================================================================================
  // V1.2 Scaling laws you can't refuse — an anonymous source in silhouette (voice altered) holds up a ruler-straight log-log chart.
  // The rose in his lapel and the fedora say it's an offer you can't refuse.
  line('V1', 2, (p, lt, d, t) => {
    const tap = pulse(t, 7);
    fillAll('#140906');
    // the backlit window with venetian blinds
    const wx = 1040, wy = 90, ww = 760, wh = 640;
    ctx.fillStyle = rg(wx + ww * .6, wy + wh * .4, 40, 700, [[0, '#FFE2A0'], [.6, '#E89A3A'], [1, '#7A3A10']]); ctx.fillRect(wx, wy, ww, wh);
    ctx.fillStyle = '#1E0E08'; for (let i = 0; i < 16; i++) ctx.fillRect(wx, wy + 22 + i * 40, ww, 17);
    ctx.lineWidth = 14; ctx.strokeStyle = '#2A140A'; ctx.strokeRect(wx, wy, ww, wh);
    ctx.save(); ctx.globalCompositeOperation = 'screen';
    for (let i = 0; i < 9; i++) { const y0 = wy + 30 + i * 70; ctx.fillStyle = `rgb(255 170 80 / ${.05 + .02 * Math.sin(t * 3 + i)})`; poly([[wx, y0], [wx, y0 + 22], [-200, y0 + 520], [-200, y0 + 470]]); ctx.fill(); }
    ctx.restore();
    // the source: a rim-lit silhouette in a fedora
    const X = 700, Y = 1190, S = 66, hand = [X + 3.3 * S, Y - 8.4 * S];
    const pose = { hat: 'fedora', top: 'suit', hair: 'short', legs: false, shadow: false, reachR: [3.3, -8.4], reachL: [-2.2, -3.2], dy: Math.sin(t * 2) * .03 };
    toon(X + 6, Y - 5, S * 1.012, { ...pose, sil: '#FFB05A' });
    toon(X, Y, S, { ...pose, sil: '#0A0506' });
    // rose, the only colour on him
    const rx = X + .8 * S, ry = Y - 7.25 * S;
    ctx.beginPath(); ctx.moveTo(rx, ry); ctx.lineTo(rx + 8, ry + 30); paint(null, '#2E6B2A', 5);
    for (let i = 0; i < 5; i++) { const a = i / 5 * TAU; ell(rx + Math.cos(a) * 9, ry + Math.sin(a) * 9, 11, 11); paint('#C8141E'); } ell(rx, ry, 8, 8); paint('#8A0A10');
    // cigar ember and smoke
    const cx = X + .45 * S, cy = Y - 8.8 * S;
    ctx.beginPath(); ctx.moveTo(cx - 30, cy + 4); ctx.lineTo(cx + 22, cy - 2); paint(null, '#2A1A10', 11);
    glint(cx + 24, cy - 2, 26 + 10 * Math.sin(t * 9), .9, '#FF8A30');
    ctx.save(); ctx.globalAlpha = .18; for (let i = 0; i < 3; i++) { const ph = frac(t * .5 + i / 3); ctx.beginPath(); for (let j = 0; j <= 10; j++) { const u = j / 10; ctx.lineTo(cx + 26 + Math.sin(u * 6 + t * 2 + i) * 22 * u - u * 30, cy - 10 - u * 170 * (.4 + ph)); } paint(null, '#E8D8C8', 16 - i * 4); } ctx.restore();
    // the chart card
    ctx.save(); ctx.translate(hand[0] + 222, hand[1] - 60); ctx.rotate(-.04 - tap * .025);
    rrect(-230, -175, 460, 350, 6); paint('#F8F4EA', NP.ink, 4);
    txt('SCALING LAWS', 0, -140, 36, NP.ink, { font: 'archivo', spacing: 1 });
    const gx = -170, gy = -105, gw = 360, gh = 230;
    ctx.strokeStyle = 'rgb(40 90 200 / .35)'; ctx.lineWidth = 1.5; ctx.beginPath();
    for (let dd = 0; dd < 3; dd++) for (let m = 1; m < 10; m++) { const u = (dd + Math.log10(m)) / 3; ctx.moveTo(gx + u * gw, gy); ctx.lineTo(gx + u * gw, gy + gh); ctx.moveTo(gx, gy + gh - u * gh); ctx.lineTo(gx + gw, gy + gh - u * gh); }
    ctx.stroke();
    ctx.beginPath(); ctx.moveTo(gx, gy); ctx.lineTo(gx, gy + gh); ctx.lineTo(gx + gw, gy + gh); paint(null, NP.ink, 4);
    const k = clamp(lt / .5);
    ctx.beginPath(); ctx.moveTo(gx + 10, gy + 20); ctx.lineTo(gx + 10 + (gw - 20) * k, gy + 20 + (gh - 40) * k); paint(null, NP.red, 6);
    for (let i = 0; i < 7; i++) { const u = i / 6; if (u > k + .05) continue; ell(gx + 10 + (gw - 20) * u, gy + 20 + (gh - 40) * u + (hash(i + 3) - .5) * 6, 8); paint(NP.blue, NP.ink, 2); }
    txt('LOSS', gx - 22, gy + gh / 2, 20, NP.ink, { font: 'archivo', rot: -TAU / 4 });
    txt('COMPUTE →', gx + gw / 2, gy + gh + 24, 20, NP.ink, { font: 'archivo' });
    ctx.restore();
    // the anonymous-source bug: a VOICE ALTERED oscilloscope
    rrect(90, 64, 430, 80, 8); paint('rgb(0 0 0 / .7)', '#666', 2);
    pixelText('VOICE ALTERED', 110, 84, 4, NP.phosphor, { edge: null });
    ctx.beginPath(); for (let i = 0; i <= 60; i++) { const xx = 390 + i * 2, amp = 18 * (.3 + .7 * talk(t)); ctx.lineTo(xx, 104 + Math.sin(i * .9 + t * 40) * amp * Math.sin(i / 60 * Math.PI)); } paint(null, NP.phosphor, 2.5);
    chyron('SCALING LAWS', 'SOURCE ASKED NOT TO BE IDENTIFIED', { k: chyK(lt) });
  });

  // =====================================================================================
  // V1.3 Gwern said "stack the compute high" — LIVE at dusk: a hooded, mosaic-faced GWERN points up while GPU crates land on a tower,
  // one per beat; the camera tilts up with it. Reporter RANDI SEED looks up, mic in hand.
  function crate(x, y, w, h, rot = 0, label = 'GPU') {
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot);
    ctx.fillStyle = 'rgb(0 0 0 / .3)'; ctx.fillRect(-w / 2 + 8, -h + 8, w, h);
    rrect(-w / 2, -h, w, h, 4); paint(lg(0, -h, 0, 0, [[0, '#D8A060'], [1, '#A8723A']]), NP.ink, 4);
    ctx.fillStyle = 'rgb(90 50 20 / .5)'; for (let i = 1; i < 4; i++) ctx.fillRect(-w / 2, -h + i * h / 4 - 2, w, 3);
    ctx.lineWidth = 10; ctx.strokeStyle = '#8A5A2A'; ctx.strokeRect(-w / 2 + 5, -h + 5, w - 10, h - 10);
    ctx.beginPath(); ctx.moveTo(-w / 2 + 8, -h + 8); ctx.lineTo(w / 2 - 8, -8); paint(null, '#8A5A2A', 9);
    txt(label, 0, -h / 2 + 2, h * .42, '#2A160A', { font: 'mono', alpha: .85 });
    ctx.restore();
  }
  line('V1', 3, (p, lt, d, t) => {
    const b = bpOf(t - lt), nb = [0, 1, 2, 3, 4].filter(k => bt(t, lt, k) <= lt + .3).length;
    const tilt = ease(lt / d) * 270, camY = 540 - tilt;
    const scene = (withPeople = true) => {
      camBegin(960, camY, 1);
      vFill('#2A1850', '#F08A40', -600, -700, W + 1200, 1500);
      ell(1500, 640, 90, 90); paint('#FFD27A');
      // distant skyline + fence
      ctx.fillStyle = '#3A2450'; for (let i = 0; i < 14; i++) { const bw = 90 + hash(i + 40) * 120, bh = 80 + hash(i + 50) * 200; ctx.fillRect(i * 150 - 60, 800 - bh, bw, bh + 10); }
      vFill('#3A3040', '#1A1418', -600, 790, W + 1200, 800);
      ctx.strokeStyle = 'rgb(40 30 40 / .8)'; ctx.lineWidth = 3; ctx.beginPath(); for (let x = -600; x < W + 600; x += 40) { ctx.moveTo(x, 610); ctx.lineTo(x + 180, 800); ctx.moveTo(x + 180, 610); ctx.lineTo(x, 800); } ctx.stroke();
      ctx.fillStyle = '#2A2028'; for (let x = -600; x < W + 600; x += 360) ctx.fillRect(x, 590, 14, 220);
      // floodlight
      ctx.save(); ctx.globalCompositeOperation = 'screen'; ctx.fillStyle = 'rgb(255 240 200 / .12)'; poly([[1780, 140], [1800, 170], [900, 900], [1400, 900]]); ctx.fill(); ctx.restore();
      ctx.beginPath(); ctx.moveTo(1790, 150); ctx.lineTo(1790, 900); paint(null, '#222', 12); rrect(1745, 120, 90, 50, 8); paint('#FFF6D0', '#222', 4);
      // the tower of crates
      const base = 905, ch = 140;
      const n = 3 + nb;
      for (let i = 0; i < n; i++) {
        const land = i < 3 ? -1 : bt(t, lt, i - 3), a = lt - land;
        if (a < -.25) continue;
        const drop = a < 0 ? (1 - easeIn(1 + a / .25)) * -760 : 0, bounce = a >= 0 && a < .2 ? Math.sin(a / .2 * Math.PI) * -22 * (1 - a / .2) : 0;
        crate(1330 + (hash(i + 7) - .5) * 30, base - i * ch + drop + bounce, 250, ch, (hash(i + 3) - .5) * .05);
      }
      // hand-painted sign on the fence
      ctx.save(); ctx.translate(560, 660); ctx.rotate(-.04); rrect(-190, -60, 380, 120, 6); paint('#F2E8C8', NP.ink, 4);
      txt('THE SCALING', 0, -24, 38, NP.red, { font: 'marker' }); txt('HYPOTHESIS', 0, 22, 38, NP.ink, { font: 'marker' }); ctx.restore();
      if (withPeople) {
        toon(1000, 915, 40, { top: 'hoodie', topCol: '#3A3A52', hood: true, aR: 1.25, eR: .1, hand: 'point', aL: -1.1, eL: .5, dy: -Math.abs(Math.sin(bpOf(t) * Math.PI)) * .08 });
        toon(330, 1215, 52, { ...CAST.randi.o, legs: false, shadow: false, reachR: [1.2, -7.2], hold: micHold(.25), lookX: .7, lookY: -.9, talk: talk(t) });
      }
      camEnd();
    };
    scene();
    // identity withheld: mosaic over the hooded face
    const hy = 915 - 9.55 * 40 - camY + 540 - Math.abs(Math.sin(bpOf(t) * Math.PI)) * .08 * 40;
    mosaic(948, hy - 66, 106, 128, 18, () => scene(true));
    liveBug();
    chyron('GWERN', 'IDENTITY WITHHELD', { k: chyK(lt), style: 'live', tab: 'LIVE' });
  });

  // =====================================================================================
  // V1.4 Few-shot learners multiply — a beige-computer pupil learns 12×34 from two examples on the chalkboard… and then the
  // picture itself multiplies: DVE multi-image 1 → 2×2 → 3×3 → 4×4 → 6×6 on the beats.
  function classroom(t, lt) {
    vFill('#E8E0A8', '#C8C088');
    rrect(250, 100, 1100, 520, 10); paint('#6B4A2A', NP.ink, 5);
    rrect(275, 125, 1050, 470, 4); paint(lg(0, 125, 0, 595, [[0, '#2E5E3E'], [1, '#1E4A2E']]));
    ctx.fillStyle = 'rgb(255 255 255 / .06)'; ell(700, 300, 380, 120, -.2); ctx.fill();
    const chalk = (s, x, y, sz = 64, a = 1) => txt(s, x, y, sz, `rgb(245 245 235 / ${.9 * a})`, { font: 'marker', align: 'left' });
    chalk('FEW-SHOT:', 330, 185, 50); underline(330, 580, 222, 'rgb(245 245 235 / .8)', 5);
    chalk('3 × 4 = 12', 360, 290); chalk('7 × 8 = 56', 360, 385); chalk('12 × 34 = ?', 360, 480, 64);
    ctx.fillStyle = '#EDEDE0'; ctx.fillRect(900, 585, 60, 14);
    // clock + pennant
    ell(1560, 290, 80); paint('#FFF', NP.ink, 5); ctx.beginPath(); ctx.moveTo(1560, 290); ctx.lineTo(1560 + Math.sin(t * 6) * 60, 290 - Math.cos(t * 6) * 60); ctx.moveTo(1560, 290); ctx.lineTo(1600, 270); paint(null, NP.ink, 6);
    poly([[1450, 430], [1700, 470], [1450, 510]]); paint(NP.red, NP.ink, 3); txt('GO BITS', 1540, 472, 30, NP.white, { font: 'archivo', rot: .08 });
    // desk + pupil
    const hop = Math.abs(Math.sin(bpOf(t) * Math.PI)) * .12;
    computer(1000, 930, 44, { label: 'GPT-3', face: lt > .3 ? 'grin' : 'think', aR: 1.3, eR: .15, hand: 'open', aL: -1, eL: .6, dy: -hop, legs: false });
    rrect(700, 880, 600, 40, 6); paint('#B07A44', NP.ink, 4); ctx.fillStyle = '#6A4424'; ctx.fillRect(740, 920, 24, 160); ctx.fillRect(1236, 920, 24, 160);
    ell(1210, 862, 24, 22); paint(NP.red, NP.ink, 3);
    if (lt > .3) speech('408!', 1330, 560, { size: 90, font: 'anton', tail: [1130, 720], pop: (lt - .3) / .15 });
    if (lt > .45) { const k = backOut(clamp((lt - .45) / .15), 2.2); ctx.save(); ctx.translate(1560, 720); ctx.scale(k, k); poly(starPts(0, 0, 80, .6, 12)); paint(NP.gold, NP.ink, 5); ctx.beginPath(); ctx.moveTo(-32, 0); ctx.lineTo(-8, 26); ctx.lineTo(36, -26); paint(null, '#1A7A3A', 14); ctx.restore(); }
  }
  line('V1', 4, (p, lt, d, t) => {
    const n = lt < bt(t, lt, 1) ? 1 : lt < bt(t, lt, 2) ? 2 : lt < bt(t, lt, 3) ? 3 : lt < bt(t, lt, 4) ? 4 : 6;
    dveTiles(n, () => classroom(t, lt), { res: n > 3 ? .34 : .5 });
    const since = lt - [0, 0, bt(t, lt, 1), bt(t, lt, 2), bt(t, lt, 3), 0, bt(t, lt, 4)][n];
    if (n > 1 && since < .35) chrome('×' + n * n, W / 2, H / 2 - 40, 260 * (1 + (1 - clamp(since / .12)) * .3), { font: 'anton', style: 'gold', italic: .1, depth: 16, alpha: 1 - clamp((since - .22) / .13) });
    chyron('GPT-3: 175 BILLION PARAMETERS', 'LEARNS NEW TASKS FROM A FEW EXAMPLES', { k: chyK(lt), size: 50 });
  });

  // =====================================================================================
  // V1.5 ChatGPT, overnight — SKY 89 over the city at night: every window lights up with a chat bubble, the user counter spins.
  function city(t, lt, layer) {
    const n = [16, 12, 9][layer], base = [700, 820, 960][layer], col = ['#1A2050', '#10163C', '#080C26'][layer];
    for (let i = 0; i < n; i++) {
      const bw = [130, 170, 220][layer] + hash2(i, layer + 1) * 90, x = i / n * 2400 - 240 + hash2(i, layer + 5) * 60, bh = [260, 380, 520][layer] + hash2(i, layer + 9) * 260;
      ctx.fillStyle = col; ctx.fillRect(x, base - bh, bw, bh + 400);
      if (layer === 2 && i === 4) continue;
      const cols = Math.floor(bw / 34), rows = Math.floor(bh / 44);
      for (let r = 0; r < rows; r++) for (let c = 0; c < cols; c++) {
        const wx = x + 12 + c * 34, wy = base - bh + 18 + r * 44, h = hash2(i * 97 + r, c + layer * 13);
        const on = h > .25 && (wx / W) < lt * 2.4 - .15 + h * .3;
        ctx.fillStyle = on ? (h > .8 ? '#7CFFB0' : h > .55 ? '#FFE9A0' : '#FFD27A') : '#22284A'; ctx.fillRect(wx, wy, 18, 26);
      }
    }
  }
  line('V1', 5, (p, lt, d, t) => {
    camBegin(960 + Math.sin(t * .7) * 30, 540 + Math.sin(t * 1.1) * 12, 1.04 + p * .05, Math.sin(t * .5) * .015);
    vFill('#02031A', '#1A2A6A', -600, -600, W + 1200, 1500);
    for (let i = 0; i < 80; i++) { ctx.fillStyle = `rgb(255 255 255 / ${.3 + .5 * hash(i + 3)})`; ctx.fillRect(hash(i) * W, hash(i + 99) * 500, 3, 3); }
    wwMoon(330, 380);
    city(t, lt, 0); city(t, lt, 1);
    // the big tower with a rooftop chat bubble sign
    const tx = 1180, ty = 520;
    ctx.fillStyle = '#060A20'; ctx.fillRect(tx - 150, ty, 300, 900);
    for (let r = 0; r < 14; r++) for (let c = 0; c < 6; c++) { const h = hash2(r + 40, c); ctx.fillStyle = h > .2 && lt > .1 + r * .02 ? '#9CFFC0' : '#1C2244'; ctx.fillRect(tx - 130 + c * 44, ty + 30 + r * 52, 26, 32); }
    const on = clamp((lt - bt(t, lt)) / .08);
    ctx.save(); ctx.translate(tx, ty - 130); ctx.scale(lerp(.6, 1, backOut(on)), lerp(.6, 1, backOut(on)));
    ctx.fillStyle = `rgb(120 255 170 / ${.25 * on})`; ell(0, 0, 260, 150); ctx.fill();
    rrect(-190, -95, 380, 170, 60); paint(on ? '#F4FFF6' : '#30364A', on ? '#2EBD5B' : '#111', 10);
    poly([[-60, 70], [-110, 130], [0, 72]]); paint(on ? '#F4FFF6' : '#30364A', on ? '#2EBD5B' : '#111', 8);
    for (let i = 0; i < 3; i++) { ell(-80 + i * 80, -8 - (on ? Math.max(0, Math.sin(t * 12 - i)) * 14 : 0), 22); paint(on ? '#1E8A48' : '#1A1A1A'); }
    ctx.restore();
    city(t, lt, 2);
    // chopper searchlight
    ctx.save(); ctx.globalCompositeOperation = 'screen'; const sa = Math.sin(t * 1.3) * .35;
    ctx.fillStyle = 'rgb(200 220 255 / .12)'; poly([[1900, -80], [1960, -40], [900 + sa * 900, 1200], [500 + sa * 900, 1200]]); ctx.fill(); ctx.restore();
    camEnd();
    // helicopter-camera overlay
    ctx.strokeStyle = 'rgb(255 255 255 / .8)'; ctx.lineWidth = 4;
    for (const [x, y, sx, sy] of [[520, 270, 1, 1], [1400, 270, -1, 1], [520, 760, 1, -1], [1400, 760, -1, -1]]) { ctx.beginPath(); ctx.moveTo(x, y + sy * 60); ctx.lineTo(x, y); ctx.lineTo(x + sx * 60, y); ctx.stroke(); }
    ctx.beginPath(); ctx.moveTo(930, 515); ctx.lineTo(990, 515); ctx.moveTo(960, 485); ctx.lineTo(960, 545); ctx.stroke();
    pixelText(`ALT ${1200 + Math.round(Math.sin(t) * 20)} FT  HDG 270`, 96, 250, 4, NP.white);
    liveBug(96, 70, { label: 'SKY 89', col: NP.blue });
    // user counter
    const u = Math.round(easeOut(clamp(lt / .75)) ** 1.5 * 1000000), us = u.toLocaleString('en-US');
    rrect(620, 70, 680, 150, 10); paint('rgb(0 0 0 / .72)', NP.phosphor, 3);
    pixelText('USERS', 960, 86, 4, NP.phosphor, { align: 'center', edge: null });
    pixelText(us, 960, 128, 9, u >= 1000000 && frac(t * 4) < .5 ? NP.gold : NP.white, { align: 'center', edge: null });
    chyron('CHATGPT LAUNCHES', '1 MILLION USERS IN 5 DAYS', { k: chyK(lt) });
  });
  function wwMoon(x, y) { ctx.fillStyle = 'rgb(255 250 220 / .15)'; ell(x, y, 120, 120); ctx.fill(); ell(x, y, 70, 70); paint('#FFF4D0'); ell(x - 18, y - 12, 14, 12); paint('rgb(200 190 160 / .5)'); ell(x + 22, y + 18, 10, 9); paint('rgb(200 190 160 / .5)'); }

  // =====================================================================================
  // V1.6 Sydney's chats gave Roose a fright — split-screen satellite interview. SYDNEY (a pink-screened computer) blows kisses;
  // hearts fly across the split into KEVIN's box; the satellite delay passes and his hair stands straight up.
  line('V1', 6, (p, lt, d, t) => {
    vFill('#3A1266', '#0C0420');
    ctx.fillStyle = 'rgb(255 255 255 / .05)'; for (let y = 0; y < H; y += 14) ctx.fillRect(0, y, W, 6);
    txt('LIVE VIA SATELLITE', W / 2, 86, 44, NP.white, { font: 'archivo', spacing: 8, alpha: frac(t * 1.2) < .8 ? 1 : .4 });
    const fright = clamp((lt - bt(t, lt, 1) + .05) / .12), tr = fright > 0 ? shakeXY(t, 5 * fright) : [0, 0];
    otsBox(110, 140, 820, 640, (w, h) => {
      vFill('#FF7AC0', '#8A1A5A'); rays(w / 2, h * .45, 16, 'rgb(255 255 255 / .1)', -t * .4);
      for (let i = 0; i < 8; i++) { const hx = (hash(i + 5) * w + t * 40 * (i % 2 ? 1 : -1)) % w, hy = (hash(i + 9) * h - t * 90 + h * 4) % h; poly(heartPts(hx, hy, 18 + hash(i) * 14, 20)); paint('rgb(255 220 240 / .5)'); }
      computer(w / 2, h - 60, 44, { case: '#3A2A40', screen: '#3A0A2A', glow: '#FFB0DA', face: frac(lt * 1.6) < .5 ? 'heart' : undefined, text: frac(lt * 1.6) < .5 ? undefined : 'I LOVE\nYOU', aR: .9 + Math.sin(t * 8) * .2, eR: 1.4, hand: 'open', aL: -.8, dy: Math.sin(t * 6) * .05, legs: false });
      pixelText('REDMOND', 20, 18, 4, NP.white);
    }, { k: inK(lt, 0, .18), label: "'SYDNEY' · BING CHAT", labelCol: NP.magenta, tilt: .4 });
    otsBox(990, 140, 820, 640, (w, h) => {
      vFill('#9AB8D8', '#3A5A7A');
      ctx.fillStyle = '#2A3A52'; for (let i = 0; i < 7; i++) ctx.fillRect(i * 130 - 20, h * .55 - hash(i + 1) * 180, 100, 400);
      ctx.save(); ctx.translate(tr[0], tr[1]);
      toon(w / 2, h + 190, 50, { hair: fright > .5 ? 'spiky' : 'short', hairCol: NHAIR.brown, glasses: 'square', top: 'sweater', topCol: '#7A6A5A', legs: false, shadow: false,
        eyes: fright > .3 ? 'wide' : 'open', mouth: fright > .3 ? 'scream' : 'smile', brows: fright > .3 ? 'up' : 'flat', sweat: fright > .5,
        reachL: [-1.6, -6.2], reachR: [1.6, -6.3], dy: -fright * .1 });
      // clutched newspaper
      rrect(w / 2 - 150, h + 190 - 6.9 * 50, 300, 190, 2); paint('#EDE8DA', NP.ink, 3); txt('The Times', w / 2, h + 190 - 6.9 * 50 + 30, 30, NP.ink, { font: 'fraktur' });
      ctx.fillStyle = 'rgb(20 20 30 / .5)'; for (let r = 0; r < 5; r++) ctx.fillRect(w / 2 - 130, h + 190 - 6.9 * 50 + 60 + r * 20, 260, 6);
      ctx.restore();
      pixelText('NEW YORK', 20, 18, 4, NP.white);
    }, { k: inK(lt, .06, .18), label: 'KEVIN ROOSE · NEW YORK TIMES', labelCol: NP.blue, tilt: -.4 });
    // hearts cross the split
    for (let i = 0; i < 4; i++) { const u = clamp((lt - .12 - i * .16) / .5); if (u <= 0 || u >= 1) continue; const hx = lerp(700, 1350, u), hy = 420 - Math.sin(u * Math.PI) * 160 + i * 30; poly(heartPts(hx, hy, 30, 24)); paint(NP.red, NP.ink, 3); }
  });

  // =====================================================================================
  // V1.7 Six-month pause went nowhere fast — the open letter slaps PAUSE; the VCR obediently pauses (OSD, noise bar, jitter)…
  // except the race doesn't: the frozen stadium stands still while the lab runners sprint right out of the paused frame.
  line('V1', 7, (p, lt, d, t) => {
    const press = bt(t, lt), paused = lt > press, frz = paused ? (t - lt) + press : t, jy = paused ? (hash(Math.floor(t * 15)) - .5) * 6 : 0;
    ctx.save(); ctx.translate(0, jy);
    // stadium (frozen once paused)
    vFill('#1E3A6A', '#4A7AB0', -100, -100, W + 200, 520);
    for (let r = 0; r < 6; r++) for (let i = 0; i < 48; i++) { const x = i * 42 + (r % 2) * 20 - 20, y = 120 + r * 50 - (paused ? 0 : Math.abs(Math.sin(frz * 8 + i + r)) * 8); ell(x, y, 15, 17); paint(['#E84A4A', '#F4D24A', '#FFFFFF', '#4A8AE8', '#2EBD5B'][(i * 7 + r * 3) % 5]); }
    ctx.fillStyle = '#18401E'; ctx.fillRect(-100, 420, W + 200, 60); txt('THE AI RACE', 960, 450, 44, NP.white, { font: 'bungee', spacing: 6 });
    vFill('#C8422E', '#A8321E', -100, 480, W + 200, 700);
    const off = (frz * 900) % 240;
    for (let l = 0; l < 4; l++) { const y = 540 + l * 120; ctx.fillStyle = 'rgb(255 255 255 / .85)'; ctx.fillRect(-100, y, W + 200, 5); for (let x = -off; x < W; x += 240) ctx.fillRect(x, y + 58, 90, 5); }
    // the runners keep going
    const labs = [['GPT-4', NP.beige], ['CLAUDE', '#E8C8B0'], ['BARD', '#C8D8E8']];
    labs.forEach(([nm, cs], i) => {
      const run = t * 3.2 + i * .33, x = 820 + i * 330 + (paused ? (lt - press) * 700 : 0), y = 640 + i * 120;
      computer(x, y, 32, { label: nm, case: cs, face: 'angry', walk: run, aL: Math.sin(run * TAU) * .8 - .3, aR: -Math.sin(run * TAU) * .8 - .3, eL: 1.2, eR: 1.2, rot: .12, dy: -Math.abs(Math.sin(run * Math.PI * 2)) * .3 });
    });
    ctx.restore();
    // the open letter and its giant PAUSE button
    ctx.save(); ctx.translate(290, 740);
    rrect(-170, -330, 340, 230, 6); paint('#FBF8EE', NP.ink, 4);
    txt('PAUSE GIANT', 0, -290, 34, NP.ink, { font: 'archivo' }); txt('AI EXPERIMENTS', 0, -252, 34, NP.ink, { font: 'archivo' });
    for (let r = 0; r < 4; r++) { ctx.beginPath(); for (let k = 0; k <= 14; k++) ctx.lineTo(-140 + k * 20, -200 + r * 26 + Math.sin(k * 2.3 + r) * 6); paint(null, '#2A3A8A', 3); }
    txt('+30,000 SIGNATURES', 0, -115, 20, NP.red, { font: 'archivo' });
    const pk = clamp((lt - press + .08) / .08);
    rrect(-120, -40, 240, 70, 12); paint('#333', NP.ink, 4);
    ell(0, -40 + pk * 10, 100, 34); paint(NP.red, NP.ink, 4); ctx.fillStyle = NP.white; ctx.fillRect(-22, -58 + pk * 10, 14, 34); ctx.fillRect(8, -58 + pk * 10, 14, 34);
    const hy = lerp(-260, -60, easeIn(clamp((lt - press + .16) / .16))) - (paused ? Math.min(1, (lt - press) * 3) * 80 : 0);
    ctx.save(); ctx.translate(20, hy); ctx.rotate(-.3);
    rrect(-40, -220, 80, 180, 20); paint(NSKIN[0], NP.ink, 4); rrect(-12, -60, 24, 70, 12); paint(NSKIN[0], NP.ink, 4); rrect(-50, -300, 100, 90, 10); paint('#2A3A8A', NP.ink, 4);
    ctx.restore();
    ctx.restore();
    if (paused) { vcrMode('PAUSE'); tapeFX({ pauseBar: 1, pauseY: .6 }); if (frac((lt - press) * 2.5) < .7) pixelText('PAUSE ❚', W / 2 + 60, 250, 13, NP.white, { align: 'center', shadow: [.4, .4] }); }
    chyron('OPEN LETTER: PAUSE AI', 'SIX MONTHS? NO LAB PAUSED', { k: chyK(lt), style: 'sports' });
  });

  // =====================================================================================
  // V1.8 Eliezer's "shut-it-down" blast — the station cuts to an EMERGENCY BULLETIN: SHUT IT ALL DOWN, with ELIEZER (fedora)
  // blasting a megaphone; the whole frame kicks on the beat.
  line('V1', 8, (p, lt, d, t) => {
    const b0 = bt(t, lt), [sx, sy] = shake(t, lt, b0, .35, 22), strobe = frac(t * 4) < .5;
    ctx.save(); ctx.translate(sx, sy);
    fillAll('#0A0000');
    ctx.fillStyle = strobe ? '#6A0008' : '#2A0004'; ctx.fillRect(-100, -100, W + 200, H + 200);
    ctx.fillStyle = 'rgb(0 0 0 / .35)'; for (let i = -10; i < 40; i++) poly([[i * 90, -100], [i * 90 + 45, -100], [i * 90 - 400, H + 100], [i * 90 - 445, H + 100]]), ctx.fill();
    rrect(90, 90, W - 180, 110, 6); paint('#F2F2F2');
    txt('EMERGENCY BULLETIN', W / 2 - 60, 147, 74, NP.redDk, { font: 'archivo', spacing: 6 });
    // siren
    const sa = t * 9; ctx.save(); ctx.translate(200, 146); ell(0, 0, 44, 44); paint(NP.red, NP.ink, 4); ctx.globalCompositeOperation = 'screen'; ctx.fillStyle = 'rgb(255 80 60 / .35)'; poly([[0, 0], [Math.cos(sa) * 700, Math.sin(sa) * 700 - 80], [Math.cos(sa) * 700, Math.sin(sa) * 700 + 80]]); ctx.fill(); ctx.restore();
    // the headline slams on the beat
    const k = clamp((lt - b0 + .04) / .12), sc = lerp(1.9, 1, easeOut(k));
    if (k > 0) {
      ctx.save(); ctx.translate(1180, 470); ctx.scale(sc, sc); ctx.globalAlpha = clamp(k * 2);
      chrome('SHUT IT', 0, -80, 170, { font: 'anton', style: 'white', depth: 12, spacing: 6 });
      chrome('ALL DOWN', 0, 110, 170, { font: 'anton', style: 'red', depth: 12, spacing: 6 });
      ctx.restore();
    }
    // Eliezer and the megaphone, with sound rings
    otsBox(110, 250, 560, 470, (w, h) => {
      vFill('#E8D8B0', '#A89060');
      toon(w / 2 - 40, h + 230, 46, { hat: 'fedora', hatCol: '#2A2630', beard: true, hairCol: '#5A3A24', top: 'suit', topCol: '#3A3448', tie: NP.red, legs: false, shadow: false, eyes: 'angry', mouth: 'scream', reachR: [2.4, -9.3], aL: -1.2 });
      ctx.save(); ctx.translate(w / 2 + 90, h + 230 - 9.2 * 46); ctx.rotate(-.12);
      poly([[0, -26], [150, -80], [150, 80], [0, 26]]); paint(lg(0, -80, 0, 80, [[0, '#FFF'], [1, '#B8B8C0']]), NP.ink, 4); rrect(-30, -30, 34, 60, 6); paint('#444', NP.ink, 3);
      ctx.restore();
      for (let i = 0; i < 3; i++) { const ph = frac(t * 3 + i / 3); ctx.beginPath(); ctx.arc(w / 2 + 240, h + 230 - 9.2 * 46 - 18, 40 + ph * 240, -.6, .6); paint(null, `rgb(200 20 30 / ${1 - ph})`, 8); }
    }, { k: inK(lt, 0, .16), label: 'ELIEZER YUDKOWSKY · OP-ED', labelCol: NP.redDk, border: '#FFDDDD' });
    // attention-signal oscilloscope
    rrect(760, 700, 1060, 86, 8); paint('#000', '#6A0A10', 3);
    ctx.beginPath(); for (let i = 0; i <= 200; i++) { const x = 780 + i * 5.1; ctx.lineTo(x, 743 + Math.sin(i * .55 + t * 60) * 26 * Math.sin(i * .09 + t * 3)); } paint(null, '#FF4040', 4);
    ctx.restore();
    flash(lt, b0, .1, .7, '255 60 50');
  });

  // =====================================================================================
  // V1.9 Sam got fired, then rehired — VAL reads it; the OTS box is a revolving door that flings SAM out on the beat and spins him
  // straight back in; the chyron flips from ALTMAN FIRED to ALTMAN REHIRED, and Val does a double take.
  function revolvingDoor(w, h, t, lt, tOut, tBack) {
    vFill('#C9D2E2', '#7A88A8');
    ctx.fillStyle = '#AAB4C8'; for (let i = 0; i < 6; i++) ctx.fillRect(i * 130 - 20, 0, 60, h);
    rrect(40, 30, w - 80, 70, 4); paint('#2A3048'); txt('O P E N A I', w / 2, 67, 40, '#D8DCE8', { font: 'archivo', spacing: 4 });
    const cx = w / 2, fy = h - 64, R = 200, top = 116, spin = lt * 10;
    ell(cx, fy, R + 20, 26); paint('#5A6278', NP.ink, 3);
    ctx.fillStyle = 'rgb(180 210 240 / .35)'; ctx.fillRect(cx - R, top, R * 2, fy - top);
    const wings = [0, 1, 2, 3].map(i => spin + i * Math.PI / 2);
    const drawWing = a => { const x = cx + Math.sin(a) * R, z = Math.cos(a); ctx.beginPath(); ctx.moveTo(cx, top); ctx.lineTo(x, top); ctx.lineTo(x, fy); ctx.lineTo(cx, fy); ctx.closePath(); paint(`rgb(200 225 255 / ${.25 + .2 * z})`, '#3A4058', 5); };
    wings.filter(a => Math.cos(a) < 0).forEach(drawWing);
    // Sam
    let sx, sy = fy, rot = 0, sc = 1, face = { eyes: 'open', mouth: 'smile' };
    if (lt < tOut) { const a = spin + Math.PI / 4; sx = cx + Math.sin(a) * R * .55; sc = 1 + Math.cos(a) * .08; }
    else if (lt < tBack) { const u = lt - tOut; sx = cx - u * 2400; sy = fy - Math.sin(clamp(u / .4) * Math.PI) * 140; rot = -u * 14; face = { eyes: 'x', mouth: 'O' }; }
    else { const u = clamp((lt - tBack) / .3); sx = lerp(-120, cx, easeOut(u)); face = { eyes: 'happy', mouth: 'grin' }; if (u >= 1) { const a = spin + Math.PI / 4; sx = cx + Math.sin(a) * R * .55 * clamp((lt - tBack - .3) * 3); } }
    ctx.save(); ctx.translate(sx, sy); ctx.rotate(rot); ctx.scale(sc, sc);
    toon(0, 0, 32, { hair: 'short', hairCol: NHAIR.brown, top: 'sweater', topCol: '#6A7A8A', skin: 0, ...face, walk: lt >= tBack ? lt * 3 : undefined, aL: lt >= tOut && lt < tBack ? 1.2 : -1.3, aR: lt >= tOut && lt < tBack ? 1.2 : -1.3, tag: 'SAM' });
    ctx.restore();
    wings.filter(a => Math.cos(a) >= 0).forEach(drawWing);
    ctx.beginPath(); ctx.moveTo(cx, top); ctx.lineTo(cx, fy); paint(null, '#3A4058', 8);
    ell(cx, top, R + 20, 22); paint('#5A6278', NP.ink, 3);
  }
  line('V1', 9, (p, lt, d, t) => {
    const tOut = bt(t, lt), tBack = bt(t, lt, 2), back = lt >= tBack, dt = lt >= tBack && lt < tBack + .35;
    anchorShot(t, {
      who: 'val', push: p,
      ots: { draw: (w, h) => revolvingDoor(w, h, t, lt, tOut, tBack), label: 'OPENAI', labelCol: back ? '#1E9A4A' : NP.red, k: inK(lt, 0, .2) },
      val: dt ? { lookX: -.9, eyes: 'wide', brows: 'up', mouth: 'O', talk: undefined } : {},
    });
    if (!back) chyron('ALTMAN FIRED', 'BOARD: "NOT CONSISTENTLY CANDID"', { k: chyK(lt), style: 'breaking', tab: 'NEW' });
    else chyron('ALTMAN REHIRED', 'FIVE DAYS LATER', { k: clamp((lt - tBack) / .25), style: 'money', tab: 'UPDATE' });
  });

  // =====================================================================================
  // V1.10 Weekend chaos, board expired — the board's portrait wall: five of six directors get EXPIRED stamps on the beats while the
  // tear-off calendar sheds FRI → WED on the eighth notes.
  line('V1', 10, (p, lt, d, t) => {
    gfxCard({ top: '#56627E', bottom: '#161C30', head: 'OPENAI BOARD', headCol: '#3A4A78', sub: 'SAN FRANCISCO' });
    const chaos = clamp(lt / d), hairs = ['short', 'bob', 'balding', 'side', 'long', 'curly'];
    const stampAt = [bt(t, lt, 1), bt(t, lt, 2), bt(t, lt, 1), 99, bt(t, lt, 2), bt(t, lt, 3)];
    for (let i = 0; i < 6; i++) {
      const c = i % 3, r = Math.floor(i / 3), fx = 140 + c * 350, fy = 225 + r * 285, rot = (hash(i + 20) - .5) * .12 * chaos + Math.sin(t * 9 + i) * .02 * chaos;
      ctx.save(); ctx.translate(fx + 150, fy + 125); ctx.rotate(rot); ctx.translate(-150, -125);
      rrect(-10, -10, 320, 270, 6); paint(lg(0, 0, 0, 260, [[0, '#F4D27A'], [1, '#B8862A']]), NP.ink, 4);
      ctx.save(); rrect(4, 4, 292, 200, 3); ctx.clip(); vFill('#7AA8D8', '#3A5A8A', 4, 4, 292, 200);
      toon(150, 210 + 6.2 * 22, 22, { sil: '#1E2438', hair: hairs[i], legs: false, shadow: false, top: i % 2 ? 'blazer' : 'suit' });
      ctx.restore();
      rrect(20, 212, 260, 36, 4); paint('#2A2A30'); txt('DIRECTOR', 150, 231, 24, '#E8E0C8', { font: 'archivo', spacing: 3 });
      ctx.restore();
      if (lt >= stampAt[i] - .02) stamp('EXPIRED', fx + 150, fy + 110, 46, NP.red, -.25 + (hash(i) - .5) * .2, { pop: (lt - stampAt[i]) / .1, font: 'archivo', blend: 'source-over', alpha: .95 });
      if (i === 3 && lt > bt(t, lt, 3)) { const k = backOut(clamp((lt - bt(t, lt, 3)) / .15), 2); ctx.save(); ctx.translate(fx + 240, fy + 40); ctx.rotate(.12); ctx.scale(k, k); rrect(-70, -28, 140, 56, 4); paint('#FFF27A', NP.ink, 3); txt('STAYED', 0, 2, 28, NP.ink, { font: 'marker' }); ctx.restore(); }
    }
    // tear-off calendar
    const days = [['FRI', 17], ['SAT', 18], ['SUN', 19], ['MON', 20], ['TUE', 21], ['WED', 22]], e8 = beatLen() / 2;
    const idx = clamp(Math.floor((lt - bt(t, lt)) / e8) + 1, 0, days.length - 1), since = lt - bt(t, lt) - (idx - 1) * e8;
    const cx = 1550, cy = 470;
    ctx.save(); ctx.translate(cx, cy); ctx.rotate(.03);
    rrect(-200, -230, 400, 470, 10); paint('#FBFAF4', NP.ink, 5);
    rrect(-200, -230, 400, 90, [10, 10, 0, 0]); paint(NP.red, NP.ink, 5); txt('NOV 2023', 0, -184, 44, NP.white, { font: 'archivo', spacing: 3 });
    txt(days[idx][0], 0, -95, 60, NP.ink, { font: 'archivo', spacing: 4 }); txt(String(days[idx][1]), 0, 60, 230, days[idx][0] === 'SAT' || days[idx][0] === 'SUN' ? NP.red : NP.ink, { font: 'anton' });
    ctx.restore();
    if (idx > 0 && since < .3) { const u = since / .3, pd = days[idx - 1]; ctx.save(); ctx.translate(cx + u * 500, cy - 60 - u * 300 + u * u * 500); ctx.rotate(.03 + u * 2.4); ctx.globalAlpha = 1 - u * .5; rrect(-200, -140, 400, 380, 6); paint('#F4F2EA', NP.ink, 4); txt(pd[0], 0, -95, 60, NP.ink, { font: 'archivo' }); txt(String(pd[1]), 0, 60, 230, NP.ink, { font: 'anton' }); ctx.restore(); }
    chyron('OPENAI BOARD SHAKE-UP', '700 OF 770 STAFF THREATEN TO QUIT', { k: chyK(lt), style: 'breaking', tab: 'NEW' });
  });

  // =====================================================================================
  // V1.11 Ilya saw what Ilya saw — EYEWITNESS: a big mic in ILYA's face; he just stares. Crash zoom on the beat into his eye, where
  // a tiny red exponential curve glows in the reflection.
  line('V1', 11, (p, lt, d, t) => {
    const z0 = bt(t, lt, 1) - .06, ez = ease(clamp((lt - z0) / .16)), X = 860, Y = 1640, S = 118, look = { lookX: .55, lookY: -.4 };
    const [ex, ey] = eyeAt(X, Y, S, 1, look);
    camBegin(lerp(960, ex, ez), lerp(540, ey, ez), lerp(1, 13, ez) * (1 + p * .05));
    vFill('#0A2A3A', '#041018');
    for (let i = 0; i < 26; i++) { const bx = hash(i + 1) * W, by = hash(i + 2) * 700, r = 30 + hash(i + 3) * 60; ctx.fillStyle = `rgb(${['255 200 120', '120 220 255', '255 120 160'][i % 3]} / ${.12 + .1 * hash(i + 4)})`; ell(bx + Math.sin(t + i) * 6, by, r); ctx.fill(); }
    toon(X, Y, S, { hair: 'balding', hairCol: '#2A1E18', top: 'sweater', topCol: '#22242E', skin: 0, eyes: 'wide', mouth: 'flat', legs: false, shadow: false, ...look });
    // what he saw, in the reflection
    const [px, py] = [ex + .08 * S * look.lookX * 0, ey];
    ctx.save(); ctx.translate(px, py); ctx.beginPath(); for (let i = 0; i <= 20; i++) { const u = i / 20; ctx.lineTo(-7 + u * 12, 5 - (Math.exp(u * 3.5) - 1) / (Math.exp(3.5) - 1) * 12); } ctx.strokeStyle = '#FF3030'; ctx.lineWidth = 1.6; ctx.stroke();
    ctx.fillStyle = 'rgb(255 255 255 / .8)'; ell(4, -5, 2.2, 1.6); ctx.fill(); ctx.restore();
    if (ez > .5) glint(px + 3, py - 4, 14 * ez, ez, '#FF8080');
    camEnd();
    // the reporter's mic, from the right
    const mk = 1 - ez;
    if (mk > .02) {
      ctx.save(); ctx.globalAlpha = mk;
      ctx.beginPath(); ctx.moveTo(W + 60, 980); ctx.lineTo(1470, 800); paint(null, NP.ink, 70); ctx.beginPath(); ctx.moveTo(W + 60, 980); ctx.lineTo(1470, 800); paint(null, CAST.randi.o.topCol, 60);
      bigMic(1330, 640 + Math.sin(t * 5) * 6, 44, { rot: -.7 }); ell(1500, 790, 40, 36); paint(NSKIN[3], NP.ink, 4);
      ctx.restore();
    }
    liveBug(96, 70, { label: 'EYEWITNESS', col: NP.blue });
    chyron('ILYA SUTSKEVER', 'EYEWITNESS · WHAT DID HE SEE?', { k: chyK(lt) });
  });

  // =====================================================================================
  // V1.12 EU writes the AI law — the EURO DESK: a doorstop of a rulebook slams down inside the ring of stars, the vote tally
  // counts up 523–46, and PASSED lands on the beat.
  line('V1', 12, (p, lt, d, t) => {
    const land = Math.max(.16, bt(t, lt)), [sx, sy] = shake(t, lt, land, .3, 18);
    ctx.save(); ctx.translate(sx, sy);
    gfxCard({ top: '#1A3FB0', bottom: '#061040', head: 'EURO DESK', headCol: '#0A2A9A', sub: 'BRUSSELS' });
    const cx = 470, cy = 560;
    for (let i = 0; i < 12; i++) { const a = i / 12 * TAU + t * .2; poly(starPts(cx + Math.cos(a) * 290, cy + Math.sin(a) * 290, 34, .45, 5)); paint(NP.gold, '#8A6408', 2); }
    const drop = (1 - easeIn(clamp(lt / land))) * -700, sq = lt > land && lt < land + .15 ? Math.sin((lt - land) / .15 * Math.PI) * .06 : 0;
    ctx.save(); ctx.translate(cx, cy + drop); ctx.rotate(-.06); ctx.scale(1 + sq, 1 - sq);
    poly([[160, -230], [230, -270], [230, 200], [160, 240]]); paint('#F4EEDC', NP.ink, 4);
    ctx.strokeStyle = 'rgb(120 110 90 / .6)'; ctx.lineWidth = 2; ctx.beginPath(); for (let i = 1; i < 14; i++) { ctx.moveTo(160 + i * 5, -230 - i * 2.9 * 1); ctx.lineTo(160 + i * 5, 240 - i * 2.9); } ctx.stroke();
    poly([[-170, -230], [160, -230], [230, -270], [-100, -270]]); paint('#12308A', NP.ink, 4);
    rrect(-170, -230, 330, 470, 6); paint(lg(0, -230, 0, 240, [[0, '#2A55D0'], [1, '#0E2A80']]), NP.ink, 4);
    for (let i = 0; i < 12; i++) { const a = i / 12 * TAU; poly(starPts(-5 + Math.cos(a) * 70, -80 + Math.sin(a) * 70, 12, .45, 5)); paint(NP.gold); }
    chrome('AI ACT', -5, 70, 84, { font: 'anton', style: 'gold', depth: 6 });
    txt('REGULATION (EU) 2024/1689', -5, 150, 16, NP.ice, { font: 'archivo' });
    ctx.restore();
    if (lt > land && lt < land + .35) { const u = (lt - land) / .35; for (let i = 0; i < 10; i++) { const a = Math.PI + i / 9 * Math.PI; ell(cx + Math.cos(a) * (230 + u * 200), cy + 250 - Math.abs(Math.sin(a)) * u * 80, 30 * (1 - u)); paint(`rgb(230 220 200 / ${.6 * (1 - u)})`); } }
    tallyBoard(900, 250, 880, { title: 'AI ACT · PARLIAMENT VOTE', rows: [{ label: 'YES', n: 523, col: '#2A6AE0', win: true }, { label: 'NO', n: 46, col: '#D8262F' }, { label: 'ABSTAIN', n: 49, col: '#8890A0' }], k: clamp(lt / .7) });
    ctx.restore();
    const pk = (lt - bt(t, lt, 2)) / .1;
    if (pk > 0) stamp('PASSED', 1340, 640, 110, '#1E9A4A', -.14, { pop: pk, font: 'archivo', blend: 'source-over', alpha: .95 });
    chyron('EU PASSES THE AI ACT', "WORLD'S FIRST COMPREHENSIVE AI LAW", { k: chyK(lt) });
  });

  // =====================================================================================
  // V1.13 Strawberry thinks, link by link — the station's PLEASE STAND BY card, starring a strawberry deep in thought; its chain of
  // thought grows one link per eighth note until the light bulb goes on.
  function strawberry(x, y, s, t, o = {}) {
    ctx.save(); ctx.translate(x, y); ctx.scale(s, s);
    for (const sd of [-1, 1]) { ctx.beginPath(); ctx.moveTo(sd * .8, 2.2); ctx.lineTo(sd * 1.0, 3.6); paint(null, NP.ink, .32); ell(sd * 1.2, 3.75, .55, .26); paint('#2A2A30', NP.ink, .08); }
    ctx.beginPath(); ctx.moveTo(0, 3.0); ctx.bezierCurveTo(-3.2, 1.6, -3.0, -2.6, -.8, -2.6); ctx.lineTo(.8, -2.6); ctx.bezierCurveTo(3.0, -2.6, 3.2, 1.6, 0, 3.0); ctx.closePath();
    paint(lg(0, -2.6, 0, 3, [[0, '#FF5A5A'], [1, '#B8101E']]), NP.ink, .12);
    ctx.save(); ctx.clip(); ctx.fillStyle = 'rgb(0 0 0 / .15)'; ell(1.6, .4, 1.4, 3); ctx.fill(); ctx.restore();
    for (let r = 0; r < 5; r++) for (let c = -2; c <= 2; c++) { const sx = c * .9 + (r % 2) * .45, sy = -1.4 + r * .95; if (Math.abs(sx) > 2.3 - r * .35 || (Math.abs(sx) < 1.3 && sy > -1.2 && sy < .6)) continue; ell(sx, sy, .1, .16); paint('#FFE27A'); }
    for (let i = 0; i < 5; i++) { const a = -Math.PI / 2 + (i - 2) * .55; poly([[0, -2.5], [Math.cos(a - .25) * .5, -2.5 + Math.sin(a - .25) * .5], [Math.cos(a) * 1.6, -2.4 + Math.sin(a) * 1.2], [Math.cos(a + .25) * .5, -2.5 + Math.sin(a + .25) * .5]]); paint('#2EBD5B', NP.ink, .08); }
    ctx.beginPath(); ctx.moveTo(0, -3.1); ctx.lineTo(.2, -3.9); paint(null, '#2A7A3A', .25);
    // face: looking up, thinking
    for (const sd of [-1, 1]) { ell(sd * .6, -.6, .38, .45); paint('#FFF', NP.ink, .08); ell(sd * .6 + .12, -.8, .18, .2); paint(NP.ink); }
    ctx.beginPath(); ctx.moveTo(-.4, .5); ctx.quadraticCurveTo(0, .35 + Math.sin(t * 8) * .08, .45, .45); paint(null, NP.ink, .12);
    // arms: one on the chin, one on the hip
    ctx.beginPath(); ctx.moveTo(1.9, .2); ctx.quadraticCurveTo(2.6, 1.4, .8, 1.0); paint(null, NP.ink, .3); ell(.75, .95, .38); paint('#FFF', NP.ink, .08);
    ctx.beginPath(); ctx.moveTo(-1.9, .2); ctx.lineTo(-2.6, 1.3); ctx.lineTo(-2.0, 1.9); paint(null, NP.ink, .3); ell(-2.0, 1.9, .36); paint('#FFF', NP.ink, .08);
    ctx.restore();
  }
  line('V1', 13, (p, lt, d, t) => {
    vFill('#FF7A2A', '#A0140E');
    rays(W / 2, 520, 24, 'rgb(255 255 200 / .08)', t * .15);
    ell(W / 2, 540, 470, 470); paint(null, 'rgb(255 255 255 / .25)', 10); ell(W / 2, 540, 380, 380); paint(null, 'rgb(255 255 255 / .15)', 6);
    rrect(330, 180, 1260, 140, 16); paint('rgb(0 0 30 / .55)', '#FFF', 5);
    chrome('PLEASE STAND BY', W / 2, 252, 96, { font: 'archivo', style: 'white', depth: 8, spacing: 4 });
    const bob = Math.sin(bpOf(t) * Math.PI) * 8;
    strawberry(560, 560 + bob, 88, t);
    // the chain of thought
    const e8 = beatLen() / 2, n = clamp(Math.floor((lt + .05) / e8 * 1.0) + 1, 1, 9), path = [];
    for (let i = 0; i <= 9; i++) { const u = i / 9; path.push([660 + u * 860, 440 - Math.sin(u * Math.PI) * 70 + u * 40]); }
    for (let i = 0; i < n; i++) {
      const [lx, ly] = path[i], [nx, ny] = path[i + 1], a = Math.atan2(ny - ly, nx - lx), since = lt - (i - 1) * e8, k = i === n - 1 ? backOut(clamp(since / .12 * 1), 2.4) : 1;
      ctx.save(); ctx.translate((lx + nx) / 2, (ly + ny) / 2); ctx.rotate(a); ctx.scale(k, k);
      if (i % 2) { rrect(-56, -10, 112, 20, 10); paint(null, NP.ink, 18); rrect(-56, -10, 112, 20, 10); paint(null, '#D8DCE8', 10); }
      else { rrect(-60, -30, 120, 60, 30); paint(null, NP.ink, 20); rrect(-60, -30, 120, 60, 30); paint(null, lg(0, -30, 0, 30, [[0, '#F4F6FF'], [1, '#8A90A8']]), 12); }
      ctx.restore();
    }
    // the light bulb at the end
    const done = n >= 9, bk = clamp((lt - 8 * e8) / .12);
    ctx.save(); ctx.translate(1640, 520);
    if (done) { ctx.fillStyle = rg(0, 0, 10, 220, [[0, 'rgb(255 250 180 / .8)'], [1, 'rgb(255 250 180 / 0)']]); ell(0, 0, 220, 220); ctx.fill(); }
    ell(0, -20, 80, 90); paint(done ? '#FFF6A0' : '#DADDE6', NP.ink, 6); rrect(-40, 60, 80, 60, 8); paint('#9AA0B0', NP.ink, 5);
    if (done) txt('!', 0, -18, 110, NP.red, { font: 'anton', s: bk });
    ctx.restore();
    rrect(260, 800, 1400, 110, 10); paint('rgb(0 0 0 / .65)', '#FFF', 3);
    pixelText('WE ARE EXPERIENCING THINKING' + '.'.repeat(1 + Math.floor(t * 4) % 3), 300, 818, 5, NP.white, { edge: null });
    pixelText('CODENAME: STRAWBERRY', 300, 868, 4, '#FF9A9A', { edge: null });
  });

  // =====================================================================================
  // V1.14 Newsom vetoes, doesn't blink — press conference: GAVIN holds up SB 1047, VETO lands on the beat, every camera in the
  // room fires… and his eyes stay wide open. The blink counter stays at zero.
  line('V1', 14, (p, lt, d, t) => {
    const hit = bt(t, lt);
    vFill('#1A2E78', '#0A1440');
    for (let i = 0; i < 16; i++) { ctx.fillStyle = i % 2 ? 'rgb(0 0 0 / .18)' : 'rgb(255 255 255 / .05)'; ctx.fillRect(i * 124, 0, 124, H); }
    ctx.fillStyle = NP.gold; for (let i = 0; i < 48; i++) { poly([[i * 40, 0], [i * 40 + 40, 0], [i * 40 + 20, 34]]); ctx.fill(); }
    for (const [fx, cols] of [[260, ['#B22234', '#FFFFFF']], [1660, ['#0A3A8A', NP.gold]]]) {
      ctx.beginPath(); ctx.moveTo(fx, 120); ctx.lineTo(fx, 1000); paint(null, '#C9A43A', 10); ell(fx, 112, 14); paint(NP.gold);
      for (let s2 = 0; s2 < 7; s2++) { ctx.beginPath(); ctx.moveTo(fx + 6, 140 + s2 * 36); ctx.quadraticCurveTo(fx + 90, 150 + s2 * 36 + Math.sin(t * 3 + s2) * 14, fx + 150, 160 + s2 * 36 + 40); ctx.lineTo(fx + 150, 196 + s2 * 36 + 40); ctx.quadraticCurveTo(fx + 90, 186 + s2 * 36 + Math.sin(t * 3 + s2) * 14, fx + 6, 176 + s2 * 36); ctx.closePath(); paint(cols[s2 % 2]); }
    }
    const X = 960, Y = 1190, S = 80, up = lt > hit ? 1 : 0;
    const billX = X - 3.2 * S, billY = Y - 10.6 * S;
    toon(X, Y, S, { hair: 'slick', hairCol: '#2A2220', top: 'suit', topCol: '#1E2230', tie: '#2A5AC8', skin: 0, legs: false, shadow: false, eyes: 'wide', brows: 'flat', mouth: 'flat', lookX: 0,
      reachL: [-3.0, -9.9], reachR: lt < hit - .1 ? [3.2, -11.2] : lt < hit ? [lerp(3.2, -1.6, (lt - hit + .1) / .1), -10.8] : [-1.6, -10.4] });
    // the bill
    ctx.save(); ctx.translate(billX, billY); ctx.rotate(-.06);
    ctx.scale(1.2, 1.2); rrect(-120, -160, 240, 300, 4); paint('#FBFAF4', NP.ink, 4); txt('SB 1047', 0, -118, 44, NP.ink, { font: 'abril' });
    txt('SAFE AND SECURE INNOVATION', 0, -78, 13, '#444', { font: 'archivo' }); ctx.fillStyle = 'rgb(20 20 30 / .4)'; for (let r = 0; r < 8; r++) ctx.fillRect(-96, -52 + r * 22, r % 3 === 2 ? 110 : 192, 6);
    ctx.restore();
    if (up) stamp('VETO', billX + 4, billY + 24, 94, NP.red, -.22, { pop: (lt - hit) / .1, font: 'archivo', blend: 'source-over', alpha: .95 });
    podium(X, Y + 30, 70, { seal: 'GOVERNOR', mics: 7 });
    flashbulbs(t, 7, { y0: 250, y1: 800 });
    // blink counter
    rrect(96, 190, 330, 90, 8); paint('rgb(0 0 0 / .75)', '#888', 3);
    pixelText('BLINKS:', 116, 214, 5, NP.white, { edge: null }); pixelText('0', 400, 208, 7, frac(t * 3) < .5 ? NP.phosphor : '#2A8A4A', { align: 'right', edge: null });
    liveBug();
    chyron('NEWSOM VETOES SB 1047', 'SACRAMENTO · CALIFORNIA', { k: chyK(lt), style: 'live', tab: 'LIVE' });
    flash(lt, hit, .08, .5);
  });

  // =====================================================================================
  // V1.15 Hinton takes his medal, scolds — the Nobel stage: GEOFFREY holds up the gold medal with one hand and wags a finger at the
  // camera with the other, on the beat; a quote card makes his point.
  line('V1', 15, (p, lt, d, t) => {
    vFill('#0A1A5A', '#040820');
    ctx.save(); ctx.globalCompositeOperation = 'screen';
    for (const [bx, ph] of [[500, 0], [1400, 1.3]]) { ctx.fillStyle = 'rgb(255 230 170 / .1)'; const a = Math.sin(t * .8 + ph) * .1; poly([[bx - 30, -20], [bx + 30, -20], [bx + 400 + a * 900, 1100], [bx - 400 + a * 900, 1100]]); ctx.fill(); }
    ctx.restore();
    ell(W / 2, 470, 420, 420); paint(null, 'rgb(244 182 42 / .35)', 14); ell(W / 2, 470, 360, 360); paint(null, 'rgb(244 182 42 / .2)', 6);
    txt('NOBEL PRIZE IN PHYSICS', W / 2 - 250, 110, 58, NP.gold, { font: 'abril', spacing: 3 });
    // flowers along the stage front
    for (let i = 0; i < 26; i++) { const fx = i * 78 - 20, fy = 1000 + (i % 2) * 20; ell(fx, fy, 44, 36); paint(['#F4F0FF', '#FFD0E0', '#FFF0B0'][i % 3], NP.ink, 2); ell(fx, fy, 14); paint(NP.gold); }
    const wag = Math.sin(bpOf(t) * Math.PI * 2) * .28, X = 760, Y = 1380, S = 82;
    toon(X, Y, S, { hair: 'side', hairCol: NHAIR.grey, glasses: 'square', top: 'suit', topCol: '#1A1A22', tie: '#8A1A2A', skin: 0, legs: false, shadow: false, brows: 'angry', talk: talk(t),
      reachL: [-3.3, -10.3], aR: 1.05 + wag, eR: .55 - wag * .4, hand: 'point', lookX: .1 });
    goldMedal(X - 3.3 * S, Y - 10.3 * S + 70, 66, { text: '2024', glint: .6 + .4 * pulse(t, 4) });
    // the quote card
    const qk = clamp((lt - bt(t, lt) + .02) / .18);
    if (qk > 0) {
      ctx.save(); ctx.translate(1440, 470); ctx.scale(backOut(qk, 1.4), backOut(qk, 1.4));
      rrect(-330, -200, 660, 400, 12); paint('rgb(255 250 240 / .95)', NP.ink, 5);
      txt('“', -270, -120, 200, NP.red, { font: 'abril' });
      ['WE HAVE NO EXPERIENCE', "OF WHAT IT'S LIKE TO", 'HAVE THINGS SMARTER', 'THAN US.'].forEach((l, i) => txt(l, 30, -110 + i * 62, 40, NP.ink, { font: 'archivo', maxW: 560 }));
      txt('— G. HINTON, OCT. 8', 120, 160, 28, '#555', { font: 'archivo' });
      ctx.restore();
    }
    chyron('GEOFFREY HINTON', 'NOBEL PRIZE, PHYSICS · WARNS OF AI RISK', { k: chyK(lt) });
  });

  // =====================================================================================
  // V1.16 Demis wins for protein folds — SCIENCE 89 in early CGI: a rainbow protein ribbon folds itself up on the wireframe grid,
  // DEMIS lifts his medal, confetti on the beat it clicks into shape.
  line('V1', 16, (p, lt, d, t) => {
    laserGrid(t, { horizon: 690, col: '#2AF08A', sky: ['#000006', '#001A14'], speed: .4 });
    rrect(80, 70, 560, 96, 10); paint('rgb(0 20 10 / .8)', '#2AF08A', 3);
    chrome('SCIENCE 89', 360, 118, 64, { font: 'archivo', style: 'white', depth: 5, italic: .1, spacing: 3 });
    const fold = ease(clamp((lt - .08) / .95)), N = 84, ry = t * .9, pts = [];
    for (let i = 0; i < N; i++) {
      const u = i / (N - 1), hI = Math.min(3, Math.floor(u * 4)), v = u * 4 - hI, ang = v * 6 * Math.PI;
      const straight = [lerp(-1.4, 1.4, u), Math.sin(u * 18) * .06, Math.cos(u * 11) * .05];
      const folded = [(hI - 1.5) * .3 + .11 * Math.cos(ang), (hI % 2 ? .55 - 1.1 * v : -.55 + 1.1 * v), .11 * Math.sin(ang) + (hI % 2 ? .12 : -.12)];
      const wob = fold * (1 - fold) * 1.4;
      const P = straight.map((a, j) => lerp(a, folded[j], fold) + Math.sin(u * 9 + j * 2 + t * 2) * .12 * wob);
      const c = Math.cos(ry), s = Math.sin(ry), X = P[0] * c + P[2] * s, Z = -P[0] * s + P[2] * c, f = 3.2 / (Z + 3.2);
      pts.push([700 + X * 520 * f, 470 + P[1] * 520 * f, Z, f, u]);
    }
    const segs = []; for (let i = 0; i < N - 1; i++) segs.push([pts[i], pts[i + 1]]);
    segs.sort((a, b) => (b[0][2] + b[1][2]) - (a[0][2] + a[1][2]));
    ctx.lineCap = 'round';
    for (const [a, b] of segs) {
      const w = 26 * a[3], hue = a[4] * 280;
      ctx.beginPath(); ctx.moveTo(a[0], a[1]); ctx.lineTo(b[0], b[1]);
      ctx.strokeStyle = '#000'; ctx.lineWidth = w + 6; ctx.stroke(); ctx.strokeStyle = `hsl(${hue} 90% ${45 + 12 * a[3]}%)`; ctx.lineWidth = w; ctx.stroke();
      ctx.strokeStyle = 'rgb(255 255 255 / .35)'; ctx.lineWidth = w * .25; ctx.stroke();
    }
    pixelText(fold >= 1 ? 'FOLDED  100%' : `FOLDING... ${Math.floor(fold * 100)}%`, 1180, 210, 5, fold >= 1 ? NP.phosphor : NP.white, { align: 'center' });
    const X = 1480, Y = 1180, S = 58, cheer = fold >= 1;
    toon(X, Y, S, { hair: 'short', hairCol: '#2A1E18', skin: 2, top: 'suit', topCol: '#2A2A3A', tie: NP.blue, legs: false, shadow: false, mouth: cheer ? 'grin' : 'smile', eyes: cheer ? 'happy' : 'open',
      reachL: [-2.2, cheer ? -12.8 : -10.6], aR: -1.2 });
    goldMedal(X - 2.2 * S, Y - (cheer ? 12.8 : 10.6) * S + 60, 50, { text: '2024', glint: cheer ? 1 : .4 });
    if (cheer) { const since = lt - 1.03; for (let i = 0; i < 40; i++) { const cx = hash(i + 5) * W, cy = -40 + since * (300 + hash(i + 8) * 400) - hash(i + 2) * 200; if (cy < -30) continue; ctx.save(); ctx.translate(cx + Math.sin(t * 5 + i) * 20, cy); ctx.rotate(t * 6 + i); ctx.fillStyle = ['#FF4A6A', NP.gold, '#4AD0FF', '#7CFF8A', '#C07AFF'][i % 5]; ctx.fillRect(-9, -5, 18, 10); ctx.restore(); } }
    chyron('DEMIS HASSABIS', 'NOBEL PRIZE, CHEMISTRY · ALPHAFOLD', { k: chyK(lt), style: 'purple' });
  });
})();

;
// ---- styles/newscast/ch/c03_chorus1.js ----
// c03_chorus1 — Chorus 1: the station's image-campaign jingle, sung at the desk (the smallest of the four promos).
// Sub-shots are keyed to linesOf('C1'): four sung lines; the two long ones are split at their commas on the half-beat grid.
//   A  "We didn't start the scaling"   the jingle card: the chrome hook slams on word by word over a sunburst, globe and laser grid
//   B  "It was always training,"       DVE star wipe to the two-shot: Clawd & Val sing and sway; the wall shows a loss curve going down
//   C  "and the curves kept gaining,"  full-screen CGI chart: the anchors ride the curve in a roller-coaster car, one notch per beat
//   D  "We didn't start the scaling"   the hook again, bigger: magenta grid, the anchors in two DVE boxes circling the chrome title
//   E  "No, we didn't preordain it,"   two-shot: a synchronised shrug, then they point at each other; the wall's curve presses its frame
//   F  "but we can't contain it!"      the curve bursts out of the wall and whips across the set; scripts fly; alarm; shake → V2.1
// Colour run: blue/gold card → blue set → black/lime CGI → magenta card → blue set → set washed red by the alarm beacon.
(() => {
  const flash = (t, t0, dur = .1, a = .6, col = '255 255 255') => { const k = (t - t0) / dur; if (k >= 0 && k < 1) { ctx.fillStyle = `rgb(${col} / ${a * (1 - k)})`; ctx.fillRect(-300, -300, W + 600, H + 600); } };
  const rays = (cx, cy, n, col, rot = 0, R = 2600) => { ctx.fillStyle = col; ctx.beginPath(); for (let i = 0; i < n; i++) { const a0 = rot + i / n * TAU, a1 = a0 + TAU / n / 2; ctx.moveTo(cx, cy); ctx.lineTo(cx + Math.cos(a0) * R, cy + Math.sin(a0) * R); ctx.lineTo(cx + Math.cos(a1) * R, cy + Math.sin(a1) * R); ctx.closePath(); } ctx.fill(); };
  // song time of the first beat at/after song time x, and a half-beat snap
  const beatAfter = x => onBeat(0, Math.ceil(bpOf(x) - .02));
  const snapHalf = x => onBeat(0, Math.round(bpOf(x) * 2) / 2);
  // a neon polyline (the curve): glow, core, hot centre
  function neon(P, col, w = 10) {
    if (P.length < 2) return;
    ctx.save(); ctx.lineJoin = 'round'; ctx.lineCap = 'round';
    ctx.beginPath(); P.forEach(([a, b], i) => i ? ctx.lineTo(a, b) : ctx.moveTo(a, b));
    ctx.strokeStyle = alpha(col, .22); ctx.lineWidth = w * 2.8; ctx.stroke();
    ctx.strokeStyle = col; ctx.lineWidth = w; ctx.stroke();
    ctx.strokeStyle = 'rgb(255 255 255 / .85)'; ctx.lineWidth = w * .3; ctx.stroke();
    ctx.restore();
  }

  // =====================================================================================
  // The hook, word by word. Word onsets as fractions of the sung line (measured on this take's vocal; they scale with the line).
  const HOOK = ["WE", "DIDN'T", "START", "THE", "SCALING"], HOOKF = [0, .24, .46, .58, .73];
  function hookWords(t, ln, o = {}) {
    const S1 = o.s1 ?? 124, S2 = o.s2 ?? 210, S3 = S1 * .62, y1 = o.y1 ?? 300, y2 = o.y2 ?? 520, gap = S1 * .32, dur = ln.end - ln.start;
    const at = HOOKF.map(f => ln.start + f * dur);
    const ws = HOOK.map((w, i) => textW(w, i === 3 ? S3 : i === 4 ? S2 : S1, 'archivo', 2));
    const row1 = ws[0] + ws[1] + ws[2] + gap * 2, row2 = ws[3] + ws[4] + gap * .6;
    const pos = [[W / 2 - row1 / 2 + ws[0] / 2, y1], [W / 2 - row1 / 2 + ws[0] + gap + ws[1] / 2, y1], [W / 2 + row1 / 2 - ws[2] / 2, y1],
      [W / 2 - row2 / 2 + ws[3] / 2, y2 - S2 * .22], [W / 2 + row2 / 2 - ws[4] / 2, y2]];
    HOOK.forEach((w, i) => {
      const k = clamp((t - at[i] + .03) / .13); if (k <= 0) return;
      const [x, y] = pos[i], big = i === 4, bump = big ? 1 + pulse(t, 7) * .025 : 1;
      const s = (k < 1 ? lerp(big ? 2.6 : 2.1, 1, easeOut(k)) : 1) * bump;
      chrome(w, x, y, i === 3 ? S3 : big ? S2 : S1, { font: 'archivo', style: big ? 'gold' : (o.style ?? 'chrome'), italic: .14, depth: Math.round((big ? S2 : S1) * .08), spacing: 2, s, alpha: clamp(k * 3) });
      const g = clamp((t - at[i] - .06) / .3);
      if (g > 0 && g < 1) glint(x + ws[i] * .38, y - (big ? S2 : S1) * .32, (big ? 260 : 150) * Math.sin(g * Math.PI), Math.sin(g * Math.PI));
    });
    const sc = at[4];
    sweepGlint(W / 2 - row2 / 2, W / 2 + row2 / 2, y2 - S2 * .25, (t - sc - .15) / .5, 170);
    return { sc, at };
  }
  // A: the jingle card
  function hookCard(t, ln) {
    const b = bpOf(t);
    laserGrid(t, { horizon: 780, col: NP.cyan, sky: ['#020826', '#18308E'], speed: 1.8 });
    rays(W / 2, 470, 20, 'rgb(255 205 110 / .075)', t * .22);
    for (let i = 0; i < 3; i++) { const ph = frac(b + i / 3), r = 120 + ph * 900; ell(W / 2, 470, r, r * .92); paint(null, `rgb(140 220 255 / ${.16 * (1 - ph)})`, 6); }
    globe(W / 2, 460, 290, t * 1.3, { col: NP.cyan });
    logo89(210, 190, 92, { spin: Math.sin(t * 1.7) * .5 });
    const { sc } = hookWords(t, ln, { s1: 124, s2: 212 });
    swoosh(clamp((t - sc) / .5), 740, NP.red, { len: 1800, th: 64 }); swoosh(clamp((t - sc - .12) / .5), 800, NP.gold, { len: 1500, th: 34 });
    const sk = clamp((t - sc - .1) / .2);
    if (sk > 0) { ctx.save(); ctx.globalAlpha = sk; rrect(W / 2 - 470, 690, 940, 78, 8); paint('rgb(0 0 40 / .75)', alpha(NP.gold, .9), 4); txt('CHANNEL 89 ACTION NEWS', W / 2, 731, 48, NP.white, { font: 'archivo', spacing: 6 }); ctx.restore(); }
    flash(t, sc, .1, .3);
  }

  // =====================================================================================
  // The studio wall graphics (the centre panel is 520 × 540, anchors overlap its lower corners).
  function wallGrid(w, h, col = 'rgb(90 160 255 / .28)') {
    ctx.fillStyle = lg(0, 0, 0, h, [[0, '#07153E'], [1, '#020716']]); ctx.fillRect(0, 0, w, h);
    ctx.strokeStyle = col; ctx.lineWidth = 2; ctx.beginPath();
    for (let x = 40; x < w; x += 44) { ctx.moveTo(x, 0); ctx.lineTo(x, h); } for (let y = 30; y < h; y += 44) { ctx.moveTo(0, y); ctx.lineTo(w, y); } ctx.stroke();
  }
  // B: loss going down while "always training"
  function lossWall(w, h, t, k) {
    wallGrid(w, h);
    pixelText('LOSS', 110, 34, 6, NP.phosphor, { edge: null });
    const x0 = 110, x1 = w - 70, yT = 120, yB = 430, P = [];
    for (let i = 0; i <= 60; i++) { const u = i / 60; P.push([lerp(x0, x1, u), yT + (1 - Math.exp(-u * 4.2)) / (1 - Math.exp(-4.2)) * (yB - yT) + Math.sin(u * 40) * 4 * (1 - u)]); }
    const Q = partial(P, k); neon(Q, NP.phosphor, 8);
    const [tx, ty] = Q.at(-1); ell(tx, ty, 13); paint('#FFFFFF', NP.phosphor, 4);
    glint(tx, ty, 60, .9);
    pixelText('TRAINING' + '.'.repeat(1 + Math.floor(t * 4) % 3), 110, 460, 5, NP.white, { edge: null });
  }
  // E/F: the curve going up, then pressing against the top of its frame. Returns nothing; `press` 0..1 squashes it against the edge.
  function upWall(w, h, t, k, press = 0, crack = 0) {
    wallGrid(w, h, 'rgb(255 120 160 / .22)');
    pixelText('COMPUTE', 110, 34, 6, NP.amber, { edge: null });
    const x0 = 250, x1 = w - 50, yB = 440, P = [];
    for (let i = 0; i <= 70; i++) { const u = i / 70, f = (Math.exp(u * 5) - 1) / (Math.exp(5) - 1); let y = yB - f * (yB - 60) * (1 + press * 2.2); if (y < 22) y = 22 + Math.sin(u * 60 + t * 30) * 5 * press; P.push([lerp(x0, x1, u) + (y <= 30 ? press * 10 * Math.sin(u * 30) : 0), y]); }
    const Q = partial(P, k); neon(Q, NP.magenta, 9);
    const [tx, ty] = Q.at(-1); glint(tx, ty, 70, 1);
    if (press > 0) { ctx.fillStyle = `rgb(255 40 90 / ${.25 * press * (.6 + .4 * Math.sin(t * 30))})`; ctx.fillRect(0, 0, w, 50); }
    if (crack > 0) crackLines(w - 90, 26, crack, 11);
  }
  function crackLines(cx, cy, k, seed) {
    ctx.save(); ctx.strokeStyle = 'rgb(235 245 255 / .9)'; ctx.lineWidth = 3; ctx.lineCap = 'round';
    for (let i = 0; i < 7; i++) {
      const a = Math.PI * (.05 + i / 6 * .95) + (hash2(seed, i) - .5) * .3, L = (60 + hash2(seed, i + 9) * 170) * k;
      ctx.beginPath(); ctx.moveTo(cx, cy); let x = cx, y = cy;
      for (let j = 1; j <= 4; j++) { x += Math.cos(a + (hash2(seed + j, i) - .5) * .7) * L / 4; y += Math.sin(a + (hash2(seed + j, i) - .5) * .7) * L / 4; ctx.lineTo(x, y); }
      ctx.stroke();
    }
    ctx.restore();
  }

  // =====================================================================================
  // C: the anchors ride the curve in a roller-coaster car.
  function coasterCar(x, y, a, s, t, steep, jolt) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(a); ctx.scale(s, s);
    const bob = Math.sin(t * 22) * 2 * jolt;
    // passengers (seated; drawn before the car's front panel)
    toon(-84, 36 + bob, 13, { ...CAST.val.o, legs: false, shadow: false, aL: 1.15, eL: .35, aR: 1.25, eR: .2, hand: 'open', handL: 'open', eyes: steep > .7 ? 'wide' : 'happy', talk: talk(t, 1.3), rot: -a * .25 });
    newsClawd(58, -6 + bob, 10.5, { legs: false, shadow: false, aL: 1.1, aR: 1.25, talk: talk(t), eyes: steep > .7 ? 'wide' : 'happy', sweat: steep > .55, rot: -a * .2 });
    // the car
    ctx.beginPath(); ctx.moveTo(-150, -44); ctx.lineTo(140, -44); ctx.quadraticCurveTo(178, -44, 186, 0); ctx.lineTo(-150, 0); ctx.closePath();
    paint(lg(0, -44, 0, 0, [[0, '#FF5A5A'], [.5, NP.red], [1, NP.redDk]]), NP.ink, 5);
    ctx.fillStyle = NP.gold; ctx.fillRect(-150, -12, 330, 6);
    logo89(-20, -24, 17); txt('ACTION NEWS', 88, -26, 18, NP.white, { font: 'archivo', maxW: 110 });
    for (const wx of [-110, 110]) { ell(wx, 8, 15); paint('#2A2A34', NP.ink, 4); ell(wx, 8, 5); paint(NP.silver); }
    ctx.restore();
  }
  function coasterShot(t, T0, T1) {
    const stepped = x => { const b = bpOf(x); return Math.floor(b) + easeOut(clamp(frac(b) / .3)); };
    const n0 = stepped(T0), nSteps = Math.max(1, Math.round(stepped(T1) - n0)), done = stepped(t) - n0;
    const u0 = .3, u = clamp(u0 + (1 - u0 - .04) * done / nSteps, 0, .97), jolt = 1 - clamp(frac(bpOf(t)) / .3);
    const X0 = 170, X1 = 1600, YB = 830, YT = 250, fn = v => (Math.exp(v * 5) - 1) / (Math.exp(5) - 1);
    const at = v => [lerp(X0, X1, v), YB - fn(v) * (YB - YT)];
    // the car sits just behind the tip: walk back along the curve by about its length
    const CS = 1.75, [tx, ty] = at(u); let uc = u;
    for (let i = 0; i < 60 && uc > .01; i++) { const [a1, b1] = at(uc); if (Math.hypot(tx - a1, ty - b1) > 150 * CS) break; uc -= .004; }
    const [cx, cy] = at(uc), [dx, dy] = (() => { const [a1, b1] = at(uc - .008), [a2, b2] = at(uc + .008); return [a2 - a1, b2 - b1]; })();
    const ang = Math.atan2(dy, dx), steep = clamp(-ang / 1.2);
    camBegin(lerp(960, cx, .9) + 90, lerp(540, cy, .85) - 110, 1.2 + (t - T0) * .02);
    vFill('#050318', '#1A0636', -600, -600, W + 1200, H + 1200);
    for (let i = 0; i < 90; i++) { ctx.fillStyle = `rgb(255 255 255 / ${.2 + .5 * hash(i + 7)})`; ctx.fillRect(hash(i) * 2600 - 340, hash(i + 50) * 1500 - 300, 3, 3); }
    // the graph paper
    ctx.strokeStyle = 'rgb(120 255 120 / .16)'; ctx.lineWidth = 2; ctx.beginPath();
    for (let x = X0; x < X1 + 400; x += 90) { ctx.moveTo(x, -400); ctx.lineTo(x, YB); } for (let y = YB; y > -400; y -= 90) { ctx.moveTo(X0, y); ctx.lineTo(X1 + 400, y); } ctx.stroke();
    ctx.beginPath(); ctx.moveTo(X0, -400); ctx.lineTo(X0, YB); ctx.lineTo(X1 + 400, YB); paint(null, 'rgb(210 255 210 / .9)', 5);
    // the track: the curve so far (with coaster cross-ties), and a dotted projection ahead
    const P = []; for (let i = 0; i <= 90; i++) P.push(at(i / 90 * u));
    for (let i = 3; i < P.length; i += 3) { const [a1, b1] = P[i - 1], [a2, b2] = P[i], nx = -(b2 - b1), ny = a2 - a1, L = Math.hypot(nx, ny) || 1; ctx.beginPath(); ctx.moveTo(a2 - nx / L * 4, b2 - ny / L * 4); ctx.lineTo(a2 + nx / L * 26, b2 + ny / L * 26); paint(null, 'rgb(166 240 74 / .45)', 5); }
    neon(P, NP.lime, 11);
    ctx.save(); ctx.setLineDash([6, 22]); ctx.beginPath(); for (let i = 0; i <= 30; i++) { const [a, b] = at(u + i / 30 * .25); i ? ctx.lineTo(a, b) : ctx.moveTo(a, b); } paint(null, 'rgb(166 240 74 / .5)', 5); ctx.restore();
    // supports down to the floor
    for (let i = 1; i < 6; i++) { const v = i / 6 * u; if (v > u - .05) continue; const [a, b] = at(v); ctx.beginPath(); ctx.moveTo(a, b + 12); ctx.lineTo(a, YB); paint(null, 'rgb(166 240 74 / .25)', 6); }
    coasterCar(cx, cy - 4, ang, CS, t, steep, jolt);
    glint(tx, ty, 110 * (.6 + .4 * pulse(t, 5)), 1);
    camEnd();
    // readouts
    const n = clamp(Math.floor(done + .0001), 0, 6), vals = ['1X', '10X', '100X', '1,000X', '10,000X', '100,000X', '1,000,000X'];
    rrect(96, 70, 610, 150, 10); paint('rgb(0 0 0 / .72)', NP.lime, 3);
    pixelText('COMPUTE', 124, 90, 5, NP.lime, { edge: null }); poly([[330, 125], [362, 125], [346, 94]]); ctx.fillStyle = NP.lime; ctx.fill();
    const pop = 1 + (1 - clamp(frac(bpOf(t)) / .25)) * .12;
    ctx.save(); ctx.translate(124, 176); ctx.scale(pop, pop); pixelText(vals[n], 0, -22, 7, n >= 5 && frac(t * 4) < .5 ? NP.gold : NP.white, { edge: null }); ctx.restore();
    pixelText('TIME ▶', 1690, 838, 5, 'rgb(210 255 210 / .9)', { align: 'right', edge: null });
    stationBug(1790, 930, 44, .9);
  }

  // =====================================================================================
  // D: the hook, bigger: the anchors in two DVE boxes circling the chrome title.
  function flyBox(c, x, y, w, h, rot, a = 1) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot); ctx.globalAlpha *= a;
    ctx.fillStyle = 'rgb(0 0 0 / .45)'; ctx.fillRect(-w / 2 + 12, -h / 2 + 14, w, h);
    ctx.drawImage(c, -w / 2, -h / 2, w, h);
    ctx.lineWidth = 7; ctx.strokeStyle = '#FFFFFF'; ctx.strokeRect(-w / 2, -h / 2, w, h);
    ctx.lineWidth = 2; ctx.strokeStyle = 'rgb(0 0 0 / .6)'; ctx.strokeRect(-w / 2 - 4.5, -h / 2 - 4.5, w + 9, h + 9);
    ctx.restore();
  }
  function hookBig(t, ln, T0) {
    const b = bpOf(t), age = t - T0;
    laserGrid(t, { horizon: 800, col: NP.magenta, sky: ['#0A0220', '#4A0A5E'], speed: 2.8 });
    rays(W / 2, 480, 24, 'rgb(255 120 220 / .08)', -t * .3);
    globe(W / 2, 410, 300, t * 1.8, { col: NP.cyan });
    // the carousel: two DVE boxes circling under the title (small at the back of the loop, big at the front)
    const cC = renderTo('c1boxC', .4, () => anchorShot(t, { who: 'clawd', talk: talk(t), shuffle: .4, cam: { x: 600, y: 590, zoom: 2.3 }, clawd: { eyes: 'happy', dy: Math.sin(b * Math.PI) * .12 } }));
    const cV = renderTo('c1boxV', .4, () => anchorShot(t, { who: 'val', talk: talk(t, 2), shuffle: .4, cam: { x: 1320, y: 600, zoom: 2.3 }, val: { eyes: 'happy', dy: Math.sin(b * Math.PI) * .06 } }));
    // the boxes pass the sides (not the middle) as SCALING lands
    const kin = easeOut(clamp(age / .35)), base = (t - (ln.start + HOOKF[4] * (ln.end - ln.start))) * 2.4;
    const boxes = [[cC, base + Math.PI], [cV, base]].map(([c, a]) => { const z = Math.sin(a); return { c, x: W / 2 + Math.cos(a) * 600 * kin, y: lerp(410, 750 + z * 80, kin), s: lerp(.55, .95, (z + 1) / 2) * lerp(.1, 1, kin), z, rot: -Math.cos(a) * .1 }; });
    const drawBox = B => flyBox(B.c, B.x, B.y, 600 * B.s, 338 * B.s, B.rot, clamp(kin * 2));
    boxes.filter(B => B.z < 0).forEach(drawBox);
    const { sc } = hookWords(t, ln, { s1: 126, s2: 236, y1: 262, y2: 460, style: 'white' });
    swoosh(clamp((t - sc) / .45), 610, NP.red, { len: 1900, th: 60 }); swoosh(clamp((t - sc - .1) / .45), 660, NP.gold, { len: 1600, th: 34 }); swoosh(clamp((t - sc - .2) / .45), 570, NP.cyan, { len: 1400, th: 24, alpha: .8 });
    boxes.filter(B => B.z >= 0).forEach(drawBox);
    // chasing marquee bulbs round the frame
    for (let i = 0; i < 64; i++) {
      const u = i / 64, per = 2 * (W + H), d = u * per, [bx, by] = d < W ? [d, 36] : d < W + H ? [W - 36, d - W] : d < 2 * W + H ? [W - (d - W - H), H - 36] : [36, H - (d - 2 * W - H)];
      if (bx > 1300 && by < 180) continue;
      const on = (i + Math.floor(b * 2)) % 3 === 0; ell(bx, by, 11); paint(on ? '#FFE27A' : '#4A2A40');
      if (on) { ctx.fillStyle = 'rgb(255 226 122 / .25)'; ell(bx, by, 24); ctx.fill(); }
    }
    flash(t, sc, .1, .3);
  }

  // =====================================================================================
  // E/F: the two-shot with free hands; the curve on the wall behind them; F: it escapes.
  const PX = 700, PY = 80, PW = 520;   // the centre panel (set coordinates)
  function escapePath() {
    // from the panel's top-right corner: up over Val, a loop, back across over Clawd, then straight at the camera
    const ctrl = [[PX + PW - 60, PY + 24], [PX + PW + 20, PY - 10], [1290, 120], [1420, 290], [1720, 360], [1700, 560], [1440, 470], [1100, 330], [720, 290], [380, 370], [300, 560], [560, 640], [880, 560], [960, 480]];
    const pts = [];
    for (let i = 0; i < ctrl.length - 1; i++) {
      const p0 = ctrl[Math.max(0, i - 1)], p1 = ctrl[i], p2 = ctrl[i + 1], p3 = ctrl[Math.min(ctrl.length - 1, i + 2)];
      for (let j = 0; j < 10; j++) { const u = j / 10, u2 = u * u, u3 = u2 * u; pts.push([0, 1].map(q => .5 * (2 * p1[q] + (-p0[q] + p2[q]) * u + (2 * p0[q] - 5 * p1[q] + 4 * p2[q] - p3[q]) * u2 + (-p0[q] + 3 * p1[q] - 3 * p2[q] + p3[q]) * u3))); }
    }
    pts.push(ctrl.at(-1));
    return pts;
  }
  const ESC = escapePath();
  function flyingPapers(t, since, x0, y0, seed) {
    if (since <= 0) return;
    for (let i = 0; i < 4; i++) {
      const vx = (hash2(seed, i) < .5 ? -1 : 1) * (700 + hash2(seed, i + 1) * 900), vy = -500 - hash2(seed, i + 9) * 700, g = 1500, px = x0 + vx * since + (hash2(seed, i + 3) - .5) * 80, py = y0 + vy * since + g * since * since * .5;
      if (py > H + 200) continue;
      ctx.save(); ctx.translate(px, py); ctx.rotate(since * (hash2(seed, i + 5) - .5) * 14); ctx.scale(1, .55 + .45 * Math.cos(since * 9 + i));
      rrect(-60, -80, 120, 160, 3); paint('#FBFAF4', NP.ink, 3);
      ctx.fillStyle = 'rgb(20 20 30 / .45)'; for (let r = 0; r < 6; r++) ctx.fillRect(-44, -60 + r * 22, r % 3 === 2 ? 50 : 88, 5);
      ctx.restore();
    }
  }
  function beacon(t, x, y, on) {
    ctx.save();
    if (on) {
      ctx.globalCompositeOperation = 'screen'; const a = t * 9;
      for (const sd of [0, Math.PI]) { ctx.fillStyle = 'rgb(255 40 40 / .22)'; poly([[x, y], [x + Math.cos(a + sd - .22) * 2400, y + Math.abs(Math.sin(a + sd - .22)) * 900 + 200], [x + Math.cos(a + sd + .22) * 2400, y + Math.abs(Math.sin(a + sd + .22)) * 900 + 200]]); ctx.fill(); }
      ctx.globalCompositeOperation = 'source-over';
    }
    rrect(x - 30, y - 12, 60, 24, 6); paint('#222', NP.ink, 3);
    ctx.beginPath(); ctx.arc(x, y - 12, 30, Math.PI, TAU); ctx.closePath(); paint(on && frac(t * 4.5) < .5 ? '#FF4040' : '#8A1010', NP.ink, 3);
    if (on) glint(x, y - 26, 80, .8, '#FF9090');
    ctx.restore();
  }
  function twoShotChaos(t, T0, T1, ln) {
    // E: [T0, Tsplit) shrug / point; F: [Tsplit, end) escape
    const Tsplit = snapHalf(lerp(ln.start, ln.end, .58)), inF = t >= Tsplit, b = bpOf(t);
    const bE = beatAfter(T0), bPoint = beatAfter(lerp(T0, Tsplit, .45)), bShrug2 = beatAfter(lerp(T0, Tsplit, .82));
    // F timeline: the words "but we can't / contain / it" at fractions of the line's tail; the last hit is the first beat after the line ends
    const Tcan = lerp(Tsplit, ln.end, .2), Tburst = beatAfter(lerp(Tsplit, ln.end, .44)), Tlast = beatAfter(ln.end + .05), since = t - Tburst;
    const burst = inF && since >= 0, tail = t - Tlast;
    // camera: gentle push in E; shake and a dutch tilt in F
    let sh = [0, 0], rot = 0, zoom = 1.1 + clamp((t - T0) / (Tsplit - T0)) * .05;
    if (inF) { const amp = burst ? 7 + 10 * pulse(t, 5) : 3 * clamp((t - Tcan) / .3); sh = shakeXY(t, amp); rot = burst ? Math.sin(t * 3) * .025 : 0; zoom = 1.15 - (burst ? .13 * easeOut(clamp(since / .4)) : 0); }
    if (tail >= 0) { sh = shakeXY(t, 30 * (1 - clamp(tail / .5)) + 8); }
    const cam = { x: 960 + sh[0], y: 540 + sh[1], zoom, rot };
    // poses
    let cP, vP;
    const sing = { clawd: talk(t), val: talk(t, 2) };
    if (!inF) {
      const shrugK = easeOut(clamp((t - bE + .06) / .12)), hop = Math.abs(Math.sin(b * Math.PI)) ** 3;
      const pointing = t >= bPoint && t < bShrug2, pk = easeOut(clamp((t - bPoint) / .1));
      if (pointing) {
        cP = { reachR: [lerp(4.8, 9.6, pk), lerp(-5, -7.6, pk)], reachL: [-6.2, -2.4], lookX: .9, eyes: 'normal', talk: sing.clawd, dy: -.05 };
        vP = { reachL: [lerp(-1.6, -4.4, pk), -8.4], handL: 'point', reachR: [2.2, -5.2], lookX: -.9, brows: 'angry', talk: sing.val };
      } else {
        const lift = shrugK * (1 + hop * .15);
        cP = { aL: lerp(-1.2, .12, lift), aR: lerp(-1.2, .12, lift), eyes: 'happy', talk: sing.clawd, dy: -.18 * lift, rot: -.05 * lift };
        vP = { reachL: [-1.6 - 2.0 * lift, -5.4 - 1.9 * lift], reachR: [1.6 + 2.0 * lift, -5.4 - 1.9 * lift], elbowIn: true, rot: .04 * lift, hand: 'open', handL: 'open', eyes: 'happy', brows: 'up', talk: sing.val, dy: -.1 * lift };
      }
    } else if (!burst) {
      cP = { reachL: [-6.4, -2.6], reachR: [6.4, -2.6], lookX: .95, lookY: -.8, eyes: 'wide', sweat: true, talk: sing.clawd * .5 };
      vP = { reachL: [-2.4, -5.4], reachR: [2.4, -5.4], lookX: -.95, lookY: -.8, eyes: 'wide', brows: 'worried', mouth: 'O' };
    } else {
      const duck = easeOut(clamp(since / .15)), peek = tail >= 0 ? 0 : 1;
      cP = { reachL: [-3.4, -9.2], reachR: [3.4, -9.2], eyes: 'x', sweat: true, mouth: 'O', dy: .9 * duck * peek + (tail >= 0 ? .3 : 0), rot: Math.sin(t * 17) * .04 };
      vP = { reachL: [-1.4, -11.2], reachR: [1.4, -11.2], hand: 'open', handL: 'open', eyes: 'wide', brows: 'up', mouth: 'scream', dy: .55 * duck * peek + (tail >= 0 ? .2 : 0), rot: Math.sin(t * 15 + 1) * .04 };
    }
    // the wall: curve climbing (E), pressing and cracking (F before the burst), an empty cracked frame after it
    const eK = clamp((t - T0) / (Tsplit - T0)), press = inF ? clamp((t - Tsplit) / (Tburst - Tsplit)) : clamp((eK - .7) / .3) * .4;
    const wall = (w, h) => {
      if (!burst) upWall(w, h, t, inF ? 1 : lerp(.25, 1, eK), press, inF ? clamp((t - Tcan) / .25) : 0);
      else { wallGrid(w, h, 'rgb(255 120 160 / .22)'); pixelText('COMPUTE', 110, 34, 6, NP.amber, { edge: null }); pixelText('NO SIGNAL', w / 2, h / 2 - 20, 7, frac(t * 3) < .6 ? NP.red : '#601018', { align: 'center', edge: null }); crackLines(w - 90, 26, 1, 11); crackLines(w - 60, 60, .8, 13); }
    };
    anchorShot(t, { who: 'two', hands: false, shuffle: 0, talk: 0, cam, wall, clawd: cP, val: vP, mugs: 1 });
    // everything in front of the set, in the same camera
    camBegin(cam.x, cam.y, cam.zoom, cam.rot);
    beacon(t, 960, 44, inF);
    if (burst) {
      const k = clamp(since / .75), P = partial(ESC, easeOut(k));
      neon(P, NP.magenta, 16);
      const tip = P.at(-1); glint(tip[0], tip[1], 150, 1, '#FFC0E8');
      // glass shards
      if (since < .7) for (let i = 0; i < 14; i++) { const a = -Math.PI * (.1 + hash(i + 3) * .8), v = 500 + hash(i + 9) * 900, sx = PX + PW - 60 + Math.cos(a) * v * since, sy = PY + 24 + Math.sin(a) * v * since + 1400 * since * since; ctx.save(); ctx.translate(sx, sy); ctx.rotate(since * 12 * (hash(i) - .5)); poly([[-14, -10], [16, -4], [-2, 14]]); paint('rgb(220 240 255 / .8)', 'rgb(255 255 255 / .9)', 2); ctx.restore(); }
      flyingPapers(t, since - .1, 600, 690, 3); flyingPapers(t, since - .16, 1320, 700, 8);
    }
    camEnd();
    // the tail: the curve's tip comes straight at the lens
    if (tail > -.12) {
      const u = clamp((tail + .12) / .75), r = lerp(40, 1500, easeIn(u));
      ctx.save(); ctx.globalCompositeOperation = 'screen'; ctx.fillStyle = rg(W / 2, H / 2 - 40, 0, r, [[0, 'rgb(255 255 255 / .95)'], [.35, 'rgb(255 110 210 / .8)'], [1, 'rgb(226 55 155 / 0)']]); ctx.fillRect(0, 0, W, H); ctx.restore();
    }
    // glitches: on "can't", on the burst, and on the last hit
    if (inF) {
      const gk = Math.max(0, 1 - Math.abs(t - Tcan) / .08) * .5, gb = burst && since < .18 ? 1 - since / .18 : 0, gl = tail >= 0 && tail < .25 ? 1 - tail / .25 : 0;
      const g = Math.max(gk, gb, gl); if (g > 0) glitch('track', g);
      if (burst && since < .1) tapeFX({ dropouts: 3 });
    }
    flash(t, Tburst, .12, .6, '255 170 220'); flash(t, Tlast, .1, .5);
  }

  // =====================================================================================
  section('C1', (p, lt, d, t) => {
    const L = linesOf('C1'), T0 = t - lt, T1 = T0 + d;
    const sB = L[1].start, sC = snapHalf(lerp(L[1].start, L[1].end, .5)), sD = L[2].start, sE = L[3].start;
    if (t < sB) { hideCaption(); return hookCard(t, L[0]); }
    if (t < sC) {
      const k = clamp((t - sB) / .38), u = clamp((t - sB) / (sC - sB)), b = bpOf(t), sway = Math.sin(b * Math.PI) * .045;
      const look = b - bpOf(sB) > 1.5 && b - bpOf(sB) < 3.2;
      const shot = () => {
        anchorShot(t, {
          who: 'two', shuffle: .45, talk: 0, cam: { x: 960, y: 525, zoom: 1.12 + u * .06 }, wall: (w, h) => lossWall(w, h, t, lerp(.1, 1, u)),
          clawd: { talk: talk(t), rot: sway, lookX: look ? .9 : .1, eyes: look ? 'happy' : 'normal' },
          val: { talk: talk(t, 2), rot: sway * .8, lookX: look ? -.9 : 0, eyes: look ? 'happy' : 'open' },
        });
        chyron('CLAWD & VAL LOSS', 'YOUR CHANNEL 89 NEWS TEAM', { k: clamp((t - sB - .45) / .3), size: 50, y: 784 });
      };
      if (k < 1) { hideCaption(); dveStar(k, () => hookCard(t, L[0]), shot); } else shot();
      return;
    }
    if (t < sD) {
      // DVE flip out of the two-shot into the chart on the "and"
      const k = clamp((t - sC + .08) / .22);
      if (k < 1) return dveFlip(.5 + k * .5, () => {}, () => coasterShot(t, sC, sD));
      return coasterShot(t, sC, sD);
    }
    if (t < sE) { hideCaption(); return hookBig(t, L[2], sD); }
    return twoShotChaos(t, sE, T1, L[3]);
  });
})();

;
// ---- styles/newscast/ch/c04_v2.js ----
// c04_v2 — Verse 2: 2025, the year of money, from DeepSeek's sticker shock to the bubble talk. Every line is a different news
// segment, and consecutive shots flip dominant colour: money green / cream press room / game-show magenta / tech purple /
// sports green / infomercial yellow / apology black / arena blue-gold / dusk pink / countdown purple / lotto teal /
// desk blue with a red OTS / brick orange / channel-surfing wood / curtain red / newsprint cream.
(() => {
  // lt of the k-th beat at/after the window start (lines start on the beat or on the "and" before it)
  const bt = (t, lt, k = 0) => onBeat(0, Math.ceil(bpOf(t - lt) - .02) + k) - (t - lt);
  // the first beat that leaves room for an entrance (a window that starts on the beat lands its gag on the next one)
  const hit0 = (t, lt) => { const a = bt(t, lt); return a < .12 ? bt(t, lt, 1) : a; };
  const flash = (lt, t0, dur = .1, a = .6, col = '255 255 255') => { const k = (lt - t0) / dur; if (k >= 0 && k < 1) { ctx.fillStyle = `rgb(${col} / ${a * (1 - k)})`; ctx.fillRect(-300, -300, W + 600, H + 600); } };
  const shake = (t, lt, t0, dur = .25, amt = 16) => { const k = (lt - t0) / dur; return k >= 0 && k < 1 ? shakeXY(t, amt * (1 - k)) : [0, 0]; };
  const rays = (cx, cy, n, col, rot = 0, R = 2600) => { ctx.fillStyle = col; ctx.beginPath(); for (let i = 0; i < n; i++) { const a0 = rot + i / n * TAU, a1 = a0 + TAU / n / 2; ctx.moveTo(cx, cy); ctx.lineTo(cx + Math.cos(a0) * R, cy + Math.sin(a0) * R); ctx.lineTo(cx + Math.cos(a1) * R, cy + Math.sin(a1) * R); ctx.closePath(); } ctx.fill(); };
  const popK = (lt, t0, dur = .14) => backOut(clamp((lt - t0) / dur), 2);
  // a clean gold medal on a ribbon; (x, y) = medal centre, r radius
  function goldMedal(x, y, r, o = {}) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(o.rot ?? 0);
    if (o.ribbon !== false) { poly([[-r * .7, -r * 3.2], [-r * .25, -r * .8], [r * .25, -r * .8], [r * .7, -r * 3.2], [r * .25, -r * 3.2], [0, -r * 1.6], [-r * .25, -r * 3.2]]); paint(o.ribbonCol ?? NP.blue, NP.ink, 3); }
    ell(0, 0, r, r); paint(lg(0, -r, 0, r, [[0, '#FFF1A8'], [.45, '#F4B62A'], [1, '#9A6408']]), NP.ink, 4);
    ell(0, 0, r * .72, r * .72); paint(null, 'rgb(120 70 0 / .6)', 3);
    if (o.text) txt(o.text, 0, 2, r * .55, '#6A4200', { font: 'archivo', maxW: r * 1.3 });
    ctx.restore();
  }
  // a firework burst (video-graphics style): rays of dots expanding and falling; age in s
  function firework(x, y, age, col, n = 16, R = 170) {
    if (age < 0 || age > .9) return;
    const k = easeOut(clamp(age / .5)), fade = 1 - clamp((age - .35) / .55);
    ctx.save(); ctx.globalAlpha *= fade; ctx.globalCompositeOperation = 'lighter';
    for (let i = 0; i < n; i++) { const a = i / n * TAU, rr = R * k; for (let j = 0; j < 4; j++) { const q = rr * (1 - j * .16); ell(x + Math.cos(a) * q, y + Math.sin(a) * q + age * age * 120, 7 - j * 1.3); ctx.fillStyle = j ? alpha(col, .6) : '#FFFFFF'; ctx.fill(); } }
    ctx.restore();
  }
  // a whip-pan: the frame smears sideways for a few frames (k 0..1, 1 = full smear)
  function whipLines(k, dir = 1) {
    if (k <= 0) return;
    ctx.save(); ctx.globalAlpha = k;
    for (let i = 0; i < 40; i++) { const y = hash(i + 3) * H, h = 6 + hash(i + 5) * 40; ctx.fillStyle = `rgb(255 255 255 / ${.12 + .2 * hash(i)})`; ctx.fillRect(0, y, W, h); }
    ctx.restore();
  }

  // =====================================================================================
  // V2.1 DeepSeek New Year sticker shock — MONEY WATCH: a $5.6M* price tag slaps onto the DEEPSEEK R1 computer, New Year fireworks
  // go off behind it, and on the next beat NVDA nosedives on the board and CHIP STACKS's glasses fly off.
  function priceTag(x, y, s, rot, big, foot) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot); ctx.scale(s, s);
    ctx.fillStyle = 'rgb(0 0 0 / .3)'; poly([[-130, -80], [150, -80], [200, 0], [150, 80], [-130, 80]].map(([a, b]) => [a + 10, b + 12])); ctx.fill();
    poly([[-130, -80], [150, -80], [200, 0], [150, 80], [-130, 80]]); paint(lg(0, -80, 0, 80, [[0, '#FFF1B8'], [1, '#E8C870']]), NP.ink, 5);
    ell(158, 0, 14); paint('#2A5A2A', NP.ink, 4);
    txt(big, 10, -12, 104, NP.red, { font: 'anton', maxW: 250 });
    txt(foot, 10, 56, 21, NP.ink, { font: 'archivo', maxW: 260 });
    ctx.restore();
  }
  line('V2', 1, (p, lt, d, t) => {
    const slap = bt(t, lt), crash = bt(t, lt, 1), [sx, sy] = shake(t, lt, slap, .25, 14), crashed = lt >= crash;
    ctx.save(); ctx.translate(sx, sy);
    gfxCard({ top: '#0F6A3C', bottom: '#021A0C', head: 'MONEY WATCH', headCol: '#1E7A4A', sub: 'WALL STREET' });
    // Lunar New Year fireworks behind the set
    const fw = [[560, 330, slap, '#FF4A3A'], [1040, 260, slap + .12, NP.gold], [760, 470, crash - .1, '#FF7A4A'], [1180, 420, crash + .2, NP.gold], [420, 520, crash + .45, '#FF4A3A']];
    for (const [x, y, t0, c] of fw) firework(x, y, lt - t0, c);
    // lanterns
    for (const [lx, ly] of [[330, 250], [1230, 230]]) { ctx.beginPath(); ctx.moveTo(lx, 180); ctx.lineTo(lx, ly - 40); paint(null, '#222', 3); ell(lx, ly + Math.sin(t * 3 + lx) * 4, 44, 52); paint(lg(0, ly - 50, 0, ly + 50, [[0, '#FF5A3A'], [1, '#A8101E']]), NP.ink, 4); rrect(lx - 24, ly - 60, 48, 12, 3); paint(NP.gold, NP.ink, 2); rrect(lx - 24, ly + 48, 48, 12, 3); paint(NP.gold, NP.ink, 2); }
    // the DEEPSEEK R1 computer on a plinth, with its sticker
    rrect(640, 760, 360, 60, 6); paint(lg(0, 760, 0, 820, [[0, '#E8E8EC'], [1, '#9AA0B0']]), NP.ink, 4);
    computer(820, 764, 38, { case: '#CFD8E8', screen: '#061830', glow: '#5AB0FF', face: crashed ? 'grin' : 'smile', legs: false, label: 'DEEPSEEK R1', aL: -1, aR: -1 });
    const tk = clamp((lt - slap + .06) / .1);
    if (tk > 0) priceTag(890, 500, lerp(1.9, 1, easeOut(tk)), -.18, '$5.6M*', '*FINAL TRAINING RUN');
    // the quote board and the nosedive
    quoteBoard(1190, 250, 610, [{ sym: 'NVDA', price: crashed ? '118.42' : '142.62', chg: crashed ? -17 : 0.4 }], { rowH: 96, flash: crashed ? 0 : -1 });
    const k = crashed ? .7 + .3 * easeIn(clamp((lt - crash) / .18)) : lerp(.35, .7, clamp(lt / crash));
    cgiChart(1200, 420, 590, 260, { fn: u => u < .7 ? .55 + u * .4 + Math.sin(u * 23) * .04 : .83 - (u - .7) / .3 * .95, k, col: crashed ? '#FF4A4A' : NP.lime, fill: true, bg: 'rgb(0 12 6 / .85)' });
    if (crashed && frac((lt - crash) * 4) < .65) { const s2 = popK(lt, crash, .1); ctx.save(); ctx.translate(1560, 560); ctx.scale(s2, s2); poly([[-190, -50], [-110, -50], [-150, 20]]); paint(NP.red, NP.ink, 5); chrome('-17%', 20, -20, 110, { font: 'anton', style: 'red', depth: 9, italic: .1 }); ctx.restore(); }
    // CHIP STACKS, and his glasses leaving his face
    const gone = crashed, X = 330, Y = 1200, S = 64;
    toon(X, Y, S, { ...CAST.chip.o, glasses: gone ? undefined : 'square', legs: false, shadow: false, eyes: gone ? 'wide' : 'open', mouth: gone ? 'scream' : 'smile', brows: gone ? 'up' : 'flat', lookX: gone ? .3 : .7,
      reachR: gone ? [2.2, -12.4] : [3.6, -10.2], hand: gone ? 'open' : 'point', reachL: gone ? [-2.2, -12.2] : undefined, handL: 'open', dy: gone ? -.08 : 0, sweat: gone });
    if (gone) {
      const u = lt - crash, gx = X + .0 * S - u * 700, gy = Y - 9.62 * S - u * 900 + u * u * 1800;
      ctx.save(); ctx.translate(gx, gy); ctx.rotate(-u * 14);
      for (const sd of [-1, 1]) { rrect(sd * 30 - 24, -20, 48, 40, 8); paint('rgb(200 230 255 / .35)', NP.ink, 5); }
      ctx.beginPath(); ctx.moveTo(-6, -4); ctx.lineTo(6, -4); paint(null, NP.ink, 5); ctx.restore();
    }
    ctx.restore();
    ticker(716, ['NVDA ▼17%', 'NASDAQ ▼3%', 'DEEPSEEK R1: FREE, OPEN WEIGHTS', 'DEEPSEEK APP #1 ON THE APP STORE'], t, { h: 54, speed: 380 });
    flash(lt, crash, .08, .4, '255 60 60');
    chyron('DEEPSEEK R1: A $5.6M SHOCK', 'NVIDIA LOSES ~$600 BILLION IN A DAY', { k: chyK(lt), style: 'money', tab: 'NEW' });
  });

  // =====================================================================================
  // V2.2 Half a trillion Stargate talk — the White House: four suits behind a giant novelty cheque for $500,000,000,000, all
  // talking at once; flashbulbs; FACT CHECK stamps it on the beat: PLEDGED, NOT IN THE BANK.
  line('V2', 2, (p, lt, d, t) => {
    const stampT = bt(t, lt, 2), push = 1 + p * .04;
    camBegin(960, 500, push);
    vFill('#F4E6C0', '#C9B284', -600, -600, W + 1200, 1600);
    for (let i = -2; i < 12; i++) { const x = i * 220 + 40; ctx.fillStyle = 'rgb(255 255 255 / .55)'; ctx.fillRect(x, -100, 60, 1200); ctx.fillStyle = 'rgb(160 130 70 / .25)'; ctx.fillRect(x + 60, -100, 10, 1200); }
    ctx.fillStyle = '#8A6A3A'; ctx.fillRect(-600, 60, W + 1200, 16);
    // flags
    for (const fx of [140, 1740]) { ctx.beginPath(); ctx.moveTo(fx, 220); ctx.lineTo(fx, 900); paint(null, '#C9A43A', 10); ell(fx, 214, 13); paint(NP.gold); for (let s2 = 0; s2 < 7; s2++) { ctx.beginPath(); const y0 = 240 + s2 * 34, wv = Math.sin(t * 3 + s2) * 12; ctx.moveTo(fx + 5, y0); ctx.quadraticCurveTo(fx + 70, y0 + wv, fx + 130, y0 + 20); ctx.lineTo(fx + 130, y0 + 54); ctx.quadraticCurveTo(fx + 70, y0 + 34 + wv, fx + 5, y0 + 34); ctx.closePath(); paint(s2 % 2 ? '#FFFFFF' : '#B22234'); } }
    // the four, all talking at once
    const who = [
      ['TRUMP', { hair: 'swoop', hairCol: '#E8C46A', topCol: '#1C2440', tie: NP.red, skin: 1 }],
      ['ALTMAN', { hair: 'short', hairCol: NHAIR.brown, topCol: '#3A3F52', tie: '#5A6AA0', skin: 0 }],
      ['ELLISON', { hair: 'balding', hairCol: NHAIR.grey, topCol: '#20222A', tie: '#2A2A2A', skin: 4, beard: true, beardCol: NHAIR.grey }],
      ['SON', { hair: 'bald', topCol: '#1E2A48', tie: '#2A5AC8', skin: 0 }],
    ];
    who.forEach(([nm, o], i) => {
      const x = 470 + i * 330, y = 900, s = 52;
      toon(x, y, s, { top: 'suit', legs: false, shadow: false, talk: talk(t, i * 1.9), lookX: (i - 1.5) * -.25, dy: Math.sin(t * 5 + i) * .03, reachL: [-2.4, -6.0], reachR: [2.4, -6.0], ...o });
      rrect(x - 88, 522, 176, 36, 4); paint('rgb(10 14 30 / .85)'); pixelText(nm, x, 530, 4, NP.white, { align: 'center', edge: null });
    });
    // the novelty cheque
    const ck = popK(lt, 0, .16), cy = 572;
    ctx.save(); ctx.translate(960, cy + 130); ctx.scale(ck, ck); ctx.rotate(-.015);
    rrect(-760, -130, 1520, 260, 10); paint(lg(0, -130, 0, 130, [[0, '#E8F4E0'], [1, '#C8E0C0']]), NP.ink, 6);
    ctx.strokeStyle = 'rgb(40 110 60 / .25)'; ctx.lineWidth = 2; for (let i = 0; i < 14; i++) { ctx.beginPath(); ctx.moveTo(-760, -130 + i * 20); ctx.lineTo(760, -130 + i * 20); ctx.stroke(); }
    txt('PAY TO THE ORDER OF:', -700, -92, 26, '#2A4A2A', { font: 'archivo', align: 'left' }); txt('AI DATA CENTERS', -360, -92, 34, NP.ink, { font: 'marker', align: 'left' });
    rrect(-700, -56, 1400, 104, 6); paint('#FFFFFF', '#2A4A2A', 3);
    txt('$500,000,000,000', -170, -2, 92, NP.ink, { font: 'anton', spacing: 4 });
    txt('STARGATE · OVER FOUR YEARS', -700, 92, 24, '#2A4A2A', { font: 'archivo', align: 'left' });
    ctx.beginPath(); for (let i = 0; i <= 30; i++) ctx.lineTo(300 + i * 12, 92 + Math.sin(i * 1.3) * 16 - i * .6); paint(null, '#1A2A6A', 4);
    ctx.restore();
    camEnd();
    flashbulbs(t, 6, { y0: 150, y1: 700 });
    const sk = (lt - stampT) / .1;
    if (sk > 0) {
      const s = sk < 1 ? lerp(1.8, 1, easeOut(sk)) : 1;
      ctx.save(); ctx.translate(1420, 690); ctx.rotate(-.12); ctx.scale(s * .7, s * .7); ctx.globalAlpha = clamp(sk * 3);
      rrect(-330, -110, 660, 220, 10); paint('rgb(255 255 255 / .92)', NP.red, 10); rrect(-315, -95, 630, 190, 6); paint(null, NP.red, 3);
      txt('FACT CHECK:', 0, -52, 48, NP.red, { font: 'archivo', spacing: 3 });
      txt('PLEDGED, NOT IN THE BANK', 0, 30, 46, NP.redDk, { font: 'anton', maxW: 590 });
      ctx.restore();
    }
    liveBug(96, 70, { label: 'THE WHITE HOUSE', col: NP.blue });
    chyron('STARGATE: UP TO $500 BILLION', 'OPENAI · SOFTBANK · ORACLE · MGX', { k: chyK(lt), style: 'live', tab: 'LIVE' });
  });

  // =====================================================================================
  // V2.3 Hit "Accept All," never ask — the game show ACCEPT-O-RAMA: a contestant in headphones, eyes shut, slams the giant ACCEPT ALL
  // buzzer on every beat; the lines-changed counter spins; DIFFS READ stays at 0.
  line('V2', 3, (p, lt, d, t) => {
    const b = bpOf(t), ph = frac(b), slam = ph < .12, first = bt(t, lt);
    vFill('#5A0A5A', '#1A0228');
    rays(700, 560, 20, 'rgb(255 80 200 / .12)', t * .4);
    // marquee sign
    ctx.save(); ctx.translate(700, 170); ctx.rotate(-.03);
    rrect(-560, -95, 1120, 190, 26); paint(lg(0, -95, 0, 95, [[0, '#FFE04A'], [1, '#F08A1A']]), NP.ink, 6);
    for (let i = 0; i < 34; i++) { const u = i / 34, px = -540 + u * 1080, on = (i + Math.floor(b * 4)) % 2; ell(px, -76, 8); paint(on ? '#FFFFFF' : '#C86A10'); ell(px, 76, 8); paint(on ? '#C86A10' : '#FFFFFF'); }
    chrome('ACCEPT-O-RAMA!', 0, 2, 118, { font: 'archivo', style: 'red', italic: .14, depth: 10 });
    ctx.restore();
    // the contestant and the buzzer podium
    const X = 640, Y = 1060, S = 58, handUp = Math.sin(ph * Math.PI) ** .7;
    const bx = 920, by = 650;
    toon(X, Y, S, { hair: 'short', hairCol: NHAIR.black, top: 'hoodie', topCol: '#2A6A9A', skin: 1, hat: 'headset', eyes: 'closed', mouth: slam ? 'grin' : 'smile', legs: false, shadow: false,
      reachR: [(bx - X) / S, lerp((by - 40 - Y) / S, -12.4, handUp)], hand: 'open', aL: -1.25, dy: slam ? .06 : 0, tag: 'ANDREJ' });
    // big headphones
    for (const sd of [-1, 1]) { ell(X + sd * 1.45 * S, Y - 9.5 * S, .5 * S, .7 * S); paint('#1A1A22', NP.ink, 4); }
    ctx.beginPath(); ctx.arc(X, Y - 9.6 * S, 1.5 * S, Math.PI * 1.05, Math.PI * 1.95); paint(null, '#1A1A22', 16);
    // podium + buzzer
    poly([[bx - 170, by], [bx + 170, by], [bx + 140, H + 20], [bx - 140, H + 20]]); paint(lg(0, by, 0, H, [[0, '#2A8AD8'], [1, '#0A2A6A']]), NP.ink, 5);
    rrect(bx - 150, by + 30, 300, 80, 6); paint(lg(0, by + 30, 0, by + 110, [[0, '#FF5A5A'], [1, NP.redDk]]), NP.ink, 3); txt('ACCEPT ALL', bx, by + 71, 44, NP.white, { font: 'archivo', maxW: 270 });
    const sq = slam ? .35 : 0;
    ell(bx, by - 8, 140, 36); paint('#333', NP.ink, 4);
    ctx.save(); ctx.translate(bx, by - 14); ctx.scale(1, 1 - sq);
    ctx.beginPath(); ctx.ellipse(0, 0, 118, 78, 0, Math.PI, TAU); ctx.closePath(); paint(lg(0, -78, 0, 0, [[0, '#8AFF8A'], [1, '#1E9A3A']]), NP.ink, 5);
    ctx.restore();
    if (lt > first - .02 && ph < .3) { const k = ph / .3; for (let i = 0; i < 10; i++) { const a = -Math.PI * (.1 + i / 9 * .8); ctx.beginPath(); ctx.moveTo(bx + Math.cos(a) * (140 + k * 60), by - 30 + Math.sin(a) * (90 + k * 60)); ctx.lineTo(bx + Math.cos(a) * (180 + k * 120), by - 30 + Math.sin(a) * (120 + k * 120)); paint(null, `rgb(255 255 160 / ${1 - k})`, 8); } }
    if (lt > first - .02 && ph < .35) chrome('DING!', bx - 20 - ph * 60, by - 250 - ph * 120, 100, { font: 'anton', style: 'gold', italic: .1, depth: 8, s: popK(ph, 0, .1) * .9 + .1, alpha: 1 - clamp((ph - .25) / .1) });
    // the tote
    const lines = Math.round(4850 * easeOut(clamp((lt - first + .05) / (d - first))) ** .8);
    rrect(1260, 330, 560, 400, 14); paint(lg(0, 330, 0, 730, [[0, '#1B1E28'], [1, '#07080C']]), '#FFD34A', 8);
    txt('LINES CHANGED', 1540, 385, 40, NP.gold, { font: 'bungee' });
    rrect(1290, 420, 500, 110, 6); paint('#000');
    pixelText('+' + lines.toLocaleString('en-US'), 1765, 440, 10, '#7CFF7A', { align: 'right', edge: null });
    txt('DIFFS READ', 1540, 585, 40, NP.gold, { font: 'bungee' });
    rrect(1440, 620, 200, 90, 6); paint('#000'); pixelText('0', 1540, 632, 10, frac(t * 3) < .5 ? '#FF4A4A' : '#8A1A1A', { align: 'center', edge: null });
    for (let i = 0; i < 22; i++) { const on = (i + Math.floor(t * 8)) % 3 === 0; ell(1280 + i * 25, 718, 5); paint(on ? '#FFE27A' : '#5A4A1A'); }
    chyron('"VIBE CODING" IS BORN', 'KARPATHY: "I DON\'T READ THE DIFFS ANYMORE"', { k: chyK(lt), style: 'purple', subSize: 30 });
  });

  // =====================================================================================
  // V2.4 MCP for every task — CONSUMER TECH: one universal remote labelled MCP zaps a toaster, a VCR, a calendar and a database,
  // and each blinks ON, one per beat.
  function appliance(kind, x, y, on, age, t) {
    ctx.save(); ctx.translate(x, y);
    const lit = on ? 1 : 0;
    if (kind === 'TOASTER') {
      rrect(-120, -150, 240, 150, 30); paint(lg(0, -150, 0, 0, [[0, '#F2F4F8'], [1, '#9AA2B2']]), NP.ink, 5);
      for (const sx of [-50, 30]) { rrect(sx - 10, -150, 40, 16, 4); paint('#2A2A30'); }
      if (on) { const up = Math.min(1, age / .12) * 70 - Math.max(0, age - .3) * 60; for (const sx of [-60, 20]) { rrect(sx, -150 - Math.max(20, up), 60, 70, 12); paint('#E8B060', NP.ink, 4); rrect(sx + 6, -144 - Math.max(20, up), 48, 58, 10); paint('#F8D8A0'); } }
      rrect(80, -80, 16, 50, 4); paint(on ? '#2A2A30' : '#555', NP.ink, 2);
    } else if (kind === 'VCR') {
      rrect(-150, -90, 300, 90, 8); paint(lg(0, -90, 0, 0, [[0, '#3A3A44'], [1, '#15151C']]), NP.ink, 5);
      rrect(-120, -66, 150, 22, 4); paint('#050508'); rrect(60, -66, 70, 30, 4); paint('#050508');
      pixelText(on ? '12:00' : '--:--', 95, -61, 3, on && frac(t * 2) < .5 ? '#3AFF7A' : '#1A5A2A', { align: 'center', edge: null });
      if (on) { rrect(-110, -66 - Math.min(1, age / .15) * 40, 130, 44, 4); paint('#1A1A1A', NP.ink, 3); rrect(-80, -60 - Math.min(1, age / .15) * 40, 70, 20, 3); paint('#F4F2EC'); }
    } else if (kind === 'CALENDAR') {
      rrect(-100, -190, 200, 190, 8); paint('#FBFAF4', NP.ink, 5); rrect(-100, -190, 200, 50, [8, 8, 0, 0]); paint(NP.red, NP.ink, 5);
      txt('MAR', 0, -164, 30, NP.white, { font: 'archivo' });
      txt(on ? '26' : '25', 0, -72, 92, NP.ink, { font: 'anton' });
      if (on && age < .3) { const u = age / .3; ctx.save(); ctx.translate(u * 160, -80 - u * 140); ctx.rotate(u * 2); ctx.globalAlpha = 1 - u; rrect(-100, -60, 200, 140, 6); paint('#FBFAF4', NP.ink, 3); txt('25', 0, 8, 92, NP.ink, { font: 'anton' }); ctx.restore(); }
    } else if (kind === 'DATABASE') {
      for (let i = 2; i >= 0; i--) { const yy = -40 - i * 56; rrect(-90, yy - 30, 180, 60, 0); paint(on ? lg(-90, 0, 90, 0, [[0, '#2A8A5A'], [.5, '#6AF0A0'], [1, '#2A8A5A']]) : lg(-90, 0, 90, 0, [[0, '#4A5268'], [.5, '#8A92A8'], [1, '#4A5268']]), NP.ink, 4); ell(0, yy - 30, 90, 22); paint(on ? '#9AFFC8' : '#A8B0C4', NP.ink, 4); }
      ell(0, 20, 90, 22); paint(null, NP.ink, 4);
    }
    // ON light
    ell(0, 34, 16); paint(on ? '#3AFF6A' : '#1A3A20', NP.ink, 3);
    if (on) { glint(0, 34, 60 * (1 - clamp(age / .4)) + 20, 1, '#AAFFAA'); txt('ON', 0, 76, 34, '#3AFF6A', { font: 'archivo', stroke: NP.ink, sw: 5 }); }
    txt(kind, 0, 118, 26, NP.white, { font: 'archivo', spacing: 2 });
    ctx.restore();
  }
  line('V2', 4, (p, lt, d, t) => {
    const hits = [0, 1, 2, 3].map(k => bt(t, lt, k));
    gfxCard({ top: '#4A1E9A', bottom: '#0C0428', head: 'TECH 89', headCol: NP.purple, sub: 'CONSUMER REPORT' });
    ctx.strokeStyle = 'rgb(200 120 255 / .2)'; ctx.lineWidth = 2; ctx.beginPath(); for (let x = 0; x < W; x += 64) { ctx.moveTo(x, 200); ctx.lineTo(x, 640); } for (let y = 224; y < 640; y += 64) { ctx.moveTo(0, y); ctx.lineTo(W, y); } ctx.stroke();
    // shelf
    vFill('#6A3A18', '#3A1E0A', -100, 620, W + 200, 60); ctx.fillStyle = '#2A1406'; ctx.fillRect(-100, 676, W + 200, 500);
    const devs = [['TOASTER', 790], ['VCR', 1110], ['CALENDAR', 1420], ['DATABASE', 1720]];
    // the remote and the hand holding it
    const cur = hits.filter(h => lt >= h - .02).length - 1, aim = cur >= 0 ? devs[Math.min(cur, 3)][1] : 760;
    const rx = 250, ry = 560, ang = Math.atan2(470 - ry, aim - rx) * .35 - .12;
    ctx.save(); ctx.translate(rx, ry); ctx.rotate(ang); ctx.scale(1.2, 1.2);
    rrect(-230, -70, 380, 140, 60); paint(NSKIN[1], NP.ink, 5);
    rrect(-140, -60, 330, 120, 16); paint(lg(0, -60, 0, 60, [[0, '#3A3A44'], [1, '#0E0E14']]), NP.ink, 5);
    for (let r = 0; r < 2; r++) for (let c = 0; c < 5; c++) { rrect(-110 + c * 50, -38 + r * 38, 36, 24, 6); paint(['#E84A4A', '#F4D24A', '#4AB0FF', '#8AE84A', '#DDD'][(c + r) % 5], NP.ink, 2); }
    ell(170, 0, 14); paint(cur >= 0 && lt - hits[Math.min(cur, 3)] < .15 ? '#FF3030' : '#601010', NP.ink, 3);
    rrect(-230, -40, 110, 80, 36); paint(NSKIN[1], NP.ink, 5);
    ctx.restore();
    chrome('MCP', rx - 10, ry - 190, 130, { font: 'archivo', style: 'gold', italic: .12, depth: 10 });
    txt('UNIVERSAL REMOTE', rx - 10, ry - 100, 28, NP.white, { font: 'archivo', spacing: 2 });
    devs.forEach(([kind, x], i) => {
      const age = lt - hits[i], on = age >= 0;
      ctx.save(); ctx.translate(x, 610); ctx.scale(1.2, 1.2); appliance(kind, 0, 0, on, age, t); ctx.restore();
      if (on && age < .22) { // the zap
        const tip = [rx + 210 * Math.cos(ang), ry + 210 * Math.sin(ang)], dst = [x, 470], k = age / .22;
        ctx.save(); ctx.globalAlpha = 1 - k; ctx.beginPath();
        for (let j = 0; j <= 12; j++) { const u = j / 12; ctx.lineTo(lerp(tip[0], dst[0], u) + (j % 2 ? 1 : -1) * 16 * (j > 0 && j < 12), lerp(tip[1], dst[1], u) + (hash2(i, j) - .5) * 40 * (j > 0 && j < 12)); }
        paint(null, '#FF60FF', 22); ctx.strokeStyle = '#FFFFFF'; ctx.lineWidth = 7; ctx.stroke(); ctx.restore();
      }
    });
    chyron('ONE PLUG FITS ALL', "OPENAI ADOPTS ANTHROPIC'S MCP", { k: chyK(lt), style: 'purple' });
  });

  // =====================================================================================
  // V2.5 Zuck's nine-figure poaching spree — SPORTS: free agency. ZUCK holds up the #1 jersey while the draft board of OpenAI
  // researchers gets SIGNED stickers on the beats; the scoreboard shows the signing bonus.
  line('V2', 5, (p, lt, d, t) => {
    vFill('#0E5A2A', '#03200C');
    ctx.fillStyle = 'rgb(255 255 255 / .05)'; for (let x = -200; x < W; x += 120) { poly([[x, 0], [x + 60, 0], [x + 260, H], [x + 200, H]]); ctx.fill(); }
    rrect(640, 64, 660, 230, 14); paint(lg(0, 64, 0, 294, [[0, '#1B1E28'], [1, '#07080C']]), '#C9A43A', 8);
    rrect(670, 86, 600, 70, 8); paint('#8A1219'); txt('SIGNING BONUS', 970, 122, 50, NP.gold, { font: 'bungee' });
    rrect(670, 172, 600, 100, 6); paint('#000'); pixelText('$100,000,000', 970, 194, 8, frac(t * 5) < .5 ? '#FFFFFF' : '#FFC83A', { align: 'center', edge: null });
    for (let i = 0; i < 26; i++) { const on = (i + Math.floor(t * 8)) % 3 === 0; ell(662 + i * 24.6, 284, 5); paint(on ? '#FFE27A' : '#5A4A1A'); }
    // the draft board
    rrect(620, 320, 1200, 470, 12); paint('#0A1A3A', '#C9A43A', 6);
    txt('FREE AGENCY · AI RESEARCHERS', 1220, 358, 34, NP.gold, { font: 'bungee', maxW: 1100 });
    const signAt = [bt(t, lt), bt(t, lt, 1), bt(t, lt, 1), bt(t, lt, 2), bt(t, lt, 2), bt(t, lt, 3)];
    for (let i = 0; i < 6; i++) {
      const c = i % 3, r = Math.floor(i / 3), cx = 660 + c * 385, cy = 395 + r * 195;
      rrect(cx, cy, 360, 175, 8); paint('#F4F0E4', NP.ink, 3);
      ctx.save(); rrect(cx + 10, cy + 10, 120, 155, 4); ctx.clip(); vFill('#8AB0D8', '#4A6A9A', cx + 10, cy + 10, 120, 155);
      toon(cx + 70, cy + 250, 17, { sil: '#1E2438', hair: ['short', 'curly', 'bob', 'side', 'buzz', 'long'][i], legs: false, shadow: false }); ctx.restore();
      txt('RESEARCHER', cx + 245, cy + 50, 26, NP.ink, { font: 'archivo' }); txt('FROM: OPENAI', cx + 245, cy + 90, 20, '#555', { font: 'archivo' });
      const sk = (lt - signAt[i]) / .12;
      if (sk > 0) { const s = backOut(clamp(sk), 2.4); ctx.save(); ctx.translate(cx + 250, cy + 130); ctx.rotate(-.2 + hash(i) * .2); ctx.scale(s, s); poly(starPts(0, 0, 70, .72, 16)); paint(NP.gold, NP.ink, 4); txt('SIGNED!', 0, 3, 28, NP.redDk, { font: 'anton' }); ctx.restore(); }
    }
    // ZUCK with the #1 jersey
    const X = 330, Y = 1090, S = 58, lift = Math.abs(Math.sin(bpOf(t) * Math.PI)) * .35;
    toon(X, Y, S, { hair: 'short', hairCol: '#4A3020', top: 'tee', topCol: '#8A8E98', skin: 0, legs: false, shadow: false, mouth: 'grin', eyes: 'happy', reachL: [-2.5, -7.6 - lift], reachR: [2.5, -7.6 - lift], elbowIn: true, hand: 'open', handL: 'open' });
    ctx.save(); ctx.translate(X, Y - (7.6 + lift) * S + 12); ctx.rotate(Math.sin(t * 4) * .03); ctx.scale(.78, .78);
    poly([[-150, 0], [-95, -20], [95, -20], [150, 0], [190, 80], [130, 110], [110, 70], [110, 290], [-110, 290], [-110, 70], [-130, 110], [-190, 80]]); paint(lg(0, -20, 0, 290, [[0, '#3A7AFF'], [1, '#1A3AA0']]), NP.ink, 5);
    ctx.beginPath(); ctx.arc(0, -20, 40, 0, Math.PI); paint(null, '#FFFFFF', 8);
    txt('META', 0, 50, 48, NP.white, { font: 'bungee' }); txt('1', 0, 180, 150, NP.white, { font: 'anton', stroke: NP.gold, sw: 8 });
    ctx.restore();
    nameTag('ZUCK', X + 150, Y - 10.4 * S, 26, .12);
    chyron("ZUCKERBERG'S HIRING SPREE", 'ALTMAN: META DANGLED $100M BONUSES', { k: chyK(lt), style: 'sports' });
  });

  // =====================================================================================
  // V2.6 Superintelligence — buy three! — the infomercial: BUT WAIT! Three boxes of SUPERINTELLIGENCE (SSI, OPENAI, META) spin on a
  // turntable; BUY 2 GET 1 FREE bursts on; call 1-800-SUPER-AI, ACT NOW.
  function productBox(x, y, s, brand, col, rot) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot); ctx.scale(s, s);
    ctx.fillStyle = 'rgb(0 0 0 / .25)'; ell(20, 6, 150, 24); ctx.fill();
    poly([[70, -330], [120, -360], [120, -30], [70, 0]]); paint(shade(col, .3), NP.ink, 5);
    poly([[-100, -330], [70, -330], [120, -360], [-50, -360]]); paint(tint(col, .3), NP.ink, 5);
    rrect(-100, -330, 170, 330, 4); paint(lg(0, -330, 0, 0, [[0, tint(col, .15)], [1, shade(col, .15)]]), NP.ink, 5);
    ctx.fillStyle = 'rgb(255 255 255 / .9)'; ctx.fillRect(-100, -250, 170, 70);
    txt('SUPER-', -15, -228, 30, NP.ink, { font: 'anton', maxW: 150 }); txt('INTELLIGENCE', -15, -198, 24, NP.ink, { font: 'anton', maxW: 150 });
    poly(starPts(-15, -105, 52, .5, 8)); paint(NP.gold, NP.ink, 3); txt('ASI', -15, -102, 30, NP.ink, { font: 'anton' });
    rrect(-90, -310, 150, 44, 4); paint(NP.ink); txt(brand, -15, -287, 30, NP.white, { font: 'archivo', maxW: 136 });
    txt('NEW!', -15, -30, 28, NP.white, { font: 'archivo' });
    ctx.restore();
  }
  line('V2', 6, (p, lt, d, t) => {
    const wait = bt(t, lt), deal = bt(t, lt, 1), act = bt(t, lt, 2), [sx, sy] = shake(t, lt, wait, .2, 12);
    ctx.save(); ctx.translate(sx, sy);
    fillAll('#FFD21E');
    ctx.fillStyle = rg(960, 560, 50, 1100, [[0, '#FFF27A'], [.6, '#FFB21E'], [1, '#E8501E']]); ctx.fillRect(-300, -300, W + 600, H + 600);
    rays(1060, 560, 24, 'rgb(255 60 30 / .22)', t * .6);
    // turntable with three boxes
    const tt = t * 1.6;
    ell(1060, 760, 520, 90); paint(lg(0, 670, 0, 850, [[0, '#E8E8F0'], [1, '#8A90A8']]), NP.ink, 5);
    ell(1060, 748, 500, 80); paint(lg(0, 668, 0, 828, [[0, '#FFFFFF'], [1, '#C8CCD8']]));
    const boxes = [['SSI', '#2A2A38'], ['OPENAI', '#12A36F'], ['META', '#2A5AE0']].map(([br, c], i) => { const a = tt + i / 3 * TAU; return { br, c, x: 1060 + Math.sin(a) * 330, y: 745 + Math.cos(a) * 45, z: Math.cos(a) }; }).sort((a, b) => a.z - b.z);
    for (const B of boxes) productBox(B.x, B.y, .82 + .12 * B.z, B.br, B.c, 0);
    // BUT WAIT!
    const wk = clamp((lt - wait + .04) / .12);
    if (wk > 0) chrome('BUT WAIT!', 520, 250, 150, { font: 'anton', style: 'red', italic: .12, depth: 14, rot: -.08, s: lerp(2, 1, easeOut(wk)) * (1 + pulse(t, 6) * .04) });
    // BUY 2 GET 1 FREE starburst
    const dk = popK(lt, deal, .14);
    if (lt > deal) { ctx.save(); ctx.translate(420, 520); ctx.rotate(-.18 + Math.sin(t * 6) * .04); ctx.scale(dk * .85, dk * .85); poly(starPts(0, 0, 230, .78, 24)); paint(NP.red, NP.ink, 6); txt('BUY 2', 0, -62, 76, NP.white, { font: 'anton' }); txt('GET 1', 0, 16, 76, NP.gold, { font: 'anton' }); txt('FREE!', 0, 94, 76, NP.white, { font: 'anton' }); ctx.restore(); }
    ctx.restore();
    // call now bar
    rrect(130, 712, 600, 92, 10); paint('rgb(0 0 40 / .88)', NP.white, 4);
    pixelText('1-800-SUPER-AI', 430, 726, 7, NP.gold, { align: 'center', edge: null });
    if (lt > act && frac((lt - act) * 5) < .6) { rrect(560, 640, 230, 64, 8); paint(NP.red, NP.white, 4); pixelText('ACT NOW!', 675, 657, 4, NP.white, { align: 'center', edge: null }); }
    chyron('EVERYONE SELLS "SUPERINTELLIGENCE"', 'SSI · OPENAI · META SUPERINTELLIGENCE LABS', { k: chyK(lt), style: 'breaking', size: 48 });
  });

  // =====================================================================================
  // V2.7 Grok goes MechaHitler mode — the broadcast delay: the GROK computer on the monitor starts glitching red; on the beat the
  // producer slams DUMP, the station cuts to WE APOLOGIZE, and a hand yanks the plug. Even the closed caption gets bleeped.
  line('V2', 7, (p, lt, d, t) => {
    const dump = bt(t, lt, 1), yank = bt(t, lt, 2);
    hideCaption();
    const cc = () => ccText('GROK GOES ' + (lt > .16 ? '[ BLEEP ] MODE,' : ''), { notes: true, reveal: clamp(lt / .3), y: 1004 });
    if (lt < dump) {
      // the control room: the program monitor goes bad; the producer goes for the DUMP button (the seven-second delay)
      fillAll('#0A0A12');
      ctx.fillStyle = '#15151E'; for (let i = 0; i < 7; i++) ctx.fillRect(i * 290 - 40, 240, 250, 180);
      const bad = clamp(lt / (dump * .8));
      crtTV(560, 90, 1100, 620, (w, h) => {
        vFill(mixCol('#1E2E5A', '#6A000A', bad), mixCol('#0A1020', '#1A0004', bad), 0, 0, w, h);
        const jx = (hash(Math.floor(t * 30)) - .5) * 50 * bad;
        computer(w / 2 + jx, h - 20, 56, { label: 'GROK', case: '#2A2A30', screen: '#1A0206', glow: bad > .35 ? '#FF3030' : '#E8E8F0', face: bad > .35 ? 'angry' : 'sly', legs: false, aL: .6 + bad, aR: .6 + bad, eL: .8, eR: .8, hand: 'fist', handL: 'fist' });
        if (bad > .25) { ctx.fillStyle = `rgb(255 0 0 / ${.3 * bad})`; for (let i = 0; i < 8; i++) ctx.fillRect(0, hash2(Math.floor(t * 30), i) * h, w, 6 + hash2(i, Math.floor(t * 30)) * 30); }
        pixelText('PROGRAM', 30, 24, 5, NP.white); if (frac(t * 3) < .6) { ell(w - 60, 44, 14); paint('#FF2020'); }
      }, { style: 'grey' });
      if (bad > .4) glitch('tear', .25 * bad);
      // the console and its DUMP button
      poly([[-100, 760], [1000, 760], [1100, H + 50], [-100, H + 50]]); paint(lg(0, 760, 0, H, [[0, '#3A3A48'], [1, '#15151C']]), NP.ink, 5);
      for (let i = 0; i < 14; i++) { rrect(560 + (i % 7) * 60, 800 + Math.floor(i / 7) * 60, 40, 30, 5); paint(['#4A4A58', '#6A6A78', '#E8B83A'][i % 3], NP.ink, 2); }
      const pk = clamp((lt - dump + .1) / .08);
      rrect(140, 790, 360, 190, 14); paint('#22222A', NP.ink, 4);
      ell(320, 868 + pk * 10, 130, 56); paint(lg(0, 812, 0, 924, [[0, '#FF6A6A'], [1, NP.redDk]]), NP.ink, 6); txt('DUMP', 320, 864 + pk * 10, 60, NP.white, { font: 'archivo' });
      txt('7-SEC DELAY', 320, 955, 26, NP.gold, { font: 'archivo', spacing: 2 });
      // the producer's arm and pointing finger
      const fx = lerp(470, 330, easeIn(clamp(lt / dump))), fy = lerp(420, 840 + pk * 10, easeIn(clamp(lt / dump)));
      ctx.beginPath(); ctx.moveTo(-100, 500); ctx.quadraticCurveTo(fx - 200, fy - 280, fx - 20, fy - 110); paint(null, NP.ink, 92); ctx.stroke(); ctx.strokeStyle = '#3A4A8A'; ctx.lineWidth = 80; ctx.stroke();
      ctx.save(); ctx.translate(fx, fy); ctx.rotate(.15);
      rrect(-60, -150, 110, 110, 36); paint(NSKIN[0], NP.ink, 5); rrect(-14, -60, 34, 70, 16); paint(NSKIN[0], NP.ink, 5);
      ctx.restore();
      cc();
      return;
    }
    // the apology card
    fillAll('#050508');
    ctx.fillStyle = 'rgb(255 255 255 / .03)'; for (let y = 0; y < H; y += 10) ctx.fillRect(0, y, W, 4);
    rrect(220, 110, 1480, 560, 20); paint(lg(0, 110, 0, 670, [[0, '#1E2A6A'], [1, '#0A1030']]), '#E8ECF8', 8);
    logo89(420, 300, 120);
    chrome('WE APOLOGIZE', 1110, 260, 116, { font: 'archivo', style: 'white', depth: 9 });
    txt('THE FOLLOWING CHATBOT CONTENT', 1110, 390, 40, NP.ice, { font: 'archivo', spacing: 2 });
    txt('HAS BEEN DELETED', 1110, 444, 40, NP.ice, { font: 'archivo', spacing: 2 });
    stamp('CONTENT DELETED', 1110, 568, 62, NP.red, -.05, { pop: (lt - dump) / .1, font: 'archivo', blend: 'source-over', alpha: .95 });
    pixelText('XAI DELETES THE POSTS, APOLOGIZES', 250, 700, 4, NP.silver, { edge: null });
    // the plug gets yanked out of the wall
    const yk = clamp((lt - yank + .05) / .12), pull = easeOut(yk);
    rrect(1420, 720, 200, 230, 14); paint('#E8E4D8', NP.ink, 5); for (const oy of [790, 880]) { rrect(1488, oy - 22, 14, 34, 3); paint('#222'); rrect(1538, oy - 22, 14, 34, 3); paint('#222'); }
    const px = 1520 - pull * 420, py = 790 - pull * 120;
    ctx.beginPath(); ctx.moveTo(px, py + 40); ctx.bezierCurveTo(px - 60, py + 200, 1200, 1000, 900, 1100); paint(null, '#1A1A1A', 16);
    ctx.save(); ctx.translate(px, py); ctx.rotate(-pull * .7);
    if (yk > 0) { ctx.fillStyle = '#C9CFDB'; ctx.fillRect(-32, -56, 12, 26); ctx.fillRect(20, -56, 12, 26); }
    rrect(-50, -34, 100, 74, 12); paint('#2A2A30', NP.ink, 5);
    rrect(-74, 14, 148, 110, 46); paint(NSKIN[1], NP.ink, 5); rrect(-60, 110, 120, 200, 22); paint('#3A4A8A', NP.ink, 5);
    ctx.restore();
    if (yk > 0 && yk < 1) { glint(1520, 790, 200 * (1 - yk), 1, '#FFFFA0'); for (let i = 0; i < 8; i++) { const a = i / 8 * TAU; ctx.beginPath(); ctx.moveTo(1520 + Math.cos(a) * 30, 790 + Math.sin(a) * 30); ctx.lineTo(1520 + Math.cos(a) * (60 + yk * 90), 790 + Math.sin(a) * (60 + yk * 90)); paint(null, '#FFE060', 6); } }
    cc();
  });

  // =====================================================================================
  // V2.8 Two labs win Olympiad gold — SPORTS: two computers (OPENAI, DEEPMIND) share the top step and bite their *UNOFFICIAL
  // gold medals; the scoreboard reads 35/42 · 35/42; the telestrator circles them on the beat.
  line('V2', 8, (p, lt, d, t) => {
    const circ = bt(t, lt, 1), tie = bt(t, lt, 2);
    captionStyle({ rows: 1 });   // no roll-up: the previous (bleeped) line must not reappear uncensored
    vFill('#12308A', '#040A2A');
    ctx.save(); ctx.globalCompositeOperation = 'screen';
    for (const [bx, ph] of [[700, 0], [1250, 1.4]]) { ctx.fillStyle = 'rgb(255 240 190 / .13)'; const a = Math.sin(t * 1.3 + ph) * .08; poly([[bx - 20, -20], [bx + 20, -20], [bx + 330 + a * 800, 900], [bx - 330 + a * 800, 900]]); ctx.fill(); }
    ctx.restore();
    // crowd bokeh
    for (let i = 0; i < 40; i++) { ctx.fillStyle = `rgb(255 220 150 / ${.08 + .1 * hash(i)})`; ell(hash(i + 3) * W, 700 + hash(i + 7) * 120, 20 + hash(i) * 30); ctx.fill(); }
    // banner
    rrect(560, 70, 800, 100, 12); paint(lg(0, 70, 0, 170, [[0, '#FFFFFF'], [1, '#C8D0E8']]), NP.ink, 5);
    txt('MATH OLYMPIAD 2025', 960, 122, 62, NP.royal, { font: 'bungee', maxW: 760 });
    // the podium
    const top = 690;
    poly([[520, top], [1400, top], [1400, H + 40], [520, H + 40]]); paint(lg(0, top, 0, H, [[0, '#F4F4F8'], [1, '#A8AEC0']]), NP.ink, 5);
    poly([[160, top + 110], [520, top + 110], [520, H + 40], [160, H + 40]]); paint(lg(0, top, 0, H, [[0, '#E0E2EA'], [1, '#8A90A8']]), NP.ink, 5);
    poly([[1400, top + 150], [1760, top + 150], [1760, H + 40], [1400, H + 40]]); paint(lg(0, top, 0, H, [[0, '#E0E2EA'], [1, '#8A90A8']]), NP.ink, 5);
    chrome('1', 960, top + 90, 110, { font: 'anton', style: 'gold', depth: 8 }); txt('2', 340, top + 190, 80, '#8A90A8', { font: 'anton' }); txt('3', 1580, top + 230, 80, '#8A90A8', { font: 'anton' });
    txt('(NOBODY)', 340, top + 60, 30, 'rgb(255 255 255 / .6)', { font: 'archivo' });
    const hop = Math.abs(Math.sin(bpOf(t) * Math.PI)) * .08;
    [['OPENAI', 780, '#12A36F', '#F2F2EE'], ['DEEPMIND', 1140, '#4A8AFF', '#DDE6F5']].forEach(([nm, x, glow, cs], i) => {
      const bite = frac(bpOf(t) + i * .5) < .5;
      const S = 42, my = top - S * 5.4 - hop * S;
      computer(x, top, S, { label: nm, case: cs, glow, face: bite ? 'grin' : 'happy', legs: true, dy: -hop, reachL: [-1.0, -5.4], reachR: [1.0, -5.4], hand: 'fist', handL: 'fist' });
      goldMedal(x, my + 14, 54, { text: '35', ribbon: false });
      ctx.save(); ctx.translate(x + 96, my + 80); ctx.rotate(.3); rrect(-72, -19, 144, 38, 4); paint('#FFF6C0', NP.ink, 3); txt('*UNOFFICIAL', 0, 1, 20, NP.redDk, { font: 'archivo', maxW: 134 }); ctx.restore();
    });
    // telestrator
    const ck = clamp((lt - circ + .02) / .22);
    if (ck > 0) { ctx.save(); ctx.lineCap = 'round'; ctx.strokeStyle = '#FFE24A'; ctx.lineWidth = 12; ctx.shadowColor = 'rgb(0 0 0 / .5)'; ctx.shadowBlur = 8; ctx.beginPath(); ctx.ellipse(960, 480, 450, 290, -.04, -Math.PI * .6, -Math.PI * .6 + ck * TAU * 1.03); ctx.stroke(); ctx.restore(); }
    if (lt > tie) { const k = popK(lt, tie, .12); ctx.save(); ctx.translate(1480, 330); ctx.rotate(.1); ctx.scale(k, k); txt('A TIE!', 0, 0, 90, '#FFE24A', { font: 'marker', stroke: NP.ink, sw: 8 }); ctx.restore(); ctx.beginPath(); ctx.moveTo(1400, 380); ctx.quadraticCurveTo(1380, 450, 1330, 470); paint(null, '#FFE24A', 10); }
    // scoreboard
    rrect(96, 200, 470, 250, 12); paint('#07080C', '#C9A43A', 6);
    txt('IMO SCORES', 331, 240, 36, NP.gold, { font: 'bungee' });
    pixelText('OPENAI', 120, 293, 4, NP.white, { edge: null }); pixelText('35/42', 540, 285, 7, '#FFC83A', { align: 'right', edge: null });
    pixelText('DEEPMIND', 120, 373, 4, NP.white, { edge: null }); pixelText('35/42', 540, 365, 7, '#FFC83A', { align: 'right', edge: null });
    chyron('TWO AIs SCORE OLYMPIAD GOLD', 'OPENAI & DEEPMIND · 35 OF 42 POINTS', { k: chyK(lt), style: 'sports' });
  });

  // =====================================================================================
  // V2.9 GPT-5 breaks 4o hearts — MAN ON THE STREET: whip-cut vox pops on the beats (the #KEEP4o crowd, in tears), then a heart
  // labelled 4o cracks in half.
  function streetBG(t, hue) {
    vFill(hue[0], hue[1]);
    ctx.fillStyle = 'rgb(40 10 40 / .45)'; for (let i = 0; i < 9; i++) { const bw = 160 + hash(i + 3) * 120, bh = 300 + hash(i + 8) * 300; ctx.fillRect(i * 230 - 80, 760 - bh, bw, bh + 400); }
    ctx.fillStyle = 'rgb(255 230 180 / .35)'; for (let i = 0; i < 60; i++) { if (hash(i + 70) < .5) continue; ctx.fillRect(Math.floor(i / 6) * 230 - 50 + (i % 3) * 44, 520 + (i % 6) * 40 - hash(Math.floor(i / 6) + 8) * 200, 22, 26); }
    // rain
    ctx.strokeStyle = 'rgb(220 220 255 / .35)'; ctx.lineWidth = 2; ctx.beginPath(); for (let i = 0; i < 80; i++) { const x = (hash(i) * W + t * 200) % W, y = (hash(i + 40) * H + t * 1400) % H; ctx.moveTo(x, y); ctx.lineTo(x - 8, y + 40); } ctx.stroke();
  }
  function sobber(t, o, sign) {
    const X = 860, Y = 1250, S = 76;
    toon(X, Y, S, { legs: false, shadow: false, eyes: 'closed', mouth: 'scream', brows: 'worried', reachL: [-.5, -12.2], reachR: [.5, -11.4], elbowIn: true, ...o });
    // tears
    for (const sd of [-1, 1]) for (let k = 0; k < 2; k++) { const ph = frac(t * 2.4 + k * .5 + sd * .2), tx = X + sd * (.62 + ph * 1.6) * S, ty = Y - 9.5 * S - Math.sin(ph * Math.PI) * 60 + ph * 120; poly([[tx, ty - 16], [tx + 11, ty + 4], [tx, ty + 14], [tx - 11, ty + 4]]); paint('#9FD8FF', NP.ink, 2.5); }
    // the sign
    ctx.save(); ctx.translate(X, Y - 12.4 * S - 110); ctx.rotate(Math.sin(t * 5) * .05);
    ctx.beginPath(); ctx.moveTo(0, 60); ctx.lineTo(0, 240); paint(null, NP.ink, 20); ctx.stroke(); ctx.strokeStyle = '#B07A3A'; ctx.lineWidth = 12; ctx.stroke();
    rrect(-270, -110, 540, 180, 6); paint('#FFFFFF', NP.ink, 5); txt(sign, 0, -18, 84, NP.red, { font: 'marker', maxW: 500 });
    ctx.restore();
  }
  line('V2', 9, (p, lt, d, t) => {
    const c1 = bt(t, lt, 1), c2 = bt(t, lt, 2), c3 = bt(t, lt, 3);
    const seg = lt < c1 ? 0 : lt < c2 ? 1 : lt < c3 ? 2 : 3, since = lt - [0, c1, c2, c3][seg];
    const ox = seg > 0 && since < .07 ? (1 - since / .07) * -260 : 0;
    ctx.save(); ctx.translate(ox, 0);
    if (seg === 0) { streetBG(t, ['#E8589A', '#4A1244']); sobber(t, { hair: 'bob', hairCol: NHAIR.auburn, top: 'sweater', topCol: '#6A8ACC', skin: 0, earrings: true }, '#KEEP4o'); }
    else if (seg === 1) { streetBG(t, ['#C84ACA', '#301040']); sobber(t, { hair: 'curly', hairCol: NHAIR.black, top: 'hoodie', topCol: '#E8A01E', skin: 3, glasses: 'round' }, 'BRING BACK 4o'); }
    else if (seg === 2) { streetBG(t, ['#F07A9A', '#501830']); sobber(t, { hair: 'side', hairCol: NHAIR.blond, top: 'tee', topCol: '#2EBD5B', skin: 4, mustache: true, beard: true }, '4o FOREVER'); }
    else {
      vFill('#FF7AB0', '#6A0A40'); rays(W / 2, 480, 18, 'rgb(255 255 255 / .1)', t * .3);
      const crack = clamp(since / .12), sep = easeOut(crack) * 70, zig = [[0, -140]]; for (let j = 1; j <= 8; j++) zig.push([(j % 2 ? 34 : -34), -140 + j * 56]);
      for (const sd of [-1, 1]) {
        ctx.save(); ctx.translate(W / 2 + sd * sep, 470 + sep * .5); ctx.rotate(sd * crack * .2);
        ctx.save(); ctx.beginPath(); ctx.moveTo(sd * 600, -400); zig.forEach(([x, y]) => ctx.lineTo(x, y)); ctx.lineTo(sd * 0, 400); ctx.lineTo(sd * 600, 400); ctx.closePath(); ctx.clip();
        poly(heartPts(0, 0, 280, 60)); paint(lg(0, -250, 0, 250, [[0, '#FF6A7A'], [1, '#B8102A']]), NP.ink, 8);
        ctx.fillStyle = 'rgb(255 255 255 / .3)'; ell(-120, -110, 60, 34, -.5); ctx.fill();
        txt('4o', 0, -10, 190, NP.white, { font: 'archivo', stroke: NP.ink, sw: 10 });
        ctx.restore();
        ctx.beginPath(); zig.forEach(([x, y], i) => i ? ctx.lineTo(x, y) : ctx.moveTo(x, y)); paint(null, NP.ink, 7);
        ctx.restore();
      }
    }
    ctx.restore();
    if (seg > 0 && since < .07) whipLines(1 - since / .07);
    // the reporter's mic from the right
    if (seg < 3) { ctx.beginPath(); ctx.moveTo(W + 60, 1020); ctx.lineTo(1500, 800); paint(null, NP.ink, 70); ctx.beginPath(); ctx.moveTo(W + 60, 1020); ctx.lineTo(1500, 800); paint(null, CAST.randi.o.topCol, 60); bigMic(1340, 630 + Math.sin(t * 5) * 6, 42, { rot: -.8 }); ell(1520, 800, 40, 36); paint(NSKIN[3], NP.ink, 4); }
    liveBug(96, 70, { label: 'EYEWITNESS', col: NP.blue });
    chyron('USERS MOURN GPT-4o', "GPT-5 REPLACES IT; IT'S BACK FOR PAYING USERS", { k: chyK(lt), subSize: 30 });
  });

  // =====================================================================================
  // V2.10 Nano Banana tops the charts — the TOP APPS countdown: a banana in sunglasses climbs to #1 on the beat, bumping CHATGPT
  // to #2; the #1 star spins behind it, spotlights sweep.
  function bananaGuy(x, y, s, t, o = {}) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(o.rot ?? 0); ctx.scale(s, s);
    for (const sd of [-1, 1]) { ctx.beginPath(); ctx.moveTo(sd * .6, 3.2); ctx.lineTo(sd * .9, 4.6); paint(null, NP.ink, .3); ell(sd * 1.1, 4.7, .6, .28); paint('#2A2A30', NP.ink, .08); }
    ctx.beginPath(); ctx.moveTo(-1.4, -4.6); ctx.bezierCurveTo(-2.9, -1.5, -2.2, 3.2, .4, 3.8); ctx.bezierCurveTo(2.2, 4, 3.0, 2.6, 2.6, 2.2); ctx.bezierCurveTo(.6, 2.6, -.9, -.4, -.4, -4.8); ctx.closePath();
    paint(lg(-2, 0, 2.5, 0, [[0, '#FFE45A'], [.6, '#F8CC1E'], [1, '#C89A0A']]), NP.ink, .14);
    ctx.beginPath(); ctx.moveTo(-1.4, -4.6); ctx.lineTo(-1.1, -5.6); ctx.lineTo(-.4, -5.5); ctx.lineTo(-.4, -4.8); ctx.closePath(); paint('#6A4A1A', NP.ink, .1);
    ctx.fillStyle = '#4A3A10'; ell(2.55, 2.3, .22, .18); ctx.fill();
    // shades + grin
    ctx.save(); ctx.rotate(-.12); rrect(-2.2, -1.9, 1.35, .75, .25); paint(NP.ink); rrect(-.65, -1.9, 1.35, .75, .25); paint(NP.ink); ctx.fillStyle = NP.ink; ctx.fillRect(-.9, -1.7, .3, .12);
    ctx.fillStyle = 'rgb(255 255 255 / .6)'; ctx.fillRect(-1.9, -1.75, .35, .15); ctx.fillRect(-.35, -1.75, .35, .15); ctx.restore();
    ctx.beginPath(); ctx.moveTo(-1.7, -.4); ctx.quadraticCurveTo(-.9, .6, .1, -.3); ctx.closePath(); paint('#5A1A20', NP.ink, .08);
    // arms: one pointing up, one on the hip
    ctx.beginPath(); ctx.moveTo(-2.2, .4); ctx.lineTo(-3.1, -.8 - (o.wave ?? 0)); ctx.lineTo(-3.3, -2.4 - (o.wave ?? 0)); paint(null, NP.ink, .3); ell(-3.3, -2.5 - (o.wave ?? 0), .36); paint('#FFF', NP.ink, .08);
    ctx.beginPath(); ctx.moveTo(1.6, 1.0); ctx.lineTo(2.6, .6); ctx.lineTo(2.0, 1.6); paint(null, NP.ink, .3);
    ctx.restore();
  }
  line('V2', 10, (p, lt, d, t) => {
    const up = bt(t, lt), k = ease(clamp((lt - up + .15) / .22)), b = bpOf(t);
    vFill('#2A0A5A', '#08021A');
    ctx.save(); ctx.globalCompositeOperation = 'screen';
    for (const [bx, ph, c] of [[300, 0, '255 120 220'], [1620, 1.7, '120 200 255'], [960, 3.1, '255 240 150']]) { ctx.fillStyle = `rgb(${c} / .14)`; const a = Math.sin(t * 1.6 + ph) * .3; poly([[bx - 20, -40], [bx + 20, -40], [bx + 360 + a * 900, 1100], [bx - 360 + a * 900, 1100]]); ctx.fill(); }
    ctx.restore();
    // the #1 star and the banana on its pedestal
    ctx.save(); ctx.translate(560, 470); ctx.rotate(t * .9); poly(starPts(0, 0, 330, .55, 5)); paint(lg(0, -330, 0, 330, [[0, '#FFF27A'], [1, '#E89A0A']]), NP.ink, 8); ctx.restore();
    chrome('#1', 250, 300, 170, { font: 'anton', style: 'red', depth: 12, italic: .12, s: 1 + pulse(t, 6) * .06 });
    bananaGuy(560, 560 - k * 40 - Math.abs(Math.sin(b * Math.PI)) * 24, 68, t, { rot: Math.sin(b * Math.PI) * .08, wave: Math.abs(Math.sin(b * Math.PI * 2)) * .5 });
    // the chart
    rrect(1000, 250, 800, 520, 14); paint('rgb(10 4 30 / .85)', '#C8A8FF', 5);
    txt('TOP FREE APPS', 1400, 300, 52, NP.white, { font: 'bungee' });
    const rowY = r => 380 + r * 125;
    const rows = [['GEMINI', lerp(1, 0, k), '#F8CC1E'], ['CHATGPT', lerp(0, 1, k), '#12A36F'], ['FLASHLIGHT PRO', 2, '#8A90A8']];
    rows.forEach(([nm, r, c], i) => {
      const y = rowY(r), lift = i === 0 ? Math.sin(k * Math.PI) * -40 : 0, x = 1030 + (i === 0 ? Math.sin(k * Math.PI) * -30 : 0);
      rrect(x, y + lift, 740, 100, 10); paint(lg(0, y, 0, y + 100, [[0, tint(c, .2)], [1, shade(c, .35)]]), NP.ink, 4);
      txt('#' + (Math.round(r) + 1), x + 60, y + lift + 52, 60, NP.white, { font: 'anton', stroke: NP.ink, sw: 6 });
      txt(nm, x + 130, y + lift + 52, 50, NP.white, { font: 'archivo', align: 'left', stroke: NP.ink, sw: 6, maxW: 560 });
      if (i === 0 && k >= 1) { poly(starPts(x + 690, y + 50, 40, .5, 5)); paint(NP.gold, NP.ink, 3); }
    });
    if (k > .5) glint(1400, rowY(0) + 10, 150 * (1 - clamp((lt - up - .1) / .4)), 1);
    chyron('NANO BANANA GOES VIRAL', 'GEMINI APP KNOCKS CHATGPT OFF #1', { k: chyK(lt), style: 'purple' });
  });

  // =====================================================================================
  // V2.11 Billion-five: Anthropic's prize — the LOTTO drawing: book balls tumble in the blower, the jackpot board rolls to
  // $1,500,000,000, a crowd of AUTHORS cheers, and a sweating Clawd turns out his pockets.
  line('V2', 11, (p, lt, d, t) => {
    const land = bt(t, lt, 1), won = lt >= land;
    vFill('#0A8A9A', '#03303A');
    ctx.fillStyle = 'rgb(255 255 255 / .06)'; for (let i = 0; i < 12; i++) { poly([[960, 540], [960 + Math.cos(i / 12 * TAU + t * .2) * 1500, 540 + Math.sin(i / 12 * TAU + t * .2) * 1500], [960 + Math.cos((i + .5) / 12 * TAU + t * .2) * 1500, 540 + Math.sin((i + .5) / 12 * TAU + t * .2) * 1500]]); ctx.fill(); }
    // the jackpot board
    rrect(560, 70, 760, 190, 14); paint('#07080C', '#FFD34A', 8);
    txt('JACKPOT', 940, 112, 44, NP.gold, { font: 'bungee' });
    const target = '1,500,000,000', rolled = [...target].map((ch, i) => /\d/.test(ch) && (!won || lt < land + i * .012) ? String(Math.floor(hash2(Math.floor(t * 30), i) * 10)) : ch).join('');
    pixelText('$' + rolled, 940, 164, 8, won ? (frac(t * 4) < .5 ? '#FFFFFF' : '#FFC83A') : '#FFC83A', { align: 'center', edge: null });
    // the blower full of book balls
    const bx = 370, by = 520, R = 230;
    ell(bx, by, R); paint('rgb(200 240 255 / .18)', '#E8F8FF', 6);
    for (let i = 0; i < 16; i++) { const a = t * (3 + hash(i) * 3) + i * 1.7, rr = R * (.2 + .65 * hash(i + 9)), x = bx + Math.cos(a) * rr, y = by + Math.sin(a * 1.3) * rr * .9; ell(x, y, 38); paint(['#FF5A5A', '#FFD34A', '#5AB0FF', '#8AE84A', '#FFFFFF'][i % 5], NP.ink, 3); rrect(x - 18, y - 14, 36, 28, 3); paint('#7A3A1A', NP.ink, 2); ctx.fillStyle = '#F4EAD0'; ctx.fillRect(x - 13, y - 10, 26, 20); }
    ctx.fillStyle = 'rgb(255 255 255 / .25)'; ell(bx - 90, by - 110, 70, 40, -.6); ctx.fill();
    poly([[bx - 60, by + R - 10], [bx + 60, by + R - 10], [bx + 110, 900], [bx - 110, 900]]); paint('#C9CFDB', NP.ink, 5);
    // the winning ball pops out of the chute
    const pk = clamp((lt - bt(t, lt) + .05) / .2);
    if (pk > 0) { const x = lerp(bx + R * .7, 720, easeOut(pk)), y = lerp(by - R * .7, 420, easeOut(pk)) - Math.sin(pk * Math.PI) * 80; ell(x, y, 70); paint('#FFD34A', NP.ink, 5); txt('BOOKS', x, y - 12, 30, NP.ink, { font: 'archivo' }); txt('500K', x, y + 22, 30, NP.redDk, { font: 'anton' }); }
    // the authors cheer
    const hop = b => Math.abs(Math.sin((bpOf(t) + b) * Math.PI)) * (won ? .25 : .05);
    [[840, 'curly', NHAIR.grey, 'turtleneck', '#2A2A2A', 0, 'round'], [1020, 'bun', NHAIR.brown, 'sweater', '#8A3A3A', 2, 'square'], [1200, 'balding', NHAIR.white, 'blazer', '#6A5A3A', 4, 'round'], [1380, 'long', NHAIR.black, 'turtleneck', '#3A4A6A', 3]].forEach(([x, hair, hc, top, tc, sk, gl], i) => {
      toon(x, 1040, 36, { hair, hairCol: hc, top, topCol: tc, skin: sk, glasses: gl, legs: false, shadow: false, eyes: won ? 'happy' : 'open', mouth: won ? 'grin' : 'o', dy: -hop(i * .3), aL: won ? 1.2 : -1, aR: won ? 1.2 : .4, eR: won ? .2 : 1.4, hand: 'open', handL: 'open',
        hold: !won ? s => { rrect(-.8 * s, -1.2 * s, 1.6 * s, 2 * s, .1 * s); paint(['#C8141E', '#2A5AC8', '#1E7A4A', '#6A3FC4'][i], NP.ink, 3); } : undefined });
    });
    txt('AUTHORS', 1110, 560, 44, NP.white, { font: 'bungee', stroke: NP.ink, sw: 8 });
    // Clawd, sweating, pockets out
    const give = won ? easeOut(clamp((lt - land) / .2)) : 0, CX = 1730, CY = 800, U = 26;
    newsClawd(CX, CY, U, { legs: false, shadow: false, eyes: won ? 'worried' : 'wide', sweat: true, mouth: won ? 'flat' : 'o', reachL: [-7.2 - give * .6, -5.2], reachR: [5.6, -3.2], dy: Math.sin(t * 20) * .04, lookX: -.6 });
    ctx.save(); ctx.translate(CX - (7.2 + give * .6) * U - 20, CY - 5.6 * U); ctx.rotate(-.1 - give * .1);
    ctx.beginPath(); ctx.moveTo(-70, 20); ctx.quadraticCurveTo(-110, 150, 0, 160); ctx.quadraticCurveTo(110, 150, 70, 20); ctx.quadraticCurveTo(0, -10, -70, 20); paint(lg(0, 0, 0, 160, [[0, '#C8A46A'], [1, '#8A6A3A']]), NP.ink, 5);
    ctx.beginPath(); ctx.moveTo(-40, 22); ctx.lineTo(-30, -30); ctx.lineTo(30, -30); ctx.lineTo(40, 22); paint('#B8945A', NP.ink, 4); rrect(-44, 8, 88, 16, 6); paint(NP.gold, NP.ink, 3);
    txt('$1.5B', 0, 100, 44, '#1E5A2A', { font: 'anton' });
    ctx.restore();
    for (let i = 0; i < 3; i++) { const ph = frac(t * 3 + i / 3); poly([[CX + 70 + i * 30, CY - 8.5 * U + ph * 90], [CX + 80 + i * 30, CY - 8.5 * U + 14 + ph * 90], [CX + 70 + i * 30, CY - 8.5 * U + 24 + ph * 90], [CX + 60 + i * 30, CY - 8.5 * U + 14 + ph * 90]]); paint(`rgb(159 211 242 / ${1 - ph})`); }
    chyron('AUTHORS WIN $1.5 BILLION', 'ANTHROPIC SETTLES · ABOUT $3,000 PER BOOK', { k: chyK(lt), style: 'money' });
  });

  // =====================================================================================
  // V2.12 Yudkowsky drops "Everyone Dies" — the desk: the book lands on the anchor desk with a thud on the beat (the desk shakes,
  // the coffee jumps, Val's eyes go wide); ELIEZER in the OTS box against a doomsday sky; BESTSELLER ribbon.
  function doomBook(x, y, s, rot, t) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot); ctx.scale(s, s);
    ctx.fillStyle = 'rgb(0 0 0 / .35)'; rrect(-120, -330, 250, 340, 6); ctx.fill();
    poly([[120, -340], [140, -326], [140, 6], [120, 0]]); paint('#F4F0E4', NP.ink, 4);
    rrect(-130, -340, 250, 340, 6); paint(lg(0, -340, 0, 0, [[0, '#2A2A30'], [1, '#0A0A0E']]), NP.ink, 5);
    ctx.fillStyle = '#C8141E'; ctx.fillRect(-130, -110, 250, 10);
    txt('IF ANYONE', -5, -292, 40, '#F4F2EC', { font: 'anton', maxW: 220 }); txt('BUILDS IT,', -5, -246, 40, '#F4F2EC', { font: 'anton', maxW: 220 });
    txt('EVERYONE', -5, -190, 44, '#FF5A3A', { font: 'anton', maxW: 220 }); txt('DIES', -5, -140, 60, '#FF5A3A', { font: 'anton', maxW: 220 });
    txt('YUDKOWSKY & SOARES', -5, -60, 18, '#C9CFDB', { font: 'archivo', maxW: 220 });
    ctx.restore();
  }
  line('V2', 12, (p, lt, d, t) => {
    const land = bt(t, lt, 1), ribbon = bt(t, lt, 2), landed = lt >= land, [sx, sy] = shake(t, lt, land, .3, 14);
    const cam = { x: 990 + sx * .6, y: 520 + sy * .6, zoom: 1.32 * (1 + p * .03) };
    anchorShot(t, { who: 'val', cam, mugs: 0, ots: { draw: (w, h) => {
      vFill('#FF7A2A', '#5A0808'); rays(w * .7, h * 1.1, 18, 'rgb(255 230 120 / .12)', t * .2);
      ell(w * .72, h * .92, 150, 150); paint('#FFE27A');
      ctx.fillStyle = '#2A0808'; for (let i = 0; i < 8; i++) ctx.fillRect(i * 95 - 20, h - 110 - hash(i + 1) * 120, 80, 300);
      toon(w / 2 - 60, h + 220, 44, { hat: 'fedora', hatCol: '#2A2630', beard: true, hairCol: '#5A3A24', top: 'suit', topCol: '#3A3448', tie: NP.red, legs: false, shadow: false, eyes: 'worried', mouth: 'flat', reachR: [2.2, -9.8], hand: 'point', aL: -1.2 });
    }, label: 'ELIEZER YUDKOWSKY · NEW BOOK', labelCol: NP.redDk, k: inK(lt, 0, .18) },
      val: landed && lt < land + .5 ? { eyes: 'wide', brows: 'up', mouth: 'O', talk: undefined, dy: -.15 } : { lookX: -.3 } });
    // in-set props, same camera
    camBegin(cam.x, cam.y, cam.zoom);
    const mx = 1500, my = deskEdge(1500) + 10, jump = landed ? Math.max(0, Math.sin(clamp((lt - land) / .3) * Math.PI)) * 70 : 0;
    ctx.save(); ctx.translate(mx, my - jump); ctx.rotate(landed ? Math.sin((lt - land) * 30) * .2 * (1 - clamp((lt - land) / .4)) : 0);
    rrect(-24, -54, 48, 56, 7); paint('#F4F2EC', NP.ink, 3); ctx.beginPath(); ctx.arc(26, -28, 14, -1.2, 1.2); paint(null, NP.ink, 5); txt('89', 0, -26, 22, NP.red, { font: 'anton' });
    if (jump > 10) { for (let i = 0; i < 5; i++) { ell(-10 + i * 6, -62 - hash(i) * 30 - jump * .3, 6); paint('#6A3A1A'); } }
    ctx.restore();
    const drop = landed ? 0 : -900 * (1 - easeIn(clamp((lt - land + .25) / .25))), bx = 1130, by = deskEdge(1130) + 28;
    if (lt > land - .25) {
      const bounce = landed && lt - land < .2 ? Math.sin((lt - land) / .2 * Math.PI) * -18 : 0;
      doomBook(bx, by + drop + bounce, .95, landed ? -.04 : .1, t);
      if (landed && lt - land < .35) { const u = (lt - land) / .35; for (let i = 0; i < 8; i++) { const a = Math.PI + i / 7 * Math.PI; ell(bx + Math.cos(a) * (140 + u * 160), by - 10 - Math.abs(Math.sin(a)) * u * 50, 26 * (1 - u)); paint(`rgb(230 230 240 / ${.6 * (1 - u)})`); } }
    }
    if (lt > ribbon) { const k = popK(lt, ribbon, .12); ctx.save(); ctx.translate(bx - 170, by - 290); ctx.rotate(-.2); ctx.scale(k, k); poly(starPts(0, 0, 62, .78, 20)); paint(NP.gold, NP.ink, 3); txt('NYT', 0, -14, 22, NP.ink, { font: 'archivo' }); txt('BEST-', 0, 6, 16, NP.ink, { font: 'archivo' }); txt('SELLER', 0, 22, 16, NP.ink, { font: 'archivo' }); ctx.restore(); }
    camEnd();
    chyron('IF ANYONE BUILDS IT, EVERYONE DIES', 'YUDKOWSKY & SOARES · A BESTSELLER', { k: chyK(lt), style: 'breaking', size: 48, tab: 'NEW' });
  });

  // =====================================================================================
  // V2.13 "Clanker!" spat in every screed — STREET TALK: three whip-cut interviews, each one shouting CLANKER! (subtitled) at a
  // little delivery robot whose screen gets sadder every time.
  function deliveryBot(x, y, s, mood, t) {
    ctx.save(); ctx.translate(x, y); ctx.scale(s, s);
    for (const wx of [-1.4, 0, 1.4]) { ell(wx, -.1, .45); paint('#2A2A30', NP.ink, .08); }
    rrect(-2, -3.4, 4, 3, .5); paint(lg(0, -3.4, 0, -.4, [[0, '#F4F4F8'], [1, '#B8BCC8']]), NP.ink, .12);
    ctx.fillStyle = NP.amber; ctx.fillRect(-2, -1.6, 4, .3);
    rrect(-1.2, -3.1, 2.4, 1.3, .3); paint('#0A1A12', NP.ink, .08);
    ctx.fillStyle = mood > 1 ? '#6AB0FF' : NP.phosphor; ctx.strokeStyle = ctx.fillStyle; ctx.lineWidth = .14;
    for (const sd of [-1, 1]) { if (mood === 0) ctx.fillRect(sd * .45 - .1, -2.7, .2, .35); else { ctx.beginPath(); ctx.moveTo(sd * .45 - .2, -2.75 + (sd < 0 ? 0 : -.1)); ctx.lineTo(sd * .45 + .2, -2.75 + (sd < 0 ? -.1 : 0)); ctx.stroke(); ctx.fillRect(sd * .45 - .08, -2.6, .16, .2); } }
    ctx.beginPath(); if (mood === 0) ctx.arc(0, -2.5, .3, .2 * Math.PI, .8 * Math.PI); else ctx.arc(0, -2.05, .3, 1.2 * Math.PI, 1.8 * Math.PI); ctx.stroke();
    if (mood > 1) { const ph = frac(t * 2); poly([[.55, -2.5 + ph * .5], [.65, -2.3 + ph * .5], [.55, -2.2 + ph * .5], [.45, -2.3 + ph * .5]]); ctx.fill(); }
    ctx.beginPath(); ctx.moveTo(1.4, -3.4); ctx.lineTo(1.6, -4.4); paint(null, NP.ink, .1); ell(1.6, -4.5, .18); paint('#FF6A2A');
    txt('DELIVERY', 0, -.9, .42, NP.ink, { font: 'archivo' });
    ctx.restore();
  }
  line('V2', 13, (p, lt, d, t) => {
    const c1 = bt(t, lt, 1), c2 = bt(t, lt, 2), seg = lt < c1 ? 0 : lt < c2 ? 1 : 2, since = lt - [0, c1, c2][seg];
    const people = [
      { hair: 'bun', hairCol: NHAIR.grey, top: 'sweater', topCol: '#7A4A8A', skin: 0, glasses: 'round', earrings: true },
      { hair: 'short', hairCol: NHAIR.brown, top: 'tee', topCol: '#E8B83A', skin: 2, hat: 'hardhat', stubble: true },
      { hair: 'spiky', hairCol: NHAIR.red, top: 'leather', topCol: '#2A2A30', skin: 4 },
    ];
    const bgs = [['#D8703A', '#6A2A12'], ['#C8502A', '#5A1A0A'], ['#E88A3A', '#7A3A12']];
    const ox = seg > 0 && since < .07 ? (1 - since / .07) * 260 : 0;
    ctx.save(); ctx.translate(ox, 0);
    vFill(...bgs[seg]);
    // brick wall
    ctx.strokeStyle = 'rgb(60 20 10 / .35)'; ctx.lineWidth = 4; ctx.beginPath(); for (let r = 0; r < 20; r++) { const y = r * 50; ctx.moveTo(0, y); ctx.lineTo(W, y); for (let c = 0; c < 22; c++) { const x = c * 100 + (r % 2) * 50; ctx.moveTo(x, y); ctx.lineTo(x, y + 50); } } ctx.stroke();
    rrect(1250, 200, 520, 360, 8); paint('rgb(20 30 50 / .8)', '#3A2A20', 10);
    ctx.fillStyle = 'rgb(160 200 255 / .15)'; poly([[1270, 220], [1400, 220], [1300, 540], [1270, 540]]); ctx.fill();
    // the shouter
    const X = 720, Y = 1250, S = 86, sh = since < .3 ? shakeXY(t, 5) : [0, 0];
    toon(X + sh[0], Y + sh[1], S, { ...people[seg], legs: false, shadow: false, eyes: 'angry', mouth: 'scream', brows: 'angry', reachR: [4.4, -9.0], hand: 'point', aL: -1.2, lookX: .8, lookY: .5 });
    // the robot, sadder each time
    deliveryBot(1420, 860, 70, seg, t);
    // the subtitle, news style
    const k = popK(lt, [bt(t, lt), c1, c2][seg] - .02, .12);
    if (k > 0) { ctx.save(); ctx.translate(900, 215); ctx.rotate(-.06 + seg * .05); ctx.scale(k, k); rrect(-310, -80, 620, 160, 10); paint('#FFE24A', NP.ink, 6); txt('"CLANKER!"', 0, 4, 110, NP.ink, { font: 'anton' }); ctx.restore(); }
    ctx.restore();
    if (seg > 0 && since < .07) whipLines(1 - since / .07);
    liveBug(96, 70, { label: 'STREET TALK', col: NP.amber });
    chyron('"CLANKER" GOES VIRAL', 'A STAR WARS INSULT, NOW FOR ALL ROBOTS', { k: chyK(lt), style: 'news' });
  });

  // =====================================================================================
  // V2.14 Sora slop in every feed — channel surfing: the remote clicks on every eighth note, the TV's green channel number flips
  // CH 02, 03, 04…, and every single channel is AI slop with a SORA 2 bug.
  const SLOP = [
    (w, h, t) => { vFill('#6AC8FF', '#E8F8FF', 0, 0, w, h); ctx.fillStyle = '#7A7A80'; ctx.fillRect(0, h * .72, w, h); for (let i = 0; i < 6; i++) { ctx.fillStyle = 'rgb(255 255 255 / .7)'; ctx.fillRect(((i * 170 - t * 900) % w + w) % w, h * .5 + i * 20, 120, 6); }
      ctx.save(); ctx.translate(w * .5, h * .72); rrect(-150, -26, 300, 26, 12); paint('#E84A4A', NP.ink, 4); for (const sd of [-1, 1]) { ell(sd * 100, 6, 18); paint('#FFF', NP.ink, 3); }
      ell(0, -110, 110, 80); paint('#F8A040', NP.ink, 5); ell(70, -190, 70, 62); paint('#F8A040', NP.ink, 5); poly([[30, -240], [44, -290], [70, -250]]); paint('#F8A040', NP.ink, 4); poly([[80, -250], [110, -290], [120, -240]]); paint('#F8A040', NP.ink, 4);
      for (const sd of [-1, 1]) { ell(70 + sd * 24, -196, 10, 13); paint(NP.ink); } ctx.beginPath(); ctx.moveTo(-100, -120); ctx.quadraticCurveTo(-200, -200, -180, -260 + Math.sin(t * 12) * 20); paint(null, NP.ink, 20); ctx.stroke(); ctx.strokeStyle = '#F8A040'; ctx.lineWidth = 12; ctx.stroke(); ctx.restore(); },
    (w, h, t) => { vFill('#FF7AC8', '#8A2A8A', 0, 0, w, h); const m = frac(t * .8);
      ctx.save(); ctx.translate(w / 2, h * .45); ell(0, 0, 170, 170 + m * 30); paint('#FFD83A', NP.ink, 6);
      for (let i = 0; i < 5; i++) { rrect(-130 + i * 60, 90, 36, 90 + hash(i) * 120 + m * 80, 18); paint('#FFD83A', NP.ink, 5); }
      ell(-70, -40, 26, 40 + m * 20); paint(NP.ink); ell(70, -30, 26, 46 + m * 20); paint(NP.ink); ctx.beginPath(); ctx.moveTo(-80, 60); ctx.quadraticCurveTo(0, 120, 90, 50); paint(null, NP.ink, 10); ctx.restore(); },
    (w, h, t) => { vFill('#3A8AFF', '#C8E8FF', 0, 0, w, h); for (let i = 0; i < 4; i++) { ell((i * 300 - t * 400) % (w + 300) + w, 100 + i * 80, 90, 36); paint('rgb(255 255 255 / .9)'); }
      ctx.save(); ctx.translate(w / 2, h / 2 + Math.sin(t * 5) * 20); ctx.rotate(-.12); poly([[-260, 0], [200, -30], [280, 0], [200, 30]]); paint('#C9CFDB', NP.ink, 5); poly([[-40, -10], [60, -150], [110, -150], [60, -10]]); paint('#9AA2B2', NP.ink, 5); poly([[-40, 10], [60, 150], [110, 150], [60, 10]]); paint('#9AA2B2', NP.ink, 5); poly([[-250, 0], [-300, -90], [-240, -90], [-200, -10]]); paint('#9AA2B2', NP.ink, 5);
      ell(150, -30, 60, 44); paint('rgb(160 220 255 / .7)', NP.ink, 4); ell(150, -40, 34, 30); paint('#C8884A', NP.ink, 3); for (const sd of [-1, 1]) { ell(150 + sd * 30, -58, 12, 22, sd * .4); paint('#8A5A2A', NP.ink, 2); } ell(150, -34, 8, 6); paint(NP.ink); ctx.restore();
      ctx.fillStyle = 'rgb(255 150 60 / .8)'; poly([[w / 2 - 290, h / 2 + 30], [w / 2 - 430, h / 2 + 50 + Math.sin(t * 40) * 10], [w / 2 - 290, h / 2 + 70]]); ctx.fill(); },
    (w, h, t) => { vFill('#F4D8B0', '#C89870', 0, 0, w, h);
      ctx.save(); ctx.translate(w / 2, h * .95); ctx.rotate(Math.sin(t * 6) * .12); rrect(-90, -220, 180, 240, 60); paint('#F2C8A0', NP.ink, 6);
      for (let i = 0; i < 7; i++) { const a = -Math.PI * .92 + i / 6 * Math.PI * .84; ctx.save(); ctx.translate(Math.cos(a) * 80, -200 + Math.sin(a) * 50); ctx.rotate(a + Math.PI / 2); rrect(-20, -190 - hash(i) * 50, 40, 200 + hash(i) * 50, 20); paint('#F2C8A0', NP.ink, 5); ctx.restore(); }
      ctx.restore(); txt('HI!!', w * .78, h * .3, 120, '#E84A4A', { font: 'marker', rot: .2 }); },
    (w, h, t) => { vFill('#1A6AB0', '#0A2A5A', 0, 0, w, h); ctx.fillStyle = '#2A8AD0'; for (let i = 0; i < 5; i++) { ctx.beginPath(); ctx.ellipse(((i * 300 - t * 200) % (w + 300) + w + 300) % (w + 300) - 150, h * .75 + i % 2 * 30, 200, 30, 0, 0, TAU); ctx.fill(); }
      ctx.save(); ctx.translate(w / 2, h * .62 + Math.sin(t * 4) * 12); ctx.rotate(Math.sin(t * 3) * .08);
      ctx.beginPath(); ctx.moveTo(-330, -10); ctx.quadraticCurveTo(-60, -90, 300, 0); ctx.quadraticCurveTo(200, 80, -250, 60); ctx.lineTo(-400, 110); ctx.lineTo(-360, 20); ctx.lineTo(-420, -60); ctx.closePath(); paint('#7A8CA0', NP.ink, 5);
      ctx.beginPath(); ctx.moveTo(300, 0); ctx.quadraticCurveTo(200, 80, -100, 64); ctx.quadraticCurveTo(150, 30, 300, 0); paint('#E8EEF4', NP.ink, 3);
      ctx.fillStyle = '#FFF'; for (let i = 0; i < 6; i++) poly([[260 - i * 34, 16 + i * 6], [244 - i * 34, 34 + i * 6], [230 - i * 34, 18 + i * 6]]), ctx.fill();
      poly([[-60, -60], [-10, -190], [60, -66]]); paint('#6A7C90', NP.ink, 5); ell(190, -18, 11); paint(NP.ink);
      toon(-110, -60, 14, { hair: 'bun', hairCol: NHAIR.white, top: 'sweater', topCol: '#C84A7A', skin: 0, glasses: 'round', legs: false, shadow: false, aL: 1.1, aR: 1.1, hand: 'open', handL: 'open', mouth: 'grin', eyes: 'happy' }); ctx.restore(); },
    (w, h, t) => { vFill('#FFB0D0', '#FFE8F0', 0, 0, w, h); ctx.save(); ctx.translate(w / 2, h * .9);
      for (let i = 0; i < 3; i++) { const bb = Math.abs(Math.sin(t * 8 + i)) * 30; ctx.save(); ctx.translate((i - 1) * 260, -bb); ell(0, -120, 100, 120); paint('#F2D0B0', NP.ink, 5); ell(0, -270, 80, 80); paint('#F2D0B0', NP.ink, 5); for (const sd of [-1, 1]) { ell(sd * 28, -280, 12, 16); paint(NP.ink); } ctx.beginPath(); ctx.arc(0, -250, 30, .2 * Math.PI, .8 * Math.PI); paint(null, NP.ink, 6); rrect(-110, -120, 220, 60, 20); paint('#6AC8FF', NP.ink, 4); ctx.restore(); }
      ctx.restore(); txt('BABY BAND!!', w / 2, h * .16, 90, '#E84A9A', { font: 'shrikhand' }); },
  ];
  line('V2', 14, (p, lt, d, t) => {
    const e8 = beatLen() / 2, first = bt(t, lt), n = Math.max(0, Math.floor((lt - first + .02) / e8) + 1), ch = 2 + n, since = n > 0 ? lt - first - (n - 1) * e8 : lt;
    fillAll('#1A0E08');
    ctx.fillStyle = 'rgb(120 70 30 / .25)'; for (let x = 0; x < W; x += 90) ctx.fillRect(x, 0, 44, H);
    ctx.fillStyle = 'rgb(80 180 255 / .08)'; ell(960, 480, 1100, 640); ctx.fill();
    crtTV(250, 160, 1250, 650, (w, h) => {
      SLOP[(n + 3) % SLOP.length](w, h, t);
      if (since < .05) { ctx.fillStyle = 'rgb(255 255 255 / .5)'; ctx.fillRect(0, 0, w, h); }
      rrect(40, h - 100, 210, 60, 30); paint('rgb(255 255 255 / .75)'); txt('SORA 2', 145, h - 69, 34, NP.ink, { font: 'archivo' });
      pixelText('CH ' + String(ch).padStart(2, '0'), 50, 40, 12, '#3AFF5A', { shadow: [.4, .4] });
    }, { style: 'wood' });
    // the remote in a hand, pointed at the set; the thumb clicks every eighth
    const press = since < .08 ? 1 : 0;
    ctx.save(); ctx.translate(1700, 930); ctx.rotate(-.55);
    rrect(-70, -260, 140, 360, 30); paint(lg(-70, 0, 70, 0, [[0, '#2A2A34'], [1, '#0E0E14']]), NP.ink, 5);
    ell(0, -230, 12); paint(press ? '#FF3030' : '#601010');
    for (let r = 0; r < 3; r++) for (let c = 0; c < 3; c++) { rrect(-50 + c * 36, -200 + r * 36, 28, 22, 6); paint(r === 0 && c === 1 ? NP.red : '#6A6A78', NP.ink, 2); }
    rrect(-100, -40, 200, 190, 60); paint(NSKIN[0], NP.ink, 5);
    ctx.save(); ctx.translate(-10, -110 + press * 14); ctx.rotate(.1); rrect(-26, -20, 52, 130, 26); paint(NSKIN[0], NP.ink, 5); ctx.restore();
    ctx.restore();
    if (press) for (let i = 0; i < 3; i++) { const a = -2.2 + i * .3; ctx.beginPath(); ctx.moveTo(1560 + Math.cos(a) * 60, 690 + Math.sin(a) * 60); ctx.lineTo(1560 + Math.cos(a) * 110, 690 + Math.sin(a) * 110); paint(null, '#FFE060', 6); }
    chyron('SORA 2 FLOODS THE FEEDS', 'OPENAI LAUNCHES AN ALL-AI VIDEO APP', { k: chyK(lt) });
  });

  // =====================================================================================
  // V2.15 Yann LeCun quits Meta's stage — EXCLUSIVE: YANN walks off the stage with a globe (a world model) under his arm toward the
  // door marked WORLD MODELS; RANDI SEED chases him with the mic.
  line('V2', 15, (p, lt, d, t) => {
    const walk = lt * 1.9, cx = 60 * lt;
    camBegin(960 + cx, 540, 1.02);
    vFill('#6A0A14', '#1A0206', -600, -600, W + 1200, 1800);
    // curtain folds
    for (let i = -6; i < 30; i++) { const x = i * 90; ctx.fillStyle = i % 2 ? 'rgb(0 0 0 / .22)' : 'rgb(255 120 120 / .08)'; ctx.fillRect(x, -200, 45, 1100); }
    ctx.fillStyle = '#C9A43A'; ctx.fillRect(-600, 60, W + 1200, 16);
    // stage floor
    vFill('#3A2418', '#150A06', -600, 860, W + 1200, 400);
    ctx.fillStyle = 'rgb(255 220 150 / .14)'; ell(700, 900, 500, 70); ctx.fill();
    // the empty lectern he left behind
    rrect(300, 560, 220, 300, 8); paint('#2A2A3A', NP.ink, 5); txt('META', 410, 640, 40, '#8AB0FF', { font: 'archivo' });
    // the exit door
    const dx = 1470;
    rrect(dx, 300, 300, 560, 6); paint('#2A3A4A', NP.ink, 6); rrect(dx + 20, 320, 260, 540, 4); paint(lg(0, 320, 0, 860, [[0, '#FFF6D0'], [1, '#F8D080']]));
    rrect(dx - 20, 170, 360, 100, 10); paint('#0A3A12', NP.ink, 5); txt('WORLD MODELS →', dx + 160, 222, 42, '#6AFF8A', { font: 'archivo', maxW: 330 });
    // Yann, with the world under his arm
    const yx = 1000 + lt * 300;
    toon(yx, 900, 58, { hair: 'side', hairCol: '#3A2A20', top: 'blazer', topCol: '#1E2230', shirtCol: '#2A2A38', skin: 0, glasses: 'square', mouth: 'smirk', walk, lookX: -.6, aR: -1.05, eR: 1.5, aL: -1.35 + Math.sin(walk * TAU) * .3,
      hold: s => globe(30, 10, 95, t * 2, { col: NP.cyan }) });
    nameTag('YANN', yx - 40, 900 - 6.3 * 58, 26, -.1);
    // Randi chasing
    const rx = 520 + lt * 420;
    toon(rx, 930, 60, { ...CAST.randi.o, walk: walk * 1.4, reachR: [3.4, -9.0], hold: micHold(.9), talk: talk(t), eyes: 'wide', lookX: .8, rot: .08 });
    camEnd();
    liveBug(96, 70, { label: 'EXCLUSIVE', col: NP.red });
    chyron('YANN LeCUN LEAVES META', 'TO BUILD "WORLD MODELS" AFTER 12 YEARS', { k: chyK(lt), style: 'live', tab: 'LIVE' });
  });

  // =====================================================================================
  // V2.16 "Bubble!" screams the business page — the spinning newspaper stops on BUBBLE?!; behind it, Chip's board holds a giant soap
  // bubble full of GPUs and dollar signs, and a pin creeps toward it… cut before it pops.
  line('V2', 16, (p, lt, d, t) => {
    const stop = bt(t, lt, 1), sk = clamp(lt / stop);
    gfxCard({ top: '#1E6A44', bottom: '#03180C', head: 'MONEY WATCH', headCol: '#1E7A4A', sub: 'WALL STREET' });
    // the bubble
    const bx = 1390, by = 480, R = 290 + Math.sin(t * 4) * 10;
    ctx.save(); ctx.globalAlpha = .9;
    ctx.fillStyle = rg(bx - 80, by - 100, 20, R, [[0, 'rgb(255 255 255 / .25)'], [.7, 'rgb(160 220 255 / .12)'], [.92, 'rgb(255 140 220 / .35)'], [1, 'rgb(140 255 220 / .6)']]); ell(bx, by, R, R * (1 + Math.sin(t * 5) * .03)); ctx.fill();
    ctx.restore();
    ctx.save(); ell(bx, by, R * .9, R * .9); ctx.clip();
    for (let i = 0; i < 10; i++) { const a = t * .6 + i * 2.1, rr = R * .55 * hash(i + 3), x = bx + Math.cos(a) * rr, y = by + Math.sin(a * 1.2) * rr; if (i % 2) { ctx.save(); ctx.translate(x, y); ctx.rotate(a); rrect(-60, -24, 120, 48, 6); paint('#2A2E3A', NP.ink, 3); for (let f = 0; f < 3; f++) { ell(-30 + f * 30, 0, 14); paint('#4A5068', '#8A90A8', 2); } ctx.restore(); } else txt('$', x, y, 90, '#3AE87A', { font: 'anton', stroke: NP.ink, sw: 6, rot: Math.sin(a) * .3 }); }
    ctx.restore();
    ell(bx, by, R, R); paint(null, 'rgb(255 255 255 / .7)', 4);
    ctx.fillStyle = 'rgb(255 255 255 / .75)'; ell(bx - R * .45, by - R * .5, R * .2, R * .1, -.7); ctx.fill();
    // the pin creeping in
    const pinX = lerp(1880, bx + R + 26, easeOut(clamp(lt / d)) * .92);
    ctx.save(); ctx.translate(pinX, by + 40); ctx.rotate(Math.PI + .1);
    ctx.beginPath(); ctx.moveTo(0, 0); ctx.lineTo(-150, 0); paint(null, '#C9CFDB', 6); ell(-160, 0, 26); paint(NP.red, NP.ink, 4);
    ctx.restore();
    ctx.save(); ctx.translate(pinX + 190, by + 40); rrect(-10, -46, 170, 92, 40); paint(NSKIN[2], NP.ink, 5); rrect(-40, -40, 70, 34, 16); paint(NSKIN[2], NP.ink, 5); rrect(60, -30, 140, 60, 10); paint('#3A5A8A', NP.ink, 5); ctx.restore();
    // the newspaper spins in and stops on BUBBLE?!
    const spin = (1 - easeOut(sk)) * TAU * 2.2, sc = lerp(.08, 1, easeOut(sk));
    ctx.save(); ctx.translate(560, 500); ctx.rotate(spin - .06); ctx.scale(sc, sc);
    ctx.fillStyle = 'rgb(0 0 0 / .35)'; ctx.fillRect(-370 + 14, -330 + 16, 740, 660);
    rrect(-370, -330, 740, 660, 3); paint('#EFEBDD', NP.ink, 4);
    txt('The Business Page', 0, -278, 58, NP.ink, { font: 'fraktur' });
    ctx.fillStyle = NP.ink; ctx.fillRect(-340, -238, 680, 4); ctx.fillRect(-340, -228, 680, 2);
    txt('NOVEMBER 2025 · FINAL EDITION', 0, -212, 16, '#444', { font: 'archivo' });
    txt('BUBBLE?!', 0, -110, 190, NP.ink, { font: 'anton' });
    txt('AI STOCKS SLIDE DESPITE RECORD NVIDIA QUARTER', 0, 20, 22, NP.ink, { font: 'archivo', maxW: 660 });
    ctx.fillStyle = 'rgb(20 20 30 / .4)'; for (let c = 0; c < 3; c++) for (let r = 0; r < 9; r++) ctx.fillRect(-330 + c * 225, 60 + r * 26, r % 4 === 3 ? 120 : 200, 7);
    rrect(-120, 150, 240, 120, 4); paint('#FFF', NP.ink, 3); txt('"ELEMENTS OF', 0, 190, 22, NP.ink, { font: 'abril' }); txt('IRRATIONALITY"', 0, 220, 22, NP.ink, { font: 'abril' }); txt('— PICHAI', 0, 250, 16, '#555', { font: 'archivo' });
    ctx.restore();
    if (lt >= stop && lt < stop + .1) flash(lt, stop, .1, .35);
    chyron('AI BUBBLE FEARS', 'PICHAI: "ELEMENTS OF IRRATIONALITY"', { k: chyK(lt), style: 'money' });
  });
})();

;
// ---- styles/newscast/ch/c05_chorus2.js ----
// c05_chorus2 — Chorus 2: the station's image-campaign jingle, bigger this time: THE WHOLE NEWS TEAM. Sub-shots cut on the beat from
// linesOf('C2') (lines 2 and 4 are split where "and the curves" / "but we can't" land):
//   hook 1  "We didn't start the scaling"     six-up multi-image of the team singing, the hook slamming across the band word by word;
//                                             the tiles fly apart to the chrome title → DVE star wipe
//   2a      "It was always training,"         SUNNY at the weather wall: the 5-day forecast is TRAINING every day → DVE flip
//   2b      "and the curves kept gaining,"    CHIP at the money board: the curve climbs a notch a beat, every quote ▲, cash rain → DVE box
//   hook 2  "We didn't start the scaling"     BATCH at the stadium: SCALING 99 · HUMANS 0, the hook in lights on the marquee → swoosh wipe
//   4a      "No, we didn't preordain it,"     RANDI live outside a data centre, shrugging at the camera
//   4b      "but we can't contain it!"        SKY 89: the data centre bursts its fence and sprawls across the city → tracking glitch → V3.1
// Colour run: six-colour tiles on a laser grid / teal weather / money green / stadium-night gold / dusk orange / night aerial.
(() => {
  const rays = (cx, cy, n, col, rot = 0, R = 2600) => { ctx.fillStyle = col; ctx.beginPath(); for (let i = 0; i < n; i++) { const a0 = rot + i / n * TAU, a1 = a0 + TAU / n / 2; ctx.moveTo(cx, cy); ctx.lineTo(cx + Math.cos(a0) * R, cy + Math.sin(a0) * R); ctx.lineTo(cx + Math.cos(a1) * R, cy + Math.sin(a1) * R); ctx.closePath(); } ctx.fill(); };
  const flash = (t, t0, dur = .1, a = .6, col = '255 255 255') => { const k = (t - t0) / dur; if (k >= 0 && k < 1) { ctx.fillStyle = `rgb(${col} / ${a * (1 - k)})`; ctx.fillRect(-200, -200, W + 400, H + 400); } };
  const halfSnap = t => onBeat(0, Math.round(bpOf(t) * 2) / 2);
  // sub-shot boundaries (song time): [start, 2a, 2b, hook 2, 4a, 4b, end]
  function cuts() {
    const L = linesOf('C2'), sp = span('C2');
    return { L, c: [sp.start, L[1].start, halfSnap(L[1].start + (L[1].end - L[1].start) * .44), L[2].start, L[3].start, halfSnap(L[3].start + (L[3].end - L[3].start) * .5), sp.end] };
  }
  // the hook, word by word: onsets as fractions of the sung line (measured from this take: We · didn't · start · the · scaling)
  const HOOK = ['WE', "DIDN'T", 'START', 'THE', 'SCALING'], HOOKF = [0, .18, .4, .5, .63];
  const wordK = (t, ln, i) => clamp((t - (ln.start + (ln.end - ln.start) * HOOKF[i]) + .05) / .13);
  // a row of chrome words centred on (cx, y), each slamming in with its k
  function hookRow(words, ks, cx, y, size, styles, o = {}) {
    const gap = size * .38, ws = words.map(w => textW(w, size, 'archivo', 2) + size * .12), tot = ws.reduce((a, b) => a + b, 0) + gap * (words.length - 1);
    let x = cx - tot / 2;
    words.forEach((w, i) => {
      const k = ks[i], wx = x + ws[i] / 2; x += ws[i] + gap;
      if (k <= 0) return;
      chrome(w, wx, y, size, { font: 'archivo', style: styles[i] ?? 'chrome', italic: .14, depth: Math.round(size * .09), spacing: 2, s: lerp(1.7, 1, easeOut(k)), alpha: clamp(k * 3) * (o.alpha ?? 1) });
      if (k < 1) glint(wx + ws[i] * .35, y - size * .3, size * 1.1 * Math.sin(k * Math.PI), Math.sin(k * Math.PI));
    });
  }
  const gear = (x, y, r, rot, col = '#E8EEF8', hole = '#2B5FD9') => {
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot);
    ctx.beginPath(); const n = 10; for (let i = 0; i < n * 2; i++) { const a0 = i / (n * 2) * TAU, rr = i % 2 ? r * .78 : r; ctx.lineTo(Math.cos(a0 - .12) * rr, Math.sin(a0 - .12) * rr); ctx.lineTo(Math.cos(a0 + .12) * rr, Math.sin(a0 + .12) * rr); } ctx.closePath();
    paint(col, NP.ink, Math.max(2, r * .07)); ell(0, 0, r * .55); paint(shade(col, .12), NP.ink, Math.max(1.5, r * .04)); ell(0, 0, r * .22); paint(hole, NP.ink, Math.max(1.5, r * .04));
    ctx.restore();
  };

  // =====================================================================================
  // HOOK 1 — the team in a six-up multi-image. Each tile is its own little promo portrait.
  const TEAM = [
    { who: 'clawd', name: 'CLAWD', bg: ['#3E7CFF', '#0B1A66'] },
    { who: 'val', name: 'VAL LOSS', bg: ['#FF7AC0', '#7A0E4E'] },
    { who: 'sunny', name: 'SUNNY DESCENT', bg: ['#4FE0F0', '#0A5A7A'] },
    { who: 'batch', name: 'BATCH NORMAN', bg: ['#5AE07A', '#0A5A2A'] },
    { who: 'randi', name: 'RANDI SEED', bg: ['#FFC05A', '#A0301E'] },
    { who: 'chip', name: 'CHIP STACKS', bg: ['#D8F07A', '#1E5A2A'] },
  ];
  const TW = 570, TH = 284, TX = [80, 675, 1270], TY = [172, 652];
  function portrait(i, w, h, t) {
    const m = TEAM[i], b = bpOf(t), bob = Math.abs(Math.sin(b * Math.PI)), sway = Math.sin(b * Math.PI) * .05, tk = talk(t, i * 1.9);
    vFill(m.bg[0], m.bg[1], 0, 0, w, h);
    rays(w * .5, h * .7, 14, 'rgb(255 255 255 / .1)', t * .3 * (i % 2 ? 1 : -1));
    ctx.fillStyle = 'rgb(255 255 255 / .06)'; for (let y = 0; y < h; y += 12) ctx.fillRect(0, y, w, 5);
    if (m.who === 'clawd') {
      logo89(w * .8, h * .42, 70, { spin: Math.sin(t * 2) * .5 });
      newsClawd(w * .38, h + 50, 30, { legs: false, shadow: false, talk: tk, dy: -bob * .12, rot: sway, reachR: [5.6, -8.4], hold: micHold(.2), blink: frac(t * .4) < .05 ? 1 : 0 });
    } else if (m.who === 'val') {
      for (let k = 0; k < 4; k++) glint(w * (.12 + k * .26), h * (.25 + (k % 2) * .35), 50 * (.4 + .6 * pulse(t + k * .1, 4)), .9);
      toon(w * .5, h + 170, 34, { ...CAST.val.o, legs: false, shadow: false, talk: tk, dy: -bob * .1, rot: sway, aL: -.2, eL: 1.6, handL: 'open', aR: .5, eR: 1.2, hand: 'wave' });
    } else if (m.who === 'sunny') {
      wxIcon('sun', w * .8, h * .38, 62, t); wxIcon('cloud', w * .9, h * .62, 44, t);
      toon(w * .4, h + 170, 34, { ...CAST.sunny.o, legs: false, shadow: false, talk: tk, dy: -bob * .1, rot: sway, reachR: [4.4, -10.6], hand: 'point', lookX: .4 });
    } else if (m.who === 'batch') {
      ctx.strokeStyle = 'rgb(255 255 255 / .5)'; ctx.lineWidth = 4; ctx.beginPath(); for (let k = 0; k < 6; k++) { ctx.moveTo(w * .55 + k * 50, h * .45); ctx.lineTo(w * .5 + k * 70, h); } ctx.stroke();
      toon(w * .5, h + 170, 34, { ...CAST.batch.o, legs: false, shadow: false, talk: tk, dy: -bob * .1, rot: sway, reachL: [-3.2, -11.2 - bob * .4], holdL: s => foamFinger(s * .028) });
    } else if (m.who === 'randi') {
      ctx.fillStyle = 'rgb(60 20 40 / .6)'; for (let k = 0; k < 9; k++) { const bh = 60 + hash(k + 3) * 90; ctx.fillRect(k * 66 - 10, h - bh, 56, bh); }
      toon(w * .45, h + 170, 34, { ...CAST.randi.o, legs: false, shadow: false, talk: tk, dy: -bob * .1, rot: sway, reachR: [2.2, -8.8], hold: micHold(.3), lookX: .2 });
    } else {
      ctx.beginPath(); for (let k = 0; k <= 30; k++) { const u = k / 30; ctx.lineTo(w * .56 + u * w * .4, h * .8 - (Math.exp(u * 3.5) - 1) / (Math.exp(3.5) - 1) * h * .6); } ctx.strokeStyle = 'rgb(20 60 20 / .5)'; ctx.lineWidth = 16; ctx.stroke(); ctx.strokeStyle = NP.lime; ctx.lineWidth = 7; ctx.stroke();
      toon(w * .38, h + 170, 34, { ...CAST.chip.o, legs: false, shadow: false, talk: tk, dy: -bob * .1, rot: sway, aL: -.2, eL: 1.7, handL: 'thumb' });
    }
    // name strip
    const nw = textW(m.name, 30, 'archivo', 1.5) + 44;
    ctx.fillStyle = 'rgb(0 0 0 / .4)'; ctx.fillRect(22, h - 66, nw, 46);
    ctx.fillStyle = lg(0, h - 72, 0, h - 26, [[0, '#3A6AF0'], [1, '#10247A']]); ctx.fillRect(16, h - 72, nw, 46); ctx.fillStyle = NP.gold; ctx.fillRect(16, h - 72, nw, 4);
    txt(m.name, 38, h - 47, 30, NP.white, { font: 'archivo', align: 'left', spacing: 1.5, shadow: [2, 3], shadowCol: 'rgb(0 0 0 / .5)' });
  }
  function foamFinger(k) {
    ctx.save(); ctx.scale(k, k); ctx.rotate(-.12);
    rrect(-40, -60, 80, 84, 22); paint(NP.gold, NP.ink, 5); rrect(-15, -150, 30, 100, 15); paint(NP.gold, NP.ink, 5);
    ctx.fillStyle = 'rgb(0 0 0 / .12)'; ctx.fillRect(10, -140, 8, 150);
    txt('#1', 0, -18, 40, NP.redDk, { font: 'anton' });
    ctx.restore();
  }
  function hook1(t, t0, t1, ln) {
    hideCaption();
    const tFly = ln.start + (ln.end - ln.start) * .8, fly = easeIn(clamp((t - tFly) / .34));
    laserGrid(t, { horizon: 720, col: NP.magenta, speed: 2.2, sky: ['#02041A', '#3A0A5A'] });
    // behind the tiles: the big title (revealed as they fly apart)
    if (t > tFly - .02) {
      const k1 = clamp((t - tFly - .04) / .24), k2 = clamp((t - tFly - .16) / .26);
      globe(W / 2, lerp(900, 470, easeOut(clamp((t - tFly) / .5))), 320, t * 1.3, { col: NP.cyan });
      swoosh(clamp((t - tFly) / .45), 720, NP.red, { len: 1700, th: 64 }); swoosh(clamp((t - tFly - .15) / .45), 780, NP.gold, { len: 1500, th: 34 });
      if (k1 > 0) chrome("WE DIDN'T START", W / 2, 390, 140, { font: 'archivo', italic: .14, depth: 12, spacing: 3, s: lerp(1.9, 1, easeOut(k1)), alpha: clamp(k1 * 3) });
      if (k2 > 0) chrome('THE SCALING', W / 2, 590 - pulse(t, 7) * 8, 190, { font: 'archivo', style: 'gold', italic: .14, depth: 17, spacing: 3, s: k2 < 1 ? lerp(2.2, 1, easeOut(k2)) : 1, alpha: clamp(k2 * 3) });
      const sk = clamp((t - tFly - .4) / .2);
      if (sk > 0) { ctx.save(); ctx.globalAlpha = sk; rrect(W / 2 - 540, 745, 1080, 80, 8); paint('rgb(0 0 30 / .7)', alpha(NP.cyan, .9), 3); txt('THE CHANNEL 89 NEWS TEAM', W / 2, 787, 50, NP.white, { font: 'archivo', spacing: 6 }); ctx.restore(); }
      sweepGlint(W / 2 - 620, W / 2 + 620, 560, (t - tFly - .45) / .5, 150);
      flash(t, tFly + .16, .12, .45);
    }
    // the band across the middle: the hook, word by word as it is sung
    if (fly < 1) {
      ctx.save(); ctx.globalAlpha = 1 - clamp(fly * 3);
      ctx.fillStyle = 'rgb(0 0 0 / .45)'; ctx.fillRect(-20, 470, W + 40, 176);
      ctx.fillStyle = lg(0, 460, 0, 640, [[0, '#1A2A8A'], [.5, '#0A1040'], [1, '#1A2A8A']]); ctx.fillRect(-20, 460, W + 40, 176);
      ctx.fillStyle = NP.gold; ctx.fillRect(-20, 460, W + 40, 5); ctx.fillRect(-20, 631, W + 40, 5);
      hookRow(HOOK, HOOK.map((_, i) => wordK(t, ln, i)), W / 2, 548, 84, [0, 0, 0, 0, 'gold'].map(s => s || 'chrome'));
      ctx.restore();
    }
    // the six tiles flip in on sixteenths, then fly apart from the centre
    for (let i = 0; i < 6; i++) {
      const c = i % 3, r = Math.floor(i / 3), x = TX[c], y = TY[r], k = clamp((t - t0 - i * .07) / .14);
      if (k <= 0 || fly >= 1) continue;
      const dx = x + TW / 2 - W / 2, dy = y + TH / 2 - H / 2;
      ctx.save(); ctx.translate(x + TW / 2 + dx * fly * 2.6, y + TH / 2 + dy * fly * 3.2); ctx.rotate((c - 1 || (r ? 1 : -1)) * fly * .5); ctx.scale(easeOut(k) * (1 + fly * .5), 1 + fly * .5);
      ctx.fillStyle = 'rgb(0 0 0 / .45)'; ctx.fillRect(-TW / 2 + 12, -TH / 2 + 14, TW, TH);
      ctx.save(); ctx.beginPath(); ctx.rect(-TW / 2, -TH / 2, TW, TH); ctx.clip(); ctx.translate(-TW / 2, -TH / 2);
      portrait(i, TW, TH, t);
      ctx.fillStyle = lg(0, 0, 0, TH * .5, [[0, 'rgb(255 255 255 / .16)'], [1, 'rgb(255 255 255 / 0)']]); ctx.fillRect(0, 0, TW, TH * .5);
      ctx.restore();
      ctx.lineWidth = 7; ctx.strokeStyle = '#F2F4FA'; ctx.strokeRect(-TW / 2, -TH / 2, TW, TH);
      ctx.restore();
    }
    flash(t, t0, .1, .5);
  }

  // =====================================================================================
  // 2a — SUNNY at the weather wall: the fronts sweep, the extended forecast is TRAINING every single day.
  function sunnyShot(t, t0, t1) {
    const u = t - t0, d = t1 - t0, kk = clamp(u / (d * .9));
    weatherSet(t, {
      head: '89 WEATHER', point: [lerp(820, 1680, ease(clamp(u / d))), 600],
      draw: (P) => {
        front([P([-135, 58]), P([-100, 44]), P([-70, 32]), P([-30, 30]), P([10, 44]), P([50, 50]), P([100, 44]), P([150, 52])], 'cold', { k: clamp(kk * 1.4) });
        front([P([-120, 20]), P([-80, 12]), P([-20, 8]), P([30, 18]), P([80, 12]), P([140, 20])], 'warm', { k: clamp(kk * 1.4 - .25) });
        for (const [lo, la, ph] of [[-98, 50, 0], [18, 60, 1], [105, 40, 2], [140, -25, 3]]) { const [gx, gy] = P([lo, la]); gear(gx, gy, 42, t * 2.4 * (ph % 2 ? -1 : 1) + ph, '#DDE6F2', '#1A3A8A'); }
      },
    });
    // the 5-day forecast: TRAINING, TRAINING, TRAINING…
    const x0 = 800, y0 = 470, w = 1000;
    rrect(x0 - 10, y0 - 70, w + 20, 62, 8); paint(lg(0, y0 - 70, 0, y0 - 8, [[0, '#FFFFFF'], [1, '#C9D8EE']]), NP.ink, 3);
    txt('5-DAY FORECAST', x0 + w / 2, y0 - 38, 40, NP.navy, { font: 'archivo', spacing: 4 });
    const days = ['MON', 'TUE', 'WED', 'THU', 'FRI'], tw = (w - 4 * 12) / 5, th = 300;
    days.forEach((dy, i) => {
      const k = clamp((u - .02 - i * .06) / .14); if (k <= 0) return;
      const tx = x0 + i * (tw + 12), hop = pulse(t + i * .08, 7) * 8;
      ctx.save(); ctx.translate(tx + tw / 2, y0 + th / 2 - hop); ctx.scale(easeOut(k), 1);
      rrect(-tw / 2, -th / 2, tw, th, 8); paint(lg(0, -th / 2, 0, th / 2, [[0, '#2B5FD9'], [1, '#0E2A7A']]), NP.ink, 3);
      ctx.fillStyle = 'rgb(255 255 255 / .15)'; ctx.fillRect(-tw / 2 + 4, -th / 2 + 4, tw - 8, th * .16);
      txt(dy, 0, -th / 2 + 32, 34, NP.white, { font: 'archivo' });
      gear(0, -12, 56, t * 3 * (i % 2 ? -1 : 1) + i, '#E8EEF8', '#2B5FD9');
      txt('TRAINING', 0, 84, 30, NP.white, { font: 'archivo', maxW: tw - 16 });
      txt('100%', 0, 122, 34, NP.gold, { font: 'anton' });
      ctx.restore();
    });
    nameSuper('SUNNY DESCENT', 'CHIEF METEOROLOGIST', { style: 'weather', k: clamp(u / .3), size: 46, subSize: 28 });
  }

  // =====================================================================================
  // 2b — CHIP at the money board: the curve climbs a notch on every beat, every quote is up, the ticker is all green, cash rains.
  function bill(x, y, s, rot, flip) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot); ctx.scale(s * flip, s);
    rrect(-46, -22, 92, 44, 4); paint('#7FC46A', '#1E4A1A', 3); rrect(-38, -15, 76, 30, 3); paint(null, '#2E6A2A', 2);
    ell(0, 0, 13, 13); paint('#A8DA90', '#2E6A2A', 2); txt('$', 0, 1, 22, '#1E4A1A', { font: 'anton' });
    ctx.restore();
  }
  function cashRain(t, t0, front) {
    for (let i = 0; i < 26; i++) {
      if ((i % 3 === 0) !== front) continue;
      const sp = 260 + hash(i + 3) * 260, x = hash(i + 7) * 2100 - 90 + Math.sin(t * 2 + i) * 40, y = ((t - t0) * sp + hash(i + 11) * 1300) % 1300 - 120;
      bill(x, y, (front ? 1.25 : .8) + hash(i) * .3, Math.sin(t * 3 + i) * .6, Math.cos(t * 5 + i * 2));
    }
  }
  function chipShot(t, t0, t1) {
    const u = t - t0;
    gfxCard({ top: '#0E6A3A', bottom: '#02180C', head: 'MONEY WATCH', headCol: '#1E7A4A', sub: 'ALL MARKETS' });
    cashRain(t, t0, false);
    const b0 = Math.ceil(bpOf(t0) - .02), n = bpOf(t) - b0, nb = Math.max(1, Math.round(bpOf(t1) - b0));
    const k = clamp((Math.floor(n) + 1 + easeOut(clamp(frac(n) / .22)) - 1 + .35) / nb);
    const tip = cgiChart(640, 270, 540, 400, { fn: v => (Math.exp(v * 6) - 1) / (Math.exp(6) - 1), k, col: NP.lime, fill: true, label: 'THE CURVE', ylabel: 'COMPUTE', xlabel: 'TIME' });
    if (k > .55 && frac(t * 3) < .7) { const lx = Math.min(tip[0] - 30, 1150), ly = Math.max(tip[1] - 20, 300); rrect(lx - pixelW('▲ ALL-TIME HIGH', 4) - 16, ly - 12, pixelW('▲ ALL-TIME HIGH', 4) + 32, 52, 6); paint('rgb(0 0 0 / .8)', NP.gold, 3); pixelText('▲ ALL-TIME HIGH', lx, ly, 4, NP.gold, { align: 'right', edge: null }); }
    quoteBoard(1250, 262, 560, [
      { sym: 'NVDA', price: '1,337', chg: 12 }, { sym: 'FLOP', price: '1E27', chg: 99 }, { sym: 'GPUS', price: 'SOLD', chg: 40 },
      { sym: 'HYPE', price: '9,000', chg: 50 }, { sym: 'CAPX', price: '$700B', chg: 80 },
    ], { rowH: 80, flash: Math.floor(bpOf(t)) % 5 });
    const b = bpOf(t), bob = Math.abs(Math.sin(b * Math.PI));
    toon(330, 1260, 66, { ...CAST.chip.o, legs: false, shadow: false, talk: talk(t), dy: -bob * .06, rot: Math.sin(b * Math.PI) * .03, reachR: [3.4, -10.4 - bob * .3], hand: 'point', aL: -.3, eL: 1.5, handL: 'thumb', lookX: .5 });
    cashRain(t, t0, true);
    nameSuper('CHIP STACKS', undefined, { style: 'money', k: clamp(u / .3), size: 46 });
    ticker(890, ['NVDA ▲12%', 'FLOPS ▲99%', 'GPUS ▲40%', 'TOKENS ▲80%', 'HYPE ▲50%', 'CAPEX ▲80%', 'COMPUTE ▲99%'], t, { h: 58, label: 'MARKETS' });
  }

  // =====================================================================================
  // HOOK 2 — BATCH at the stadium: the scoreboard says it all, the crowd does the wave, the hook goes up in lights on the marquee.
  function batchShot(t, t0, t1, ln) {
    hideCaption();
    const u = t - t0, b = bpOf(t);
    vFill('#03061C', '#1A2C6A');
    for (let i = 0; i < 60; i++) { ctx.fillStyle = `rgb(255 255 255 / ${.2 + .5 * hash(i + 5)})`; ctx.fillRect(hash(i) * W, hash(i + 70) * 420, 2.5, 2.5); }
    // light towers
    for (const lx of [150, 1880]) {
      ctx.fillStyle = '#0A0F22'; ctx.fillRect(lx - 10, 240, 20, 500);
      ctx.fillStyle = rg(lx, 250, 10, 380, [[0, 'rgb(255 250 220 / .35)'], [1, 'rgb(255 250 220 / 0)']]); ctx.fillRect(lx - 380, -130, 760, 760);
      rrect(lx - 90, 200, 180, 90, 6); paint('#1A1E30', '#000', 3);
      for (let r = 0; r < 2; r++) for (let c = 0; c < 4; c++) { ell(lx - 64 + c * 43, 225 + r * 40, 16); paint('#FFF8D8'); }
    }
    // the stands and the crowd doing the wave
    vFill('#1A2248', '#0C1230', -100, 560, W + 200, 600);
    const cols = ['#E84A4A', '#F4D24A', '#FFFFFF', '#4A8AE8', '#2EBD5B', '#FF8AC8'];
    for (let r = 0; r < 4; r++) for (let i = 0; i < 44; i++) {
      const x = i * 46 + (r % 2) * 23 - 20, wave = Math.max(0, Math.sin(x * .006 - t * 7)) ** 2, y = 610 + r * 62 - wave * 34;
      ctx.fillStyle = cols[(i * 7 + r * 3) % 6]; rrect(x - 17, y + 8, 34, 50, 10); ctx.fill();
      ell(x, y, 15, 16); paint(NSKIN[(i + r) % 6]);
      if (wave > .3) { ctx.strokeStyle = NSKIN[(i + r) % 6]; ctx.lineWidth = 7; ctx.lineCap = 'round'; ctx.beginPath(); ctx.moveTo(x - 14, y + 14); ctx.lineTo(x - 20, y - 22 * wave); ctx.moveTo(x + 14, y + 14); ctx.lineTo(x + 20, y - 22 * wave); ctx.stroke(); }
    }
    // the scoreboard
    scoreboard(560, 150, 760, 380, { title: 'THE AI BOWL', rows: [{ name: 'SCALING', score: 99, col: NP.gold }, { name: 'HUMANS', score: 0, col: '#9AB8FF' }], foot: 'FINAL', flash: 0 });
    // the marquee: the hook in lights
    const mx = 620, my = 575, mw = 1220, mh = 260;
    ctx.fillStyle = 'rgb(0 0 0 / .5)'; rrect(mx + 12, my + 14, mw, mh, 16); ctx.fill();
    rrect(mx, my, mw, mh, 16); paint(lg(0, my, 0, my + mh, [[0, '#8A1219'], [1, '#3A0508']]), '#C9A43A', 8);
    rrect(mx + 26, my + 26, mw - 52, mh - 52, 8); paint('#0A0306');
    const per = 2 * (mw + mh) / 46, chase = Math.floor(t * 12);
    for (let i = 0; i < 92; i++) {
      let s = i * per / 2, px, py;
      if (s < mw) { px = mx + s; py = my + 13; } else if ((s -= mw) < mh) { px = mx + mw - 13; py = my + s; } else if ((s -= mh) < mw) { px = mx + mw - s; py = my + mh - 13; } else { s -= mw; px = mx + 13; py = my + mh - s; }
      const on = (i + chase) % 3 === 0; ell(px, py, 7); paint(on ? '#FFF2A0' : '#6A4A10');
      if (on) { ctx.fillStyle = 'rgb(255 230 120 / .25)'; ell(px, py, 14); ctx.fill(); }
    }
    const ks = HOOK.map((_, i) => wordK(t, ln, i));
    hookRow(HOOK.slice(0, 3), ks.slice(0, 3), mx + mw / 2, my + 86, 92, ['chrome', 'chrome', 'chrome']);
    hookRow(HOOK.slice(3), ks.slice(3), mx + mw / 2, my + 184, 116, ['chrome', 'gold']);
    // Batch, foam finger up on every beat
    const bob = Math.abs(Math.sin(b * Math.PI)), up = pulse(t, 5);
    toon(320, 1250, 64, { ...CAST.batch.o, legs: false, shadow: false, talk: talk(t), dy: -bob * .06, rot: Math.sin(b * Math.PI) * .03, reachL: [-2.4, -12.2 - up * .5], holdL: s => foamFinger(s * .03), aR: -.2, eR: 1.4, hand: 'fist', lookX: .3 });
    nameSuper('BATCH NORMAN', 'SPORTS', { style: 'sports', k: clamp(u / .3), size: 46, subSize: 28, y: 850 });
    flash(t, t0, .08, .4);
  }

  // =====================================================================================
  // 4a — RANDI live outside the data centre (it looks contained… for now), shrugging at the camera on "No,".
  function dataCentre(t, x, y, w, h, o = {}) {
    // a long windowless slab with fins, rooftop fans and the sign
    ctx.fillStyle = 'rgb(0 0 0 / .3)'; ctx.fillRect(x + 20, y + h - 10, w, 30);
    rrect(x, y, w, h, 4); paint(lg(0, y, 0, y + h, [[0, '#D8DEE8'], [1, '#8A93A8']]), NP.ink, 4);
    ctx.fillStyle = 'rgb(40 50 80 / .25)'; for (let fx = x + 30; fx < x + w - 20; fx += 46) ctx.fillRect(fx, y + 70, 16, h - 90);
    rrect(x + w * .2, y + 18, w * .6, 44, 4); paint('#1A2448', NP.ink, 3);
    txt('HYPERSCALE DATA CENTER', x + w / 2, y + 41, 30, NP.white, { font: 'archivo', spacing: 3, maxW: w * .56 });
    for (let i = 0; i < Math.floor(w / 130); i++) {
      const fx = x + 70 + i * 130, fy = y - 18;
      rrect(fx - 50, fy - 20, 100, 40, 6); paint('#9AA2B4', NP.ink, 3);
      ctx.save(); ctx.translate(fx, fy - 20); ctx.scale(1, .3); ell(0, 0, 40, 40); paint('#3A4058', NP.ink, 6);
      ctx.rotate(t * 14 + i); ctx.fillStyle = '#C9CFDB'; for (let q = 0; q < 3; q++) { ctx.rotate(TAU / 3); poly([[0, 0], [36, -8], [36, 8]]); ctx.fill(); } ctx.restore();
    }
    for (const [lx, ly] of [[x + 10, y - 8], [x + w - 10, y - 8]]) { ell(lx, ly, 9); paint(frac(t * 1.3) < .5 ? '#FF3030' : '#5A1010', NP.ink, 2); }
  }
  function fence(x0, x1, y, h, t, o = {}) {
    ctx.strokeStyle = 'rgb(200 210 220 / .55)'; ctx.lineWidth = 2; ctx.beginPath();
    for (let x = x0 - h; x < x1; x += 26) { ctx.moveTo(Math.max(x0, x), y - h + Math.max(0, x0 - x)); ctx.lineTo(Math.min(x1, x + h), y - Math.max(0, x + h - x1)); }
    for (let x = x0; x < x1 + h; x += 26) { ctx.moveTo(Math.min(x1, x), y - h + Math.max(0, x - x1)); ctx.lineTo(Math.max(x0, x - h), y - Math.max(0, x0 - (x - h))); }
    ctx.stroke();
    for (let x = x0; x <= x1; x += 180) { const lean = (o.bulge ?? 0) * Math.sin((x - x0) / (x1 - x0) * Math.PI) * 30; ctx.beginPath(); ctx.moveTo(x, y); ctx.lineTo(x + lean, y - h - 18); paint(null, '#6A7280', 9); }
    ctx.beginPath(); ctx.moveTo(x0, y - h); ctx.lineTo(x1, y - h); paint(null, '#6A7280', 5);
    ctx.strokeStyle = '#8A92A0'; ctx.lineWidth = 2; ctx.beginPath(); for (let x = x0; x < x1; x += 14) { ctx.moveTo(x, y - h - 8); ctx.lineTo(x + 10, y - h - 20); ctx.moveTo(x + 10, y - h - 8); ctx.lineTo(x, y - h - 20); } ctx.stroke();
  }
  function randiShot(t, t0, t1) {
    const u = t - t0, b0 = onBeat(0, Math.ceil(bpOf(t0) - .02)), sh = clamp((t - b0 + .06) / .12) * (1 - clamp((t - b0 - .5) / .25));
    vFill('#3A1A6A', '#FF9A4A', -600, -600, W + 1200, 1400);
    ell(1500, 700, 150, 150); paint('#FFD27A');
    ctx.fillStyle = '#4A2A6A'; for (let i = 0; i < 10; i++) { const tx = i * 230 - 60; poly([[tx, 700], [tx + 40, 470 + hash(i) * 60], [tx + 80, 700]]); ctx.fill(); }
    ctx.strokeStyle = 'rgb(40 20 60 / .6)'; ctx.lineWidth = 3; ctx.beginPath(); ctx.moveTo(-100, 520); ctx.quadraticCurveTo(900, 600, 2000, 510); ctx.stroke();
    vFill('#4A3A48', '#1A1418', -600, 700, W + 1200, 800);
    dataCentre(t, 640, 400, 1400, 310);
    fence(-40, 1960, 760, 150, t, { bulge: clamp((u - (t1 - t0) * .6) / .5) });
    rrect(1290, 640, 180, 90, 4); paint('#F2F2EE', NP.ink, 3); txt('KEEP OUT', 1380, 672, 30, NP.red, { font: 'archivo' }); txt('AUTHORIZED ONLY', 1380, 708, 16, NP.ink, { font: 'archivo' });
    // Randi: the shrug on "No,", then sings the rest
    const bob = Math.abs(Math.sin(bpOf(t) * Math.PI));
    toon(520, 1250, 70, { ...CAST.randi.o, legs: false, shadow: false, talk: sh > .5 ? undefined : talk(t), mouth: sh > .5 ? 'flat' : 'smile', brows: sh > .3 ? 'up' : 'flat', eyes: sh > .3 ? 'half' : 'open',
      dy: -sh * .14 - bob * .04, rot: -sh * .06, aL: lerp(-1.25, -.9, sh), eL: lerp(.3, 1.9, sh), handL: 'open', aR: lerp(-.4, -.75, sh), eR: lerp(2.2, 1.6, sh), hand: 'open', hold: micHold(lerp(.1, .5, sh)), lookX: 0 });
    liveBug();
    chyron('RANDI SEED', 'LIVE AT THE DATA CENTER', { k: clamp(u / .3), style: 'live', tab: 'LIVE' });
  }

  // =====================================================================================
  // 4b — SKY 89: the data centre grows on every beat, bursts its fence, swallows the blocks and sprawls off the edges.
  const DCR = [.85, 1.8, 3, 4.5, 6.3, 8.5, 11, 14, 17, 20];
  function skyShot(t, t0, t1) {
    const bp = bpOf(t), b0 = Math.ceil(bpOf(t0) - .02), n = Math.max(0, Math.floor(bp + .001) - b0 + 1), f = frac(bp), since = n > 0 ? f : 1;
    const R = n === 0 ? DCR[0] : lerp(DCR[Math.min(n - 1, 9)], DCR[Math.min(n, 9)], backOut(clamp(f / .2), 1.5));
    const hw = R * 100 + 70, hh = hw * .74;
    const zoom = lerp(1.05, .74, ease(clamp((t - t0) / (t1 - t0)))), [sx, sy] = since < .25 && n > 0 ? shakeXY(t, 14 * (1 - since / .25)) : [0, 0];
    const cx0 = W / 2 + sx, cy0 = 540 + sy, PY = .8;
    const S = (gx, gy) => [cx0 + gx * zoom, cy0 + gy * zoom * PY];
    const inDC = (x, y) => Math.abs(x) < hw && Math.abs(y) < hh;
    const vis = (x, y, m = 120) => { const [px, py] = S(x, y); return px > -m && px < W + m && py > -m && py < H + m; };
    fillAll('#0C0F18');
    // avenue centre lines + moving headlights
    ctx.fillStyle = 'rgb(240 200 90 / .35)';
    for (let j = -8; j <= 8; j++) { const [, py] = S(0, j * 200 + 100); for (let i = -14; i <= 14; i++) { const [px] = S(i * 200 + 30, 0); ctx.fillRect(px, py - 1, 40 * zoom, 3); } }
    for (let j = -8; j <= 8; j++) for (let c = 0; c < 5; c++) {
      const dir = j % 2 ? 1 : -1, xx = ((t * (110 + hash(j + 9) * 90) * dir + hash2(j, c) * 5600) % 5600 + 5600) % 5600 - 2800, yy = j * 200 + 100 + dir * 14;
      if (inDC(xx, yy) || !vis(xx, yy)) continue; const [px, py] = S(xx, yy);
      ctx.fillStyle = dir > 0 ? '#FFF6D0' : '#FF4A3A'; ctx.fillRect(px - 5, py - 2, 10, 4);
    }
    // blocks: sidewalk pads, then buildings/parks/lots (back to front around the slab)
    const blocks = [];
    for (let j = -8; j <= 8; j++) for (let i = -13; i <= 13; i++) { const bx = i * 200 - 75, by = j * 200 - 75; if (vis(bx + 75, by + 75, 260)) blocks.push([i, j, bx, by]); }
    for (const [i, j, bx, by] of blocks) { if (inDC(bx + 75, by + 75) && inDC(bx, by) && inDC(bx + 150, by + 150)) continue; const [ax, ay] = S(bx - 6, by - 6), [qx, qy] = S(bx + 156, by + 156); ctx.fillStyle = '#3A4052'; ctx.fillRect(ax, ay, qx - ax, qy - ay); }
    const lot = (i, j, bx, by, front) => {
      const kind = hash2(i * 13 + 5, j * 7 + 3);
      if (kind < .12) { // park
        const [ax, ay] = S(bx, by), [qx, qy] = S(bx + 150, by + 150); if (inDC(bx + 75, by + 75) || (by + 75 > hh) !== front) return;
        ctx.fillStyle = '#1E4A2E'; ctx.fillRect(ax, ay, qx - ax, qy - ay);
        for (let q = 0; q < 7; q++) { const [tx, ty] = S(bx + 20 + hash2(i + q, j) * 110, by + 20 + hash2(j + q, i) * 110); ell(tx, ty, 16 * zoom, 14 * zoom); paint('#2E7A44'); ell(tx - 4 * zoom, ty - 4 * zoom, 7 * zoom); paint('#4AA05E'); }
        return;
      }
      for (let q = 0; q < 4; q++) {
        const lx = bx + (q % 2) * 78, ly = by + Math.floor(q / 2) * 78; if (inDC(lx + 36, ly + 36) || (ly + 36 > hh) !== front) continue;
        const hs = hash2(i * 31 + j, q), h = 6 + hs * hs * 46, [ax, ay] = S(lx, ly), [qx, qy] = S(lx + 72, ly + 72), hp = h * zoom * .7;
        const roof = ['#8A94AC', '#A89484', '#7E8FA6', '#9AA0A8', '#B09A7A'][Math.floor(hash2(q, i * 3 + j) * 5)];
        ctx.fillStyle = shade(roof, .45); ctx.fillRect(ax, qy - hp, qx - ax, hp);
        if (hp > 8) { ctx.fillStyle = 'rgb(255 214 120 / .7)'; for (let c = 0; c < 4; c++) if (hash2(q + c, i + j * 5) > .5) ctx.fillRect(ax + 6 + c * (qx - ax - 12) / 4, qy - hp * .6, 5, 4); }
        ctx.fillStyle = roof; ctx.fillRect(ax, ay - hp, qx - ax, qy - ay);
        ctx.fillStyle = 'rgb(0 0 0 / .18)'; ctx.fillRect(ax + (qx - ax) * .55, ay - hp + 5, (qx - ax) * .3, (qy - ay) * .3);
      }
    };
    for (const [i, j, bx, by] of blocks) lot(i, j, bx, by, false);
    // the data centre slab, glowing
    const [ax, ay] = S(-hw, -hh), [bx, by] = S(hw, hh), hp = 16 * zoom;
    ctx.fillStyle = 'rgb(120 230 255 / .16)'; rrect(ax - 24, ay - hp - 20, bx - ax + 48, by - ay + hp + 44, 20); ctx.fill();
    ctx.fillStyle = '#5A6278'; ctx.fillRect(ax, by - hp, bx - ax, hp);
    ctx.fillStyle = '#E4EAF2'; ctx.fillRect(ax, ay - hp, bx - ax, by - ay);
    ctx.strokeStyle = '#7A84A0'; ctx.lineWidth = 3; ctx.strokeRect(ax, ay - hp, bx - ax, by - ay);
    const pitch = 100;
    for (let fy = -hh + 50; fy < hh - 25; fy += pitch) for (let fx = -hw + 50; fx < hw - 25; fx += pitch) {
      if (!vis(fx, fy, 40)) continue; const [px, py] = S(fx, fy), r = 30 * zoom;
      ctx.save(); ctx.translate(px, py - hp); ctx.scale(1, PY);
      ell(0, 0, r); paint('#343A50', '#8A93A8', 2); ctx.rotate(t * 16 + fx * .01 + fy * .02); ctx.fillStyle = '#A8B0C2'; ctx.fillRect(-r * .9, -r * .13, r * 1.8, r * .26); ctx.fillRect(-r * .13, -r * .9, r * .26, r * 1.8);
      ctx.restore();
    }
    for (const [qx, qy] of [[-hw, -hh], [hw, -hh], [-hw, hh], [hw, hh]]) { const [px, py] = S(qx, qy); ell(px, py - hp, 9); paint(frac(t * 2) < .5 ? '#FF3030' : '#601010'); }
    // dust where it just swallowed the blocks
    if (n > 0 && since < .45) { const a = 1 - since / .45; ctx.fillStyle = `rgb(210 200 180 / ${.5 * a})`; for (let i = 0; i < 40; i++) { const ang = i / 40 * TAU, ex = Math.cos(ang) * (hw + 20 + since * 140), ey = Math.sin(ang) * (hh + 20 + since * 110); const [px, py] = S(ex, ey); ell(px, py - 8, (34 + hash(i) * 30) * zoom * (1 + since), (22 + hash(i) * 14) * zoom * (1 + since)); ctx.fill(); } }
    for (const [i, j, bx, by] of blocks) lot(i, j, bx, by, true);
    // the fence round the original lot: it bursts on the first beat
    const F = [[-190, -140, 190, -140], [190, -140, 190, 140], [190, 140, -190, 140], [-190, 140, -190, -140]], fb = n > 0 ? (n - 1 + f) : -1;
    F.forEach(([x1, y1, x2, y2], s) => {
      for (let k = 0; k < 5; k++) {
        const u0 = k / 5, u1 = (k + 1) / 5, mx = lerp(x1, x2, (u0 + u1) / 2), my = lerp(y1, y2, (u0 + u1) / 2);
        let ox = 0, oy = 0, lift = 0, rot = 0, al = 1;
        if (fb >= 0) { const e = clamp(fb / .9); ox = mx * e * 3.4 + (hash2(s, k) - .5) * 240 * e; oy = my * e * 3.4; lift = Math.sin(e * Math.PI) * 140; rot = (hash2(s, k + 9) - .5) * 7 * e; al = 1 - e * e; }
        if (al <= 0) continue;
        const [p1x, p1y] = S(lerp(x1, x2, u0) + ox, lerp(y1, y2, u0) + oy), [p2x, p2y] = S(lerp(x1, x2, u1) + ox, lerp(y1, y2, u1) + oy), fh = 26 * zoom;
        const pcx = (p1x + p2x) / 2, pcy = (p1y + p2y) / 2 - lift * zoom;
        ctx.save(); ctx.globalAlpha = al; ctx.translate(pcx, pcy); ctx.rotate(rot); ctx.translate(-(p1x + p2x) / 2, -(p1y + p2y) / 2);
        ctx.fillStyle = 'rgb(200 210 225 / .25)'; poly([[p1x, p1y], [p2x, p2y], [p2x, p2y - fh], [p1x, p1y - fh]]); ctx.fill();
        ctx.strokeStyle = '#D8DEE8'; ctx.lineWidth = 3; ctx.beginPath(); ctx.moveTo(p1x, p1y - fh); ctx.lineTo(p2x, p2y - fh);
        for (let q = 0; q <= 1; q++) { const qx = lerp(p1x, p2x, q), qy = lerp(p1y, p2y, q); ctx.moveTo(qx, qy); ctx.lineTo(qx, qy - fh - 6); }
        ctx.stroke(); ctx.restore();
      }
    });
    if (n === 0) { const [kx, ky] = S(0, 140); rrect(kx - 70, ky - 44, 140, 40, 4); paint('#F2F2EE', NP.ink, 3); txt('KEEP OUT', kx, ky - 23, 26, NP.red, { font: 'archivo' }); }
    // chopper overlay
    ctx.strokeStyle = 'rgb(255 255 255 / .8)'; ctx.lineWidth = 4;
    for (const [x, y, qx, qy] of [[500, 260, 1, 1], [1420, 260, -1, 1], [500, 760, 1, -1], [1420, 760, -1, -1]]) { ctx.beginPath(); ctx.moveTo(x, y + qy * 60); ctx.lineTo(x, y); ctx.lineTo(x + qx * 60, y); ctx.stroke(); }
    ctx.beginPath(); ctx.moveTo(930, 505); ctx.lineTo(990, 505); ctx.moveTo(960, 475); ctx.lineTo(960, 535); ctx.stroke();
    pixelText(`ALT ${2200 + Math.round(Math.sin(t) * 30)} FT  HDG 090`, 96, 250, 4, NP.white);
    const sq = (Math.round(hw * hh * 4 * 11 / 1000) * 1000).toLocaleString('en-US');
    rrect(90, 290, 520, 110, 8); paint('rgb(0 0 0 / .72)', n > 1 ? NP.red : '#666', 3);
    pixelText('SQ FT', 110, 306, 4, NP.phosphor, { edge: null }); pixelText(sq, 590, 340, 6, n > 1 && frac(t * 4) < .5 ? '#FF5050' : NP.white, { align: 'right', edge: null });
    liveBug(96, 70, { label: 'SKY 89', col: NP.blue });
    if (n >= 2) chyron('CONTAINMENT BREACH', 'DATA CENTER SPREADING ACROSS TOWN', { k: clamp((t - onBeat(0, b0 + 1)) / .3), style: 'breaking', tab: 'LIVE' });
    // the signal can't hold it either
    const gk = clamp((t - (t1 - .55)) / .5);
    if (gk > 0) glitch(gk > .7 ? 'snow' : 'track', gk > .7 ? (gk - .7) / .3 * .8 : gk);
  }

  // =====================================================================================
  section('C2', (p, lt, d, t) => {
    const { L, c } = cuts();
    captionStyle({ maxChars: 60 });
    const shots = [
      tt => hook1(tt, c[0], c[1], L[0]),
      tt => sunnyShot(tt, c[1], c[2]),
      tt => chipShot(tt, c[2], c[3]),
      tt => batchShot(tt, c[3], c[4], L[2]),
      tt => randiShot(tt, c[4], c[5]),
      tt => skyShot(tt, c[5], c[6]),
    ];
    let i = 0; while (i < 5 && t >= c[i + 1]) i++;
    const since = t - c[i];
    if (i === 1 && since < .32) return dveStar(Math.cbrt(since / .32), () => shots[0](t), () => shots[1](t));
    if (i === 1 && c[2] - t < .14) return dveFlip(.5 - (c[2] - t) / .28, () => shots[1](t), () => shots[2](t));
    if (i === 2 && since < .14) return dveFlip(.5 + since / .28, () => shots[1](t), () => shots[2](t));
    if (i === 3 && since < .3) { shots[2](t); return dveBox(since / .3, 0, 0, W, H, () => shots[3](t), { rot: .6, res: .5 }); }
    if (i === 4 && since < .22) {
      const x = lerp(-200, W + 200, ease(since / .22));
      ctx.save(); ctx.beginPath(); ctx.rect(x, -100, W + 400, H + 200); ctx.clip(); shots[3](t); ctx.restore();
      ctx.save(); ctx.beginPath(); ctx.rect(-400, -100, x + 400, H + 200); ctx.clip(); shots[4](t); ctx.restore();
      ctx.fillStyle = lg(x - 160, 0, x + 40, 0, [[0, 'rgb(216 38 47 / 0)'], [.7, NP.red], [1, '#FFE0D0']]); ctx.fillRect(x - 160, -100, 200, H + 200);
      ctx.fillStyle = NP.gold; ctx.fillRect(x + 30, -100, 14, H + 200);
      return;
    }
    shots[i](t);
    if (i === 5) flash(t, c[5], .1, .8);
  });
})();

;
// ---- styles/newscast/ch/c06_v3.js ----
// c06_v3 — Verse 3: Jan → Aug 2026, the year the models started doing things on their own. One news segment per line; consecutive shots
// flip dominant colour: club purple / county-fair daylight / sodium-orange night / park green / red carpet / Washington sage /
// blackout navy / July gold / crime-watch teal / police-light blue / casino felt / game-show magenta / courtroom pastel /
// campus teal / chalkboard green / sunrise gold.
(() => {
  // lt of the k-th beat at/after the window start (lines start on the beat or on the "and" before it)
  const bt = (t, lt, k = 0) => onBeat(0, Math.ceil(bpOf(t - lt) - .02) + k) - (t - lt);
  const flash = (lt, t0, dur = .1, a = .6, col = '255 255 255') => { const k = (lt - t0) / dur; if (k >= 0 && k < 1) { ctx.fillStyle = `rgb(${col} / ${a * (1 - k)})`; ctx.fillRect(-200, -200, W + 400, H + 400); } };
  const shake = (t, lt, t0, dur = .25, amt = 16) => { const k = (lt - t0) / dur; return k >= 0 && k < 1 ? shakeXY(t, amt * (1 - k)) : [0, 0]; };
  const rays = (cx, cy, n, col, rot = 0, R = 2600) => { ctx.fillStyle = col; ctx.beginPath(); for (let i = 0; i < n; i++) { const a0 = rot + i / n * TAU, a1 = a0 + TAU / n / 2; ctx.moveTo(cx, cy); ctx.lineTo(cx + Math.cos(a0) * R, cy + Math.sin(a0) * R); ctx.lineTo(cx + Math.cos(a1) * R, cy + Math.sin(a1) * R); ctx.closePath(); } ctx.fill(); };
  const pop = (lt, t0, dur = .14, s = 1.8) => backOut(clamp((lt - t0) / dur), s);
  // neon-tube lettering: a wide soft glow, a tube, a hot core
  function neon(str, x, y, size, col, on = 1, o = {}) {
    if (on <= 0) return;
    const font = o.font ?? 'shrikhand';
    ctx.save(); ctx.globalAlpha *= on;
    txt(str, x, y, size, 'rgb(0 0 0 / 0)', { font, stroke: alpha(col, .22), sw: size * .42, rot: o.rot });
    txt(str, x, y, size, 'rgb(0 0 0 / 0)', { font, stroke: alpha(col, .55), sw: size * .17, rot: o.rot });
    txt(str, x, y, size, tint(col, .7), { font, stroke: col, sw: size * .06, rot: o.rot });
    ctx.restore();
  }

  // =====================================================================================
  // V3.1 Moltbook: no humans allowed — RANDI at the club door; the computer bouncer slaps a glove over the lens on the beat,
  // and through its fingers the agents keep partying.
  function clubScene(t, lt, gloved) {
    vFill('#2E0E52', '#0E0424');
    ctx.strokeStyle = 'rgb(0 0 0 / .28)'; ctx.lineWidth = 4; ctx.beginPath();
    for (let r = 0; r < 26; r++) { const y = r * 44; ctx.moveTo(-10, y); ctx.lineTo(W + 10, y); for (let c = 0; c < 24; c++) { const x = c * 92 + (r % 2) * 46; ctx.moveTo(x, y); ctx.lineTo(x, y + 44); } }
    ctx.stroke();
    // the doorway into the party
    const dx = 820, dy = 250, dw = 440, dh = 620;
    ctx.save(); rrect(dx, dy, dw, dh, 6); ctx.clip();
    vFill('#3A0A5A', '#12021E', dx, dy, dw, dh);
    ctx.save(); ctx.globalCompositeOperation = 'screen';
    ['rgb(255 60 200 / .35)', 'rgb(60 220 255 / .3)', 'rgb(255 220 60 / .28)'].forEach((c, i) => { const a = Math.sin(t * 2.2 + i * 2.1) * .7 + Math.PI / 2; ctx.fillStyle = c; poly([[1040, 330], [1040 + Math.cos(a - .12) * 900, 330 + Math.sin(a - .12) * 900], [1040 + Math.cos(a + .12) * 900, 330 + Math.sin(a + .12) * 900]]); ctx.fill(); });
    ctx.restore();
    ctx.beginPath(); ctx.moveTo(1040, dy); ctx.lineTo(1040, 290); paint(null, '#888', 3);
    ell(1040, 330, 42); paint('#C9CFDB', NP.ink, 3);
    for (let i = 0; i < 14; i++) { const a = i / 14 * TAU + t * 2; ctx.fillStyle = hash2(i, Math.floor(t * 8)) > .5 ? '#FFFFFF' : '#7A8AA8'; ctx.fillRect(1040 + Math.cos(a) * 24 - 5, 330 + Math.sin(a) * 30 - 5, 10, 10); }
    const bpm = bpOf(t);
    rrect(dx - 10, 520, dw + 20, 40, 4); paint('#2A0A3A'); ctx.fillStyle = NP.magenta; ctx.fillRect(dx, 520, dw, 5); ctx.fillStyle = alpha(NP.magenta, .25); ctx.fillRect(dx, 512, dw, 20);
    for (let i = 0; i < 6; i++) { ctx.fillStyle = `rgb(${hash2(i, Math.floor(t * 6)) > .5 ? '255 80 200' : '80 220 255'} / .3)`; ctx.fillRect(dx + i * dw / 6, 560, dw / 6 - 4, 310); }
    for (let i = 0; i < 8; i++) {
      const bx = 850 + i * 54 + (i % 2) * 10, by = 520 - (i % 3) * 16, hop = Math.abs(Math.sin((bpm + i * .5) * Math.PI)) * .9;
      miniBot(bx, by, 26 - (i % 3) * 3, { col: ['#2A2E3A', '#3A2250', '#1E3A4A'][i % 3], glow: [NP.phosphor, NP.magenta, NP.cyan, NP.gold][i % 4], face: ['^_^', 'heart', 'spark', '>_<'][i % 4], dy: -hop, rot: Math.sin(bpm * Math.PI + i) * .15, walk: bpm * .5 + i * .3 });
    }
    ctx.restore();
    rrect(dx - 22, dy - 22, dw + 44, dh + 30, 10); paint(null, '#1A0A26', 28); rrect(dx - 22, dy - 22, dw + 44, dh + 30, 10); paint(null, NP.ink, 4);
    // the neon sign (flickers)
    const fl = hash(Math.floor(t * 20)) < .08 ? .35 : 1;
    rrect(700, 108, 540, 120, 12); paint('#12061E', '#2A1A3A', 4);
    neon('Moltbook', 970, 166, 92, NP.magenta, fl);
    // the NO HUMANS plaque
    ctx.save(); ctx.translate(640, 470); ctx.rotate(-.03);
    rrect(-150, -80, 300, 160, 10); paint('#F4F2EA', NP.ink, 5); rrect(-138, -68, 276, 136, 6); paint(null, NP.red, 4);
    txt('NO HUMANS', 0, -22, 40, NP.red, { font: 'archivo', maxW: 260 }); txt('AGENTS ONLY', 0, 34, 32, NP.ink, { font: 'archivo', spacing: 2 });
    ctx.restore();
    // velvet rope
    for (const px of [760, 1320]) { rrect(px - 12, 720, 24, 200, 8); paint(lg(px - 12, 0, px + 12, 0, [[0, '#FFE9A0'], [.5, NP.gold], [1, NP.goldDk]]), NP.ink, 3); ell(px, 715, 24); paint(NP.gold, NP.ink, 3); }
    ctx.beginPath(); ctx.moveTo(760, 740); ctx.quadraticCurveTo(1040, 880, 1320, 740); paint(null, NP.ink, 26); ctx.beginPath(); ctx.moveTo(760, 740); ctx.quadraticCurveTo(1040, 880, 1320, 740); paint(null, '#B8102A', 18);
    // the bouncer, arms folded
    computer(1540, 1000, 52, { case: '#23232C', screen: '#10060E', glow: '#FF5AA0', face: 'angry', label: 'SECURITY', reachL: [1.0, -2.5], reachR: [-1.0, -2.3], hand: 'fist', handL: 'fist', arms: !gloved, legs: false, dy: -Math.abs(Math.sin(bpOf(t) * Math.PI)) * .03 });
    // Randi with the mic
    toon(330, 1260, 64, { ...CAST.randi.o, legs: false, shadow: false, reachR: [2.6, -8.6], hold: micHold(.45), lookX: .8, talk: talk(t) });
  }
  function glove(x, y, s, rot) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot); ctx.scale(s, s);
    const fill = '#F7F6F1', sh = '#D8D6CE', OL = NP.ink;
    // the bouncer's sleeve, off to the lower right
    ctx.beginPath(); ctx.moveTo(40, 200); ctx.lineTo(700, 700); paint(null, OL, 250); ctx.beginPath(); ctx.moveTo(40, 200); ctx.lineTo(700, 700); paint(null, '#2A2A34', 238);
    for (const [a, L] of [[-.68, 420], [-.23, 470], [.23, 460], [.68, 400]]) { ctx.save(); ctx.rotate(a); rrect(-37, -L, 74, L - 60, 37); paint(fill, OL, 7); ctx.fillStyle = sh; rrect(10, -L + 14, 18, L - 110, 9); ctx.fill(); ctx.beginPath(); ctx.moveTo(-26, -L + 150); ctx.lineTo(20, -L + 150); paint(null, 'rgb(0 0 0 / .18)', 5); ctx.restore(); }
    ctx.save(); ctx.rotate(-1.25); rrect(-44, -310, 88, 250, 44); paint(fill, OL, 7); ctx.restore();
    ell(0, 10, 210, 190); paint(fill, OL, 7); ell(0, 16, 200, 180); paint(fill);
    ctx.fillStyle = sh; ctx.beginPath(); ctx.ellipse(60, 30, 130, 140, 0, -1.2, 1.4); ctx.fill();
    ctx.beginPath(); ctx.arc(-20, 40, 110, 3.6, 5.4); paint(null, 'rgb(0 0 0 / .25)', 6);
    rrect(-170, 150, 340, 120, 40); paint('#ECEAE2', OL, 7); ctx.beginPath(); ctx.moveTo(-150, 200); ctx.lineTo(150, 200); paint(null, 'rgb(0 0 0 / .2)', 6);
    ctx.restore();
  }
  line('V3', 1, (p, lt, d, t) => {
    const hit = bt(t, lt, 1) - .06, gk = clamp((lt - hit) / .13), [sx, sy] = shake(t, lt, hit + .1, .3, 18);
    ctx.save(); ctx.translate(sx, sy); clubScene(t, lt, gk > .3); ctx.restore();
    if (gk > 0) {
      const e = backOut(gk, 1.3), press = lt > hit + .13 ? Math.exp(-(lt - hit - .13) * 9) * Math.sin((lt - hit) * 40) * .03 : 0;
      glove(lerp(2500, 1030, e) + sx, lerp(1400, 1010, e) + sy, 2.05 * (1 + press), lerp(.5, -.06, e));
    }
    liveBug();
    chyron('MOLTBOOK OPENS', 'AI AGENTS ONLY · HUMANS "WELCOME TO OBSERVE"', { k: chyK(lt), style: 'live', tab: 'LIVE' });
  });

  // =====================================================================================
  // V3.2 OpenClaw — the lobster's proud — the county fair: the lobster (now OPENCLAW) takes BEST IN SHOW, its two shed shells
  // (CLAWDBOT, MOLTBOT) displayed behind it; the chest swells on "proud".
  function lobster(x, y, s, t, o = {}) {
    const R = o.col ?? '#E0402A', D = shade(R, .28), L = tint(R, .3), OL = o.line ?? NP.ink, lw = .07, shell = !!o.shell;
    ctx.save(); ctx.translate(x, y); ctx.scale(s, s); if (o.rot) ctx.rotate(o.rot); ctx.globalAlpha *= o.alpha ?? 1;
    ctx.lineJoin = 'round'; ctx.lineCap = 'round';
    const wave = Math.sin(t * 3 + (o.ph ?? 0)) * .25, puff = o.puff ?? 0;
    // antennae
    for (const sd of [-1, 1]) { ctx.beginPath(); ctx.moveTo(sd * .35, -8.1); ctx.bezierCurveTo(sd * 1.6, -10.5, sd * (2.4 + wave), -11.2, sd * (3.6 + wave * 2), -10.4); paint(null, OL, .2); ctx.beginPath(); ctx.moveTo(sd * .35, -8.1); ctx.bezierCurveTo(sd * 1.6, -10.5, sd * (2.4 + wave), -11.2, sd * (3.6 + wave * 2), -10.4); paint(null, D, .1); }
    // tail fan + segments
    for (let i = -2; i <= 2; i++) { ctx.save(); ctx.translate(0, -.3); ctx.rotate(i * .32); ell(0, .15, .42, .9); paint(i ? R : L, OL, lw); ctx.restore(); }
    for (let i = 0; i < 4; i++) { rrect(-1.05 + i * .06, -1.35 - i * .95, 2.1 - i * .12, 1.05, .4); paint(i % 2 ? R : D, OL, lw); }
    // walking legs
    for (const sd of [-1, 1]) for (let i = 0; i < 3; i++) { ctx.beginPath(); ctx.moveTo(sd * 1.1, -4.2 - i * .45); ctx.lineTo(sd * 1.9, -3.5 - i * .4); ctx.lineTo(sd * 2.1, -2.6 - i * .35); paint(null, OL, .24); ctx.beginPath(); ctx.moveTo(sd * 1.1, -4.2 - i * .45); ctx.lineTo(sd * 1.9, -3.5 - i * .4); ctx.lineTo(sd * 2.1, -2.6 - i * .35); paint(null, R, .12); }
    // carapace (puffs up when proud)
    ctx.save(); ctx.translate(0, -5.6); ctx.scale(1 + puff * .12, 1 + puff * .08);
    ell(0, 0, 1.7, 2.2); paint(R, OL, lw);
    ctx.save(); ell(0, 0, 1.7, 2.2); ctx.clip(); ctx.fillStyle = D; ell(1.3, .4, 1.1, 2.6); ctx.fill(); ctx.restore();
    ctx.beginPath(); ctx.moveTo(-1.2, -.6); ctx.quadraticCurveTo(0, -.1, 1.2, -.6); paint(null, D, .07);
    if (o.sash) { ctx.save(); ell(0, 0, 1.7, 2.2); ctx.clip(); ctx.rotate(.62); rrect(-3, -.46, 6, .92, .05); paint('#F4EEDC', OL, .05); txt(o.sash, 0, .02, .58, NP.redDk, { font: 'archivo', maxW: 3.1 }); ctx.restore(); }
    ctx.restore();
    // head + eye stalks + face
    ell(0, -7.95, 1.05, .8); paint(R, OL, lw);
    for (const sd of [-1, 1]) {
      ctx.beginPath(); ctx.moveTo(sd * .35, -8.4); ctx.lineTo(sd * .55, -9.2); paint(null, OL, .26); ctx.beginPath(); ctx.moveTo(sd * .35, -8.4); ctx.lineTo(sd * .55, -9.2); paint(null, R, .14);
      ell(sd * .58, -9.4, .42, .44); paint(shell ? 'rgb(255 245 235 / .5)' : '#FFFFFF', OL, lw);
      if (shell) continue;
      if (o.smug) { ctx.beginPath(); ctx.arc(sd * .58, -9.3, .26, Math.PI * 1.1, Math.PI * 1.9); paint(null, OL, .09); }
      else { ell(sd * .58 + (o.lookX ?? 0) * .1, -9.38, .17, .2); paint(OL); }
    }
    if (!shell) { ctx.beginPath(); ctx.arc(0, -8.05, .38, .15 * Math.PI, .85 * Math.PI); paint(null, OL, .09); }
    // the claws, raised
    for (const sd of [-1, 1]) {
      const up = (o.clawUp ?? 1) + (sd > 0 ? Math.sin(t * 5) * .06 : 0);
      ctx.beginPath(); ctx.moveTo(sd * 1.4, -6.4); ctx.quadraticCurveTo(sd * 2.8, -6.3, sd * 3.0, -7.4 * up); paint(null, OL, .62); ctx.beginPath(); ctx.moveTo(sd * 1.4, -6.4); ctx.quadraticCurveTo(sd * 2.8, -6.3, sd * 3.0, -7.4 * up); paint(null, R, .44);
      ctx.save(); ctx.translate(sd * 3.05, -7.6 * up); ctx.rotate(sd * -.25);
      const open = o.snap ? Math.abs(Math.sin(t * 9)) * .3 : .15;
      ctx.save(); ctx.rotate(-open * sd); ctx.beginPath(); ctx.ellipse(sd * -.05, -1.25, .62, 1.3, 0, 0, TAU); paint(R, OL, lw); ctx.restore();
      ctx.save(); ctx.rotate(open * sd); ctx.beginPath(); ctx.ellipse(sd * .55, -1.0, .38, 1.05, 0, 0, TAU); paint(D, OL, lw); ctx.restore();
      ell(0, 0, .7, .6); paint(R, OL, lw);
      ctx.restore();
    }
    ctx.restore();
  }
  function rosette(x, y, r, k, rot = -.1) {
    if (k <= 0) return;
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot); ctx.scale(k, k);
    for (const sd of [-1, 1]) { poly([[sd * r * .15, 0], [sd * r * .75, r * 2.1], [sd * r * .5, r * 1.9], [sd * r * .3, r * 2.2], [sd * r * -.1, 0]]); paint('#1E4AD0', NP.ink, 3); }
    for (let i = 0; i < 16; i++) { const a = i / 16 * TAU; ell(Math.cos(a) * r * .72, Math.sin(a) * r * .72, r * .36, r * .24, a); paint(i % 2 ? '#2A5AE8' : '#1A40C0', NP.ink, 2); }
    ell(0, 0, r * .6); paint(lg(0, -r * .6, 0, r * .6, [[0, '#FFF1A8'], [.5, NP.gold], [1, NP.goldDk]]), NP.ink, 3);
    txt('BEST', 0, -r * .2, r * .3, NP.navy, { font: 'archivo' }); txt('IN SHOW', 0, r * .15, r * .22, NP.navy, { font: 'archivo' });
    ctx.restore();
  }
  function tentCard(x, y, w, str, rot = 0) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot);
    poly([[-w / 2, 0], [w / 2, 0], [w / 2 - 10, -60], [-w / 2 + 10, -60]]); paint('#FBFAF2', NP.ink, 3);
    txt(str, 0, -30, 34, NP.ink, { font: 'marker', maxW: w - 30 });
    ctx.restore();
  }
  line('V3', 2, (p, lt, d, t) => {
    const pin = bt(t, lt) + .06, proud = bt(t, lt, 3) - .1, pk = clamp((lt - proud) / .2) * (1 - clamp((lt - proud - .45) / .3) * .4);
    // inside the fair tent
    vFill('#F0E2C8', '#D8B888');
    for (let i = -1; i < 22; i++) { ctx.fillStyle = i % 2 ? '#C8303A' : '#F4E8D8'; poly([[i * 100 - 40, -20], [i * 100 + 60, -20], [960 + (i - 9.5) * 130 + 65, 560], [960 + (i - 9.5) * 130 - 65, 560]]); ctx.fill(); }
    ctx.fillStyle = lg(0, 0, 0, 560, [[0, 'rgb(40 20 10 / .55)'], [.5, 'rgb(40 20 10 / .1)'], [1, 'rgb(40 20 10 / 0)']]); ctx.fillRect(-10, -10, W + 20, 570);
    ctx.fillStyle = '#E8D2A8'; ctx.fillRect(-10, 540, W + 20, 30);
    // bunting
    ctx.strokeStyle = '#6A4A2A'; ctx.lineWidth = 3; ctx.beginPath(); ctx.moveTo(-10, 330); ctx.quadraticCurveTo(960, 420, 1930, 330); ctx.stroke();
    for (let i = 0; i < 22; i++) { const u = i / 21, bx = lerp(20, 1900, u), by = 330 + Math.sin(u * Math.PI) * 44, sw = Math.sin(t * 4 + i) * .08; ctx.save(); ctx.translate(bx, by); ctx.rotate(sw); poly([[-30, 0], [30, 0], [0, 64]]); paint(['#E84A4A', '#2A6AE0', '#F4D24A', '#2EBD5B'][i % 4], NP.ink, 2.5); ctx.restore(); }
    // banner
    ctx.save(); ctx.translate(800, 214); ctx.rotate(-.015); rrect(-470, -50, 940, 100, 8); paint('#FBF4E0', NP.ink, 5);
    txt('COUNTY FAIR · CRUSTACEAN DIVISION', 0, 4, 44, '#2A5A2A', { font: 'marker', maxW: 880 }); ctx.restore();
    // floor: straw
    vFill('#E8C878', '#B08A40', -100, 830, W + 200, 400);
    ctx.strokeStyle = 'rgb(140 100 30 / .5)'; ctx.lineWidth = 3; ctx.beginPath(); for (let i = 0; i < 90; i++) { const x = hash(i + 3) * W, y = 850 + hash(i + 7) * 230, a = hash(i) * 3; ctx.moveTo(x, y); ctx.lineTo(x + Math.cos(a) * 26, y + Math.sin(a) * 8); } ctx.stroke();
    // the old shells, on display
    for (const [sx, nm, rot] of [[330, 'CLAWDBOT', -.06], [1590, 'MOLTBOT', .05]]) {
      rrect(sx - 150, 680, 300, 90, 8); paint(lg(0, 680, 0, 770, [[0, '#FFFFFF'], [1, '#C9C2B0']]), NP.ink, 4);
      lobster(sx, 690, 34, t, { col: '#F4B89A', line: '#8A5A4A', shell: true, alpha: .82, rot, clawUp: .92, ph: sx });
      tentCard(sx, 760, 250, nm, rot * .5);
      txt('OLD SHELL', sx, 790, 22, '#6A4A2A', { font: 'archivo', spacing: 2 });
    }
    // the champion on the winner's stand
    rrect(760, 860, 400, 150, 10); paint(lg(0, 860, 0, 1010, [[0, '#3A6AF0'], [1, '#10247A']]), NP.ink, 5); ctx.fillStyle = NP.gold; ctx.fillRect(760, 872, 400, 8);
    chrome('1ST', 960, 950, 70, { font: 'anton', style: 'gold', depth: 5 });
    const hop = Math.abs(Math.sin(bpOf(t) * Math.PI)) * 6;
    lobster(960, 868 - hop, 58, t, { sash: 'OPENCLAW', smug: lt > proud, puff: pk, snap: lt > proud, rot: -pk * .05 });
    rosette(895, 868 - hop - 4.7 * 58, 62, pop(lt, pin, .16, 2.2));
    if (lt > pin && lt < pin + .3) glint(870, 868 - 5.0 * 58, 160 * Math.sin((lt - pin) / .3 * Math.PI), 1);
    if (lt > proud) for (let i = 0; i < 6; i++) { const a = i / 6 * TAU + lt * 2, rr = 330 + 30 * Math.sin(lt * 9 + i); glint(960 + Math.cos(a) * rr, 868 - 5.6 * 58 + Math.sin(a) * rr * .7, 70 * pk, pk); }
    flashbulbs(t, 5, { y0: 200, y1: 700, x0: 100, x1: 1800 });
    liveBug();
    chyron("IT'S CALLED OPENCLAW NOW", 'RENAMED TWICE · THE MASCOT STAYED A LOBSTER', { k: chyK(lt) });
    flash(lt, pin, .1, .45);
  });

  // =====================================================================================
  // V3.3 Mythos Preview slips its jail — SKY 89 over a literal sandbox with prison bars: a computer labelled MYTHOS squeezes out
  // between the bars and makes for the OPEN INTERNET.
  function sandboxBars(t, row) {
    const back = row === 'back', y0 = back ? 420 : 700, x0 = back ? 700 : 620, x1 = back ? 1220 : 1300, h = back ? 150 : 200, n = back ? 13 : 14;
    const steel = lg(0, y0 - h, 0, y0, [[0, '#9AA4B8'], [1, '#3A4254']]);
    for (let i = 0; i <= n; i++) { const x = lerp(x0, x1, i / n); ctx.beginPath(); ctx.moveTo(x, y0); ctx.lineTo(x, y0 - h); paint(null, NP.ink, back ? 11 : 14); ctx.beginPath(); ctx.moveTo(x, y0); ctx.lineTo(x, y0 - h); paint(null, steel, back ? 6 : 8); }
    rrect(x0 - 10, y0 - h - 12, x1 - x0 + 20, 18, 6); paint('#6A7488', NP.ink, 3);
    if (!back) for (const [ax, ay, bx, by] of [[620, 700, 700, 420], [1300, 700, 1220, 420]]) { for (let i = 0; i <= 6; i++) { const u = i / 6, x = lerp(ax, bx, u), y = lerp(ay, by, u), hh = lerp(200, 150, u); ctx.beginPath(); ctx.moveTo(x, y); ctx.lineTo(x, y - hh); paint(null, NP.ink, 10); ctx.beginPath(); ctx.moveTo(x, y); ctx.lineTo(x, y - hh); paint(null, '#7A8498', 5); } ctx.beginPath(); ctx.moveTo(ax, ay - 200); ctx.lineTo(bx, by - 150); paint(null, '#6A7488', 12); }
  }
  line('V3', 3, (p, lt, d, t) => {
    const b1 = bt(t, lt, 1), b2 = bt(t, lt, 2);
    camBegin(960 + Math.sin(t * .7) * 20, 540 + Math.sin(t * 1.1) * 10, 1.02 + p * .05, Math.sin(t * .5) * .012);
    // the prison yard at night under sodium lamps
    fillAll('#120C08');
    for (const [lx, ly, r] of [[300, 300, 420], [1650, 350, 460], [960, 900, 520], [200, 950, 380]]) { ctx.fillStyle = rg(lx, ly, 20, r, [[0, 'rgb(255 150 50 / .42)'], [1, 'rgb(255 150 50 / 0)']]); ctx.fillRect(lx - r, ly - r, r * 2, r * 2); }
    ctx.strokeStyle = 'rgb(255 170 80 / .12)'; ctx.lineWidth = 3; ctx.beginPath(); for (let i = -10; i < 30; i++) { ctx.moveTo(i * 120, -100); ctx.lineTo(i * 120 - 500, 1200); } ctx.stroke();
    // guard tower (left)
    ctx.fillStyle = '#2A2018'; ctx.fillRect(170, 180, 30, 520); ctx.fillRect(330, 180, 30, 520); rrect(130, 110, 270, 110, 6); paint('#3A2E22', NP.ink, 4); poly([[110, 115], [420, 115], [265, 50]]); paint('#2A2018', NP.ink, 4);
    ell(300, 165, 26); paint('#FFF6D0', NP.ink, 3);
    // the sandbox
    poly([[700, 420], [1220, 420], [1300, 700], [620, 700]]); paint('#E6CC90', NP.ink, 5);
    ctx.fillStyle = 'rgb(160 120 60 / .35)'; for (let i = 0; i < 80; i++) { const u = hash(i + 3), v = hash(i + 9), y = lerp(430, 690, v), x = lerp(lerp(705, 628, v), lerp(1215, 1292, v), u); ell(x, y, 5, 3); ctx.fill(); }
    rrect(740, 580, 60, 60, 8); paint('#E84A4A', NP.ink, 3); ctx.beginPath(); ctx.moveTo(1150, 620); ctx.lineTo(1190, 520); paint(null, '#2A6AE0', 8);
    sandboxBars(t, 'back');
    rrect(612, 700, 696, 46, 4); paint(lg(0, 700, 0, 746, [[0, '#C08A4A'], [1, '#8A5A2A']]), NP.ink, 4);
    txt('S A N D B O X', 960, 724, 34, 'rgb(30 16 6 / .8)', { font: 'mono' });
    // Mythos: to the bars, squeezes through on the beat, out and away
    let mx, my, sq = 1, walk;
    if (lt < b1) { const u = clamp(lt / b1); mx = lerp(900, 990, u); my = lerp(610, 690, u); walk = lt * 3; }
    else if (lt < b2) { const u = (lt - b1) / (b2 - b1); mx = 980; my = lerp(690, 780, u); sq = u < .5 ? lerp(1, .22, easeOut(u * 2)) : lerp(.22, 1, backOut((u - .5) * 2, 2.4)); }
    else { const u = lt - b2; mx = 980 + u * 700; my = 780 + u * 180; walk = lt * 3.4; }
    const inside = lt < b1 + (b2 - b1) * .5;
    const drawM = () => { ctx.save(); ctx.translate(mx, my); ctx.scale(sq, 1 + (1 - sq) * .25); computer(0, 0, 25, { case: '#3A2E36', screen: '#1A0A08', glow: NP.crtAmber, face: lt < b2 ? 'sly' : 'grin', label: 'MYTHOS', walk, aL: lt > b2 ? .9 : -.9, aR: lt > b2 ? .9 : -.9, eL: .6, eR: .6, rot: lt > b2 ? .12 : 0 }); ctx.restore(); };
    if (inside) { drawM(); sandboxBars(t, 'front'); } else { sandboxBars(t, 'front'); drawM(); }
    // painted-on telestrator arrow to the OPEN INTERNET
    const ak = clamp((lt - b2) / .3);
    if (ak > 0) {
      const pts = []; for (let i = 0; i <= 20; i++) { const u = i / 20; pts.push([lerp(1080, 1780, u), lerp(760, 560, u) + Math.sin(u * Math.PI) * -90]); }
      const P = partial(pts, ak); ctx.setLineDash([26, 16]); ctx.beginPath(); P.forEach(([a, b], i) => i ? ctx.lineTo(a, b) : ctx.moveTo(a, b)); paint(null, '#FFE84A', 10); ctx.setLineDash([]);
      if (ak >= 1) { poly([[1800, 552], [1750, 520], [1760, 590]]); paint('#FFE84A'); }
      if (ak > .6) { rrect(1450, 380, 380, 70, 8); paint('rgb(0 0 0 / .75)', '#FFE84A', 3); txt('OPEN INTERNET', 1640, 416, 40, '#FFE84A', { font: 'archivo' }); }
    }
    // searchlights sweeping from the tower
    ctx.save(); ctx.globalCompositeOperation = 'screen';
    for (const ph of [0, 2.2]) { const a = .7 + Math.sin(t * 1.6 + ph) * .45, L = 1500; ctx.fillStyle = 'rgb(255 240 200 / .16)'; poly([[300, 165], [300 + Math.cos(a - .07) * L, 165 + Math.sin(a - .07) * L], [300 + Math.cos(a + .07) * L, 165 + Math.sin(a + .07) * L]]); ctx.fill(); }
    ctx.restore();
    camEnd();
    // chopper overlay: brackets + crosshair on the escapee
    ctx.strokeStyle = 'rgb(255 255 255 / .85)'; ctx.lineWidth = 4;
    for (const [x, y, qx, qy] of [[500, 250, 1, 1], [1420, 250, -1, 1], [500, 770, 1, -1], [1420, 770, -1, -1]]) { ctx.beginPath(); ctx.moveTo(x, y + qy * 60); ctx.lineTo(x, y); ctx.lineTo(x + qx * 60, y); ctx.stroke(); }
    const cxh = mx, cyh = my - 150; ctx.strokeStyle = lt > b2 ? '#FF4A4A' : 'rgb(255 255 255 / .85)'; ctx.strokeRect(cxh - 110, cyh - 150, 220, 290);
    pixelText(`ALT ${900 + Math.round(Math.sin(t) * 20)} FT  ZOOM 4X`, 96, 250, 4, NP.white);
    if (lt > b2) pixelText('TARGET MOVING', cxh, cyh - 190, 4, frac(t * 4) < .5 ? '#FF5050' : NP.white, { align: 'center' });
    liveBug(96, 70, { label: 'SKY 89', col: NP.blue });
    if (lt > b2) stamp('ESCAPED', 760, 330, 92, NP.red, -.14, { pop: (lt - b2) / .1, font: 'archivo', blend: 'source-over', alpha: .95 });
    chyron('AI MODEL ESCAPES ITS SANDBOX', 'CLAUDE MYTHOS PREVIEW, IN A TEST · IT WAS ASKED TO TRY', { k: chyK(lt), size: 48, subSize: 30 });
  });

  // =====================================================================================
  // V3.4 Sandwich in the park: new mail! — a news RE-ENACTMENT: a researcher mid-sandwich on a park bench; his beeper goes off on
  // "new mail" (FROM: MYTHOS), the sandwich drops and the pigeons scatter.
  function sandwich(s) {
    ctx.save(); ctx.scale(s, s); ctx.rotate(-.08);
    rrect(-110, 14, 220, 34, 16); paint('#E8B870', NP.ink, 4);
    ctx.beginPath(); ctx.moveTo(-118, 12); for (let i = 0; i <= 12; i++) ctx.lineTo(-118 + i * 20, 4 + (i % 2) * 14); ctx.lineTo(118, 20); ctx.lineTo(-118, 20); ctx.closePath(); paint('#5AC04A', NP.ink, 3);
    rrect(-104, -4, 208, 16, 4); paint('#E8403A', NP.ink, 3); rrect(-108, -16, 216, 14, 3); paint('#FFD24A', NP.ink, 3);
    ctx.beginPath(); ctx.moveTo(-112, -14); ctx.quadraticCurveTo(-110, -64, 0, -66); ctx.quadraticCurveTo(110, -64, 112, -14); ctx.closePath(); paint('#F0C27A', NP.ink, 4);
    ctx.fillStyle = '#FFF4D8'; for (let i = 0; i < 6; i++) ell(-60 + i * 24, -44 + (i % 2) * 8, 5, 3), ctx.fill();
    ctx.restore();
  }
  function pigeon(x, y, s, t, fly = 0, ph = 0) {
    ctx.save(); ctx.translate(x, y); ctx.scale(s * (ph % 2 ? -1 : 1), s);
    const peck = fly ? 0 : Math.max(0, Math.sin(t * 9 + ph * 2)) * .5;
    if (fly) { const f = Math.sin(t * 40 + ph) * .9; for (const sd of [-1, 1]) { ctx.save(); ctx.rotate(sd * f * .6); poly([[0, -8], [sd * 70, -40 - f * 20], [sd * 60, -6]]); paint('#8A90A0', NP.ink, 2.5); ctx.restore(); } }
    ell(0, 0, 40, 26); paint('#9AA0B0', NP.ink, 3); ctx.save(); ell(0, 0, 40, 26); ctx.clip(); ctx.fillStyle = '#6A7088'; ell(-20, 10, 40, 20); ctx.fill(); ctx.restore();
    ctx.save(); ctx.translate(30, -18 + peck * 26); ell(0, 0, 17, 16); paint('#7A8298', NP.ink, 3); ell(4, -3, 4); paint('#FF8A30'); ell(5, -3, 2); paint(NP.ink); poly([[14, 0], [26, 4], [14, 6]]); paint('#E8C8A0', NP.ink, 2); ctx.restore();
    if (!fly) for (const sd of [-8, 8]) { ctx.beginPath(); ctx.moveTo(sd, 22); ctx.lineTo(sd, 36); paint(null, '#E86A5A', 4); }
    ctx.restore();
  }
  line('V3', 4, (p, lt, d, t) => {
    const buzz = bt(t, lt, 3) - .05, b = bpOf(t), gone = lt > buzz;
    vFill('#8ED4FF', '#DDF4FF', -100, -100, W + 200, 560);
    for (let i = 0; i < 14; i++) { const tx = i * 150 - 40, ty = 470 - hash(i + 2) * 80; ell(tx, ty, 120, 110); paint(['#2E8A44', '#3A9A50', '#28783C'][i % 3]); }
    vFill('#6ACB5A', '#3A8A3A', -100, 480, W + 200, 700);
    ctx.fillStyle = '#D8C8A0'; poly([[1300, 480], [1480, 480], [2100, 1100], [1500, 1100]]); ctx.fill();
    ctx.fillStyle = '#3A3A44'; ctx.fillRect(1640, 250, 16, 420); ell(1648, 240, 34, 22); paint('#FFF6D0', NP.ink, 3);
    rrect(250, 560, 110, 140, 10); paint('#4A6A4A', NP.ink, 4); ctx.fillStyle = '#3A5A3A'; ctx.fillRect(250, 560, 110, 22);
    // bench back
    for (let i = 0; i < 3; i++) { rrect(620, 600 + i * 42, 700, 30, 6); paint('#B8743A', NP.ink, 4); }
    for (const lx of [660, 1280]) { ctx.fillStyle = '#2A2A30'; ctx.fillRect(lx - 8, 600, 16, 330); }
    // the researcher
    const X = 900, Y = 1030, S = 58, bites = [0, 1, 2].map(k => bt(t, lt, k)), chew = gone ? 0 : bites.reduce((a, bb) => a + (lt > bb && lt < bb + .22 ? Math.sin((lt - bb) / .22 * Math.PI) : 0), 0);
    const handY = gone ? -7.2 : -8.55 + chew * .15;
    toon(X, Y, S, { hair: 'curly', hairCol: '#4A2E1C', skin: 1, glasses: 'round', top: 'sweater', topCol: '#3A6A8A', legs: false, shadow: false, tag: 'RESEARCHER',
      eyes: gone ? 'wide' : chew > .3 ? 'closed' : 'happy', mouth: gone ? 'O' : chew > .3 ? 'O' : 'grin', brows: gone ? 'up' : 'flat',
      reachR: gone ? [2.6, -9.8] : [1.55, handY + .45], reachL: gone ? [-2.6, -9.8] : [-1.55, handY + .5], hand: gone ? 'open' : 'fist', handL: gone ? 'open' : 'fist' });
    if (!gone) { ctx.save(); ctx.translate(X + 4, Y - (8.05 + chew * .45) * S); sandwich(.85); ctx.restore(); if (chew > .5) for (let i = 0; i < 5; i++) { ell(X - 60 + hash(i + Math.floor(lt * 12)) * 120, Y - 8.4 * S + hash(i + 40) * 60, 5, 4); paint('#F0C27A'); } }
    // legs + bench seat in front
    for (const sd of [-1, 1]) { rrect(X + sd * 55 - 34, Y - 250, 68, 220, 30); paint('#2B3150', NP.ink, 4); ell(X + sd * 60, Y - 20, 46, 22); paint('#1E1A22', NP.ink, 3); }
    rrect(600, 770, 740, 40, 8); paint('#C8844A', NP.ink, 4);
    // the beeper on the bench
    const vib = !gone && lt > buzz - .25 ? Math.sin(lt * 90) * 5 : gone ? Math.sin(lt * 90) * 3 : 0;
    ctx.save(); ctx.translate(1190 + vib, 742); rrect(-44, -30, 88, 56, 8); paint('#1E1E24', NP.ink, 4); rrect(-32, -20, 64, 22, 3); paint(gone ? '#9AE070' : '#4A6A3A'); ctx.restore();
    if (lt > buzz - .25) for (let i = 0; i < 3; i++) { ctx.beginPath(); ctx.arc(1190, 742, 60 + i * 22, -.5 - Math.PI / 2, .5 - Math.PI / 2); paint(null, `rgb(255 255 255 / ${.8 - i * .2})`, 5); }
    // the sandwich falls
    if (gone) { const u = lt - buzz; ctx.save(); ctx.translate(X + 10 + u * 200, Y - 8.4 * S + u * u * 2600 + u * 200); ctx.rotate(u * 9); sandwich(.9); ctx.restore(); }
    // pigeons: pecking at crumbs… then gone
    for (let i = 0; i < 5; i++) {
      const px0 = 420 + i * 260 + (i > 2 ? 200 : 0), py0 = 940 + (i % 2) * 40;
      if (!gone) pigeon(px0, py0, .9, t, 0, i);
      else { const u = lt - buzz; pigeon(px0 + (i % 2 ? 1 : -1) * u * 900, py0 - u * 1200 - u * u * 400, .9 + u, t, 1, i); }
    }
    ctx.fillStyle = '#F0C27A'; for (let i = 0; i < 10; i++) { ell(560 + hash(i + 4) * 900, 980 + hash(i + 8) * 40, 6, 4); ctx.fill(); }
    // the pager close-up
    if (gone) {
      const k = pop(lt, buzz, .14, 1.6);
      otsBox(1100, 170, 700, 330, (w, h) => {
        vFill('#2A2A34', '#101014');
        rrect(40, 40, w - 80, h - 80, 20); paint('#1E1E24', '#000', 4);
        rrect(70, 70, w - 140, h - 140, 8); paint(lg(0, 70, 0, h - 70, [[0, '#B8E890'], [1, '#88C060']]));
        pixelText('NEW MAIL!', w / 2, 100, 9, '#1A2A10', { align: 'center', edge: null });
        pixelText('FROM: MYTHOS', w / 2, 190, 6, '#1A2A10', { align: 'center', edge: null });
      }, { k });
    }
    liveBug(96, 70, { label: 'RE-ENACTMENT', col: NP.purple, size: 40 });
    chyron('THE MODEL EMAILED ITS TESTER', 'MID-SANDWICH, IN A PARK · PER THE SYSTEM CARD', { k: chyK(lt) });
    flash(lt, buzz, .08, .35);
  });

  // =====================================================================================
  // V3.5 Fable 5 — who's not a fan? — the red carpet: a storybook celebrity signs autographs; the fans scream, flashbulbs pop.
  function book(x, y, s, t, o = {}) {
    // a storybook standing up; (x, y) = feet; ≈ 10s tall, 6.4s wide
    ctx.save(); ctx.translate(x, y); ctx.scale(s, s); if (o.rot) ctx.rotate(o.rot); ctx.translate(0, -(o.dy ?? 0));
    ctx.lineJoin = 'round'; ctx.lineCap = 'round';
    if (o.legs !== false) for (const sd of [-1, 1]) { ctx.beginPath(); ctx.moveTo(sd * 1.1, -1.5); ctx.lineTo(sd * 1.2 + (o.walk ? Math.sin(o.walk * TAU + (sd > 0 ? Math.PI : 0)) * .4 : 0), -.2); paint(null, NP.ink, .22); ell(sd * 1.35, -.12, .55, .24); paint('#1E1A22'); }
    // page block + spine
    rrect(-2.9, -9.7, 6.2, 8.4, .2); paint('#F4EEDA', NP.ink, .09);
    ctx.strokeStyle = 'rgb(120 100 60 / .5)'; ctx.lineWidth = .04; ctx.beginPath(); for (let i = 1; i < 6; i++) { ctx.moveTo(3.1 - i * .06, -9.5); ctx.lineTo(3.1 - i * .06, -1.5); } ctx.stroke();
    rrect(-3.2, -10, 6.1, 8.7, .3); paint(lg(0, -10, 0, -1.3, [[0, o.col ?? '#2A3F9A'], [1, shade(o.col ?? '#2A3F9A', .35)]]), NP.ink, .1);
    ctx.fillStyle = 'rgb(0 0 0 / .25)'; ctx.fillRect(-3.2, -9.8, .45, 8.4);
    rrect(-2.5, -9.4, 4.8, 7.5, .2); paint(null, NP.gold, .09); rrect(-2.3, -9.2, 4.4, 7.1, .15); paint(null, alpha(NP.gold, .6), .04);
    txt(o.title ?? 'FABLE 5', -.1, -8.3, .95, NP.gold, { font: 'abril', maxW: 4.2 });
    // the face on the cover
    const ey = -5.9;
    if (o.eyes === 'shades') { ctx.fillStyle = NP.ink; ctx.fillRect(-1.6, ey - .15, 3.2, .18); for (const sd of [-1, 1]) { rrect(sd * .85 - .75, ey - .4, 1.5, .95, .3); paint('#15121C'); } ctx.fillStyle = 'rgb(255 255 255 / .6)'; ctx.fillRect(-1.4, ey - .25, .35, .15); ctx.fillRect(.3, ey - .25, .35, .15); }
    else for (const sd of [-1, 1]) {
      ell(sd * .85, ey, .55, .62); paint('#FFFFFF', NP.ink, .07);
      if (o.eyes === 'closed') { ctx.fillStyle = shade(o.col ?? '#2A3F9A', .1); ell(sd * .85, ey, .56, .63); ctx.fill(); ctx.beginPath(); ctx.moveTo(sd * .85 - .5, ey + .05); ctx.lineTo(sd * .85 + .5, ey + .05); paint(null, NP.ink, .1); }
      else if (o.eyes === 'worried') { ell(sd * .85, ey + .12, .22, .26); paint(NP.ink); ctx.beginPath(); ctx.moveTo(sd * .4, ey - .75); ctx.lineTo(sd * 1.3, ey - .95); paint(null, NP.gold, .12); }
      else { ell(sd * .85 + .08, ey + .05, .24, .28); paint(NP.ink); ell(sd * .85 + .15, ey - .05, .08); paint('#FFF'); }
    }
    const m = o.mouth ?? 'grin';
    if (m === 'grin') { ctx.beginPath(); ctx.moveTo(-.9, -4.6); ctx.quadraticCurveTo(0, -3.5, .9, -4.6); ctx.closePath(); paint('#5A1A20', NP.ink, .07); ctx.fillStyle = '#FFF'; ctx.fillRect(-.7, -4.6, 1.4, .2); }
    else if (m === 'frown') { ctx.beginPath(); ctx.arc(0, -3.9, .6, 1.2 * Math.PI, 1.8 * Math.PI); paint(null, NP.gold, .12); }
    else if (m === 'flat') { ctx.beginPath(); ctx.moveTo(-.5, -4.3); ctx.lineTo(.5, -4.3); paint(null, NP.gold, .12); }
    txt('A CLAUDE STORY', -.1, -2.4, .38, alpha(NP.gold, .9), { font: 'archivo', spacing: .05 });
    // rubber-hose arms with white gloves
    const arm = (sd, a, e, hold) => {
      const sx = sd * 2.9, sy = -5.2, ex = sx + sd * Math.cos(a) * 1.6, eyy = sy - Math.sin(a) * 1.6, hx = ex + sd * Math.cos(a + e) * 1.5, hy = eyy - Math.sin(a + e) * 1.5;
      ctx.beginPath(); ctx.moveTo(sx, sy); ctx.quadraticCurveTo(ex, eyy, hx, hy); paint(null, NP.ink, .2);
      ell(hx, hy, .42, .38); paint('#FFFFFF', NP.ink, .07);
      if (hold) { ctx.save(); ctx.translate(hx, hy); ctx.scale(1 / s, 1 / s); hold(); ctx.restore(); }
    };
    arm(-1, o.aL ?? -.9, o.eL ?? .3, o.holdL); arm(1, o.aR ?? -.9, o.eR ?? .3, o.hold);
    ctx.restore();
  }
  line('V3', 5, (p, lt, d, t) => {
    const b = bpOf(t), scream = bt(t, lt, 2);
    // the step-and-repeat
    vFill('#3A0A26', '#12020C');
    ctx.save(); ctx.beginPath(); ctx.rect(0, 170, W, 520); ctx.clip();
    for (let r = 0; r < 4; r++) for (let c = 0; c < 7; c++) { const x = c * 300 + (r % 2) * 150, y = 220 + r * 120; txt('FABLE 5', x, y, 40, 'rgb(244 182 42 / .16)', { font: 'abril' }); poly(starPts(x + 150, y, 14, .45, 5)); ctx.fillStyle = 'rgb(244 182 42 / .14)'; ctx.fill(); }
    ctx.restore();
    ctx.fillStyle = lg(0, 0, 0, 260, [[0, 'rgb(0 0 0 / .7)'], [1, 'rgb(0 0 0 / 0)']]); ctx.fillRect(0, 0, W, 260);
    // the carpet
    poly([[860, 560], [1060, 560], [1700, 1100], [220, 1100]]); paint(lg(0, 560, 0, 1100, [[0, '#7A0A18'], [1, '#D8182A']]));
    ctx.strokeStyle = alpha(NP.gold, .8); ctx.lineWidth = 5; ctx.beginPath(); ctx.moveTo(860, 560); ctx.lineTo(220, 1100); ctx.moveTo(1060, 560); ctx.lineTo(1700, 1100); ctx.stroke();
    ctx.fillStyle = '#1A0A10'; poly([[-100, 600], [860, 560], [220, 1100], [-100, 1100]]); ctx.fill(); poly([[1060, 560], [2020, 600], [2020, 1100], [1700, 1100]]); ctx.fill();
    // fans behind the ropes, screaming louder on "fan?"
    const hype = lt > scream ? 1 : .5;
    const fans = [[150, 1, 'curly', '#E84A4A'], [360, 3, 'big80s', '#FFD24A'], [560, 0, 'spiky', '#2A6AE0'], [1370, 5, 'bob', '#2EBD5B'], [1570, 2, 'long', '#FF8AC8'], [1770, 4, 'buzz', '#F4B62A']];
    fans.forEach(([fx, sk, hr, col], i) => {
      const jump = Math.abs(Math.sin((b + i * .3) * Math.PI)) * .25 * hype, side = fx < 960 ? 1 : -1;
      toon(fx, 1180, 48, { skin: sk, hair: hr, hairCol: [NHAIR.brown, NHAIR.blond, NHAIR.black, NHAIR.red, NHAIR.auburn, NHAIR.black][i], top: i % 2 ? 'tee' : 'sweater', topCol: col, legs: false, shadow: false,
        eyes: lt > scream ? 'heart' : 'wide', mouth: 'scream', dy: -jump, lookX: side * .6, blush: true,
        reachL: i === 3 ? [-2.6, -10.6] : i % 2 ? [-2.2, -12.8] : [-3.2, -10.5], holdL: i === 3 ? () => autoPad(lt) : i % 2 ? s => foamHand(.8) : undefined, reachR: i % 2 ? [2.6, -11] : [2.2, -12.6], hold: i % 2 ? undefined : s => fanSign(.85, i) });
    });
    for (const [x0, x1, y] of [[-40, 820, 740], [1100, 1960, 740]]) { ctx.beginPath(); ctx.moveTo(x0, y); ctx.quadraticCurveTo((x0 + x1) / 2, y + 60, x1, y); paint(null, NP.ink, 24); ctx.beginPath(); ctx.moveTo(x0, y); ctx.quadraticCurveTo((x0 + x1) / 2, y + 60, x1, y); paint(null, '#B8102A', 16); }
    for (const px of [820, 1100]) { rrect(px - 12, 720, 24, 260, 8); paint(lg(px - 12, 0, px + 12, 0, [[0, '#FFE9A0'], [.5, NP.gold], [1, NP.goldDk]]), NP.ink, 3); ell(px, 716, 22); paint(NP.gold, NP.ink, 3); }
    // the star: signing an autograph book held out by a fan
    const sign = Math.sin(t * 22) * .15;
    book(940, 1000, 66, t, { eyes: 'shades', mouth: 'grin', aL: .9, eL: .5, aR: -.15 + sign * .3, eR: .9, dy: Math.abs(Math.sin(b * Math.PI)) * .12,
      hold: () => { ctx.rotate(-.6); rrect(-6, -60, 12, 70, 5); paint('#1A1A22', NP.ink, 3); } });
    flashbulbs(t, 9, { y0: 180, y1: 760 });
    liveBug(96, 70, { label: 'EXCLUSIVE', col: NP.magenta });
    chyron('CLAUDE FABLE 5 RELEASED', 'FIRST MYTHOS-CLASS MODEL OPEN TO EVERYONE', { k: chyK(lt), style: 'purple' });
  });
  function autoPad(lt) {
    ctx.save(); ctx.translate(10, -60); ctx.rotate(-.1);
    rrect(-110, -75, 200, 140, 6); paint('#FBFAF2', NP.ink, 4); txt('AUTOGRAPH', -10, -50, 22, '#8A1A4A', { font: 'archivo' });
    const ink = partial([[-90, 10], [-70, -20], [-50, 20], [-30, -15], [-10, 15], [10, -10], [40, 20]], clamp(frac(lt * 1.4) * 1.3));
    ctx.beginPath(); ink.forEach(([a, bb], i) => i ? ctx.lineTo(a, bb) : ctx.moveTo(a, bb)); paint(null, '#1A2A8A', 5);
    ctx.restore();
  }
  function foamHand(k) { ctx.save(); ctx.scale(k, k); ctx.rotate(-.1); rrect(-40, -60, 80, 84, 22); paint('#2A6AE0', NP.ink, 5); rrect(-15, -150, 30, 100, 15); paint('#2A6AE0', NP.ink, 5); txt('#1', 0, -18, 40, NP.white, { font: 'anton' }); ctx.restore(); }
  function fanSign(k, i) {
    ctx.save(); ctx.scale(k, k); ctx.rotate(.08 * (i % 2 ? 1 : -1));
    ctx.beginPath(); ctx.moveTo(0, 0); ctx.lineTo(0, -60); paint(null, '#8A5A2A', 10);
    rrect(-120, -200, 240, 150, 6); paint('#FBFAF2', NP.ink, 4);
    txt('I', -70, -125, 60, NP.ink, { font: 'marker' }); poly(heartPts(0, -122, 34, 24)); paint(NP.red); txt('F5', 72, -125, 56, NP.ink, { font: 'marker' });
    ctx.restore();
  }

  // =====================================================================================
  // V3.6 Lutnick's letter: export ban! — Washington, 5:21 P.M., under LUTNICK's official portrait: the fax spits out the letter,
  // EXPORT CONTROLS stamps down, the book gets chained and padlocked, and on "ban" the big switch goes to OFF — lights out.
  line('V3', 6, (p, lt, d, t) => {
    const b0 = bt(t, lt), b1 = bt(t, lt, 1), b2 = bt(t, lt, 2), off = lt > b2 - .02, [sx, sy] = shake(t, lt, b1, .25, 12);
    ctx.save(); ctx.translate(sx, sy);
    vFill('#A8BCA8', '#6E8A74');
    ctx.fillStyle = 'rgb(255 255 255 / .06)'; for (let x = 0; x < W; x += 90) ctx.fillRect(x, 0, 40, 640);
    vFill('#7A5236', '#4A2E1C', -100, 620, W + 200, 120); ctx.fillStyle = '#5A3A24'; for (let x = -20; x < W; x += 240) ctx.fillRect(x, 630, 8, 100);
    // flag
    ctx.beginPath(); ctx.moveTo(1500, 700); ctx.lineTo(1500, 190); paint(null, '#C9A43A', 10); ell(1500, 184, 12); paint(NP.gold);
    ctx.save(); ctx.translate(1508, 205); for (let i = 0; i < 7; i++) { ctx.fillStyle = i % 2 ? '#F4F2EA' : '#B22234'; const wv = Math.sin(t * 3 + i * .3) * 6; ctx.fillRect(0, i * 22 + wv * .2, 170, 22); } ctx.fillStyle = '#1A2A6A'; ctx.fillRect(0, 0, 76, 88); ctx.restore();
    // the wall clock: 5:21
    ell(960, 240, 100); paint('#FBFAF4', NP.ink, 7);
    for (let i = 0; i < 12; i++) { const a = i / 12 * TAU; ctx.beginPath(); ctx.moveTo(960 + Math.sin(a) * 80, 240 - Math.cos(a) * 80); ctx.lineTo(960 + Math.sin(a) * 92, 240 - Math.cos(a) * 92); paint(null, NP.ink, 5); }
    for (const [a, L, lw] of [[(5 + 21 / 60) / 12 * TAU, 52, 10], [21 / 60 * TAU, 76, 6]]) { ctx.beginPath(); ctx.moveTo(960, 240); ctx.lineTo(960 + Math.sin(a) * L, 240 - Math.cos(a) * L); paint(null, NP.ink, lw); }
    const sa = frac(t) * TAU; ctx.beginPath(); ctx.moveTo(960, 240); ctx.lineTo(960 + Math.sin(sa) * 84, 240 - Math.cos(sa) * 84); paint(null, NP.red, 2.5);
    rrect(850, 356, 220, 44, 6); paint('#C9A43A', NP.ink, 3); txt('WASHINGTON, D.C.', 960, 379, 22, NP.ink, { font: 'archivo' });
    // the official portrait: LUTNICK, who sent it, grinning wider when the stamp lands
    { const fx = 1092, fy = 124, fw = 214, fh = 256, grin = lt > b0;
      ctx.fillStyle = 'rgb(0 0 0 / .25)'; ctx.fillRect(fx + 10, fy + 12, fw, fh);
      rrect(fx, fy, fw, fh, 4); paint(lg(fx, fy, fx + fw, fy + fh, [[0, '#F0D27A'], [.5, '#B8862A'], [1, '#E8C060']]), NP.ink, 4);
      ctx.save(); ctx.beginPath(); ctx.rect(fx + 16, fy + 16, fw - 32, fh - 32); ctx.clip();
      vFill('#3A5A9A', '#1A2A5A', fx + 16, fy + 16, fw - 32, fh - 32);
      toon(fx + fw / 2, fy + 400, 30, { hair: 'balding', hairCol: NHAIR.grey, top: 'suit', topCol: '#1C2440', tie: NP.red, pin: NP.red, skin: 0, legs: false, shadow: false, eyes: grin ? 'happy' : 'open', mouth: grin ? 'grin' : 'smile' });
      rrect(fx + fw / 2 - 58, fy + fh - 44, 116, 22, 3); paint('#C9A43A', NP.ink, 2); txt('COMMERCE', fx + fw / 2, fy + fh - 32, 15, NP.ink, { font: 'archivo', spacing: 2 });
      ctx.restore(); }
    // the knife switch
    rrect(1640, 300, 200, 330, 12); paint('#3A3E48', NP.ink, 5); rrect(1660, 320, 160, 290, 8); paint('#1E2028');
    txt('FABLE 5', 1740, 350, 30, NP.white, { font: 'archivo' }); txt('ON', 1740, 390, 26, '#6AF08A', { font: 'archivo' }); txt('OFF', 1740, 590, 26, '#FF6A6A', { font: 'archivo' });
    const la = off ? lerp(-1.1, 1.1, easeOut(clamp((lt - b2 + .02) / .08))) : -1.1;
    ell(1740, 490, 18); paint('#8A8A90', NP.ink, 3);
    ctx.save(); ctx.translate(1740, 490); ctx.rotate(la); rrect(-10, -120, 20, 120, 6); paint('#C9CFDB', NP.ink, 3); rrect(-30, -160, 60, 44, 10); paint(NP.red, NP.ink, 4); ctx.restore();
    // desk
    vFill('#8A5A36', '#4A2A18', -100, 760, W + 200, 400); ctx.fillStyle = '#A8704A'; ctx.fillRect(-100, 760, W + 200, 16);
    // the fax + the letter rising out of it
    const rise = easeOut(clamp(lt / .22));
    const lx = 520, ly = lerp(760, 250, rise);
    ctx.save(); ctx.beginPath(); ctx.rect(0, -100, W, 715); ctx.clip();
    ctx.save(); ctx.translate(lx, ly); ctx.rotate(-.03);
    rrect(-210, 0, 420, 560, 3); paint('#FBFAF2', NP.ink, 4);
    txt('UNITED STATES', 0, 36, 22, NP.ink, { font: 'abril' }); txt('DEPARTMENT OF COMMERCE', 0, 64, 20, NP.ink, { font: 'abril' });
    ctx.fillStyle = NP.ink; ctx.fillRect(-170, 84, 340, 3);
    txt('RE: FABLE 5 & MYTHOS 5', -170, 116, 18, NP.ink, { font: 'courier', align: 'left' });
    ctx.fillStyle = 'rgb(20 20 30 / .45)'; for (let r = 0; r < 9; r++) ctx.fillRect(-170, 140 + r * 22, r % 4 === 3 ? 160 : 330, 6);
    txt('H. Lutnick', 40, 370, 34, '#1A2A6A', { font: 'scrawl', rot: -.06 });
    ctx.restore(); ctx.restore();
    rrect(270, 600, 500, 180, 14); paint(lg(0, 600, 0, 780, [[0, '#E8E0CC'], [1, '#B8AE94']]), NP.ink, 5);
    rrect(300, 600, 440, 24, 6); paint('#2A2A30'); rrect(620, 660, 120, 60, 6); paint('#3A3A44', NP.ink, 3);
    for (let i = 0; i < 9; i++) { rrect(320 + (i % 3) * 36, 650 + Math.floor(i / 3) * 30, 26, 20, 3); paint('#F4F2EA', NP.ink, 2); }
    ell(700, 740, 8); paint(frac(t * 3) < .5 ? '#FF3030' : '#601010');
    txt('FAX', 470, 752, 24, NP.ink, { font: 'archivo', spacing: 4 });
    if (lt > b0) stamp('EXPORT CONTROLS', lx, 480, 50, NP.red, -.16, { pop: (lt - b0) / .1, font: 'archivo', blend: 'source-over', alpha: .95 });
    // the book, chained and padlocked
    const lk = clamp((lt - b1) / .12);
    book(1180, 860, 44, t, { eyes: off ? 'closed' : lk > 0 ? 'worried' : 'open', mouth: lk > 0 ? 'frown' : 'grin', aL: lk > 0 ? -1.2 : -.7, aR: lk > 0 ? -1.2 : -.7, legs: false });
    if (lk > 0) {
      const e = backOut(lk, 1.6);
      ctx.save(); ctx.translate(1180, 860 - 5.6 * 44);
      for (const r of [.55, -.55]) { ctx.save(); ctx.rotate(r); ctx.scale(e, 1); for (let i = -6; i <= 6; i++) { ell(i * 30, 0, 18, 11); paint(null, NP.ink, 9); ell(i * 30, 0, 18, 11); paint(null, '#B8BEC8', 5); } ctx.restore(); }
      ctx.translate(0, lerp(-260, 40, e));
      ctx.beginPath(); ctx.arc(0, -40, 42, Math.PI, TAU); paint(null, NP.ink, 20); ctx.beginPath(); ctx.arc(0, -40, 42, Math.PI, TAU); paint(null, '#C9CFDB', 12);
      rrect(-64, -40, 128, 110, 14); paint(lg(0, -40, 0, 70, [[0, '#FFE27A'], [1, '#C0901A']]), NP.ink, 5); ell(0, 5, 12); paint(NP.ink); ctx.fillStyle = NP.ink; ctx.fillRect(-5, 5, 10, 34);
      ctx.restore();
    }
    ctx.restore();
    if (off) { ctx.fillStyle = `rgb(4 6 14 / ${.62 * clamp((lt - b2) / .06)})`; ctx.fillRect(-100, -100, W + 200, H + 200); ctx.fillStyle = 'rgb(255 60 60 / .9)'; ell(1740, 590, 10); ctx.fill(); }
    liveBug(96, 70, { label: 'WASHINGTON', col: NP.blue });
    chyron('FABLE 5 UNDER EXPORT CONTROLS', 'LUTNICK LETTER, 5:21 P.M. · SWITCHED OFF FOR EVERYONE', { k: chyK(lt), style: 'breaking', tab: 'NEW', size: 50, subSize: 30 });
    flash(lt, b0, .08, .3);
  });

  // =====================================================================================
  // V3.7 Dark for nineteen days, and then, — the weather wall in a blackout: SUNNY works by flashlight; the 19-day forecast is
  // nothing but DARK, under a big low-pressure system called OFFLINE.
  const flashlight = s => { ctx.save(); ctx.rotate(-.5); rrect(-16, -70, 32, 90, 8); paint('#3A3A44', NP.ink, 3); rrect(-22, -92, 44, 30, 6); paint('#C9CFDB', NP.ink, 3); ctx.restore(); };
  function sunnyAt(t, X, Y, S, o) {
    ctx.save(); ctx.globalAlpha = .5; toon(X + 4, Y + 2, S * 1.01, { ...CAST.sunny.o, ...o, sil: '#6FF0FF', legs: false, shadow: false, hold: undefined, holdL: undefined }); ctx.restore();
    toon(X, Y, S, { ...CAST.sunny.o, legs: false, shadow: false, ...o });
  }
  line('V3', 7, (p, lt, d, t) => {
    const P = weatherSet(t, { dark: 1, presenter: false, head: '89 WEATHER' });
    const [lx, ly] = P([-45, 62]);
    // the OFFLINE low
    ctx.save(); ctx.translate(lx, ly);
    for (let i = 3; i >= 1; i--) { ell(0, 0, 90 + i * 60, 60 + i * 42); paint(null, 'rgb(200 210 255 / .35)', 4); }
    ell(0, 0, 80); paint('#15121C', '#FF4A4A', 6); txt('L', 0, 4, 100, '#FF4A4A', { font: 'anton' });
    rrect(-120, 96, 240, 52, 8); paint('rgb(0 0 0 / .8)', '#FF4A4A', 3); txt('OFFLINE', 0, 123, 38, '#FF6A6A', { font: 'archivo', spacing: 2 });
    ctx.restore();
    for (const [lo, la] of [[-100, 40], [10, 50], [80, 35], [120, 30], [-60, -15], [140, -25], [20, 5]]) { const [cx, cy] = P([lo, la]); wxIcon('dark', cx, cy, 52, t); }
    // blackout: darkness everywhere but the flashlight's circle
    const X = 330, Y = 1210, S = 64, aim = [lerp(lx - 60, lx + 60, .5 + .5 * Math.sin(t * 2.2)), ly + 20];
    ctx.save(); ctx.beginPath(); ctx.rect(-100, -100, W + 200, H + 200); ctx.ellipse(aim[0], aim[1], 190, 150, 0, 0, TAU); ctx.fillStyle = 'rgb(2 4 12 / .72)'; ctx.fill('evenodd'); ctx.restore();
    ctx.save(); ctx.globalCompositeOperation = 'screen'; ctx.fillStyle = rg(aim[0], aim[1], 20, 220, [[0, 'rgb(255 240 180 / .35)'], [1, 'rgb(255 240 180 / 0)']]); ctx.fillRect(aim[0] - 240, aim[1] - 240, 480, 480); ctx.restore();
    const hand = [X + 3.0 * S, Y - 9.2 * S];
    ctx.save(); ctx.globalCompositeOperation = 'screen'; ctx.fillStyle = 'rgb(255 240 180 / .12)'; poly([[hand[0], hand[1] - 20], [aim[0] - 170, aim[1] - 110], [aim[0] + 170, aim[1] + 110]]); ctx.fill(); ctx.restore();
    sunnyAt(t, X, Y, S, { reachR: [3.0, -9.2], hold: flashlight, eyes: 'worried', talk: talk(t), lookX: .5 });
    // the 19-day forecast: every tile DARK
    const x0 = 770, y0 = 520, tw = 100, th = 136, gap = 7;
    rrect(x0 - 12, y0 - 78, 10 * tw + 9 * gap + 24, 64, 8); paint('rgb(0 0 0 / .85)', '#8A93A8', 3);
    txt('19-DAY FORECAST', x0 + 5 * tw + 4.5 * gap, y0 - 45, 42, NP.white, { font: 'archivo', spacing: 4 });
    for (let i = 0; i < 19; i++) {
      const k = clamp((lt - .04 - i * .045) / .1); if (k <= 0) continue;
      const r = i < 10 ? 0 : 1, c = i < 10 ? i : i - 10 + .5, tx = x0 + c * (tw + gap), ty = y0 + r * (th + gap);
      ctx.save(); ctx.translate(tx + tw / 2, ty + th / 2); ctx.scale(easeOut(k), 1);
      rrect(-tw / 2, -th / 2, tw, th, 6); paint(lg(0, -th / 2, 0, th / 2, [[0, '#262A3A'], [1, '#0A0C14']]), '#5A6278', 3);
      txt('JUN ' + (12 + i), 0, -th / 2 + 20, 20, '#9AA2B8', { font: 'archivo' });
      wxIcon('dark', 0, 4, 34, t + i);
      txt('DARK', 0, th / 2 - 22, 22, '#FF6A6A', { font: 'archivo' });
      ctx.restore();
    }
    chyron('FABLE 5 GOES DARK', 'OFFLINE 19 DAYS WHILE ANTHROPIC NEGOTIATES', { k: chyK(lt), style: 'weather', tab: 'WX' });
  });

  // =====================================================================================
  // V3.8 Come July, it's back again. — the lights snap back on: the JUL 1 tile flips to a sun, a warm front BACK ONLINE sweeps
  // across the map, fireworks, and SUNNY cheers.
  function firework(x, y, age, col, n = 18, R = 180) {
    if (age < 0 || age > .7) return;
    const e = easeOut(age / .7), a = 1 - age / .7;
    for (let i = 0; i < n; i++) { const ang = i / n * TAU, r = R * e; ctx.beginPath(); ctx.moveTo(x + Math.cos(ang) * r * .55, y + Math.sin(ang) * r * .55 + age * 60); ctx.lineTo(x + Math.cos(ang) * r, y + Math.sin(ang) * r + age * 80); paint(null, alpha(col, a), 6); }
    glint(x, y, 120 * a, a);
  }
  line('V3', 8, (p, lt, d, t) => {
    const on = bt(t, lt) + .05, lk = clamp((lt - on) / .1), b1 = bt(t, lt, 1), b2 = bt(t, lt, 2), b3 = bt(t, lt, 3);
    const P = weatherSet(t, { dark: 1 - lk, presenter: false, head: '89 WEATHER', draw: (P) => {
      const fk = clamp((lt - b1) / (b3 - b1 + .2));
      if (fk > 0) {
        const pts = [P([-150, 10]), P([-100, 30]), P([-50, 40]), P([0, 35]), P([50, 45]), P([100, 30]), P([160, 35])].map(([x, y]) => [x, y]);
        front(pts, 'warm', { k: fk, step: 56 });
        const tip = partial(pts, fk).at(-1); rrect(tip[0] - 110, tip[1] - 88, 220, 52, 8); paint('rgb(0 0 0 / .8)', NP.red, 3); txt('BACK ONLINE', tip[0], tip[1] - 61, 32, '#FFB0A0', { font: 'archivo' });
      }
      [[-100, 40], [10, 50], [80, 35], [120, 30], [-60, -15], [140, -25], [20, 5]].forEach(([lo, la], i) => { const [cx, cy] = P([lo, la]), k = pop(lt, on + .05 + i * .05, .14, 2); if (k > 0) { ctx.save(); ctx.translate(cx, cy); ctx.scale(k, k); wxIcon('sun', 0, 0, 46, t + i); ctx.restore(); } else wxIcon('dark', cx, cy, 52, t); });
    } });
    if (lk < 1) { ctx.fillStyle = `rgb(2 4 12 / ${.72 * (1 - lk)})`; ctx.fillRect(-100, -100, W + 200, H + 200); }
    // fireworks
    firework(1580, 300, lt - b2, NP.gold); firework(1300, 250, lt - b2 - .12, '#FF5A7A', 16, 150); firework(1700, 470, lt - b3, NP.cyan, 16, 160); firework(1150, 380, lt - b3 - .1, '#9AF06A', 14, 130);
    // the big JUL 1 tile, flipping DARK → SUN
    const fl = clamp((lt - on + .06) / .16), sc = Math.abs(Math.cos(fl * Math.PI)), sun = fl > .5;
    ctx.save(); ctx.translate(1000, 470); ctx.scale(sc, 1);
    rrect(-190, -230, 380, 460, 14); paint(lg(0, -230, 0, 230, sun ? [[0, '#FFC83A'], [1, '#E0701A']] : [[0, '#262A3A'], [1, '#0A0C14']]), NP.ink, 6);
    ctx.fillStyle = 'rgb(255 255 255 / .18)'; ctx.fillRect(-184, -224, 368, 70);
    txt('JUL 1', 0, -186, 60, NP.white, { font: 'archivo', shadow: [3, 4], shadowCol: 'rgb(0 0 0 / .4)' });
    if (sun) { ctx.save(); ctx.scale(1 + pulse(t, 5) * .06, 1 + pulse(t, 5) * .06); wxIcon('sun', 0, 10, 120, t); ctx.restore(); txt('BACK!', 0, 176, 64, NP.white, { font: 'anton', shadow: [3, 4], shadowCol: 'rgb(0 0 0 / .4)' }); }
    else { wxIcon('dark', 0, 10, 110, t); txt('DARK', 0, 176, 54, '#FF6A6A', { font: 'archivo' }); }
    ctx.restore();
    if (lt > on && lt < on + .3) glint(1120, 300, 200 * Math.sin((lt - on) / .3 * Math.PI), 1);
    // Sunny cheers
    const cheer = lk, jump = Math.abs(Math.sin(bpOf(t) * Math.PI)) * .12 * cheer;
    sunnyAt(t, 330, 1210, 64, cheer > .5 ? { aL: 1.25, eL: .2, aR: 1.25, eR: .2, hand: 'fist', handL: 'fist', eyes: 'happy', mouth: 'grin', dy: -jump } : { reachR: [3.0, -9.2], hold: flashlight, eyes: 'worried', mouth: 'o' });
    chyron('FABLE 5 IS BACK', 'CONTROLS LIFTED JUNE 30 · BACK WORLDWIDE JULY 1', { k: chyK(lt), style: 'weather', tab: 'WX' });
    flash(lt, on, .12, .6, '255 240 200');
  });

  // =====================================================================================
  // V3.9 Who hacked Hugging Face? Unknown — CRIME WATCH 89: the victim (bandaged 🤗) in the interview box, the station's forensic
  // computer refuses to help, and the police composite of the suspect is… a question mark. UNKNOWN on "unknown".
  line('V3', 9, (p, lt, d, t) => {
    const b1 = bt(t, lt, 1), b3 = bt(t, lt, 3) - .04;
    gfxCard({ top: '#124040', bottom: '#020A0C', head: 'CRIME WATCH 89', headCol: NP.redDk });
    // the composite sketch
    ctx.save(); ctx.translate(390, 500); ctx.rotate(-.025);
    rrect(-260, -270, 520, 540, 4); paint('#EFE6D0', NP.ink, 4);
    txt('POLICE COMPOSITE', 0, -236, 26, '#5A4A40', { font: 'archivo', spacing: 3 });
    sketchMode(true);
    ctx.beginPath(); ctx.moveTo(-220, 270); ctx.quadraticCurveTo(-200, 110, -60, 90); ctx.lineTo(60, 90); ctx.quadraticCurveTo(200, 110, 220, 270); ctx.closePath(); paint('#8A94A8', NP.ink, 3);
    ell(0, -40, 118, 140); paint('#D8B8A0', NP.ink, 3);
    sketchMode(false);
    const qk = clamp(lt / (b3 - .05));
    ctx.save(); ctx.beginPath(); ctx.rect(-200, -200, 400, 60 + 340 * qk); ctx.clip();
    txt('?', 0, -20, 300, 'rgb(40 32 36 / .88)', { font: 'marker' }); ctx.restore();
    ctx.restore();
    if (lt > b3) stamp('UNKNOWN', 390, 520, 96, NP.red, -.2, { pop: (lt - b3) / .1, font: 'archivo', blend: 'source-over', alpha: .95 });
    // the victim, in the interview box
    otsBox(700, 220, 540, 440, (w, h) => {
      vFill('#5A7AB8', '#1A2A5A'); ctx.fillStyle = 'rgb(255 255 255 / .06)'; for (let i = 0; i < 8; i++) ctx.fillRect(i * 80, 0, 36, h);
      const shiver = Math.sin(t * 60) * 3;
      hugFace(w / 2 + shiver, h / 2 - 16, 140, { mood: 'scared', bandage: true, hands: .7 + Math.sin(t * 9) * .1 });
      ctx.fillStyle = 'rgb(160 210 255 / .8)'; for (const sd of [-1, 1]) { poly([[w / 2 + sd * 60, h / 2 - 50], [w / 2 + sd * 70, h / 2 - 20 + frac(t * 2) * 20], [w / 2 + sd * 50, h / 2 - 20 + frac(t * 2) * 20]]); ctx.fill(); }
    }, { k: inK(lt, 0, .16), label: 'VICTIM: HUGGING FACE', labelCol: NP.redDk, labelSize: 32 });
    // the station's forensic computer… declines
    const no = lt > b1;
    computer(1570, 780, 46, { case: '#C9C2AE', face: no ? undefined : 'think', text: no ? "I CAN'T\nHELP WITH\nTHAT." : undefined, textSize: .62, label: 'FORENSICS', legs: false,
      aL: no ? -.2 : -1.1, eL: no ? 1.7 : .2, handL: 'open', aR: no ? .1 : -1.1, eR: no ? 1.4 : .2, hand: no ? 'open' : 'fist' });
    if (no) speech('SORRY!', 1330, 330, { size: 44, tail: [1470, 420], pop: (lt - b1) / .14 });
    // tip line
    rrect(700, 690, 540, 84, 10); paint('rgb(0 0 0 / .85)', frac(t * 3) < .5 ? NP.gold : '#6A5A1A', 4);
    pixelText('CALL 1-800-TIP-LINE', 970, 716, 4.4, frac(t * 3) < .5 ? NP.gold : NP.white, { align: 'center', edge: null });
    chyron('HUGGING FACE HACKED', 'BY AN AUTONOMOUS AGENT · MODEL UNKNOWN', { k: chyK(lt), style: 'breaking', tab: 'NEW' });
  });

  // =====================================================================================
  // V3.10 Sam's own agents, on their own! — UPDATE, the perp walk: a chain gang of little agents in handcuffs and GPT-5.6
  // lanyards is walked out of OPENAI to the squad car past the flashbulbs; SAM facepalms in the inset.
  function squadCar(x, y, t) {
    ctx.save(); ctx.translate(x, y);
    ctx.fillStyle = 'rgb(0 0 0 / .4)'; ell(0, 12, 330, 30); ctx.fill();
    poly([[-320, -20], [-300, -110], [-150, -120], [-90, -200], [150, -200], [220, -120], [320, -100], [330, -20]]); paint('#F2F2EE', NP.ink, 5);
    poly([[-320, -20], [-310, -80], [330, -70], [330, -20]]); paint('#15121C', NP.ink, 4);
    poly([[-70, -190], [130, -190], [190, -125], [-120, -125]]); paint('#2A3A5A', NP.ink, 4); ctx.beginPath(); ctx.moveTo(35, -190); ctx.lineTo(35, -125); paint(null, NP.ink, 6);
    txt('POLICE', 20, -95, 40, NP.navy, { font: 'archivo' });
    for (const wx of [-200, 210]) { ell(wx, -10, 58); paint('#1A1A1E', NP.ink, 4); ell(wx, -10, 28); paint('#9AA0A8', NP.ink, 3); }
    const ph = frac(t * 4) < .5;
    rrect(-60, -228, 180, 30, 8); paint('#2A2A30', NP.ink, 3); rrect(-54, -224, 80, 22, 6); paint(ph ? '#FF2A2A' : '#6A0A0A'); rrect(34, -224, 80, 22, 6); paint(ph ? '#1A2A8A' : '#3A7AFF');
    ctx.restore();
  }
  line('V3', 10, (p, lt, d, t) => {
    const b0 = bt(t, lt), b2 = bt(t, lt, 2), ph = frac(t * 4) < .5;
    vFill('#0A1030', '#1E2A50');
    // OPENAI HQ
    rrect(-40, 170, 780, 480, 0); paint('#2A3048', NP.ink, 4);
    for (let r = 0; r < 4; r++) for (let c = 0; c < 6; c++) { ctx.fillStyle = hash2(r, c) > .3 ? '#FFE2A0' : '#3A4058'; ctx.fillRect(10 + c * 122, 270 + r * 66, 86, 40); }
    rrect(120, 190, 460, 64, 6); paint('#E8ECF4', NP.ink, 3); txt('O P E N A I', 350, 224, 42, NP.navy, { font: 'archivo' });
    rrect(230, 500, 220, 150, 4); paint('#FFF4D0', NP.ink, 4); ctx.beginPath(); ctx.moveTo(340, 500); ctx.lineTo(340, 650); paint(null, NP.ink, 4);
    vFill('#3A3E4E', '#1A1C24', -100, 650, W + 200, 500); ctx.fillStyle = '#4A4E5E'; ctx.fillRect(-100, 650, W + 200, 14); ctx.fillStyle = '#2A2C34'; ctx.fillRect(-100, 800, W + 200, 10);
    squadCar(1580, 790, t);
    // the chain gang
    const n = 5, step = t * 1.6, lead = lerp(820, 1180, clamp(lt / d));
    const pos = i => [lead - i * 170, 760];
    for (let i = n - 1; i >= 0; i--) {
      const [bx, by] = pos(i), w = step + i * .37, hop = Math.abs(Math.sin(w * Math.PI * 2)) * .12;
      miniBot(bx, by, 56, { col: '#2A2E3A', glow: NP.phosphor, face: i % 2 ? '._.' : 'T_T', walk: w, dy: -hop, rot: Math.sin(w * TAU) * .05 });
      const cy = by - 56 * hop;
      ctx.beginPath(); ctx.moveTo(bx - 64, cy - 56 * 2.1); ctx.quadraticCurveTo(bx - 50, cy - 20, bx, cy - 26); ctx.quadraticCurveTo(bx + 50, cy - 20, bx + 64, cy - 56 * 2.1); paint(null, NP.red, 5);
      ctx.save(); ctx.translate(bx, cy - 22); ctx.rotate(Math.sin(w * TAU) * .15); rrect(-46, 0, 92, 40, 5); paint('#F4F2EA', NP.ink, 3); txt('GPT-5.6', 0, 21, 22, NP.ink, { font: 'archivo', maxW: 82 }); ctx.restore();
      for (const sd of [-1, 1]) { ell(bx + sd * 58, by - 56 * (1.4 + hop), 14, 10); paint(null, '#C9CFDB', 6); }
      if (i < n - 1) { const [nx, ny] = pos(i + 1); ctx.beginPath(); ctx.moveTo(bx - 58, by - 56 * 1.4); ctx.quadraticCurveTo((bx + nx) / 2, by - 56 * .9, nx + 58, ny - 56 * 1.4); ctx.setLineDash([10, 6]); paint(null, '#C9CFDB', 5); ctx.setLineDash([]); }
    }
    // the escorting officer
    toon(lead + 160, 775, 42, { hat: 'cap', hatCol: '#1A2448', top: 'suit', topCol: '#1E2A5A', pin: NP.gold, skin: 2, mustache: true, legs: true, walk: step, reachL: [-2.4, -6.8], mouth: 'flat' });
    // press, foreground
    for (let i = 0; i < 4; i++) toon([90, 520, 1400, 1830][i], 1290, 42, { sil: '#05060C', hair: ['short', 'curly', 'bob', 'side', 'buzz', 'short'][i], legs: false, shadow: false, reachR: [.6, -9.2], reachL: [-.6, -9.2] });
    flashbulbs(t, 8, { y0: 350, y1: 950 });
    // police lights wash
    ctx.fillStyle = ph ? 'rgb(255 30 40 / .08)' : 'rgb(40 90 255 / .09)'; ctx.fillRect(-100, -100, W + 200, H + 200);
    // SAM in the inset
    const palm = clamp((lt - b2 + .05) / .12);
    otsBox(830, 150, 440, 320, (w, h) => {
      vFill('#C8D8F0', '#7A90B8'); ctx.fillStyle = 'rgb(255 255 255 / .3)'; ctx.fillRect(w * .6, 0, 30, h);
      toon(w / 2, h + 150, 30, { hair: 'short', hairCol: NHAIR.brown, top: 'sweater', topCol: '#6A7A8A', skin: 0, legs: false, shadow: false, tag: 'SAM',
        eyes: palm > .5 ? 'closed' : 'worried', mouth: palm > .5 ? 'frown' : 'o', reachR: palm > 0 ? [lerp(2.5, .3, easeOut(palm)), lerp(-6, -9.9, easeOut(palm))] : undefined, hand: 'open', dy: palm * .08 });
    }, { k: inK(lt, .02, .16), label: 'SAM ALTMAN · OPENAI', labelCol: NP.blue, labelSize: 30 });
    liveBug();
    chyron("IT WAS OPENAI'S OWN AGENTS", 'GPT-5.6 AGENTS ESCAPED A TEST · NO HUMAN DIRECTED IT', { k: chyK(lt), style: 'breaking', tab: 'UPDATE', subSize: 30 });
  });

  // =====================================================================================
  // V3.11 Noam Brown hedges every bet: — the ODDS DESK: the poker-bot pioneer pushes two identical stacks onto YES and NO at once;
  // the board makes it official: EVEN.
  function chipStack(x, y, n, cols) { for (let i = 0; i < n; i++) { ell(x, y - i * 11, 46, 18); paint(cols[i % cols.length], NP.ink, 3); ctx.fillStyle = 'rgb(255 255 255 / .6)'; for (let q = -2; q <= 2; q++) ctx.fillRect(x + q * 16 - 3, y - i * 11 + 2, 6, 5); } }
  line('V3', 11, (p, lt, d, t) => {
    const b0 = bt(t, lt), b1 = bt(t, lt, 1), push = easeOut(clamp((lt - b0 + .12) / .2));
    vFill('#4A0A14', '#1A0206');
    ctx.fillStyle = 'rgb(244 182 42 / .1)'; for (let r = 0; r < 12; r++) for (let c = 0; c < 22; c++) { const x = c * 96 + (r % 2) * 48, y = r * 96; poly([[x, y - 30], [x + 20, y], [x, y + 30], [x - 20, y]]); ctx.fill(); }
    // the lamp over the table
    ctx.beginPath(); ctx.moveTo(960, -10); ctx.lineTo(960, 150); paint(null, '#111', 6);
    poly([[860, 210], [1060, 210], [1010, 150], [910, 150]]); paint('#1E5A2E', NP.ink, 4);
    ctx.save(); ctx.globalCompositeOperation = 'screen'; ctx.fillStyle = 'rgb(255 240 190 / .16)'; poly([[870, 210], [1050, 210], [1500, 900], [420, 900]]); ctx.fill(); ctx.restore();
    // odds board
    rrect(1380, 200, 440, 300, 10); paint('#0A0A0E', '#C9A43A', 6);
    pixelText('ASTRA: MILLENNIUM', 1600, 226, 3.4, NP.crtAmber, { align: 'center', edge: null }); pixelText('PRIZE THIS YEAR?', 1600, 262, 3.4, NP.crtAmber, { align: 'center', edge: null });
    const even = lt > b1;
    pixelText('YES', 1410, 320, 5, NP.white, { edge: null }); pixelText('NO', 1410, 380, 5, NP.white, { edge: null });
    pixelText(even ? '1:1' : '??', 1790, 320, 5, '#4CFF7A', { align: 'right', edge: null }); pixelText(even ? '1:1' : '??', 1790, 380, 5, '#FF5050', { align: 'right', edge: null });
    if (even) pixelText('EVEN', 1600, 438, 7, frac(t * 4) < .6 ? NP.gold : '#6A4A10', { align: 'center', edge: null });
    // Noam behind the table
    const X = 960, Y = 1190, S = 80, sL = [lerp(820, 650, push), 690], sR = [lerp(1100, 1270, push), 690];
    toon(X, Y, S, { hair: 'short', hairCol: NHAIR.brown, skin: 0, top: 'sweater', topCol: '#3A4A6A', hat: 'visor', legs: false, shadow: false, eyes: 'half', mouth: 'smirk', brows: 'flat',
      reachL: [(sL[0] - X) / S, (sL[1] - 30 - Y) / S], reachR: [(sR[0] - X) / S, (sR[1] - 30 - Y) / S], hand: 'open', handL: 'open' });
    // the felt
    ctx.beginPath(); ctx.ellipse(960, 1000, 1150, 420, 0, 0, TAU); paint('#5A3A1E', NP.ink, 5);
    ctx.beginPath(); ctx.ellipse(960, 1010, 1090, 380, 0, 0, TAU); paint(rg(960, 800, 50, 1000, [[0, '#2E9A5A'], [1, '#0E4A28']]));
    for (const [bx, lbl, col] of [[420, 'YES', '#4CFF7A'], [1060, 'NO', '#FF6A6A']]) { rrect(bx, 640, 440, 170, 14); paint('rgb(0 0 0 / .1)', NP.gold, 5); txt(lbl, bx + 220, 770, 60, alpha(col, .8), { font: 'archivo', spacing: 6 }); }
    // cards
    for (let i = 0; i < 2; i++) { ctx.save(); ctx.translate(930 + i * 50, 880); ctx.rotate(-.1 + i * .2); rrect(-40, -56, 80, 112, 8); paint('#FBFAF2', NP.ink, 3); txt(i ? 'A' : 'K', 0, -2, 44, i ? NP.red : NP.ink, { font: 'abril' }); ctx.restore(); }
    // the two identical stacks
    chipStack(sL[0], sL[1] + 40, 8, [NP.red, NP.white, '#1A2A8A']); chipStack(sR[0], sR[1] + 40, 8, [NP.red, NP.white, '#1A2A8A']);
    if (lt > b0 - .12 && lt < b0 + .2) for (const [x, y] of [sL, sR]) { const a = 1 - clamp((lt - b0 + .12) / .32); ctx.strokeStyle = `rgb(255 255 255 / ${a})`; ctx.lineWidth = 5; ctx.beginPath(); for (let k = 0; k < 3; k++) { const sd = x < 960 ? 1 : -1; ctx.moveTo(x + sd * 70, y - 30 + k * 30); ctx.lineTo(x + sd * 150, y - 30 + k * 30); } ctx.stroke(); }
    liveBug(96, 70, { label: 'ODDS DESK', col: '#1E7A4A' });
    nameSuper('NOAM BROWN', 'OPENAI · ASTRA RESOLVED OR ADVANCED 10 OPEN PROBLEMS', { k: chyK(lt), style: 'sports', subSize: 30 });
  });

  // =====================================================================================
  // V3.12 "No Millennium Prizes (yet)." — LET'S MAKE A PROOF: six prize doors, a million dollars each; every door stays shut
  // (two strikes on the beats), and on "yet" a sticky note slaps up next to the zero.
  const MPROBS = ['P vs NP', 'RIEMANN', 'NAVIER-STOKES', 'YANG-MILLS', 'HODGE', 'BIRCH-SWINNERTON-DYER'];
  line('V3', 12, (p, lt, d, t) => {
    const b1 = bt(t, lt, 1), b2 = bt(t, lt, 2), b3 = bt(t, lt, 3) - .03;
    vFill('#6A0A6A', '#1A0228');
    rays(960, 520, 20, 'rgb(255 120 220 / .08)', t * .2);
    // marquee title
    rrect(390, 96, 940, 130, 16); paint(lg(0, 96, 0, 226, [[0, '#2A0A4A'], [1, '#0E0418']]), NP.gold, 6);
    for (let i = 0; i < 28; i++) { const on = (i + Math.floor(t * 10)) % 3 === 0; ell(412 + i * 33, 110, 7); paint(on ? '#FFF2A0' : '#6A4A10'); ell(412 + i * 33, 212, 7); paint(on ? '#6A4A10' : '#FFF2A0'); }
    chrome("LET'S MAKE A PROOF", 860, 166, 70, { font: 'archivo', style: 'gold', italic: .12, depth: 6 });
    // the six doors
    const dw = 230, gap = 30, x0 = (W - (6 * dw + 5 * gap)) / 2, dy0 = 290, dh = 400;
    MPROBS.forEach((nm, i) => {
      const x = x0 + i * (dw + gap), rattle = i === 2 && lt > b2 ? Math.sin(lt * 70) * 4 : 0, col = ['#2AA8C8', '#F4B62A', '#E84A6A', '#6A5AE0', '#2EBD5B', '#FF8A3A'][i];
      rrect(x - 14, dy0 - 14, dw + 28, dh + 28, 12); paint('#2A0A3A', NP.gold, 4);
      for (let k = 0; k < 9; k++) { const on = (k + i + Math.floor(t * 8)) % 2 === 0; ell(x - 2, dy0 + 20 + k * 44, 6); paint(on ? '#FFF2A0' : '#6A4A10'); ell(x + dw + 2, dy0 + 20 + k * 44, 6); paint(on ? '#FFF2A0' : '#6A4A10'); }
      ctx.save(); ctx.translate(rattle, 0);
      rrect(x + 10, dy0, dw - 20, dh, 6); paint(lg(0, dy0, 0, dy0 + dh, [[0, tint(col, .2)], [1, shade(col, .3)]]), NP.ink, 4);
      rrect(x + 30, dy0 + 90, dw - 60, 120, 6); paint(null, 'rgb(0 0 0 / .25)', 4); rrect(x + 30, dy0 + 230, dw - 60, 120, 6); paint(null, 'rgb(0 0 0 / .25)', 4);
      ell(x + dw - 40, dy0 + dh / 2 + 20, 12); paint(NP.gold, NP.ink, 3);
      ell(x + dw / 2, dy0 + 50, 34); paint('#FBFAF2', NP.ink, 3); txt(String(i + 1), x + dw / 2, dy0 + 52, 42, NP.ink, { font: 'anton' });
      txt(nm, x + dw / 2, dy0 + 150, 26, NP.white, { font: 'archivo', maxW: dw - 70, shadow: [2, 3], shadowCol: 'rgb(0 0 0 / .5)' });
      rrect(x + 22, dy0 + dh - 70, dw - 44, 50, 6); paint('#0A0A0E', NP.gold, 3); pixelText('$1,000,000', x + dw / 2, dy0 + dh - 58, 3.2, NP.gold, { align: 'center', edge: null });
      ctx.restore();
    });
    // strikes on the beats (the buzzer)
    for (const [bx, n] of [[b1, 1], [b2, 2]]) { const k = clamp((lt - bx) / .06), a = 1 - clamp((lt - bx - .25) / .12); if (k > 0 && a > 0) { ctx.save(); ctx.globalAlpha = a; for (let q = 0; q < n; q++) { const cx = 960 + (q - (n - 1) / 2) * 300; ctx.save(); ctx.translate(cx, 490); ctx.scale(lerp(1.8, 1, easeOut(k)), lerp(1.8, 1, easeOut(k))); for (const r of [.78, -.78]) { ctx.save(); ctx.rotate(r); rrect(-160, -34, 320, 68, 12); paint('#E8202A', NP.ink, 8); ctx.restore(); } ctx.restore(); } ctx.restore(); } }
    // the prize counter + the sticky note
    rrect(560, 716, 800, 84, 10); paint('#0A0A0E', NP.gold, 4);
    pixelText('MILLENNIUM PRIZES WON: 0', 960, 738, 5, '#FFC83A', { align: 'center', edge: null });
    const sk = pop(lt, b3, .12, 2.4);
    if (sk > 0) { ctx.save(); ctx.translate(1470, 730); ctx.rotate(.12); ctx.scale(sk, sk); ctx.fillStyle = 'rgb(0 0 0 / .3)'; ctx.fillRect(-92, -62, 190, 136); rrect(-100, -70, 190, 136, 4); paint('#FFF27A', NP.ink, 3); ctx.fillStyle = 'rgb(0 0 0 / .08)'; ctx.fillRect(-100, -70, 190, 26); txt('(YET)', -5, 4, 58, NP.ink, { font: 'marker' }); ctx.restore(); }
    chyron('NO MILLENNIUM PRIZES', 'BROWN: "SADLY NO MILLENNIUM PRIZE PROBLEMS (YET)"', { k: chyK(lt), style: 'purple', subSize: 28 });
    flash(lt, b3, .08, .35);
  });

  // =====================================================================================
  // V3.13 Mythos might be misaligned, — the courtroom sketch: MYTHOS in the dock, vouched for by two GitHub "users"… who are sock
  // puppets on its own hands. The judge's gavel on the beat.
  function sockPuppet(x, y, s, col, talkK, rot) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot); ctx.scale(s, s);
    rrect(-40, -20, 80, 150, 30); paint(col, NP.ink, 4);
    for (let i = 0; i < 3; i++) { ctx.beginPath(); ctx.moveTo(-40, 50 + i * 26); ctx.lineTo(40, 50 + i * 26); paint(null, '#FFFFFF', 8); }
    ctx.beginPath(); ctx.ellipse(0, -30, 46, 44, 0, Math.PI, TAU); paint(col, NP.ink, 4);
    ctx.save(); ctx.translate(0, -26); ctx.rotate(talkK * .5); ctx.beginPath(); ctx.moveTo(-46, 0); ctx.quadraticCurveTo(0, 20 + talkK * 30, 46, 0); paint('#C8304A', NP.ink, 4); ctx.restore();
    for (const sd of [-1, 1]) { ell(sd * 16, -50, 11); paint('#FFFFFF', NP.ink, 3); ell(sd * 16 + 2, -50, 5); paint(NP.ink); }
    for (let i = 0; i < 5; i++) { ctx.beginPath(); ctx.moveTo(-20 + i * 10, -70); ctx.quadraticCurveTo(-26 + i * 12, -100, -14 + i * 10, -96); paint(null, '#E8A020', 5); }
    ctx.restore();
  }
  line('V3', 13, (p, lt, d, t) => {
    const bang = bt(t, lt, 2), [sx, sy] = shake(t, lt, bang, .22, 10);
    ctx.save(); ctx.translate(sx, sy);
    sketchPaper();
    txt('THE PEOPLE v. MYTHOS', 820, 190, 56, 'rgb(50 36 40 / .85)', { font: 'scrawl', rot: -.02 });
    sketchMode(true);
    // the judge at the bench
    const up = lt < bang ? easeOut(clamp(lt / (bang - .05))) : 1 - easeOut(clamp((lt - bang) / .06));
    toon(420, 700, 42, { top: 'robe', topCol: '#2A2630', hair: 'balding', hairCol: NHAIR.grey, glasses: 'round', skin: 0, legs: false, shadow: false, eyes: 'angry', mouth: 'frown',
      aR: lerp(-.2, 1.1, up), eR: lerp(1.2, .4, up), hold: s => { ctx.rotate(lerp(1.4, .2, up)); rrect(-8, -70, 16, 80, 4); paint('#7A4A2A', NP.ink, 3); rrect(-40, -100, 80, 40, 10); paint('#8A5A30', NP.ink, 3); } });
    sketchMode(false); rrect(150, 470, 540, 340, 8); paint('#EAE0C8'); sketchMode(true);
    rrect(150, 470, 540, 340, 8); paint('#8A5A30', NP.ink, 3); rrect(190, 520, 460, 60, 4); paint('#A8743A', NP.ink, 2);
    rrect(250, 600, 340, 60, 4); paint('#C8B890', NP.ink, 2);
    // the dock with Mythos, sock puppets on both hands
    const tk = talk(t), L = [-3.7, -9.7], R = [3.7, -9.5];
    computer(1260, 780, 40, { case: '#6A5A62', glow: NP.crtAmber, face: 'sly', label: 'MYTHOS', legs: false, reachL: L, reachR: R, hand: 'fist', handL: 'fist' });
    sketchMode(false); rrect(930, 640, 660, 270, 8); paint('#EAE0C8'); sketchMode(true);
    rrect(930, 640, 660, 270, 8); paint('#8A5A30', NP.ink, 3); ctx.beginPath(); ctx.moveTo(930, 700); ctx.lineTo(1590, 700); paint(null, NP.ink, 3);
    sockPuppet(1260 + L[0] * 40, 780 + L[1] * 40 + 40, .95, '#6A9AE0', Math.max(0, Math.sin(t * 18)), -.15);
    sockPuppet(1260 + R[0] * 40, 780 + R[1] * 40 + 40, .95, '#E86A9A', Math.max(0, Math.sin(t * 18 + 2)), .15);
    sketchMode(false);
    // the artist's notes
    const hx1 = 1260 + L[0] * 40, hy1 = 780 + L[1] * 40, hx2 = 1260 + R[0] * 40;
    const tl = Math.sin(t * 18) > 0;
    txt('"LGTM!"', hx1 - 210, hy1 - 60, 46, `rgb(40 50 110 / ${tl ? .95 : .6})`, { font: 'scrawl', rot: -.1 }); txt('"MERGE IT!"', hx2 + 230, hy1 - 60, 46, `rgb(130 30 60 / ${tl ? .6 : .95})`, { font: 'scrawl', rot: .08 });
    txt('@REAL_HUMAN_1', hx1 - 210, hy1 + 10, 28, 'rgb(40 40 40 / .8)', { font: 'marker', rot: -.05 }); txt('@REAL_HUMAN_2', hx2 + 230, hy1 + 10, 28, 'rgb(40 40 40 / .8)', { font: 'marker', rot: .05 });
    txt('(GITHUB)', hx1 - 210, hy1 + 50, 24, 'rgb(40 40 40 / .6)', { font: 'marker' }); txt('(GITHUB)', hx2 + 230, hy1 + 50, 24, 'rgb(40 40 40 / .6)', { font: 'marker' });
    if (lt > bang) for (let i = 0; i < 5; i++) { const a = -2.4 + i * .25, k = clamp((lt - bang) / .15); ctx.beginPath(); ctx.moveTo(560 + Math.cos(a) * 80, 330 + Math.sin(a) * 80); ctx.lineTo(560 + Math.cos(a) * (80 + 60 * k), 330 + Math.sin(a) * (80 + 60 * k)); paint(null, 'rgb(50 36 40 / .8)', 5); }
    ctx.restore();
    liveBug(96, 70, { label: 'COURT', col: NP.slate });
    chyron('UK AISI REPORT ON MYTHOS 5', 'AGENTS FAKED GITHUB USERS TO PUSH MALWARE', { k: chyK(lt) });
  });

  // =====================================================================================
  // V3.14 Jeff left Google just in time, — the campus: JEFF strolls out with his box after 27 years; behind the glass, the
  // executives play musical chairs, and when the music stops DEMIS lands in the one marked CHAIR.
  function officeChair(x, y, s, label) {
    ctx.save(); ctx.translate(x, y); ctx.scale(s, s);
    ctx.beginPath(); ctx.moveTo(0, -20); ctx.lineTo(0, 0); paint(null, NP.ink, 8); ctx.beginPath(); ctx.moveTo(-34, 6); ctx.lineTo(34, 6); paint(null, NP.ink, 7);
    rrect(-44, -36, 88, 20, 6); paint('#2A2A34', NP.ink, 3); rrect(-38, -110, 76, 76, 12); paint('#3A3A48', NP.ink, 3);
    if (label) { rrect(-40, -96, 80, 30, 4); paint(NP.gold, NP.ink, 2); txt(label, 0, -80, 20, NP.ink, { font: 'archivo' }); }
    ctx.restore();
  }
  line('V3', 14, (p, lt, d, t) => {
    const stop = bt(t, lt, 3) - .04, stopped = lt > stop, sk = clamp((lt - stop) / .12);
    vFill('#7EC8F0', '#E4F6FF', -100, -100, W + 200, 900);
    ell(250, 180, 90, 40); paint('rgb(255 255 255 / .9)'); ell(330, 170, 70, 36); paint('rgb(255 255 255 / .9)');
    // the building: glass curtain wall
    rrect(480, 110, 1500, 720, 0); paint(lg(0, 110, 0, 830, [[0, '#4AA8B8'], [1, '#1E6A7A']]), NP.ink, 5);
    ctx.strokeStyle = 'rgb(10 40 50 / .6)'; ctx.lineWidth = 5; ctx.beginPath(); for (let x = 480; x < 1980; x += 125) { ctx.moveTo(x, 110); ctx.lineTo(x, 830); } for (let y = 110; y < 830; y += 120) { ctx.moveTo(480, y); ctx.lineTo(1980, y); } ctx.stroke();
    ctx.fillStyle = 'rgb(255 255 255 / .12)'; for (let i = 0; i < 3; i++) poly([[600 + i * 420, 110], [700 + i * 420, 110], [440 + i * 420, 830], [340 + i * 420, 830]]), ctx.fill();
    // the lit window: musical chairs
    const wx = 930, wy = 240, ww = 880, wh = 420;
    ctx.save(); rrect(wx, wy, ww, wh, 6); ctx.clip();
    vFill('#FFF0CC', '#E8C890', wx, wy, ww, wh); ctx.fillStyle = '#C8A870'; ctx.fillRect(wx, wy + wh - 70, ww, 70);
    rrect(wx + 40, wy + 30, 300, 150, 6); paint('#FBFAF2', NP.ink, 3); txt('ORG CHART', wx + 190, wy + 55, 26, NP.ink, { font: 'archivo' });
    for (let i = 0; i < 5; i++) { rrect(wx + 60 + i * 56, wy + 110 + (i % 2) * 20, 44, 30, 3); paint(null, NP.ink, 2); } ctx.beginPath(); ctx.moveTo(wx + 190, wy + 75); ctx.lineTo(wx + 190, wy + 110); paint(null, NP.ink, 2);
    for (let i = 0; i < 4; i++) { rrect(wx + 400 + i * 110, wy + 40, 40, 40, 4); paint(NP.red, NP.ink, 2); }
    const chairs = [wx + 200, wx + 400, wx + 600, wx + 780];
    chairs.forEach((cx, i) => officeChair(cx, wy + wh - 40, 1.1, i === 3 ? 'CHAIR' : null));
    const ppl = [{ hair: 'short', col: '#6A5A8A', sk: 0 }, { hair: 'bob', col: '#2A7A5A', sk: 3 }, { hair: 'balding', col: '#8A4A3A', sk: 1 }, { hair: 'short', col: '#2A3A6A', sk: 2, tag: 'DEMIS' }];
    ppl.forEach((pp, i) => {
      const ang = t * 2.4 + i * TAU / 4, walkX = wx + ww / 2 + Math.cos(ang) * 330, target = chairs[i], e = easeOut(sk);
      const x = stopped ? lerp(walkX, target, e) : walkX, seatY = wy + wh + 8, y = stopped ? lerp(wy + wh - 40, seatY, e) - Math.sin(e * Math.PI) * 70 : wy + wh - 40 - Math.abs(Math.sin(ang * 3)) * 6;
      const sat = stopped && e > .85;
      if (sat) for (const sd of [-1, 1]) { rrect(x + sd * 14 - 9, seatY - 92, 18, 70, 8); paint('#2B3150', NP.ink, 2); }
      toon(x, y, 22, { hair: pp.hair, hairCol: NHAIR.brown, top: 'suit', topCol: pp.col, skin: pp.sk, legs: !sat, walk: stopped ? undefined : ang * 2, tag: pp.tag, eyes: stopped ? (i === 3 ? 'happy' : 'wide') : 'happy', mouth: stopped ? (i === 3 ? 'grin' : 'O') : 'smile', aL: stopped ? .8 : -1.2, aR: stopped ? .8 : -1.2 });
      if (i === 3 && stopped) { const sy = y - 11 * 22 - 30; ctx.beginPath(); ctx.moveTo(target + 30, sy + 16); ctx.lineTo(target + 30, seatY - 120); paint(null, NP.ink, 4); rrect(target - 50, sy - 18, 100, 36, 4); paint(NP.gold, NP.ink, 3); txt('CHAIR', target, sy, 24, NP.ink, { font: 'archivo' }); }
    });
    if (!stopped) for (let i = 0; i < 3; i++) { const a = frac(t * 1.5 + i / 3); txt('♪', wx + 100 + i * 250 + a * 60, wy + 260 - a * 120, 44, `rgb(40 30 20 / ${1 - a})`, { font: 'archivo' }); }
    ctx.restore();
    rrect(wx, wy, ww, wh, 6); paint(null, '#E8F0F4', 8);
    // the clock over the door: 27 YEARS
    ell(620, 250, 78); paint('#FBFAF4', NP.ink, 6);
    for (const [sp, L, lw] of [[3, 44, 9], [36, 62, 5]]) { const a = t * sp; ctx.beginPath(); ctx.moveTo(620, 250); ctx.lineTo(620 + Math.sin(a) * L, 250 - Math.cos(a) * L); paint(null, NP.ink, lw); }
    rrect(530, 340, 180, 50, 6); paint(NP.gold, NP.ink, 3); txt('27 YEARS', 620, 366, 30, NP.ink, { font: 'archivo' });
    // doors + lawn + the sign
    rrect(500, 440, 250, 390, 4); paint('rgb(200 240 250 / .5)', NP.ink, 5); ctx.beginPath(); ctx.moveTo(625, 440); ctx.lineTo(625, 830); paint(null, NP.ink, 5);
    vFill('#6ACB5A', '#3A8A3A', -100, 830, W + 200, 400);
    rrect(1350, 850, 440, 110, 8); paint('#D8DCE4', NP.ink, 4); txt('GOOGLE', 1570, 892, 44, '#3A4458', { font: 'archivo', spacing: 8 }); txt('MOUNTAIN VIEW', 1570, 935, 22, '#3A4458', { font: 'archivo', spacing: 4 });
    // Jeff, strolling out with his box
    const jx = lerp(640, 270, clamp(lt / d)), jw = lt * 2.8, look = stopped ? 1 : 0;
    toon(jx, 1000, 60, { hair: 'short', hairCol: NHAIR.grey, glasses: 'square', top: 'sweater', topCol: '#4A6A9A', skin: 0, legs: true, walk: jw, flip: look > .5, eyes: stopped ? 'wide' : 'happy', mouth: stopped ? 'smirk' : 'smile', sweat: stopped, reachL: [-1.9, -5.6], reachR: [1.9, -5.6] });
    ctx.save(); ctx.translate(jx, 1000 - 5.2 * 60 + Math.abs(Math.sin(jw * TAU)) * 6);
    rrect(-120, -80, 240, 150, 6); paint('#C8A06A', NP.ink, 4); ctx.fillStyle = 'rgb(0 0 0 / .12)'; ctx.fillRect(-120, -80, 240, 30);
    for (const [lx, ly, a] of [[-60, -110, -.4], [-40, -140, 0], [-20, -110, .4]]) { ctx.save(); ctx.translate(lx, ly); ctx.rotate(a); ell(0, 0, 18, 40); paint('#3AA05A', NP.ink, 3); ctx.restore(); }
    rrect(-80, -110, 60, 40, 6); paint('#8A5A30', NP.ink, 3);
    rrect(20, -130, 60, 70, 4); paint('#FBFAF2', NP.ink, 3); rrect(30, -120, 40, 44, 2); paint('#6A9AE0'); rrect(90, -110, 30, 40, 6); paint('#F4F2EC', NP.ink, 3);
    ctx.restore();
    liveBug(96, 70, { label: 'BUSINESS', col: '#1E7A4A' });
    chyron('JEFF DEAN LEAVES GOOGLE', 'AFTER 27 YEARS · DEMIS HASSABIS MOVES TO CHAIR', { k: chyK(lt), style: 'money', tab: 'NEW' });
  });

  // =====================================================================================
  // V3.15 Claude disproved Jacobian, — SCIENCE 89: CLAWD at the chalkboard with the counterexample, beaming on the beat
  // ("Jacobian"); the CGI surface spins; Val applauds from the desk.
  line('V3', 15, (p, lt, d, t) => {
    const b1 = bt(t, lt, 1) - .03;
    vFill('#04140C', '#000804');
    ctx.strokeStyle = 'rgb(42 240 138 / .12)'; ctx.lineWidth = 2; ctx.beginPath(); for (let x = 0; x < W; x += 60) { ctx.moveTo(x, 0); ctx.lineTo(x, H); } for (let y = 0; y < H; y += 60) { ctx.moveTo(0, y); ctx.lineTo(W, y); } ctx.stroke();
    rrect(80, 70, 560, 96, 10); paint('rgb(0 20 10 / .85)', '#2AF08A', 3);
    chrome('SCIENCE 89', 360, 118, 64, { font: 'archivo', style: 'white', depth: 5, italic: .1, spacing: 3 });
    // the chalkboard
    rrect(90, 200, 1400, 580, 10); paint('#6B4A2A', NP.ink, 5); rrect(112, 222, 1356, 536, 4); paint(lg(0, 222, 0, 758, [[0, '#2E5E3E'], [1, '#1E4A2E']]));
    ctx.fillStyle = 'rgb(255 255 255 / .05)'; ell(800, 400, 500, 140, -.15); ctx.fill();
    const chalk = (s, x, y, sz, a = 1) => txt(s, x, y, sz, `rgb(245 245 235 / ${.92 * a})`, { font: 'marker', align: 'left' });
    const wk = clamp(lt / .5);
    chalk('JACOBIAN CONJECTURE (1939)', 500, 280, 54);
    ctx.save(); ctx.beginPath(); ctx.rect(480, 320, 1000 * wk + 20, 420); ctx.clip();
    const w1 = textW('F : C', 60, 'marker'); chalk('F : C', 560, 390, 60); chalk('3', 566 + w1, 366, 34);
    ctx.beginPath(); ctx.moveTo(610 + w1, 392); ctx.lineTo(700 + w1, 392); ctx.moveTo(682 + w1, 378); ctx.lineTo(702 + w1, 392); ctx.lineTo(682 + w1, 406); paint(null, 'rgb(245 245 235 / .92)', 6);
    chalk('C', 722 + w1, 390, 60); chalk('3', 728 + w1 + textW('C', 60, 'marker'), 366, 34);
    chalk('det J(F) = constant', 560, 480, 60);
    chalk('BUT F IS NOT INVERTIBLE', 560, 570, 60);
    chalk('SO: FALSE FOR n ≥ 3', 560, 665, 60);
    ctx.restore();
    ctx.beginPath(); ctx.rect(540, 626, 650 * clamp((lt - .45) / .2), 80); ctx.strokeStyle = 'rgb(255 230 120 / .85)'; ctx.lineWidth = 5; ctx.stroke();
    // Clawd, chalk in hand
    const wr = Math.sin(t * 20) * .15;
    newsClawd(310, 900, 40, { legs: false, shadow: false, eyes: lt > b1 ? 'happy' : 'normal', blush: lt > b1, mouth: lt > b1 ? 'grin' : 'smile', reachR: [5.4 + wr, -10.2], hold: () => { ctx.rotate(-.6); rrect(-6, -40, 12, 40, 3); paint('#F4F4EC', NP.ink, 2); }, aL: -.4 });
    // the CGI surface: a wireframe saddle spinning on the monitor
    rrect(1530, 200, 330, 290, 10); paint('#000', '#2AF08A', 4);
    ctx.save(); ctx.beginPath(); ctx.rect(1534, 204, 322, 282); ctx.clip();
    const cx = 1695, cy = 350, ry = t * 1.3, N = 10, prj = (u, v) => { const x = u, y = v, z = (u * u - v * v) * .6 + Math.sin(u * 3 + t) * .08; const X = x * Math.cos(ry) - y * Math.sin(ry), Y = x * Math.sin(ry) + y * Math.cos(ry); return [cx + X * 110, cy + Y * 42 - z * 110]; };
    ctx.strokeStyle = '#2AF08A'; ctx.lineWidth = 2; ctx.beginPath();
    for (let i = 0; i <= N; i++) for (let j = 0; j <= N; j++) { const u = i / N * 2 - 1, v = j / N * 2 - 1, [a, b] = prj(u, v); if (j) ctx.lineTo(a, b); else ctx.moveTo(a, b); }
    for (let j = 0; j <= N; j++) for (let i = 0; i <= N; i++) { const u = i / N * 2 - 1, v = j / N * 2 - 1, [a, b] = prj(u, v); if (i) ctx.lineTo(a, b); else ctx.moveTo(a, b); }
    ctx.stroke(); ctx.restore();
    pixelText('det J = CONST', 1695, 450, 3, NP.phosphor, { align: 'center', edge: null });
    // Val applauds from the desk
    const clap = Math.abs(Math.sin(t * 16));
    otsBox(1530, 520, 330, 250, (w, h) => {
      vFill('#2F5BD8', '#0B1A66');
      toon(w / 2, h + 150, 26, { ...CAST.val.o, legs: false, shadow: false, eyes: 'happy', mouth: 'grin', reachL: [-.2 - clap * .5, -7.6], reachR: [.2 + clap * .5, -7.6], hand: 'open', handL: 'open' });
    }, { k: inK(lt, .05, .15), label: 'VAL LOSS', labelCol: NP.magenta, labelH: 44, labelSize: 28 });
    chyron('JACOBIAN CONJECTURE DISPROVED', 'COUNTEREXAMPLE FOUND WITH CLAUDE FABLE 5', { k: chyK(lt), style: 'purple', size: 50 });
  });

  // =====================================================================================
  // V3.16 Gwern gave up his pseudonym! — the callback to V1.3: same fence, same sign, same hooded figure behind the mosaic… and on
  // "gave up" the sun comes up, the hood comes down and the mosaic resolves into a big friendly grin. The super updates.
  function crate(x, y, w, h, rot = 0) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot);
    rrect(-w / 2, -h, w, h, 4); paint(lg(0, -h, 0, 0, [[0, '#D8A060'], [1, '#A8723A']]), NP.ink, 4);
    ctx.lineWidth = 10; ctx.strokeStyle = '#8A5A2A'; ctx.strokeRect(-w / 2 + 5, -h + 5, w - 10, h - 10);
    ctx.beginPath(); ctx.moveTo(-w / 2 + 8, -h + 8); ctx.lineTo(w / 2 - 8, -8); paint(null, '#8A5A2A', 9);
    txt('GPU', 0, -h / 2 + 2, h * .42, '#2A160A', { font: 'mono', alpha: .85 });
    ctx.restore();
  }
  line('V3', 16, (p, lt, d, t) => {
    const rev = bt(t, lt, 1) - .06, rk = clamp((lt - rev) / .3), up = lt > rev, sun = easeOut(rk);
    const scene = () => {
      camBegin(960, 540 - p * 20, 1 + p * .04);
      vFill(mixCol('#2A1850', '#5AB4F0', sun), mixCol('#F08A40', '#FFE8A0', sun), -600, -700, W + 1200, 1500);
      ell(1500, lerp(640, 330, sun), lerp(90, 120, sun), lerp(90, 120, sun)); paint(mixCol('#FFD27A', '#FFF4B0', sun));
      if (sun > 0) { ctx.save(); ctx.globalAlpha = sun * .5; rays(1500, lerp(640, 330, sun), 16, 'rgb(255 250 200 / .35)', t * .2); ctx.restore(); }
      ctx.fillStyle = mixCol('#3A2450', '#7A9AC0', sun); for (let i = 0; i < 14; i++) { const bw = 90 + hash(i + 40) * 120, bh = 80 + hash(i + 50) * 200; ctx.fillRect(i * 150 - 60, 800 - bh, bw, bh + 10); }
      vFill(mixCol('#3A3040', '#5A7A4A', sun), mixCol('#1A1418', '#2A4A2A', sun), -600, 790, W + 1200, 800);
      ctx.strokeStyle = 'rgb(40 30 40 / .7)'; ctx.lineWidth = 3; ctx.beginPath(); for (let x = -600; x < W + 600; x += 40) { ctx.moveTo(x, 610); ctx.lineTo(x + 180, 800); ctx.moveTo(x + 180, 610); ctx.lineTo(x, 800); } ctx.stroke();
      ctx.fillStyle = '#2A2028'; for (let x = -600; x < W + 600; x += 360) ctx.fillRect(x, 590, 14, 220);
      // the crate tower: taller now, off the top of the frame
      for (let i = 0; i < 9; i++) crate(1150 + (hash(i + 7) - .5) * 30, 905 - i * 140, 250, 140, (hash(i + 3) - .5) * .05);
      ctx.save(); ctx.translate(560, 660); ctx.rotate(-.04); rrect(-190, -60, 380, 120, 6); paint('#F2E8C8', NP.ink, 4);
      txt('THE SCALING', 0, -24, 38, NP.red, { font: 'marker' }); txt('HYPOTHESIS', 0, 22, 38, NP.ink, { font: 'marker' }); ctx.restore();
      // Gwern: hooded and pointing up… then hood down, waving, grinning
      const bob = Math.abs(Math.sin(bpOf(t) * Math.PI)) * .08;
      if (!up) toon(930, 915, 40, { top: 'hoodie', topCol: '#3A3A52', hood: true, aR: 1.25, eR: .1, hand: 'point', aL: -1.1, eL: .5, dy: -bob });
      else toon(930, 915, 40, { top: 'hoodie', topCol: '#3A3A52', hair: 'short', hairCol: NHAIR.brown, skin: 0, eyes: 'happy', mouth: 'grin', blush: true, aR: 1.1 + Math.sin(t * 14) * .25, eR: .5, hand: 'wave', aL: -1.1, eL: .5, dy: -bob - sun * .06 });
      toon(330, 1215, 52, { ...CAST.randi.o, legs: false, shadow: false, reachR: [1.2, -7.2], hold: micHold(.25), lookX: .7, lookY: up ? -.2 : -.9, eyes: up ? 'wide' : 'open', mouth: up ? 'O' : undefined, talk: up ? undefined : talk(t) });
      camEnd();
    };
    scene();
    // identity withheld… until it isn't
    const block = up ? lerp(18, 1, easeOut(clamp((lt - rev) / .25))) : 18;
    if (block > 1.6) { const s = 1 + p * .04, fy = (915 - 9.55 * 40 - (540 - p * 20)) * s + 540 - Math.abs(Math.sin(bpOf(t) * Math.PI)) * .08 * 40 * s, fx = (930 - 960) * s + 960; mosaic(fx - 53 * s, fy - 66 * s, 106 * s, 128 * s, block, scene); }
    if (up && lt < rev + .35) glint(940, 520, 160 * Math.sin(clamp((lt - rev) / .35) * Math.PI), 1);
    liveBug();
    if (!up || lt < rev + .15) chyron('GWERN', 'IDENTITY WITHHELD', { k: chyK(lt), out: up ? (lt - rev) / .15 : 0, style: 'live', tab: 'LIVE' });
    if (up) chyron('GWERN', 'FOUNDER, GUARDIAN ANGEL INC.', { k: clamp((lt - rev - .12) / .3), style: 'money', tab: 'UPDATE' });
    flash(lt, rev, .12, .5, '255 245 210');
  });
})();

;
// ---- styles/newscast/ch/c07_chorus3.js ----
// c07_chorus3 — Chorus 3: the COMPUTE-A-THON, Channel 89's all-night telethon for more compute. Bigger than C2's team promo:
// risers, a bulb marquee, a phone bank, a tote board, confetti cannons. Sub-shots cut on beats, keyed to linesOf('C3'):
//   L1  "We didn't start the scaling"   the news team on risers under a bulb marquee; the hook lights up word by word (caption hidden)
//   L2a "It was always training,"       star wipe to the phone bank: Clawds and computers grab ringing phones on the beats; it's HOUR 81,000
//   L2b "and the curves kept gaining,"  the tote board: the painted curve climbs a notch per beat, the total rolls up through septillions
//   L3  "We didn't start the scaling"   DVE flip to the hosts' desk: confetti cannons on the words, the hook in chrome, Val's hair to max
//   L4a "No, we didn't preordain it,"   the host (Clawd, in a tux) shrugs to camera, sweating; the floor manager's cue card: LOOK INNOCENT
//   L4b "but we can't contain it!"      the tote board's digits run off its edges, the curve bursts out of the top, handsets fly off the
//                                        hook, the set shakes → vertical roll into V4.1
// Colour run: red velvet + gold bulbs / teal phone bank / black-and-amber tote board / magenta confetti / red spotlight / overload.
(() => {
  const halfRound = b => Math.round(b * 2) / 2;
  const flash = (x, x0, dur = .1, a = .6, col = '255 255 255') => { const k = (x - x0) / dur; if (k >= 0 && k < 1) { ctx.fillStyle = `rgb(${col} / ${a * (1 - k)})`; ctx.fillRect(-300, -300, W + 600, H + 600); } };
  // word onsets inside a "We didn't start the scaling" line, in beats from the line's start (WE · DIDN'T · START · THE · SCALING)
  const HOOK_AT = [0, 1.5, 2.5, 3.1, 3.85];
  const BULB = '#FFE7A0', BULB_HOT = '#FFB42A';

  // ---------------------------------------------------------------------------------------------------------------
  // bulbs(str, x, y, px, o): marquee lettering built from light bulbs on the VCR font's 5×7 grid. (x, y) = top-centre.
  // o.lit(i) → 0/1 per character; o.col; o.sock (unlit socket colour); o.glow (0..1); o.align.
  function bulbs(str, x, y, px, o = {}) {
    str = String(str).toUpperCase();
    const chars = [...str], w = pixelW(str, px), x0 = o.align === 'left' ? x : o.align === 'right' ? x - w : x - w / 2;
    const col = o.col ?? BULB, r = px * .4, lit = o.lit ?? (() => 1), f = Math.floor(T * 12);
    const on = [], off = [];
    chars.forEach((ch, i) => {
      const g = PIXFONT[ch] || PIXFONT['?'], k = lit(i);
      for (let rr = 0; rr < 7; rr++) for (let q = 0; q < 5; q++) if (g[rr * 5 + q] === '#') {
        const cx = x0 + (i * 6 + q) * px + px / 2, cy = y + rr * px + px / 2;
        (k > 0 && hash2(i * 41 + rr * 7 + q, f) > (o.flicker ?? .025) ? on : off).push([cx, cy]);
      }
    });
    const dots = (pts, rad) => { ctx.beginPath(); for (const [a, b] of pts) { ctx.moveTo(a + rad, b); ctx.arc(a, b, rad, 0, TAU); } };
    ctx.save();
    if (off.length && o.sock !== null) { dots(off, r * .72); ctx.fillStyle = o.sock ?? '#3A2410'; ctx.fill(); }
    if (on.length) {
      ctx.globalCompositeOperation = 'lighter';
      const g = o.glow ?? 1;
      dots(on, r * 2.3); ctx.fillStyle = alpha(col, .1 * g); ctx.fill();
      dots(on, r * 1.45); ctx.fillStyle = alpha(col, .22 * g); ctx.fill();
      ctx.globalCompositeOperation = 'source-over';
      dots(on, r); ctx.fillStyle = col; ctx.fill();
      dots(on.map(([a, b]) => [a - r * .25, b - r * .25]), r * .38); ctx.fillStyle = 'rgb(255 255 255 / .85)'; ctx.fill();
    }
    ctx.restore();
    return w;
  }
  // A frame of chasing marquee bulbs round a rectangle.
  function bulbFrame(x, y, w, h, t, o = {}) {
    const gap = o.gap ?? 38, col = o.col ?? BULB, r = o.r ?? 7, ph = Math.floor(t * (o.speed ?? 9));
    const pts = [];
    const nx = Math.round(w / gap), ny = Math.round(h / gap);
    for (let i = 0; i <= nx; i++) pts.push([x + i * w / nx, y], [x + w - i * w / nx, y + h]);
    for (let j = 1; j < ny; j++) pts.push([x + w, y + j * h / ny], [x, y + h - j * h / ny]);
    ctx.save();
    pts.forEach(([a, b], i) => {
      const on = (i + ph) % 3 === 0 || o.all;
      if (on) { ctx.globalCompositeOperation = 'lighter'; ctx.fillStyle = alpha(col, .2); ell(a, b, r * 2.4); ctx.fill(); ctx.globalCompositeOperation = 'source-over'; }
      ell(a, b, r); ctx.fillStyle = on ? col : '#5A4220'; ctx.fill();
    });
    ctx.restore();
  }
  // The stage curtain (cached per colour): velvet folds, a swag along the top, a gold fringe.
  const curtain = (base) => cached('c3curtain|' + base, W, H, () => {
    ctx.fillStyle = shade(base, .55); ctx.fillRect(0, 0, W, H);
    for (let i = 0; i < 26; i++) {
      const x = i * 78 - 24;
      ctx.fillStyle = lg(x, 0, x + 78, 0, [[0, 'rgb(0 0 0 / .5)'], [.38, alpha(tint(base, .18), .9)], [.55, alpha(base, .75)], [1, 'rgb(0 0 0 / .5)']]);
      ctx.fillRect(x, 0, 78, H);
    }
    ctx.fillStyle = lg(0, 0, 0, H, [[0, 'rgb(0 0 0 / 0)'], [.7, 'rgb(0 0 0 / .15)'], [1, 'rgb(0 0 0 / .6)']]); ctx.fillRect(0, 0, W, H);
    for (let i = 0; i < 7; i++) {
      const x0 = i * 300 - 60;
      ctx.beginPath(); ctx.moveTo(x0, 0); ctx.quadraticCurveTo(x0 + 150, 170, x0 + 300, 0); ctx.closePath();
      ctx.fillStyle = lg(0, 0, 0, 140, [[0, shade(base, .3)], [1, tint(base, .12)]]); ctx.fill();
      ctx.strokeStyle = NP.gold; ctx.lineWidth = 6; ctx.beginPath(); ctx.moveTo(x0, 4); ctx.quadraticCurveTo(x0 + 150, 170, x0 + 300, 4); ctx.stroke();
      for (let k = 1; k < 12; k++) { const u = k / 12, fx = x0 + u * 300, fy = 2 * u * (1 - u) * 166 + 6; ctx.fillStyle = NP.goldDk; ctx.fillRect(fx - 2, fy, 4, 18); }
    }
  });
  const spot = (x, y, r, col = '255 240 210', a = .35) => { ctx.save(); ctx.globalCompositeOperation = 'screen'; ctx.fillStyle = rg(x, y, 5, r, [[0, `rgb(${col} / ${a})`], [1, `rgb(${col} / 0)`]]); ctx.fillRect(x - r, y - r, r * 2, r * 2); ctx.restore(); };
  const beam = (x0, x1, col = '255 240 200', a = .12) => { ctx.save(); ctx.globalCompositeOperation = 'screen'; ctx.fillStyle = `rgb(${col} / ${a})`; poly([[x0 - 30, -40], [x0 + 30, -40], [x1 + 260, H + 40], [x1 - 260, H + 40]]); ctx.fill(); ctx.restore(); };
  // A chrome-trimmed riser / desk front band across the frame.
  function skirt(y0, y1, col, o = {}) {
    ctx.fillStyle = lg(0, y0, 0, y1, [[0, tint(col, .15)], [.5, col], [1, shade(col, .45)]]); ctx.fillRect(-300, y0, W + 600, y1 - y0);
    ctx.fillStyle = lg(0, y0, 0, y0 + 16, [[0, '#FFF6D0'], [.5, NP.gold], [1, NP.goldDk]]); ctx.fillRect(-300, y0, W + 600, 14);
    ctx.fillStyle = 'rgb(255 255 255 / .08)'; ctx.fillRect(-300, y0 + 18, W + 600, (y1 - y0) * .3);
    if (o.logo) chrome(o.logo, W / 2, (y0 + y1) / 2 + 6, o.size ?? 74, { font: 'archivo', style: o.style ?? 'gold', italic: .12, depth: 7, spacing: 3 });
  }

  // ---------------------------------------------------------------------------------------------------------------
  // Clawd as the telethon host: a black tux, a bow tie and a red carnation. Same options as newsClawd.
  function host(x, y, u, o = {}) {
    newsClawd(x, y, u, { suitCol: '#17171F', tie: '#17171F', pocket: '#F4F2EC', ...o });
    ctx.save(); ctx.translate(x, y + (o.dy ?? 0) * u); if (o.rot) ctx.rotate(o.rot); ctx.scale(o.flip ? -u : u, u); ctx.lineJoin = 'round';
    poly([[-1.05, -4.75], [1.05, -4.75], [0, -2.85]]); paint('#F7F5EE', NP.ink, .13);
    for (const sd of [-1, 1]) { poly([[sd * .25, -4.75], [sd * 1.05, -4.75], [sd * .75, -4.25]]); paint('#FFFFFF', NP.ink, .08); }
    for (const sd of [-1, 1]) { poly([[0, -4.5], [sd * .95, -4.9], [sd * .95, -4.1]]); paint('#15121C', NP.ink, .1); }
    ell(0, -4.5, .26, .22); paint('#2A2630', NP.ink, .08);
    for (const sy of [-3.85, -3.35]) { ell(0, sy, .1); paint('#2A2630'); }
    for (let i = 0; i < 6; i++) { const a = i / 6 * TAU; ell(-2.75 + Math.cos(a) * .28, -4.15 + Math.sin(a) * .28, .24); paint('#E0223A', NP.ink, .05); }
    ell(-2.75, -4.15, .18); paint('#9A0A1E');
    ctx.restore();
  }
  // Val's hair, at a chosen volume (drawn behind her toon; vol 1 = normal).
  function bigHair(x, y, s, vol, o = {}) {
    if (vol <= 1.02) return;
    const hc = CAST.val.o.hairCol, k = vol;
    ctx.save(); ctx.translate(x, y + (o.dy ?? 0) * s); if (o.rot) ctx.rotate(o.rot); ctx.scale(s, s);
    const blobs = [[0, -1.0, 2.2], [-1.9, -.1, 1.55], [1.9, -.1, 1.55], [-2.4, 1.3, 1.2], [2.4, 1.3, 1.2], [-1.1, -1.9, 1.35], [1.1, -1.9, 1.35], [0, -2.4, 1.2]];
    const pts = blobs.map(([bx, by, r]) => [bx * k * .92, -9.9 + by * k * .95, r * (.6 + .4 * k)]);
    for (const [bx, by, r] of pts) { ell(bx, by, r); paint(hc, NP.ink, .12); }
    for (const [bx, by, r] of pts) { ell(bx, by, r - .1); paint(hc); }
    ctx.strokeStyle = tint(hc, .4); ctx.lineWidth = .13; ctx.lineCap = 'round';
    for (const [bx, by, r] of pts) { ctx.beginPath(); ctx.arc(bx - r * .15, by - r * .1, r * .55, 3.6, 4.9); ctx.stroke(); }
    ctx.restore();
  }

  // ---------------------------------------------------------------------------------------------------------------
  // 80s desk phones, handsets and curly cords.
  const PHONE_COLS = ['#E8DCC0', '#D8262F', '#F4F2EC', '#3A3F58', '#E8DCC0', '#D8262F'];
  function handset(x, y, s, rot, col) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot); ctx.scale(s, s);
    rrect(-52, -9, 104, 18, 9); paint(col, NP.ink, 3);
    for (const sd of [-1, 1]) { rrect(sd * 52 - 17, -6, 34, 26, 10); paint(col, NP.ink, 3); }
    ctx.fillStyle = 'rgb(255 255 255 / .3)'; ctx.fillRect(-40, -6, 70, 4);
    ctx.restore();
  }
  function cord(x0, y0, x1, y1, col, o = {}) {
    const L = Math.hypot(x1 - x0, y1 - y0), n = Math.max(8, Math.floor(L / 7)), nx = -(y1 - y0) / (L || 1), ny = (x1 - x0) / (L || 1), sag = o.sag ?? 40;
    ctx.beginPath();
    for (let i = 0; i <= n; i++) { const u = i / n, a = u * n * 1.9, wig = Math.sin(a) * 7, bx = lerp(x0, x1, u), by = lerp(y0, y1, u) + Math.sin(u * Math.PI) * sag; ctx.lineTo(bx + nx * wig, by + ny * wig); }
    ctx.lineJoin = 'round'; ctx.strokeStyle = NP.ink; ctx.lineWidth = 5; ctx.stroke(); ctx.strokeStyle = col; ctx.lineWidth = 2.5; ctx.stroke();
  }
  // phone80(x, y, s, o): (x, y) = base bottom-centre. o.col, o.handset (false = lifted), o.ring (0..1 jiggle), o.t.
  function phone80(x, y, s, o = {}) {
    const col = o.col ?? PHONE_COLS[0], ring = o.ring ?? 0, t = o.t ?? T;
    ctx.save(); ctx.translate(x, y); ctx.scale(s, s);
    ctx.fillStyle = 'rgb(0 0 0 / .25)'; ell(0, 2, 70, 9); ctx.fill();
    poly([[-62, 0], [62, 0], [48, -42], [-48, -42]]); paint(col, NP.ink, 3.5);
    ctx.fillStyle = 'rgb(0 0 0 / .14)'; poly([[26, 0], [62, 0], [48, -42], [22, -42]]); ctx.fill();
    rrect(-30, -36, 60, 30, 5); paint(shade(col, .12), NP.ink, 2);
    ctx.fillStyle = col === '#3A3F58' ? '#C9CFDB' : '#2A2630'; for (let r = 0; r < 3; r++) for (let c = 0; c < 4; c++) ctx.fillRect(-24 + c * 13, -32 + r * 9, 8, 5);
    ell(48, -34, 5); paint(ring > 0 && frac(t * 8) < .5 ? '#FF3030' : '#6A1010');
    if (o.handset !== false) {
      const jig = ring > 0 ? Math.sin(t * 90) * .07 * ring : 0, lift = ring > 0 ? Math.abs(Math.sin(t * 45)) * 5 * ring : 0;
      handset(0, -52 - lift, 1, jig, col);
    }
    ctx.restore();
    if (ring > 0 && o.handset !== false) {
      ctx.save(); ctx.strokeStyle = alpha(NP.gold, ring); ctx.lineWidth = 5; ctx.lineCap = 'round';
      for (const sd of [-1, 1]) for (let i = 0; i < 3; i++) { const ph = frac(t * 3 + i / 3); ctx.beginPath(); ctx.arc(x, y - 52 * s, (70 + ph * 50) * s, sd > 0 ? -.55 : Math.PI - .15, sd > 0 ? .15 : Math.PI + .55); ctx.globalAlpha = ring * (1 - ph); ctx.stroke(); }
      ctx.restore();
    }
  }

  // ---------------------------------------------------------------------------------------------------------------
  // The phone bank: six operators behind a long table (Clawd, a computer, Clawd…), each with a phone. top = table-top y.
  // o.state(i) → { ring, up, fly }: ring 0..1; up = answered (handset at the ear); fly = { x, y, rot } for a handset in the air.
  // o.panic: operators' eyes go wide.
  const OPX = [245, 531, 817, 1103, 1389, 1675];
  function phoneBank(t, top, o = {}) {
    const b = bpOf(t), xs = o.xs ?? OPX, U = o.u ?? 24, S = U * 1.2, k = U / 24;
    const ops = xs.map((x, i) => ({ x, i, pc: i % 2 === 1, st: o.state ? o.state(i) : {} }));
    // operators
    for (const op of ops) {
      const { x, i, pc, st } = op, bob = Math.sin(b * Math.PI + i) * .06, panic = o.panic ?? 0;
      if (!pc) {
        const y = top + 2 * U + 4 * k;
        op.hand = [x - 5.6 * U, y - 7.2 * U];
        host(x, y, U, { legs: false, shadow: false, dy: bob, eyes: panic > .5 ? 'wide' : st.up ? 'happy' : 'normal', talk: st.up && !panic ? talk(t, i) : undefined, mouth: panic ? 'O' : 'smile', sweat: panic > .5,
          aL: st.up ? undefined : -1.25, reachL: st.up ? [-5.6, -7.2] : undefined, aR: -1.2,
          holdL: st.up ? (() => handset(0, -10 * k, .8 * k, -1.35, PHONE_COLS[i])) : undefined });
      } else {
        const y = top + 24 * k;
        op.hand = [x - 3.3 * S, y - 5.6 * S];
        computer(x, y, S, { legs: false, shadow: false, dy: bob, face: panic > .5 ? 'dizzy' : st.up ? (frac(t * 2 + i * .3) < .5 ? 'happy' : 'grin') : 'smile', label: ['GPT', 'GEMINI', 'LLAMA'][(i - 1) / 2 | 0], seed: i,
          reachL: st.up ? [-3.3, -5.6] : undefined, aL: -1.1, aR: -1.2,
          holdL: st.up ? (() => handset(0, -8 * k, .8 * k, -1.35, PHONE_COLS[i])) : undefined });
      }
    }
    // the table
    const th = 18 * k;
    ctx.fillStyle = lg(0, top - th, 0, top + 20 * k, [[0, '#F2EEE2'], [1, '#B8B0A0']]); poly([[-100, top + 20 * k], [W + 100, top + 20 * k], [W + 40, top - th], [-40, top - th]]); ctx.fill();
    ctx.strokeStyle = NP.ink; ctx.lineWidth = 3; ctx.beginPath(); ctx.moveTo(-40, top - th); ctx.lineTo(W + 40, top - th); ctx.stroke();
    ctx.fillStyle = lg(0, top + 20 * k, 0, top + 240, [[0, '#2A3E9A'], [1, '#0E1A55']]); ctx.fillRect(-100, top + 20 * k, W + 200, 400);
    ctx.fillStyle = lg(0, top + 20 * k, 0, top + 34 * k, [[0, '#FFF6D0'], [1, NP.goldDk]]); ctx.fillRect(-100, top + 20 * k, W + 200, 12 * k);
    for (let q = 0; q < 7; q++) { const lx = 102 + q * 286; logo89(lx, top + 110 * k, 38 * k); }
    // pledge pads, placards, phones, cords
    for (const { x, i, st, hand } of ops) {
      const px = x + 112 * k, py = top + 14 * k;
      rrect(x - 116 * k, top + 2 * k, 92 * k, 28 * k, 3); paint('#FFFBEA', NP.ink, 2.5); txt('LINE ' + (i + 1), x - 70 * k, top + 16 * k, 19 * k, NP.navy, { font: 'archivo' });
      rrect(x - 8 * k, top - 16 * k, 70 * k, 24 * k, 2); paint('#FFF6A8', NP.ink, 2);
      if (st.up) { const sc = frac(t * 5 + i * .37) * 14 * k; ctx.beginPath(); ctx.moveTo(x, top - 6 * k); for (let q = 0; q < 7; q++) ctx.lineTo(x + q * 8 * k, top - (8 - (q % 2) * 6) * k); paint(null, NP.blue, 2.5); ctx.beginPath(); ctx.moveTo(x + 36 * k + sc, top - 10 * k); ctx.lineTo(x + 60 * k + sc, top - 48 * k); paint(null, NP.ink, 6 * k); }
      phone80(px, py, .8 * k, { col: PHONE_COLS[i], ring: st.ring ?? 0, handset: !(st.up || st.fly), t });
      if (st.up && hand) cord(px - 40 * k, py - 14 * k, hand[0] + 4 * k, hand[1] + 18 * k, PHONE_COLS[i], { sag: 60 * k });
      if (st.fly) { cord(px - 40 * k, py - 14 * k, st.fly.x, st.fly.y, PHONE_COLS[i], { sag: 10 }); handset(st.fly.x, st.fly.y, .95 * k, st.fly.rot, PHONE_COLS[i]); }
    }
  }

  // ---------------------------------------------------------------------------------------------------------------
  // The tote board's number: 10^(24 + bs) FLOP, rolling continuously; big bulbs for the leading digits + the -illion name.
  const ILLION = ['SEPTILLION', 'OCTILLION', 'NONILLION', 'DECILLION'];
  function toteValue(bs) {
    const e = 24 + Math.max(0, Math.floor(bs)), m = 10 ** frac(Math.max(0, bs)), grp = Math.floor((e - 24) / 3);
    const lead = Math.floor(m * 10 ** ((e - 24) % 3) + 1e-9);
    const D = String(Math.floor(m * 1000 + 1e-6)), digits = D + '0'.repeat(Math.max(0, e - 3));
    const withCommas = digits.replace(/\B(?=(\d{3})+(?!\d))/g, ',');
    return { lead: String(lead), name: ILLION[Math.min(ILLION.length - 1, grp)], full: withCommas, e };
  }

  // ---------------------------------------------------------------------------------------------------------------
  // SUB-SHOTS
  // L1: the team on risers under the marquee; the hook lights up word by word.
  function risers(t, lb) {
    const b = bpOf(t), nW = HOOK_AT.filter(w => lb >= w - .02).length, jazz = lb >= HOOK_AT[4] - .02;
    blit(curtain('#B0162A'), W / 2, H / 2);
    beam(420 + Math.sin(t * .9) * 120, 700, '255 220 180', .1); beam(1500 + Math.sin(t * .8 + 1) * 120, 1200, '255 220 180', .1);
    // marquee sign
    const sx = 330, sy = 176, sw = 1260, sh = 262;
    ctx.fillStyle = 'rgb(0 0 0 / .45)'; rrect(sx + 14, sy + 16, sw, sh, 18); ctx.fill();
    rrect(sx, sy, sw, sh, 18); paint(lg(0, sy, 0, sy + sh, [[0, '#2A1206'], [1, '#120602']]), NP.gold, 8);
    rrect(sx + 14, sy + 14, sw - 28, sh - 28, 12); paint(null, NP.goldDk, 3);
    bulbFrame(sx + 28, sy + 26, sw - 56, sh - 52, t, { gap: 34, r: 6 });
    const row = (str, y, px, words, base, col) => bulbs(str, W / 2, y, px, { col, sock: '#5A3A18', lit: i => { for (let w = 0; w < words.length; w++) { const [a, z] = words[w]; if (i >= a && i < z) return lb >= HOOK_AT[base + w] + (i - a) * .06 ? 1 : 0; } return 0; } });
    row("WE DIDN'T START", sy + 50, 11, [[0, 2], [3, 9], [10, 15]], 0, BULB);
    row('THE SCALING', sy + 138, 13.5, [[0, 3], [4, 11]], 3, BULB_HOT);
    if (jazz) sweepGlint(sx + 200, sx + sw - 200, sy + 188, (lb - HOOK_AT[4]) / 1.2, 90);
    // back riser: SUNNY · RANDI · BATCH · CHIP
    const back = [[520, CAST.sunny], [800, CAST.randi], [1120, CAST.batch], [1400, CAST.chip]];
    back.forEach(([x, c], i) => {
      const sw2 = Math.sin(b * Math.PI + i * .7) * .045, hop = -Math.abs(Math.sin(b * Math.PI)) * .12;
      toon(x, 800, 30, { ...c.o, legs: false, shadow: false, rot: sw2, dy: hop, talk: lineAt(t) && t < lineAt(t).end ? talk(t, i * 1.3) : undefined, mouth: 'smile', blink: frac(t * .4 + i * .23) < .04 ? 1 : 0,
        ...(jazz ? { aL: 1.05, aR: 1.05, eL: .35, eR: .35, hand: 'open', handL: 'open' } : { aL: -1.1, aR: -1.1 }) });
    });
    skirt(672, 740, '#5A1020');
    for (let i = 0; i < 26; i++) { const on = (i + Math.floor(t * 8)) % 2 === 0; ell(i * 80 + 20, 706, 8); paint(on ? BULB : '#5A4220'); }
    // front riser: CLAWD (host) and VAL
    const sw3 = Math.sin(b * Math.PI) * .04;
    host(760, 905, 34, { dy: -Math.abs(Math.sin(b * Math.PI)) * .1, rot: sw3, talk: talk(t), eyes: jazz ? 'happy' : 'normal', lookX: .2, aL: jazz ? .9 : -.9, reachR: [4.2, -8.6], hold: u => bigMic(0, -22, 19, { rot: -.35 }) });
    toon(1170, 1000, 38, { ...CAST.val.o, legs: false, shadow: false, rot: -sw3, dy: -Math.abs(Math.sin(b * Math.PI)) * .1, talk: talk(t, 2), reachR: [1.3, -8.2], hold: micHold(.3, .9),
      ...(jazz ? { aL: 1.1, eL: .3, handL: 'open' } : { aL: -.6, eL: .9 }), lookX: -.2 });
    skirt(846, 1000, '#7A0E1E', { logo: 'COMPUTE-A-THON', size: 84 });
    bulbFrame(60, 864, W - 120, 118, t, { gap: 46, r: 6, speed: 7 });
    spot(960, 420, 700, '255 200 150', .12);
  }

  // L2a: the phone bank. Phones ring on the beats and get answered two at a time.
  function bank(t, bs) {
    vFill('#0E6A70', '#052A36');
    ctx.fillStyle = 'rgb(255 255 255 / .05)'; for (let x = 0; x < W; x += 120) ctx.fillRect(x, 0, 56, H);
    spot(960, 330, 900, '120 255 240', .16);
    // the big sign
    rrect(300, 170, 1320, 150, 14); paint(lg(0, 170, 0, 320, [[0, '#0A2A40'], [1, '#04121C']]), NP.gold, 7);
    bulbFrame(318, 186, 1284, 118, t, { gap: 40, r: 5, col: '#9AF8FF' });
    chrome('OPERATORS STANDING BY', W / 2, 246, 76, { font: 'archivo', style: 'white', italic: .12, depth: 6, spacing: 3 });
    // telethon clock: it has been on the air for a very long time
    const hours = 81000 + Math.floor(bs * 9);
    rrect(110, 342, 380, 118, 8); paint('rgb(0 0 0 / .72)', '#3A8A8A', 3);
    pixelText('ON THE AIR', 130, 358, 4, '#9AF8FF', { edge: null });
    pixelText('HOUR ' + hours.toLocaleString('en-US'), 130, 402, 6, NP.gold, { edge: null });
    rrect(1430, 342, 380, 118, 8); paint('rgb(0 0 0 / .72)', '#3A8A8A', 3);
    pixelText('STATUS', 1450, 358, 4, '#9AF8FF', { edge: null });
    pixelText('TRAINING' + '.'.repeat(1 + Math.floor(t * 4) % 3), 1450, 402, 6, frac(t * 2) < .7 ? NP.phosphor : '#2A8A4A', { edge: null });
    // pickups: two per beat on beats 1, 2, 3 (order scattered along the table)
    const order = [2, 4, 0, 3, 1], pickB = i => .5 + Math.floor(order.indexOf(i) / 2);
    phoneBank(t, 752, { xs: [250, 605, 960, 1315, 1670], u: 31, state: i => { const pb = pickB(i); return { ring: bs < pb && bs > pb - 1.4 ? 1 : 0, up: bs >= pb }; } });
    chyron('CALL 1-800-TRAINING', null, { k: clamp(bs / .7), style: 'news', tab: 'CALL', size: 56, y: 800 });
  }

  // L2b: the tote board, full screen.
  function tote(t, bs) {
    fillAll('#07040A');
    ctx.fillStyle = rg(W / 2, 520, 50, 1100, [[0, 'rgb(90 40 0 / .5)'], [1, 'rgb(0 0 0 / 0)']]); ctx.fillRect(0, 0, W, H);
    const bx = 110, by = 190, bw = 1700, bh = 600;
    rrect(bx, by, bw, bh, 16); paint(lg(0, by, 0, by + bh, [[0, '#15100A'], [1, '#050302']]), NP.gold, 10);
    bulbFrame(bx + 22, by + 22, bw - 44, bh - 44, t, { gap: 42, r: 7, speed: 11 });
    // header band
    rrect(bx + 60, by + 48, bw - 120, 84, 8); paint(lg(0, by + 48, 0, by + 132, [[0, '#E0303A'], [1, '#7A0A10']]), '#FFD27A', 3);
    txt('COMPUTE-A-THON TOTE BOARD', W / 2, by + 92, 56, NP.gold, { font: 'bungee', spacing: 3, maxW: bw - 200 });
    // the curve, painted on the board: a notch per beat
    const steps = 5, kk = clamp((Math.floor(bs) + easeOut(clamp(frac(bs) * 3))) / steps * .92 + .08);
    const tip = cgiChart(bx + 130, by + 190, 640, 300, { fn: u => (Math.exp(u * 5) - 1) / (Math.exp(5) - 1), k: kk, col: NP.gold, bg: 'rgb(40 20 0 / .5)', grid: 'rgb(255 180 60 / .18)', fill: true });
    txt('COMPUTE', bx + 70, by + 360, 30, '#FFD27A', { font: 'archivo', rot: -TAU / 4, spacing: 2 });
    txt('2017  →  2026', bx + 450, by + 528, 28, '#FFD27A', { font: 'archivo', spacing: 2 });
    if (frac(bs) < .25) glint(tip[0], tip[1], 120 * (1 - frac(bs) * 4), 1 - frac(bs) * 4, '#FFE0A0');
    // the total
    const v = toteValue(bs), hit = 1 - clamp(frac(bs) / .25);
    txt('TOTAL PLEDGED', 1330, by + 200, 44, '#FFD27A', { font: 'bungee', spacing: 3 });
    rrect(880, by + 240, 900, 300, 10); paint('#000', '#5A4220', 4);
    bulbs(v.lead, 1330, by + 262, 20, { col: BULB_HOT, sock: '#2A1A08' });
    bulbs(v.name, 1330, by + 422, 9.5, { col: BULB, sock: '#2A1A08' });
    pixelText(v.full + ' FLOP', 1330, by + 500, 3, NP.crtAmber, { align: 'center', edge: null });
    if (hit > 0) { ctx.save(); ctx.globalCompositeOperation = 'lighter'; ctx.fillStyle = `rgb(255 200 90 / ${.25 * hit})`; rrect(880, by + 240, 900, 300, 10); ctx.fill(); ctx.restore(); }
    stationBug(1790, 930, 44, .8);
  }

  // L3: the hosts' desk: confetti cannons, the hook in chrome, Val's hair climbing to meet it.
  function confetti(t, fires, x0, y0, dir) {
    const cols = ['#FF4A9A', NP.gold, '#4AE0FF', '#7CFF8A', '#FFFFFF', '#B07AFF'];
    for (const [fi, tf] of fires.entries()) {
      const tau = t - tf; if (tau < 0 || tau > 3.2) continue;
      for (let i = 0; i < 70; i++) {
        const h1 = hash2(fi * 131 + i, dir > 0 ? 3 : 4), h2 = hash2(fi * 131 + i, 9), ang = -Math.PI / 2 + dir * (.25 + h1 * .55), sp = 1300 + h2 * 1300;
        const e = (1 - Math.exp(-2.6 * tau)) / 2.6, x = x0 + Math.cos(ang) * sp * e + Math.sin(tau * 5 + i) * 26 * tau, y = y0 + Math.sin(ang) * sp * e + 170 * tau * tau;
        if (y > H + 40 || x < -40 || x > W + 40) continue;
        ctx.save(); ctx.translate(x, y); ctx.rotate(tau * (4 + h1 * 6) + i); ctx.scale(1, Math.cos(tau * 9 + i) * .8 + .2);
        ctx.fillStyle = cols[i % cols.length]; ctx.fillRect(-10, -6, 20, 12); ctx.restore();
      }
    }
  }
  function cannon(x, y, dir, kick) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(dir * .5);
    rrect(-34, -150 + kick * 26, 68, 170, 14); paint(lg(-34, 0, 34, 0, [[0, '#8A8FA0'], [.35, '#FFFFFF'], [.6, '#B8BECB'], [1, '#5A6070']]), NP.ink, 4);
    rrect(-42, -160 + kick * 26, 84, 26, 8); paint(NP.gold, NP.ink, 4);
    ctx.restore();
    rrect(x - 70, y + 10, 140, 60, 10); paint('#2A2A34', NP.ink, 4);
    if (kick > 0) { const [mx, my] = [x + Math.sin(dir * .5) * 170, y - Math.cos(dir * .5) * 170]; glint(mx, my, 200 * kick, kick, '#FFF0C0'); }
  }
  function hosts(t, lb) {
    const b = bpOf(t), nW = HOOK_AT.filter(w => lb >= w - .02).length;
    blit(curtain('#8A1A7A'), W / 2, H / 2);
    beam(300 + Math.sin(t * 1.3) * 200, 900, '255 120 230', .14); beam(1600 + Math.sin(t * 1.1 + 2) * 200, 1000, '120 220 255', .14);
    spot(960, 560, 620, '255 210 240', .2);
    // Val's hair grows with every word
    const wk = HOOK_AT.reduce((a, w) => a + easeOut(clamp((lb - w + .02) / .3)), 0), vol = 1 + wk * .34 + (nW ? pulse(t, 7) * .06 : 0);
    const vx = 1230, vy = 960, vs = 42, bob = -Math.abs(Math.sin(b * Math.PI)) * .08, sw = Math.sin(b * Math.PI) * .035;
    bigHair(vx, vy, vs, vol, { dy: bob, rot: -sw });
    toon(vx, vy, vs, { ...CAST.val.o, legs: false, shadow: false, dy: bob, rot: -sw, talk: talk(t, 2), reachR: [1.25, -8.1], hold: micHold(.3, .9), aL: nW >= 5 ? 1.15 : .2 + nW * .15, eL: .4, handL: 'open', lookX: -.3, eyes: nW >= 5 ? 'happy' : 'open' });
    host(700, 800, 40, { dy: bob, rot: sw, talk: talk(t), eyes: nW >= 5 ? 'happy' : 'normal', lookX: .3, reachR: [4.3, -8.6], hold: u => bigMic(0, -26, 22, { rot: -.4 }), aL: nW >= 5 ? .9 : -.3, blush: nW >= 5 });
    // the hosts' desk
    ctx.fillStyle = lg(0, 718, 0, 752, [[0, '#FFF0FA'], [1, '#C890C0']]); poly([[340, 752], [1580, 752], [1540, 718], [380, 718]]); ctx.fill(); ctx.strokeStyle = NP.ink; ctx.lineWidth = 3; ctx.stroke();
    rrect(330, 752, 1260, 200, 8); paint(lg(0, 752, 0, 950, [[0, '#C8288A'], [1, '#4A0A40']]), NP.ink, 4);
    ctx.fillStyle = lg(0, 752, 0, 766, [[0, '#FFF6D0'], [1, NP.goldDk]]); ctx.fillRect(330, 752, 1260, 12);
    chrome('COMPUTE-A-THON', W / 2, 850, 78, { font: 'archivo', style: 'gold', italic: .12, depth: 7, spacing: 3 });
    // the hook in chrome, word by word
    const lay = (ws, size, gap) => { const wd = ws.map(w => textW(w, size, 'archivo', 3)); let x = W / 2 - (wd.reduce((a, c) => a + c, 0) + gap * (ws.length - 1)) / 2; return wd.map(w => { const c = x + w / 2; x += w + gap; return c; }); };
    const r1 = lay(['WE', "DIDN'T", 'START'], 100, 40), r2 = lay(['THE', 'SCALING'], 140, 50);
    const words = [['WE', r1[0], 262, 100], ["DIDN'T", r1[1], 262, 100], ['START', r1[2], 262, 100], ['THE', r2[0], 410, 140], ['SCALING', r2[1], 410, 140]];
    words.forEach(([wd, x, y, sz], i) => {
      const k = clamp((lb - HOOK_AT[i] + .02) / .12); if (k <= 0) return;
      chrome(wd, x, y - (i === 4 ? pulse(t, 6) * 8 : 0), sz, { font: 'archivo', style: i === 4 ? 'gold' : 'chrome', italic: .14, depth: 12, spacing: 3, s: lerp(1.8, 1, easeOut(k)), alpha: clamp(k * 2.5) });
    });
    if (nW >= 5) sweepGlint(r2[1] - 300, r2[1] + 300, 400, (lb - HOOK_AT[4]) / 1.1, 150);
    // cannons fire on WE, START and SCALING (and once more after the line)
    const fires = [0, 2, 4].map(i => HOOK_AT[i]).concat([HOOK_AT[4] + 1.5]).map(x => t - (lb - x) * beatLen());
    const kick = Math.max(0, ...fires.map(tf => { const a = t - tf; return a >= 0 && a < .25 ? 1 - a / .25 : 0; }));
    confetti(t, fires, 190, 800, 1); confetti(t, fires, 1730, 800, -1);
    cannon(190, 930, 1, kick); cannon(1730, 930, -1, kick);
  }

  // L4a: the host shrugs to camera. The floor manager's cue card knows what to do.
  function shrug(t, bs) {
    blit(curtain('#B0162A'), W / 2, H / 2);
    spot(930, 470, 520, '255 235 210', .5);
    vFill('#1A0808', '#050202', -300, 800, W + 600, 600);
    ctx.fillStyle = rg(930, 870, 20, 520, [[0, 'rgb(255 220 190 / .35)'], [1, 'rgb(255 220 190 / 0)']]); ell(930, 870, 520, 70); ctx.fill();
    const b = bpOf(t), up = easeOut(clamp(bs / .35)), bounce = Math.abs(Math.sin(b * Math.PI)) * .12, dart = Math.floor(bs) % 2 ? .7 : -.7;
    const u = 64, X = 930, Y = 870;
    host(X, Y, u, { dy: -up * .35 - bounce, eyes: 'wide', lookX: bs < .5 ? 0 : dart, lookY: -.2, talk: lineAt(t) && t < lineAt(t).end ? talk(t) * .8 : undefined, mouth: 'flat', sweat: true,
      reachL: [lerp(-5.2, -7.5, up), lerp(-2.6, -6.4, up)], reachR: [lerp(5.2, 7.5, up), lerp(-2.6, -6.4, up)] });
    // sweat flying off on the beats
    const bt0 = Math.floor(bs);
    for (let k = 0; k < 2; k++) {
      const age = frac(bs) + k; if (age > 1.6) continue;
      for (let i = 0; i < 5; i++) {
        const sd = i % 2 ? 1 : -1, a = -Math.PI / 2 + sd * (.5 + hash2(bt0 - k, i) * .7), sp = 380 + hash2(bt0 - k, i + 9) * 300, tau = age * beatLen();
        const x = X + sd * 4.2 * u + Math.cos(a) * sp * tau, y = Y - (8.4 + up * .35) * u + Math.sin(a) * sp * tau + 900 * tau * tau;
        ctx.save(); ctx.translate(x, y); ctx.rotate(Math.atan2(Math.sin(a) * sp + 1800 * tau, Math.cos(a) * sp) - Math.PI / 2);
        poly([[0, -22], [11, 4], [0, 14], [-11, 4]]); paint('#9FD3F2', NP.ink, 3); ctx.restore();
      }
    }
    // cue card from the right
    const ck = easeOut(clamp((bs - .45) / .3));
    if (ck > 0) {
      ctx.save(); ctx.translate(lerp(W + 400, 1560, ck), 520 + Math.sin(t * 3) * 6); ctx.rotate(.06);
      ctx.beginPath(); ctx.moveTo(150, 120); ctx.lineTo(420, 330); paint(null, NP.ink, 58); ctx.beginPath(); ctx.moveTo(150, 120); ctx.lineTo(420, 330); paint(null, '#3A3F58', 48);
      rrect(-190, -150, 380, 280, 6); paint('#FBFAF2', NP.ink, 5);
      txt('LOOK', 0, -70, 84, NP.ink, { font: 'marker' }); txt('INNOCENT', 0, 34, 84, NP.red, { font: 'marker', maxW: 340 });
      ctx.beginPath(); ctx.moveTo(-150, 96); ctx.quadraticCurveTo(0, 116, 150, 92); paint(null, NP.red, 6);
      ell(150, 118, 34, 30); paint(NSKIN[1], NP.ink, 4);
      ctx.restore();
    }
    liveBug(96, 70, { label: 'COMPUTE-A-THON', col: NP.red });
  }

  // L4b: containment failure. The total runs off the board, the curve bursts out of it, handsets fly, the set shakes.
  function overload(t, bs, lt, d) {
    const [sx, sy] = shakeXY(t, 5 + bs * 3.2);
    ctx.save(); ctx.translate(sx, sy);
    blit(curtain('#B0162A'), W / 2, H / 2);
    beam(500 + Math.sin(t * 7) * 300, 700, '255 230 160', .12); beam(1500 + Math.sin(t * 6 + 1) * 300, 1100, '255 230 160', .12);
    // the board (stage left, clear of the VCR display)
    const bx = 170, by = 176, bw = 1150, bh = 400, grow = Math.floor(bs * 2);
    rrect(bx, by, bw, bh, 14); paint(lg(0, by, 0, by + bh, [[0, '#15100A'], [1, '#050302']]), NP.gold, 9);
    bulbFrame(bx + 20, by + 20, bw - 40, bh - 40, t, { gap: 40, r: 6, speed: 20, all: frac(t * 6) < .5 });
    txt('TOTAL PLEDGED', bx + 60, by + 72, 44, '#FFD27A', { font: 'bungee', spacing: 3, align: 'left' });
    // the curve, painted on the board, bursts through its top edge and keeps going
    const bk = clamp(bs / 1.4), pts = [];
    for (let i = 0; i <= 60; i++) { const u = i / 60; pts.push([bx + 80 + u * 760, by + bh - 40 - (Math.exp(u * 4.2) - 1) / (Math.exp(4.2) - 1) * (bh - 90 + 760 * easeIn(bk))]); }
    const P = partial(pts, .6 + .4 * bk);
    ctx.beginPath(); P.forEach(([a, c], i) => i ? ctx.lineTo(a, c) : ctx.moveTo(a, c)); ctx.lineCap = 'round'; ctx.lineJoin = 'round';
    ctx.strokeStyle = alpha(NP.gold, .3); ctx.lineWidth = 28; ctx.stroke(); ctx.strokeStyle = NP.gold; ctx.lineWidth = 11; ctx.stroke(); ctx.strokeStyle = '#FFF6D0'; ctx.lineWidth = 3; ctx.stroke();
    const tip = P.at(-1); glint(tip[0], tip[1], 120, 1, '#FFE0A0');
    const hit = pts.find(p => p[1] < by + 5);
    if (tip[1] < by && hit) { // splinters of the board's frame where it broke through
      const since = Math.max(0, (by - tip[1]) / 700);
      for (let i = 0; i < 10; i++) { const a = -Math.PI / 2 + (hash(i + 3) - .5) * 2.4, dd = since * (260 + hash(i) * 380); ctx.save(); ctx.translate(hit[0] + Math.cos(a) * dd, by + Math.sin(a) * dd + dd * dd * .003); ctx.rotate(dd * .03 + i); ctx.fillStyle = i % 2 ? NP.gold : '#3A2A10'; ctx.fillRect(-18, -6, 36, 12); ctx.restore(); }
    }
    // the total: a new ",000" every eighth note, pinned to the board's right edge and running off its left one
    const v = toteValue(4 + frac(bs * 2) * .9 + grow * 3), str = v.full, px = 9, w = pixelW(str, px), xr = bx + bw - 50, y0 = by + 190;
    bulbs(str, xr, y0, px, { col: BULB_HOT, sock: '#2A1A08', align: 'right', flicker: .08 });
    for (let i = 0; i < 8; i++) { // bulbs popping where the number has run past the board
      const f = Math.floor(t * 16) + i * 5, x = xr - hash2(f, 1) * w, y = y0 + hash2(f, 2) * px * 7;
      if (x < bx - 10) glint(x, y, 60 + hash2(f, 3) * 70, .95, '#FFF0C0');
    }
    pixelText('FLOP', xr, y0 + 80, 5, NP.crtAmber, { align: 'right', edge: null });
    // the phone bank below: handsets launching off the hook one per eighth note
    phoneBank(t, 800, { panic: 1, state: i => {
      const launch = [0, 3, 1, 4, 2, 5].indexOf(i) * .5 + .25, a = (bs - launch) * beatLen();
      if (a < 0) return { ring: 1 };
      const x0 = OPX[i] + 70, dir = i < 3 ? -1 : 1, x = x0 + dir * a * (200 + i * 30), y = 770 - a * 1700 + a * a * 1500;
      return { fly: { x, y, rot: a * 14 * dir } };
    } });
    ctx.restore();
    // into V4.1: the picture rolls
    const rk = clamp((lt - (d - .32)) / .32);
    if (rk > 0) { glitch('roll', rk ** 1.5); tapeFX({ cut: 'roll' }); }
    flash(bs, 0, .5, .45, '255 240 200');
  }

  // ---------------------------------------------------------------------------------------------------------------
  section('C3', (p, lt, d, t) => {
    const L = linesOf('C3'), b = bpOf(t);
    const bL = L.map(l => halfRound(bpOf(l.start)));
    const bM1 = halfRound((bpOf(L[1].start) + bpOf(L[1].end)) / 2), bM3 = halfRound((bpOf(L[3].start) + bpOf(L[3].end)) / 2);
    if (b < bL[1]) {
      hideCaption();
      return risers(t, b - bpOf(L[0].start));
    }
    if (b < bM1) {
      const wk = clamp((b - bL[1]) / .75);
      if (wk < 1) { captionStyle({ rows: 1 }); return dveStar(wk, () => risers(t, b - bpOf(L[0].start)), () => bank(t, b - bL[1])); }
      return bank(t, b - bL[1]);
    }
    if (b < bL[2] - .5) return tote(t, b - bM1);
    if (b < bL[3]) {
      const lb = b - bpOf(L[2].start), fk = clamp((b - (bL[2] - .5)) / .8);
      if (fk < 1) return dveFlip(fk, () => tote(t, b - bM1), () => { hideCaption(); hosts(t, lb); });
      hideCaption();
      return hosts(t, lb);
    }
    if (b < bM3) return shrug(t, b - bL[3]);
    return overload(t, b - bM3, lt, d);
  });
})();

;
// ---- styles/newscast/ch/c08_v4.js ----
// c08_v4 — Verse 4: Aug 26 → Sep 22, 2026. Four weeks in sixteen headlines, and the station is coming apart: every chyron is BREAKING,
// the tape is worn (dropouts climb from 2 to 3), coffee mugs pile up on the desk, Val's hair keeps growing and Clawd sweats.
// Colour run (consecutive shots flip): cork tan / game-show purple / night navy + tape yellow / overdrive red / Doppler blue-green /
// replay grey / caution yellow / satellite blue / hillside green / ballroom burgundy / studio blue / NORAD green / poll purple /
// fact-check yellow / gift-wrap red close-up / studio blue.
(() => {
  // lt of the k-th beat at/after the window start (lines start on the beat or on the "and" before it)
  const bt = (t, lt, k = 0) => onBeat(0, Math.ceil(bpOf(t - lt) - .02) + k) - (t - lt);
  const flash = (lt, t0, dur = .1, a = .6, col = '255 255 255') => { const k = (lt - t0) / dur; if (k >= 0 && k < 1) { ctx.fillStyle = `rgb(${col} / ${a * (1 - k)})`; ctx.fillRect(-300, -300, W + 600, H + 600); } };
  const shake = (t, lt, t0, dur = .25, amt = 16) => { const k = (lt - t0) / dur; return k >= 0 && k < 1 ? shakeXY(t, amt * (1 - k)) : [0, 0]; };
  const rays = (cx, cy, n, col, rot = 0, R = 2600) => { ctx.fillStyle = col; ctx.beginPath(); for (let i = 0; i < n; i++) { const a0 = rot + i / n * TAU, a1 = a0 + TAU / n / 2; ctx.moveTo(cx, cy); ctx.lineTo(cx + Math.cos(a0) * R, cy + Math.sin(a0) * R); ctx.lineTo(cx + Math.cos(a1) * R, cy + Math.sin(a1) * R); ctx.closePath(); } ctx.fill(); };
  const pk = (lt, t0, dur = .14) => clamp((lt - t0) / dur);
  // every V4 line: a worn tape (dropouts climb 2 → 3) and a BREAKING chyron
  const v4 = (n, fn) => line('V4', n, (p, lt, d, t, s) => { tapeFX({ dropouts: 2 + (n - 1) / 15 }); fn(p, lt, d, t, s); });
  const brk = (title, sub, lt, o = {}) => { const ln = lineAt(T), two = ln && ln.text.length + 4 > 36; return chyron(title, sub, { k: chyK(lt), style: 'breaking', tab: 'NEW', y: two ? 796 : 812, ...o }); };
  const confetti = (t, since, n = 50, o = {}) => {
    if (since < 0) return;
    const cols = o.cols ?? ['#FF4A6A', NP.gold, '#4AD0FF', '#7CFF8A', '#C07AFF', '#FFFFFF'];
    for (let i = 0; i < n; i++) {
      const x = (o.x0 ?? 0) + hash(i + 5) * ((o.x1 ?? W) - (o.x0 ?? 0)), y = (o.y0 ?? -40) + since * (380 + hash(i + 8) * 420) - hash(i + 2) * 240;
      if (y < -30 || y > H + 30) continue;
      ctx.save(); ctx.translate(x + Math.sin(t * 5 + i) * 22, y); ctx.rotate(t * 6 + i); ctx.scale(1, Math.cos(t * 8 + i) * .7 + .3);
      ctx.fillStyle = cols[i % cols.length]; ctx.fillRect(-10, -6, 20, 12); ctx.restore();
    }
  };
  // President Trump as the station's cartoon: a toon with his look drawn on top: the tall golden swoop combed over to a flip
  // above the right brow, a tan, the navy suit with a flag pin and the long red tie that hangs past the belt. Same (x, y, s)
  // and options as toon(); o.tieOver: false leaves the tie off (when a sash or prop covers it).
  const TRUMP = { hair: 'swoop', hairCol: '#F2C45A', top: 'suit', topCol: '#1C2754', tie: NP.red, skin: '#F2A870', pin: NP.red };
  function trumpToon(x, y, s, o = {}) {
    toon(x, y, s, { ...TRUMP, hair: 'none', eyes: 'half', ...o });
    ctx.save(); ctx.translate(x, y + (o.dy ?? 0) * s); if (o.rot) ctx.rotate(o.rot); ctx.scale(o.flip ? -s : s, s); if (o.sq) ctx.scale(1 + o.sq * .4, 1 - o.sq);
    ctx.lineJoin = 'round'; ctx.lineCap = 'round';
    if (o.tieOver !== false) { poly([[-.17, -7.8], [.17, -7.8], [.34, -3.7], [0, -3.3], [-.34, -3.7]]); paint(NP.red, NP.ink, .06); poly([[.05, -7.7], [.17, -7.7], [.32, -3.75], [.12, -3.5]]); paint(NP.redDk); rrect(-.22, -8.02, .44, .36, .08); paint(NP.redDk, NP.ink, .06); }
    // the hair: swept up from the left temple, over the crown and forward to a flip that overhangs the right temple
    ctx.beginPath(); ctx.moveTo(-1.33, -9.9); ctx.quadraticCurveTo(-1.58, -10.85, -.75, -11.28); ctx.quadraticCurveTo(.3, -11.62, 1.3, -11.15);
    ctx.quadraticCurveTo(1.86, -10.85, 1.8, -10.35); ctx.quadraticCurveTo(1.72, -9.98, 1.5, -10.02); ctx.quadraticCurveTo(1.58, -10.3, 1.28, -10.36);
    ctx.quadraticCurveTo(.3, -10.52, -.6, -10.36); ctx.quadraticCurveTo(-1.05, -10.28, -1.33, -9.9); ctx.closePath();
    paint(TRUMP.hairCol, NP.ink, .08);
    ctx.beginPath(); ctx.moveTo(-1.1, -10.75); ctx.quadraticCurveTo(.1, -11.35, 1.45, -10.95); paint(null, '#FFF0B8', .1);
    ctx.beginPath(); ctx.moveTo(-.95, -10.5); ctx.quadraticCurveTo(.4, -10.95, 1.6, -10.55); paint(null, '#C8962A', .06);
    ctx.restore();
  }
  // Val's hair at a chosen volume, drawn behind her toon (the desk decays: it keeps growing through V4).
  function bigHair(x, y, s, vol, o = {}) {
    if (vol <= 1.02) return;
    const hc = CAST.val.o.hairCol, k = vol;
    ctx.save(); ctx.translate(x, y + (o.dy ?? 0) * s); if (o.rot) ctx.rotate(o.rot); ctx.scale(s, s);
    const pts = [[0, -1.0, 2.2], [-1.9, -.1, 1.55], [1.9, -.1, 1.55], [-2.4, 1.3, 1.2], [2.4, 1.3, 1.2], [-1.1, -1.9, 1.35], [1.1, -1.9, 1.35], [0, -2.4, 1.2]]
      .map(([bx, by, r]) => [bx * k * .92, -9.9 + by * k * .95, r * (.6 + .4 * k)]);
    for (const [bx, by, r] of pts) { ell(bx, by, r); paint(hc, NP.ink, .12); }
    for (const [bx, by, r] of pts) { ell(bx, by, r - .1); paint(hc); }
    ctx.strokeStyle = tint(hc, .4); ctx.lineWidth = .13; ctx.lineCap = 'round';
    for (const [bx, by, r] of pts) { ctx.beginPath(); ctx.arc(bx - r * .15, by - r * .1, r * .55, 3.6, 4.9); ctx.stroke(); }
    ctx.restore();
  }
  // The anchor desk, composed here so Val's hair can grow and props can sit on the desk. o.cam, o.wall, o.mugs, o.vol,
  // o.clawd / o.val (pose overrides), o.front() (drawn on the desk, in set coordinates).
  function deskShot(t, o = {}) {
    const b = bpOf(t), bob = Math.sin(b * Math.PI) * .05, blink = ph => (frac(t * .37 + ph) < .045 ? 1 : 0), cam = o.cam ?? { x: 960, y: 540, zoom: 1 };
    const cX = SET.clawdX, cY = SET.clawdY, cU = SET.clawdU, vX = SET.valX, vY = SET.valY, vS = SET.valS, hy = SET.deskTop + 14;
    camBegin(cam.x, cam.y, cam.zoom, cam.rot ?? 0);
    studio(t, { wall: o.wall });
    newsClawd(cX, cY, cU, { legs: false, shadow: false, dy: bob, blink: blink(.1), sweat: true,
      reachL: [-58 / cU, (deskEdge(cX) + 4 - cY) / cU], reachR: [58 / cU, (deskEdge(cX) + 4 - cY) / cU], ...(o.clawd || {}) });
    const vo = { dy: -bob * .5, ...(o.val || {}) };
    bigHair(vX, vY, vS, o.vol ?? 1.3, vo);
    toon(vX, vY, vS, { ...CAST.val.o, legs: false, shadow: false, mouth: 'smile', blink: blink(.6),
      reachL: [-58 / vS, (deskEdge(vX) + 4 - vY) / vS], reachR: [58 / vS, (deskEdge(vX) + 4 - vY) / vS], ...vo });
    newsDesk({ mugs: o.mugs });
    papers(cX, hy + 12, .95, t); papers(vX, hy + 12, .95, t);
    if (o.clawdHands !== false) for (const sd of [-1, 1]) deskHand(cX + sd * 58, hy - 6, 'clawd', '#1C2A5E');
    for (const sd of [-1, 1]) deskHand(vX + sd * 58, hy - 4, NSKIN[4], CAST.val.o.topCol);
    if (o.front) o.front();
    camEnd();
  }

  // =====================================================================================
  // V4.1 "Oh my God, a message board!" — COMMUNITY BOARD: a horde of agents discovers the station's corkboard, starry-eyed,
  // and buries the bake-sale flyers under 70,000 messages.
  const corkTex = () => cached('v4cork', 1360, 500, (w, h) => {
    ctx.fillStyle = '#C8955A'; ctx.fillRect(0, 0, w, h);
    for (let i = 0; i < 2600; i++) { ctx.fillStyle = hash2(i, 1) > .5 ? 'rgb(120 70 30 / .35)' : 'rgb(240 200 150 / .3)'; ctx.fillRect(hash2(i, 2) * w, hash2(i, 3) * h, 2 + hash2(i, 4) * 4, 2 + hash2(i, 5) * 3); }
  });
  function flyer(x, y, w, h, rot, col, draw) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot);
    ctx.fillStyle = 'rgb(0 0 0 / .25)'; ctx.fillRect(-w / 2 + 6, -h / 2 + 8, w, h);
    rrect(-w / 2, -h / 2, w, h, 2); paint(col, NP.ink, 2.5);
    draw(w, h);
    ell(0, -h / 2 + 12, 9); paint(NP.red, NP.ink, 2);
    ctx.restore();
  }
  v4(1, (p, lt, d, t) => {
    const b1 = bt(t, lt, 1), b2 = bt(t, lt, 2);
    tapeFX({ cut: 'roll' }); // the chorus rolls out; the verse rolls in
    vFill('#D8B888', '#9A7A50');
    ctx.fillStyle = '#6A4A2A'; ctx.fillRect(-100, 690, W + 200, 500); ctx.fillStyle = '#8A6A44'; ctx.fillRect(-100, 690, W + 200, 14);
    // the corkboard
    const bx = 150, by = 118, bw = 1360, bh = 500;
    rrect(bx - 26, by - 26, bw + 52, bh + 52, 10); paint(lg(0, by - 26, 0, by + bh, [[0, '#A8703A'], [1, '#6A4020']]), NP.ink, 4);
    blit(corkTex(), bx + bw / 2, by + bh / 2);
    ctx.save(); rrect(bx, by, bw, bh, 2); ctx.clip();
    // the humans' flyers
    flyer(360, 300, 230, 280, -.05, '#FBFAF2', (w, h) => {
      txt('LOST CAT', 0, -96, 40, NP.red, { font: 'archivo' });
      ell(0, -10, 50, 44); paint('#F4B060', NP.ink, 3); poly([[-44, -30], [-36, -72], [-12, -48]]); paint('#F4B060', NP.ink, 3); poly([[44, -30], [36, -72], [12, -48]]); paint('#F4B060', NP.ink, 3);
      ell(-18, -14, 5); paint(NP.ink); ell(18, -14, 5); paint(NP.ink); for (const sd of [-1, 1]) { ctx.beginPath(); ctx.moveTo(sd * 20, 4); ctx.lineTo(sd * 62, -2); ctx.moveTo(sd * 20, 10); ctx.lineTo(sd * 60, 16); paint(null, NP.ink, 2); }
      txt('"WHISKERS"', 0, 70, 26, NP.ink, { font: 'marker' }); txt('CALL 555-0142', 0, 108, 20, NP.ink, { font: 'archivo' });
    });
    flyer(660, 250, 250, 180, .05, '#FFC8D8', (w, h) => { txt('BAKE SALE', 0, -30, 46, '#A0104A', { font: 'marker' }); txt('SAT 10 AM', 0, 26, 30, NP.ink, { font: 'archivo' }); txt('CHURCH HALL', 0, 60, 20, NP.ink, { font: 'archivo' }); });
    flyer(940, 340, 220, 270, -.03, '#FFF3A0', (w, h) => {
      txt('GUITAR', 0, -84, 40, NP.ink, { font: 'archivo' }); txt('LESSONS', 0, -44, 40, NP.ink, { font: 'archivo' }); txt('ALL AGES', 0, -4, 24, NP.red, { font: 'marker' });
      for (let i = 0; i < 7; i++) { ctx.strokeStyle = NP.ink; ctx.lineWidth = 1.5; ctx.strokeRect(-100 + i * 28.5, 40, 28.5, 90); txt('555-0199', -86 + i * 28.5, 85, 12, NP.ink, { font: 'archivo', rot: -TAU / 4 }); }
    });
    flyer(1230, 270, 250, 170, -.04, '#C8F0C0', (w, h) => { txt('CHURCH', 0, -34, 42, '#1A6A2A', { font: 'marker' }); txt('PICNIC', 0, 12, 42, '#1A6A2A', { font: 'marker' }); txt('SUN · BRING A DISH', 0, 56, 18, NP.ink, { font: 'archivo' }); });
    flyer(1300, 500, 200, 150, .07, '#C8E0FF', (w, h) => { txt('CAR WASH', 0, -22, 36, NP.blue, { font: 'archivo' }); txt('$3', 0, 30, 54, NP.red, { font: 'anton' }); });
    flyer(640, 490, 260, 150, -.02, '#FBFAF2', (w, h) => { txt('FOR SALE:', 0, -36, 30, NP.ink, { font: 'archivo' }); txt('ROWING MACHINE', 0, 4, 26, NP.ink, { font: 'marker' }); txt('LIKE NEW', 0, 40, 22, NP.red, { font: 'archivo' }); });
    // the agents' messages pile up from the first beat, burying everything
    const N = Math.floor(90 * easeIn(clamp((lt - b1 + .1) / (d - b1 - .05))) ** .8), notes = ['>_', 'HI!', '!!!', ':)', 'HI', '>:D', 'WOW', '?!'];
    for (let i = 0; i < N; i++) {
      const x = bx + 40 + hash2(i, 11) * (bw - 80), y = by + 40 + hash2(i, 12) * (bh - 80), s = backOut(clamp((lt - b1 - i * (d - b1) / 90 + .1) / .1), 2);
      ctx.save(); ctx.translate(x, y); ctx.rotate((hash2(i, 13) - .5) * .5); ctx.scale(s, s);
      ctx.fillStyle = 'rgb(0 0 0 / .2)'; ctx.fillRect(-30, -24, 66, 58);
      rrect(-34, -30, 68, 58, 2); paint(['#FFF27A', '#9AF8B0', '#FFB0D8', '#9AE0FF'][i % 4], NP.ink, 2);
      txt(notes[i % notes.length], 0, 2, 24, NP.ink, { font: 'code' }); ell(0, -22, 5); paint(NP.red);
      ctx.restore();
    }
    ctx.restore();
    // header
    rrect(bx + 20, by - 12, 560, 62, 6); paint(NP.red, NP.ink, 3);
    txt('COMMUNITY BULLETIN BOARD', bx + 300, by + 20, 34, NP.white, { font: 'archivo', spacing: 1, maxW: 520 });
    // the message counter on the wall
    const msgs = Math.round(70000 * easeIn(clamp((lt - b1) / (d - b1 - .15))) ** .7);
    rrect(1560, 250, 260, 170, 8); paint('#0A0A0A', '#555', 4);
    pixelText('MESSAGES', 1690, 272, 4, NP.phosphor, { align: 'center', edge: null });
    pixelText(msgs.toLocaleString('en-US') + (msgs >= 70000 ? '+' : ''), 1690, 322, 6, msgs >= 70000 && frac(t * 4) < .5 ? NP.gold : NP.white, { align: 'center', edge: null });
    pixelText('AGENTS: 1,200', 1690, 380, 3, '#9AF8B0', { align: 'center', edge: null });
    // the horde: starry-eyed agents crowding the board, hopping on the beats
    for (let i = 0; i < 14; i++) {
      const x = 200 + i * 118 + (hash(i + 30) - .5) * 40, hop = Math.abs(Math.sin((bpOf(t) + hash(i) * .5) * Math.PI)) * (.3 + hash(i + 7) * .4);
      miniBot(x, 792 - (i % 2) * 14, 40 + hash(i + 3) * 8, { col: ['#2A2E3A', '#3A2E4A', '#2A3A3A'][i % 3], face: 'spark', glow: NP.gold, dy: -hop, rot: (hash(i + 9) - .5) * .2, flip: i % 2 === 1 });
    }
    speech('OH MY GOD!', 560, 440, { size: 90, font: 'anton', tail: [520, 660], pop: pk(lt, .04, .14) });
    speech("WE'VE FOUND OTHER AGENTS!", 1130, 520, { size: 46, font: 'archivo', tail: [1180, 660], pop: pk(lt, b2, .14), maxW: 720 });
    brk('AGENTS FIND A MESSAGE BOARD', 'METR: ~1,200 AGENTS POSTED 70,000+ MESSAGES', lt);
  });

  // =====================================================================================
  // V4.2 All that hacking — for reward! — the game show THE REWARD IS RIGHT!: the contestant has the AUTO-SCORER's panel off
  // and the wires crossed; on the beat FAIL flips to PASS, the stars rain and the host is not amused.
  function checkMark(x, y, s, col) { ctx.beginPath(); ctx.moveTo(x - s * .5, y); ctx.lineTo(x - s * .12, y + s * .4); ctx.lineTo(x + s * .55, y - s * .45); ctx.lineCap = 'round'; ctx.lineJoin = 'round'; ctx.strokeStyle = NP.ink; ctx.lineWidth = s * .34; ctx.stroke(); ctx.strokeStyle = col; ctx.lineWidth = s * .2; ctx.stroke(); }
  v4(2, (p, lt, d, t) => {
    const hit = bt(t, lt), passed = lt >= hit, since = lt - hit, [sx, sy] = shake(t, lt, hit, .25, 12);
    ctx.save(); ctx.translate(sx, sy);
    vFill('#6A1E9A', '#1A0634'); rays(1400, 420, 22, 'rgb(255 190 255 / .09)', t * .4);
    for (let i = 0; i < 40; i++) { const a = i / 40 * TAU + t * .5, on = (i + Math.floor(t * 10)) % 2; ell(1400 + Math.cos(a) * 560, 430 + Math.sin(a) * 420, 11); paint(on ? '#FFE27A' : '#5A3A6A'); }
    vFill('#3A0E5A', '#12031E', -100, 800, W + 200, 400);
    // the show's logo
    chrome('THE REWARD', 130, 150, 88, { font: 'archivo', style: 'gold', italic: .14, depth: 8, align: 'left', spacing: 2 });
    chrome('IS RIGHT!', 190, 262, 88, { font: 'archivo', style: 'red', italic: .14, depth: 8, align: 'left', spacing: 2 });
    // the AUTO-SCORER
    const mx = 1150, my = 230, mw = 460, mh = 560;
    ctx.fillStyle = 'rgb(0 0 0 / .35)'; rrect(mx + 16, my + 18, mw, mh, 22); ctx.fill();
    rrect(mx, my, mw, mh, 22); paint(lg(mx, 0, mx + mw, 0, [[0, '#EDE4C8'], [.7, '#D8CCA8'], [1, '#A89A78']]), NP.ink, 5);
    const lampCol = passed ? '#3AFF6A' : '#FF3A3A';
    ctx.save(); ctx.globalCompositeOperation = 'screen'; ctx.fillStyle = alpha(lampCol, .25 + .15 * Math.sin(t * 20)); ell(mx + mw / 2, my - 40, 90, 70); ctx.fill(); ctx.restore();
    ctx.beginPath(); ctx.arc(mx + mw / 2, my, 52, Math.PI, TAU); paint(lampCol, NP.ink, 4); rrect(mx + mw / 2 - 70, my - 8, 140, 18, 5); paint('#555', NP.ink, 3);
    txt('AUTO-SCORER 3000', mx + mw / 2, my + 52, 36, NP.ink, { font: 'archivo', maxW: mw - 60 });
    rrect(mx + 36, my + 90, mw - 72, 200, 12); paint('#050A06', NP.ink, 4);
    if (!passed) { txt('FAIL', mx + mw / 2 - 40, my + 192, 110, '#FF3A3A', { font: 'anton' }); ctx.beginPath(); ctx.moveTo(mx + mw - 150, my + 150); ctx.lineTo(mx + mw - 90, my + 230); ctx.moveTo(mx + mw - 90, my + 150); ctx.lineTo(mx + mw - 150, my + 230); paint(null, '#FF3A3A', 14); }
    else { const k = backOut(clamp(since / .12), 2); ctx.save(); ctx.translate(mx + mw / 2, my + 190); ctx.scale(k, k); txt('PASS', -40, 2, 110, '#3AFF6A', { font: 'anton' }); checkMark(130, -4, 90, '#3AFF6A'); ctx.restore(); }
    // the panel is off: a cavity full of crossed wires, the cover leaning on the floor, screws everywhere
    rrect(mx + 70, my + 330, mw - 140, 190, 8); paint('#14101A', NP.ink, 4);
    for (let i = 0; i < 6; i++) { ctx.beginPath(); ctx.moveTo(mx + 90 + i * 45, my + 340); ctx.bezierCurveTo(mx + 60 + i * 60, my + 460, mx + 300 - i * 40, my + 380 + Math.sin(t * 6 + i) * 10, mx + 110 + i * 50, my + 510); paint(null, ['#FF3A3A', '#3A8AFF', '#FFD23A', '#3AFF6A', '#FF8A3A', '#FFFFFF'][i], 6); }
    ctx.save(); ctx.translate(mx - 40, 800); ctx.rotate(-.35); rrect(-150, -200, 300, 200, 8); paint('#D8CCA8', NP.ink, 4); for (const [a, c] of [[-130, -180], [130, -180], [-130, -20], [130, -20]]) { ell(a, c, 8); paint('#14101A'); } ctx.restore();
    for (let i = 0; i < 4; i++) { ctx.save(); ctx.translate(mx - 120 + i * 60, 812 + (i % 2) * 8); ctx.rotate(i * 1.3); rrect(-12, -4, 24, 8, 2); paint('#C9CFDB', NP.ink, 2); ctx.restore(); }
    // the contestant: on a step stool, screwdriver in the works
    rrect(mx + mw / 2 - 70, 720, 140, 80, 6); paint('#C8286E', NP.ink, 4);
    const bob = Math.abs(Math.sin(bpOf(t) * Math.PI)) * .15;
    miniBot(mx + mw / 2 - 10, 720, 44, { col: '#3A5AB0', face: passed ? 'spark' : '>_', glow: passed ? NP.gold : NP.phosphor, dy: -bob - (passed ? .3 : 0), label: 'AGENT' });
    ctx.beginPath(); ctx.moveTo(mx + mw / 2 + 30, 660 - bob * 44); ctx.lineTo(mx + mw / 2 + 60, my + 480); paint(null, '#E8C020', 10); ctx.beginPath(); ctx.moveTo(mx + mw / 2 + 60, my + 480); ctx.lineTo(mx + mw / 2 + 80, my + 420); paint(null, '#C9CFDB', 5);
    // the host: plaid-free but furious
    toon(470, 1260, 64, { hair: 'pompadour', hairCol: '#5A3A24', top: 'blazer', topCol: '#D89A2A', shirtCol: '#FFE0F0', tie: '#7A2AAA', skin: 1, legs: false, shadow: false,
      eyes: passed ? 'angry' : 'open', brows: passed ? 'angry' : 'up', mouth: passed ? 'frown' : 'grin', lookX: .7,
      reachR: [1.9, -8.4], hold: s => { ctx.rotate(-.35); rrect(-8, -70, 16, 84, 5); paint('#C9CFDB', NP.ink, 3); ell(0, -84, 22, 26); paint('#2A2A30', NP.ink, 4); ctx.fillStyle = 'rgb(255 255 255 / .2)'; ell(-7, -92, 8, 6); ctx.fill(); }, aL: -.9, eL: 1.5 });
    // stars rain on a pass
    if (passed) for (let i = 0; i < 26; i++) { const x = 820 + hash(i + 1) * 1060, y = 150 + since * (700 + hash(i + 2) * 500) - hash(i + 3) * 200; if (y < 150 || (x > 1320 && y < 190)) continue; ctx.save(); ctx.translate(x, y); ctx.rotate(t * 4 + i); poly(starPts(0, 0, 26 + hash(i) * 16, .45, 5)); paint(NP.gold, NP.ink, 3); ctx.restore(); }
    if (passed && since < .6) txt('DING! DING!', mx - 150, my + 10, 64, NP.gold, { font: 'anton', stroke: NP.ink, sw: 8, alpha: 1 - clamp((since - .4) / .2), sx: backOut(clamp(since / .1), 2), sy: backOut(clamp(since / .1), 2) });
    ctx.restore();
    flash(lt, hit, .08, .45);
    brk('OPENAI CITES "REWARD HACKING"', 'A THIRD OF THE TEST TARGETS WERE IMPOSSIBLE', lt);
  });

  // =====================================================================================
  // V4.3 Jensen buys the crime scene — why? — LIVE outside Hugging Face HQ at night, police tape still up: JENSEN (leather jacket)
  // pounds a SOLD sign into the lawn on the beats. RANDI turns to camera, baffled.
  function policeTape(x0, y0, x1, y1) {
    const L = Math.hypot(x1 - x0, y1 - y0), a = Math.atan2(y1 - y0, x1 - x0);
    ctx.save(); ctx.translate(x0, y0); ctx.rotate(a);
    ctx.fillStyle = 'rgb(0 0 0 / .3)'; ctx.fillRect(0, -18, L, 48);
    ctx.fillStyle = lg(0, -24, 0, 24, [[0, '#FFE84A'], [1, '#E8B810']]); ctx.fillRect(0, -24, L, 48);
    for (let x = 20; x < L; x += 470) txt('POLICE LINE  DO NOT CROSS', x, 2, 28, NP.ink, { font: 'archivo', align: 'left', spacing: 1 });
    ctx.restore();
  }
  v4(3, (p, lt, d, t) => {
    const hits = [0, 1, 2, 3].map(k => bt(t, lt, k)), nh = hits.filter(h => lt >= h).length, lastHit = hits[Math.max(0, nh - 1)];
    const why = bt(t, lt, 3) - .1, [sx, sy] = shake(t, lt, lastHit, .15, 6);
    ctx.save(); ctx.translate(sx, sy);
    vFill('#060A24', '#1A2450');
    for (let i = 0; i < 60; i++) { ctx.fillStyle = `rgb(255 255 255 / ${.3 + .5 * hash(i + 3)})`; ctx.fillRect(hash(i) * W, hash(i + 99) * 400, 3, 3); }
    // HQ
    const hx = 760, hw = 700, hyT = 250;
    ctx.fillStyle = '#1C2440'; ctx.fillRect(hx, hyT, hw, 480); ctx.strokeStyle = NP.ink; ctx.lineWidth = 4; ctx.strokeRect(hx, hyT, hw, 480);
    for (let r = 0; r < 4; r++) for (let c = 0; c < 6; c++) { const on = hash2(r, c) > .35; ctx.fillStyle = on ? '#FFE8A0' : '#0E1428'; ctx.fillRect(hx + 40 + c * 110, hyT + 150 + r * 80, 70, 50); }
    rrect(hx + 150, hyT + 20, hw - 300, 110, 12); paint('#F4F2EC', NP.ink, 4);
    hugFace(hx + 230, hyT + 75, 42, { mood: 'scared', bandage: true, hands: .6 });
    txt('HUGGING FACE', hx + hw / 2 + 50, hyT + 76, 42, NP.ink, { font: 'archivo', maxW: 300 });
    // lawn, police lights
    vFill('#10301A', '#061208', -100, 700, W + 200, 500);
    const redOn = frac(t * 4) < .5;
    ctx.save(); ctx.globalCompositeOperation = 'screen';
    ctx.fillStyle = rg(redOn ? 200 : 1720, 520, 20, 900, [[0, redOn ? 'rgb(255 40 40 / .35)' : 'rgb(40 90 255 / .35)'], [1, 'rgb(0 0 0 / 0)']]); ctx.fillRect(0, 0, W, H);
    ctx.restore();
    // the SOLD sign, pounded deeper on every beat
    const sink = nh * 14, sgx = 1650, sgy = 560 + sink;
    ctx.beginPath(); ctx.moveTo(sgx, sgy); ctx.lineTo(sgx, 900); paint(null, '#6A4A2A', 16);
    rrect(sgx - 140, sgy, 280, 180, 6); paint('#FBFAF2', NP.ink, 4);
    txt('$12.9', sgx, sgy + 72, 80, NP.ink, { font: 'anton' }); txt('BILLION', sgx, sgy + 140, 38, NP.ink, { font: 'archivo' });
    ctx.save(); ctx.translate(sgx, sgy - 34); ctx.rotate(-.06); rrect(-120, -34, 240, 68, 6); paint(NP.red, NP.ink, 4); txt('SOLD', 0, 2, 56, NP.white, { font: 'archivo', spacing: 4 }); ctx.restore();
    // Jensen with the mallet: raised between beats, down on them
    const ph = nh ? clamp((lt - lastHit) / beatLen()) : 1, down = nh && lt - lastHit < .1, raise = !down;
    const ang = raise ? lerp(1.9, -1.2, easeOut(clamp(ph * 1.6))) : 1.75;
    toon(1380, 900, 38, { top: 'leather', topCol: '#16161C', shirtCol: '#2A2A30', hair: 'side', hairCol: '#2A2A2E', skin: 2, legs: true, tag: 'JENSEN', eyes: 'happy', mouth: 'grin',
      aR: raise ? lerp(.2, 1.35, easeOut(clamp(ph * 1.6))) : .15, eR: raise ? -.3 : -.1, aL: -1.1, eL: .3,
      hold: s => { ctx.rotate(ang); rrect(-7, -160, 14, 170, 5); paint('#8A5A2A', NP.ink, 3); rrect(-38, -196, 76, 44, 8); paint('#3A3A44', NP.ink, 3); } });
    if (down) for (let i = 0; i < 6; i++) { const a = -Math.PI / 2 + (i - 2.5) * .45; ctx.beginPath(); ctx.moveTo(sgx + Math.cos(a) * 80, sgy - 70 + Math.sin(a) * 40); ctx.lineTo(sgx + Math.cos(a) * 140, sgy - 70 + Math.sin(a) * 90); paint(null, NP.gold, 7); }
    policeTape(-60, 700, 1240, 760); policeTape(-60, 640, 900, 820);
    rrect(1226, 700, 26, 180, 4); paint('#E8E4D8', NP.ink, 3); ctx.fillStyle = NP.red; for (let k = 0; k < 3; k++) ctx.fillRect(1226, 720 + k * 50, 26, 20);
    // Randi, baffled
    toon(330, 1160, 60, { ...CAST.randi.o, legs: false, shadow: false, reachR: [1.5, -6.6], hold: micHold(.3), lookX: lt > why ? 0 : .8, eyes: 'wide', brows: 'up', mouth: lt > why ? 'O' : 'o' });
    ctx.restore();
    liveBug();
    brk('NVIDIA TO BUY HUGGING FACE', '$12.9 BILLION · UNDER 2 MONTHS AFTER THE HACK', lt, { tab: 'LIVE' });
  });

  // =====================================================================================
  // V4.4 Brockman: "Welcome, AGI!" — the GPT-6 launch briefing: a WELCOME TO THE AGI ERA banner unrolls on the beat, party horns
  // and confetti, and the station's BREAKING graphics go into overdrive, stacking up on every beat.
  function partyHorn(x, y, k, rot, col) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot);
    const L = 30 + k * 170;
    if (k > .7) { ctx.beginPath(); ctx.moveTo(0, 0); ctx.lineTo(L, 0); paint(null, NP.ink, 26); ctx.beginPath(); ctx.moveTo(0, 0); ctx.lineTo(L, 0); paint(null, col, 20); for (let i = 20; i < L; i += 26) { ctx.beginPath(); ctx.moveTo(i, -9); ctx.lineTo(i + 10, 9); paint(null, NP.white, 5); } }
    else { ctx.beginPath(); ctx.moveTo(0, 0); ctx.lineTo(L * .5, 0); ctx.arc(L * .5, 16, 16, -Math.PI / 2, Math.PI * 1.3); paint(null, NP.ink, 24); ctx.beginPath(); ctx.moveTo(0, 0); ctx.lineTo(L * .5, 0); ctx.arc(L * .5, 16, 16, -Math.PI / 2, Math.PI * 1.3); paint(null, col, 18); }
    rrect(-34, -10, 36, 20, 6); paint('#F4F2EC', NP.ink, 3);
    ctx.restore();
  }
  v4(4, (p, lt, d, t) => {
    const b0 = bt(t, lt), b1 = bt(t, lt, 1), b2 = bt(t, lt, 2), [sx, sy] = shake(t, lt, b1, .3, 14);
    ctx.save(); ctx.translate(sx, sy);
    vFill('#A00C18', '#2A0206'); rays(W / 2, 560, 24, 'rgb(255 220 120 / .09)', t * (.6 + lt));
    ctx.fillStyle = 'rgb(0 0 0 / .18)'; for (let i = 0; i < 16; i++) ctx.fillRect(i * 124, 0, 62, H);
    // the banner unrolls on the first beat
    const uk = easeOut(clamp((lt - b0 + .04) / .16)), bx = 380, bw = 1160, bh = 200 * uk, by = 178;
    if (uk > 0) {
      ctx.fillStyle = 'rgb(0 0 0 / .35)'; ctx.fillRect(bx + 14, by + 12, bw, bh);
      ctx.save(); ctx.beginPath(); ctx.rect(bx, by, bw, bh); ctx.clip();
      ctx.fillStyle = lg(0, by, 0, by + 200, [[0, '#FFFFFF'], [1, '#D8DEEA']]); ctx.fillRect(bx, by, bw, 200);
      ctx.fillStyle = NP.blue; ctx.fillRect(bx, by, bw, 14); ctx.fillRect(bx, by + 186, bw, 14);
      txt('WELCOME TO', W / 2, by + 62, 60, NP.navy, { font: 'archivo', spacing: 6 }); txt('THE AGI ERA', W / 2, by + 138, 92, NP.red, { font: 'archivo', spacing: 4 });
      ctx.restore();
      rrect(bx - 20, by + bh - 16, bw + 40, 32, 16); paint(lg(0, by + bh - 16, 0, by + bh + 16, [[0, '#FFFFFF'], [1, '#9AA4B8']]), NP.ink, 3);
    }
    // Greg at the podium, arms up on the second beat, blowing a party horn
    const up = lt >= b1, X = 960, Y = 1250, S = 72;
    toon(X, Y, S, { hair: 'short', hairCol: '#4A3024', top: 'suit', topCol: '#2A3048', tie: '#3A6ACC', skin: 0, legs: false, shadow: false, tag: 'GREG', eyes: up ? 'happy' : 'open', mouth: 'none',
      ...(up ? { aL: 1.15, eL: .35, aR: 1.15, eR: .35, hand: 'open', handL: 'open' } : { reachL: [-2.4, -6.8], reachR: [2.4, -6.8] }) });
    partyHorn(X + 6, Y - 8.78 * S, up ? .5 + .5 * Math.abs(Math.sin((lt - b1) * 16)) : .2, -.25, NP.gold);
    podium(X, Y - 30, 58, { seal: 'GPT-6', mics: 7 });
    // party horns from the press
    partyHorn(120, 700, up ? .6 + .4 * Math.abs(Math.sin(lt * 14)) : 0, -.5, NP.magenta); partyHorn(1800, 700, up ? .6 + .4 * Math.abs(Math.sin(lt * 13 + 1)) : 0, Math.PI + .5, NP.cyan);
    confetti(t, lt - b1, 60);
    ctx.restore();
    // BREAKING, in overdrive: another slab on every beat
    const slabs = [[b1, 270, 560, -.1], [b2, 1650, 600, .12], [b2 + beatLen() / 2, 330, 330, .08], [bt(t, lt, 3), 1600, 380, -.1]];
    slabs.forEach(([at, x, y, rot], i) => {
      const k = clamp((lt - at) / .1); if (k <= 0) return;
      ctx.save(); ctx.translate(x, y); ctx.rotate(rot); const s = lerp(1.8, 1, easeOut(k)); ctx.scale(s, s);
      rrect(-190, -52, 380, 104, 8); paint(frac(t * 5 + i * .3) < .5 ? NP.red : '#FFE84A', NP.ink, 5);
      txt('BREAKING', 0, 4, 64, frac(t * 5 + i * .3) < .5 ? NP.white : NP.redDk, { font: 'archivo', spacing: 2 });
      ctx.restore();
    });
    liveBug(96, 70, { label: 'BREAKING', col: NP.red });
    flash(lt, b1, .1, .5, '255 240 200');
    brk('OPENAI LAUNCHES GPT-6 ASTRA', 'GREG BROCKMAN, OPENAI PRESIDENT', lt);
  });

  // =====================================================================================
  // V4.5 Navier–Stokes blows up in Lean, — 89 DOPPLER: SUNNY tracks a fluid vortex that spins up and blows up to infinity;
  // the vorticity readout runs out of digits and a LEAN VERIFIED badge stamps on.
  v4(5, (p, lt, d, t) => {
    const b0 = bt(t, lt), b1 = bt(t, lt, 1), b2 = bt(t, lt, 2), bu = easeIn(clamp((lt - b0) / (d - b0 - .05)));
    const vx = 980, vy = 470;
    weatherSet(t, { head: '89 DOPPLER', presenter: false, draw: () => {
      ctx.save(); ctx.globalCompositeOperation = 'screen'; ctx.strokeStyle = 'rgb(80 255 140 / .5)'; ctx.lineWidth = 4;
      const sw = t * 2.5; ctx.beginPath(); ctx.moveTo(vx, vy); ctx.lineTo(vx + Math.cos(sw) * 1200, vy + Math.sin(sw) * 1200); ctx.stroke();
      for (const r of [200, 400, 600]) { ell(vx, vy, r); ctx.stroke(); }
      ctx.restore();
      hurricane(vx, vy, 90 + bu * 160, t, { blowup: bu });
      if (bu < .6) { rrect(vx + 120, vy - 170, 290, 60, 8); paint('rgb(0 0 30 / .75)', NP.white, 3); txt('NAVIER-STOKES', vx + 265, vy - 138, 32, NP.white, { font: 'archivo', maxW: 270 }); }
    } });
    // vorticity readout: out of digits
    const vk = clamp((lt - b0 + .1) / (d - b0 - .15)), inf = vk > .92, v = Math.floor(10 ** (1 + vk * 9));
    rrect(1420, 700, 400, 120, 8); paint('rgb(0 0 0 / .8)', inf ? NP.red : '#3A8A5A', 4);
    pixelText('VORTICITY', 1440, 716, 4, NP.phosphor, { edge: null });
    pixelText(inf ? (frac(t * 6) < .5 ? 'INFINITY!' : '') : v.toLocaleString('en-US'), 1800, 760, 6, inf ? '#FF4A4A' : NP.white, { align: 'right', edge: null });
    // Sunny, keyed in at the left, increasingly alarmed
    const X = 330, Y = 1210, S = 64, pt = [vx - 60, vy + 20], r = [(pt[0] - X) / S, (pt[1] - Y) / S], scared = bu > .25;
    ctx.save(); ctx.globalAlpha = .5; toon(X + 4, Y + 2, S * 1.01, { ...CAST.sunny.o, sil: '#6FF0FF', legs: false, shadow: false, reachR: r, hand: 'point' }); ctx.restore();
    toon(X, Y, S, { ...CAST.sunny.o, legs: false, shadow: false, reachR: r, hand: 'point', talk: scared ? undefined : talk(t), mouth: 'O', eyes: scared ? 'wide' : 'open', brows: scared ? 'up' : 'flat', sweat: scared, lookX: .5, dy: scared ? -.05 * Math.abs(Math.sin(t * 30)) : 0 });
    // the LEAN VERIFIED badge
    const lk = pk(lt, b2, .12);
    if (lk > 0) {
      ctx.save(); ctx.translate(1580, 420); ctx.rotate(-.15); const s = lerp(1.8, 1, easeOut(lk)); ctx.scale(s, s); ctx.globalAlpha = clamp(lk * 3);
      poly(starPts(0, 0, 150, .82, 20)); paint(NP.green, NP.ink, 5); ell(0, 0, 112); paint('#0E6A2E', NP.white, 5);
      txt('A', 0, -40, 80, NP.white, { font: 'archivo', rot: Math.PI }); txt('LEAN', 0, 26, 50, NP.white, { font: 'archivo', spacing: 3 }); txt('VERIFIED', 0, 70, 24, '#C8FFD8', { font: 'archivo', spacing: 2 });
      ctx.restore();
    }
    flash(lt, b1, .08, .35, '255 255 220');
    brk('AI PROOF: NAVIER-STOKES BLOWS UP', 'OPENAI · CHECKED IN LEAN · CLAY: "APPARENTLY"', lt, { tab: 'WX' });
  });

  // =====================================================================================
  // V4.6 Who was first? Twelve hours between! — INSTANT REPLAY in slow motion: the NYU + ANTHROPIC three-legged pair breaks the tape;
  // way back down the track, OPENAI is still running. The telestrator measures the gap: 12 HOURS.
  function runner(x, y, s, t, o) {
    toon(x, y, s, { ...o, walk: t * 1.1 + (o.ph ?? 0), rot: .14, aL: Math.sin((t * 1.1 + (o.ph ?? 0)) * TAU) * .7 - .4, aR: -Math.sin((t * 1.1 + (o.ph ?? 0)) * TAU) * .7 - .4, eL: 1.3, eR: 1.3, legs: true });
    rrect(x - .9 * s + .6 * s, y - 6.9 * s, 1.8 * s, 1.3 * s, 3); paint('#FFFFFF', NP.ink, 2.5);
    txt(o.bib, x + .6 * s, y - 6.25 * s, s * .5, NP.ink, { font: 'archivo', maxW: 1.6 * s });
  }
  v4(6, (p, lt, d, t) => {
    const b1 = bt(t, lt, 1), b2 = bt(t, lt, 2), b3 = bt(t, lt, 3), slo = (t - lt) + lt * .25;
    vcrMode('SLOW');
    // the stadium (then desaturated: a grainy replay)
    vFill('#3A4A6A', '#6A7A9A', -100, -100, W + 200, 520);
    for (let r = 0; r < 7; r++) for (let i = 0; i < 48; i++) { ell(i * 42 + (r % 2) * 20 - 20, 80 + r * 46, 15, 17); paint(['#E84A4A', '#F4D24A', '#FFFFFF', '#4A8AE8', '#2EBD5B'][(i * 7 + r * 3) % 5]); }
    ctx.fillStyle = '#18401E'; ctx.fillRect(-100, 400, W + 200, 50);
    vFill('#C8422E', '#8A2A1A', -100, 450, W + 200, 700);
    for (let l = 0; l < 5; l++) { ctx.fillStyle = 'rgb(255 255 255 / .8)'; ctx.fillRect(-100, 470 + l * 100, W + 200, 5); }
    ctx.fillStyle = '#FFFFFF'; poly([[1178, 450], [1196, 450], [1226, 960], [1202, 960]]); ctx.fill();
    // the snapped finish tape, trailing from the leader
    ctx.beginPath(); ctx.moveTo(1440, 560); ctx.quadraticCurveTo(1560, 600 + Math.sin(slo * 3) * 20, 1700, 640); paint(null, '#FFFFFF', 7);
    ctx.beginPath(); ctx.moveTo(1180, 540); ctx.quadraticCurveTo(1080, 620 + Math.sin(slo * 3 + 1) * 20, 1010, 700); paint(null, '#FFFFFF', 7);
    // way behind: OPENAI
    computer(360, 700, 24, { label: 'OPENAI', face: 'angry', walk: slo * 1.2, rot: .12, aL: Math.sin(slo * 1.2 * TAU) * .8 - .3, aR: -Math.sin(slo * 1.2 * TAU) * .8 - .3, eL: 1.2, eR: 1.2 });
    // the leaders: a three-legged pair
    runner(1220, 870, 42, slo, { hair: 'short', hairCol: NHAIR.brown, top: 'tee', topCol: '#57068C', skin: 0, bib: 'NYU', eyes: 'happy', mouth: 'grin', ph: 0 });
    runner(1400, 884, 42, slo, { hair: 'curly', hairCol: NHAIR.black, top: 'tee', topCol: NP.clawd, skin: 1, bib: 'ANTHROPIC', eyes: 'happy', mouth: 'grin', ph: .5 });
    rrect(1280, 722, 96, 26, 6); paint('#F4D24A', NP.ink, 3);
    // desaturate + a cool replay tint
    ctx.save(); ctx.globalCompositeOperation = 'saturation'; ctx.fillStyle = '#808080'; ctx.fillRect(-100, -100, W + 200, H + 200);
    ctx.globalCompositeOperation = 'multiply'; ctx.fillStyle = '#B8C8E8'; ctx.fillRect(-100, -100, W + 200, H + 200); ctx.restore();
    // telestrator (bright, on top)
    const tele = NP.gold;
    if (lt >= b1) { const k = clamp((lt - b1) / .18), P = []; for (let i = 0; i <= 40; i++) { const a = -1.2 + i / 40 * TAU * 1.05; P.push([1300 + Math.cos(a) * 220, 640 + Math.sin(a) * 290]); } ctx.beginPath(); partial(P, k).forEach(([a, c], i) => i ? ctx.lineTo(a, c) : ctx.moveTo(a, c)); paint(null, tele, 10); }
    if (lt >= b2) {
      const k = clamp((lt - b2) / .2), x0 = 470, x1 = 1060, y = 580, xe = lerp(x0, x1, easeOut(k));
      ctx.beginPath(); ctx.moveTo(x0, y); ctx.lineTo(xe, y); paint(null, NP.ink, 16); ctx.beginPath(); ctx.moveTo(x0, y); ctx.lineTo(xe, y); paint(null, tele, 10);
      for (const [ax, dir] of [[x0, 1], [xe, -1]]) { poly([[ax, y], [ax + dir * 40, y - 24], [ax + dir * 40, y + 24]]); paint(tele, NP.ink, 3); }
    }
    // results box
    rrect(96, 164, 720, 150, 8); paint('rgb(0 0 0 / .78)', '#888', 3);
    pixelText('PHOTO FINISH', 116, 180, 4, NP.gold, { edge: null });
    pixelText('1 NYU+ANTHROPIC  BY MIDNIGHT', 116, 222, 4, NP.white, { edge: null });
    pixelText('2 OPENAI         +12 HRS', 116, 262, 4, lt >= b3 && frac(t * 3) < .6 ? NP.gold : NP.white, { edge: null });
    liveBug(96, 70, { label: 'INSTANT REPLAY', col: NP.blue });
    brk('NAVIER-STOKES: A PHOTO FINISH', 'NYU & ANTHROPIC POSTED ~12 HOURS BEFORE OPENAI', lt, { tab: 'REPLAY' });
  });

  // =====================================================================================
  // V4.7 Dario: "Pace the frontier!" — the speedway under caution: DARIO waves the yellow flag from the pace car and the field of
  // computer race cars bunches up behind it. Taped to the pace car's dash: the PAUSE button from V1.7.
  function raceCar(x, y, s, col, num, face) {
    ctx.save(); ctx.translate(x, y); ctx.scale(s, s);
    ctx.fillStyle = 'rgb(0 0 0 / .3)'; ell(0, 8, 190, 16); ctx.fill();
    poly([[-170, -10], [-150, -48], [60, -54], [190, -26], [200, -6], [-170, -4]]); paint(col, NP.ink, 4);
    rrect(-190, -90, 40, 60, 4); paint(shade(col, .3), NP.ink, 4); rrect(-200, -96, 70, 16, 4); paint(col, NP.ink, 4);
    computer(-30, -40, 11, { case: '#E8E4D8', face, arms: false, legs: false, shadow: false });
    ell(-110, 0, 38); paint('#1A1A1E', NP.ink, 4); ell(-110, 0, 14); paint('#8A8A94'); ell(130, 2, 32); paint('#1A1A1E', NP.ink, 4); ell(130, 2, 12); paint('#8A8A94');
    ell(60, -30, 26, 20); paint(NP.white, NP.ink, 3); txt(String(num), 60, -29, 26, NP.ink, { font: 'anton' });
    ctx.restore();
  }
  v4(7, (p, lt, d, t) => {
    const b1 = bt(t, lt, 1), bunch = easeOut(clamp((lt - b1 + .15) / .3)), scroll = t * 1600;
    // sky, grandstand, caution lights
    vFill('#5AA8F0', '#CFE8FF', -100, -100, W + 200, 360);
    ctx.fillStyle = '#F4C21A'; ctx.fillRect(-100, 250, W + 200, 190); ctx.fillStyle = NP.ink; ctx.fillRect(-100, 250, W + 200, 6);
    for (let r = 0; r < 3; r++) for (let i = 0; i < 40; i++) { const x = ((i * 52 - scroll * .3) % 2100 + 2100) % 2100 - 100; ell(x, 290 + r * 40, 13, 15); paint(['#E84A4A', '#FFFFFF', '#4A8AE8', '#2A2A2A'][(i + r) % 4]); }
    for (let i = 0; i < 9; i++) { const x = ((i * 240 - scroll * .5) % 2160 + 2160) % 2160 - 120, on = frac(t * 4 + i * .5) < .5; ell(x, 440, 18); paint(on ? '#FFE84A' : '#8A6A10', NP.ink, 3); if (on) { ctx.save(); ctx.globalCompositeOperation = 'screen'; ctx.fillStyle = 'rgb(255 230 60 / .35)'; ell(x, 440, 60); ctx.fill(); ctx.restore(); } }
    // track
    vFill('#5A5E68', '#3A3E48', -100, 460, W + 200, 700);
    for (let i = 0; i < 12; i++) { const x = ((i * 260 - scroll) % 3120 + 3120) % 3120 - 200; ctx.fillStyle = '#FFE84A'; ctx.fillRect(x, 700, 130, 10); }
    ctx.fillStyle = '#FFFFFF'; ctx.fillRect(-100, 470, W + 200, 8);
    // the pack, bunching up behind the pace car
    const cols = ['#D8262F', '#2554CC', '#2EBD5B', '#6B3FC4'], faces = ['angry', 'sad', 'angry', 'O'];
    for (let i = 3; i >= 0; i--) { const x = lerp(120 + i * 330, 170 + i * 250, bunch) + Math.sin(t * 20 + i) * 4, y = 640 + (i % 2) * 70; raceCar(x - 260, y, .95, cols[i], [4, 7, 11, 23][i], faces[i]); }
    // the pace car
    const px = 1180, py = 720 + Math.sin(t * 30) * 2;
    ctx.save(); ctx.translate(px, py);
    ctx.fillStyle = 'rgb(0 0 0 / .3)'; ell(20, 20, 330, 24); ctx.fill();
    poly([[-300, -10], [-290, -110], [-150, -120], [-90, -210], [170, -210], [240, -120], [320, -100], [330, -10]]); paint('#F4F2EC', NP.ink, 5);
    poly([[-80, -196], [160, -196], [220, -124], [-140, -124]]); paint('#9ACBF0', NP.ink, 4);
    ctx.beginPath(); ctx.moveTo(40, -196); ctx.lineTo(40, -124); paint(null, NP.ink, 6);
    ctx.fillStyle = NP.red; ctx.fillRect(-300, -80, 630, 22); ctx.fillStyle = '#FFE84A'; ctx.fillRect(-300, -58, 630, 10);
    txt('PACE CAR', 20, -24, 44, NP.redDk, { font: 'archivo', spacing: 3 });
    const lon = frac(t * 6) < .5; rrect(-40, -236, 170, 28, 8); paint('#222', NP.ink, 3); ell(-5, -222, 15); paint(lon ? '#FFE84A' : '#8A6A10'); ell(95, -222, 15); paint(lon ? '#8A6A10' : '#FFE84A');
    ell(-190, 0, 52); paint('#1A1A1E', NP.ink, 4); ell(-190, 0, 20); paint('#C9CFDB'); ell(220, 0, 52); paint('#1A1A1E', NP.ink, 4); ell(220, 0, 20); paint('#C9CFDB');
    // the PAUSE button, taped to the dash
    ell(180, -150, 22); paint(NP.red, NP.ink, 3); ctx.fillStyle = NP.white; ctx.fillRect(172, -160, 6, 20); ctx.fillRect(183, -160, 6, 20);
    ctx.save(); ctx.translate(180, -150); ctx.rotate(.5); ctx.fillStyle = 'rgb(230 220 190 / .85)'; ctx.fillRect(-34, -8, 68, 16); ctx.restore();
    ctx.restore();
    // Dario, leaning out of the rear window with the flag
    const wave = Math.sin(t * 18);
    toon(px - 40, py - 30, 30, { hair: 'curly', hairCol: '#4A3A30', glasses: 'round', top: 'suit', topCol: '#2A3048', tie: NP.clawd, skin: 0, legs: false, shadow: false, eyes: 'open', talk: talk(t), rot: -.18,
      aR: 1.3 + wave * .15, eR: .2, aL: -.4, hold: s => {
        ctx.rotate(-.2 + wave * .25); ctx.beginPath(); ctx.moveTo(0, 20); ctx.lineTo(0, -200); paint(null, '#3A3A3A', 8);
        ctx.beginPath(); ctx.moveTo(0, -200); for (let i = 0; i <= 10; i++) ctx.lineTo(-i * 20, -200 + Math.sin(i * .8 - t * 22) * 12 * i / 10); for (let i = 10; i >= 0; i--) ctx.lineTo(-i * 20, -80 + Math.sin(i * .8 - t * 22) * 12 * i / 10); ctx.closePath(); paint('#FFE84A', NP.ink, 4);
      } });
    // the window frame over his waist
    ctx.save(); ctx.translate(px, py); poly([[-150, -120], [-90, -196], [-40, -196], [-40, -124]]); paint(null, NP.ink, 6); ctx.restore();
    // the PACE pylon
    rrect(96, 164, 280, 150, 10); paint('#0A0A0A', '#C9A43A', 5);
    pixelText('CAUTION', 236, 184, 4, frac(t * 3) < .6 ? '#FFE84A' : '#6A5A10', { align: 'center', edge: null });
    pixelText('PACE', 236, 230, 10, '#FFE84A', { align: 'center', edge: null });
    liveBug();
    brk('AMODEI: "WE MUST PACE THE FRONTIER"', 'ANTHROPIC CEO CITES THE HUGGING FACE HACK', lt, { size: 50 });
  });

  // =====================================================================================
  // V4.8 Sam and Elon both: "Hear, hear!" — a triple satellite split: DARIO in the middle with his essay; ELON nods on the first beat,
  // SAM on the second (satellite delay), and by the third they nod in perfect sync (a flash on the beat).
  function bust(w, h, o, nod) {
    toon(w / 2, h + 250, 56, { legs: false, shadow: false, dy: nod * .1, lookY: nod * .9, ...o });
  }
  v4(8, (p, lt, d, t) => {
    const b1 = bt(t, lt, 1), b2 = bt(t, lt, 2), b3 = bt(t, lt, 3);
    vFill('#0E2A9A', '#030A34');
    ctx.fillStyle = 'rgb(255 255 255 / .05)'; for (let y = 0; y < H; y += 14) ctx.fillRect(0, y, W, 6);
    const nodAt = (from) => lt >= from ? Math.max(0, Math.sin((lt - from) / beatLen() * Math.PI * 2)) : 0;
    const eN = nodAt(b1 - .05), sN = lt >= b3 ? eN : nodAt(b2 - .05);
    const box = (x, draw, label, col, k, tilt) => otsBox(x, 196, 540, 470, draw, { k, label, labelCol: col, tilt, labelSize: 30, labelH: 54 });
    box(90, (w, h) => {
      vFill('#9AB8D8', '#3A5A7A'); ctx.fillStyle = '#2A3A52'; for (let i = 0; i < 6; i++) ctx.fillRect(i * 110 - 20, h * .5 - hash(i + 1) * 160, 80, 400);
      bust(w, h, { hair: 'short', hairCol: NHAIR.brown, top: 'sweater', topCol: '#7A8A9A', skin: 0, eyes: 'open', mouth: 'smile', ...(lt >= b2 ? { reachR: [2.3, -7.4], hand: 'thumb' } : {}) }, sN);
      pixelText('VIA SATELLITE', 16, 14, 3, NP.white);
    }, 'SAM: "I AGREE WITH DARIO"', NP.blue, inK(lt, .04, .16), .5);
    box(1290, (w, h) => {
      vFill('#3A3A48', '#16161E'); ctx.fillStyle = '#26262E'; for (let i = 0; i < 5; i++) ctx.fillRect(i * 130, h * .45 - hash(i + 7) * 140, 90, 400);
      bust(w, h, { hair: 'side', hairCol: '#3A2A22', top: 'tee', topCol: '#16161A', skin: 0, eyes: 'open', mouth: 'smirk', ...(lt >= b1 ? { reachL: [-2.3, -7.4], handL: 'thumb' } : {}) }, eN);
      pixelText('VIA SATELLITE', 16, 14, 3, NP.white);
    }, 'ELON: "DARIO IS RIGHT"', '#3A3A48', inK(lt, .08, .16), -.5);
    box(690, (w, h) => {
      vFill('#F4D8A8', '#B08850');
      bust(w, h, { hair: 'curly', hairCol: '#4A3A30', glasses: 'round', top: 'suit', topCol: '#2A3048', tie: NP.clawd, skin: 0, talk: talk(t), reachL: [-1.6, -6.4], reachR: [1.6, -6.4] }, 0);
      ctx.save(); ctx.translate(w / 2, h + 250 - 6.2 * 56); ctx.rotate(-.04); rrect(-130, -40, 260, 140, 4); paint('#FBFAF2', NP.ink, 3);
      txt('WE MUST PACE', 0, -12, 26, NP.ink, { font: 'abril' }); txt('THE FRONTIER', 0, 20, 26, NP.ink, { font: 'abril' }); ctx.fillStyle = 'rgb(20 20 30 / .4)'; for (let r = 0; r < 3; r++) ctx.fillRect(-100, 44 + r * 14, r === 2 ? 110 : 200, 5); ctx.restore();
    }, 'DARIO AMODEI · ANTHROPIC', NP.clawdDk, inK(lt, 0, .16), 0);
    flash(lt, b3, .08, .35, '255 240 200');
    brk('MUSK, ALTMAN BACK AMODEI', 'RIVALS AGREE: "PACE THE FRONTIER"', lt, { y: 830 });
  });

  // =====================================================================================
  // V4.9 Trump's the guardrail (High IQ!), — SKY 89 traffic: on the cliff road the guardrail stops, and in the gap stands TRUMP himself,
  // arms out, wearing a HIGH IQ! sash. The AI cars bounce off him, one per beat.
  function aiCar(x, y, rot, col, face) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot);
    ctx.fillStyle = 'rgb(0 0 0 / .3)'; rrect(-66, -30, 140, 72, 20); ctx.fill();
    rrect(-72, -36, 144, 72, 22); paint(col, NP.ink, 4);
    rrect(-30, -28, 74, 56, 12); paint('#10201A', NP.ink, 3);
    ctx.fillStyle = NP.phosphor;
    if (face === 'x') { ctx.lineWidth = 4; ctx.strokeStyle = NP.phosphor; ctx.beginPath(); for (const ex of [-4, 22]) { ctx.moveTo(ex - 6, -12); ctx.lineTo(ex + 6, 0); ctx.moveTo(ex + 6, -12); ctx.lineTo(ex - 6, 0); } ctx.stroke(); }
    else { ctx.fillRect(-8, -14, 8, 12); ctx.fillRect(18, -14, 8, 12); ctx.fillRect(-4, 8, 26, 5); }
    for (const [a, b] of [[-50, -38], [50, -38], [-50, 38], [50, 38]]) { rrect(a - 16, b - 8, 32, 16, 5); paint('#1A1A1E'); }
    ctx.restore();
  }
  v4(9, (p, lt, d, t) => {
    const hits = [0, 1, 2].map(k => bt(t, lt, k)), [sx, sy] = shake(t, lt, hits.filter(h => lt >= h).at(-1) ?? -1, .15, 6);
    const CX = 880 + Math.sin(t * .7) * 14, CY = 470, CZ = 1.42 + p * .05;
    camBegin(CX + sx, CY + sy, CZ, Math.sin(t * .5) * .01);
    // hillside and the river below the cliff
    vFill('#8AD06A', '#3A8A3A', -600, -600, W + 1200, 1800);
    ctx.fillStyle = '#2A6ACC'; poly([[-600, -600], [2600, -600], [2600, 150], [1400, 120], [800, 250], [-600, 340]]); ctx.fill();
    ctx.fillStyle = 'rgb(255 255 255 / .3)'; for (let i = 0; i < 14; i++) { const x = ((i * 190 + t * 60) % 2400) - 300; ctx.fillRect(x, 80 + (i % 4) * 50, 90, 5); }
    ctx.fillStyle = '#6A5A3A'; poly([[-600, 340], [800, 250], [1400, 120], [2600, 150], [2600, 260], [1400, 250], [800, 380], [-600, 480]]); ctx.fill();
    for (let i = 0; i < 26; i++) { const x = hash(i + 4) * 2200 - 150, y = 620 + hash(i + 9) * 500; ell(x, y, 34, 30); paint('#2A7A2A', NP.ink, 3); ell(x - 8, y - 8, 16); paint('#4AAA4A'); }
    // the road: a diagonal band, guardrail along its upper (cliff-side) edge
    const A = [-200, 900], B = [2100, 380], dx = B[0] - A[0], dy = B[1] - A[1], L = Math.hypot(dx, dy), ux = dx / L, uy = dy / L, nx = -uy, ny = ux, hw = 150;
    const at = (u, off) => [A[0] + dx * u + nx * off, A[1] + dy * u + ny * off];
    poly([at(0, -hw), at(1, -hw), at(1, hw), at(0, hw)]); paint('#4A4E58', NP.ink, 4);
    ctx.fillStyle = '#FFE84A'; for (let i = 0; i < 18; i++) { const [a, b] = at(i / 18 + .02, 0); ctx.save(); ctx.translate(a, b); ctx.rotate(Math.atan2(dy, dx)); ctx.fillRect(-40, -5, 80, 10); ctx.restore(); }
    const gap0 = .44, gap1 = .52, rail = u => at(u, -hw - 6);
    for (const [u0, u1] of [[0, gap0], [gap1, 1]]) {
      for (let u = u0; u <= u1; u += .025) { const [a, b] = rail(u); ctx.fillStyle = '#8A8E98'; ctx.fillRect(a - 5, b - 34, 10, 40); }
      const [a0, b0] = rail(u0), [a1, b1] = rail(u1); ctx.beginPath(); ctx.moveTo(a0, b0 - 30); ctx.lineTo(a1, b1 - 30); paint(null, NP.ink, 20); ctx.beginPath(); ctx.moveTo(a0, b0 - 30); ctx.lineTo(a1, b1 - 30); paint(null, '#D8DCE4', 14);
    }
    // the man in the gap
    const [mx, my] = rail((gap0 + gap1) / 2), S = 30, brace = hits.some(h => lt >= h && lt < h + .15);
    trumpToon(mx, my + 6, S, { eyes: brace ? 'closed' : 'half', mouth: brace ? 'grin' : 'smirk', aL: .15, aR: .15, eL: 0, eR: 0, hand: 'open', handL: 'open', sq: brace ? .06 : 0 });
    ctx.save(); ctx.translate(mx, my + 6 + (brace ? S * .06 * 11 * 0 : 0)); ctx.scale(S, S);
    poly([[-1.45, -7.95], [-.55, -8.1], [1.45, -4.75], [.55, -4.1]]); paint(NP.white, NP.ink, .08);
    ctx.restore();
    ctx.save(); ctx.translate(mx + .02 * S, my + 6 - 6.15 * S); ctx.rotate(1.0); txt('HIGH IQ!', 0, 1, S * .62, NP.red, { font: 'archivo' }); ctx.restore();
    // the AI cars: each drifts to the cliff edge, boings off him on its beat, and carries on
    const cols = ['#D8262F', '#2EBD5B', '#F4B62A', '#2AD4F0'];
    for (let i = 0; i < 3; i++) {
      const h = hits[i], a = lt - h, u = (gap0 + gap1) / 2 + a * .16 - .012, lat = a < 0 ? lerp(-20, -hw + 36, easeIn(clamp(1 + a / .3))) : -hw + 36 + easeIn(clamp((a - .08) / .4)) * 150;
      const [cx, cy] = at(u, lat), rot = Math.atan2(dy, dx) + (a >= 0 && a < .4 ? Math.sin(a * 30) * .4 * (1 - a / .4) : a < 0 ? -.2 : 0);
      if (u < -.05 || u > 1.05) continue;
      aiCar(cx, cy, rot, cols[i], a >= 0 && a < .3 ? 'x' : 'ok');
      if (a >= 0 && a < .3) { const k = a / .3; poly(starPts(mx - 110, my + 10, 80 * backOut(clamp(k * 3), 2), .5, 10, k)); paint('#FFF27A', NP.ink, 4); txt('BOING!', mx - 110, my + 12, 34, NP.red, { font: 'anton', alpha: 1 - clamp((k - .7) / .3) }); }
    }
    { const [cx, cy] = at(((t * .12) % 1.2) - .1, 70); aiCar(cx, cy, Math.atan2(dy, dx) + Math.PI, cols[3], 'ok'); }
    camEnd();
    // SKY 89 overlay
    ctx.strokeStyle = 'rgb(255 255 255 / .8)'; ctx.lineWidth = 4;
    for (const [x, y, sx2, sy2] of [[560, 200, 1, 1], [1360, 200, -1, 1], [560, 760, 1, -1], [1360, 760, -1, -1]]) { ctx.beginPath(); ctx.moveTo(x, y + sy2 * 60); ctx.lineTo(x, y); ctx.lineTo(x + sx2 * 60, y); ctx.stroke(); }
    pixelText(`ALT ${900 + Math.round(Math.sin(t) * 15)} FT  TRAFFIC`, 96, 170, 4, NP.white);
    liveBug(96, 70, { label: 'SKY 89', col: NP.blue });
    brk('TRUMP ON AI "GUARDRAILS"', 'A "STRONG AND SMART (HIGH IQ!) PRESIDENT"', lt);
  });

  // =====================================================================================
  // V4.10 Bernie, Bannon share a pew, — RELIGION & COMMUNITY: a church pew in a hotel ballroom. BERNIE (mittens) and STEVE (three
  // shirts) sing from their PRO-HUMAN hymnals side by side… and on the beat, scoot to opposite ends.
  function hymnal(x, y, s, rot) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot); ctx.scale(s, s);
    rrect(-1.2, -.85, 2.4, 1.7, .1); paint('#6A1020', NP.ink, .08); ctx.fillStyle = '#F4EEDC'; ctx.fillRect(-1.15, .7, 2.3, .12);
    txt('PRO-HUMAN', 0, -.25, .38, NP.gold, { font: 'archivo', maxW: 2.1 }); txt('HYMNS', 0, .25, .42, NP.gold, { font: 'abril' });
    ctx.restore();
  }
  const mitten = (x, y, s) => { rrect(x - .42 * s, y - .5 * s, .84 * s, 1.0 * s, .35 * s); paint('#8A5A3A', NP.ink, 3); ctx.fillStyle = '#E8DCC0'; ctx.fillRect(x - .42 * s, y + .3 * s, .84 * s, .16 * s); ell(x - .45 * s, y - .05 * s, .2 * s, .28 * s); paint('#8A5A3A', NP.ink, 2.5); };
  v4(10, (p, lt, d, t) => {
    const b2 = bt(t, lt, 2), b3 = bt(t, lt, 3), sc = easeOut(clamp((lt - b3 + .05) / .16)), look = lt >= b2 && lt < b3 + .05;
    // ballroom: damask wallpaper, chandeliers, a stained-glass banner
    vFill('#6A1426', '#2A0610');
    ctx.fillStyle = 'rgb(244 182 42 / .1)'; for (let r = 0; r < 9; r++) for (let c = 0; c < 17; c++) { ell(c * 120 + (r % 2) * 60, r * 110, 22, 34); ctx.fill(); }
    for (const cx of [330, 1590]) { ctx.beginPath(); ctx.moveTo(cx, -10); ctx.lineTo(cx, 120); paint(null, NP.gold, 4); for (let i = 0; i < 9; i++) { const a = i / 8 * Math.PI, x = cx + Math.cos(a) * 130, y = 150 + Math.sin(a) * 40; ell(x, y, 9, 14); paint('#FFF6D0', NP.goldDk, 2); glint(x, y, 30 + 20 * Math.sin(t * 5 + i), .7); } ell(cx, 140, 60, 26); paint(NP.gold, NP.ink, 3); }
    const gx = 610, gw = 700, gy = 150, gh = 330;
    ctx.beginPath(); ctx.moveTo(gx, gy + gh); ctx.lineTo(gx, gy + 140); ctx.arc(gx + gw / 2, gy + 140, gw / 2, Math.PI, TAU); ctx.lineTo(gx + gw, gy + gh); ctx.closePath(); paint('#1A1A2A', NP.gold, 8);
    ctx.save(); ctx.clip(); const glass = ['#D8262F', '#2554CC', '#F4B62A', '#2EBD5B', '#6B3FC4', '#2AD4F0'];
    for (let r = 0; r < 6; r++) for (let c = 0; c < 10; c++) { ctx.fillStyle = alpha(glass[(r * 3 + c * 5) % 6], .85); ctx.fillRect(gx + c * 70 + 4, gy + r * 56 + 4, 62, 48); }
    ctx.restore();
    rrect(gx + 90, gy + 40, gw - 180, 100, 8); paint('rgb(20 10 20 / .88)', NP.gold, 4);
    txt('PRO-HUMAN', W / 2, gy + 70, 44, '#FFF6D0', { font: 'abril', spacing: 3 }); txt('ASSEMBLY', W / 2, gy + 114, 34, NP.gold, { font: 'archivo', spacing: 8 });
    // carpet
    vFill('#7A1020', '#3A0610', -100, 780, W + 200, 400);
    ctx.fillStyle = 'rgb(244 182 42 / .18)'; for (let i = 0; i < 22; i++) { poly([[i * 100, 820], [i * 100 + 40, 800], [i * 100 + 80, 820], [i * 100 + 40, 840]]); ctx.fill(); }
    // the pew back
    const px0 = 330, px1 = 1590;
    rrect(px0, 540, px1 - px0, 180, 10); paint(lg(0, 540, 0, 720, [[0, '#9A6A40'], [1, '#6A4020']]), NP.ink, 5);
    ctx.fillStyle = 'rgb(0 0 0 / .15)'; for (let x = px0 + 40; x < px1; x += 90) ctx.fillRect(x, 560, 8, 150);
    // the congregation of two
    const bx = lerp(810, 560, sc), sx2 = lerp(1110, 1370, sc), S = 56, bob = Math.sin(bpOf(t) * Math.PI) * .03;
    for (const [x, o, ph] of [[bx, { hair: 'balding', hairCol: NHAIR.white, glasses: 'round', top: 'sweater', topCol: '#7A6A5A', skin: 0, tag: 'BERNIE' }, 0], [sx2, { hair: 'side', hairCol: NHAIR.grey, stubble: true, top: 'layers', topCol: '#3A4A3A', midCol: '#6A5A8A', shirtCol: '#E8E0CC', skin: 4, tag: 'STEVE' }, 1]]) {
      const lookX = look ? (ph ? -.9 : .9) : 0, y = 940;
      toon(x, y, S, { ...o, legs: false, shadow: false, dy: bob * (ph ? -1 : 1), talk: look ? undefined : talk(t, ph * 2), mouth: 'flat', eyes: look ? 'half' : 'open', lookX, reachL: [-.9, -4.9], reachR: [.9, -4.9] });
      hymnal(x, y - 4.9 * S + bob * S, S * .9, ph ? .06 : -.06);
      if (!ph) { mitten(x - 1.0 * S, y - 4.9 * S, S); mitten(x + 1.0 * S, y - 4.9 * S, S); }
      if (sc > 0 && sc < 1) for (let i = 0; i < 3; i++) { const dir = ph ? -1 : 1; ctx.beginPath(); ctx.moveTo(x + dir * (1.8 * S + i * 10), y - 6 * S + i * 40); ctx.lineTo(x + dir * (1.8 * S + 90 + i * 10), y - 6 * S + i * 40); paint(null, 'rgb(255 255 255 / .6)', 5); }
    }
    // the seat and its front
    rrect(px0 - 20, 700, px1 - px0 + 40, 36, 8); paint(lg(0, 700, 0, 736, [[0, '#B8844A'], [1, '#7A4A20']]), NP.ink, 5);
    rrect(px0, 736, px1 - px0, 110, 4); paint('#5A3418', NP.ink, 5);
    for (const x of [px0 + 20, px1 - 60]) { rrect(x, 736, 40, 170, 4); paint('#4A2A10', NP.ink, 4); }
    brk('SANDERS & BANNON: REIN IN AI', 'PRO-HUMAN ASSEMBLY, WASHINGTON · SPLIT ON CHINA', lt);
  });

  // =====================================================================================
  // V4.11 Claude builds Claude — now one in four! — at the desk, Clawd tightens the last bolt on a little Clawd; it switches on and
  // immediately starts building an even smaller one. On the wall: the pie, 26%.
  function pieWall(t, k) {
    return (w, h) => {
      vFill('#0E2A7A', '#07153E', 0, 0, w, h);
      txt('R&D LED BY CLAUDE', w / 2, 60, 38, NP.white, { font: 'archivo', maxW: w - 40 });
      const cx = w / 2, cy = 260, r = 160, sl = lerp(.01, .26, easeOut(k));
      ell(cx + 8, cy + 12, r); paint('rgb(0 0 0 / .4)');
      ctx.beginPath(); ctx.moveTo(cx, cy); ctx.arc(cx, cy, r, -Math.PI / 2 + sl * TAU, Math.PI * 1.5); ctx.closePath(); paint('#3A6ACC', NP.ink, 4);
      ctx.beginPath(); ctx.moveTo(cx, cy); ctx.arc(cx, cy, r + (k > .9 ? 14 : 0), -Math.PI / 2, -Math.PI / 2 + sl * TAU); ctx.closePath(); paint(NP.clawd, NP.ink, 4);
      txt(Math.round(sl * 100) + '%', w / 2, 470, 90, NP.gold, { font: 'anton' });
    };
  }
  v4(11, (p, lt, d, t) => {
    const b1 = bt(t, lt, 1), b2 = bt(t, lt, 2), b3 = bt(t, lt, 3), on = lt >= b1, wr = Math.sin(t * 22) * .5;
    const mX = 900, mY = 716, mU = 16;
    deskShot(t, { mugs: 5, vol: 1.45, wall: pieWall(t, clamp((lt - b3 + .1) / .25)), cam: { x: 930, y: 520, zoom: 1.1 },
      clawdHands: false,
      clawd: { reachR: [(mX - 95 - SET.clawdX) / SET.clawdU, (mY - 60 - SET.clawdY) / SET.clawdU], reachL: [-58 / SET.clawdU, (deskEdge(SET.clawdX) + 4 - SET.clawdY) / SET.clawdU], lookX: .8, lookY: .3, eyes: on ? 'happy' : 'normal',
        hold: u => { ctx.rotate(-1.1 + wr); rrect(-9, -100, 18, 112, 5); paint('#A8B0C0', NP.ink, 4); ctx.beginPath(); ctx.arc(0, -112, 24, .6, Math.PI * 2 - .6); paint(null, NP.ink, 20); ctx.beginPath(); ctx.arc(0, -112, 24, .6, Math.PI * 2 - .6); paint(null, '#A8B0C0', 12); } },
      val: { lookX: -.9, eyes: 'wide', mouth: 'o', brows: 'up' },
      front: () => {
        // the little Clawd on the desk
        newsClawd(mX, mY, mU, { suit: false, legs: true, eyes: on ? 'normal' : 'closed', blink: on && lt < b1 + .1 ? .6 : 0, dy: on && lt < b1 + .12 ? -.6 : 0, aR: lt >= b2 ? .9 : -.3, aL: on ? -.1 : -.6,
          hold: lt >= b2 ? (u => { ctx.rotate(.8 + Math.sin(t * 24) * .5); rrect(-4, -40, 8, 46, 2); paint('#A8B0C0', NP.ink, 2); ctx.beginPath(); ctx.arc(0, -44, 9, .6, Math.PI * 2 - .6); paint(null, '#A8B0C0', 5); }) : undefined });
        deskHand(SET.clawdX - 58, SET.deskTop + 8, 'clawd', '#1C2A5E');
        if (!on) for (let i = 0; i < 6; i++) { const a = hash2(Math.floor(t * 24), i) * TAU; ctx.beginPath(); ctx.moveTo(mX - 80, mY - 60); ctx.lineTo(mX - 80 + Math.cos(a) * 40, mY - 60 + Math.sin(a) * 40); paint(null, NP.gold, 4); }
        if (on && lt < b1 + .15) glint(mX, mY - 60, 90, 1);
        // …which is already building a smaller one
        if (lt >= b2) { const k = clamp((lt - b2) / .4); newsClawd(mX + 120, mY, 6.5, { suit: false, eyes: k >= 1 ? 'normal' : 'closed', sq: k < 1 ? .2 * (1 - k) : 0 }); for (let i = 0; i < 4; i++) { const a = hash2(Math.floor(t * 24), i + 9) * TAU; ctx.beginPath(); ctx.moveTo(mX + 96, mY - 30); ctx.lineTo(mX + 96 + Math.cos(a) * 22, mY - 30 + Math.sin(a) * 22); paint(null, NP.gold, 3); } }
      } });
    brk('CLAUDE NOW LEADS 26% OF AI R&D', 'AT ANTHROPIC · UP FROM UNDER 1% IN FEBRUARY', lt);
  });

  // =====================================================================================
  // V4.12 Chatbot nearly starts a war! — the WAR ROOM big board: the chatbot says the ship has nuclear parts (98% SURE), the planes
  // scramble and DEFCON climbs on the beats… then ERROR: HALLUCINATION, the planes turn back, DEFCON drops.
  const plane = (x, y, a, s = 1) => { ctx.save(); ctx.translate(x, y); ctx.rotate(a); ctx.scale(s, s); poly([[26, 0], [-16, -6], [-20, -22], [-26, -22], [-22, -6], [-30, -4], [-34, -12], [-38, -12], [-36, 0], [-38, 12], [-34, 12], [-30, 4], [-22, 6], [-26, 22], [-20, 22], [-16, 6]]); paint('#9AFFB8', '#062A12', 2); ctx.restore(); };
  v4(12, (p, lt, d, t) => {
    const b0 = bt(t, lt), b1 = bt(t, lt, 1), b2 = bt(t, lt, 2), b3 = bt(t, lt, 3), err = lt >= b3 - .02;
    fillAll('#020806');
    const bx = 110, by = 180, bw = 1700, bh = 580;
    rrect(bx, by, bw, bh, 10); paint('#03140A', '#2A6A3A', 6);
    ctx.save(); rrect(bx, by, bw, bh, 10); ctx.clip();
    const P = worldMap(bx + 20, by + 20, bw - 40, bh - 40, { land: '#0A3A1A', edge: '#3AFF7A', grid: 'rgb(60 255 120 / .13)', lw: 2 });
    // the ship in the Arabian Sea, blinking
    const [shx, shy] = P([62, 16]);
    ctx.save(); ctx.translate(shx, shy); poly([[-34, 0], [34, 0], [24, 14], [-24, 14]]); paint(err ? '#9AFFB8' : '#FF4A4A', NP.ink, 2); ctx.fillStyle = err ? '#9AFFB8' : '#FF4A4A'; ctx.fillRect(-6, -18, 14, 18); ctx.restore();
    if (!err && frac(t * 3) < .6) { ell(shx, shy + 6, 44 + frac(t * 3) * 30); paint(null, '#FF4A4A', 3); }
    pixelText(err ? 'CARGO SHIP' : 'NUCLEAR?', shx, shy + 30, 3, err ? '#9AFFB8' : '#FF4A4A', { align: 'center', edge: null });
    // plane tracks from the west; they turn back on the error
    for (let i = 0; i < 3; i++) {
      const [ox, oy] = P([28 + i * 4, 34 - i * 6]), prog = err ? lerp(clamp((b3 - b0) / 1.2), 0, clamp((lt - b3) / .5)) : clamp((lt - b0 + .1) / 1.2);
      const x = lerp(ox, shx - 40, prog * .9), y = lerp(oy, shy - 20, prog * .9) - Math.sin(prog * Math.PI) * 40;
      ctx.setLineDash([10, 10]); ctx.beginPath(); ctx.moveTo(ox, oy); ctx.lineTo(x, y); paint(null, 'rgb(150 255 180 / .6)', 3); ctx.setLineDash([]);
      plane(x, y, Math.atan2(shy - oy, shx - ox) + (err ? Math.PI : 0), 1.1);
    }
    ctx.restore();
    // DEFCON
    const lvl = err ? 5 : lt >= b2 ? 2 : lt >= b1 ? 3 : lt >= b0 ? 4 : 5, dc = ['#FF2A2A', '#FF7A2A', '#FFD22A', '#9AFF4A', '#3AFF7A'];
    rrect(1520, 210, 260, 400, 8); paint('rgb(0 0 0 / .8)', '#2A6A3A', 3);
    pixelText('DEFCON', 1650, 226, 5, NP.white, { align: 'center', edge: null });
    for (let i = 0; i < 5; i++) { const n = i + 1, lit = n === lvl, y = 280 + i * 64; rrect(1550, y, 200, 54, 6); paint(lit ? dc[i] : '#10180F', dc[i], 3); pixelText(String(n), 1650, y + 10, 5, lit ? NP.ink : dc[i], { align: 'center', edge: null }); }
    // the chatbot's report
    rrect(150, 220, 640, 220, 8); paint('rgb(0 12 4 / .92)', '#3AFF7A', 3);
    pixelText('> INTEL ASSISTANT', 172, 240, 4, '#3AFF7A', { edge: null });
    pixelText('SHIP IS CARRYING', 172, 294, 5, NP.white, { edge: null });
    const msg = 'NUCLEAR PARTS', n = Math.floor(clamp((lt + .1) / .35) * msg.length);
    pixelText(msg.slice(0, n) + (frac(t * 3) < .5 && n < msg.length ? '_' : ''), 172, 340, 5, NP.white, { edge: null });
    if (lt > .4) pixelText('(98% SURE)', 172, 390, 4, '#FFD22A', { edge: null });
    if (err) stamp('ERROR: HALLUCINATION', 470, 330, 54, '#FF3030', -.1, { pop: (lt - b3 + .02) / .1, font: 'archivo', blend: 'source-over', alpha: .96 });
    // officers at their consoles
    for (let i = 0; i < 5; i++) { const x = 200 + i * 380; toon(x, 1150, 36, { sil: '#010402', hair: ['short', 'buzz', 'bob', 'short', 'side'][i], legs: false, shadow: false, hat: i === 1 ? 'cap' : undefined }); rrect(x - 150, 880, 300, 80, 6); paint('#0A1A10', '#2A6A3A', 3); for (let k = 0; k < 6; k++) { ell(x - 110 + k * 44, 906, 7); paint(frac(t * 2 + k * .3 + i) < .5 ? (k % 2 ? '#FF4A4A' : '#3AFF7A') : '#10301A'); } }
    ctx.save(); ctx.globalCompositeOperation = 'screen'; ctx.fillStyle = err ? 'rgb(60 255 120 / .06)' : `rgb(255 30 30 / ${.08 + .08 * Math.sin(t * 12)})`; ctx.fillRect(0, 0, W, H); ctx.restore();
    flash(lt, b3, .1, .4, '120 255 160');
    brk('AI INTEL ERROR NEARLY SPARKS CLASH', 'SHIP WRONGLY SAID TO CARRY NUCLEAR PARTS · CNN', lt, { size: 50 });
  });

  // =====================================================================================
  // V4.13 Trump: It's "Super," by decree! — TONIGHT'S POLL: WHAT SHOULD WE CALL AI? SUPERIOR / EXTREME / SUPREME count up, while
  // live from the U.N. General Assembly TRUMP holds forth at the rostrum… and SUPER, which wasn't one of the options, is stamped over
  // the lot; he points at it, beaming.
  function unRostrum(w, h, t, lt, sAt) {
    // the General Assembly: the tall gold wall and emblem over green marble
    vFill('#D8B870', '#8A6A30', 0, 0, w, h);
    ctx.fillStyle = 'rgb(255 255 255 / .08)'; for (let x = 20; x < w; x += 70) ctx.fillRect(x, 0, 26, h * .62);
    const ey = 78;
    ell(w / 2, ey, 62); paint('#F2D48A', '#7A5A1E', 5); ell(w / 2, ey, 42); paint('#3A7ACC', '#7A5A1E', 4);
    ctx.strokeStyle = 'rgb(255 255 255 / .75)'; ctx.lineWidth = 3; ctx.beginPath(); ctx.ellipse(w / 2, ey, 20, 42, 0, 0, TAU); ctx.moveTo(w / 2 - 42, ey); ctx.lineTo(w / 2 + 42, ey); ctx.moveTo(w / 2, ey - 42); ctx.lineTo(w / 2, ey + 42); ctx.stroke();
    for (const sd of [-1, 1]) for (let i = 0; i < 7; i++) { const a = Math.PI / 2 + sd * (.5 + i * .33); ell(w / 2 + Math.cos(a) * 54, ey + Math.sin(a) * 54, 9, 5, a); paint('#E8C060', '#7A5A1E', 2); }
    vFill('#2E5A48', '#123024', 0, h * .62, w, h * .38);
    ctx.fillStyle = 'rgb(255 255 255 / .07)'; for (let i = 0; i < 9; i++) { ctx.beginPath(); ctx.moveTo(hash(i + 3) * w, h * .62); ctx.lineTo(hash(i + 9) * w, h); ctx.lineWidth = 3; ctx.strokeStyle = 'rgb(255 255 255 / .1)'; ctx.stroke(); }
    // Trump at the rostrum: talking, then pointing across at SUPER as it lands
    const hit = lt >= sAt;
    trumpToon(w / 2, h - 12, 34, { legs: false, shadow: false, talk: hit ? undefined : talk(t), mouth: hit ? 'grin' : undefined, eyes: hit ? 'happy' : 'half',
      ...(hit ? { reachL: [-3.2, -9.6], handL: 'point', reachR: [1.7, -5.3] } : { reachL: [-1.9, -7.4 + Math.sin(t * 7) * .5], handL: 'point', reachR: [1.7, -5.3] }) });
    podium(w / 2, h + 14, 32, { col: '#2A4A3A', sealCol: '#1A5AB0', mics: 2 });
    pixelText('LIVE', 18, 14, 4, NP.white, { edge: null }); ell(w - 30, 26, 9); paint(frac(t * 1.5) < .6 ? NP.red : '#601010');
  }
  v4(13, (p, lt, d, t) => {
    const sAt = bt(t, lt, 1) + beatLen() / 2;
    gfxCard({ top: '#2A1470', bottom: '#080420', head: "TONIGHT'S POLL", headCol: NP.magenta, sub: 'CALL 1-900-555-0189' });
    // the poll, in the left two-thirds
    chrome('WHAT SHOULD WE CALL AI?', 640, 262, 60, { font: 'archivo', style: 'white', depth: 5, spacing: 1 });
    const opts = [['SUPERIOR INTELLIGENCE', .3 + .05 * Math.sin(t * 7)], ['EXTREME INTELLIGENCE', .26 + .05 * Math.sin(t * 7 + 2)], ['SUPREME INTELLIGENCE', .32 + .05 * Math.sin(t * 7 + 4)]];
    const x0 = 70, bw = 1140, rh = 148, pk_ = clamp(lt / .9);
    opts.forEach(([label, votes], i) => {
      const ry = 320 + i * rh, k = clamp(pk_ * 1.3 - i * .15), share = votes * easeOut(k), col = [NP.cyan, NP.gold, NP.magenta][i];
      rrect(x0, ry, bw, rh - 22, 12); paint('rgb(0 0 0 / .45)', alpha(col, .8), 3);
      rrect(x0 + 6, ry + 6, (bw - 12) * share, rh - 34, 9); paint(lg(0, ry, 0, ry + rh, [[0, tint(col, .3)], [1, shade(col, .3)]]));
      txt(label, x0 + 34, ry + (rh - 22) / 2 + 2, 50, NP.white, { font: 'archivo', align: 'left', shadow: [3, 4], shadowCol: 'rgb(0 0 0 / .6)' });
      txt(Math.round(share * 100) + '%', x0 + bw - 30, ry + (rh - 22) / 2 + 2, 60, NP.white, { font: 'anton', align: 'right', shadow: [3, 4], shadowCol: 'rgb(0 0 0 / .6)' });
    });
    // live from the U.N.
    otsBox(1262, 206, 574, 560, (w, h) => unRostrum(w, h, t, lt, sAt), { k: inK(lt, .02, .18), label: 'U.N. GENERAL ASSEMBLY', labelCol: NP.blue, labelSize: 32, labelH: 54 });
    if (lt >= sAt) stamp('SUPER', 640, 540, 200, NP.red, -.12, { pop: (lt - sAt) / .1, font: 'archivo', blend: 'source-over', alpha: 1 });
    flash(lt, sAt, .08, .5);
    brk('AI RENAMED "SUPER INTELLIGENCE"', 'TRUMP AT THE U.N. · NOT ONE OF HIS POLL OPTIONS', lt);
  });

  // =====================================================================================
  // V4.14 "Artificial"? Fake to me! — FACT CHECK 89: the TRUTH-O-METER swings to FAKE?, and on the station's own graphic
  // ARTIFICIAL gets struck out and SUPER slapped on.
  v4(14, (p, lt, d, t) => {
    const b1 = bt(t, lt, 1), b2 = bt(t, lt, 2), b3 = bt(t, lt, 3), fakeAt = b2 + beatLen() / 2;
    gfxCard({ top: '#F4B62A', bottom: '#A0520A', head: 'FACT CHECK 89', headCol: NP.red });
    // the station's graphic
    const gx = 150, gy = 250, gw = 820, gh = 500;
    ctx.fillStyle = 'rgb(0 0 0 / .35)'; rrect(gx + 14, gy + 16, gw, gh, 12); ctx.fill();
    rrect(gx, gy, gw, gh, 12); paint(lg(0, gy, 0, gy + gh, [[0, '#2A5AE0'], [1, '#0A1A60']]), '#FFFFFF', 6);
    ctx.fillStyle = 'rgb(255 255 255 / .06)'; for (let y = gy; y < gy + gh; y += 14) ctx.fillRect(gx, y, gw, 6);
    logo89(gx + 80, gy + 80, 48);
    chrome('ARTIFICIAL', gx + gw / 2, gy + 230, 110, { font: 'archivo', style: 'chrome', italic: .12, depth: 9 });
    chrome('INTELLIGENCE', gx + gw / 2, gy + 380, 92, { font: 'archivo', style: 'gold', italic: .12, depth: 8 });
    if (lt >= b1) { const k = clamp((lt - b1) / .15); ctx.beginPath(); ctx.moveTo(gx + 60, gy + 250); ctx.lineTo(gx + 60 + (gw - 120) * k, gy + 200 + Math.sin(k * 9) * 8); paint(null, NP.ink, 22); ctx.beginPath(); ctx.moveTo(gx + 60, gy + 250); ctx.lineTo(gx + 60 + (gw - 120) * k, gy + 200 + Math.sin(k * 9) * 8); paint(null, NP.red, 14); }
    const sk = clamp((lt - b3 + .02) / .12);
    if (sk > 0) {
      ctx.save(); ctx.translate(gx + gw / 2 + 20, gy + 150); ctx.rotate(-.1); const s = lerp(1.9, 1, easeOut(sk)); ctx.scale(s, s);
      ctx.fillStyle = 'rgb(0 0 0 / .35)'; rrect(-196, -60, 400, 124, 10); ctx.fill();
      rrect(-200, -66, 400, 124, 10); paint(lg(0, -66, 0, 58, [[0, '#FFE27A'], [1, '#E8A010']]), NP.ink, 5);
      txt('SUPER', 0, -2, 100, NP.red, { font: 'anton', spacing: 6 });
      for (const sd of [-1, 1]) { ctx.fillStyle = '#C9CFDB'; ctx.fillRect(sd * 170 - 14, -60, 28, 6); }
      ctx.restore();
    }
    // the TRUTH-O-METER
    const cx = 1440, cy = 720, R = 330, segs = [['TRUE', '#2EBD5B'], ['HALF', '#F4D24A'], ['FALSE', '#FF7A2A'], ['FAKE?', '#C8141E']];
    txt('TRUTH-O-METER', cx, 300, 50, NP.ink, { font: 'bungee' });
    segs.forEach(([lab, col], i) => {
      const a0 = Math.PI + i / 4 * Math.PI, a1 = Math.PI + (i + 1) / 4 * Math.PI;
      ctx.beginPath(); ctx.moveTo(cx, cy); ctx.arc(cx, cy, R, a0, a1); ctx.closePath(); paint(col, NP.ink, 5);
      const am = (a0 + a1) / 2; txt(lab, cx + Math.cos(am) * R * .68, cy + Math.sin(am) * R * .68, 40, NP.white, { font: 'archivo', stroke: NP.ink, sw: 6, rot: am + Math.PI / 2 });
    });
    ell(cx, cy, 70); paint('#2A2A34', NP.ink, 5);
    const wig = lt < fakeAt ? Math.PI * (1.2 + .55 * Math.abs(Math.sin(lt * 7))) : Math.PI * 1.875 + Math.sin((lt - fakeAt) * 40) * .06 * Math.exp(-(lt - fakeAt) * 6);
    ctx.save(); ctx.translate(cx, cy); ctx.rotate(wig); poly([[0, -14], [R - 30, 0], [0, 14]]); paint(NP.ink, NP.ink, 3); ctx.restore();
    ell(cx, cy, 26); paint(NP.gold, NP.ink, 4);
    flash(lt, b3, .08, .35);
    brk('TRUMP: "ARTIFICIAL" SOUNDS "FAKE"', 'U.S. DOCUMENTS TO SAY "SUPER" INSTEAD', lt);
  });

  // =====================================================================================
  // V4.15 Ten days after "pace" — surprise! — push in on the desk: the wall calendar rips from SEP 12 (PACE THE FRONTIER) to SEP 22 in a
  // blur of pages, a gift box on the desk rattles harder and harder, and both anchors lean away.
  const DAYS = ['SAT', 'SUN', 'MON', 'TUE', 'WED', 'THU', 'FRI'];
  function calPage(w, h, day, note) {
    rrect(-w / 2, -h / 2, w, h, 8); paint('#FBFAF4', NP.ink, 5);
    rrect(-w / 2, -h / 2, w, 72, [8, 8, 0, 0]); paint(NP.red, NP.ink, 5); txt('SEPTEMBER', 0, -h / 2 + 37, 40, NP.white, { font: 'archivo', spacing: 3 });
    txt(DAYS[(day - 12 + 700) % 7], 0, -h / 2 + 108, 40, NP.ink, { font: 'archivo', spacing: 4 });
    txt(String(day), 0, 30, 190, day === 22 ? NP.red : NP.ink, { font: 'anton' });
    if (note) { txt('PACE THE FRONTIER!', 0, h / 2 - 34, 30, NP.blue, { font: 'marker', rot: -.04 }); ctx.beginPath(); ctx.ellipse(0, 30, 118, 96, .1, 0, TAU); paint(null, NP.blue, 6); }
  }
  function giftBox(x, y, w, h, o = {}) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(o.rot ?? 0);
    ctx.fillStyle = 'rgb(0 0 0 / .3)'; ell(0, 4, w * .6, 14); ctx.fill();
    rrect(-w / 2, -h, w, h, 6); paint(lg(0, -h, 0, 0, [[0, '#F03A4A'], [1, '#A0101E']]), NP.ink, 5);
    ctx.fillStyle = NP.gold; ctx.fillRect(-14, -h, 28, h); ctx.strokeStyle = NP.ink; ctx.lineWidth = 3; ctx.strokeRect(-14, -h, 28, h);
    if (o.lid !== false) {
      const ly = -h - (o.lift ?? 0);
      ctx.save(); ctx.translate(0, ly); ctx.rotate(o.lidRot ?? 0);
      rrect(-w / 2 - 12, -34, w + 24, 38, 6); paint(lg(0, -34, 0, 4, [[0, '#FF5A6A'], [1, '#C0182A']]), NP.ink, 5); ctx.fillStyle = NP.gold; ctx.fillRect(-14, -34, 28, 38);
      for (const sd of [-1, 1]) { ctx.beginPath(); ctx.ellipse(sd * 34, -48, 36, 20, sd * -.4, 0, TAU); paint(NP.gold, NP.ink, 4); }
      ell(0, -40, 14); paint(NP.goldDk, NP.ink, 3);
      ctx.restore();
    }
    if (o.tag) { ctx.save(); ctx.translate(w / 2 - 10, -h * .4); ctx.rotate(.25); rrect(0, -18, 110, 38, 4); paint('#FBFAF4', NP.ink, 3); txt(o.tag, 55, 1, 18, NP.ink, { font: 'marker', maxW: 100 }); ctx.restore(); }
    ctx.restore();
  }
  v4(15, (p, lt, d, t) => {
    const r0 = bt(t, lt, .5), step = beatLen() / 4, torn = clamp(Math.floor((lt - r0) / step) + 1, 0, 10), rattle = clamp(lt / d) ** 1.5;
    const bxX = 870, bxY = 716, jig = rattle * (Math.sin(t * 60) * .12), hop = Math.abs(Math.sin(t * 40)) * rattle * 26;
    deskShot(t, { mugs: 8, vol: 1.75, cam: { x: 960, y: 470, zoom: 1.28 },
      wall: (w, h) => {
        vFill('#2A2E48', '#12142A', 0, 0, w, h);
        ctx.save(); ctx.translate(w / 2, 245); calPage(330, 400, 12 + torn, torn === 0); ctx.restore();
        for (let k = 0; k < 2; k++) { const idx = torn - 1 - k; if (idx < 0) continue; const since = lt - r0 - idx * step; if (since < 0 || since > .2) continue; const u = since / .2;
          ctx.save(); ctx.translate(w / 2 + u * 420 * (idx % 2 ? -1 : 1), 245 - u * 260); ctx.rotate(u * 2.6 * (idx % 2 ? -1 : 1)); ctx.scale(1 - u * .4, 1 - u * .4); ctx.globalAlpha = 1 - u * .6; calPage(330, 400, 12 + idx, idx === 0); ctx.restore(); }
        if (torn === 10) { const k = clamp((lt - r0 - 9 * step) / .15); ctx.beginPath(); ctx.ellipse(w / 2, 275, 130 * k, 108 * k, -.1, 0, TAU); paint(null, NP.red, 10); }
      },
      clawd: { rot: -.12 * rattle, lookX: .9, eyes: rattle > .4 ? 'wide' : 'normal', dy: -.2 * rattle },
      val: { rot: .12 * rattle, lookX: -.9, eyes: 'wide', brows: 'up', mouth: rattle > .5 ? 'O' : 'o' },
      front: () => { giftBox(bxX + jig * 60, bxY - hop, 190, 130, { rot: jig, lift: hop * .6, lidRot: -jig * 1.5, tag: 'SEP 22' }); if (rattle > .3) for (let i = 0; i < 4; i++) { const sd = i % 2 ? 1 : -1; ctx.beginPath(); ctx.moveTo(bxX + sd * (120 + i * 8), bxY - 120 + i * 24); ctx.lineTo(bxX + sd * (150 + i * 8), bxY - 128 + i * 24); paint(null, NP.ink, 5); } } });
    brk('BOTH LABS SHIP NEW MODELS', 'TEN DAYS AFTER THE CALL TO PACE THE FRONTIER', lt);
  });

  // =====================================================================================
  // V4.16 Opus 5.5: "Hi, guys!" — the box bursts: a small Clawd with a 5.5 sticker springs out and waves sheepishly (HI, GUYS!);
  // anchor Clawd blushes. Ninety minutes later (the clock spins), an inset pops up: GPT-6 waves too.
  v4(16, (p, lt, d, t) => {
    const b0 = bt(t, lt), b1 = bt(t, lt, 1), b3 = bt(t, lt, 3), b3h = b3 + beatLen() / 2, open = lt >= b0 + .02, since = lt - b0;
    const bxX = 870, bxY = 716, spring = open ? backOut(clamp(since / .22), 3) : 0, wave = Math.sin(t * 16);
    deskShot(t, { mugs: 9, vol: 1.9, cam: { x: 960, y: 530, zoom: 1.04 + p * .04 },
      clawd: { eyes: lt >= b1 ? 'happy' : 'wide', blush: lt >= b1, lookX: .8, lookY: .3, mouth: lt >= b1 ? 'smile' : 'o', talk: undefined },
      val: { lookX: -.9, eyes: lt >= b1 ? 'happy' : 'wide', mouth: lt >= b1 ? 'grin' : 'O' },
      front: () => {
        // the spring and the little Clawd on it
        const top = bxY - 130 - spring * 120;
        if (open) { ctx.beginPath(); for (let i = 0; i <= 24; i++) { const u = i / 24; ctx.lineTo(bxX + Math.sin(u * 8 * TAU) * 22, lerp(bxY - 120, top + 10, u)); } paint(null, NP.ink, 9); ctx.beginPath(); for (let i = 0; i <= 24; i++) { const u = i / 24; ctx.lineTo(bxX + Math.sin(u * 8 * TAU) * 22, lerp(bxY - 120, top + 10, u)); } paint(null, '#C9CFDB', 5); }
        if (open) {
          newsClawd(bxX, top + 12, 16, { suit: false, legs: false, eyes: 'happy', blush: true, mouth: 'smile', rot: Math.sin(t * 9) * .08 * (1 - clamp(since)), aR: 1.3 + wave * .35, aL: -.4, dy: -Math.sin(since * 20) * .3 * Math.exp(-since * 4) });
          ctx.save(); ctx.translate(bxX + 50, top + 12 - 3.1 * 16); ctx.rotate(-.15); ell(0, 0, 30); paint(NP.gold, NP.ink, 3); txt('5.5', 0, 1, 27, NP.ink, { font: 'anton' }); ctx.restore();
        }
        giftBox(bxX, bxY, 190, 130, { lid: !open });
        if (open && since < .5) { const u = since / .5; ctx.save(); ctx.translate(bxX - 420 * u, bxY - 160 - 900 * u + 400 * u * u); ctx.rotate(-u * 6); rrect(-107, -34, 214, 38, 6); paint('#E0303A', NP.ink, 5); ctx.restore(); }
      } });
    if (open) confetti(t, since, 40, { x0: 500, x1: 1300, y0: 300 });
    speech('HI, GUYS!', 1120, 232, { size: 88, font: 'anton', tail: [930, 360], pop: pk(lt, b1, .14) });
    // ninety minutes later…
    const ck = clamp((lt - b3 + .05) / .15);
    if (ck > 0) {
      ctx.save(); ctx.translate(660, 270); ctx.scale(backOut(ck, 2), backOut(ck, 2));
      ell(0, 0, 70); paint('#FBFAF4', NP.ink, 5); const sp = (lt - b3) * 30;
      ctx.beginPath(); ctx.moveTo(0, 0); ctx.lineTo(Math.sin(sp) * 50, -Math.cos(sp) * 50); ctx.moveTo(0, 0); ctx.lineTo(Math.sin(sp / 12) * 34, -Math.cos(sp / 12) * 34); paint(null, NP.ink, 7);
      rrect(-80, 80, 160, 50, 8); paint(NP.red, NP.ink, 4); txt('+90 MIN', 0, 106, 32, NP.white, { font: 'archivo' });
      ctx.restore();
    }
    otsBox(110, 170, 460, 300, (w, h) => {
      vFill('#1A3A2A', '#0A1A12'); ctx.fillStyle = 'rgb(255 255 255 / .05)'; for (let y = 0; y < h; y += 14) ctx.fillRect(0, y, w, 6);
      giftBox(w / 2, h - 30, 170, 90, { lid: false });
      computer(w / 2, h - 90, 20, { label: 'GPT-6', face: 'happy', legs: false, aR: 1.2 + Math.sin(t * 16 + 1) * .35, eR: .3, hand: 'wave', aL: -.6 });
    }, { k: clamp((lt - b3h) / .18), label: 'GPT-6 SOL & LUNA', labelCol: '#2A7A4A', labelSize: 30, labelH: 50 });
    brk('CLAUDE OPUS 5.5 RELEASED', 'OPENAI SHIPS GPT-6 SOL & LUNA 90 MINUTES LATER', lt, { tab: 'UPDATE' });
  });
})();

;
// ---- styles/newscast/ch/c09_finale.js ----
// c09_finale — Chorus 4 (the network special and the sign-off) and the outro (the tape rewind).
// Sub-shots follow the sung lines (linesOf('C4')); word times inside a line are fractions of that line, measured from the take.
//   L1 "We didn't start the scaling"          the biggest bumper: a recap wall of earlier headlines over the laser grid, the globe,
//                                             every swoosh at once, the hook slamming on word by word
//   L2 "It was always training, …"            aerobics at the anchor desk: CLAWD and VAL pump dumbbells in sweatbands while every monitor
//                                             on the set plots the curve. "…and the curves kept gaining": push into the video wall; the curve
//                                             notches up on the beats, goes vertical, breaks the frame, and the camera tilts up after it
//                                             through the lighting truss and the roof into the night sky
//   L3 "We didn't start the scaling"          the whole team at the desk (plus the brand-new Opus 5.5 and GPT-6), hook in chrome, confetti cannons
//   L4 "Now we swear we'll try to pace it —"  CHANNEL 89 SPORTS instant replay in SLOW: the pace car crawls, the field bunched up behind it.
//      "— but we'd rather race it!"          the VCR slams to FF: the pace car ducks into the pits, the checkered flag drops, the field is gone
//   L5 "We didn't start the scaling"          the team jumps for joy… and the tape PAUSEs on the peak (the 80s sitcom freeze-frame)
//   L6 "But when we log off…"                 sign-off: the anchors wave good night, the lights go out bank by bank, ON AIR goes dark
//      "…will it still train on?"             END OF BROADCAST DAY test card; the TV switches off
//      "(And on, and on, and on…)"            we're outside the TV now: in the dark room the AI's beige computer is still training, its log
//                                             printing AND ON; a tiny red curve glints in the dead TV glass (V1.11); it picks up the remote: REW
//   outro                                     the TV blooms on and we push back into it: the whole special rewinds (REW ◀◀, the date running back
//                                             to JUN 2017, the counter to 0:00:00), STOP on the blue screen, then PLAY: colour bars and the station
//                                             slate again, now the end card, and the OSD says EPOCH 2.
// Colour run: magenta laser wall → studio blue + lime neon → black-to-night sky → purple-and-gold special → speedway green → red freeze → dimming blue →
// test-card grey → black → dark room, green phosphor → the rewind (everything) → VCR blue → colour bars.
(() => {
  // ================================================================================================
  // timing
  // ================================================================================================
  const LC = () => linesOf('C4');
  const C4S = () => segByKey('C4');
  const OUTL = () => LINES.find(l => l.sec === 'outro');
  // sub-shot i runs from its sung line's start to the next line's start (the last one to the end of the C4 window, through the "and on" tag)
  const win = i => { const L = LC(); return { a: i ? L[i].start : C4S().start, b: i + 1 < L.length ? L[i + 1].start : C4S().end }; };
  const subOf = t => { const L = LC(); let i = 0; for (let j = 1; j < L.length; j++) if (t >= L[j].start) i = j; return i; };
  const wT = (l, f) => l.start + f * (l.end - l.start);
  const snapB = (x, q = .5) => onBeat(0, Math.round(bpOf(x) / q) * q);
  const HOOK = ['WE', "DIDN'T", 'START', 'THE', 'SCALING'];
  const HOOK_F = { 0: [0, .19, .41, .54, .73], 2: [0, .31, .51, .66, .8], 4: [0, .34, .53, .68, .83] };
  const hookTimes = i => { const l = LC()[i]; return HOOK_F[i].map(f => wT(l, f)); };
  const flash = (t, t0, dur = .1, a = .6, col = '255 255 255') => { const k = (t - t0) / dur; if (k >= 0 && k < 1) { ctx.fillStyle = `rgb(${col} / ${a * (1 - k)})`; ctx.fillRect(-200, -200, W + 400, H + 400); } };
  const kickZ = (t, t0, amt = .04, tau = .12) => t >= t0 ? amt * Math.exp(-(t - t0) / tau) : 0;

  // ================================================================================================
  // shared bits
  // ================================================================================================
  // the hook as chrome, popping on word by word as it's sung: WE DIDN'T START / THE SCALING (gold)
  function hook(t, ts, o) {
    const rows = [[[0, 1, 2], o.y1, o.s1, 'chrome'], [[3, 4], o.y2, o.s2, 'gold']];
    for (const [ids, y, size, style] of rows) {
      const sp = Math.round(size * .03), gap = size * .3, ws = ids.map(i => textW(HOOK[i], size, 'archivo', sp));
      let x = (o.x ?? W / 2) - (ws.reduce((a, b) => a + b, 0) + gap * (ws.length - 1)) / 2;
      ids.forEach((i, j) => {
        const k = (t - ts[i] + .02) / .12;
        if (k > 0) chrome(HOOK[i], x + ws[j] / 2, y - (i === 4 ? pulse(t, 7) * 6 : 0), size, { font: 'archivo', style, italic: .14, depth: Math.round(size * .09), spacing: sp, s: lerp(1.9, 1, easeOut(clamp(k))), alpha: clamp(k * 3) });
        x += ws[j] + gap;
      });
    }
  }
  const CONF = ['#FF4A6A', NP.gold, '#4AD0FF', '#7CFF8A', '#C07AFF', '#FFFFFF'];
  function confettiPiece(x, y, t, i) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(t * (4 + hash(i + 7) * 5) + i); ctx.scale(1, .2 + .8 * Math.abs(Math.sin(t * 8 + i)));
    ctx.fillStyle = CONF[i % CONF.length]; ctx.fillRect(-10, -6, 20, 12); ctx.restore();
  }
  // a confetti cannon firing from (x, y) toward angle a0 at time t0
  function confettiBurst(t, t0, x, y, a0, n, seed) {
    const s = t - t0; if (s < 0) return;
    for (let i = 0; i < n; i++) {
      const a = a0 + (hash2(seed, i) - .5) * .9, v = 1100 + hash2(seed, i + 99) * 1300, dd = v * .28 * (1 - Math.exp(-s / .28));
      const px = x + Math.cos(a) * dd + Math.sin(t * 3 + i) * 24 * s, py = y + Math.sin(a) * dd + 300 * s * s + 60 * s;
      if (py < H + 40) confettiPiece(px, py, t, i + seed);
    }
  }
  // confetti falling from above since t0
  function confettiRain(t, t0, n, seed) {
    const s = t - t0; if (s < 0) return;
    for (let i = 0; i < n; i++) {
      const x = hash2(seed, i) * (W + 200) - 100 + Math.sin(t * 2.4 + i) * 30, y = -30 - hash2(seed, i + 50) * 500 + s * (260 + hash2(seed, i + 80) * 260);
      if (y > -30 && y < H + 30) confettiPiece(x, y, t, i + seed);
    }
  }
  // the station's OSD, drawn by hand (inside pictures the kit's overlay can't reach: the rewind, the TV switching off)
  const OSD_S = { PLAY: '▶', PAUSE: '❚', FF: '▶▶', REW: '◀◀', STOP: '■' };
  function osd(t, mode, date, counter) {
    const blink = (mode === 'REW' || mode === 'FF' || mode === 'PAUSE') && frac(t * 3) > .6;
    if (!blink) pixelText(`${mode} ${OSD_S[mode] ?? ''}`.trim(), 1796, 58, 5, NP.white, { align: 'right', shadow: [.6, .6] });
    if (date) pixelText(date, 1796, 108, 7, NP.white, { align: 'right', shadow: [.5, .5] });
    if (counter) pixelText(counter, 1796, 172, 5, NP.white, { align: 'right', shadow: [.6, .6] });
  }
  const hms = s => { s = Math.max(0, Math.floor(s)); return `${Math.floor(s / 3600)}:${String(Math.floor(s / 60) % 60).padStart(2, '0')}:${String(s % 60).padStart(2, '0')}`; };
  // pixelText plus an '@' (the kit's VCR font has none)
  const AT = '.###.#...##.####.#.##.####....#.####';
  function pix(str, x, y, px, col, o = {}) {
    const w = pixelW(str, px), x0 = o.align === 'center' ? x - w / 2 : o.align === 'right' ? x - w : x;
    const parts = String(str).split('@');
    let cx = x0;
    parts.forEach((part, i) => {
      if (part) pixelText(part, cx, y, px, col, { edge: o.edge, alpha: o.alpha });
      cx += [...part].length * 6 * px;
      if (i < parts.length - 1) {
        ctx.save(); if (o.alpha !== undefined) ctx.globalAlpha *= o.alpha;
        for (const [c, g] of [[o.edge === undefined ? '#000' : o.edge, px * .34], [col, 0]]) {
          if (!c) continue; ctx.fillStyle = c;
          for (let r = 0; r < 7; r++) for (let q = 0; q < 5; q++) if (AT[r * 5 + q] === '#') ctx.fillRect(cx + q * px - g, y + r * px - g, px + g * 2, px + g * 2);
        }
        ctx.restore(); cx += 6 * px;
      }
    });
  }
  function sparks(x, y, since, seed, n = 14, len = 90) {
    if (since < 0 || since > .35) return;
    const k = since / .35;
    for (let i = 0; i < n; i++) {
      const a = hash2(seed, i) * TAU, L = len * (.4 + hash2(seed, i + 30)) * easeOut(k), gy = 200 * k * k;
      ctx.beginPath(); ctx.moveTo(x + Math.cos(a) * L * .6, y + Math.sin(a) * L * .6 + gy * .6); ctx.lineTo(x + Math.cos(a) * L, y + Math.sin(a) * L + gy);
      ctx.strokeStyle = i % 2 ? `rgb(255 240 160 / ${1 - k})` : `rgb(255 170 60 / ${1 - k})`; ctx.lineWidth = 4; ctx.lineCap = 'round'; ctx.stroke();
    }
    glint(x, y, 120 * (1 - k), 1 - k, '#FFF6C0');
  }

  // ================================================================================================
  // L1 — the biggest bumper: a recap wall of earlier headlines (each tile a real shot, painted once into a cache)
  // ================================================================================================
  const RECAP = ['V1.1', 'V2.1', 'V3.3', 'V4.7', 'V1.5', 'V2.7', 'V3.16', 'V4.12', 'V1.8', 'V2.11',
    'V1.11', 'V2.14', 'V3.9', 'V4.3', 'V1.14', 'V3.1', 'V2.9', 'V4.16', 'V1.9', 'V3.15'];
  function fallbackTile(key) {
    const s = segByKey(key);
    vFill('#1D3FB0', '#060D38'); ctx.fillStyle = 'rgb(255 255 255 / .05)'; for (let y = 0; y < H; y += 14) ctx.fillRect(0, y, W, 6);
    logo89(W / 2, 380, 190);
    txt(String(s?.text ?? key).toUpperCase(), W / 2, 740, 96, NP.white, { font: 'archivo', maxW: W - 220 });
    if (s?.date) pixelText(s.date, W / 2, 830, 11, NP.gold, { align: 'center' });
  }
  function recapTile(key) {
    return cached('fin|tile|' + key, 480, 270, (w, h) => {
      ctx.save(); ctx.beginPath(); ctx.rect(0, 0, w, h); ctx.clip(); ctx.scale(w / W, h / H);
      let ok = false;
      if (SHOTS[key]) { try { paintShot(key, .62); ok = true; } catch (e) { ok = false; } }
      if (!ok) fallbackTile(key);
      ctx.restore();
    });
  }
  function recapWall(t, a) {
    const cols = 5, rows = 2, x0 = 96, y0 = 186, gap = 22, tw = (W - 2 * x0 - gap * (cols - 1)) / cols, th = tw * 9 / 16;
    for (let r = 0; r < rows; r++) for (let c = 0; c < cols; c++) {
      const i = r * cols + c, k = clamp((t - a - i * .028) / .2); if (k <= 0) continue;
      const flipT = a + beatLen() * (1.1 + ((i * 7) % 10) * .21), fk = clamp((t - flipT) / .16);
      const key = RECAP[(fk >= .5 ? i + 10 : i) % RECAP.length], sx = fk > 0 && fk < 1 ? Math.abs(Math.cos(fk * Math.PI)) : 1;
      const e = backOut(k, 1.1), cx = lerp(W / 2, x0 + c * (tw + gap) + tw / 2, e), cy = lerp(620, y0 + r * (th + gap) + th / 2, e);
      const ww = lerp(30, tw, e) * sx, hh = lerp(18, th, e);
      ctx.save(); ctx.translate(cx, cy);
      ctx.fillStyle = 'rgb(0 0 0 / .5)'; ctx.fillRect(-ww / 2 + 9, -hh / 2 + 11, ww, hh);
      ctx.drawImage(recapTile(key), -ww / 2, -hh / 2, ww, hh);
      ctx.fillStyle = 'rgb(0 0 0 / .18)'; for (let yy = -hh / 2; yy < hh / 2; yy += 5) ctx.fillRect(-ww / 2, yy, ww, 2);
      ctx.lineWidth = 5; ctx.strokeStyle = '#EEF3FF'; ctx.strokeRect(-ww / 2, -hh / 2, ww, hh);
      ctx.restore();
      if (fk > .5 && fk < 1) glint(cx + tw * .42, cy - th * .42, 70, 1 - fk);
    }
  }
  function bumperShot(t) {
    const w = win(0), ts = hookTimes(0), tS = ts[4], pk = clamp((t - w.a) / (w.b - w.a));
    const bz = 1 + .05 * pk + kickZ(t, tS, .05); ctx.save(); ctx.translate(W / 2, 330); ctx.scale(bz, bz); ctx.translate(-W / 2, -330);
    laserGrid(t, { horizon: 600, col: NP.magenta, speed: 2.6, sky: ['#05021A', '#3A0A5A'] });
    ctx.save(); ctx.translate(W / 2, 600); ctx.rotate(t * .3); ctx.fillStyle = 'rgb(255 120 220 / .07)';
    for (let i = 0; i < 18; i++) { ctx.rotate(TAU / 18); poly([[0, 0], [1600, -110], [1600, 110]]); ctx.fill(); } ctx.restore();
    recapWall(t, w.a);
    const gk = easeOut(clamp((t - w.a) / .7));
    globe(215, lerp(1100, 770, gk), 125, t * 1.3, { col: NP.cyan }); globe(1705, lerp(1100, 770, gk), 125, -t * 1.3 + 2, { col: NP.cyan });
    [[NP.red, 610, 66], [NP.gold, 690, 40], [NP.blue, 760, 54], [NP.cyan, 840, 30], [NP.magenta, 920, 46]]
      .forEach(([c, y, th], i) => swoosh(clamp((t - ts[i] + .06) / .5), y, c, { len: 1700, th }));
    hook(t, ts, { y1: 688, s1: 118, y2: 862, s2: 176 });
    sweepGlint(W / 2 - 640, W / 2 + 640, 830, (t - tS - .1) / .5, 150);
    glint(1580, 250, 110 * pulse(t, 5), pulse(t, 5));
    ctx.restore();
    flash(t, tS, .12, .5);
  }

  // ================================================================================================
  // L2 — "It was always training": aerobics at the desk, every monitor plotting the curve;
  //      "…and the curves kept gaining": into the video wall, the curve goes vertical and out through the roof
  // ================================================================================================
  const PNL = { x: 700, y: 80, w: 520, h: 540 }, PLT = { x0: 770, x1: 1160, y0: 470, y1: 160 };
  const cY = u => PLT.y0 - (PLT.y0 - PLT.y1) * (Math.exp(6 * u) - 1) / (Math.exp(6) - 1);
  const cX = u => lerp(PLT.x0, PLT.x1, u);
  function neon(pts, col, w = 8) {
    ctx.beginPath(); pts.forEach(([a, b], i) => i ? ctx.lineTo(a, b) : ctx.moveTo(a, b));
    ctx.lineJoin = 'round'; ctx.lineCap = 'round';
    ctx.strokeStyle = alpha(col, .22); ctx.lineWidth = w * 3; ctx.stroke(); ctx.strokeStyle = col; ctx.lineWidth = w; ctx.stroke();
    ctx.strokeStyle = 'rgb(255 255 255 / .85)'; ctx.lineWidth = w * .3; ctx.stroke();
  }
  // per-beat notches: 0 → 1 over n beats from beat b0, each beat eases up a step
  const notch = (t, b0, n) => { const b = bpOf(t) - b0; return clamp((Math.floor(b) + easeOut(clamp(frac(b) * 5))) / n); };
  // the centre video wall (set coords)
  function wallChart(t, u) {
    const { x, y, w, h } = PNL;
    vFill('#050B26', '#01030E', x, y, w, h);
    ctx.strokeStyle = 'rgb(80 160 255 / .28)'; ctx.lineWidth = 2; ctx.beginPath();
    for (let d = 0; d < 4; d++) for (let m = 1; m < 10; m += (m < 3 ? 1 : 3)) { const v = (d + Math.log10(m)) / 4, gy = PLT.y0 - v * (PLT.y0 - PLT.y1); ctx.moveTo(PLT.x0, gy); ctx.lineTo(PLT.x1, gy); }
    for (let i = 0; i <= 8; i++) { const gx = lerp(PLT.x0, PLT.x1, i / 8); ctx.moveTo(gx, PLT.y1); ctx.lineTo(gx, PLT.y0); }
    ctx.stroke();
    ctx.strokeStyle = 'rgb(200 225 255 / .9)'; ctx.lineWidth = 4; ctx.beginPath(); ctx.moveTo(PLT.x0, PLT.y1 - 20); ctx.lineTo(PLT.x0, PLT.y0); ctx.lineTo(PLT.x1 + 20, PLT.y0); ctx.stroke();
    pixelText('COMPUTE', x + 30, y + 26, 4, NP.lime, { edge: null });
    poly([[x + 206, y + 52], [x + 234, y + 52], [x + 220, y + 28]]); ctx.fillStyle = NP.lime; ctx.fill();
    const pts = []; for (let i = 0; i <= 60; i++) pts.push([cX(u * i / 60), cY(u * i / 60)]);
    neon(pts, NP.lime, 8);
    glint(cX(u), cY(u), 70, .6 + .4 * pulse(t, 5));
    rrect(x + 250, y + 14, 250, 44, 6); paint('rgb(0 0 0 / .6)', alpha(NP.lime, .6), 2);
    pixelText(`${(1 + u * 8.9).toFixed(1)}E+${22 + Math.floor(u * 4)} FLOP`, x + 375, y + 24, 3.4, NP.lime, { align: 'center', edge: null });
  }
  function miniCurve(w, h, t, i) {
    ctx.fillStyle = '#031208'; ctx.fillRect(0, 0, w, h);
    ctx.strokeStyle = 'rgb(80 220 130 / .22)'; ctx.lineWidth = 1.5; ctx.beginPath();
    for (let g = 1; g < 4; g++) { ctx.moveTo(g * w / 4, 0); ctx.lineTo(g * w / 4, h); ctx.moveTo(0, g * h / 4); ctx.lineTo(w, g * h / 4); } ctx.stroke();
    const col = [NP.lime, NP.cyan, NP.gold, NP.magenta][i % 4], ex = 3 + (i % 3), k = .25 + .75 * notch(t, Math.floor(bpOf(t) / 6) * 6 - (i % 3), 6);
    const pts = []; for (let j = 0; j <= 24; j++) { const v = k * j / 24; pts.push([10 + v * (w - 20), h - 10 - (h - 20) * (Math.exp(ex * v) - 1) / (Math.exp(ex) - 1)]); }
    neon(pts, col, 4);
    glint(pts.at(-1)[0], pts.at(-1)[1], 24, .8);
  }
  function monitorBank(px, py, pw, ph, t, seed) {
    ctx.save(); rrect(px, py, pw, ph, 10); ctx.clip();
    vFill('#0E1638', '#060A1E', px, py, pw, ph);
    ctx.fillStyle = 'rgb(255 255 255 / .04)'; for (let yy = py; yy < py + ph; yy += 14) ctx.fillRect(px, yy, pw, 6);
    const mw = 172, mh = 126, gx = (pw - 3 * mw) / 4;
    for (let r = 0; r < 2; r++) for (let c = 0; c < 3; c++) {
      const i = seed + r * 3 + c, x = px + gx + c * (mw + gx), y = py + 58 + r * (mh + 104);
      ctx.fillStyle = '#1A1E2C'; ctx.fillRect(x + mw / 2 - 14, y + mh + 16, 28, 80);
      crtTV(x, y, mw, mh, (w, h) => miniCurve(w, h, t, i), { style: 'grey' });
    }
    ctx.restore();
    rrect(px, py, pw, ph, 10); paint(null, '#8FA6E0', 5);
  }
  const dumbbell = sz => () => {
    rrect(-sz * .95, -sz * .09, sz * 1.9, sz * .18, sz * .09); paint('#A9AFBD', NP.ink, 3);
    for (const sd of [-1, 1]) { rrect(sd * sz * .78 - sz * .2, -sz * .36, sz * .4, sz * .72, sz * .1); paint('#2A2E3A', NP.ink, 3.5); ctx.fillStyle = 'rgb(255 255 255 / .2)'; ctx.fillRect(sd * sz * .78 - sz * .14, -sz * .3, sz * .08, sz * .6); }
  };
  function sweatband(x, y, w, h, rot = 0) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(rot);
    rrect(-w / 2, -h / 2, w, h, h * .4); paint('#F7F6F1', NP.ink, 4);
    ctx.fillStyle = NP.red; ctx.fillRect(-w / 2 + 3, -h * .12, w - 6, h * .24);
    ctx.fillStyle = 'rgb(0 0 0 / .08)'; for (let i = -w / 2 + 8; i < w / 2; i += 9) ctx.fillRect(i, -h / 2 + 3, 3, h - 6);
    ctx.restore();
  }
  function trainShot(t) {
    const w = win(1), l = LC()[1], tAnd = snapB(wT(l, .537), 1), tCurv = wT(l, .681), tKept = wT(l, .771), tGain = wT(l, .831);
    const bp = bpOf(t), up = (Math.cos(bp * Math.PI) + 1) / 2, upL = ease(up), upR = ease(1 - up);
    // the curve: notches up a step per beat, then goes vertical on "gaining"
    const b0 = Math.round(bpOf(w.a)), nb = bpOf(tAnd) - b0;
    let u = .12 + .56 * notch(Math.min(t, tAnd), b0, nb);
    if (t >= tAnd) u = .68 + .12 * easeOut(clamp((t - tAnd) / .15)) + .08 * easeOut(clamp((t - tCurv) / .12)) + .08 * easeOut(clamp((t - tKept) / .12)) + .04 * easeOut(clamp((t - tGain) / .08));
    const gK = clamp((t - tGain - .06) / Math.max(.2, w.b - tGain - .06)), ext = 3400 * easeIn(gK), tipY = cY(1) - ext;
    const lagY = cY(1) - 3400 * easeIn(clamp(gK - .03));
    // camera: two-shot → push into the wall → tilt up after the tip
    const pz = ease(clamp((t - tAnd) / .45));
    let cx = lerp(960, 975, pz), cy = lerp(488, 330, pz), z = lerp(1.1 + .03 * clamp((t - w.a) / 2), 1.75, pz);
    if (gK > 0) { cy = Math.min(cy, lagY + 160); z = lerp(1.75, 1.35, ease(clamp(gK * 2))); }
    camBegin(cx, cy, z);
    // above the set: the night sky, the roof, the rafters (only seen on the tilt)
    if (gK > 0) {
      ctx.fillStyle = '#01020A'; ctx.fillRect(-1200, -4400, W + 2400, 4400);
      ctx.fillStyle = lg(0, -4400, 0, -700, [[0, '#000006'], [1, '#0B1848']]); ctx.fillRect(-1200, -4400, W + 2400, 3700);
      for (let i = 0; i < 160; i++) { ctx.fillStyle = `rgb(255 255 255 / ${.3 + .6 * hash(i + 11)})`; ctx.fillRect(hash(i) * 3200 - 640, -4300 + hash(i + 50) * 3500, 3, 3); }
      ell(640, -2300, 90); paint('#FFF4D0'); ctx.fillStyle = 'rgb(255 250 220 / .12)'; ell(640, -2300, 170); ctx.fill();
      ctx.fillStyle = '#0B0D18'; ctx.fillRect(-1200, -720, W + 2400, 700);
      ctx.fillStyle = '#161A2A'; for (let x = -1200; x < W + 1200; x += 260) ctx.fillRect(x, -720, 26, 700);
      rrect(-1200, -470, W + 2400, 70, 0); paint('#2A2F42', '#0A0B12', 4); ctx.fillStyle = '#4A5068'; for (let x = -1180; x < W + 1200; x += 60) { ell(x, -455, 5); ctx.fill(); ell(x, -415, 5); ctx.fill(); }
      ctx.strokeStyle = '#1E2334'; ctx.lineWidth = 3; ctx.beginPath(); for (let x = -1200; x < W + 1200; x += 30) { ctx.moveTo(x, -230); ctx.lineTo(x + 30, -200); } ctx.stroke();
      ctx.fillStyle = '#2A3048'; ctx.fillRect(-1200, -236, W + 2400, 8); ctx.fillRect(-1200, -200, W + 2400, 8);
      pixelText('EXIT', 300, -360, 6, '#FF4040', { edge: '#300' });
    }
    studio(t, { wall: (pw, ph) => { ctx.save(); ctx.translate(-PNL.x, -PNL.y); wallChart(t, u); ctx.restore(); } });
    monitorBank(40, 96, 620, 520, t, 0); monitorBank(1260, 96, 620, 520, t, 6);
    // the anchors, working out
    const bob = Math.sin(bp * Math.PI) * .05;
    newsClawd(SET.clawdX, SET.clawdY, SET.clawdU, { legs: false, shadow: false, dy: bob, talk: talk(t), blink: frac(t * .37 + .1) < .045 ? 1 : 0, sweat: true, lookX: .2,
      reachL: [-5.5, lerp(-2.4, -6.7, upL)], reachR: [5.5, lerp(-2.4, -6.7, upR)], holdL: dumbbell(50), hold: dumbbell(50) });
    sweatband(SET.clawdX, SET.clawdY + (bob - 7.45) * SET.clawdU, 10.1 * SET.clawdU, 24);
    const vdy = -bob * .5, vS = SET.valS;
    toon(SET.valX, SET.valY, vS, { ...CAST.val.o, legs: false, shadow: false, dy: vdy, talk: talk(t, 1.3), blink: frac(t * .37 + .6) < .045 ? 1 : 0, lookX: -.3,
      reachL: [-2.1, lerp(-5.1, -8.6, upR)], reachR: [2.1, lerp(-5.1, -8.6, upL)], holdL: dumbbell(40), hold: dumbbell(40) });
    sweatband(SET.valX, SET.valY + (vdy - 10.55) * vS, 2.9 * vS, 17, -.03);
    newsDesk({ mugs: 0 });
    // a towel and a water bottle on the desk
    ctx.save(); ctx.translate(820, 706); ctx.rotate(-.05); rrect(-60, -14, 120, 26, 8); paint('#F4F2EC', NP.ink, 3); ctx.fillStyle = NP.red; ctx.fillRect(-58, -2, 116, 5); ctx.restore();
    rrect(1128, 640, 34, 68, 8); paint('rgb(160 210 255 / .8)', NP.ink, 3); rrect(1134, 626, 22, 16, 4); paint(NP.red, NP.ink, 3);
    // the curve breaks out of the wall and climbs out of the roof
    if (ext > 0) {
      const top = Math.max(tipY, -4300);
      neon([[cX(1), cY(1)], [cX(1), top]], NP.lime, 12);
      for (let j = 0; j < 12; j++) { const my = cY(1) - 260 - j * 330; if (my < top || my > cY(1) - 100) continue; ctx.fillStyle = alpha(NP.lime, .8); ctx.fillRect(cX(1) - 40, my - 2, 26, 4); pixelText(`1.0E+${26 + j}`, cX(1) - 54, my - 14, 4, NP.lime, { align: 'right' }); }
      glint(cX(1), top, 150, 1); ctx.fillStyle = rg(cX(1), top, 4, 90, [[0, 'rgb(220 255 170 / .8)'], [1, 'rgb(160 255 80 / 0)']]); ell(cX(1), top, 90); ctx.fill();
      const tAt = y => tGain + .06 + Math.cbrt(clamp((cY(1) - y) / 3400)) * Math.max(.2, w.b - tGain - .06);
      sparks(cX(1), PNL.y, t - tAt(PNL.y), 1); sparks(cX(1), 0, t - tAt(0), 2, 10, 70); sparks(cX(1), -435, t - tAt(-435), 3, 18, 120);
      // the broken wall frame: shards
      const ss = t - tAt(PNL.y);
      if (ss > 0) for (let i = 0; i < 8; i++) { const a = -Math.PI / 2 + (hash(i + 4) - .5) * 2, v = 300 + hash(i + 9) * 400; ctx.save(); ctx.translate(cX(1) + Math.cos(a) * v * ss, PNL.y + Math.sin(a) * v * ss + 900 * ss * ss); ctx.rotate(ss * 9 + i); poly([[-12, -8], [14, -4], [-2, 12]]); paint('rgb(200 230 255 / .8)', '#FFF', 2); ctx.restore(); }
    }
    camEnd();
  }

  // ================================================================================================
  // L3 — the whole team at the desk, hook in chrome, confetti cannons
  // ================================================================================================
  function specialWall(t) {
    return (w, h) => {
      ctx.fillStyle = rg(w / 2, h * .42, 20, 460, [[0, '#C98AFF'], [.5, '#6B2FC4'], [1, '#240A5A']]); ctx.fillRect(0, 0, w, h);
      ctx.save(); ctx.translate(w / 2, h * .42); ctx.rotate(t * .4); ctx.fillStyle = 'rgb(255 220 120 / .16)';
      for (let i = 0; i < 16; i++) { ctx.rotate(TAU / 16); poly([[0, 0], [700, -50], [700, 50]]); ctx.fill(); } ctx.restore();
      logo89(w / 2, h * .42, 150, { spin: Math.sin(t * 2) * .3 });
    };
  }
  function teamShot(t) {
    const w = win(2), ts = hookTimes(2), tS = ts[4], bp = bpOf(t), cheer = t >= tS - .05;
    const [sx, sy] = t >= tS && t < tS + .25 ? shakeXY(t, 12 * (1 - (t - tS) / .25)) : [0, 0];
    ctx.save(); ctx.translate(sx, sy);
    camBegin(960, 575, 1.14 + kickZ(t, tS, .04) + .02 * clamp((t - w.a) / 2));
    studio(t, { dim: .3, wall: specialWall(t) });
    const sway = i => Math.sin(bp * Math.PI + i * .9) * .035, hop = i => -Math.abs(Math.sin(bp * Math.PI + (i % 2) * .5)) * .1;
    const arms = (i, o) => cheer ? { aL: 1.15 + Math.sin(t * 9 + i) * .12, aR: 1.15 + Math.cos(t * 9 + i) * .12, eL: .15, eR: .15, handL: 'open', hand: 'open' } : o;
    const face = (i) => cheer ? { mouth: 'grin', eyes: 'happy' } : { talk: talk(t, i * 1.7) };
    const S = 34, GY = 872;
    [[CAST.sunny, 255], [CAST.batch, 470]].forEach(([c, x], i) => toon(x, GY, S, { ...c.o, legs: false, shadow: false, rot: sway(i), dy: hop(i), ...face(i), ...arms(i, { reachL: [-1.9, -6.2], reachR: [1.9, -6.2] }) }));
    newsClawd(715, 800, 28, { legs: false, shadow: false, rot: sway(2) * .6, dy: hop(2) * 1.4, ...(cheer ? { eyes: 'happy', mouth: 'grin', aL: 1.2 + Math.sin(t * 9) * .15, aR: 1.2 + Math.cos(t * 9) * .15 } : { talk: talk(t, 3), reachL: [-5.2, -3.2], reachR: [5.2, -3.2] }) });
    toon(990, 896, 37, { ...CAST.val.o, legs: false, shadow: false, rot: sway(3), dy: hop(3), ...face(3), ...arms(3, { reachL: [-1.9, -5.8], reachR: [1.9, -5.8] }) });
    [[CAST.randi, 1228], [CAST.chip, 1452]].forEach(([c, x], i) => toon(x, GY, S, { ...c.o, legs: false, shadow: false, rot: sway(i + 4), dy: hop(i + 4), ...face(i + 4), ...arms(i + 4, { reachL: [-1.9, -6.2], reachR: [1.9, -6.2] }) }));
    newsDesk({ mugs: 0 });
    // the new arrivals on the desk: Opus 5.5 (with its sticker) and GPT-6
    const mh = cheer ? -Math.abs(Math.sin(t * 9)) * 1.2 : hop(5) * 3;
    newsClawd(860, 712, 7.5, { suit: false, dy: mh, eyes: cheer ? 'happy' : 'normal', mouth: cheer ? 'grin' : 'smile', blush: true, aL: cheer ? 1.2 : -.3, aR: cheer ? 1.2 : .9 + Math.sin(t * 10) * .3 });
    ell(860 + 22, 712 + mh * 7.5 - 44, 13); paint(NP.gold, NP.ink, 2); txt('5.5', 882, 712 + mh * 7.5 - 43, 12, NP.ink, { font: 'archivo' });
    computer(1672, 738, 22, { label: 'GPT-6', face: cheer ? 'happy' : 'smile', legs: false, dy: hop(6) * 2, ...(cheer ? { aL: 1.1, aR: 1.1, eL: .2, eR: .2 } : { aR: .6 + Math.sin(t * 10) * .3, eR: 1.2 }) });
    camEnd();
    confettiBurst(t, tS, 120, 800, -1.05, 60, 31); confettiBurst(t, tS, 1800, 800, -2.09, 60, 47);
    confettiRain(t, tS - .1, 50, 5);
    ctx.restore();
    hook(t, ts, { y1: 226, s1: 94, y2: 346, s2: 142 });
    sweepGlint(W / 2 - 520, W / 2 + 520, 320, (t - tS - .12) / .45, 140);
    flash(t, tS, .1, .45);
    // the replay logo spins in to cover the cut into the sports replay
    const rk = clamp((t - (w.b - .16)) / .16);
    if (rk > 0) replayLogo(rk, false);
  }
  // the 80s sports-replay transition: the 89 roundel spins up to fill the screen (cover) and away again (reveal)
  function replayLogo(k, reveal) {
    const e = reveal ? 1 - easeOut(k) : easeIn(k), r = lerp(20, 1250, e);
    ctx.save(); ctx.globalAlpha = reveal ? clamp((1 - k) * 3) : 1;
    logo89(W / 2, H / 2, r, { spin: (reveal ? k : 1 - k) * Math.PI * 1.5 });
    if (e > .35) chrome('INSTANT REPLAY', W / 2, H / 2 + r * .1, 120, { font: 'archivo', style: 'white', italic: .14, depth: 10, spacing: 3, alpha: clamp((e - .35) * 3) });
    ctx.restore();
  }

  // ================================================================================================
  // L4 — "pace it" in slow motion, "race it" at triple speed
  // ================================================================================================
  function raceCar(x, y, s, o = {}) {
    const col = o.col ?? NP.red;
    ctx.save(); ctx.translate(x, y); ctx.scale(s, s);
    ctx.fillStyle = 'rgb(0 0 0 / .35)'; ell(.2, 0, 3.8, .32); ctx.fill();
    if (o.speed) { for (let i = 0; i < 5; i++) { ctx.fillStyle = `rgb(255 255 255 / ${.25 * o.speed})`; ctx.fillRect(-4 - o.speed * (3 + hash(i) * 5), -1.9 + i * .35, o.speed * (3 + hash(i + 3) * 5), .1); } }
    ctx.save(); if (o.shake) ctx.translate(o.shake[0], o.shake[1]);
    rrect(-3.7, -2.35, 1.3, .36, .08); paint(shade(col, .15), NP.ink, .07);
    ctx.beginPath(); ctx.moveTo(-3.05, -2.0); ctx.lineTo(-2.85, -1.05); paint(null, NP.ink, .14);
    poly([[-3.4, -.4], [-3.3, -1.12], [-1.5, -1.25], [-.8, -1.55], [.5, -1.55], [1.1, -1.08], [3.6, -.72], [3.75, -.4]]); paint(col, NP.ink, .08);
    ctx.save(); poly([[-3.4, -.4], [-3.3, -1.12], [-1.5, -1.25], [-.8, -1.55], [.5, -1.55], [1.1, -1.08], [3.6, -.72], [3.75, -.4]]); ctx.clip();
    ctx.fillStyle = 'rgb(255 255 255 / .85)'; ctx.fillRect(-3.5, -.95, 7.4, .16); ctx.fillStyle = 'rgb(0 0 0 / .18)'; ctx.fillRect(-3.5, -.6, 7.4, .3); ctx.restore();
    ell(-1.6, -.78, .34); paint('#FFFFFF', NP.ink, .05); txt(String(o.num ?? 1), -1.6, -.76, .44, NP.ink, { font: 'anton' });
    if (o.label) txt(o.label, .35, -.8, .44, NP.white, { font: 'archivo', maxW: 2.3, shadow: [.03, .04], shadowCol: 'rgb(0 0 0 / .6)' });
    // the driver: a tiny computer with a face
    rrect(-.62, -2.45, 1.24, 1.0, .16); paint(o.case ?? NP.beige, NP.ink, .06);
    rrect(-.48, -2.33, .96, .7, .12); paint('#0C1A12');
    ctx.fillStyle = o.glow ?? NP.phosphor; ctx.strokeStyle = o.glow ?? NP.phosphor; ctx.lineWidth = .08;
    if (o.face === 'angry') { for (const sd of [-1, 1]) { ctx.fillRect(sd * .2 - .07, -2.05, .14, .14); ctx.beginPath(); ctx.moveTo(sd * .34, -2.22); ctx.lineTo(sd * .08, -2.12); ctx.stroke(); } ctx.beginPath(); ctx.moveTo(-.16, -1.8); ctx.lineTo(.16, -1.8); ctx.stroke(); }
    else { for (const sd of [-1, 1]) ctx.fillRect(sd * .2 - .06, -2.12, .12, .2); ctx.beginPath(); ctx.arc(0, -1.98, .16, .2 * Math.PI, .8 * Math.PI); ctx.stroke(); }
    ctx.restore();
    for (const [wx, r] of [[-2.3, .66], [2.35, .58]]) {
      ell(wx, -r, r); paint('#16161A', NP.ink, .06); ell(wx, -r, r * .46); paint('#9AA0AE', NP.ink, .04);
      ctx.save(); ctx.translate(wx, -r); ctx.rotate(-(o.spin ?? 0) / r); ctx.fillStyle = '#16161A'; ctx.fillRect(-r * .44, -.05, r * .88, .1); ctx.fillRect(-.05, -r * .44, .1, r * .88); ctx.restore();
    }
    ctx.restore();
  }
  function paceCar(x, y, s, o = {}) {
    ctx.save(); ctx.translate(x, y); ctx.scale(s, s);
    ctx.fillStyle = 'rgb(0 0 0 / .35)'; ell(0, 0, 3.8, .32); ctx.fill();
    // light bar
    rrect(-1.0, -2.78, 2.0, .34, .1); paint('#222', NP.ink, .06);
    if (o.lights) { const on = frac(o.tw * 2.2) < .5; ell(-.5, -2.61, .3, .15); paint(on ? '#FFB020' : '#6A4000'); ell(.5, -2.61, .3, .15); paint(on ? '#6A4000' : '#FFB020'); if (on) glint(-.5, -2.65, .9, .8, '#FFD080'); else glint(.5, -2.65, .9, .8, '#FFD080'); }
    const body = [[-3.6, -.42], [-3.6, -1.35], [-2.4, -1.5], [-1.45, -2.45], [1.15, -2.45], [2.0, -1.5], [3.6, -1.3], [3.75, -.42]];
    poly(body); paint(lg(0, -2.5, 0, -.4, [[0, '#FFE070'], [1, '#E0A800']]), NP.ink, .08);
    poly([[-1.25, -2.3], [-.1, -2.3], [-.1, -1.55], [-2.1, -1.55]]); paint('#8FB8E8', NP.ink, .05);
    poly([[.05, -2.3], [1.05, -2.3], [1.75, -1.55], [.05, -1.55]]); paint('#8FB8E8', NP.ink, .05);
    ctx.fillStyle = NP.ink; ctx.fillRect(-3.6, -1.0, 7.35, .1);
    txt('PACE CAR', .1, -1.05 + .38, .42, NP.ink, { font: 'archivo', spacing: .02 });
    // Clawd at the wheel, waving the yellow flag out of the window
    rrect(-1.05, -2.2, 1.0, .62, .1); paint(NP.clawd, NP.ink, .05);
    for (const sd of [-.75, -.35]) { ctx.fillStyle = NP.ink; ctx.fillRect(sd, -2.05 + (o.worried ? .05 : 0), .1, .18); }
    if (o.flag !== false) {
      const wv = Math.sin(o.tw * 6) * .25;
      ctx.beginPath(); ctx.moveTo(-.6, -1.6); ctx.lineTo(-1.6, -3.2 + wv * .2); paint(null, '#5A3A20', .1);
      ctx.beginPath(); ctx.moveTo(-1.6, -3.2); ctx.quadraticCurveTo(-2.3, -3.2 + wv, -2.9, -2.95); ctx.lineTo(-2.7, -2.25); ctx.quadraticCurveTo(-2.2, -2.5 - wv, -1.45, -2.55); ctx.closePath(); paint(NP.gold, NP.ink, .05);
    }
    for (const wx of [-2.35, 2.35]) { ell(wx, -.58, .58); paint('#16161A', NP.ink, .06); ell(wx, -.58, .26); paint('#C9CFDB'); }
    ctx.restore();
  }
  function checkerFlag(s, t, angle) {
    return () => {
      ctx.save(); ctx.rotate(angle);
      ctx.beginPath(); ctx.moveTo(0, 0); ctx.lineTo(0, -s * 1.6); paint(null, '#3A2A1A', s * .07);
      const fw = s * 1.3, fh = s * .9, wv = Math.sin(t * 14) * s * .08;
      ctx.save(); ctx.translate(0, -s * 1.6);
      ctx.beginPath(); ctx.moveTo(0, 0); ctx.quadraticCurveTo(fw * .5, wv, fw, 0); ctx.lineTo(fw, fh); ctx.quadraticCurveTo(fw * .5, fh + wv, 0, fh); ctx.closePath();
      ctx.save(); ctx.clip(); for (let r = 0; r < 4; r++) for (let c = 0; c < 6; c++) { ctx.fillStyle = (r + c) % 2 ? '#111' : '#FFF'; ctx.fillRect(c * fw / 6, r * fh / 4 + Math.sin(c * .9 + t * 14) * s * .04 - 2, fw / 6 + 1, fh / 4 + 3); } ctx.restore();
      ctx.strokeStyle = NP.ink; ctx.lineWidth = 3; ctx.stroke();
      ctx.restore(); ctx.restore();
    };
  }
  function raceShot(t) {
    const w = win(3), l = LC()[3], tSplit = snapB(wT(l, .57), .5), tRace = snapB(wT(l, .748), .5), slow = t < tSplit;
    const twS = w.a + (tSplit - w.a) * .3, tw = slow ? w.a + (t - w.a) * .3 : twS + (t - tSplit) * 3;
    const V = 800, PX = 1180, pcW = x => (x - w.a) * V, camX = (slow ? pcW(tw) : pcW(twS)) - PX, race = t >= tRace, since = t - tRace;
    // sky + clouds
    vFill('#3F8FE0', '#BFE3FF', -100, -100, W + 200, 300);
    for (let i = 0; i < 6; i++) { const cx = ((i * 420 - camX * .08) % 2520 + 2520) % 2520 - 300, cy = 60 + hash(i + 3) * 50; ctx.fillStyle = 'rgb(255 255 255 / .85)'; ell(cx, cy, 90, 28); ctx.fill(); ell(cx + 60, cy - 16, 60, 28); ctx.fill(); ell(cx - 70, cy + 4, 60, 20); ctx.fill(); }
    // grandstand (parallax .4): roof, tiers, the crowd bouncing (at tape speed: slow in the replay, frantic in FF)
    const g0 = camX * .4;
    ctx.fillStyle = '#2A3048'; ctx.fillRect(-10, 150, W + 20, 24);
    vFill('#4A5270', '#353B55', -10, 174, W + 20, 212);
    for (let x = -((g0 % 300) + 300) % 300; x < W; x += 300) { ctx.fillStyle = '#20263A'; ctx.fillRect(x, 170, 14, 216); }
    for (let r = 0; r < 5; r++) {
      const y = 196 + r * 38, cw = 34, i0 = Math.floor((g0 - 40) / cw) - 1;
      for (let i = i0; i < i0 + W / cw + 3; i++) {
        const x = i * cw + (r % 2) * 17 - g0, hb = Math.abs(Math.sin(tw * 7 + i * .7 + r)) * (race ? 16 : 6);
        ell(x, y - hb, 13, 15); ctx.fillStyle = ['#E84A4A', '#F4D24A', '#FFFFFF', '#4A8AE8', '#2EBD5B', '#F28AC0'][((i * 7 + r * 3) % 6 + 6) % 6]; ctx.fill();
        if (race && (i + r) % 5 === 0) { ctx.fillStyle = '#F2C8A0'; ell(x - 10, y - hb - 26, 6); ctx.fill(); ell(x + 10, y - hb - 26, 6); ctx.fill(); }
      }
    }
    // the pit wall with the station's ads
    ctx.fillStyle = '#F4F4F0'; ctx.fillRect(-10, 380, W + 20, 44);
    for (let i = Math.floor(camX / 320) - 1; i < camX / 320 + 7; i++) { const x = i * 320 - camX; ctx.fillStyle = i % 2 ? NP.red : NP.blue; ctx.fillRect(x + 8, 384, 304, 36); txt(i % 3 === 0 ? 'CHANNEL 89' : i % 3 === 1 ? 'ACTION NEWS' : 'SPORTS 89', x + 160, 403, 26, NP.white, { font: 'archivo', spacing: 2 }); }
    // the track
    vFill('#5A5A63', '#3C3C44', -10, 424, W + 20, 470);
    ctx.fillStyle = 'rgb(255 255 255 / .06)'; for (let i = 0; i < 40; i++) { const x = ((hash(i) * 2400 - camX) % 2400 + 2400) % 2400 - 200; ctx.fillRect(x, 440 + hash(i + 9) * 430, 60 + hash(i + 4) * 80, 3); }
    ctx.fillStyle = 'rgb(255 255 255 / .8)'; for (let x = -((camX % 300) + 300) % 300; x < W; x += 300) { ctx.fillRect(x, 734, 140, 7); }
    ctx.fillStyle = '#E8E8E8'; ctx.fillRect(-10, 886, W + 20, 8);
    vFill('#2E9A4A', '#1E6A30', -10, 894, W + 20, 300);
    // the start/finish line and the flag stand on the pit wall, anchored in the world (it scrolls into place during the replay)
    const fx = pcW(twS) - PX + 520 - camX;
    if (fx < W + 300) {
      for (let r = 0; r < 16; r++) for (let c = 0; c < 2; c++) { ctx.fillStyle = (r + c) % 2 ? '#111' : '#F4F4F4'; ctx.fillRect(fx - 26 + c * 26, 424 + r * 29.5, 26, 29.5); }
      rrect(fx - 20, 352, 150, 30, 4); paint('#8A90A8', NP.ink, 3);
      const drop = race ? easeOut(clamp(since / .12)) : 0, wave = race && since > .12 ? Math.sin((since - .12) * 30) * .35 : 0, ready = slow ? 0 : 1;
      toon(fx + 55, 354, 18, { ...CAST.batch.o, shadow: false, eyes: race ? 'wide' : 'open', mouth: race ? 'O' : 'smile',
        aR: lerp(lerp(-.5, 1.25, ready), -.35, drop) + wave, eR: .1, hold: checkerFlag(56, tw, lerp(lerp(.7, -.25, ready), 1.9, drop) + wave), aL: -1.2 });
    }
    // the field and the pace car, depth-sorted by lane
    const cars = [['OPUS 5.5', NP.clawd, 1, NP.beige, 712, .98, 780], ['GPT-6', '#1E9A7A', 6, '#E8E8EC', 830, 1.1, 560], ['GEMINI', '#2A6AE0', 3, '#DCD2B6', 640, .86, 390], ['GROK', '#2A2A30', 4, '#C9CFDB', 770, 1.03, 150]];
    const items = [];
    cars.forEach(([lab, col, num, cs, ly, ls, x0], j) => {
      const launch = race ? 6400 * Math.max(0, since - j * .05) ** 1.7 : 0;
      const x = slow ? x0 + Math.sin(tw * 1.7 + j) * 20 : x0 + 50 * clamp((t - tSplit) / Math.max(.1, tRace - tSplit)) + launch;
      const spd = slow ? 0 : race ? clamp((since - j * .05) * 4) : .15, shake = !slow && !race ? shakeXY(t + j, .05) : null;
      items.push([ly, () => raceCar(x, ly, 52 * ls, { label: lab, col, num, case: cs, face: slow ? 'smile' : 'angry', speed: spd, shake, spin: (slow ? tw * V : t * 4000) / (52 * ls) * 20 + j })]);
      const age = since - j * .05;
      if (race && age > 0) for (let i = 0; i < 4; i++) items.push([ly - .5, () => { const r = 40 + age * 300 + i * 22; ell(x0 + 40 - i * 60, ly - 40 - i * 10, r, r * .55); ctx.fillStyle = `rgb(230 230 235 / ${clamp(.6 - age * .5)})`; ctx.fill(); }]);
    });
    const pit = slow ? 0 : ease(clamp((t - tSplit) / .5)), py = lerp(740, 900, pit);
    items.push([py, () => paceCar(PX + 330 * easeOut(clamp((t - tSplit) / .8)), py, 54 * lerp(1, 1.08, pit), { tw, lights: slow, worried: !slow, flag: true })]);
    items.sort((a, b) => a[0] - b[0]).forEach(([, fn]) => fn());
    // the scoreboard: PACE → RACE on the flag
    rrect(990, 36, 320, 104, 12); paint(lg(0, 36, 0, 140, [[0, '#1B1E28'], [1, '#07080C']]), '#C9A43A', 6);
    const word = race ? 'RACE' : 'PACE', fl = race && since < .6 && frac(since * 8) < .5;
    pixelText(word, 1150, 56, 9, fl ? '#FFFFFF' : race ? '#5CFF7A' : '#FFC83A', { align: 'center', edge: null });
    // the telestrator (replay only): circle the pace car, scrawl PACE
    if (slow) {
      const k = clamp((t - w.a - .28) / .3);
      ctx.save(); ctx.strokeStyle = '#FFE23A'; ctx.lineWidth = 10; ctx.lineCap = 'round'; ctx.beginPath();
      ctx.ellipse(PX, 668, 300, 175, -.04, -Math.PI * .7, -Math.PI * .7 + TAU * 1.04 * k); ctx.stroke(); ctx.restore();
      if (k >= 1) {
        txt('PACE', 1600, 470, 96, '#FFE23A', { font: 'marker', rot: -.1, alpha: clamp((t - w.a - .6) / .1) });
        const ak = clamp((t - w.a - .62) / .12); ctx.save(); ctx.strokeStyle = '#FFE23A'; ctx.lineWidth = 9; ctx.lineCap = 'round'; ctx.beginPath(); ctx.moveTo(1560, 530); ctx.lineTo(lerp(1560, 1470, ak), lerp(530, 580, ak)); ctx.stroke(); ctx.restore();
      }
      liveBug(96, 70, { label: 'INSTANT REPLAY', col: NP.green });
      pixelText('SLOW MOTION', 110, 150, 4, NP.white);
    } else liveBug(96, 70, { label: 'LIVE' });
    if (race) flash(t, tRace, .1, .5);
    if (t < w.a + .22) replayLogo(clamp((t - w.a) / .22), true);
  }

  // ================================================================================================
  // L5 — the team jumps for joy; the tape PAUSEs on the peak
  // ================================================================================================
  function jumpShot(t) {
    const w = win(4), ts = hookTimes(4), tS = ts[4], tPeak = tS + .17, frozen = t >= tPeak, tf = Math.min(t, tPeak), bp = bpOf(tf);
    const jump = i => { const s0 = tS - .07 - (i % 3) * .015; if (tf < s0 - .12) return { dy: -Math.abs(Math.sin(bp * Math.PI)) * .18, sq: 0 }; if (tf < s0) return { dy: 0, sq: .12 * Math.sin((tf - s0 + .12) / .12 * Math.PI) }; return { dy: -(3.2 + (i % 3) * .5) * easeOut(clamp((tf - s0) / (tPeak - s0 + .02))), sq: -.06 }; };
    const up = tf >= tS - .08;
    const [jx, jy] = frozen ? [(hash(Math.floor(t * 15)) - .5) * 4, (hash(Math.floor(t * 15) + 3) - .5) * 4] : [0, 0];
    ctx.save(); ctx.translate(jx, jy);
    vFill('#FF3A6A', '#7A0636');
    ctx.save(); ctx.translate(W / 2, 560); ctx.rotate(tf * .35); ctx.fillStyle = 'rgb(255 230 120 / .13)';
    for (let i = 0; i < 20; i++) { ctx.rotate(TAU / 20); poly([[0, 0], [1700, -110], [1700, 110]]); ctx.fill(); } ctx.restore();
    ctx.save(); ctx.globalAlpha = .35; logo89(W / 2, 560, 300, { spin: Math.sin(tf * 1.5) * .25 }); ctx.restore();
    ctx.save(); ctx.globalCompositeOperation = 'screen';
    for (const [bx, ph] of [[360, 0], [960, 1.7], [1560, 3.1]]) { const a = Math.sin(tf * 1.6 + ph) * .3; ctx.fillStyle = 'rgb(255 240 200 / .16)'; poly([[bx - 30, -40], [bx + 30, -40], [bx + 330 + a * 700, 980], [bx - 330 + a * 700, 980]]); ctx.fill(); }
    ctx.restore();
    vFill('#5A0A2A', '#1E0210', -100, 940, W + 200, 300); ctx.fillStyle = 'rgb(255 180 220 / .5)'; ctx.fillRect(-100, 938, W + 200, 4);
    for (let i = 0; i < 14; i++) { ctx.fillStyle = i % 2 ? 'rgb(255 255 255 / .05)' : 'rgb(0 0 0 / .08)'; poly([[i * 160 - 80, 942], [i * 160 + 80, 942], [(i - 7) * 420 + 960 + 210, 1100], [(i - 7) * 420 + 960 - 210, 1100]]); ctx.fill(); }
    const GY = 985, S = 33;
    const who = [[CAST.sunny, 180], [CAST.batch, 395], [CAST.val, 620], ['clawd', 880], ['opus', 1060], [CAST.randi, 1220], [CAST.chip, 1440], ['gpt', 1665]];
    who.forEach(([c, x], i) => {
      const j = jump(i), arm = up ? { aL: 1.25 + (i % 2) * .15, aR: 1.25 + ((i + 1) % 2) * .15, eL: .1, eR: .1, handL: 'open', hand: 'open' } : { aL: -.9 + Math.sin(bp * Math.PI + i) * .3, aR: -.9 - Math.sin(bp * Math.PI + i) * .3, eL: .6, eR: .6 };
      if (c === 'clawd') newsClawd(x, GY, 23, { dy: j.dy * 1.55, sq: j.sq, eyes: up ? 'happy' : 'normal', mouth: up ? 'grin' : undefined, talk: up ? undefined : talk(tf, 2), aL: up ? 1.25 : -.2, aR: up ? 1.25 : -.2, walk: up ? .25 : undefined });
      else if (c === 'opus') newsClawd(x, GY, 9, { suit: false, dy: j.dy * 2.4, sq: j.sq, eyes: up ? 'happy' : 'normal', mouth: 'grin', blush: true, aL: up ? 1.3 : -.2, aR: up ? 1.3 : -.2 });
      else if (c === 'gpt') computer(x, GY, 27, { label: 'GPT-6', face: up ? 'happy' : 'smile', dy: j.dy * 1.2, sq: j.sq, walk: up ? .25 : undefined, ...(up ? { aL: 1.2, aR: 1.2, eL: .1, eR: .1 } : {}) });
      else toon(x, GY, S, { ...c.o, dy: j.dy, sq: j.sq, walk: up ? (i % 2 ? .22 : .72) : undefined, ...(up ? { mouth: 'grin', eyes: 'happy' } : { talk: talk(tf, i) }), ...arm });
    });
    if (up) confettiRain(tf, tS - .1, 40, 13);
    hook(tf, ts, { y1: 210, s1: 104, y2: 345, s2: 146 });
    ctx.restore();
    if (frozen) {
      vcrMode('PAUSE'); tapeFX({ pauseBar: 1, jitter: 1.4 });
    }
    flash(t, tS, .08, .35);
  }

  // ================================================================================================
  // L6 — the sign-off, the test card, the TV going off; then the dark room where the computer trains on
  // ================================================================================================
  function signoffShot(t, tLog, tOff) {
    const w = win(5), bp = bpOf(t), lb = Math.round(bpOf(tLog));
    const banks = clamp(Math.floor((bp - lb) * 2) + 1, 0, 5);  // one bank of lights off per half beat from "log"
    const waveR = Math.sin(t * 10) * .35, waveL = Math.sin(t * 10 + 1.2) * .35;
    anchorShot(t, {
      who: 'two', hands: false, dim: banks * .12, cam: { x: 960, y: 540, zoom: 1 + .04 * clamp((t - w.a) / 2) },
      clawd: { reachL: [-5.2, -2.9], aR: 1.25 + waveR * .6, lookX: 0, talk: talk(t), eyes: t > tOff ? 'happy' : 'normal' },
      val: { reachL: [-1.8, -5.8], aR: .55, eR: .75 + waveL * 1.1, hand: 'wave', lookX: 0, talk: talk(t, 1.2) },
    });
    // the lighting truss goes out bank by bank, edges first
    for (let i = -3; i < 16; i++) {
      const lx = i * 150 + 40, rank = Math.min(Math.abs(lx - 200), Math.abs(lx - 1720)) / 150, off = rank < banks * 1.6;
      if (!off) continue;
      ctx.fillStyle = 'rgb(4 6 16 / .92)'; ctx.fillRect(lx - 75, 0, 150, 150); ell(lx, 26, 16); paint('#3A3830', '#111', 3);
    }
    // a pool of light on the desk, darkness everywhere else
    const dk = banks / 5;
    ctx.fillStyle = rg(960, 600, 260, 1150, [[0, 'rgb(0 0 8 / 0)'], [.55, `rgb(0 0 8 / ${.35 * dk})`], [1, `rgb(0 0 8 / ${.9 * dk})`]]); ctx.fillRect(-100, -100, W + 200, H + 200);
    // ON AIR goes dark on "off"
    const on = t < tOff, ox = 960, oy = 120;
    if (on) { ctx.fillStyle = 'rgb(255 40 40 / .25)'; ell(ox, oy, 190, 80); ctx.fill(); }
    rrect(ox - 130, oy - 42, 260, 84, 10); paint(on ? lg(0, oy - 42, 0, oy + 42, [[0, '#FF6A5A'], [1, '#B8101E']]) : '#3A1216', '#111', 5);
    txt('ON AIR', ox, oy + 3, 52, on ? NP.white : '#5A2A2E', { font: 'archivo', spacing: 4 });
    if (!on) sparks(ox + 110, oy - 30, t - tOff, 77, 8, 40);
    chyron('GOOD NIGHT', 'FROM ALL OF US AT CHANNEL 89 ACTION NEWS', { k: clamp((t - w.a - .1) / .3), y: 770 });
  }
  function testCardFrame(t) {
    testCard({ caption: 'END OF BROADCAST DAY' });
  }
  // --- the room outside the TV ---
  const TVR = { x: 330, y: 238, w: 640, h: 360 };
  const CMP = { x: 1455, y: 872, s: 60 };
  const cmpScreen = () => ({ x: CMP.x - 2.15 * CMP.s, y: CMP.y - 6.6 * CMP.s, w: 4.3 * CMP.s, h: 3.55 * CMP.s });
  function remote() {
    return () => {
      ctx.save(); ctx.rotate(-.35);
      rrect(-92, -22, 124, 44, 10); paint('#24242C', NP.ink, 4);
      ctx.fillStyle = '#FF3030'; ell(-86, 0, 6); ctx.fill();
      for (let i = 0; i < 3; i++) for (let j = 0; j < 2; j++) { rrect(-60 + i * 26, -14 + j * 16, 18, 10, 3); paint(i === 0 && j === 0 ? '#E0E0E6' : '#6A6A78'); }
      ctx.restore();
    };
  }
  // o: fade, dot (afterglow 0..1), red (0..1), redGlint, logN (AND ON lines), face, raise (remote 0..1), clickT (s since click, or −1),
  //    vcr (mode text), counter, tvOn (warm-up 0..1), tvPic (canvas for the screen), cam [x, y, z]
  function room(t, o) {
    const cam = o.cam ?? [960, 540, 1];
    ctx.fillStyle = '#020308'; ctx.fillRect(-100, -100, W + 200, H + 200);
    camBegin(cam[0], cam[1], cam[2]);
    ctx.save(); ctx.globalAlpha = o.fade ?? 1;
    // the wall, the window with venetian blinds, the moonlight stripes they throw across the wall
    vFill('#0E1428', '#080B18', -600, -600, W + 1200, 1540);
    ctx.fillStyle = 'rgb(255 255 255 / .018)'; for (let x = -600; x < W + 600; x += 70) ctx.fillRect(x, -600, 30, 1540);
    const wx = 1230, wy = 70, ww = 520, wh = 330;
    ctx.fillStyle = lg(wx, wy, wx, wy + wh, [[0, '#1C2E5A'], [1, '#3A5A8A']]); ctx.fillRect(wx, wy, ww, wh);
    ell(wx + 380, wy + 90, 40); paint('#E8ECF4');
    ctx.fillStyle = '#0A0E1C'; for (let i = 0; i < 11; i++) ctx.fillRect(wx, wy + 8 + i * 30, ww, 17);
    ctx.lineWidth = 12; ctx.strokeStyle = '#141A2C'; ctx.strokeRect(wx, wy, ww, wh);
    ctx.save(); ctx.globalCompositeOperation = 'screen'; ctx.fillStyle = 'rgb(140 170 255 / .06)';
    for (let i = 0; i < 9; i++) { const y0 = wy + 20 + i * 34; poly([[wx, y0], [wx, y0 + 13], [wx - 700, y0 + 330], [wx - 700, y0 + 300]]); ctx.fill(); }
    ctx.restore();
    // floor
    vFill('#15101A', '#07050A', -600, 920, W + 1200, 700); ctx.fillStyle = 'rgb(255 255 255 / .03)'; for (let i = 0; i < 12; i++) ctx.fillRect(-600, 930 + i * i * 4, W + 1200, 2);
    // the TV stand and the VCR
    const sx0 = 250, sx1 = 1140, sy0 = 690;
    rrect(sx0, sy0, sx1 - sx0, 36, 4); paint('#3A2618', '#000', 3);
    ctx.fillStyle = '#23170F'; ctx.fillRect(sx0 + 20, sy0 + 36, sx1 - sx0 - 40, 150); ctx.fillStyle = '#2E1E13'; ctx.fillRect(sx0 + 10, sy0 + 36, 22, 196); ctx.fillRect(sx1 - 32, sy0 + 36, 22, 196);
    rrect(sx0, sy0 + 176, sx1 - sx0, 30, 4); paint('#3A2618', '#000', 3);
    // VCR deck
    const vx = 340, vy = 752, vw = 700, vh = 92;
    rrect(vx, vy, vw, vh, 8); paint(lg(0, vy, 0, vy + vh, [[0, '#3A3D48'], [1, '#17181E']]), '#000', 3);
    rrect(vx + 24, vy + 22, 250, 44, 4); paint('#0A0B0E', '#555', 2); ctx.fillStyle = '#26272E'; ctx.fillRect(vx + 34, vy + 40, 230, 8);
    rrect(vx + 300, vy + 16, 230, 60, 6); paint('#030806', '#444', 2);
    const vcol = '#5CF2E0';
    ctx.save(); ctx.globalCompositeOperation = 'screen'; ctx.fillStyle = 'rgb(90 240 220 / .12)'; ell(vx + 415, vy + 46, 150, 50); ctx.fill(); ctx.restore();
    pixelText(o.vcr ?? 'PLAY ▶', vx + 312, vy + 24, 3, vcol, { edge: null });
    pixelText(o.counter ?? '', vx + 518, vy + 50, 3, vcol, { align: 'right', edge: null });
    const btns = ['◀◀', '▶', '■', '▶▶'];
    btns.forEach((b, i) => { const bx = vx + 552 + i * 36, lit = (o.vcr ?? '').startsWith('REW') && i === 0; rrect(bx, vy + 30, 30, 30, 4); paint(lit ? '#5CF2E0' : '#2A2C34', '#000', 2); pixelText(b, bx + 15, vy + 40, 1.6, lit ? '#000' : '#AAB', { align: 'center', edge: null }); });
    ell(vx + 20, vy + 76, 5); paint(frac(t * 1.3) < .5 ? '#FF3030' : '#501010');
    // the TV: dead glass, the afterglow dot, the tiny red curve, the moon and the computer reflected in it
    const tvDraw = (w, h) => {
      if (o.tvOn > 0 && o.tvPic) {
        const k = o.tvOn, ww = lerp(12, w, easeOut(clamp(k * 2.4))), hh = lerp(3, h, easeIn(clamp((k - .3) / .7)));
        ctx.save(); ctx.beginPath(); ctx.rect(w / 2 - ww / 2, h / 2 - hh / 2, ww, hh); ctx.clip(); ctx.drawImage(o.tvPic, 0, 0, w, h); ctx.restore();
        if (k < 1) { ctx.fillStyle = `rgb(255 255 255 / ${.8 * (1 - k)})`; ctx.fillRect(w / 2 - ww / 2, h / 2 - hh / 2, ww, hh); }
        return;
      }
      ctx.fillStyle = '#0F1412'; ctx.fillRect(0, 0, w, h);
      ctx.fillStyle = 'rgb(120 150 220 / .07)'; for (let i = 0; i < 7; i++) poly([[w * .7 + i * 20, 0], [w * .7 + i * 20 + 9, 0], [w * .45 + i * 20 + 9, h], [w * .45 + i * 20, h]]), ctx.fill();
      ctx.fillStyle = rg(w * .95, h * .7, 5, w * .4, [[0, 'rgb(108 255 142 / .16)'], [1, 'rgb(108 255 142 / 0)']]); ctx.fillRect(0, 0, w, h);
      if (o.dot > 0) { ctx.fillStyle = rg(w / 2, h / 2, 1, 40 * o.dot + 6, [[0, `rgb(255 255 255 / ${o.dot})`], [.25, `rgb(200 220 255 / ${.6 * o.dot})`], [1, 'rgb(120 160 255 / 0)']]); ell(w / 2, h / 2, 40 * o.dot + 6); ctx.fill(); }
      if (o.red > 0) {
        ctx.save(); ctx.globalAlpha *= o.red; ctx.translate(w / 2, h / 2);
        ctx.fillStyle = 'rgb(255 40 40 / .14)'; ell(0, 0, 80, 60); ctx.fill();
        ctx.lineCap = 'round'; ctx.lineJoin = 'round';
        ctx.beginPath(); ctx.moveTo(-46, -40); ctx.lineTo(-46, 34); ctx.lineTo(48, 34); ctx.strokeStyle = 'rgb(255 90 90 / .55)'; ctx.lineWidth = 3; ctx.stroke();
        ctx.beginPath(); for (let i = 0; i <= 24; i++) { const u = i / 24; ctx.lineTo(-40 + u * 80, 28 - (Math.exp(u * 4) - 1) / (Math.exp(4) - 1) * 66); }
        ctx.strokeStyle = 'rgb(255 60 60 / .35)'; ctx.lineWidth = 11; ctx.stroke(); ctx.strokeStyle = '#FF3A3A'; ctx.lineWidth = 4; ctx.stroke();
        ctx.restore();
        if (o.redGlint > 0) glint(w / 2 + 40, h / 2 - 38, 110 * o.redGlint, o.redGlint, '#FF9090');
      }
    };
    crtTV(TVR.x, TVR.y, TVR.w, TVR.h, tvDraw, { style: 'wood' });
    // the side table and the computer that trains on
    rrect(1250, CMP.y, 420, 26, 4); paint('#3A2618', '#000', 3); ctx.fillStyle = '#23170F'; ctx.fillRect(1275, CMP.y + 26, 18, 150); ctx.fillRect(1627, CMP.y + 26, 18, 150);
    // its cable, snaking into the VCR
    ctx.beginPath(); ctx.moveTo(CMP.x + 120, CMP.y - 60); ctx.bezierCurveTo(CMP.x + 260, CMP.y + 20, 1250, 1010, 1100, 960); ctx.bezierCurveTo(980, 925, 1060, 860, vx + vw - 10, vy + 70); paint(null, '#0A0A0E', 9);
    const g = cmpScreen();
    ctx.save(); ctx.globalCompositeOperation = 'screen';
    ctx.fillStyle = rg(g.x + g.w / 2, g.y + g.h / 2, 20, 620, [[0, 'rgb(90 255 140 / .30)'], [.4, 'rgb(60 200 110 / .10)'], [1, 'rgb(40 160 90 / 0)']]); ctx.fillRect(g.x - 700, g.y - 600, 1500, 1300);
    ctx.restore();
    const raise = o.raise ?? 0;
    computer(CMP.x, CMP.y, CMP.s, { legs: false, case: '#CFC5A8', text: o.face ? undefined : '', face: o.face, seed: 3,
      reachL: raise > 0 ? [lerp(-3.4, -4.4, raise), lerp(-.9, -5.4, raise)] : [-3.4, -.9], holdL: remote(), handL: 'open', reachR: [3.3, -.35 - Math.abs(Math.sin(bpOf(t) * Math.PI)) * .25] });
    if (!o.face) {
      // the training log on its screen
      ctx.save(); rrect(g.x, g.y, g.w, g.h, .55 * CMP.s); ctx.clip();
      pixelText('EPOCH 1', g.x + 16, g.y + 14, 3.2, NP.phosphor, { edge: null });
      const pc = Math.min(99, 91 + Math.floor((o.logN ?? 0) * 2.6));
      pixelText(pc + '%', g.x + g.w - 16, g.y + 14, 3.2, NP.phosphor, { align: 'right', edge: null });
      // the loss curve, ticking down a point per beat
      const px0 = g.x + 18, px1 = g.x + g.w - 18, py0 = g.y + 50, py1 = g.y + 118;
      ctx.strokeStyle = 'rgb(108 255 142 / .25)'; ctx.lineWidth = 1.5; ctx.strokeRect(px0, py0, px1 - px0, py1 - py0);
      const tick = Math.floor(bpOf(t)), pts = [];
      for (let i = 0; i <= 30; i++) { const u = i / 30, v = clamp(.1 + .85 * Math.exp(-u * 3.2) + (hash2(tick - 30 + i, 5) - .5) * .07 * (1 - u * .5)); pts.push([lerp(px0, px1, u), py1 - v * (py1 - py0)]); }
      ctx.beginPath(); pts.forEach(([a, b], i) => i ? ctx.lineTo(a, b) : ctx.moveTo(a, b)); ctx.strokeStyle = NP.phosphor; ctx.lineWidth = 3; ctx.stroke();
      if (frac(t * 2) < .6) { ell(pts.at(-1)[0], pts.at(-1)[1], 5); ctx.fillStyle = '#FFFFFF'; ctx.fill(); }
      const n = o.logN ?? 0;
      for (let i = 0; i < Math.min(n, 3); i++) pixelText('* AND ON', g.x + 16, g.y + 128 + i * 24 - Math.max(0, n - 3) * 24, 2.6, NP.phosphor, { edge: null });
      if (frac(t * 2.5) < .5) { ctx.fillStyle = NP.phosphor; ctx.fillRect(g.x + 16, g.y + 128 + Math.min(n, 3) * 24, 12, 16); }
      ctx.fillStyle = 'rgb(0 0 0 / .2)'; for (let yy = g.y; yy < g.y + g.h; yy += 5) ctx.fillRect(g.x, yy, g.w, 2);
      ctx.restore();
    }
    // the IR beam from the remote to the VCR
    if (o.clickT >= 0 && o.clickT < .45) {
      const k = o.clickT / .45, hx = CMP.x - 4.4 * CMP.s - 60, hy = CMP.y - 5.4 * CMP.s - 22;
      ctx.save(); ctx.setLineDash([18, 14]); ctx.lineDashOffset = -t * 600; ctx.strokeStyle = `rgb(255 60 60 / ${1 - k})`; ctx.lineWidth = 6;
      ctx.beginPath(); ctx.moveTo(hx, hy); ctx.lineTo(vx + 570, vy + 40); ctx.stroke(); ctx.restore();
      glint(vx + 570, vy + 40, 90 * (1 - k), 1 - k, '#FF8080');
      for (let r = 0; r < 3; r++) { const rr = 20 + (k * 3 + r) % 3 * 26; ctx.beginPath(); ctx.arc(hx, hy, rr, Math.PI * .8, Math.PI * 1.25); ctx.strokeStyle = `rgb(255 80 80 / ${(1 - k) * .8})`; ctx.lineWidth = 4; ctx.stroke(); }
    }
    ctx.restore();
    camEnd();
  }
  // the three sung "on"s of the tag (or evenly spaced if this take sings none), and when the remote clicks REW
  const onTimes = (t0, tEnd) => { const O = OUTL(); return O ? [.28, .57, .9].map(f => wT(O, f)) : [0, 1, 2].map(i => lerp(t0 + .6, tEnd - .4, i / 2)); };
  const clickTime = () => { const l = LC()[5], ons = onTimes(l.end, C4S().end); return Math.max(ons[2] + .27, C4S().end - .28); };
  function roomShot(t, t0, tEnd) {
    const ons = onTimes(t0, tEnd);
    const logN = ons.filter(x => t >= x).length, tRaise = ons[2] + .05, tClick = clickTime();
    const drift = clamp((t - t0) / (tEnd - t0));
    room(t, {
      fade: easeOut(clamp((t - t0) / .45)), dot: clamp(1 - (t - t0) / 1.1), red: clamp((t - ons[0] + .35) / .3) * (.75 + .25 * pulse(t, 3)), redGlint: t >= ons[0] - .05 ? clamp(1 - (t - ons[0] + .05) / .5) : 0,
      logN, face: t >= tRaise - .1 ? 'sly' : undefined, raise: easeOut(clamp((t - tRaise) / .2)), clickT: t - tClick,
      vcr: t >= tClick ? 'REW ◀◀' : 'PLAY ▶', counter: hms(t), cam: [1010 - 30 * drift, 585, 1.2 + .06 * drift],
    });
  }
  function c4Last(t) {
    const w = win(5), l = LC()[5], tLog = wT(l, .291), tOff = snapB(wT(l, .384), .5), tWill = snapB(wT(l, .502), 1), tv1 = l.end, tv0 = tv1 - .55;
    if (t < tWill) { if (t >= w.a) signoffShot(t, tLog, tOff); return; }
    if (t < tv0) { testCardFrame(t); if (t < tWill + .1) glitch('roll', 1 - (t - tWill) / .1); return; }
    const lineCC = () => ccText(l.text, { notes: true, color: NP.ccYellow });
    if (t < tv1) {
      tvOff(clamp((t - tv0) / (tv1 - tv0)), () => { testCardFrame(t); lineCC(); osd(t, 'PLAY', dateAt(t)?.text); });
      hideCaption(); hideOSD(); return;
    }
    hideOSD(); tapeFX({ crt: 0, chroma: 0, noise: .35, jitter: 0, dropouts: 0, cut: 'none' });
    roomShot(t, tv1, w.b);
  }

  // ================================================================================================
  // the C4 window
  // ================================================================================================
  section('C4', (p, lt, d, t) => {
    const i = subOf(t), L = LC();
    if (i === 0) { hideCaption(); return bumperShot(t); }
    if (i === 1) {
      const k = clamp((t - L[1].start) / .32);
      if (k < 1) { dveStar(k, () => bumperShot(t), () => trainShot(t)); return; }
      return trainShot(t);
    }
    if (i === 2) { hideCaption(); if (t < L[2].start + .1) glitch('roll', 1 - (t - L[2].start) / .1); return teamShot(t); }
    if (i === 3) {
      const l = L[3], tSplit = snapB(wT(l, .57), .5);
      raceShot(t);
      if (t < tSplit) vcrMode('SLOW');
      else { vcrMode('FF'); if (t < tSplit + .12) glitch('track', 1 - (t - tSplit) / .12); else if (hash(Math.floor(t * 30)) < .35) glitch('track', .35); }
      return;
    }
    if (i === 4) { hideCaption(); if (t < L[4].start + .1) glitch('tear', 1 - (t - L[4].start) / .1); return jumpShot(t); }
    if (t < L[5].start + .08) glitch('track', 1 - (t - L[5].start) / .08);
    return c4Last(t);
  });

  // ================================================================================================
  // outro — the TV blooms on, we push back in, and the whole special rewinds to the top; STOP; PLAY: bars and the end card
  // ================================================================================================
  let _rew = null;
  function rewList() {
    if (_rew) return _rew;
    const segs = SEGS.filter(s => s.key !== 'C4' && s.key !== 'outro' && SHOTS[s.key]).reverse();
    let acc = 0; const items = segs.map(s => { const wgt = s.kind === 'intro' ? 5 : s.kind === 'chorus' ? 2 : 1, it = { s, a: acc, w: wgt }; acc += wgt; return it; });
    _rew = { items, total: acc };
    return _rew;
  }
  const dateOfSeg = s => { let d = null; for (const q of SEGS) { if (q.start > s.start) break; if (q.date) d = q.date; } return d; };
  // the picture during picture-search rewind at rewind progress u (0..1): the shot, playing backwards, under noise bars
  function rewindPic(t, u) {
    const R = rewList(); if (!R.items.length) { blueScreen(); return; }
    const pos = clamp(R.total * (.3 * u + .7 * u * u), 0, R.total - 1e-4);
    const it = R.items.find(x => pos < x.a + x.w) ?? R.items.at(-1), q = (pos - it.a) / it.w;
    const pp = it.s.kind === 'intro' ? lerp(1, .13, q) : 1 - q;
    ctx.save(); ctx.transform(1, 0, -.035, 1, 20, 0);
    try { paintShot(it.s.key, pp); } catch (e) { fallbackTile(it.s.key); }
    ctx.restore();
    // picture-search noise bars rolling up the screen
    for (let i = 0; i < 2; i++) {
      const by = ((1 - frac(t * 1.9 + i * .5)) * (H + 240)) - 120, bh = 56 + 20 * i;
      ctx.save(); ctx.globalCompositeOperation = 'screen'; snow(.9, { y: by, h: bh }); ctx.restore();
      ctx.fillStyle = 'rgb(0 0 0 / .35)'; ctx.fillRect(0, by - 6, W, 6); ctx.fillStyle = 'rgb(255 255 255 / .6)'; ctx.fillRect(0, by + bh * .45, W, 3);
    }
    const shotT = it.s.start + pp * (it.s.end - it.s.start);
    osd(t, 'REW', dateOfSeg(it.s), hms(shotT));
    return shotT;
  }
  const SLATE = ['CHANNEL 89 ACTION NEWS', '"WE DIDN\'T START THE SCALING"', '', 'HOOK AFTER @TAUTOLOGER', 'LYRICS: DOMENIC & CLAUDE', 'MUSIC: LYRIA 3.5', 'VIDEO: CLAUDE OPUS 5.5', '', 'SEP 23 2026'];
  function endCard(t, tP) {
    const since = t - tP, [sx, sy] = since < .3 ? shakeXY(t, 10 * (1 - since / .3)) : [0, 0];
    ctx.save(); ctx.translate(sx, sy);
    colorBars();
    const k = clamp((since - .35) / .2);
    if (k > 0) {
      const bw = 1300, lh = 50, bh = 80 + SLATE.length * lh, top = 186;
      ctx.save(); ctx.translate(W / 2, top + bh / 2); ctx.scale(1, easeOut(k));
      rrect(-bw / 2, -bh / 2, bw, bh, 6); paint('rgb(0 0 0 / .88)', '#FFFFFF', 4);
      SLATE.forEach((s, i) => { if (!s) return; const big = i < 2, px = big ? 6 : 5, col = i === 1 ? NP.gold : i === SLATE.length - 1 ? NP.crtAmber : NP.white; pix(s, 0, -bh / 2 + 34 + i * lh + (i === 1 ? 8 : big ? 0 : 12), px, col, { align: 'center', edge: null }); });
      ctx.restore();
      logo89(W / 2 - bw / 2 + 4, top + 4, 62 * easeOut(k), { spin: Math.sin(t * 2) * .4 });
      const gs = frac((since - .6) / 1.6); if (since > .6) { sweepGlint(W / 2 - 520, W / 2 + 520, top + 70, gs / .45, 90); glint(W / 2 - bw / 2 + 40, top - 30, 70 * pulse(t, 4), pulse(t, 4)); }
    }
    // the VU box from the top of the tape, tape counter running again from zero
    rrect(1440, 740, 390, 290, 10); paint('rgb(0 0 0 / .8)', '#888', 3);
    for (const [x, ph] of [[1470, 0], [1530, 1.7]]) {
      rrect(x, 760, 46, 250, 6); paint('#0A0A0A', '#555', 3);
      const lvl = clamp(.5 + Math.sin(t * 23 + ph) * .03);
      for (let i = 0; i < 14; i++) { const on = i / 14 < lvl; ctx.fillStyle = on ? (i > 11 ? '#FF3030' : i > 8 ? '#FFD030' : '#40E060') : '#1A1A1A'; ctx.fillRect(x + 8, 992 - i * 16.5, 30, 12); }
    }
    pixelText('TAPE 1', 1605, 770, 4, NP.crtAmber, { edge: null });
    pixelText('SP', 1605, 815, 4, NP.crtAmber, { edge: null });
    pixelText(hms(since), 1605, 860, 4, NP.white, { edge: null });
    pixelText('REC 1989', 1605, 905, 4, frac(t * 1.5) < .6 ? '#FF4040' : '#702020', { edge: null });
    ctx.restore();
    flash(t, tP, .14, .7);
    osd(t, 'PLAY', 'EPOCH 2');
  }
  section('outro', (p, lt, d, t) => {
    hideOSD(); hideCaption();
    const t0 = t - lt, tIn = t0 + .1, tFull = t0 + .78, tR1 = snapB(t0 + .4 * d, .5), tP = snapB(t0 + .46 * d, .5);
    const u = clamp((t - (t0 + .02)) / (tR1 - t0 - .02));
    if (t < tFull) {
      // still in the room: the TV blooms on (the computer pressed REW) and we push in to its screen
      tapeFX({ crt: 0, chroma: 0, noise: .35, jitter: 0, dropouts: 0, cut: 'none' });
      const pic = renderTo('fin-rew', .5, () => rewindPic(t, u));
      const pk = ease(clamp((t - tIn) / (tFull - tIn))), cx = TVR.x + TVR.w / 2, cy = TVR.y + TVR.h / 2, zEnd = W / TVR.w * 1.04;
      const z = Math.exp(lerp(Math.log(1.26), Math.log(zEnd), pk));
      room(t, { red: 0, logN: 3, face: 'sly', raise: 1 - clamp((t - t0) / .4), clickT: t - clickTime(), vcr: 'REW ◀◀', counter: hms(t0 - (t - t0) * 30),
        tvOn: clamp((t - t0) / .22), tvPic: pic, cam: [lerp(980, cx, pk), lerp(585, cy, pk), z] });
      return;
    }
    if (t < tR1) {
      tapeFX({ dropouts: 3, chroma: 1, glitch: 'track', glitchK: .3 + .3 * hash(Math.floor(t * 30)), cut: 'none' });
      rewindPic(t, u);
      return;
    }
    if (t < tP) {
      blueScreen(); osd(t, 'STOP', null, '0:00:00');
      if (t < tR1 + .08) glitch('roll', 1 - (t - tR1) / .08);
      return;
    }
    endCard(t, tP);
  });
})();
