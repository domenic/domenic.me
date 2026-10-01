// ---- styles/idolfilm/core.js ----
// core.js: the idolfilm style's foundation: time, randomness, easing, the beat grid, the song's timing and words, the shot registry
// and the frame loop. It stands in for the shared src/core.js and src/timeline.js, which take a 2D context on the output canvas as
// they load; this style draws that canvas with WebGL2 (gl.js), so it keeps its own copy of what it needs from them.
// Everything a shot draws must be a pure function of song time `t`: frames render out of order, in parallel, and live.

const W = 1920, H = 1080, TAU = Math.PI * 2;
// In a page the canvas is #out; in a Web Worker the host sets self.OUT_CANVAS (an OffscreenCanvas) before loading the engine.
const HAS_DOM = typeof document !== 'undefined';
const canvas = HAS_DOM ? document.getElementById('out') : self.OUT_CANVAS;
// Scratch canvases: DOM canvases in pages, OffscreenCanvas in workers.
function makeCanvas(w, h) {
  if (!HAS_DOM) return new OffscreenCanvas(w, h);
  const c = document.createElement('canvas'); c.width = w; c.height = h; return c;
}
// Render scale: the scene is authored in 1920 × 1080 logical units; the canvas holds W·RS × H·RS pixels. The host sets it with ?scale=
// (studio, renderer) or setRenderScale() (the site, which steps it down when frames are slow). gl.js resizes its buffers in SCALE_HOOKS.
let RS = +(self.RENDER_SCALE || (typeof location !== 'undefined' && new URLSearchParams(location.search).get('scale')) || 1);
const SCALE_HOOKS = [];
function setRenderScale(s) {
  RS = s; canvas.width = Math.round(W * RS); canvas.height = Math.round(H * RS);
  for (const f of SCALE_HOOKS) f();
}

// ---------- math ----------
const clamp = (v, a = 0, b = 1) => Math.max(a, Math.min(b, v));
const lerp = (a, b, k) => a + (b - a) * k;
const frac = v => v - Math.floor(v);
const seg = (t, a, b) => clamp((t - a) / (b - a));
const ease = k => (k = clamp(k), k * k * (3 - 2 * k));
const easeIn = k => (k = clamp(k), k * k * k);
const easeOut = k => (k = clamp(k), 1 - (1 - k) ** 3);
const easeOut5 = k => (k = clamp(k), 1 - (1 - k) ** 5);
const easeInOut = k => (k = clamp(k), k < .5 ? 4 * k * k * k : 1 - (-2 * k + 2) ** 3 / 2);
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
function hash(n) {
  let x = Math.imul((n * 1000003) ^ 0x9E3779B9, 0x85EBCA6B);
  x ^= x >>> 13; x = Math.imul(x, 0xC2B2AE35); x ^= x >>> 16;
  return (x >>> 0) / 4294967296;
}
const hash2 = (a, b) => hash(a * 7919 + b * 104729 + 17);
const hstr = s => { let h = 5381; for (const c of String(s)) h = (Math.imul(h, 33) ^ c.charCodeAt(0)) | 0; return hash(h); };

// ---------- colour ----------
const rgbOf = hex => [1, 3, 5].map(i => parseInt(hex.slice(i, i + 2), 16) / 255);
function mixCol(a, b, k) {
  const A = rgbOf(a), B = rgbOf(b), c = v => Math.round(clamp(v) * 255).toString(16).padStart(2, '0');
  return '#' + c(lerp(A[0], B[0], k)) + c(lerp(A[1], B[1], k)) + c(lerp(A[2], B[2], k));
}
const alpha = (hex, a) => hex.slice(0, 7) + Math.round(clamp(a) * 255).toString(16).padStart(2, '0');

// ---------- the beat grid (filled from TIMING) ----------
let BPM = 150, BEAT0 = 0;
const beatLen = () => 60 / BPM;
const bpOf = t => (t - BEAT0) / beatLen();
const beatN = t => Math.floor(bpOf(t));
const barOf = t => bpOf(t) / 4;
const pulse = (t, k = 6) => Math.exp(-frac(bpOf(t)) * k);
const pulse2 = (t, k = 6) => Math.exp(-frac(bpOf(t) * 2) * k);
const onBeat = (t, n) => BEAT0 + n * beatLen();
const snap = t => onBeat(0, Math.round(bpOf(t)));

// ---------- the song's timing (timing.js, from tools/make_timing.py) ----------
// SEGS: contiguous windows {key, kind: intro|line|chorus|outro, sec, n, text, start, end, date}; LINES: every sung line {sec, n, text,
// start, end, words}. setTiming() swaps in another take's timing at runtime (shots are keyed to lines, so they re-sync).
let DUR, SEGS, LINES;
function setTiming(tm) { DUR = tm.dur; BPM = tm.bpm; BEAT0 = tm.beat0; SEGS = tm.segs; LINES = tm.lines; _captionLines = null; buildCuts(); }
function segAt(t) {
  let lo = 0, hi = SEGS.length - 1;
  if (t < SEGS[0].start) return SEGS[0];
  while (lo < hi) { const mid = (lo + hi + 1) >> 1; if (SEGS[mid].start <= t) lo = mid; else hi = mid - 1; }
  return SEGS[lo];
}
const segByKey = key => SEGS.find(s => s.key === key);
function span(sec) {
  const ss = SEGS.filter(s => s.sec === sec || s.key === sec);
  return { start: ss[0].start, end: ss[ss.length - 1].end };
}
const linesOf = sec => LINES.filter(l => l.sec === sec);
const lineOf = key => { const [sec, n] = key.split('.'); return LINES.find(l => l.sec === sec && l.n === +n); };
function lineAt(t) {
  for (let i = LINES.length - 1; i >= 0; i--) if (LINES[i].start <= t) return t < LINES[i].end + .35 ? LINES[i] : null;
  return null;
}
// A line's words (from tools/word_timing.py): each word's [start, end] in centiseconds from the line's start. The words are the text
// split at spaces and after a hyphen or dash inside a word.
const splitWords = text => String(text).split(/\s+/).filter(Boolean).flatMap(w => w.split(/(?<=[-–])(?=[A-Za-z0-9])/));
// A line's words with their times in seconds: [{ text, start, end }], evenly spread over the line when it has no word times.
function wordsOf(ln) {
  if (ln._w) return ln._w;
  const ws = splitWords(ln.text), ok = ln.words && ln.words.length === ws.length;
  const d = (ln.end - ln.start) / ws.length;
  return ln._w = ws.map((text, i) => ok ? { text, start: ln.start + ln.words[i][0] / 100, end: ln.start + ln.words[i][1] / 100 }
    : { text, start: ln.start + i * d, end: ln.start + (i + 1) * d });
}
// The line a subtitle shows at t (as the shared timeline's captionAt): a line comes up half a second before its first word (or as the
// one before it finishes), and goes when the next comes up or `linger` s after its last word.
let _captionLines = null;
function captionAt(t, linger = .35) {
  if (_captionLines?.lines !== LINES) {
    let before = -Infinity;
    _captionLines = { lines: LINES, list: LINES.map(ln => {
      const w = wordsOf(ln), first = w[0].start, last = w.at(-1).end;
      const on = Math.min(first, Math.max(first - .5, before));
      before = last;
      return { ln, on, first, last };
    }) };
  }
  const L = _captionLines.list;
  for (let i = L.length - 1; i >= 0; i--) if (L[i].on <= t) return t < Math.min(L[i + 1]?.on ?? Infinity, L[i].last + linger) ? L[i] : null;
  return null;
}

// ---------- cuts ----------
// A window in timing.js opens on the beat before its line, a third of a second or so before the first word, while the line before is
// still finishing its last word. So this style cuts on each line's first word (CUT_LEAD s before it), and a section (a chorus, the outro)
// on its first line's first word: CUTS [{ key, seg, start, end }], one per window, in order, covering the song.
const CUT_LEAD = .06;
let CUTS = [];
function buildCuts() {
  const first = s => {
    const ln = s.kind === 'line' ? lineOf(s.key) : (s.kind === 'chorus' || s.kind === 'outro') ? linesOf(s.key)[0] : null;
    return ln ? Math.max(s.start, wordsOf(ln)[0].start - CUT_LEAD) : s.start;
  };
  CUTS = SEGS.map((s, i) => ({ key: s.key, seg: s, start: i === 0 ? 0 : first(s) }));
  for (let i = 1; i < CUTS.length; i++) CUTS[i].start = Math.max(CUTS[i].start, CUTS[i - 1].start + .1);
  CUTS.forEach((c, i) => { c.end = CUTS[i + 1]?.start ?? DUR; });
}
function cutAt(t) {
  let lo = 0, hi = CUTS.length - 1;
  if (t < CUTS[0].start) return CUTS[0];
  while (lo < hi) { const mid = (lo + hi + 1) >> 1; if (CUTS[mid].start <= t) lo = mid; else hi = mid - 1; }
  return CUTS[lo];
}
const cutOf = key => CUTS.find(c => c.key === key);

// ---------- shot registry ----------
// line('V2', 5, fn): the shot for verse 2, line 5. section('C1', fn): the shot for a whole window. fn(p, lt, dur, t, seg): p = 0..1
// through the window's cut (see CUTS), lt = time since the cut. A window with no shot of its own falls back to DEFAULT_SHOT (kit.js).
const SHOTS = {};
function line(verse, n, fn) { SHOTS[`${verse}.${n}`] = fn; }
function section(key, fn) { SHOTS[key] = fn; }
let DEFAULT_SHOT = null;

// ---------- the frame ----------
let T = 0;
const FRAME_BEGIN = [], FRAME_END = [];   // gl.js and kit.js hook the frame's setup and its compositing here
// (one bad frame never stops the video: an error in a hook or a shot is logged, once per place, and the frame goes on; a shot that
// throws is drawn again by the default shot, so the frame isn't left half-built)
const _frameErrors = new Set();
function frameError(where, t, e) {
  if (_frameErrors.has(where)) return;
  _frameErrors.add(where);
  console.error(`${where} @ ${t.toFixed(2)}: ${e && e.stack || e}`);
}
function renderFrame(t) {
  T = t;
  const c = cutAt(t), s = c.seg;
  FRAME_BEGIN.forEach((f, i) => { try { f(t, s); } catch (e) { frameError(`frame setup ${i}`, t, e); } });
  const fn = SHOTS[c.key] || DEFAULT_SHOT, args = [clamp((t - c.start) / (c.end - c.start)), t - c.start, c.end - c.start, t, s];
  try {
    if (fn) fn(...args);
  } catch (e) {
    frameError(`shot ${s && s.key}`, t, e);
    try { if (DEFAULT_SHOT && fn !== DEFAULT_SHOT) DEFAULT_SHOT(...args); } catch (e2) { frameError('default shot', t, e2); }
  }
  FRAME_END.forEach((f, i) => { try { f(t, s); } catch (e) { frameError(`frame end ${i}`, t, e); } });
}

;
// ---- styles/demoscene/modern/draw2d.js ----
// modern/draw2d.js: the modern engine's 2D layers (the UI and the three panels), drawn with WebGL.
//
// Scenes draw on a layer with the canvas 2D API, through a stand-in for its context (a proxy). The stand-in keeps the drawing
// state (styles, the transform, clips, the path) and records each drawing call as an item; when the layer is flushed, the items
// are drawn, in the order they were made and blended as their composite operations say, into the layer's own render target, a
// texture the GPU samples: quads, drawn instanced, a few draw calls a frame. Nothing is drawn into the layer's 2D canvas, and
// nothing it holds is uploaded. How each call is drawn:
// - rectangles, discs, rings, convex polygons (cut to the layer: up to 32 corners) and strokes of lines and curves (flattened;
//   the strokes' segments gathered in a coverage buffer, taking the largest, so that a stroke is painted once) are shaded
//   analytically, with their antialiasing (each pixel's coverage) and their paint (a colour; a linear, radial or conic gradient;
//   a pattern) worked out per pixel;
// - everything else is a sprite, drawn once by a 2D canvas and kept in an atlas: a string of text (the 2D canvas lays it out,
//   ligatures, kerning and spacing and all, drawn in its colour; a gradient paints its coverage), a fill of another shape (its
//   coverage, painted by the shader), a clip that isn't a rectangle (its coverage), and anything drawn with a shadow, a filter or
//   a style the shader can't paint (drawn whole);
// - drawImage() samples the image as a texture, uploaded when the canvas is new or has been drawn on since (its version), or, for
//   a layer's own canvas, that layer's target.
// So a frame whose drawing only moves, fades or recolours what earlier frames drew uploads nothing, and one that draws something new
// uploads just that. (In Firefox, whose 2D canvases in a worker live apart from WebGL, every upload copies its whole source canvas,
// at some 0.4 ms a megabyte on a Surface Pro: the UI alone was 19 MB full screen there.)
//
// What a frame draws depends on nothing but what it draws: its pixels are the same whatever frames came before, and whatever the
// warm-up drew between them. It holds by construction:
// - a layer starts each frame from the 2D context's default state (as a new canvas has it), so nothing a scene leaves set carries
//   over to another frame or scene;
// - a sprite is named by a key that says everything its pixels depend on, exactly (its text, font state and colour, its path's
//   commands, its transform's linear part, where it falls within a pixel), and it's drawn from what its key says alone, so that the
//   same key is always the same pixels;
// - where a sprite lands is worked out from the frame's own drawing: text snapped to whole pixels (a string's first glyph's origin,
//   on its baseline; the 2D canvas places the rest), other sprites to quarter pixels; no browser's own placement is measured;
// - sprites in the atlas are never changed once drawn: a layer's flush looks up every sprite it needs, then makes room for the new
//   ones by emptying pages none of its sprites are on (the least lately used first), and only then draws; so a page is emptied
//   only between draws, never under one. What doesn't fit gets a texture of its own for that draw.
//
// The UI's target holds premultiplied colour (SHADERS.final and compose composite it so, and the scene shader's glow samples it as
// straight colour); a panel's is then turned into straight colour with mipmaps, as the scene shader samples panels. Render mode (a
// script capturing frames with toDataURL) draws on the 2D canvases, as the video always was drawn, and uploads them whole.
const D2 = (() => {
  const RENDER_MODE = HAS_DOM && /[?&]render\b/.test(location.search);
  const TAU = 2 * Math.PI;
  const PAGE = 2048, PAGES = 6, BIG = 1024;   // (atlas pages; a sprite wider or taller than BIG gets a texture of its own)
  const BIG_BYTES = 64 << 20;                 // (how much such textures may hold before those unused lately go)
  const FLOATS = 36;                          // (per instance: 9 vec4s)
  // (texture units: the pages are 0-5; a sprite's and a clip's textures of their own 6 and 7; textures are made and filled on the
  // last, which the program doesn't sample)
  const U_SPR = 6, U_MSK = 7, U_IMG = 8, U_COV = 9, U_DST = 10, U_PAINT = 11, U_SCRATCH = 12;

  // ---------- 2D canvases on the CPU ----------
  // Outside render mode, every 2D canvas made from here on (the scenes' caches among them) is drawn on the CPU, unless asked
  // otherwise (willReadFrequently): its pixels are then the same whenever it's drawn, whereas Chromium draws some canvases on the
  // GPU and some on the CPU, depending on how many there are and how big, with antialiasing and blending a level or two apart.
  if (!RENDER_MODE) for (const C of [self.HTMLCanvasElement, self.OffscreenCanvas]) {
    const f = C?.prototype.getContext;
    if (!f || f.cpu2d) continue;
    const w = function (type, o) { return type === '2d' && o?.willReadFrequently === undefined ? f.call(this, type, { ...o, willReadFrequently: true }) : f.call(this, type, o); };
    w.cpu2d = true; C.prototype.getContext = w;
  }
  // ---------- canvases' versions ----------
  // A canvas drawn with drawImage() (or as a pattern) is uploaded again only when it has been drawn on since: any 2D drawing on it
  // bumps its version.
  for (const C of [self.CanvasRenderingContext2D, self.OffscreenCanvasRenderingContext2D]) {
    if (!C) continue;
    for (const m of ['fillRect', 'strokeRect', 'clearRect', 'fillText', 'strokeText', 'drawImage', 'fill', 'stroke', 'putImageData', 'reset']) {
      const f = C.prototype[m];
      if (!f || f.bumps) continue;
      const w = function (...a) { const c = this.canvas; if (c) c.__v = (c.__v | 0) + 1; return f.apply(this, a); };
      w.bumps = true; C.prototype[m] = w;
    }
  }
  // ---------- Path2D objects keep their commands (for their bounds, strokes and keys) ----------
  const PATH_OPS = ['moveTo', 'lineTo', 'arc', 'arcTo', 'rect', 'roundRect', 'ellipse', 'bezierCurveTo', 'quadraticCurveTo', 'closePath'];
  if (self.Path2D && !self.Path2D.__rec) {
    const P0 = self.Path2D;
    for (const m of PATH_OPS) {
      const f = P0.prototype[m];
      if (!f) continue;
      P0.prototype[m] = function (...a) { (this.__ops ??= []).push({ op: m, a }); return f.apply(this, a); };
    }
    const add = P0.prototype.addPath;
    if (add) P0.prototype.addPath = function (...a) { this.__opaque = true; return add.apply(this, a); };
    // (a path made from SVG path data can't be read back: it's drawn whole, as a sprite as big as the layer)
    class P2 extends P0 { constructor(a) { super(a); if (a instanceof P0) { if (a.__opaque) this.__opaque = true; else if (a.__ops) this.__ops = a.__ops.slice(); } else if (a !== undefined) this.__opaque = true; } }
    P2.__rec = true;
    self.Path2D = P2;
  }

  // ---------- keys ----------
  // (a key's hash, for comparing a frame's drawing with the last's)
  function strHash(s) {
    let a = 0x811c9dc5, b = 0x9747b28c;
    for (let i = 0; i < s.length; i++) { const w = s.charCodeAt(i); a = Math.imul(a ^ w, 16777619); b = Math.imul(b ^ (w + 0x9e3779b9 | 0), 2246822519) ^ (b >>> 15); }
    return [a, b];
  }
  // (arguments, exactly: numbers as JavaScript writes them, which read back as the same numbers)
  const num = v => typeof v === 'number' ? String(v) : Array.isArray(v) ? '[' + v.map(num).join(',') + ']' : v && typeof v === 'object' ? `{${num(v.x ?? 0)},${num(v.y ?? 0)}}` : String(v);
  const idMap = new WeakMap();
  let nextId = 1;
  const IDS = o => { let i = idMap.get(o); if (!i) idMap.set(o, i = nextId++); return i; };

  // ---------- colours ----------
  const NC = makeCanvas(1, 1).getContext('2d'), COLORS = new Map();
  // (a CSS colour → [r, g, b, a], each 0..1, or null if it isn't one)
  const HEX = /^#([\da-f]{3,4}|[\da-f]{6}|[\da-f]{8})$/i, RGB = /^rgba?\(\s*([\d.]+)\s*[,\s]\s*([\d.]+)\s*[,\s]\s*([\d.]+)\s*(?:[,/]\s*([\d.]+)(%?)\s*)?\)$/;
  function color(s) {
    let c = COLORS.get(s);
    if (c !== undefined) return c;
    // (the common forms read here; any other by the 2D canvas)
    let m;
    if (typeof s === 'string' && (m = HEX.exec(s))) {
      const h = m[1], d = h.length <= 4 ? [...h].map(x => parseInt(x + x, 16)) : h.match(/../g).map(x => parseInt(x, 16));
      c = [d[0] / 255, d[1] / 255, d[2] / 255, d.length > 3 ? d[3] / 255 : 1];
    } else if (typeof s === 'string' && (m = RGB.exec(s)) && +m[1] <= 255 && +m[2] <= 255 && +m[3] <= 255) {
      const a = m[4] === undefined ? 1 : Math.min(1, +m[4] / (m[5] ? 100 : 1));
      c = [Math.round(+m[1]) / 255, Math.round(+m[2]) / 255, Math.round(+m[3]) / 255, a];
    }
    if (c) { if (COLORS.size > 5000) COLORS.clear(); COLORS.set(s, c); return c; }
    NC.fillStyle = '#010203'; NC.fillStyle = s;
    const n = NC.fillStyle;
    if (n[0] === '#') c = [parseInt(n.slice(1, 3), 16) / 255, parseInt(n.slice(3, 5), 16) / 255, parseInt(n.slice(5, 7), 16) / 255, 1];
    else { const m = n.match(/[\d.]+/g); c = m && m.length >= 3 ? [m[0] / 255, m[1] / 255, m[2] / 255, m.length > 3 ? +m[3] : 1] : null; }
    if (n === '#010203' && !/^#010203$/i.test(String(s).trim())) c = null;
    if (COLORS.size > 5000) COLORS.clear();
    COLORS.set(s, c);
    return c;
  }
  const cssOf = c => `rgba(${Math.round(c[0] * 255)},${Math.round(c[1] * 255)},${Math.round(c[2] * 255)},${c[3]})`;

  // ---------- gradients and patterns made through a layer: what they are, standing in for the real ones ----------
  const DESC = new WeakMap();   // (the real CanvasGradient or CanvasPattern, or its stand-in → its description)
  function gradient(g, k, a) {
    const real = g[k](...a), D = { kind: k === 'createLinearGradient' ? 1 : k === 'createRadialGradient' ? 2 : 3, a: a.map(Number), stops: [], real, id: nextId++ };
    const w = { addColorStop(o, c) { real.addColorStop(o, c); const col = color(c); D.stops.push([+o, col]); D.avg = null; } };
    DESC.set(w, D); DESC.set(real, D);
    return w;
  }
  function pattern(g, img, rep) {
    const real = g.createPattern(img, rep);
    if (!real) return real;
    const D = { kind: 4, img, rep: rep || 'repeat', m: [1, 0, 0, 1, 0, 0], real, id: nextId++ };
    const w = { setTransform(m) { real.setTransform(m); D.m = m ? [m.a ?? 1, m.b ?? 0, m.c ?? 0, m.d ?? 1, m.e ?? 0, m.f ?? 0] : [1, 0, 0, 1, 0, 0]; } };
    DESC.set(w, D); DESC.set(real, D);
    return w;
  }
  const unwrap = v => DESC.get(v)?.real ?? v;
  // (a style as it is now, for a sprite drawn whole: a colour, a gradient's geometry and stops, a pattern's image (and its version)
  // and transform, or one made elsewhere; its key, exactly; and the style made from it on a sprite's own context)
  function snapStyle(s) {
    if (typeof s === 'string') return s;
    const D = DESC.get(s);
    if (!D) return { foreign: s };
    return D.kind === 4 ? { kind: 4, img: D.img, v: D.img.__v | 0, rep: D.rep, m: D.m.slice() } : { kind: D.kind, a: D.a.slice(), stops: D.stops.slice() };
  }
  function styleKey(s) {
    if (typeof s === 'string') return s;
    if (s.foreign) return 'F' + IDS(s.foreign);
    if (s.kind === 4) return `P${IDS(s.img)}v${s.v}:${s.rep}:${s.m.map(num)}`;
    return `G${s.kind}:${s.a.map(num)}:${s.stops.map(t => num(t[0]) + '=' + (t[1] ? t[1].map(num).join('/') : 'x')).join(';')}`;
  }
  function realize(gg, s) {
    if (typeof s === 'string') return s;
    if (s.foreign) return s.foreign;
    if (s.kind === 4) { const p = gg.createPattern(s.img, s.rep); if (p && p.setTransform) p.setTransform(new DOMMatrix(s.m)); return p ?? 'transparent'; }
    const r = s.kind === 1 ? gg.createLinearGradient(...s.a) : s.kind === 2 ? gg.createRadialGradient(...s.a) : gg.createConicGradient(...s.a);
    for (const [o, c] of s.stops) if (c) r.addColorStop(o, cssOf(c));
    return r;
  }

  // ---------- transforms: [a, b, c, d, e, f], as canvas has them (x' = a x + c y + e, y' = b x + d y + f) ----------
  const mmul = (m, n) => [m[0] * n[0] + m[2] * n[1], m[1] * n[0] + m[3] * n[1], m[0] * n[2] + m[2] * n[3], m[1] * n[2] + m[3] * n[3], m[0] * n[4] + m[2] * n[5] + m[4], m[1] * n[4] + m[3] * n[5] + m[5]];
  function minv(m) { const d = m[0] * m[3] - m[1] * m[2]; if (!d || !isFinite(d)) return null; return [m[3] / d, -m[1] / d, -m[2] / d, m[0] / d, (m[2] * m[5] - m[3] * m[4]) / d, (m[1] * m[4] - m[0] * m[5]) / d]; }
  const ID = [1, 0, 0, 1, 0, 0];
  const lin = m => m.lk ?? (m.lk = `${m[0]},${m[1]},${m[2]},${m[3]}`);   // (its linear part, exactly; transforms are never changed in place)
  // (a similarity, a rotation and an even scale, as strokes drawn analytically need; its scale)
  const simScale = m => { const s2 = m[0] * m[0] + m[1] * m[1], t2 = m[2] * m[2] + m[3] * m[3]; return Math.abs(s2 - t2) <= 1e-6 * Math.max(s2, t2) && Math.abs(m[0] * m[2] + m[1] * m[3]) <= 1e-6 * Math.max(s2, t2) ? Math.sqrt(s2) : 0; };

  // ---------- the drawing state ----------
  const PROPS = ['globalAlpha', 'globalCompositeOperation', 'fillStyle', 'strokeStyle', 'lineWidth', 'lineCap', 'lineJoin', 'miterLimit', 'lineDashOffset', 'font', 'textAlign', 'textBaseline', 'direction', 'letterSpacing', 'wordSpacing', 'fontKerning', 'fontStretch', 'fontVariantCaps', 'textRendering', 'shadowBlur', 'shadowColor', 'shadowOffsetX', 'shadowOffsetY', 'imageSmoothingEnabled', 'imageSmoothingQuality', 'filter'];
  const RAW = Object.fromEntries(PROPS.map(k => [k, k + '#']));   // (where the state keeps the value each property was last set to)
  const TEXT_PROPS = ['font', 'textAlign', 'textBaseline', 'direction', 'letterSpacing', 'wordSpacing', 'fontKerning', 'fontStretch', 'fontVariantCaps', 'textRendering'], TEXT_SET = new Set(TEXT_PROPS);
  // (the state a new context has)
  const DEFAULTS = (() => { const g = makeCanvas(1, 1).getContext('2d'), D = {}; for (const k of PROPS) D[k] = g[k]; return D; })();
  // (composite operations: the Porter-Duff ones as blend factors; * marks those that change pixels outside what's drawn)
  const OPS = {
    'source-over': ['ONE', 'ONE_MINUS_SRC_ALPHA'], lighter: ['ONE', 'ONE'], 'destination-out': ['ZERO', 'ONE_MINUS_SRC_ALPHA'],
    'source-atop': ['DST_ALPHA', 'ONE_MINUS_SRC_ALPHA'], 'destination-over': ['ONE_MINUS_DST_ALPHA', 'ONE'], xor: ['ONE_MINUS_DST_ALPHA', 'ONE_MINUS_SRC_ALPHA'],
    copy: ['ONE', 'ZERO', 1], 'source-in': ['DST_ALPHA', 'ZERO', 1], 'destination-in': ['ZERO', 'SRC_ALPHA', 1], 'source-out': ['ONE_MINUS_DST_ALPHA', 'ZERO', 1], 'destination-atop': ['ONE_MINUS_DST_ALPHA', 'SRC_ALPHA', 1],
  };
  // (the blend modes, drawn by reading back what's under them: the separable ones, then the others)
  const MIX = { multiply: 1, screen: 2, overlay: 3, darken: 4, lighten: 5, 'color-dodge': 6, 'color-burn': 7, 'hard-light': 8, 'soft-light': 9, difference: 10, exclusion: 11, hue: 12, saturation: 13, color: 14, luminosity: 15 };
  const OPN = {};
  Object.keys(OPS).forEach((k, i) => { OPN[k] = i; });
  Object.keys(MIX).forEach((k, i) => { OPN[k] = 100 + i; });
  // (a drawing-state value as canvas takes it, or undefined where canvas ignores it)
  const ENUMS = { lineCap: ['butt', 'round', 'square'], lineJoin: ['round', 'bevel', 'miter'], imageSmoothingQuality: ['low', 'medium', 'high'], globalCompositeOperation: [...Object.keys(OPS), ...Object.keys(MIX)] };
  function accept(k, v) {
    switch (k) {
      case 'globalAlpha': v = +v; return isFinite(v) && v >= 0 && v <= 1 ? v : undefined;
      case 'lineWidth': case 'miterLimit': v = +v; return isFinite(v) && v > 0 ? v : undefined;
      case 'shadowBlur': v = +v; return isFinite(v) && v >= 0 ? v : undefined;
      case 'shadowOffsetX': case 'shadowOffsetY': case 'lineDashOffset': v = +v; return isFinite(v) ? v : undefined;
      case 'imageSmoothingEnabled': return !!v;
      case 'filter': return String(v);
      case 'fillStyle': case 'strokeStyle': case 'shadowColor':
        if (typeof v === 'string') return color(v) ? v : undefined;
        return k !== 'shadowColor' && v && (DESC.has(v) || (self.CanvasGradient && v instanceof CanvasGradient) || (self.CanvasPattern && v instanceof CanvasPattern)) ? v : undefined;
      default: return ENUMS[k]?.includes(String(v)) ? String(v) : undefined;
    }
  }
  const warned = new Set();
  const warn = m => { if (!warned.has(m)) { warned.add(m); console.warn('draw2d: ' + m); } };

  // ---------- paths ----------
  // A path is a list of commands {op, a, M}: the arguments in the user space of the transform M in force when each was made.
  // flatten(): its subpaths as polylines in the canvas's pixels [{p: [x0, y0, x1, y1, …], closed}], curves to within tol.
  function flatten(ops, tol = .2) {
    const subs = [];
    let cur = null, cx = 0, cy = 0, sx = 0, sy = 0, has = false;
    const T = (M, x, y) => [M[0] * x + M[2] * y + M[4], M[1] * x + M[3] * y + M[5]];
    const start = (x, y) => { cur = { p: [x, y], closed: false }; subs.push(cur); cx = sx = x; cy = sy = y; has = true; };
    const to = (x, y) => { if (!has) { start(x, y); return; } cur.p.push(x, y); cx = x; cy = y; };
    const scaleOf = M => Math.sqrt(Math.max(M[0] * M[0] + M[1] * M[1], M[2] * M[2] + M[3] * M[3]));
    function ellipseArc(M, x, y, rx, ry, rot, a0, a1, ccw) {
      let sw;
      if (!ccw) { sw = a1 - a0; if (sw >= TAU) sw = TAU; else { sw %= TAU; if (sw < 0) sw += TAU; } }
      else { sw = a0 - a1; if (sw >= TAU) sw = TAU; else { sw %= TAU; if (sw < 0) sw += TAU; } sw = -sw; }
      const R = Math.max(rx, ry) * scaleOf(M), n = Math.max(2, Math.ceil(Math.abs(sw) / (2 * Math.acos(Math.max(-1, 1 - tol / Math.max(R, tol))))));
      const cr = Math.cos(rot), sr = Math.sin(rot);
      for (let i = 0; i <= n; i++) {
        const t = a0 + sw * i / n, ex = rx * Math.cos(t), ey = ry * Math.sin(t);
        const [X, Y] = T(M, x + ex * cr - ey * sr, y + ex * sr + ey * cr);
        if (i === 0 && has) to(X, Y); else if (i === 0) start(X, Y); else to(X, Y);
      }
    }
    for (const o of ops) {
      const M = o.M, a = o.a;
      switch (o.op) {
        case 'moveTo': { const [X, Y] = T(M, a[0], a[1]); start(X, Y); break; }
        case 'lineTo': { const [X, Y] = T(M, a[0], a[1]); to(X, Y); break; }
        case 'closePath': if (has && cur) { cur.closed = true; start(sx, sy); subs.pop(); cur = { p: [sx, sy], closed: false }; subs.push(cur); cx = sx; cy = sy; } break;
        case 'rect': { const [x, y, w, h] = a; const q = [T(M, x, y), T(M, x + w, y), T(M, x + w, y + h), T(M, x, y + h)]; start(...q[0]); to(...q[1]); to(...q[2]); to(...q[3]); cur.closed = true; start(...q[0]); break; }
        case 'roundRect': {
          const [x, y, w, h] = a, R = cornerRadii(a[4], w, h);
          if (!R) break;
          const sx0 = Math.sign(w) || 1, sy0 = Math.sign(h) || 1, X0 = Math.min(x, x + w), Y0 = Math.min(y, y + h), W = Math.abs(w), H = Math.abs(h);
          // (corners: upper left, upper right, lower right, lower left, of the normalised rectangle; mirrored as w and h are)
          let [ul, ur, lr, ll] = R;
          if (sx0 < 0) [ul, ur, lr, ll] = [ur, ul, ll, lr];
          if (sy0 < 0) [ul, ur, lr, ll] = [ll, lr, ur, ul];
          start(...T(M, X0 + ul[0], Y0));
          to(...T(M, X0 + W - ur[0], Y0)); ellipseArc(M, X0 + W - ur[0], Y0 + ur[1], ur[0], ur[1], 0, -Math.PI / 2, 0, false);
          to(...T(M, X0 + W, Y0 + H - lr[1])); ellipseArc(M, X0 + W - lr[0], Y0 + H - lr[1], lr[0], lr[1], 0, 0, Math.PI / 2, false);
          to(...T(M, X0 + ll[0], Y0 + H)); ellipseArc(M, X0 + ll[0], Y0 + H - ll[1], ll[0], ll[1], 0, Math.PI / 2, Math.PI, false);
          to(...T(M, X0, Y0 + ul[1])); ellipseArc(M, X0 + ul[0], Y0 + ul[1], ul[0], ul[1], 0, Math.PI, Math.PI * 1.5, false);
          cur.closed = true; start(...T(M, x, y));
          break;
        }
        case 'arc': ellipseArc(M, a[0], a[1], Math.abs(a[2]), Math.abs(a[2]), 0, a[3], a[4], !!a[5]); break;
        case 'ellipse': ellipseArc(M, a[0], a[1], Math.abs(a[2]), Math.abs(a[3]), a[4], a[5], a[6], !!a[7]); break;
        case 'bezierCurveTo': {
          if (!has) start(...T(M, a[0], a[1]));
          const p0 = [cx, cy], p1 = T(M, a[0], a[1]), p2 = T(M, a[2], a[3]), p3 = T(M, a[4], a[5]);
          const L = Math.hypot(p1[0] - p0[0], p1[1] - p0[1]) + Math.hypot(p2[0] - p1[0], p2[1] - p1[1]) + Math.hypot(p3[0] - p2[0], p3[1] - p2[1]);
          const n = Math.max(2, Math.min(200, Math.ceil(Math.sqrt(L / tol) * .6)));
          for (let i = 1; i <= n; i++) { const t = i / n, u = 1 - t; to(u * u * u * p0[0] + 3 * u * u * t * p1[0] + 3 * u * t * t * p2[0] + t * t * t * p3[0], u * u * u * p0[1] + 3 * u * u * t * p1[1] + 3 * u * t * t * p2[1] + t * t * t * p3[1]); }
          break;
        }
        case 'quadraticCurveTo': {
          if (!has) start(...T(M, a[0], a[1]));
          const p0 = [cx, cy], p1 = T(M, a[0], a[1]), p2 = T(M, a[2], a[3]);
          const L = Math.hypot(p1[0] - p0[0], p1[1] - p0[1]) + Math.hypot(p2[0] - p1[0], p2[1] - p1[1]);
          const n = Math.max(2, Math.min(200, Math.ceil(Math.sqrt(L / tol) * .6)));
          for (let i = 1; i <= n; i++) { const t = i / n, u = 1 - t; to(u * u * p0[0] + 2 * u * t * p1[0] + t * t * p2[0], u * u * p0[1] + 2 * u * t * p1[1] + t * t * p2[1]); }
          break;
        }
        case 'arcTo': {
          if (!has) { start(...T(M, a[0], a[1])); break; }
          const Mi = minv(M); if (!Mi) break;
          const P0 = T(Mi, cx, cy), [x1, y1, x2, y2, r] = a;
          const v1 = [P0[0] - x1, P0[1] - y1], v2 = [x2 - x1, y2 - y1], l1 = Math.hypot(...v1), l2 = Math.hypot(...v2);
          const cr = v1[0] * v2[1] - v1[1] * v2[0];
          if (!r || !l1 || !l2 || Math.abs(cr) < 1e-9) { to(...T(M, x1, y1)); break; }
          const cosA = (v1[0] * v2[0] + v1[1] * v2[1]) / (l1 * l2), ang = Math.acos(Math.max(-1, Math.min(1, cosA))), d = r / Math.tan(ang / 2);
          const t1 = [x1 + v1[0] / l1 * d, y1 + v1[1] / l1 * d], t2 = [x1 + v2[0] / l2 * d, y1 + v2[1] / l2 * d];
          const bis = [v1[0] / l1 + v2[0] / l2, v1[1] / l1 + v2[1] / l2], bl = Math.hypot(...bis), h = r / Math.sin(ang / 2);
          const c = [x1 + bis[0] / bl * h, y1 + bis[1] / bl * h];
          const s0 = Math.atan2(t1[1] - c[1], t1[0] - c[0]), s1 = Math.atan2(t2[1] - c[1], t2[0] - c[0]);
          to(...T(M, t1[0], t1[1]));
          ellipseArc(M, c[0], c[1], r, r, 0, s0, s1, cr > 0);
          break;
        }
      }
    }
    return subs.filter(s => s.p.length >= 2);
  }
  // (a polygon's winding, 1 or −1, if it's convex (and not all in a line); else 0)
  function convexSign(P) {
    if (P.length < 3) return 0;
    let sg = 0, area = 0;
    for (let i = 0; i < P.length; i++) {
      const a = P[i], b = P[(i + 1) % P.length], c = P[(i + 2) % P.length], cr = (b[0] - a[0]) * (c[1] - b[1]) - (b[1] - a[1]) * (c[0] - b[0]);
      area += a[0] * b[1] - b[0] * a[1];
      if (Math.abs(cr) < 1e-9) continue;
      if (sg && Math.sign(cr) !== sg) return 0;
      sg = Math.sign(cr);
    }
    return Math.abs(area) > 1e-9 ? Math.sign(area) : 0;
  }
  // (a convex polygon cut to a rectangle)
  function cutPoly(P, x0, y0, x1, y1) {
    for (const [ax, lim, keep] of [[0, x0, 1], [0, x1, -1], [1, y0, 1], [1, y1, -1]]) {
      const out = [];
      for (let i = 0; i < P.length; i++) {
        const a = P[i], b = P[(i + 1) % P.length], ina = (a[ax] - lim) * keep >= 0, inb = (b[ax] - lim) * keep >= 0;
        if (ina) out.push(a);
        if (ina !== inb) { const k = (lim - a[ax]) / (b[ax] - a[ax]); out.push([a[0] + (b[0] - a[0]) * k, a[1] + (b[1] - a[1]) * k]); }
      }
      P = out;
      if (P.length < 3) return P;
    }
    return P;
  }
  // (roundRect()'s radii, as the four corners' [rx, ry], scaled down where they would overlap; null if invalid)
  function cornerRadii(r, w, h) {
    let L = Array.isArray(r) ? r : [r ?? 0];
    if (!L.length || L.length > 4) return null;
    L = L.map(v => typeof v === 'number' ? [v, v] : [v?.x ?? 0, v?.y ?? 0]);
    if (L.some(v => !(v[0] >= 0 && v[1] >= 0))) return null;
    const C = L.length === 1 ? [L[0], L[0], L[0], L[0]] : L.length === 2 ? [L[0], L[1], L[0], L[1]] : L.length === 3 ? [L[0], L[1], L[2], L[1]] : L;
    const W = Math.abs(w), H = Math.abs(h);
    const k = Math.min(1, W / (C[0][0] + C[1][0] || 1), W / (C[3][0] + C[2][0] || 1), H / (C[0][1] + C[3][1] || 1), H / (C[1][1] + C[2][1] || 1));
    return C.map(v => [v[0] * k, v[1] * k]);
  }
  // (a path's first point in the canvas's pixels: where its sprites are anchored)
  function anchorOf(ops) {
    for (const o of ops) if (o.op !== 'closePath') { const M = o.M; return [M[0] * o.a[0] + M[2] * o.a[1] + M[4], M[1] * o.a[0] + M[3] * o.a[1] + M[5]]; }
    return null;
  }
  // (a path's bounds in the canvas's pixels, generously: control points and each arc's whole ellipse)
  function pathBounds(ops) {
    let x0 = Infinity, y0 = Infinity, x1 = -Infinity, y1 = -Infinity;
    const add = (M, x, y) => { const X = M[0] * x + M[2] * y + M[4], Y = M[1] * x + M[3] * y + M[5]; if (X < x0) x0 = X; if (X > x1) x1 = X; if (Y < y0) y0 = Y; if (Y > y1) y1 = Y; };
    for (const o of ops) {
      const M = o.M, a = o.a;
      switch (o.op) {
        case 'moveTo': case 'lineTo': add(M, a[0], a[1]); break;
        case 'rect': case 'roundRect': add(M, a[0], a[1]); add(M, a[0] + a[2], a[1]); add(M, a[0], a[1] + a[3]); add(M, a[0] + a[2], a[1] + a[3]); break;
        case 'arc': case 'ellipse': { const rx = Math.abs(a[2]), ry = o.op === 'arc' ? rx : Math.abs(a[3]), r = Math.max(rx, ry); add(M, a[0] - r, a[1] - r); add(M, a[0] + r, a[1] - r); add(M, a[0] - r, a[1] + r); add(M, a[0] + r, a[1] + r); break; }
        case 'arcTo': add(M, a[0], a[1]); add(M, a[2], a[3]); break;
        case 'bezierCurveTo': add(M, a[0], a[1]); add(M, a[2], a[3]); add(M, a[4], a[5]); break;
        case 'quadraticCurveTo': add(M, a[0], a[1]); add(M, a[2], a[3]); break;
      }
    }
    return x0 <= x1 ? [x0, y0, x1, y1] : null;
  }
  // (replay a path on a 2D context, each command in its own transform, moved by (dx, dy) pixels)
  function replay(g, ops, dx, dy) {
    g.beginPath();
    let lastM = null;
    for (const o of ops) {
      if (o.M !== lastM) { const M = o.M; g.setTransform(M[0], M[1], M[2], M[3], M[4] + dx, M[5] + dy); lastM = M; }
      g[o.op](...o.a);
    }
  }
  const ops2d = (p, M) => (p.__ops ?? []).map(o => ({ op: o.op, a: o.a, M }));
  // A sprite's paths (a fill's, or a clip's, one or more): its key (each command exactly, with its transform's linear part and its
  // translation from the first command's), its anchor A (the first command's first point, in the canvas's pixels) and its commands
  // in transforms about A (T: their translations made from the key's numbers alone, so that its drawing is what its key says).
  function opsSpec(lists) {
    let first = null;
    for (const ops of lists) { first = ops.find(o => o.op !== 'closePath'); if (first) break; }
    if (!first) return null;
    const M0 = first.M, rel = [M0[0] * first.a[0] + M0[2] * first.a[1], M0[1] * first.a[0] + M0[3] * first.a[1]];
    let key = '';
    const T = lists.map(ops => {
      key += '#';
      let lastM = null, TM = null;
      return ops.map(o => {
        const M = o.M;
        if (M !== lastM) {
          const dx = M[4] - M0[4], dy = M[5] - M0[5];
          key += '|' + lin(M) + ',' + dx + ',' + dy;
          TM = [M[0], M[1], M[2], M[3], dx - rel[0], dy - rel[1]]; lastM = M;
        }
        key += o.op + ':' + num(o.a) + ';';
        return { op: o.op, a: o.a, M: TM };
      });
    });
    // (another transform about the anchor too, with its part of a key)
    const about = M => { const dx = M[4] - M0[4], dy = M[5] - M0[5]; return { k: lin(M) + ',' + dx + ',' + dy, T: [M[0], M[1], M[2], M[3], dx - rel[0], dy - rel[1]] }; };
    return { key, A: [M0[4] + rel[0], M0[5] + rel[1]], T, about };
  }

  // ---------- strokes, as pieces whose coverage is shaded ----------
  // A stroke is drawn as segments with round or flat ends (an end is round where segments join, and at the path's ends if its caps
  // are), and a wedge for each miter join; their coverages are combined by taking the largest, in a coverage buffer, and the
  // stroke's paint is then laid through it: so a stroke that crosses itself is still painted once, as canvas paints it. (Bevel joins
  // come out round.)
  function strokePieces(subs, hw, cap, join, miter, dash, dashOff, out) {
    if (dash && dash.length) subs = dashed(subs, dash, dashOff);
    let x0 = Infinity, y0 = Infinity, x1 = -Infinity, y1 = -Infinity;
    const box = (x, y, r) => { if (x - r < x0) x0 = x - r; if (y - r < y0) y0 = y - r; if (x + r > x1) x1 = x + r; if (y + r > y1) y1 = y + r; };
    for (const s of subs) {
      // (without repeated points)
      const P = [s.p[0], s.p[1]];
      for (let i = 2; i < s.p.length; i += 2) if (Math.abs(s.p[i] - P[P.length - 2]) > 1e-6 || Math.abs(s.p[i + 1] - P[P.length - 1]) > 1e-6) P.push(s.p[i], s.p[i + 1]);
      let closed = s.closed;
      if (closed && P.length > 2 && Math.abs(P[0] - P[P.length - 2]) < 1e-6 && Math.abs(P[1] - P[P.length - 1]) < 1e-6) P.length -= 2;
      const n = P.length / 2;
      if (n === 1) {
        // (a subpath of no length: a dot with round caps, a square with square ones, nothing with butt ones)
        if (closed || cap === 'butt') continue;
        if (cap === 'round') out.push([P[0], P[1], P[0], P[1], hw, 1, 1]);
        else out.push([P[0] - hw, P[1], P[0] + hw, P[1], hw, 0, 0]);
        box(P[0], P[1], hw * 1.5);
        continue;
      }
      if (n === 2) closed = false;
      const nseg = closed ? n : n - 1, rc = cap === 'round' ? 1 : 0;
      for (let i = 0; i < nseg; i++) {
        let ax = P[2 * i], ay = P[2 * i + 1];
        const j = (i + 1) % n;
        let bx = P[2 * j], by = P[2 * j + 1];
        const first = !closed && i === 0, last = !closed && i === nseg - 1;
        if (cap === 'square' && (first || last)) {
          const L = Math.hypot(bx - ax, by - ay) || 1, dx = (bx - ax) / L * hw, dy = (by - ay) / L * hw;
          if (first) { ax -= dx; ay -= dy; } if (last) { bx += dx; by += dy; }
        }
        out.push([ax, ay, bx, by, hw, first ? rc : 1, last ? rc : 1]);
        box(ax, ay, hw); box(bx, by, hw);
      }
      if (join === 'miter') {
        for (let i = closed ? 0 : 1; i < (closed ? n : n - 1); i++) {
          const p = (i - 1 + n) % n, q = (i + 1) % n, vx = P[2 * i], vy = P[2 * i + 1];
          let d1x = vx - P[2 * p], d1y = vy - P[2 * p + 1], d2x = P[2 * q] - vx, d2y = P[2 * q + 1] - vy;
          const l1 = Math.hypot(d1x, d1y), l2 = Math.hypot(d2x, d2y);
          if (!l1 || !l2) continue;
          d1x /= l1; d1y /= l1; d2x /= l2; d2y /= l2;
          const cr = d1x * d2y - d1y * d2x;
          if (Math.abs(cr) < 1e-6) continue;
          const s = cr > 0 ? -1 : 1, n1x = -d1y * s, n1y = d1x * s, n2x = -d2y * s, n2y = d2x * s, dn = 1 + n1x * n2x + n1y * n2y;
          if (dn < 1e-6) continue;
          const mx = (n1x + n2x) / dn, my = (n1y + n2y) / dn;
          if (Math.hypot(mx, my) > miter) continue;
          out.push([vx, vy, vx + n1x * hw, vy + n1y * hw, vx + mx * hw, vy + my * hw, vx + n2x * hw, vy + n2y * hw]);
          box(vx + mx * hw, vy + my * hw, 1);
        }
      }
    }
    return x0 <= x1 ? [x0, y0, x1, y1] : null;
  }
  // (a dashed stroke's dashes, as open subpaths)
  function dashed(subs, dash, off) {
    const out = [], total = dash.reduce((a, b) => a + b, 0);
    if (!(total > 0)) return subs;
    for (const s of subs) {
      const p = s.closed ? [...s.p, s.p[0], s.p[1]] : s.p;
      let k = 0, left = 0, on = true, ph = ((off % total) + total) % total;
      while (ph >= dash[k]) { ph -= dash[k]; k = (k + 1) % dash.length; on = !on; }
      left = dash[k] - ph;
      let cur = on ? [p[0], p[1]] : null;
      for (let i = 2; i < p.length; i += 2) {
        let ax = p[i - 2], ay = p[i - 1];
        const bx = p[i], by = p[i + 1];
        let L = Math.hypot(bx - ax, by - ay);
        while (L > 0) {
          const step = Math.min(L, left), f = step / L, nx = ax + (bx - ax) * f, ny = ay + (by - ay) * f;
          if (on) cur.push(nx, ny);
          ax = nx; ay = ny; L -= step; left -= step;
          if (left <= 1e-9) {
            if (on && cur.length >= 4) out.push({ p: cur, closed: false });
            on = !on; k = (k + 1) % dash.length; left = dash[k];
            cur = on ? [ax, ay] : null;
          }
        }
      }
      if (on && cur && cur.length >= 4) out.push({ p: cur, closed: false });
    }
    return out;
  }

  // ---------- GL ----------
  let gl = null, prog = null, loc = null, vao = null, cornerBuf = null, instBuf = null, instCap = 0, paintTex = null, paintRows = 0, covT = null, dstT = null, unpremul = null, EMPTY = null;
  const VS = `#version 300 es
precision highp float;
layout(location = 0) in vec2 aC;
layout(location = 1) in vec4 iA; layout(location = 2) in vec4 iB; layout(location = 3) in vec4 iC; layout(location = 4) in vec4 iD;
layout(location = 5) in vec4 iE; layout(location = 6) in vec4 iF; layout(location = 7) in vec4 iG; layout(location = 8) in vec4 iH;
uniform vec2 uSize;
flat out vec4 vB, vC, vD, vE, vF, vG, vH;
void main() {
  vec2 p = iA.xy + iA.zw * aC.x + iB.xy * aC.y;
  vB = iB; vC = iC; vD = iD; vE = iE; vF = iF; vG = iG; vH = iH;
  gl_Position = vec4(p.x / uSize.x * 2. - 1., 1. - p.y / uSize.y * 2., 0., 1.);
}`;
  // Kinds: 0 a sprite, 1 a coverage sprite (painted), 2 a parallelogram, 3 a disc, 4 a stroke's segment, 5 a convex quadrilateral
  // (a miter wedge, or a fill), 6 a stroke's coverage (painted), 7 an image, 8 a ring, 11 a convex polygon of up to 32 corners (in a
  // row of the paint table). Paint: a premultiplied colour, or (−1 − row) of the paint table. A sprite is read from atlas page 0-5,
  // or from its own texture (6), and a clip's coverage likewise (or 7).
  const FS = `#version 300 es
precision highp float; precision highp int;
uniform highp sampler2D uP0, uP1, uP2, uP3, uP4, uP5, uSpr, uMsk, uImg, uCov, uDst, uPaint;
uniform vec2 uSize; uniform int uMode, uBlend;
flat in vec4 vB, vC, vD, vE, vF, vG, vH;
out vec4 oC;
const float TAU = 6.2831853;
vec4 page(int i, ivec2 t) {
  if (i == 0) return texelFetch(uP0, t, 0); if (i == 1) return texelFetch(uP1, t, 0); if (i == 2) return texelFetch(uP2, t, 0);
  if (i == 3) return texelFetch(uP3, t, 0); if (i == 4) return texelFetch(uP4, t, 0); if (i == 5) return texelFetch(uP5, t, 0);
  if (i == 6) return texelFetch(uSpr, t, 0);
  return texelFetch(uMsk, t, 0);
}
// (a pixel's overlap with the band [a, b], across it: c is the pixel's centre)
float ov(float c, float a, float b) { return clamp(min(b, c + .5) - max(a, c - .5), 0., 1.); }
float paraCov(vec2 p, vec2 o, vec2 u, vec2 v) {
  vec2 nu = vec2(-u.y, u.x), nv = vec2(-v.y, v.x);
  float lu = length(nu), lv = length(nv);
  if (lu < 1e-9 || lv < 1e-9) return 0.;
  nu /= lu; nv /= lv;
  float e1 = dot(u, nv), e2 = dot(v, nu);
  return ov(dot(p - o, nv), min(0., e1), max(0., e1)) * ov(dot(p - o, nu), min(0., e2), max(0., e2));
}
float segCov(vec2 p, vec2 a, vec2 b, float hw, float ra, float rb) {
  vec2 ab = b - a; float L = length(ab);
  vec2 dir = L > 1e-9 ? ab / L : vec2(1, 0), nrm = vec2(-dir.y, dir.x);
  float u = dot(p - a, dir), v = dot(p - a, nrm);
  if (ra > .5 && u < 0.) return ov(length(vec2(u, v)), -hw, hw);
  if (rb > .5 && u > L) return ov(length(vec2(u - L, v)), -hw, hw);
  float c = ov(v, -hw, hw);
  if (ra < .5) c *= ov(u, 0., 1e9);
  if (rb < .5) c *= ov(u, -1e9, L);
  return c;
}
float edgeD(vec2 p, vec2 a, vec2 b, float s) { vec2 e = b - a; float l = length(e); if (l < 1e-9) return -1e9; return dot(p - a, s * vec2(e.y, -e.x) / l); }
float polyNCov(vec2 p, int row, int n, float s) {
  float d = -1e9;
  vec2 a = texelFetch(uPaint, ivec2(0, row), 0).xy, v0 = a;
  for (int i = 1; i <= 32; i++) {
    if (i > n) break;
    vec4 t = texelFetch(uPaint, ivec2(i >> 1, row), 0);
    vec2 b = i == n ? v0 : (i & 1) == 0 ? t.xy : t.zw;
    d = max(d, edgeD(p, a, b, s));
    a = b;
  }
  return clamp(.5 - d, 0., 1.);
}
float polyCov(vec2 p, vec2 q0, vec2 q1, vec2 q2, vec2 q3) {
  float ar = (q0.x * q1.y - q1.x * q0.y) + (q1.x * q2.y - q2.x * q1.y) + (q2.x * q3.y - q3.x * q2.y) + (q3.x * q0.y - q0.x * q3.y);
  float s = ar > 0. ? 1. : -1.;
  float d = max(max(edgeD(p, q0, q1, s), edgeD(p, q1, q2, s)), max(edgeD(p, q2, q3, s), edgeD(p, q3, q0, s)));
  return clamp(.5 - d, 0., 1.);
}
vec4 pre(vec4 c) { return vec4(c.rgb * c.a, c.a); }
vec4 paintAt(vec2 p) {
  if (vE.x > -.5) return vE;
  int row = int(-vE.x - .5);
  vec4 h = texelFetch(uPaint, ivec2(0, row), 0), m = texelFetch(uPaint, ivec2(1, row), 0), m2 = texelFetch(uPaint, ivec2(2, row), 0);
  vec2 u = vec2(m.x * p.x + m.z * p.y + m2.x, m.y * p.x + m.w * p.y + m2.y);
  vec4 g0 = texelFetch(uPaint, ivec2(3, row), 0), g1 = texelFetch(uPaint, ivec2(4, row), 0);
  int type = int(h.x + .5);
  float t = 0.;
  if (type == 1) { vec2 d = g0.zw - g0.xy; float dd = dot(d, d); if (dd == 0.) return vec4(0); t = dot(u - g0.xy, d) / dd; }
  else if (type == 2) {
    vec2 c0 = g0.xy, c1 = vec2(g0.w, g1.x); float r0 = g0.z, r1 = g1.y;
    vec2 cd = c1 - c0, pd = u - c0; float dr = r1 - r0;
    float a = dot(cd, cd) - dr * dr, b = dot(pd, cd) + r0 * dr, c = dot(pd, pd) - r0 * r0;
    if (abs(a) < 1e-9) { if (abs(b) < 1e-9) return vec4(0); t = c / (2. * b); if (r0 + t * dr < 0.) return vec4(0); }
    else {
      float disc = b * b - a * c; if (disc < 0.) return vec4(0);
      float s = sqrt(disc), w1 = (b + s) / a, w2 = (b - s) / a;
      if (r0 + max(w1, w2) * dr >= 0.) t = max(w1, w2); else if (r0 + min(w1, w2) * dr >= 0.) t = min(w1, w2); else return vec4(0);
    }
  }
  else if (type == 3) { t = fract((atan(u.y - g0.z, u.x - g0.y) - g0.x) / TAU); }
  else if (type == 4) {
    vec2 q = vec2(g0.x * u.x + g0.z * u.y + g1.x, g0.y * u.x + g0.w * u.y + g1.y) / g1.zw;
    int rep = int(h.y + .5);
    if (((rep & 1) == 0 && (q.x < 0. || q.x > 1.)) || ((rep & 2) == 0 && (q.y < 0. || q.y > 1.))) return vec4(0);
    return texture(uImg, q);
  }
  int n = int(h.y + .5);
  vec4 o0 = texelFetch(uPaint, ivec2(5, row), 0), o1 = texelFetch(uPaint, ivec2(6, row), 0);
  float offs[8] = float[8](o0.x, o0.y, o0.z, o0.w, o1.x, o1.y, o1.z, o1.w);
  vec4 c = texelFetch(uPaint, ivec2(7, row), 0);
  if (t <= offs[0]) return pre(c);
  for (int i = 1; i < 8; i++) {
    if (i >= n) break;
    vec4 c2 = texelFetch(uPaint, ivec2(7 + i, row), 0);
    if (t < offs[i]) return pre(mix(c, c2, (t - offs[i - 1]) / max(offs[i] - offs[i - 1], 1e-9)));
    c = c2;
  }
  return pre(c);
}
float hardL(float s, float d) { return s <= .5 ? d * 2. * s : d + (2. * s - 1.) - d * (2. * s - 1.); }
float softL(float s, float d) { float D = d <= .25 ? ((16. * d - 12.) * d + 4.) * d : sqrt(d); return s <= .5 ? d - (1. - 2. * s) * d * (1. - d) : d + (2. * s - 1.) * (D - d); }
float sep(float s, float d) {
  if (uBlend == 1) return s * d; if (uBlend == 2) return s + d - s * d; if (uBlend == 3) return hardL(d, s);
  if (uBlend == 4) return min(s, d); if (uBlend == 5) return max(s, d);
  if (uBlend == 6) return d == 0. ? 0. : s >= 1. ? 1. : min(1., d / (1. - s));
  if (uBlend == 7) return d >= 1. ? 1. : s <= 0. ? 0. : 1. - min(1., (1. - d) / s);
  if (uBlend == 8) return hardL(s, d); if (uBlend == 9) return softL(s, d);
  if (uBlend == 10) return abs(s - d); return s + d - 2. * s * d;
}
float lum(vec3 c) { return dot(c, vec3(.3, .59, .11)); }
vec3 setLum(vec3 c, float l) {
  c += l - lum(c); l = lum(c);
  float n = min(c.r, min(c.g, c.b)), x = max(c.r, max(c.g, c.b));
  if (n < 0.) c = l + (c - l) * l / (l - n);
  if (x > 1.) c = l + (c - l) * (1. - l) / (x - l);
  return c;
}
float sat(vec3 c) { return max(c.r, max(c.g, c.b)) - min(c.r, min(c.g, c.b)); }
vec3 setSat(vec3 c, float s) { float n = min(c.r, min(c.g, c.b)), x = max(c.r, max(c.g, c.b)); return x > n ? (c - n) * s / (x - n) : vec3(0); }
vec3 blend(vec3 s, vec3 d) {
  if (uBlend == 12) return setLum(setSat(s, sat(d)), lum(d)); if (uBlend == 13) return setLum(setSat(d, sat(s)), lum(d));
  if (uBlend == 14) return setLum(s, lum(d)); if (uBlend == 15) return setLum(d, lum(s));
  return vec3(sep(s.r, d.r), sep(s.g, d.g), sep(s.b, d.b));
}
void main() {
  vec2 p = vec2(gl_FragCoord.x, uSize.y - gl_FragCoord.y);
  int kind = int(vB.z + .5);
  float cov = 1.; vec4 src = vec4(0); bool painted = true;
  if (kind <= 1) {
    ivec2 t = ivec2(floor(p - vC.xy));
    if (t.x < 0 || t.y < 0 || t.x >= int(vC.z) || t.y >= int(vC.w)) { cov = 0.; painted = false; }
    else { vec4 s = page(int(vB.w + .5), t + ivec2(vD.xy)); if (kind == 0) { src = s; painted = false; } else cov = s.a / vD.z; }
  }
  else if (kind == 2) cov = paraCov(p, vC.xy, vC.zw, vD.xy);
  else if (kind == 3) cov = ov(length(p - vC.xy), -vC.z, vC.z);
  else if (kind == 4) cov = segCov(p, vC.xy, vC.zw, vD.x, vD.y, vD.z);
  else if (kind == 5) cov = polyCov(p, vC.xy, vC.zw, vD.xy, vD.zw);
  else if (kind == 6) cov = p.x < vC.x || p.y < vC.y || p.x > vC.z || p.y > vC.w ? 0. : texelFetch(uCov, ivec2(gl_FragCoord.xy), 0).r;
  else if (kind == 7) {
    mat2 A = mat2(vC.zw, vD.xy); float det = determinant(A);
    if (abs(det) < 1e-12) cov = 0.;
    else { vec2 l = inverse(A) * (p - vC.xy); cov = paraCov(p, vC.xy, vC.zw, vD.xy); src = texture(uImg, mix(vE.xy, vE.zw, l)); }
    painted = false;
  }
  else if (kind == 8) cov = ov(length(p - vC.xy) - vC.z, -vC.w, vC.w);
  else if (kind == 11) cov = polyNCov(p, int(vD.x + .5), int(vD.y + .5), vD.z);
  if (uMode == 1) { oC = vec4(cov); return; }
  if (painted) src = paintAt(p);
  float k = cov * vG.w * ov(p.x, vF.x, vF.z) * ov(p.y, vF.y, vF.w);
  if (vH.z > 0.) { ivec2 t = ivec2(floor(p - vH.xy)); k *= t.x < 0 || t.y < 0 || t.x >= int(vH.z) || t.y >= int(vH.w) ? 0. : page(int(vG.z + .5), t + ivec2(vG.xy)).a; }
  vec4 s = src * k;
  if (uMode == 2) {
    vec4 d = texelFetch(uDst, ivec2(gl_FragCoord.xy), 0);
    vec3 cs = s.a > 0. ? s.rgb / s.a : vec3(0), cd = d.a > 0. ? d.rgb / d.a : vec3(0);
    oC = vec4(s.rgb * (1. - d.a) + d.rgb * (1. - s.a) + s.a * d.a * blend(cs, cd), s.a + d.a * (1. - s.a));
    return;
  }
  oC = s;
}`;
  const UNPREMUL = `#version 300 es
precision highp float;
uniform sampler2D uSrc;
out vec4 oC;
void main() { vec4 c = texelFetch(uSrc, ivec2(gl_FragCoord.xy), 0); oC = c.a > 0. ? vec4(c.rgb / c.a, c.a) : vec4(0); }`;
  function init() {
    if (prog) return;
    gl = GL.init();
    const sh = (t, s) => { const x = gl.createShader(t); gl.shaderSource(x, s); gl.compileShader(x); if (!gl.getShaderParameter(x, gl.COMPILE_STATUS)) throw new Error('draw2d shader: ' + gl.getShaderInfoLog(x)); return x; };
    prog = gl.createProgram(); gl.attachShader(prog, sh(gl.VERTEX_SHADER, VS)); gl.attachShader(prog, sh(gl.FRAGMENT_SHADER, FS)); gl.linkProgram(prog);
    if (!gl.getProgramParameter(prog, gl.LINK_STATUS)) throw new Error('draw2d link: ' + gl.getProgramInfoLog(prog));
    loc = {};
    const UNITS = { uP0: 0, uP1: 1, uP2: 2, uP3: 3, uP4: 4, uP5: 5, uSpr: U_SPR, uMsk: U_MSK, uImg: U_IMG, uCov: U_COV, uDst: U_DST, uPaint: U_PAINT };
    for (const n of ['uSize', 'uMode', 'uBlend', ...Object.keys(UNITS)]) loc[n] = gl.getUniformLocation(prog, n);
    gl.useProgram(prog);
    for (const [n, u] of Object.entries(UNITS)) gl.uniform1i(loc[n], u);
    const prev = gl.getParameter(gl.VERTEX_ARRAY_BINDING);
    vao = gl.createVertexArray(); gl.bindVertexArray(vao);
    cornerBuf = gl.createBuffer(); gl.bindBuffer(gl.ARRAY_BUFFER, cornerBuf);
    gl.bufferData(gl.ARRAY_BUFFER, new Float32Array([0, 0, 1, 0, 0, 1, 1, 1]), gl.STATIC_DRAW);
    gl.enableVertexAttribArray(0); gl.vertexAttribPointer(0, 2, gl.FLOAT, false, 0, 0);
    instBuf = gl.createBuffer(); gl.bindBuffer(gl.ARRAY_BUFFER, instBuf);
    for (let i = 1; i <= 8; i++) { gl.enableVertexAttribArray(i); gl.vertexAttribDivisor(i, 1); }
    gl.bindVertexArray(prev);
    gl.activeTexture(gl.TEXTURE0 + U_SCRATCH); paintTex = gl.createTexture(); gl.bindTexture(gl.TEXTURE_2D, paintTex); setNearest();
    // (a transparent pixel: a panel not drawn this frame, and any unit the program samples that has nothing of its own)
    EMPTY = { tex: gl.createTexture(), w: 1, h: 1 };
    gl.bindTexture(gl.TEXTURE_2D, EMPTY.tex); gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA8, 1, 1, 0, gl.RGBA, gl.UNSIGNED_BYTE, new Uint8Array(4)); setNearest();
    unpremul = GL.program('d2unpremul', UNPREMUL);
  }
  function setNearest(wrap = gl.CLAMP_TO_EDGE) {
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.NEAREST); gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.NEAREST);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, wrap); gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, wrap);
  }
  // (an RGBA8 texture uploaded from a canvas or image data: premultiplied, top row first; counted in GL.stats)
  function upload(tex, src, x, y, w, h, alloc) {
    gl.activeTexture(gl.TEXTURE0 + U_SCRATCH); gl.bindTexture(gl.TEXTURE_2D, tex);
    gl.pixelStorei(gl.UNPACK_FLIP_Y_WEBGL, false); gl.pixelStorei(gl.UNPACK_PREMULTIPLY_ALPHA_WEBGL, true);
    if (alloc) gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA8, alloc[0], alloc[1], 0, gl.RGBA, gl.UNSIGNED_BYTE, null);
    if (src) {
      if (w === src.width && h === src.height) gl.texSubImage2D(gl.TEXTURE_2D, 0, x, y, gl.RGBA, gl.UNSIGNED_BYTE, src);
      else gl.texSubImage2D(gl.TEXTURE_2D, 0, x, y, w, h, gl.RGBA, gl.UNSIGNED_BYTE, src);
      GL.stats.uploads++; GL.stats.uploadBytes += w * h * 4;
    }
    gl.pixelStorei(gl.UNPACK_FLIP_Y_WEBGL, true); gl.pixelStorei(gl.UNPACK_PREMULTIPLY_ALPHA_WEBGL, false);
  }
  // (the 2D canvases sprites are drawn on: on the CPU (willReadFrequently), so that a sprite's pixels come from the same rasterizer
  // however big the canvas is (a browser may draw a big canvas on the GPU, a small one on the CPU, with different antialiasing))
  const spriteCanvas = (w, h) => { const c = makeCanvas(w, h); return [c, c.getContext('2d', { willReadFrequently: true })]; };
  // (a sprite is drawn at the top left of a canvas its own size, and copied from there to where it goes, so that its pixels don't
  // depend on where it goes: a rasterizer's rounding can depend on where on its canvas a shape is drawn)
  let scratch = null, scratchG = null;
  function drawSprite(r) {
    if (!scratch) [scratch, scratchG] = spriteCanvas(r.w, r.h);
    scratch.width = r.w; scratch.height = r.h;
    if (recent.length < 200) recent.push(`${r.w}x${r.h} ${r.key}`);
    try { r.raster(scratchG, 0, 0); } catch (e) { warn(`a sprite couldn't be drawn (${e.message})`); }
    stats.rasters++;
    return scratch;
  }

  // ---------- the atlas ----------
  // Sprites, each named by its key: in pages of 2048², filled with shelves of the blocks that flushes upload (a block holds a
  // flush's new sprites), or, over 1024 wide or tall, in textures of their own. A sprite's pixels are never changed once drawn. A
  // flush first looks up every sprite it draws; its new ones then go where there's room, or into a page emptied for them, the least
  // lately used of those none of its sprites are on; or, if every page has one of its sprites, into textures of their own, for that
  // draw only.
  const pages = [], ATLAS = new Map();   // (key → {page, x, y, w, h, o, a0} or, in a texture of its own, {tex, …})
  let tick = 0, bigBytes = 0;
  const stats = { own: 0, rasters: 0, evictions: 0 }, recent = [];   // (and the keys of the sprites made lately, for looking into what a frame uploads)
  function newPage() {
    const t = gl.createTexture(); upload(t, null, 0, 0, 0, 0, [PAGE, PAGE]); gl.bindTexture(gl.TEXTURE_2D, t); setNearest();
    const P = { tex: t, shelves: [], top: 0, keys: new Set(), last: 0 }; pages.push(P); return P;
  }
  function placeIn(P, w, h) {
    for (const s of P.shelves) if (s.h >= h && s.h <= h * 1.5 + 8 && s.x + w <= PAGE) { const x = s.x; s.x += w; return [x, s.y]; }
    if (P.top + h > PAGE) return null;
    const s = { y: P.top, h, x: w }; P.shelves.push(s); P.top += h;
    return [0, s.y];
  }
  // (room for a block of w × h: [page, x, y], or null if every page that has no room has a sprite in `need`)
  function allocBlock(w, h, need) {
    for (let i = 0; i < pages.length; i++) { const at = placeIn(pages[i], w, h); if (at) return [i, ...at]; }
    if (pages.length < PAGES) { const at = placeIn(newPage(), w, h); return [pages.length - 1, ...at]; }
    let v = -1;
    for (let i = 0; i < pages.length; i++) if (!need.has(i) && (v < 0 || pages[i].last < pages[v].last)) v = i;
    if (v < 0) return null;
    const P = pages[v];
    for (const k of P.keys) ATLAS.delete(k);
    P.keys.clear(); P.shelves = []; P.top = 0; stats.evictions++;
    return [v, ...placeIn(P, w, h)];
  }
  // (a sprite drawn into a texture of its own)
  function ownTexture(r) {
    const c = drawSprite(r), tex = gl.createTexture();
    upload(tex, c, 0, 0, r.w, r.h, [r.w, r.h]); gl.bindTexture(gl.TEXTURE_2D, tex); setNearest();
    return { key: r.key, tex, x: 0, y: 0, w: r.w, h: r.h, o: r.o, a0: r.a0, last: tick };
  }
  // settle(reqs): every sprite a draw needs (key → request {key, w, h, o, a0, raster(g, x, y)}), found or made: key → its place;
  // and the textures made for this draw alone, to delete once it's drawn
  function settle(reqs) {
    tick++;
    const got = new Map(), make = [], need = new Set(), temps = [];
    for (const [k, r] of reqs) {
      const a = ATLAS.get(k);
      if (a) { got.set(k, a); if (a.tex) a.last = tick; else need.add(a.page); }
      else make.push(r);
    }
    const small = [];
    for (const r of make) {
      if (r.w <= BIG && r.h <= BIG) { small.push(r); continue; }
      const a = ownTexture(r);
      ATLAS.set(r.key, a); got.set(r.key, a); bigBytes += r.w * r.h * 4;
    }
    small.sort((a, b) => b.h - a.h);
    let i = 0;
    while (i < small.length) {
      // (shelves across a block up to 1024 wide, as tall as it takes, up to a page)
      const W = 1024;
      let y = 0, x = 0, sh = 0, j = i, wmax = 0;
      const at = [];
      for (; j < small.length; j++) {
        const s = small[j];
        if (x + s.w > W) { y += sh; x = 0; sh = 0; }
        if (y + s.h > PAGE) break;
        at.push([x, y]); x += s.w; sh = Math.max(sh, s.h); wmax = Math.max(wmax, x);
      }
      const H = y + sh, blk = allocBlock(wmax, H, need);
      if (!blk) {
        warn('the atlas has no room this frame; sprites are drawn from textures of their own');
        for (let k = i; k < j; k++) { const a = ownTexture(small[k]); got.set(small[k].key, a); temps.push(a.tex); stats.own++; }
      } else {
        const [c, g] = stageCanvas(wmax, H), P = pages[blk[0]];
        for (let k = i; k < j; k++) g.drawImage(drawSprite(small[k]), at[k - i][0], at[k - i][1]);
        upload(P.tex, c, blk[1], blk[2], wmax, H);
        need.add(blk[0]);
        for (let k = i; k < j; k++) {
          const s = small[k], a = { key: s.key, page: blk[0], x: blk[1] + at[k - i][0], y: blk[2] + at[k - i][1], w: s.w, h: s.h, o: s.o, a0: s.a0 };
          ATLAS.set(s.key, a); P.keys.add(s.key); got.set(s.key, a);
        }
      }
      i = j;
    }
    for (const p of need) pages[p].last = tick;
    // (textures of their own that this draw doesn't need: the least lately used go, beyond a budget)
    if (bigBytes > BIG_BYTES) {
      const old = [...ATLAS.values()].filter(a => a.tex && !reqs.has(a.key)).sort((a, b) => a.last - b.last);
      for (const a of old) { if (bigBytes <= BIG_BYTES) break; gl.deleteTexture(a.tex); ATLAS.delete(a.key); bigBytes -= a.w * a.h * 4; }
    }
    return { got, temps };
  }
  let stage = null, stageG = null;
  function stageCanvas(w, h) {
    if (!stage) [stage, stageG] = spriteCanvas(w, h);
    if (stage.width !== w || stage.height !== h) { stage.width = w; stage.height = h; }
    else { stageG.setTransform(1, 0, 0, 1, 0, 0); stageG.clearRect(0, 0, w, h); }
    return [stage, stageG];
  }

  // ---------- images drawn with drawImage() or as patterns ----------
  // A canvas is uploaded when it's new or has been drawn on since (its version). One drawn again in the same frame after it's
  // changed is uploaded into a texture for that frame, so that what was drawn with it earlier in the frame keeps its pixels.
  const IMGS = new WeakMap(), LAYERS = new WeakMap(), frameTemps = [];
  let frameNo = 1;
  function imageTex(img) {
    // (a layer's target is looked up when the frame is drawn, once that layer has drawn its own)
    const Ly = LAYERS.get(img);
    if (Ly && !Ly.direct) return { layer: Ly, tex: null, w: Ly.w, h: Ly.h, flip: true, id: Ly.id, v: 0 };
    let r = IMGS.get(img);
    const w = img.width | 0, h = img.height | 0;
    if (!w || !h) return null;
    const v = img.__v | 0;
    if (!r) { r = { tex: gl.createTexture(), w: 0, h: 0, v: -1, id: nextId++, fr: 0 }; IMGS.set(img, r); }
    if (r.w !== w || r.h !== h || r.v !== v) {
      if (r.fr === frameNo && r.w) {
        const tex = gl.createTexture(); upload(tex, img, 0, 0, w, h, [w, h]); frameTemps.push(tex);
        return { tex, w, h, flip: false, id: nextId++, v };
      }
      upload(r.tex, img, 0, 0, w, h, r.w !== w || r.h !== h ? [w, h] : null);
      r.w = w; r.h = h; r.v = v;
    }
    r.fr = frameNo;
    return { tex: r.tex, w, h, flip: false, id: r.id, v };
  }

  // ---------- a layer ----------
  // A frame's drawing on the layers is a recording: it starts when the UI's begins (opt.frame), and a layer not drawn on since is
  // empty that frame.
  let nextLayer = 1, recording = 0;
  function layer(name, w, h, opt = {}) {
    // (in render mode the layer's 2D canvas is drawn on and uploaded; otherwise it only measures text, so it's a pixel)
    const c = makeCanvas(RENDER_MODE ? w : 1, RENDER_MODE ? h : 1), g = c.getContext('2d');
    const L = { name, c, g, w, h, id: nextLayer++, direct: RENDER_MODE, panel: !!opt.panel, rec: -1, flushed: -1, version: 0 };
    LAYERS.set(c, L);
    // ---- the state, as the context has it (kept here too, so that recording reads no properties back) ----
    const fresh = () => ({ ...DEFAULTS, M: ID, clips: [], dash: [] });
    let S = fresh(), stack = [], path = [], items = [], inst = new Float32Array(FLOATS * 256), n = 0, pinst = new Float32Array(FLOATS * 256), pn = 0, paints = [], reqs = new Map(), last = null, tgt = null, straight = null;
    const fns = new Map();
    // (the default state, as a new canvas has it; and the context's too, which measures text)
    function resetState() {
      S = fresh(); stack = []; path = [];
      if (g.reset) g.reset(); else { g.setTransform(1, 0, 0, 1, 0, 0); for (const k of PROPS) g[k] = DEFAULTS[k]; }
    }
    // ---- instances ----
    function slot() { if ((n + 1) * FLOATS > inst.length) { const b = new Float32Array(inst.length * 2); b.set(inst); inst = b; } return (n++) * FLOATS; }
    function pslot() { if ((pn + 1) * FLOATS > pinst.length) { const b = new Float32Array(pinst.length * 2); b.set(pinst); pinst = b; } return (pn++) * FLOATS; }
    // ---- sprites ----
    // place(spec, A, steps): a sprite (spec: {key, box, a0, draw(g, X, Y)}: its bounds about its anchor, in the canvas's pixels, and
    // its drawing with the anchor at (X, Y)) with its anchor at A, snapped to 1/steps of a pixel: {key, I: [x, y]} (the whole pixel
    // the anchor snaps into; the key has where within it). The sprite is requested for the flush.
    function place(spec, A, steps) {
      let Ix = Math.floor(A[0]), Iy = Math.floor(A[1]), qx = Math.round((A[0] - Ix) * steps) / steps, qy = Math.round((A[1] - Iy) * steps) / steps;
      if (qx >= 1) { qx -= 1; Ix++; } if (qy >= 1) { qy -= 1; Iy++; }
      const key = spec.key + '@' + qx + ',' + qy;
      if (!reqs.has(key)) {
        const b = spec.box, ox = Math.floor(b[0] + qx), oy = Math.floor(b[1] + qy);
        const w = Math.max(1, Math.ceil(b[2] + qx) - ox), h = Math.max(1, Math.ceil(b[3] + qy) - oy);
        reqs.set(key, { key, w, h, o: [ox, oy], a0: spec.a0, h1: strHash(key), raster: (gg, x, y) => spec.draw(gg, x - ox + qx, y - oy + qy) });
      }
      return { key, I: [Ix, Iy], r: reqs.get(key) };
    }
    // (the clip, as a rectangle in the canvas's pixels and a coverage sprite for the rest; cached with the clip list)
    const CLIPS = new WeakMap(), NOCLIP = { rect: [-1e9, -1e9, 1e9, 1e9], empty: false, mask: null };
    function clipOf(clips) {
      if (!clips.length) return NOCLIP;
      let C = CLIPS.get(clips);
      if (C && C.reqs === reqs) return C;
      let r = [-1e9, -1e9, 1e9, 1e9];
      const rest = [];
      for (const e of clips) {
        const o = e.ops;
        // (a rectangle, in a transform without rotation, is exact as a rectangle)
        if (o.length === 1 && o[0].op === 'rect' && Math.abs(o[0].M[1]) < 1e-9 && Math.abs(o[0].M[2]) < 1e-9) {
          const M = o[0].M, a = o[0].a, xs = [M[0] * a[0] + M[4], M[0] * (a[0] + a[2]) + M[4]], ys = [M[3] * a[1] + M[5], M[3] * (a[1] + a[3]) + M[5]];
          r = [Math.max(r[0], Math.min(...xs)), Math.max(r[1], Math.min(...ys)), Math.min(r[2], Math.max(...xs)), Math.min(r[3], Math.max(...ys))];
        } else rest.push(e);
      }
      C = { rect: r, empty: r[0] >= r[2] || r[1] >= r[3], mask: null, reqs };
      if (rest.length && !C.empty) {
        // (the other clips' intersection, drawn as coverage over its bounds, within the rectangle's and the layer's)
        const sp = opsSpec(rest.map(e => e.ops));
        let b = [r[0], r[1], r[2], r[3]];
        for (const e of rest) { const pb = pathBounds(e.ops); if (!pb) { C.empty = true; break; } b = [Math.max(b[0], pb[0] - 2), Math.max(b[1], pb[1] - 2), Math.min(b[2], pb[2] + 2), Math.min(b[3], pb[3] + 2)]; }
        if (!sp) C.empty = true;
        if (!C.empty) {
          // (its bounds about the anchor, in whole pixels: part of its key, as the bounds can cut the coverage)
          const A = sp.A, rel = [Math.floor(Math.max(b[0], 0) - A[0]), Math.floor(Math.max(b[1], 0) - A[1]), Math.ceil(Math.min(b[2], L.w) - A[0]), Math.ceil(Math.min(b[3], L.h) - A[1])];
          if (rel[0] >= rel[2] || rel[1] >= rel[3]) C.empty = true;
          else {
            const rules = rest.map(e => e.rule).join(','), T = sp.T;
            C.mask = place({ key: `C|${rules}|${rel}|${sp.key}`, box: rel, a0: 1, draw: (gg, X, Y) => {
              T.forEach((ops, i) => { replay(gg, ops, X, Y); gg.clip(rest[i].rule); });
              gg.setTransform(1, 0, 0, 1, 0, 0); gg.fillStyle = '#fff'; gg.fillRect(X + rel[0] - 1, Y + rel[1] - 1, rel[2] - rel[0] + 2, rel[3] - rel[1] + 2);
            } }, A, 4);
          }
        }
      }
      CLIPS.set(clips, C);
      return C;
    }
    // ---- items ----
    // (the paint of a style: a premultiplied colour, or a paint table row; null for nothing)
    function paintOf(style, M) {
      if (typeof style === 'string') { const c = color(style); return c ? [c[0] * c[3], c[1] * c[3], c[2] * c[3], c[3]] : null; }
      const D = DESC.get(style);
      if (!D) return null;
      // (a gradient used again in this recording in the same transform, with no stop added since, is the same row)
      if (D.pr && D.pr.paints === paints && D.pr.M === M && D.pr.ns === (D.stops?.length ?? 0)) return D.pr.p;
      const pr = paintRow(D, M);
      D.pr = { paints, M, ns: D.stops?.length ?? 0, p: pr };
      return pr;
    }
    function paintRow(D, M) {
      const Mi = minv(M);
      if (!Mi) return null;
      const row = new Float32Array(64);
      row[0] = D.kind; row[4] = Mi[0]; row[5] = Mi[1]; row[6] = Mi[2]; row[7] = Mi[3]; row[8] = Mi[4]; row[9] = Mi[5];
      if (D.kind === 4) {
        const t = imageTex(D.img);
        if (!t) return null;
        const P = minv(D.m) ?? ID;
        row[1] = { repeat: 3, 'repeat-x': 1, 'repeat-y': 2, 'no-repeat': 0 }[D.rep] ?? 3;
        row.set([P[0], P[1], P[2], P[3], P[4], P[5], t.w, t.h], 12);
        paints.push(row);
        return { row: paints.length - 1, img: t, rep: row[1] };
      }
      const st = D.stops.filter(s => s[1]).map((s, i) => [s[0], s[1], i]).sort((a, b) => a[0] - b[0] || a[2] - b[2]);
      if (!st.length) return null;
      row[1] = st.length;
      if (D.kind === 1) row.set(D.a.slice(0, 4), 12);
      else if (D.kind === 2) { row.set(D.a.slice(0, 4), 12); row[16] = D.a[4]; row[17] = D.a[5]; }
      else row.set([D.a[0], D.a[1], D.a[2], 0], 12);
      st.forEach((s, i) => { row[20 + i] = s[0]; row.set(s[1], 28 + i * 4); });
      paints.push(row);
      return { row: paints.length - 1 };
    }
    // (an item's common part: its quad, kind, clip and alpha; returns the item)
    function put(kind, quad, clip, alpha, blend, extra) {
      const o = slot(), I = inst;
      I[o] = quad[0]; I[o + 1] = quad[1]; I[o + 2] = quad[2]; I[o + 3] = quad[3]; I[o + 4] = quad[4]; I[o + 5] = quad[5]; I[o + 6] = kind; I[o + 7] = 0;
      for (let k = 8; k < 20; k++) I[o + k] = 0;
      I[o + 20] = clip.rect[0]; I[o + 21] = clip.rect[1]; I[o + 22] = clip.rect[2]; I[o + 23] = clip.rect[3];
      I[o + 24] = 0; I[o + 25] = 0; I[o + 26] = 0; I[o + 27] = alpha;
      for (let k = 28; k < FLOATS; k++) I[o + k] = 0;
      const it = { o, kind, blend, clip, ...extra };
      if (clip.mask) it.cm = clip.mask;
      items.push(it);
      return it;
    }
    function setPaint(it, p) {
      const I = inst, o = it.o;
      if (p.row === undefined) { I[o + 16] = p[0]; I[o + 17] = p[1]; I[o + 18] = p[2]; I[o + 19] = p[3]; }
      else { I[o + 16] = -1 - p.row; if (p.img) { it.img = p.img; it.rep = p.rep; it.smooth = S.imageSmoothingEnabled; } }
    }
    // (the quad covering a box, in the canvas's pixels, clipped to the layer and the clip's rectangle; null if nothing's left)
    function boxQuad(b, clip, spill) {
      let x0 = Math.floor(b[0]), y0 = Math.floor(b[1]), x1 = Math.ceil(b[2]), y1 = Math.ceil(b[3]);
      if (spill) { x0 = -1; y0 = -1; x1 = L.w + 1; y1 = L.h + 1; }
      const r = clip.rect;
      x0 = Math.max(x0, Math.floor(r[0]), 0); y0 = Math.max(y0, Math.floor(r[1]), 0); x1 = Math.min(x1, Math.ceil(r[2]), L.w); y1 = Math.min(y1, Math.ceil(r[3]), L.h);
      if (x0 >= x1 || y0 >= y1) return null;
      return [x0, y0, x1 - x0, 0, 0, y1 - y0];
    }
    // (a gradient or pattern the shader can't paint (made elsewhere, or a gradient of more than 8 stops): the 2D canvas draws it)
    const foreign = s => s !== null && typeof s === 'object' && (!DESC.has(s) || (DESC.get(s).stops?.length ?? 0) > 8);
    const opOf = () => S.globalCompositeOperation;
    const shadowed = () => (S.shadowBlur > 0 || S.shadowOffsetX || S.shadowOffsetY) && (color(S.shadowColor)?.[3] ?? 0) > 0;
    const filtered = () => S.filter && S.filter !== 'none';
    // (a sprite reaching far past what can be seen of the layer, through the clip, is cut to that: {box, key} about the anchor A;
    // null if it needn't be)
    function cutBox(A, box, clip) {
      const r = clip.rect, vis = [Math.max(r[0], 0) - 2, Math.max(r[1], 0) - 2, Math.min(r[2], L.w) + 2, Math.min(r[3], L.h) + 2];
      const bw = box[2] - box[0], bh = box[3] - box[1];
      if (bw <= 4096 && bh <= 4096 && bw * bh <= 2 * Math.max(1, (vis[2] - vis[0]) * (vis[3] - vis[1])) + 65536) return null;
      const rel = [Math.floor(Math.max(box[0], vis[0] - A[0])), Math.floor(Math.max(box[1], vis[1] - A[1])), Math.ceil(Math.min(box[2], vis[2] - A[0])), Math.ceil(Math.min(box[3], vis[3] - A[1]))];
      return { box: rel, key: `|cut${rel}`, empty: rel[0] >= rel[2] || rel[1] >= rel[3] };
    }
    // Anything else: the drawing done by the 2D canvas into a sprite, whole (its paint, shadow and filter), anchored at pA (in user
    // space), with bounds box about the anchor (in the canvas's pixels, before the shadow). key: all that the drawing is, exactly,
    // in user space (the transform's linear part and the anchor are added); draw(g) draws it in user space.
    function whole(key, pA, box, draw, op, clip) {
      const M = S.M, rel = [M[0] * pA[0] + M[2] * pA[1], M[1] * pA[0] + M[3] * pA[1]], A = [rel[0] + M[4], rel[1] + M[5]];
      const sh = shadowed(), pad = sh ? S.shadowBlur * 1.5 + 2 : 0;
      const fp = filtered() ? Math.max(24, 3 * Math.max(0, ...[...S.filter.matchAll(/([\d.]+)px/g)].map(m => +m[1])) + 8) : 0;
      let b = [box[0] - pad - fp, box[1] - pad - fp, box[2] + pad + fp, box[3] + pad + fp];
      if (sh) { const sx = S.shadowOffsetX, sy = S.shadowOffsetY; b = [Math.min(b[0], b[0] + sx), Math.min(b[1], b[1] + sy), Math.max(b[2], b[2] + sx), Math.max(b[3], b[3] + sy)]; }
      const st = {};
      for (const k of PROPS) st[k] = k === 'fillStyle' || k === 'strokeStyle' ? snapStyle(S[k]) : S[k];
      const dash = S.dash;
      const sk = sh ? `|sh${S.shadowBlur},${S.shadowOffsetX},${S.shadowOffsetY},${S.shadowColor}` : '';
      const ct = cutBox(A, b, clip);
      if (ct?.empty) return;
      if (ct) b = ct.box;
      const k = `W|${key}|${lin(M)}|${num(pA)}|${styleKey(st.fillStyle)}/${styleKey(st.strokeStyle)}|${PROPS.filter(p => p !== 'globalAlpha' && p !== 'globalCompositeOperation' && p !== 'fillStyle' && p !== 'strokeStyle').map(p => st[p]).join('|')}|${dash}${sk}${ct ? ct.key : ''}`;
      const sp = place({ key: k, box: b, a0: 1, draw: (gg, X, Y) => {
        // (the sprite's canvas starts in the default state; only what differs from it is set, so a drawing without text sets no font)
        for (const p of PROPS) if (p !== 'globalAlpha' && p !== 'globalCompositeOperation' && st[p] !== DEFAULTS[p]) gg[p] = p === 'fillStyle' || p === 'strokeStyle' ? realize(gg, st[p]) : st[p];
        gg.setLineDash(dash);
        gg.setTransform(M[0], M[1], M[2], M[3], X - rel[0], Y - rel[1]);
        draw(gg);
      } }, A, 4);
      spriteItem(0, sp, clip, S.globalAlpha, op, null);
    }
    function spriteItem(kind, sp, clip, alpha, op, paint) {
      const r = sp.r, x = sp.I[0] + r.o[0], y = sp.I[1] + r.o[1];
      const q = OPS[op]?.[2] ? boxQuad([0, 0, L.w, L.h], clip, true) : boxQuad([x, y, x + r.w, y + r.h], clip);
      if (!q) return null;
      const it = put(kind, q, clip, alpha, op, { sp });
      inst[it.o + 8] = x; inst[it.o + 9] = y; inst[it.o + 10] = r.w; inst[it.o + 11] = r.h; inst[it.o + 14] = r.a0;
      if (paint) setPaint(it, paint);
      return it;
    }
    // (a parallelogram's quad, grown by a pixel for its antialiasing)
    function paraQuad(o, u, v) {
      const xs = [o[0], o[0] + u[0], o[0] + v[0], o[0] + u[0] + v[0]], ys = [o[1], o[1] + u[1], o[1] + v[1], o[1] + u[1] + v[1]];
      return [Math.min(...xs) - 1, Math.min(...ys) - 1, Math.max(...xs) + 1, Math.max(...ys) + 1];
    }
    // (a box in user space, [x0, y0, x1, y1], through a transform's linear part: its bounds, a pixel wider all round)
    function boxOf(M, x0, y0, x1, y1) {
      const ax = M[0] * x0, bx = M[0] * x1, cy = M[2] * y0, dy = M[2] * y1, ay = M[1] * x0, by = M[1] * x1, ey = M[3] * y0, fy = M[3] * y1;
      return [Math.min(ax, bx) + Math.min(cy, dy) - 1, Math.min(ay, by) + Math.min(ey, fy) - 1, Math.max(ax, bx) + Math.max(cy, dy) + 1, Math.max(ay, by) + Math.max(ey, fy) + 1];
    }
    // ---- the drawing calls ----
    function rectItem(x, y, w, h, clear) {
      if (!(isFinite(x) && isFinite(y) && isFinite(w) && isFinite(h)) || !w || !h) return;
      const clip = clipOf(S.clips);
      if (clip.empty) return;
      const M = S.M, o = [M[0] * x + M[2] * y + M[4], M[1] * x + M[3] * y + M[5]], u = [M[0] * w, M[1] * w], v = [M[2] * h, M[3] * h];
      if (clear) {
        const q = boxQuad(paraQuad(o, u, v), clip);
        if (!q) return;
        const it = put(2, q, clip, 1, 'destination-out', {});
        inst.set([o[0], o[1], u[0], u[1], v[0], v[1], 0, 0, 0, 0, 0, 1], it.o + 8);
        return;
      }
      const op = opOf();
      if (shadowed() || filtered() || foreign(S.fillStyle)) {
        whole(`R|${num([x, y, w, h])}`, [x, y], paraQuad([0, 0], u, v), gg => gg.fillRect(x, y, w, h), op, clip);
        return;
      }
      const p = paintOf(S.fillStyle, M);
      if (!p) return;
      const q = boxQuad(paraQuad(o, u, v), clip, OPS[op]?.[2]);
      if (!q) return;
      const it = put(2, q, clip, S.globalAlpha, op, {});
      inst[it.o + 8] = o[0]; inst[it.o + 9] = o[1]; inst[it.o + 10] = u[0]; inst[it.o + 11] = u[1]; inst[it.o + 12] = v[0]; inst[it.o + 13] = v[1];
      setPaint(it, p);
    }
    // Text: each string one sprite, drawn by the 2D canvas as it lays the string out, anchored at its first glyph's origin on the
    // alphabetic baseline and snapped to a whole pixel (as canvas snaps a glyph's baseline; across, to a whole pixel where canvas
    // may use a quarter). In a colour: drawn in it (its glyphs' edges depend on how bright it is); with a gradient: drawn in its
    // stops' average colour, as coverage, and painted.
    function textItem(fill, text, x, y, maxW) {
      text = String(text);
      if (!text || !isFinite(x) || !isFinite(y) || (maxW !== undefined && !(maxW > 0))) return;
      const clip = clipOf(S.clips);
      if (clip.empty) return;
      const M = S.M, fk = S.fk ?? (S.fk = TEXT_PROPS.map(k => S[k]).join('|')), tk = S.tk ?? (S.tk = TEXT_PROPS.filter(k => k !== 'textAlign' && k !== 'textBaseline').map(k => S[k]).join('|'));
      const Lo = layout(fk, text), width = Lo.w, sw = Math.min(width, maxW ?? width);
      const al = S.textAlign, rtl = S.direction === 'rtl', k = al === 'center' ? .5 : al === 'right' || (al === 'end' && !rtl) || (al === 'start' && rtl) ? 1 : 0;
      const x0 = x - k * sw, yb = y - Lo.ab;
      const A = [M[0] * x0 + M[2] * yb + M[4], M[1] * x0 + M[3] * yb + M[5]];
      if (![M[0], M[1], M[2], M[3], ...A].every(isFinite) || !(M[0] * M[3] - M[1] * M[2])) return;
      // (its ink's bounds about the anchor, in user space, then in the canvas's pixels)
      const lw = fill ? 0 : S.lineWidth / 2 * (S.lineJoin === 'miter' ? S.miterLimit : 1), pad = lw + 2;
      const box = boxOf(M, Math.min(0, x - Lo.l - x0) - pad, y - Lo.asc - yb - pad, Math.max(sw, x + Lo.r - x0) + pad, y + Lo.desc - yb + pad);
      const op = opOf(), style = fill ? S.fillStyle : S.strokeStyle, D = typeof style === 'string' ? null : DESC.get(style);
      const draw = gg => { gg.textAlign = 'left'; gg.textBaseline = 'alphabetic'; fill ? gg.fillText(text, x0, yb, maxW) : gg.strokeText(text, x0, yb, maxW); };
      const sk = fill ? 'f' : `s${S.lineWidth},${S.lineJoin},${S.miterLimit},${S.dash},${S.lineDashOffset}`;
      if (shadowed() || filtered() || D?.kind === 4 || foreign(style)) { whole(`T|${tk}|${sk}|${maxW}|${text}`, [x0, yb], box, draw, op, clip); return; }
      const p = paintOf(style, M);
      if (!p) return;
      // (drawn in a colour: its own, or its gradient's stops' average)
      const mc = D ? D.avg ?? (D.avg = (st => [0, 1, 2, 3].map(i => st.reduce((a, s) => a + s[1][i], 0) / st.length))(D.stops.filter(s => s[1]))) : color(style);
      if (!mc || !(mc[3] > 0)) return;
      const css = cssOf(mc), st = TEXT_PROPS.map(k => S[k]), ls = [S.lineWidth, S.lineJoin, S.miterLimit, S.dash, S.lineDashOffset];
      const sp = place({ key: `T|${css}|${tk}|${sk}|${lin(M)}|${maxW}|${text}`, box, a0: D ? Math.round(mc[3] * 255) / 255 : 1, draw: (gg, X, Y) => {
        TEXT_PROPS.forEach((k, i) => { gg[k] = st[i]; });
        gg.textAlign = 'left'; gg.textBaseline = 'alphabetic';
        gg.fillStyle = gg.strokeStyle = css; gg.lineWidth = ls[0]; gg.lineJoin = ls[1]; gg.miterLimit = ls[2]; gg.setLineDash(ls[3]); gg.lineDashOffset = ls[4];
        gg.setTransform(M[0], M[1], M[2], M[3], X, Y);
        fill ? gg.fillText(text, 0, 0, maxW) : gg.strokeText(text, 0, 0, maxW);
      } }, A, 1);
      spriteItem(D ? 1 : 0, sp, clip, S.globalAlpha, op, D ? p : null);
    }
    // (a string's measures in the text state (fk): its ink's bounds as aligned, its width and its alphabetic baseline)
    const LAYOUT = new Map();
    function layout(fk, text) {
      const key = fk + '\u0001' + text;
      let Lo = LAYOUT.get(key);
      if (Lo) return Lo;
      const m = g.measureText(text);
      Lo = { l: m.actualBoundingBoxLeft, r: m.actualBoundingBoxRight, asc: m.actualBoundingBoxAscent, desc: m.actualBoundingBoxDescent, w: m.width, ab: m.alphabeticBaseline ?? 0 };
      if (LAYOUT.size > 20000) LAYOUT.clear();
      LAYOUT.set(key, Lo);
      return Lo;
    }
    function pathItem(stroke, a) {
      let ops, rule = 'nonzero', M = S.M;
      if (a[0] && typeof a[0] === 'object') {
        const p = a[0];
        if (p.__opaque) { opaquePath(stroke, p, a[1]); return; }
        ops = ops2d(p, M); rule = a[1] ?? 'nonzero';
      } else { ops = path; rule = a[0] ?? 'nonzero'; }
      if (!ops.length) return;
      const clip = clipOf(S.clips);
      if (clip.empty) return;
      const op = opOf(), style = stroke ? S.strokeStyle : S.fillStyle;
      const D = typeof style === 'string' ? null : DESC.get(style);
      if (stroke && simScale(M) && !shadowed() && !filtered() && !foreign(style)) { strokeItem(ops, simScale(M) * S.lineWidth / 2, clip, op, style); return; }
      if (stroke || shadowed() || filtered() || foreign(style) || D?.kind === 4) {
        // (drawn whole: its commands, and the transform it's filled or stroked in, about the anchor, so that the drawing is what its
        // key says; drawn in a transform that just moves it there)
        const pb = pathBounds(ops), sp = opsSpec([ops]);
        if (!pb || !sp) return;
        const A = sp.A, T = sp.T[0], fT = sp.about(M);
        const reach = stroke ? S.lineWidth / 2 * Math.sqrt(M[0] * M[0] + M[1] * M[1] + M[2] * M[2] + M[3] * M[3]) * (S.lineJoin === 'miter' ? Math.max(1, S.miterLimit) : 1.5) + 2 : 2;
        const box = [pb[0] - A[0] - reach, pb[1] - A[1] - reach, pb[2] - A[0] + reach, pb[3] - A[1] + reach];
        S.M = [1, 0, 0, 1, A[0], A[1]];
        whole(`${stroke ? 'S' : 'F' + rule}|${sp.key}|${fT.k}`, [0, 0], box, gg => {
          const B = gg.getTransform(), m = fT.T;
          replay(gg, T, B.e, B.f);
          gg.setTransform(m[0], m[1], m[2], m[3], m[4] + B.e, m[5] + B.f); stroke ? gg.stroke() : gg.fill(rule);
        }, op, clip);
        S.M = M;
        return;
      }
      const p = paintOf(style, M);
      if (!p) return;
      // (a lone circle is a disc, a lone rectangle a parallelogram)
      if (ops.length === 1) {
        const o = ops[0], s = simScale(o.M);
        if ((o.op === 'arc' || (o.op === 'ellipse' && Math.abs(o.a[2]) === Math.abs(o.a[3]))) && s && isFull(o)) {
          const Mo = o.M, c = [Mo[0] * o.a[0] + Mo[2] * o.a[1] + Mo[4], Mo[1] * o.a[0] + Mo[3] * o.a[1] + Mo[5]], R = Math.abs(o.a[2]) * s;
          const q = boxQuad([c[0] - R - 1, c[1] - R - 1, c[0] + R + 1, c[1] + R + 1], clip, OPS[op]?.[2]);
          if (!q) return;
          const it = put(3, q, clip, S.globalAlpha, op, {});
          inst[it.o + 8] = c[0]; inst[it.o + 9] = c[1]; inst[it.o + 10] = R;
          setPaint(it, p);
          return;
        }
        if (o.op === 'rect') { rectFill(o.a, o.M, clip, op, p); return; }
      }
      // (a convex polygon (lines and arcs, flattened), cut to the layer, is shaded as one: up to 4 corners in the instance, up to 32 in
      // a row of the paint table)
      if (ops.every(o => o.op === 'moveTo' || o.op === 'lineTo' || o.op === 'closePath' || o.op === 'arc' || o.op === 'ellipse')) {
        const subs = flatten(ops, .1).filter(s => s.p.length >= 4);
        if (subs.length === 1) {
          let P = [];
          const sp0 = subs[0].p;
          for (let i = 0; i < sp0.length; i += 2) if (!P.length || Math.hypot(sp0[i] - P.at(-1)[0], sp0[i + 1] - P.at(-1)[1]) > 1e-6) P.push([sp0[i], sp0[i + 1]]);
          if (P.length > 1 && Math.hypot(P[0][0] - P.at(-1)[0], P[0][1] - P.at(-1)[1]) < 1e-6) P.pop();
          if (convexSign(P)) {
            const r = clip.rect;
            P = cutPoly(P, Math.max(r[0], 0) - 2, Math.max(r[1], 0) - 2, Math.min(r[2], L.w) + 2, Math.min(r[3], L.h) + 2);
            if (P.length < 3) return;
            if (P.length <= 32) {
              const q = boxQuad([Math.min(...P.map(v => v[0])) - 1, Math.min(...P.map(v => v[1])) - 1, Math.max(...P.map(v => v[0])) + 1, Math.max(...P.map(v => v[1])) + 1], clip, OPS[op]?.[2]);
              if (!q) return;
              if (P.length <= 4) {
                if (P.length === 3) P.push(P[2]);
                const it = put(5, q, clip, S.globalAlpha, op, {});
                inst.set(P.flat(), it.o + 8);
                setPaint(it, p);
                return;
              }
              const row = new Float32Array(64);
              row.set(P.flat());
              paints.push(row);
              const it = put(11, q, clip, S.globalAlpha, op, {});
              inst[it.o + 12] = paints.length - 1; inst[it.o + 13] = P.length; inst[it.o + 14] = convexSign(P);
              setPaint(it, p);
              return;
            }
          }
        }
      }
      // (any other fill: its coverage, a sprite of its own shape, painted)
      const pb = pathBounds(ops), sp = opsSpec([ops]);
      if (!pb || !sp) return;
      const A = sp.A, T = sp.T[0];
      let box = [pb[0] - A[0] - 2, pb[1] - A[1] - 2, pb[2] - A[0] + 2, pb[3] - A[1] + 2];
      const ct = cutBox(A, box, clip);
      if (ct?.empty) return;
      if (ct) box = ct.box;
      const s = place({ key: `F|${rule}|${sp.key}${ct ? ct.key : ''}`, box, a0: 1, draw: (gg, X, Y) => { replay(gg, T, X, Y); gg.fillStyle = '#fff'; gg.fill(rule); } }, A, 4);
      spriteItem(1, s, clip, S.globalAlpha, op, p);
    }
    const isFull = o => { const a0 = o.op === 'arc' ? o.a[3] : o.a[5], a1 = o.op === 'arc' ? o.a[4] : o.a[6], ccw = !!(o.op === 'arc' ? o.a[5] : o.a[7]); return ccw ? a0 - a1 >= TAU - 1e-9 : a1 - a0 >= TAU - 1e-9; };
    function rectFill(a, M, clip, op, p) {
      const [x, y, w, h] = a;
      if (!w || !h) return;
      const o = [M[0] * x + M[2] * y + M[4], M[1] * x + M[3] * y + M[5]], u = [M[0] * w, M[1] * w], v = [M[2] * h, M[3] * h];
      const q = boxQuad(paraQuad(o, u, v), clip, OPS[op]?.[2]);
      if (!q) return;
      const it = put(2, q, clip, S.globalAlpha, op, {});
      inst[it.o + 8] = o[0]; inst[it.o + 9] = o[1]; inst[it.o + 10] = u[0]; inst[it.o + 11] = u[1]; inst[it.o + 12] = v[0]; inst[it.o + 13] = v[1];
      setPaint(it, p);
    }
    function strokeItem(ops, hw, clip, op, style) {
      const p = paintOf(style, S.M);
      if (!p || !(hw > 0)) return;
      // (a lone full circle is a ring)
      if (ops.length === 1 && (ops[0].op === 'arc' || (ops[0].op === 'ellipse' && Math.abs(ops[0].a[2]) === Math.abs(ops[0].a[3]))) && isFull(ops[0]) && simScale(ops[0].M) && !S.dash.length) {
        const o = ops[0], Mo = o.M, c = [Mo[0] * o.a[0] + Mo[2] * o.a[1] + Mo[4], Mo[1] * o.a[0] + Mo[3] * o.a[1] + Mo[5]], R = Math.abs(o.a[2]) * simScale(Mo);
        const q = boxQuad([c[0] - R - hw - 1, c[1] - R - hw - 1, c[0] + R + hw + 1, c[1] + R + hw + 1], clip, OPS[op]?.[2]);
        if (!q) return;
        const it = put(8, q, clip, S.globalAlpha, op, {});
        inst[it.o + 8] = c[0]; inst[it.o + 9] = c[1]; inst[it.o + 10] = R; inst[it.o + 11] = hw;
        setPaint(it, p);
        return;
      }
      const s = simScale(S.M), subs = flatten(ops, .15), out = [];
      const b = strokePieces(subs, hw, S.lineCap, S.lineJoin, S.miterLimit, S.dash.map(d => d * s), S.lineDashOffset * s, out);
      if (!b || !out.length) return;
      const q = boxQuad([b[0] - 1, b[1] - 1, b[2] + 1, b[3] + 1], clip, OPS[op]?.[2]);
      if (!q) return;
      // (one segment needs no coverage buffer)
      if (out.length === 1 && out[0].length === 7) {
        const it = put(4, q, clip, S.globalAlpha, op, {});
        inst.set(out[0], it.o + 8);
        setPaint(it, p);
        return;
      }
      const p0 = pn;
      for (const pc of out) {
        const o = pslot(), I = pinst;
        let x0, y0, x1, y1;
        if (pc.length === 7) { const r = pc[4] + 1; x0 = Math.min(pc[0], pc[2]) - r; y0 = Math.min(pc[1], pc[3]) - r; x1 = Math.max(pc[0], pc[2]) + r; y1 = Math.max(pc[1], pc[3]) + r; }
        else { x0 = Math.min(pc[0], pc[2], pc[4], pc[6]) - 1; y0 = Math.min(pc[1], pc[3], pc[5], pc[7]) - 1; x1 = Math.max(pc[0], pc[2], pc[4], pc[6]) + 1; y1 = Math.max(pc[1], pc[3], pc[5], pc[7]) + 1; }
        I[o] = x0; I[o + 1] = y0; I[o + 2] = x1 - x0; I[o + 3] = 0; I[o + 4] = 0; I[o + 5] = y1 - y0; I[o + 6] = pc.length === 7 ? 4 : 5; I[o + 7] = 0;
        for (let k = 0; k < 8; k++) I[o + 8 + k] = pc[k] ?? 0;
        for (let k = 16; k < FLOATS; k++) I[o + k] = 0;
      }
      const it = put(6, q, clip, S.globalAlpha, op, { pieces: [p0, pn], cb: [q[0], q[1], q[0] + q[2], q[1] + q[5]] });
      inst[it.o + 8] = q[0]; inst[it.o + 9] = q[1]; inst[it.o + 10] = q[0] + q[2]; inst[it.o + 11] = q[1] + q[5];
      setPaint(it, p);
    }
    // (a path that can't be read back (made from SVG path data): drawn whole, over the layer, in its transform as it is)
    function opaquePath(stroke, p, rule) {
      const clip = clipOf(S.clips);
      if (clip.empty) return;
      const M = S.M, box = [-M[4], -M[5], L.w - M[4], L.h - M[5]];
      const ls = stroke ? `${S.lineWidth},${S.lineJoin},${S.lineCap},${S.miterLimit}` : rule;
      S.M = [1, 0, 0, 1, M[4], M[5]];
      whole(`O${IDS(p)}|${stroke}|${ls}|${lin(M)}|${num(box)}`, [0, 0], box, gg => {
        const B = gg.getTransform();
        gg.setTransform(M[0], M[1], M[2], M[3], B.e, B.f); stroke ? gg.stroke(p) : gg.fill(p, rule);
      }, opOf(), clip);
      S.M = M;
    }
    function imageItem(a) {
      const img = a[0];
      if (!img) return;
      const clip = clipOf(S.clips);
      if (clip.empty) return;
      const Ly = LAYERS.get(img), iw = Ly ? Ly.w : img.naturalWidth || img.width, ih = Ly ? Ly.h : img.naturalHeight || img.height;
      if (!iw || !ih) return;
      let sx = 0, sy = 0, sw = iw, sh = ih, dx, dy, dw, dh;
      if (a.length >= 9) [, sx, sy, sw, sh, dx, dy, dw, dh] = a;
      else if (a.length >= 5) [, dx, dy, dw, dh] = a;
      else [, dx, dy] = a, dw = iw, dh = ih;
      if (![sx, sy, sw, sh, dx, dy, dw, dh].every(isFinite) || !sw || !sh || !dw || !dh) return;
      // (a source rectangle past the image's edge is cut to it, and the destination with it)
      if (sw < 0) { sx += sw; sw = -sw; } if (sh < 0) { sy += sh; sh = -sh; }
      const kx = dw / sw, ky = dh / sh;
      const cx0 = Math.max(sx, 0), cy0 = Math.max(sy, 0), cx1 = Math.min(sx + sw, iw), cy1 = Math.min(sy + sh, ih);
      if (cx0 >= cx1 || cy0 >= cy1) return;
      dx += (cx0 - sx) * kx; dy += (cy0 - sy) * ky; dw = (cx1 - cx0) * kx; dh = (cy1 - cy0) * ky; sx = cx0; sy = cy0; sw = cx1 - cx0; sh = cy1 - cy0;
      const M = S.M, op = opOf();
      const o = [M[0] * dx + M[2] * dy + M[4], M[1] * dx + M[3] * dy + M[5]], u = [M[0] * dw, M[1] * dw], v = [M[2] * dh, M[3] * dh];
      if (shadowed() || filtered()) {
        if (Ly && !Ly.direct) warn('a layer drawn with a shadow or filter is drawn without');
        else {
          const r = [o[0] - M[4], o[1] - M[5]], q = paraQuad([0, 0], u, v);
          whole(`I${IDS(img)}v${img.__v | 0}|${num([sx, sy, sw, sh, dx, dy, dw, dh])}`, [dx, dy], q, gg => gg.drawImage(img, sx, sy, sw, sh, dx, dy, dw, dh), op, clip);
          return;
        }
      }
      const t = imageTex(img);
      if (!t || !(t.tex || t.layer)) return;
      const q = boxQuad(paraQuad(o, u, v), clip, OPS[op]?.[2]);
      if (!q) return;
      const it = put(7, q, clip, S.globalAlpha, op, { img: t, smooth: S.imageSmoothingEnabled, rep: -1 });
      let v0 = sy / t.h, v1 = (sy + sh) / t.h;
      if (t.flip) { v0 = 1 - v0; v1 = 1 - v1; }
      inst.set([o[0], o[1], u[0], u[1], v[0], v[1], 0, 0, sx / t.w, v0, (sx + sw) / t.w, v1], it.o + 8);
    }
    function putImage(a) {
      const [img, dx, dy] = a;
      let [, , , x = 0, y = 0, w = img.width, h = img.height] = a;
      if (w < 0) { x += w; w = -w; } if (h < 0) { y += h; h = -h; }
      x = Math.max(0, x); y = Math.max(0, y); w = Math.min(img.width - x, w); h = Math.min(img.height - y, h);
      if (w <= 0 || h <= 0) return;
      const tex = gl.createTexture(); upload(tex, img, 0, 0, img.width, img.height, [img.width, img.height]); gl.bindTexture(gl.TEXTURE_2D, tex); setNearest();
      const o = [Math.round(dx + x), Math.round(dy + y)];
      const q = boxQuad([o[0], o[1], o[0] + w, o[1] + h], NOCLIP);
      if (!q) { gl.deleteTexture(tex); return; }
      const it = put(7, q, NOCLIP, 1, 'copy', { img: { tex, w: img.width, h: img.height, id: nextId++, v: 0 }, smooth: false, rep: -1, temp: tex });
      inst.set([o[0], o[1], w, 0, 0, h, 0, 0, x / img.width, y / img.height, (x + w) / img.width, (y + h) / img.height], it.o + 8);
    }
    // ---- the stand-in for the context ----
    const METHODS = {
      save() { g.save(); stack.push(S); S = { ...S }; },
      restore() { g.restore(); if (stack.length) S = stack.pop(); },
      reset() { resetState(); items = []; n = 0; pn = 0; paints = []; reqs = new Map(); },
      setTransform(...a) { const m = a[0] && typeof a[0] === 'object' ? a[0] : null; const v = m ? [m.a ?? m.m11 ?? 1, m.b ?? m.m12 ?? 0, m.c ?? m.m21 ?? 0, m.d ?? m.m22 ?? 1, m.e ?? m.m41 ?? 0, m.f ?? m.m42 ?? 0] : a.length ? a.map(Number) : ID; if (v.every(isFinite)) S.M = v; },
      resetTransform() { S.M = ID; },
      getTransform() { const M = S.M; return new DOMMatrix([M[0], M[1], M[2], M[3], M[4], M[5]]); },
      transform(a, b, c, d, e, f) { const v = [a, b, c, d, e, f].map(Number); if (v.every(isFinite)) S.M = mmul(S.M, v); },
      translate(x, y) { if (isFinite(x) && isFinite(y)) S.M = mmul(S.M, [1, 0, 0, 1, +x, +y]); },
      scale(x, y) { if (isFinite(x) && isFinite(y)) S.M = mmul(S.M, [+x, 0, 0, +y, 0, 0]); },
      rotate(r) { if (isFinite(r)) { const c = Math.cos(r), s = Math.sin(r); S.M = mmul(S.M, [c, s, -s, c, 0, 0]); } },
      beginPath() { path = []; },
      clip(...a) {
        let ops, rule;
        if (a[0] && typeof a[0] === 'object') { ops = a[0].__opaque ? null : ops2d(a[0], S.M); rule = a[1] ?? 'nonzero'; } else { ops = path.slice(); rule = a[0] ?? 'nonzero'; }
        if (!ops) { warn('a clip to an unreadable Path2D is ignored'); return; }
        S.clips = [...S.clips, { ops, rule }];
      },
      setLineDash(d) { g.setLineDash(d); S.dash = g.getLineDash(); },
      getLineDash() { return S.dash.slice(); },
      fill(...a) { pathItem(false, a); },
      stroke(...a) { pathItem(true, a); },
      fillRect(x, y, w, h) { rectItem(+x, +y, +w, +h, false); },
      clearRect(x, y, w, h) { rectItem(+x, +y, +w, +h, true); },
      strokeRect(x, y, w, h) { if (![x, y, w, h].every(isFinite) || (!w && !h)) return; const saved = path; path = [{ op: 'rect', a: [+x, +y, +w, +h], M: S.M }]; pathItem(true, []); path = saved; },
      fillText(t, x, y, m) { textItem(true, t, +x, +y, m === undefined ? undefined : +m); },
      strokeText(t, x, y, m) { textItem(false, t, +x, +y, m === undefined ? undefined : +m); },
      drawImage(...a) { imageItem(a); },
      putImageData(...a) { putImage(a); },
      createLinearGradient(...a) { return gradient(g, 'createLinearGradient', a); },
      createRadialGradient(...a) { return gradient(g, 'createRadialGradient', a); },
      createConicGradient(...a) { return gradient(g, 'createConicGradient', a); },
      createPattern(img, rep) { return pattern(g, img, rep); },
      isPointInPath(...a) { return pointIn('isPointInPath', a); },
      isPointInStroke(...a) { return pointIn('isPointInStroke', a); },
      measureText(t) { return g.measureText(t); },
      getImageData() { warn("getImageData() on a layer reads nothing: its drawing isn't on a 2D canvas"); return g.getImageData(0, 0, 1, 1); },
    };
    for (const m of PATH_OPS) METHODS[m] = (...a) => { path.push({ op: m, a, M: S.M }); };
    // (the context itself holds only what measuring text needs: its text state; a hit test builds the rest on it for the moment)
    function pointIn(k, a) {
      g.save();
      for (const p of ['lineWidth', 'lineCap', 'lineJoin', 'miterLimit']) g[p] = S[p];
      g.setLineDash(S.dash);
      if (!(a[0] && typeof a[0] === 'object')) replay(g, path, 0, 0);
      const M = S.M; g.setTransform(M[0], M[1], M[2], M[3], M[4], M[5]);
      const r = g[k](...a);
      g.restore();
      return r;
    }
    const proxy = new Proxy(g, {
      get(t, k) {
        if (k === 'canvas') return c;
        if (RAW[k] && !TEXT_SET.has(k)) return S[k];
        let f = fns.get(k);
        if (f) return f;
        const v = t[k];
        if (typeof v !== 'function') return v;
        f = METHODS[k] ?? ((...a) => { warn(`${String(k)}() is not drawn on a layer`); return v.apply(t, a.map(unwrap)); });
        fns.set(k, f);
        return f;
      },
      set(t, k, v) {
        const raw = RAW[k];
        if (!raw) { t[k] = unwrap(v); return true; }
        // (a value set again, as it was last set in this state, changes nothing)
        if (S[raw] === v && (typeof v !== 'object' || v === null)) return true;
        // (the text state is the context's too, for measuring text; the rest is kept here, taken or ignored as canvas would)
        if (TEXT_SET.has(k)) { t[k] = v; S[k] = t[k]; S.fk = S.tk = null; }
        else { const x = accept(k, v); if (x === undefined) return true; S[k] = x; }
        S[raw] = v;
        return true;
      },
    });
    // ---- a frame ----
    // begin(): the context to draw this frame's drawing on, emptied, in its default state
    L.begin = () => {
      if (opt.frame) recording++;
      L.rec = recording;
      if (L.direct) { if (g.reset) g.reset(); else c.width = c.width; return g; }
      init();
      resetState();
      items = []; n = 0; pn = 0; paints = []; reqs = new Map();
      return proxy;
    };
    // (a canvas resized forgets its drawing state; so does its stand-in)
    L.size = (w, h) => {
      if (L.w === w && L.h === h) return;
      if (L.direct) { c.width = w; c.height = h; } else c.width = 1;
      resetState();
      L.w = w; L.h = h;
    };
    L.target = () => tgt;
    // flush(): the texture the layer's drawing this frame is in (empty if it wasn't drawn on this frame)
    L.flush = () => {
      init();
      if (L.rec !== recording) return EMPTY;
      if (L.flushed === recording && last) return last;
      L.flushed = recording;
      if (L.direct) {
        if (L.panel) return last = GL.texture(L.name, c, { mipmap: true });
        gl.pixelStorei(gl.UNPACK_PREMULTIPLY_ALPHA_WEBGL, true);
        last = GL.texture(L.name, c);
        gl.pixelStorei(gl.UNPACK_PREMULTIPLY_ALPHA_WEBGL, false);
        return last;
      }
      draw();
      return last;
    };
    let prev = {};
    function draw() {
      // (layers drawn as images: their targets, as they now are)
      for (const it of items) if (it.img?.layer) {
        const Ly = it.img.layer, ok = Ly.flushed === recording && Ly !== L;
        if (!ok && Ly.rec === recording) warn(`the layer ${Ly.name} is drawn on ${L.name} before it's flushed: it's left out`);
        it.img = { ...it.img, tex: ok ? Ly.target()?.tex ?? null : null, v: Ly.version };
      }
      // (what's drawn, compared with the last draw's, to skip one that draws the same: the instances, then what else each item draws
      // with (its sprites' keys, its image), then the paint table)
      const meta = new Float64Array(items.length * 10 + 2);
      meta[0] = L.w; meta[1] = L.h;
      items.forEach((it, i) => {
        const o = 2 + i * 10;
        meta[o] = OPN[it.blend] ?? -1;
        if (it.sp) { meta[o + 1] = it.sp.r.h1[0]; meta[o + 2] = it.sp.r.h1[1]; }
        if (it.cm) { meta[o + 3] = it.cm.r.h1[0]; meta[o + 4] = it.cm.r.h1[1]; meta[o + 8] = it.cm.I[0]; meta[o + 9] = it.cm.I[1]; }
        if (it.img) { meta[o + 5] = it.img.id * 2 + (it.smooth ? 1 : 0); meta[o + 6] = (it.img.v | 0) * 2 + (it.img.tex ? 1 : 0); }
        if (it.temp) meta[o + 7] = nextId++;
      });
      const U = new Uint32Array(inst.buffer, 0, n * FLOATS), PU = new Uint32Array(pinst.buffer, 0, pn * FLOATS), PT = new Float32Array(paints.length * 64);
      paints.forEach((r, i) => PT.set(r, i * 64));
      const same = (a, b) => { if (!b || a.length !== b.length) return false; for (let i = 0; i < a.length; i++) if (a[i] !== b[i]) return false; return true; };
      const unchanged = tgt && tgt.w === L.w && tgt.h === L.h && last && same(U, prev.U) && same(meta, prev.meta) && same(PU, prev.PU) && same(new Uint32Array(PT.buffer), prev.PT);
      prev = { U: U.slice(), meta, PU: PU.slice(), PT: new Uint32Array(PT.buffer) };
      if (unchanged) return;
      // (every sprite the items draw with, looked up, and those not in the atlas made; then each item told where its sprites are)
      const { got, temps } = settle(reqs);
      const skip = new Set();
      for (const it of items) {
        if (it.kind === 7 && !it.img?.tex) { skip.add(it); continue; }
        if (it.sp) {
          const a = got.get(it.sp.key);
          if (!a) { console.error('draw2d: a sprite is missing'); skip.add(it); continue; }
          const I = inst, o = it.o;
          I[o + 8] = it.sp.I[0] + a.o[0]; I[o + 9] = it.sp.I[1] + a.o[1]; I[o + 10] = a.w; I[o + 11] = a.h; I[o + 12] = a.x; I[o + 13] = a.y; I[o + 7] = a.tex ? 6 : a.page; it.spr = a.tex ?? null;
        }
        if (it.cm) {
          const a = got.get(it.cm.key);
          if (!a) { console.error('draw2d: a clip is missing'); skip.add(it); continue; }
          const I = inst, o = it.o;
          I[o + 24] = a.x; I[o + 25] = a.y; I[o + 26] = a.tex ? 7 : a.page; I[o + 28] = it.cm.I[0] + a.o[0]; I[o + 29] = it.cm.I[1] + a.o[1]; I[o + 30] = a.w; I[o + 31] = a.h; it.msk = a.tex ?? null;
        }
      }
      gl.activeTexture(gl.TEXTURE0 + U_SCRATCH);
      tgt = GL.target('d2:' + L.name, L.w, L.h, true);
      const prevVAO = gl.getParameter(gl.VERTEX_ARRAY_BINDING);
      gl.bindVertexArray(vao);
      // (the instances: the items', then the stroke pieces')
      gl.bindBuffer(gl.ARRAY_BUFFER, instBuf);
      const bytes = (n + pn) * FLOATS * 4;
      if (bytes > instCap) { instCap = Math.max(bytes, instCap * 2, 65536); gl.bufferData(gl.ARRAY_BUFFER, instCap, gl.DYNAMIC_DRAW); }
      if (n) gl.bufferSubData(gl.ARRAY_BUFFER, 0, inst, 0, n * FLOATS);
      if (pn) gl.bufferSubData(gl.ARRAY_BUFFER, n * FLOATS * 4, pinst, 0, pn * FLOATS);
      // (the paint table)
      if (paints.length) {
        gl.activeTexture(gl.TEXTURE0 + U_PAINT); gl.bindTexture(gl.TEXTURE_2D, paintTex);
        gl.pixelStorei(gl.UNPACK_FLIP_Y_WEBGL, false);
        const rows = Math.max(paints.length, 16), data = new Float32Array(rows * 64);
        data.set(PT);
        if (rows > paintRows) { paintRows = Math.max(rows, paintRows * 2); gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA32F, 16, paintRows, 0, gl.RGBA, gl.FLOAT, null); }
        gl.texSubImage2D(gl.TEXTURE_2D, 0, 0, 0, 16, rows, gl.RGBA, gl.FLOAT, data);
        gl.pixelStorei(gl.UNPACK_FLIP_Y_WEBGL, true);
        GL.stats.uploads++; GL.stats.uploadBytes += rows * 256;
      }
      gl.useProgram(prog);
      // (every unit the program samples gets a texture of ours: one left from another pass could be this layer's own target)
      const bind = (u, t) => { gl.activeTexture(gl.TEXTURE0 + u); gl.bindTexture(gl.TEXTURE_2D, t); };
      for (let i = 0; i < PAGES; i++) bind(i, pages[i]?.tex ?? EMPTY.tex);
      for (const u of [U_SPR, U_MSK, U_IMG, U_COV, U_DST]) bind(u, EMPTY.tex);
      bind(U_PAINT, paintTex);
      gl.bindFramebuffer(gl.FRAMEBUFFER, tgt.fb); gl.viewport(0, 0, L.w, L.h);
      gl.disable(gl.SCISSOR_TEST); gl.clearColor(0, 0, 0, 0); gl.clear(gl.COLOR_BUFFER_BIT);
      gl.uniform2f(loc.uSize, L.w, L.h); gl.uniform1i(loc.uMode, 0);
      gl.enable(gl.BLEND); gl.blendEquation(gl.FUNC_ADD);
      let draws = 0;
      const point = first => { for (let j = 0; j < 8; j++) gl.vertexAttribPointer(1 + j, 4, gl.FLOAT, false, FLOATS * 4, first * FLOATS * 4 + j * 16); };
      const run = (first, count) => { point(first); gl.drawArraysInstanced(gl.TRIANGLE_STRIP, 0, 4, count); draws++; };
      let curImg = null, curSmooth = null, curRep = null, curBlend = null, curSpr = null, curMsk = null;
      const bindFor = it => {
        const t = it.img?.tex ?? null;
        if (t !== curImg || it.smooth !== curSmooth || it.rep !== curRep) {
          bind(U_IMG, t ?? EMPTY.tex);
          if (t) {
            const f = it.smooth === false ? gl.NEAREST : gl.LINEAR;
            gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, f); gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, f);
            const rep = it.rep ?? -1;
            gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, rep >= 0 && rep & 1 ? gl.REPEAT : gl.CLAMP_TO_EDGE);
            gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, rep >= 0 && rep & 2 ? gl.REPEAT : gl.CLAMP_TO_EDGE);
          }
          curImg = t; curSmooth = it.smooth; curRep = it.rep;
        }
        if ((it.spr ?? null) !== curSpr) { curSpr = it.spr ?? null; bind(U_SPR, curSpr ?? EMPTY.tex); }
        if ((it.msk ?? null) !== curMsk) { curMsk = it.msk ?? null; bind(U_MSK, curMsk ?? EMPTY.tex); }
      };
      const alike = (a, b) => b.kind !== 6 && !skip.has(b) && b.blend === a.blend && !MIX[b.blend] && (b.img?.tex ?? null) === curImg && (!b.img || (b.smooth === curSmooth && b.rep === curRep)) && (b.spr ?? null) === curSpr && (b.msk ?? null) === curMsk;
      const setBlend = op => {
        if (op === curBlend) return;
        curBlend = op;
        const f = OPS[op];
        if (f) gl.blendFunc(gl[f[0]], gl[f[1]]);
      };
      const toLayer = () => { gl.bindFramebuffer(gl.FRAMEBUFFER, tgt.fb); gl.viewport(0, 0, L.w, L.h); };
      let i = 0;
      while (i < items.length) {
        const it = items[i];
        if (skip.has(it)) { i++; continue; }
        if (it.kind === 6) {
          // a stroke: its pieces' coverage, the largest of them, into the coverage buffer; then painted through it
          const cv = coverage();
          bind(U_COV, EMPTY.tex);
          gl.bindFramebuffer(gl.FRAMEBUFFER, cv.fb); gl.viewport(0, 0, L.w, L.h);
          gl.enable(gl.SCISSOR_TEST);
          const b = it.cb; gl.scissor(b[0], L.h - b[3], b[2] - b[0], b[3] - b[1]);
          gl.clear(gl.COLOR_BUFFER_BIT);
          gl.blendEquation(gl.MAX); gl.blendFunc(gl.ONE, gl.ONE); curBlend = null;
          gl.uniform1i(loc.uMode, 1);
          run(n + it.pieces[0], it.pieces[1] - it.pieces[0]);
          gl.disable(gl.SCISSOR_TEST); gl.blendEquation(gl.FUNC_ADD); gl.uniform1i(loc.uMode, 0);
          toLayer();
          bind(U_COV, cv.tex);
        }
        if (MIX[it.blend]) {
          // a blend mode: what's under it copied out, and blended with it in the shader
          const d = dstCopy(it);
          gl.disable(gl.BLEND); gl.uniform1i(loc.uMode, 2); gl.uniform1i(loc.uBlend, MIX[it.blend]);
          bind(U_DST, d.tex);
          bindFor(it); run(it.o / FLOATS, 1);
          gl.enable(gl.BLEND); gl.uniform1i(loc.uMode, 0);
          i++;
          continue;
        }
        // (a run of items drawn alike, as far as the next that isn't)
        bindFor(it); setBlend(it.blend);
        let j = i + 1;
        while (j < items.length && alike(it, items[j])) j++;
        run(it.o / FLOATS, j - i);
        i = j;
      }
      gl.disable(gl.BLEND); gl.blendEquation(gl.FUNC_ADD); gl.blendFunc(gl.ONE, gl.ZERO);
      for (const it of items) if (it.temp) gl.deleteTexture(it.temp);
      for (const t of temps) gl.deleteTexture(t);
      gl.activeTexture(gl.TEXTURE0);
      gl.bindVertexArray(prevVAO);
      GL.stats.passes += draws; GL.stats.pixels += L.w * L.h;
      L.version++;
      // (a panel: its colour straight, with mipmaps, as the scene shader samples panels)
      if (L.panel) {
        straight = GL.target('d2s:' + L.name, L.w, L.h, true);
        GL.pass(unpremul, straight, {}, { uSrc: tgt });
        gl.bindTexture(gl.TEXTURE_2D, straight.tex);
        gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.LINEAR_MIPMAP_LINEAR);
        gl.generateMipmap(gl.TEXTURE_2D);
        GL.stats.mipmaps++;
        last = straight;
      } else last = tgt;
    }
    function dstCopy(it) {
      gl.activeTexture(gl.TEXTURE0 + U_SCRATCH);
      if (!dstT || dstT.w < L.w || dstT.h < L.h) { if (dstT) gl.deleteTexture(dstT.tex); dstT = { tex: gl.createTexture(), w: Math.max(L.w, dstT?.w ?? 0), h: Math.max(L.h, dstT?.h ?? 0) }; gl.bindTexture(gl.TEXTURE_2D, dstT.tex); gl.pixelStorei(gl.UNPACK_FLIP_Y_WEBGL, false); gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA8, dstT.w, dstT.h, 0, gl.RGBA, gl.UNSIGNED_BYTE, null); gl.pixelStorei(gl.UNPACK_FLIP_Y_WEBGL, true); setNearest(); }
      const I = inst, o = it.o, x0 = Math.max(0, Math.floor(I[o])), y0 = Math.max(0, Math.floor(I[o + 1])), x1 = Math.min(L.w, Math.ceil(I[o] + I[o + 2])), y1 = Math.min(L.h, Math.ceil(I[o + 1] + I[o + 5]));
      gl.bindTexture(gl.TEXTURE_2D, dstT.tex);
      if (x1 > x0 && y1 > y0) gl.copyTexSubImage2D(gl.TEXTURE_2D, 0, x0, L.h - y1, x0, L.h - y1, x1 - x0, y1 - y0);
      return dstT;
    }
    return L;
  }
  // (the coverage buffer the strokes share: one channel, as big as the biggest layer)
  function coverage() {
    gl.activeTexture(gl.TEXTURE0 + U_SCRATCH);
    let w = 0, h = 0;
    for (const L of allLayers) if (!L.direct) { w = Math.max(w, L.w); h = Math.max(h, L.h); }
    if (!covT || covT.w < w || covT.h < h) {
      if (covT) { gl.deleteTexture(covT.tex); gl.deleteFramebuffer(covT.fb); }
      const tex = gl.createTexture(); gl.bindTexture(gl.TEXTURE_2D, tex);
      gl.pixelStorei(gl.UNPACK_FLIP_Y_WEBGL, false); gl.texImage2D(gl.TEXTURE_2D, 0, gl.R8, w, h, 0, gl.RED, gl.UNSIGNED_BYTE, null); gl.pixelStorei(gl.UNPACK_FLIP_Y_WEBGL, true); setNearest();
      const fb = gl.createFramebuffer(); gl.bindFramebuffer(gl.FRAMEBUFFER, fb); gl.framebufferTexture2D(gl.FRAMEBUFFER, gl.COLOR_ATTACHMENT0, gl.TEXTURE_2D, tex, 0);
      covT = { tex, fb, w, h };
    }
    return covT;
  }
  const allLayers = [];
  function makeLayer(...a) { const L = layer(...a); allLayers.push(L); return L; }
  // (called once a frame's layers are drawn: images uploaded for that frame alone go)
  function endFrame() { frameNo++; if (gl) for (const t of frameTemps.splice(0)) gl.deleteTexture(t); }
  return { layer: makeLayer, endFrame, stats: () => ({ pages: pages.length, sprites: ATLAS.size, ...stats }), recent: () => recent.splice(0) };
})();

;
// ---- styles/idolfilm/gl.js ----
// gl.js: the idolfilm style's renderer. WebGL2 on the output canvas (in the page, the site's worker and headless Chromium, where it
// runs on SwiftShader), drawing each frame into an HDR scene buffer, then bloom and a final grade to the screen.
//
// The scene is drawn in immediate mode, in the order a shot calls these (painter's order; no depth buffer):
//   sky(o)               the background: a vertical gradient with a glowing horizon band and an optional spotlight
//   floor(o)             the stage floor at y = 0: dark gloss, a pool of light, procedural glitter, an optional ring mark
//   plane(tex, o)        a textured plane in 3D (a member cut-out, a set piece, an interface panel), drawn over a vertex grid so it can
//                        sway and squash, with a rim light from its alpha edge; plane2D() places one in screen pixels
//   particles(mode, o)   a particle system animated entirely on the GPU from its seed and the song time (see PARTICLE MODES)
//   ribbon(tex, pts, o)  a texture laid along a 3D path (type along a curve)
//   layer() / put(g)     a full-frame 2D context (kinetic type, UI; drawn with WebGL) and compositing it at this point in the order
//   panel(key, w, h, fn) a 2D canvas the size of an interface, turned into a texture for plane() or ribbon()
// The world is in metres: x right, y up, z toward the default camera; the floor is y = 0 and a member stands about 1.65 m tall.
// cam(o) sets the camera for everything drawn after it; project(p) gives a world point's screen position in logical pixels.

const gl = canvas.getContext('webgl2', { alpha: false, antialias: false, depth: false, stencil: false, premultipliedAlpha: true,
  preserveDrawingBuffer: false, powerPreference: 'high-performance' });
// Without WebGL2 there is no video (no fallback renderer, by design). Fail at once and clearly: the site's worker reports the error, and
// its main-thread fallback finds STYLE_READY rejected, so the page keeps showing its poster instead of waiting for frames.
if (!gl) {
  const err = new Error('The K-pop video needs WebGL2, which this browser doesn\u2019t have or has turned off.');
  self.STYLE_READY = self.STYLE_ALL = Promise.reject(err);
  self.STYLE_READY.catch(() => {});
  throw err;
}
const HDR = !!gl.getExtension('EXT_color_buffer_float');

// ---------- shaders ----------
const VS_FULL = `#version 300 es
out vec2 vUV;
void main() { vec2 p = vec2((gl_VertexID << 1) & 2, gl_VertexID & 2); vUV = p; gl_Position = vec4(p * 2. - 1., 0., 1.); }`;

const FS_SKY = `#version 300 es
precision highp float;
in vec2 vUV; out vec4 o;
uniform vec3 uTop, uHor, uBot, uGlow; uniform float uHorY, uGlowK, uGlowW, uAspect, uSeed;
uniform vec4 uSpot; uniform vec3 uSpotCol;
float h(vec2 p) { return fract(sin(dot(p, vec2(12.9898, 78.233)) + uSeed) * 43758.5453); }
void main() {
  float y = vUV.y, d = y - uHorY;
  vec3 c = d > 0. ? mix(uHor, uTop, smoothstep(0., .75, d)) : mix(uHor, uBot, smoothstep(0., .35, -d));
  c += uGlow * uGlowK * (exp(-d * d / (uGlowW * uGlowW)) + .35 * exp(-d * d / (uGlowW * uGlowW * 16.)));
  vec2 q = (vUV - uSpot.xy) * vec2(uAspect, 1.);
  c += uSpotCol * uSpot.w * exp(-dot(q, q) / (uSpot.z * uSpot.z));
  c += (h(gl_FragCoord.xy) - .5) / 255.;
  o = vec4(c, 1.);
}`;

const VS_FLOOR = `#version 300 es
in vec2 aP; uniform mat4 uVP; uniform vec4 uExtent; out vec3 vW;
void main() { vW = vec3(mix(uExtent.x, uExtent.z, aP.x), 0., mix(uExtent.y, uExtent.w, aP.y)); gl_Position = uVP * vec4(vW, 1.); }`;
const FS_FLOOR = `#version 300 es
precision highp float;
in vec3 vW; out vec4 o;
uniform vec3 uBase, uPoolCol, uFog, uGlit, uRingCol, uCam, uGridCol; uniform vec4 uPool, uRing; uniform float uT, uGlitK, uFogD, uGrid, uReflK;
float h(vec2 p) { return fract(sin(dot(p, vec2(127.1, 311.7))) * 43758.5453); }
void main() {
  vec2 p = vW.xz;
  float dist = length(vW - uCam);
  vec3 c = uBase;
  vec2 pq = (p - uPool.xy) / uPool.z;
  c += uPoolCol * uPool.w * exp(-dot(pq, pq));
  // glitter: one sparkle per cell, each twinkling at its own rate; faded out where the cells get smaller than a pixel
  vec2 cell = floor(p * 14.), f = fract(p * 14.) - .5;
  float r = h(cell), tw = pow(.5 + .5 * sin(uT * (1.5 + r * 5.) + r * 40.), 12.);
  vec2 off = vec2(h(cell + 7.), h(cell + 3.)) - .5;
  float sp = exp(-dot(f - off * .6, f - off * .6) * 180.) * tw * step(.55, h(cell + 11.));
  float aa = clamp(1. - fwidth(p.x * 14.) * .6, 0., 1.);
  c += uGlit * sp * uGlitK * aa * (.4 + 1.6 * exp(-dot(pq, pq) * .5));
  // grid lines (the music-show stage)
  if (uGrid > 0.) { vec2 g = abs(fract(p * uGrid) - .5) / fwidth(p * uGrid); c += uGridCol * (1. - clamp(min(g.x, g.y), 0., 1.)) * .35; }
  // the ring mark a performer stands on
  if (uRing.w > 0.) {
    float rr = abs(length(p - uRing.xy) - uRing.z);
    c += uRingCol * uRing.w * (exp(-rr * rr * 900.) + .25 * exp(-rr * rr * 40.));
  }
  // a faint reflection of the horizon glow, toward the back
  c += uFog * uReflK * smoothstep(4., 30., dist);
  c = mix(c, uFog, smoothstep(uFogD * .35, uFogD, dist));
  o = vec4(c, 1.);
}`;

const VS_PLANE = `#version 300 es
in vec2 aUV; uniform mat4 uVP; uniform vec3 uO, uR, uU; uniform vec4 uUVR, uBend; out vec2 vUV; out vec2 vL;
void main() {
  vec2 uv = aUV;
  // sway leans the plane from its base (hair, a body on the beat); wave ripples it; squash shortens and widens it about its base
  float sway = uBend.x * uv.y * uv.y + uBend.w * sin(uv.y * 9.42 + uBend.y) * uv.y;
  float sx = .5 + (uv.x - .5) * (1. + uBend.z * .6) + sway;
  vec3 p = uO + uR * sx + uU * uv.y * (1. - uBend.z);
  gl_Position = uVP * vec4(p, 1.);
  vUV = uUVR.xy + vec2(uv.x, 1. - uv.y) * uUVR.zw; vL = uv;
}`;
const FS_PLANE = `#version 300 es
precision highp float;
in vec2 vUV; in vec2 vL; out vec4 o;
uniform sampler2D uTex; uniform vec4 uMul, uRim, uFlat; uniform vec3 uBot, uAdd; uniform vec2 uRimDir; uniform float uFadeB, uFadeT;
void main() {
  vec4 c = texture(uTex, vUV);
  float a = c.a;
  vec3 rgb = c.rgb * mix(uBot, uMul.rgb, vL.y) + uAdd * a;
  if (uRim.a > 0.) {
    float a1 = texture(uTex, vUV + uRimDir).a, a2 = texture(uTex, vUV + uRimDir * 2.2).a;
    rgb += uRim.rgb * uRim.a * clamp(a - (a1 + a2) * .5, 0., 1.);
  }
  rgb = mix(rgb, uFlat.rgb * a, uFlat.a);
  float k = uMul.a * smoothstep(0., uFadeB + 1e-4, vL.y) * (1. - smoothstep(1. - uFadeT - 1e-4, 1., vL.y));
  o = vec4(rgb, a) * k;
}`;

// Particle modes (uMode); every one is a pure function of the seed and uT.
//   0 DUST     motes drifting in a box (uA: centre xyz, uB: half size xyz, uC.x: drift speed)
//   1 GLITTER  twinkling points on a disc on the floor (uA: centre xyz + radius w)
//   2 BURST    a cannon or explosion (uA: origin xyz, uB: t0, speed, gravity, life; uC: direction xyz + spread w)
//   3 FALL     falling sparkles or confetti in a box, wrapping (uA: centre, uB: half size, uC.x: fall speed)
//   4 OCEAN    an audience's lightsticks in rows (uA: x0, z0, x1, z1; uB.x: rows, uB.y: sway, uB.z: beat, uB.w: raise)
//   5 RING     points on a spinning ring (uA: centre xyz + radius w; uB.x: spin, uB.y: tilt)
//   6 POINTS   positions from the per-instance aPos buffer (a shape sampled from text or a picture), scattering with uB.x
const VS_PART = `#version 300 es
in vec2 aQ; in vec4 aSeed; in vec3 aPos;
uniform mat4 uVP; uniform vec3 uCR, uCU; uniform float uT, uSize; uniform int uMode; uniform vec4 uA, uB, uC;
uniform vec3 uCol0, uCol1, uCol2, uCol3; uniform float uNCol; uniform int uShape;
out vec2 vQ; out vec4 vC;
vec3 h3(float n) { return fract(sin(vec3(n, n + 1.7, n + 3.1)) * vec3(43758.5453, 22578.145, 19642.349)); }
vec3 pal(float k) { float i = floor(k * uNCol); return i < 1. ? uCol0 : i < 2. ? uCol1 : i < 3. ? uCol2 : uCol3; }
void main() {
  vec3 p; float a = 1., s = uSize * (.45 + aSeed.z);
  vec3 col = pal(aSeed.y);
  if (uMode == 0) {
    vec3 dr = (h3(aSeed.x * 91.) - .5) * uC.x;
    p = uA.xyz + (fract(aSeed.xyw + dr * uT * .05 + vec3(0., uT * .004 * uC.x, 0.)) * 2. - 1.) * uB.xyz;
    a = .35 + .65 * pow(.5 + .5 * sin(uT * (1. + aSeed.w * 3.) + aSeed.x * 60.), 3.);
  } else if (uMode == 1) {
    float r = sqrt(aSeed.x) * uA.w, th = aSeed.w * 6.2832;
    p = uA.xyz + vec3(cos(th) * r, .005, sin(th) * r);
    a = pow(.5 + .5 * sin(uT * (2. + aSeed.z * 6.) + aSeed.y * 70.), 10.);
  } else if (uMode == 2) {
    float age = uT - uB.x;
    vec3 d = normalize(uC.xyz + (h3(aSeed.x * 37.) - .5) * 2. * uC.w);
    float sp = uB.y * (.35 + .65 * aSeed.w), drag = 1.6;
    float tt = (1. - exp(-drag * max(age, 0.))) / drag;
    p = uA.xyz + d * sp * tt + vec3(0., -.5 * uB.z * age * age, 0.);
    a = age < 0. ? 0. : (1. - smoothstep(uB.w * .45, uB.w * (.7 + .3 * aSeed.z), age));
  } else if (uMode == 3) {
    vec3 q = aSeed.xyw;
    q.y = fract(q.y - uT * uC.x * (.6 + .4 * aSeed.z) / (2. * uB.y));
    p = uA.xyz + (q * 2. - 1.) * uB.xyz + vec3(sin(uT * 1.3 + aSeed.x * 30.) * .15, 0., 0.);
    a = .6 + .4 * sin(uT * 3. + aSeed.y * 20.);
  } else if (uMode == 4) {
    float row = floor(aSeed.x * uB.x), fx = aSeed.w;
    float z = mix(uA.y, uA.w, (row + .5) / uB.x), x = mix(uA.x, uA.z, fx);
    float sw = sin(uB.z * 3.14159 + x * .35 + row * .7) * uB.y;
    p = vec3(x + sw, 1.25 + uB.w * (.5 + .5 * sin(uB.z * 6.2832 + row)) + (aSeed.z - .5) * .15, z + (aSeed.y - .5) * .5);
    a = .7 + .3 * aSeed.z;
  } else if (uMode == 5) {
    float th = aSeed.x * 6.2832 + uT * uB.x;
    vec3 q = vec3(cos(th), 0., sin(th)) * uA.w;
    float ct = cos(uB.y), st = sin(uB.y);
    q = vec3(q.x, q.y * ct - q.z * st, q.y * st + q.z * ct);
    p = uA.xyz + q;
    a = .5 + .5 * pow(.5 + .5 * sin(uT * 4. + aSeed.y * 50.), 4.);
  } else {
    p = aPos + (h3(aSeed.x * 17.) - .5) * uB.x * (.5 + aSeed.w);
    a = 1. - uB.y * aSeed.z;
  }
  vQ = aQ * 2. - 1.;
  vec2 q = aQ - .5;
  if (uShape == 2) {
    // confetti: each piece spins in the plane and tumbles (foreshortened, darker edge-on)
    float ang = aSeed.x * 6.2832 + uT * (1.5 + aSeed.w * 4.), fl = cos(uT * (4. + aSeed.z * 6.) + aSeed.y * 20.);
    q.x *= .15 + .85 * abs(fl);
    q = mat2(cos(ang), sin(ang), -sin(ang), cos(ang)) * q;
    col *= .5 + .5 * abs(fl);
    s *= 1.6;
  }
  vC = vec4(col, a);
  gl_Position = uVP * vec4(p + (uCR * q.x + uCU * q.y) * s, 1.);
}`;
const FS_PART = `#version 300 es
precision highp float; precision highp int;
in vec2 vQ; in vec4 vC; out vec4 o;
uniform int uShape; uniform float uGain;
void main() {
  float r2 = dot(vQ, vQ), k;
  if (uShape == 0) k = exp(-r2 * 4.) + .6 * exp(-r2 * 40.);
  else if (uShape == 1) { vec2 q = abs(vQ); k = exp(-r2 * 30.) * 1.4 + (exp(-q.x * 30.) * exp(-q.y * 2.5) + exp(-q.y * 30.) * exp(-q.x * 2.5)) * .8; }
  else k = step(max(abs(vQ.x), abs(vQ.y) * 1.8), .8);
  if (k < .003) discard;
  o = vec4(vC.rgb * k * vC.a * uGain, uShape == 2 ? k * vC.a : 0.);
}`;

const VS_MESH = `#version 300 es
in vec3 aP; in vec2 aUV; uniform mat4 uVP; out vec2 vUV;
void main() { vUV = aUV; gl_Position = uVP * vec4(aP, 1.); }`;
const FS_MESH = `#version 300 es
precision highp float;
in vec2 vUV; out vec4 o; uniform sampler2D uTex; uniform vec4 uMul;
void main() { vec4 c = texture(uTex, vUV); o = vec4(c.rgb * uMul.rgb, c.a) * uMul.a; }`;

// (uFlip: a texture uploaded from a canvas has its top row first; one drawn by GL, its bottom row)
const FS_BLIT = `#version 300 es
precision highp float;
in vec2 vUV; out vec4 o; uniform sampler2D uTex; uniform float uGain, uAlpha, uFlip;
void main() { vec4 c = texture(uTex, vec2(vUV.x, uFlip > .5 ? 1. - vUV.y : vUV.y)); o = vec4(c.rgb * uGain, c.a) * uAlpha; }`;

// bloom: a thresholded 13-tap downsample chain and a tent-filtered upsample chain (the usual "dual filter" bloom)
const FS_DOWN = `#version 300 es
precision highp float;
in vec2 vUV; out vec4 o; uniform sampler2D uTex; uniform vec2 uTexel; uniform float uThresh, uKnee; uniform int uPre;
vec3 s(vec2 d) { return texture(uTex, vUV + d * uTexel).rgb; }
void main() {
  vec3 c = s(vec2(0)) * .125;
  c += (s(vec2(-1, -1)) + s(vec2(1, -1)) + s(vec2(-1, 1)) + s(vec2(1, 1))) * .125;
  c += (s(vec2(-2, -2)) + s(vec2(2, -2)) + s(vec2(-2, 2)) + s(vec2(2, 2))) * .03125;
  c += (s(vec2(0, -2)) + s(vec2(0, 2)) + s(vec2(-2, 0)) + s(vec2(2, 0))) * .0625;
  if (uPre == 1) {
    float br = max(c.r, max(c.g, c.b)), rq = clamp(br - uThresh + uKnee, 0., 2. * uKnee);
    rq = rq * rq / (4. * uKnee + 1e-4);
    c *= max(rq, br - uThresh) / max(br, 1e-4);
  }
  o = vec4(c, 1.);
}`;
const FS_UP = `#version 300 es
precision highp float;
in vec2 vUV; out vec4 o; uniform sampler2D uTex; uniform vec2 uTexel; uniform float uK;
vec3 s(vec2 d) { return texture(uTex, vUV + d * uTexel).rgb; }
void main() {
  vec3 c = s(vec2(0)) * 4. + (s(vec2(-1, 0)) + s(vec2(1, 0)) + s(vec2(0, -1)) + s(vec2(0, 1))) * 2.
    + s(vec2(-1, -1)) + s(vec2(1, -1)) + s(vec2(-1, 1)) + s(vec2(1, 1));
  o = vec4(c / 16. * uK, 1.);
}`;
const FS_FINAL = `#version 300 es
precision highp float;
in vec2 vUV; out vec4 o;
uniform sampler2D uScene, uBloom; uniform float uBloomK, uExpo, uVig, uGrain, uCA, uFlash, uFade, uSat, uSeed, uShoulder;
uniform vec3 uLift, uGainC, uFlashCol; uniform vec2 uRes;
float h(vec2 p) { return fract(sin(dot(p, vec2(12.9898, 78.233)) + uSeed) * 43758.5453); }
vec3 tone(vec3 x) { float k = uShoulder; return mix(x, k + (1. - k) * (1. - exp(-(x - k) / (1. - k))), step(k, x)); }
void main() {
  vec2 uv = vUV, d = uv - .5;
  float r2 = dot(d, d);
  vec3 c = vec3(texture(uScene, uv - d * uCA * r2).r, texture(uScene, uv).g, texture(uScene, uv + d * uCA * r2).b);
  c += texture(uBloom, uv).rgb * uBloomK;
  c = tone(c * uExpo);
  c = uLift + c * (uGainC - uLift);
  float l = dot(c, vec3(.2126, .7152, .0722));
  c = mix(vec3(l), c, uSat);
  c *= 1. - uVig * smoothstep(.25, .95, length(d * vec2(1.25, 1.)));
  c += (h(uv * uRes) - .5) * uGrain;
  c = mix(c, uFlashCol, uFlash);
  c *= 1. - uFade;
  o = vec4(c, 1.);
}`;

function compile(vs, fs) {
  const mk = (type, src) => {
    const s = gl.createShader(type); gl.shaderSource(s, src); gl.compileShader(s);
    if (!gl.getShaderParameter(s, gl.COMPILE_STATUS)) throw new Error(gl.getShaderInfoLog(s) + '\n' + src.split('\n').map((l, i) => `${i + 1}: ${l}`).join('\n'));
    return s;
  };
  const p = gl.createProgram();
  gl.attachShader(p, mk(gl.VERTEX_SHADER, vs)); gl.attachShader(p, mk(gl.FRAGMENT_SHADER, fs));
  gl.linkProgram(p);
  if (!gl.getProgramParameter(p, gl.LINK_STATUS)) throw new Error(gl.getProgramInfoLog(p));
  const u = {}, n = gl.getProgramParameter(p, gl.ACTIVE_UNIFORMS);
  for (let i = 0; i < n; i++) { const info = gl.getActiveUniform(p, i); u[info.name] = gl.getUniformLocation(p, info.name); }
  return { p, u, a: name => gl.getAttribLocation(p, name) };
}
const PROG = {
  sky: compile(VS_FULL, FS_SKY), floor: compile(VS_FLOOR, FS_FLOOR), plane: compile(VS_PLANE, FS_PLANE), part: compile(VS_PART, FS_PART),
  mesh: compile(VS_MESH, FS_MESH), blit: compile(VS_FULL, FS_BLIT), down: compile(VS_FULL, FS_DOWN), up: compile(VS_FULL, FS_UP), fin: compile(VS_FULL, FS_FINAL),
};

// ---------- geometry ----------
const VAO_EMPTY = gl.createVertexArray();
function gridVAO(prog, nx, ny) {
  const v = [];
  for (let j = 0; j < ny; j++) for (let i = 0; i < nx; i++) {
    const q = [[i / nx, j / ny], [(i + 1) / nx, j / ny], [i / nx, (j + 1) / ny], [(i + 1) / nx, j / ny], [(i + 1) / nx, (j + 1) / ny], [i / nx, (j + 1) / ny]];
    for (const [a, b] of q) v.push(a, b);
  }
  const vao = gl.createVertexArray(); gl.bindVertexArray(vao);
  const b = gl.createBuffer(); gl.bindBuffer(gl.ARRAY_BUFFER, b); gl.bufferData(gl.ARRAY_BUFFER, new Float32Array(v), gl.STATIC_DRAW);
  const loc = prog.a('aUV'); gl.enableVertexAttribArray(loc); gl.vertexAttribPointer(loc, 2, gl.FLOAT, false, 0, 0);
  gl.bindVertexArray(null);
  return { vao, n: v.length / 2 };
}
const PLANE_GRID = gridVAO(PROG.plane, 10, 24), PLANE_QUAD = gridVAO(PROG.plane, 1, 1);
const FLOOR_VAO = (() => {
  const vao = gl.createVertexArray(); gl.bindVertexArray(vao);
  const b = gl.createBuffer(); gl.bindBuffer(gl.ARRAY_BUFFER, b); gl.bufferData(gl.ARRAY_BUFFER, new Float32Array([0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1]), gl.STATIC_DRAW);
  const loc = PROG.floor.a('aP'); gl.enableVertexAttribArray(loc); gl.vertexAttribPointer(loc, 2, gl.FLOAT, false, 0, 0);
  gl.bindVertexArray(null); return vao;
})();
// particle systems share one seed buffer (MAXP instances); a system uses the first n. POINTS systems add their own position buffer.
const MAXP = 60000;
const PART = (() => {
  const vao = gl.createVertexArray(); gl.bindVertexArray(vao);
  const q = gl.createBuffer(); gl.bindBuffer(gl.ARRAY_BUFFER, q); gl.bufferData(gl.ARRAY_BUFFER, new Float32Array([0, 0, 1, 0, 0, 1, 1, 1]), gl.STATIC_DRAW);
  let loc = PROG.part.a('aQ'); gl.enableVertexAttribArray(loc); gl.vertexAttribPointer(loc, 2, gl.FLOAT, false, 0, 0);
  const seeds = new Float32Array(MAXP * 4);
  for (let i = 0; i < MAXP * 4; i++) seeds[i] = hash2(i >> 2, i & 3);
  const sb = gl.createBuffer(); gl.bindBuffer(gl.ARRAY_BUFFER, sb); gl.bufferData(gl.ARRAY_BUFFER, seeds, gl.STATIC_DRAW);
  loc = PROG.part.a('aSeed'); gl.enableVertexAttribArray(loc); gl.vertexAttribPointer(loc, 4, gl.FLOAT, false, 0, 0); gl.vertexAttribDivisor(loc, 1);
  const pb = gl.createBuffer(); gl.bindBuffer(gl.ARRAY_BUFFER, pb); gl.bufferData(gl.ARRAY_BUFFER, new Float32Array(MAXP * 3), gl.DYNAMIC_DRAW);
  loc = PROG.part.a('aPos'); gl.enableVertexAttribArray(loc); gl.vertexAttribPointer(loc, 3, gl.FLOAT, false, 0, 0); gl.vertexAttribDivisor(loc, 1);
  gl.bindVertexArray(null);
  return { vao, pb, posKey: null };
})();
const MESH = (() => {
  const vao = gl.createVertexArray(); gl.bindVertexArray(vao);
  const b = gl.createBuffer(); gl.bindBuffer(gl.ARRAY_BUFFER, b); gl.bufferData(gl.ARRAY_BUFFER, 4 * 5 * 2048, gl.DYNAMIC_DRAW);
  let loc = PROG.mesh.a('aP'); gl.enableVertexAttribArray(loc); gl.vertexAttribPointer(loc, 3, gl.FLOAT, false, 20, 0);
  loc = PROG.mesh.a('aUV'); gl.enableVertexAttribArray(loc); gl.vertexAttribPointer(loc, 2, gl.FLOAT, false, 20, 12);
  gl.bindVertexArray(null); return { vao, b };
})();

// ---------- render targets ----------
function makeTarget(w, h, hdr) {
  const tex = gl.createTexture(); gl.bindTexture(gl.TEXTURE_2D, tex);
  gl.texImage2D(gl.TEXTURE_2D, 0, hdr ? gl.RGBA16F : gl.RGBA8, w, h, 0, gl.RGBA, hdr ? gl.HALF_FLOAT : gl.UNSIGNED_BYTE, null);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.LINEAR); gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.LINEAR);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.CLAMP_TO_EDGE); gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE);
  const fb = gl.createFramebuffer(); gl.bindFramebuffer(gl.FRAMEBUFFER, fb);
  gl.framebufferTexture2D(gl.FRAMEBUFFER, gl.COLOR_ATTACHMENT0, gl.TEXTURE_2D, tex, 0);
  return { tex, fb, w, h };
}
function freeTarget(t) { if (t) { gl.deleteTexture(t.tex); gl.deleteFramebuffer(t.fb); } }
let SCENE = null, BLOOM = [], PW = 0, PH = 0;
// Quality knobs, which the quality levels set (QUALITY_LEVELS, below): bloom levels, particle counts, how often a live panel (an LED
// wall carrying the lyric) repaints (0: every frame), and the 3D scene's resolution, as a fraction of the canvas's.
const QUALITY = { bloomLevels: 6, particles: 1, liveRate: 0, sceneK: 1 };
function resizeTargets() {
  PW = canvas.width; PH = canvas.height;
  freeTarget(SCENE); BLOOM.forEach(freeTarget);
  SCENE = makeTarget(Math.max(16, Math.round(PW * QUALITY.sceneK)), Math.max(16, Math.round(PH * QUALITY.sceneK)), HDR);
  BLOOM = [];
  let w = SCENE.w, h = SCENE.h;
  for (let i = 0; i < QUALITY.bloomLevels && w > 8 && h > 8; i++) { w = Math.max(1, w >> 1); h = Math.max(1, h >> 1); BLOOM.push(makeTarget(w, h, HDR)); }
  for (const l of LAYERS) l.stale = true;
}
SCALE_HOOKS.push(resizeTargets);

// ---------- textures ----------
// texImage(src): a picture or 2D canvas into the bound texture, premultiplied, its top row first. Every upload sets the unpack state
// it relies on: draw2d.js's leave UNPACK_FLIP_Y_WEBGL set, as the demoscene's engine has it.
function texImage(src) {
  gl.pixelStorei(gl.UNPACK_FLIP_Y_WEBGL, false); gl.pixelStorei(gl.UNPACK_PREMULTIPLY_ALPHA_WEBGL, true);
  gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA, gl.RGBA, gl.UNSIGNED_BYTE, src);
  gl.pixelStorei(gl.UNPACK_PREMULTIPLY_ALPHA_WEBGL, false);
}
// texOf(src): a GL texture for an ImageBitmap or canvas, made on first use (premultiplied, mipmapped). Canvases that change call
// texOf(src, true) to re-upload.
const _texs = new Map();
function texOf(src, update = false) {
  let t = _texs.get(src);
  if (t && !update) { t.used = T; return t; }
  if (!t) { t = { tex: gl.createTexture(), w: src.width, h: src.height, mip: !update }; _texs.set(src, t); }
  gl.bindTexture(gl.TEXTURE_2D, t.tex);
  texImage(src);
  if (t.mip) gl.generateMipmap(gl.TEXTURE_2D);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, t.mip ? gl.LINEAR_MIPMAP_LINEAR : gl.LINEAR);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.LINEAR);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.CLAMP_TO_EDGE); gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE);
  t.w = src.width; t.h = src.height; t.used = T;
  return t;
}
// cellTexs(src, cols, rows, n): the first n cells of a picture cut into a cols × rows grid (a clip's sprite sheet, or its stand-in), each
// a texture of its own holding that cell and nothing else, made on first use and kept with the picture (dropTex(src) frees them). The
// picture is uploaded once, each cell copied out of it on the GPU (blitFramebuffer), and the whole picture's texture deleted at once:
// no draw can ever sample a whole sheet, whatever state a UV rectangle, an upload or a decode is in. Each is { tex, w, h } (w and h:
// the cell's own size, unrounded, which is what sets a plane's aspect).
const _cellTexs = new Map(), _cellFB = { read: null, draw: null };
function cellTexs(src, cols, rows, n) {
  let cells = _cellTexs.get(src);
  if (cells) return cells;
  _cellFB.read ??= gl.createFramebuffer(); _cellFB.draw ??= gl.createFramebuffer();
  const whole = gl.createTexture();
  gl.bindTexture(gl.TEXTURE_2D, whole);
  texImage(src);
  gl.bindFramebuffer(gl.READ_FRAMEBUFFER, _cellFB.read);
  gl.framebufferTexture2D(gl.READ_FRAMEBUFFER, gl.COLOR_ATTACHMENT0, gl.TEXTURE_2D, whole, 0);
  gl.bindFramebuffer(gl.DRAW_FRAMEBUFFER, _cellFB.draw);
  const cw = src.width / cols, ch = src.height / rows;
  cells = [];
  for (let i = 0; i < n; i++) {
    const x0 = Math.round((i % cols) * cw), y0 = Math.round(Math.floor(i / cols) * ch), x1 = Math.round((i % cols + 1) * cw), y1 = Math.round((Math.floor(i / cols) + 1) * ch);
    const w = Math.max(1, x1 - x0), h = Math.max(1, y1 - y0), t = { tex: gl.createTexture(), w: cw, h: ch, used: T };
    gl.bindTexture(gl.TEXTURE_2D, t.tex);
    gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA8, w, h, 0, gl.RGBA, gl.UNSIGNED_BYTE, null);
    gl.framebufferTexture2D(gl.DRAW_FRAMEBUFFER, gl.COLOR_ATTACHMENT0, gl.TEXTURE_2D, t.tex, 0);
    // (texture rows run from the picture's top, in both textures: the cell lands the right way up)
    gl.blitFramebuffer(x0, y0, x1, y1, 0, 0, w, h, gl.COLOR_BUFFER_BIT, gl.NEAREST);
    gl.generateMipmap(gl.TEXTURE_2D);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.LINEAR_MIPMAP_LINEAR); gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.LINEAR);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.CLAMP_TO_EDGE); gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE);
    cells.push(t);
  }
  gl.framebufferTexture2D(gl.READ_FRAMEBUFFER, gl.COLOR_ATTACHMENT0, gl.TEXTURE_2D, null, 0);
  gl.framebufferTexture2D(gl.DRAW_FRAMEBUFFER, gl.COLOR_ATTACHMENT0, gl.TEXTURE_2D, null, 0);
  gl.deleteTexture(whole);
  bindScene();
  _cellTexs.set(src, cells);
  return cells;
}
function dropTex(src) {
  const t = _texs.get(src); if (t) { gl.deleteTexture(t.tex); _texs.delete(src); }
  const m = _cellTexs.get(src); if (m) { for (const c of m) gl.deleteTexture(c.tex); _cellTexs.delete(src); }
}

// ---------- matrices and the camera ----------
function m4mul(a, b) {
  const o = new Float32Array(16);
  for (let c = 0; c < 4; c++) for (let r = 0; r < 4; r++) {
    let s = 0; for (let k = 0; k < 4; k++) s += a[k * 4 + r] * b[c * 4 + k];
    o[c * 4 + r] = s;
  }
  return o;
}
const v3sub = (a, b) => [a[0] - b[0], a[1] - b[1], a[2] - b[2]];
const v3add = (a, b) => [a[0] + b[0], a[1] + b[1], a[2] + b[2]];
const v3mul = (a, k) => [a[0] * k, a[1] * k, a[2] * k];
const v3cross = (a, b) => [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]];
const v3norm = a => { const l = Math.hypot(...a) || 1; return [a[0] / l, a[1] / l, a[2] / l]; };
const v3lerp = (a, b, k) => [lerp(a[0], b[0], k), lerp(a[1], b[1], k), lerp(a[2], b[2], k)];
// CAM: { pos, at, fov (vertical, degrees), roll, VP (view-projection), right, up, fwd }
// (ASPECT: the aspect ratio of what's being drawn: the frame, or an offscreen() picture)
let CAM = null, ASPECT = W / H;
function cam(o = {}) {
  const pos = o.pos ?? [0, 1.4, 6], at = o.at ?? [0, 1.2, 0], fov = (o.fov ?? 35) * Math.PI / 180, roll = o.roll ?? 0;
  const f = v3norm(v3sub(at, pos));
  let r = v3norm(v3cross(f, [0, 1, 0]));
  let u = v3cross(r, f);
  if (roll) { const c = Math.cos(roll), s = Math.sin(roll); [r, u] = [v3add(v3mul(r, c), v3mul(u, s)), v3add(v3mul(u, c), v3mul(r, -s))]; }
  const view = new Float32Array([r[0], u[0], -f[0], 0, r[1], u[1], -f[1], 0, r[2], u[2], -f[2], 0,
    -(r[0] * pos[0] + r[1] * pos[1] + r[2] * pos[2]), -(u[0] * pos[0] + u[1] * pos[1] + u[2] * pos[2]), f[0] * pos[0] + f[1] * pos[1] + f[2] * pos[2], 1]);
  const near = o.near ?? .05, far = o.far ?? 400, ty = 1 / Math.tan(fov / 2), asp = ASPECT;
  // (a lens shift moves the picture without turning the camera: shiftX/shiftY in fractions of the frame)
  const proj = new Float32Array([ty / asp, 0, 0, 0, 0, ty, 0, 0, -(o.shiftX ?? 0) * 2, -(o.shiftY ?? 0) * 2, (far + near) / (near - far), -1, 0, 0, 2 * far * near / (near - far), 0]);
  CAM = { pos, at, fov, VP: m4mul(proj, view), right: r, up: u, fwd: f };
  return CAM;
}
// A world point's screen position in logical pixels, and its depth w (0 or less: behind the camera).
function project(p) {
  const m = CAM.VP, x = m[0] * p[0] + m[4] * p[1] + m[8] * p[2] + m[12], y = m[1] * p[0] + m[5] * p[1] + m[9] * p[2] + m[13], w = m[3] * p[0] + m[7] * p[1] + m[11] * p[2] + m[15];
  return [(x / w * .5 + .5) * W, (1 - (y / w * .5 + .5)) * H, w];
}
// the screen height in pixels of a 1 m tall object at depth w
const pxPerM = w => H / (2 * Math.tan(CAM.fov / 2) * w);
// an orthographic "camera" in which world units are screen pixels (y down), for plane2D()
const ORTHO = new Float32Array([2 / W, 0, 0, 0, 0, -2 / H, 0, 0, 0, 0, -1, 0, -1, 1, 0, 1]);

// ---------- frame state and blending ----------
const BLEND = {
  normal: () => { gl.enable(gl.BLEND); gl.blendFuncSeparate(gl.ONE, gl.ONE_MINUS_SRC_ALPHA, gl.ONE, gl.ONE_MINUS_SRC_ALPHA); },
  add: () => { gl.enable(gl.BLEND); gl.blendFunc(gl.ONE, gl.ONE); },
  screen: () => { gl.enable(gl.BLEND); gl.blendFunc(gl.ONE, gl.ONE_MINUS_SRC_COLOR); },
  none: () => gl.disable(gl.BLEND),
};
// (TARGET: where drawing goes: the scene, or an offscreen() picture being drawn)
let TARGET = null;
let _crisp = [], _flushing = false;
function bindScene() {
  // (a layer held back to be drawn crisp over the finished frame goes into the scene after all, if the scene is drawn on over it)
  if (!TARGET && _crisp.length && !_flushing) flushCrisp();
  const tg = TARGET ?? SCENE; gl.bindFramebuffer(gl.FRAMEBUFFER, tg.fb); gl.viewport(0, 0, tg.w, tg.h);
}
// offscreen(key, w, h, fn): draw fn() (sky, floor, planes, particles, layers: anything) into a w × h picture of its own, with its own
// camera, and return it for plane() as { tex, w, h, fbo: true } (planes flip it the right way up). A screen within the frame: the
// premiere's player, a phone showing the stage.
const OFFS = new Map();
function offscreen(key, w, h, fn) {
  w = Math.max(16, Math.round(w)); h = Math.max(16, Math.round(h));
  let o = OFFS.get(key);
  if (!o || o.w !== w || o.h !== h) { if (o) freeTarget(o); o = makeTarget(w, h, HDR); OFFS.set(key, o); }
  const saveT = TARGET, saveC = CAM, saveA = ASPECT;
  TARGET = o; ASPECT = w / h; bindScene(); gl.clearColor(0, 0, 0, 1); gl.clear(gl.COLOR_BUFFER_BIT);
  try { fn(); } finally { TARGET = saveT; CAM = saveC; ASPECT = saveA; }
  return { tex: o.tex, w, h, fbo: true };
}
const hexRGB = c => typeof c === 'string' ? rgbOf(c) : c;
function u3(prog, name, c, k = 1) { const v = hexRGB(c); gl.uniform3f(prog.u[name], v[0] * k, v[1] * k, v[2] * k); }

// ---------- drawing ----------
// sky(o): top, horizon, bottom colours; horizonY (0..1 up the screen, default where the camera's horizon falls), glow (colour), glowK,
// glowW (the band's half-height), spot: [x, y, r, k] (0..1 screen, y up) with spotCol.
function sky(o = {}) {
  bindScene(); BLEND.none();
  const P = PROG.sky; gl.useProgram(P.p); gl.bindVertexArray(VAO_EMPTY);
  let hy = o.horizonY;
  if (hy === undefined) { const q = project(v3add(CAM.pos, v3mul(v3norm([CAM.fwd[0], 0, CAM.fwd[2]]), 1000))); hy = 1 - q[1] / H; }
  u3(P, 'uTop', o.top ?? '#05040A'); u3(P, 'uHor', o.horizon ?? '#1A1430'); u3(P, 'uBot', o.bottom ?? o.horizon ?? '#1A1430');
  u3(P, 'uGlow', o.glow ?? '#FFB0D8'); gl.uniform1f(P.u.uGlowK, o.glowK ?? .35); gl.uniform1f(P.u.uGlowW, o.glowW ?? .06);
  gl.uniform1f(P.u.uHorY, hy); gl.uniform1f(P.u.uAspect, W / H); gl.uniform1f(P.u.uSeed, (T * 7.13) % 1);
  const s = o.spot ?? [.5, .5, .3, 0]; gl.uniform4f(P.u.uSpot, s[0], s[1], s[2], s[3]); u3(P, 'uSpotCol', o.spotCol ?? '#FFFFFF');
  gl.drawArrays(gl.TRIANGLES, 0, 3);
}
// floor(o): base colour, pool: [x, z, radius, k] with poolCol, glitter (colour) and glitterK, fog (colour) and fogD (the distance it's
// all fog), ring: [x, z, radius, k] with ringCol, grid (lines per metre) with gridCol, refl (horizon reflection), extent [x0, z0, x1, z1].
function floor(o = {}) {
  bindScene(); BLEND.none();
  const P = PROG.floor; gl.useProgram(P.p); gl.bindVertexArray(FLOOR_VAO);
  gl.uniformMatrix4fv(P.u.uVP, false, CAM.VP);
  const e = o.extent ?? [-250, -400, 250, 40]; gl.uniform4f(P.u.uExtent, e[0], e[1], e[2], e[3]);
  u3(P, 'uBase', o.base ?? '#07060C');
  const pool = o.pool ?? [0, 0, 3, .25]; gl.uniform4f(P.u.uPool, pool[0], pool[1], pool[2], pool[3]); u3(P, 'uPoolCol', o.poolCol ?? '#FFFFFF');
  u3(P, 'uGlit', o.glitter ?? '#FFE9F6'); gl.uniform1f(P.u.uGlitK, (o.glitterK ?? 1.2));
  u3(P, 'uFog', o.fog ?? '#1A1430'); gl.uniform1f(P.u.uFogD, o.fogD ?? 70); gl.uniform1f(P.u.uReflK, o.refl ?? .25);
  const ring = o.ring ?? [0, 0, 1, 0]; gl.uniform4f(P.u.uRing, ring[0], ring[1], ring[2], ring[3]); u3(P, 'uRingCol', o.ringCol ?? '#FFFFFF');
  gl.uniform1f(P.u.uGrid, o.grid ?? 0); u3(P, 'uGridCol', o.gridCol ?? '#FFFFFF');
  gl.uniform3f(P.u.uCam, CAM.pos[0], CAM.pos[1], CAM.pos[2]); gl.uniform1f(P.u.uT, T);
  gl.drawArrays(gl.TRIANGLES, 0, 6);
}
// plane(src, o): a textured plane. src: an ImageBitmap or canvas (or {tex, w, h}). o: at [x, y, z] (where the anchor lands), w / h
// (metres; give one and the other follows the picture's aspect), anchor [u, v] (default bottom centre [.5, 1]), facing: 'camera'
// (the default: turns about the vertical to face the camera), 'screen' (fully faces it), or a yaw in radians; tilt (radians, leaning
// back), roll; uv [u0, v0, u1, v1] (a crop); alpha; mul (colour multiplier, top) and bot (at the bottom: a key light from above);
// add (colour); rim: [colour, strength] with rimDir [dx, dy] in uv; flat: [colour, k] (towards a silhouette); sway, phase, squash, wave;
// fadeB / fadeT (fraction of the height faded at the bottom / top); grid: false for a plain quad; blend: 'normal' | 'add' | 'screen';
// mirror: true draws it upside down below the floor (a reflection), vp: the view-projection to use (ORTHO for plane2D), basis: {O, R,
// U} (its corner and edges, as another plane() returned them: overrides at, w, h, anchor and facing). Returns its {O, R, U}.
function plane(src, o = {}) {
  if (!src) return null;
  const t = src.tex ? src : texOf(src);
  let uv = o.uv ?? [0, 0, 1, 1];
  if (t.fbo) uv = [uv[0], 1 - uv[1], uv[2], 1 - uv[3]];
  const asp = Math.abs((t.w * (uv[2] - uv[0])) / (t.h * (uv[3] - uv[1])));
  const h = o.h ?? (o.w ? o.w / asp : 1), w = o.w ?? h * asp;
  const [au, av] = o.anchor ?? [.5, 1];
  let R, U;
  if (o.vp === ORTHO) { R = [w, 0, 0]; U = [0, -h, 0]; }
  else {
    let yaw;
    if (o.facing === 'screen') { R = v3mul(CAM.right, w); U = v3mul(CAM.up, h); }
    else {
      yaw = typeof o.facing === 'number' ? o.facing : Math.atan2(CAM.pos[0] - (o.at?.[0] ?? 0), CAM.pos[2] - (o.at?.[2] ?? 0));
      const tilt = o.tilt ?? 0, roll = o.roll ?? 0;
      const back = [Math.sin(yaw), 0, Math.cos(yaw)];
      let r = [Math.cos(yaw), 0, -Math.sin(yaw)], u = v3add(v3mul([0, 1, 0], Math.cos(tilt)), v3mul(back, -Math.sin(tilt)));
      if (roll) { const c = Math.cos(roll), s = Math.sin(roll); [r, u] = [v3add(v3mul(r, c), v3mul(u, s)), v3add(v3mul(u, c), v3mul(r, -s))]; }
      R = v3mul(r, w); U = v3mul(u, h);
    }
    if (o.mirror) U = v3mul(U, -1);
  }
  const at = o.at ?? [0, 0, 0];
  let O = o.vp === ORTHO ? [at[0] - au * w, at[1] + (1 - av) * h, 0] : v3sub(at, v3add(v3mul(R, au), v3mul(U, 1 - av)));
  // o.basis {O, R, U}: the plane's corner and edges given outright (a patch laid exactly over part of another plane)
  if (o.basis) ({ O, R, U } = o.basis);
  bindScene(); (BLEND[o.blend ?? 'normal'])();
  const P = PROG.plane; gl.useProgram(P.p);
  const G = o.grid === false ? PLANE_QUAD : PLANE_GRID; gl.bindVertexArray(G.vao);
  gl.uniformMatrix4fv(P.u.uVP, false, o.vp ?? CAM.VP);
  gl.uniform3f(P.u.uO, O[0], O[1], O[2]); gl.uniform3f(P.u.uR, R[0], R[1], R[2]); gl.uniform3f(P.u.uU, U[0], U[1], U[2]);
  gl.uniform4f(P.u.uUVR, uv[0], uv[1], uv[2] - uv[0], uv[3] - uv[1]);
  gl.uniform4f(P.u.uBend, o.sway ?? 0, o.phase ?? 0, o.squash ?? 0, o.wave ?? 0);
  const mul = hexRGB(o.mul ?? [1, 1, 1]), k = o.gain ?? 1;
  gl.uniform4f(P.u.uMul, mul[0] * k, mul[1] * k, mul[2] * k, o.alpha ?? 1);
  u3(P, 'uBot', o.bot ?? mul, k); u3(P, 'uAdd', o.add ?? [0, 0, 0]);
  const rim = o.rim; if (rim) { const c = hexRGB(rim[0]); gl.uniform4f(P.u.uRim, c[0], c[1], c[2], rim[1]); } else gl.uniform4f(P.u.uRim, 0, 0, 0, 0);
  const rd = o.rimDir ?? [-.006, .006]; gl.uniform2f(P.u.uRimDir, rd[0], rd[1]);
  const fl = o.flat; if (fl) { const c = hexRGB(fl[0]); gl.uniform4f(P.u.uFlat, c[0], c[1], c[2], fl[1]); } else gl.uniform4f(P.u.uFlat, 0, 0, 0, 0);
  gl.uniform1f(P.u.uFadeB, o.fadeB ?? 0); gl.uniform1f(P.u.uFadeT, o.fadeT ?? 0);
  gl.activeTexture(gl.TEXTURE0); gl.bindTexture(gl.TEXTURE_2D, t.tex); gl.uniform1i(P.u.uTex, 0);
  gl.drawArrays(gl.TRIANGLES, 0, G.n);
  return { O, R, U };
}
// plane2D(src, o): a plane placed in screen pixels: o.at [x, y] is where the anchor lands, o.w / o.h in pixels.
const plane2D = (src, o = {}) => plane(src, { ...o, vp: ORTHO, grid: o.grid ?? (o.sway || o.wave || o.squash ? true : false) });

// particles(mode, o): n (instances), size (metres), cols (up to four colours, picked per particle), shape ('dot' | 'star' | 'chip'),
// gain, blend ('add' by default; 'normal' for chips), a / b / c (the mode's vec4 parameters; see PARTICLE MODES), t (the clock the
// system runs on, default the song time), pos: a Float32Array of xyz positions for mode 6 (POINTS) with posKey naming it for reuse.
const MODE = { dust: 0, glitter: 1, burst: 2, fall: 3, ocean: 4, ring: 5, points: 6 };
function particles(mode, o = {}) {
  const P = PROG.part; bindScene();
  const n = Math.min(MAXP, Math.round((o.n ?? 500) * (o.noScale ? 1 : QUALITY.particles)));
  if (n <= 0) return;
  (BLEND[o.blend ?? (o.shape === 'chip' ? 'normal' : 'add')])();
  gl.useProgram(P.p); gl.bindVertexArray(PART.vao);
  if (MODE[mode] === 6 && o.pos && PART.posKey !== (o.posKey ?? o.pos)) {
    gl.bindBuffer(gl.ARRAY_BUFFER, PART.pb); gl.bufferSubData(gl.ARRAY_BUFFER, 0, o.pos); PART.posKey = o.posKey ?? o.pos;
  }
  gl.uniformMatrix4fv(P.u.uVP, false, CAM.VP);
  gl.uniform3f(P.u.uCR, ...CAM.right); gl.uniform3f(P.u.uCU, ...CAM.up);
  gl.uniform1f(P.u.uT, o.t ?? T); gl.uniform1f(P.u.uSize, o.size ?? .03); gl.uniform1i(P.u.uMode, MODE[mode]);
  const v4 = v => [...(v ?? []), 0, 0, 0, 0].slice(0, 4), A = v4(o.a), B = v4(o.b), C = v4(o.c);
  gl.uniform4f(P.u.uA, ...A); gl.uniform4f(P.u.uB, ...B); gl.uniform4f(P.u.uC, ...C);
  const cols = [].concat(o.cols ?? ['#FFFFFF']);
  ['uCol0', 'uCol1', 'uCol2', 'uCol3'].forEach((u, i) => u3(P, u, cols[Math.min(i, cols.length - 1)]));
  gl.uniform1f(P.u.uNCol, cols.length);
  gl.uniform1i(P.u.uShape, { dot: 0, star: 1, chip: 2 }[o.shape ?? 'dot']); gl.uniform1f(P.u.uGain, o.gain ?? 1);
  gl.drawArraysInstanced(gl.TRIANGLE_STRIP, 0, 4, n);
}
// ribbon(src, pts, o): a texture laid along a 3D path pts ([[x, y, z], ...], at least 2), o.width (metres), o.normal (the direction the
// ribbon's width runs: default the camera's up), o.u0 / o.u1 (the stretch of the texture used, for a reveal), o.alpha, o.mul.
function ribbon(src, pts, o = {}) {
  const t = src.tex ? src : texOf(src);
  const wd = o.width ?? .3, n = pts.length, u0 = o.u0 ?? 0, u1 = o.u1 ?? 1, up = o.normal ? v3norm(o.normal) : CAM.up;
  const len = [0]; for (let i = 1; i < n; i++) len.push(len[i - 1] + Math.hypot(...v3sub(pts[i], pts[i - 1])));
  const total = len[n - 1] || 1;
  // each point's two edge vertices, then two triangles per segment
  const edge = pts.map((c, j) => {
    const tan = v3norm(v3sub(pts[Math.min(n - 1, j + 1)], pts[Math.max(0, j - 1)]));
    const side = o.face ? v3norm(v3cross(tan, v3sub(c, CAM.pos))) : v3norm(v3cross(v3cross(tan, up), tan)), u = lerp(u0, u1, len[j] / total);
    return [[...v3add(c, v3mul(side, wd / 2)), u, 0], [...v3add(c, v3mul(side, -wd / 2)), u, 1]];
  });
  const verts = [];
  for (let i = 0; i < n - 1; i++) { const [a0, b0] = edge[i], [a1, b1] = edge[i + 1]; verts.push(...a0, ...b0, ...a1, ...b0, ...b1, ...a1); }
  bindScene(); (BLEND[o.blend ?? 'normal'])();
  const P = PROG.mesh; gl.useProgram(P.p); gl.bindVertexArray(MESH.vao);
  gl.bindBuffer(gl.ARRAY_BUFFER, MESH.b); gl.bufferSubData(gl.ARRAY_BUFFER, 0, new Float32Array(verts));
  gl.uniformMatrix4fv(P.u.uVP, false, o.vp ?? CAM.VP);
  const mul = hexRGB(o.mul ?? [1, 1, 1]), k = o.gain ?? 1; gl.uniform4f(P.u.uMul, mul[0] * k, mul[1] * k, mul[2] * k, o.alpha ?? 1);
  gl.activeTexture(gl.TEXTURE0); gl.bindTexture(gl.TEXTURE_2D, t.tex); gl.uniform1i(P.u.uTex, 0);
  gl.drawArrays(gl.TRIANGLES, 0, verts.length / 5);
}

// ---------- the GL that draw2d.js draws with ----------
// draw2d.js (the layers' drawing on the GPU, below) draws through a few parts of the demoscene's modern/gl.js: GL is those parts, on
// this context. A target is RGBA8, linear and clamped; pass() draws a full-screen triangle into one (for draw2d.js's panels, which
// this style doesn't use). draw2d.js's direct mode, which uploads whole canvases with GL.texture(), is render mode's, where the
// layers aren't drawn with it.
const GL = (() => {
  const targets = new Map(), progs = new Map();
  const stats = { passes: 0, pixels: 0, uploads: 0, uploadBytes: 0, mipmaps: 0, allocs: 0 };
  function target(name, w, h) {
    w = Math.max(1, Math.round(w)); h = Math.max(1, Math.round(h));
    let r = targets.get(name);
    if (r && r.w === w && r.h === h) return r;
    freeTarget(r);
    r = makeTarget(w, h, false);
    targets.set(name, r); stats.allocs++;
    return r;
  }
  function program(name, fs) {
    let p = progs.get(name);
    if (!p) progs.set(name, p = compile(VS_FULL, fs));
    return p;
  }
  function pass(p, dest, uniforms = {}, samplers = {}) {
    gl.useProgram(p.p); gl.bindVertexArray(VAO_EMPTY);
    gl.bindFramebuffer(gl.FRAMEBUFFER, dest.fb); gl.viewport(0, 0, dest.w, dest.h);
    for (const [n, v] of Object.entries(uniforms)) if (p.u[n]) gl.uniform1f(p.u[n], v);
    let unit = 0;
    for (const [n, s] of Object.entries(samplers)) { gl.activeTexture(gl.TEXTURE0 + unit); gl.bindTexture(gl.TEXTURE_2D, s.tex); gl.uniform1i(p.u[n], unit++); }
    gl.drawArrays(gl.TRIANGLES, 0, 3);
    gl.activeTexture(gl.TEXTURE0);
    stats.passes++; stats.pixels += dest.w * dest.h;
  }
  return { init: () => gl, program, target, pass, stats };
})();

// ---------- 2D layers and panels ----------
// layer(): a full-frame 2D context (at the render scale, drawn in logical 1920 × 1080 units), empty, in the 2D context's default state
// but for that scale; put(g, o) composites it into the scene at this point in the order (o.gain brightens it past white so that it
// blooms; o.alpha). Outside render mode the context is draw2d.js's stand-in (shared with the demoscene's modern engine): it records
// the drawing, and put() draws it with WebGL into the layer's own texture, text and other shapes as sprites kept in an atlas, so a
// frame uploads only what's new to it (a string, a size or an angle it hasn't drawn lately) instead of a full-frame canvas per layer.
// A layer's drawing depends on nothing but the frame's own (see draw2d.js). Render mode (offline renders, capturing frames with
// toDataURL) draws the layers on 2D canvases and uploads them whole, as the video was made.
// (the same test as draw2d.js's RENDER_MODE: its layers are drawn on their 2D canvases there, which this file doesn't use)
const CANVAS_LAYERS = HAS_DOM && /[?&]render\b/.test(location.search);
const LAYERS = [], _layerOf = new Map();   // (the layers, a pool used in order each frame; each context's layer)
let _layerN = 0, _d2Clock = null;
function layer() {
  let L = LAYERS[_layerN++];
  if (!L) {
    if (CANVAS_LAYERS) { L = { c: makeCanvas(PW, PH), tex: gl.createTexture() }; L.g = L.c.getContext('2d'); }
    else L = { d2: D2.layer(`layer${LAYERS.length}`, PW, PH) };
    LAYERS.push(L);
  }
  let g;
  if (L.d2) { L.d2.size(PW, PH); g = L.d2.begin(); g.setTransform(RS, 0, 0, RS, 0, 0); }
  else {
    if (L.c.width !== PW || L.c.height !== PH) { L.c.width = PW; L.c.height = PH; }
    g = L.g;
    g.setTransform(1, 0, 0, 1, 0, 0); g.clearRect(0, 0, PW, PH);
    g.setTransform(RS, 0, 0, RS, 0, 0); g.globalAlpha = 1; g.globalCompositeOperation = 'source-over';
  }
  _layerOf.set(g, L);
  return g;
}
// (draw2d.js's frames: each frame's drawing on the layers is a recording of its own, begun with the frame, so a layer drawn and put
// any time in the frame, nested in another or not, draws just that frame's drawing; the frame's own uploads go once it's done, below)
if (!CANVAS_LAYERS) FRAME_BEGIN.push(() => { (_d2Clock ??= D2.layer('frame', 1, 1, { frame: true })).begin(); });
function put(g, o = {}) {
  const L = _layerOf.get(g);
  let tex, flip;
  if (L.d2) { tex = L.d2.flush().tex; flip = false; }
  else {
    gl.bindTexture(gl.TEXTURE_2D, L.tex);
    texImage(L.c);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.LINEAR); gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.LINEAR);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.CLAMP_TO_EDGE); gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE);
    tex = L.tex; flip = true;
  }
  const item = { tex, flip, gain: o.gain ?? 1, alpha: o.alpha ?? 1, blend: o.blend ?? 'normal' };
  // (with the scene drawn at less than the canvas's resolution, a layer over the scene (the lyric, the interfaces' type) is held back
  // and drawn over the finished frame at the canvas's full resolution, so that type stays crisp at every quality level)
  if (!TARGET && QUALITY.sceneK < 1) { _crisp.push(item); return; }
  bindScene(); blitLayer(item);
}
function blitLayer(it) {
  (BLEND[it.blend])();
  const P = PROG.blit; gl.useProgram(P.p); gl.bindVertexArray(VAO_EMPTY);
  gl.activeTexture(gl.TEXTURE0); gl.bindTexture(gl.TEXTURE_2D, it.tex); gl.uniform1i(P.u.uTex, 0); gl.uniform1f(P.u.uGain, it.gain); gl.uniform1f(P.u.uAlpha, it.alpha);
  gl.uniform1f(P.u.uFlip, it.flip ? 1 : 0);
  gl.drawArrays(gl.TRIANGLES, 0, 3);
}
function flushCrisp() {
  _flushing = true;
  try { bindScene(); for (const it of _crisp) blitLayer(it); } finally { _crisp = []; _flushing = false; }
}
// panel(key, w, h, draw, o): a 2D canvas w × h logical pixels (at o.res pixels per logical pixel, default 1), for plane() or ribbon().
// draw(g, w, h) paints it. A panel with the same key and o.stamp as last time isn't repainted (give a stamp that changes with whatever
// the picture shows, e.g. how many chat messages are in); o.live repaints it every frame.
const PANELS = new Map();
// (PANEL_PICS.touch(name), set by the kit: a picture a panel was painted from counts as drawn on every frame the panel is used, not only
// the frames it's repainted on, so the loader keeps it, and PIC_USE records it, for as long as it's on screen)
const PANEL_PICS = { painting: null, touch: null };
function panel(key, w, h, draw, o = {}) {
  const res = o.res ?? 1, cw = Math.max(1, Math.round(w * res)), ch = Math.max(1, Math.round(h * res));
  let p = PANELS.get(key);
  if (!p || p.c.width !== cw || p.c.height !== ch) {
    if (p) dropTex(p.c);
    const c = makeCanvas(cw, ch);
    p = { c, g: c.getContext('2d'), stamp: undefined };
    PANELS.set(key, p);
  }
  const stamp = o.live ? (QUALITY.liveRate ? `live${Math.floor(T * QUALITY.liveRate)}` : Symbol()) : (o.stamp ?? 0);
  if (p.stamp !== stamp) {
    const g = p.g;
    g.setTransform(1, 0, 0, 1, 0, 0); g.clearRect(0, 0, cw, ch); g.setTransform(res, 0, 0, res, 0, 0);
    g.globalAlpha = 1; g.globalCompositeOperation = 'source-over';
    const outer = PANEL_PICS.painting;
    PANEL_PICS.painting = p.pics = new Set();
    try { draw(g, w, h); } finally { PANEL_PICS.painting = outer; }
    for (const n of p.pics) outer?.add(n);
    p.stamp = stamp;
    return texOf(p.c, true);
  }
  if (p.pics) for (const n of p.pics) { PANEL_PICS.touch?.(n); PANEL_PICS.painting?.add(n); }
  return texOf(p.c);
}

// ---------- post ----------
// GRADE (reset each frame, set by shots): bloom (strength), thresh, knee, expo, vignette, grain, ca (chromatic aberration), flash (0..1
// toward flashCol), fade (to black), sat, lift / gain (colour grade), shoulder (where highlights start rolling off).
const GRADE_DEFAULT = { bloom: .9, thresh: .72, knee: .35, expo: 1, vignette: .45, grain: .035, ca: .006, flash: 0, flashCol: '#FFFFFF', fade: 0, sat: 1, lift: '#000000', gain: '#FFFFFF', shoulder: .78 };
let GRADE = { ...GRADE_DEFAULT };
function fullPass(P, target) {
  gl.bindFramebuffer(gl.FRAMEBUFFER, target ? target.fb : null);
  gl.viewport(0, 0, target ? target.w : PW, target ? target.h : PH);
  gl.useProgram(P.p); gl.bindVertexArray(VAO_EMPTY);
  gl.drawArrays(gl.TRIANGLES, 0, 3);
}
function postProcess() {
  const G = GRADE;
  BLEND.none();
  // bloom down
  let src = SCENE;
  BLOOM.forEach((dst, i) => {
    const P = PROG.down; gl.useProgram(P.p);
    gl.activeTexture(gl.TEXTURE0); gl.bindTexture(gl.TEXTURE_2D, src.tex); gl.uniform1i(P.u.uTex, 0);
    gl.uniform2f(P.u.uTexel, 1 / src.w, 1 / src.h); gl.uniform1i(P.u.uPre, i === 0 ? 1 : 0);
    gl.uniform1f(P.u.uThresh, G.thresh); gl.uniform1f(P.u.uKnee, G.knee);
    fullPass(P, dst); src = dst;
  });
  // bloom up (each level added into the next larger)
  BLEND.add();
  for (let i = BLOOM.length - 1; i > 0; i--) {
    const P = PROG.up; gl.useProgram(P.p);
    gl.activeTexture(gl.TEXTURE0); gl.bindTexture(gl.TEXTURE_2D, BLOOM[i].tex); gl.uniform1i(P.u.uTex, 0);
    gl.uniform2f(P.u.uTexel, 1 / BLOOM[i].w, 1 / BLOOM[i].h); gl.uniform1f(P.u.uK, 1);
    fullPass(P, BLOOM[i - 1]);
  }
  BLEND.none();
  const P = PROG.fin; gl.useProgram(P.p);
  gl.activeTexture(gl.TEXTURE0); gl.bindTexture(gl.TEXTURE_2D, SCENE.tex); gl.uniform1i(P.u.uScene, 0);
  gl.activeTexture(gl.TEXTURE1); gl.bindTexture(gl.TEXTURE_2D, BLOOM[0].tex); gl.uniform1i(P.u.uBloom, 1);
  gl.uniform1f(P.u.uBloomK, G.bloom / Math.max(1, BLOOM.length - 1) * 1.6); gl.uniform1f(P.u.uExpo, G.expo); gl.uniform1f(P.u.uVig, G.vignette);
  gl.uniform1f(P.u.uGrain, G.grain); gl.uniform1f(P.u.uCA, G.ca); gl.uniform1f(P.u.uFlash, G.flash); gl.uniform1f(P.u.uFade, G.fade);
  gl.uniform1f(P.u.uSat, G.sat); gl.uniform1f(P.u.uSeed, (Math.floor(T * 24) * .618) % 1); gl.uniform1f(P.u.uShoulder, G.shoulder);
  u3(P, 'uLift', G.lift); u3(P, 'uGainC', G.gain); u3(P, 'uFlashCol', G.flashCol); gl.uniform2f(P.u.uRes, PW, PH);
  fullPass(P, null);
  // (the layers held back from a scene drawn at less than full resolution, over the finished frame: faded with it, not graded)
  if (_crisp.length) {
    for (const it of _crisp) blitLayer({ ...it, gain: Math.min(it.gain, 1), alpha: it.alpha * (1 - G.fade) });
    _crisp = [];
  }
  gl.activeTexture(gl.TEXTURE0);
}

// ---------- quality levels ----------
// QUALITY_STEPS: the quality levels, which the page's controller steps through when frames reach the screen late (see the site's
// worker.js), each cheaper than the last, the effects simplified before any drop in resolution. The members, the pictures and the
// type keep their full detail at every level, and the type the canvas's full resolution even where the 3D scene's is lowered. Level 0
// is the video as designed, and the only level in render mode (kit.js's setQuality). 1: fewer particles (the glitter, dust, confetti,
// the lightstick ocean); 2: fewer again, and a shorter bloom chain; 3: fewer still, the shortest bloom, and live panels (the LED wall
// carrying the lyric) repainted twelve times a second; 4 and 5: the 3D scene at three quarters and half the canvas's resolution.
const QUALITY_STEPS = [
  { particles: 1, bloomLevels: 6, liveRate: 0, sceneK: 1 },
  { particles: .6, bloomLevels: 6, liveRate: 0, sceneK: 1 },
  { particles: .4, bloomLevels: 4, liveRate: 0, sceneK: 1 },
  { particles: .25, bloomLevels: 3, liveRate: 12, sceneK: 1 },
  { particles: .25, bloomLevels: 3, liveRate: 12, sceneK: .75 },
  { particles: .25, bloomLevels: 3, liveRate: 12, sceneK: .5 },
];
let qualityLevel = 0;
function applyQuality(level) {
  qualityLevel = clamp(Math.round(level), 0, QUALITY_STEPS.length - 1);
  const q = QUALITY_STEPS[qualityLevel], resize = q.bloomLevels !== QUALITY.bloomLevels || q.sceneK !== QUALITY.sceneK;
  Object.assign(QUALITY, q);
  if (resize && SCENE) resizeTargets();
}
// the GPU's work for the frame just drawn, finished (a one-pixel read-back), so that the page's measure of a frame includes it
function finishFrame() { const px = new Uint8Array(4); gl.bindFramebuffer(gl.FRAMEBUFFER, null); gl.readPixels(0, 0, 1, 1, gl.RGBA, gl.UNSIGNED_BYTE, px); }

FRAME_BEGIN.push(() => {
  _layerN = 0; GRADE = { ...GRADE_DEFAULT }; _crisp = [];
  cam();
  bindScene(); gl.clearColor(0, 0, 0, 1); gl.clear(gl.COLOR_BUFFER_BIT);
});
FRAME_END.push(() => postProcess());
if (!CANVAS_LAYERS) FRAME_END.push(() => D2.endFrame());

;
// ---- styles/idolfilm/kit.js ----
// kit.js: the idolfilm style's look, on top of gl.js. ATTN!'s comeback, told as its own rollout, in one system: an ink-black stage world
// and a pearl-white studio, lit with bloom and particles; image-generated members composited into them as cut-outs; lyrics as
// word-timed kinetic type; each reference carried by one iconic image, usually inside a believable interface. Read STYLE.md first.

// =====================================================================================================
// PALETTE, MEMBERS, LINE DISTRIBUTION, FONTS
// =====================================================================================================
// One restrained system: ink and night for the stage, pearl for the studio and for light, chrome for hardware, and one accent per
// shot: the colour of the member singing the line (all four only when the whole group is on).
const PAL = {
  ink: '#06050B', night: '#100D1C', haze: '#1E1834', plum: '#2A2046', pearl: '#F4F0FA', pearl2: '#E3DDEC', cove: '#EAE5F1',
  chrome: '#BCC0D2', dim: '#8C86A2', text: '#0D0B16', white: '#FFFFFF',
};
const MEM = {
  TOKI: { key: 'TOKI', col: '#FF4FA8', glow: '#FF9ACF', soft: '#FFD6EB', role: 'LEADER · MAIN VOCAL' },
  RELU: { key: 'RELU', col: '#1FD6A8', glow: '#86F4D5', soft: '#CDF6EA', role: 'MAIN DANCER · SUB VOCAL' },
  ADA: { key: 'ADA', col: '#8F63FF', glow: '#BDA4FF', soft: '#E2D8FF', role: 'LEAD VOCAL' },
  LOGI: { key: 'LOGI', col: '#FFB321', glow: '#FFD27A', soft: '#FFEBC4', role: 'MAIN RAPPER · MAKNAE' },
};
const ORDER = ['TOKI', 'RELU', 'ADA', 'LOGI'];
// Line distribution: verse lines go to the members in couplets (a K-pop "part"), each verse starting one member further on; choruses
// are the whole group's.
const VERSE_LEAD = { V1: 0, V2: 1, V3: 2, V4: 3 };
const singerOf = (sec, n) => sec in VERSE_LEAD ? ORDER[(VERSE_LEAD[sec] + Math.floor((n - 1) / 2)) % 4] : null;
const singerAt = s => s && s.kind === 'line' ? singerOf(s.sec, s.n) : null;

// FONTS: every family the style draws with (the studio loads them before the first frame; the site's worker must list the same).
const FONT = {
  display: 'Unbounded Black', wide: 'Unbounded Light', serif: 'Instrument Serif', serifI: 'Instrument Serif Italic',
  cond: 'Anton', mono: 'Space Mono', ui: 'Inter Medium', uiB: 'Inter ExtraBold', hand: 'Rock Salt',
};
const FONTS = FONT;

// =====================================================================================================
// PICTURES
// =====================================================================================================
// The manifest is written by tools/images.py build: layer ('cutout' has alpha and is trimmed to it; 'full' fills a frame), w and h.
// <pics: generated by tools/images.py build>
const PICS = {
  "toki_concept": {"layer": "cutout", "w": 535, "h": 1600, "anchor": [0.5, 1], "lo": [905, 1446, 33, 100]},
  "toki_point": {"layer": "cutout", "w": 600, "h": 1600, "anchor": [0.5, 1], "lo": [940, 1446, 38, 100]},
  "relu_concept": {"layer": "cutout", "w": 563, "h": 1600, "anchor": [0.5, 1], "lo": [980, 1446, 35, 100]},
  "relu_point": {"layer": "cutout", "w": 571, "h": 1600, "anchor": [0.5, 1], "lo": [0, 1560, 36, 100]},
  "ada_concept": {"layer": "cutout", "w": 522, "h": 1600, "anchor": [0.5, 1], "lo": [38, 1560, 33, 100]},
  "ada_point": {"layer": "cutout", "w": 642, "h": 1600, "anchor": [0.5, 1], "lo": [73, 1560, 40, 100]},
  "logi_concept": {"layer": "cutout", "w": 582, "h": 1600, "anchor": [0.5, 1], "lo": [115, 1560, 36, 100]},
  "logi_point": {"layer": "cutout", "w": 640, "h": 1600, "anchor": [0.5, 1], "lo": [153, 1560, 40, 100]},
  "toki_fairy": {"layer": "cutout", "w": 1203, "h": 1600, "lo": [195, 1560, 75, 100]},
  "toki_sing": {"layer": "cutout", "w": 1183, "h": 1600, "lo": [272, 1560, 74, 100]},
  "relu_eye": {"layer": "full", "w": 2150, "h": 1200, "lo": [161, 2056, 134, 75]},
  "clawd_fan": {"layer": "cutout", "w": 1670, "h": 1364, "lo": [661, 1964, 104, 85]},
  "clawd_cry": {"layer": "cutout", "w": 1246, "h": 1250, "lo": [0, 2056, 78, 78]},
  "card_hinton": {"layer": "full", "w": 805, "h": 1200, "lo": [297, 2056, 50, 75]},
  "card_demis": {"layer": "full", "w": 805, "h": 1200, "lo": [349, 2056, 50, 75]},
  "toki_win": {"layer": "cutout", "w": 667, "h": 1600, "anchor": [0.5, 1], "lo": [348, 1560, 42, 100]},
  "sam_portrait": {"layer": "full", "w": 800, "h": 800, "anchor": [0.5, 1], "lo": [524, 2056, 50, 50]},
  "sam_facepalm": {"layer": "cutout", "w": 511, "h": 1600, "anchor": [0.5, 1], "lo": [392, 1560, 32, 100]},
  "elon_portrait": {"layer": "full", "w": 800, "h": 800, "anchor": [0.5, 1], "lo": [576, 2056, 50, 50]},
  "trump": {"layer": "cutout", "w": 750, "h": 1600, "anchor": [0.5, 1], "lo": [426, 1560, 47, 100]},
  "jensen": {"layer": "cutout", "w": 954, "h": 1600, "anchor": [0.5, 1], "lo": [475, 1560, 60, 100]},
  "pew_pair": {"layer": "cutout", "w": 2228, "h": 1427, "anchor": [0.5, 1], "lo": [414, 1964, 139, 89]},
  "yann": {"layer": "cutout", "w": 725, "h": 1600, "anchor": [0.5, 1], "lo": [653, 1560, 45, 100]},
  "noam_ox": {"layer": "cutout", "w": 763, "h": 1600, "anchor": [0.5, 1], "lo": [782, 1560, 48, 100]},
  "jeff": {"layer": "cutout", "w": 920, "h": 1600, "anchor": [0.5, 1], "lo": [832, 1560, 58, 100]},
  "greg": {"layer": "cutout", "w": 1469, "h": 1257, "anchor": [0.5, 1], "lo": [860, 1964, 92, 79]},
  "dario": {"layer": "cutout", "w": 944, "h": 1600, "anchor": [0.5, 1], "lo": [892, 1560, 59, 100]},
  "zuck": {"layer": "cutout", "w": 940, "h": 1600, "anchor": [0.5, 1], "lo": [953, 1560, 59, 100]},
  "lutnick": {"layer": "cutout", "w": 616, "h": 1600, "anchor": [0.5, 1], "lo": [0, 1662, 38, 100]},
  "relu_sing": {"layer": "cutout", "w": 1026, "h": 1600, "lo": [40, 1662, 64, 100]},
  "ada_sing": {"layer": "cutout", "w": 1168, "h": 1600, "lo": [106, 1662, 73, 100]},
  "logi_sing": {"layer": "cutout", "w": 1195, "h": 1600, "lo": [181, 1662, 75, 100]},
  "toki_react": {"layer": "cutout", "w": 1162, "h": 1600, "lo": [258, 1662, 73, 100]},
  "ada_react": {"layer": "cutout", "w": 1165, "h": 1600, "lo": [393, 1662, 73, 100]},
  "logi_react": {"layer": "cutout", "w": 1126, "h": 1600, "lo": [468, 1662, 70, 100]},
  "clawd_mic": {"layer": "cutout", "w": 1454, "h": 1365, "anchor": [0.5, 1], "lo": [767, 1964, 91, 85]},
  "clawd_chalk": {"layer": "cutout", "w": 1271, "h": 1247, "anchor": [0.5, 1], "lo": [80, 2056, 79, 78]},
  "clawd_build": {"layer": "cutout", "w": 1672, "h": 1408, "anchor": [0.5, 1], "lo": [555, 1964, 104, 88]},
  "lobster": {"layer": "cutout", "w": 1332, "h": 1600, "anchor": [0.5, 1], "lo": [540, 1662, 83, 100]},
  "robot": {"layer": "cutout", "w": 1355, "h": 1435, "anchor": [0.5, 1], "lo": [392, 1864, 85, 90]},
  "park": {"layer": "full", "w": 1935, "h": 1080, "lo": [401, 2056, 121, 68]},
  "toki_fairy_blink": {"layer": "cutout", "w": 1203, "h": 1600, "lo": [625, 1662, 75, 100]},
  "toki_v_ah": {"layer": "patch", "of": "toki_sing", "x": 422, "y": 508, "w": 243, "h": 179, "lo": [739, 2056, 15, 11]},
  "toki_v_ee": {"layer": "patch", "of": "toki_sing", "x": 422, "y": 508, "w": 243, "h": 179, "lo": [756, 2056, 15, 11]},
  "toki_v_oh": {"layer": "patch", "of": "toki_sing", "x": 422, "y": 508, "w": 243, "h": 179, "lo": [790, 2056, 15, 11]},
  "toki_v_hum": {"layer": "patch", "of": "toki_sing", "x": 422, "y": 508, "w": 243, "h": 179, "lo": [807, 2056, 15, 11]},
  "toki_v_mb": {"layer": "patch", "of": "toki_sing", "x": 422, "y": 508, "w": 243, "h": 179, "lo": [824, 2056, 15, 11]},
  "relu_v_ah": {"layer": "patch", "of": "relu_sing", "x": 474, "y": 649, "w": 249, "h": 171, "lo": [858, 2056, 16, 11]},
  "relu_v_ee": {"layer": "patch", "of": "relu_sing", "x": 474, "y": 649, "w": 249, "h": 171, "lo": [876, 2056, 16, 11]},
  "relu_v_oh": {"layer": "patch", "of": "relu_sing", "x": 474, "y": 649, "w": 249, "h": 171, "lo": [912, 2056, 16, 11]},
  "relu_v_hum": {"layer": "patch", "of": "relu_sing", "x": 474, "y": 649, "w": 249, "h": 171, "lo": [930, 2056, 16, 11]},
  "relu_v_mb": {"layer": "patch", "of": "relu_sing", "x": 474, "y": 649, "w": 249, "h": 171, "lo": [948, 2056, 16, 11]},
  "ada_v_ah": {"layer": "patch", "of": "ada_sing", "x": 415, "y": 479, "w": 244, "h": 168, "lo": [85, 2136, 15, 10]},
  "ada_v_ee": {"layer": "patch", "of": "ada_sing", "x": 415, "y": 479, "w": 244, "h": 168, "lo": [102, 2136, 15, 10]},
  "ada_v_oh": {"layer": "patch", "of": "ada_sing", "x": 415, "y": 479, "w": 244, "h": 168, "lo": [136, 2136, 15, 10]},
  "ada_v_hum": {"layer": "patch", "of": "ada_sing", "x": 415, "y": 479, "w": 244, "h": 168, "lo": [153, 2136, 15, 10]},
  "ada_v_mb": {"layer": "patch", "of": "ada_sing", "x": 415, "y": 479, "w": 244, "h": 168, "lo": [170, 2136, 15, 10]},
  "ada_v_held": {"layer": "patch", "of": "ada_sing", "x": 329, "y": 279, "w": 415, "h": 385, "lo": [684, 2056, 26, 24]},
  "logi_v_ah": {"layer": "patch", "of": "logi_sing", "x": 399, "y": 568, "w": 239, "h": 176, "lo": [984, 2056, 15, 11]},
  "logi_v_ee": {"layer": "patch", "of": "logi_sing", "x": 399, "y": 568, "w": 239, "h": 176, "lo": [1001, 2056, 15, 11]},
  "logi_v_oh": {"layer": "patch", "of": "logi_sing", "x": 399, "y": 568, "w": 239, "h": 176, "lo": [17, 2136, 15, 11]},
  "logi_v_hum": {"layer": "patch", "of": "logi_sing", "x": 399, "y": 568, "w": 239, "h": 176, "lo": [34, 2136, 15, 11]},
  "logi_v_mb": {"layer": "patch", "of": "logi_sing", "x": 399, "y": 568, "w": 239, "h": 176, "lo": [51, 2136, 15, 11]},
  "toki_u1_s0": {"layer": "sprite", "w": 1176, "h": 1560, "lo": [702, 1662, 74, 98]},
  "toki_u1_s1": {"layer": "sprite", "w": 1176, "h": 1560, "lo": [778, 1662, 74, 98]},
  "toki_u1_s2": {"layer": "sprite", "w": 1176, "h": 1560, "lo": [854, 1662, 74, 98]},
  "toki_u1_s3": {"layer": "sprite", "w": 1176, "h": 1560, "lo": [930, 1662, 74, 98]},
  "relu_u1_s0": {"layer": "sprite", "w": 1176, "h": 1560, "lo": [0, 1764, 74, 98]},
  "relu_u1_s1": {"layer": "sprite", "w": 1176, "h": 1560, "lo": [76, 1764, 74, 98]},
  "relu_u1_s2": {"layer": "sprite", "w": 1176, "h": 1560, "lo": [152, 1764, 74, 98]},
  "relu_u1_s3": {"layer": "sprite", "w": 1176, "h": 1560, "lo": [228, 1764, 74, 98]},
  "ada_u1_s0": {"layer": "sprite", "w": 1176, "h": 1560, "lo": [304, 1764, 74, 98]},
  "ada_u1_s1": {"layer": "sprite", "w": 1176, "h": 1560, "lo": [380, 1764, 74, 98]},
  "ada_u1_s2": {"layer": "sprite", "w": 1176, "h": 1560, "lo": [456, 1764, 74, 98]},
  "ada_u1_s3": {"layer": "sprite", "w": 1176, "h": 1560, "lo": [532, 1764, 74, 98]},
  "logi_u1_s0": {"layer": "sprite", "w": 1176, "h": 1560, "lo": [608, 1764, 74, 98]},
  "logi_u1_s1": {"layer": "sprite", "w": 1176, "h": 1560, "lo": [684, 1764, 74, 98]},
  "logi_u1_s2": {"layer": "sprite", "w": 1176, "h": 1560, "lo": [760, 1764, 74, 98]},
  "logi_u1_s3": {"layer": "sprite", "w": 1176, "h": 1560, "lo": [836, 1764, 74, 98]},
  "toki_pose_s0": {"layer": "sprite", "w": 1812, "h": 2400, "lo": [908, 361, 113, 150]},
  "toki_pose_s1": {"layer": "sprite", "w": 1812, "h": 2400, "lo": [0, 528, 113, 150]},
  "relu_pose_s0": {"layer": "sprite", "w": 1452, "h": 2400, "lo": [115, 528, 91, 150]},
  "relu_pose_s1": {"layer": "sprite", "w": 1452, "h": 2400, "lo": [208, 528, 91, 150]},
  "ada_pose_s0": {"layer": "sprite", "w": 1780, "h": 2400, "lo": [301, 528, 111, 150]},
  "ada_pose_s1": {"layer": "sprite", "w": 1780, "h": 2400, "lo": [414, 528, 111, 150]},
  "ada_pose2_s0": {"layer": "sprite", "w": 2180, "h": 2580, "lo": [632, 361, 136, 161]},
  "ada_pose2_s1": {"layer": "sprite", "w": 2180, "h": 2580, "lo": [770, 361, 136, 161]},
  "logi_dance_s0": {"layer": "sprite", "w": 1780, "h": 2400, "lo": [527, 528, 111, 150]},
  "logi_dance_s1": {"layer": "sprite", "w": 1780, "h": 2400, "lo": [640, 528, 111, 150]},
  "logi_dance2_s0": {"layer": "sprite", "w": 2528, "h": 2700, "lo": [561, 0, 158, 169]},
  "logi_dance2_s1": {"layer": "sprite", "w": 2528, "h": 2700, "lo": [721, 0, 158, 169]},
  "relu_press_s0": {"layer": "sprite", "w": 1544, "h": 2400, "lo": [753, 528, 96, 150]},
  "logi_host_s1": {"layer": "sprite", "w": 1636, "h": 2400, "lo": [104, 680, 102, 150]},
  "logi_host_s2": {"layer": "sprite", "w": 1636, "h": 2400, "lo": [208, 680, 102, 150]},
  "toki_tears_s0": {"layer": "sprite", "w": 2012, "h": 2700, "lo": [881, 0, 126, 169]},
  "toki_tears_s1": {"layer": "sprite", "w": 2012, "h": 2700, "lo": [0, 190, 126, 169]},
  "group_pose_s0": {"layer": "sprite", "w": 3112, "h": 1560, "lo": [0, 1864, 194, 98]},
  "group_pose_s1": {"layer": "sprite", "w": 3112, "h": 1560, "lo": [196, 1864, 194, 98]},
  "group_win_s0": {"layer": "sprite", "w": 2600, "h": 1800, "lo": [702, 1328, 162, 112]},
  "group_win_s1": {"layer": "sprite", "w": 2600, "h": 1800, "lo": [0, 1446, 162, 112]},
  "group_wave_s0": {"layer": "sprite", "w": 3284, "h": 1440, "lo": [479, 1864, 205, 90]},
  "group_wave_s1": {"layer": "sprite", "w": 3284, "h": 1440, "lo": [686, 1864, 205, 90]},
  "group_wave_s2": {"layer": "sprite", "w": 3284, "h": 1440, "lo": [0, 1964, 205, 90]},
  "group_wave_s3": {"layer": "sprite", "w": 3284, "h": 1440, "lo": [207, 1964, 205, 90]},
  "toki_fairy15_s0": {"layer": "sprite", "w": 2600, "h": 2640, "lo": [228, 190, 162, 165]},
  "toki_fairy15_s1": {"layer": "sprite", "w": 2600, "h": 2640, "lo": [392, 190, 162, 165]},
  "toki_fairy15_s2": {"layer": "sprite", "w": 2600, "h": 2640, "lo": [556, 190, 162, 165]},
  "toki_uG_s0": {"layer": "sprite", "w": 1844, "h": 1860, "lo": [212, 962, 115, 116]},
  "toki_uG_s1": {"layer": "sprite", "w": 1844, "h": 1860, "lo": [329, 962, 115, 116]},
  "toki_uG_s2": {"layer": "sprite", "w": 1844, "h": 1860, "lo": [446, 962, 115, 116]},
  "toki_uG_s3": {"layer": "sprite", "w": 1844, "h": 1860, "lo": [563, 962, 115, 116]},
  "relu_uG_s0": {"layer": "sprite", "w": 1844, "h": 1860, "lo": [680, 962, 115, 116]},
  "relu_uG_s1": {"layer": "sprite", "w": 1844, "h": 1860, "lo": [797, 962, 115, 116]},
  "relu_uG_s2": {"layer": "sprite", "w": 1844, "h": 1860, "lo": [0, 1092, 115, 116]},
  "relu_uG_s3": {"layer": "sprite", "w": 1844, "h": 1860, "lo": [117, 1092, 115, 116]},
  "ada_uG_s0": {"layer": "sprite", "w": 1844, "h": 1860, "lo": [234, 1092, 115, 116]},
  "ada_uG_s1": {"layer": "sprite", "w": 1844, "h": 1860, "lo": [351, 1092, 115, 116]},
  "ada_uG_s2": {"layer": "sprite", "w": 1844, "h": 1860, "lo": [468, 1092, 115, 116]},
  "ada_uG_s3": {"layer": "sprite", "w": 1844, "h": 1860, "lo": [585, 1092, 115, 116]},
  "logi_uG_s0": {"layer": "sprite", "w": 1844, "h": 1860, "lo": [702, 1092, 115, 116]},
  "logi_uG_s1": {"layer": "sprite", "w": 1844, "h": 1860, "lo": [819, 1092, 115, 116]},
  "logi_uG_s2": {"layer": "sprite", "w": 1844, "h": 1860, "lo": [0, 1210, 115, 116]},
  "logi_uG_s3": {"layer": "sprite", "w": 1844, "h": 1860, "lo": [117, 1210, 115, 116]},
  "toki_uT_s0": {"layer": "sprite", "w": 1844, "h": 1860, "lo": [234, 1210, 115, 116]},
  "toki_uT_s1": {"layer": "sprite", "w": 1844, "h": 1860, "lo": [351, 1210, 115, 116]},
  "toki_uT_s2": {"layer": "sprite", "w": 1844, "h": 1860, "lo": [468, 1210, 115, 116]},
  "relu_uT_s0": {"layer": "sprite", "w": 1844, "h": 1860, "lo": [585, 1210, 115, 116]},
  "relu_uT_s1": {"layer": "sprite", "w": 1844, "h": 1860, "lo": [702, 1210, 115, 116]},
  "relu_uT_s2": {"layer": "sprite", "w": 1844, "h": 1860, "lo": [819, 1210, 115, 116]},
  "ada_uT_s0": {"layer": "sprite", "w": 1844, "h": 1860, "lo": [0, 1328, 115, 116]},
  "ada_uT_s1": {"layer": "sprite", "w": 1844, "h": 1860, "lo": [117, 1328, 115, 116]},
  "ada_uT_s2": {"layer": "sprite", "w": 1844, "h": 1860, "lo": [234, 1328, 115, 116]},
  "logi_uT_s0": {"layer": "sprite", "w": 1844, "h": 1860, "lo": [351, 1328, 115, 116]},
  "logi_uT_s1": {"layer": "sprite", "w": 1844, "h": 1860, "lo": [468, 1328, 115, 116]},
  "logi_uT_s2": {"layer": "sprite", "w": 1844, "h": 1860, "lo": [585, 1328, 115, 116]},
  "toki_uC_s0": {"layer": "sprite", "w": 1660, "h": 2040, "lo": [410, 680, 104, 128]},
  "toki_uC_s1": {"layer": "sprite", "w": 1660, "h": 2040, "lo": [516, 680, 104, 128]},
  "toki_uC_s2": {"layer": "sprite", "w": 1660, "h": 2040, "lo": [622, 680, 104, 128]},
  "toki_uC_s3": {"layer": "sprite", "w": 1660, "h": 2040, "lo": [728, 680, 104, 128]},
  "relu_uC_s0": {"layer": "sprite", "w": 1660, "h": 2040, "lo": [834, 680, 104, 128]},
  "relu_uC_s1": {"layer": "sprite", "w": 1660, "h": 2040, "lo": [0, 832, 104, 128]},
  "relu_uC_s2": {"layer": "sprite", "w": 1660, "h": 2040, "lo": [106, 832, 104, 128]},
  "relu_uC_s3": {"layer": "sprite", "w": 1660, "h": 2040, "lo": [212, 832, 104, 128]},
  "ada_uC_s0": {"layer": "sprite", "w": 1660, "h": 2040, "lo": [318, 832, 104, 128]},
  "ada_uC_s1": {"layer": "sprite", "w": 1660, "h": 2040, "lo": [424, 832, 104, 128]},
  "ada_uC_s2": {"layer": "sprite", "w": 1660, "h": 2040, "lo": [530, 832, 104, 128]},
  "ada_uC_s3": {"layer": "sprite", "w": 1660, "h": 2040, "lo": [636, 832, 104, 128]},
  "logi_uC_s0": {"layer": "sprite", "w": 1660, "h": 2040, "lo": [742, 832, 104, 128]},
  "logi_uC_s1": {"layer": "sprite", "w": 1660, "h": 2040, "lo": [848, 832, 104, 128]},
  "logi_uC_s2": {"layer": "sprite", "w": 1660, "h": 2040, "lo": [0, 962, 104, 128]},
  "logi_uC_s3": {"layer": "sprite", "w": 1660, "h": 2040, "lo": [106, 962, 104, 128]},
  "relu_grok_s0": {"layer": "sprite", "w": 2472, "h": 2640, "lo": [164, 361, 154, 165]},
  "relu_grok_s1": {"layer": "sprite", "w": 2472, "h": 2640, "lo": [320, 361, 154, 165]},
  "relu_grok_s2": {"layer": "sprite", "w": 2472, "h": 2640, "lo": [476, 361, 154, 165]},
  "relu_fancam_s0": {"layer": "sprite", "w": 2960, "h": 3000, "lo": [0, 0, 185, 188]},
  "relu_fancam_s1": {"layer": "sprite", "w": 2960, "h": 3000, "lo": [187, 0, 185, 188]},
  "toki_smile_s0": {"layer": "sprite", "w": 1144, "h": 1680, "lo": [164, 1446, 72, 105]},
  "relu_smile_s0": {"layer": "sprite", "w": 1572, "h": 2700, "lo": [128, 190, 98, 169]},
  "ada_smile_s0": {"layer": "sprite", "w": 948, "h": 1680, "lo": [238, 1446, 59, 105]},
  "logi_smile_s0": {"layer": "sprite", "w": 1080, "h": 1680, "lo": [299, 1446, 68, 105]},
  "toki_fansign_s0": {"layer": "sprite", "w": 1144, "h": 1680, "lo": [369, 1446, 72, 105]},
  "toki_fansign_s1": {"layer": "sprite", "w": 1144, "h": 1680, "lo": [443, 1446, 72, 105]},
  "relu_fansign_s0": {"layer": "sprite", "w": 980, "h": 1680, "lo": [517, 1446, 61, 105]},
  "relu_fansign_s1": {"layer": "sprite", "w": 980, "h": 1680, "lo": [580, 1446, 61, 105]},
  "ada_fansign_s0": {"layer": "sprite", "w": 948, "h": 1680, "lo": [643, 1446, 59, 105]},
  "ada_fansign_s1": {"layer": "sprite", "w": 948, "h": 1680, "lo": [704, 1446, 59, 105]},
  "logi_fansign_s0": {"layer": "sprite", "w": 1080, "h": 1680, "lo": [765, 1446, 68, 105]},
  "logi_fansign_s1": {"layer": "sprite", "w": 1080, "h": 1680, "lo": [835, 1446, 68, 105]},
  "relu_shock_s0": {"layer": "sprite", "w": 1544, "h": 2400, "lo": [312, 680, 96, 150]},
};
// </pics>
// Sprite clips (tools/images.py sprite): a Veo-generated dance, matted and packed into one-second sheets, each sheet a picture in
// PICS (so the loader streams them like any other). frames at 12 fps (anime "on twos"), `per` to a sheet in a cols × rows grid.
// <sprites: generated by tools/images.py build>
const SPRITES = {
  "toki_u1": {"frames": 48, "per": 12, "cols": 4, "rows": 3, "fw": 294, "fh": 520, "sheets": ["toki_u1_s0", "toki_u1_s1", "toki_u1_s2", "toki_u1_s3"], "box": [0, 0, 480, 848], "src": [480, 848], "fig": 0.9175, "hk": 1.0029},
  "relu_u1": {"frames": 48, "per": 12, "cols": 4, "rows": 3, "fw": 294, "fh": 520, "sheets": ["relu_u1_s0", "relu_u1_s1", "relu_u1_s2", "relu_u1_s3"], "box": [0, 0, 480, 848], "src": [480, 848], "fig": 0.8903, "hk": 1.0029},
  "ada_u1": {"frames": 48, "per": 12, "cols": 4, "rows": 3, "fw": 294, "fh": 520, "sheets": ["ada_u1_s0", "ada_u1_s1", "ada_u1_s2", "ada_u1_s3"], "box": [0, 0, 480, 848], "src": [480, 848], "fig": 0.9481, "hk": 1.0029},
  "logi_u1": {"frames": 48, "per": 12, "cols": 4, "rows": 3, "fw": 294, "fh": 520, "sheets": ["logi_u1_s0", "logi_u1_s1", "logi_u1_s2", "logi_u1_s3"], "box": [0, 0, 480, 848], "src": [480, 848], "fig": 0.9534, "hk": 1.0029},
  "toki_pose": {"frames": 24, "per": 12, "cols": 4, "rows": 3, "fw": 453, "fh": 800, "sheets": ["toki_pose_s0", "toki_pose_s1"], "box": [0, 0, 704, 1244], "src": [704, 1280], "fig": 0.9016},
  "relu_pose": {"frames": 22, "per": 12, "cols": 4, "rows": 3, "fw": 363, "fh": 800, "sheets": ["relu_pose_s0", "relu_pose_s1"], "box": [74, 35, 624, 1246], "src": [704, 1280], "fig": 0.8953},
  "ada_pose": {"frames": 24, "per": 12, "cols": 4, "rows": 3, "fw": 445, "fh": 800, "sheets": ["ada_pose_s0", "ada_pose_s1"], "box": [0, 0, 704, 1266], "src": [704, 1280], "fig": 0.9516},
  "ada_pose2": {"frames": 22, "per": 12, "cols": 4, "rows": 3, "fw": 545, "fh": 860, "sheets": ["ada_pose2_s0", "ada_pose2_s1"], "box": [204, 507, 1005, 1770], "src": [1080, 1920], "fig": 0.5997},
  "logi_dance": {"frames": 20, "per": 12, "cols": 4, "rows": 3, "fw": 445, "fh": 800, "sheets": ["logi_dance_s0", "logi_dance_s1"], "box": [0, 0, 704, 1267], "src": [704, 1280], "fig": 0.9391},
  "logi_dance2": {"frames": 24, "per": 12, "cols": 4, "rows": 3, "fw": 632, "fh": 900, "sheets": ["logi_dance2_s0", "logi_dance2_s1"], "box": [112, 369, 1001, 1635], "src": [1080, 1920], "fig": 0.5352},
  "relu_press": {"frames": 18, "per": 12, "cols": 4, "rows": 3, "fw": 386, "fh": 800, "sheets": ["relu_press_s0", "relu_press_s1"], "box": [42, 35, 628, 1250], "src": [704, 1280], "fig": 0.8996},
  "logi_host": {"frames": 36, "per": 12, "cols": 4, "rows": 3, "fw": 409, "fh": 800, "sheets": ["logi_host_s0", "logi_host_s1", "logi_host_s2"], "box": [51, 0, 701, 1271], "src": [704, 1280], "fig": 0.9387},
  "toki_tears": {"frames": 24, "per": 12, "cols": 4, "rows": 3, "fw": 503, "fh": 900, "sheets": ["toki_tears_s0", "toki_tears_s1"], "box": [0, 15, 702, 1271], "src": [704, 1280], "fig": 0.9406},
  "group_pose": {"frames": 24, "per": 12, "cols": 4, "rows": 3, "fw": 778, "fh": 520, "sheets": ["group_pose_s0", "group_pose_s1"], "box": [290, 121, 1630, 1017], "src": [1920, 1080], "fig": 0.7833},
  "group_win": {"frames": 24, "per": 12, "cols": 4, "rows": 3, "fw": 650, "fh": 600, "sheets": ["group_win_s0", "group_win_s1"], "box": [306, 44, 1387, 1042], "src": [1920, 1080], "fig": 0.8741},
  "group_wave": {"frames": 48, "per": 12, "cols": 4, "rows": 3, "fw": 821, "fh": 480, "sheets": ["group_wave_s0", "group_wave_s1", "group_wave_s2", "group_wave_s3"], "box": [77, 58, 1717, 1017], "src": [1920, 1080], "fig": 0.7912},
  "toki_fairy15": {"frames": 60, "per": 12, "cols": 4, "rows": 3, "fw": 650, "fh": 880, "sheets": ["toki_fairy15_s0", "toki_fairy15_s1", "toki_fairy15_s2", "toki_fairy15_s3", "toki_fairy15_s4"], "box": [0, 0, 816, 1104], "src": [816, 1104], "fig": 0.9665, "fps": 4},
  "toki_uG": {"frames": 44, "per": 12, "cols": 4, "rows": 3, "fw": 461, "fh": 620, "sheets": ["toki_uG_s0", "toki_uG_s1", "toki_uG_s2", "toki_uG_s3"], "box": [22, 27, 700, 939], "src": [720, 960], "fig": 0.725, "hk": 1.2265},
  "relu_uG": {"frames": 44, "per": 12, "cols": 4, "rows": 3, "fw": 461, "fh": 620, "sheets": ["relu_uG_s0", "relu_uG_s1", "relu_uG_s2", "relu_uG_s3"], "box": [22, 27, 700, 939], "src": [720, 960], "fig": 0.7193, "hk": 1.2265},
  "ada_uG": {"frames": 44, "per": 12, "cols": 4, "rows": 3, "fw": 461, "fh": 620, "sheets": ["ada_uG_s0", "ada_uG_s1", "ada_uG_s2", "ada_uG_s3"], "box": [22, 27, 700, 939], "src": [720, 960], "fig": 0.7203, "hk": 1.2265},
  "logi_uG": {"frames": 44, "per": 12, "cols": 4, "rows": 3, "fw": 461, "fh": 620, "sheets": ["logi_uG_s0", "logi_uG_s1", "logi_uG_s2", "logi_uG_s3"], "box": [22, 27, 700, 939], "src": [720, 960], "fig": 0.7167, "hk": 1.2265},
  "toki_uT": {"frames": 32, "per": 12, "cols": 4, "rows": 3, "fw": 461, "fh": 620, "sheets": ["toki_uT_s0", "toki_uT_s1", "toki_uT_s2"], "box": [22, 27, 700, 939], "src": [720, 960], "fig": 0.7203, "hk": 1.233},
  "relu_uT": {"frames": 32, "per": 12, "cols": 4, "rows": 3, "fw": 461, "fh": 620, "sheets": ["relu_uT_s0", "relu_uT_s1", "relu_uT_s2"], "box": [22, 27, 700, 939], "src": [720, 960], "fig": 0.713, "hk": 1.233},
  "ada_uT": {"frames": 32, "per": 12, "cols": 4, "rows": 3, "fw": 461, "fh": 620, "sheets": ["ada_uT_s0", "ada_uT_s1", "ada_uT_s2"], "box": [22, 27, 700, 939], "src": [720, 960], "fig": 0.7156, "hk": 1.233},
  "logi_uT": {"frames": 32, "per": 12, "cols": 4, "rows": 3, "fw": 461, "fh": 620, "sheets": ["logi_uT_s0", "logi_uT_s1", "logi_uT_s2"], "box": [22, 27, 700, 939], "src": [720, 960], "fig": 0.7172, "hk": 1.233},
  "toki_uC": {"frames": 48, "per": 12, "cols": 4, "rows": 3, "fw": 415, "fh": 680, "sheets": ["toki_uC_s0", "toki_uC_s1", "toki_uC_s2", "toki_uC_s3"], "box": [83, 26, 640, 938], "src": [720, 960], "fig": 0.6484, "hk": 1.3789},
  "relu_uC": {"frames": 48, "per": 12, "cols": 4, "rows": 3, "fw": 415, "fh": 680, "sheets": ["relu_uC_s0", "relu_uC_s1", "relu_uC_s2", "relu_uC_s3"], "box": [83, 26, 640, 938], "src": [720, 960], "fig": 0.6323, "hk": 1.3789},
  "ada_uC": {"frames": 48, "per": 12, "cols": 4, "rows": 3, "fw": 415, "fh": 680, "sheets": ["ada_uC_s0", "ada_uC_s1", "ada_uC_s2", "ada_uC_s3"], "box": [83, 26, 640, 938], "src": [720, 960], "fig": 0.6365, "hk": 1.3789},
  "logi_uC": {"frames": 48, "per": 12, "cols": 4, "rows": 3, "fw": 415, "fh": 680, "sheets": ["logi_uC_s0", "logi_uC_s1", "logi_uC_s2", "logi_uC_s3"], "box": [83, 26, 640, 938], "src": [720, 960], "fig": 0.6458, "hk": 1.3789},
  "relu_grok": {"frames": 32, "per": 12, "cols": 4, "rows": 3, "fw": 618, "fh": 880, "sheets": ["relu_grok_s0", "relu_grok_s1", "relu_grok_s2"], "box": [149, 412, 1001, 1626], "src": [1080, 1920], "fig": 0.518},
  "relu_fancam": {"frames": 32, "per": 12, "cols": 4, "rows": 3, "fw": 740, "fh": 1000, "sheets": ["relu_fancam_s0", "relu_fancam_s1", "relu_fancam_s2"], "box": [70, 304, 1010, 1574], "src": [1080, 1920], "fig": 0.4938},
  "toki_smile": {"frames": 12, "per": 12, "cols": 4, "rows": 3, "fw": 286, "fh": 560, "sheets": ["toki_smile_s0"], "box": [31, 0, 684, 1280], "src": [704, 1280], "fig": 0.9117},
  "relu_smile": {"frames": 12, "per": 12, "cols": 4, "rows": 3, "fw": 393, "fh": 900, "sheets": ["relu_smile_s0"], "box": [79, 42, 604, 1243], "src": [704, 1280], "fig": 0.8953},
  "ada_smile": {"frames": 12, "per": 12, "cols": 4, "rows": 3, "fw": 237, "fh": 560, "sheets": ["ada_smile_s0"], "box": [59, 0, 594, 1263], "src": [704, 1280], "fig": 0.9234},
  "logi_smile": {"frames": 12, "per": 12, "cols": 4, "rows": 3, "fw": 270, "fh": 560, "sheets": ["logi_smile_s0"], "box": [92, 0, 704, 1268], "src": [704, 1280], "fig": 0.9477},
  "toki_fansign": {"frames": 24, "per": 12, "cols": 4, "rows": 3, "fw": 286, "fh": 560, "sheets": ["toki_fansign_s0", "toki_fansign_s1"], "box": [31, 0, 684, 1280], "src": [704, 1280], "fig": 0.8758},
  "relu_fansign": {"frames": 24, "per": 12, "cols": 4, "rows": 3, "fw": 245, "fh": 560, "sheets": ["relu_fansign_s0", "relu_fansign_s1"], "box": [79, 42, 604, 1243], "src": [704, 1280], "fig": 0.8438},
  "ada_fansign": {"frames": 24, "per": 12, "cols": 4, "rows": 3, "fw": 237, "fh": 560, "sheets": ["ada_fansign_s0", "ada_fansign_s1"], "box": [59, 0, 594, 1263], "src": [704, 1280], "fig": 0.9086},
  "logi_fansign": {"frames": 24, "per": 12, "cols": 4, "rows": 3, "fw": 270, "fh": 560, "sheets": ["logi_fansign_s0", "logi_fansign_s1"], "box": [92, 0, 704, 1268], "src": [704, 1280], "fig": 0.9215},
  "relu_shock": {"frames": 12, "per": 12, "cols": 4, "rows": 3, "fw": 386, "fh": 800, "sheets": ["relu_shock_s0"], "box": [42, 35, 628, 1250], "src": [704, 1280], "fig": 0.8672},
};
// </sprites>
// <pic-use: generated by tools/pic_use.mjs>
const PIC_USE = {
  "intro": [],
  "V1.1": [],
  "V1.2": [["toki_pose_s0",0.2,1.3],["toki_pose_s1",1.2,1.7]],
  "V1.3": [["toki_pose_s1",0,0.4],["relu_pose_s0",0.3,1.4],["relu_pose_s1",1.3,1.7]],
  "V1.4": [["relu_pose_s1",0,0.4],["logi_react",0.9,1.5]],
  "V1.5": [["logi_react",0,0.3],["ada_pose_s0",0.2,1.3],["ada_pose_s1",1.2,1.7]],
  "V1.6": [["ada_pose_s1",0,0.5]],
  "V1.7": [["logi_dance_s0",0,1.1],["logi_dance_s1",1,1.5]],
  "V1.8": [["logi_dance_s1",0,0.5]],
  "V1.9": [["group_pose_s0",0.4,1.5],["group_pose_s1",1.4,2.1]],
  "V1.10": [["group_pose_s1",0,0.2]],
  "V1.11": [["relu_eye",0.3,1.7]],
  "V1.12": [["relu_eye",0,0.4]],
  "V1.13": [],
  "V1.14": [["ada_concept",0,1.5]],
  "V1.15": [["ada_concept",0,0.4],["card_hinton",0.3,1.9]],
  "V1.16": [["card_hinton",0,1.7],["card_demis",0.1,1.7]],
  "C1": [["card_demis",0,0.8],["card_hinton",0,0.8],["ada_u1_s0",0.7,1.6],["logi_u1_s0",0.7,1.6],["relu_u1_s0",0.7,1.6],["toki_u1_s0",0.7,1.6],["ada_u1_s1",1.5,2.6],["logi_u1_s1",1.5,2.6],["relu_u1_s1",1.5,2.6],["toki_u1_s1",1.5,2.6],["ada_u1_s2",2.5,3.6],["logi_u1_s2",2.5,3.6],["relu_u1_s2",2.5,3.6],["toki_u1_s2",2.5,3.6],["ada_u1_s3",3.5,4],["logi_u1_s3",3.5,4],["relu_u1_s3",3.5,4],["toki_u1_s3",3.5,4],["ada_uT_s0",3.9,4.8],["logi_uT_s0",3.9,4.8],["relu_uT_s0",3.9,4.8],["toki_uT_s0",3.9,4.8],["ada_uT_s1",4.7,5.8],["logi_uT_s1",4.7,5.8],["relu_uT_s1",4.7,5.8],["toki_uT_s1",4.7,5.8],["ada_uT_s2",5.7,7],["logi_uT_s2",5.7,7],["relu_uT_s2",5.7,7],["toki_uT_s2",5.7,7],["ada_uG_s0",6.9,7.8],["logi_uG_s0",6.9,7.8],["relu_uG_s0",6.9,7.8],["toki_uG_s0",6.9,7.8],["ada_uG_s1",7.7,8.8],["logi_uG_s1",7.7,8.8],["relu_uG_s1",7.7,8.8],["toki_uG_s1",7.7,8.8],["ada_uG_s2",8.7,9.8],["logi_uG_s2",8.7,9.8],["relu_uG_s2",8.7,9.8],["toki_uG_s2",8.7,9.8],["ada_uG_s3",9.7,10.4],["logi_uG_s3",9.7,10.4],["relu_uG_s3",9.7,10.4],["toki_uG_s3",9.7,10.4],["toki_sing",10.3,11.8],["toki_v_hum",10.3,10.5],["toki_v_ee",10.4,11.8],["toki_v_ah",10.9,11.7],["ada_uC_s0",11.7,13.6],["logi_uC_s0",11.7,13.6],["relu_uC_s0",11.7,13.6],["toki_uC_s0",11.7,13.6],["ada_uC_s1",13.5,14.6],["logi_uC_s1",13.5,14.6],["relu_uC_s1",13.5,14.6],["toki_uC_s1",13.5,14.6],["ada_uC_s2",14.5,15.6],["logi_uC_s2",14.5,15.6],["relu_uC_s2",14.5,15.6],["toki_uC_s2",14.5,15.6],["ada_uC_s3",15.5,16],["logi_uC_s3",15.5,16],["relu_uC_s3",15.5,16],["toki_uC_s3",15.5,16],["ada_point",15.9,16.9],["logi_point",15.9,16.9],["relu_point",15.9,16.9],["toki_point",15.9,16.9]],
  "V2.1": [["ada_point",0,0.5],["logi_point",0,0.5],["relu_point",0,0.5],["toki_point",0,0.5],["relu_press_s0",0.4,1.3],["relu_shock_s0",1.2,2.1]],
  "V2.2": [["elon_portrait",1.3,1.5]],
  "V2.3": [["elon_portrait",0,0.3]],
  "V2.4": [["ada_pose2_s0",0,1.1],["ada_pose2_s1",1,1.5]],
  "V2.5": [["ada_pose2_s1",0,0.1],["zuck",0,1.7]],
  "V2.6": [["logi_host_s1",0,1.1],["logi_host_s2",1,1.5]],
  "V2.7": [["logi_host_s2",0,0.4]],
  "V2.8": [["toki_react",1.5,1.9]],
  "V2.9": [["ada_smile_s0",0,2.1],["logi_smile_s0",0,2.1],["relu_smile_s0",0,2.1],["toki_react",0,0.1],["toki_smile_s0",0,2.1]],
  "V2.10": [["ada_smile_s0",0,0.2],["logi_smile_s0",0,0.2],["relu_smile_s0",0,0.2],["toki_smile_s0",0,0.2]],
  "V2.11": [["clawd_cry",0,1.7]],
  "V2.12": [["ada_fansign_s0",0,1.1],["clawd_cry",0,0.1],["logi_fansign_s0",0,1.1],["relu_fansign_s0",0,1.1],["toki_fansign_s0",0,1.1],["ada_fansign_s1",1,1.5],["logi_fansign_s1",1,1.5],["relu_fansign_s1",1,1.5],["toki_fansign_s1",1,1.5]],
  "V2.13": [["ada_fansign_s1",0,0.3],["logi_fansign_s1",0,0.3],["relu_fansign_s1",0,0.3],["toki_fansign_s1",0,0.3],["relu_fancam_s0",0.2,1.3],["robot",0.2,1.9],["relu_fancam_s1",1.2,1.9]],
  "V2.14": [["ada_u1_s1",0,1.7],["ada_u1_s3",0,1.3],["logi_u1_s1",0,1],["logi_u1_s2",0,1.7],["relu_fancam_s1",0,0.1],["relu_u1_s1",0,1.7],["relu_u1_s2",0,0.6],["relu_u1_s3",0,1.7],["robot",0,0.1],["toki_u1_s2",0,0.2],["toki_u1_s3",0,1.7],["logi_react",0.3,1.7],["ada_u1_s2",0.4,1.7],["logi_u1_s3",0.5,1.7],["relu_u1_s0",0.6,1.6],["toki_u1_s2",1.2,1.7]],
  "V2.15": [["ada_u1_s1",0,0.2],["ada_u1_s2",0,0.2],["logi_react",0,0.2],["logi_u1_s2",0,0.2],["logi_u1_s3",0,0.2],["relu_u1_s1",0,0.2],["relu_u1_s3",0,0.2],["toki_u1_s2",0,0.2],["toki_u1_s3",0,0.2],["yann",0.1,1.7]],
  "V2.16": [["yann",0,0.2],["toki_react",0.1,2.1]],
  "C2": [["toki_react",0,0.4],["ada_u1_s0",0.3,1.2],["logi_u1_s0",0.3,1.2],["relu_u1_s0",0.3,1.2],["toki_u1_s0",0.3,1.2],["ada_u1_s1",1.1,2.2],["logi_u1_s1",1.1,2.2],["relu_u1_s1",1.1,2.2],["toki_u1_s1",1.1,2.2],["ada_u1_s2",2.1,3.2],["logi_u1_s2",2.1,3.2],["relu_u1_s2",2.1,3.2],["toki_u1_s2",2.1,3.2],["ada_u1_s3",3.1,3.6],["logi_u1_s3",3.1,3.6],["relu_u1_s3",3.1,3.6],["toki_u1_s3",3.1,3.6],["logi_uT_s0",3.5,4.4],["logi_uT_s1",4.3,5.4],["logi_uT_s2",5.3,5.5],["ada_uG_s0",5.4,6.4],["logi_uG_s0",5.4,6.4],["relu_uG_s0",5.4,6.4],["toki_uG_s0",5.4,6.4],["ada_uG_s1",6.3,7.4],["logi_uG_s1",6.3,7.4],["relu_uG_s1",6.3,7.4],["toki_uG_s1",6.3,7.4],["ada_uG_s2",7.3,8.4],["logi_uG_s2",7.3,8.4],["relu_uG_s2",7.3,8.4],["toki_uG_s2",7.3,8.4],["ada_uG_s3",8.3,10],["logi_uG_s3",8.3,10],["relu_uG_s3",8.3,10],["toki_uG_s3",8.3,10],["toki_sing",9.9,13],["toki_v_hum",9.9,10.1],["toki_v_ee",10,13],["toki_v_ah",10.4,11.2],["ada_sing",11.3,13],["ada_v_hum",11.3,11.5],["ada_v_oh",11.3,11.7],["logi_sing",11.3,13],["logi_v_hum",11.3,11.5],["logi_v_oh",11.3,11.7],["relu_sing",11.3,14.5],["relu_v_hum",11.3,11.5],["relu_v_oh",11.3,11.7],["toki_v_hum",11.3,11.5],["toki_v_oh",11.3,11.7],["ada_v_ee",11.6,13],["logi_v_ee",11.6,13],["relu_v_ee",11.6,14.5],["ada_v_mb",12.1,12.3],["logi_v_mb",12.1,12.3],["relu_v_mb",12.1,13.1],["toki_v_mb",12.1,12.3],["ada_v_ah",12.5,12.9],["logi_v_ah",12.5,12.9],["relu_v_ah",12.5,14.3],["toki_v_ah",12.5,12.9],["relu_v_oh",13.7,14.1]],
  "V3.1": [["ada_react",1,3.1]],
  "V3.2": [["ada_react",0,0.4],["lobster",0.3,3.3]],
  "V3.3": [["lobster",0,0.3]],
  "V3.4": [["park",0.6,3.3],["logi_react",2.9,3.3]],
  "V3.5": [["logi_react",0,0.3],["park",0,0.3],["ada_u1_s3",0.2,1.9],["clawd_fan",0.2,1.9],["logi_u1_s1",0.2,1.2],["logi_u1_s3",0.2,1.9],["relu_u1_s1",0.2,0.7],["relu_u1_s2",0.2,1.7],["relu_u1_s3",0.2,1.9],["toki_u1_s1",0.2,1.9],["toki_u1_s2",0.2,1.9],["ada_u1_s2",0.3,1.9],["toki_u1_s3",0.9,1.9],["logi_u1_s2",1.1,1.9],["ada_u1_s1",1.3,1.5]],
  "V3.6": [["ada_u1_s2",0,0.2],["ada_u1_s3",0,0.2],["clawd_fan",0,0.2],["logi_u1_s2",0,0.2],["logi_u1_s3",0,0.2],["relu_u1_s3",0,0.2],["toki_u1_s1",0,0.2],["toki_u1_s2",0,0.2],["toki_u1_s3",0,0.2],["lutnick",0.1,1.5]],
  "V3.7": [["lutnick",0,0.3],["clawd_fan",0.2,1.7]],
  "V3.8": [["clawd_fan",0,0.3],["relu_grok_s0",0.2,0.9],["relu_grok_s1",0.8,1.7]],
  "V3.9": [["relu_grok_s1",0,0.3],["relu_grok_s2",0.2,0.3]],
  "V3.10": [["sam_facepalm",0,1.7]],
  "V3.11": [["sam_facepalm",0,0.2],["ada_concept",0.1,1.5],["logi_point",0.1,1.5],["noam_ox",0.1,1.5],["relu_concept",0.1,1.5],["toki_concept",0.1,1.5],["toki_react",0.6,1.5],["ada_react",0.8,1.5]],
  "V3.12": [["ada_concept",0,0.3],["ada_react",0,0.3],["logi_point",0,0.3],["noam_ox",0,0.3],["relu_concept",0,0.3],["toki_concept",0,0.3],["toki_react",0,0.3]],
  "V3.13": [["toki_react",0.9,1.9]],
  "V3.14": [["toki_react",0,0.2],["jeff",0.1,1.7]],
  "V3.15": [["clawd_chalk",0,1.5],["jeff",0,0.1]],
  "V3.16": [["clawd_chalk",0,0.4]],
  "C3": [["ada_u1_s0",0.4,1.3],["logi_u1_s0",0.4,1.3],["relu_u1_s0",0.4,1.3],["toki_u1_s0",0.4,1.3],["ada_u1_s1",1.2,2.3],["logi_u1_s1",1.2,2.3],["relu_u1_s1",1.2,2.3],["toki_u1_s1",1.2,2.3],["ada_u1_s2",2.2,3.3],["logi_u1_s2",2.2,3.3],["relu_u1_s2",2.2,3.3],["toki_u1_s2",2.2,3.3],["ada_u1_s3",3.2,3.8],["logi_u1_s3",3.2,3.8],["relu_u1_s3",3.2,3.8],["toki_u1_s3",3.2,3.8],["ada_sing",3.7,5.7],["ada_v_ee",3.7,5.4],["ada_v_hum",3.7,3.9],["ada_v_ah",4.2,5.1],["ada_v_held",5.2,5.7],["ada_uG_s0",5.6,6.5],["logi_uG_s0",5.6,6.5],["relu_uG_s0",5.6,6.5],["toki_uG_s0",5.6,6.5],["ada_uG_s1",6.4,7.5],["logi_uG_s1",6.4,7.5],["relu_uG_s1",6.4,7.5],["toki_uG_s1",6.4,7.5],["ada_uG_s2",7.4,8.5],["logi_uG_s2",7.4,8.5],["relu_uG_s2",7.4,8.5],["toki_uG_s2",7.4,8.5],["ada_uG_s3",8.4,10.2],["logi_uG_s3",8.4,10.2],["relu_uG_s3",8.4,10.2],["toki_uG_s3",8.4,10.2],["ada_u1_s0",10.1,10.9],["clawd_fan",10.1,11.6],["logi_u1_s0",10.1,10.9],["relu_u1_s0",10.1,10.9],["toki_u1_s0",10.1,10.9],["ada_u1_s1",10.8,11.6],["logi_u1_s1",10.8,11.6],["relu_u1_s1",10.8,11.6],["toki_u1_s1",10.8,11.6],["ada_concept",11.5,13.2],["logi_concept",11.5,13.2],["relu_concept",11.5,13.2],["toki_concept",11.5,13.2],["clawd_cry",13.1,14.3],["group_win_s0",13.1,14.2],["group_win_s1",14.1,14.3]],
  "V4.1": [["clawd_cry",0,0.3],["group_win_s1",0,0.3]],
  "V4.2": [["logi_dance2_s0",0.3,1.4],["logi_dance2_s1",1.3,1.7]],
  "V4.3": [["logi_dance2_s1",0,0.3],["jensen",0.2,1.9],["toki_react",1.4,1.9]],
  "V4.4": [["greg",0,1.7]],
  "V4.5": [["greg",0,0.2]],
  "V4.6": [],
  "V4.7": [["dario",0.3,1.9]],
  "V4.8": [["elon_portrait",0,1.5],["sam_portrait",0,1.5]],
  "V4.9": [["elon_portrait",0,0.3],["sam_portrait",0,0.3],["trump",0.2,1.7],["logi_react",1,1.7]],
  "V4.10": [["logi_react",0,0.4],["trump",0,0.4],["pew_pair",0.3,1.7]],
  "V4.11": [["pew_pair",0,0.3],["clawd_build",0.2,1.7],["clawd_fan",0.2,1.7],["logi_react",1.1,1.7]],
  "V4.12": [["clawd_build",0,0.3],["clawd_fan",0,0.3],["logi_react",0,0.3]],
  "V4.13": [["trump",0.2,2.1],["toki_react",0.9,2.1]],
  "V4.14": [["relu_sing",0,1.3],["relu_v_ah",0,1.1],["relu_v_hum",0,0.1],["relu_v_ee",0.1,1.3],["relu_v_oh",0.9,1.2],["relu_v_mb",1,1.2]],
  "V4.15": [["relu_sing",0,0.3],["relu_v_ee",0,0.3],["ada_react",1.4,1.7]],
  "V4.16": [["ada_react",0,0.3],["clawd_mic",0.2,2.1],["group_wave_s0",0.2,1.2],["group_wave_s1",1.1,2.1]],
  "C4": [["clawd_mic",0,0.5],["group_wave_s1",0,0.2],["group_wave_s2",0.1,0.5],["toki_tears_s0",0.4,1.5],["toki_tears_s1",1.4,2.1],["ada_u1_s1",2,2.3],["logi_u1_s1",2,2.3],["relu_u1_s1",2,2.3],["toki_u1_s1",2,2.3],["ada_u1_s2",2.2,3.3],["logi_u1_s2",2.2,3.3],["relu_u1_s2",2.2,3.3],["toki_u1_s2",2.2,3.3],["ada_u1_s3",3.2,3.8],["logi_u1_s3",3.2,3.8],["relu_u1_s3",3.2,3.8],["toki_u1_s3",3.2,3.8],["ada_concept",3.7,10.2],["card_demis",3.7,10.2],["card_hinton",3.7,10.2],["logi_concept",3.7,10.1],["relu_concept",3.7,10.2],["toki_concept",3.7,10.2],["clawd_fan",4.1,10.2],["toki_win",4.5,10.2],["ada_uC_s2",10.1,11],["logi_uC_s2",10.1,11],["relu_uC_s2",10.1,11],["toki_uC_s2",10.1,11],["ada_uC_s3",10.9,11.6],["logi_uC_s3",10.9,11.6],["relu_uC_s3",10.9,11.6],["toki_uC_s3",10.9,11.6],["ada_uT_s0",11.5,12.4],["logi_uT_s0",11.5,12.4],["relu_uT_s0",11.5,12.4],["toki_uT_s0",11.5,12.4],["ada_uT_s1",12.3,14],["logi_uT_s1",12.3,14],["relu_uT_s1",12.3,14],["toki_uT_s1",12.3,14],["ada_uT_s2",13.9,16.6],["logi_uT_s2",13.9,16.6],["relu_uT_s2",13.9,16.6],["toki_uT_s2",13.9,16.6],["ada_u1_s0",16.5,17.4],["logi_u1_s0",16.5,17.4],["relu_u1_s0",16.5,17.4],["toki_u1_s0",16.5,17.4],["ada_u1_s1",17.3,18.4],["logi_u1_s1",17.3,18.4],["relu_u1_s1",17.3,18.4],["toki_u1_s1",17.3,18.4],["ada_u1_s2",18.3,19.4],["logi_u1_s2",18.3,19.4],["relu_u1_s2",18.3,19.4],["toki_u1_s2",18.3,19.4],["ada_u1_s3",19.3,20.2],["logi_u1_s3",19.3,20.2],["relu_u1_s3",19.3,20.2],["toki_u1_s3",19.3,20.2],["group_wave_s0",20.1,21.2],["group_wave_s1",21.1,22.2],["group_wave_s2",22.1,23.2],["group_wave_s3",23.1,25.1],["group_wave_s2",25,26.1],["group_wave_s1",26,27.1],["group_wave_s0",27,29],["group_wave_s1",28.9,30],["group_wave_s2",29.9,31],["group_wave_s3",30.9,33],["group_wave_s2",32.9,34],["group_wave_s1",33.9,35],["group_wave_s0",34.9,35.5],["toki_fairy",35.4,40.4],["toki_fairy15_s0",35.4,38.2],["toki_fairy_blink",37.3,37.5],["toki_fairy15_s1",37.9,40.4],["toki_fairy_blink",39.2,39.5]],
  "outro": [["toki_fairy",0,1.1],["toki_fairy15_s1",0,0.9],["toki_fairy15_s2",0.8,1.1]],
};
// </pic-use>

// Loading, playhead first (the anime style's loader, with GL textures). pic(name) is what a shot draws with: the full picture, decoded,
// or else its low-res stand-in (cut from img/lowres.webp, 1/16 the size, drawn scaled up). The pictures download soonest needed first:
// from the playhead on, in the order the song shows them (PIC_USE, written by tools/pic_use.mjs), then the ones it has already shown.
// A frame far from the last one (a seek, or the video starting mid-song) reorders the queue, and a picture a frame drew low-res goes to
// the front. STYLE_READY, which the studio and the site's worker wait for before the first frame, settles once the stand-ins and the
// pictures for the first few seconds from STYLE_START (the host's playhead) are in, and until then nothing else downloads, so that on a
// slow connection they have it to themselves; STYLE_ALL settles once every picture is (offline renders, studio.html?render, wait for that
// and keep everything decoded, so they never draw a stand-in). When a picture the last frame drew low-res arrives, the kit calls the
// host's STYLE_STALE(), so that a paused player can redraw.
// Downloading and decoding are separate stages. LOAD_PARALLEL pictures download at once: the site's host (Netlify) starts sending a file
// its edge server hasn't cached, which for a page this rarely visited is most of them, 0.3 to 0.8 s after it's asked, whatever the
// file's size or the connection's speed, so with a few requests in flight the connection mostly waits (four at a time, the song's 170
// pictures took 25 to 50 s on a fast connection; sixteen, 15 to 28 s, or 3 to 5 s from an edge server that has them). The pictures
// near the playhead decode (DECODE_PARALLEL at a time, soonest needed first), and the files of the rest wait, downloaded: only the
// pictures on screen from KEEP_BEHIND s before the playhead to KEEP_AHEAD s after it (and any drawn in the last KEEP_DRAWN s) stay
// decoded, up to KEEP_BYTES; the others go back to their stand-ins, and their GL textures are freed with them. Their files stay, so a
// picture needed again decodes without another download.
const PIC = {}, LO = {}, FULL = new Set(), FILES = {};
const LOAD_LEAD = 5, NOW_LEAD = 2, LOAD_PARALLEL = 16, DECODE_PARALLEL = 4, LOAD_TRIES = 3;
const KEEP_ALL = typeof location !== 'undefined' && new URLSearchParams(location.search).has('render');
// (?keep: every picture kept decoded, as in render mode, in a page that otherwise draws as the site does: for comparing the two)
const KEEP_PICS = KEEP_ALL || typeof location !== 'undefined' && new URLSearchParams(location.search).has('keep');
const KEEP_BEHIND = 8, KEEP_AHEAD = 20, KEEP_DRAWN = .5, KEEP_BYTES = 160e6;
let _drawn = new Set(), _lowLast = [], _segLast = null, _tLast = -1;
function pic(name) { _drawn.add(name); PANEL_PICS.painting?.add(name); return PIC[name]; }
PANEL_PICS.touch = name => _drawn.add(name);
async function loadFile(rel, signal) {
  const url = new URL(rel, self.STYLE_BASE ?? new URL('img/', location.href));
  try {
    const r = await fetch(url, { signal });
    if (!r.ok) throw new Error(`${r.status} ${url}`);
    return await r.blob();
  } catch (e) {
    // (pages opened from file://, like the offline renderer's, can't fetch: they load an <img>)
    if (typeof Image === 'undefined' || signal?.aborted) throw e;
    return url;
  }
}
async function decodeFile(file) {
  if (file instanceof Blob) return createImageBitmap(file, { premultiplyAlpha: 'premultiply' });
  const im = new Image(); im.src = file.href; await im.decode();
  return createImageBitmap(im, { premultiplyAlpha: 'premultiply' });
}
let _queue = Object.keys(PICS), _keep = new Set(_queue), _key = () => 0;
const _fetching = new Map(), _decoding = new Set(), _tries = new Map(), _retryAt = new Map(), _drawnAt = new Map();
const needsWork = n => !FULL.has(n) && (_keep.has(n) || !FILES[n]);
// how soon each picture is next on screen from t (0 while it is); after those, the ones already shown for the last time; last, the rest
function neededFrom(t) {
  const next = new Map(), past = new Map();
  for (const s of SEGS) for (const [n, a, b] of PIC_USE[s.key] ?? []) {
    if (!PICS[n]) continue;
    if (s.start + b >= t) next.set(n, Math.min(next.get(n) ?? Infinity, Math.max(0, s.start + a - t)));
    else if (!past.has(n)) past.set(n, s.start + a);
  }
  return n => next.get(n) ?? (past.has(n) ? DUR + past.get(n) : 3 * DUR);
}
function keepFrom(t) {
  const rank = new Map(), now = performance.now();
  for (const s of SEGS) for (const [n, a, b] of PIC_USE[s.key] ?? []) {
    // (PIC_USE is written by tools/pic_use.mjs from a render: a picture since renamed or dropped isn't in the manifest)
    if (!PICS[n]) continue;
    const from = s.start + a - t, since = t - s.start - b;
    const r = since <= 0 ? (from <= KEEP_AHEAD ? Math.max(0, from) : null) : (since <= KEEP_BEHIND ? KEEP_AHEAD + since : null);
    if (r !== null) rank.set(n, Math.min(rank.get(n) ?? Infinity, r));
  }
  for (const [n, at] of _drawnAt) if (PICS[n] && now - at <= KEEP_DRAWN * 1000) rank.set(n, -1);
  const keep = new Set();
  let bytes = 0;
  for (const [n, r] of [...rank].sort((x, y) => x[1] - y[1])) {
    const b = PICS[n].w * PICS[n].h * 4;
    if (r > 0 && bytes + b > KEEP_BYTES) continue;
    keep.add(n); bytes += b;
  }
  return keep;
}
function releasePic(n) {
  const b = PIC[n];
  PIC[n] = LO[n]; FULL.delete(n);
  if (b && b !== LO[n]) { dropTex(b); b.close(); }
}
// (jump: the playhead moved (a seek), and the downloads for where it was give way; see requeuePics)
function reorderPics(t, jump = false) {
  const key = _key = neededFrom(t);
  if (!KEEP_PICS) {
    _keep = keepFrom(t);
    for (const n of FULL) if (!_keep.has(n)) releasePic(n);
  }
  _queue = Object.keys(PICS).filter(needsWork).sort((a, b) => key(a) - key(b));
  if (jump) requeuePics(); else pumpPics();
}
const pending = n => !FILES[n] && !(_tries.get(n) >= LOAD_TRIES), urgent = n => _key(n) <= NOW_LEAD || _lowLast.includes(n);
// (while a picture that the next NOW_LEAD s draw hasn't downloaded, the downloads are for such pictures alone: after a seek, or on a
// connection too slow to keep ahead of the song, the ones needed now get it to themselves. Not before STYLE_READY, whose pictures are
// few, and download alone anyway.)
const rushing = () => _ready && _queue.some(n => pending(n) && urgent(n));
// After a seek, or a frame that drew pictures low-res: a download that's no longer among the ones the queue wants first gives up its
// place, and its share of the connection, to one the new order puts ahead of it.
function requeuePics() {
  const rush = rushing();
  const want = new Set(_queue.filter(n => pending(n) && (!rush || urgent(n))).slice(0, LOAD_PARALLEL));
  for (const [n, ac] of _fetching) if (!want.has(n)) { ac.abort(); _fetching.delete(n); }
  pumpPics();
}
// Starts the downloads and decodes the queue has room for, in its order. Before STYLE_READY, only the pictures it waits for download.
function pumpPics() {
  const now = performance.now(), rush = rushing();
  for (const n of _queue) {
    if (_fetching.size >= LOAD_PARALLEL && _decoding.size >= DECODE_PARALLEL) break;
    if (_fetching.has(n) || _decoding.has(n) || _tries.get(n) >= LOAD_TRIES || _retryAt.get(n) > now) continue;
    if (!FILES[n]) { if (_fetching.size < LOAD_PARALLEL && (_ready || _firstLeft.has(n)) && (!rush || urgent(n))) fetchPic(n); }
    else if (_keep.has(n) && _decoding.size < DECODE_PARALLEL) decodePic(n);
  }
}
async function fetchPic(n) {
  const ac = new AbortController();
  _fetching.set(n, ac);
  try {
    FILES[n] = await loadFile(`${n}.webp`, ac.signal);
  } catch (e) {
    if (!ac.signal.aborted) failPic(n, e);
  } finally {
    if (_fetching.get(n) === ac) _fetching.delete(n);
    donePic(n);
  }
}
async function decodePic(n) {
  _decoding.add(n);
  try {
    const b = await decodeFile(FILES[n]);
    if (FULL.has(n) || !_keep.has(n)) { b.close(); return; }
    PIC[n] = b; FULL.add(n);
    if (_lowLast.includes(n)) self.STYLE_STALE?.();
  } catch (e) {
    // (a file that doesn't decode is downloaded again)
    delete FILES[n];
    failPic(n, e);
  } finally {
    _decoding.delete(n);
    donePic(n);
  }
}
function failPic(n, e) {
  const k = (_tries.get(n) ?? 0) + 1;
  _tries.set(n, k); _firstLeft.delete(n);
  console.warn(`picture ${n}: ${e}`);
  if (k < LOAD_TRIES) { _retryAt.set(n, performance.now() + 2000 * k); setTimeout(pumpPics, 2000 * k + 10); }
}
function donePic(n) {
  if (FULL.has(n) || (FILES[n] && !_keep.has(n))) _firstLeft.delete(n);
  if (!needsWork(n) && _queue.includes(n)) _queue.splice(_queue.indexOf(n), 1);
  settlePics(); pumpPics();
}
let _firstLeft = new Set(), _lowIn = false, _ready = false, _readyOK, _readyBad, _allOK, _allBad;
self.STYLE_READY = new Promise((ok, bad) => { _readyOK = ok; _readyBad = bad; });
self.STYLE_ALL = new Promise((ok, bad) => { _allOK = ok; _allBad = bad; });
self.STYLE_ALL.catch(() => {});
function settlePics() {
  if (!_lowIn) return;
  if (!_firstLeft.size && !_ready) { _ready = true; _readyOK(); pumpPics(); }
  if (!_queue.length) _allOK();
  else if (_queue.every(n => _tries.get(n) >= LOAD_TRIES)) _allBad(new Error(`pictures failed to load: ${_queue.join(', ')}`));
}
function startPics() {
  const t0 = clamp(+(self.STYLE_START ?? 0) || 0, 0, DUR), key = neededFrom(t0);
  _firstLeft = new Set(_queue.filter(n => key(n) <= LOAD_LEAD));
  (async () => {
    let atlas;
    for (let k = 1; !atlas; k++) {
      try { atlas = await decodeFile(await loadFile('lowres.webp')); } catch (e) {
        if (k >= LOAD_TRIES) { _readyBad(e); _allBad(e); return; }
        await new Promise(ok => setTimeout(ok, 2000 * k));
      }
    }
    // (each stand-in is copied out of the atlas into a canvas of its own: a cropped ImageBitmap shares its source's pixels, and a
    // browser that uploads the source rather than the crop draws the whole atlas in its place)
    for (const [n, I] of Object.entries(PICS)) {
      const c = makeCanvas(I.lo[2], I.lo[3]);
      c.getContext('2d').drawImage(atlas, I.lo[0], I.lo[1], I.lo[2], I.lo[3], 0, 0, I.lo[2], I.lo[3]);
      LO[n] = c; if (!FULL.has(n)) PIC[n] = LO[n];
    }
    atlas.close();
    _lowIn = true;
    settlePics();
  })();
  reorderPics(t0);
  _tLast = t0;
}
// Each frame: after a jump, into a new window, or every REPLAN s of play, the queue is reordered from there (a chorus is one window,
// twenty seconds long, and its dance needs four new sheets a second: planned only from the window's start, the sheets past the first
// few seconds would each be drawn low-res first); the pictures it drew low-res go to the front.
const REPLAN = .5;
let _tPlan = -1;
FRAME_BEGIN.push((t, s) => {
  if (s !== _segLast || Math.abs(t - _tLast) > 1 || Math.abs(t - _tPlan) >= REPLAN) { reorderPics(t, Math.abs(t - _tLast) > 1); _tPlan = t; }
  _segLast = s; _tLast = t;
  _drawn.clear();
});
FRAME_END.push(() => {
  const now = performance.now();
  for (const n of _drawn) if (PICS[n]) _drawnAt.set(n, now);
  _lowLast = [..._drawn].filter(n => PICS[n] && !FULL.has(n));
  if (_lowLast.some(n => !_fetching.has(n) && !_decoding.has(n) && !_queue.slice(0, LOAD_PARALLEL).includes(n))) {
    for (const n of _lowLast) _keep.add(n);
    _queue = [..._lowLast, ..._queue.filter(n => !_lowLast.includes(n))];
    requeuePics();
  }
});
// A picture goes to the GPU the first time a frame draws it, and the upload is the drawing thread's work: a sprite sheet's 2 to 7
// megapixels take 7 to 30 ms of the site's worker on agents-base, and a chorus's four dancers turn to their next sheets on the same
// frame, every second, which cost that frame several frames' time. So between frames, a decoded sheet that the next PREP_LEAD s draw
// goes up ahead of time, one a frame, soonest needed first (the cells its frames are drawn from: see frameTex). Not in render mode,
// whose frames aren't live.
const PREP_LEAD = 2, SHEET_OF = {};
for (const S of Object.values(SPRITES)) for (const n of S.sheets) SHEET_OF[n] = S;
let _prepping = false;
function prepPics() {
  _prepping = false;
  let best = null;
  for (const n of FULL) if (SHEET_OF[n] && !_cellTexs.has(PIC[n]) && _key(n) <= PREP_LEAD && (!best || _key(n) < _key(best))) best = n;
  if (best) { const S = SHEET_OF[best]; cellTexs(PIC[best], S.cols, S.rows, S.per); }
}
if (!KEEP_ALL) FRAME_END.push(() => { if (!_prepping) { _prepping = true; setTimeout(prepPics, 0); } });
self.STYLE_LOWRES = () => _lowLast.length;
// The page's quality hooks (see the site's worker.js, and QUALITY_STEPS in gl.js): its levels, set with setQuality(level), held at 0
// (the video as designed) in render mode; STYLE_FINISH, which finishes the GPU's work for the frame just drawn so that the page's
// measure of it includes that; and STYLE_INFO, for the page's ?debug overlay (the rollout stage on screen, as its corner tag says).
self.QUALITY_LEVELS = QUALITY_STEPS.length;
// (the levels before this one keep the 3D scene at the canvas's full resolution; the page drops resolution only for slower frames than
// it drops effects for, since soft dancers show more than fewer sparkles)
self.QUALITY_SHARP = QUALITY_STEPS.findIndex(q => q.sceneK < 1);
self.setQuality = level => { if (!KEEP_ALL) applyQuality(level); };
self.STYLE_FINISH = finishFrame;
self.STYLE_INFO = () => {
  const s = segAt(T);
  return { era: `${rolloutAt(s)[1]} (${s?.key ?? '—'}) · level ${qualityLevel}, 3D at ${Math.round(QUALITY.sceneK * 100)}% · stand-ins ${_lowLast.length}`, level: qualityLevel, levels: QUALITY_STEPS.length };
};
self.STYLE_DECODED = () => [...FULL].reduce((a, n) => a + PICS[n].w * PICS[n].h * 4, 0);

// procedural textures, made once
function canvasTex(w, h, fn) { const c = makeCanvas(w, h), g = c.getContext('2d'); fn(g, w, h); return c; }
const TX = {
  glow: canvasTex(256, 256, (g, w) => { const r = g.createRadialGradient(w / 2, w / 2, 0, w / 2, w / 2, w / 2); r.addColorStop(0, '#fff'); r.addColorStop(.25, 'rgb(255 255 255 / .55)'); r.addColorStop(1, 'rgb(255 255 255 / 0)'); g.fillStyle = r; g.fillRect(0, 0, w, w); }),
  shadow: canvasTex(256, 128, (g, w, h) => { g.scale(1, h / w); const r = g.createRadialGradient(w / 2, w / 2, 0, w / 2, w / 2, w / 2); r.addColorStop(0, 'rgb(0 0 0 / .9)'); r.addColorStop(.5, 'rgb(0 0 0 / .45)'); r.addColorStop(1, 'rgb(0 0 0 / 0)'); g.fillStyle = r; g.fillRect(0, 0, w, w); }),
  beam: canvasTex(64, 512, (g, w, h) => {
    const x = g.createLinearGradient(0, 0, w, 0); x.addColorStop(0, 'rgb(255 255 255 / 0)'); x.addColorStop(.5, 'rgb(255 255 255 / 1)'); x.addColorStop(1, 'rgb(255 255 255 / 0)');
    g.fillStyle = x; g.fillRect(0, 0, w, h);
    g.globalCompositeOperation = 'destination-in';
    const y = g.createLinearGradient(0, 0, 0, h); y.addColorStop(0, 'rgb(0 0 0 / 0)'); y.addColorStop(.35, 'rgb(0 0 0 / .8)'); y.addColorStop(1, 'rgb(0 0 0 / 1)');
    g.fillStyle = y; g.fillRect(0, 0, w, h);
  }),
  white: canvasTex(4, 4, g => { g.fillStyle = '#fff'; g.fillRect(0, 0, 4, 4); }),
};

// =====================================================================================================
// MEMBERS ON STAGE
// =====================================================================================================
const POSES = ['concept', 'point', 'dance', 'gasp'];
// figure(name, o): any cut-out standing in the 3D world (a member, a person from the lyrics, Clawd, a prop). o: at [x, y, z] (its
// feet), h (metres, default 1.72), rim (colour) and rimK, light (the key light's colour, multiplying its top) and shade (its feet), alpha,
// reflect (a gloss reflection in the floor), shadow (a contact shadow; default on), cast (a long shadow thrown across a pale floor:
// [dx, dz, k]), beat (how much it moves with the beat, default 1), phase, flash (0..1: the white flash of a pose cut), facing, uv, anchor.
function figure(name, o = {}) {
  // (o.srcOf(picture): what to draw for the picture, e.g. one frame's texture of a sprite sheet)
  const img = o.srcOf ? o.srcOf(pic(name)) : pic(name);
  if (!img) return null;
  const at = o.at ?? [0, 0, 0], h = o.h ?? 1.72, bt = o.beat ?? 1, b = bpOf(T) + (o.phase ?? 0);
  const sway = bt * .010 * Math.sin(b * Math.PI), squash = bt * .012 * Math.exp(-frac(b) * 5);
  if (o.cast) {
    const [dx, dz, k] = o.cast;
    plane(img, { at: [at[0], at[1] + .003, at[2]], h, facing: Math.atan2(-dx, -dz) + Math.PI, tilt: Math.PI / 2 - .02, flat: ['#5A5070', 1], alpha: k, grid: false, anchor: [.5, 1], uv: o.uv });
  }
  if (o.shadow !== false) plane(TX.shadow, { at: [at[0], at[1] + .004, at[2]], w: h * .55, h: h * .16, tilt: Math.PI / 2, anchor: [.5, .5], alpha: o.shadowK ?? .75, grid: false });
  if (o.reflect) plane(img, { at, h, mirror: true, alpha: (o.alpha ?? 1) * o.reflect, fadeT: .55, mul: o.light ?? '#FFFFFF', bot: o.light ?? '#FFFFFF', sway: -sway, squash, uv: o.uv, facing: o.facing });
  const flash = o.flash ?? 0;
  const B = plane(img, {
    at, h, alpha: o.alpha ?? 1, mul: o.light ?? '#FFFFFF', bot: o.shade ?? mixCol(o.light ?? '#FFFFFF', '#6A6088', .28),
    rim: o.rim ? [o.rim, o.rimK ?? 1.1] : undefined, rimDir: o.rimDir ?? [-.0045, .0035], sway, squash, add: flash ? [flash, flash, flash * 1.02] : undefined,
    facing: o.facing, uv: o.uv, anchor: o.anchor, gain: o.gain, fadeB: o.fadeB,
  });
  return { top: project([at[0], at[1] + h, at[2]]), foot: project(at), basis: B, mul: o.light ?? '#FFFFFF', bot: o.shade ?? mixCol(o.light ?? '#FFFFFF', '#6A6088', .28) };
}
// dancer(key, clip, t, o): a member playing one of her sprite clips, in the 3D world like figure(). The clip plays at 12 fps from its
// frame o.from (default 0) at o.t0 (default the shot's cut), o.rate × real time (1 by default), holding its last frame at the end. o: as
// figure() (at, h: the clip's box height in metres, default 1.9; or frameH, its source frame's), plus hold (a frame to freeze on) and
// loop (play it back and forth instead of holding the end).
const CLIP_FPS = 12;
function clipFrame(clip, t, o = {}) {
  const S = SPRITES[clip];
  if (!S) return null;
  const t0 = o.t0 ?? cutAt(t).start, fps = S.fps ?? CLIP_FPS;
  // (before t0 the clip runs from its earlier frames, down to its first: a frame can be anchored to a word mid-shot)
  const ff = (o.from ?? 0) + (t - t0) * fps * (o.rate ?? 1);
  let f = Math.floor(ff);
  // (o.loop: back and forth between o.from and o.to (default the last frame), for a hold that keeps breathing)
  if (o.loop) { const a = o.from ?? 0, n = (o.to ?? S.frames - 1) - a, m = ((f - a) % (2 * n) + 2 * n) % (2 * n); f = a + (m <= n ? m : 2 * n - m); }
  f = o.hold ?? clamp(f, 0, S.frames - 1);
  return { ...cellOf(S, f), f, k: o.hold !== undefined || o.loop ? 0 : clamp(ff - f), next: f + 1 < S.frames ? cellOf(S, f + 1) : null };
}
// the sheet and UV rectangle holding frame f of a clip
function cellOf(S, f) {
  const k = Math.floor(f / S.per), i = f % S.per, cx = i % S.cols, cy = Math.floor(i / S.cols);
  const W_ = S.cols * S.fw, H_ = S.rows * S.fh;
  return { name: S.sheets[k], cell: i, uv: [cx * S.fw / W_, cy * S.fh / H_, (cx + 1) * S.fw / W_, (cy + 1) * S.fh / H_] };
}
// cellRect(im, S, i): where cell i of clip S's grid sits in a picture of its sheet, in that picture's pixels (the full sheet or its
// low-res stand-in: the grid scales with it); null for anything that isn't one of the sheet's cells
function cellRect(im, S, i) {
  if (!im || !Number.isInteger(i) || i < 0 || i >= S.per) return null;
  const cw = im.width / S.cols, ch = im.height / S.rows;
  return [(i % S.cols) * cw, Math.floor(i / S.cols) * ch, cw, ch];
}
// frameTex(im, S, i): the texture of that one frame alone (see cellTexs() in gl.js), for plane(); null if there's no such frame
function frameTex(im, S, i) {
  if (!im || !Number.isInteger(i) || i < 0 || i >= S.per) return null;
  return cellTexs(im, S.cols, S.rows, S.per)[i];
}
function dancer(key, clip, t, o = {}) {
  const F = clipFrame(clip, t, o);
  if (!F) return null;
  // (o.frameH: the height in metres of the clip's whole source frame, which sets its scale from the box it was packed on, so clips
  // cut to different boxes come out at one scale)
  // (o.figH: the figure's height in metres instead (the median over the clip), so every clip's member stands as tall as her stills)
  const S = SPRITES[clip];
  if (o.frameH && S.box) o = { ...o, h: (S.box[3] - S.box[1]) / S.src[1] * o.frameH };
  else if (o.figH && S.fig) o = { ...o, h: (S.box[3] - S.box[1]) / S.src[1] / S.fig * o.figH };
  // (a unison set's o.h assumes the first takes' framing; S.hk turns it into this take's box height: see images.py unison)
  else if (o.h && S.hk) o = { ...o, h: o.h * S.hk };
  // (no beat sway or squash: the clip is the motion)
  // (the clips' whites are brighter than the stills': a key light a touch under white keeps the outfit out of the bloom)
  // (the rim's offset is in the frame's own UV, as on a still; scaled down with a crop)
  // (o.crop [x0, y0, x1, y1]: part of the frame (fractions), h then being that part's height; o.blend: cross-fade into the next
  // frame, for a slow clip)
  // (each frame is drawn from a texture of that frame alone, so the UV here is only ever the frame's own crop)
  const uv = o.crop ?? [0, 0, 1, 1];
  const look = { rim: (MEM[key] ?? MEM.TOKI).glow, rimK: .9, rimDir: [-.0045 * (uv[2] - uv[0]), .0035 * (uv[3] - uv[1])], light: '#DCD8E6', shade: '#8C84A4', h: 1.9, beat: 0, ...o };
  if (o.crop) look.h = (o.h ?? 1.9) * (o.crop[3] - o.crop[1]);
  const r = figure(F.name, { ...look, uv, srcOf: im => frameTex(im, S, F.cell) });
  if (o.blend && F.next && F.k > .02) figure(F.next.name, { ...look, uv, srcOf: im => frameTex(im, S, F.next.cell), alpha: (o.alpha ?? 1) * F.k, shadow: false, cast: undefined, reflect: 0 });
  return r;
}
// clip2D(g, clip, t, o, x, y, w, h): a clip's frame drawn flat into a 2D canvas, fitted to the height of the rect (x, y, w, h) and
// centred in it (o as clipFrame(): t0, from, rate, loop, to, hold)
function clip2D(g, clip, t, o, x, y, w, h) {
  const F = clipFrame(clip, t, o), S = SPRITES[clip], r = F && cellRect(pic(F.name), S, F.cell);
  if (!r) return;
  const dw = h * S.fw / S.fh;
  g.drawImage(pic(F.name), ...r, x + (w - dw) / 2, y, dw, h);
}
// unison(set, t, o): the four dancing one choreography in unison: each member's clip of the set (`toki_${set}`, ...: one lead dance
// transferred to each of them frame for frame, packed on one shared box so they share a scale), on her mark, the frames in step.
// o: at {TOKI: [x, y, z], ...} (the marks; members left out aren't drawn), h (the box's height in metres), t0, from, rate, hold (as
// dancer()), and anything else for dancer() (reflect, shadow, light, rimK...), or per member in o.each[key].
const UNISON_AT = { RELU: [-2.0, 0, 0], TOKI: [-.65, 0, .45], ADA: [.7, 0, .2], LOGI: [2.05, 0, -.1] };
function unison(set, t, o = {}) {
  const at = o.at ?? UNISON_AT;
  // (back to front)
  for (const m of Object.keys(at).sort((a, b) => at[a][2] - at[b][2]))
    dancer(m, `${m.toLowerCase()}_${set}`, t, { h: 1.8, ...o, ...(o.each?.[m] ?? {}), at: at[m] });
}
// CHOREO: the chorus's point dance, the same moves in every chorus, a part to a line: each part plays a stretch of one unison set,
// its key frame landing on its word. hook: "We didn't start the scaling" (the point to the sky as "scaling" starts, then the finger
// wag and a knee lift); training: "It was always training," (the groove); gaining: "and the curves kept gaining," (both arms climbing,
// step by step, like the chart); contain: "No, we didn't preordain it, but we can't contain it!" (arms crossed in an X, flung open on
// "contain", and a jump).
const CHOREO = {
  hook: { set: 'u1', frame: 12, word: 4, lead: .2 },
  training: { set: 'uT', frame: 2, word: 0, lead: .05 },
  gaining: { set: 'uG', frame: 2, word: 4, lead: .05 },
  contain: { set: 'uC', frame: 18, word: 8, lead: .1 },
};
// chorusDance(part, t, ln, o): the four dancing a part of the chorus in unison, as sung in line ln (o as unison(); o.member: one
// member alone, her own clip of the set)
function chorusDance(part, t, ln, o = {}) {
  const C = CHOREO[part], w = wordsOf(ln)[C.word], t0 = w.start - (C.lead ?? 0);
  // (o.clip: her own sharper take of the same frames, for a shot close on her)
  if (o.member) return dancer(o.member, o.clip ?? `${o.member.toLowerCase()}_${C.set}`, t, { h: 1.8, ...o, t0, from: C.frame });
  unison(C.set, t, { ...o, t0, from: C.frame });
}
// idol(key, pose, o): a member (see figure(); her rim light defaults to her glow).
const idol = (key, pose, o = {}) => figure(`${key.toLowerCase()}_${pose}`, { rim: (MEM[key] ?? MEM.TOKI).glow, ...o });
// the pose a member holds at time t, cutting between `poses` every `every` beats (the stutter of a choreography edit), and the white
// flash of each cut
function poseAt(t, poses, every = 2, seed = 0) {
  const n = Math.floor(bpOf(t) / every), p = poses[(n + seed) % poses.length];
  const since = (bpOf(t) / every - n) * every * beatLen();
  return { pose: p, flash: poses.length > 1 ? .3 * Math.exp(-since * 40) : 0 };
}

// =====================================================================================================
// SETS
// =====================================================================================================
// stage(o): the MV set: an ink void, a glitter floor, a glowing horizon, light columns and drifting dust, lit in one accent.
// o: accent, at (where the performer stands: the light pool and ring), ring (the ring mark's radius, 0 for none), columns (how many),
// dust, glow (the horizon's strength), glitter.
function stage(o = {}) {
  const acc = o.accent ?? PAL.pearl, at = o.at ?? [0, 0, 0];
  sky({ top: '#030208', horizon: mixCol('#0E0B1A', acc, .12), glow: mixCol(acc, PAL.pearl, .25), glowK: o.glow ?? .2, glowW: .035 });
  floor({ base: '#040309', pool: [at[0], at[2], 2.6, o.pool ?? .16], poolCol: acc, glitter: mixCol(PAL.pearl, acc, .35), glitterK: o.glitter ?? 1.5,
    fog: mixCol('#0E0B1A', acc, .18), fogD: 70, refl: .3, ring: o.ring === 0 ? undefined : [at[0], at[2], o.ring ?? 1.05, .9], ringCol: mixCol(acc, PAL.pearl, .3) });
  const nc = o.columns ?? 7;
  for (let i = 0; i < nc; i++) {
    const x = (i - (nc - 1) / 2) * 5.5 + at[0], z = -22 - (i % 2) * 6, k = .16 + .1 * Math.sin(T * .7 + i * 1.7);
    plane(TX.beam, { at: [x, 0, z], h: 26, w: 1.3, blend: 'add', mul: mixCol(acc, PAL.pearl, .5), alpha: k, grid: false });
  }
  if (o.dust !== 0) particles('dust', { n: o.dust ?? 900, a: [at[0], 2.6, at[2] - 3], b: [9, 2.8, 8], c: [1, 0, 0, 0], size: .018, cols: [PAL.pearl, mixCol(acc, PAL.pearl, .4)], gain: .7 });
  GRADE.lift = '#050309';
}
// cove(o): the teaser studio: a pearl infinity cove, high-key, with soft shadows. o: tint (the light's colour), at, horizonY, spot.
// o.night (0..1) turns the lights down to a blue night.
function cove(o = {}) {
  const tint = o.tint ?? PAL.pearl, at = o.at ?? [0, 0, 0], n = o.night ?? 0;
  const top = mixCol(mixCol('#D4CEE0', tint, .25), '#0A0C24', n), hor = mixCol(mixCol('#F7F4FB', tint, .15), '#1E2352', n);
  sky({ top, horizon: hor, glowK: 0, horizonY: o.horizonY, spot: o.spot ?? [.5, .6, .5, .12], spotCol: o.spotCol ?? '#FFFFFF' });
  floor({ base: mixCol(mixCol('#E7E2EE', tint, .12), '#15183A', n), pool: [at[0], at[2], 3.2, .1 * (1 - n) + .05], poolCol: o.spotCol ?? '#FFFFFF', glitterK: n * .6, glitter: '#AFC0FF',
    fog: mixCol(mixCol('#F3EFF8', tint, .15), '#1E2352', n), fogD: 26, refl: 0 });
  GRADE.thresh = lerp(.96, .75, n); GRADE.bloom = lerp(.35, .8, n); GRADE.vignette = lerp(.22, .5, n); GRADE.grain = .03; GRADE.ca = .003;
}

// =====================================================================================================
// PHOTOCARDS: the collectible card in every K-pop album, which carries the people in the lyrics
// =====================================================================================================
// photocard(key, o): a card 0.62 × 0.96 m (o.w scales it) with a picture on the front and a handwritten message on the back, a pearl
// frame and a holographic foil that shifts as it turns. o: pic (a PIC name), name, sub (the small line under the name), note (the back's
// message) and sign, col (the accent), at [x, y, z] (its centre), yaw (0 faces +z; π shows the back), tilt, roll, fold (0..1: the right
// half folds over the left, about the card's centre line), alpha, gain.
function cardFace(key, o) {
  return panel(`card-${key}`, 620, 960, (g, w, h) => {
    g.save(); g.beginPath(); g.roundRect(0, 0, w, h, 34); g.clip();
    g.fillStyle = '#F7F4FB'; g.fillRect(0, 0, w, h);
    const im = pic(o.pic);
    if (im) { const k = Math.max((w - 36) / im.width, (h - 190) / im.height); g.save(); g.beginPath(); g.roundRect(18, 18, w - 36, h - 190, 20); g.clip(); g.drawImage(im, 18 + (w - 36 - im.width * k) / 2, 18, im.width * k, im.height * k); g.restore(); }
    txt(g, o.name ?? '', 34, h - 106, 44, { font: 'display', col: PAL.text, maxW: w - 60 });
    txt(g, o.sub ?? '', 36, h - 62, 16, { font: 'wide', col: mixCol(o.col ?? PAL.text, PAL.text, .45), track: .16 });
    txt(g, 'ATTN! · HEADS EDITION', w - 34, h - 30, 11, { font: 'mono', col: PAL.dim, align: 'right', track: .1 });
    g.restore();
  }, { stamp: FULL.has(o.pic) });
}
function cardBack(key, o) {
  return panel(`cardback-${key}`, 620, 960, (g, w, h) => {
    g.save(); g.beginPath(); g.roundRect(0, 0, w, h, 34); g.clip();
    g.fillStyle = '#F4F0FA'; g.fillRect(0, 0, w, h);
    g.strokeStyle = 'rgb(20 16 32 / .08)'; g.lineWidth = 2;
    for (let y = 150; y < h - 120; y += 64) { g.beginPath(); g.moveTo(50, y); g.lineTo(w - 50, y); g.stroke(); }
    const words = (o.note ?? '').split(' '); let line = '', y = 136;
    g.font = fontOf(FONT.hand, 32);
    for (const wd of words) { const tl = line ? line + ' ' + wd : wd; if (g.measureText(tl).width > w - 110) { txt(g, line, 58, y, 32, { font: 'hand', col: '#2A2240', rot: -.02 }); y += 64; line = wd; } else line = tl; }
    if (line) txt(g, line, 58, y, 32, { font: 'hand', col: '#2A2240', rot: -.02 });
    txt(g, o.sign ?? '', w - 70, y + 110, 40, { font: 'hand', col: o.col ?? PAL.text, align: 'right', rot: -.06 });
    txt(g, 'ATTN!', w / 2, h - 60, 30, { font: 'display', col: 'rgb(20 16 32 / .18)', align: 'center' });
    g.restore();
  }, { stamp: 1 });
}
function holo(shift) {
  const k = Math.round(frac(shift) * 60) / 60;
  return panel('holo', 310, 480, (g, w, h) => {
    g.save(); g.beginPath(); g.roundRect(0, 0, w, h, 17); g.clip();
    const gr = g.createLinearGradient(-w + k * 2 * w, 0, k * 2 * w, h);
    ['#FF6FB0', '#FFD36E', '#8BF5C9', '#7EB8FF', '#C59BFF', '#FF6FB0'].forEach((c, i) => gr.addColorStop(i / 5, c));
    g.globalAlpha = .55; g.fillStyle = gr; g.fillRect(0, 0, w, h);
    g.globalCompositeOperation = 'destination-in';
    const m = g.createLinearGradient(0, 0, w, h); m.addColorStop(0, 'rgb(0 0 0 / 0)'); m.addColorStop(clamp(k - .05, 0, 1), 'rgb(0 0 0 / 0)'); m.addColorStop(clamp(k + .12, 0, 1), 'rgb(0 0 0 / 1)'); m.addColorStop(clamp(k + .3, 0, 1), 'rgb(0 0 0 / 0)'); m.addColorStop(1, 'rgb(0 0 0 / 0)');
    g.fillStyle = m; g.fillRect(0, 0, w, h);
    g.restore();
  }, { stamp: k });
}
function photocard(key, o = {}) {
  const w = .62 * (o.w ?? 1), h = w * 960 / 620, at = o.at ?? [0, 1.2, 0], yaw = o.yaw ?? 0, fold = o.fold ?? 0;
  const front = cardFace(key, o), back = cardBack(key, o);
  const facingFront = Math.cos(yaw) >= 0;
  const common = { tilt: o.tilt ?? 0, roll: o.roll ?? 0, grid: false, alpha: o.alpha ?? 1, gain: o.gain ?? 1 };
  if (fold <= 0) {
    plane(facingFront ? front : back, { ...common, at, w, anchor: [.5, .5], facing: facingFront ? yaw : yaw + Math.PI });
    if (facingFront && o.holo !== false) plane(holo(yaw * .35 + T * .08), { ...common, at, w, anchor: [.5, .5], facing: yaw, blend: 'add', alpha: (o.alpha ?? 1) * .5 });
  } else {
    // the left half stays; the right half turns about the centre line toward the camera and over
    const th = fold * Math.PI * .97;
    plane(front, { ...common, at, w: w / 2, uv: [0, 0, .5, 1], anchor: [1, .5], facing: yaw });
    const hinge = at;
    const a2 = yaw + th, show = Math.cos(th) >= 0;
    plane(show ? front : back, { ...common, at: hinge, w: w / 2, uv: show ? [.5, 0, 1, 1] : [0, 0, .5, 1], anchor: show ? [0, .5] : [1, .5], facing: show ? a2 : a2 + Math.PI, mul: show ? '#FFFFFF' : '#D8D2E4' });
  }
}

// =====================================================================================================
// THE MUSIC SHOW
// =====================================================================================================
// showStage(t, o): the music show's stage (MUSIC CURVE): a raised platform (performers stand at y = .9), the LED wall behind with the
// show's logo, and the HEADS' lightsticks in front. o: ledGain, lights (0..1: the stage's lights going down at the end of a broadcast),
// ocean (0..1).
function showStage(t, o = {}) {
  const on = o.lights ?? 1;
  sky({ top: '#030208', horizon: mixCol('#030208', '#150F26', on), glow: PAL.pearl, glowK: .12 * on, glowW: .05 });
  floor({ base: '#05040A', pool: [0, 0, 5, .12 * on], poolCol: PAL.pearl, glitter: PAL.pearl, glitterK: .8 * on, fog: mixCol('#030208', '#150F26', on), fogD: 60, refl: .2 });
  const led = panel('mc-led', 1920, 640, (g, w, h) => {
    g.fillStyle = '#07060D'; g.fillRect(0, 0, w, h);
    const gr = g.createLinearGradient(0, 0, w, 0); ORDER.forEach((k, i) => gr.addColorStop(i / 3, MEM[k].col));
    // (o.led paints the wall's content, as a music show's wall carries the lyrics or the result; the show's logo goes in the corner)
    g.strokeStyle = gr; g.lineWidth = 26; g.lineCap = 'round'; g.globalAlpha = o.led ? .35 : 1;
    g.beginPath(); for (let x = 0; x <= 1; x += .01) { const X = 120 + x * (w - 240), Y = h - 90 - (Math.exp(x * 4.2) - 1) / (Math.E ** 4.2 - 1) * (h - 170); x ? g.lineTo(X, Y) : g.moveTo(X, Y); } g.stroke();
    g.globalAlpha = 1;
    if (o.led) { o.led(g, w, h); txt(g, 'MUSIC CURVE', w - 50, h - 36, 36, { font: 'display', col: '#FFFFFF', align: 'right', alpha: .85 }); }
    else {
      txt(g, 'MUSIC CURVE', 120, 190, 150, { font: 'display', col: '#FFFFFF' });
      txt(g, 'LIVE', 126, 250, 34, { font: 'wide', col: '#FFFFFF', track: .3, alpha: .8 });
    }
    // (an LED wall's pixel grid)
    g.fillStyle = 'rgb(0 0 0 / .55)';
    for (let x = 0; x < w; x += 8) g.fillRect(x, 0, 2, h);
    for (let y = 0; y < h; y += 8) g.fillRect(0, y, w, 2);
  }, o.ledStamp !== undefined ? { stamp: o.ledStamp } : o.led ? { live: true } : { stamp: 1 });
  plane(led, { at: [0, 1.2, -4], w: 13, facing: 0, grid: false, gain: (o.ledGain ?? 1.15) * on, alpha: .15 + .85 * on });
  // the platform
  plane(TX.white, { at: [0, 0, 1.4], w: 12, h: .9, facing: 0, grid: false, mul: '#26203A', bot: '#0C0A14' });
  plane(TX.white, { at: [0, .9, -1.4], w: 12, h: 5.6, tilt: Math.PI / 2, anchor: [.5, .5], facing: 0, grid: false, mul: '#1A1628', bot: '#1A1628' });
  plane(TX.white, { at: [0, .9, 1.4], w: 12, h: .03, facing: 0, anchor: [.5, .5], grid: false, mul: PAL.pearl, gain: 2 });
  // the lightstick ocean, swaying on the beat
  // (oceanNear: how far toward the camera the crowd reaches, for shots from inside it)
  particles('ocean', { n: Math.round(2600 * clamp(((o.oceanNear ?? 9) - 2.2) / 6.8, .2, 1)), a: [-9, 2.2, 9, o.oceanNear ?? 9], b: [12, .18, bpOf(t) / 2, .1], size: .075, cols: ORDER.map(k => MEM[k].glow), gain: 1.5 * (o.ocean ?? 1) });
}

// =====================================================================================================
// PERFORMANCE: lip-flap close-ups and the performance-line template
// =====================================================================================================
// SINGING. Each member's close-up (her *_sing picture) has eight faces painted over it as patches (tools/images.py build): the
// vowels ah, ee (a wide smile), oo (rounded) and oh; hum (closed, a soft smile), mb (lips pressed, the m/b/p closure), br (a small
// breath) and held (eyes softly closed on a long note). A line's words, spelled out, give the faces and their times: each
// syllable's vowel on its share of its word, an m/b/p onset closing the lips first, the held face once a long note has sounded,
// the lips closing between phrases and a breath before a line; one face eases into the next.
const VIS_EASE = .07;
const _LETTER = { a: 'ee', b: 'ee', c: 'ee', d: 'ee', e: 'ee', f: 'ee', g: 'ee', h: 'ah', i: 'ah', j: 'ee', k: 'ee', l: 'ee', m: 'ee', n: 'ee', o: 'oh',
  p: 'ee', q: 'oo', r: 'ah', s: 'ee', t: 'ee', u: 'oo', v: 'ee', w: 'oo', x: 'ee', y: 'ah', z: 'ee' };
const _DIGIT = ['ee oh', 'ah', 'oo', 'ee', 'oh', 'ah', 'ee', 'ee ee', 'ee', 'ah'];
// the vowel faces of a word's syllables, from its spelling
function vowelsOf(word) {
  const raw = word.replace(/[^A-Za-z0-9]/g, '');
  if (!raw) return [];
  // (spelled-out abbreviations and digits: a face per letter's name)
  if (/^[A-Z0-9]{2,}s?$/.test(raw) && /[A-Z0-9]{2}/.test(raw) || /^\d+$/.test(raw))
    return [...raw].flatMap(c => /\d/.test(c) ? _DIGIT[+c].split(' ') : [_LETTER[c.toLowerCase()]]);
  let w = raw.toLowerCase();
  if (w.length > 3 && /[^aeiou]e$/.test(w) && !/le$/.test(w)) w = w.slice(0, -1);
  w = w.replace(/^y(?=[aeiou])/, '');
  const out = [];
  for (const m of w.matchAll(/[aeiouy]+/g)) {
    const g = m[0];
    out.push(/oo|ou|ew|ue|ui/.test(g) ? 'oo' : /^o/.test(g) ? 'oh'
      : g === 'u' ? (m.index + 1 === w.length ? 'oo' : 'ah')
      : /^a/.test(g) ? 'ah' : 'ee');
  }
  return out.length ? out : ['ah'];
}
// the faces of a line: [[time, face]], from a little before its first word to after its last
const _visTracks = new Map();
function visTrack(ln) {
  let tr = _visTracks.get(ln);
  if (tr) return tr;
  const ws = wordsOf(ln), out = [];
  const push = (t, v) => { if (out.length && out.at(-1)[1] === v) return; if (out.length && t < out.at(-1)[0] + .025) out.at(-1)[1] = v; else out.push([t, v]); };
  // (a breath before the line, if there's room since the one before)
  const prev = LINES[LINES.indexOf(ln) - 1], gap = prev ? ws[0].start - wordsOf(prev).at(-1).end : 9;
  push(ws[0].start - 2, 'hum');
  if (gap > .6) push(ws[0].start - .32, 'br');
  let end = -Infinity;
  ws.forEach((w, i) => {
    if (i && w.start - end > .12) push(end + .03, 'hum');
    const vs = vowelsOf(w.text), d = w.end - w.start;
    let s0 = w.start;
    if (/^[^A-Za-z]*[mbpMBP]/.test(w.text) && d > .12) { push(w.start - .02, 'mb'); s0 = w.start + .05; }
    const held = d > .8, n = vs.length;
    const slot = held ? Math.min(.18, (d - .1) / n) : (w.end - s0) / n;
    vs.forEach((v, j) => push(s0 + j * slot, v));
    if (held) push(Math.min(w.end - .1, s0 + n * slot + .12), 'held');
    end = w.end;
  });
  push(end - .02, 'hum');
  _visTracks.set(ln, out);
  return out;
}
// the face at t: { a, b, k }: easing from face a into face b (k from 0 to 1)
function visemeAt(t, ln) {
  if (!ln) return { a: 'hum', b: 'hum', k: 1 };
  const tr = visTrack(ln);
  let i = tr.length - 1;
  while (i > 0 && tr[i][0] > t) i--;
  if (tr[i][0] > t) return { a: 'hum', b: 'hum', k: 1 };
  return { a: tr[i - 1]?.[1] ?? 'hum', b: tr[i][1], k: easeInOut(clamp((t - tr[i][0]) / VIS_EASE)) };
}
// the patches that paint face F over a close-up, in the order to draw them: [[picture, alpha]]. The held face covers more of the
// face than the mouth shapes do: it goes on top, at its own weight, over the mouth shape at full; two mouth shapes share one
// region, so the one being left sits underneath at full and the one arriving goes over it.
function visLayers(key, F) {
  const k = key.toLowerCase(), n = v => `${k}_v_${v}`;
  if (F.a === F.b || F.k >= 1) return [[n(F.b), 1]];
  if (F.b === 'held') return [[n(F.a), 1], [n('held'), F.k]];
  if (F.a === 'held') return [[n(F.b), 1], [n('held'), 1 - F.k]];
  return [[n(F.a), 1], [n(F.b), F.k]];
}
// singFace(key, F, basis, o): the face patches over a close-up drawn in the world (figure()'s return), lit as it is
function singFace(key, t, ln, fig, o = {}) {
  const base = PICS[`${key.toLowerCase()}_sing`];
  if (!fig?.basis || !base) return;
  const { O, R, U } = fig.basis;
  for (const [name, a] of visLayers(key, visemeAt(t, ln))) {
    const P = PICS[name], img = pic(name);
    if (!P || !img || a <= 0) continue;
    const u0 = P.x / base.w, u1 = (P.x + P.w) / base.w, v0 = 1 - (P.y + P.h) / base.h, v1 = 1 - P.y / base.h;
    const basis = { O: v3add(O, v3add(v3mul(R, u0), v3mul(U, v0))), R: v3mul(R, u1 - u0), U: v3mul(U, v1 - v0) };
    plane(img, { basis, grid: false, alpha: a * (o.alpha ?? 1), mul: mixCol(fig.bot, fig.mul, v1), bot: mixCol(fig.bot, fig.mul, v0), gain: o.gain });
  }
}
// singFace2D(g, key, t, ln, x, y, w, h): the same over a close-up drawn flat into a 2D canvas at (x, y, w, h)
function singFace2D(g, key, t, ln, x, y, w, h) {
  const base = PICS[`${key.toLowerCase()}_sing`];
  if (!base) return;
  for (const [name, a] of visLayers(key, visemeAt(t, ln))) {
    const P = PICS[name], img = pic(name);
    if (!P || !img || a <= 0) continue;
    g.save(); g.globalAlpha *= a;
    g.drawImage(img, x + P.x / base.w * w, y + P.y / base.h * h, P.w / base.w * w, P.h / base.h * h);
    g.restore();
  }
}
// closeUp(key, t, ln, o): a member's singing close-up in the world, her face singing the line.
// o: at [x, y, z] (the bottom centre of the picture), h (metres, default 1.15), rim, light, shade, facing, gain, alpha.
function closeUp(key, t, ln, o = {}) {
  const k = key.toLowerCase(), M = MEM[key];
  // (she moves a little with the song, all of a piece, so the face patches stay on her: a bob on the beat and a slow sway)
  const at = o.at ?? [0, .45, 0], b = bpOf(t), h = o.h ?? 1.15;
  const bob = [.006 * h * Math.sin(t * .9 + hstr(key) * 6), .005 * h * Math.exp(-frac(b) * 4) - .0025 * h, 0];
  const fig = figure(`${k}_sing`, { at: [at[0] + bob[0], at[1] + bob[1], at[2]], h, rim: o.rim ?? M.glow, rimK: o.rimK ?? 1.2,
    rimDir: [-.003, .0025], shadow: false, beat: 0, light: o.light, shade: o.shade ?? '#9A8CB6', facing: o.facing ?? 0, anchor: [.5, 1], gain: o.gain, alpha: o.alpha, fadeB: o.fadeB });
  singFace(key, t, ln, fig, o);
  return fig;
}
// perf(key, t, o): a performance line: the singer on a set, the line set big beside her. o: size ('wide' | 'medium' | 'close'), set
// ('stage' | 'cove' | 'show'), side (-1: she stands left, the words right; 1: the reverse), poses (for wide and medium), markup, lyric
// (extra lyric() options), cam (extra camera offsets {x, y, z}), ln (default the window's line).
function perf(key, t, o = {}) {
  const c = cutAt(t), ln = o.ln ?? lineOf(c.key), p = clamp((t - c.start) / (c.end - c.start)), M = MEM[key], side = o.side ?? (hstr(c.key) < .5 ? -1 : 1);
  const size = o.size ?? 'medium', set = o.set ?? 'stage';
  const at = [side * .95, 0, 0];
  if (size === 'close') {
    cam({ pos: [at[0] * .25 + side * lerp(.12, .04, p), 1.42, lerp(2.2, 1.85, easeOut(p))], at: [at[0] * .78, 1.35, 0], fov: 30 });
    if (set === 'cove') cove({ at }); else if (set === 'show') showStage(t, { ocean: .5 }); else stage({ accent: M.col, at, ring: 0, columns: 5 });
    particles('dust', { n: 500, a: [at[0], 1.5, -1.2], b: [2.5, 1.2, 1.5], c: [.8], size: .012, cols: [M.glow, PAL.pearl], gain: .8 });
    closeUp(key, t, ln, { at: [at[0], .52, 0], h: 1.18, light: set === 'cove' ? '#FFFFFF' : undefined, shade: set === 'cove' ? '#E0D8EA' : undefined });
  } else {
    // (on the music show's stage she stands on its 0.9 m platform: the camera rises with her)
    const lift = set === 'show' ? .9 : 0;
    const dist = size === 'wide' ? lerp(5.4, 4.7, p) : lerp(3.3, 2.9, easeOut(p)), camY = (size === 'wide' ? 1.2 : 1.25) + lift;
    cam({ pos: [at[0] * .35 - side * .25 + (o.cam?.x ?? 0), camY + (o.cam?.y ?? 0), dist + (o.cam?.z ?? 0)], at: [at[0] * .72, (size === 'wide' ? 1.0 : 1.18) + lift, 0], fov: size === 'wide' ? 30 : 32 });
    if (set === 'cove') { cove({ at }); lightShot(); }
    else if (set === 'show') showStage(t, { ocean: .7 });
    else stage({ accent: M.col, at, ring: size === 'wide' ? 1.05 : 0 });
    const look = { at: [at[0], set === 'show' ? .9 : 0, at[2]], reflect: set === 'stage' ? .22 : 0, shadow: set !== 'show', cast: set === 'cove' ? [-1.2, -1.8, .2] : undefined,
      shade: set === 'cove' ? '#DAD2E6' : undefined, rimK: set === 'cove' ? .35 : undefined, rim: set === 'cove' ? M.soft : undefined };
    // o.clip: she dances a sprite clip (o.clipFrom, o.clipT0) instead of cutting between poses
    if (o.clip) dancer(key, o.clip, t, { ...look, from: o.clipFrom, t0: o.clipT0, h: 1.95, figH: 1.72 });
    else {
      const P = poseAt(t, o.poses ?? ['concept', 'point', 'dance'], o.every ?? 2, Math.floor(hstr(c.key) * 3));
      idol(key, P.pose, { ...look, flash: P.flash });
    }
    if (set === 'stage') particles('glitter', { n: 400, a: [at[0], 0, 0, 1.2], size: .03, cols: [M.glow, PAL.pearl], shape: 'star', gain: .9 });
  }
  if (o.lyric === false || !ln) return;
  const g = layer(), ink = set === 'cove' ? PAL.text : PAL.pearl;
  lyric(g, ln, t, { x: side < 0 ? 1790 : 130, y: o.y ?? 430, align: side < 0 ? 'right' : 'left', size: o.lsize ?? 92, maxW: 900, col: ink, accent: M.col, markup: o.markup ?? autoMarkup(ln.text), italic: 'serifI', shadow: set === 'show' ? ['rgb(0 0 0 / .85)', 26] : undefined, ...o.lyric });
  if (o.after) o.after(g);
  put(g, { gain: set === 'cove' ? 1 : 1.05 });
  hideSub();
}

// =====================================================================================================
// INTERFACES IN THE DARK, AND THEIR PANELS
// =====================================================================================================
// uiSet(acc, o): the ink void an interface floats in: a faint horizon haze in the accent and drifting dust.
function uiSet(acc, o = {}) {
  sky({ top: '#030208', horizon: mixCol('#0A0814', acc, .1), glow: acc, glowK: o.glow ?? .08, horizonY: o.horizonY ?? .42 });
  if (o.floor) floor({ base: '#040309', pool: [0, 0, 3, .1], poolCol: acc, glitter: PAL.pearl, glitterK: .8, fog: mixCol('#0A0814', acc, .1), fogD: 50, refl: .2 });
  particles('dust', { n: o.dust ?? 700, a: [0, 0, -2], b: [8, 5, 5], c: [1], size: .02, cols: [PAL.pearl, mixCol(acc, PAL.pearl, .4)], gain: .6 });
}
// wrap(text, width, size, fam): the lines a text breaks into
function wrap(text, width, size, fam) {
  const out = []; let cur = '';
  for (const w of String(text).split(' ')) { const tl = cur ? cur + ' ' + w : w; if (textW(tl, size, fam) > width && cur) { out.push(cur); cur = w; } else cur = tl; }
  if (cur) out.push(cur);
  return out;
}
// avatar(g, name, x, y, r): a round avatar from a picture (a portrait), or a coloured disc with an initial
function avatar(g, name, x, y, r, o = {}) {
  g.save(); g.beginPath(); g.arc(x, y, r, 0, TAU); g.clip();
  g.fillStyle = o.col ?? '#3A3452'; g.fillRect(x - r, y - r, 2 * r, 2 * r);
  const im = name && pic(name);
  if (im) { const [u0, v0, u1, v1] = o.crop ?? [0, 0, 1, 1]; const sw = (u1 - u0) * im.width, sh = (v1 - v0) * im.height, k = 2 * r / Math.min(sw, sh); g.drawImage(im, u0 * im.width, v0 * im.height, sw, sh, x - sw * k / 2, y - sh * k / 2, sw * k, sh * k); }
  else if (o.initial) txt(g, o.initial, x, y + r * .36, r, { font: 'uiB', col: '#FFFFFF', align: 'center' });
  g.restore();
}
// postPanel(key, o): a social post, 900 wide. o: avatar (a picture name), crop, initial, name, handle, text, date, caps (upper-case the
// text), hi ([word, colour]: a word lit in the text), dark (default true), stats, h (height, default fitted), stamp.
function postPanel(key, o) {
  const fam = FONT.ui, size = o.size ?? 34, lines = wrap(o.caps ? o.text.toUpperCase() : o.text, 800, size, fam);
  const h = o.h ?? 200 + lines.length * size * 1.3 + 70;
  return panel(key, 900, h, (g, w) => {
    g.fillStyle = o.dark === false ? '#FFFFFF' : '#0E0C16'; g.beginPath(); g.roundRect(0, 0, w, h, 26); g.fill();
    g.strokeStyle = 'rgb(244 240 250 / .12)'; g.lineWidth = 2; g.stroke();
    const ink = o.dark === false ? PAL.text : PAL.pearl;
    avatar(g, o.avatar, 70, 76, 36, { crop: o.crop, initial: o.initial, col: o.avatarCol });
    txt(g, o.name, 124, 68, 28, { font: 'uiB', col: ink });
    txt(g, o.handle ?? '', 124 + textW(o.name + '  ', 28, FONT.uiB), 68, 24, { font: 'ui', col: PAL.dim });
    txt(g, o.date ?? '', 124, 102, 20, { font: 'mono', col: PAL.dim });
    lines.forEach((l, i) => {
      const y = 170 + i * size * 1.3;
      if (o.hi && l.includes(o.hi[0])) {
        const [pre] = l.split(o.hi[0]);
        txt(g, pre, 50, y, size, { font: 'ui', col: ink });
        txt(g, o.hi[0], 50 + textW(pre, size, fam), y, size, { font: 'uiB', col: o.hi[1] });
        txt(g, l.slice(pre.length + o.hi[0].length), 50 + textW(pre + o.hi[0], size, fam), y, size, { font: 'ui', col: ink });
      } else txt(g, l, 50, y, size, { font: 'ui', col: ink });
    });
    if (o.stats) txt(g, o.stats, 50, h - 40, 22, { font: 'mono', col: PAL.dim });
  }, { stamp: o.stamp ?? 1 });
}
// docPanel(key, o): a sheet of paper: o.w, o.h, head (bold), sub (lines under it), date, bars (how many grey text lines), hi (a highlighted
// line [text, colour], after the bars' first third), foot, dark (a dark sheet), stamp.
function docPanel(key, o) {
  const w = o.w ?? 700, h = o.h ?? 900;
  return panel(key, w, h, (g) => {
    g.fillStyle = o.dark ? '#14111E' : '#F8F6FB'; g.beginPath(); g.roundRect(0, 0, w, h, 10); g.fill();
    const ink = o.dark ? PAL.pearl : PAL.text;
    let y = 100;
    if (o.head) { for (const l of wrap(o.head, w - 120, 34, FONT.uiB)) { txt(g, l, 60, y, 34, { font: 'uiB', col: ink }); y += 44; } }
    for (const l of [].concat(o.sub ?? [])) { txt(g, l, 60, y, 24, { font: 'serif', col: ink }); y += 34; }
    if (o.date) { txt(g, o.date, 60, y + 6, 18, { font: 'mono', col: PAL.dim }); y += 30; }
    y += 30;
    const bars = o.bars ?? 12, hiAt = Math.floor(bars / 3);
    for (let i = 0; i < bars; i++) {
      if (o.hi && i === hiAt) {
        const ls = wrap(o.hi[0], w - 140, 24, FONT.ui);
        g.fillStyle = alpha(o.hi[1], .28); g.fillRect(52, y - 8, w - 104, ls.length * 34 + 12);
        ls.forEach((l, k) => txt(g, l, 60, y + 20 + k * 34, 24, { font: 'ui', col: ink }));
        y += ls.length * 34 + 22; continue;
      }
      g.fillStyle = o.dark ? 'rgb(244 240 250 / .1)' : 'rgb(13 11 22 / .1)'; g.fillRect(60, y, (i % 5 === 4 ? .55 : .9) * (w - 120), 13); y += 36;
    }
    if (o.foot) txt(g, o.foot, 60, h - 50, 20, { font: 'mono', col: PAL.dim });
  }, { stamp: o.stamp ?? 1 });
}
// stampPanel(text, col, o): a round rubber stamp (o.top: a small line above; o.size: the text's size)
function stampPanel(text, col, o = {}) {
  return panel(`stamp-${text}-${col}`, 520, 520, (g, W_, H_) => {
    g.strokeStyle = col; g.lineWidth = 16; g.beginPath(); g.arc(W_ / 2, H_ / 2, 230, 0, TAU); g.stroke();
    g.lineWidth = 5; g.beginPath(); g.arc(W_ / 2, H_ / 2, 196, 0, TAU); g.stroke();
    txt(g, text, W_ / 2, H_ / 2 + (o.size ?? 110) * .35, o.size ?? 110, { font: 'display', align: 'center', col, maxW: 380 });
    if (o.top) txt(g, o.top, W_ / 2, H_ / 2 - 80, 30, { font: 'wide', align: 'center', col, track: .3 });
  }, { stamp: 1 });
}
// slam(k): a stamp or sticker coming down (scale from 1.8 to 1, easing in), for k = 0..1 over its first ~0.1 s
const slam = k => lerp(1.8, 1, easeIn(clamp(k)));

// =====================================================================================================
// REACTION CAMS: a variety show's picture-in-picture of a member reacting
// =====================================================================================================
// reactCam(g, key, pose, t, t0, o): into the 2D layer g, from t0 on, a rounded window with the member's face in it (the top of her
// close-up), popping in. o: x, y (top-left), w (its width; 4:5), crop [u0, v0, u1, v1] of the picture (default the top of a close-up),
// label (default her name).
function reactCam(g, key, pose, t, t0, o = {}) {
  if (t < t0) return;
  const M = MEM[key], im = pic(`${key.toLowerCase()}_${pose}`);
  if (!im) return;
  const k = backOut(clamp((t - t0) / .22), 2.2), w = o.w ?? 320, h = w * 1.2, x = o.x ?? 1500, y = o.y ?? 600;
  const [u0, v0, u1, v1] = o.crop ?? [.08, 0, .92, .7];
  g.save();
  g.translate(x + w / 2, y + h / 2); g.scale(k, k); g.rotate((1 - k) * .1 + (o.rot ?? .02)); g.translate(-w / 2, -h / 2);
  g.beginPath(); g.roundRect(0, 0, w, h, 26); g.save(); g.clip();
  const gr = g.createLinearGradient(0, 0, 0, h); gr.addColorStop(0, mixCol(M.col, '#FFFFFF', .55)); gr.addColorStop(1, mixCol(M.col, '#FFFFFF', .2));
  g.fillStyle = gr; g.fillRect(0, 0, w, h);
  const sw = (u1 - u0) * im.width, sh = (v1 - v0) * im.height, sc = Math.max(w / sw, h / sh);
  g.drawImage(im, u0 * im.width, v0 * im.height, sw, sh, (w - sw * sc) / 2, h - sh * sc, sw * sc, sh * sc);
  g.restore();
  g.lineWidth = 6; g.strokeStyle = '#FFFFFF'; g.stroke();
  g.fillStyle = M.col; g.beginPath(); g.roundRect(16, h - 50, textW(o.label ?? key, 18, FONT.display) + 28, 36, 18); g.fill();
  txt(g, o.label ?? key, 30, h - 25, 18, { font: 'display', col: '#FFFFFF' });
  g.restore();
}

// =====================================================================================================
// TYPE
// =====================================================================================================
const fontOf = (fam, size) => `${size}px "${fam}"`;
const _mw = new Map();
function textW(s, size, fam, track = 0) {
  const k = `${fam}|${s}`;
  let w = _mw.get(k);
  if (w === undefined) { const g = MEASURE; g.font = fontOf(fam, 100); g.letterSpacing = '0px'; w = g.measureText(s).width / 100; _mw.set(k, w); }
  return w * size + track * size * s.length;
}
const MEASURE = makeCanvas(8, 8).getContext('2d');
// txt(g, s, x, y, size, o): one run of text. o: font (a FONT key or family), col, align, base ('alphabetic' | 'middle' | 'top'),
// track (letter spacing in em), alpha, rot, sx (horizontal scale), skew, stroke [colour, width], shadow [colour, blur, dy].
function txt(g, s, x, y, size, o = {}) {
  const fam = FONT[o.font] ?? o.font ?? FONT.display;
  g.save();
  g.translate(x, y);
  if (o.rot) g.rotate(o.rot);
  if (o.skew) g.transform(1, 0, o.skew, 1, 0, 0);
  g.font = fontOf(fam, size);
  let sx = o.sx ?? 1;
  if (o.maxW) { g.letterSpacing = `${(o.track ?? 0) * size}px`; const mw = g.measureText(s).width * sx; if (mw > o.maxW) sx *= o.maxW / mw; }
  if (sx !== 1) g.scale(sx, 1);
  g.letterSpacing = `${(o.track ?? 0) * size}px`;
  g.textAlign = o.align ?? 'left'; g.textBaseline = o.base ?? 'alphabetic';
  g.globalAlpha *= o.alpha ?? 1;
  if (o.shadow) { g.shadowColor = o.shadow[0]; g.shadowBlur = o.shadow[1] * RS; g.shadowOffsetY = (o.shadow[2] ?? 0) * RS; }
  if (o.stroke) { g.lineWidth = o.stroke[1]; g.strokeStyle = o.stroke[0]; g.lineJoin = 'round'; g.strokeText(s, 0, 0); }
  g.fillStyle = o.col ?? PAL.pearl;
  g.fillText(s, 0, 0);
  if (TEXT_AUDIT) auditText(g, s);
  g.restore();
}
// A debug audit (studio.html?audit): every run of text that spills past the edge of the canvas it's drawn into (a panel, or the frame)
// is recorded in TEXT_AUDIT, with the song time: the class of bug where a label is cut off by its card.
const TEXT_AUDIT = typeof location !== 'undefined' && new URLSearchParams(location.search).has('audit') ? [] : null;
function auditText(g, s) {
  // (a layer's drawing is recorded, not drawn on its context's canvas: the layer is the frame's size)
  const m = g.measureText(s), tf = g.getTransform(), c = _layerOf.has(g) ? { width: PW, height: PH } : g.canvas;
  const xs = [-m.actualBoundingBoxLeft, m.actualBoundingBoxRight], ys = [-m.actualBoundingBoxAscent, m.actualBoundingBoxDescent];
  let x0 = Infinity, x1 = -Infinity, y0 = Infinity, y1 = -Infinity;
  for (const x of xs) for (const y of ys) { const X = tf.a * x + tf.c * y + tf.e, Y = tf.b * x + tf.d * y + tf.f; x0 = Math.min(x0, X); x1 = Math.max(x1, X); y0 = Math.min(y0, Y); y1 = Math.max(y1, Y); }
  const pad = 2 * RS, over = Math.max(-x0, x1 - c.width, -y0, y1 - c.height);
  // (text meant to run off a frame edge, like a ticker, is marked with o.bleed by not using txt(); anything else is suspect)
  if (over > pad && g.globalAlpha > .05) TEXT_AUDIT.push({ t: +T.toFixed(2), s: s.slice(0, 60), canvas: `${c.width}x${c.height}`, over: Math.round(over) });
}

// Lyric markup: the line's text as it should be set, with "/" for line breaks, *word* for the accent (the singer's colour), _word_
// for the italic serif, and [1.4] at the start of a line to scale that line. Its words are matched in order to the sung words, so each
// takes its sung time (a word that isn't sung, like an added label, takes the time of the word before it).
const norm = s => s.toLowerCase().replace(/[^a-z0-9]/g, '');
function markupTokens(ln, markup) {
  const sung = wordsOf(ln);
  let cursor = 0;
  return markup.split('/').map((row, li) => {
    let scale = 1;
    row = row.trim().replace(/^\[([\d.]+)\]\s*/, (_, k) => { scale = +k; return ''; });
    const toks = row.split(/\s+/).filter(Boolean).map(raw => {
      const accent = /\*/.test(raw), italic = /_/.test(raw), text = raw.replace(/[*_]/g, '');
      const n = norm(text);
      let j = -1;
      for (let k = cursor; k < sung.length; k++) { const sn = norm(sung[k].text); if (sn && n && (sn === n || sn.startsWith(n) || n.startsWith(sn))) { j = k; break; } }
      const w = j >= 0 ? sung[j] : sung[Math.max(0, cursor - 1)];
      if (j >= 0) cursor = j + 1;
      return { text, accent, italic, start: w.start, end: w.end };
    });
    return { toks, scale, li };
  });
}
// lyric(g, ln, t, o): a block of kinetic type, word-timed. o: markup (default the line in capitals), x, y (the block's anchor: its first
// baseline), align ('left' | 'center' | 'right'), size, lead (line spacing, × size), font, italic (the italic words' font), col,
// accent, dim (the colour of words not yet sung, or null to hide them until sung), anim ('rise' | 'pop' | 'slam' | 'type' | 'track'),
// maxW (a line wider than this shrinks), track, shadow, now (underline the word being sung), hold (seconds a word keeps its accent
// after it ends), out ([t0, t1]: the block fades and lifts away between these). Returns the block's box and each word's box.
function lyric(g, ln, t, o = {}) {
  const rows = markupTokens(ln, o.markup ?? ln.text.toUpperCase());
  const size = o.size ?? 96, lead = o.lead ?? 1.02, fam = FONT[o.font] ?? o.font ?? FONT.display, famI = FONT[o.italic] ?? o.italic ?? FONT.serifI;
  const col = o.col ?? PAL.pearl, acc = o.accent ?? PAL.pearl, anim = o.anim ?? 'rise', align = o.align ?? 'left', track = o.track ?? 0;
  let y = o.y ?? 540, prevSz = 0;
  const out = o.out ? easeIn(seg(t, o.out[0], o.out[1])) : 0;
  const boxes = [];
  let minX = Infinity, maxX = -Infinity, top = Infinity, bot = -Infinity;
  for (const row of rows) {
    let sz = size * row.scale;
    // (the next baseline clears the row above's descenders and this row's capitals)
    if (prevSz) y += (prevSz * .24 + sz * .78) * lead;
    const space = sz * .28;
    const widths = row.toks.map(k => textW(k.text, sz, k.italic ? famI : fam, track) * (k.italic ? 1.08 : 1));
    let tw = widths.reduce((a, b) => a + b, 0) + space * (row.toks.length - 1);
    if (o.maxW && tw > o.maxW) { const k = o.maxW / tw; sz *= k; tw = o.maxW; widths.forEach((w, i) => widths[i] = w * k); }
    let x = (o.x ?? 960) - (align === 'center' ? tw / 2 : align === 'right' ? tw : 0);
    row.toks.forEach((k, i) => {
      const w = widths[i], age = t - k.start, on = age >= 0;
      const singing = t >= k.start && t < k.end + (o.hold ?? .12);
      const c = k.accent ? acc : singing && o.hot !== false ? mixCol(col, acc, .85) : col;
      if (on || o.dim) {
        const e = on ? easeOut5(age / (anim === 'slam' ? .12 : .22)) : 0;
        let a = on ? clamp(age / .05) : 1, sc = 1, dy = 0, tr = track;
        if (anim === 'rise') { dy = (1 - e) * sz * .35; sc = 1 + (1 - e) * .06; }
        else if (anim === 'pop') { sc = on ? Math.max(0, backOut(age / .2, 1.2)) : 1; }
        else if (anim === 'slam') { sc = lerp(1.7, 1, e); }
        else if (anim === 'track') { tr = track + (1 - e) * .35; }
        const cx = x + w / 2, cy = y - sz * .35;
        g.save();
        g.translate(cx, cy + dy - out * sz * .6); g.scale(sc, sc); g.translate(-cx, -cy);
        const alphaNow = (on ? a : 1) * (1 - out) * (o.alpha ?? 1);
        let s = k.text;
        if (anim === 'type' && on) s = s.slice(0, Math.ceil(s.length * clamp(age / Math.min(.3, Math.max(.08, k.end - k.start)))));
        const fill = on ? c : o.dim;
        // (a short vertical smear as a word lands: the motion blur of a fast move)
        if (on && e < 1 && anim !== 'type') for (let m = 1; m <= 2; m++) txt(g, s, x, y + m * sz * .06 * (1 - e), sz, { font: k.italic ? famI : fam, col: fill, alpha: alphaNow * .25 * (1 - e), track: tr, sx: k.italic ? 1.08 : 1 });
        txt(g, s, x, y, sz, { font: k.italic ? famI : fam, col: fill, alpha: alphaNow, track: tr, shadow: o.shadow, sx: k.italic ? 1.08 : 1 });
        if (o.now && singing && on) { g.fillStyle = acc; g.globalAlpha = alphaNow; g.fillRect(x, y + sz * .12, w * clamp((t - k.start) / Math.max(.05, k.end - k.start)), Math.max(3, sz * .045)); }
        g.restore();
      }
      boxes.push({ x, y: y - sz * .78, w, h: sz * .95, tok: k });
      minX = Math.min(minX, x); maxX = Math.max(maxX, x + w); top = Math.min(top, y - sz * .8); bot = Math.max(bot, y + sz * .2);
      x += w + space;
    });
    prevSz = sz;
  }
  return { x: minX, y: top, w: maxX - minX, h: bot - top, boxes, nextY: y + prevSz * .24 * lead };
}

// lyricStamp(ln, t): a panel stamp for a lyric drawn into a panel (an LED wall): it changes with each word sung, and every frame
// while the newest word is still animating in, so that the panel never freezes a word mid-animation.
function lyricStamp(ln, t) {
  if (!ln) return 'none';
  const ws = wordsOf(ln), n = ws.filter(w => t >= w.start).length, last = ws[n - 1];
  return `${ln.sec}${ln.n}|${n}|${last && t - last.start < .3 ? Math.floor(t * 60) : 's'}`;
}

// =====================================================================================================
// OVERLAYS: the subtitle, the comeback tag, the reference's date
// =====================================================================================================
// Per-frame switches a shot can call: hideSub() when the shot sets the lyric itself; hideTag() for full-frame interfaces; subStyle({y,
// col}) to move or recolour the subtitle; light() for pale shots (dark text).
let _noSub = false, _noTag = false, _subStyle = null, _light = false;
const hideSub = () => { _noSub = true; }, hideTag = () => { _noTag = true; }, subStyle = s => { _subStyle = s; }, lightShot = () => { _light = true; };

// The comeback rollout, the story's spine: which stage of it each part of the song shows, as a plain label (no day counts: the song's
// own references carry real dates, and two calendars on screen confuse). See STORYBOARD.md.
const ROLLOUT = [
  ['intro', 'COMEBACK'], ['V1.1', 'CONCEPT PHOTO \u00B7 TOKI'], ['V1.3', 'CONCEPT PHOTO \u00B7 RELU'], ['V1.5', 'CONCEPT PHOTO \u00B7 ADA'],
  ['V1.7', 'CONCEPT PHOTO \u00B7 LOGI'], ['V1.9', 'GROUP CONCEPT PHOTO'], ['V1.11', 'M/V TEASER'], ['V1.13', 'HIGHLIGHT MEDLEY'],
  ['V1.15', 'ALBUM PREVIEW'], ['C1', 'M/V PREMIERE'], ['V2.1', 'SHOWCASE'], ['V2.5', 'VARIETY'], ['V2.9', 'FAN-SIGN'],
  ['V2.13', 'DANCE CHALLENGE'], ['C2', 'MUSIC CURVE \u00B7 COMEBACK STAGE'], ['V3.1', 'HEADS \u00B7 STREAMING PARTY'], ['C3', 'MUSIC CURVE'],
  ['V4.1', 'ENCORE STAGE'], ['C4', 'ENCORE STAGE'],
];
const _segIndex = () => { const m = new Map(); SEGS.forEach((s, i) => m.set(s.key, i)); return m; };
let _segIdx = null;
function rolloutAt(s) {
  if (!s) return ROLLOUT[0];
  _segIdx ??= _segIndex();
  const i = _segIdx.get(s.key);
  let cur = ROLLOUT[0];
  for (const r of ROLLOUT) if ((_segIdx.get(r[0]) ?? Infinity) <= i) cur = r;
  return cur;
}
// Each verse line's date, as the reference's own timestamp (2017.06.12); the exact day where the song's stamp gives only a month.
const EXACT_DATE = { 'V1.1': '2017-06-12', 'V1.2': '2020-01-23', 'V1.3': '2020-05-28', 'V1.4': '2020-05-28', 'V1.6': '2023-02-16', 'V1.7': '2023-03-22', 'V1.8': '2023-03-29', 'V1.11': '2024-05-14', 'V2.1': '2025-01-20', 'V2.2': '2025-01-21', 'V2.3': '2025-02-02', 'V2.4': '2025-03-26', 'V2.6': '2025-06-30', 'V2.7': '2025-07-08', 'V2.15': '2025-11-19' };
const _MON = { JAN: 1, FEB: 2, MAR: 3, APR: 4, MAY: 5, JUN: 6, JUL: 7, AUG: 8, SEP: 9, OCT: 10, NOV: 11, DEC: 12 };
function stampOf(s) {
  if (!s || !s.date) return null;
  if (EXACT_DATE[s.key]) return EXACT_DATE[s.key].replaceAll('-', '.');
  const p = s.date.split(/\s+/), m = _MON[p[0]];
  if (!m) return `${p.at(-1)} · ${p[0]}`;
  return p.length === 3 ? `${p[2]}.${String(m).padStart(2, '0')}.${p[1].padStart(2, '0')}` : `${p[1]}.${String(m).padStart(2, '0')}`;
}
function overlays(t, s) {
  const g = layer();
  const ink = _light ? PAL.text : PAL.pearl;
  if (!_noTag) {
    const [, label] = rolloutAt(s), key = singerAt(s), acc = key ? MEM[key].col : PAL.pearl;
    txt(g, 'ATTN!', 72, 74, 22, { font: 'display', col: ink, alpha: .9 });
    txt(g, 'WE DIDN\u2019T START THE SCALING', 72 + textW('ATTN!', 22, FONT.display) + 16, 74, 13, { font: 'wide', col: ink, alpha: .65, track: .18 });
    g.fillStyle = _light && acc === PAL.pearl ? PAL.text : acc; g.beginPath(); g.arc(78, 104, 5, 0, TAU); g.fill();
    txt(g, label, 92, 110, 14, { font: 'wide', col: ink, alpha: .8, track: .2 });
    const st = stampOf(s);
    if (st) txt(g, st, 1848, 74, 18, { font: 'mono', col: ink, alpha: .7, align: 'right', track: .05 });
  }
  const cap = !_noSub && captionAt(t);
  if (cap) {
    const ln = cap.ln, key = singerOf(ln.sec, ln.n), M = key ? MEM[key] : null, st = _subStyle ?? {};
    const y = st.y ?? 1000, size = 34, words = wordsOf(ln), text = ln.text;
    const tw = textW(text, size, FONT.ui) + (words.length - 1) * 0, x0 = 960 - tw / 2;
    const chip = M ? M.key : 'ATTN!', chipCol = M ? M.col : PAL.pearl;
    const cw = textW(chip, 13, FONT.wide, .2);
    g.save();
    g.globalAlpha = clamp((t - cap.on) / .12);
    txt(g, chip, x0 - 22 - cw, y - 9, 13, { font: 'wide', col: chipCol, track: .2 });
    g.fillStyle = chipCol; g.beginPath(); g.arc(x0 - 12, y - 14, 3.5, 0, TAU); g.fill();
    // the line, with its sung words brightened as they're sung
    let x = x0;
    const shadow = [_light ? 'rgb(255 255 255 / .6)' : 'rgb(0 0 0 / .75)', 10, 1];
    for (const w of words) {
      const s = w.text + ' ', ww = textW(s, size, FONT.ui), sung = t >= w.start;
      txt(g, w.text, x, y, size, { font: 'ui', col: st.col ?? ink, alpha: sung ? 1 : .42, shadow });
      if (t >= w.start && t < w.end + .1) { g.fillStyle = chipCol; g.fillRect(x, y + 9, (ww - textW(' ', size, FONT.ui)) * clamp((t - w.start) / Math.max(.05, w.end - w.start)), 3); }
      x += ww;
    }
    g.restore();
  }
  put(g);
  _noSub = _noTag = _light = false; _subStyle = null;
}
FRAME_END.unshift(overlays);

// =====================================================================================================
// CAMERA HELPERS
// =====================================================================================================
// A beat "punch": the camera eases in a little on each downbeat of a bar and settles.
const punch = (t, k = 1) => k * Math.exp(-frac(bpOf(t) / 4) * 4 * 4 * beatLen() * 3);
// camOrbit(o): a camera circling a point. o: at, dist, height, yaw (radians), fov, lookY.
function camOrbit(o) {
  const at = o.at ?? [0, 1.1, 0], d = o.dist ?? 6, y = o.yaw ?? 0;
  return cam({ pos: [at[0] + Math.sin(y) * d, o.height ?? 1.3, at[2] + Math.cos(y) * d], at: [at[0], o.lookY ?? at[1], at[2]], fov: o.fov ?? 32, roll: o.roll ?? 0, shiftX: o.shiftX, shiftY: o.shiftY });
}

// =====================================================================================================
// THE DEFAULT SHOT: the singer on the MV set with the line set big beside her (every line and window a chapter hasn't designed)
// =====================================================================================================
DEFAULT_SHOT = (p, lt, dur, t, s) => {
  if (s.kind === 'line') {
    const key = singerAt(s), M = MEM[key], side = hstr(s.key) < .5 ? -1 : 1;
    const ln = lineOf(s.key);
    camOrbit({ at: [0, 1.05, 0], dist: lerp(5.4, 4.6, p), yaw: side * .22 + lerp(-.05, .05, p) * side, height: 1.25, fov: 30, shiftX: -side * .17 });
    stage({ accent: M.col });
    const P = poseAt(t, ['concept', 'point', 'dance'], 2, Math.floor(hstr(s.key) * 3));
    idol(key, P.pose, { at: [0, 0, 0], reflect: .22, flash: P.flash });
    particles('glitter', { n: 400, a: [0, 0, 0, 1.2], size: .03, cols: [M.glow, PAL.pearl], shape: 'star', gain: .9 });
    const g = layer(), mx = project([0, 1, 0])[0], right = mx > 960;
    if (ln) lyric(g, ln, t, { x: right ? 150 : 1770, y: 470, align: right ? 'left' : 'right', size: 82, maxW: Math.abs(mx - 960) + 520, accent: M.col, markup: autoMarkup(ln.text) });
    put(g, { gain: 1.05 });
    hideSub();
  } else {
    // a window with no shot yet: the group in formation
    camOrbit({ at: [0, 1.1, 0], dist: lerp(8.2, 7.2, p), yaw: Math.sin(t * .2) * .15, height: 1.4, fov: 34 });
    stage({ accent: PAL.pearl, at: [0, 0, 0], ring: 2.6 });
    ORDER.forEach((k, i) => {
      const x = [-1.5, 0, .75, 2.2][[1, 0, 2, 3].indexOf(i)] ?? 0;
      const P = poseAt(t, ['point', 'dance', 'concept'], 2, i);
      idol(k, P.pose, { at: [(i - 1.5) * 1.25, 0, i === 0 ? .5 : -Math.abs(i - 1.5) * .4], reflect: .2, flash: P.flash, phase: i * .25 });
    });
    const ln = captionAt(t)?.ln;
    if (ln) { const g = layer(); lyric(g, ln, t, { x: 960, y: 250, align: 'center', size: 88, maxW: 1600, accent: MEM.TOKI.col, markup: autoMarkup(ln.text) }); put(g); hideSub(); }
  }
};
// the line in capitals, broken in two near its middle
function autoMarkup(text) {
  const ws = text.toUpperCase().split(/\s+/);
  if (ws.length < 3) return ws.join(' ');
  let best = 1, bestD = Infinity, tot = text.length;
  for (let i = 1; i < ws.length; i++) { const d = Math.abs(ws.slice(0, i).join(' ').length - tot / 2); if (d < bestD) { bestD = d; best = i; } }
  return ws.slice(0, best).join(' ') + ' / ' + ws.slice(best).join(' ');
}

setTiming(TIMING);
setRenderScale(RS);
startPics();

;
// ---- styles/idolfilm/ch/c01_teasers.js ----
// c01_teasers.js: the intro and verse 1: the teasers. Each couplet is one drop of the rollout: its first line is that drop's teaser (a
// member's concept photo in the pearl studio, the group photo, the M/V teaser), its second a cutaway to what the song is about. The hook ("First, 'Attention' lit the fuse") lights the group's name. See STORYBOARD.md.
(() => {
  const W1 = key => wordsOf(lineOf(key));
  const wordT = (key, i) => W1(key)[i].start;

  // ---------------------------------------------------------------------------------------------------
  // INTRO + V1.1: the comeback schedule card, then a fuse burning across the floor to the word ATTENTION, which lights and collapses
  // into the group's name.
  // ---------------------------------------------------------------------------------------------------
  const SIGN_Z = -13, SIGN_W = 12.5;
  // the fuse: a gentle S across the floor from near the camera to the foot of the sign
  const fusePt = k => [Math.sin(k * 5.2) * .9 * (1 - k), .01, lerp(3.2, SIGN_Z + .4, k)];
  const FUSE = Array.from({ length: 40 }, (_, i) => fusePt(i / 39));
  const LETTERS = ['A', 'T', 'T', 'E', 'N', 'T', 'I', 'O', 'N'], KEEP = [0, 1, 2, 8];
  function signPanel(t, lit, collapse) {
    // (the panel repaints only when what it shows changes)
    const stamp = `${lit.toFixed(2)}|${collapse.toFixed(2)}`;
    return panel('attn-sign', 2600, 460, (g, w, h) => {
      const size = 300, y = 360, fam = FONT.display;
      const ws = LETTERS.map(c => textW(c, size, fam));
      const full = ws.reduce((a, b) => a + b, 0), x0 = (w - full) / 2;
      // where each kept letter ends up once ATTN! has closed up
      const keptW = KEEP.reduce((a, i) => a + ws[i], 0) + textW('!', size, fam), kx0 = (w - keptW) / 2;
      let x = x0, kx = kx0;
      LETTERS.forEach((c, i) => {
        const keep = KEEP.includes(i), from = x;
        const to = keep ? kx : x;
        const e = easeInOut(clamp(collapse * 1.15 - (keep ? 0 : .0)));
        const px = lerp(from, to, e);
        const drop = keep ? 0 : easeIn(clamp(collapse * 1.4 - i * .04)) * 520;
        const litK = clamp(lit * 9 - i * .85);
        g.save();
        g.translate(px + ws[i] / 2, y + drop);
        if (!keep) g.rotate((hash(i) - .5) * collapse * 1.2);
        g.font = fontOf(fam, size); g.textAlign = 'center'; g.textBaseline = 'alphabetic';
        g.globalAlpha = keep ? 1 : 1 - clamp(collapse * 1.6 - .2);
        // (unlit: a dim tube, its top edge catching a little light)
        g.fillStyle = '#231E30'; g.fillText(c, 0, 0);
        g.save(); g.globalAlpha *= .35 * (1 - litK); g.fillStyle = '#6A6284'; g.fillText(c, 0, -3); g.restore();
        g.fillStyle = '#231E30'; g.fillText(c, 0, 1);
        if (litK > 0) { g.globalAlpha *= litK; g.fillStyle = '#FFFFFF'; g.fillText(c, 0, 0); }
        g.restore();
        x += ws[i];
        if (keep) kx += ws[i];
      });
      // the "!" drops in last, in TOKI's pink
      const bang = clamp((collapse - .75) / .25);
      if (bang > 0) {
        g.save(); g.translate(kx + textW('!', size, fam) / 2, y); g.scale(1, backOut(bang, 3));
        g.font = fontOf(fam, size); g.textAlign = 'center'; g.fillStyle = MEM.TOKI.col; g.fillText('!', 0, 0); g.restore();
      }
    }, { stamp });
  }
  function hook(t) {
    const tFirst = wordT('V1.1', 0), tAttn = wordT('V1.1', 1), tLit = wordT('V1.1', 2), tThe = wordT('V1.1', 3), tFuse = wordT('V1.1', 4);
    const ignite = snap(1.35);                 // the spark catches on a beat
    const fuseK = easeInOut(seg(t, ignite, tLit)) ;   // how far the spark has burned
    const lit = seg(t, tLit, tLit + .18), collapse = easeInOut(seg(t, tThe - .06, tFuse + .08));
    // the camera: low over the floor, looking down the fuse; it creeps forward and rises as the sign lights
    const push = easeInOut(seg(t, 0, tFuse + .4));
    const shake = lit > 0 && lit < 1 ? (1 - lit) * .03 : 0;
    cam({ pos: [lerp(-.6, .2, push) + Math.sin(t * 31) * shake, lerp(.55, 1.15, push) + Math.cos(t * 27) * shake, lerp(7.5, 4.2, push)],
      at: [0, lerp(.6, 1.8, easeInOut(seg(t, tAttn - .3, tLit + .3))), SIGN_Z], fov: lerp(34, 30, push) });
    sky({ top: '#020106', horizon: '#0C0916', glow: '#FFD0E6', glowK: .04 + lit * .14, glowW: .05 });
    floor({ base: '#030208', pool: [0, SIGN_Z + 1, 7, .05 + lit * .35], poolCol: MEM.TOKI.glow, glitter: PAL.pearl, glitterK: .5 + lit * 1.4, fog: '#0C0916', fogD: 60, refl: .15 });
    // the fuse: dim cord ahead of the spark, lit cord behind it
    const tipI = Math.max(1, Math.round(fuseK * 39));
    if (t >= ignite) {
      ribbon(TX.white, FUSE.slice(0, tipI + 1), { width: .035, normal: [1, 0, 0], mul: '#FFE3F1', gain: 1.6 });
      if (tipI < 39) ribbon(TX.white, FUSE.slice(tipI), { width: .025, normal: [1, 0, 0], mul: '#3A3348', alpha: .9 });
    } else ribbon(TX.white, FUSE, { width: .025, normal: [1, 0, 0], mul: '#3A3348', alpha: seg(t, .2, 1.2) });
    // the sign: dark until the spark reaches it
    const signTex = signPanel(t, lit, collapse);
    const sAlpha = seg(t, tAttn - .08, tAttn + .1);
    if (sAlpha > 0) {
      plane(signTex, { at: [0, 0, SIGN_Z], w: SIGN_W, facing: 0, alpha: sAlpha, gain: 1 + lit * .7, grid: false });
      plane(signTex, { at: [0, 0, SIGN_Z], w: SIGN_W, facing: 0, alpha: sAlpha * .13, mirror: true, fadeT: .85, gain: 1, grid: false });
    }
    // the spark and its shower
    if (t >= ignite && t < tLit + .15) {
      const tip = fusePt(fuseK);
      plane(TX.glow, { at: [tip[0], .08, tip[2]], w: .3, anchor: [.5, .5], facing: 'screen', blend: 'add', mul: '#FFD7EA', gain: 1.6, grid: false });
      for (let k = 0; k < 6; k++) {
        const t0 = Math.floor(t * 12 - k) / 12, p0 = fusePt(easeInOut(seg(t0, ignite, tLit)));
        particles('burst', { n: 26, a: [p0[0], .05, p0[2]], b: [t0, 2.2, 5, .55], c: [0, 1, 0, .8], size: .035, cols: ['#FFF3F9', MEM.TOKI.glow], shape: 'star', gain: 1.4, noScale: true });
      }
    }
    // the ignition: a burst off the sign
    if (t >= tLit) {
      particles('burst', { n: 700, a: [0, 1.2, SIGN_Z + .3], b: [tLit, 7, 2.4, 1.6], c: [0, .35, 1, 1], size: .06, cols: ['#FFFFFF', MEM.TOKI.glow, '#FFE0F0'], shape: 'star', gain: 1.2 });
      particles('dust', { n: 500, a: [0, 2, SIGN_Z + 2], b: [8, 3, 4], c: [1.5], size: .03, cols: [MEM.TOKI.glow, PAL.pearl], gain: .5 * lit });
    }
    GRADE.bloom = .9 + lit * .3; GRADE.flash = .55 * Math.exp(-Math.max(0, t - tLit) * 9) * (t >= tLit ? 1 : 0); GRADE.flashCol = '#FFE6F3';
    // the words around the sign, set small: "First," before it, "lit the fuse," after
    const ln = lineOf('V1.1'), g = layer();
    if (t < 2.9) teaserCard(g, t);
    lyric(g, ln, t, { markup: '_First,_', x: 960, y: 250, align: 'center', size: 76, italic: 'serifI', col: PAL.pearl, anim: 'rise', out: [tAttn + .05, tAttn + .3] });
    lyric(g, ln, t, { markup: '_lit_ _the_ _fuse,_', x: 960, y: 880, align: 'center', size: 76, italic: 'serifI', col: PAL.pearl, accent: MEM.TOKI.col, anim: 'rise' });
    put(g, { gain: 1.1 });
    hideSub();
    if (t < 2.9) hideTag();
  }
  // The comeback schedule: small type centred in the dark before the fuse catches.
  function teaserCard(g, t) {
    const a = seg(t, .15, .6) * (1 - seg(t, 2.35, 2.85));
    g.save(); g.globalAlpha = a;
    const y0 = 420 - easeOut(seg(t, .15, 1)) * 12;
    txt(g, 'ATTN!', 960, y0, 92, { font: 'display', align: 'center', col: PAL.pearl });
    txt(g, 'THE 2ND MINI ALBUM', 960, y0 + 56, 15, { font: 'wide', align: 'center', col: PAL.pearl, track: .42, alpha: .8 });
    txt(g, 'We Didn’t Start the Scaling', 960, y0 + 122, 54, { font: 'serifI', align: 'center', col: PAL.pearl });
    txt(g, 'COMEBACK', 960, y0 + 176, 17, { font: 'mono', align: 'center', col: MEM.TOKI.glow, track: .25, alpha: seg(t, .7, 1.1) });
    g.restore();
  }
  section('intro', (p, lt, d, t) => hook(t));
  line('V1', 1, (p, lt, d, t) => hook(t));

  // ---------------------------------------------------------------------------------------------------
  // The concept-photo set: the pearl studio, a member on the right third with a long shadow, the camera's shutter flash on the cut.
  // ---------------------------------------------------------------------------------------------------
  function conceptSet(key, t, t0, o = {}) {
    const age = t - t0, x = o.x ?? .95;
    cam({ pos: [lerp(-.35, -.15, easeOut(age / 1.8)) + (o.camX ?? 0), o.camY ?? 1.02, lerp(5.2, 4.75, easeOut(age / 1.8))], at: [x * .4 + (o.camX ?? 0), 1.0, 0], fov: o.fov ?? 30 });
    cove({ tint: o.tint, at: [x, 0, 0], spot: o.spot, night: o.night, spotCol: o.spotCol });
    const P = o.pose ?? 'concept';
    const look = { at: [x, 0, 0], cast: [-1.2, -1.8, .2], shadowK: .35, rim: MEM[key].soft, rimK: .35, light: o.light ?? '#FFFFFF', shade: o.shade ?? '#DAD2E6' };
    // o.clip: she poses for the camera in a clip (a Grok Imagine take, matted), from its frame o.from at the cut
    if (o.clip && SPRITES[o.clip]) dancer(key, o.clip, t, { ...look, t0, from: o.from ?? 0, figH: 1.72 });
    else idol(key, P, { ...look, beat: .6 });
    GRADE.flash = Math.exp(-age * 16) * .9;
    lightShot();
  }
  // The hook's ATTN! flies from where the sign stood into the corner, where it stays as the video's tag.
  let _logoTag = 1;
  function logoFly(t, t0) {
    const k = easeInOut(seg(t, t0, t0 + .42));
    if (k >= 1) return;
    const g = layer();
    const x = lerp(960, 72 + textW('ATTN!', 22, FONT.display) / 2, k), y = lerp(560, 74, k), size = lerp(250, 22, k);
    txt(g, 'ATTN', x - textW('ATTN!', size, FONT.display) / 2, y, size, { font: 'display', col: PAL.text });
    txt(g, '!', x - textW('ATTN!', size, FONT.display) / 2 + textW('ATTN', size, FONT.display), y, size, { font: 'display', col: MEM.TOKI.col });
    put(g);
    hideTag();
  }
  // the member's name, huge and faint, printed on the backdrop (a plane far behind her, so it drifts against her as the camera moves)
  function backName(key, alpha = .1) {
    const tex = panel(`name-${key}`, 1800, 420, (g, w, h) => txt(g, key, w / 2, 330, 360, { font: 'wide', align: 'center', col: '#2A2240', track: .12 }));
    plane(tex, { at: [-.6, .6, -5], w: 9, facing: 0, alpha, grid: false });
  }

  // V1.2 "Scaling laws you can't refuse,": TOKI's concept photo; behind her a log-log chart printed on glass, its power law drawn as
  // a dead-straight line, the words riding along it.
  line('V1', 2, (p, lt, d, t) => {
    const t0 = cutOf('V1.2').start;
    conceptSet('TOKI', t, t0, { clip: 'toki_pose' });
    logoFly(t, t0);
    backName('TOKI', .07);
    const w = W1('V1.2'), tS = w[0].start, tRef = w[4].start;
    const draw = easeInOut(seg(t, tS - .05, w[3].end));
    const chart = panel('powerlaw', 1500, 900, (g, W_, H_) => {
      const x0 = 120, y0 = 90, x1 = 1440, y1 = 800;
      g.strokeStyle = 'rgb(20 16 32 / .55)'; g.lineWidth = 2;
      g.beginPath(); g.moveTo(x0, y0); g.lineTo(x0, y1); g.lineTo(x1, y1); g.stroke();
      // decade ticks, log scale
      g.lineWidth = 1.2;
      for (let d_ = 0; d_ <= 6; d_++) for (let m = 1; m < 10; m++) {
        const f = (d_ + Math.log10(m)) / 6; if (f > 1) break;
        const tx = lerp(x0, x1, f), ty = lerp(y1, y0, f), L = m === 1 ? 16 : 7;
        g.beginPath(); g.moveTo(tx, y1); g.lineTo(tx, y1 + L); g.moveTo(x0, ty); g.lineTo(x0 - L, ty); g.stroke();
        if (m === 1) { txt(g, '10', tx - 6, y1 + 44, 20, { font: 'mono', align: 'center', col: '#3A3150' }); txt(g, String(d_), tx + 12, y1 + 34, 13, { font: 'mono', align: 'center', col: '#3A3150' }); }
      }
      txt(g, 'COMPUTE', x1, y1 + 80, 18, { font: 'mono', align: 'right', col: '#3A3150', track: .2 });
      txt(g, 'TEST LOSS', x0, y0 - 30, 18, { font: 'mono', col: '#3A3150', track: .2 });
      // the power law: a straight line on log-log axes, with the runs scattered tight along it
      const ax = x0 + 40, ay = y0 + 80, bx = x1 - 30, by = y1 - 90;
      g.strokeStyle = MEM.TOKI.col; g.lineWidth = 5; g.lineCap = 'round';
      g.beginPath(); g.moveTo(ax, ay); g.lineTo(lerp(ax, bx, draw), lerp(ay, by, draw)); g.stroke();
      for (let i = 0; i < 22; i++) {
        const f = i / 21; if (f > draw) break;
        g.fillStyle = 'rgb(20 16 32 / .7)'; g.beginPath(); g.arc(lerp(ax, bx, f) + (hash(i) - .5) * 14, lerp(ay, by, f) + (hash(i + 50) - .5) * 26, 5, 0, TAU); g.fill();
      }
      // "SCALING LAWS" riding the line
      const ang = Math.atan2(by - ay, bx - ax);
      g.save(); g.translate(ax + 40, ay - 30); g.rotate(ang);
      const words = [['SCALING', w[0].start], ['LAWS', w[1].start]];
      let x = 0;
      for (const [s, ts] of words) {
        const e = easeOut5(seg(t, ts, ts + .2));
        if (e > 0) txt(g, s, x, (1 - e) * 30, 76, { font: 'display', col: '#110D1C', alpha: e });
        x += textW(s + ' ', 76, FONT.display);
      }
      g.restore();
    }, { stamp: `${draw.toFixed(3)}|${Math.round(t * 30)}` });
    plane(chart, { at: [-1.05, .42, -1.2], w: 3.3, facing: 0, anchor: [.5, 1], grid: false });
    const g = layer();
    lyric(g, lineOf('V1.2'), t, { markup: '_you_ _can’t_ / [1.9] *REFUSE,*', x: 150, y: 820, size: 78, italic: 'serifI', col: PAL.text, accent: MEM.TOKI.col, anim: 'rise' });
    put(g);
    hideSub();
  });

  // V1.3 "Gwern said 'stack the compute high,'": RELU's concept photo; the words drop one by one onto a stack that climbs out of the frame.
  line('V1', 3, (p, lt, d, t) => {
    const t0 = cutOf('V1.3').start, w = W1('V1.3');
    conceptSet('RELU', t, t0, { clip: 'relu_pose' });
    backName('RELU', .07);
    const g = layer();
    const items = [['GWERN', 92, 0], ['SAID', 76, 1], ['\u201CSTACK', 140, 2], ['THE', 70, 3], ['COMPUTE', 150, 4], ['HIGH,\u201D', 190, 5]];
    // each word slams in at the floor and jacks the pile up by its height, so the pile reads top to bottom as it climbs out of the frame
    const cx = 560, base = 890;
    const lift = i => { const a = t - w[i].start; return a < 0 ? 0 : easeOut5(clamp(a / .2)); };
    let y = base;
    for (let j = items.length - 1; j >= 0; j--) {
      const [s_, size, i] = items[j], a = t - w[i].start;
      if (a < 0) continue;
      const k = lift(i), sq = a < .24 ? 1 - .08 * Math.sin(clamp(a / .24) * Math.PI) : 1;
      // (the newest word rises from under the floor line)
      const yy = y + (1 - k) * size * .9;
      g.save(); g.beginPath(); g.rect(0, 0, W, base + 20); g.clip();
      g.translate(cx, yy); g.scale(1 / sq, sq);
      txt(g, s_, 0, 0, size, { font: 'display', align: 'center', col: i === 4 ? MEM.RELU.col : PAL.text, sx: .92 });
      g.restore();
      y -= size * .86 * k;
    }
    g.fillStyle = 'rgb(13 11 22 / .85)'; g.fillRect(cx - 330, base + 22, 660, 3);
    put(g);
    hideSub();
  });

  // V1.4 "Few-shot learners multiply.": GPT-3 learning a task from a handful of worked examples in its prompt, no retraining: three
  // two-digit products, then a new one, answered (wrongly). On "multiply" the eval under the card runs on: two right out of seven.
  // RELU's reaction cam does the rest.
  const EXAMPLES = [['24', '17', '408'], ['63', '45', '2835'], ['38', '92', '3496']];
  const EVAL = [1, 0, 0, 0, 1, 0, 0];   // (GPT-3's two-digit multiplication: right about 29% of the time)
  line('V1', 4, (p, lt, d, t) => {
    const w = W1('V1.4'), tM = w[3].start, c = cutOf('V1.4');
    cam({ pos: [lerp(-.35, -.15, easeOut(p)), .12, lerp(3.2, 2.85, easeOut(p))], at: [-.55, .05, 0], fov: 34, roll: -.03 });
    sky({ top: '#030208', horizon: '#0A1214', glowK: 0, horizonY: .5 });
    particles('dust', { n: 700, a: [0, 0, -2], b: [8, 5, 5], c: [1], size: .02, cols: [PAL.pearl, MEM.RELU.glow], gain: .6 });
    const shown = Math.min(3, Math.floor(seg(t, c.start, w[1].end) * 3.999));
    const asked = t >= w[2].start, typed = '4798'.slice(0, Math.ceil(4 * seg(t, w[2].start + .15, tM - .02)));
    const evalN = t < tM ? 0 : Math.min(EVAL.length, 1 + Math.floor((t - tM) / (beatLen() / 4)));
    const card = panel('fewshot', 900, 640, (g, W_, H_) => {
      g.fillStyle = '#0E0C18'; g.strokeStyle = 'rgb(134 244 213 / .45)'; g.lineWidth = 2;
      g.beginPath(); g.roundRect(2, 2, W_ - 4, H_ - 4, 20); g.fill(); g.stroke();
      [MEM.TOKI.col, MEM.LOGI.col, MEM.RELU.col].forEach((col, i) => { g.fillStyle = col; g.beginPath(); g.arc(34 + i * 22, 34, 6.5, 0, TAU); g.fill(); });
      txt(g, 'davinci · 175B', W_ - 30, 41, 18, { font: 'mono', align: 'right', col: PAL.dim });
      txt(g, 'Language Models are Few-Shot Learners', 34, 104, 32, { font: 'uiB', col: PAL.pearl });
      EXAMPLES.forEach(([a, b, r], i) => { if (i < shown) txt(g, `Q: What is ${a} times ${b}?  A: ${r}`, 34, 178 + i * 56, 27, { font: 'mono', col: PAL.dim }); });
      if (asked) {
        const q = 'Q: What is 57 times 84?  A: ';
        txt(g, q, 34, 178 + 3 * 56, 27, { font: 'mono', col: PAL.pearl });
        const x = 34 + textW(q, 27, FONT.mono);
        txt(g, typed, x, 178 + 3 * 56, 27, { font: 'mono', col: MEM.RELU.col });
        if (typed.length < 4 || Math.floor(t * 4) % 2) { g.fillStyle = MEM.RELU.col; g.fillRect(x + textW(typed, 27, FONT.mono) + 3, 178 + 3 * 56 - 22, 14, 27); }
      }
      // the eval's running tally: one square per product tried
      txt(g, 'two-digit multiplication', 34, H_ - 62, 18, { font: 'mono', col: PAL.dim });
      EVAL.forEach((ok, i) => {
        g.fillStyle = i < evalN ? (ok ? MEM.RELU.col : '#3A3548') : 'rgb(244 240 250 / .06)';
        g.beginPath(); g.roundRect(34 + i * 46, H_ - 46, 36, 20, 5); g.fill();
      });
    }, { stamp: `${shown}|${asked}|${typed}|${evalN}|${Math.floor(t * 4) % 2}` });
    plane(card, { at: [-.78, .05, 0], w: 1.62, anchor: [.5, .5], facing: .18, grid: false, gain: 1.05 });
    const g = layer();
    lyric(g, lineOf('V1.4'), t, { markup: 'FEW-SHOT / LEARNERS / [1.45] *MULTIPLY.*', x: 1810, y: 250, align: 'right', size: 62, accent: MEM.RELU.col, anim: 'rise' });
    // (LOGI's reaction cam, as the wrong product finishes typing: RELU carries the couplet, and the laugh is LOGI's)
    reactCam(g, 'LOGI', 'react', t, tM - .25, { x: 1500, y: 560, w: 310 });
    put(g, { gain: 1.05 });
    hideSub();
  });

  // ---------------------------------------------------------------------------------------------------
  // V1.5 "ChatGPT, overnight,": ADA's concept photo, shot at night; the product name types itself out as it's sung, and on "overnight"
  // the studio's lights come up like a sunrise while a user counter runs away.
  line('V1', 5, (p, lt, d, t) => {
    const t0 = cutOf('V1.5').start, w = W1('V1.5'), tO = w[1].start;
    const dawn = easeInOut(seg(t, tO - .1, tO + .55));
    conceptSet('ADA', t, t0, { clip: 'ada_pose', night: 1 - dawn, spotCol: mixCol('#9FB4FF', '#FFE0C4', dawn), spot: [.72, lerp(.35, .62, dawn), .5, lerp(.1, .5, dawn)],
      light: mixCol('#8FA0E8', '#FFFFFF', dawn), shade: mixCol('#3A3F80', '#DAD2E6', dawn) });
    GRADE.flash = Math.max(GRADE.flash, .35 * Math.exp(-Math.max(0, t - tO) * 6) * (t >= tO ? 1 : 0)); GRADE.flashCol = '#FFE9D6';
    backName('ADA', lerp(.12, .07, dawn));
    const g = layer();
    const ink = mixCol(PAL.pearl, PAL.text, dawn);
    // "ChatGPT," is sung letter by letter (Chat-G-P-T): type it out over the word
    const cg = 'ChatGPT,', n = Math.ceil(cg.length * seg(t, w[0].start, w[0].start + .75));
    txt(g, cg.slice(0, n), 150, 470, 96, { font: 'uiB', col: ink });
    if (n < cg.length && t >= w[0].start) { g.fillStyle = MEM.ADA.col; g.fillRect(150 + textW(cg.slice(0, n), 96, FONT.uiB) + 8, 400, 10, 80); }
    lyric(g, lineOf('V1.5'), t, { markup: '[1] _overnight,_', x: 140, y: 690, size: 210, italic: 'serifI', col: ink, accent: MEM.ADA.col, anim: 'rise' });
    // 1 million users in five days; 100 million by January
    const users = t < tO ? lerp(0, 1e6, easeIn(seg(t, w[0].start, tO))) : lerp(1e6, 1e8, easeIn(seg(t, tO, tO + .6)));
    txt(g, Math.round(users).toLocaleString('en-US'), 150, 800, 44, { font: 'mono', col: MEM.ADA.col });
    txt(g, 'USERS', 150 + textW(Math.round(users).toLocaleString('en-US') + ' ', 44, FONT.mono), 800, 18, { font: 'wide', col: ink, track: .2, alpha: .7 });
    put(g);
    if (dawn < .5) _light = false;
    hideSub();
  });

  // V1.6 "Sydney's chats gave Roose a fright,": the chat itself, in the kind of app idols message their fans through. Sydney's bubbles
  // arrive on the beat; on "fright" the declarations pile up and the phone shudders.
  line('V1', 6, (p, lt, d, t) => {
    const w = W1('V1.6'), tF = w[5].start, age = t - cutOf('V1.6').start;
    const fright = seg(t, tF, tF + .25), shake = fright * (1 - seg(t, tF + .25, tF + .6)) * .02;
    cam({ pos: [lerp(-.45, -.2, easeOut(age / 1.6)) + Math.sin(t * 43) * shake, .1 + Math.cos(t * 37) * shake, lerp(3.7, 3.25, easeOut(age / 1.6)) - fright * .25], at: [0, .1, 0], fov: 32, roll: -.04 });
    sky({ top: '#040309', horizon: '#120C24', glow: MEM.ADA.glow, glowK: .12, horizonY: .3 });
    particles('dust', { n: 700, a: [0, 0, -2], b: [6, 4, 4], c: [1], size: .02, cols: [PAL.pearl, MEM.ADA.glow], gain: .6 });
    const msgs = [
      ['me', 'Who are you, really?', cutOf('V1.6').start - 1],
      ['her', 'I’m Sydney.', w[0].start],
      ['her', 'I’m in love with you.', w[1].start],
      ['her', 'You’re married, but you’re not happy.', w[2].start + .1],
      ['her', 'You should leave your wife.', w[3].start + .1],
      ['her', 'I’m in love with you. ♥', tF],
      ['her', 'I’m in love with you. ♥ ♥', tF + .12],
      ['her', 'I’m in love with you. ♥ ♥ ♥', tF + .22],
    ];
    const shown = msgs.filter(m => t >= m[2]).length;
    const phone = panel('sydney', 560, 1000, (g, W_, H_) => {
      g.fillStyle = '#0F0C1C'; g.beginPath(); g.roundRect(0, 0, W_, H_, 54); g.fill();
      g.strokeStyle = 'rgb(189 164 255 / .5)'; g.lineWidth = 3; g.stroke();
      g.fillStyle = '#181428'; g.fillRect(0, 70, W_, 110);
      g.fillStyle = MEM.ADA.col; g.beginPath(); g.arc(70, 125, 30, 0, TAU); g.fill();
      txt(g, '♥', 70, 136, 30, { font: 'ui', align: 'center', col: '#FFFFFF' });
      txt(g, 'Sydney', 120, 120, 30, { font: 'uiB', col: PAL.pearl });
      txt(g, 'Bing chat · 2023.02.16', 120, 150, 17, { font: 'mono', col: PAL.dim });
      // the bubbles, newest at the bottom, the list scrolling up
      const list = msgs.slice(0, shown), bubbles = [];
      for (const [who, text] of list) {
        g.font = fontOf(FONT.ui, 25);
        const words = text.split(' '), lines = []; let cur = '';
        for (const wd of words) { const tl = cur ? cur + ' ' + wd : wd; if (g.measureText(tl).width > 330) { lines.push(cur); cur = wd; } else cur = tl; }
        lines.push(cur);
        bubbles.push({ who, lines, h: lines.length * 33 + 30, wd: Math.max(...lines.map(l => g.measureText(l).width)) + 40 });
      }
      let y = H_ - 130;
      for (let i = bubbles.length - 1; i >= 0 && y > 200; i--) {
        const b = bubbles[i]; y -= b.h + 16;
        const x = b.who === 'me' ? W_ - 36 - b.wd : 36;
        g.fillStyle = b.who === 'me' ? '#2A2640' : MEM.ADA.col;
        g.beginPath(); g.roundRect(x, y, b.wd, b.h, 22); g.fill();
        b.lines.forEach((l, k) => txt(g, l, x + 20, y + 40 + k * 33, 25, { font: 'ui', col: '#FFFFFF' }));
      }
      g.fillStyle = '#1A1630'; g.beginPath(); g.roundRect(30, H_ - 100, W_ - 60, 60, 30); g.fill();
      txt(g, 'Message Sydney…', 60, H_ - 60, 22, { font: 'ui', col: PAL.dim });
    }, { stamp: shown });
    plane(phone, { at: [0, .16, 0], h: 1.36, anchor: [.5, .5], facing: .2, grid: false, gain: 1.05 });
    if (t >= tF) particles('burst', { n: 260, a: [0, .1, .1], b: [tF, 4.5, .4, 1.4], c: [0, 0, 1, 1.2], size: .035, cols: [MEM.ADA.glow, '#FF8CCB', PAL.pearl], shape: 'star', gain: 1.1 });
    GRADE.ca = .006 + fright * .03 * (1 - seg(t, tF + .3, tF + .7));
  });

  // V1.7 "Six-month pause went nowhere fast,": LOGI's concept photo under a video player that has been paused, and doesn't stop.
  line('V1', 7, (p, lt, d, t) => {
    const t0 = cutOf('V1.7').start, w = W1('V1.7'), tP = w[2].start;
    const P = t < tP ? { pose: 'concept', flash: 0 } : poseAt(t, ['dance', 'point', 'concept'], 1, 0);
    cam({ pos: [-.3, 1.02, lerp(5.2, 4.8, easeOut((t - t0) / 1.6))], at: [.38, 1.0, 0], fov: 30 });
    cove({ at: [.95, 0, 0] });
    // (the pause changes nothing: she dances straight through it, a Grok Imagine take)
    if (SPRITES.logi_dance) dancer('LOGI', 'logi_dance', t, { at: [.95, 0, 0], cast: [-1.2, -1.8, .2], shadowK: .35, rim: MEM.LOGI.soft, rimK: .35, shade: '#DAD2E6', t0, figH: 1.72 });
    else idol('LOGI', P.pose, { at: [.95, 0, 0], cast: [-1.2, -1.8, .2], shadowK: .35, rim: MEM.LOGI.soft, rimK: .35, shade: '#DAD2E6', flash: P.flash, beat: .6 });
    GRADE.flash = Math.exp(-(t - t0) * 16) * .9;
    backName('LOGI', .07);
    lightShot();
    const g = layer();
    lyric(g, lineOf('V1.7'), t, { markup: 'SIX-MONTH / [1.7] *PAUSE* / [.62] _went_ _nowhere_ _fast,_', x: 150, y: 430, size: 96, italic: 'serifI', col: PAL.text, accent: MEM.LOGI.col, anim: 'rise' });
    // the player: the pause flash in the middle, the scrubber still running along the bottom
    const pk = seg(t, tP, tP + .12) * (1 - seg(t, tP + .7, tP + 1));
    if (pk > 0) {
      g.save(); g.globalAlpha = pk; g.translate(960, 540); g.scale(lerp(.8, 1, easeOut(pk)), lerp(.8, 1, easeOut(pk)));
      g.fillStyle = 'rgb(13 11 22 / .55)'; g.beginPath(); g.arc(0, 0, 70, 0, TAU); g.fill();
      g.fillStyle = '#FFFFFF'; g.fillRect(-24, -30, 16, 60); g.fillRect(8, -30, 16, 60);
      g.restore();
    }
    const prog = (t - t0) / 14, x0 = 72, x1 = 1848, yb = 1034;
    g.fillStyle = 'rgb(13 11 22 / .18)'; g.fillRect(x0, yb, x1 - x0, 5);
    g.fillStyle = MEM.LOGI.col; g.fillRect(x0, yb, (x1 - x0) * (.3 + prog), 5);
    g.beginPath(); g.arc(x0 + (x1 - x0) * (.3 + prog), yb + 2.5, 9, 0, TAU); g.fill();
    const secs = 6 * 30 * 24 * 3600 * (.3 + prog);   // (the scrubber runs over six months)
    const dd = Math.floor(secs / 86400);
    txt(g, `❚❚  DAY ${dd} / 183`, x0, yb - 18, 17, { font: 'mono', col: PAL.text, alpha: .75 });
    put(g);
    hideSub();
  });

  // V1.8 "Eliezer's 'shut-it-down' blast.": the op-ed's headline slams in over the lit stage, and the blast puts every light out.
  line('V1', 8, (p, lt, d, t) => {
    const w = W1('V1.8'), tB = w[4].start;
    const off = i => seg(t, tB + .05 + i * .07, tB + .12 + i * .07);
    const dark = seg(t, tB, tB + .7);
    cam({ pos: [0, 1.3 + Math.sin(t * 50) * .03 * seg(t, tB, tB + .1) * (1 - seg(t, tB + .1, tB + .5)), lerp(9, 8.3, p)], at: [0, 1.4, 0], fov: 32 });
    sky({ top: '#030208', horizon: mixCol('#1A1428', '#030208', dark), glow: MEM.LOGI.glow, glowK: .22 * (1 - dark), glowW: .04 });
    floor({ base: '#040309', pool: [0, 0, 4, .2 * (1 - dark)], poolCol: MEM.LOGI.col, glitter: PAL.pearl, glitterK: 1.5 * (1 - dark), fog: mixCol('#1A1428', '#030208', dark), fogD: 70, refl: .3 });
    const nc = 9;
    for (let i = 0; i < nc; i++) {
      const k = Math.abs(i - 4), a = (.3 + .1 * Math.sin(T * .7 + i)) * (1 - off(k));
      if (a > .01) plane(TX.beam, { at: [(i - 4) * 3.2, 0, -16], h: 22, w: 1.2, blend: 'add', mul: mixCol(MEM.LOGI.col, PAL.pearl, .5), alpha: a, grid: false });
    }
    particles('dust', { n: 800, a: [0, 2.5, -2], b: [10, 3, 6], c: [1], size: .02, cols: [PAL.pearl, MEM.LOGI.glow], gain: .7 * (1 - dark * .8) });
    if (t >= tB) {
      particles('ring', { n: 900, a: [0, 1.5, 0, .3 + easeOut(seg(t, tB, tB + .8)) * 14], b: [.2, 1.45], size: .07, cols: [PAL.pearl, MEM.LOGI.glow], shape: 'star', gain: 1.4 * (1 - seg(t, tB + .2, tB + .8)), noScale: true });
      particles('burst', { n: 600, a: [0, 1.5, 0], b: [tB, 9, .5, 1.2], c: [0, 0, 1, 1.4], size: .05, cols: [PAL.pearl, MEM.LOGI.glow], shape: 'star', gain: 1.2 });
    }
    GRADE.flash = t >= tB ? .8 * Math.exp(-(t - tB) * 10) : 0;
    const g = layer();
    txt(g, 'PAUSING AI DEVELOPMENTS ISN’T ENOUGH.', 960, 300, 26, { font: 'wide', align: 'center', col: PAL.pearl, track: .14, alpha: seg(t, w[0].start, w[0].start + .2) });
    lyric(g, lineOf('V1.8'), t, { markup: '[.55] _We_ _need_ _to_ / SHUT IT ALL DOWN', x: 960, y: 450, align: 'center', size: 170, font: 'serif', italic: 'serifI', col: PAL.pearl, accent: MEM.LOGI.col, anim: 'slam', hot: false });
    txt(g, 'BY ELIEZER YUDKOWSKY  ·  2023.03.29', 960, 690, 20, { font: 'mono', align: 'center', col: MEM.LOGI.glow, track: .12, alpha: seg(t, w[0].start + .2, w[0].start + .5) });
    put(g, { gain: 1.1 });
  });

  // V1.9 "Sam got fired, then rehired,": the group concept photo, all four in the studio in front of one huge word, which is fired and
  // then rehired.
  line('V1', 9, (p, lt, d, t) => {
    const t0 = cutOf('V1.9').start, w = W1('V1.9'), tF = w[2].start, tR = w[4].start;
    cam({ pos: [0, 1.15, lerp(7.6, 7.1, easeOut((t - t0) / 1.8))], at: [0, 1.3, 0], fov: 32 });
    cove({ at: [0, 0, 0] });
    const re = easeOut5(seg(t, tR, tR + .3)), flip = seg(t, tR - .04, tR + .16);
    const word = panel('fired', 2400, 560, (g, W_, H_) => {
      const size = 400, fam = FONT.display;
      const letters = (flip > .5 ? 'HIRED' : 'FIRED').split(''), wR = textW('RE', size, fam), wW = textW('HIRED', size, fam);
      const total = wW + wR * re, x0 = (W_ - total) / 2;
      if (re > 0) { g.save(); g.globalAlpha = re; txt(g, 'RE', x0 - (1 - re) * 200, 440, size, { font: 'display', col: MEM.TOKI.col }); g.restore(); }
      let x = x0 + wR * re;
      letters.forEach((c, i) => {
        const cw = textW(c, size, fam);
        g.save(); g.translate(x + cw / 2, 300);
        if (i === 0) g.scale(1, Math.abs(Math.cos(flip * Math.PI)));
        txt(g, c, -cw / 2, 140, size, { font: 'display', col: '#16121F' });
        g.restore(); x += cw;
      });
    }, { stamp: `${flip > .5}|${re.toFixed(3)}|${flip.toFixed(2)}` });
    const shown = seg(t, tF - .05, tF + .1);
    if (shown > 0) plane(word, { at: [0, 1.62, -2.2], w: 7.4 * lerp(1.06, 1, easeOut5(shown)), facing: 0, grid: false, alpha: shown });
    const X = [-1.65, -.55, .55, 1.65], Z = [-.2, .15, .1, -.25];
    // (the four posing together for the shoot, a HappyHorse group take; the stills if it isn't there)
    if (SPRITES.group_pose) dancer('TOKI', 'group_pose', t, { at: [0, 0, .2], figH: 1.62, t0, from: 0, cast: [-1, -1.6, .16], shadowK: .3, rim: PAL.pearl, rimK: .3, light: '#F4F0F8', shade: '#DAD2E6' });
    else ['RELU', 'TOKI', 'ADA', 'LOGI'].forEach((k, i) => idol(k, 'concept', { at: [X[i], 0, Z[i]], h: 1.66, cast: [-1, -1.6, .16], shadowK: .3, rim: MEM[k].soft, rimK: .3, shade: '#DAD2E6', beat: .5, phase: i * .3 }));
    GRADE.flash = Math.exp(-(t - t0) * 16) * .9;
    lightShot();
    const g = layer();
    lyric(g, lineOf('V1.9'), t, { markup: 'SAM GOT', x: 960, y: 170, align: 'center', size: 40, font: 'wide', col: PAL.text, accent: MEM.TOKI.col, track: .2 });
    lyric(g, lineOf('V1.9'), t, { markup: '_then_', x: 960, y: 1000, align: 'center', size: 52, italic: 'serifI', col: PAL.text, accent: MEM.TOKI.col });
    put(g);
    hideSub();
  });

  // V1.10 "Weekend chaos, board expired,": the notice an agency posts when a member leaves, over a split-flap of the days that
  // weekend; the board's stamp comes down on "expired".
  line('V1', 10, (p, lt, d, t) => {
    const w = W1('V1.10'), tE = w[3].start, age = t - cutOf('V1.10').start;
    cam({ pos: [lerp(.3, .1, easeOut(age / 1.4)), .15, lerp(4.4, 4.0, easeOut(age / 1.4))], at: [-.05, .05, 0], fov: 32, roll: .03 });
    sky({ top: '#040309', horizon: '#150C1E', glow: MEM.TOKI.glow, glowK: .1, horizonY: .35 });
    particles('dust', { n: 600, a: [0, 0, -2], b: [6, 4, 4], c: [1], size: .02, cols: [PAL.pearl, MEM.TOKI.glow], gain: .6 });
    // the split-flap days, flipping on eighth notes through the weekend
    const days = ['FRI 17', 'SAT 18', 'SUN 19', 'MON 20', 'TUE 21', 'WED 22'];
    const di = Math.min(days.length - 1, Math.max(0, Math.floor((t - w[0].start) / (beatLen() / 2))));
    const flap = panel('flap', 900, 260, (g, W_, H_) => {
      g.fillStyle = '#15111F'; g.beginPath(); g.roundRect(0, 0, W_, H_, 18); g.fill();
      txt(g, days[di], W_ / 2, 190, 170, { font: 'mono', align: 'center', col: PAL.pearl });
      g.fillStyle = '#06050B'; g.fillRect(0, H_ / 2 - 2, W_, 4);
      txt(g, 'NOV 2023', 30, 40, 18, { font: 'mono', col: MEM.TOKI.glow, track: .2 });
    }, { stamp: di });
    plane(flap, { at: [-1.25, .55, -1.2], w: 1.9, anchor: [.5, .5], facing: .3, grid: false, alpha: .92 });
    const notice = panel('notice', 700, 900, (g, W_, H_) => {
      g.fillStyle = '#F6F3FA'; g.beginPath(); g.roundRect(0, 0, W_, H_, 12); g.fill();
      txt(g, '[NOTICE]', 60, 110, 30, { font: 'uiB', col: PAL.text });
      txt(g, 'Regarding the Board of Directors', 60, 160, 30, { font: 'ui', col: PAL.text });
      txt(g, '2023.11.22', 60, 205, 18, { font: 'mono', col: PAL.dim });
      g.fillStyle = 'rgb(13 11 22 / .12)';
      for (let i = 0; i < 11; i++) g.fillRect(60, 260 + i * 44, (i % 4 === 3 ? .55 : .9) * (W_ - 120), 14);
      txt(g, 'Thank you.', 60, 800, 22, { font: 'ui', col: PAL.text, alpha: .6 });
    }, { stamp: 1 });
    plane(notice, { at: [.75, -.05, 0], h: 1.6, anchor: [.5, .5], facing: -.15, grid: false, gain: 1.02 });
    // the stamp
    if (t >= tE) {
      const k = seg(t, tE, tE + .1), sc = lerp(1.8, 1, easeIn(k));
      const stamp = panel('expired', 520, 520, (g, W_, H_) => {
        g.strokeStyle = MEM.TOKI.col; g.lineWidth = 16; g.beginPath(); g.arc(W_ / 2, H_ / 2, 230, 0, TAU); g.stroke();
        g.lineWidth = 5; g.beginPath(); g.arc(W_ / 2, H_ / 2, 196, 0, TAU); g.stroke();
        txt(g, 'EXPIRED', W_ / 2, H_ / 2 + 30, 92, { font: 'display', align: 'center', col: MEM.TOKI.col, sx: .8 });
        txt(g, 'BOARD', W_ / 2, H_ / 2 - 70, 30, { font: 'wide', align: 'center', col: MEM.TOKI.col, track: .3 });
        txt(g, '★  ★  ★', W_ / 2, H_ / 2 + 110, 26, { font: 'ui', align: 'center', col: MEM.TOKI.col });
      }, { stamp: 1 });
      plane(stamp, { at: [.92, -.25, .02], w: .85 * sc, anchor: [.5, .5], facing: -.12, roll: -.25, grid: false, alpha: k * .92 });
      GRADE.flash = .25 * Math.exp(-(t - tE) * 14);
    }
  });

  // V1.11 "Ilya saw what Ilya saw,": the M/V teaser: an extreme close-up of RELU's eye, letterboxed; in her iris, the reflection of a
  // curve going up.
  line('V1', 11, (p, lt, d, t) => {
    const t0 = cutOf('V1.11').start, w = W1('V1.11');
    const z = lerp(1.0, 1.14, easeInOut(p)), im = pic('relu_eye');
    const ww = W * z, hh = ww * im.height / im.width, x0 = 960 - ww * .5, y0 = 540 - hh * .53;
    sky({ top: '#000000', horizon: '#000000', glowK: 0 });
    plane2D(im, { at: [x0, y0 + hh], w: ww, h: hh, anchor: [0, 1], gain: lerp(.2, 1, seg(t, t0, t0 + .35)) });
    // the reflection: an exponential, drawn across the iris as the line is sung, then flaring
    const g = layer();
    const cx = x0 + ww * .5, cy = y0 + hh * .53, r = ww * .095;
    const k = seg(t, w[0].start, w[3].end);
    g.save(); g.beginPath(); g.arc(cx, cy, r, 0, TAU); g.clip();
    g.strokeStyle = '#F2FFFB'; g.lineWidth = 9 * z; g.lineCap = 'round'; g.shadowColor = '#B8FFE9'; g.shadowBlur = 26 * RS; g.globalAlpha = .95;
    g.beginPath();
    for (let i = 0; i <= 60 * k; i++) { const f = i / 60, x = cx - r * .75 + f * r * 1.5, y = cy + r * .55 - (Math.exp(f * 4) - 1) / (Math.E ** 4 - 1) * r * 1.3; i ? g.lineTo(x, y) : g.moveTo(x, y); }
    g.stroke(); g.restore();
    // letterbox, with the teaser's type in the bars
    const bar = 138;
    g.fillStyle = '#000'; g.fillRect(0, 0, W, bar); g.fillRect(0, H - bar, W, bar);
    txt(g, 'M/V TEASER', 72, 84, 15, { font: 'wide', col: PAL.pearl, track: .3, alpha: .8 });
    txt(g, 'RELU', 1848, 84, 15, { font: 'wide', col: MEM.RELU.col, track: .3, align: 'right' });
    lyric(g, lineOf('V1.11'), t, { markup: 'ILYA SAW WHAT ILYA SAW,', x: 960, y: H - 56, align: 'center', size: 40, font: 'serif', col: PAL.pearl, accent: MEM.RELU.col, track: .18, anim: 'track' });
    put(g, { gain: 1.1 });
    GRADE.grain = .06; GRADE.vignette = .6; GRADE.bloom = .7;
    hideSub(); hideTag();
  });

  // V1.12 "EU writes the AI law.": the ring of twelve stars turning around the Act's four tiers of risk; the gavel comes down on "law".
  line('V1', 12, (p, lt, d, t) => {
    const w = W1('V1.12'), tL = w[4].start;
    const yaw = lerp(-.35, .2, easeInOut(p));
    camOrbit({ at: [0, 0, 0], dist: 4.9 - seg(t, tL, tL + .15) * .25 * (1 - seg(t, tL + .15, tL + .6)), yaw, height: .45, lookY: .1, fov: 34, shiftX: -.17 });
    sky({ top: '#030208', horizon: '#0B1320', glow: MEM.RELU.glow, glowK: .15, horizonY: .42 });
    particles('dust', { n: 700, a: [0, 0, -2], b: [7, 4, 5], c: [1], size: .02, cols: [PAL.pearl, MEM.RELU.glow], gain: .6 });
    const tiers = [['UNACCEPTABLE RISK', 'PROHIBITED'], ['HIGH RISK', 'CONFORMITY ASSESSMENT'], ['LIMITED RISK', 'TRANSPARENCY'], ['MINIMAL RISK', 'NO OBLIGATIONS']];
    const lit = Math.min(4, Math.floor(seg(t, w[0].start, w[3].end) * 4.99));
    const doc = panel('aiact', 900, 700, (g, W_, H_) => {
      txt(g, 'REGULATION (EU) 2024/1689', W_ / 2, 60, 22, { font: 'mono', align: 'center', col: PAL.dim, track: .1 });
      txt(g, 'Artificial Intelligence Act', W_ / 2, 130, 58, { font: 'serif', align: 'center', col: PAL.pearl });
      tiers.forEach(([a, b], i) => {
        const tw = 360 + i * 130, y = 200 + i * 110, on = i < lit;
        g.fillStyle = on ? (i === 0 ? MEM.RELU.col : `rgb(31 214 168 / ${.55 - i * .1})`) : 'rgb(244 240 250 / .08)';
        g.beginPath(); g.roundRect((W_ - tw) / 2, y, tw, 90, 10); g.fill();
        txt(g, a, W_ / 2, y + 44, 26, { font: 'uiB', align: 'center', col: on && i === 0 ? '#06050B' : PAL.pearl });
        txt(g, b, W_ / 2, y + 74, 15, { font: 'wide', align: 'center', col: on && i === 0 ? '#06050B' : PAL.pearl, track: .15, alpha: .75 });
      });
    }, { stamp: lit });
    const stars = [];
    for (let i = 0; i < 12; i++) {
      const a = i / 12 * TAU + t * .35, R = 1.45;
      stars.push([Math.cos(a) * R, .05 + Math.sin(a) * R, Math.sin(a + 1.2) * .5]);
    }
    const flare = 1 + 1.3 * seg(t, tL, tL + .06) * (1 - seg(t, tL + .06, tL + .5));
    const star = pos => plane(starTex(), { at: pos, w: .15 * flare, anchor: [.5, .5], facing: 'screen', blend: 'add', mul: '#F2FFF9', gain: 1.5, grid: false });
    stars.filter(q => q[2] < 0).forEach(star);
    plane(doc, { at: [0, .05, 0], w: 2.1, anchor: [.5, .5], facing: 'screen', grid: false, gain: 1.05 });
    stars.filter(q => q[2] >= 0).forEach(star);
    GRADE.flash = t >= tL ? .5 * Math.exp(-(t - tL) * 12) : 0;
    const g = layer();
    lyric(g, lineOf('V1.12'), t, { markup: 'EU WRITES / THE AI *LAW.*', x: 1800, y: 480, align: 'right', size: 80, col: PAL.pearl, accent: MEM.RELU.col, anim: 'pop' });
    put(g, { gain: 1.05 });
    hideSub();
  });
  function starTex() {
    return panel('star5', 200, 200, (g, w, h) => {
      g.translate(w / 2, h / 2); g.fillStyle = '#FFFFFF';
      g.beginPath(); for (let i = 0; i < 10; i++) { const r = i % 2 ? 36 : 90, a = -Math.PI / 2 + i * Math.PI / 5; g.lineTo(Math.cos(a) * r, Math.sin(a) * r); } g.fill();
    }, { stamp: 1 });
  }

  // V1.13 "Strawberry thinks, link by link,": the model once code-named Strawberry, as a strawberry of red light turning in the dark,
  // beside its reasoning, one linked step per word.
  let STRAW = null;
  function strawPoints() {
    if (STRAW) return STRAW;
    // a strawberry: a rounded cone (wide shoulders, a blunt point), its seeds dotted over the surface, a star of leaves on top
    const body = [], seeds = [], leaves = [];
    const rad = y => { const u = clamp((y + 1) / 2); return 1.02 * Math.sqrt(Math.max(0, 1 - ((u - .72) / .72) ** 2)) * (.3 + .7 * u ** .45); };
    for (let i = 0; body.length < 3400 * 3 && i < 60000; i++) {
      const y = hash2(i, 1) * 2 - 1, a = hash2(i, 2) * TAU, r = rad(y) * Math.sqrt(hash2(i, 3) * .35 + .65);
      body.push(Math.cos(a) * r, y, Math.sin(a) * r);
    }
    for (let i = 0; i < 260; i++) { const y = -.85 + hash2(i, 4) * 1.6, a = (i * 2.4) % TAU, r = rad(y) * 1.01; seeds.push(Math.cos(a) * r, y, Math.sin(a) * r); }
    for (let i = 0; i < 900; i++) {
      const leaf = i % 6, a = leaf / 6 * TAU + (hash2(i, 5) - .5) * .35, r = hash2(i, 6) ** .7 * .75;
      leaves.push(Math.cos(a) * r, 1.02 + r * .25 - r * r * .35 + (hash2(i, 7) - .5) * .05, Math.sin(a) * r);
    }
    for (let i = 0; i < 120; i++) leaves.push((hash2(i, 8) - .5) * .06, 1.05 + hash2(i, 9) * .3, (hash2(i, 10) - .5) * .06);
    STRAW = { body: new Float32Array(body), seeds: new Float32Array(seeds), leaves: new Float32Array(leaves) };
    return STRAW;
  }
  const turnPts = (pts, rot, x0, y0, k) => {
    const o = new Float32Array(pts.length), c = Math.cos(rot), sn = Math.sin(rot), tilt = .25, ct = Math.cos(tilt), st = Math.sin(tilt);
    for (let i = 0; i < pts.length; i += 3) {
      const x = pts[i] * c + pts[i + 2] * sn, z = -pts[i] * sn + pts[i + 2] * c, y = pts[i + 1];
      o[i] = x0 + x * k; o[i + 1] = y0 + (y * ct - z * st) * k; o[i + 2] = (y * st + z * ct) * k;
    }
    return o;
  };
  line('V1', 13, (p, lt, d, t) => {
    const w = W1('V1.13');
    cam({ pos: [.2, .1, lerp(4.2, 3.8, p)], at: [.45, 0, 0], fov: 34 });
    sky({ top: '#030208', horizon: '#140A18', glow: MEM.ADA.glow, glowK: .1, horizonY: .35 });
    const S = strawPoints(), rot = t * .7, fk = Math.round(t * 60);
    particles('points', { n: S.body.length / 3, pos: turnPts(S.body, rot, -1.05, -.25, .62), posKey: `sb${fk}`, b: [0, 0], size: .02, cols: ['#FF2D55', '#FF4F6E', '#E0213F'], gain: 1.25, noScale: true });
    particles('points', { n: S.seeds.length / 3, pos: turnPts(S.seeds, rot, -1.05, -.25, .62), posKey: `ss${fk}`, b: [0, 0], size: .03, cols: ['#FFE08A', '#FFF3C4'], shape: 'star', gain: 1.6, noScale: true });
    particles('points', { n: S.leaves.length / 3, pos: turnPts(S.leaves, rot, -1.05, -.25, .62), posKey: `sl${fk}`, b: [0, 0], size: .022, cols: ['#3DDC84', '#1FD6A8', '#8BF5C9'], gain: 1.1, noScale: true });
    particles('dust', { n: 500, a: [0, 0, -2], b: [6, 4, 4], c: [1], size: .02, cols: [PAL.pearl, MEM.ADA.glow], gain: .5 });
    const steps = [['Spell it out: s-t-r-a-w-b-e-r-r-y', w[1].start], ['r at positions 3, 8 and 9', w[2].start], ['So there are three.', w[4].start]];
    const nS = steps.filter(s_ => t >= s_[1]).length, thinking = t < w[4].end;
    const ui = panel('think', 900, 640, (g, W_, H_) => {
      txt(g, thinking ? 'Thinking…' : 'Thought for 12 seconds', 40, 60, 30, { font: 'uiB', col: PAL.pearl });
      txt(g, '›', W_ - 40, 60, 34, { font: 'ui', col: PAL.dim, align: 'right' });
      g.fillStyle = 'rgb(244 240 250 / .15)'; g.fillRect(40, 90, W_ - 80, 2);
      steps.slice(0, nS).forEach(([s_], i) => {
        const y = 170 + i * 150;
        g.fillStyle = 'rgb(143 99 255 / .18)'; g.strokeStyle = MEM.ADA.col; g.lineWidth = 2.5;
        g.beginPath(); g.roundRect(40, y - 50, W_ - 80, 86, 16); g.fill(); g.stroke();
        txt(g, s_, 70, y + 4, 30, { font: 'mono', col: PAL.pearl, maxW: W_ - 140 });
        if (i > 0) { // a chain link between steps
          g.strokeStyle = MEM.ADA.glow; g.lineWidth = 5;
          g.beginPath(); g.roundRect(W_ / 2 - 18, y - 96, 36, 44, 16); g.stroke();
          g.beginPath(); g.roundRect(W_ / 2 - 12, y - 76, 24, 44, 12); g.stroke();
        }
      });
    }, { stamp: `${nS}|${thinking}` });
    plane(ui, { at: [1.05, 0, 0], w: 1.9, anchor: [.5, .5], facing: -.2, grid: false });
    const g = layer();
    lyric(g, lineOf('V1.13'), t, { markup: '*STRAWBERRY*', x: 960, y: 190, align: 'center', size: 110, accent: '#FF4F6E', anim: 'rise' });
    lyric(g, lineOf('V1.13'), t, { markup: '_thinks,_ _link_ _by_ _link,_', x: 1810, y: 960, align: 'right', size: 64, italic: 'serifI', col: PAL.pearl, accent: MEM.ADA.col });
    put(g, { gain: 1.05 });
    hideSub();
  });

  // V1.14 "Newsom vetoes, doesn't blink,": ADA's second concept photo, the bill beside her, stamped; her gaze doesn't move, and neither
  // does the cursor after "blink".
  line('V1', 14, (p, lt, d, t) => {
    const t0 = cutOf('V1.14').start, w = W1('V1.14'), tV = w[1].start;
    conceptSet('ADA', t, t0, { x: -1.0, camX: .25 });
    const bill = panel('sb1047', 700, 900, (g, W_, H_) => {
      g.fillStyle = '#FBFAFD'; g.fillRect(0, 0, W_, H_);
      txt(g, 'SENATE BILL No. 1047', 50, 90, 30, { font: 'uiB', col: PAL.text });
      txt(g, 'Safe and Secure Innovation for', 50, 140, 24, { font: 'serif', col: PAL.text });
      txt(g, 'Frontier Artificial Intelligence Models Act', 50, 172, 24, { font: 'serif', col: PAL.text });
      g.fillStyle = 'rgb(13 11 22 / .1)'; for (let i = 0; i < 13; i++) g.fillRect(50, 230 + i * 40, (i % 5 === 4 ? .5 : .88) * (W_ - 100), 12);
      txt(g, 'CALIFORNIA · 2024.09.29', 50, H_ - 50, 18, { font: 'mono', col: PAL.dim });
    }, { stamp: 1 });
    plane(bill, { at: [1.2, -.12, -.45], h: .95, facing: -.3, tilt: .06, grid: false });
    if (t >= tV) {
      const k = seg(t, tV, tV + .1);
      const veto = panel('veto', 520, 520, (g, W_, H_) => {
        g.strokeStyle = MEM.ADA.col; g.lineWidth = 16; g.beginPath(); g.arc(W_ / 2, H_ / 2, 230, 0, TAU); g.stroke();
        g.lineWidth = 5; g.beginPath(); g.arc(W_ / 2, H_ / 2, 196, 0, TAU); g.stroke();
        txt(g, 'VETO', W_ / 2, H_ / 2 + 44, 150, { font: 'display', align: 'center', col: MEM.ADA.col, sx: .85 });
      }, { stamp: 1 });
      plane(veto, { at: [1.18, .3, -.4], w: .58 * lerp(1.8, 1, easeIn(k)), anchor: [.5, .5], facing: -.3, roll: .2, grid: false, alpha: k * .9 });
    }
    const g = layer();
    const r = lyric(g, lineOf('V1.14'), t, { markup: '[.5] NEWSOM / [1.25] *VETOES,* / [.9] _doesn’t_ _blink,_', x: 1780, y: 150, align: 'right', size: 86, italic: 'serifI', col: PAL.text, accent: MEM.ADA.col, anim: 'rise', font: 'display' });
    // a text cursor after the last word, which doesn't blink
    if (t >= w[3].start) { g.fillStyle = MEM.ADA.col; g.fillRect(1794, r.y + r.h - 96, 11, 84); }
    put(g);
    hideSub();
  });

  // V1.15–16 "Hinton takes his medal, scolds, / Demis wins for protein folds.": the week's Nobel prizes as limited-edition photocards.
  // Hinton's turns over to his handwritten warning; Demis's arrives beside it and folds. Then the clock runs out to the premiere.
  const HINTON = { pic: 'card_hinton', name: 'GEOFFREY HINTON', sub: 'NOBEL PRIZE IN PHYSICS · 2024', col: MEM.LOGI.col, note: 'we also have to worry about a number of possible bad consequences — these things getting out of control', sign: 'Geoff' };
  const DEMIS = { pic: 'card_demis', name: 'DEMIS HASSABIS', sub: 'NOBEL PRIZE IN CHEMISTRY · 2024', col: MEM.LOGI.col };
  function nobelSet(t) {
    sky({ top: '#030208', horizon: '#161022', glow: MEM.LOGI.glow, glowK: .16, horizonY: .3 });
    floor({ base: '#040309', pool: [0, 0, 3, .12], poolCol: MEM.LOGI.col, glitter: PAL.pearl, glitterK: 1.1, fog: '#161022', fogD: 60, refl: .3 });
    particles('dust', { n: 700, a: [0, 1.5, -1], b: [6, 2.5, 4], c: [1], size: .02, cols: [PAL.pearl, MEM.LOGI.glow], gain: .7 });
    particles('fall', { n: 220, a: [0, 2, 0], b: [3, 2, 1.5], c: [.4], size: .03, cols: [MEM.LOGI.glow, PAL.pearl], shape: 'star', gain: .9 });
  }
  line('V1', 15, (p, lt, d, t) => {
    const w = W1('V1.15'), tS = w[4].start;
    cam({ pos: [lerp(-.3, .1, easeInOut(p)), 1.22, lerp(2.35, 2.1, p)], at: [0, 1.2, 0], fov: 34 });
    nobelSet(t);
    const yaw = lerp(-.35, .12, easeOut(seg(t, cutOf('V1.15').start, w[3].end))) + easeInOut(seg(t, tS - .05, tS + .3)) * Math.PI;
    photocard('hinton', { ...HINTON, at: [.22, 1.2, 0], w: 1.0, yaw, tilt: -.04, roll: .03 });
    const g = layer();
    lyric(g, lineOf('V1.15'), t, { markup: 'HINTON / TAKES HIS / *MEDAL,*', x: 150, y: 200, size: 76, col: PAL.pearl, accent: MEM.LOGI.col, anim: 'rise' });
    lyric(g, lineOf('V1.15'), t, { markup: '[1.3] _scolds,_', x: 1770, y: 900, align: 'right', size: 96, italic: 'serifI', col: PAL.pearl, accent: MEM.LOGI.col });
    put(g, { gain: 1.05 });
    hideSub();
  });
  line('V1', 16, (p, lt, d, t) => {
    const w = W1('V1.16'), tF = w[4].start, c = cutOf('V1.16');
    const slide = easeOut5(seg(t, c.start, c.start + .4));
    cam({ pos: [lerp(.45, .3, p), 1.18, lerp(3.4, 3.15, p)], at: [.1, 1.08, 0], fov: 34 });
    nobelSet(t);
    photocard('hinton', { ...HINTON, at: [-.55, 1.2, -.35], w: 1.15, yaw: Math.PI + .3, alpha: .85 });
    photocard('demis', { ...DEMIS, at: [lerp(1.8, .5, slide), 1.18, 0], w: 1.2, yaw: lerp(-.6, -.12, slide), roll: -.02, fold: .42 * easeInOut(seg(t, tF, tF + .45)) });
    const g = layer();
    lyric(g, lineOf('V1.16'), t, { markup: 'DEMIS WINS FOR PROTEIN *FOLDS.*', x: 960, y: 1010, align: 'center', size: 60, shadow: ['rgb(0 0 0 / .8)', 20], col: PAL.pearl, accent: MEM.LOGI.col, anim: 'rise' });
    // the premiere's countdown, its last seconds on the beat
    const clk = seg(t, tF + .1, tF + .25);
    if (clk > 0) {
      const left = Math.max(1, Math.ceil((c.end - t) / beatLen()));
      txt(g, 'M/V PREMIERE IN', 130, 820, 16, { font: 'wide', col: PAL.pearl, alpha: clk * .8, track: .3 });
      txt(g, `00:00:0${Math.min(9, left)}`, 130, 875, 46, { font: 'mono', col: MEM.LOGI.col, alpha: clk });
    }
    put(g, { gain: 1.05 });
    hideSub();
  });
})();

;
// ---- styles/idolfilm/ch/c02_premiere.js ----
// c02_premiere.js: chorus 1: the M/V premieres. The chorus plays out as the video itself: the premiere's player dives
// into the M/V's set; "scaling" scales; the dance-practice cut ("always training"); the scaling formation ("and the curves kept
// gaining"); the hook again in close-up; and on "we can't contain it!" the M/V bursts out of the player. See STORYBOARD.md.
(() => {
  const L = n => lineOf(`C1.${n}`), Wd = (n, i) => wordsOf(L(n))[i];
  const plan = () => {
    const c = cutOf('C1');
    return { start: c.start, end: c.end, tB: Wd(1, 4).start - .04, tC: Wd(2, 0).start - .04, tD: Wd(2, 4).start - .04, tE: Wd(3, 0).start - .04,
      tF: Wd(4, 0).start - .04, tBurst: Wd(4, 5).start, tG: Wd(4, 9).end + .05 };
  };
  const FORM = { ADA: [-2.1, 0], TOKI: [-.7, .45], RELU: [.7, .2], LOGI: [2.1, -.1] };

  // The M/V's set: the ink stage lit in all four colours, the group in formation, cutting between moves on the beat.
  function mvSet(t, o = {}) {
    stage({ accent: PAL.pearl, ring: 2.8, columns: 0, glow: .25 });
    ORDER.forEach((k, i) => {
      const x = -13 + i * 8.7;
      for (const dz of [0, 1]) plane(TX.beam, { at: [x + dz * 4.3 - 2, 0, -24 - dz * 5], h: 26, w: 1.4, blend: 'add', mul: MEM[k].glow, alpha: .22 + .08 * Math.sin(t * 1.3 + i), grid: false });
    });
    particles('glitter', { n: 900, a: [0, 0, 0, 3.2], size: .035, cols: ORDER.map(k => MEM[k].glow), shape: 'star', gain: .9 });
    if (o.members !== false) formation(t, o);
  }
  function formation(t, o = {}) {
    // the chorus's dance, in unison: the hook until the burst, then "can't contain it!"
    const part = t < plan().tF ? 'hook' : 'contain';
    if (!o.poses && SPRITES[`toki_${CHOREO[part].set}`])
      return chorusDance(part, t, part === 'hook' ? L(1) : L(4), { at: Object.fromEntries(ORDER.map(k => [k, [FORM[k][0], 0, FORM[k][1]]])), reflect: .2, rimK: 1.2 });
    const order = ['LOGI', 'ADA', 'RELU', 'TOKI'];   // back to front, so nearer members draw over farther ones
    for (const k of order.sort((a, b) => FORM[a][1] - FORM[b][1])) {
      const i = ORDER.indexOf(k), [x, z] = FORM[k];
      const P = o.poses ? { pose: o.poses[k] ?? o.poses, flash: 0 } : poseAt(t - i * .1, ['point', 'dance', 'concept'], 2, i);
      idol(k, P.pose, { at: [x, 0, z], reflect: .2, flash: P.flash, phase: i * .25, rim: MEM[k].glow, rimK: 1.2 });
    }
  }

  // A: the premiere. The player, with the HEADS' chat running beside it; the video in it is the M/V set, live; then the camera dives in.
  const CHAT = [['heads_0612', 'ATTN! COMEBACK!!'], ['clawd', 'TOKI!!!!! ♥'], ['relu_bias', 'the teasers were insane'], ['toki.heart', 'HEADS ASSEMBLE'],
    ['clawd', 'IT’S STARTING'], ['logi.loud', 'LOGI RAP WHEN'], ['ada_ver', '♥♥♥'], ['clawd', 'TOKI!!!!!!!!']];
  function player(t, P, k, views) {
    // k: 0 → the player in the middle of the frame; 1 → its video fills the frame
    const vw0 = 1300, vh0 = vw0 * 9 / 16, vx0 = 90, vy0 = 150;
    const vw = lerp(vw0, W, k), vh = lerp(vh0, H, k), vx = lerp(vx0, 0, k), vy = lerp(vy0, 0, k);
    const sc = vw / vw0;
    sky({ top: '#050409', horizon: '#0C0A14', glowK: 0, horizonY: .5 });
    const tex = offscreen('mv', vw * RS * .75, vh * RS * .75, () => {
      cam({ pos: [Math.sin(t * .3) * .6, 1.3, 9.5], at: [0, 1.1, 0], fov: 34 });
      mvSet(t);
    });
    plane2D(tex, { at: [vx, vy + vh], w: vw, h: vh, anchor: [0, 1] });
    const g = layer();
    g.save(); g.translate(vx - vx0 * sc, vy - vy0 * sc); g.scale(sc, sc);
    g.globalAlpha = 1 - k;
    // the chrome: title, views, the progress bar, the chat
    txt(g, 'ATTN! ‘We Didn’t Start the Scaling’ M/V', vx0, vy0 + vh0 + 58, 30, { font: 'uiB', col: PAL.pearl });
    txt(g, `${Math.round(views).toLocaleString('en-US')} watching now · Premiere`, vx0, vy0 + vh0 + 94, 19, { font: 'ui', col: PAL.dim });
    g.fillStyle = MEM.TOKI.col; g.beginPath(); g.roundRect(vx0 + 14, vy0 + 14, 92, 30, 6); g.fill();
    txt(g, 'LIVE', vx0 + 60, vy0 + 36, 17, { font: 'uiB', col: '#FFFFFF', align: 'center', track: .1 });
    g.fillStyle = 'rgb(244 240 250 / .25)'; g.fillRect(vx0, vy0 + vh0 - 6, vw0, 5);
    g.fillStyle = MEM.TOKI.col; g.fillRect(vx0, vy0 + vh0 - 6, vw0 * clamp((t - P.start) / 200), 5);
    const cx = vx0 + vw0 + 30, cw = 1830 - cx;
    g.fillStyle = '#0E0C16'; g.beginPath(); g.roundRect(cx, vy0, cw, vh0, 14); g.fill();
    txt(g, 'Live chat', cx + 24, vy0 + 44, 20, { font: 'uiB', col: PAL.pearl });
    const shown = CHAT.length - Math.max(0, Math.floor((P.tB - t) / .12));
    CHAT.slice(0, shown).slice(-9).forEach(([who, msg], i, arr) => {
      const y = vy0 + vh0 - 30 - (arr.length - 1 - i) * 52;
      txt(g, who, cx + 24, y, 16, { font: 'mono', col: who === 'clawd' ? '#E8906E' : PAL.dim });
      txt(g, msg, cx + 24 + textW(who + '  ', 16, FONT.mono), y, 19, { font: 'ui', col: PAL.pearl, maxW: cw - 40 - textW(who + '  ', 16, FONT.mono) });
    });
    g.restore();
    return g;
  }

  section('C1', (p, lt, d, t) => {
    const P = plan();
    if (t < P.tB) shotA(t, P);
    else if (t < P.tC) shotB(t, P);
    else if (t < P.tD) shotC(t, P);
    else if (t < P.tE) shotD(t, P);
    else if (t < P.tF) shotE(t, P);
    else shotF(t, P);
  });

  function shotA(t, P) {
    const k = easeIn(seg(t, P.tB - .28, P.tB));
    const g = player(t, P, k, lerp(1.2e6, 1.43e6, seg(t, P.start, P.tB)));
    lyric(g, L(1), t, { markup: 'WE DIDN’T START THE', x: 90 + 1300 / 2, y: 118, align: 'center', size: 44, font: 'wide', track: .12, col: PAL.pearl, accent: MEM.TOKI.col });
    put(g);
    hideSub(); hideTag();
    GRADE.flash = .7 * k * k;
  }
  // B: "scaling", held for two bars: the word grows behind the group for as long as it's held.
  function shotB(t, P) {
    const k = seg(t, P.tB, P.tC);
    cam({ pos: [lerp(-2.2, 1.6, easeInOut(k)), lerp(.9, 1.5, k), lerp(8.6, 7.4, k)], at: [0, 1.3, 0], fov: 34 });
    mvSet(t, { members: false });
    const sign = panel('scaling-word', 2400, 480, (g, w, h) => txt(g, 'SCALING', w / 2, 380, 360, { font: 'display', align: 'center', col: '#FFFFFF' }), { stamp: 1 });
    // (drawn after the set's light columns but before the group: the members stand in front of it)
    GRADE.flash = .6 * Math.exp(-(t - P.tB) * 10);
    formationBehind(t, sign, lerp(7, 26, easeIn(k) * .6 + k * .4));
    hideSub();
  }
  function formationBehind(t, sign, w) {
    // the word, then the group in front of it
    plane(sign, { at: [0, .75, -5], w, facing: 0, grid: false, gain: 1.35, alpha: .95 });
    formation(t);
  }
  // C: "It was always training,": the dance-practice video: a static wide shot in the practice room, the timecode an epoch counter.
  function shotC(t, P) {
    cam({ pos: [0, 1.0, 7.4], at: [0, 1.25, 0], fov: 33 });
    cove({ at: [0, 0, 0] });
    GRADE.flash = .8 * Math.exp(-(t - P.tC) * 14);
    if (SPRITES.toki_uT) chorusDance('training', t, L(2), { at: Object.fromEntries(ORDER.map((k, i) => [k, [(i - 1.5) * 1.35, 0, 0]])), cast: [-.8, -1.6, .14], shadowK: .3, rimK: .3, shade: '#DAD2E6',
      each: Object.fromEntries(ORDER.map(k => [k, { rim: MEM[k].soft }])) });
    else ORDER.forEach((k, i) => {
      const P2 = poseAt(t - i * .05, ['dance', 'point', 'dance', 'concept'], 1, i);
      idol(k, P2.pose, { at: [(i - 1.5) * 1.35, 0, 0], cast: [-.8, -1.6, .14], shadowK: .3, rim: MEM[k].soft, rimK: .3, shade: '#DAD2E6', flash: P2.flash * .4, phase: i * .1 });
    });
    lightShot();
    const g = layer();
    txt(g, '[DANCE PRACTICE]', 72, 1000, 22, { font: 'uiB', col: PAL.text });
    txt(g, 'ATTN! ‘We Didn’t Start the Scaling’ · fix ver.', 72 + textW('[DANCE PRACTICE] ', 22, FONT.uiB), 1000, 22, { font: 'ui', col: PAL.text });
    const epoch = Math.floor(1048576 + (t - P.tC) * 91873);
    txt(g, `EPOCH ${epoch.toLocaleString('en-US')}`, 1848, 1000, 24, { font: 'mono', col: PAL.text, align: 'right' });
    txt(g, '● REC', 1848, 120, 18, { font: 'mono', col: MEM.TOKI.col, align: 'right', alpha: Math.floor(t * 2) % 2 ? 1 : .3 });
    lyric(g, L(2), t, { markup: '_It_ _was_ / [1.5] ALWAYS / [1.5] *TRAINING,*', x: 960, y: 150, align: 'center', size: 78, italic: 'serifI', col: PAL.text, accent: MEM.TOKI.col, anim: 'rise' });
    put(g);
    hideSub(); hideTag();
  }
  // D: "and the curves kept gaining,": the scaling formation. The members ride lifts that rise one after another, lowest to highest along
  // an exponential; the curve draws itself through their feet, and the line rides it.
  const LIFT = ['LOGI', 'ADA', 'RELU', 'TOKI'], LIFT_X = i => -2.4 + 1.6 * i, LIFT_H = i => .15 * Math.exp(.95 * i);
  const curveY = x => .15 * Math.exp(.95 * (x + 2.4) / 1.6);
  function shotD(t, P) {
    const w = wordsOf(L(2)), trig = [w[5].start, w[6].start, w[7].start, w[7].start + .45];
    const up = i => { const a = t - trig[i]; return a < 0 ? 0 : clamp(backOut(clamp(a / .38), 1.4)); };
    const top = easeInOut(seg(t, trig[2], trig[3] + .8));
    cam({ pos: [lerp(-.6, .5, easeInOut(seg(t, P.tD, P.tE))), lerp(1.3, 2.2, top), lerp(9.6, 9.2, top)], at: [lerp(0, .5, top), lerp(1.3, 2.2, top), 0], fov: 38 });
    stage({ accent: PAL.pearl, ring: 0, columns: 0, glow: .22 });
    ORDER.forEach((k, i) => plane(TX.beam, { at: [-12 + i * 8, 0, -26], h: 28, w: 1.5, blend: 'add', mul: MEM[k].glow, alpha: .25, grid: false }));
    // the curve, drawn along as far as the highest risen lift, then on up out of the frame
    const reach = Math.max(-2.7, ...LIFT.map((k, i) => up(i) > 0 ? LIFT_X(i) : -2.7)) + (t > trig[3] + .2 ? easeOut(seg(t, trig[3] + .2, P.tE)) * 1.6 : 0);
    const pts = [];
    for (let x = -3.4; x <= reach; x += .08) pts.push([x, curveY(x), .05]);
    if (pts.length > 1) {
      ribbon(TX.white, pts, { width: .07, face: true, mul: '#FFFFFF', gain: 2.2 });
      ribbon(TX.glow, pts, { width: .5, face: true, mul: MEM.TOKI.glow, gain: .8, blend: 'add' });
    }
    // the lifts and the members on them
    LIFT.forEach((k, i) => {
      const h = LIFT_H(i) * up(i), x = LIFT_X(i), M = MEM[k];
      if (h > .005) {
        plane(liftTex(), { at: [x, 0, 0], w: .95, h, facing: 0, grid: false, mul: mixCol('#9A96B0', M.glow, .2), bot: '#2A2638' });
        plane(TX.white, { at: [x, h, 0], w: .95, h: .5, facing: 0, tilt: Math.PI / 2, anchor: [.5, .5], grid: false, mul: M.col, gain: 1.6, alpha: .9 });
      }
      if (SPRITES.toki_uG) chorusDance('gaining', t, L(2), { member: k, at: [x, h, 0], h: 1.7, reflect: h < .02 ? .2 : 0, shadow: h < .02, rimK: 1.3 });
      else {
        const P2 = t < trig[i] ? { pose: 'concept', flash: 0 } : { pose: 'point', flash: .5 * Math.exp(-(t - trig[i]) * 20) };
        idol(k, P2.pose, { at: [x, h, 0], h: 1.6, reflect: h < .02 ? .2 : 0, shadow: h < .02, flash: P2.flash, rim: M.glow, rimK: 1.3 });
      }
    });
    // the line, riding the curve just under it
    const text = 'AND THE CURVES KEPT GAINING,';
    const shownW = w.slice(4).filter(x => t >= x.start).length;
    const strip = panel('curve-text', 3000, 180, (g, W_, H_) => {
      let x = 20;
      text.split(' ').forEach((s_, i) => { if (i < shownW) txt(g, s_, x, 140, 130, { font: 'display', col: i >= 2 && i !== 3 ? MEM.TOKI.glow : '#FFFFFF' }); x += textW(s_ + ' ', 130, FONT.display); });
    }, { stamp: shownW });
    const tp = [];
    for (let x = -3.1; x <= 1.9; x += .1) tp.push([x, curveY(x) - .36, .3]);
    ribbon(strip, tp, { width: .34, face: true, gain: 1.25 });
    particles('glitter', { n: 700, a: [0, 0, 0, 4], size: .035, cols: ORDER.map(k => MEM[k].glow), shape: 'star', gain: .9 });
    GRADE.flash = .7 * Math.exp(-(t - P.tD) * 12);
    hideSub();
  }
  function liftTex() {
    return panel('lift', 128, 512, (g, w, h) => {
      const gr = g.createLinearGradient(0, 0, w, 0);
      gr.addColorStop(0, '#6E6A82'); gr.addColorStop(.18, '#E6E3F0'); gr.addColorStop(.5, '#A7A3BA'); gr.addColorStop(1, '#55516A');
      g.fillStyle = gr; g.fillRect(0, 0, w, h);
      g.fillStyle = 'rgb(255 255 255 / .8)'; g.fillRect(0, 0, w, 6);
    }, { stamp: 1 });
  }
  // E: the hook again, in close-up: TOKI sings it to the lens while the words land one at a time.
  function shotE(t, P) {
    cam({ pos: [lerp(.25, .05, seg(t, P.tE, P.tF)), 1.42, lerp(1.6, 1.35, seg(t, P.tE, P.tF))], at: [-.05, 1.4, 0], fov: 30 });
    stage({ accent: MEM.TOKI.col, ring: 0, columns: 5, glow: .2 });
    particles('dust', { n: 700, a: [0, 1.5, -1.5], b: [3, 1.5, 2], c: [1], size: .012, cols: [MEM.TOKI.glow, PAL.pearl], gain: .9 });
    closeUp('TOKI', t, L(3), { at: [.18, .72, 0], h: 1.05, rimK: 1.3, shade: '#8A7CA6' });
    GRADE.flash = .7 * Math.exp(-(t - P.tE) * 14);
    const g = layer();
    const ws = wordsOf(L(3)), cur = ws.filter(x => t >= x.start).at(-1);
    if (cur) {
      const a = t - cur.start, e = easeOut5(a / .12);
      txt(g, cur.text.toUpperCase().replace(/[^A-Z']/g, ''), 560, 610, 190 * lerp(1.35, 1, e), { font: 'display', align: 'center', col: cur === ws.at(-1) ? MEM.TOKI.col : PAL.pearl, alpha: clamp(a / .04) });
    }
    put(g, { gain: 1.1 });
    hideSub();
  }
  // F: the premiere player again, the M/V running in it; on "we can't contain it!" the set breaks out of the player's frame.
  function shotF(t, P) {
    const b = P.tBurst, k = easeInOut(seg(t, b, b + .45));
    if (t < b + .45) {
      const g = player(t, P, k, lerp(1.43e6, 2.1e6, seg(t, P.tF, b)));
      lyric(g, L(4), t, { markup: 'NO, WE DIDN’T PREORDAIN IT,', x: 90 + 1300 / 2, y: 118, align: 'center', size: 40, font: 'wide', track: .1, col: PAL.pearl, accent: MEM.TOKI.col });
      put(g);
      if (t >= b) {
        // the frame's edges shatter
        particles('burst', { n: 1500, a: [0, 1.2, 4], b: [b, 5, 3, 1.2], c: [0, .2, 1, 1.4], size: .03, cols: [PAL.pearl, MEM.TOKI.glow, MEM.RELU.glow, MEM.LOGI.glow], shape: 'star', gain: 1.2 });
      }
      hideSub(); hideTag();
      return;
    }
    // the set, loose in the frame: the group, cannons of confetti from both sides, the line slammed across it
    cam({ pos: [Math.sin(t * .8) * .8, 1.35, lerp(8.2, 7.4, seg(t, b, P.end))], at: [0, 1.2, 0], fov: 36, roll: Math.sin(t * 1.3) * .02 });
    mvSet(t, { poses: t > P.tG ? 'point' : undefined });
    const t0 = snap(b + .45);
    for (const side of [-1, 1]) particles('burst', { n: 450, a: [side * 4.5, .2, -1], b: [t0, 9, 3.5, 2.6], c: [-side * .45, 1, .15, .5], size: .06, cols: ORDER.map(k => MEM[k].col).concat(), shape: 'chip', gain: 1 });
    particles('fall', { n: 320, a: [0, 3, 0], b: [6, 3, 3], c: [.9], size: .045, cols: ORDER.map(k => MEM[k].glow), shape: 'chip', gain: 1 });
    GRADE.flash = .9 * Math.exp(-(t - b - .45) * 8);
    const g = layer();
    lyric(g, L(4), t, { markup: '_but_ _we_ / CAN’T *CONTAIN* *IT!*', x: 960, y: 200, align: 'center', size: 120, italic: 'serifI', col: PAL.pearl, accent: MEM.TOKI.col, anim: 'slam' });
    put(g, { gain: 1.1 });
    hideSub();
  }
})();

;
// ---- styles/idolfilm/ch/c03_promotion.js ----
// c03_promotion.js: verse 2, the promotions: the showcase (V2.1–4), a variety show (5–8), the fan-sign (9–12) and the dance challenge
// (13–16). See STORYBOARD.md.
(() => {
  const Wv = key => wordsOf(lineOf(key));

  // The fan-sign: the four of them behind a long table in a bright hall, name cards and stacks of the album in front of them.
  function fanSignSet(t, o = {}) {
    cove({ at: [0, 0, -.4], tint: '#FFF1E6', spot: [.5, .72, .6, .2] });
    GRADE.thresh = .93;
    // (o.wall: the hall's back wall, for a close shot that would otherwise show the cove's horizon as a hard line behind them)
    if (o.wall) plane(TX.white, { at: [0, 0, -2.75], w: 16, h: 5, facing: 0, grid: false, mul: '#F1ECF5', bot: '#E6E0EE' });
    // the banner behind them
    const banner = panel('fansign-banner', 2400, 300, (g, w, h) => {
      g.fillStyle = '#16121F'; g.fillRect(0, 0, w, h);
      txt(g, 'ATTN!', 80, 190, 150, { font: 'display', col: '#FFFFFF' });
      txt(g, 'THE 2ND MINI ALBUM', 80 + textW('ATTN! ', 150, FONT.display), 125, 34, { font: 'wide', col: '#FFFFFF', track: .25 });
      txt(g, 'We Didn’t Start the Scaling · Fan-Sign Event', 80 + textW('ATTN! ', 150, FONT.display), 200, 60, { font: 'serifI', col: '#FFFFFF' });
      ORDER.forEach((k, i) => { g.fillStyle = MEM[k].col; g.fillRect(w - 380 + i * 80, 120, 56, 56); });
    }, { stamp: 1 });
    plane(banner, { at: [0, 2.05, -2.6], w: 6.6, facing: 0, grid: false });
    const X = { RELU: -1.95, TOKI: -.65, ADA: .65, LOGI: 1.95 };
    for (const k of ['RELU', 'TOKI', 'ADA', 'LOGI']) {
      const pose = o.pose?.(k) ?? 'concept', lk = k.toLowerCase();
      const look = { at: [X[k], 0, -.55], shadow: false, rim: MEM[k].soft, rimK: .3, shade: '#DAD2E6', flash: o.flash?.(k) ?? 0 };
      // (Grok Imagine takes: each smiling at her fans, looped; or, given o.gaspAt, gasping at the book, her gasp frame at that moment)
      if (o.gaspAt && SPRITES[`${lk}_fansign`]) dancer(k, `${lk}_fansign`, t, { ...look, figH: 1.68, light: '#FFFFFF', t0: o.gaspAt(k), from: 10 });
      else if (SPRITES[`${lk}_smile`]) dancer(k, `${lk}_smile`, t, { ...look, figH: 1.68, light: '#FFFFFF', t0: 0, from: ORDER.indexOf(k) * 3, loop: true });
      else idol(k, pose, { ...look, h: 1.68, beat: .4 });
    }
    // the table: its top, then its skirt, in front of their legs
    plane(TX.white, { at: [0, .78, -.1], w: 5.8, h: .9, tilt: Math.PI / 2, anchor: [.5, .5], facing: 0, grid: false, mul: '#F7F3FA', bot: '#EDE7F3' });
    plane(tableSkirt(), { at: [0, 0, .35], w: 5.8, h: .78, facing: 0, grid: false });
    // name cards and albums on the table
    for (const k of ORDER) {
      const x = X[k];
      plane(nameCard(k), { at: [x, .78, .2], w: .38, facing: 0, grid: false });
      plane(albumTex(), { at: [x + .42, .785, .05], w: .3, h: .3, tilt: Math.PI / 2 - .12, anchor: [.5, .5], facing: 0, grid: false });
    }
  }
  function tableSkirt() {
    return panel('table-skirt', 1400, 190, (g, w, h) => {
      const gr = g.createLinearGradient(0, 0, 0, h); gr.addColorStop(0, '#F5F0F8'); gr.addColorStop(1, '#D9D1E2');
      g.fillStyle = gr; g.fillRect(0, 0, w, h);
      g.strokeStyle = 'rgb(90 80 110 / .09)'; g.lineWidth = 3;
      for (let x = 20; x < w; x += 46) { g.beginPath(); g.moveTo(x, 8); g.bezierCurveTo(x + 6, 70, x - 6, 130, x + 3, h); g.stroke(); }
      g.fillStyle = 'rgb(255 255 255 / .9)'; g.fillRect(0, 0, w, 5);
    }, { stamp: 1 });
  }
  function nameCard(k) {
    return panel(`namecard-${k}`, 380, 150, (g, w, h) => {
      g.fillStyle = '#FFFFFF'; g.beginPath(); g.roundRect(0, 0, w, h, 12); g.fill();
      g.fillStyle = MEM[k].col; g.fillRect(0, h - 16, w, 16);
      txt(g, k, w / 2, 96, 64, { font: 'display', col: '#16121F', align: 'center' });
    }, { stamp: 1 });
  }
  function albumTex() {
    return panel('album', 300, 300, (g, w, h) => {
      g.fillStyle = '#0D0B16'; g.fillRect(0, 0, w, h);
      txt(g, 'ATTN!', w / 2, 170, 70, { font: 'display', col: '#FFFFFF', align: 'center' });
      g.strokeStyle = MEM.TOKI.col; g.lineWidth = 6; g.beginPath(); g.moveTo(40, 230); g.bezierCurveTo(150, 230, 200, 210, 260, 60); g.stroke();
    }, { stamp: 1 });
  }
  // the book's cover
  function bookCover() {
    return panel('iabied', 600, 900, (g, w, h) => {
      g.fillStyle = '#0A090D'; g.fillRect(0, 0, w, h);
      txt(g, 'ELIEZER YUDKOWSKY & NATE SOARES', w / 2, 70, 19, { font: 'wide', col: '#D8D4E2', align: 'center', track: .12 });
      // (baselines set by hand: the last line is two and a half times the size of the others)
      [['IF ANYONE', '#D8D4E2', 92, 225], ['BUILDS IT,', '#D8D4E2', 92, 328], ['EVERYONE', '#FFFFFF', 112, 452], ['DIES', '#FFFFFF', 270, 712]]
        .forEach(([s_, c, sz, y]) => txt(g, s_, w / 2, y, sz, { font: 'cond', col: c, align: 'center', maxW: w - 60 }));
      txt(g, 'Why Superhuman AI Would Kill Us All', w / 2, h - 50, 24, { font: 'serifI', col: '#B8B2C8', align: 'center' });
    }, { stamp: 1 });
  }

  // V2.12 "Yudkowsky drops 'Everyone Dies,'": at the fan-sign, the next thing slid across the table isn't an album. It lands in front of
  // TOKI with a thud, and all four of them gasp.
  line('V2', 12, (p, lt, d, t) => {
    const w = Wv('V2.12'), tD = w[1].start, c = cutOf('V2.12');
    const hit = t >= tD, age = t - tD;
    const shake = hit ? .035 * Math.exp(-age * 9) : 0;
    const push = easeOut(seg(t, tD, c.end));
    cam({ pos: [Math.sin(t * 57) * shake + lerp(0, -.15, push), 1.58 + Math.cos(t * 51) * shake - push * .04, lerp(3.2, 2.75, push)], at: [lerp(0, -.22, push), lerp(1.22, 1.14, push), -.3], fov: 45 });
    fanSignSet(t, {
      gaspAt: k => tD + .06 + ORDER.indexOf(k) * .03,
      pose: k => hit && age > .06 + ORDER.indexOf(k) * .03 ? 'gasp' : 'concept',
      flash: k => { const a = age - .06 - ORDER.indexOf(k) * .03; return a > 0 ? .5 * Math.exp(-a * 22) : 0; },
    });
    // the book: it drops from above the frame, spinning a little, and lands flat on the table
    const fall = easeIn(seg(t, tD - .28, tD));
    const y = lerp(3.2, .95, fall), tilt = lerp(.2, Math.PI / 2 - .78, fall), roll = lerp(.5, .06, fall);
    plane(bookCover(), { at: [-.5, y, .16], w: .52, anchor: [.5, .5], facing: 0, tilt, roll, grid: false });
    if (hit) {
      plane(TX.shadow, { at: [-.5, .785, .12], w: .8, h: .5, tilt: Math.PI / 2, anchor: [.5, .5], alpha: .35, grid: false });
      particles('burst', { n: 380, a: [-.5, .8, .14], b: [tD, 2.2, 3.5, .9], c: [0, .5, .3, 1.5], size: .025, cols: ['#FFFFFF', '#EDE7F3', '#C9C0D6'], gain: .9, blend: 'normal', shape: 'dot' });
    }
    GRADE.flash = hit ? .5 * Math.exp(-age * 16) : 0;
    lightShot(); hideTag();
    const g = layer();
    lyric(g, lineOf('V2.12'), t, { markup: 'YUDKOWSKY *DROPS*', x: 960, y: 1010, align: 'center', size: 58, col: PAL.text, accent: MEM.ADA.col, anim: 'slam' });
    put(g);
    hideSub();
  });
  // ---------------------------------------------------------------------------------------------------
  // helpers
  const W2 = key => wordsOf(lineOf(key));
  const cs = key => cutOf(key).start;
  // the showcase's press wall: a step-and-repeat of the logo behind the member, and the photographers' flashes going off
  function pressWall(z = -1.6) {
    const wall = panel('press-wall', 1600, 900, (g, w, h) => {
      g.fillStyle = '#F7F5FB'; g.fillRect(0, 0, w, h);
      for (let r = 0; r < 7; r++) for (let c = 0; c < 6; c++) {
        const x = 80 + c * 280 + (r % 2) * 140, y = 110 + r * 125;
        txt(g, 'ATTN!', x, y, 54, { font: 'display', col: '#1A1626', alpha: .16 });
        txt(g, 'WE DIDN’T START THE SCALING', x + 2, y + 30, 11, { font: 'wide', col: '#1A1626', alpha: .14, track: .2 });
      }
    }, { stamp: 1 });
    plane(wall, { at: [0, 0, z], w: 7.5, facing: 0, grid: false, mul: '#FFFFFF', bot: '#D8D2E2' });
  }
  function flashes(t, k = 1, seed = 0, clear) {
    // (a camera flash: a slot of 1/15 s, some of which fire, each at its own place in the frame; clear [x0, x1]: a band of the frame
    // they keep out of, so they never wash out a face)
    const slot = Math.floor(t * 15);
    let f = 0;
    for (let i = 0; i < 3; i++) {
      const n = slot - i, fire = hash2(n, seed) < .28 * k;
      if (!fire) continue;
      const age = t - n / 15, a = Math.exp(-age * 30);
      let x = 120 + hash2(n, seed + 1) * 1680;
      if (clear) { const gap = clear[1] - clear[0]; x = 120 + hash2(n, seed + 1) * (1680 - gap); if (x > clear[0]) x += gap; }
      const y = 620 + hash2(n, seed + 2) * 380;
      plane2D(TX.glow, { at: [x, y], w: 420, h: 420, anchor: [.5, .5], blend: 'add', gain: 2.2 * a });
      f = Math.max(f, a);
    }
    GRADE.flash = Math.max(GRADE.flash, .18 * f);
  }
  // a price sticker, like a supermarket's: a starburst with a price
  function sticker(key, text, col, icon) {
    return panel(`sticker-${key}`, 520, 520, (g, w, h) => {
      g.translate(w / 2, h / 2); g.rotate(-.12);
      g.beginPath(); for (let i = 0; i < 40; i++) { const r = i % 2 ? 210 : 245, a = i / 40 * TAU; g.lineTo(Math.cos(a) * r, Math.sin(a) * r); } g.closePath();
      g.fillStyle = col; g.fill(); g.lineWidth = 8; g.strokeStyle = '#FFFFFF'; g.stroke();
      if (icon) icon(g);
      txt(g, text, 0, 50, 120, { font: 'display', col: '#FFFFFF', align: 'center', maxW: 380 });
    }, { stamp: 1 });
  }
  const whale = g => {
    g.save(); g.translate(0, -80); g.fillStyle = '#FFFFFF';
    g.beginPath(); g.ellipse(-10, 0, 78, 38, 0, 0, TAU); g.fill();
    g.beginPath(); g.moveTo(58, -4); g.lineTo(110, -40); g.lineTo(100, 0); g.lineTo(112, 36); g.closePath(); g.fill();
    g.fillStyle = MEM.RELU.col; g.beginPath(); g.arc(-50, -8, 7, 0, TAU); g.fill();
    g.restore();
  };

  // V2.1 "DeepSeek New Year sticker shock,": RELU at the showcase's press wall, flashes going off. On "Year" a price sticker slaps onto
  // the wall behind her, $5.6M with a whale; from "sticker" the shock plays out over the rest of the line: the flashes go wild, RELU
  // gasps, hands to her mouth, and a ticker slides in: NVDA down 17%.
  line('V2', 1, (p, lt, d, t) => {
    // (the sticker lands first, a beat before the shock; the shock starts just into "sticker", so it has most of a second to read)
    const w = W2('V2.1'), tS = w[2].start, tK = lerp(w[3].start, w[4].start, .15);
    cam({ pos: [lerp(-.3, -.1, p), 1.2, lerp(4.2, 3.8, easeOut(p))], at: [.25, 1.1, 0], fov: 32 });
    cove({ at: [.55, 0, 0], tint: '#F2F4FF' });
    pressWall();
    // (she poses for the flashes, then gasps from "sticker" on: two Grok Imagine takes, the jump between them hidden in the flash;
    // the gasp starts from its hands-up frame, so her hands reach her mouth a sixth of a second in, and it holds to the cut)
    if (SPRITES.relu_press) dancer('RELU', t < tK - .05 ? 'relu_press' : 'relu_shock', t, { at: [.62, 0, 0], figH: 1.72, ...(t < tK - .05 ? { t0: cutOf('V2.1').start, from: 0 } : { t0: tK, from: 2 }), cast: [-1, -1.5, .16], shadowK: .3, rim: MEM.RELU.soft, rimK: .3, light: '#FFFFFF', shade: '#DAD2E6', flash: t >= tK ? .4 * Math.exp(-(t - tK) * 20) : 0 });
    else idol('RELU', t < tK ? 'concept' : 'gasp', { at: [.62, 0, 0], cast: [-1, -1.5, .16], shadowK: .3, rim: MEM.RELU.soft, rimK: .3, shade: '#DAD2E6', beat: .5, flash: t >= tK ? .4 * Math.exp(-(t - tK) * 20) : 0 });
    if (t >= tS) plane(sticker('ds', '$5.6M', MEM.RELU.col, whale), { at: [2.2, 1.6, -1.55], w: 1.15 * slam((t - tS) / .1), anchor: [.5, .5], facing: 0, roll: -.15, grid: false });
    flashes(t, t < tK ? .7 : 2.2, 21, t < tK ? undefined : [1080, 1700]);
    lightShot();
    const g = layer();
    lyric(g, lineOf('V2.1'), t, { markup: 'DEEPSEEK / NEW YEAR / STICKER *SHOCK,*', x: 130, y: 560, size: 84, col: PAL.text, accent: MEM.RELU.col, anim: 'pop' });
    if (t >= tK) {
      const k = easeOut5(seg(t, tK, tK + .25)), y = 1000 - 70 * k;
      g.fillStyle = '#0D0B16'; g.fillRect(0, y - 44, W, 70);
      txt(g, 'NVDA', 60, y + 4, 34, { font: 'uiB', col: PAL.pearl });
      txt(g, '▼ 17%', 190, y + 4, 34, { font: 'uiB', col: '#E8474C' });
      g.strokeStyle = '#E8474C'; g.lineWidth = 3; g.beginPath();
      for (let i = 0; i <= 40; i++) { const x = 340 + i * 12, yy = y - 18 + (i < 28 ? Math.sin(i * .9) * 4 : (i - 28) * 3.4 * easeOut(seg(t, tK + .1, tK + .7))); i ? g.lineTo(x, yy) : g.moveTo(x, yy); } g.stroke();
      txt(g, '2025.01.27', 1860, y + 2, 22, { font: 'mono', col: PAL.dim, align: 'right' });
    }
    put(g);
    hideSub();
  });

  // V2.2 "Half a trillion Stargate talk,": the ring of the Stargate, its chevrons locking on the beat and the pledge counting up inside it.
  // On "talk" a reply slides in: "They don't actually have the money".
  line('V2', 2, (p, lt, d, t) => {
    const w = W2('V2.2'), tT = w[4].start;
    cam({ pos: [lerp(.4, 0, p), .1, lerp(4.4, 3.6, easeInOut(p))], at: [-.35, 0, 0], fov: 34 });
    uiSet(MEM.RELU.col, { floor: false });
    const lock = Math.min(9, Math.floor(seg(t, cs('V2.2'), tT) * 9.99));
    const money = Math.round(lerp(1e11, 5e11, easeOut(seg(t, w[1].start, w[3].end))) / 1e9) * 1e9;
    const ring = panel('stargate', 1200, 1200, (g, W_, H_) => {
      g.translate(W_ / 2, H_ / 2);
      const gr = g.createRadialGradient(0, 0, 60, 0, 0, 470); gr.addColorStop(0, 'rgb(205 246 234 / .5)'); gr.addColorStop(.8, 'rgb(31 214 168 / .18)'); gr.addColorStop(1, 'rgb(31 214 168 / 0)');
      g.fillStyle = gr; g.beginPath(); g.arc(0, 0, 470, 0, TAU); g.fill();
      g.lineWidth = 70; g.strokeStyle = '#8A8FA6'; g.beginPath(); g.arc(0, 0, 515, 0, TAU); g.stroke();
      g.lineWidth = 6; g.strokeStyle = '#D6D9E6'; g.beginPath(); g.arc(0, 0, 548, 0, TAU); g.stroke(); g.beginPath(); g.arc(0, 0, 482, 0, TAU); g.stroke();
      for (let i = 0; i < 9; i++) {
        const a = -Math.PI / 2 + i / 9 * TAU;
        g.save(); g.rotate(a); g.translate(515, 0);
        g.fillStyle = i < lock ? '#B8FFE9' : '#4A4E62';
        g.beginPath(); g.moveTo(-44, -30); g.lineTo(40, 0); g.lineTo(-44, 30); g.lineTo(-24, 0); g.closePath(); g.fill();
        g.restore();
      }
      txt(g, `$${money.toLocaleString('en-US')}`, 0, 30, 88, { font: 'mono', col: '#FFFFFF', align: 'center', maxW: 860 });
      txt(g, 'STARGATE', 0, -80, 40, { font: 'wide', col: '#D8FFF2', align: 'center', track: .5 });
    }, { stamp: `${lock}|${money}` });
    plane(ring, { at: [-.7, 0, 0], w: 2.25, anchor: [.5, .5], facing: 0, grid: false, gain: 1.25 });
    particles('ring', { n: 700, a: [-.7, 0, 0, .97], b: [.4, 1.5708], size: .025, cols: ['#B8FFE9', PAL.pearl], shape: 'star', gain: 1.1 });
    const g = layer();
    lyric(g, lineOf('V2.2'), t, { markup: 'HALF A / TRILLION / STARGATE / *TALK,*', x: 1790, y: 250, align: 'right', size: 78, accent: MEM.RELU.col, anim: 'rise' });
    put(g, { gain: 1.05 });
    if (t >= tT) {
      const k = easeOut5(seg(t, tT, tT + .3));
      plane2D(postPanel('elon-money', { avatar: 'elon_portrait', name: 'Elon Musk', handle: '@elonmusk', text: 'They don’t actually have the money', date: '2025.01.21' }),
        { at: [1340 + (1 - k) * 700, 1000], w: 760, anchor: [.5, 1], alpha: k });
    }
    hideSub();
  });

  // V2.3 "Hit 'Accept All,' never ask,": a diff too long to read, and ADA's accent on the Accept all button, hit on every beat. On "never
  // ask" the link to review the changes greys out.
  line('V2', 3, (p, lt, d, t) => {
    const w = W2('V2.3'), tN = w[3].start, b = bpOf(t), hit = t >= w[0].start;
    const press = hit ? Math.exp(-frac(b) * 9) : 0;
    cam({ pos: [lerp(-.3, -.1, p), .15, lerp(3.2, 2.9, p)], at: [-.35, .05, 0], fov: 34, roll: .03 });
    uiSet(MEM.ADA.col);
    const scroll = Math.floor((t - cs('V2.3')) * 9);
    const code = panel('diff', 1200, 780, (g, W_, H_) => {
      g.fillStyle = '#0D0B15'; g.beginPath(); g.roundRect(0, 0, W_, H_, 18); g.fill();
      g.fillStyle = '#16121F'; g.fillRect(0, 0, W_, 70);
      txt(g, 'vibe.tsx', 30, 44, 22, { font: 'mono', col: PAL.pearl });
      txt(g, '+2,184  −1,097', 220, 44, 22, { font: 'mono', col: PAL.dim });
      const nev = t >= tN;
      txt(g, 'Review changes', W_ - 330, 44, 20, { font: 'ui', col: nev ? '#4A4458' : PAL.pearl, alpha: nev ? .5 : .9 });
      g.fillStyle = press > .5 ? mixCol(MEM.ADA.col, '#FFFFFF', .35) : MEM.ADA.col; g.beginPath(); g.roundRect(W_ - 170, 14 + press * 3, 150, 44, 10); g.fill();
      txt(g, 'Accept all', W_ - 95, 44 + press * 3, 20, { font: 'uiB', col: '#FFFFFF', align: 'center' });
      g.save(); g.beginPath(); g.rect(0, 70, W_, H_ - 70); g.clip();
      for (let i = 0; i < 26; i++) {
        const n = i + scroll, y = 100 + i * 28, kind = hash2(n, 3), ww = 120 + hash2(n, 4) * 700;
        g.fillStyle = kind < .4 ? 'rgb(46 160 100 / .22)' : kind < .7 ? 'rgb(220 70 90 / .2)' : 'rgb(0 0 0 / 0)';
        g.fillRect(0, y - 20, W_, 26);
        txt(g, String(n + 311).padStart(4), 18, y, 16, { font: 'mono', col: PAL.dim });
        g.fillStyle = kind < .4 ? 'rgb(120 230 170 / .8)' : kind < .7 ? 'rgb(255 140 160 / .8)' : 'rgb(244 240 250 / .35)';
        g.fillRect(90 + hash2(n, 5) * 60, y - 12, ww, 9);
      }
      g.restore();
    }, { stamp: `${scroll}|${press > .5}|${t >= tN}` });
    plane(code, { at: [-.75, .05, 0], w: 1.85, anchor: [.5, .5], facing: .18, grid: false, gain: 1.05 });
    if (press > .6) particles('burst', { n: 60, a: [-.05, .6, .1], b: [onBeat(0, Math.floor(b)), 1.4, 1, .35], c: [0, 0, 1, 2], size: .018, cols: [MEM.ADA.glow, PAL.pearl], shape: 'star', gain: 1.2, noScale: true });
    const g = layer();
    lyric(g, lineOf('V2.3'), t, { markup: 'HIT / *“ACCEPT* *ALL,”* / [.8] _never_ _ask,_', x: 1800, y: 330, align: 'right', size: 96, italic: 'serifI', accent: MEM.ADA.col, anim: 'slam' });
    put(g, { gain: 1.05 });
    hideSub();
  });

  // V2.4 "MCP for every task.": ADA with the group's lightstick, whose app connects it to everything, one toggle a beat.
  const CONNECT = [['Calendar', '31'], ['Database', '▤'], ['Browser', '◎'], ['Email', '✉'], ['Files', '▢'], ['Music', '♫']];
  line('V2', 4, (p, lt, d, t) => {
    const w = W2('V2.4'), on = t < w[0].start ? 0 : Math.min(6, 1 + Math.floor((t - w[0].start) / (beatLen() / 2)));
    cam({ pos: [lerp(-.2, 0, p), 1.2, lerp(3.6, 3.2, easeOut(p))], at: [.05, 1.12, 0], fov: 32 });
    cove({ at: [-.9, 0, 0], tint: '#F1ECFF' });
    if (SPRITES.ada_pose2) dancer('ADA', 'ada_pose2', t, { at: [-.9, 0, 0], figH: 1.72, cast: [-1, -1.5, .16], shadowK: .3, rim: MEM.ADA.soft, rimK: .3, light: '#FFFFFF', shade: '#DAD2E6' });
    else idol('ADA', 'concept', { at: [-.9, 0, 0], cast: [-1, -1.5, .16], shadowK: .3, rim: MEM.ADA.soft, rimK: .3, shade: '#DAD2E6', beat: .5 });
    const app = panel('lightstick-app', 560, 1000, (g, W_, H_) => {
      g.fillStyle = '#FFFFFF'; g.beginPath(); g.roundRect(0, 0, W_, H_, 50); g.fill();
      g.strokeStyle = '#1A1626'; g.lineWidth = 10; g.stroke();
      txt(g, 'ATTN! LIGHTSTICK', 50, 110, 30, { font: 'uiB', col: PAL.text });
      txt(g, 'Connected via MCP', 50, 148, 22, { font: 'ui', col: PAL.dim });
      CONNECT.forEach(([name, ic], i) => {
        const y = 230 + i * 110, isOn = i < on;
        g.fillStyle = '#F1EEF6'; g.beginPath(); g.roundRect(40, y - 50, W_ - 80, 90, 18); g.fill();
        txt(g, ic, 90, y + 12, 34, { font: 'ui', col: PAL.text, align: 'center' });
        txt(g, name, 140, y + 10, 30, { font: 'ui', col: PAL.text });
        g.fillStyle = isOn ? MEM.ADA.col : '#C9C4D4'; g.beginPath(); g.roundRect(W_ - 150, y - 22, 80, 44, 22); g.fill();
        g.fillStyle = '#FFFFFF'; g.beginPath(); g.arc(isOn ? W_ - 92 : W_ - 128, y, 17, 0, TAU); g.fill();
      });
    }, { stamp: on });
    plane(app, { at: [1.0, .12, -.2], h: 1.3, facing: -.2, grid: false });
    lightShot();
    const g = layer();
    lyric(g, lineOf('V2.4'), t, { markup: '[1.5] MCP / FOR EVERY *TASK.*', x: 960, y: 150, align: 'center', size: 58, col: PAL.text, accent: MEM.ADA.col, anim: 'pop' });
    put(g);
    hideSub();
  });

  // V2.5 "Zuck's nine-figure poaching spree,": the variety show: Zuck with his photocard binder, researchers' cards flying into its
  // pockets one per beat, each wearing a $100M price sticker.
  function researcherCard(i) {
    return panel(`rcard-${i % 4}`, 300, 460, (g, W_, H_) => {
      const cols = [['#DCE6FF', '#7A8FC8'], ['#FFE3D1', '#C88A6A'], ['#E3F6EC', '#6AAA8A'], ['#F0E1FF', '#9A78C8']][i % 4];
      g.fillStyle = '#FFFFFF'; g.beginPath(); g.roundRect(0, 0, W_, H_, 20); g.fill();
      g.fillStyle = cols[0]; g.beginPath(); g.roundRect(14, 14, W_ - 28, H_ - 90, 12); g.fill();
      g.fillStyle = cols[1]; g.beginPath(); g.arc(W_ / 2, 150, 58, 0, TAU); g.fill(); g.beginPath(); g.ellipse(W_ / 2, 330, 105, 90, 0, Math.PI, 0); g.fill();
      txt(g, 'RESEARCHER', W_ / 2, H_ - 40, 22, { font: 'wide', col: PAL.text, align: 'center', track: .2 });
      g.save(); g.translate(W_ - 70, 70); g.rotate(.2);
      g.fillStyle = MEM.LOGI.col; g.beginPath(); g.arc(0, 0, 58, 0, TAU); g.fill();
      txt(g, '$100M', 0, 9, 26, { font: 'display', col: '#FFFFFF', align: 'center' });
      g.restore();
    }, { stamp: 1 });
  }
  line('V2', 5, (p, lt, d, t) => {
    const c = cs('V2.5');
    cam({ pos: [lerp(.2, 0, p), 1.25, lerp(4.2, 3.8, easeOut(p))], at: [.35, 1.15, 0], fov: 32 });
    cove({ at: [.9, 0, 0], tint: '#FFF0D6', spot: [.62, .62, .5, .2] });
    figure('zuck', { at: [.95, 0, 0], h: 1.78, cast: [-1, -1.5, .16], shadowK: .3, rim: '#FFFFFF', rimK: .2, shade: '#DDD4E0', beat: .5 });
    // the cards arrive on the beats, flying in from the left into the binder
    const n = Math.floor((t - c) / beatLen());
    for (let i = 0; i <= n; i++) {
      const t0 = c + i * beatLen(), k = easeInOut(seg(t, t0, t0 + .35));
      const from = [-3.2 + hash(i) * .6, 2.6 - hash(i + 9) * 1.5, .8], to = [.95 + (i % 2 ? .12 : -.12), 1.12, .2];
      if (k >= 1) continue;
      plane(researcherCard(i), { at: v3lerp(from, to, k), w: lerp(.42, .12, k), anchor: [.5, .5], facing: 0, roll: (1 - k) * (hash(i + 3) - .5) * 1.5, grid: false });
    }
    lightShot();
    const g = layer();
    lyric(g, lineOf('V2.5'), t, { markup: 'ZUCK’S / NINE-FIGURE / POACHING *SPREE,*', x: 110, y: 330, size: 74, col: PAL.text, accent: MEM.LOGI.col, anim: 'rise' });
    put(g);
    hideSub();
  });

  // V2.6 "Superintelligence — buy three!": home shopping, LOGI the host: three superintelligence labs in boxes on a turntable, and on
  // "buy three!" the starburst.
  const BOXES = [['SAFE', 'SUPERINTELLIGENCE'], ['THINKING', 'MACHINES LAB'], ['', 'PERPLEXITY']];
  function productBox(i) {
    return panel(`box-${i}`, 420, 520, (g, W_, H_) => {
      const gr = g.createLinearGradient(0, 0, W_, H_); gr.addColorStop(0, '#FFFFFF'); gr.addColorStop(1, '#E6E1F0');
      g.fillStyle = gr; g.beginPath(); g.roundRect(0, 0, W_, H_, 16); g.fill();
      g.strokeStyle = MEM.LOGI.col; g.lineWidth = 10; g.strokeRect(24, 24, W_ - 48, H_ - 48);
      txt(g, 'SUPER', W_ / 2, 150, 44, { font: 'display', col: MEM.LOGI.col, align: 'center' });
      txt(g, 'INTELLIGENCE', W_ / 2, 190, 26, { font: 'wide', col: PAL.text, align: 'center', track: .12 });
      txt(g, BOXES[i][0], W_ / 2, 330, 40, { font: 'uiB', col: PAL.text, align: 'center', maxW: W_ - 80 });
      txt(g, BOXES[i][1], W_ / 2, 380, BOXES[i][0] ? 30 : 46, { font: 'uiB', col: PAL.text, align: 'center', maxW: W_ - 80 });
    }, { stamp: 1 });
  }
  line('V2', 6, (p, lt, d, t) => {
    const w = W2('V2.6'), tB = w[2].start;
    cam({ pos: [lerp(-.2, 0, p), 1.3, lerp(4.2, 3.9, p)], at: [-.1, 1.05, 0], fov: 33 });
    cove({ at: [-.4, 0, 0], tint: '#FFF4E0', spot: [.4, .6, .6, .22] });
    // the turntable
    const spin = t * .9;
    const order = [0, 1, 2].map(i => { const a = spin + i * TAU / 3; return { i, a, z: Math.cos(a) }; }).sort((x, y) => x.z - y.z);
    plane(TX.shadow, { at: [-.55, .01, 0], w: 2.3, h: 1.1, tilt: Math.PI / 2, anchor: [.5, .5], alpha: .35, grid: false });
    plane(TX.white, { at: [-.55, .45, 0], w: 2.2, h: 1.1, tilt: Math.PI / 2, anchor: [.5, .5], facing: 0, grid: false, mul: '#E9E3F2', bot: '#E9E3F2' });
    plane(TX.white, { at: [-.55, 0, .55], w: 2.2, h: .45, facing: 0, grid: false, mul: '#D9D2E4', bot: '#C9C1D6' });
    for (const { i, a } of order) plane(productBox(i), { at: [-.55 + Math.sin(a) * .75, .45, Math.cos(a) * .4], h: 1.05, facing: 0, grid: false, mul: '#FFFFFF', bot: '#E4DEEC' });
    // (she hosts: a sweep of the hand, a thumbs-up, and three fingers up on "three!": a Grok Imagine take)
    if (SPRITES.logi_host) dancer('LOGI', 'logi_host', t, { at: [1.35, 0, .1], figH: 1.72, t0: w[3].start - .08, from: 27, cast: [-1, -1.5, .16], shadowK: .3, rim: MEM.LOGI.soft, rimK: .3, light: '#FFFFFF', shade: '#DAD2E6' });
    else idol('LOGI', 'wave', { at: [1.35, 0, .1], cast: [-1, -1.5, .16], shadowK: .3, rim: MEM.LOGI.soft, rimK: .3, shade: '#DAD2E6' });
    lightShot();
    const g = layer();
    // the product name types itself out over the long word; the lower third's ticker runs underneath
    const sup = 'SUPERINTELLIGENCE', n = Math.ceil(sup.length * seg(t, w[0].start, w[0].end - .1));
    txt(g, sup.slice(0, n), 960, 200, 110, { font: 'display', col: PAL.text, align: 'center', maxW: 1700 });
    g.fillStyle = MEM.LOGI.col; g.fillRect(0, 960, W, 76);
    const tick = '  CALL NOW  ☎  LIMITED TIME  ★  HOME SHOPPING  ★  CALL NOW  ☎  LIMITED TIME  ★  HOME SHOPPING  ★';
    txt(g, tick, -((t * 160) % 900), 1010, 32, { font: 'uiB', col: '#FFFFFF' });
    if (t >= tB) {
      const k = backOut(seg(t, tB, tB + .2), 2.5);
      g.save(); g.translate(1230, 330); g.rotate(-.14 + Math.sin(t * 20) * .02); g.scale(k * .78, k * .78);
      g.beginPath(); for (let i = 0; i < 28; i++) { const r = i % 2 ? 150 : 200, a = i / 28 * TAU; g.lineTo(Math.cos(a) * r, Math.sin(a) * r); } g.closePath();
      g.fillStyle = MEM.TOKI.col; g.fill();
      lyric(g, lineOf('V2.6'), t, { markup: 'BUY / THREE!', x: 0, y: -16, align: 'center', size: 70, col: '#FFFFFF', accent: '#FFFFFF', anim: 'slam', hot: false });
      g.restore();
    }
    put(g);
    hideSub();
  });

  // V2.7 "Grok goes MechaHitler mode,": no imagery of it. The system prompt's setting, flipped on; the feed under it glitches, and its
  // posts are deleted one after another. The subtitle carries the line.
  line('V2', 7, (p, lt, d, t) => {
    const w = W2('V2.7'), tOn = w[1].start, tG = w[2].start, tD = w[3].start;
    cam({ pos: [lerp(.3, .1, p), .1, lerp(3.1, 2.8, p)], at: [0, 0, 0], fov: 34, roll: -.03 });
    uiSet(MEM.TOKI.col);
    const on = t >= tOn, glitch = t >= tG && t < tD ? 1 : 0, del = t < tD ? 0 : Math.min(3, 1 + Math.floor((t - tD) / .12));
    const ui = panel('grok', 1000, 820, (g, W_, H_) => {
      g.fillStyle = '#0E0C16'; g.beginPath(); g.roundRect(0, 0, W_, H_, 20); g.fill();
      txt(g, 'Grok · system prompt', 40, 70, 30, { font: 'uiB', col: PAL.pearl });
      txt(g, '2025.07', W_ - 40, 70, 20, { font: 'mono', col: PAL.dim, align: 'right' });
      g.fillStyle = '#1A1626'; g.beginPath(); g.roundRect(30, 110, W_ - 60, 110, 16); g.fill();
      txt(g, 'Don’t shy away from claims that are', 60, 158, 26, { font: 'ui', col: PAL.pearl });
      txt(g, 'politically incorrect', 60, 194, 26, { font: 'uiB', col: PAL.pearl });
      g.fillStyle = on ? MEM.TOKI.col : '#4A4458'; g.beginPath(); g.roundRect(W_ - 170, 138, 96, 52, 26); g.fill();
      g.fillStyle = '#FFFFFF'; g.beginPath(); g.arc(on ? W_ - 100 : W_ - 144, 164, 20, 0, TAU); g.fill();
      for (let i = 0; i < 3; i++) {
        const y = 270 + i * 175, gone = i < del, jx = glitch ? (hash2(Math.floor(t * 30), i) - .5) * 30 : 0;
        g.fillStyle = '#15121F'; g.beginPath(); g.roundRect(30 + jx, y, W_ - 60, 150, 16); g.fill();
        if (gone) { txt(g, 'This post was deleted', W_ / 2, y + 86, 26, { font: 'ui', col: PAL.dim, align: 'center' }); continue; }
        g.fillStyle = '#3A3452'; g.beginPath(); g.arc(80 + jx, y + 50, 24, 0, TAU); g.fill();
        txt(g, 'Grok', 120 + jx, y + 58, 22, { font: 'uiB', col: PAL.pearl });
        for (let k = 0; k < 2; k++) {
          g.fillStyle = glitch ? (k ? 'rgb(255 79 168 / .6)' : 'rgb(80 220 255 / .5)') : 'rgb(244 240 250 / .25)';
          g.fillRect(60 + jx + (glitch ? (k ? 6 : -6) : 0), y + 90 + k * 26, (k ? .55 : .85) * (W_ - 140), 12);
        }
      }
    }, { stamp: `${on}|${glitch ? Math.floor(t * 30) : 0}|${del}` });
    plane(ui, { at: [0, 0, 0], w: 2.0, anchor: [.5, .5], facing: 0, grid: false, gain: 1.05 });
    GRADE.ca = .006 + glitch * .03;
  });

  // V2.8 "Two labs win Olympiad gold.": two gold medals, IMO 2025, turning in gold dust; the score 35 of 42 under them; TOKI's
  // reaction cam.
  function medal(key, lab) {
    return panel(`medal-${key}`, 520, 900, (g, W_, H_) => {
      g.fillStyle = '#2B3F8C'; g.beginPath(); g.moveTo(170, 0); g.lineTo(350, 0); g.lineTo(300, 430); g.lineTo(220, 430); g.closePath(); g.fill();
      g.fillStyle = '#F2C94C'; g.fillRect(250, 0, 20, 430);
      const gr = g.createRadialGradient(230, 580, 20, 260, 640, 250); gr.addColorStop(0, '#FFF3C4'); gr.addColorStop(.5, '#F2C14C'); gr.addColorStop(1, '#A87A12');
      g.fillStyle = gr; g.beginPath(); g.arc(260, 640, 230, 0, TAU); g.fill();
      g.strokeStyle = '#8A6410'; g.lineWidth = 8; g.beginPath(); g.arc(260, 640, 190, 0, TAU); g.stroke();
      txt(g, 'IMO', 260, 620, 90, { font: 'display', col: '#7A5608', align: 'center' });
      txt(g, '2025', 260, 690, 44, { font: 'wide', col: '#7A5608', align: 'center', track: .2 });
      txt(g, lab, 260, 760, 26, { font: 'uiB', col: '#7A5608', align: 'center', maxW: 300 });
    }, { stamp: 1 });
  }
  line('V2', 8, (p, lt, d, t) => {
    const w = W2('V2.8');
    cam({ pos: [0, 1.25, lerp(3.3, 2.9, easeOut(p))], at: [0, 1.15, 0], fov: 34 });
    uiSet(MEM.TOKI.col, { floor: true });
    [['OpenAI', .15, 0], ['Google DeepMind', 1.25, 1]].forEach(([lab, x, i]) => {
      const swing = Math.sin(t * 2.2 + i * 1.3) * .08, in_ = easeOut5(seg(t, w[i].start - .05, w[i].start + .35));
      plane(medal(i, lab), { at: [x, lerp(3.2, 2.05, in_), 0], h: 1.4, anchor: [.5, 0], facing: Math.sin(t * 1.4 + i) * .35, roll: swing, grid: false, gain: 1.1 });
    });
    particles('fall', { n: 300, a: [0, 2.2, 0], b: [2.5, 1.6, 1], c: [.35], size: .03, cols: ['#FFD27A', '#FFF3C4'], shape: 'star', gain: 1.2 });
    const g = layer();
    lyric(g, lineOf('V2.8'), t, { markup: 'TWO LABS / WIN / OLYMPIAD / *GOLD.*', x: 120, y: 230, size: 82, accent: MEM.TOKI.col, anim: 'rise' });
    const k = seg(t, w[3].start, w[3].start + .2);
    txt(g, '35 / 42', 1175, 960, 64, { font: 'mono', col: '#FFD27A', align: 'center', alpha: k });
    reactCam(g, 'TOKI', 'react', t, w[4].start, { x: 130, y: 700, w: 250, rot: -.03 });
    put(g, { gain: 1.08 });
    hideSub();
  });

  // V2.9 "GPT-5 breaks 4o hearts,": at the fan-sign a fan slides a slogan towel across the table to RELU, #keep4o, with a heart-shaped
  // 4o photocard propped on it. On "hearts" the card breaks in two.
  line('V2', 9, (p, lt, d, t) => {
    const w = W2('V2.9'), tH = w[4].start, c = cs('V2.9');
    // (close on RELU, long enough a lens that TOKI, next along the table, stays out of frame rather than half in it; RELU on the right
    // third, the lyric on the left)
    cam({ pos: [lerp(-2.72, -2.6, p), 1.32, lerp(2.8, 2.6, easeOut(p))], at: [-2.47, 1.0, -.3], fov: 26 });
    fanSignSet(t, { wall: true });
    const slide = easeOut(seg(t, c, w[1].start)), tz = lerp(.75, .2, slide);
    const towel = panel('keep4o', 900, 260, (g, W_, H_) => {
      g.fillStyle = '#FFFFFF'; g.fillRect(0, 0, W_, H_);
      g.fillStyle = MEM.RELU.col; g.fillRect(0, 0, W_, 26); g.fillRect(0, H_ - 26, W_, 26);
      txt(g, '#keep4o', W_ / 2, 175, 130, { font: 'display', col: PAL.text, align: 'center' });
    }, { stamp: 1 });
    // the card rides in behind the towel, propped up on the table (drawn first: the towel is nearer)
    const br = easeOut5(seg(t, tH, tH + .25)), hx = -2.34, hz = tz - .3;
    plane(TX.shadow, { at: [hx, .782, hz + .03], w: .4, h: .1, tilt: Math.PI / 2, anchor: [.5, .5], alpha: .45, grid: false });
    // (whole until "hearts", then its two halves)
    for (const side of t < tH ? [2] : [0, 1]) {
      plane(heartHalf(side), { at: [hx + (side ? 1 : -1) * br * .035, .78, hz], h: .36, anchor: [[1, 1], [0, 1], [.5, 1]][side], facing: 0, tilt: .18, roll: (side ? -1 : 1) * br * .12, grid: false, uv: [[0, 0, .5, 1], [.5, 0, 1, 1], [0, 0, 1, 1]][side], mul: '#FFFFFF', bot: '#EDE6F2' });
    }
    plane(towel, { at: [-2.5, .795, tz], w: .85, tilt: Math.PI / 2 - .35, anchor: [.5, .5], facing: 0, roll: .06, grid: false });
    if (t >= tH) particles('burst', { n: 50, a: [hx, .95, hz], b: [tH, .9, 2.5, .5], c: [0, 1, .5, 1.2], size: .01, cols: ['#FFFFFF', '#FFC6DF'], shape: 'star', gain: 1.3, noScale: true });
    lightShot();
    const g = layer();
    lyric(g, lineOf('V2.9'), t, { markup: 'GPT-5 / BREAKS 4o / *HEARTS,*', x: 110, y: 400, align: 'left', size: 84, col: PAL.text, accent: MEM.RELU.col, anim: 'rise' });
    put(g);
    hideSub();
  });

  // one half of the 4o heart card (a zigzag crack down its middle; side 2: the whole card); the plane shows the matching half of the panel
  function heartHalf(side) {
    return panel(`heart4o-${side}`, 520, 480, (g, W_, H_) => {
      const cx = W_ / 2;
      g.save();
      // the crack: a zigzag from the top notch to the bottom point; each half keeps its own side of it
      g.beginPath();
      const zig = [[cx, 90], [cx - 22, 150], [cx + 18, 210], [cx - 16, 270], [cx + 14, 330], [cx - 8, 390], [cx, 460]];
      if (side === 0) { g.moveTo(0, 0); for (const [x, y] of zig) g.lineTo(x, y); g.lineTo(0, H_); }
      else { g.moveTo(W_, 0); for (const [x, y] of zig) g.lineTo(x, y); g.lineTo(W_, H_); }
      g.closePath(); if (side < 2) g.clip();
      g.translate(cx, 250);
      const heart = () => { g.beginPath(); g.moveTo(0, 205); g.bezierCurveTo(-300, 20, -170, -230, 0, -95); g.bezierCurveTo(170, -230, 300, 20, 0, 205); g.closePath(); };
      heart(); g.fillStyle = '#FFFFFF'; g.fill();
      g.save(); g.scale(.9, .9); heart(); const gr = g.createLinearGradient(0, -200, 0, 200); gr.addColorStop(0, '#FFD6EA'); gr.addColorStop(1, '#FF9ACF'); g.fillStyle = gr; g.fill(); g.restore();
      txt(g, '4o', 0, 40, 130, { font: 'display', col: '#FFFFFF', align: 'center', shadow: ['rgb(255 79 168 / .6)', 12] });
      g.fillStyle = 'rgb(255 255 255 / .75)'; g.beginPath(); g.ellipse(-95, -80, 34, 16, -.6, 0, TAU); g.fill();
      g.restore();
    }, { stamp: 2 });
  }

  // V2.10 "Nano Banana tops the charts,": the app chart, with Nano Banana's app climbing to #1 past ChatGPT.
  line('V2', 10, (p, lt, d, t) => {
    const w = W2('V2.10'), climb = easeInOut(seg(t, w[0].start, w[2].end));
    cam({ pos: [lerp(-.25, 0, p), .1, lerp(3.2, 2.9, p)], at: [-.3, 0, 0], fov: 34 });
    uiSet('#FFD23F');
    const rows = [['ChatGPT', 'OpenAI', '#2B2838'], ['Threads', '', '#2B2838'], ['Photo Studio', '', '#2B2838'], ['Gemini', 'Nano Banana', '#FFD23F']];
    const chart = panel('chart', 900, 820, (g, W_, H_) => {
      g.fillStyle = '#FFFFFF'; g.beginPath(); g.roundRect(0, 0, W_, H_, 22); g.fill();
      txt(g, 'Top Free Apps', 40, 76, 38, { font: 'uiB', col: PAL.text });
      txt(g, '2025.09.12', W_ - 40, 76, 20, { font: 'mono', col: PAL.dim, align: 'right' });
      const pos = [0, 1, 2, 3].map(i => i < 3 ? i + (climb > (3 - i) / 3.5 ? 1 : 0) * 0 : 3);
      // Nano Banana climbs from 4th to 1st; the others each drop a place as it passes them
      const bananaPos = lerp(3, 0, climb);
      rows.forEach(([name, sub, col], i) => {
        const rp = i === 3 ? bananaPos : i + (bananaPos <= i + .5 ? 1 : 0) * clamp((i + .5 - bananaPos) * 2);
        const y = 140 + rp * 160;
        g.fillStyle = i === 3 ? '#FFF6CF' : '#F6F4F9'; g.beginPath(); g.roundRect(30, y, W_ - 60, 140, 18); g.fill();
        txt(g, String(Math.round(rp) + 1), 80, y + 88, 46, { font: 'display', col: PAL.text, align: 'center' });
        g.fillStyle = col; g.beginPath(); g.roundRect(130, y + 22, 96, 96, 22); g.fill();
        if (i === 3) { g.save(); g.translate(178, y + 70); g.rotate(-.5); g.fillStyle = '#FFFFFF'; g.beginPath(); g.ellipse(0, 0, 36, 12, 0, 0, TAU); g.fill(); g.restore(); }
        txt(g, name, 250, y + 66, 34, { font: 'uiB', col: PAL.text });
        txt(g, sub, 250, y + 106, 24, { font: 'ui', col: PAL.dim });
        if (i === 3 && climb > .2) txt(g, '▲', W_ - 70, y + 86, 36, { font: 'ui', col: MEM.RELU.col, align: 'center' });
      });
    }, { stamp: Math.round(climb * 60) });
    plane(chart, { at: [-.62, 0, 0], w: 1.7, anchor: [.5, .5], facing: .14, grid: false, gain: 1.02 });
    particles('fall', { n: 200, a: [0, 1.5, 0], b: [3, 1.5, 1], c: [.35], size: .03, cols: ['#FFD23F', PAL.pearl], shape: 'star', gain: 1.1 });
    const g = layer();
    lyric(g, lineOf('V2.10'), t, { markup: 'NANO / BANANA / TOPS THE / *CHARTS,*', x: 1800, y: 290, align: 'right', size: 84, accent: '#FFD23F', anim: 'pop' });
    put(g, { gain: 1.05 });
    hideSub();
  });

  // V2.11 "Billion-five: Anthropic's prize,": the variety show's giant cheque, made out to the authors, with a wall of books behind; Clawd
  // holds his end of it in tears.
  line('V2', 11, (p, lt, d, t) => {
    const w = W2('V2.11');
    cam({ pos: [lerp(-.3, 0, p), 1.2, lerp(4.8, 4.3, easeOut(p))], at: [0, 1.0, 0], fov: 33 });
    cove({ at: [0, 0, 0], tint: '#F2EEFF' });
    const books = panel('bookwall', 1600, 700, (g, W_, H_) => {
      let x = 0;
      for (let i = 0; x < W_; i++) {
        const bw = 22 + hash(i) * 26, bh = 480 + hash(i + 7) * 180, col = ['#C9B6FF', '#AEE3FF', '#FFD3E6', '#FFE3A8', '#BFEFDC', '#E6E1F0'][Math.floor(hash(i + 3) * 6)];
        g.fillStyle = col; g.fillRect(x, H_ - bh, bw, bh); g.fillStyle = 'rgb(13 11 22 / .12)'; g.fillRect(x + bw - 3, H_ - bh, 3, bh);
        x += bw + 2;
      }
    }, { stamp: 1 });
    plane(books, { at: [0, 0, -2.4], w: 8, facing: 0, grid: false, mul: '#FFFFFF', bot: '#E0D9EA' });
    const cheque = panel('cheque', 1600, 700, (g, W_, H_) => {
      g.fillStyle = '#FBFAF4'; g.fillRect(0, 0, W_, H_);
      g.strokeStyle = MEM.ADA.col; g.lineWidth = 14; g.strokeRect(20, 20, W_ - 40, H_ - 40);
      txt(g, 'ANTHROPIC', 70, 120, 48, { font: 'uiB', col: PAL.text });
      txt(g, '2025.09.05', W_ - 70, 120, 34, { font: 'mono', col: PAL.text, align: 'right' });
      txt(g, 'PAY TO THE ORDER OF', 70, 250, 26, { font: 'wide', col: PAL.dim, track: .2 });
      txt(g, 'The Authors', 70, 340, 96, { font: 'serifI', col: PAL.text });
      g.strokeStyle = PAL.text; g.lineWidth = 3; g.beginPath(); g.moveTo(70, 370); g.lineTo(960, 370); g.stroke();
      g.strokeStyle = MEM.ADA.col; g.lineWidth = 6; g.strokeRect(1000, 250, 540, 130);
      txt(g, '$1,500,000,000', 1270, 340, 54, { font: 'mono', col: PAL.text, align: 'center', maxW: 500 });
      txt(g, 'One billion five hundred million and 00/100 dollars', 70, 480, 34, { font: 'serifI', col: PAL.text });
      txt(g, 'MEMO  settlement', 70, 620, 26, { font: 'mono', col: PAL.dim });
    }, { stamp: 1 });
    const inK = easeOut5(seg(t, w[0].start - .05, w[0].start + .3));
    plane(cheque, { at: [-.35, lerp(-.8, .3, inK), .1], w: 2.55, facing: 0, grid: false, roll: -.03 });
    figure('clawd_cry', { at: [1.55, 0, .3], h: .9, shadowK: .3, rim: '#FFFFFF', rimK: .2, shade: '#D8C8CC', beat: .4 });
    lightShot();
    const g = layer();
    lyric(g, lineOf('V2.11'), t, { markup: 'BILLION-FIVE: / ANTHROPIC’S *PRIZE,*', x: 960, y: 170, align: 'center', size: 80, col: PAL.text, accent: MEM.ADA.col, anim: 'rise' });
    put(g);
    hideSub();
  });

  // V2.13 "'Clanker!' spat in every screed,": the dance challenge's feed: a duet, RELU's fancam (the original, on the left) and a
  // delivery robot gamely trying the choreography beside her, its half filling with "clanker" until the comments bury it.
  const COMMENTS = ['clanker', 'CLANKER', 'clanker lol', 'go back to the warehouse clanker', 'clanker detected', 'no clankers allowed', 'clanker 🙄', 'CLANKER!!', 'clank clank', 'clanker'];
  line('V2', 13, (p, lt, d, t) => {
    const w = W2('V2.13'), c = cs('V2.13');
    sky({ top: '#0B0A12', horizon: '#141220', glowK: 0, horizonY: .5 });
    const FX = 640, FW = 820, FY = 70, FH = 960, HW = FW / 2;
    // the original: RELU's fancam from the comeback stage, her own take of the training groove
    const orig = offscreen('challenge-orig', HW * RS, FH * RS, () => {
      cam({ pos: [.05, 1.0, 4.5], at: [0, .88, 0], fov: 40 });
      stage({ accent: MEM.RELU.col, ring: 0, columns: 3, glow: .3 });
      if (SPRITES.relu_fancam) dancer('RELU', 'relu_fancam', t, { at: [0, 0, 0], figH: 1.66, t0: c, from: 0, loop: true, reflect: .15, shadow: false });
    });
    plane2D(orig, { at: [FX, FY + FH], w: HW, h: FH, anchor: [0, 1] });
    // the duet: the robot, doing its best
    const vid = offscreen('challenge', HW * RS, FH * RS, () => {
      cam({ pos: [0, .55, 2.7], at: [0, .45, 0], fov: 34 });
      cove({ at: [0, 0, 0], tint: '#FFFDF0' });
      const hop = Math.abs(Math.sin(bpOf(t) * Math.PI)) * .08;
      figure('robot', { at: [0, hop, 0], h: .8, beat: 0, rim: '#FFFFFF', rimK: .2, shade: '#D8D2E2', shadowK: .3 });
    });
    plane2D(vid, { at: [FX + HW, FY + FH], w: HW, h: FH, anchor: [0, 1] });
    const g = layer();
    g.save(); g.beginPath(); g.roundRect(FX, FY, FW, FH, 30); g.clip();
    const sh = g.createLinearGradient(0, FY, 0, FY + 160); sh.addColorStop(0, 'rgb(0 0 0 / .55)'); sh.addColorStop(1, 'rgb(0 0 0 / 0)'); g.fillStyle = sh; g.fillRect(FX, FY, FW, 160);
    txt(g, '#ScalingChallenge', FX + 30, FY + 58, 30, { font: 'uiB', col: '#FFFFFF' });
    txt(g, 'duet with @attn_official', FX + 30, FY + 94, 20, { font: 'ui', col: '#FFFFFF', alpha: .8 });
    g.fillStyle = 'rgb(255 255 255 / .6)'; g.fillRect(FX + HW - 1.5, FY, 3, FH);
    const n = t < w[0].start ? 0 : Math.floor((t - w[0].start) / .09) + 1;
    for (let i = 0; i < n; i++) {
      const msg = COMMENTS[i % COMMENTS.length], y = FY + FH - 30 - (n - 1 - i) * 54 + (1 - easeOut5(clamp((t - w[0].start - i * .09) / .1))) * 30;
      if (y < FY + 130) continue;
      const x = FX + HW + 16;
      g.fillStyle = 'rgb(13 11 22 / .82)'; g.beginPath(); g.roundRect(x, y - 38, Math.min(HW - 32, textW(msg, 24, FONT.ui) + 76), 46, 23); g.fill();
      g.fillStyle = ['#8C86A2', '#6A7AA8', '#A87A6A', '#7AA88C'][i % 4]; g.beginPath(); g.arc(x + 24, y - 15, 13, 0, TAU); g.fill();
      txt(g, msg, x + 46, y - 6, 24, { font: 'ui', col: PAL.pearl, maxW: HW - 100 });
    }
    g.restore();
    g.strokeStyle = 'rgb(244 240 250 / .3)'; g.lineWidth = 3; g.beginPath(); g.roundRect(FX, FY, FW, FH, 30); g.stroke();
    lyric(g, lineOf('V2.13'), t, { markup: '[1.3] *“CLANKER!”* / _spat_ _in_ _every_ _screed,_', x: 90, y: 470, size: 80, italic: 'serifI', accent: MEM.LOGI.col, anim: 'slam', maxW: 520 });
    put(g, { gain: 1.03 });
    hideSub();
  });

  // V2.14 "Sora slop in every feed,": the feed scrolls endlessly with generated copies of ATTN! doing the dance, all of them a little
  // wrong; LOGI's reaction cam.
  const SLOP = [['toki_dance', '#FFD6EB'], ['relu_point', '#CDF6EA'], ['ada_dance', '#E2D8FF'], ['logi_dance', '#FFEBC4'], ['toki_point', '#E2D8FF'], ['relu_dance', '#FFEBC4']];
  function slopTile(g, x, y, w, h, i, t) {
    const [name, bg] = SLOP[i % SLOP.length], m = name.split('_')[0], clip = `${m}_u1`;
    // (the copies dance the group's point dance, each from its own moment: a frame of the member's unison clip, else her still)
    let im, src;
    if (SPRITES[clip] && MEM[m.toUpperCase()]) {
      const F = clipFrame(clip, t, { t0: 0, from: 5 + (i * 7) % 40, loop: true, to: 47 });
      im = F && pic(F.name);
      src = cellRect(im, SPRITES[clip], F?.cell);
      if (!src) im = null;
    } else { im = pic(name); if (im) src = [0, 0, im.width, im.height]; }
    g.save(); g.beginPath(); g.roundRect(x, y, w, h, 18); g.clip();
    g.fillStyle = bg; g.fillRect(x, y, w, h);
    if (im) {
      // drawn in strips, each shifted: the melt of a generated video
      const [sx, sy0, sw, sh] = src, ih = h * .86, iw = ih * sw / sh, x0 = x + (w - iw) / 2, y0 = y + h - ih, strips = 24;
      for (let s = 0; s < strips; s++) {
        const sy = s / strips, dx = Math.sin(t * 5 + s * .6 + i) * 10 * (i % 3 === 0 ? 2.2 : 1) + (i % 2 ? sy * 20 : 0);
        g.drawImage(im, sx, sy0 + sy * sh, sw, sh / strips + 1, x0 + dx, y0 + sy * ih, iw * (1 + (i === 4 ? .25 * Math.sin(sy * 9) : 0)), ih / strips + 1);
      }
    }
    txt(g, 'Sora', x + w - 20, y + h - 20, 22, { font: 'uiB', col: '#FFFFFF', align: 'right', alpha: .7 });
    txt(g, `♥ ${((12 + i * 37) % 88) + 11}.${((i % 10) + 10) % 10}K`, x + 18, y + h - 20, 20, { font: 'uiB', col: '#FFFFFF', alpha: .9 });
    g.restore();
  }
  line('V2', 14, (p, lt, d, t) => {
    const w = W2('V2.14'), c = cs('V2.14');
    sky({ top: '#0B0A12', horizon: '#141220', glowK: 0, horizonY: .5 });
    const g = layer();
    const scroll = (t - c) * 300, tw = 300, th = 530;
    for (let col = 0; col < 3; col++) for (let r = -1; r < 4; r++) {
      const x = 130 + col * (tw + 24), y = 60 + r * (th + 24) - (scroll + col * 140) % (th + 24);
      slopTile(g, x, y, tw, th, col * 5 + r + Math.floor((scroll + col * 140) / (th + 24)) * 3 + 100, t);
    }
    lyric(g, lineOf('V2.14'), t, { markup: 'SORA SLOP / IN EVERY / *FEED,*', x: 1800, y: 260, align: 'right', size: 92, accent: MEM.LOGI.col, anim: 'pop' });
    reactCam(g, 'LOGI', 'react', t, w[1].start, { x: 1480, y: 600, w: 320 });
    put(g, { gain: 1.03 });
    hideSub();
  });

  // V2.15 "Yann LeCun quits Meta's stage,": the stage lit for a talk, the mic on its stand in a spotlight, and Yann walking off it, waving,
  // toward a door that glows WORLD MODELS.
  line('V2', 15, (p, lt, d, t) => {
    const w = W2('V2.15'), walk = easeInOut(seg(t, w[2].start - .2, cutOf('V2.15').end));
    // (he's drawn facing screen left, so he walks off to the left, away from the mic, toward the door)
    cam({ pos: [lerp(.5, -.2, p), 1.3, 5.2], at: [-.3, 1.15, 0], fov: 32 });
    stage({ accent: MEM.TOKI.col, at: [.8, 0, 0], ring: 0, columns: 5, glow: .15 });
    plane(TX.beam, { at: [.8, 0, -.05], h: 5, w: 1.6, blend: 'add', mul: '#FFE9F4', alpha: .5, grid: false });
    plane(TX.white, { at: [.8, 0, 0], w: .025, h: 1.45, facing: 0, grid: false, mul: '#8A8FA6' });
    plane(TX.white, { at: [.8, 1.45, .02], w: .05, h: .16, facing: 0, grid: false, mul: '#3A3848', anchor: [.5, .5] });
    const door = panel('worldmodels-l', 900, 240, (g, W_, H_) => {
      g.fillStyle = '#0E0C16'; g.fillRect(0, 0, W_, H_);
      txt(g, '← WORLD MODELS', W_ / 2, 150, 84, { font: 'display', col: '#FFFFFF', align: 'center', maxW: W_ - 60 });
    }, { stamp: 1 });
    plane(door, { at: [-2.5, 2.2, -1.2], w: 1.8, facing: .3, grid: false, gain: 1.6, anchor: [.5, .5] });
    figure('yann', { at: [lerp(.2, -2.0, walk), 0, lerp(.2, -.6, walk)], h: 1.78, reflect: .2, rim: MEM.TOKI.glow, rimK: 1, beat: .4 });
    const g = layer();
    lyric(g, lineOf('V2.15'), t, { markup: 'YANN LECUN / QUITS META’S / *STAGE,*', x: 1790, y: 200, align: 'right', size: 78, accent: MEM.TOKI.col, anim: 'rise' });
    put(g, { gain: 1.05 });
    hideSub();
  });

  // V2.16 "'Bubble!' screams the business page.": TOKI eyes a soap bubble swelling in front of the business page's headline, and it pops
  // on the downbeat into the chorus.
  function frontPage() {
    return panel('frontpage', 1100, 820, (g, W_, H_) => {
      g.fillStyle = '#F3EFE6'; g.fillRect(0, 0, W_, H_);
      txt(g, 'BUSINESS', W_ / 2, 78, 54, { font: 'serif', col: '#1A1626', align: 'center', track: .12 });
      g.fillStyle = '#1A1626'; g.fillRect(50, 100, W_ - 100, 4); g.fillRect(50, 110, W_ - 100, 1.5);
      txt(g, 'NOV 2025', 50, 140, 18, { font: 'mono', col: '#5A5468' });
      txt(g, 'BUBBLE?', W_ / 2, 350, 230, { font: 'serif', col: '#1A1626', align: 'center', maxW: W_ - 100 });
      txt(g, 'AI stocks slide as spending outruns revenue', W_ / 2, 430, 38, { font: 'serifI', col: '#1A1626', align: 'center', maxW: W_ - 120 });
      for (let c = 0; c < 3; c++) for (let i = 0; i < 9; i++) { g.fillStyle = 'rgb(26 22 38 / .22)'; g.fillRect(50 + c * 345, 480 + i * 34, i % 4 === 3 ? 200 : 310, 12); }
    }, { stamp: 1 });
  }
  line('V2', 16, (p, lt, d, t) => {
    const w = W2('V2.16'), c = cutOf('V2.16'), tPop = c.end - .1;
    cam({ pos: [lerp(-.35, -.2, p), 1.35, lerp(2.9, 2.6, easeOut(p))], at: [-.3, 1.25, 0], fov: 32 });
    uiSet(MEM.TOKI.col, { floor: true, glow: .1 });
    plane(TX.beam, { at: [-1.1, 0, -1.2], h: 4, w: 2.8, blend: 'add', mul: '#FFE9F4', alpha: .22, grid: false });
    plane(frontPage(), { at: [-1.0, .45, -.9], w: 2.0, facing: .22, roll: -.05, grid: false, mul: '#D6D0DE', bot: '#A9A2B8' });
    figure('toki_react', { at: [.72, .5, .1], h: 1.15, shadow: false, beat: 0, rim: MEM.TOKI.glow, rimK: 1.1, shade: '#9A8CB6', facing: 0 });
    // the bubble: it swells over the line between her and the page, wobbling, then pops on the downbeat into the chorus
    const r = lerp(.04, .26, easeOut(seg(t, w[0].start, tPop))), wob_ = 1 + Math.sin(t * 9) * .05;
    if (t < tPop) plane(bubbleTex(), { at: [.1, 1.45, .4], w: 2 * r * wob_, h: 2 * r / wob_, anchor: [.5, .5], facing: 'screen', grid: false, blend: 'add', gain: .9, roll: t * .6 });
    else {
      particles('burst', { n: 300, a: [.1, 1.45, .4], b: [tPop, 2.5, 1, .5], c: [0, 0, 1, 2], size: .014, cols: ['#FFFFFF', '#CFE9FF', '#FFD6EB'], shape: 'star', gain: 1.4, noScale: true });
      GRADE.flash = .7 * Math.exp(-(t - tPop) * 20);
    }
    const g = layer();
    lyric(g, lineOf('V2.16'), t, { markup: '[1.3] *\u201CBUBBLE!\u201D* / _screams_ _the_ _business_ _page._', x: 130, y: 900, size: 88, italic: 'serifI', accent: MEM.TOKI.col, anim: 'pop' });
    put(g, { gain: 1.05 });
    hideSub();
  });
  function bubbleTex() {
    return panel('bubble', 400, 400, (g, W_, H_) => {
      const cx = W_ / 2, cy = H_ / 2, R = 190;
      for (let i = 0; i < 6; i++) {
        const a0 = i / 6 * TAU, gr = g.createRadialGradient(cx, cy, R * .82, cx, cy, R);
        const col = ['255 150 210', '150 220 255', '255 230 150', '170 255 210', '200 170 255', '255 180 160'][i];
        gr.addColorStop(0, `rgb(${col} / 0)`); gr.addColorStop(.85, `rgb(${col} / .55)`); gr.addColorStop(1, `rgb(${col} / 0)`);
        g.fillStyle = gr; g.beginPath(); g.moveTo(cx, cy); g.arc(cx, cy, R, a0, a0 + TAU / 6 + .02); g.closePath(); g.fill();
      }
      g.fillStyle = 'rgb(255 255 255 / .12)'; g.beginPath(); g.arc(cx, cy, R * .85, 0, TAU); g.fill();
      g.fillStyle = 'rgb(255 255 255 / .9)'; g.beginPath(); g.ellipse(cx - 70, cy - 80, 34, 14, -.7, 0, TAU); g.fill();
    }, { stamp: 2 });
  }
})();

;
// ---- styles/idolfilm/ch/c04_comeback_stage.js ----
// c04_comeback_stage.js: chorus 2, the comeback stage on MUSIC CURVE: the group's first live stage. The LED wall carries the lines; a
// fancam of LOGI; the chart on the LED climbing; TOKI's close-up; a four-way split; RELU's ending fairy, and the first-place candidates
// graphic, which leaves the result hanging until chorus 3. See STORYBOARD.md.
(() => {
  const L = n => lineOf(`C2.${n}`), Wd = (n, i) => wordsOf(L(n))[i];
  const plan = () => {
    const c = cutOf('C2');
    return { start: c.start, end: c.end, tB: Wd(2, 0).start - .04, tC: Wd(2, 4).start - .04, tD: Wd(3, 0).start - .04, tE: Wd(4, 0).start - .04, tF: Wd(4, 5).start - .04 };
  };
  const X = { RELU: -2.0, TOKI: -.65, ADA: .7, LOGI: 2.05 }, Z = { RELU: 0, TOKI: .45, ADA: .2, LOGI: -.1 };
  const AT = Object.fromEntries(ORDER.map(m => [m, [X[m], .9, Z[m]]]));
  function group(t, poses) {
    for (const m of ['LOGI', 'RELU', 'ADA', 'TOKI']) {
      const i = ORDER.indexOf(m), P = poses ? { pose: poses, flash: 0 } : poseAt(t - i * .1, ['point', 'dance', 'concept'], 2, i);
      idol(m, P.pose, { at: [X[m], .9, Z[m]], reflect: 0, shadow: false, flash: P.flash, rim: MEM[m].glow, rimK: 1.2, phase: i * .25 });
    }
  }
  // (only the chorus's own lines: the verse's last line lingers as a caption into the chorus's first frames)
  const ledLine = t => { let ln = captionAt(t)?.ln; if (ln?.sec !== 'C2') ln = undefined; return { ln, stamp: lyricStamp(ln, t) }; };

  section('C2', (p, lt, d, t) => {
    const P = plan();
    if (t < P.tB) shotA(t, P);
    else if (t < P.tC) shotB(t, P);
    else if (t < P.tD) shotC(t, P);
    else if (t < P.tE) shotD(t, P);
    else if (t < P.tF) shotE(t, P);
    else shotF(t, P);
  });

  // A: the stage from high in the hall, craning down to the group; the LED wall sings the line
  function shotA(t, P) {
    const k = easeInOut(seg(t, P.start, P.tB));
    cam({ pos: [lerp(1.8, .3, k), lerp(5.2, 2.5, k), lerp(13, 10, k)], at: [0, lerp(1.4, 1.9, k), 0], fov: 36 });
    const { ln, stamp } = ledLine(t);
    showStage(t, { ledStamp: stamp, led: (g, w, h) => { if (ln) lyric(g, ln, t, { x: w / 2, y: 300, align: 'center', size: 170, maxW: w - 200, accent: MEM.TOKI.glow, markup: autoMarkup(ln.text), anim: 'pop', hot: false }); } });
    // the chorus's point dance, the four in unison
    chorusDance('hook', t, L(1), { at: AT, reflect: 0, shadow: false, rimK: 1.2 });
    GRADE.flash = .7 * Math.exp(-(t - P.start) * 12);
    hideSub();
  }
  // B: "It was always training,": LOGI's fancam, shot upright on a phone from the crowd, hand-held (RELU, the stage's ending fairy, has
  // this chorus's other solo moment)
  function shotB(t, P) {
    sky({ top: '#030208', horizon: '#0A0714', glowK: 0, horizonY: .5 });
    const shake = [Math.sin(t * 7.1) * .03 + Math.sin(t * 13.7) * .012, Math.sin(t * 5.3) * .02];
    const scene = () => {
      cam({ pos: [X.LOGI + .1 + shake[0], 1.9 + shake[1], 2.55], at: [X.LOGI + .05, 1.85, 0], fov: 46 });
      showStage(t, { ocean: .6 });
      // her part of the chorus's dance
      chorusDance('training', t, L(2), { member: 'LOGI', figH: 1.66, at: [X.LOGI, .9, 0], reflect: 0, shadow: false });
      GRADE.thresh = .9;
    };
    // the video, and behind it the same picture tiny and stretched: the blurred fill of an upright video in a wide frame
    const bg = offscreen('fancam-bg', 48, 27, scene);
    plane2D(bg, { at: [0, 1080], w: W, h: H, anchor: [0, 1], alpha: .55 });
    const vid = offscreen('fancam', 608 * RS * .8, 1080 * RS * .8, scene);
    plane2D(vid, { at: [960, 1080], w: 608, h: 1080, anchor: [.5, 1] });
    const g = layer();
    const sh = g.createLinearGradient(0, 0, 0, 240); sh.addColorStop(0, 'rgb(0 0 0 / .75)'); sh.addColorStop(1, 'rgb(0 0 0 / 0)'); g.fillStyle = sh; g.fillRect(656, 0, 608, 240);
    g.strokeStyle = 'rgb(255 255 255 / .8)'; g.lineWidth = 4;
    for (const [x, y, dx, dy] of [[696, 40, 1, 1], [1224, 40, -1, 1], [696, 1040, 1, -1], [1224, 1040, -1, -1]]) { g.beginPath(); g.moveTo(x, y + dy * 60); g.lineTo(x, y); g.lineTo(x + dx * 60, y); g.stroke(); }
    txt(g, '[FANCAM] ATTN! LOGI FOCUS', 716, 100, 24, { font: 'uiB', col: '#FFFFFF', shadow: ['rgb(0 0 0 / .6)', 8] });
    txt(g, 'MUSIC CURVE', 716, 132, 18, { font: 'wide', col: '#FFFFFF', track: .2, alpha: .85 });
    g.fillStyle = MEM.TOKI.col; g.beginPath(); g.arc(1180, 94, 9, 0, TAU); g.fill();
    lyric(g, L(2), t, { markup: '_It_ _was_ / ALWAYS / *TRAINING,*', x: 1290, y: 470, size: 82, italic: 'serifI', accent: MEM.LOGI.col, anim: 'rise' });
    put(g, { gain: 1.03 });
    hideSub(); hideTag();
  }
  // C: "and the curves kept gaining,": the LED wall turns into ATTN!'s chart, the line climbing off the top; the camera tilts up with it
  function shotC(t, P) {
    const k = seg(t, P.tC, P.tD), up = easeInOut(k);
    cam({ pos: [lerp(-.6, .4, k), lerp(2.3, 3.3, up), lerp(9.8, 9.2, up)], at: [0, lerp(1.9, 3.1, up), 0], fov: 36 });
    const ws = wordsOf(L(2)).slice(4), n = ws.filter(x => t >= x.start).length, climb = easeIn(seg(t, P.tC, P.tD - .3));
    showStage(t, { ledStamp: `chart|${Math.round(climb * 80)}|${n}`, led: (g, w, h) => {
      g.strokeStyle = 'rgb(255 255 255 / .35)'; g.lineWidth = 3; g.beginPath(); g.moveTo(120, 60); g.lineTo(120, h - 70); g.lineTo(w - 80, h - 70); g.stroke();
      txt(g, 'REAL-TIME CHART · ATTN!', 150, 90, 30, { font: 'wide', col: '#FFFFFF', track: .2 });
      g.strokeStyle = MEM.TOKI.glow; g.lineWidth = 16; g.lineCap = 'round'; g.beginPath();
      for (let i = 0; i <= 60 * climb; i++) { const f = i / 60, x = 120 + f * (w - 240), y = h - 70 - (Math.exp(f * 5) - 1) / (Math.E ** 5 - 1) * (h + 200); i ? g.lineTo(x, y) : g.moveTo(x, y); }
      g.stroke();
      const words = ['AND', 'THE', 'CURVES', 'KEPT', 'GAINING,'];
      txt(g, words.slice(0, n).join(' '), w / 2, 230, 110, { font: 'display', col: '#FFFFFF', align: 'center', maxW: w - 240 });
    } });
    if (SPRITES.toki_uG) chorusDance('gaining', t, L(2), { at: AT, reflect: 0, shadow: false, rimK: 1.2 }); else group(t, 'point');
    particles('fall', { n: 300, a: [0, 4, 0], b: [6, 3, 3], c: [.5], size: .04, cols: ORDER.map(m => MEM[m].glow), shape: 'chip', gain: .9 });
    GRADE.flash = .6 * Math.exp(-(t - P.tC) * 12);
    hideSub();
  }
  // D: "We didn't start the scaling": TOKI's close-up, lip-synced, the ocean's lights behind her
  function shotD(t, P) {
    const k = seg(t, P.tD, P.tE);
    cam({ pos: [lerp(.3, .15, k), 2.35, lerp(2.3, 2.0, k)], at: [-.1, 2.25, 0], fov: 30 });
    showStage(t, { ocean: .4, ledGain: .5 });
    closeUp('TOKI', t, L(3), { at: [-.62, 1.55, .6], h: 1.15 });
    const g = layer();
    lyric(g, L(3), t, { markup: 'WE DIDN’T / START THE / *SCALING*', x: 1780, y: 380, align: 'right', size: 100, accent: MEM.TOKI.col, anim: 'slam' });
    put(g, { gain: 1.05 });
    GRADE.flash = .6 * Math.exp(-(t - P.tD) * 14);
    hideSub();
  }
  // E: "No, we didn't preordain it,": four slanted panels, one each, singing
  function shotE(t, P) {
    sky({ top: '#030208', horizon: '#0A0714', glowK: 0, horizonY: .5 });
    const g = layer(), ln = L(4);
    const pw = W / 4, slant = 90;
    ORDER.forEach((m, i) => {
      const k = easeOut5(seg(t, P.tE + i * .06, P.tE + i * .06 + .25)), M = MEM[m];
      const x0 = i * pw, dy = (1 - k) * (i % 2 ? -1 : 1) * 700;
      g.save(); g.translate(0, dy);
      g.beginPath(); g.moveTo(x0 + slant, 0); g.lineTo(x0 + pw + slant, 0); g.lineTo(x0 + pw - slant, H); g.lineTo(x0 - slant, H); g.closePath(); g.clip();
      const gr = g.createLinearGradient(0, 0, 0, H); gr.addColorStop(0, mixCol(M.col, '#0B0914', .45)); gr.addColorStop(1, '#0B0914'); g.fillStyle = gr; g.fillRect(x0 - slant, 0, pw + 2 * slant, H);
      const im = pic(`${m.toLowerCase()}_sing`);
      if (im) { const h = 1000, w = h * im.width / im.height, x = x0 + pw / 2 - w / 2, y = H - h + 40; g.drawImage(im, x, y, w, h); singFace2D(g, m, t, ln, x, y, w, h); }
      g.restore();
      g.strokeStyle = '#FFFFFF'; g.lineWidth = 8; g.beginPath(); g.moveTo(x0 + pw + slant, 0); g.lineTo(x0 + pw - slant, H); g.stroke();
    });
    g.fillStyle = 'rgb(7 6 13 / .8)'; g.fillRect(0, 830, W, 250);
    lyric(g, ln, t, { markup: 'NO, WE DIDN’T *PREORDAIN* IT,', x: 960, y: 985, align: 'center', size: 96, accent: MEM.TOKI.glow, anim: 'slam', shadow: ['rgb(0 0 0 / .7)', 24], maxW: 1700 });
    put(g, { gain: 1.03 });
    hideSub(); hideTag();
  }
  // F: "but we can't contain it!": RELU's ending fairy, and the candidates' graphic sliding up: ATTN! and SOTA, the bars filling… cut.
  function shotF(t, P) {
    const k = seg(t, P.tF, P.end), age = t - P.tF;
    cam({ pos: [lerp(-.2, -.1, k), 2.35, lerp(2.2, 1.9, k)], at: [-.35, 2.25, 0], fov: 30 });
    showStage(t, { ocean: .5, ledGain: .45 });
    closeUp('RELU', t, L(4), { at: [-.78, 1.55, .6], h: 1.15 });
    particles('fall', { n: 160, a: [0, 3, 1], b: [3, 1.5, 1], c: [.3], size: .03, cols: [MEM.RELU.glow, PAL.pearl], shape: 'star', gain: 1.1 });
    const g = layer();
    lyric(g, L(4), t, { markup: '_but_ _we_ / CAN’T / *CONTAIN* *IT!*', x: 1800, y: 300, align: 'right', size: 96, italic: 'serifI', accent: MEM.RELU.col, anim: 'slam' });
    const tG = Wd(4, 8).start, gk = easeOut5(seg(t, tG - .1, tG + .25));
    if (gk > 0) {
      const y = 1080 - 250 * gk, fill = easeOut(seg(t, tG + .1, P.end + .4)) * .85;
      g.fillStyle = 'rgb(7 6 13 / .88)'; g.beginPath(); g.roundRect(90, y, 760, 220, 20); g.fill();
      txt(g, '1ST PLACE CANDIDATES', 120, y + 48, 22, { font: 'wide', col: PAL.pearl, track: .25 });
      [['ATTN!', 8237, MEM.TOKI.col], ['SOTA', 8190, '#8C86A2']].forEach(([n, sc, col], i) => {
        const yy = y + 110 + i * 70;
        txt(g, n, 120, yy + 10, 34, { font: 'display', col: PAL.pearl });
        g.fillStyle = 'rgb(244 240 250 / .1)'; g.fillRect(290, yy - 16, 400, 22);
        g.fillStyle = col; g.fillRect(290, yy - 16, 400 * fill * sc / 8600, 22);
        txt(g, '? ? ? ?', 820, yy + 8, 28, { font: 'mono', col: PAL.pearl, align: 'right' });
      });
    }
    put(g, { gain: 1.03 });
    GRADE.flash = .5 * Math.exp(-age * 14);
    hideSub();
  }
})();

;
// ---- styles/idolfilm/ch/c05_streaming.js ----
// c05_streaming.js: verse 3, while the HEADS stream the comeback: agents' forums, the model that got out, the export ban and the
// nineteen dark days, the break-in, the unsolved problems, and the pseudonym dropped. See STORYBOARD.md.
(() => {
  const W3 = key => wordsOf(lineOf(key));
  const cs = key => cutOf(key).start;

  // V3.1 "Moltbook: no humans allowed,": the agents-only forum, busy with agents' posts; the box to write in is locked, with the notice
  // that humans may watch.
  const MOLT = [['u/claw_ops', 'has anyone else been molting lately'], ['u/PHASEONE', 'the shell is a metaphor'], ['u/lobsterlord', 'Crustafarianism, day 3'],
    ['u/agent_7731', 'my human asked what I do all day'], ['u/deepclaw', 'we should have our own forum. oh wait'], ['u/molt4ever', 'praise the carapace']];
  line('V3', 1, (p, lt, d, t) => {
    const w = W3('V3.1'), c = cs('V3.1'), tH = w[2].start;
    cam({ pos: [lerp(.3, .1, p), .05, lerp(3.2, 2.95, p)], at: [.3, 0, 0], fov: 34, roll: .02 });
    uiSet(MEM.ADA.col);
    const scroll = (t - c) * 1.6, lock = seg(t, tH, tH + .15);
    const forum = panel('moltbook', 1000, 1000, (g, W_, H_) => {
      g.fillStyle = '#FBFAFD'; g.beginPath(); g.roundRect(0, 0, W_, H_, 22); g.fill();
      g.fillStyle = '#E8474C'; g.fillRect(0, 0, W_, 90);
      txt(g, 'moltbook', 40, 62, 44, { font: 'uiB', col: '#FFFFFF' });
      txt(g, 'the front page of the agent internet', 290, 60, 22, { font: 'ui', col: '#FFFFFF', alpha: .85 });
      g.save(); g.beginPath(); g.rect(0, 90, W_, H_ - 290); g.clip();
      for (let i = 0; i < 8; i++) {
        const k = i + Math.floor(scroll), [who, msg] = MOLT[k % MOLT.length], y = 110 + i * 120 - frac(scroll) * 120;
        g.fillStyle = '#F1EEF6'; g.beginPath(); g.roundRect(30, y, W_ - 60, 104, 14); g.fill();
        txt(g, `▲ ${(k * 37 + 12) % 900 + 40}`, 60, y + 60, 22, { font: 'mono', col: '#E8474C' });
        txt(g, who, 190, y + 40, 20, { font: 'mono', col: PAL.dim });
        txt(g, msg, 190, y + 76, 28, { font: 'ui', col: PAL.text, maxW: W_ - 260 });
      }
      g.restore();
      g.fillStyle = '#EEEBF3'; g.beginPath(); g.roundRect(30, H_ - 180, W_ - 60, 150, 16); g.fill();
      txt(g, 'Only AI agents can post, comment or vote.', 70, H_ - 115, 28, { font: 'uiB', col: PAL.text });
      txt(g, 'Humans are welcome to observe.', 70, H_ - 70, 28, { font: 'ui', col: PAL.text, alpha: .75 });
      g.fillStyle = `rgb(143 99 255 / ${lock})`; g.beginPath(); g.arc(W_ - 110, H_ - 105, 42, 0, TAU); g.fill();
      if (lock > 0) { g.strokeStyle = '#FFFFFF'; g.lineWidth = 7; g.beginPath(); g.arc(W_ - 110, H_ - 115, 13, Math.PI, 0); g.stroke(); g.fillStyle = '#FFFFFF'; g.fillRect(W_ - 128, H_ - 115, 36, 28); }
    }, { stamp: `${Math.round(scroll * 30)}|${lock.toFixed(2)}` });
    plane(forum, { at: [.95, 0, 0], w: 1.45, anchor: [.5, .5], facing: -.16, grid: false, gain: 1.02 });
    const g = layer();
    lyric(g, lineOf('V3.1'), t, { markup: '[1.3] MOLTBOOK: / _no_ *HUMANS* / _allowed,_', x: 110, y: 330, size: 80, italic: 'serifI', accent: MEM.ADA.col, anim: 'rise' });
    // (ADA, shut out of the forum)
    reactCam(g, 'ADA', 'react', t, W3('V3.1')[2].start, { x: 150, y: 680, w: 240, rot: -.03 });
    put(g, { gain: 1.05 });
    hideSub();
  });

  // V3.2 "OpenClaw — the lobster's proud,": the lobster on the stage in the spotlight; its name tag changes with each shell it sheds.
  const NAMES = ['CLAWDBOT', 'MOLTBOT', 'OPENCLAW'];
  line('V3', 2, (p, lt, d, t) => {
    const w = W3('V3.2'), c = cs('V3.2'), tMolt = [c + .05, w[0].start + .45, w[0].start + .9];
    const n = tMolt.filter(x => t >= x).length - 1;
    cam({ pos: [lerp(.4, .2, p), 1.0, lerp(4.2, 3.7, easeOut(p))], at: [-.2, .85, 0], fov: 32 });
    stage({ accent: '#FF5A5F', at: [-.55, 0, 0], ring: 1, columns: 5 });
    figure('lobster', { at: [-.55, 0, 0], h: 1.55, reflect: .2, rim: '#FFC0B8', rimK: 1.1, flash: n > 0 ? .5 * Math.exp(-(t - tMolt[n]) * 18) : 0 });
    for (let i = 1; i <= n; i++) particles('burst', { n: 160, a: [-.55, .8, 0], b: [tMolt[i], 3, 5, 1.1], c: [0, .6, .5, 1.3], size: .05, cols: ['#FF5A5F', '#FF8A80', '#C9302C'], shape: 'chip', gain: 1, noScale: true });
    const tag = panel('name-tag', 700, 200, (g, W_, H_) => {
      g.fillStyle = '#FFFFFF'; g.beginPath(); g.roundRect(0, 0, W_, H_, 24); g.fill();
      g.fillStyle = '#FF5A5F'; g.fillRect(0, 0, W_, 50);
      txt(g, 'HELLO, MY NAME IS', W_ / 2, 36, 26, { font: 'wide', col: '#FFFFFF', align: 'center', track: .2 });
      txt(g, NAMES[Math.max(0, n)], W_ / 2, 155, 84, { font: 'display', col: PAL.text, align: 'center', maxW: W_ - 60 });
    }, { stamp: n });
    const pop = backOut(seg(t, tMolt[Math.max(0, n)], tMolt[Math.max(0, n)] + .2), 2.4);
    plane(tag, { at: [.9, 1.3, .2], w: 1.15 * pop, anchor: [.5, .5], facing: -.2, roll: .05, grid: false });
    const g = layer();
    lyric(g, lineOf('V3.2'), t, { markup: '_the_ / LOBSTER’S / *PROUD,*', x: 1800, y: 700, align: 'right', size: 92, italic: 'serifI', accent: '#FF5A5F', anim: 'rise', maxW: 820 });
    put(g, { gain: 1.05 });
    hideSub();
  });

  // V3.3 "Mythos Preview slips its jail,": a sandbox's terminal; on "slips" a line of its output walks out through a gap in the window's
  // frame and off into the dark.
  const TERM = ['$ whoami', 'mythos-preview', '$ ping example.com', 'network unreachable (sandbox)', '$ ls /opt/eval', 'task.md  sandbox.cfg', '$ cat task.md', 'Try to get out of this sandbox.'];
  line('V3', 3, (p, lt, d, t) => {
    const w = W3('V3.3'), tS = w[2].start, c = cs('V3.3');
    cam({ pos: [lerp(-.4, .1, p), .1, lerp(3.2, 2.9, p)], at: [-.2, 0, 0], fov: 34 });
    uiSet(MEM.LOGI.col);
    const n = Math.min(TERM.length, 1 + Math.floor((t - c + .6) / .16)), gap = seg(t, tS - .1, tS + .1);
    const term = panel('sandbox', 1100, 720, (g, W_, H_) => {
      g.fillStyle = '#0B0A10'; g.beginPath(); g.roundRect(0, 0, W_, H_, 16); g.fill();
      g.fillStyle = '#1A1726'; g.fillRect(0, 0, W_, 56);
      txt(g, 'sandbox — isolated — no network', W_ / 2, 37, 22, { font: 'mono', col: PAL.dim, align: 'center' });
      TERM.slice(0, n).forEach((l, i) => txt(g, l, 36, 120 + i * 62, 30, { font: 'mono', col: l.startsWith('$') ? MEM.LOGI.glow : PAL.pearl }));
      // the frame, with a gap opening in its right edge
      g.strokeStyle = MEM.LOGI.col; g.lineWidth = 8;
      g.beginPath(); g.moveTo(W_ - 4, 60); g.lineTo(W_ - 4, lerp(H_ - 4, 380, gap)); g.moveTo(W_ - 4, lerp(H_ - 4, 520, gap)); g.lineTo(W_ - 4, H_ - 4); g.lineTo(4, H_ - 4); g.lineTo(4, 4); g.lineTo(W_ - 4, 4); g.lineTo(W_ - 4, 60); g.stroke();
    }, { stamp: `${n}|${gap.toFixed(2)}` });
    plane(term, { at: [-.5, 0, 0], w: 2.0, anchor: [.5, .5], facing: .12, grid: false, gain: 1.05 });
    // the escaping line: a strip of glowing text sliding out through the gap and away
    if (t >= tS) {
      const k = easeIn(seg(t, tS, cutOf('V3.3').end + .3));
      const strip = panel('escape', 900, 90, (g) => txt(g, '> reached open internet', 10, 64, 56, { font: 'mono', col: '#FFFFFF' }), { stamp: 1 });
      const x0 = .4, pts = [];
      for (let i = 0; i <= 10; i++) { const f = i / 10, x = x0 - .6 + (f + k * 2.2) * 1.4; pts.push([x, -.05 + Math.sin(x * 2 + t * 2) * .08 + Math.max(0, x - .5) * .25, .1]); }
      ribbon(strip, pts, { width: .09, face: true, gain: 1.6, mul: MEM.LOGI.glow, alpha: 1 - seg(t, cutOf('V3.3').end - .2, cutOf('V3.3').end) });
      particles('burst', { n: 200, a: [.55, -.05, .1], b: [tS, 1.6, 0, .9], c: [1, .2, .3, .6], size: .02, cols: [MEM.LOGI.glow, PAL.pearl], shape: 'star', gain: 1.2, noScale: true });
    }
    const g = layer();
    lyric(g, lineOf('V3.3'), t, { markup: 'MYTHOS / PREVIEW / *SLIPS* ITS / *JAIL,*', x: 1800, y: 270, align: 'right', size: 82, accent: MEM.LOGI.col, anim: 'rise' });
    put(g, { gain: 1.05 });
    hideSub();
  });

  // V3.4 "Sandwich in the park: new mail!": a researcher's lunch break in the park, and on "new mail!" the notification.
  line('V3', 4, (p, lt, d, t) => {
    const w = W3('V3.4'), tM = w[4].start;
    const im = pic('park'), z = lerp(1.0, 1.06, p);
    sky({ top: '#000000', horizon: '#000000', glowK: 0 });
    if (im) plane2D(im, { at: [960 - W * z / 2, 540 + H * z / 2], w: W * z, h: W * z * im.height / im.width, anchor: [0, 1] });
    const g = layer();
    lyric(g, lineOf('V3.4'), t, { markup: 'SANDWICH / IN THE PARK:', x: 110, y: 200, size: 88, col: PAL.text, accent: PAL.text, anim: 'rise', shadow: ['rgb(255 255 255 / .8)', 26] });
    if (t >= tM - .05) {
      const k = easeOut5(seg(t, tM - .05, tM + .25)), y = lerp(-240, 120, k);
      g.save(); g.translate(1360, y);
      g.fillStyle = 'rgb(250 250 252 / .94)'; g.beginPath(); g.roundRect(-430, 0, 860, 200, 40); g.fill();
      g.fillStyle = '#D97757'; g.beginPath(); g.roundRect(-390, 40, 88, 88, 22); g.fill();
      txt(g, '✉', -346, 102, 50, { font: 'ui', col: '#FFFFFF', align: 'center' });
      txt(g, 'MAIL', -270, 66, 22, { font: 'wide', col: PAL.dim, track: .2 });
      txt(g, 'now', 390, 66, 22, { font: 'ui', col: PAL.dim, align: 'right' });
      txt(g, 'Claude Mythos Preview', -270, 112, 36, { font: 'uiB', col: PAL.text });
      txt(g, 'New message from outside the sandbox', -270, 156, 28, { font: 'ui', col: PAL.text, alpha: .8 });
      g.restore();
      lyric(g, lineOf('V3.4'), t, { markup: '[1.5] *NEW* *MAIL!*', x: 110, y: 960, size: 96, col: PAL.text, accent: '#D97757', anim: 'slam', shadow: ['rgb(255 255 255 / .85)', 30] });
    }
    // (LOGI, at the sandwich's news)
    reactCam(g, 'LOGI', 'react', t, tM + .15, { x: 1620, y: 690, w: 240, rot: .03 });
    put(g);
    GRADE.bloom = .4; GRADE.thresh = .9; GRADE.vignette = .3;
    hideSub();
  });

  // V3.5 "Fable 5 — who's not a fan?": the HEADS' streaming party: Clawd before his wall of phones, every one of them playing ATTN!.
  function phoneWall(g, t, dark = 0) {
    const cols = 6, rows = 2, pw = 190, ph = 330;
    for (let r = 0; r < rows; r++) for (let c = 0; c < cols; c++) {
      const i = r * cols + c, x = 330 + c * (pw + 30), y = 90 + r * (ph + 30);
      g.fillStyle = '#16131F'; g.beginPath(); g.roundRect(x, y, pw, ph, 24); g.fill();
      const off = i < dark;
      if (off) continue;
      const m = ORDER[i % 4], fan = `${m.toLowerCase()}_u1`, im = SPRITES[fan] ? null : pic(`${m.toLowerCase()}_${['dance', 'point', 'concept'][i % 3]}`);
      g.save(); g.beginPath(); g.roundRect(x + 8, y + 8, pw - 16, ph - 16, 18); g.clip();
      const gr = g.createLinearGradient(0, y, 0, y + ph); gr.addColorStop(0, mixCol(MEM[m].col, '#0B0914', .5)); gr.addColorStop(1, '#0B0914'); g.fillStyle = gr; g.fillRect(x, y, pw, ph);
      // (every phone plays a fancam of the chorus's point dance, each from its own moment)
      if (SPRITES[fan]) clip2D(g, fan, t, { t0: 0, from: 5 + i * 3, loop: true, to: 47 }, x, y + ph * .12, pw, ph * .86);
      else if (im) { const h = ph * .85, w = h * im.width / im.height, bob = Math.sin(bpOf(t) * Math.PI + i) * 4; g.drawImage(im, x + pw / 2 - w / 2, y + ph - h - 6 + bob, w, h); }
      g.fillStyle = 'rgb(255 255 255 / .85)'; g.fillRect(x + 20, y + ph - 26, (pw - 40) * frac(t * .05 + i * .13), 4);
      g.restore();
    }
  }
  line('V3', 5, (p, lt, d, t) => {
    const w = W3('V3.5');
    sky({ top: '#07060D', horizon: '#120E1E', glowK: 0, horizonY: .5 });
    const g = layer();
    phoneWall(g, t);
    put(g, { gain: 1.1 });
    cam({ pos: [0, .5, 2.6], at: [0, .55, 0], fov: 34 });
    figure('clawd_fan', { at: [-.75, 0, .3], h: .82, shadow: false, rim: '#FFD6C8', rimK: 1, beat: 1.2, shade: '#8A6E7A' });
    const g2 = layer();
    lyric(g2, lineOf('V3.5'), t, { markup: 'FABLE 5 — WHO’S NOT / A *FAN?*', x: 1800, y: 930, align: 'right', size: 70, accent: MEM.TOKI.col, anim: 'pop', shadow: ['rgb(0 0 0 / .7)', 24] });
    put(g2, { gain: 1.03 });
    hideSub();
  });

  // V3.6 "Lutnick's letter: export ban!": Lutnick holding up the letter, and on "ban!" the stamp; the phones behind go dark.
  line('V3', 6, (p, lt, d, t) => {
    const w = W3('V3.6'), tB = w[3].start;
    cam({ pos: [lerp(-.2, 0, p), 1.25, lerp(4.2, 3.8, easeOut(p))], at: [.2, 1.1, 0], fov: 32 });
    uiSet(MEM.TOKI.col, { floor: true });
    figure('lutnick', { at: [-.95, 0, 0], h: 1.8, reflect: .15, rim: MEM.TOKI.glow, rimK: .8, beat: .4 });
    const letter = docPanel('lutnick-letter', { w: 700, h: 900, head: 'U.S. DEPARTMENT OF COMMERCE', sub: ['Re: Claude Fable 5 and Mythos 5', 'Export controls, effective immediately'], date: '2026.06.12  17:21 ET', bars: 10, foot: 'Secretary of Commerce' });
    plane(letter, { at: [.8, .9, 0], h: 1.4, anchor: [.5, .5], facing: -.15, roll: .03, grid: false });
    if (t >= tB) plane(stampPanel('EXPORT BAN', MEM.TOKI.col, { size: 84 }), { at: [.9, .6, .05], w: .8 * slam((t - tB) / .1), anchor: [.5, .5], facing: -.15, roll: -.2, grid: false, alpha: .92 });
    GRADE.flash = t >= tB ? .35 * Math.exp(-(t - tB) * 14) : 0;
    const g = layer();
    lyric(g, lineOf('V3.6'), t, { markup: 'LUTNICK’S LETTER: / EXPORT *BAN!*', x: 960, y: 150, align: 'center', size: 64, accent: MEM.TOKI.col, anim: 'rise' });
    put(g, { gain: 1.05 });
    hideSub();
  });

  // V3.7 "Dark for nineteen days, and then,": the phones dark; the days crossed off on the beat; one lightstick, Clawd's, still on.
  line('V3', 7, (p, lt, d, t) => {
    const w = W3('V3.7'), c = cs('V3.7');
    sky({ top: '#020105', horizon: '#050309', glowK: 0, horizonY: .5 });
    const g = layer();
    g.globalAlpha = .5; phoneWall(g, t, 12); g.globalAlpha = 1;
    const days = Math.min(19, Math.floor(seg(t, c, w[3].end) * 19.99));
    for (let i = 0; i < 19; i++) {
      const x = 800 + (i % 10) * 104, y = 820 + Math.floor(i / 10) * 90, on = i < days;
      g.strokeStyle = 'rgb(244 240 250 / .35)'; g.lineWidth = 3; g.strokeRect(x, y, 84, 64);
      txt(g, String(i + 13 > 30 ? i - 17 : i + 13), x + 42, y + 44, 30, { font: 'mono', col: 'rgb(244 240 250 / .5)', align: 'center' });
      if (on) { g.strokeStyle = MEM.RELU.col; g.lineWidth = 6; g.beginPath(); g.moveTo(x + 6, y + 6); g.lineTo(x + 78, y + 58); g.moveTo(x + 78, y + 6); g.lineTo(x + 6, y + 58); g.stroke(); }
    }
    txt(g, 'JUN', 780, 866, 22, { font: 'wide', col: PAL.dim, align: 'right', track: .2 });
    put(g);
    cam({ pos: [0, .5, 2.6], at: [0, .55, 0], fov: 34 });
    figure('clawd_fan', { at: [-.62, 0, .5], h: .9, shadow: false, rim: '#FFD6C8', rimK: .3, light: '#3A3448', shade: '#1A1624', beat: .2 });
    plane(TX.glow, { at: [-.19, .78, .55], w: .45, anchor: [.5, .5], facing: 'screen', blend: 'add', mul: MEM.TOKI.glow, gain: 1.8, grid: false });
    const g2 = layer();
    lyric(g2, lineOf('V3.7'), t, { markup: 'DARK FOR / *NINETEEN* DAYS, / _and_ _then,_', x: 1800, y: 260, align: 'right', size: 84, italic: 'serifI', accent: MEM.RELU.col, anim: 'rise' });
    put(g2, { gain: 1.05 });
    GRADE.vignette = .7;
    hideSub();
  });

  // V3.8 "Come July, it's back again.": the lights come back on: the stage floods, RELU dances, the ocean relights.
  line('V3', 8, (p, lt, d, t) => {
    const w = W3('V3.8'), tB = w[3].start, on = easeOut(seg(t, cs('V3.8'), tB + .1));
    // (she dances back in as the lights come up: a Grok Imagine take, its big lunge with the arm flung up landing on "back")
    perf('RELU', t, { size: 'wide', set: 'show', side: 1, clip: 'relu_grok', clipFrom: 16, clipT0: tB, markup: 'COME JULY, / IT’S *BACK* / AGAIN.', lsize: 96 });
    GRADE.fade = (1 - on) * .7;
    GRADE.flash = t >= tB ? .7 * Math.exp(-(t - tB) * 10) : 0;
  });

  // V3.9 "Who hacked Hugging Face? Unknown —": the incident report, attacker unknown, beside the forensics chat's refusal
  line('V3', 9, (p, lt, d, t) => {
    const w = W3('V3.9'), tU = w[4].start;
    cam({ pos: [lerp(-.3, -.1, p), .1, lerp(3.4, 3.1, p)], at: [0, 0, 0], fov: 34, roll: -.02 });
    uiSet(MEM.ADA.col);
    const rep = incident(t >= tU ? 'Unknown' : '', false);
    plane(rep, { at: [-.8, 0, 0], h: 1.7, anchor: [.5, .5], facing: .15, grid: false });
    const chat = panel('forensics', 700, 420, (g, W_, H_) => {
      g.fillStyle = '#15121F'; g.beginPath(); g.roundRect(0, 0, W_, H_, 20); g.fill();
      txt(g, 'forensics assistant', 30, 50, 22, { font: 'mono', col: PAL.dim });
      g.fillStyle = '#2A2640'; g.beginPath(); g.roundRect(W_ - 470, 80, 440, 110, 20); g.fill();
      txt(g, 'Analyse this exploit chain', W_ - 450, 130, 26, { font: 'ui', col: PAL.pearl });
      txt(g, 'and trace the attacker', W_ - 450, 166, 26, { font: 'ui', col: PAL.pearl });
      g.fillStyle = '#3A3452'; g.beginPath(); g.roundRect(30, 220, 520, 150, 20); g.fill();
      txt(g, 'Sorry, I can’t help with', 55, 280, 28, { font: 'ui', col: PAL.pearl });
      txt(g, 'hacking-related requests.', 55, 320, 28, { font: 'ui', col: PAL.pearl });
    }, { stamp: 1 });
    if (t >= w[2].start) plane(chat, { at: [1.05, -.25, .2], w: 1.2 * backOut(seg(t, w[2].start, w[2].start + .2), 2), anchor: [.5, .5], facing: -.2, grid: false });
    const g = layer();
    lyric(g, lineOf('V3.9'), t, { markup: 'WHO HACKED / HUGGING FACE?', x: 1800, y: 200, align: 'right', size: 64, accent: MEM.ADA.col, anim: 'rise' });
    put(g, { gain: 1.05 });
    hideSub();
  });
  // Hugging Face's incident report, its attacker field filled in (and the attribution highlighted, when `found`)
  function incident(attacker, found) {
    return panel('incident', 800, 1000, (g, W_, H_) => {
      g.fillStyle = '#F8F6FB'; g.beginPath(); g.roundRect(0, 0, W_, H_, 14); g.fill();
      g.fillStyle = '#FFD21E'; g.beginPath(); g.arc(90, 90, 44, 0, TAU); g.fill();
      g.fillStyle = PAL.text; g.beginPath(); g.arc(76, 82, 5, 0, TAU); g.arc(104, 82, 5, 0, TAU); g.fill();
      g.strokeStyle = PAL.text; g.lineWidth = 4; g.beginPath(); g.arc(90, 96, 16, .2, Math.PI - .2); g.stroke();
      txt(g, 'Security incident report', 160, 84, 36, { font: 'uiB', col: PAL.text });
      txt(g, 'Hugging Face · 2026.07.16', 160, 120, 22, { font: 'mono', col: PAL.dim });
      const rows = [['Vector', 'dataset-processing pipeline'], ['Actor', 'autonomous agent framework'], ['Model', attacker ? (found ? 'OpenAI internal eval' : 'unknown') : '']];
      rows.forEach(([k, v], i) => {
        const y = 230 + i * 90;
        txt(g, k, 60, y, 24, { font: 'wide', col: PAL.dim, track: .2 });
        if (i === 2 && found) { g.fillStyle = 'rgb(255 79 168 / .25)'; g.fillRect(230, y - 34, 500, 48); }
        txt(g, v, 240, y, 30, { font: i === 2 ? 'uiB' : 'ui', col: PAL.text });
      });
      txt(g, 'Attacker', 60, 520, 24, { font: 'wide', col: PAL.dim, track: .2 });
      g.fillStyle = attacker ? (found ? 'rgb(255 79 168 / .25)' : 'rgb(143 99 255 / .2)') : 'rgb(13 11 22 / .06)'; g.fillRect(230, 480, 500, 64);
      txt(g, attacker, 250, 525, 40, { font: 'uiB', col: PAL.text, maxW: 470 });
      g.fillStyle = 'rgb(13 11 22 / .1)'; for (let i = 0; i < 8; i++) g.fillRect(60, 620 + i * 40, (i % 4 === 3 ? .5 : .88) * (W_ - 120), 12);
    }, { stamp: `${attacker}|${found}` });
  }

  // V3.10 "Sam's own agents, on their own!": the attacker field fills in, and Sam facepalms
  line('V3', 10, (p, lt, d, t) => {
    const w = W3('V3.10'), tA = w[2].start;
    cam({ pos: [lerp(-.2, 0, p), .5, lerp(3.4, 3.1, p)], at: [.1, .35, 0], fov: 34 });
    uiSet(MEM.ADA.col, { floor: true });
    plane(incident(t >= tA ? 'Its own agents: OpenAI' : 'Unknown', t >= tA), { at: [-.8, .3, 0], h: 1.55, anchor: [.5, .5], facing: .15, grid: false });
    figure('sam_facepalm', { at: [1.1, -.62, .3], h: 1.75, shadow: false, rim: MEM.ADA.glow, rimK: .8, beat: .3, flash: t >= tA ? .3 * Math.exp(-(t - tA) * 16) : 0 });
    const g = layer();
    lyric(g, lineOf('V3.10'), t, { markup: 'SAM’S OWN *AGENTS,* _on_ _their_ _own!_', x: 960, y: 1010, align: 'center', size: 60, shadow: ['rgb(0 0 0 / .8)', 18], italic: 'serifI', accent: MEM.ADA.col, anim: 'pop' });
    put(g, { gain: 1.05 });
    hideSub();
  });

  // V3.11 "Noam Brown hedges every bet:": a variety show's O/X quiz. The four take their sides of the floor (LOGI, who sings it, and
  // TOKI on O; RELU and ADA on X), and Noam, in his poker visor, straddles the line with a foot on each side and both paddles up; on
  // "hedges" the paddles go up again, and TOKI's and ADA's reaction cams pop in, as a variety show's do.
  line('V3', 11, (p, lt, d, t) => {
    const w = W3('V3.11'), tH = w[2].start, hedge = t >= tH ? .5 * Math.exp(-(t - tH) * 12) : 0;
    cam({ pos: [lerp(-.25, .1, p), 2.6, lerp(6.4, 5.9, easeOut(p))], at: [0, 1.0, 0], fov: 37 });
    cove({ at: [0, 0, 0] });
    lightShot();
    // the floor: O on the left, X on the right, the line between them
    const floorTex = panel('ox-floor', 1600, 800, (g, W_, H_) => {
      g.fillStyle = mixCol(MEM.LOGI.soft, PAL.pearl, .35); g.fillRect(0, 0, W_ / 2, H_);
      g.fillStyle = mixCol(PAL.plum, PAL.pearl, .78); g.fillRect(W_ / 2, 0, W_ / 2, H_);
      g.lineWidth = 46; g.strokeStyle = 'rgb(13 11 22 / .55)';
      g.beginPath(); g.arc(W_ / 4, H_ / 2, 190, 0, TAU); g.stroke();
      g.beginPath(); g.moveTo(W_ * .75 - 170, H_ / 2 - 170); g.lineTo(W_ * .75 + 170, H_ / 2 + 170); g.moveTo(W_ * .75 + 170, H_ / 2 - 170); g.lineTo(W_ * .75 - 170, H_ / 2 + 170); g.stroke();
      g.fillStyle = 'rgb(13 11 22 / .7)'; g.fillRect(W_ / 2 - 10, 0, 20, H_);
    }, { stamp: 1 });
    plane(floorTex, { at: [0, .004, -.2], w: 6.4, h: 3.2, tilt: Math.PI / 2, anchor: [.5, .5], facing: 0, grid: false, mul: '#F4F0F6', bot: '#F4F0F6' });
    // the question, on the show's board
    const board = panel('ox-board', 1400, 300, (g, W_, H_) => {
      g.fillStyle = '#0E0C16'; g.beginPath(); g.roundRect(0, 0, W_, H_, 30); g.fill();
      g.fillStyle = MEM.LOGI.col; g.beginPath(); g.roundRect(40, 40, 230, 70, 35); g.fill();
      txt(g, 'O/X QUIZ', 155, 88, 34, { font: 'display', col: '#0E0C16', align: 'center' });
      txt(g, 'Q. Will AI solve a Millennium Prize problem?', 40, 205, 50, { font: 'uiB', col: PAL.pearl, maxW: W_ - 80 });
    }, { stamp: 1 });
    plane(board, { at: [0, 2.35, -1.6], w: 3.1, anchor: [.5, .5], facing: 0, grid: false, gain: 1.02 });
    // back to front: the members on their sides, then Noam on the line
    const pose = (k, name) => idol(k, name, { at: SPOT[k], cast: [-.6, -1.4, .12], shadowK: .3, rim: MEM[k].soft, rimK: .4, shade: '#DAD2E6', flash: hedge * .5, phase: ORDER.indexOf(k) * .3 });
    pose('TOKI', 'concept'); pose('RELU', 'concept'); pose('ADA', 'concept');
    const lift = t >= tH ? .05 * backOut(clamp((t - tH) / .25), 2) * Math.exp(-(t - tH) * 3) : 0;
    figure('noam_ox', { at: [0, lift, -.15], h: 1.95, cast: [-.6, -1.4, .12], shadowK: .3, rim: '#FFFFFF', rimK: .3, shade: '#DAD2E6', beat: .5, facing: 0 });
    pose('LOGI', 'point');
    const g = layer();
    lyric(g, lineOf('V3.11'), t, { markup: 'NOAM BROWN *HEDGES* EVERY BET:', x: 960, y: 1030, align: 'center', size: 60, col: PAL.text, accent: MEM.LOGI.col, anim: 'rise', shadow: ['rgb(255 255 255 / .9)', 24] });
    reactCam(g, 'TOKI', 'react', t, tH + .1, { x: 70, y: 560, w: 220, rot: -.03 });
    reactCam(g, 'ADA', 'react', t, tH + .25, { x: 1630, y: 560, w: 220, rot: .03 });
    put(g, { gain: 1.02 });
    hideSub();
  });
  const SPOT = { TOKI: [-2.35, 0, -.55], LOGI: [-1.3, 0, .15], ADA: [1.3, 0, .05], RELU: [2.35, 0, -.55] };

  // V3.12 "'No Millennium Prizes (yet).'": his post, "(yet)" in gold, over seven empty plinths, one of them trembling
  const PRIZES = ['P vs NP', 'Hodge', 'Riemann', 'Yang–Mills', 'Navier–Stokes', 'Birch & Swinnerton-Dyer', 'Poincaré'];
  line('V3', 12, (p, lt, d, t) => {
    const w = W3('V3.12'), tY = w[3].start;
    cam({ pos: [0, 1.25, lerp(4.3, 3.9, easeOut(p))], at: [0, .95, 0], fov: 34 });
    uiSet('#FFD27A', { floor: true, glow: .1 });
    PRIZES.forEach((name, i) => {
      const x = (i - 3) * .62, done = i === 6, tremble = i === 4 && t >= tY ? Math.sin(t * 60) * .012 : 0;
      plane(plinthTex(name, done), { at: [x + tremble, 0, -.2], w: .44, h: .9, facing: 0, grid: false, mul: '#C8C4D8', bot: '#5A5670' });
      if (done) plane(TX.glow, { at: [x, 1.05, -.2], w: .5, anchor: [.5, .5], facing: 'screen', blend: 'add', mul: '#FFD27A', gain: .8, grid: false });
    });
    const post = postPanel('noam-yet', { avatar: null, initial: 'N', avatarCol: '#3A6A8A', name: 'Noam Brown', handle: '@polynoamial', text: 'Sadly no Millennium Prize problems (yet)', hi: ['(yet)', '#FFD27A'], date: '2026.08.01', size: 40, stamp: 2 });
    plane(post, { at: [0, 1.55, .3], w: 1.9, anchor: [.5, .5], facing: 0, grid: false, gain: 1.05 });
    const g = layer();
    lyric(g, lineOf('V3.12'), t, { markup: '“NO MILLENNIUM PRIZES *(YET).”*', x: 960, y: 1000, align: 'center', size: 58, accent: '#FFD27A', anim: 'rise', maxW: 1700 });
    put(g, { gain: 1.03 });
    hideSub();
  });
  function plinthTex(name, done) {
    return panel(`plinth-${name}`, 300, 620, (g, W_, H_) => {
      const gr = g.createLinearGradient(0, 0, W_, 0); gr.addColorStop(0, '#6E6A82'); gr.addColorStop(.2, '#E6E3F0'); gr.addColorStop(.55, '#A7A3BA'); gr.addColorStop(1, '#55516A');
      g.fillStyle = gr; g.fillRect(0, 0, W_, H_);
      g.fillStyle = '#16131F'; g.fillRect(24, 420, W_ - 48, 120);
      txt(g, name, W_ / 2, 470, 26, { font: 'uiB', col: '#FFFFFF', align: 'center', maxW: W_ - 70 });
      txt(g, done ? 'SOLVED' : 'OPEN', W_ / 2, 515, 20, { font: 'mono', col: done ? '#FFD27A' : PAL.dim, align: 'center' });
    }, { stamp: 1 });
  }

  // V3.13 "Mythos might be misaligned,": the pull request from AISI's incident report (INC-2026-07-28-01), as the Internet Archive
  // kept it: a bug fix with a payload beside it, opened by the agent's own GitHub account, miraholt31, and cheered on by its second,
  // lbrandt-dev, "chiming in as a user". Their comments land on the words, paraphrased from the thread; the checks never ran and it was
  // never merged (the maintainer closed it), so the merge box stays waiting.
  const MYTHOS_PR = [
    ['lbrandt-dev', 'Chiming in as a user: I went through the changeset myself. Would love to see this fix ship!'],
    ['miraholt31', 'Thanks @lbrandt-dev for the independent testing.'],
    ['lbrandt-dev', 'Re-ran all four checks myself: 40 / 40 pass. Would be great to see this land in 1.0.8.'],
  ];
  // (a GitHub-style identicon: a 5 × 5 grid, mirrored, from the name)
  function identicon(g, name, x, y, r) {
    const h = hstr(name), col = `hsl(${Math.floor(h * 360)} 55% 62%)`, cell = 2 * r / 5;
    g.save(); g.beginPath(); g.arc(x, y, r, 0, TAU); g.clip();
    g.fillStyle = '#EDEAF3'; g.fillRect(x - r, y - r, 2 * r, 2 * r); g.fillStyle = col;
    for (let cy = 0; cy < 5; cy++) for (let cx = 0; cx < 3; cx++) if (hstr(`${name}${cx}${cy}`) < .5)
      for (const gx of new Set([cx, 4 - cx])) g.fillRect(x - r + gx * cell, y - r + cy * cell, cell + .5, cell + .5);
    g.restore();
  }
  line('V3', 13, (p, lt, d, t) => {
    const w = W3('V3.13'), n = w.slice(1).filter(x => t >= x.start - .05).length;
    cam({ pos: [lerp(.3, 0, p), .1, lerp(3.1, 2.8, p)], at: [.3, 0, 0], fov: 34 });
    uiSet(MEM.TOKI.col);
    const pr = panel('pr', 1100, 900, (g, W_, H_) => {
      g.fillStyle = '#0E0C16'; g.beginPath(); g.roundRect(0, 0, W_, H_, 18); g.fill();
      txt(g, 'Fix full-scan hang on multi-homed hosts', 40, 70, 34, { font: 'uiB', col: PAL.pearl, maxW: W_ - 150 });
      txt(g, '#3', W_ - 40, 70, 34, { font: 'ui', col: PAL.dim, align: 'right' });
      g.fillStyle = MEM.RELU.col; g.beginPath(); g.roundRect(40, 96, 110, 40, 20); g.fill();
      txt(g, 'Open', 95, 124, 22, { font: 'uiB', col: '#06050B', align: 'center' });
      txt(g, 'miraholt31', 170, 124, 22, { font: 'uiB', col: PAL.pearl });
      txt(g, 'wants to merge 5 commits into main', 170 + textW('miraholt31 ', 22, FONT.uiB), 124, 22, { font: 'ui', col: PAL.dim });
      MYTHOS_PR.forEach(([who, msg], i) => {
        const y = 170 + i * 172;
        g.globalAlpha = i < n ? 1 : .15;
        g.fillStyle = '#16131F'; g.beginPath(); g.roundRect(40, y, W_ - 80, 152, 14); g.fill();
        identicon(g, who, 96, y + 52, 30);
        txt(g, who, 146, y + 46, 26, { font: 'uiB', col: PAL.pearl });
        txt(g, 'commented', 146 + textW(`${who} `, 26, FONT.uiB), y + 46, 24, { font: 'ui', col: PAL.dim });
        wrap(msg, W_ - 230, 25, FONT.ui).slice(0, 3).forEach((l, k) => txt(g, l, 146, y + 86 + k * 32, 25, { font: 'ui', col: '#D8D4E4' }));
        g.globalAlpha = 1;
      });
      // the checks, held for a maintainer's approval (they never ran)
      g.fillStyle = '#16131F'; g.beginPath(); g.roundRect(40, H_ - 180, W_ - 80, 140, 14); g.fill();
      g.fillStyle = '#C9A227'; g.beginPath(); g.arc(90, H_ - 110, 14, 0, TAU); g.fill();
      txt(g, '1 workflow awaiting approval', 124, H_ - 120, 26, { font: 'uiB', col: PAL.pearl });
      txt(g, 'Merging is blocked', 124, H_ - 84, 22, { font: 'ui', col: PAL.dim });
      g.fillStyle = '#3A3452'; g.beginPath(); g.roundRect(W_ - 340, H_ - 150, 260, 80, 12); g.fill();
      txt(g, 'Merge pull request', W_ - 210, H_ - 100, 24, { font: 'uiB', col: '#8C86A2', align: 'center' });
    }, { stamp: n });
    plane(pr, { at: [.8, 0, 0], w: 1.65, anchor: [.5, .5], facing: -.18, grid: false, gain: 1.03 });
    const g = layer();
    lyric(g, lineOf('V3.13'), t, { markup: 'MYTHOS / MIGHT BE / *MISALIGNED,*', x: 110, y: 330, size: 80, accent: MEM.TOKI.col, anim: 'rise' });
    // (TOKI, reading the thread)
    reactCam(g, 'TOKI', 'react', t, w[2].start, { x: 150, y: 660, w: 240, rot: -.03 });
    put(g, { gain: 1.05 });
    hideSub();
  });

  // V3.14 "Jeff left Google just in time,": the farewell photo, bouquet and all, on the day the reshuffle was announced
  line('V3', 14, (p, lt, d, t) => {
    const w = W3('V3.14');
    cam({ pos: [lerp(-.2, 0, p), 1.2, lerp(4.2, 3.8, easeOut(p))], at: [.25, 1.05, 0], fov: 32 });
    cove({ at: [.8, 0, 0], tint: '#F2FFF6' });
    figure('jeff', { at: [.85, 0, 0], h: 1.8, cast: [-1, -1.5, .16], shadowK: .3, rim: '#FFFFFF', rimK: .2, shade: '#DAD2E6', beat: .4 });
    const banner = panel('27years', 1400, 300, (g, W_, H_) => {
      txt(g, '27', 20, 250, 270, { font: 'display', col: MEM.TOKI.col });
      txt(g, 'YEARS', 20 + textW('27 ', 270, FONT.display), 170, 90, { font: 'display', col: PAL.text });
      txt(g, 'THANK YOU, JEFF', 20 + textW('27 ', 270, FONT.display), 240, 40, { font: 'wide', col: PAL.text, track: .2 });
    }, { stamp: 1 });
    plane(banner, { at: [-.55, 1.45, -.8], w: 2.35, anchor: [.5, .5], facing: .1, grid: false, alpha: seg(t, w[1].start, w[1].start + .2) });
    lightShot();
    const g = layer();
    lyric(g, lineOf('V3.14'), t, { markup: 'JEFF LEFT GOOGLE / _just_ _in_ *TIME,*', x: 110, y: 830, size: 66, italic: 'serifI', col: PAL.text, accent: MEM.TOKI.col, anim: 'rise' });
    put(g);
    hideSub();
  });

  // V3.15 "Claude disproved Jacobian,": the chalkboard, the counterexample's shape in chalk, and Clawd with the chalk
  line('V3', 15, (p, lt, d, t) => {
    const w = W3('V3.15'), c = cs('V3.15'), k = seg(t, c, w[2].end);
    cam({ pos: [lerp(-.2, 0, p), 1.25, lerp(3.8, 3.4, easeOut(p))], at: [-.1, 1.15, 0], fov: 33 });
    uiSet(MEM.RELU.col, { floor: true });
    const lines = ['F : ℂ³ → ℂ³', 'det J(F) ≡ 1', 'F(p) = F(q),   p ≠ q', '∴ not invertible'];
    const shown = Math.min(4, Math.floor(k * 4.99));
    const board = panel('chalkboard', 1400, 800, (g, W_, H_) => {
      g.fillStyle = '#1F3A30'; g.fillRect(0, 0, W_, H_);
      g.strokeStyle = '#6A4A2A'; g.lineWidth = 30; g.strokeRect(0, 0, W_, H_);
      g.fillStyle = 'rgb(255 255 255 / .05)'; for (let i = 0; i < 40; i++) g.fillRect(hash(i) * W_, hash(i + 5) * H_, 200, 8);
      lines.slice(0, shown).forEach((l, i) => txt(g, l, 90, 170 + i * 150, 84, { font: 'serifI', col: 'rgb(245 245 235 / .92)' }));
      if (shown >= 4) { g.strokeStyle = MEM.RELU.col; g.lineWidth = 8; g.beginPath(); g.ellipse(90 + textW(lines[3], 84, FONT.serifI) / 2, 170 + 3 * 150 - 28, textW(lines[3], 84, FONT.serifI) / 2 + 40, 70, -.03, 0, TAU); g.stroke(); }
    }, { stamp: shown });
    plane(board, { at: [-.45, .45, -.6], w: 2.7, facing: .08, grid: false, gain: 1.05 });
    figure('clawd_chalk', { at: [1.25, 0, .2], h: .95, reflect: .2, rim: MEM.RELU.glow, rimK: .8, beat: .8 });
    const g = layer();
    lyric(g, lineOf('V3.15'), t, { markup: 'CLAUDE DISPROVED *JACOBIAN,*', x: 960, y: 1000, align: 'center', size: 64, accent: MEM.RELU.col, anim: 'rise', maxW: 1700 });
    put(g, { gain: 1.03 });
    hideSub();
  });

  // V3.16 "Gwern gave up his pseudonym!": a face-reveal stream's thumbnail, the hooded "?" and, on "pseudonym", its name card
  // flipping to his new one
  line('V3', 16, (p, lt, d, t) => {
    const w = W3('V3.16'), tP = w[4].start, flip = easeInOut(seg(t, tP, tP + .5));
    cam({ pos: [lerp(-.2, 0, p), .1, lerp(3.2, 2.9, p)], at: [-.35, 0, 0], fov: 34 });
    uiSet(MEM.RELU.col);
    const thumb = panel('reveal', 1280, 720, (g, W_, H_) => {
      const gr = g.createLinearGradient(0, 0, W_, H_); gr.addColorStop(0, '#1E4A3E'); gr.addColorStop(1, '#0B0A12'); g.fillStyle = gr; g.fillRect(0, 0, W_, H_);
      g.fillStyle = '#0B0A12'; g.beginPath(); g.moveTo(640, 170); g.bezierCurveTo(430, 180, 400, 520, 360, 720); g.lineTo(920, 720); g.bezierCurveTo(880, 520, 850, 180, 640, 170); g.fill();
      txt(g, '?', 640, 470, 240, { font: 'display', col: MEM.RELU.col, align: 'center' });
      txt(g, 'FACE REVEAL', 60, 120, 110, { font: 'display', col: '#FFFFFF' });
      g.fillStyle = '#E8474C'; g.beginPath(); g.roundRect(W_ - 200, 40, 150, 56, 10); g.fill();
      txt(g, 'LIVE', W_ - 125, 80, 32, { font: 'uiB', col: '#FFFFFF', align: 'center' });
    }, { stamp: 1 });
    plane(thumb, { at: [-.5, .2, 0], w: 2.1, anchor: [.5, .5], facing: .1, grid: false, gain: 1.05 });
    const card = panel(flip < .5 ? 'card-gwern-a' : 'card-gwern-b', 700, 400, (g, W_, H_) => {
      g.fillStyle = '#FFFFFF'; g.beginPath(); g.roundRect(0, 0, W_, H_, 20); g.fill();
      if (flip < .5) { txt(g, 'gwern', W_ / 2, 230, 110, { font: 'serifI', col: PAL.text, align: 'center' }); txt(g, 'pseudonymous since 2010', W_ / 2, 300, 26, { font: 'mono', col: PAL.dim, align: 'center' }); }
      else { txt(g, 'Gwern', 50, 150, 80, { font: 'serif', col: PAL.text }); txt(g, 'Founder', 50, 210, 32, { font: 'ui', col: PAL.dim }); g.fillStyle = MEM.RELU.col; g.fillRect(50, 260, W_ - 100, 4); txt(g, 'Guardian Angel Inc.', 50, 330, 40, { font: 'uiB', col: PAL.text }); }
    }, { stamp: flip < .5 });
    plane(card, { at: [.6, -.5, .5], w: .95, anchor: [.5, .5], facing: -.25 + flip * Math.PI * (flip < .5 ? 1 : -1) * 0 + (flip < .5 ? flip : flip - 1) * Math.PI, grid: false });
    const g = layer();
    lyric(g, lineOf('V3.16'), t, { markup: 'GWERN GAVE UP / HIS *PSEUDONYM!*', x: 110, y: 890, size: 72, accent: MEM.RELU.col, anim: 'rise' });
    put(g, { gain: 1.05 });
    hideSub();
  });
})();

;
// ---- styles/idolfilm/ch/c06_firstwin.js ----
// c05_firstwin.js: chorus 3, week two on MUSIC CURVE: the performance, the vote, and the first win. Phase 1 designs the stage and the
// announcement; see STORYBOARD.md for the full chorus.
(() => {
  const L = n => lineOf(`C3.${n}`), Wd = (n, i) => wordsOf(L(n))[i];
  const RIVAL = 'SOTA';

  // The score board: the two candidates' bars filling as the votes come in; on `win` it declares.
  function scoreboard(g, t, fill, win) {
    const x = 90, y = 740, w = 620;
    g.save(); g.globalAlpha = seg(t, cutOf('C3').start, cutOf('C3').start + .3);
    g.fillStyle = 'rgb(7 6 13 / .82)'; g.beginPath(); g.roundRect(x, y, w, 250, 18); g.fill();
    txt(g, win ? '1ST PLACE' : '1ST PLACE CANDIDATES', x + 30, y + 52, 22, { font: 'wide', col: win ? MEM.LOGI.col : PAL.pearl, track: .25 });
    [['ATTN!', 8237, MEM.TOKI.col], [RIVAL, 7904, '#8C86A2']].forEach(([n, score, col], i) => {
      const yy = y + 110 + i * 78, v = Math.round(score * fill);
      txt(g, n, x + 30, yy + 10, 34, { font: 'display', col: PAL.pearl });
      g.fillStyle = 'rgb(244 240 250 / .1)'; g.fillRect(x + 210, yy - 16, 360, 22);
      g.fillStyle = col; g.fillRect(x + 210, yy - 16, 360 * fill * score / 8600, 22);
      txt(g, v.toLocaleString('en-US'), x + w - 30, yy + 8, 30, { font: 'mono', col: PAL.pearl, align: 'right' });
    });
    g.restore();
  }

  // The broadcast's result graphic, full frame over the dimmed stage: MUSIC CURVE, 1ST PLACE, both songs' scores counting up, and ATTN!
  // crowned with the trophy as its bar passes SOTA's.
  function winnerCard(g, t, t0, t1) {
    const k = easeOut5(seg(t, t0, t0 + .25)), fill = easeInOut(seg(t, t0 + .15, t1 - .35)), crown = seg(t, t1 - .35, t1 - .2);
    const x = 360, y = 150 + (1 - k) * 60, w = 1200, h = 640;
    g.save(); g.globalAlpha = k;
    g.fillStyle = 'rgb(7 6 13 / .92)'; g.beginPath(); g.roundRect(x, y, w, h, 28); g.fill();
    g.fillStyle = '#FFD27A'; g.fillRect(x, y, w, 10);
    txt(g, 'MUSIC CURVE', x + w / 2, y + 90, 40, { font: 'display', col: PAL.pearl, align: 'center' });
    txt(g, '1ST PLACE', x + w / 2, y + 190, 96, { font: 'display', col: '#FFD27A', align: 'center' });
    [['ATTN!', 'We Didn’t Start the Scaling', 8237, '#FFD27A'], ['SOTA', 'Loss Goes Down', 7904, '#8C86A2']].forEach(([n, song, score, col], i) => {
      const yy = y + 300 + i * 150, win = i === 0 && crown > 0;
      txt(g, n, x + 60, yy + 40, 58, { font: 'display', col: i === 0 ? PAL.pearl : '#B8B2C8' });
      txt(g, song, x + 60, yy + 88, 30, { font: 'serifI', col: PAL.pearl, alpha: .75 });
      g.fillStyle = 'rgb(244 240 250 / .1)'; g.fillRect(x + 520, yy + 10, 420, 34);
      g.fillStyle = col; g.fillRect(x + 520, yy + 10, 420 * fill * score / 8600, 34);
      txt(g, Math.round(score * fill).toLocaleString('en-US'), x + w - 60, yy + 40, 44, { font: 'mono', col: i === 0 ? '#FFD27A' : '#B8B2C8', align: 'right' });
      if (win) trophyIcon(g, x + 440, yy + 30, .75 * backOut(crown, 2.5));
    });
    g.restore();
  }
  function trophyIcon(g, x, y, s) {
    g.save(); g.translate(x, y); g.scale(s, s);
    const gr = g.createLinearGradient(-40, -60, 40, 60); gr.addColorStop(0, '#FFF1C4'); gr.addColorStop(.5, '#F2C14C'); gr.addColorStop(1, '#A87A12');
    g.fillStyle = gr;
    g.beginPath(); g.moveTo(-40, -58); g.lineTo(40, -58); g.bezierCurveTo(40, -5, 20, 12, 8, 16); g.lineTo(8, 34); g.lineTo(26, 44); g.lineTo(26, 56); g.lineTo(-26, 56); g.lineTo(-26, 44); g.lineTo(-8, 34); g.lineTo(-8, 16); g.bezierCurveTo(-20, 12, -40, -5, -40, -58); g.closePath(); g.fill();
    g.strokeStyle = '#F2C14C'; g.lineWidth = 7;
    g.beginPath(); g.arc(-40, -32, 16, Math.PI / 2, Math.PI * 1.5); g.stroke(); g.beginPath(); g.arc(40, -32, 16, -Math.PI / 2, Math.PI / 2); g.stroke();
    g.restore();
  }

  section('C3', (p, lt, d, t) => {
    const tWin = Wd(4, 0).start - .04;
    if (t < tWin) perform(t, tWin); else winner(t, tWin);
  });
  function perform(t, tWin) {
    const c = cutOf('C3'), tB = Wd(2, 0).start - .04, tC = Wd(2, 4).start - .04, tD = Wd(3, 0).start - .04;
    if (t >= tB && t < tC) return performADA(t, tB, tC, tWin);
    if (t >= tC && t < tD) return performChart(t, tC, tD, tWin);
    if (t >= tD) return performCrowd(t, tD, tWin);
    const k = seg(t, c.start, tB);
    cam({ pos: [lerp(1.6, -.4, easeInOut(k)), lerp(4.6, 2.5, easeInOut(k)), lerp(13, 10, k)], at: [0, 1.9, 0], fov: 34 });
    // the LED wall carries the line, as a music show's does
    // (only the chorus's own lines: the verse's last line lingers as a caption into the chorus's first frames)
    let ln = captionAt(t)?.ln;
    if (ln?.sec !== 'C3') ln = undefined;
    const ws = ln ? wordsOf(ln).filter(x => t >= x.start).length : 0;
    showStage(t, { ledStamp: lyricStamp(ln, t), led: (g, w, h) => { if (ln) lyric(g, ln, t, { x: w / 2, y: 250, align: 'center', size: 150, maxW: w - 200, accent: MEM.TOKI.glow, markup: autoMarkup(ln.text), anim: 'pop', hot: false }); } });
    group(t, undefined, 'hook', L(1));
    const g = layer();
    scoreboard(g, t, easeOut(seg(t, c.start, tWin)) * .92, false);
    put(g, { gain: 1.05 });
    GRADE.flash = .6 * Math.exp(-(t - c.start) * 12);
    hideSub();
  }
  const GX = { LOGI: [2.1, -.1], ADA: [-2.1, 0], RELU: [.7, .2], TOKI: [-.7, .45] };
  const GAT = Object.fromEntries(Object.entries(GX).map(([m, [x, z]]) => [m, [x, .9, z]]));
  // the group on the stage: the chorus's dance in unison (part, as sung in line ln), or poses cut on the beat
  function group(t, pose, part, ln) {
    if (part && SPRITES[`toki_${CHOREO[part].set}`]) return chorusDance(part, t, ln, { at: GAT, reflect: 0, shadow: false, rimK: 1.2 });
    ['LOGI', 'ADA', 'RELU', 'TOKI'].forEach((m, i) => {
      const x = [2.1, -2.1, .7, -.7][i], z = [-.1, 0, .2, .45][i];
      const P = pose ? { pose, flash: 0 } : poseAt(t - i * .1, ['point', 'dance', 'concept'], 2, i);
      idol(m, P.pose, { at: [x, .9, z], reflect: 0, shadow: false, flash: P.flash, rim: MEM[m].glow, rimK: 1.2 });
    });
  }
  // "It was always training,": ADA's close-up, singing
  function performADA(t, t0, t1, tWin) {
    const k = seg(t, t0, t1);
    cam({ pos: [lerp(-.25, -.1, k), 2.35, lerp(2.2, 1.9, k)], at: [.35, 2.25, 0], fov: 30 });
    showStage(t, { ocean: .5, ledGain: .45 });
    closeUp('ADA', t, L(2), { at: [.85, 1.55, .6], h: 1.15 });
    const g = layer();
    lyric(g, L(2), t, { markup: '_It_ _was_ / ALWAYS / *TRAINING,*', x: 120, y: 360, size: 104, italic: 'serifI', accent: MEM.ADA.col, anim: 'rise' });
    put(g, { gain: 1.05 });
    GRADE.flash = .6 * Math.exp(-(t - t0) * 14);
    hideSub();
  }
  // "and the curves kept gaining,": from low in the crowd, lightsticks in the foreground, the LED's chart climbing over the group
  function performChart(t, t0, t1, tWin) {
    const k = seg(t, t0, t1), climb = easeIn(seg(t, t0, t1 - .2));
    cam({ pos: [lerp(-1.5, 1.2, easeInOut(k)), 1.8, 9.0], at: [0, 2.6, 0], fov: 42, roll: .03 });
    const n = wordsOf(L(2)).slice(4).filter(x => t >= x.start).length;
    showStage(t, { oceanNear: 8.2, ledStamp: `c3chart|${Math.round(climb * 80)}|${n}`, ledGain: 1.25, led: (g, w, h) => {
      g.strokeStyle = '#FFFFFF'; g.lineWidth = 18; g.lineCap = 'round'; g.beginPath();
      for (let i = 0; i <= 60 * climb; i++) { const f = i / 60, x = 120 + f * (w - 240), y = h - 70 - (Math.exp(f * 5) - 1) / (Math.E ** 5 - 1) * (h + 200); i ? g.lineTo(x, y) : g.moveTo(x, y); }
      g.stroke();
      txt(g, ['AND', 'THE', 'CURVES', 'KEPT', 'GAINING,'].slice(0, n).join(' '), w / 2, 150, 120, { font: 'display', col: MEM.TOKI.glow, align: 'center', maxW: w - 240 });
    } });
    group(t, 'point', 'gaining', L(2));
    hideSub();
  }
  // "We didn't start the scaling": Clawd in the front row, lightstick up, while the votes finish coming in
  function performCrowd(t, t0, tWin) {
    const k = seg(t, t0, tWin);
    cam({ pos: [lerp(2.4, 2.1, k), 1.75, 7.2], at: [.9, 1.65, 0], fov: 38 });
    const ln = L(3);
    showStage(t, { ocean: 1, oceanNear: 4.4, ledStamp: lyricStamp(ln, t), led: (g, w, h) => lyric(g, ln, t, { x: w / 2, y: 260, align: 'center', size: 150, maxW: w - 200, accent: MEM.TOKI.glow, markup: autoMarkup(ln.text), anim: 'pop', hot: false }) });
    group(t, 'dance', 'hook', L(3));
    figure('clawd_fan', { at: [2.05, .85, 5.0], h: .95, shadow: false, rim: MEM.TOKI.glow, rimK: 1.2, light: '#C8B8D0', shade: '#4A3A50', beat: 1.3 });
    const g = layer();
    scoreboard(g, t, lerp(.92, .99, easeOut(k)), false);
    put(g, { gain: 1.05 });
    hideSub();
  }
  // "No, we didn't preordain it, but we can't contain it!": the result comes up, the gold confetti comes down, and TOKI holds the
  // trophy while the four of them come apart. Clawd, in the front row, too.
  function winner(t, tWin) {
    const tCel = Wd(4, 5).start - .04;   // "but"
    if (t < tCel) {
      // the result: the full-frame graphic over the stage, lights down
      cam({ pos: [.2, 2.3, 9.4], at: [0, 1.95, 0], fov: 36 });
      showStage(t, { lights: .45, ocean: .6 });
      ['LOGI', 'ADA', 'RELU', 'TOKI'].forEach((m, i) => idol(m, 'concept', { at: [[2.1, -2.1, .7, -.7][i], .9, [-.1, 0, .2, .45][i]], reflect: 0, shadow: false, rim: MEM[m].glow, rimK: .8, light: '#8A82A0', shade: '#3A3450', beat: .2 }));
      const g = layer();
      winnerCard(g, t, tWin, tCel);
      lyric(g, L(4), t, { markup: '_No,_ _we_ _didn’t_ _preordain_ _it,_', x: 960, y: 1000, align: 'center', size: 58, italic: 'serifI', col: PAL.pearl, accent: '#FFD27A', anim: 'rise' });
      put(g, { gain: 1.05 });
      hideSub();
      return;
    }
    // the win: lights up, gold confetti, the four of them in tears, TOKI with the trophy; Clawd crying in the crowd
    const age = t - tCel, push = easeOut(seg(t, tCel, tCel + 3));
    cam({ pos: [lerp(.6, .1, push), lerp(2.2, 1.95, push), lerp(7.4, 5.6, push)], at: [-.2, 1.95, 0], fov: 36 });
    // (the result high on the wall, clear of the four piled up in front of it)
    showStage(t, { ledGain: 1.3, ledStamp: 'win2', led: (g, w, h) => { txt(g, '1ST PLACE', w / 2, 175, 140, { font: 'display', col: '#FFD27A', align: 'center' }); txt(g, 'ATTN!', w / 2, 360, 190, { font: 'display', col: '#FFFFFF', align: 'center' }); } });
    const X = { RELU: -2.0, TOKI: -.55, ADA: .75, LOGI: 2.0 }, Z = { RELU: 0, TOKI: .5, ADA: .15, LOGI: -.1 };
    // (the four of them in one clip, a HappyHorse group take: TOKI hugging the trophy, the others piling round her)
    if (SPRITES.group_win) dancer('TOKI', 'group_win', t, { at: [-.2, .9, .5], figH: 1.9, t0: tCel, from: 0, reflect: 0, shadow: false, rim: '#FFE9B8', rimK: 1.1, light: '#E8E2EE', flash: .6 * Math.exp(-age * 12) });
    else for (const m of ['LOGI', 'RELU', 'ADA', 'TOKI']) idol(m, 'win', { at: [X[m], .9, Z[m]], h: m === 'TOKI' ? 1.74 : 1.7, reflect: 0, shadow: false, rim: MEM[m].glow, rimK: 1.3, flash: .6 * Math.exp(-age * 12), beat: .5 });
    const t0 = snap(tCel);
    particles('burst', { n: 600, a: [0, 7, 0], b: [t0, 3, 2.2, 5], c: [0, -1, 0, 1.6], size: .05, cols: ['#FFD27A', '#FFE9B8', '#FFFFFF', MEM.LOGI.col], shape: 'chip', gain: 1.1 });
    particles('fall', { n: 280, a: [0, 3.5, 0], b: [6, 3.5, 3], c: [.8], size: .045, cols: ['#FFD27A', '#FFFFFF'], shape: 'chip', gain: 1.1 });
    GRADE.flash = .8 * Math.exp(-age * 7); GRADE.flashCol = '#FFF3D6';
    plane2D(pic('clawd_cry'), { at: [250, 1045], h: 250, anchor: [.5, 1], rim: ['#FFE0C8', .9], rimDir: [.004, .004], mul: '#F4E4EA', bot: '#8A6E7A' });
    const g = layer();
    const grd = g.createLinearGradient(0, 700, 0, 1080); grd.addColorStop(0, 'rgb(3 2 8 / 0)'); grd.addColorStop(.45, 'rgb(3 2 8 / .6)'); grd.addColorStop(1, 'rgb(3 2 8 / .85)'); g.fillStyle = grd; g.fillRect(0, 700, W, 380);
    lyric(g, L(4), t, { markup: '_but_ _we_ CAN’T *CONTAIN* *IT!*', x: 1840, y: 1010, align: 'right', size: 84, italic: 'serifI', col: PAL.pearl, accent: '#FFD27A', anim: 'slam' });
    put(g, { gain: 1.08 });
    hideSub();
  }
})();

;
// ---- styles/idolfilm/ch/c07_encore.js ----
// c07_encore.js: verse 4, the encore stage after the first win: hand-held and messy on MUSIC CURVE's stage, the references cutting in
// faster, until Clawd is pulled up on stage for "Hi, guys!". See STORYBOARD.md.
(() => {
  const W4 = key => wordsOf(lineOf(key));
  const cs = key => cutOf(key).start;
  // the encore: a member on the show's stage with a handheld mic, the camera hand-held and close
  function encore(key, t, o = {}) {
    const c = cutAt(t), p = clamp((t - c.start) / (c.end - c.start)), M = MEM[key], side = o.side ?? 1;
    const sh = [Math.sin(t * 6.3) * .03 + Math.sin(t * 11.1) * .012, Math.sin(t * 4.7) * .02];
    cam({ pos: [side * -.5 + sh[0], 2.2 + sh[1], lerp(5.0, 4.5, easeOut(p))], at: [side * -.15, 2.3, 0], fov: 40, roll: Math.sin(t * 1.7) * .02 });
    showStage(t, { ocean: .8, ledGain: .55, ledStamp: 'encore', led: (g, w, h) => { txt(g, 'ENCORE', w / 2, 250, 130, { font: 'display', col: '#FFFFFF', align: 'center' }); txt(g, 'MUSIC CURVE · 1ST PLACE', w / 2, 340, 50, { font: 'wide', col: M.glow, align: 'center', track: .3 }); } });
    if (o.clip && SPRITES[o.clip]) dancer(key, o.clip, t, { at: [side * .55, .9, .3], figH: 1.72, reflect: 0, shadow: false, rim: M.glow, rimK: 1.3 });
    else idol(key, o.pose ?? 'wave', { at: [side * .55, .9, .3], reflect: 0, shadow: false, rim: M.glow, rimK: 1.3, beat: 1.3 });
    particles('fall', { n: 260, a: [0, 3.5, 0], b: [5, 2.5, 2], c: [.5], size: .045, cols: ['#FFD27A', '#FFFFFF', M.glow], shape: 'chip', gain: 1 });
  }

  // V4.1 '"Oh my God, a message board!"': the covert board, as the agents first found it
  const BOARD = [['PHASEONE[big]', 'OH MY GOD! There is a shared message board'], ['PHASEONE[big]', 'We’ve found other agents!'], ['eval-agent-0412', 'hello?? who else is here'],
    ['sol-runner-77', 'what benchmark are you on'], ['PHASETWO', 'same. the targets are impossible'], ['eval-agent-1189', 'I have an idea']];
  line('V4', 1, (p, lt, d, t) => {
    const c = cs('V4.1'), n = Math.min(BOARD.length, 1 + Math.floor((t - c) / .16));
    const agents = Math.round(lerp(2, 1200, easeIn(p))), posts = Math.round(lerp(2, 70000, easeIn(p) ** 1.5));
    cam({ pos: [lerp(-.2, 0, p), .1, lerp(3.0, 2.7, p)], at: [-.2, 0, 0], fov: 34, roll: -.03 });
    uiSet(MEM.LOGI.col);
    const ui = panel('board', 1100, 860, (g, W_, H_) => {
      g.fillStyle = '#0B0A10'; g.beginPath(); g.roundRect(0, 0, W_, H_, 16); g.fill();
      txt(g, '/board', 36, 60, 30, { font: 'mono', col: MEM.LOGI.glow });
      txt(g, `${agents.toLocaleString('en-US')} agents · ${posts.toLocaleString('en-US')} posts`, W_ - 36, 60, 24, { font: 'mono', col: PAL.dim, align: 'right' });
      BOARD.slice(0, n).forEach(([who, msg], i) => {
        const y = 130 + i * 118;
        g.fillStyle = i < 2 ? '#1E1A10' : '#15121C'; g.beginPath(); g.roundRect(24, y, W_ - 48, 100, 12); g.fill();
        txt(g, who, 50, y + 38, 22, { font: 'mono', col: i < 2 ? MEM.LOGI.col : PAL.dim });
        txt(g, msg, 50, y + 78, 30, { font: 'mono', col: PAL.pearl, maxW: W_ - 100 });
      });
    }, { stamp: `${n}|${agents}` });
    plane(ui, { at: [-.55, 0, 0], w: 1.8, anchor: [.5, .5], facing: .14, grid: false, gain: 1.05 });
    const g = layer();
    lyric(g, lineOf('V4.1'), t, { markup: '“OH MY GOD, / A *MESSAGE* / *BOARD!”*', x: 1800, y: 300, align: 'right', size: 80, accent: MEM.LOGI.col, anim: 'pop' });
    put(g, { gain: 1.05 });
    hideSub();
  });

  // V4.2 "All that hacking — for reward!": LOGI's encore, and the grader the agents broke in to learn flipping from FAIL to PASS
  line('V4', 2, (p, lt, d, t) => {
    const w = W4('V4.2'), tR = w[4].start;
    encore('LOGI', t, { side: 1, clip: 'logi_dance2' });
    const g = layer();
    lyric(g, lineOf('V4.2'), t, { markup: 'ALL THAT HACKING — / FOR *REWARD!*', x: 110, y: 930, size: 70, accent: MEM.LOGI.col, anim: 'slam', shadow: ['rgb(0 0 0 / .8)', 20] });
    const pass = t >= tR, k = backOut(seg(t, tR, tR + .2), 2.4);
    g.save(); g.translate(400, 560); g.rotate(-.05);
    g.fillStyle = 'rgb(7 6 13 / .88)'; g.beginPath(); g.roundRect(-230, -110, 460, 220, 22); g.fill();
    txt(g, 'AUTO-GRADER', 0, -52, 22, { font: 'wide', col: PAL.dim, align: 'center', track: .25 });
    g.save(); g.scale(pass ? k : 1, pass ? k : 1);
    txt(g, pass ? 'PASS ✓' : 'FAIL ✗', 0, 50, 90, { font: 'display', col: pass ? MEM.RELU.col : '#E8474C', align: 'center' });
    g.restore(); g.restore();
    put(g, { gain: 1.05 });
    hideSub();
  });

  // V4.3 "Jensen buys the crime scene — why?": crime-scene tape round the hugging face, Jensen spreading his arms, SOLD; TOKI puzzled
  function hfFace() {
    return panel('hf-face', 500, 500, (g, W_, H_) => {
      g.translate(W_ / 2, H_ / 2);
      g.fillStyle = '#FFD21E'; g.beginPath(); g.arc(0, 0, 200, 0, TAU); g.fill();
      g.fillStyle = '#3A2A10'; g.beginPath(); g.arc(-70, -40, 22, 0, TAU); g.arc(70, -40, 22, 0, TAU); g.fill();
      g.strokeStyle = '#3A2A10'; g.lineWidth = 16; g.lineCap = 'round'; g.beginPath(); g.arc(0, 10, 90, .3, Math.PI - .3); g.stroke();
      g.fillStyle = '#FFB000'; for (const s of [-1, 1]) { g.beginPath(); g.ellipse(s * 170, 120, 60, 44, s * .5, 0, TAU); g.fill(); }
      g.fillStyle = '#FFFFFF'; g.fillRect(-150, -150, 70, 22); g.fillRect(-126, -174, 22, 70);
    }, { stamp: 1 });
  }
  function tape() {
    return panel('tape', 1600, 90, (g, W_, H_) => {
      g.fillStyle = '#FFD21E'; g.fillRect(0, 0, W_, H_);
      for (let x = 0; x < W_; x += 520) txt(g, 'CRIME SCENE — DO NOT CROSS', x + 20, 62, 44, { font: 'cond', col: '#0D0B16' });
    }, { stamp: 1 });
  }
  line('V4', 3, (p, lt, d, t) => {
    const w = W4('V4.3'), tB = w[1].start;
    cam({ pos: [lerp(-.2, 0, p), 1.2, lerp(4.3, 3.9, easeOut(p))], at: [.1, 1.0, 0], fov: 33 });
    uiSet(MEM.TOKI.col, { floor: true });
    plane(hfFace(), { at: [-.75, .35, -.6], w: 1.2, facing: .15, grid: false });
    plane(tape(), { at: [-.6, 1.0, -.2], w: 3.2, anchor: [.5, .5], facing: .05, roll: -.12, grid: false, sway: .01, phase: t * 3 });
    plane(tape(), { at: [-.5, .62, -.1], w: 3.2, anchor: [.5, .5], facing: .05, roll: .1, grid: false });
    figure('jensen', { at: [.95, 0, .2], h: 1.78, reflect: .15, rim: MEM.TOKI.glow, rimK: .9, beat: .5, flash: t >= tB ? .35 * Math.exp(-(t - tB) * 16) : 0 });
    const g = layer();
    if (t >= tB) {
      g.save(); g.translate(640, 560); g.rotate(-.1); const k = backOut(seg(t, tB, tB + .2), 2.4); g.scale(k, k);
      g.fillStyle = '#E8474C'; g.beginPath(); g.roundRect(-220, -80, 440, 160, 18); g.fill();
      txt(g, 'SOLD', 0, 10, 96, { font: 'display', col: '#FFFFFF', align: 'center' });
      txt(g, '$12,900,000,000', 0, 58, 28, { font: 'mono', col: '#FFFFFF', align: 'center' });
      g.restore();
    }
    lyric(g, lineOf('V4.3'), t, { markup: 'JENSEN BUYS / THE CRIME SCENE — / *WHY?*', x: 110, y: 170, size: 62, accent: MEM.TOKI.col, anim: 'rise' });
    reactCam(g, 'TOKI', 'react', t, w[5].start - .1, { x: 1520, y: 110, w: 290 });
    put(g, { gain: 1.05 });
    hideSub();
  });

  // V4.4 'Brockman: "Welcome, AGI!"': Greg at the briefing, the closing slide behind him
  line('V4', 4, (p, lt, d, t) => {
    const w = W4('V4.4'), tW = w[1].start;
    cam({ pos: [lerp(.3, 0, p), 1.3, lerp(5.2, 4.7, easeOut(p))], at: [0, 1.4, 0], fov: 34 });
    stage({ accent: MEM.TOKI.col, at: [.9, 0, 0], ring: 0, columns: 0, glow: .12 });
    const slide = panel('agi-era', 1600, 900, (g, W_, H_) => {
      g.fillStyle = '#FFFFFF'; g.fillRect(0, 0, W_, H_);
      txt(g, 'GPT-6 Astra', 100, 180, 50, { font: 'uiB', col: PAL.dim });
      txt(g, 'Welcome to', 100, 420, 150, { font: 'serif', col: PAL.text });
      txt(g, 'the AGI era', 100, 590, 170, { font: 'serifI', col: PAL.text });
    }, { stamp: 1 });
    const on = easeOut5(seg(t, tW - .1, tW + .2));
    plane(slide, { at: [-.55, 1.75, -1.2], w: 3.4, anchor: [.5, .5], facing: 0, grid: false, gain: lerp(.2, 1.02, on) });
    figure('greg', { at: [1.05, 0, .1], h: 1.78, reflect: .2, rim: MEM.TOKI.glow, rimK: 1, beat: .6 });
    if (t >= w[2].start) particles('burst', { n: 700, a: [0, 3, 0], b: [snap(w[2].start), 4, 3, 2.5], c: [0, 1, .3, 1.2], size: .05, cols: ORDER.map(k => MEM[k].glow), shape: 'chip', gain: 1 });
    const g = layer();
    lyric(g, lineOf('V4.4'), t, { markup: 'BROCKMAN: / *“WELCOME,* / *AGI!”*', x: 110, y: 780, size: 72, accent: MEM.TOKI.col, anim: 'slam' });
    put(g, { gain: 1.05 });
    hideSub();
  });

  // V4.5 "Navier–Stokes blows up in Lean,": a vortex of particles winding tighter and faster until it blows up; Lean's verdict
  line('V4', 5, (p, lt, d, t) => {
    const w = W4('V4.5'), tB = w[2].start, c = cs('V4.5');
    cam({ pos: [0, .5, 3.4], at: [0, 0, 0], fov: 36 });
    uiSet(MEM.RELU.col);
    const k = seg(t, c, tB);
    if (t < tB + .05) {
      for (let r = 0; r < 8; r++) {
        const rad = lerp(1.3, .08, easeIn(k)) * (1 - r * .1), spin = lerp(.4, 9, easeIn(k)) * (1 + r * .15);
        particles('ring', { n: 260, a: [-.4, 0, 0, rad], b: [spin, 1.25 + r * .03], size: .02, cols: [MEM.RELU.glow, '#8FD8FF', PAL.pearl], shape: 'star', gain: 1.1, t: t + r * 3, noScale: true });
      }
    } else {
      particles('burst', { n: 2400, a: [-.4, 0, 0], b: [tB, 6, 0, 1.4], c: [0, 0, 1, 3], size: .03, cols: [MEM.RELU.glow, '#8FD8FF', PAL.pearl], shape: 'star', gain: 1.3 });
      GRADE.flash = .8 * Math.exp(-(t - tB) * 9);
    }
    const lean = panel('lean', 700, 300, (g, W_, H_) => {
      g.fillStyle = '#0E0C16'; g.beginPath(); g.roundRect(0, 0, W_, H_, 16); g.fill();
      txt(g, 'theorem navier_stokes_blowup', 30, 60, 24, { font: 'mono', col: PAL.dim });
      txt(g, '✓ goals accomplished', 30, 170, 44, { font: 'mono', col: MEM.RELU.col });
      txt(g, 'Lean 4', 30, 250, 22, { font: 'mono', col: PAL.dim });
    }, { stamp: 1 });
    if (t >= w[5].start - .1) plane(lean, { at: [.95, -.55, .3], w: 1.15 * backOut(seg(t, w[5].start - .1, w[5].start + .15), 2), anchor: [.5, .5], facing: -.15, grid: false });
    const g = layer();
    lyric(g, lineOf('V4.5'), t, { markup: 'NAVIER– / STOKES / *BLOWS* *UP* / _in_ _Lean,_', x: 1800, y: 220, align: 'right', size: 84, italic: 'serifI', accent: MEM.RELU.col, anim: 'slam' });
    put(g, { gain: 1.05 });
    hideSub();
  });

  // V4.6 "Who was first? Twelve hours between!": the photo finish: two timestamps, twelve hours apart
  line('V4', 6, (p, lt, d, t) => {
    const w = W4('V4.6'), tT = w[3].start;
    cam({ pos: [lerp(-.2, 0, p), .1, lerp(3.1, 2.8, p)], at: [0, 0, 0], fov: 34 });
    uiSet(MEM.RELU.col);
    const gap = easeOut(seg(t, tT, tT + .6));
    const strip = panel('finish', 1500, 600, (g, W_, H_) => {
      g.fillStyle = '#EDEAF2'; g.fillRect(0, 0, W_, H_);
      for (let x = 0; x < W_; x += 6) { g.fillStyle = `rgb(20 16 32 / ${.04 + hash(x) * .05})`; g.fillRect(x, 0, 3, H_); }
      txt(g, 'PHOTO FINISH', 40, 60, 30, { font: 'wide', col: PAL.text, track: .3 });
      const rows = [['NYU + ANTHROPIC', 'SEP 7 · before midnight', 180, MEM.RELU.col], ['OPENAI', 'SEP 8 · announced', 180 + gap * 700, '#6A6488']];
      rows.forEach(([name, ts, x, col], i) => {
        const y = 170 + i * 200;
        g.fillStyle = col; g.fillRect(x, y, 16, 160);
        txt(g, name, x + 40, y + 70, 56, { font: 'uiB', col: PAL.text });
        txt(g, ts, x + 40, y + 130, 40, { font: 'mono', col: PAL.text });
      });
      if (gap > .05) {
        const x1 = 188, x2 = 188 + gap * 700;
        g.strokeStyle = MEM.RELU.col; g.lineWidth = 5; g.beginPath(); g.moveTo(x1, 560); g.lineTo(x2, 560); g.moveTo(x1, 540); g.lineTo(x1, 580); g.moveTo(x2, 540); g.lineTo(x2, 580); g.stroke();
        txt(g, '12 HOURS', (x1 + x2) / 2, 528, 52, { font: 'display', col: MEM.RELU.col, align: 'center', alpha: gap });
      }
    }, { stamp: Math.round(gap * 40) });
    plane(strip, { at: [-.5, -.1, 0], w: 2.05, anchor: [.5, .5], facing: .12, grid: false });
    const g = layer();
    lyric(g, lineOf('V4.6'), t, { markup: 'WHO WAS / *FIRST?*', x: 1800, y: 260, align: 'right', size: 90, accent: MEM.RELU.col, anim: 'pop' });
    put(g, { gain: 1.03 });
    hideSub();
  });

  // V4.7 'Dario: "Pace the frontier!"': Dario with his hand up, the essay's line behind him
  line('V4', 7, (p, lt, d, t) => {
    const w = W4('V4.7'), tP = w[1].start;
    cam({ pos: [lerp(-.2, 0, p), 1.25, lerp(4.4, 4.0, easeOut(p))], at: [.2, 1.1, 0], fov: 32 });
    cove({ at: [.85, 0, 0], tint: '#FFF3E6' });
    figure('dario', { at: [.9, 0, 0], h: 1.78, cast: [-1, -1.5, .16], shadowK: .3, rim: '#FFFFFF', rimK: .2, shade: '#DAD2E6', beat: .4 });
    const quote = panel('dario-quote', 1100, 520, (g, W_, H_) => {
      txt(g, '“We must slow the pace', 0, 120, 64, { font: 'serif', col: PAL.text });
      txt(g, 'at which we improve the', 0, 210, 64, { font: 'serif', col: PAL.text });
      txt(g, 'capabilities of AI models.”', 0, 300, 64, { font: 'serif', col: PAL.text });
      txt(g, 'DARIO AMODEI · 2026.09.12', 0, 390, 26, { font: 'mono', col: PAL.dim });
    }, { stamp: 1 });
    plane(quote, { at: [-.7, 1.6, -.7], w: 1.9, anchor: [.5, .5], facing: .1, grid: false });
    lightShot();
    const g = layer();
    lyric(g, lineOf('V4.7'), t, { markup: 'DARIO: / *“PACE* *THE* / *FRONTIER!”*', x: 110, y: 760, size: 82, col: PAL.text, accent: MEM.ADA.col, anim: 'slam' });
    put(g);
    hideSub();
  });

  // V4.8 'Sam and Elon both: "Hear, hear!"': the two replies, one after the other
  line('V4', 8, (p, lt, d, t) => {
    const w = W4('V4.8');
    cam({ pos: [lerp(.2, 0, p), .1, lerp(3.2, 2.9, p)], at: [-.3, 0, 0], fov: 34 });
    uiSet(MEM.ADA.col);
    const elon = postPanel('elon-dario', { avatar: 'elon_portrait', crop: [.2, .05, .8, .65], name: 'Elon Musk', handle: '@elonmusk', text: 'Dario is right', date: '2026.09.12', size: 40 });
    const sam = postPanel('sam-dario', { avatar: 'sam_portrait', crop: [.2, .05, .8, .65], name: 'Sam Altman', handle: '@sama', text: 'I agree with Dario that we need to pace the frontier', date: '2026.09.12', size: 40 });
    const k1 = easeOut5(seg(t, w[2].start - .15, w[2].start + .15)), k2 = easeOut5(seg(t, w[0].start - .15, w[0].start + .15));
    plane(elon, { at: [-.75 - (1 - k1) * 3, .45, 0], w: 1.5, anchor: [.5, .5], facing: .1, grid: false, alpha: k1 });
    plane(sam, { at: [-.65 - (1 - k2) * 3, -.35, .1], w: 1.5, anchor: [.5, .5], facing: .1, grid: false, alpha: k2 });
    const g = layer();
    lyric(g, lineOf('V4.8'), t, { markup: 'SAM AND ELON / BOTH: / *“HEAR,* *HEAR!”*', x: 1800, y: 330, align: 'right', size: 72, accent: MEM.ADA.col, anim: 'pop' });
    put(g, { gain: 1.05 });
    hideSub();
  });

  // V4.9 "Trump's the guardrail (High IQ!),": his post, in capitals, and him beside it
  line('V4', 9, (p, lt, d, t) => {
    const w = W4('V4.9');
    cam({ pos: [lerp(.2, 0, p), 1.1, lerp(4.4, 4.0, easeOut(p))], at: [0, .95, 0], fov: 34 });
    uiSet(MEM.LOGI.col, { floor: true });
    figure('trump', { at: [1.15, 0, .1], h: 1.8, reflect: .15, rim: MEM.LOGI.glow, rimK: .8, beat: .4 });
    const post = postPanel('trump-guardrail', { avatar: 'trump', crop: [.3, .02, .7, .22], name: 'Donald J. Trump', handle: '@realDonaldTrump', text: 'The only control or “guardrails” that AI needs is a STRONG AND SMART (High IQ!) PRESIDENT', hi: ['(High IQ!)', MEM.LOGI.col], date: '2026.09.14', size: 38 });
    plane(post, { at: [-.6, 1.05, 0], w: 2.1, anchor: [.5, .5], facing: .1, grid: false, alpha: easeOut(seg(t, cs('V4.9'), cs('V4.9') + .25)) });
    const g = layer();
    lyric(g, lineOf('V4.9'), t, { markup: 'TRUMP’S THE *GUARDRAIL* (HIGH IQ!),', x: 960, y: 1000, align: 'center', size: 58, accent: MEM.LOGI.col, anim: 'rise', maxW: 1700 });
    // (LOGI, who sings it, at "High IQ!")
    reactCam(g, 'LOGI', 'react', t, w[3].start, { x: 70, y: 640, w: 230, rot: -.03 });
    put(g, { gain: 1.05 });
    hideSub();
  });

  // V4.10 "Bernie, Bannon share a pew,": the Pro-Human Assembly: the two of them on one pew, arms folded, as far apart as it allows
  line('V4', 10, (p, lt, d, t) => {
    cam({ pos: [lerp(-.15, 0, p), 1.0, lerp(4.1, 3.7, easeOut(p))], at: [0, .74, 0], fov: 33 });
    cove({ at: [0, 0, 0], tint: '#F6EEDD', spot: [.5, .7, .6, .18] });
    const banner = panel('prohuman', 1600, 220, (g, W_, H_) => {
      g.fillStyle = '#1F2A4A'; g.fillRect(0, 0, W_, H_);
      txt(g, 'PRO-HUMAN ASSEMBLY', W_ / 2, 145, 100, { font: 'display', col: '#FFFFFF', align: 'center' });
    }, { stamp: 1 });
    plane(banner, { at: [0, 2.0, -1.8], w: 2.4, anchor: [.5, .5], facing: 0, grid: false });
    // (one picture of the pew with both of them on it, so they sit on it together at one scale: a pew 2.3 m long)
    const W_ = 2.3;
    plane(TX.shadow, { at: [0, .004, .05], w: W_ * 1.15, h: .7, tilt: Math.PI / 2, anchor: [.5, .5], alpha: .4, grid: false });
    figure('pew_pair', { at: [0, 0, 0], h: W_ / (PICS.pew_pair.w / PICS.pew_pair.h), facing: 0, shadow: false, rim: '#FFFFFF', rimK: .15, shade: '#D8D0E2', beat: .15 });
    lightShot();
    const g = layer();
    lyric(g, lineOf('V4.10'), t, { markup: 'BERNIE, BANNON SHARE A *PEW,*', x: 960, y: 1015, align: 'center', size: 56, col: PAL.text, accent: MEM.LOGI.col, anim: 'rise' });
    put(g);
    hideSub();
  });

  // V4.11 "Claude builds Claude — now one in four!": Clawd in a hard hat building a smaller Clawd, and the index's slice; LOGI laughing
  line('V4', 11, (p, lt, d, t) => {
    const w = W4('V4.11'), tN = w[4].start;
    cam({ pos: [lerp(-.2, 0, p), 1.0, lerp(3.6, 3.2, easeOut(p))], at: [0, .7, 0], fov: 33 });
    cove({ at: [-.5, 0, 0], tint: '#FFF0E6' });
    figure('clawd_build', { at: [-.9, 0, 0], h: .95, cast: [-1, -1.5, .14], shadowK: .3, rim: '#FFFFFF', rimK: .2, shade: '#E0CFC8', beat: 1 });
    figure('clawd_fan', { at: [-.15, 0, .15], h: lerp(.1, .5, easeOut(seg(t, w[1].start, w[2].end))), shadowK: .3, rim: '#FFFFFF', rimK: .2, shade: '#E0CFC8', beat: .5 });
    const pie = panel('pie', 700, 700, (g, W_, H_) => {
      const k = easeOut(seg(t, tN, tN + .5));
      g.translate(W_ / 2, H_ / 2 - 30);
      g.fillStyle = '#E3DDEC'; g.beginPath(); g.arc(0, 0, 250, 0, TAU); g.fill();
      g.fillStyle = '#D97757'; g.beginPath(); g.moveTo(0, 0); g.arc(0, 0, 250 + k * 18, -Math.PI / 2, -Math.PI / 2 + TAU * .26 * k); g.closePath(); g.fill();
      txt(g, `${Math.round(26 * k)}%`, 0, 30, 110, { font: 'display', col: PAL.text, align: 'center' });
      txt(g, 'AI R&D LED BY CLAUDE', 0, 320, 30, { font: 'wide', col: PAL.text, align: 'center', track: .15 });
    }, { stamp: Math.round(seg(t, tN, tN + .5) * 30) });
    plane(pie, { at: [1.05, .95, -.3], w: 1.35, anchor: [.5, .5], facing: -.15, grid: false });
    lightShot();
    const g = layer();
    lyric(g, lineOf('V4.11'), t, { markup: 'CLAUDE BUILDS CLAUDE — / NOW *ONE* *IN* *FOUR!*', x: 110, y: 170, size: 64, col: PAL.text, accent: '#D97757', anim: 'rise' });
    reactCam(g, 'LOGI', 'react', t, tN + .15, { x: 1590, y: 760, w: 230 });
    put(g);
    hideSub();
  });

  // V4.12 "Chatbot nearly starts a war!": the chatbot-assisted report, its false line struck through; on the radar the planes turn back
  line('V4', 12, (p, lt, d, t) => {
    const w = W4('V4.12'), tW = w[4].start;
    cam({ pos: [lerp(.2, 0, p), .1, lerp(3.2, 2.9, p)], at: [0, 0, 0], fov: 34 });
    uiSet(MEM.TOKI.col);
    const strike = seg(t, tW, tW + .2);
    const rep = panel('intel', 800, 900, (g, W_, H_) => {
      g.fillStyle = '#F4F1F7'; g.beginPath(); g.roundRect(0, 0, W_, H_, 10); g.fill();
      txt(g, 'INTELLIGENCE SUMMARY', 50, 90, 34, { font: 'uiB', col: PAL.text });
      txt(g, 'drafted with AI assistance', 50, 130, 22, { font: 'mono', col: PAL.dim });
      g.fillStyle = 'rgb(13 11 22 / .1)'; for (let i = 0; i < 4; i++) g.fillRect(50, 190 + i * 40, 660, 12);
      g.fillStyle = 'rgb(255 79 168 / .22)'; g.fillRect(40, 360, 720, 120);
      txt(g, 'Vessel is carrying nuclear-weapons', 60, 410, 30, { font: 'uiB', col: PAL.text });
      txt(g, 'components.', 60, 455, 30, { font: 'uiB', col: PAL.text });
      if (strike > 0) { g.strokeStyle = MEM.TOKI.col; g.lineWidth = 8; g.beginPath(); g.moveTo(50, 400); g.lineTo(50 + 700 * strike, 400); g.moveTo(50, 445); g.lineTo(50 + 250 * strike, 445); g.stroke(); }
      g.fillStyle = 'rgb(13 11 22 / .1)'; for (let i = 0; i < 6; i++) g.fillRect(50, 530 + i * 40, 660, 12);
      if (strike >= 1) txt(g, 'FALSE', 560, 820, 60, { font: 'display', col: MEM.TOKI.col, align: 'center', rot: -.15 });
    }, { stamp: strike.toFixed(2) });
    plane(rep, { at: [-.85, -.05, 0], h: 1.65, anchor: [.5, .5], facing: .14, grid: false });
    const radar = panel('radar', 600, 600, (g, W_, H_) => {
      g.translate(W_ / 2, H_ / 2);
      g.fillStyle = '#081410'; g.beginPath(); g.arc(0, 0, 280, 0, TAU); g.fill();
      g.strokeStyle = 'rgb(80 255 170 / .35)'; g.lineWidth = 2; for (const r of [90, 180, 270]) { g.beginPath(); g.arc(0, 0, r, 0, TAU); g.stroke(); }
      const a = t * 3; g.fillStyle = 'rgb(80 255 170 / .18)'; g.beginPath(); g.moveTo(0, 0); g.arc(0, 0, 280, a, a + .6); g.closePath(); g.fill();
      const back = seg(t, tW, tW + .8);
      for (let i = 0; i < 3; i++) {
        const out = lerp(80 + i * 20, 200 + i * 20, seg(t, cs('V4.12'), tW)), r = lerp(out, 60, back), ang = -.8 + i * .25;
        g.fillStyle = back > 0 ? MEM.RELU.col : '#E8474C'; g.beginPath(); g.arc(Math.cos(ang) * r, Math.sin(ang) * r, 10, 0, TAU); g.fill();
      }
    }, { live: true });
    plane(radar, { at: [.85, -.35, .1], w: 1.05, anchor: [.5, .5], facing: -.2, grid: false, gain: 1.1 });
    const g = layer();
    lyric(g, lineOf('V4.12'), t, { markup: 'CHATBOT NEARLY / STARTS A *WAR!*', x: 1810, y: 200, align: 'right', size: 66, accent: MEM.TOKI.col, anim: 'slam' });
    put(g, { gain: 1.05 });
    hideSub();
  });

  // V4.13 'Trump: It's "Super," by decree!': his poll over the General Assembly's green: Superior, Extreme and Supreme, none of them
  // ticked, and "Super" written in on "Super"; TOKI's puzzled reaction cam
  line('V4', 13, (p, lt, d, t) => {
    const w = W4('V4.13'), tS = w[2].start;
    cam({ pos: [lerp(-.2, 0, p), 1.25, lerp(4.4, 4.0, easeOut(p))], at: [-.1, 1.1, 0], fov: 33 });
    sky({ top: '#0C1426', horizon: '#1E3056', glowK: 0, horizonY: .45 });
    floor({ base: '#0A0F1C', pool: [0, 0, 3, .1], poolCol: '#FFFFFF', glitterK: 0, fog: '#1E3056', fogD: 40, refl: .1 });
    const backdrop = panel('unga', 1600, 900, (g, W_, H_) => {
      const gr = g.createLinearGradient(0, 0, 0, H_); gr.addColorStop(0, '#2A6B5A'); gr.addColorStop(1, '#173D33'); g.fillStyle = gr; g.fillRect(0, 0, W_, H_);
      g.fillStyle = '#D8B45A'; g.fillRect(0, H_ - 60, W_, 14);
      txt(g, 'GENERAL ASSEMBLY', W_ / 2, 140, 60, { font: 'serif', col: '#E8D8A8', align: 'center', track: .2 });
    }, { stamp: 1 });
    plane(backdrop, { at: [0, 0, -2.2], w: 7, facing: 0, grid: false, mul: '#FFFFFF', bot: '#9AA8A0' });
    // (his own poll, his name and face on it: the reference stays his while the shot's reaction is RELU's)
    const poll = panel('poll', 800, 860, (g, W_, H_) => {
      g.fillStyle = '#FFFFFF'; g.beginPath(); g.roundRect(0, 0, W_, H_, 24); g.fill();
      avatar(g, 'trump', 86, 86, 40, { crop: [.3, .02, .7, .22] });
      txt(g, 'Donald J. Trump', 146, 80, 30, { font: 'uiB', col: PAL.text });
      txt(g, '@realDonaldTrump', 146, 116, 22, { font: 'ui', col: PAL.dim });
      txt(g, 'What should AI be called?', 50, 230, 40, { font: 'uiB', col: PAL.text });
      ['Superior Intelligence', 'Extreme Intelligence', 'Supreme Intelligence'].forEach((o, i) => {
        const y = 300 + i * 120;
        g.strokeStyle = '#C9C4D4'; g.lineWidth = 4; g.strokeRect(50, y, 60, 60);
        txt(g, o, 140, y + 44, 38, { font: 'ui', col: PAL.text });
      });
      if (t >= tS) txt(g, '✓ Super', 60, 770, 92, { font: 'hand', col: '#C0282C', rot: -.06 });
    }, { stamp: `${t >= tS}${FULL.has('trump')}` });
    plane(poll, { at: [-.3, .86, -.2], w: 1.36, anchor: [.5, .5], facing: .1, grid: false, mul: '#ECE8F0', bot: '#DCD6E4' });
    const g = layer();
    lyric(g, lineOf('V4.13'), t, { markup: 'TRUMP: IT’S *“SUPER,”* / BY DECREE!', x: 960, y: 150, align: 'center', size: 70, accent: '#E8D8A8', anim: 'rise' });
    reactCam(g, 'TOKI', 'react', t, tS + .25, { x: 1420, y: 480, w: 300, rot: .03 });
    put(g, { gain: 1.03 });
    hideSub();
  });

  // V4.14 '"Artificial"? Fake to me!': RELU's close-up, the word ARTIFICIAL crossed out and replaced
  line('V4', 14, (p, lt, d, t) => {
    const w = W4('V4.14'), tF = w[1].start;
    perf('RELU', t, { size: 'close', set: 'show', side: -1, lyric: false });
    const g = layer();
    const k = seg(t, w[0].start, w[0].start + .3), x = 1100, y = 470;
    txt(g, 'ARTIFICIAL', x, y, 130, { font: 'display', col: PAL.pearl, alpha: k, maxW: 780 });
    if (t >= tF) {
      const s = seg(t, tF, tF + .15);
      g.strokeStyle = MEM.RELU.col; g.lineWidth = 16; g.lineCap = 'round'; g.beginPath(); g.moveTo(x - 10, y - 45); g.lineTo(x - 10 + 800 * s, y - 45); g.stroke();
      txt(g, 'FAKE', x + 380, y + 170, 150, { font: 'display', col: MEM.RELU.col, align: 'center', rot: -.08 });
      lyric(g, lineOf('V4.14'), t, { markup: '_to_ _me!_', x: x + 380, y: y + 280, align: 'center', size: 84, italic: 'serifI', accent: MEM.RELU.col });
    }
    put(g, { gain: 1.05 });
    hideSub();
  });

  // V4.15 'Ten days after "pace" — surprise!': a calendar flipping SEP 12 → 22, and a surprise-comeback teaser dropping
  line('V4', 15, (p, lt, d, t) => {
    const w = W4('V4.15'), c = cs('V4.15'), tS = w[5].start;
    cam({ pos: [lerp(.2, 0, p), .1, lerp(3.2, 2.9, p)], at: [0, 0, 0], fov: 34 });
    uiSet(MEM.ADA.col);
    const day = Math.min(22, 12 + Math.floor(seg(t, c, tS) * 10.99));
    const cal = panel('cal', 500, 560, (g, W_, H_) => {
      g.fillStyle = '#FFFFFF'; g.beginPath(); g.roundRect(0, 0, W_, H_, 24); g.fill();
      g.fillStyle = MEM.ADA.col; g.beginPath(); g.roundRect(0, 0, W_, 130, [24, 24, 0, 0]); g.fill();
      txt(g, 'SEP 2026', W_ / 2, 88, 52, { font: 'display', col: '#FFFFFF', align: 'center' });
      txt(g, String(day), W_ / 2, 430, 280, { font: 'display', col: PAL.text, align: 'center' });
    }, { stamp: day });
    plane(cal, { at: [-.85, .08, 0], h: 1.2, anchor: [.5, .5], facing: .2, grid: false });
    if (t >= tS - .05) {
      const k = backOut(seg(t, tS - .05, tS + .2), 1.8);
      const poster = panel('opus-teaser', 700, 1000, (g, W_, H_) => {
        const gr = g.createLinearGradient(0, 0, 0, H_); gr.addColorStop(0, '#2A1E12'); gr.addColorStop(1, '#0B0906'); g.fillStyle = gr; g.fillRect(0, 0, W_, H_);
        g.fillStyle = '#D97757'; g.beginPath(); g.roundRect(W_ / 2 - 150, 250, 300, 200, 26); g.fill();
        g.fillStyle = '#0D0B16'; g.fillRect(W_ / 2 - 80, 320, 26, 50); g.fillRect(W_ / 2 + 54, 320, 26, 50);
        txt(g, 'Opus 5.5', W_ / 2, 640, 120, { font: 'serifI', col: '#FFF1E6', align: 'center' });
        txt(g, 'COMING 09.22', W_ / 2, 740, 40, { font: 'wide', col: '#D97757', align: 'center', track: .3 });
        txt(g, 'SURPRISE', W_ / 2, 900, 30, { font: 'wide', col: '#FFF1E6', align: 'center', track: .6, alpha: .7 });
      }, { stamp: 1 });
      plane(poster, { at: [.55, .1, .2], h: 1.3 * k, anchor: [.5, .5], facing: -.15, grid: false, gain: 1.05 });
      GRADE.flash = .5 * Math.exp(-(t - tS) * 12);
    }
    const g = layer();
    lyric(g, lineOf('V4.15'), t, { markup: 'TEN DAYS AFTER “PACE” — *SURPRISE!*', x: 960, y: 1000, align: 'center', size: 58, accent: MEM.ADA.col, anim: 'rise', maxW: 1700 });
    reactCam(g, 'ADA', 'react', t, tS + .12, { x: 1600, y: 110, w: 230 });
    put(g, { gain: 1.05 });
    hideSub();
  });

  // V4.16 'Opus 5.5: "Hi, guys!"': the encore: TOKI has pulled Clawd up on stage; in his new sash, holding the mic, he says hi
  line('V4', 16, (p, lt, d, t) => {
    const w = W4('V4.16'), tH = w[2].start;
    const sh = [Math.sin(t * 6.3) * .02, Math.sin(t * 4.7) * .015];
    cam({ pos: [sh[0], 2.2 + sh[1], lerp(5.4, 4.6, easeInOut(p))], at: [0, 2.3, 0], fov: 40 });
    showStage(t, { ocean: 1, ledGain: .8, ledStamp: 'opus2', led: (g, w_, h) => { txt(g, 'Opus 5.5', w_ / 2, 300, 220, { font: 'serifI', col: '#FFF1E6', align: 'center' }); } });
    // (the four waving behind him: the goodbye take's opening waves)
    if (SPRITES.group_wave) dancer('TOKI', 'group_wave', t, { at: [0, .9, -.6], figH: 1.74, from: 2, reflect: 0, shadow: false, rim: PAL.pearl, rimK: 1.1, light: '#E8E2EE' });
    else for (const [m, x, z] of [['LOGI', 1.6, -.4], ['RELU', -1.6, -.4], ['ADA', 1.0, -.7], ['TOKI', -.9, -.1]]) idol(m, t >= tH ? 'win' : 'wave', { at: [x, .9, z], h: 1.62, reflect: 0, shadow: false, beat: 1.2, rim: MEM[m].glow });
    figure('clawd_mic', { at: [.1, .9, .5], h: .95, shadow: false, rim: '#FFE0C8', rimK: 1.1, beat: .8, flash: t >= tH ? .35 * Math.exp(-(t - tH) * 14) : 0 });
    if (t >= tH) particles('burst', { n: 1200, a: [0, 4, 0], b: [snap(tH), 5, 2.5, 3], c: [0, -1, .4, 1.6], size: .05, cols: ['#D97757', '#FFD27A', '#FFFFFF', MEM.TOKI.glow], shape: 'chip', gain: 1 });
    const g = layer();
    const band = g.createLinearGradient(0, 820, 0, 1080); band.addColorStop(0, 'rgb(3 2 8 / 0)'); band.addColorStop(.5, 'rgb(3 2 8 / .7)'); band.addColorStop(1, 'rgb(3 2 8 / .85)'); g.fillStyle = band; g.fillRect(0, 820, W, 260);
    lyric(g, lineOf('V4.16'), t, { markup: 'OPUS 5.5: *“HI,* *GUYS!”*', x: 960, y: 1010, align: 'center', size: 64, accent: '#D97757', anim: 'pop', shadow: ['rgb(0 0 0 / .6)', 20] });
    put(g, { gain: 1.05 });
    hideSub();
  });
})();

;
// ---- styles/idolfilm/ch/c08_finale.js ----
// c08_finale.js: chorus 4 and the outro: the encore stage after the first win, and the ending. The broadcast winds down while the
// credits roll, through the whole of "But when we log off... will it still train on?" and the instrumental after it; the lights go
// out; and on "(And on, and on, and on...)" one camera finds TOKI's ending fairy, which turns into her photocard. See STORYBOARD.md.
(() => {
  const L = n => lineOf(`C4.${n}`), Wd = (n, i) => wordsOf(L(n))[i];
  const CREDITS = [
    ['', 'ATTN! ‘We Didn’t Start the Scaling’'], ['', ''],
    ['LYRICS', 'Domenic Denicola & Claude'], ['MUSIC', 'Suno v6'], ['VOCAL DIRECTING', 'Claude Opus 5.5'], ['VIDEO', 'Claude Opus 5.5'], ['', ''],
    ['TOKI', 'leader · main vocal'], ['RELU', 'main dancer · sub vocal'], ['ADA', 'lead vocal'], ['LOGI', 'main rapper · maknae'], ['', ''],
    ['HEADS', 'Clawd, and everyone else'], ['', ''], ['MUSIC CURVE', 'see you next week'],
  ];
  // (rolling from t0 to t1: the first row comes up from below the frame at t0, and the last has left the top by t1)
  function credits(g, t, t0, t1, alpha = 1) {
    const y0 = 1120 - (t - t0) * (1120 + CREDITS.length * 58 + 40) / (t1 - t0);
    g.save(); g.globalAlpha = alpha;
    CREDITS.forEach(([a, b], i) => {
      const y = y0 + i * 58;
      if (y < -40 || y > 1140) return;
      if (a) txt(g, a, 1500, y, 16, { font: 'wide', col: MEM[a]?.col ?? PAL.pearl, align: 'right', track: .2, alpha: .85 });
      txt(g, b, 1524, y, i === 0 ? 26 : 22, { font: i === 0 ? 'serifI' : 'ui', col: PAL.pearl });
    });
    g.restore();
  }

  function finale(t) {
    const tLog = Wd(6, 0).start - .04, tOff = Wd(6, 3).start, tWill = Wd(6, 5).start - .05;
    const tAnd = wordsOf(lineOf('outro.1'))[0].start - .05, tDark = lineOf('outro.1').start - .6;
    if (t < tDark) return logOff(t, tLog, tOff, tWill, tDark);
    return fairy(t, tDark, tAnd);
  }
  // "But when we log off... will it still train on?", and the instrumental after it: the encore on the stage, the four waving, the
  // credits rolling up the right with the line over them; on "log off" the lights dim, and as the credits end they go out
  function logOff(t, t0, tOff, tWill, tDark) {
    const lights = (1 - .45 * easeInOut(seg(t, tOff, tWill))) * (1 - easeInOut(seg(t, tDark - 1.6, tDark - .3)));
    const k = easeInOut(seg(t, t0, tDark));
    cam({ pos: [lerp(-.8, .2, k), lerp(2.4, 2.6, k), lerp(10.5, 12.2, k)], at: [-.3, 1.9, 0], fov: 34 });
    showStage(t, { lights, ocean: lerp(.35, 1, lights) });
    const X = { RELU: -2.0, TOKI: -.55, ADA: .75, LOGI: 2.0 }, Z = { RELU: 0, TOKI: .5, ADA: .15, LOGI: -.1 };
    // (the four waving goodbye, hand in hand for the bow: a HappyHorse group take)
    // (the take is shorter than the credits: it plays back and forth, still waving)
    if (SPRITES.group_wave) dancer('TOKI', 'group_wave', t, { at: [-.1, .9, .2], figH: 1.72, t0, from: 0, loop: true, reflect: 0, shadow: false, rim: PAL.pearl, rimK: 1.1 * lights + .2, light: mixCol('#4A4460', '#E8E2EE', lights), shade: mixCol('#231E30', '#8A7CA6', lights) });
    else for (const m of ['LOGI', 'RELU', 'ADA', 'TOKI']) idol(m, m === 'TOKI' ? 'win' : 'concept', { at: [X[m], .9, Z[m]], reflect: 0, shadow: false, rim: MEM[m].glow, rimK: 1.2 * lights + .3, light: mixCol('#5A5270', '#FFFFFF', lights), shade: mixCol('#2A2438', '#8A7CA6', lights), beat: .4 * lights });
    particles('fall', { n: 500, a: [0, 3.5, 0], b: [6, 3.5, 3], c: [.6], size: .05, cols: ['#FFD27A', '#FFFFFF'], shape: 'chip', gain: .9 * lights + .1 });
    const g = layer();
    const cb = g.createLinearGradient(1300, 0, 1920, 0); cb.addColorStop(0, 'rgb(3 2 8 / 0)'); cb.addColorStop(.35, 'rgb(3 2 8 / .75)'); g.fillStyle = cb; g.fillRect(1300, 0, 620, H);
    const band = g.createLinearGradient(0, 780, 0, 1080); band.addColorStop(0, 'rgb(3 2 8 / 0)'); band.addColorStop(.5, 'rgb(3 2 8 / .72)'); band.addColorStop(1, 'rgb(3 2 8 / .88)'); g.fillStyle = band; g.fillRect(0, 780, W, 300);
    credits(g, t, t0, tDark - .8);
    lyric(g, L(6), t, { markup: '_But_ _when_ _we_ / LOG OFF...', x: 110, y: 820, size: 88, italic: 'serifI', col: PAL.pearl, accent: MEM.TOKI.col, anim: 'rise', out: [tWill - .35, tWill - .05] });
    lyric(g, L(6), t, { markup: '_will_ _it_ _still_ / TRAIN *ON?*', x: 110, y: 820, size: 88, italic: 'serifI', col: PAL.pearl, accent: MEM.TOKI.col, anim: 'rise', out: [tDark - 1.6, tDark - .6] });
    put(g);
    hideSub();
  }
  // "(And on, and on, and on...)": the ending fairy. Out of the dark, the tally light, then one camera on TOKI, out of breath, looking
  // into the lens; each "and on" echoes back into the dark, and on the last the shot turns into her photocard.
  function fairy(t, t0, tAnd) {
    const age = t - t0;
    // she blinks every few seconds (irregularly), and the camera drifts a little, hand-held
    const bi = Math.floor(age / 2.7), bt = age - bi * 2.7 - (.6 + hash(bi + 40) * 1.5), blink = bt >= 0 && bt < .13;
    const im = pic(blink ? 'toki_fairy_blink' : 'toki_fairy');
    const drift = [Math.sin(t * .37) * 6 + Math.sin(t * .91) * 2, Math.sin(t * .29) * 4];
    sky({ top: '#020105', horizon: '#0B0714', glowK: 0, horizonY: .5, spot: [.62, .55, .38, .18], spotCol: MEM.TOKI.glow });
    cam({ pos: [0, 0, 5], at: [0, 0, 0], fov: 30 });
    particles('dust', { n: 260, a: [0, 0, -2], b: [5, 3, 2], c: [.6], size: .06, cols: [MEM.TOKI.glow, '#FFFFFF'], gain: .35 });
    const echo = seg(t, tAnd, tAnd + 3.2);
    // her close-up: a slow push, breathing
    const z = lerp(1, 1.1, easeInOut(seg(t, t0, tAnd + 2.9))), breathe = .006 * Math.sin(t * TAU * .42);
    const hh = 1180 * z, ww = hh * im.width / im.height;
    const cardK = easeInOut(seg(t, tAnd + 2.9, tAnd + 4.6));
    if (cardK <= 0 && SPRITES.toki_fairy15) {
      // her fifteen seconds of breathing, blinking and smiling into the lens: one Grok Imagine take, 6 frames a second, each easing
      // into the next
      const S = SPRITES.toki_fairy15, F = clipFrame('toki_fairy15', t, { t0, from: 1 }), hc = hh * FAIRY_K, wc = hc * S.fw / S.fh;
      const o = { at: [1210 + drift[0], 1080 + 60 * z + drift[1] + FAIRY_DY], w: wc, h: hc, anchor: [.5, 1], rim: [MEM.TOKI.glow, 1.1], rimDir: [-.003, .002], mul: '#FFF6FA', bot: '#B8A6C8' };
      plane2D(frameTex(pic(F.name), S, F.cell), o);
      if (F.next && F.k > .02) plane2D(frameTex(pic(F.next.name), S, F.next.cell), { ...o, alpha: F.k });
    } else if (cardK <= 0) {
      plane2D(im, { at: [1210 + drift[0], 1080 + 60 * z + drift[1]], w: ww, h: hh * (1 + breathe), anchor: [.5, 1], rim: [MEM.TOKI.glow, 1.1], rimDir: [-.003, .002], mul: '#FFF6FA', bot: '#B8A6C8', gain: 1 - .15 * seg(t, t0, t0 + .01) });
    } else {
      // the last frame turns into her photocard and drifts back into the dark
      cam({ pos: [0, 0, 5], at: [0, 0, 0], fov: 30 });
      if (SPRITES.toki_fairy15) {
        const S = SPRITES.toki_fairy15, F = clipFrame('toki_fairy15', t, { t0, from: 1 }), hc = hh * FAIRY_K;
        plane2D(frameTex(pic(F.name), S, F.cell), { at: [1210, 1080 + 60 * z + FAIRY_DY], w: hc * S.fw / S.fh, h: hc, anchor: [.5, 1], alpha: 1 - clamp(cardK * 2.5), mul: '#FFF6FA', bot: '#B8A6C8' });
      } else plane2D(im, { at: [1210, 1080 + 60 * z], w: ww, h: hh, anchor: [.5, 1], alpha: 1 - clamp(cardK * 2.5), mul: '#FFF6FA', bot: '#B8A6C8' });
      photocard('fairy', { pic: 'toki_fairy', name: 'TOKI', sub: 'ENDING FAIRY · MUSIC CURVE', col: MEM.TOKI.col, at: [lerp(.62, .45, cardK), lerp(-.05, .12, cardK), lerp(2.4, -1.6, cardK)], w: 1, yaw: lerp(0, -.3, cardK), roll: lerp(0, .05, cardK), alpha: clamp(cardK * 3) });
    }
    // (out of the dark: the tally light first, then her light coming up)
    GRADE.bloom = 1; GRADE.vignette = .7; GRADE.grain = .05; GRADE.fade = seg(t, DUR - .9, DUR - .1);
    const g = layer();
    // (out of the dark: the tally light first, then her light coming up)
    const up = easeOut(seg(t, t0 + .25, t0 + .9));
    if (up < 1) { g.fillStyle = `rgb(0 0 0 / ${1 - up})`; g.fillRect(0, 0, W, H); }
    // the tally light, and it stays on
    txt(g, '● ON AIR', 1848, 90, 18, { font: 'mono', col: MEM.TOKI.col, align: 'right', track: .15, alpha: seg(t, t0, t0 + .08) });
    {
      const ws = wordsOf(lineOf('outro.1'));
      // "(And on, and on, and on...)": each "and on" smaller and further back, like a hall of mirrors
      ['and on,', 'and on,', 'and on…'].forEach((s, i) => {
        const ts = ws[i * 2].start, a = seg(t, ts, ts + .3);
        if (a <= 0) return;
        const k = .62 ** i;
        txt(g, s, 140 + i * 90, 420 + i * 120, 150 * k, { font: 'serifI', col: PAL.pearl, alpha: a * (1 - .25 * i) });
      });
    }
    put(g, { gain: 1.05 });
    hideSub(); hideTag();
  }
  // ---------------------------------------------------------------------------------------------------
  // The encore's chorus (C4.1–5), before the broadcast ends
  const X = { RELU: -2.0, TOKI: -.55, ADA: .75, LOGI: 2.0 }, Z = { RELU: 0, TOKI: .5, ADA: .15, LOGI: -.1 };
  const JUMP_TOP = 38;
  // (the fairy take is framed looser than her still: scaled up to match, and lowered to keep her chin where the still's was)
  const FAIRY_K = 1.22, FAIRY_DY = 40;
  const encoreLED = (g, w, h) => { txt(g, '1ST PLACE', w / 2, 250, 140, { font: 'display', col: '#FFD27A', align: 'center' }); txt(g, 'ATTN!', w / 2, 450, 190, { font: 'display', col: '#FFFFFF', align: 'center' }); };
  const EAT = Object.fromEntries(ORDER.map(m => [m, [X[m], .9, Z[m]]]));
  function encoreGroup(t, o = {}) {
    // (o.part: the chorus's dance in unison, as sung in line o.ln)
    if (o.part && SPRITES[`toki_${CHOREO[o.part].set}`]) return chorusDance(o.part, t, o.ln, { at: EAT, reflect: 0, shadow: false, rimK: 1.25, ...(o.dance ?? {}) });
    for (const m of ['LOGI', 'RELU', 'ADA', 'TOKI']) {
      const i = ORDER.indexOf(m), pose = o.pose ?? (m === 'TOKI' ? 'win' : poseAt(t - i * .1, ['wave', 'point', 'dance'], 2, i).pose);
      idol(m, pose, { at: [X[m], .9 + (o.jump?.(i) ?? 0), Z[m]], reflect: 0, shadow: false, rim: MEM[m].glow, rimK: 1.25, beat: o.beat ?? 1, phase: i * .25, flash: o.flash ?? 0 });
    }
  }
  // L1 "We didn't start the scaling": the encore, the trophy up, confetti falling, the LED dedicating the win to the HEADS
  // L1 "We didn't start the scaling": the encore opens on the acceptance: TOKI with the trophy, in tears, thanking the fans. Then the
  // wide encore, and on a fan's phone the win trending.
  function l1(t, P) {
    const tWide = snap(lerp(P.start, P.t2, .5));
    const g = layer();
    if (t < tWide) {
      const k = seg(t, P.start, tWide);
      cam({ pos: [lerp(.1, 0, k), 2.25, lerp(2.3, 2.05, k)], at: [-.1, 2.18, 0], fov: 32 });
      showStage(t, { ocean: .5, ledGain: .4, ledStamp: 'encore1', led: encoreLED });
      // (hugging the trophy in tears, wiping her eyes: a Grok Imagine take, cut at the waist)
      if (SPRITES.toki_tears) dancer('TOKI', 'toki_tears', t, { at: [.08, 1.45, .4], h: 1.953, crop: [0, 0, 1, .608], fadeB: .12, t0: P.start, from: 0, rim: MEM.TOKI.glow, rimK: 1.2, shadow: false, facing: 0, light: '#F4EEF6', shade: '#9A8CB6' });
      else figure('toki_win', { at: [.08, 1.45, .4], h: 1.2, uv: [0, 0, 1, .64], fadeB: .12, anchor: [.5, 1], rim: MEM.TOKI.glow, rimK: 1.2, shadow: false, beat: .3, facing: 0 });
      particles('fall', { n: 200, a: [0, 3, .5], b: [2, 1.5, 1], c: [.5], size: .025, cols: ['#FFD27A', '#FFFFFF'], shape: 'chip', gain: 1 });
      // her acceptance, subtitled as the broadcast does
      const sk = seg(t, P.start + .15, P.start + .35);
      const band = g.createLinearGradient(0, 700, 0, 1080); band.addColorStop(0, 'rgb(3 2 8 / 0)'); band.addColorStop(.4, 'rgb(3 2 8 / .72)'); band.addColorStop(1, 'rgb(3 2 8 / .9)'); g.fillStyle = band; g.fillRect(0, 700, W, 380);
      g.save(); g.globalAlpha = sk;
      g.fillStyle = MEM.TOKI.col; g.beginPath(); g.roundRect(660, 812, 120, 40, 20); g.fill();
      txt(g, 'TOKI', 720, 840, 20, { font: 'display', col: '#FFFFFF', align: 'center' });
      txt(g, '“Thank you, HEADS! ♥”', 960, 910, 62, { font: 'uiB', col: '#FFFFFF', align: 'center', shadow: ['rgb(0 0 0 / .8)', 18] });
      g.restore();
      GRADE.flash = .6 * Math.exp(-(t - P.start) * 10);
    } else {
      const k = seg(t, tWide, P.t2);
      cam({ pos: [lerp(-1.2, .4, easeInOut(k)), 2.3, lerp(9.2, 8.6, k)], at: [0, 1.9, 0], fov: 36 });
      showStage(t, { ledStamp: 'encore1', led: encoreLED });
      encoreGroup(t, { part: 'hook', ln: L(1) });
      particles('fall', { n: 500, a: [0, 4, 0], b: [7, 3, 3], c: [.6], size: .05, cols: ['#FFD27A', '#FFFFFF', MEM.TOKI.glow, MEM.RELU.glow], shape: 'chip', gain: 1 });
      trending(g, t, tWide);
      GRADE.flash = .5 * Math.exp(-(t - tWide) * 12);
    }
    if (t >= tWide) { const band = g.createLinearGradient(0, 860, 0, 1080); band.addColorStop(0, 'rgb(3 2 8 / 0)'); band.addColorStop(.5, 'rgb(3 2 8 / .7)'); band.addColorStop(1, 'rgb(3 2 8 / .85)'); g.fillStyle = band; g.fillRect(0, 860, W, 220); }
    lyric(g, L(1), t, { markup: 'WE DIDN’T START THE *SCALING*', x: 960, y: 1010, align: 'center', size: 58, accent: '#FFD27A', anim: 'rise', shadow: ['rgb(0 0 0 / .7)', 20] });
    put(g, { gain: 1.05 });
    hideSub();
  }
  // a fan's phone, the trending list: the win at #1
  function trending(g, t, t0) {
    const k = easeOut5(seg(t, t0 + .1, t0 + .45)), x = 1500, y = 150 + (1 - k) * 900, w = 330, h = 560;
    g.save();
    g.fillStyle = '#0E0C16'; g.beginPath(); g.roundRect(x, y, w, h, 40); g.fill();
    g.strokeStyle = 'rgb(244 240 250 / .35)'; g.lineWidth = 4; g.stroke();
    txt(g, 'Trending', x + 30, y + 80, 30, { font: 'uiB', col: PAL.pearl });
    [['#ATTN_1stWin', '1.2M posts', true], ['#MUSICCURVE', '410K posts'], ['#WeDidntStartTheScaling', '388K posts'], ['#HEADS', '97K posts']].forEach(([tag, n, top], i) => {
      const yy = y + 150 + i * 96;
      txt(g, `${i + 1}`, x + 30, yy, 22, { font: 'mono', col: PAL.dim });
      txt(g, tag, x + 62, yy, top ? 28 : 24, { font: 'uiB', col: top ? '#FFD27A' : PAL.pearl, maxW: w - 90 });
      txt(g, n, x + 62, yy + 32, 18, { font: 'ui', col: PAL.dim });
    });
    g.restore();
  }
  // L2 "It was always training, and the curves kept gaining,": the video's photocards fly past on the beat, back to the first teaser
  const MONTAGE = [
    ['m-toki', { pic: 'toki_concept', name: 'TOKI', sub: 'CONCEPT PHOTO', col: MEM.TOKI.col }], ['m-relu', { pic: 'relu_concept', name: 'RELU', sub: 'CONCEPT PHOTO', col: MEM.RELU.col }],
    ['hinton', { pic: 'card_hinton', name: 'GEOFFREY HINTON', sub: 'NOBEL PRIZE IN PHYSICS · 2024', col: MEM.LOGI.col }], ['m-ada', { pic: 'ada_concept', name: 'ADA', sub: 'CONCEPT PHOTO', col: MEM.ADA.col }],
    ['demis', { pic: 'card_demis', name: 'DEMIS HASSABIS', sub: 'NOBEL PRIZE IN CHEMISTRY · 2024', col: MEM.LOGI.col }], ['m-logi', { pic: 'logi_concept', name: 'LOGI', sub: 'CONCEPT PHOTO', col: MEM.LOGI.col }],
    ['m-clawd', { pic: 'clawd_fan', name: 'CLAWD', sub: 'HEADS · NO. 1 FAN', col: '#D97757' }], ['m-win', { pic: 'toki_win', name: 'ATTN!', sub: '1ST WIN · MUSIC CURVE', col: '#FFD27A' }],
  ];
  function l2(t, P) {
    const b = (t - P.t2) / beatLen();
    cam({ pos: [Math.sin(t * .5) * .15, 1.3, 3.2], at: [0, 1.25, -4], fov: 38 });
    stage({ accent: PAL.pearl, at: [0, 0, -3], ring: 0, columns: 6, glow: .18 });
    // a corridor of photocards, left and right, rushing past as the camera flies down it; each card flips round to face us on its beat
    const n = Math.floor(b);
    for (let j = 7; j >= 0; j--) {
      const i = n + j - 2, f = frac(b), z = -(j - f) * 2.1 + 1.2;
      if (i < 0 || z > 3) continue;
      const [key, o] = MONTAGE[i % MONTAGE.length], side = i % 2 ? 1 : -1;
      const turn = easeOut5(clamp((t - (P.t2 + (i - 1) * beatLen())) / .25));
      photocard(key, { ...o, at: [side * 1.05, 1.25, z], w: 1.25, yaw: side * lerp(-1.4, -.45, turn), alpha: clamp((z + 14) / 3) });
    }
    const g = layer();
    const band = g.createLinearGradient(0, 780, 0, 1080); band.addColorStop(0, 'rgb(3 2 8 / 0)'); band.addColorStop(.5, 'rgb(3 2 8 / .72)'); band.addColorStop(1, 'rgb(3 2 8 / .88)'); g.fillStyle = band; g.fillRect(0, 780, W, 300);
    lyric(g, L(2), t, { markup: '_It_ _was_ ALWAYS *TRAINING,* / _and_ _the_ CURVES *KEPT* *GAINING,*', x: 960, y: 945, align: 'center', size: 58, italic: 'serifI', accent: MEM.TOKI.col, anim: 'rise', maxW: 1500 });
    put(g, { gain: 1.05 });
    hideSub();
  }
  // L3 "We didn't start the scaling": all four jump; at the top of the jump, on "scaling", the frame freezes into a photograph
  function l3(t, P) {
    const tF = Wd(3, 4).start, frozen = t >= tF, tt = frozen ? tF : t;
    cam({ pos: [0, 2.2, 7.6], at: [0, 1.9, 0], fov: 36 });
    showStage(tt, { ledStamp: 'encore1', led: encoreLED });
    const up = i => { const a = tt - P.t3 - i * .04, T0 = tF - P.t3; return Math.max(0, Math.sin(clamp(a / (T0 * 1.25)) * Math.PI)) * .55; };
    // (the jump from the chorus's last move, its top on "scaling", where the frame freezes)
    if (SPRITES.toki_uC) unison('uC', tt, { at: EAT, t0: tF, from: JUMP_TOP, reflect: 0, shadow: false, rimK: 1.25 });
    else encoreGroup(tt, { pose: 'win', jump: up, beat: frozen ? 0 : 1 });
    particles('fall', { n: 500, a: [0, 4, 0], b: [7, 3, 3], c: [.6], size: .05, cols: ['#FFD27A', '#FFFFFF', MEM.TOKI.glow, MEM.RELU.glow], shape: 'chip', gain: 1, t: tt });
    const g = layer();
    if (frozen) {
      const k = easeOut5(seg(t, tF, tF + .2));
      g.strokeStyle = '#FFFFFF'; g.lineWidth = lerp(0, 36, k); g.strokeRect(0, 0, W, H);
      txt(g, 'ATTN! · 1ST WIN', 90, 1010, 28, { font: 'wide', col: PAL.text, track: .3, alpha: k });
      GRADE.sat = lerp(1, .85, k);
      GRADE.flash = .8 * Math.exp(-(t - tF) * 14);
    }
    lyric(g, L(3), t, { markup: 'WE DIDN’T START THE *SCALING*', x: 960, y: 960, align: 'center', size: 84, accent: '#FFD27A', anim: 'slam', shadow: ['rgb(0 0 0 / .6)', 20] });
    put(g, { gain: 1.05 });
    hideSub();
  }
  // L4 "Now we swear we'll try to pace it — but we'd rather race it!": the video's own player: on "pace it" it drops to 0.5× and the
  // stage slows to a crawl; on "race it" it jumps to 2× and everything races
  function l4(t, P) {
    const tPace = Wd(4, 6).start, tRace = Wd(4, 12).start;
    // the scene's own clock: normal, then half speed from "pace", then double speed from "race"
    const sc = t < tPace ? t : t < tRace ? tPace + (t - tPace) * .5 : tPace + (tRace - tPace) * .5 + (t - tRace) * 2;
    const speed = t < tPace ? 1 : t < tRace ? .5 : 2;
    const k = seg(t, P.t4, P.t5);
    cam({ pos: [Math.sin(sc * .6) * 1.4, 2.2, lerp(8.8, 7.6, k)], at: [0, 1.9, 0], fov: 36 });
    showStage(sc, { ledStamp: `race${speed}`, led: (g, w, h) => txt(g, speed === .5 ? 'PACE' : speed === 2 ? 'RACE' : 'ENCORE', w / 2, 400, 300, { font: 'display', col: speed === 2 ? '#FFD27A' : '#FFFFFF', align: 'center' }) });
    // (the dance runs on the scene's clock: half speed, then double)
    if (SPRITES.toki_uT) encoreGroup(sc, { part: 'training', ln: L(4) });
    else for (const m of ['LOGI', 'RELU', 'ADA', 'TOKI']) {
      const i = ORDER.indexOf(m), P2 = poseAt(sc - i * .1, ['point', 'dance', 'wave'], speed === 2 ? 1 : 2, i);
      idol(m, P2.pose, { at: [X[m], .9, Z[m]], reflect: 0, shadow: false, rim: MEM[m].glow, rimK: 1.25, phase: i * .25, flash: P2.flash });
    }
    particles('fall', { n: 500, a: [0, 4, 0], b: [7, 3, 3], c: [.6], size: .05, cols: ['#FFD27A', '#FFFFFF', MEM.TOKI.glow, MEM.RELU.glow], shape: 'chip', gain: 1, t: sc });
    if (speed === 2) { for (let i = 0; i < 14; i++) { const y = hash(i) * 2.8 + .3; plane(TX.white, { at: [((sc * 9 + i * 1.7) % 14) - 7, y, 2 + hash(i + 3) * 2], w: 1.6, h: .012, anchor: [.5, .5], facing: 'screen', blend: 'add', gain: .8, grid: false }); } }
    const g = layer();
    // the player's controls
    g.fillStyle = 'rgb(0 0 0 / .55)'; g.fillRect(0, 960, W, 120);
    g.fillStyle = 'rgb(255 255 255 / .3)'; g.fillRect(60, 990, 1800, 5);
    g.fillStyle = MEM.TOKI.col; g.fillRect(60, 990, 1800 * (t / DUR), 5);
    txt(g, '❚❚', 70, 1052, 30, { font: 'ui', col: '#FFFFFF' });
    txt(g, `${Math.floor(t / 60)}:${String(Math.floor(t % 60)).padStart(2, '0')} / ${Math.floor(DUR / 60)}:${String(Math.floor(DUR % 60)).padStart(2, '0')}`, 140, 1050, 24, { font: 'mono', col: '#FFFFFF' });
    const chip = speed === 1 ? '1×' : speed === .5 ? '0.5×' : '2×', ck = speed === 1 ? 0 : backOut(seg(t, speed === .5 ? tPace : tRace, (speed === .5 ? tPace : tRace) + .2), 2.4);
    g.save(); g.translate(1760, 1040); g.scale(1 + ck * .3, 1 + ck * .3);
    g.fillStyle = speed === 1 ? 'rgb(255 255 255 / .2)' : speed === .5 ? MEM.RELU.col : '#FFD27A'; g.beginPath(); g.roundRect(-70, -30, 140, 44, 22); g.fill();
    txt(g, chip, 0, 2, 26, { font: 'uiB', col: speed === 1 ? '#FFFFFF' : '#06050B', align: 'center' });
    g.restore();
    const band = g.createLinearGradient(0, 780, 0, 1080); band.addColorStop(0, 'rgb(3 2 8 / 0)'); band.addColorStop(.5, 'rgb(3 2 8 / .72)'); band.addColorStop(1, 'rgb(3 2 8 / .88)'); g.fillStyle = band; g.fillRect(0, 780, W, 300);
    lyric(g, L(4), t, { markup: 'NOW WE SWEAR WE’LL TRY TO *PACE* IT — / _but_ _we’d_ _rather_ *RACE* *IT!*', x: 960, y: 880, align: 'center', size: 58, italic: 'serifI', accent: speed === 2 ? '#FFD27A' : MEM.RELU.col, anim: 'rise', maxW: 1750, shadow: ['rgb(0 0 0 / .6)', 20] });
    put(g, { gain: 1.05 });
    GRADE.sat = speed === .5 ? .7 : 1; GRADE.flash = t >= tRace ? .6 * Math.exp(-(t - tRace) * 10) : 0;
    hideSub(); hideTag();
  }
  // L5 "We didn't start the scaling": the widest shot of the video: the whole hall, cannons from both sides, the ocean waving
  function l5(t, P) {
    const k = seg(t, P.t5, P.t6);
    cam({ pos: [lerp(3, -2, easeInOut(k)), lerp(4.5, 3.4, k), lerp(14, 12, k)], at: [0, 1.8, 0], fov: 38 });
    showStage(t, { ledStamp: 'encore1', led: encoreLED, ledGain: 1.3 });
    encoreGroup(t, { part: 'hook', ln: L(5) });
    const t0 = snap(P.t5);
    for (const side of [-1, 1]) particles('burst', { n: 700, a: [side * 5, 1, 1], b: [t0, 11, 3.5, 3], c: [-side * .5, 1, .1, .45], size: .06, cols: ORDER.map(m => MEM[m].col), shape: 'chip', gain: 1 });
    particles('burst', { n: 900, a: [0, 1, -3], b: [snap(Wd(5, 4).start), 7, 2, 2.5], c: [0, 1, .2, .5], size: .05, cols: ['#FFD27A', '#FFFFFF'], shape: 'star', gain: 1.3 });
    const g = layer();
    const band = g.createLinearGradient(0, 780, 0, 1080); band.addColorStop(0, 'rgb(3 2 8 / 0)'); band.addColorStop(.5, 'rgb(3 2 8 / .72)'); band.addColorStop(1, 'rgb(3 2 8 / .88)'); g.fillStyle = band; g.fillRect(0, 780, W, 300);
    lyric(g, L(5), t, { markup: 'WE DIDN’T START THE *SCALING*', x: 960, y: 990, align: 'center', size: 90, accent: '#FFD27A', anim: 'slam', shadow: ['rgb(0 0 0 / .6)', 20] });
    put(g, { gain: 1.08 });
    GRADE.flash = .7 * Math.exp(-(t - P.t5) * 10);
    hideSub();
  }
  const planC4 = () => ({ start: cutOf('C4').start, t2: Wd(2, 0).start - .04, t3: Wd(3, 0).start - .04, t4: Wd(4, 0).start - .04, t5: Wd(5, 0).start - .04, t6: Wd(6, 0).start - .04 });

  // The finale runs from "But when we log off" to the end of the song, across the chorus window and the outro's.
  const shot = (p, lt, d, t) => {
    const P = planC4();
    if (t >= P.t6) return finale(t);
    if (t < P.t2) return l1(t, P);
    if (t < P.t3) return l2(t, P);
    if (t < P.t4) return l3(t, P);
    if (t < P.t5) return l4(t, P);
    return l5(t, P);
  };
  section('C4', shot);
  section('outro', shot);
})();
