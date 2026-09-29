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
// ---- styles/demoscene/audio.js ----
// audio.js: this take's sound, measured once (tools: numpy over music/suno/eurodance-2.vocals.wav and the mix), 50 values a second.
// VOX_RMS: the vocal stem's loudness (square-rooted, 0..255); VOX_NOTE: its pitch as a MIDI note (0 where unvoiced);
// MIX_LOW: the mix's low end (kick and bass, square-rooted, 0..255). Read them with vox(t), voxNote(t) and lowEnd(t) (kit.js).
const AUDIO_FPS = 50;
const VOX_RMS = Uint8Array.from(atob('BgYFBAQEBAQFFkdWVU1CQD03My1CeI+CY11dXFpTRm2UloSDfXR3dGFPeJmTkZ+dmZWRhZTI4NGwq7HCzL+qkrfYzcDNycC+vqmIjZuturGajIOBhsHh1sTExsW9o395kratgXuHjIN/fnuRoK69saCenbWwk5eTjJGXmJiTkqK7z8qzsra4urq4pqCnkXh/eXV2c25ufX2HmqShlJWZlIR6gHZ6e4CHiZKWkp+zsJ6gpqOXjpaNeGtYXVxRTk5OU1BHSk1kcWlTV3BwXE9QVniMh4CJmaGpsLGmnZ+oqo2Ch4F5aFpXU1BRU1hSQ0BDTmRkUEZTWlJERVNVVmRsbnN2dX+Hgn55f4yAZmJkW0g8PT02LSwvLiomJTFHSjknJickHyEnLjAwMC4qJCQ3R0U0LzxJS0xFMjg0LiwiISAkKSUfMUVYaHNrUWJnfbDJysC8xsbGx8LAwMW+qZ+qt87ZyMjIqaa6xM3OxsDBxsS9sKGgpaelt8Ozpaqwt7u7uLCwxsm6s7Kuvb+ptcvGsaamtr+wrrmphZ+xtL61sLO1v8CvjHhweXZdVEpSVFmVvsrDt664tY5kUGmCg2xNR0ZEPDaDrK2qvLuzsaquubq2sq2pq7K0rqShrby9ury7v721tLWqkouMj5eepKOhpZuRo6mkmpWamZ6nnZGdo52Tj4qGlaKfpKefqa+trKWnp5uPjJKcnZqTjY6Hhp6moKGZlqCpsKublZWRlaCYhI2Vk5uinp+kpJeUnpeDdnZ6fn99f4N9bF1RS1qRyd/awZ6qwsS5sqyxqJartquWjqSztbS3trm4taefp6OTenRsUHeeqKm1u7q9xLWfwcapj4OOlYdTVY/GzLSuubeqsLe2sLC6x8a5r5l3cICyw728srbJyLSpl4mgpKapm35SSk+r2+DVzb6sj2xgcpa8wLm8qZaGZ3mou7zDx8XGv7y4qq+ol46Kh3VeUVVfX15hdHlvZVBKS0p9k46Eh4mKj4FaQ0uGs8nEv8LHwrzM19TCsbGywtDUyKCs1+DUyr2/zMPCwLi/vbu6rquzt6+Zh3t2foWJm56Wl5OJjJ2ZhHFjYF9fYaPBxsGyqqy0va+coaGZm6OWiIuFdmKNtberqrG6tameoKWRcHh0V05QUVSBqLGtsLO5vbuuopeOl5SGbFJITlVUdZizs6mvtbeypJyPcnaDfmNHREFAXZCts7Goqrm8rJ6bk5KRkoJbTk5LTFp6jZeosrCom46WmoyTmI6ShE1WXVttd5mxr73Kx8vGx9LGuLq4ubixoYuTkn6Aioh/foeJi46HjJukr7awqqWmq6qsp5+sr6uurK6wqaevr5+Qko2SiWlnamp4gYKDdGRmXl1paWt7fnZuZl1hZHmMhm9eXldSUEpPXWBebnp9e4F4aWdVRztFU1NDToCSmKWsrKWaoKOKY0VEREBTa3RrYVtSXGd0eoGUn6CkoZGBb2NaWlRPVlt4jZOPi5Obq7y4q5p/k7LEvqeptrKjhnZ/hoVuTUhKQC4lHyAhHxsYHSAhIyMiJCYpMDs7LyQhHx4iIx8bGRIODQsKCgkJCQkJCQkHBwcICQgJCAcHBwYGBgcHBwYGBgYGBgYGBgYGBgYFBgYGBgYGBgYGBgYGBgYGBgUFBgYFBgYGBgYFBQUFBQUFBQYGBgUFBQUFBQUFBwcGBgYGBgYGBgYGBgYGBQYGBgYGBgYGBgUFBQUFBQUFBgYGBQYGBgUFBQUGBgYGBQUFBQUGBgYGBgYGBgYGBgcHBwYGBgYGBgYGBgYGBgYGBwgICAcHBwcGBgYGBgYGBgYGBgUGBgYGBgYGCAcGBgYGBgcIDyJdlailoqSrqqy0v8C2qaaprq+vsLa2q6itraurp5ydoKGooYqJi42VlZSWi4CLl6KknJugop+blpORlYmFgmFSYXqKlqCgm5ygoaSlnYxuSUBBRklGRURLcImSmp+jm5ajno6RiW5pZ1tJMjRvrK2HfomdoqKSf3Njc3dpWkcuLy8pJiUoOUdQVFZaWVu40biNUSclKERfgKu1rqaNjpKCgYmFgJCblZCaoqSjoa22p4NZLygnK1mMsKFLLjRXi6itqJmFiI2Vn6WwsKKjpZBtcW9bU1RUUkd8nrC2rqqvqqahorCzqp+YnKasr66wr66zsKemsbSbd3t9mK6qmYVqRmuMm6OqrqeaimlEOGqrx8CngUcuKSovRqG9urGqqKejoaOjm4iQnZJ8a11OhbXQ0MCzrJ6anYZPT3qhqphzRUFCOy1MqbupkE4wLSspJ3OfnW0wiaWxvLafl5aDbHOcp62unZ2mrqalqaS0t66sqKiinaKkoZydn5mWnp+Ykn9cPEBEWY63x8C4sp2Ih4yLorq0o5FyZn6Zsb3Av7iyr6uqqaWclaewp6CNZ2eZvMXDvKyloINRPjc8UHV6XD9hjaiztbGonqKroI2XkW06Yn2CpbekgWJmhod/hX6LmZuejFM1Li+Eqre1pZB5VC82QE+OtLqvpZ2alpKMeVhgcn2EgYSEa3DE0764q6CamIx3msLOs5OisK6ej5KLdmNYXFQ/MDhUbn5/cmVYQUVJPTYyaaK0m2U2YJ+6u7+3qKWXhXVVSm14fbW8m4NdNzM6OFmcxs7Fu66amKmnr8rTx8G/tJ9uSD9UkZFOKyo2krbGwaqel4yCfmtAMU1wgIN9bFtAY21ZRTpPk551N0dYb6TJz8rJwauNazchIECQsLu5saqmrq2UbHyjuLetooRPXYS0yc7Jv7mrpaehpbTJx7i4t6JsLygoKWq4y7annZienpuXmJ6eo6qccUMyJSWTsLq8q6OvrZ6amJCFZTVwlKWysaOdnp2XlpOUm5iHeHygvLqdgIF/enl6lbS0jmutwp9verfUwqajpqaYj46Mq66PhoKAe3qBhIWBc3JvVjsyKykpMYSxvbSrpJ2bnpaHtcmzpI9NJiUkJTWy1sq5t66rq6SclaCwtrKroH1EUGR8m7CpnZ2Ul6Kkoaavq56bmJ2klYOPp72/vL20p6KgoJ+nq6WejXaYrKqvuLWWjZmIYjYjGyx3p7apmZOaj2FsiZWkubSosK2jp6iqs7aylFtIRGyNmqLR1r66qKq2ta6QprqYX1phUj4yIiGGztu+r6mwsKesp6OnoJ+lrK2qnXk4c6KyqKGkqK+vqamZbUlAOkOhvrq7vrm3sqimtLeuqaGvvrm9t4pKIigxOoSvtqqjnqaztbizjltPSkdIkbvDwMDCw767uba5uphJMVJyd3BydXR5dFRUnrq5tK+pqrGwq6ywrKuytLa3t77L29S1nImCYT4zJSWTsqFqJm+cra+xtamcoaWqsa+rr7Syp6OkpKmmpKixtbuyoaWgnZaId2NfhsbeybS+w7GCcHaiqJunmG5hq7yto41mOSYleK+7q6KRgn1oXVZCPDcwSXCWnpGMfmCiztbJua6llH1sXmJ9ncfRurS/u7CnqbKys7OuoY5zXV5PWVs7NWJ0dnt2YonM4tbJu62xuryqelZVpruyuLaqqLSxoJ6ms7WwsKyUbVVNl8PGt7/CspdwRChZmriwilFAia2urriqf2lzvtO5srOnknRaUkwxJml8bEYzQ1BcY2NmYkxPmsnJqZyRajwwL1SQt8zQyrycaU82RZu3taJ3PU5TQTQ3kK+zooOCpb3M0si6tLWheqW6sq+lhkw9Pj9AR05DI3mqvsXBsqqwsKSjoqCioJiQhWlWSkJZpb63o5qyu7y3nXhWbZ2/upmnv8fHu6antLy1lV5FOjF0s8a7o3QsJCSFnZ2/yrWaemU9Kz5PlK6qpKqlh2EyLkHB4Mm3uLi9u7asraibp6ecmZeLbVxkal5UWFpgYXKSssrRx77CwcDEwb23tbzCw77Kyriwq5eIpLbArnlkY2NjmcnRx8e+srWhaV1pipV9XFxfXV9cd7nErKqikJits7mvpqudo7a9vbKdk5Kerr61m5uko5qPempsbXR/gYB7aG6vyb+nhGRZVVBRb8DOt729ubuvjV5ZqMbKztPZ4ePQsq+0q5+JYVJPUl9hX5XCwMfZz8rQ0sKsqKiotsTDu7SurLrHyMK7raass7a1sqmkpJ2Zln1hW1taXGpucn9+eXx1bmheYHB1b21dQme80Lqtr62trKmqrsC/k1NAPV+EnKCWqM/azsW8vMG+u8DExdHUw7jH09HCweb58di2pMTa19LS0se3r6WXpqyoqJN4dGVZWW1ybIqisr28w8i/u7GScWJQTFRqcW5pZmh0q8nJyLuqv9DCp6y3yc++wcG0vLOUg7fPw7SstL64p4+Cf4SKi5WYgG+CrsTBuLfEu6+7u6+Uo8bGxMK7vL7DwaeDjJSKZVVVVlVYpdHQvsDNyb2jY1RJSktJSEZHSUpFYazG0NrPwsC0qqOVn6+sprDBys7LyLzFy7i2qrbQx62wvbmxtsHP1dHDsZ+bu8fEzMvAxszBm3mWqKytqZR9aldnrsG+xMPBw8vMxcbV0sTL18SKV1RomL/CvsvEtsLMvaenrqSeqaupqKOam7PQ2MOvvMbAtbe6sKysootjWlhZWWV1d3B7gnp3gJCHZmtxaFNGYnyPnLXP18i8w6x1X2l5m8bUzLOFXlhofJKkxM20tb2wq7O/vsPBtKywtLXLx7KvtcK9tbe/vbO4uLGgjoV2ZWNkXW2So8jYycTFuLvIysHGycTEvLa0ucbN08+6p5V+dnuAem5qnK+mu87FvL62r7CpoaOrqKSsooiEttLV0sLBxsrLx9DX1sC8xL69xM/U1My1ur+tp6ujkn13hYqGhoR9jIyAf4mZlHxxcXZ+f3JnfpWrt7WpqLGooZyShGlVQzw0LSQeUnqxw7yyooZaQzkyLSIbFR0uNTAkJV+HnKmto41nOh4RDg0MCwsRFxYPFVupz8q4r5FlOSIdPZG0tKKLclU5LSZZkrO8tJlsPyIXKHGlvLqhbTkhIihJcqCqmZOJgXFJJhsVEiUyODo5Nzg6QUhqiJaVh21IJBQlKjuRzujo3dvY0c+/p6CgoqSloKWrqbG4qIJYRj0wKjUzHxcYTIiwsZqIiop/hYuQobGzqqazn1MwJm6HkpGOoq6tqqeio6elnZ2UdGNnW0A0MjU8a7LCm00kR4mdjXmApKudlJWenpiAf6uvmp2ijFhGQTUnlL21l5ueoaOJVFmXqZ6cmoA6JEFhZHKRkZajnqKom3hrb0xRfpCOiX1kYpmmlo59gpaeiTApPUdEPjtHk7qzgEdRWUcqKywkJihps8y+sbO4vb6tmZ+mn5F+YE6FqqiEWiYiJDucq5yenqKkmYV6eHNfS1BIMUWMrrWvrKWWnayrm3tPOTo9PDo6OTlpmKOZj3E9FxQjnqidpZiZm4VPMTORxMzCuJtvMRcXN6SvkYVqV2dxd3ubu7eaek0pIS5CTICvspWFhoiIiYWJgWNERkZEfJaIWz1rl5JYP1poYVaNs7ajmZyemIRiSzApbJaPVTWDprm0jFE7IRdBn8fJtZJnXFg2WnmChI+QkqKjjGpUQTUgFhYolrizl4uMhYuHbFBNXoO0waV1NiAbOae3n5FyYp2xramUgoVxQztNZ67DsKWlpZ+PkJukpo5leY+orJ6ajWlTQj+pvqmipaShpaegoKGcnZd7PTc/TWGZrJuQmZmWl5eSe1VmhJWak3xXMEOQytOwl5V4QjcxL2GkycrDuppwaJzJyrWmkXI4WpGsqJqUiX+Hla26vbaRTTlOdY6aoauin6+ztszVy8XAtK2rsbqti21mXVFEMVdcZ6zGxcPFzMK3ubC0rpGNlYhojJqKmLDLx6ebrLepl52ruL2umI17Y1I3fKa9xsCti3mNkZObtMW8vMO7sKu0trm/wMLCvbChkoqQlYuVn5qYnI91Xz+nuqqsqqaYdks2MEV+naObnJqEYDFRzt+5tb2zoIBdeZTQ1qaIcVNcWzwxVLnWz8KxsbGQOSiXxb+jqaahoZ6XsL3Lz7+xqa+sraqmm3VHMjM2OliQsrm3tqqfnaGhn5qJiZGTm5qalXhveYa2vpWBlqCurZ6go6ehk5KEcJCgppJSNDM/TY6vtaiQckw0NUFKTEY6T2lwma2TUyckV4GPiYKdtrOekZympJ+gm3w+Li8scrLIxbqrp6eflpqZoqWana6ym4uLe1xFLzWkxbSTjIuQlJuMWY+4vayioIZNLUGlybqXfElBiJ+LZFVMOC4rl8rfzb28rKmWiY2NkY6AZU1jnbq1mGcwGxEXYIWdoZiZnJmBST8ue6y+uLCro5uNhZSzwKh+Yj1qb1A+OYejur60saOFUlyLqZ12Z3Oisqyol46nq5Jxo7+8rq2uoJeYnaCdlpWSkI99W0ZCOjRZdYaktqeTlpWRi3pdQoKhlHFiSkA+NSMeMcHHi3dXSD4zMCyNr6+lsr68u7q2triypJuWfVFbYF9/rrGLcWlrdGpIUo3J0riom5WRlZeam4RaS1ZZU09JR0hkmLCroaSrrp+SrrWUWEA9PD06NWmtybmXi4duMzEzMZrEuJqww8G1sbGxrI9XUVpVSkxXbKDBuI9oTC4rKSYucbGzjYqTl42NkZObmIqTqK+tsLKwrrCnnJ2ZjJKhrbzEq2k5eIqpx8Wyop2joqKbgFpoeoS4wZJVQEtMcqfK0c3Hs5yOhqOvlmlKPjgtJTCJtcO5r6yjm5eWkpCSlZmcj3F3gYeKjJCNi47J4tTFr4GMt8HCvKCBYVRVWWhzZKPDxrq7v6qkprPCrG2l0MF+TaDMzreoqaCEcYe619XIv7iogFBSWlA8P7DOwrWvrK6urq6rp6Kdna60q6mloZuJfJOel5CTj3tqjMDRztLNwcHN0szPzK2rx8/Nva29y8OmipCrva2AcGhjZWar3OLNw87Ir5BxbJWyo3dkX15fYV9jgoyGj5aRl6KqrbKmgXqHj5ablpGPjYqIgX9/fH+FiH1lVFheXltfYlhLYIqXinFSPzo3MzhypamnrqWcjoNuUl10gZGVlaCinJOSmI6BdVdJRVFkbm58hoWFkp+gr7eyrJeFiIuNkpaWkH1wgISFjpOVnKeikYBzbGJmamdWPDQ0Nj5PV1dbWVNUUEhBRVBbY2ReUUVidXJnZ3eEjJKUnJyHblZFPzpGYYCNhHd5i5qal5WeqqSemJSsu7SsnJ2tnYWMjoWHi52oo5J0X1pSUlBMTE57i4R6kpiGipKZq7W2tKyenZ+Tk5yflYBlTU9RVFRRWWNfbZGkoZ+gnZ2kraqYfHSFk5mXmZ6UfpKpp56cnp+dn6OeiW5dVl1rdG1kZoOYoqGhpaSqsrGbdXSHlJaamp2eimtHOTw/OTI3PDo1QmiAkJOPkpCIc1NLSUA8NS4uLiwpK0x5k5eYmp2nppiNi5WbkH1+iYaEm56Hf42Vm5ufrK6ekouBlJ+opJyllGRmjZ2ampyZn6OVe1FIU1tWRTg3QWuRj3+Ji5ajr7Oys7iynKGloJyDUjw8UXKOlpKVnaKnrLizn5WTlaCqoZGHi56gkIyYoaSdmZ6Zj39kXVFDQ0ZHSkhKV2JqbXBrboqhs6yReFE6NThAeK2vinNwbF5bWmyNpKOko4JMTWuBh4J/i5KMipOcoKGkpKCnqqiglaWtp6CRhIaKlZiWnp+bmI6BcFdSV1VehJSIfZiblZ2coquxtLm7tKahpqmnqKeUfXZ5dm1iYmVfWZWysLa2rrCztLOumIOAiZCRkZGLhqG6uqiirrCuuby5uaqTnaaZnq2xtrmxvcHCy7+1sq6luca7tK6xpH1xnLS4uLu8u6+Jd5y2vMbHtrGysZdjf6S6xsXGzMqxiLXW2tfLtrGurquQZjctLCooMYq8xbOklnVuh5aPm8jXzL65vrq1uLKsn5CLipGZkqvCv72/urW5vLeuqaKkrq2egXB/rMfDtLO2t7m5u8bHtZ6YlIuFjZOSl5ymrrC3xszLwLXFzrN2NXihpY93pLjDysC9trjBvpphpsbJuqyxubazwb60qX5EcnldRTBTmbesiGI1Ih01kLLCxbaqpKGfnaCip73Cv7yhkLbJx8fIqU0sY6/FwL22t6d1SC4jICFMtufqzbmxnJmcg2eJtMrJwb+xiF5VRnClycuhSTVeY01Eiba1k4SChYR4f5OhtLy1raKfpa6wtL29vKt+VEU6Ojd+ssC3raaho6SgnLHS0ryZMzViiIx3kra9qKKytLO0vKddQkmTw9DJxMXHxsjFs4hjot3s2Ma3rKqns7unjqOyztK/vressr+4qKW3va+6wrm3ur2xnLS5oJucq7SefLjAjVg3RL/Utq+yrKajqKijoaatmXKIxtjOwrKjh3ur0NDKyramp5WlvKp8PDM1TKbFu6uloaqnnZ6gnaCimpOWnqSblKazvMXCu7/EwqdtNCk5Z5KrwLuNTUtNTny7z8nPyrapoLPBvbemq7e5sJZ6TywqOG5wR0A6MzJISjQjmNPbz9K/kEJZd4OCrsS1oJqam5ycmZOXmpmcm5ONj5OewdDHvLK2roxwPUCgx7+tsra5t6ecnJyRhIeSjnA5NkFNmLSup626v8C6pLfHtaersrGqo5R9kLfAs7W9wL68wMTLwaWho6emoqaqsKaSm6eiglN+mqHB0ceuo7W/wK+ktcW8sLnEv62nrrG1ubSrqKisp6Wlo6GRbjk1WIegp6rJ19LGrqKkoX4jlcC6kIelt7mvqa2qpaWns7ewq62sn8/o1b+yssbYyq6jopySj35iRzU7Oi06T2Jtd3p0ZXCtx8e0iWqWsre0q7GpekVDr87AqqCalH9POz5HQiscXsng0dHO1Nzc1cm94fHc3N7R0crAwLi3tbKwt7COgId7ea62npygoZ6graqPpLq9vrWwuLmvq7ezqaWemZ6lloaTrLaxqaeeeU1gqtba1NK7nJufpLTL0MfCvL+8vNDRxcvN09bMwrm2tcPPx7e9ztXe3tXb3tbQyruuraCnubSos8fItqursbCmqKiprK+ura6ZfY2QiJGitLq5rJ6MZUJRobWusqyMY3KAjqi6t7Kmmaepm5B/p7ipnJqZhWQvIyA2mcLZ7eTTzL+8u8XMxr66p5CWrMnUyb23t7m6ubWwrp2YrrO0ta2np6q2sKOwt6+ggXTM4tjMtaqjpaelnoVbdJyxsaKLh5uws7bBwL29sZR1XExDjLzT3ePl6uzj18a1lj8tP5a5uLm+uberjV95q7y5u8TBr6OegkYsJkSOucO7tausvMXIycjFr3c1MDJxrburrraxsrewop+cnKOmnZaUjJCVmJqZmaCek4yFiJ2ZlZqdqqaKViEbLn60xbibcUpPZWJPcJ7K1MO6uLi3tKKGh6O919i8rJ6dmIKHmaKfhkQzLyYbI426v6qntr6sfExMmbG2tKalpqSinJyclox7dHB+oaGqxMC3tbO3saGGTWuktZprRTAjHz2JusS9vLSqnZGSlomDoLGkdzcjIDiUpqzHw6mruMfMu5GMr7Knm5ihqKaorquel5+os7eumoO339vOxr/ExL61tbi+vrWto46SnImMv8q8vbu5v8Osfsbg0c66eTIqM6u+vLaIWj0yNDUyMEp6sb+0u766s6mht8C2tMHEubexopu3xb22trW3urqwoqi0t7mym4BdPTt+qK6otLy1qqGenLzDr7a1pJqnpYqWsr69vbi0sKq1ys7HwsPJysjHt52kxtLQzdTW0sq7rJ+fq7Geh4iFg4KJx9rMyNDazKWJg4yal4R9fH19fH15iZWapaepuL2nnaahqamgpaSjpaWlqbjGyMi7sbOqr62jk3uDkJGQiHVprd/fvZ6JeXBrYnHG28XEzsi9tqqLZqnGx9Dc1MG7xr+oqre8pnlkYV5rfZrV3b+1qsbh18S2sLuvlJmkqq2ytrzN0sW2rrC6wcC6tbS4tKKThHRrYGJscnd0cnVzdHh3bmpqbWtmZV5WU5m8y87Hyc3R1ODfxMTLtIpdWW6Imp+71NTZ28TQ5OLS0uDPusLI0Mi8w8LC0dzi2tPY3dXGt5SKgYF5hH5pgZyyvdDV1NbS1tLi4tXh4tDHyMrW297j2LKTh3+CeWhufJXN18rMxM3Z3+HQvr+6s7a3usC4rbbEz9HLyMbEys3Mzse/v7mwzM++1eXWw8fJxr7AxsKrtNXi3s/KzsvBrpGtxci1kXtkZmVbns7h5eLQxtDUuIZsh7i2hGhhXllUUKHIzdHOyczX2NPHtru1rq2rq6upp6e2y8S0usDCwsTNycjQwrK/xcW3kXOx0MzDyMjJ0MWwr73KybGWiXlpWGWmyMfDyNLTxsK/vMLKysbU4Nu/jWiv0NLNxcDE1OPVs7CvqLm7s8XIrJCmxtTS083W5uPe2tbZ3dC1rr/GuMHDoH95jIt4hYuIfn6GfXh7dmlvdXKRwNLJvq6ScmRigKCqt7ukgWRqfomJmK+9t7fFwre1ubu8wL7Fway3tq20wMfDw763s6qyxMrAr6mspZJ+b2+EmZ+9ycfU1NPQzuLhzcvT29nW0tLd2MvT5vDz8eLJxNHWybCbiHdxcGVeb6C4xNPZ2Nne39bLz8jCy8zFvLrBztfSzdvi39nb49/Ksaamo6uzs7Krl42t0+fp3N/m59/Q29fV4d/P1+Dg0sjG1+HZ3MzE2+Pe39PFysvLzcrNzM/X29zVz8LS4t3i4dXPzcfK0tHP0s3Q3t/Vz9LX2NrQwbu9uK+xx83GzMvJzcfIzc/NztHDwMW8usDCvb+7r7XAxMbBwMLEys7Ny87Qy8nFuLG4vLXZ8eHBwM7Eta2vwtXq5dDVzbiZdIKay9jPy9Ld2t7dzay20NbZybbF2d/e2d3TvrubYVRYWFZ0qsSwkKaqtLCbwufp3t3c18/W29nZ19PNyc/c4NO+r7u/srO9xtLYwYuPwc7GycSmlqSlnamzppKZp5dpTE15q7eqmZ23uJNFO5e0t7/JycfOuYix0tC6r626z9rf4uTXtr7Nx9Ha2NXQx83Qx6lrbpqhjIeyvaeim5uvp3E/RYKrtbnN3NW/s9/ov6astLu2mGVBiqWPWYOfwt/g1tfKsqalsqyys4dMQGCnxL67v8a/0N7p6dLRzs3e38/MycrIxsm+qqaosrnEyLempp+JbFG/3+Da0M3KwMHMx8Xc6ODa2drXxqaAR4/B3OXaxcjQuZ3D0cnSx7a4urCYl42Ckqi7wMPHxMfHvr/CvLzFx8PAvb/BxcjR3uPj3NPW0LWjoaSMV7LNw7+9sp15T0RDQj1lsrqflX6EeFNamszj2cfEvbizsp5rhbCslIdeLiIfK4u8ysC0scDNz8rJx76wpautsba5v8K7tLS8ubrEwre+1d7Iqai1w72bXEg8LCU4ueDb0dDT1sWtmXReU0dpfKXQ2dnZ0NDTvYN/2+a/tay4u8nUuYhee6vFtn87QV1qkrTGvLG9wb25xsm8sKqwtri9vbKUqtDGra7AzMS+xsnBu7u+vre8x8rN0dfUy83Qw6yTYbjLvr6tpaGMaUQ8OmO4v4liRzs9PlG32tbJvrKcnp57UFCGoamloq+1rKOgqrrAtKGZk5OVi5u8vaOZoaWnqqu4xsmznr7GuLjHyMXArJ+rv8rIu8PV1tPMt6Sxwbqurcji2MXDv7ink46kqaGnt76+vbmmkZmjrLK7wsPEu62vrqejqq2nnJ+jkqzV3MWhlKmbaVxSlbysh6G+xsTP09fe3dfazaN2hZ/S7968u8DDwtHPsKjO3822sratr7S7vba0trm0onk/YYWepa++wLq+xMK/v7/Dxb6dYF9lal2rw8/VysvQyr64s660tKWjmZOysoqqzsexp6yvqKeuppeyv6yknY+SjZKPrLmvrquzw8nAwN/q5MuHMh0laZurrcfTy8fBxMS6u73Bxc3OsMDNpa3d59nO1OLVtpCBnszYzMembGVdcI2cxs68w8zIxrGQvuHeybiw2OfImJe/7PHVxLGoxtHBusexa09IP6LU6u7r6ena0Nzk6Onm4NnQwpxfNTuIn5eNrtHKq6WPV2uXrtjw6uHWwqWAWbTf5NO6srK7ysrAvLu7vLWbblBPUEFjxOPf5+XRs39MV2h/ssewpbjK3uv19fDm2tfc4N/b29XNz9XLqn5diZWHh87v4cm/r5N6XUeAu8GRRT9LT0xGRVCSvMbQ1LBhOSiLxNDAq4NPeq6/sq7X3sHDxbqvq5mCn5dXc5Sio8Te1sXJxrOsr7e9urq4vcW2pKOhlH5kOjrN8u/k3uv27s6mvbhcLCg+lcPPzsKegYWCf4q+ztLq5bhySDwqJSQiL57T28nErnVQT0xgdsXhxavC4ObY0dDPz8vN1cq7t7q7sa2heUs+QENJV2yy2dS3p5yy0NvIrc7WwLi8xMrEomV5sLqwvcCrfj80VKTOw4VHKh8dInGr29WkraZ4VU1MXMTWo0AeFRkqbKjb48S2wdDc29nZ2dbNwrq2urizqqDP4drWy7mKPi8zns/avHlLTldPOETM5s+/vb7DrmM5TnvG6eTJtKmFSTY6jdTcxs/Y4uXe3NbPycnHwbq4ubm1t7etqqelp6iqpYxYLyU7bY6ZmqeqoJiMkqextLWtnJmeoqKYlJGMelJOj7u8pamon6Kkpqypqqynpqiqp6WloaOnoZF3W0VBQD5AQkRLUFVXWFlWU09LRkA+Ozg0MTAwNDQ0Nzs+RENDTVFUWFxka2luc3NzfIKFiY6SlpycnKGoqKirqaitu8Dc6+bf0M3TytXh29HL1tnSz9TPz9DBq6y7zLqJcXF0c4rR8PDx7ejoz5l0lLy9mXZsZmdoZGN/l6Gqt7zD0OLVp6a0rqSrs7K2w8XD0dbX0cjQ2eHh08bLztPUzsjArazG0c7Ny8GthWBbl9727uPa18y3kGya0e3w4N/g6/XaubrHx76gdGZpb3SHss/T1+LXxsTIzdTS0dPFxsvGxrqrvcPS39rX3uPe19XUzsbCyMjDurS6u6ycoqimmZympa+6ua+lnJugp6CXz9i2s73N1NDLzszGycGieW1xlKumy+Ha2eDo8PHn5u/j2tXQ7vT09ObV0dnX5+7j5Ojw8dOso5eMj5ebjYeevdXp7d3Y5uTJytLf8PDfyt/v7/Xy3dPCnYZ4g4J4gZPR49HNvsjT3+HTybKlprK4ucC/p6XM2dzk4uLn28PK1+Pk0tDZ3NPDt7Da7dnEwsG+w8Kzor7V2NbRxcXNybSarszZ0a1xX1hRXL3j5NbQ2NjHoHqKxtm5eVlYVFJMaMjXx7+7xby+xMDAx8/R0NDOzdDX1dvax8PI1d7Yzb26ycalclJRVl1ln83e4+7o5eXZ18rDyMfEwbKOa253fKHH09DR0Nng3NTDw9jaxp5uXE1jn8zTxb2ztLCTblhMUIaqwMvS2tzQxsPPy7i+oGpmZFZVeJmyurOio7KqnKi3uK+pkWZnYE85P1tvenVvfI6Wl7bW18vHx7+kh5SyuLS7wMa4t8nHw8/t6dLc4ODj3tzezbWzvMHMyr28w9HVysLK2t7W0dPU0s/g4+Dd0sqnfpq7y8fF1tTT39/h39fVz8zV2tfS2+TezMTK0dPNxLu7y9bLwNPZ1c/Bw8K0nYNkXFpcX2BhjbzLwM3Wx83QwMvT0M/U4erjzL+6urGop6qvrq+zp4mbvL6+v7m7tq6gepixu8KzjmZbWVaYvtDLub/JzMytWmqRpqGCUUlKS0tmkq25wMjPztLT0trb19jY19PNyMXR29XR1Nrf3d3b2dvb1si6saKsxtba19TR1Nre28/K1NPU0cnT1NHS0dXY1Mi+wcbGxL21tbW3t7m6vL+7s7G7ys3LzNTVzNXb1NTNu7/Q1dTUzsvOzsrFzt3i3NLT19PS18+/ws/Z2NTa4d3I1efo6vn/8Ofs7+XKwdbU3N/j5czDx7/H0Me+wMjFvb20uMzPzs3DxcPLzs7a2cOWg7G6t77CzNHRzc7W0MHBso1vcWplaY6jopeVo6qkoaiyq5mXlqzU4trNydnZzcS5u7m+wb7FzbBkSFJcWEZAhdXdvruffIWTj4Caz9/a0sbDuru9usDFvrnBwrionLjHv8jNyMW9s7i/2OPSxcTDwbqyra24trS4ubextLi6tbO1tri0sbC9w7LAyr+7wMG3uri1vbu1s7S5vbzJybW4v7m7xM3OwcTNzsy9vsfGv8PMyrq5xr+5u7y4t8TKwLnGyMPHw7/N1r+l1+nbzcrO0NHX0MbV5ejjzsXV1M7MycnY4drRy8rKzM/NxsbO0dHRz8Wpkpyqo5ultb3AxcO6vMTHysjM19/j1MPEvcHMz9Xb2M7GytDT1NDO09fZ1s/GvsLKzcfJ0NTT0M3P0czBxtbZzLy4tLK/zdPQzc/PyMzY1s7QztDPvsTOx8rOztLX3d3Y0c3P0dbe4NvZ0srIw8nS1Nfd3+Dc1dXTz9PXzcfO0NHJubbD0dbX2dXS2NLP2djV1tfg3s7Ausve4NbQ1tjQz9bX1tfY1c7MwsHHwLS2xtLGtsjOz8/L0Njc2dLZ2Mm+vMLFwsvUzsS8vsnPz8zMztPY1Mq8rrC6xMzS1M7JyszMztLS19jZxKaxqqmwuMXNwLnGx83TzcPD0dLPwrm+uru7v764usHCwb+3tbu0tsG/rJefqa61t7rAs7TU07y6vsvR0sqqo7q6r6uprru9sZiUr7y2sbS9vLKegZiopqWwt7m8vKWUqbjGxbq+xr2rmZmloqOor7e5v7y3wLq7yMTDxbq6sZagpZ+xu7vDtZOdsryvmqSpqKqima+6r6yrusrHuKCfrrqzk6K7wsW1kperq6y2vsLCv6iktLW5u77I0dPApqmtqKGosr3Cwr+0tby4u8C/wsHAu6inqam2vsDGyrWbpra/uK6vsba7uaqfpaquu8jKw6ybprC0ppu2wrmsk4meoZ+vvb/Ay7eYtruzsLC6wMG2m6CztbCoscLHyMfFztG/x8/H1dnZ1K+EfnVvdXB5nrCusbvAvrq4vruroay6vLi+zM/Dwc3MwL3Fv7vCwsXDtqenpbC5ubivqJmrtKuvvMDK0cu+pKrGysjDxcvV2Me6uMDX49LAxcrW0rGpuLq5ycrAv7Gqtr7Fxb2/xMKzmpCZp7TAurG8w7GWpL3CurOus7WqqaiamqCnr7O1rpiesru/v8DAvb2zlY+hoaCsrrC5urm2sKert7Wxt7i8wbalq6uqtrarqa+tp6WoqKusrbGxrKKdnp+kpaapsLe6r52anJaPnamomoN5gYF6d3Z7fXlvXktAODAvLScgGRMSExUWFBMSEQ4KCQoMDQ4QERIRDAkICQsMDAwODgwKCQkKCwoICAoLCgkJCgsMDQ0MDRxks9HOyNDUxry/wL69t7e5srW7wcbEzM3Dvbq2t7vDxr2sttXj4t7e39jg5t7Yz8zR08q/yM3N1tLLw8DNzs7Pz8W+x9LSzM7Go3x6ho2Rk5CPin1yZ2NwenNudXpxeXllXE9PXmNgYl9YU05RUk5JT1FMSEA1MjI0Nzg2My4gGBgbHR8fIB8aGBQSEhUZGhsbGzuf09G6vLq3t8DIw7W1vsDBxcnKyci9tre0trCwvcC8taarub6/y9PQzc+/rLnBwb67uru6rq3Ax72ssbi6vb63s7q3tquiqq+1saamq62qqa2poKqvrK6tqaCeoqqxrqSho5+qs6abpKynpqypoKCoq6qmnpueoaSrq6Sgp6yppZ6UkpeWlpmYmZ+jpKOfnJuamZqWj4yQkpKSjYN4cGRUR0RLUVFORj07Oz5EREE/PDo4Njc7Pj89'), c => c.charCodeAt(0));
const VOX_NOTE = Uint8Array.from(atob('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'), c => c.charCodeAt(0));
const MIX_LOW = Uint8Array.from(atob('BQICAQEBAQEBGi0sKCEfHhoZFxM1SEQvKCMmJiQfGkhNPTQvKSkqKBsXS0gxKi0rLTAvJmNyY0pAMS40MzMwPFI2LDA0LjAwLS4qMEpTVDYnISEkNkhKODY3Oz47KSgjNkguKSYsLCw5UFJkfpymu+Tn482umYN/d4F1c1dWem5eZFtnX2BhYFdlbHleY2lRRl9MQ1JkcVldWVZZV1FMUWJWUlJOTlJMTUdCS15XVkxRSkpCRkpXXl1XV1JMS0VDQF1bXV1gXFxcXllWUldaWVlZWVddXFVfVVRPVVRXUEtVVVxbVFBRU09MSkk8R1BMSUlLUFJSUV5RSUtZW0tJUk1JVlpYTkpJSktCQk5VTUZIRkpEQUE+TFdYW1NPU1ZdU1RVWVpbWVdUUU9LQVZaWFJRTU1MQkA+S01MTExMTUhMSkxaVVFNTE5PTE8/TVBTVFRUWFRUUU5LUU9NTUxLTFFMRlJPTFNTUFBLSkpLU1RQVVBXUVNLUlBSVlZUUVVPTEVMUU9SUUhPUEpCTlNMTUtLTUxIQz8+QEtJRklLRklDRD4+RklETkNEPD4+PkJFUUxDQkNAQD04OkhHSEhARENFPT5MWk9PV1dcVllZVGRlcm9xc3V5b2BbVFxjXl9wbGdhW09cZGtpdHV7cmlmXVxeZWVmbGRfYlpcbmpycXZ9dmtpW15cYWNoZ1xeZl5XXnJxe32AgX15bFhgXFpfYl1dalxcYWhoaW1yc3J7bGJiZmltaWxxa2VrXmJsb25ze3h4fXVmaGhucW99sJyMZ2VlcmlmaW5rYGdiZm90dHF7coWKjXhzZlldaWZoY2RfTGBlX1heW2JfVVdfYmRlY3Z9i11ja5Oaa1lVXl9qa2VdVFhaXl1cW1xlVnl5WldZUlNWVk5UVFFSU1ZZWFhZXEuFWlROUE5TUVJSVFhpW2BSUVhaUkdDSFFQUU5WUVhRV05JXF5eV1ldYVNHQ1VpXGdhYl5gXlZRXGVlZmhgZGRtUkZXX1dST1dTWExTRUtQVlVbVl1TUEtKTlNWV1FUVFVZSlJWVlhVV1ZYV05IUmumq+Ha08CzvaafjXaEdoiJaHubmn9rYXKPf4N4gGeBeYFnZlFtbIVoRGaBUmVjZFdsaGtXcWprY2JSX1RdRFFYYVVSSVJXWFJUR19rZl9ZWGheXUpCTlFRTERKSkxFQUhjY1tNSFBUU0Q3QFJPTUlAUFBPQT9VXVhUTkVJSEg7NVhaUk1FSVFNSj9CWlROSURGV1BIODpTS05BO0lKR0g+SlpSSEU9SktKOjZHVktKQj9KSUg+PE5aV1NNSFNTRzs/XFZYSURHU09LPT5fV1hYVFFiVEY/Ol5gV0o7TlJPQTdOaFZdTDxVUUg4OE5eVFJEQE9QRz0zWlRTTUFIU1BINDNfXFpKQlBfUU05QGNSTkk/XVZWRj1KXl5cSURiWVNEOUljX2FKRW5fU0hBXWddTkdNa1hUP0FmYF5QRkxtW0xGUW9kZ2ZmYWBma3lhg21seGZxc2x4YHN7gH2BfoCEiI6WhpSDfGdeW3B7a1Vrd4B/homThpCOh4t9f35vb1VEU09Ua3Z3fH9+hoV2aFxuenp5f3WHh3t4V3prgXCAhJCPkpZyfYd/f4B5goh9f2JocW11d3F1gXJYaXFubW1hSDc5MkZobXWBhIKNi4iRhG1wc2RbZXl5foeQjYuBdmlseHx6XG1zcm1lVlxdWlNNampuc3uFfWVDP1Nucnx9fIGCgH5xXm16fYeIkpSZk5+MeHt6fH9+f355dXl6g4eKkZiVmZyVbX18eHt7fXlycHJ0cXJ2g4F9f4KJjWxzc3h5g4N/foZyZ2Jsbm1vc3N1dGJlbmxsa3FwcW5ub4J5hnyGf454gWtwfnd9iYaIgX5ya1lzbYF7goGOhIhpaHR9eH51fXR9enl0d3t2eXJ5fHl3VlZUWGBecGt4b3ZQZG6BgIaFgYR8bGR0goeIjoeVhYhwhcbQ1MjGuLfDmpKJfpReZnh2gJqPkmqFco97ZZiUeXJ0dWNoZXRuZ2RTbphma1xuhHxbU2RWc2RfdnyBfmtiR1xfWGFkXl9YXmV9bmRfV1ZVb2haZU9pd12DbHyFem14dGddYWRjYmdeV01MbVZNV2BaX1pdWV5eWmFxX2VgXGFjZFdeXFlUV1FJPzlbdXtwdGNeVk84V3NeWlpVXllSWlx/Y2VhXmNfYGFeT4Bybm97fnp5fXZ8Y15ve2ljalVme5KEeWtlZWx2eGJZUmNnbG9wcm9pZFpWZVdUVFBPTElDP2JoYFdYXnZ7UlVQaGZpZnaDgoNkaGlgZGxicYdlUkdCPmRvdG6QfoVsbFVWcm12cGxwYWlSSHyCkIWJdF5WVk8/fW1kYGVraGxtbWlsaW1qY21mWFFWYnNfYmVqa2SWp4mAX2ZpaW9jZ1tROmhvYV5YgnRcWU5GTGJyaXFqbmxeVzlkb2VZXG1qdWs9PVxbZWxaaV9YX1KEc2xiWl1gWmdVST58d2dwaVl4a11dVGJiW2ZfYWViXmdsZnR5bnJ2Ym9baF5dU2BmW1xRVExCaHFzf3Nvc3BiVWJ5enh0d3ZzZmFPXWRwbGVneo6Agndpd25yZ2xlZmBaXWFeXl5pZGJhVEV1cHNvbHB7gJ6AkJCKfo6Hi4Bxa2VZYnNscHR1fHBrYlVRXGdoamJgYGJURl9kZ2hrZl1hWE9XXmJncG5wa5KmkHVraXhcX1paV22WhnFnY2JlYmxdaXaCaF9aYVpeYHeQkot0aGFmbGdtdnRsWVxcZFpdWl5aUF11bmJnYWNhWVNEVm9xcnuCdW1kW0BRZm1sfHV5Z2pfSWRpZ2ViZWJiYFFRXGJqdnV5gpCLdGGCiYZ0cWdoX1s/Yl1ZU1VgVlt2YlRYT1VJVU1gWlxkhoGesrC2z77Kt6l7j21ybYuGaWxpaXhudmVfbG9teGRgVm5kWmdoaGpRPVNmZFBhY2JZTE5IQWdra25rZ15VY2dlcmVqbWpfenhxd3hlXltdVWRiX1RbfGxmaWpqaW1jWEloY2RiWmF7dY+Ah45+e3trbHNqZ2BqZmNnbXeDhHpuVVdvY2pvdXJve2xiV1JORkZGVG99g4Z8aHFnamtkYldPX2NeXmFWWFhRT0RdcmJeWF9jYl1YUlFbY2tudHZvb2ZYTmRnY3FfZHBdWVVfaHBydneFb21gWmZydHJtZ2ptXmltfoCBeXt9fXpzZl5xb2tpcoFqbWpdV1dpcXV3fHZuaV9qem14cX1rbGBcRWpycXN1em16aFhcfH13gIFxeX5xY3aIgYGEgo2OfqmGc2ZtbnF0bW9mZElqaWZucGxoamJeV11sandwd2lfW1FJcnBzenB3a35ya11kanBqYmJPTk1GZYF5bmhuaV9lZWNrYGJfaGRfamNjXXBocXpwhndmWUJKYlxUU1dSR09DOFFjZWtlb2+ZgodxXFtcXWdbVmNtjYdOVFdTTk5PV1RSXXd0bWNzb2Jrak8/WVFRV1hkX3yumImCfHGGj4Vzd2JOeH2GiYqSdnBmZl9aYm1rZ2pcSjkwdGteaXJuantfVlFUY2lkW11mdnCBe3qCZYFdf3V0bWVcU1pbbmhjYFdWT05odHt+hYSCiH56Z5h1ZXRqY2djXlFniIOHioBrbV5VT3xxaWhoZ2llXVZLdXNnXnN/m5Kfi4RgWllTZm5iX29eQ21vbnRxbmtsamVoaWhxbn96dnF4b2lyfH6FeXhxZmZBe3BkZXaFeW9raDZOhp6DhXNvaWBfT2p8hYiNfHBpYE5gbW9ycnVzdGyKZWZWYWhhcWJlYFdTdml1Y39saGhrWkllVExTU1dYWFpcXl5dbGBgYVlNRj1HNB8fHh0jL1Vydm1dSEs9Rjw8QjkvST1AOTw8ODQ1NDNBUVdaNSEbGxshPk1AOzs1O0AjHyItRTghHB8dHB4ZLnKmr8TYy8fLyLugg4B7cpmBc4JTdWlwiHJue1N8gGh1koqNmJGRloKPj3hfXF9IUldQVmhQYGpiVl1hY2NjXmJcY1FRVltfZGNWUFliZWtoc3FzamllS2FZS19XUlZYWFNcdHR5d3t5b3BzY2JgYVxZWVpbZWRdhH2Ch318gHRrcFtMTE9JS0ZRTlBYZIODhId/gXqBf31aUEtoaF9haWFmYF5cSlBMUEdFQ0BRUmZeWlhWV11aW15fX2RdV1tiYV5QXmxsYlNETmJfXVxeYmFbXVpWXFhcT0BAQz9DRUlIQ0BMYVxSWE5PUUlEQTxAPUFITk85SkkzWlhKSkNJUU5HQTw0OjlBPjc7QTtASm5pam1xa2pkYWFJPDs8OEFDPlZZbmltbW5vbnFwamZgUktCRUpPUk5RS0FcaWpjWFpYW1FPW0lERUhJRU5DRUJEXFxcWF1XXFhWTlNXV1pOUk1LSEI/a1xbYG5sb3Jpa1VVTElFPEtLSUtaY2hnYF5dXFpRTkNKTUVERkVCQT5AOVpiW15fXFZOU05Ka1VOR0NGS05NQ1JfVFVYWEdEQkFKVUdIUlBJS1BPSENndnp9fX96eXdwZFNYVkdNUVNHTkxQXFtYV09UUFNLQEA8QENFQ0FESEo6WV5cW1VXXGVudHNfVEpRTDg6OUJSa3p/dm1VVFZNSUJPc1dDTUZFSExNSFVPTUtNRk1RREM+QUI9Q0NIPT1DP0FTVlBAQENDPjw7VHRSSkVGPkdIRUFPR0VCP0E9QERGR0E9OTM4MjM2MDBGWUtESUtER0hHQTk5PD47Pj9EP0FBT1NUVUtQTFNMTUxRSUhOTk1NUFBTTllZWllVWVFSSUY/SU5HR0RER0A/QE9UVE5PTk1MR0M7R1NXVlJSUlVOUk5kWVxbV1BUUUlEWZCjbmVeVEZGW1Jtj3xsaHdjgGpaV2OPe2FoVGdrTFFFhXVjVVxbfGlcTlyul2dfSmpoUm5fmbSFeG9zb4iJeUxluoNiXF1xeXF6mJyklXF4f3+fjIF/qdTw+Nzi18a5nHF4gI2Ro5ycoZuMY7Xf6ejd0b+1onlndIicuruvvauukKjQ6end4sy2n5BvbnyIgpyblKSYjWnF7fX13dTBtpRkYHd6gY+RmZGLjXiV3v//6uTUvrCPYXN+hI+QipebmI9irN7m893Ux7ieeYGHhoeWnJWaopiHi9ft7uPhz72oi3GBgpOalZqjlpaTeavg5+TUzsC1nH5tcnqCgpOWi5adcojW5+rn2M+7qY1vanV9g4aNkJCIjIKu4+zv4si3rJV0a2lwcXuDh4OEg2mG1e328+TTv7CPiXNqc3V4fHx4ipJ2qdrz7e7Wv7KQc2lrdXx9hIWHiIh4b8jk6PHVzcKnhmV2eouAkYuVlpWbYbLf7+Lcx7Spj3BodX5+lYOdj5WSjIzW6e7o2si3p46CgXqKgJCOlJiUlVmf1/bu7t7Hu5+IYG2BgZCOoJqWno1zye7r+OLWxLOLYmpqfIidl6yrn5lqo9368fvawremjl9xeXqTmp2fl6GIdMjt9uzhybegfmN0gYeSxqqTlJeSaqvc8eHj2MKsl4p8anuDi6OenZShn4DE6fXr3M6xnIhhcoack6CVmKWam3qa0Ork6tq9rpJ7b3KRi4uTpo+QmoBpwevs6Nm/taeQbHeDipyaoKCqpZ55mdbn4+PVwq+ji2h8jo2SnKedn6GVec7w9u7cxLKoj21sa3Z/foWIhoWZh6Xc8Obp2sm1m4BvdHmBhHh/iaSfiXfH9f/46dGypItucm1xiYGAhX+Aglin2evo5dHJvKeWgHNyfoOFgn+Hi4B0xevy7+jRvKaIcZCOjJOZnJqTmolemN3w5ufXxbCelYeOf4mFlI2XmpWWYVNUXl5NUD88YW14f3x7jXCSmoWee19JTUtMTlNdXWNpbmpucmpkcWVAImTJ6ffj6trBuKesjn+Km5igpKiqmm+z2PHn59TLwKGTeHl8iZilsbKwrqJxyfv////y3cu4lYGIjZiilp+jlZp4o9Hk4enm2s66oX9tf3KCgoyUjpR7YMPi5t7f1tDGs5N4eniEiZaYo6qbfaPY19fT1MzKuqmEdXuOlpahrZqpn3LC3eva6uTPyLidfXyBiJqjnqernneu3N7m3NzZzLqmkH59iJ6dprenqJZ4u+Xn2OPl1cWxkW9udHWJnpjNwoeFntnk3t3f18u8podrbYB6jZujoqWJbL/e6tvi4NXArZF5eHiVlJ+or6akeKbV3+br6tjIsZmAc3t/nLGjkY+XfG/B5eLb49vQwauNg3aAf5KUlKaRoXOl0trf59/Ux7igiH+EkoWfnbaqp498xOHs4OXcxbaliXlxhH6RlZKgkqB6rtfk3+3byrytkoKVj4qVipiSn5V6aMHl7+Ph2dDGqIh9iomSmJuppqOrbarT4dvp2tPJtqKEhYmLoJefsKCpiYrC2+bi6N3Ov66Lb4CKjaOTo56Uo3ui0+Tb4uLa1MKlf4SEhZahl6ylpqSjzefi59/Yz8KxhXhle4+WnKSsoJZtr9jm29PPz8S4l3d5e4uWnJ+ptKuQesbf5urb1cm9oZeBgZOip6Kpo5qga7Hc7+Tj2dTHvKCAe4SFj6avpbG7h3rJ5fHr4d/Rw6mPbH5/iJGYmaOrh26x4ODdz97VzruQZ3R1fH2OiIWLk3yWxt7i2NjWyMGmd2R0fIaNm6ers5lhtc3l2trWybmwmHRyeH2GioyMj4psltLb3dvczcGpi21nZGttcm9qcnpZSENCKxdKSVVdUEUkFhMTExkbFUFeWD02MztCVnJzTTNnVjonJ2hNQT0+Rk1KTmqGglhPTVJALxkyPBgXF42YTTw5OkBGRkdERUA3MjE2Nzk5PD05SUglIB8iHiVBbYprYlxKRDE7REhGNS5LPD89NTY5NzkrOUZYVjcoIR0XGR5RU0Y4PkM4OSQkIlBTMiMgHB0fHhwunOvy8vP59uvj3L6BgYB2kaWtrpyobdHk8u7m7uTc3MiVWnyCjJ2kt8C7fafq8f/7//fn39a1eIGChpKnqrKqmXTP6vLk7uzl2dC/ioVyg42bnKCqpGS24fHv9e3m3tbAmHtyj5ect8CwuqKI3ebs6ubq4NbKvYl+f4ulsLHIw7hxyPP88+3r7ejf1K2CmpGbrMTBxtaOneTk9PHu7uTd0sGPfpCksbO3xcSsfcvt8O/f8uvf1secdHeAiZOZn6ishpfR5ujk6uTa08WqcXR7jJGdoaq2lYDP4e7k+Ove1dG5h2hyfoyUm6SppWy75ezv9Pjv6N7Jo2Vma3aGlaCdpIeE2fHx+/vy5eDPuYR+dICHmZqukatnxOHy7/Pt6OTcyJd3eniMj5elpLV3k+b0+fHq69zXz7qJhXiQiJ+cq6qec8vr8Pbr8+vf18aghHeJgZGJoJujYaPj9u3r9e3j2tC4iH+EjqCnsbG2pYPV4PDi7Oni29rIqYKDhJWLpKGqpWa85u/v+e/i2dbDs32JfpyYrLi5trOP0+zy6+jp5N3Qs4h1gYCMkZy2spZ+yO/v4+Xn597awpuDfoSOl66urrx9kePf5Obi59bSzrSCdoGerKy5xMW3bdL6+fDq7evk4tOejY2Oobi1t83SjaPU7O/q8u3h3dnCmYaHoqatw8G+sXTV6e/l+fPm3tXBlnB7f4SRnaOpo4Oy3+vr7PDr49rIo3F2eX+Lm6qttZOJ2Obr7vXs5t/Rrm5sdoGQm6GioJdov+Pz6urr59zRvIpnZmxygImQl594keXv9e/t7uPX0rOFdHR2ipC3y7i0c8nz9//5///99t6zlYGHoJuyr7S3q6rZ/fjs/v7/8OLPq5aXoZ69uMHGqJHF5u/j7uzs5ODPrZuLlZaorM22zZycqszSy9bGvauuxKPDuaCRmHp9fVdjbHlwr7ecmIiGboyMhIx8c297eGhOiZ6NlIqOgoB/c4+FkZB+mo97e2dubXVpbW9xZ2hnYG55dHdyeGJhXVpUcG1lYG9tX1xfTWhyblxZWF1nd1hJc4h4YVhUT0xPRThsZlZcWFtZW1dZUVRRSENEa0pEPjNhfW95ZlFIRjyBuqBlXFRLS0dBQUA9UVVRWFhEc5COiHlmWVlbaGBSWmBmbXdqa2diXlhev9iYXFxTVltRTl1mdIiQhIh4VllVSV1raVZHT01QOzAtYYJ1bHNbgoN9Z15tY1BTUlFMTktLUl1jal1XVlFMSENSaGxoZmRla2thZHJ2bVRKSFRPT0pEY2BfZWt0dG1xZWBiWVB1ZlVTT0xGTVBOSU9shKqOdlVKQj9ARkIyLzU/SztAPTg0NDUwMTZDQjhJQEFGTEtEXKHGyMibsZOLe3hxcWpgYmNZUkpHO1ZtYWdhWmFZW0p9kYt/dm9kWGeAgnRWUk9MSkdPTUkqQ01LSVpQRT01MzJbWVdcVlVNTDw8SGJkcHBjd3xvZ1lQWlBSUU1MS2V2UVVkYlpbZWt+b29eZFtbW1hUTkhBQjg4LCUXEBAOHB0UEREPDg4yLA4LXF1VWFY3HCVMXVxYWUI3MC4qKCgpKCstMjU5WHuPko5/faDBsaKslHJnZFpxYW53eWdYW1RSQUFNUVpnY0g9OjQ+eIFwaHuChIl4bmhXUUtOVlBQXGReYm9ueH18eXBudXJjW1FSUVRTUEc+Sl9kaGtsU0xKSlV8X1xkaHN9fHZZY2RnY2JgWlVNSj9PY1lbWVZZU0xENVVXU15WY39xg4ZwREk5LysrIg0NLzE7T2NvX08+PkI6NTYzNDEzNDY5WJF6YVpaY25qZTAyj8XX1crIyL+xppZ+d4aFipWUkZVmdLHL0r/Cw7mzsaaAa21reoN6fXlrXLDG2sTEyb2yp5N6ZHuBko6Mhnh9m3ZhYlZXWlJXV15daG1peWVFW19PVHy01tnHyMi+wa2VdmtzeoKDjI2KbWS1wMe9uMXCu7WmhW13fouLiYGQfk1JSEk7WV9caXJeP0dDQkVATVdQUE5HUUxJRUlGTlBXUlGAiZedlYmVjXZ0u9TPwMfNwbyvnYiBfH6Bi46RmnVotrvMx7/GycOxnomFiIeDmqSZlIFRoMPbwr7Jxru0oo6AiXaOj6WWm5Zgj7XHwcDAvry9rpuKop2iqJWaiJlseK7N0bW8urSwrqN+cn5+gn2Jhn9vW7HO1M/Ixr+7spx3Z19/f4hxi43Fn5e9zcq4wb21tJ14e4KEiY6SjZuGbWVYUkxANS0kHhwdco+Vn52fn5eIfnez3Na9xcOzt7Ojh4SEe42xl52Yg3C2us3AusS+tqmtg3x5fI6QnKmml3ykwszBvMK7tKygjXiEeYCKf46KgFiKv83Jtre1r7OjiHBxbZOfp7SUmlR8ttPZv83Jw8GvoXpyd36QhoyNmqeSu8zSxbjAwb+0pIJ9e35/h5ySqI5KoMTPvrjCwbStnYyBcYKLnJ+inI1hmMDPvr7ExMS8r5h7doONi5ihl6KMfbHR0LvDw66vqJd9c3d+h5Gam5ufn73Dz7y4yMTHs56CgXGAiIySkJWJUafF2MLAx8S/uKeOeHiGjZCQkZCGTKa908/Dy8rFtLCtlYaAg4mPi4yHaIC409TPxc3g5867gYFzc3N0fnp6XGKNbmBOXW1wbY5uXnFkbmpycHB0V0SpkG1iZnVxbV5PXHl8fH53f3yCd1igmXxWV1pfWV9aWHuJg4J/iIaAcEeCoWhMVl5ZUU9COj85PURAOTtBMjNmpIhAQkpLRkxkYE9PRjZDOEA4MCs/i4RNRUNEQjw5MTZFSEU0MC8rMCk5k35QREVEOzAqLTVDPC0rKSopKygsl8rj2tbO0NXDzbGSell7dmxscXpsZVdnYlxVVlFfamFcUVBWVlpUVFVUU0tKTD5JSElRRVFqXlpTUlRVVVFCPFZMR1BRSkxJUkpJVFtZTEdEQz45NkRvVVZZVWhkaWBkZmBkYV9maWx3eXF5aVlZXFheZVtiaF1nY2BZVUpMSEZLR0M/Q0NGRkVKUEpGS1BMTU1MRVZlZ2p4eXmAfZN2aWxrWkNEPjw8P1F4en52dm59fXl1dXhvaGxnaV1cXFpbYWJjXWJeYVZZRUpBQURCRj1CQTxBSVpVUElLS0pWRk1MS0NGQkhKSk9RSUE8OTo7Nzc4OUhfRz5EQUZHTEg7SV9XW1RdYF9hZ2pdYlpeXVxZWlVXU1FLR0lGTkdUX1pPU0lLRktKR0w8SEtFQkZHQj5AOTFIR0Y9MzYzMzEtVklPUEQ/PkM/MDArSlk6NC0pKiwtJl94d2lcXl1XXVxeqKOuqZ6kqqKnlWhoXVZPXGdpbHBwmKmpq62orbCjomxoXFhOVEpJR0RCfaerqKarpqehr5J4Y1dKR01GUUhJbaigpaCepJynoo5vdFpUWFBRW1pQVoqbmJCRl5CJnndaX1lQVE1aV1dUWZWZl5Kll5SkkoxUZkNBRT5ERUVCOZCcnqiooam2pKiLcGBNT0RGSEZKV4CClaGXjaCalYxweXFmUlRfUFNWUGianJmfnZuhoZ9/ZFtaUklPZlpPVVSXo6aprK+vq6t7UGReUlBPXVZGTVKPpJqXl5KdnqKbZGhWU1hWWFdRUFRtl56ooqSipKajUW9rXlRTW1xYWVFljZadkZ+VmaeSa15eU1RRUldRVEpIiqefn5yhnqSkiF9cV1VTVF1XWE5PfZiYmZagkaSQjl1gW1JSUFFVVlJRfZiVlpWdmaGWnoJkW1hYUFddV1ZZaY6elqOanqKcmGlaV1lMSFBLTEpHV4STkZaQnY6ei4BOXllQRENXWElJS5Oao5uYkZuamo1WXVdVU01bTldXQXaFkomUiKCRlZNlkb3jwL+8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PUtwZVNNSU9JS0k7RVFTRkVBQ0VCOzNDVFdYUj4uJyUlNFNOTUBDRUZANTBHaWBGOTgxMC0mPqjD2OC9sqB9gJGUc3dtfoV/j4N8dYytsZx4YFVRUFtpeHlignF5i2F9bY21wKqRb1tOTEdeZ2tmdHZugHBrV4Our51tTktEPUZOXFtsZ3hvcX11jHOqtppyVUs9MCxIYGpnaXJyfHt7cW6oq5h5Qjk8OzY8Z2ZvdXJ1fn10a2u2w6qBPUZCPjk0Z2duamx8eI5vc3KgqpR5UVNITVpkd3Bpa2p5fX19eW2erqeLV1ZRSVBOcWZpa21rZ3NzcGagqqaCVExGRUZFZmxwbHRucm9pa12braCFVUVPTUxRZGdkam93dXR0cWWWqa2NUkRLSU1GaGJiZ25vb21vcGSarK+bWjc5NCwsbHBzbHx6enpydFeOoamIYlpKQkRMdH16eISCiYSHdUmVvLafa0xIRT85XG10a315c3N1bUCRtKuVY0dHSUIxZ299eXd4cIFyf02Otr7BoZBxbllOY3NycYN1hIiBgk5+q7GsjndrX1NOV3VsdHh0cn+AgWB/uLOpeF1ZTkpMWmtranBsfXl3eW51s6yfdFhSTERARnZ2fX52ioZ/iFtpr7ebeFVJSlBRU3Z6hoWCkpKIi2thpqOYclRSUFBQT3Z3fn5+iomGindwn6WgdVKIkLGddHF2dnpwfp2Sm4V5mK2ee11wbm1oanVveHl0e4uIhndtlqmYcVlaTUNLVGZnaWVtd3puclpcmpR7Z0FENTAvM2ljaWhmZnBzeHBaoqyhfG+Vhol8dIpsb2t3fIKGhXBnjqiWcD5QRTg0UnxvcXFzeXRzeIN1dGNPQEM9NzQwMjMyLjEzMzU5Rj9CQEVFRUM+Oj89WFBQTFhMSkpTWmlXREpISkZGSEpJR0BEQUZERUBIQ2JbRUJGSEU+QjpEREU+QUBESEpLSFxWRjw/RkhFO0dESUA4Qj1CPkJDQD9BQDc8PTw6Nz88PDdENEE9OD5MSjQ+U1BEPkU/QkNGP0FDR0RENz9BPTo6PUFOR0Y/Pjo7PUI+OTlARUVAQD5Kleny/+7y7+rg2sOHj6udq7Cyq6OUpbvu9+ru6uLa3ceUh4+WoqSurqeglKXy/+bt6ebb1cOIhY6Wo6mxsJakksDu/eTq5uPe38yWhpOZoK2hrZ6jjMbp/+Xp7+bZ28SVmJ2ps66mtrN6g6/q8+Dp6uXl4cONmpqeqa6hu7KRi83x/+zo7Ozh5cmfnp6et7Smubl6isDe79vm7urd3siYp6qjs7eovcCbisvz+ujo6uDa2cmko6elrKius7uuicns++Xu6t/d3cWkpqmvq6ustbiukM/9/+ft8OTZ3smYnqamrbGutbSkg8zw9ejv79/Y1sSgm5uhpKinr7Oki8/1/+/s8ezn38SGlJKsn7Okt6+Wiszo/Ovp5+fc4NJ8momlo6ynsrCXi874//Pu6+jl3sKNjqCZsayntLCYhs3i+Ori6N3X1cd9n4mjoa+tt7aZisbm/u/u7+vn3dSejZWkqLGypK2je8/a//nq7eTZ4diVlYqhrLG3s6+5gM7s//3w9+3u3NimjIuhrK2fqqaodb/c/+rr6uTN1d2plI+bpq6orKeuc9Tr//Tz7uXg1tCKjqqqorayr66ufcHb9eLn6uTT2tijk6Ksp7S3rbS5gMbn/+js6e7m4dyUk6Ous6+/va61gMLm/eHo8erV3N2Vk6Kwsa3BurfAfr3q/OXs8eXZ6PG8j5Ohq7S7usC6dtP3////////+vawjouSmKWls7amgc3j///v+fT08+q2hZKgqrC7u760bMPq//j5//v09PW+kpacoaiwuLmdgMru//r+//fo6tutiZaSq5uzt7aebMPv//j////38vO5jZueqaa7vbfDd8fz/////////+67m6Kps7jJxLnNjcPv////////9vGxp6WzrbW8xrnDfs3s///6///7//jOgoqLiZKJj5KDb32IhYWQio2Ohod3gICMgYOQmIqNeX6GhX6CjYaKk4eBbYOEiYyMi5KKb4uZhJKKjqmMm6CBg4iHiYSHiYR7aHJrb2txdnB4eG5veXeBgHuJhn2AaGd5dHN+gXh9gHBjgHx9e2mDd3l0bW97gnuAjYN+ioVma3d5eH6Fe36EfHR+hIJ+m4uLlpJ6d3l1gYt/gYx/c2FqZWxxb3R4fHtyb3NvcHR4cXFxZGNnZ2ZudnV2e3djcGhnaGlpaWtsa3FzaGhxb292dnFVb2Vpa21ybXN0Zm1xbW9obm1ubG5jY3Fxb29xcXBvbGeKkpOkkaKSnZR+cH56d3x4fXd7XmuFkIeRiJSImpWPdIB/g4SIg5N+jHh5hYOPjZKTl5R4goGLkIeQjJyQlnSFh42Uj5CHm495gYmEkIiYkaGXjXWu3v/40+Td19zQopmGjJiSkYuMjpOTjI+LkIuWjI6Ki4mOjn+BiI+IiX57g4J/iHyBfHF+gXt6dXd7em10cHB7dXJ2fHmCfH57cm9wcmxpcm10eHZ+e290cnF1c2trZ2dsbW9qY1pUTEc1MzhCPkE5NC8vMTc5OTo4NDItKy0wMzU0'), c => c.charCodeAt(0));
// The mix's spectrum (tools: numpy over music/suno/eurodance-2.mp3): 16 log-spaced bands from 40 Hz to 10 kHz, 25 frames a second,
// each frame the peak of its 40 ms (so a kick keeps its attack), each band scaled to its own range over the song, 0..255,
// row by row. Read it with spectrum(t) (kit.js). It's also the music's own pulse for any effect that should visibly follow the mix.
const SPEC_FPS = 25, SPEC_BANDS = 16;
const MIX_SPEC = Uint8Array.from(atob('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cFqR/8ZJTnB8PId2mpCQVm5Te+XGKVFuenGIco6bmK2FgcTglldzgFprbGZfnYrYi4jL7Lh0fIh9Q2xVhJaL3H1nusaJZ2hkhk+HfZyQgs1TdZ2vXkBWTIhHiJCkknaAYE1kZhAbIBmGV4Cly7abvZa+unaNhnCGdGFym7+uncK15eKBvMR6jXI7e2aEVYeWsOfIYK7Ean98UIZ0i2F8VbHRv1qcp2FufVORfpFfcGqkn45cbXU4Q39Nk4CMYZaVq3Z7XE9JSqR5W45zg4/B5rKqs4+Xh33EVUhxTJSSuuSVnrnDypR/xHM6Zkuej6vOXm54xdmYcqF6QWVmtYekZx8uVqnTdl97cENqZ7JtgmAuUVFo5rG6xmNRc1SOWpiOlnlbqv/SzMVlhm9tZnebms/SebjgsJ6fTpRji005THmu3mviu7F4dkmWXpxMPEtwtbRh9MywbWstk1OjUSstQ7yZce7Gm2RgRJNio0g0M0eonarQxZ5qYzOKXZNwpZ2Ftr2sx6+Fa2g1jmGcdrWog7ezpLamiGteSJRemXeukYmUjY6rmoVbU0yUWqaHp5CLhGJrhYpYgZdUjVWjgZeFeIBaWGR1ia/GV35yioKflZiPhXOaboWIlV+beLOPo52oh6Jwnmx7UmxEqHCxiIVmoIGiZ4xogFBiS6lvqIKFNF2UjnCFamw/WUGnbalxaVlxgm1zdmVxPUlZp3miW3GiXZNxeq7GmJ2xW5NttHOjwXKwm5i0yZuYr0pzXLpwnbJ6vKCoq56bd5NGhla2Zp/VXbF0lZFzlGhxQIRTu4WO1kqBb29/X2OG1leIXr6Cho5cgltWUEQ5m+NXfFGddLSAiMR5faCRdprSYotYjG+yiYHmuHu0kI6AoVSOVYhmgzIDytaKzn6RYXk+jlSVcIEuC+C9i9Oph2lyQI1RmG5xLTbOynrquJBohTiFW5ZWVmp4ZMFr//Oqe5Y0cFiTcnOLlXyHd//3rH6cEXRHp3xwi5Rwd3vi7biImDd3SauAclh7h1V1+Pm4hZYbbTurgnYkd4ZQWP//qnGaOmUxonJpM3dxa2b316NVkFtwM49sgnaCetSQ/9a7dYtXhVeZa3lxQ4Hoj/zIq2+JMotanG1XPD6m5n6/q5l0gCGHSJhgRi0Y1MmOvbyUc3YujVKdV0UgEOK9f7S6kV1sT4xWk1hpg2/ijnK0tIhmgVqRY3xmd56L6HB0vLWZaIQ0mGJ8ZmWdjOVpd6aNkmZ+QJ1jbXRXj4nWa3awl4pWg0mcW2F4UoV9329eqpiLV4Nhm3JUYk9wf9Z5YKiAeVV5f5eVr9SdcpikoYHIpYhzioez7t/omm9leK9ou4JXSF659P3RqiQkAKqvRoFQPA4o3ffWijMVAAC5mlOQa0UTFuPgloQPAAAAuW9Ki20/CAvizZNMZ2SIdLBmPJJ9SBQVzc2fcpNlkX7GaUGZezwPE8W+h2iTQFxfu1Y/lXI5AAbHvZFmhjRvQIqZTnw+FgAAv8y1VWssdUSDk099QRYAAJndvkRnHVBNcYyFpWcQAACz1LBra1WLaIPbo+KBKAAAtbynbmRPgGB05GPMUSgAAMHNo1ljKkUjx9Bgn01EAADCv6ZPZx5VAMfAXqdQSgAAvbauU1oDRA/TtzeaX0IAALy7onCSXqab1XlQlW47AACzuqdzok+nm9N0VpBqMQAAj6WkaJssdmvIST6TTjEAALKwrF6RTmQruXBJi1UhAACywLFYjUpcCrRtVodQHQAAsrKbXnYsbVKhrH2hZycAALe4fWV8UYZec9+HwnE5AACvo3pXfklyMY3bT6xeKAAArKR1UmxKfR/ZtnySZk8AAK6qgU98Tost1cNpjWNQAACur31JeUBuSManTI9tKgAAqbCEdaJvpLPfeH2SeUcDAJ6hjnerX6azz3V4jGdEAACbmoxjokt+hpFnZ3pPPgAAlI2DW5FrrlyogoWGa00AEJWVglOGUKlbp3BvhGQ3AACWmndha3CgZXS0oNd3UwAAkJeAYot3rWSB3KbnflQAAICAf0WDUY8At95ft0UoAACIgnBsiSuPSOG5aYZaSRcGenttaZoojkjOz2SVVEwdCYeFbFySQ2Rh0IJJnWE2GwB/fHx4t1qpsMyaZqhpQg8BV3t8ebpXp6zKfk6aYDIEAHmIeXKwVYpuoFw9kFU4BAd3fX96uV2nd6OIWJVwVhkhZHZ2a7A4pWWRglaFXT4AAGd1clqEgoOBesmtwJJgCgBmeXdFbYhtcnXrqcmMVQ4AdX52LmlvaBrH5W2NUigAAGx1bShkbmw91cJ0nVpeMghFbmsyamhrL8/DYJpiYTQDNF9mPn5phqDLh1GnZz4qAD9YaVykiLTJxZxhq2w2LBROXVdjpICluq54XZpsTB4LTmRYVJN2mHOaj2qYakwSCUBfX1eXeKh7kaFynW9cJhhIUlZMjlqNaXORX3pFLAAAVWNkJFORd42V2JLLi3k2LD9qbipqklmHjeWOyIBkNCM7ZWhFbX9QLcLgb4ZxQwMAP19kRXCCg0bXwpGOg2EpGiZZXDpye3sx1b+GgXpNKgwxV2BfhYdsoM6FaqacZDYPN2VrZpuTerPPlHyto2lAGB5fZFyWhl6exIton3VLNgk7YmlajIFzXqiWe6WAYj43LWNpSX17cmN9lYCkg2pLNjRQT0V2bHtjmYlpeVxDIwJOWl1Hf6GqlLLVobqhhFpDQFxkN4OZiXSx3JKvi2pRO0NaXTFueoMj0tp1f3trTDZFZGo1bY6XNtW9iZKKfWVZKlxcMnCFghXBuW2SZnNOSE5aWkJ2jqmfz6GFuYtxYEJNY15AfY6spMuqjbaQdGFHG0xWQHRsg4HIsGGKgHJMJC9YXDZanrxqlLijmIFsUEo0W2IoTJ24Z6xurJyFcFNJJlVWNDl4jV+dspOgglo0LztWWj9RkJttr8G9w62Vd3U5WlsSNIp/FKDdp7+elXZ0MUNFBB9oTDSS6n+voYiPWjJNThdAb1k4nfCFr6CMj2IHRkoNO1s2F5bygpyPWIVPKFNVMHSGpZO/91yomneOXyFYVyB2iZ6Qve5Tpod1hVwxSUwCMINdR57jVo9XckxPNFRXME12llWY6IOmjHZrYh5ZWCZPdogulua2pJhsbVstSVNIX3JpYJS2+6+jcHdaH3BtTnmSc26fyPK9tH6XaSdtailbhD5DfMjvrKdqiVw5YGcwRmyBSnat/qyvhHhsJG9uM2FveUFrov+urINybi5kaDZfUFArloX3vYB0YVhEW2FcnXuWhbWx5cGqeHBwO1xmU56CkoSlqe65qGluaSlXUU+Qeo5hZ4P31ZF6VVsvYWNKiJmaXYmZ9dithW5wHVdiRm+XbjaCkOXFoXdta1dmZjmBjrSGiIv5oqmSfnJYdnM4g6a4kY2X876pkYB0F2VtAlufm3t5ivGtgnxzaTRpbzBeoYlLYl7/zZN7cnU1c3IzaqOAM2Ve/dKbenJ3IGNlQUt6gFuQb//MjItyaB1nc1eblKOKvKP/xZ2MhHYqbHJppICEfa2h/Kyeen93Ol9ea6SbqWhagvmjnH52dTpzc0iOsLNvYIr6oqaFgHo1ZHI3QJmhTUp18aKcf2l0N2luLoSzsnSBgvOnsIt/fER3dSuIuahhiIzura2SgX9DaWorb6eIO16E6aaugXtxNXJ5WH2YlGlGleHMyZaRh013eDd/kXdXP4nfycZuiIE/b2ZFYJ6xi2t746eygIN6LWBvRYm7xZWPkeans46Hgx1iZkWFsrNvjHrdqbJ/cHc0ZWY4ZayEb0R77sm1goCHO2hrOFuufWZWkP3HuoyPiy9fYjEshWw1Qnfdr7aCj3s4YnNLlZuxj42g66vGoZiEQ251PJOki46GiezAtZqPgzpfZjV9lYNpSGLgvcWSgHhBbHc3h3+NdG909qPZrod8QWxxN317MFNiWviaxrGDcTdaZEtff7GhspbwqNidjnU+aG5HZoe9ormZ3qPaoZSCS2RrOWmJsn6IeNC33JB8f09hcjqIcLF5VHTUxPKtiYdCcXRDjVupblR258TwoYWKQGZmNGp+kH5ii8O67ZeBkFd1dD2NpMCZet/Dzs+hnJZLenQ6i5OxcmDnybmui5CPPmRrT4SWk299ttKXx5F9kklmdlqemKhupJ72u+KthppIZm4ziISNA5Rm+q7BpYWWUGNtK1CO1JGju9fY27uTkURibyVfhdGQnLex2965o49DbWIvaIepWZKJpuPSnpeORG9zR3Wlw4muoKPk7JqWoDN0djN4n7KBqI+m0ueam51LaWIvapqWkJ2rnc7hn5CbQmpsP3y7pZ6W6KrA3aKOoSVqbzt9tJZ7X+l4lrCTg5ozYW84fqTKVYbo6pyckI+dKHV7QYqox06Hsv+dsp2UmzJncSFjm28zPZzslbWdipRTZmk5kpvRfX/F1b+rqpSiTWttOpqwzYR9xrvUqJqUllJhW0+OrLSLbaOr2s6Qi5tPdHhYkbXXm5KbxNzmn5KtOnB0SG6uuI1xkqbf4oqNqltmY0OGrMyMZJ+f5OKRk6ZYf3o/jbzUgnXho+DflpWlWHVyJmyoqW5D53upo4+EmVRsdCd5v8yCiOy/oZ6Zhp9IdXlBcMDJcoql9Jezoo6dSWlqSVWPllR60/i0nJWMklh1dliPwcCOqtSt1rmRkp05en0oi7+ql5mdiM/UkI6gTmx3U4abuZN+j5nI43+HpFCKhV+fo86XmZ6j+N2Xka8/f3xgfJOninp/mPzDlpCscomVfqOuw6N6vovrvJiMpnGZmmqns7yR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jXbRpp9wsrW4m6SbubWPrmRTz0edI7G2oaiCi6OjdpJQXNAxfimlr5OlgXqRoHF9TlXQHoBHn6OXon51ipBofE5HzCZtTZmVjod4TXduT1Jsd8iRpnuOo76SiIu0sHyFeXO/nKqCk53BjoCFoJlxcIpmyKiyjJycsXZnfHpmYTeMXcqqtJien59+XXN5bGQulVbPr7Wgl56hcVhlYl1RLZuA1LO0oKiQwIl0h66coZ2ShMajk323pMibiJW0p6mmRUHOKIp0qqeaiouWkYx6gjpi1CyOZpSnl4+Ve5aDanY8RdUig1uUqJqQlFqXe2poN3/WNGZYg6COfpBifG1PUGyC0XhwpHaT3Hq1jp6je4B7YbyCcKZ/g95uqXOVfnFseES+hkupjoHQTpteomNdVIRfxI08qJB60a+tcJ52X0aDWMeQR517XZXghpKKemFGeI7GkGiddms15m+dh6CHjWqOwGmOnYWNYd15ooegi49EP8E3k4OMj3TWhp+Nf3l5O0/CBZ5pjott2nqekn9ucUBRwwuoQ4uHeNySmZWJb3BCZMONqFeHaGndg6V5m2BWYqy+ypyZYIXMx5qqkZ1va1u3jdGSmF570LKsh51+YGFNuoTTjZVmWL61sGadkW5VWr+L1ZCXbh26b69fmItsSV28iNOIi2Q0q7atgKODWi5dtYTFeGx9qJnRjImxk4h8X6t71WZYea2nwKt4tJF7dlSeZd+BWmaYqYqoW6Z+YFNToGXhf1lHl6Cvo3ODgVRIV59w33VwNpaWsqZyh3Y3PmSQe9WUb4V4oYOzlqaWWmdtso6tmG6oiqCtsZiin2BwW72GxIp9noG6u6mQjIpJSGu9h9GSf25ivKLCYYx7NyBiv4bXl4RHV6iUxDOebjYMasCK2Jp9P0qJvKt9pJFXS2u1hsiYiHWbw6myjLeviYZspm3Se4pvnbx8uIe0kW1rZKJr1XVxVHiso7NzpZdfbFKjZ9J5oqSPk7iof6eTaXxPoGHSeKmphISMlHWjcUplXpta05ekqnWybZd3h4Vvcl+ndc2Vjq5quLubco6IdW9HqXfPgouiRJfDkHB0ZFZhUKd3zY+CppV4z4OFm5Zza06gddOMkJ6UedRxgJmPcmhKm2vUj5h+d1LUhnZ8nGV3XZhjt4mWrY6UzJl8lrF4hlSeZn93qqpzl5+id5WTbXxRp26s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CGAyqFlxRW6Qy36FbIpRThZEKJ9ZbzZrocJ2fVd5REwpLDCVVlZFSMR5bWxqaVVkM0A0g0F4cHDYmYZuh39odhJGFoM5eHJqzpyHZIFsVGsNTBaIT2xqO7mBcIJnZ0VTAE0Uh05XWzStsnF3VWRATD1WO4BGYzdruaNmZWJZRExDXUuWS41qlcnDlJ6KlXd8ImtMmDB/gZK5y46Wj5F2cDlvSJ0zYHlzobGFgXJ4VERBZzKcKFh7P62qe2mCfV5CN2YxlTFJekaroXdBgVNUPiRROYVEgGqRzoqagJOThYYtPDWKQ59/leyInY+Rl4qJLTsqlDCgfX/sgXWRfIt7dBNCHp1Am3Am071shYN8dGM3RSShQ4VTPKvRZoR4jGthOEZBpVp6aXvJnICReJd5ciFNR6p3l7SMxLqHoIWvkYMqaS2pYJK0i6vEgp+An4FtKmwsqGCOooaPnohzZX9eUDZnL6JZg4ttlqp5bXKBZ1E8X2KaZnhxPIaZZmJxiaWfSFecnvWpm2N9a32Qscj04k1Cl5X/wodNiVh8y8eNyL8jSl2oyMlZK5M1cNfTcqCED0hlloqwTEGdfj7MqG2PcgpVZK16WTA7mIdCblVRYGMvSnrBr4u6ma1xcnWJlY6XSF173bqNyJyasn2Ak52Sl0BRhdB5VMSalbdgboOVdm07P0PJrqGkj5ecUmN2inl4SFNXycSQh2mKmVB0enVzb0Ndm6+vdF1UjnthZ2ikyMpoep+U7Kuke35ymaajyOvqYHN4ouyxmliHXZ7T2IWur0s2cKWss2NbiU9Y0tlmmIM7SGuew5tmXIRyYaSqVnNlIDdCnrBYUVKCcV1GYmdvbk1ui8W+rpmSnoSSho6fmphPcYPMtaCwnJqoj4SOmZSTPl1brZJ1rJOJoYF7gJR7ezxjgbPOnoWIg5R0f3WDfn9AXY+x0H1EZYmVd2ptf3ZwPlSerNhch1qqfW6Ip9Hm6GltqLX/oKpllVyawr3U5uloZJOY7MGEMW0skdrmcYWaSGR7nrqpkmp4TVbX3nuJkUVhbq3CmYVwfXRpeIKBhYBfe3PBpGV8SnllYD92i62ycX+K7PDIroiEZ4WqqK7i3n6Rj+Xm34KJglR/z7iQsqh5kZDKlsJUimldYcy5j4+LNnms1M2dY5BqZ1WUnIaMiWF9q925ZVNoSFhDVXeMhYNneLSt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iIRjUfDRgLmLsWROkcKjxaC8knDSUXWspbRjRq3OlNSWuJR9xYBbs+a5Y2CpzU/Ve6ujeayVVrbuwVhhp8tV03+Zp0elamOW/7tbVK7OkdJ4k6s4hmBYm/+9Rk6tyaPFYoa8to2dasXA0G9ia2d6nHSMt7LV03Xc1OB+dFRvbIptVG079cVit5zCfGdARjVsYzJOb/9QQKN6t2pRP0opa2wzQ1L/WDamgbhpRn6ajKKqhneN/1JEroXKWGmuypHRxa6Ek/dATrueyl1urs5r1beZeXb4Y2S2pMtZVq7PUNa6dH9x0mdhrZK4TlSrz0DYt2aAUd9qZrSdxztKrM2O1q53YoroS2WllMBPTaW0lLKUj7SY5XJmjYSleHpvV3SXmoWWf7B4Z32DoXh7L05GYXJSRk+4SEtzdophWUpPQW1+Wk9VuEwzaVeGWEo/RRVvdzktQbw9MVdKck1JnbyrzIu3c3+3RiptY5pUUbXTpNycxHV0vEhIbWiZWFCw0mLkq7xoUbA9SE0zclFEt9dO6KmuZ0miPihZKFM8GbjXX+itm1ZEmTwdWzRNORO01aTms8W4rbySnkpskmRZmamborPNwdbSva5Ff7yUclFObY11jErI1LWeQHaylHFAU0R7V3FztLCZlihUpXRSSGUyiHZycmiBd1oiJ4FWQF95fpmEv4CIgJxVIieUSjmkxpXAqMqkmXmmjYbH6Yx1sNOQw7fOoIFlWnON4vWRgLHSTsO5xqZjXSsnea/Mam+z1k7Gsq2ZWVxAJ0KPuLSYstZwx7KZQlI5PSdEt9bPua3Di7Sj4JOWj1BZjL3Nu6JyaZSQqOiPo6GRhJWvwKiQSlZ8dGzMS5/QpJaqlrOUczhYa1t2vG2y15iKrY62emE9QnRpasRXqbO2iaWbunpbf5q+iq3AhIjKupGkmLV1VaWc35bRrYqQ2JeKqJe4fGGxfuB3yLJRq9iumZh8t3JbsXDiacCyW5/DvY6Ni7huXbJ05Wi6lGKbr7isjZG0fWGwmeSHqaVblr2mj7OXs31Umpy6jaSkfbfCzZK2kMeJdEpXeoienVSg0MecupTCjHNRWnJ1kqiFqMuanLqZwIVhYl9uba+6iKunrZyvpcKBX0k6bYWcmSN/zc2djp+8fFqkmdesh7qTl9fBr4KlwXxXuYjmqIjdkZG9baB7m8CAVb1/6I2S62+Hd2d7XWKUbz+/euyNv9SFd1t3T0hIc4Bqv5rrk7uvWXlRaz9SlrGYnLml3Y6fooyTYVhrf8rju7tsZ4Zwqaqsn+ZwmZK90bCyTGB7bYNuml/n55mfgbiWgm1kZTibgotS6+i2nnCwjWRxaVU5nnlyQ93rspxgtYpmfpOmbGl/eUWu/YSHXrB+VLWe4KCRv6NyxPOShmLIemO7g+GXfrxta5r0l3R8y3xkuXHef6mnaXWV95Rxe8RuULiA4XPDeG54dPWNboLNdFG5j+OJsFsLUEX6kXWAzHRPsKHQjbGYhHC68oifituKbTtIbWutiXZuwP+FmYXXkHJDS11wa3hcTa//jo2Fw4hnb2pvaZyNdUSO/5+ajd2OYWticXGdcDBVleGfpJThimCWob2AxpaegrXolKqL2X1XvKLepc6yn5Kt0pCygtGAWMSH4KzHsHd9f6lniUavc2nEeuCstZ+XdFyHVDIvW5jOxH3jrcJ8em1Xf1IoG2LY9cWx4LKjmbenjolpbVia2/eWj4SQtr/Ou7+1gbGY1MPCTTdtlK6yfo3Z5Xm6ktCniEtCRmR4oWJa9951hHSyh29KRUd9mqNgXObzXY50q4t0S2d0kJaLQEXB9VaOd6yIZojNsLGlsIpknO5gjnPJjVp/2bDDoY17XproXpNpx45cbdijyox6al+U7UR1ZLWJXH/apMuwl25jo+RNk3LAnWWW3K/Mr5QuQLXkVI94woplm8mns5Oof2G09FaBdceTd1o/enqcrIFfqPJchH7Blnw+SV52fXhPSdD2S5h6xZVzV1NJT41og0/R71OnhsuTclJTMA+IbWNCw/xNooPBjW6BqaKCb4qReKz3U5aos4VwkN67t5S0o5mexl+myb6YinrftcGlqKOOpYZWoOWunImG3KTPpaaoe5teMqD/uZF+eNyp17OgpHuQbke08byMiZHcsNeJk5hfg3BwsuOrf3iNvqWwlaa0gsyqnsC77auZXEdtZ5KckWb/yJjCuOmhkktOPWJ7dlRA/rqOqZ/Qj3hWTDtclX1ZYv/tgKCh1Ip3O1ZIZnpKS1rk9XmXgLaKbIG/q7GmbWRp+duCn5rDi2qK2K/Fo4d5aPimk5yhyYxsd9efz5d6dzP26pGFmMV+YHnWndOng2Q07e1xhIWlgVx81Z/TqH9HSf7AequOp5Bck9GjyI9liVfxrnGmlrORe3+OgoyjipVr2et4nZe1mIpMVnpddnE/YfXtjqKWtKF+ZV1dW4SKeEP2mqmpp9KbfWZkUmCThXA0+dGmnKDWn357joRtdm9SUuT2e5+CupRymtWzupuohXbm8nGZkMyEcHHYrb+Kn5Vr7Z18k4y6fWl22Z7HlJGXb+LrdYONuXloc9qizaqcj2rU62+SfrJ8coraqtGdZ0VG77qEnJeteneXzqnCmZCCjvWetJinu5SNdmmHepaMgHr+nrCEqciajkFHZWOQiFBU+3JrhaHEnYJpbUNtmZtdZvq4bYWauqB7ZGdFeY6BVmbv/2hikZ6QdIeyo52Vol6Ad/9fUHCXkXuO1a/JosKBh3L4aVlyk5eAcdek1qO2gX188G1FgaCWdnnYn9ieoGdyg/V1YH6+j2Jr157bnJhbSIb0ZG5wvpR1l9Ok15mJUj+D9HlkfbGQdZKkjpKNnHVlf/98d4uyqJBkc214kotYXJb9iXeKqaeLR2VjdG9sbWiW87R6jJ+UhEdaR2NydHVncviohZK0loUuWFFYf2haTnj4k7J8sIp/g8KpoazJmYl93KWtkrSjjIDWq7+oyZV8cdyUx7Czool516TDmqtyhYili+3Ho5F7htiix5incXKClZj+yqSLc4bXoMiboGFWYYuW/8esioKJy6O7pJRsf16afv/NmpKKfIJ7e6Ope4mX14//xciZjVNWYmWakXNrh+aGzrHDmoZNVktloZhWXl3pdM6RqZaLUF9Gd6OYSGJg7rDFeKWGiXibmpeNioVweND7wpmbgHmU2r3BsbOykHZE/6uZoJKMc92uv7atqYRwKvLOm4eRimjapry4o5deUzTxzJiLjo1z26i8tpiYSEcv7dSlpI2Ql9qptL2RdBY/MvfArqaMkpPAnaeokJZ9VDD9yLizopdgcX+Tnot1gG1A+sy2rKecJmxilI6Gam5jPvXTmJ2elkI5PYWflIhsSkX/1qCdm5FBSDhwq4tvKktE/9WZrJuafLerh62bpoBCKf/UtqqsmXbTsa2xo6WCNCP/0bO8rJpt1J+1m491clER/NCQwKuUdNabybmhiG5NEuXMo6ejk33Wocu+pX1wQznvxaKfvJCX0qXHopmBvf+e38S5o7qTh7jm8ei0k+f/rI2TvKangbzs+O/HYkz2sYNXPXd8ilvl7cdrFW8b+Uo/U2RjZIJg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H0VbUZpev3i50KuknHlhW3KQs7yZdql9oeXAsO3XkU5agaythYfM9emwu67vzbWlYom1hZLK7PjXdFRPj9+2t36YpXHA0NKbPEc4J3PywbSav6JtwqFuXG9cWj5X87SNqc+YU8mUcmV+WVxEKvG8gKLjjj3InZx7p4N4WErrvJqe15R8qY2rd8CdeHBV26rCo72Td6qArHvBnVyHgbmS29O9iFebaKuBwpxsinZiRdnRyplXm3ipc7qZdl+/vkzNxMPHbpF8kMnOj22Q4+9Qc8C/1YOHsev03JB5hPjFOkSOusqAq9bu115Ty17wTjUaXoXDdMDJmHg3Vr1ch1gzGhpGdU/IlnOOl4aljneSPj8XQ11lzpKJkbqkyKm93KGiwraYgLy1ktGJpr2SuNW+oOLGr7qEuIfahqGkoYZteT58k8zVY7t9239ugaJ7VlMUUa3QzVy+gt57TouafV5eGEKcq6ONvovbc36XlenjaW6frZujkafC99zAhp/o5qeNptCohJfG7f/RrERletG/wH+gemS91N7HSX8oiqG6yNCksk1TxK1puV2DT4uYWae2gHopNMmPh7yprr+sgGNeQzN4hYPIpaGtteLBz/h8YkdgoquNoLicx4/Jor3/1nqRmZ2qiWS/g9RtsJFTxNaT2b10jn9ZwoXcY56MTYdmcNSoVoeRaMWS4IBzlEmDRj8yLE2BpZHEk9W/U5ms09V1i4+hsL+Crev201KRquTmd4+Y0bKzrNfw5HJIHDfN6rNvnfigTsLSrp0yMUUvaPy0co7sjku/iV6XOhRAElr71Gx45HVKwYJogyREgjVf7NZql+p3TbWvj6BxdqZQYuLNiJjojnyEtn+1fXSXfYPb0I+A74RxccCIyXpriZCrwNN+pO98V3bEiNSBcYCPrafUkp3tgk6Bxo7VgnF6kpOk07ex3HtJfbKz6ua2oqGxqKLOuNqHfZHA7/jhpYKBrnNqxbiicne80+fGTFZYk6NKXce7mlxex7xurFVaaKV9TV/MwpNTXcaIZ6pujIqpfEiiybd6UV3HsqS1qZGbk5VImYNxgYl6o8Gm27KSt6iZWlJEWJaZinzGlN+nhq6qpYiXhpmulINixI/cnIF6mpyRo43Gw4htcsKL25N6b2+DoL6UwdmEc36/jMyBWmtBc5u9mbfWf3V0i256HXInHU2GpX2DqF5r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Xo2HVS9xaJuiyvKus53cd1d/aUczlW/LsNHwprZbxnKFr3JRV6B02Z63qjCqN8Sb0dmNQmKmdt6EnJosujSKoNfajk5lq3negnOagLooXMzAzX9Xaqp31beguIqEUGnDnpBxZXam2O/ptNy0in965sfDlYOi2eXqwXC8irWWaeWsvHdxp9K2g01nkXi0u2bXq8m1Zno9QIEwW5GDdcNuvqnMs1g2Mx14MoSFf2uvh6qmyKBbWo97pIzIxNiNbpmEntaMbGWlfb+JvcDZiU/Uhp3ojHFCrHzLhJiG32VXz3xDzniBSqt2y3qHhLNyYXJORmafwGGof8x0YW5YWmM6RUBElbpml5PR6qKIyYmJw9CHuK2Vksnf6+6YecbbyNDSiLKsi6DS2bdqXE0u1MTafZuur1Obn3xuR1ZFNlDS6YSX0MFScUcgbkY5UTle5M2GmdrBUTtiXW2swMZ5b8NvaVuidDxvpom4vcnRtpmCp3B5orKDaqmBx6iu0ryYbZl2fKO/tFKodMuXnMiJa0BfL0NkuOBosX3PlpCNTz5GTRosL5LedrGFzqePej1niVtJZniR03Oo1uzwttWInqVxtJ60lZK95+ro0XLTht1varybwpWA0+PEVzU2TGn1VHGedrSHWcmenm9vWmVG93RnhHCUfVGhf5tfaVxqRfihanBooI1YjKqXeJ+ptnv/oW15abN9V5WtsneinrJ3/6V8hFuxjFKruLxlmod7Ofuve3BOjohaqL3CfquLgjD4rWVsVISSWIq/xYaqYn0M7qpzbGmDi0SLsa3B3bd4Yf+fgnaHlpt+jtHf4+a1iF//mn9ygJmagMPg3Ld7EnAC/JR3YmiNjmrFu5VVb0hrA/+Wdk9nnpNgrIZqSms7WAz/ymdiTZuTV3aLi3FniLZz+NNkZGWRhFV6mah9iarFef3KbWBpoIBUhbGyjJWmmWHv0nZhYpZzUoWytpGwnJxbw86Cb1l2gU52t76ZsoSXUtHHhGxkenhXXbe/np9wfkvp3WpuZJKLb2aYy+zsp6By6elhfY+mm42k2uLq1395PMTxUmJmi5Nyr9bCXkssRCTd8U5oWYSbcZ90UTRQQkU15uk2Y1KIqV1rVlQ7Yj1YMrD1SWtFhKlZZJ6WYIyls0+V+GpnZ4mOYW2qrnyEpa1Qlfhsc2WWiGR4sraCaY2NJZD2TnVRk4hKcLe7goGSdSWM9URpSqWKTGC5v4tkcWopafY5Y0eao0ZxsrvC3Z2Jo3H5TnmIiLZ8kcrc5+mii6Bt90V1gYWueqnY2r+SMGBmc+pSg2NnrmaqsYw7c1xzYYfpUZFfZa9ZfE02OXZNbliF5We6b3OfbF2Ch4ylXZZee8SC1aB2oHJgn6uWxWivapC4jtmvdZxecK2vncxbgXOFyZvXl3B+VHWwtaHVQ3p5edGdw5Koak9vtbqk1UN7fXPRo7WSuWVPaLe8msZyc4h6zq+kk62SW22ZxevisKGLpequwZ+npXyb1d3t0IVxU5Huc7lsmIZrptO6jGJKRjd99WaicpiBVoprUWNJT2U2e/Vok3KQd1VISzWCRl1mPGX8WYxehYdGaJmCsbKsr3qp9neeZHyaS46qcNC0qqp/qe9xll5qi0mRrU7WnZOMcJT3TYZQfYI9k7Vb4KWAaVpi+D+FV4mLNZG1c9+bb2Q5fvdWaF53ikGNrY7L0IWpbIT0fnNsfpNyhsHU4t6Jq3GD832AbIacdJ7S1MF6H3dQb/lPf1eEl1KdsIp9Nz5LPFf/R3tMhIBFdWU+ijwwXzpE/ESJXISCRWd/g5hTa5p2fvg7jlZ6gkR0nY3GkaCugpv4TnJdjXJAiqlB0JaafXyM+E6GW4+BPYatStShg1B8Z/BCcWSNgT+Ys0/aqWFMY0b6OoRni3xFjLOJ2p15XzVG+TGDd6mMZnqSu9/frohhc/9ckoy3o4ua0tnhzJBPO3P6RX14o5V0oNDBaqWfPiJu/0SDapSHXnldY8v31FctM/1JgnuHgF1gWWHa/6lChG7rNWhNXINYZpl90d27iPOl61eEhHycdYOncrScsYT5yelMfJONq3SNqlLGiWB+2MTmOGeOjqVolK9X1N9whYiV8jBlb4yFY5GuiNnsjWxdiuowVGR4hVyKrZbR4cZx8bjpaXiSlqOGh8La4tG/TvGy1LaurZefiKXV2ch5lzjOYLLA0q+Rdnajto18g+p5kpO5nMaOk3RuZVQ4hoDrfYCgtm3AipZ0bHGBb4d75au8qMFoqHOWh4l9n4O1hNTSuaTOmcydv4mSi6NewGHMx4OSkY/Yv9R3hX+jUdNkxr9egn5tuPH/ZmuJqmrXZtObY2NZkJfw/29vhqyW13nXi6llk4575/+Ne3GJwNvWwafZtraMiub/p4uVzNve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gJWjm6vni3xmy7KY1pLfspqappqj8XBmXtSxmNGQ4rSflJ9XcvKWgEvUlojSkOS3nJFtTpftnIRd1KJ216PnvJx3Rz+Z9Yp8WNObctGv4+Den93N0PamioPZrZyu7//45p3Uw8TsoIV00J+U8///vmhNGD5t2nFtNLJ7Wf3nkncnKQNVg+x8aS7El1/7wHd3LkAGaZ/1kGBGwpZV9ryflW+PeY+c9JNtccWxjeS41rGDoIaemfGObIDSuaPQjt+xg6t9i3rwnXtlxq2Y0prkuIWthHJu8pKIVc6ee9KW58KRjohobviVimvHnXXSsObBoG6nlrX5kIWIy5WQvLrl+uyuzbnJ6qORmtGrq9T9/PfRhoJ7f9t8cHWniIj8/dR1Ui4gWZbbcmxUtH1h/dSAaTxMOU+W8XBkSbZpTvatjmQ/Tkk6zPCNZ0+1YVHvuMycnZ10mu6txlqB3JWp0YXWnqCmd5vj1MBec9SWpsuO36aelXh04M/MW1Dae4fNieK8qYtYb9qk1GpT73N6z5vlxquHSXLa58+qTOBlecqu4uDbo9/P8OXIpIHOkpyp7v/55qTWxvCgxl1yt4mS9P/+v3ZIPivZ1bBQRbJRTP3olnUoMBkozNbPVk+7Skz9wG6INCVaMc6M1FZO0k1G+MaYmHVLd4u2ydSscuibl97PpMyOf36dyMzjqXrus65t27TXloGMi8WE5VRu46CbeeC42p2Ik5S7tuKPd9qAdorjt92ciHyTxrrXnmrUc3Oh4rvcq6W4fs+i5nuC4ImOnMDl9fbI3p/Ppd6hl+qnq9T+/fPffYllbsDGpnvWk5r6/tqBRDc3SsW81nxk0Xx4+9KCgjIgJk/AZudvdtBeYfi0cIs6NmtDv3zmonjFQ0rzy6u0b4iMZdZp3+S68JmwstWr0oGEfU7QRNvOtfWZsoDbqeGIhWlTx2jSyKnkhJJ637LijXt4a8mT+8Gr63h/ieC35I9xd2SGf/+oicV3c6LYuNzkq+fc4YT5hYe/opGq7f/77Krg0dat/HKAupOM8///zHUoJVyDt85SVKtPQ/3rm3IcGxF9bbXiYXenUDv8v2CFJDkSd37I4pV/v1U++L+jkniKh5KdwLaUidigjN7Qq8OPqayepqC85LX2tql33LHXlaaqhoWihOXO7ZaVhd+13ZamnINtrpDPzt6ZhH/itOKboIKJequg2cPgkHyW4rvgmJO3qq6Mocem4Jd0k8Lk9vG828vQqK7Sr+O6ps/9/PXee4SJkKzIyYXCoJv4/dpwQT0IYIq+3W5twId3+tCAYC1BJGSAuuBpeuBdaParh2s8SmNUl8XconXrYVrwxay2i5ejiaivvaSy+6q4v9St1Y2UmY6SasTlvf+muXjbq96Ng4B8mYWq68H0f5mC37Dnj3Z8hNOBnNq051OMkuC065x1VGjWY8u+o+VJiqXct+DfpOng1KjSqJDuopGn6f726KPj1su4v6+G7pyj8P78yYJAUSqYtM+SV8iCp/3qnII7J100rXjfV2Hdgaf9voOXDzNVKsCq4lta4I2k+cWnmIxOlUvVwbxkU8i1q+fGx5qsc7ha3M6PcGrbxri6y9KrvHuySM3XjW1p3bCywMzVs8t7pirU1Y5zStKbksLQ17bQiqdO2M2MaVnIjoS9zti7yI66kMnHvWtu25KQqb3f+u+137/VvsZwkd2wrdD/+/jhfph8up67ZXDLn6H6/+BsXiJTHcenzFxWtIyI/M6Hc1I5VxTbosqKfrmDffmzhYBLTXk0342moHe8fW/1yrKol5Wli55vneWlzKO9xcLMs6GTmYzAdpPvoc6jusDN0cK5lsB7s4CTyYrEi52/0dvHzpnITLpfp6SJx5SKvtPdzM6a2C6pc6yjg8iSgsLT2NjerOjX4Jflk5HlqaSn6v/766/h1d6P7oaH36Gh8f//0YtFRhu1r9JWTblrZv7woo03HyRDYK3+Z1C7bU3+xX+NQBZJQHOp/4lWunVH+8KImph8i5WBmuOsi76RjejGwqmynKKrmLW2xMDjq7G3yNCxqp2fo424stmx4Zyjus3WvLycnKJok4vSoOWUerfP17vAl4+Sa7e41LT7iXa1z9m8wIOmo7Kstdeo/JF9qMHg7uas2MPUlurFutq6uM3+/ezae5iGgbbot4PMpK75/uN5YiIbK1C/5ZR2z4uE+9F2aDw3MUl2y+exetxsY/eujmBFP1hZh82xzG3WU1b0y7Kfq3GNkoKixtSq6KqxzcLMr7F2doy0qMHYsuansrzM0r26enJetruj3ai3gIy9zdbGwHtqXmq/qveTx210uc3bycJuUGJ1vqX/jsdgYrrM2tvfqM7F1JHW7pXVjZyg5//88K3PxNKu28GY1oya7v//zJY0NyqTrMuGS8lcWfzxqIYjGiIsq6jecUTSVUv8xICrMhcpM8y44IJD001I98mHrJaBnlfPtNBubMuGjdzHe9O1qMSI27qyb3TWpqiz1FLjuaS1h9q7sXZhz5mWs9ZY67yYnX/Rv56QY8yDbrDXbu69jJ5r2rW2jkrNcGC0157wuo2fmN22tnBi0YJvqcTY8u6v0c3msNGOitm1o8j7+PPjiJ+Tt5XSeW3WpZz4/d17ZCw9GsOh2mlVwoV1+86FcUQwKx/TktrDccJmXvi3g21HPWwS1YSq4HDCZjz0yaq6qazkb7x7kcaYzKuuytKb3KWz4mq3krTmqNepr7bZbuaVqrhPoI+15aDdlpS32mjosZbeSbRrk6+l45B1u96b67KK6D+yeY2EnPqNWr/drufYdPnE1YnKjZz+rJ2h5P356HHww9WG1YaT46af6///1owzSS22m9JaV6eAbPzvsX9EIiU8nrvtalveZFn8xG+XR0QyQFm986tf7GBj+s9+tGaFdYWLvNuziNyJi+HPeNiMr5ixmoXWnM38rKu41mLpnaqTqZmRwbrO+Jmfttlr8p6hapGXgq7BoOp+gLbaW/WfklSEjZO25J3xenWy2I/2nYZ4lZqUucyg8nlrr8vZ++eRqcXKldy2o+K2p8j8/P7ecn6JlK3bq4rUrqL5/+J8YyIpIla+4mxxyo+E/dKEdiQqTD5txeWMeeRvX/i2fo9QIUE1htTDwn7iYkP0zZjKh3azlXi7y9Kn4rCsxs+J5IiUtZOuo9zWruSwr7XXZu+blqNqsqjIwanikqC02Hj1romgUp61ouiWzXR9uNyT+KqEmHmSrYnwgcZbXrrbqfXWnNnCyanF2ZDdnaKi4v356abcw8jMzI+R5pyg6f7/2ZdKWVpZyMRtWNlWVPzxroQ0QEZgRrjjdEThYUX7yWeQTitAQl3J6WFi62VJ+8Sup2pkV0pl0+hZa+WRj/HCz7yIknV8htX6ZmvmrrTBneDIlZxdgYLV73tu5qKkw4jrzpaaQHJZxPxySuaPiMWI79OWkz5ea8T/cFfufX7GovHSkX+RfY22/3p07ox0sqPe//i44szCnv+hpvPDq83////wobalk4fNg37Ss6X///GNe0wSOW2Gmm9ZqZB//+GRbTBDKD6Kf4N1UJdtWf/AnWcvSkU5v5GUnJW9dWT+y7aTf6OZhb/BtbC87ri01qzKvYGuko+u1bKzuu27tr+L1cmUp12Cj9W7uZvooKPElN/TmZVFapjDyciS7ZiQyY7m15uNM21+u8nJg++Sh8i85NHYorndw6Lbvpf3t6Sg4f7/9aXC4Mms5L2a+Lyq6///5K1CP1aZvNqNWdePg//3uoNLEgwvx9Hec1PZiW7/xYhZJBohJM/O1WRTzXpT/sSmc2ppTFzvu9lSXNqem/HH0a2QiVie7MHRdHnqubm/juC8m4NRn8bI5XNz4qilx5Hpy6h/RYLQxeJ7aNqbiciR79Srektk087Rf2nehXzItO/TpnB4kb3azpKD3HmDra/Z/Ourwdeoy96/remrq8n////iipOvmqzXsY/jp6H+/+6EXDcAInTMnr6C25GM/9t6VCgyAAmUy526mOGNjv+5n1k1blNHoa+QnYjafYH9zLCgnJOyqMuRlsG0/6u/27XQw6WerK7Lna7Cu/+sw8qT1cqjom6Oub2yz7X0kqLRmd7SrZJkdLnNtduf8IOI0Zjl2LGJSFTAy57dk+GEgc6238/epbvM4LLExaPqo6Sh4///9Kq/z+S8376k8KOi7v//4qYuJirQxsOubNpta//5r2ovAC0f16XeY2XTYlz/zmhTGQAvHNXH9G1f2GBk/MGkiWiDk2e+y/B2aM+Hi+nMsrmGtbN+x6zhcm7XqLGf1qjJg7amW9fA/2BwzaGnfN6414alf0ndvfxfbtKTinXkv+GLmm01xqn2Y3nGgnyG473koYGTisC8/2aA2YuHicXd/e6r1dLDu/+Zqeuzt8f+///miqinsa3liojWnaj//+uJWz80Isar7GZ40ZKD/914aB4JNyvMkPKXi82HgP+8gl8nVkREzZvbn4nOb2390qKjlaPIrN2DsKDD3qTD1tamwJ6d1Knfe7fOzNypxongtdCcnreEzcSf1afWna6B5rvckaaAb8zAoryg23iMgOnE3qe1g2nKpaW7k+x6fqfoyNzc0t2/4Husop7urq2g5f//8c3ivuOFu6Gg8LGx7///4ahweUXLlNhPbMdsfv/8t5BYakU0uqLpPmnLaWj/0oSPSoImL5XE2VdZ11df/8ulpIOyc2t8v9yFb9WNlu/TtsqbwrOEzIOtuqzcucip3LTbnMawa99ijLy+46K9f+fB6Ja/qnvUfn2WuOuJon/pxeuMvKh8uo6Arajqho2P6cbvxb+dhLmQfa6i43yEmNvb/PPA3Mfkjrmete27uMr////rhrWiw5mwepjOqK////WPdExvc7Wno1F0pY6A/+NqW2pDhnfIqaU8daBzd//AhliVMZZvy5eqRW+TXVz91ba1p7LWj9FtiKWa0LTK1t+1wo/C347kaYausdW70Y7lvM+QvN1445BspLK+ma9z6MLfm6vDfuCYhquuvY6ZgevJ5quurXjdmoSpn7uCiqzpzODfpuK/3JOjm7LFrb2e4f/+/q7rweGXrJuyzLHB6v//5MV3kza0qaJigbCKlf/8yHGhVZ81t7XHOF6tfo//1Z5xm16vIKrMySpWqnmH/8Step5ts2CrzrxdYaSFi/jKuIuSifOZwMrAfoi5nJq2wMKPoHjvmL65yWt1q4aHl8HEkrWV5Ji/tMtBS5Jpco3BxJPNht+Lwq2/OkSRYmtzwsKOznLcisvEuTJRimtsf7StlbKg+t3PxsBrlsuwkIewuZXBoPna0a3Cao7CnX1cuL2T03bgysqzql9wnnZta7m+qteFy7DBtMVAW5ZiVXW6vqvThsKdwaKvMVGLUkx4u72eyX3hx8OmxGmOwpiJgrm3frCj89a7mMpqk76WgWq4voW1pOrOxYm1SGOXa0BgvsSA0HfTv8WJt1RRjl1PW8DHhddS1568hLxcT5RVUG2+xJvOrr+awoC7Z26sjXB8tq+Yxbvfws54rJmGvJeCd7i7crS238HMbpeic5p/cFC+wYytq9m8zGiLmleaZ2RwvsWRv6rSsLxoiZVVkk1QdcHEf9CZ0pfHX46Ze6B5b2WyuYPFpurV2HOTnqy9n41subyIqrbo18ZifpCWpnpocrrBd8Ks6suaXnp3eplMSm66wXPSseS8rmp2XWV5JEFTvcGe0L/okqpiXl5SXTQ6jLGsrcXe8Zylj4l4vb6xmZbGl7fE5vCVooKScLizpo1qyJXEut3mh4aJlVV0h2hTcM6Z28DV2JiEh5VBTnA+H3nRo9i6w9eYhX5/P0BFGQCXz6faxrj3zop3eHenp4F5mbS6o6G3/9ucfX95ra2Iel67wFibo/rYoXltSXBrSCtbvMFlmKjzx6FwY1BVRTMAX73Cbpuq8LuVbFRGTDQVAH66u4iUrtevm4NtdrKgp6aGnJ+PnL/jwMGQfpPTur64kbJUiWi83bO/fmByq36CYJS3YaZqosywrldiVnVkUS2aukS6YZq/nZtXT0BbVDIQmbx5uWKHvXqSYkUzXkhNYJW0hLI+pPepz2J0aqubnKGdr3/GQp7yqcpWdVejdoNuk7Rn0Dxy256xaV9GbS5KKZC4UdUkbbyQk3RTMU8pNwWeu3jSFmirdW1qOQwvFhwNmrGAvTaQ7Li/XnRw0LGtjY+bZ7o8qO69yFlrbs+ko36MrmbHUqbasbJOVjaMW2c4kbNkynSlz5yhSVEygjFLBJG3VMl1mcSFo0lTLlkLFQCQs3++W6zdm7hYZmKqhIOOkqF3yTm765vBY3BzuJGOk46ka8tKpuSRsl1NPoNaXC+VuKHDeqTTr7c8f3Gfj4aUjbacsnet4be8RYtvoIeEh4auhLM0pNe1xUWLZHmDhnWMmpPAS53ns9NbimqBoKKRkqOE0Dyh3bDJVHhbeWZxYoytStoveMSvsF1bOFg0RymNsmTbOHamp6ZlTDhILDMIl7SM1lN4o4uLbU0dTnRQO5OmlMNwn+DE78mMZZ/fqpWgrXS2PafguOzeeFKV0ZWLlLRryUaT1bjU72Eqa81iZZazV8xVkLmYsu7SKlTZVFiVuGLPVXm2f8C22h1P2EpglLWJyk2r6LS5u+RZgfKtmJPBkshlruixsLjnVoTup5ZcwIrRapvci7W64jJx43iFbMGG33ie15m2zb0qV+Bof23Di+J2fcqb2ca4GEbqY3p9xKTjhKrAttbZszNz6KScm6SbuXPXxcLi1ro4g/CpoJ67SsMv1KWJ07DBK2vSeXugvVHMGsmggcbJrSZFy1ljl7xJ0BnHlHLQvsIbQ+FJVZi5fNE0t6Gi0dDENmfakIWPoY+iUKvSs83NqUWL46+ein6lmGupwqP/uqBAb8eAcppmsZV4qZCM/6B+N1/SY2Khb72Zb6OMdP+3hDNi0Uhco2XCoWCdoXT9uZAhUNNMVp+bu5NWu9u4/86oRZbgl46akbOFRMHat+7X1TeT7n6Dm2C+jzy7x6Xmet4xiu08T5hav5FAq66R6dTdQmXwGk+VXr+UTZWKfc/Zy0tX9hxXkHu3e29206fokuVHmv+lon6Dr3NwcNOt3eHlXZn8m6KQa7uKbGK0nNjc2mN7/E1/mF7BnHRTro/wjtBPfO8tb6BsxZx7W6iE88LRQXf3FG+ggMWbe56tlN3G9GWK8pKjiHSok2e3wLK/0vWIl/aerJFfppFUtLO9nOO5m4D+YZOXW6iWdKObv6vl2bSA8Vidl16xnnOalbimyO/Km+IyopJetaZwk8CeqqblvZaTboeKf6ehc7r3p6qowZp5vJqOjXCojUi+7aKtpr6VZqtlaJpvtaFctcyGqo7AaTWbSjGaYL6sX6Wlh7COr0YuiiManHq/rmGfhYifZ6U4KZQfIpOOsqVkoeK+p36qbnK7jYaKjLKRWqrbvKeaoolnpXRzjlm/hXSkxJ+nnqCPTZAfN5Jbw4WAjqGbhpiwfz5wDTWea8OGg5RhmpJ+r3lSZQAPm3u6d3eg6suliY6KrMK6po+GqXNzse/Tm4ySnK7DuKKUdayRbrLexJGNdIV4kWBBk3G2mWmtyqaeknZ1QGtDLJJRu6FsoLqSjIt1RDxbKBGOc7unb5Sfv5h/hnGawaOGh3+slovJy9CqhIKRtNKylpNqs4GKzsm/olqdlIGCZVGXUrmHf8irqphvlYZmbUAlmme+h4rAcZqNf4VWX2QkEJuTv4GGp6Cje3FvT1VrXluNsajLkcnxzah9eG2os6CghMaV4IrO7bundnZalYd+dl/KpOSJut2WqmNRQ2R6W0FeyJXmhKfPiaxnRj0+Tz4hesmd5ZGLuoWhcz4tPTokKn7BoNSUtvzGn4Jvcpm7oZiGvp9tS8P/wq5/a3OUrZaKbMOTm0jD77CtbnRAXWhdO17Dkq1Puc6ikl9xLDhXQxhew5mxWbS7mYFwVykvNhkAe7mdmm296sSTc3BWpaGppYDFn8h9y/THpXBxXqeprKppxY/TccnnoKhnej9qZG5ZbMSN3Hm2z46kVm9AN0BUK2TFk+B6q7h4m0VNFDItMQCPx5/hqbO2teGTe5LAyZOGe7Scw7HSy8frkn2iz9Wbl3PBirmqz9Wp1KltnI+3dnZixY/Dk8i6r8q5a4uJlWZxWsiVxG7Mu7DbsoqceaNpfYXJob9Z17Cd3q6ao2Sebn+KuaSrbdzrrtWtvIyopKybdMGVxoW67LDVzbyGlYulemPIms5wyNKdu9i1RU9vd0tyzZnSeMfInMnaqiM2d1w7es6i0nvOrJ/NzcQ4S3BXQIjCn7+B4u7AzaO8l6umo5lzwZvDn9nxvNt8vZioo5uVdsqezZjM04jUo4eap4OFdW3Hm9Jx1qaHyqiDmXmQbHtwzKfZf9exgMqmm4t0j2J8jsqs037V2py7kKxznryWnX3Erbh72Oec0MfFXqnDoKZozZrEkNrfgcPQvVeAmn6GacyayXrY333Q4pM+a5RqXWHNltFvyMxzzt62QpKVX1CNzqLNc9HCkM3NzHmOrIaMib+hr5fi38bVh6K0pcidpn/Mm6+n0Ny43YeMtJy8jKBy0p++o8yzmtaXf7aElHeeb9WhzJvKsZTXonexc4dsiYXWssuI3rOW0p2Fn2qDYoiJttrc5+6SnMmkxoV/kYmmvPv/3t3IZ4vRscNzcXp9mfH/86ShnXU+yrC+Mlp5aX322bampYx5NNDPsERLhmR19ra2op2IaTnb0ZBIUX9bYvHFw5aXaGxO1cZ2LU9lWVXQxceclmV3TMTKWh5FXVVSrsfMnphdcmW5xns0R1RHTKbJz5iZZYllurGQNkJVU06ByM6Tn0mHWLbGjjNJX1NMgMfNpZ50gk+yvosdQVdENoTIz6lyfoosuq6bJUNVPjKIyM6ia3eTBbW0oyomWDc0hMjNnGV7mAirscohF2RCNYTL0pxoiJQtpJ7HIRZjQSyBydGUd3SZNK6ixRoJWTUrecjMgWthmSqqo80WHE43L1zJzoZKeIs/raPCGSNWPyNwxctteWObLKaJshgOST0edMXKbbk/n0G/iq8wH1AlLFzGyYa9bp9HwmyxJiNWJC51wMVvn3SkSrddozEnYSMrZL3BbcJTpUmvZ5o8T18VLnS7v4fFbbhlum+WQ1NaFCdzub2YvIevZaZehFMyVRsnXLW5j79ns123XHJXJjsmKly0uHvEZLVfq1JbXDBFHyxqsrSZxYq4VbE8T1opLgAiZK2tisx/t06eRjpRIS4EIj+lrGjQbMBSmVVHayQ/FCpPoqGWypO/PpVIR1wpLg4pNaSkl8mVozGVPDoyIBsFITOfpHHRcLpHgTskNyENDxtBmpeT0HjLQXVBJjQgAA0SSqaopdCWwURxRykgFQAACEapq5PYd79CW0crGhQAAAY7qqtg12HRT1k7KzIiAAArQKepicSMzzpULw0qEwAAI0ynqHrFhrwuPDEaCgAAAABEn6BMxli9I1MVIAAEAAAAP5yhk8KRuxxUDRQFBQAAAE2bnZ3RlqQzMgYJAAAAAABLmJiP3WSzMkoHAAAAAAAAPZOYi9t+wAZEDQAAAAAAAByJi5rPhLoGNCIAAAAAAAA0jo6O1GGiHQ8bAAAAAAAAPo2LU9Q/qxcTDgAAAAAAAD6ChY3LWqkIEgAAAAAAAAA/eHuVymKWCiYFAAAAAAAAN3x7htEhexMoEQAAAAAAAEB0dmjPFJUkEwAAAAAAAAA2aGyCuj6VExIAAAAAAAAADmhhgqAydAIHAAAAAAAAAA9kZV2ABjIUAAAAAAAAAAAZYGRIgwhTCgAAAAAAAAAAEWVhS4cDUgAPAAAAAAAAABNiXz59AEAAEAAAAAAAAAAAUVEmYQBBDQAAAAAAAAAAFVNSIW8ASgoAAAAAAAAAAB5RTUB3AFIABwAAAAAAAAAdS0pFeAA3AAAAAAAAAAAABkxFP3IACAAAAAAAAAAAAAVEOydiAAAAAQAAAAAAAAAAODMqYAZFAAMAAAAAAAAAAENBRWsASwAAAAAAAAAAAA=='), c => c.charCodeAt(0));

;
// ---- styles/demoscene/font.js ----
// font.js: the demo's own 8×8 bitmap font, pixelled here: arcade-style capitals with 2-pixel stems and 1-pixel bars, readable
// lowercase, digits, punctuation and the few symbols the lyrics and the greetings need. Each glyph is its rows, top to bottom,
// '#' lit and '.' not; a glyph is as wide as its rows (text set proportionally trims nothing else) and row 8 is the descender.
// kit.js turns these into the text-mode font (each row doubled, 8×16 cells), the small UI font, and the big fonts (Scale2x/Scale3x).
const FONT8_SRC = `
A ..###.. .##.##. ##...## ##...## ####### ##...## ##...##
B ######. ##...## ##...## ######. ##...## ##...## ######.
C .#####. ##...## ##..... ##..... ##..... ##...## .#####.
D #####.. ##..##. ##...## ##...## ##...## ##..##. #####..
E ####### ##..... ##..... ######. ##..... ##..... #######
F ####### ##..... ##..... ######. ##..... ##..... ##.....
G .#####. ##...## ##..... ##.#### ##...## ##...## .######
H ##...## ##...## ##...## ####### ##...## ##...## ##...##
I ###### ..##.. ..##.. ..##.. ..##.. ..##.. ######
J ....### .....## .....## .....## ##...## ##...## .#####.
K ##...## ##..##. ##.##.. ####... ##.##.. ##..##. ##...##
L ##..... ##..... ##..... ##..... ##..... ##..... #######
M ##...## ###.### ####### ##.#.## ##...## ##...## ##...##
N ##...## ###..## ####.## ##.#### ##..### ##...## ##...##
O .#####. ##...## ##...## ##...## ##...## ##...## .#####.
P ######. ##...## ##...## ######. ##..... ##..... ##.....
Q .#####. ##...## ##...## ##...## ##.#.## ##..##. .###.##
R ######. ##...## ##...## ######. ##.##.. ##..##. ##...##
S .#####. ##...## ##..... .#####. .....## ##...## .#####.
T ###### ..##.. ..##.. ..##.. ..##.. ..##.. ..##..
U ##...## ##...## ##...## ##...## ##...## ##...## .#####.
V ##...## ##...## ##...## ##...## .##.##. ..###.. ...#...
W ##...## ##...## ##...## ##.#.## ####### ###.### ##...##
X ##...## ##...## .##.##. ..###.. .##.##. ##...## ##...##
Y ##..## ##..## ##..## .####. ..##.. ..##.. ..##..
Z ####### .....## ....##. ..###.. .##.... ##..... #######
a ....... ....... .#####. .....## .###### ##...## .######
b ##..... ##..... ######. ##...## ##...## ##...## ######.
c ...... ...... .#####. ##..... ##..... ##..... .#####.
d .....## .....## .###### ##...## ##...## ##...## .######
e ....... ....... .#####. ##...## ####### ##..... .#####.
f ..###. .##... ###### .##... .##... .##... .##...
g ....... ....... .###### ##...## ##...## .###### .....## .#####.
h ##..... ##..... ######. ##...## ##...## ##...## ##...##
i .##. .... ###. .##. .##. .##. ####
j ...## ..... ..### ...## ...## ...## ##.## .###.
k ##..... ##..... ##..##. ##.##.. ####... ##.##.. ##..##.
l ###. .##. .##. .##. .##. .##. ####
m ....... ....... ###.##. ##.#.## ##.#.## ##.#.## ##...##
n ....... ....... ######. ##...## ##...## ##...## ##...##
o ....... ....... .#####. ##...## ##...## ##...## .#####.
p ....... ....... ######. ##...## ##...## ######. ##..... ##.....
q ....... ....... .###### ##...## ##...## .###### .....## .....##
r ...... ...... ##.###. ###..## ##..... ##..... ##.....
s ....... ....... .###### ##..... .#####. .....## ######.
t .##... .##... ###### .##... .##... .##... ..####
u ....... ....... ##...## ##...## ##...## ##...## .######
v ....... ....... ##...## ##...## ##...## .##.##. ..###..
w ....... ....... ##...## ##.#.## ##.#.## ##.#.## .##.##.
x ....... ....... ##...## .##.##. ..###.. .##.##. ##...##
y ....... ....... ##...## ##...## ##...## .###### .....## .#####.
z ....... ....... ####### ....##. ..###.. .##.... #######
0 .#####. ##...## ##..### ##.#.## ###..## ##...## .#####.
1 ..##.. .###.. ..##.. ..##.. ..##.. ..##.. ######
2 .#####. ##...## .....## ..####. .##.... ##..... #######
3 .#####. ##...## .....## ..####. .....## ##...## .#####.
4 ...###. ..####. .##.##. ##..##. ####### ....##. ....##.
5 ####### ##..... ######. .....## .....## ##...## .#####.
6 .#####. ##..... ##..... ######. ##...## ##...## .#####.
7 ####### ##...## ....##. ...##.. ..##... ..##... ..##...
8 .#####. ##...## ##...## .#####. ##...## ##...## .#####.
9 .#####. ##...## ##...## .###### .....## .....## .#####.
! ## ## ## ## ## .. ##
? .#####. ##...## .....## ...###. ..##... ....... ..##...
. .. .. .. .. .. ## ##
, .. .. .. .. .. ## ## #.
: .. ## ## .. ## ## ..
; .. ## ## .. ## ## #.
' ## ## #.
" ##.## ##.## #..#.
- ..... ..... ..... ##### ..... ..... .....
– ...... ...... ...... ###### ...... ...... ......
— ........ ........ ........ ######## ........ ........ ........
( ..## .##. ##.. ##.. ##.. .##. ..##
) ##.. .##. ..## ..## ..## .##. ##..
[ #### ##.. ##.. ##.. ##.. ##.. ####
] #### ..## ..## ..## ..## ..## ####
/ .....## ....##. ...##.. ..##... .##.... ##..... #......
\\ ##..... .##.... ..##... ...##.. ....##. .....## ......#
$ ..##... .#####. ##..... .#####. .....## .#####. ..##...
% ##...## ##..##. ....##. ...##.. ..##... .##..## ##...##
& ..###.. .##.##. ..###.. .###.## ##.###. ##..##. .###.##
# .##.##. .##.##. ####### .##.##. ####### .##.##. .##.##.
+ ...... ..##.. ..##.. ###### ..##.. ..##.. ......
= ...... ...... ###### ...... ###### ...... ......
* ....... .##.##. ..###.. ####### ..###.. .##.##. .......
@ .#####. ##...## ##.#### ##.#.## ##.#### ##..... .#####.
< ...## ..##. .##.. ##... .##.. ..##. ...##
> ##... .##.. ..##. ...## ..##. .##.. ##...
_ ....... ....... ....... ....... ....... ....... ....... #######
| ## ## ## ## ## ## ## ##
^ ..#.. .###. ##.## ..... .....
~ .###.## ##.###. ....... .......
\` ##. .## ...
× ....... ##...## .##.##. ..###.. .##.##. ##...## .......
· .. .. .. ## ## .. ..
• .... .... .##. #### #### .##. ....
… ........ ........ ........ ........ ........ ##.##.## ##.##.##
✦ ...#... ...#... ..###.. ####### ..###.. ...#... ...#...
♥ .##.##. ####### ####### ####### .#####. ..###.. ...#...
→ ....... ....#.. ....##. ####### ....##. ....#.. .......
← ....... ..#.... .##.... ####### .##.... ..#.... .......
↑ ...#... ..###.. .#####. ...#... ...#... ...#... ...#...
↓ ...#... ...#... ...#... ...#... .#####. ..###.. ...#...
▶ ##.... ####.. ###### ####### ###### ####.. ##....
◀ ....## ..#### ###### ####### ###### ..#### ....##
✓ ......# .....## ....##. ##.##.. .###... ..#....
€ ..#####. .##..... ######.. .##..... ######.. .##..... ..#####.
■ ###### ###### ###### ###### ###### ######
∝ ....... .##..## #..##.. #..#... #..##.. .##..## .......
ö .##.##. ....... .#####. ##...## ##...## ##...## .#####.
é ....##. ...##.. .#####. ##...## ####### ##..... .#####.
ü .##.##. ....... ##...## ##...## ##...## ##...## .######
`;

;
// ---- styles/demoscene/kit.js ----
// kit.js: the "demoscene" style's engine: a 1996 PC demo's software renderer, running in the page.
// Every frame is painted into a 640×360 framebuffer of palette indices (FB) with a 256-colour VGA palette, then shown ×3 at 1920×1080
// with nearest-neighbour (and a soft CRT glow). Effects are the classic per-pixel loops (plasma, tunnel, rotozoom, fire…), 3D is a
// z-buffered flat/Gouraud rasterizer, type is bitmap fonts drawn in code. Read STYLE.md before painting a part.
// Everything is a pure function of song time: no Math.random(), no state carried between frames (effects that are stateful in a
// real demo, like fire and "infinite bobs", re-simulate a fixed number of steps up to t).
OVERLAYS.length = 0;   // (the zine's caption, stamp and grain overlays: this style draws its own, bottom of this file)

// =====================================================================================================
// SCREEN
// =====================================================================================================
const SW = 640, SH = 360, SN = SW * SH, PXS = W / SW;   // 1 demo pixel = 3×3 output pixels at 1080p
const FB = new Uint8Array(SN);        // palette indices, row-major
const ZB = new Float32Array(SN);      // 1/z of the nearest 3D surface drawn (0 = nothing)
const FB2 = new Uint8Array(SN);       // scratch copy for post effects (squash, mirror, wobble)
const _scr = makeCanvas(SW, SH), _sg = _scr.getContext('2d');
const _img = _sg.createImageData(SW, SH), _u32 = new Uint32Array(_img.data.buffer);
// A slower device gets a lighter load (LOWQ): the heavy per-pixel effects run chunkier, fire at 2×2, and the glow is skipped. The
// page sets it, as one of its quality levels (modern/wire.js's setQuality), from how long frames really take to reach the screen;
// it's never taken from the canvas's size, since the framebuffer's loops cost the same at any size, and a player docked small on a
// desktop needs the full effects' detail most. Off wherever nothing sets it (the studio page, render mode).
let LOWQ = false;
SCALE_HOOKS.push(() => { _upC = null; });

// =====================================================================================================
// PALETTE: 256 VGA colours. Three 64-shade effect ramps a part loads for itself, and four 16-shade house ramps for type.
// =====================================================================================================
const RA = 0, RB = 64, RC = 128;                          // effect ramps (a part's own: plasma, tunnel, 3D shading, …)
const HC = 192, HM = 208, HO = 224, HS = 240;             // house ramps: MC Token cyan, Softmax magenta, Clawd orange, steel
const BLACK = 240, WHITE = 255;                           // (the steel ramp's ends)
const BG = '#07060f';
const VGA = new Uint8Array(768);                          // this frame's palette (r, g, b), in the VGA DAC's 64 levels per channel
const P32 = new Uint32Array(256);
const _rgb = h => [parseInt(h.slice(1, 3), 16), parseInt(h.slice(3, 5), 16), parseInt(h.slice(5, 7), 16)];
const _rampCache = new Map();
// A ramp of n shades through colour stops (evenly spaced, or [pos, hex] pairs). Cached by its stops.
function ramp(stops, n = 64) {
  const key = n + '|' + stops.join();
  let r = _rampCache.get(key);
  if (r) return r;
  const S = stops.map((s, i) => Array.isArray(s) ? [s[0], _rgb(s[1])] : [i / (stops.length - 1), _rgb(s)]);
  r = new Uint8Array(n * 3);
  for (let i = 0; i < n; i++) {
    const k = i / (n - 1);
    let j = 0; while (j < S.length - 2 && k > S[j + 1][0]) j++;
    const [k0, c0] = S[j], [k1, c1] = S[j + 1], f = clamp((k - k0) / (k1 - k0 || 1));
    for (let c = 0; c < 3; c++) r[i * 3 + c] = Math.round(Math.round(lerp(c0[c], c1[c], f) / 255 * 63) * 255 / 63);   // (the VGA DAC's 6 bits)
  }
  _rampCache.set(key, r);
  return r;
}
// Load a ramp into the palette at index `at` (RA, RB, RC, or anywhere for a short one).
function setRamp(at, stops, n = 64) { VGA.set(ramp(stops, n), at * 3); }
// The brightness (0..255) of palette colour i as this frame's palette has it.
const lumOf = i => VGA[i * 3] * .3 + VGA[i * 3 + 1] * .59 + VGA[i * 3 + 2] * .11;
function setCol(i, hex) { const [r, g, b] = _rgb(hex); VGA[i * 3] = r; VGA[i * 3 + 1] = g; VGA[i * 3 + 2] = b; }
// The house ramps, restored every frame (a part may borrow them, like text mode's 16 colours).
const RAMPS = {
  cyan: [BG, '#0b2a4a', '#0a6d9e', '#17c0ec', '#8af2ff', '#f2ffff'],
  magenta: [BG, '#2e0a3c', '#8c1474', '#f1289e', '#ff90d2', '#fff2fb'],
  orange: [BG, '#3c0e06', '#9b3114', '#d97757', '#ffb45c', '#fff3c8'],
  steel: [BG, '#161b38', '#3c4878', '#8592c6', '#d5dcff', '#ffffff'],
  fire: ['#000000', '#3a0602', '#8f1a04', '#d9481a', '#f59a2a', '#ffd873', '#fffbe8'],
  gold: [BG, '#3a2404', '#8d5c0e', '#dfa826', '#ffe487', '#fffdf0'],
  night: [BG, '#0b0f2a', '#1a2358', '#34479a', '#6f86d6', '#c9d6ff'],
  green: [BG, '#062414', '#0d5c2c', '#1fae4c', '#8ef08a', '#f0ffe8'],
  red: [BG, '#2e0406', '#7a0b12', '#d61d2a', '#ff7a6e', '#fff0ea'],
  blue: [BG, '#06123a', '#0c2f8c', '#1f5ce0', '#79a8ff', '#eef4ff'],
  yellow: [BG, '#2a2204', '#7a6208', '#e2c216', '#fff07a', '#fffff0'],
};
function _houseRamps() { setRamp(HC, RAMPS.cyan, 16); setRamp(HM, RAMPS.magenta, 16); setRamp(HO, RAMPS.orange, 16); setRamp(HS, RAMPS.steel, 16); }
// A part loads its own effect ramps each frame; before it does, they're these (so nothing leaks from one frame to the next).
function _defaultRamps() { setRamp(RA, RAMPS.night); setRamp(RB, RAMPS.cyan); setRamp(RC, RAMPS.orange); }
_houseRamps(); _defaultRamps();
const HOUSE = { cyan: HC, magenta: HM, orange: HO, steel: HS };
// Index of shade k (0..1) in a 64-shade ramp at `at`; hk() the same in a 16-shade house ramp.
const rk = (at, k) => at + clamp(Math.round(k * 63), 0, 63);
const hk = (at, k) => at + clamp(Math.round(k * 15), 0, 15);
// Ramp-aware shading tables: DIMT[n][i] is colour i n shades darker within its own ramp (a house ramp counts 4 of its shades as 1),
// LITT[n][i] n shades lighter (saturating). They make shadows, glenz and additive light without leaving the palette.
const DIMT = [], LITT = [];
for (let n = 0; n <= 64; n++) {
  const d = new Uint8Array(256), l = new Uint8Array(256);
  for (let i = 0; i < 256; i++) {
    if (i < 192) { const b = i & ~63, s = i & 63; d[i] = b + Math.max(0, s - n); l[i] = b + Math.min(63, s + n); }
    else { const b = i & ~15, s = i & 15, m = Math.round(n / 4); d[i] = b + Math.max(0, s - m); l[i] = b + Math.min(15, s + m); }
  }
  DIMT.push(d); LITT.push(l);
}
// The frame's palette effects, reset every frame: flash (toward white), fade (toward black), and a pump of light on the kick.
const PFX = { flash: 0, fade: 0, pump: 0, glow: .55, tint: null };
const flash = k => { PFX.flash = Math.max(PFX.flash, clamp(k)); };
const fadeOut = k => { PFX.fade = Math.max(PFX.fade, clamp(k)); };
const setGlow = k => { PFX.glow = k; };

// =====================================================================================================
// TIME, BEAT AND SOUND
// =====================================================================================================
// The take's beat grid (TIMING.bpm/beat0, via core.js): bt(t) is the beat position, beatT(n) the time of beat n.
const bt = t => bpOf(t);
const beatT = n => onBeat(0, n);
const kick = (t, k = 7) => Math.exp(-frac(bpOf(t)) * k);          // 1 on each beat, decaying
const kick8 = (t, k = 7) => Math.exp(-frac(bpOf(t) * 2) * k);     // on eighths
const _aud = (arr, t) => { const f = t * AUDIO_FPS, i = Math.floor(f); if (i < 0 || i >= arr.length - 1) return 0; return lerp(arr[i], arr[i + 1], f - i); };
// The singers' loudness (0..1), their pitch (a MIDI note, 0 when unvoiced) and the mix's low end, from audio.js.
const vox = t => _aud(VOX_RMS, t) / 255;
const voxNote = t => { const i = Math.round(t * AUDIO_FPS); return i >= 0 && i < VOX_NOTE.length ? VOX_NOTE[i] : 0; };
const lowEnd = t => _aud(MIX_LOW, t) / 255;
// The mix's spectrum at t: 16 bands, low to high, each 0..1 (interpolated between audio.js's 25 frames a second). out: reused array.
function spectrum(t, out = new Float32Array(SPEC_BANDS)) {
  const f = t * SPEC_FPS, i = Math.floor(f), k = f - i, n = MIX_SPEC.length / SPEC_BANDS;
  for (let b = 0; b < SPEC_BANDS; b++) {
    const a = i >= 0 && i < n ? MIX_SPEC[i * SPEC_BANDS + b] : 0, c = i + 1 >= 0 && i + 1 < n ? MIX_SPEC[(i + 1) * SPEC_BANDS + b] : 0;
    out[b] = lerp(a, c, k) / 255;
  }
  return out;
}
// Seconds from a window's start to its k-th beat (k = 0: the first beat at or after the start).
const beatIn = (t, lt, k = 0) => beatT(Math.ceil(bt(t - lt) - 1e-3) + k) - (t - lt);

// =====================================================================================================
// PIXELS
// =====================================================================================================
let CX0 = 0, CY0 = 0, CX1 = SW, CY1 = SH;   // clip rectangle
const clip = (x0, y0, x1, y1) => { CX0 = Math.max(0, x0 | 0); CY0 = Math.max(0, y0 | 0); CX1 = Math.min(SW, Math.ceil(x1)); CY1 = Math.min(SH, Math.ceil(y1)); };
const noClip = () => { CX0 = 0; CY0 = 0; CX1 = SW; CY1 = SH; };
const cls = (c = 0) => FB.fill(c);
function pset(x, y, c) { x |= 0; y |= 0; if (x >= CX0 && x < CX1 && y >= CY0 && y < CY1) FB[y * SW + x] = c; }
function hspan(x0, x1, y, c) {
  y |= 0; if (y < CY0 || y >= CY1) return;
  x0 = Math.max(CX0, Math.round(x0)); x1 = Math.min(CX1, Math.round(x1)); if (x1 > x0) FB.fill(c, y * SW + x0, y * SW + x1);
}
function rectf(x, y, w, h, c) { for (let j = Math.round(y), e = Math.round(y + h); j < e; j++) hspan(x, x + w, j, c); }
// Darken (or lighten, n < 0) an area by n shades within each pixel's own ramp: plates behind text, shadows, beams of light.
function shadeRect(x, y, w, h, n) {
  const T = n >= 0 ? DIMT[Math.min(64, n)] : LITT[Math.min(64, -n)];
  const x0 = Math.max(CX0, Math.round(x)), x1 = Math.min(CX1, Math.round(x + w)), y0 = Math.max(CY0, Math.round(y)), y1 = Math.min(CY1, Math.round(y + h));
  for (let j = y0; j < y1; j++) for (let i = j * SW + x0, e = j * SW + x1; i < e; i++) FB[i] = T[FB[i]];
}
function shadePx(x, y, n) { x |= 0; y |= 0; if (x >= CX0 && x < CX1 && y >= CY0 && y < CY1) { const i = y * SW + x; FB[i] = (n >= 0 ? DIMT[n] : LITT[-n])[FB[i]]; } }
// Bresenham line; `c` a colour, or a function (x, y) → colour | -1.
function lineP(x0, y0, x1, y1, c) {
  x0 = Math.round(x0); y0 = Math.round(y0); x1 = Math.round(x1); y1 = Math.round(y1);
  const dx = Math.abs(x1 - x0), dy = -Math.abs(y1 - y0), sx = x0 < x1 ? 1 : -1, sy = y0 < y1 ? 1 : -1;
  let e = dx + dy, n = 0;
  for (;;) {
    if (typeof c === 'function') { const v = c(x0, y0, n); if (v >= 0) pset(x0, y0, v); } else pset(x0, y0, c);
    if ((x0 === x1 && y0 === y1) || ++n > 4000) break;
    const e2 = 2 * e;
    if (e2 >= dy) { e += dy; x0 += sx; }
    if (e2 <= dx) { e += dx; y0 += sy; }
  }
}
function circf(cx, cy, r, c) { for (let y = Math.ceil(cy - r); y <= cy + r; y++) { const w = Math.sqrt(Math.max(0, r * r - (y - cy) ** 2)); hspan(cx - w, cx + w + 1, y, c); } }
// Polygon fill (even-odd), sampled at pixel centres. pts = [[x, y], …].
function polyf(pts, c) {
  let y0 = Infinity, y1 = -Infinity; for (const p of pts) { y0 = Math.min(y0, p[1]); y1 = Math.max(y1, p[1]); }
  const xs = [];
  for (let y = Math.max(CY0, Math.ceil(y0 - .5)); y < Math.min(CY1, y1); y++) {
    const sy = y + .5; xs.length = 0;
    for (let i = 0, n = pts.length; i < n; i++) {
      const [ax, ay] = pts[i], [bx, by] = pts[(i + 1) % n];
      if ((ay <= sy) !== (by <= sy)) xs.push(ax + (sy - ay) / (by - ay) * (bx - ax));
    }
    xs.sort((a, b) => a - b);
    for (let i = 0; i + 1 < xs.length; i += 2) hspan(Math.round(xs[i]), Math.round(xs[i + 1]), y, c);
  }
}

// =====================================================================================================
// FONTS: the 8×8 font (font.js), text mode's 8×16 cells, and the big fonts (Scale2x/Scale3x of the 8×8)
// =====================================================================================================
const G8 = {};
for (const raw of FONT8_SRC.split('\n')) {
  const s = raw.replace(/\s+$/, ''); if (!s) continue;
  const ch = [...s][0], rows = s.slice(ch.length).trim().split(/\s+/);
  const w = rows[0].length, bits = new Uint8Array(8 * w);
  rows.forEach((r, y) => [...r].forEach((c, x) => { if (c === '#') bits[y * w + x] = 1; }));
  G8[ch] = { w, bits };
}
G8[' '] = { w: 4, bits: new Uint8Array(32) };
const _ALIAS = { '’': "'", '‘': "'", 'ʼ': "'", '“': '"', '”': '"', '‑': '-', 'Ö': 'O', 'É': 'E', 'Ü': 'U', 'Á': 'A', 'á': 'a', 'ó': 'o', 'í': 'i', 'ñ': 'n', 'ç': 'c' };
function glyph(ch) { return G8[ch] || G8[_ALIAS[ch]] || G8[ch.toUpperCase()] || G8['?']; }
// Small text in the 8×8 font. o: mono (8-px cells, like text mode), sc (integer scale), shadow (colour, or n > 0 for a darkening
// of n shades), align ('left'|'center'|'right'), n (draw only the first n characters: typing), gap. Returns the width.
function text8W(str, o = {}) {
  const sc = o.sc || 1, gap = o.gap ?? 1; let w = 0;
  for (const ch of String(str)) w += (o.mono ? 8 : glyph(ch).w + gap) * sc;
  return w - (o.mono ? 0 : gap * sc);
}
function text8(str, x, y, c, o = {}) {
  const sc = o.sc || 1, gap = o.gap ?? 1, s = [...String(str)], n = o.n ?? s.length;
  const w = text8W(str, o);
  let cx = Math.round(o.align === 'center' ? x - w / 2 : o.align === 'right' ? x - w : x); y = Math.round(y);
  for (let i = 0; i < Math.min(n, s.length); i++) {
    const g = glyph(s[i]), ox = o.mono ? Math.floor((8 - g.w) / 2) : 0, col = typeof c === 'function' ? c(i) : c;
    for (let gy = 0; gy < 8; gy++) for (let gx = 0; gx < g.w; gx++) if (g.bits[gy * g.w + gx]) {
      const px = cx + (ox + gx) * sc, py = y + gy * sc;
      if (o.shadow !== undefined) rectf(px + sc, py + sc, sc, sc, o.shadow);        // a solid drop shadow
      else if (o.shadowN) for (let a = 0; a < sc; a++) for (let b = 0; b < sc; b++) shadePx(px + b + sc, py + a + sc, o.shadowN);
    }
    for (let gy = 0; gy < 8; gy++) for (let gx = 0; gx < g.w; gx++) if (g.bits[gy * g.w + gx]) rectf(cx + (ox + gx) * sc, y + gy * sc, sc, sc, col);
    cx += (o.mono ? 8 : g.w + gap) * sc;
  }
  return w;
}

// ---- text mode: 80 columns of 8×16 cells (the 8×8 font, each row doubled) and the CP437 blocks, shades and box lines ----
const TMC = 80, TMR = 23;                            // (360 / 16 = 22.5 rows; the 23rd is half off-screen, which a scroll hides)
const TM = { ch: new Array(TMC * TMR * 4).fill(' '), fg: new Uint8Array(TMC * TMR * 4), bg: new Uint8Array(TMC * TMR * 4), rows: TMR * 4 };
// The 16 text-mode colours (CGA/VGA), loaded at RA while a part draws text mode.
const CGA = ['#000000', '#0000aa', '#00aa00', '#00aaaa', '#aa0000', '#aa00aa', '#aa5500', '#aaaaaa', '#555555', '#5555ff', '#55ff55', '#55ffff', '#ff5555', '#ff55ff', '#ffff55', '#ffffff'];
function tmPalette() { CGA.forEach((h, i) => setCol(RA + i, h)); }
function tmClear(bg = 0) { TM.ch.fill(' '); TM.fg.fill(7); TM.bg.fill(bg); }
function tmPut(col, row, str, fg = 7, bg = -1) {
  let i = 0;
  for (const ch of String(str)) {
    const x = col + i++; if (x < 0 || x >= TMC || row < 0 || row >= TM.rows) continue;
    const k = row * TMC + x; TM.ch[k] = ch; TM.fg[k] = fg; if (bg >= 0) TM.bg[k] = bg;
  }
}
// 8×16 cell bitmaps: letters from the 8×8 font (rows doubled), CP437 blocks/shades/lines drawn here.
const _cell16 = new Map();
function cell16(ch) {
  let b = _cell16.get(ch);
  if (b) return b;
  b = new Uint8Array(128);
  const set = f => { for (let y = 0; y < 16; y++) for (let x = 0; x < 8; x++) b[y * 8 + x] = f(x, y) ? 1 : 0; };
  const H = y => y === 7 || y === 8, V = x => x === 3 || x === 4, HH = y => y === 6 || y === 9, VV = x => x === 2 || x === 5;
  switch (ch) {
    case '█': set(() => 1); break;
    case '▀': set((x, y) => y < 8); break;
    case '▄': set((x, y) => y >= 8); break;
    case '▌': set(x => x < 4); break;
    case '▐': set(x => x >= 4); break;
    case '░': set((x, y) => (x + (y >> 1) * 2) % 4 === 0 && y % 2 === 0); break;
    case '▒': set((x, y) => (x + y) % 2 === 0); break;
    case '▓': set((x, y) => !((x + (y >> 1) * 2) % 4 === 0 && y % 2 === 0)); break;
    case '─': set((x, y) => H(y)); break;
    case '│': set(x => V(x)); break;
    case '┌': set((x, y) => (H(y) && x >= 3) || (V(x) && y >= 7)); break;
    case '┐': set((x, y) => (H(y) && x <= 4) || (V(x) && y >= 7)); break;
    case '└': set((x, y) => (H(y) && x >= 3) || (V(x) && y <= 8)); break;
    case '┘': set((x, y) => (H(y) && x <= 4) || (V(x) && y <= 8)); break;
    case '├': set((x, y) => V(x) || (H(y) && x >= 3)); break;
    case '┤': set((x, y) => V(x) || (H(y) && x <= 4)); break;
    case '═': set((x, y) => HH(y)); break;
    case '║': set(x => VV(x)); break;
    case '╔': set((x, y) => (y === 6 && x >= 2) || (y === 9 && x >= 5) || (x === 2 && y >= 6) || (x === 5 && y >= 9)); break;
    case '╗': set((x, y) => (y === 6 && x <= 5) || (y === 9 && x <= 2) || (x === 5 && y >= 6) || (x === 2 && y >= 9)); break;
    case '╚': set((x, y) => (y === 9 && x >= 2) || (y === 6 && x >= 5) || (x === 2 && y <= 9) || (x === 5 && y <= 6)); break;
    case '╝': set((x, y) => (y === 9 && x <= 5) || (y === 6 && x <= 2) || (x === 5 && y <= 9) || (x === 2 && y <= 6)); break;
    case '▪': set((x, y) => x >= 2 && x <= 5 && y >= 6 && y <= 9); break;
    default: {
      const g = glyph(ch), ox = Math.floor((8 - g.w) / 2);
      for (let y = 0; y < 16; y++) for (let x = 0; x < g.w; x++) if (x + ox < 8 && g.bits[(y >> 1) * g.w + x]) b[y * 8 + x + ox] = 1;
    }
  }
  _cell16.set(ch, b);
  return b;
}
// Draw the text-mode grid, scrolled up by `scroll` pixels, at palette base `pal` (RA once tmPalette() has loaded the colours).
// o.blinkOn: whether blinking cells (fg ≥ 16) show this frame.
function tmRender(scroll = 0, o = {}) {
  const pal = o.pal ?? RA, top = o.top ?? 4;
  const r0 = Math.max(0, Math.floor((scroll - top) / 16)), r1 = Math.min(TM.rows, Math.ceil((scroll - top + SH) / 16) + 1);
  for (let r = r0; r < r1; r++) {
    const y0 = top + r * 16 - Math.round(scroll);
    for (let c = 0; c < TMC; c++) {
      const k = r * TMC + c, bits = cell16(TM.ch[k]);
      let fg = TM.fg[k]; const blink = fg >= 16; fg &= 15;
      const bgc = pal + TM.bg[k], fgc = pal + fg, on = !blink || o.blinkOn !== false;
      for (let y = 0; y < 16; y++) {
        const py = y0 + y; if (py < CY0 || py >= CY1) continue;
        const row = py * SW + c * 8;
        for (let x = 0; x < 8; x++) FB[row + x] = on && bits[y * 8 + x] ? fgc : bgc;
      }
    }
  }
}
// Half-block ANSI letters: text in the 8×8 font as ▀▄█ characters, 1 cell per pixel column and 2 pixel rows per cell.
function tmBig(col, row, str, fg, o = {}) {
  let x = col;
  for (const ch of String(str)) {
    const g = glyph(ch);
    for (let cy = 0; cy < 4; cy++) for (let gx = 0; gx < g.w; gx++) {
      const a = g.bits[(cy * 2) * g.w + gx], b = g.bits[(cy * 2 + 1) * g.w + gx];
      if (!a && !b) { if (o.shade && gx > 0 && (g.bits[(cy * 2) * g.w + gx - 1] || g.bits[(cy * 2 + 1) * g.w + gx - 1])) tmPut(x + gx, row + cy, '░', o.shade); continue; }
      tmPut(x + gx, row + cy, a && b ? '█' : a ? '▀' : '▄', typeof fg === 'function' ? fg(gx, cy) : fg);
    }
    x += g.w + (o.gap ?? 1);
  }
  return x - col;
}

// ---- big fonts: the 8×8 glyphs scaled with Scale2x/Scale3x (smooth diagonals, still pixel-crisp), then shaded like 1996 ----
function _scale2x(src, w, h) {
  const out = new Uint8Array(w * h * 4), W2 = w * 2, g = (x, y) => x < 0 || y < 0 || x >= w || y >= h ? 0 : src[y * w + x];
  for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) {
    const P = g(x, y), A = g(x, y - 1), B = g(x + 1, y), C = g(x - 1, y), D = g(x, y + 1);
    out[(2 * y) * W2 + 2 * x] = C === A && C !== D && A !== B ? A : P;
    out[(2 * y) * W2 + 2 * x + 1] = A === B && A !== C && B !== D ? B : P;
    out[(2 * y + 1) * W2 + 2 * x] = D === C && D !== B && C !== A ? C : P;
    out[(2 * y + 1) * W2 + 2 * x + 1] = B === D && B !== A && D !== C ? D : P;
  }
  return out;
}
function _scale3x(src, w, h) {
  const out = new Uint8Array(w * h * 9), W3 = w * 3, g = (x, y) => x < 0 || y < 0 || x >= w || y >= h ? 0 : src[y * w + x];
  for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) {
    const A = g(x - 1, y - 1), B = g(x, y - 1), C = g(x + 1, y - 1), D = g(x - 1, y), E = g(x, y), F = g(x + 1, y), G = g(x - 1, y + 1), Hh = g(x, y + 1), I = g(x + 1, y + 1);
    const e = [E, E, E, E, E, E, E, E, E];
    if (B !== Hh && D !== F) {
      e[0] = D === B ? D : E;
      e[1] = (D === B && E !== C) || (B === F && E !== A) ? B : E;
      e[2] = B === F ? F : E;
      e[3] = (D === B && E !== G) || (D === Hh && E !== A) ? D : E;
      e[5] = (B === F && E !== I) || (Hh === F && E !== C) ? F : E;
      e[6] = D === Hh ? D : E;
      e[7] = (D === Hh && E !== I) || (Hh === F && E !== G) ? Hh : E;
      e[8] = Hh === F ? F : E;
    }
    for (let j = 0; j < 9; j++) out[(3 * y + Math.floor(j / 3)) * W3 + 3 * x + j % 3] = e[j];
  }
  return out;
}
// A glyph's mask at a big-font scale: 1 (8 px), 2 (16), 3 (24), 4 (32), 6 (48), 8 (64).
const _bigG = new Map();
function bigGlyph(ch, s) {
  const key = ch + '|' + s; let b = _bigG.get(key);
  if (b) return b;
  const g = glyph(ch); let m = g.bits, w = g.w, h = 8;
  const steps = { 1: [], 2: [2], 3: [3], 4: [2, 2], 6: [2, 3], 8: [2, 2, 2] }[s] || [2];
  for (const k of steps) { m = k === 2 ? _scale2x(m, w, h) : _scale3x(m, w, h); w *= k; h *= k; }
  b = { w, h, m }; _bigG.set(key, b);
  return b;
}
// Lay out a line of big text: its shaded pixels (0 empty, 1 outline, 2..17 shade 0..15) and each character's x.
// The shading is 1996 "copper" type: a vertical gradient with a bright horizon line, lit top edges, shaded bottom edges, a dark outline.
const _bigL = new Map();
function bigForm(s, keep) { const a = [...String(s)].map(c => _ALIAS[c] || c).join('').replace(/[“”]/g, '"'); return keep ? a : a.toUpperCase(); }
function bigLayout(str, s = 2, o = {}) {
  const key = str + '|' + s + '|' + (o.grad || '') + '|' + (o.gap ?? ''); let L = _bigL.get(key);
  if (L) return L;
  const chars = [...str], gap = o.gap ?? Math.max(1, s), pad = 1;
  const xs = [], gs = chars.map(c => bigGlyph(c, s));
  let w = pad;
  gs.forEach((g, i) => { xs.push(w); w += (chars[i] === ' ' ? 4 * s : g.w) + gap; });
  w += pad - gap; const h = 8 * s + 2 * pad;
  const m = new Uint8Array(w * h);
  gs.forEach((g, i) => { if (chars[i] === ' ') return; for (let y = 0; y < g.h; y++) for (let x = 0; x < g.w; x++) if (g.m[y * g.w + x]) m[(y + pad) * w + xs[i] + x] = 1; });
  const out = new Uint8Array(w * h), gh = 7 * s;   // (cap height: row 8 is the descender)
  const grad = o.grad === 'flat' ? () => .75 : o.grad === 'chrome'
    ? k => k < .48 ? lerp(1, .55, k / .48) : k < .56 ? 1 : lerp(.35, .8, (k - .56) / .44)
    : k => k < .08 ? 1 : k < .5 ? lerp(.95, .62, (k - .08) / .42) : k < .56 ? .98 : lerp(.72, .4, (k - .56) / .44);
  for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) {
    const i = y * w + x;
    if (m[i]) {
      let v = grad(clamp((y - pad) / gh));
      if (!m[i - w]) v += .25; else if (y + 1 < h && !m[i + w]) v -= .22;
      out[i] = 2 + clamp(Math.round(v * 15), 0, 15);
    } else if (m[i - 1] || m[i + 1] || m[i - w] || m[i + w]) out[i] = 1;
  }
  L = { w, h, m: out, xs, pad, s, chars };
  _bigL.set(key, L);
  return L;
}
// Draw big text. o: s (scale), ramp (house ramp base: HC, HM, HO, HS, or any 16-colour ramp's index), align, gap, grad
// ('copper' default | 'chrome' | 'flat'), outline (colour | -1 none), shadow (shades of darkening, 0 none; default 6) and its offset
// (sx, sy), dy(x) (column displacement: sine scrollers), n (characters shown: typing), level (0..1 brightness, for fades), keep (keep
// lower case, for handles: the 8×8 font's lowercase scales as well),
// colour(i) → a ramp base per character (sung/unsung words). Returns {x, w, h}.
function bigText(str, x, y, o = {}) {
  str = bigForm(str, o.keep);
  const L = bigLayout(str, o.s ?? 2, o), base = o.ramp ?? HS, lv = o.level ?? 1;
  const x0 = Math.round(o.align === 'center' ? x - L.w / 2 : o.align === 'right' ? x - L.w : x), y0 = Math.round(y) - L.pad;
  const nMax = o.n ?? L.chars.length, xMax = nMax >= L.chars.length ? L.w : L.xs[Math.max(0, nMax)] ?? L.w;
  const ol = o.outline ?? BLACK, sh = o.shadow ?? 6, sx = o.sx ?? Math.max(1, L.s), sy = o.sy ?? Math.max(1, L.s);
  const dy = o.dy, colOf = o.colour;
  const xa = Math.max(0, CX0 - x0 - sx - 1), xb = Math.min(L.w, xMax, CX1 - x0);
  // shadow pass, then the letters
  if (sh > 0) {
    const T = DIMT[Math.min(64, sh)];
    for (let x = xa; x < xb; x++) {
      const px = x0 + x + sx; if (px < CX0 || px >= CX1) continue;
      const oy = dy ? Math.round(dy(px - sx)) : 0;
      for (let y = 0; y < L.h; y++) if (L.m[y * L.w + x] > 1) { const py = y0 + y + sy + oy; if (py >= CY0 && py < CY1) FB[py * SW + px] = T[FB[py * SW + px]]; }
    }
  }
  let ci = 0, cb = base, cl = lv, lastCi = -1;
  for (let x = Math.max(0, CX0 - x0); x < xb; x++) {
    const px = x0 + x;
    if (colOf) {
      while (ci + 1 < L.xs.length && L.xs[ci + 1] <= x) ci++;
      if (ci !== lastCi) { const r = colOf(ci); if (Array.isArray(r)) { cb = r[0]; cl = r[1] * lv; } else { cb = r; cl = lv; } lastCi = ci; }
    }
    const oy = dy ? Math.round(dy(px)) : 0;
    for (let y = 0; y < L.h; y++) {
      const v = L.m[y * L.w + x]; if (!v) continue;
      const py = y0 + y + oy; if (py < CY0 || py >= CY1) continue;
      if (v === 1) { if (ol >= 0) FB[py * SW + px] = ol; }
      else FB[py * SW + px] = cb + clamp(Math.round((v - 2) * cl), 0, 15);
    }
  }
  return { x: x0, w: L.w, h: L.h };
}
const bigW = (str, s = 2, o = {}) => bigLayout(bigForm(str, o.keep), s, o).w;

// =====================================================================================================
// SPRITES: bobs (shaded balls, the Amiga's "vector bobs") and the pixel DJ Clawd
// =====================================================================================================
const _balls = new Map();
// A ball of radius r: shade 0..63 per pixel (-1 outside), lit from the upper left with a hot spot.
function ballSpr(r) {
  r = Math.max(1, Math.round(r * 2) / 2);
  let b = _balls.get(r); if (b) return b;
  const n = Math.ceil(r) * 2 + 1, c = (n - 1) / 2, m = new Int8Array(n * n).fill(-1);
  for (let y = 0; y < n; y++) for (let x = 0; x < n; x++) {
    const dx = (x - c) / (r + .35), dy = (y - c) / (r + .35), d2 = dx * dx + dy * dy;
    if (d2 > 1) continue;
    const z = Math.sqrt(1 - d2), l = clamp(-.45 * dx - .6 * dy + .66 * z), spec = Math.pow(clamp(-.4 * dx - .55 * dy + .73 * z), 18);
    m[y * n + x] = clamp(Math.round((.12 + .72 * l + .5 * spec) * 63), 1, 63);
  }
  b = { n, c, m }; _balls.set(r, b);
  return b;
}
// Draw a bob at (x, y), radius r, in the 64-shade ramp at `at`; k scales its brightness (depth fog). o.house: a 16-shade ramp instead.
function bob(x, y, r, at, k = 1, o = {}) {
  const B = ballSpr(r), x0 = Math.round(x - B.c), y0 = Math.round(y - B.c), house = o.house;
  for (let j = 0; j < B.n; j++) {
    const py = y0 + j; if (py < CY0 || py >= CY1) continue;
    for (let i = 0; i < B.n; i++) {
      const v = B.m[j * B.n + i]; if (v < 0) continue;
      const px = x0 + i; if (px < CX0 || px >= CX1) continue;
      FB[py * SW + px] = house ? at + clamp(Math.round(v * k / 4.2), 0, 15) : at + clamp(Math.round(v * k), 0, 63);
    }
  }
}
// DJ Clawd, the group's mascot: the pixel Clawd (a Claude-orange block with slit eyes, stubby arms and four legs) in DJ headphones.
// (x, y) = ground point under its middle; u = pixel size of its 10×6 body grid. o: eyes ('open'|'happy'|'closed'|'wide'), aL/aR (arm
// raise, −1..1), hop (px), phones (default true), shades, walk (phase), wave (right arm waving, 0..1 phase).
function djClawd(x, y, u = 4, o = {}) {
  x = Math.round(x); y = Math.round(y - (o.hop || 0)); u = Math.max(1, Math.round(u));
  const O = HO, body = O + 10, dk = O + 7, lit = O + 13, ink = BLACK;
  const bw = 10 * u, bh = 6 * u, legH = 2 * u, bx = x - 5 * u, by = y - legH - bh;
  // legs
  [-3.6, -1.4, 1.4, 3.6].forEach((lx, i) => {
    const lift = o.walk !== undefined ? Math.max(0, Math.round(Math.sin((o.walk + (i % 2) * .5) * TAU) * u)) : 0;
    rectf(x + Math.round(lx * u - u / 2), y - legH - lift, u, legH, dk);
  });
  // arms
  const arm = (side, a) => {
    const sx = side < 0 ? bx - 2 * u : bx + bw, sy = by + Math.round(2.2 * u) - Math.round(a * 2 * u);
    rectf(sx, sy, 2 * u, u + (a > .3 ? u : 0), body);
  };
  arm(-1, o.aL ?? 0);
  if (o.wave !== undefined) { const a = .8 + .5 * Math.sin(o.wave * TAU); rectf(bx + bw, by + Math.round(2.2 * u - a * 2.2 * u), u, Math.round(1.6 * u), body); rectf(bx + bw + u, by + Math.round(1.4 * u - a * 2.6 * u), u, Math.round(1.4 * u), body); }
  else arm(1, o.aR ?? 0);
  // body with light from the upper left
  rectf(bx, by, bw, bh, body);
  rectf(bx, by, bw, Math.max(1, u >> 1), lit); rectf(bx, by, Math.max(1, u >> 1), bh, O + 12);
  rectf(bx + bw - Math.max(1, u >> 1), by + 1, Math.max(1, u >> 1), bh - 1, dk); rectf(bx, by + bh - Math.max(1, u >> 1), bw, Math.max(1, u >> 1), dk);
  // eyes
  const ew = u, eh = Math.round(1.6 * u), eyes = o.eyes ?? 'open';
  for (const side of [-1, 1]) {
    const ex = x + Math.round(side * 2.3 * u - ew / 2), ey = by + Math.round(1.3 * u);
    if (o.shades) { rectf(ex - u, ey, ew + 2 * u, Math.round(u * 1.2), ink); continue; }
    if (eyes === 'open') rectf(ex, ey, ew, eh, ink);
    else if (eyes === 'wide') { rectf(ex - 1, ey - 1, ew + 2, eh + 2, WHITE); rectf(ex, ey, ew, eh, ink); }
    else if (eyes === 'happy') { rectf(ex - (u >> 1), ey + (u >> 1), ew + u, Math.max(1, u >> 1), ink); rectf(ex - (u >> 1), ey + u, Math.max(1, u >> 1), Math.max(1, u >> 1), ink); rectf(ex + ew, ey + u, Math.max(1, u >> 1), Math.max(1, u >> 1), ink); }
    else rectf(ex - (u >> 1), ey + eh - Math.max(1, u >> 1), ew + u, Math.max(1, u >> 1), ink);
  }
  if (o.shades) rectf(x - 2 * u, by + Math.round(1.5 * u), 4 * u, Math.max(1, u >> 1), ink);
  // headphones: a band over the top and two cups, with a cyan light on each
  if (o.phones !== false) {
    const band = HS + 4, cup = HS + 2;
    rectf(bx - Math.round(u * .6), by - Math.round(u * 1.4), bw + Math.round(u * 1.2), Math.max(1, Math.round(u * .6)), band);
    rectf(bx - Math.round(u * .6), by - Math.round(u * 1.4), Math.max(1, Math.round(u * .6)), Math.round(u * 1.8), band);
    rectf(bx + bw, by - Math.round(u * 1.4), Math.max(1, Math.round(u * .6)), Math.round(u * 1.8), band);
    for (const side of [-1, 1]) {
      const cx = side < 0 ? bx - Math.round(u * 1.4) : bx + bw - Math.round(u * .2);
      rectf(cx, by + Math.round(u * .3), Math.round(u * 1.6), Math.round(u * 2.2), cup);
      rectf(cx + Math.round(u * .5), by + Math.round(u * .9), Math.max(1, Math.round(u * .6)), Math.max(1, Math.round(u * .9)), HC + 13);
    }
  }
  return { top: by - Math.round(u * 1.4), bx, by, bw, bh };
}

// =====================================================================================================
// 3D: a z-buffered rasterizer for flat- and Gouraud-shaded triangles, meshes, and a projection
// =====================================================================================================
const CAM = { f: 300, cx: SW / 2, cy: SH / 2 };             // focal length (px) and screen centre; the camera looks down +z
const zclear = () => ZB.fill(0);
function rot3(ax = 0, ay = 0, az = 0) {
  const ca = Math.cos(ax), sa = Math.sin(ax), cb = Math.cos(ay), sb = Math.sin(ay), cc = Math.cos(az), sc = Math.sin(az);
  // R = Rz · Ry · Rx
  return [cb * cc, sa * sb * cc - ca * sc, ca * sb * cc + sa * sc,
          cb * sc, sa * sb * sc + ca * cc, ca * sb * sc - sa * cc,
          -sb, sa * cb, ca * cb];
}
const mmul = (A, B) => [0, 1, 2].flatMap(r => [0, 1, 2].map(c => A[r * 3] * B[c] + A[r * 3 + 1] * B[3 + c] + A[r * 3 + 2] * B[6 + c]));
const proj = (x, y, z) => { const iz = 1 / Math.max(.05, z); return [CAM.cx + x * CAM.f * iz, CAM.cy + y * CAM.f * iz, iz]; };
// One triangle. a/b/c = [sx, sy, 1/z, shade]; `at` the ramp base; flat if shades are equal. o.glenz: add shades to what's there
// instead of painting (see-through glass), o.len: ramp length (64, or 16 for a house ramp).
function tri3(a, b, c, at, o = {}) {
  const x0 = Math.max(CX0, Math.floor(Math.min(a[0], b[0], c[0]))), x1 = Math.min(CX1 - 1, Math.ceil(Math.max(a[0], b[0], c[0])));
  const y0 = Math.max(CY0, Math.floor(Math.min(a[1], b[1], c[1]))), y1 = Math.min(CY1 - 1, Math.ceil(Math.max(a[1], b[1], c[1])));
  if (x1 < x0 || y1 < y0) return;
  const area = (b[0] - a[0]) * (c[1] - a[1]) - (b[1] - a[1]) * (c[0] - a[0]);
  if (Math.abs(area) < 1e-6) return;
  const ia = 1 / area, len = (o.len ?? 64) - 1, glenz = o.glenz, noz = o.noz;
  for (let y = y0; y <= y1; y++) {
    const py = y + .5;
    for (let x = x0; x <= x1; x++) {
      const px = x + .5;
      let w0 = ((b[0] - px) * (c[1] - py) - (b[1] - py) * (c[0] - px)) * ia;
      let w1 = ((c[0] - px) * (a[1] - py) - (c[1] - py) * (a[0] - px)) * ia;
      const w2 = 1 - w0 - w1;
      if (w0 < 0 || w1 < 0 || w2 < 0) continue;
      const iz = w0 * a[2] + w1 * b[2] + w2 * c[2], i = y * SW + x;
      if (!noz) { if (iz <= ZB[i]) continue; ZB[i] = iz; }
      const s = w0 * a[3] + w1 * b[3] + w2 * c[3];
      if (glenz) FB[i] = LITT[clamp(Math.round(s * glenz), 0, 64)][FB[i]];
      else FB[i] = at + clamp(Math.round(s * len), 0, len);
    }
  }
}
// A mesh: v = [[x, y, z], …] (x right, y down, z into the screen), f = [[i0, i1, i2, …], …] (convex; wound so that
// cross(v1 − v0, v2 − v0) points outward), fm = per-face ramp base
// (optional), and its normals computed on first draw.
function mesh(v, f, fm) { return { v, f, fm }; }
function _normals(M) {
  if (M.fn) return;
  M.fn = M.f.map(f => {
    const [a, b, c] = [M.v[f[0]], M.v[f[1]], M.v[f[2]]];
    const u = [b[0] - a[0], b[1] - a[1], b[2] - a[2]], w = [c[0] - a[0], c[1] - a[1], c[2] - a[2]];
    const n = [u[1] * w[2] - u[2] * w[1], u[2] * w[0] - u[0] * w[2], u[0] * w[1] - u[1] * w[0]], l = Math.hypot(...n) || 1;
    return n.map(q => q / l);
  });
  M.vn = M.v.map(() => [0, 0, 0]);
  M.f.forEach((f, i) => f.forEach(j => { for (let k = 0; k < 3; k++) M.vn[j][k] += M.fn[i][k]; }));
  M.vn = M.vn.map(n => { const l = Math.hypot(...n) || 1; return n.map(q => q / l); });
}
// Draw a mesh rotated by R (rot3) and moved to pos. o: at (ramp base), len (ramp length), gouraud, light ([x, y, z] toward the light),
// amb (ambient, default .18), spec, glenz (see-through: shades added), scale, cull (default true), fog ([zNear, zFar]),
// vshade(v) → a multiplier per object-space vertex (a copper gradient down 3D letters: each row of the font gets its own band).
function drawMesh(M, R, pos, o = {}) {
  _normals(M);
  const sc = o.scale ?? 1, L = o.light ?? [-.45, -.6, -.66], ll = Math.hypot(...L), lx = L[0] / ll, ly = L[1] / ll, lz = L[2] / ll;
  const amb = o.amb ?? .18, at = o.at ?? RC, gour = o.gouraud;
  const P = M.v.map(([x, y, z]) => {
    const X = R[0] * x + R[1] * y + R[2] * z, Y = R[3] * x + R[4] * y + R[5] * z, Z = R[6] * x + R[7] * y + R[8] * z;
    return [X * sc + pos[0], Y * sc + pos[1], Z * sc + pos[2]];
  });
  const shadeN = n => { const X = R[0] * n[0] + R[1] * n[1] + R[2] * n[2], Y = R[3] * n[0] + R[4] * n[1] + R[5] * n[2], Z = R[6] * n[0] + R[7] * n[1] + R[8] * n[2]; const d = X * lx + Y * ly + Z * lz; return clamp(amb + (1 - amb) * Math.max(0, d) + (o.spec ? o.spec * Math.pow(Math.max(0, d), 12) : 0)); };
  const S = P.map(p => proj(p[0], p[1], p[2]));
  const vs = gour ? M.vn.map(shadeN) : null;
  M.f.forEach((f, i) => {
    const a = S[f[0]], b = S[f[1]], c = S[f[2]];
    if (o.cull !== false && (b[0] - a[0]) * (c[1] - a[1]) - (b[1] - a[1]) * (c[0] - a[0]) >= 0) return;
    if (P[f[0]][2] < .1 || P[f[1]][2] < .1 || P[f[2]][2] < .1) return;
    const fs = gour ? null : shadeN(M.fn[i]), base = M.fm ? M.fm[i] ?? at : at;
    let fog = 1; if (o.fog) fog = clamp(1 - (P[f[0]][2] - o.fog[0]) / (o.fog[1] - o.fog[0]), .15, 1);
    const V = j => [S[f[j]][0], S[f[j]][1], S[f[j]][2], (gour ? vs[f[j]] : fs) * fog * (o.vshade ? o.vshade(M.v[f[j]]) : 1)];
    for (let k = 1; k + 1 < f.length; k++) tri3(V(0), V(k), V(k + 1), base, { len: o.len ?? (base >= 192 ? 16 : 64), glenz: o.glenz, noz: o.noz });
  });
}
// Mesh builders.
function boxMesh(x0, y0, z0, x1, y1, z1, m) {
  const v = [[x0, y0, z0], [x1, y0, z0], [x1, y1, z0], [x0, y1, z0], [x0, y0, z1], [x1, y0, z1], [x1, y1, z1], [x0, y1, z1]];
  const f = [[0, 1, 2, 3], [5, 4, 7, 6], [4, 0, 3, 7], [1, 5, 6, 2], [4, 5, 1, 0], [3, 2, 6, 7]].map(q => q.reverse());
  return mesh(v, f, m !== undefined ? f.map(() => m) : undefined);
}
function mergeMeshes(list) {
  const v = [], f = [], fm = [];
  for (const M of list) { const o = v.length; v.push(...M.v); M.f.forEach((q, i) => { f.push(q.map(j => j + o)); fm.push(M.fm ? M.fm[i] : undefined); }); }
  return mesh(v, f, fm.some(x => x !== undefined) ? fm : undefined);
}
// Text extruded from the 8×8 font, one box per horizontal run of pixels: the 1996 "voxel logo". Centred on the origin; 1 unit per pixel.
const _textMesh = new Map();
function textMesh(str, depth = 3) {
  const key = str + '|' + depth; let M = _textMesh.get(key);
  if (M) return M;
  const chars = [...bigForm(str)], boxes = [];
  let w = 0; const xs = chars.map(c => { const x = w; w += (c === ' ' ? 4 : glyph(c).w) + 1; return x; }); w -= 1;
  chars.forEach((c, i) => {
    if (c === ' ') return;
    const g = glyph(c);
    for (let y = 0; y < 8; y++) {
      let x = 0;
      while (x < g.w) {
        if (!g.bits[y * g.w + x]) { x++; continue; }
        let e = x; while (e < g.w && g.bits[y * g.w + e]) e++;
        boxes.push(boxMesh(xs[i] + x - w / 2, y - 3.5, -depth / 2, xs[i] + e - w / 2, y + 1 - 3.5, depth / 2));
        x = e;
      }
    }
  });
  M = mergeMeshes(boxes); M.w = w;
  _textMesh.set(key, M);
  return M;
}
// A copper gradient for textMesh letters (rows −3.5…4.5): bright tops, darker feet.
const letterShade = v => clamp(1.12 - (v[1] + 3.5) / 8 * .62, 0, 1.2);
// A lathe (coins, medals, rings): profile [[r, y], …] (y increasing: top to bottom) turned n times around the y axis.
function latheMesh(profile, n = 24) {
  const v = [], f = [], P = profile.length;
  for (let i = 0; i < n; i++) { const a = i / n * TAU; for (const [r, y] of profile) v.push([Math.cos(a) * r, y, Math.sin(a) * r]); }
  for (let i = 0; i < n; i++) for (let j = 0; j + 1 < P; j++) {
    const a = i * P + j, b = ((i + 1) % n) * P + j;
    f.push([a, a + 1, b + 1, b]);
  }
  return mesh(v, f);
}
function torusMesh(R, r, n = 20, m = 10) {
  const v = [], f = [];
  for (let i = 0; i < n; i++) for (let j = 0; j < m; j++) {
    const a = i / n * TAU, b = j / m * TAU;
    v.push([(R + r * Math.cos(b)) * Math.cos(a), r * Math.sin(b), (R + r * Math.cos(b)) * Math.sin(a)]);
  }
  for (let i = 0; i < n; i++) for (let j = 0; j < m; j++) {
    const a = i * m + j, b = ((i + 1) % n) * m + j, c = ((i + 1) % n) * m + (j + 1) % m, d = i * m + (j + 1) % m;
    f.push([a, d, c, b]);
  }
  return mesh(v, f);
}

// =====================================================================================================
// LYRICS: the verse scroller (MC Token), word times, and the intro's lines
// =====================================================================================================
// The intro's a-cappella teaser isn't in song.txt (its [Intro] has no lines), so it isn't in the timing. Its words were aligned
// the same way as every other line: take2/tools/word_timing.py's CTC log-probs of this take's vocal stem (music/suno/
// eurodance-2.ctc.npz) and its align(), given these three lines; the two "it"s were then read off the stem (the vowel out of
// "-dain" at 13.58 and 15.50). w: each word's start; we: its end (held notes included).
const INTRO_LINES = [
  { sec: 'intro', n: 1, text: "We didn't start the scaling", start: 1.08, end: 5.43, w: [1.08, 1.28, 1.64, 1.94, 2.04], we: [1.28, 1.64, 1.94, 2.04, 5.43] },
  { sec: 'intro', n: 2, text: "Oh, we didn't start the scaling", start: 7.84, end: 11.82, w: [7.84, 7.96, 8.18, 8.54, 8.84, 8.96], we: [7.96, 8.18, 8.54, 8.84, 8.96, 11.82] },
  { sec: 'intro', n: 3, text: "No, we didn't preordain it, but we can't contain it!", start: 11.82, end: 18.52, w: [11.82, 12.24, 12.48, 12.88, 13.58, 13.76, 13.98, 14.2, 14.86, 15.5], we: [12.24, 12.48, 12.88, 13.58, 13.76, 13.98, 14.2, 14.86, 15.5, 18.52] },
];
// A line's words with their times: [{w, t0, t1}], from the timing's words, or evenly spread without them.
function wordsOf(ln) {
  if (ln._ws) return ln._ws;
  const ws = splitWords(ln.text);
  if (ln.w) return (ln._ws = ws.map((w, i) => ({ w, t0: ln.w[i], t1: ln.we[i] })));
  const wt = wordTimes(ln);
  return (ln._ws = ws.map((w, i) => wt ? { w, t0: wt.starts[i], t1: wt.ends[i] } : { w, t0: lerp(ln.start, ln.end, i / ws.length), t1: lerp(ln.start, ln.end, (i + 1) / ws.length) }));
}
// The sung line of a verse window (its SEGS entry → its LINES entry), and the time its i-th word starts.
const lineOf = s => LINES.find(l => l.sec === s.sec && l.n === s.n);
const wordT = (s, i) => { const ln = lineOf(s); return ln ? wordsOf(ln)[i]?.t0 ?? s.start : s.start; };
// Easing and colour helpers the parts share.
const easeInOut = k => (k = clamp(k), k < .5 ? 4 * k * k * k : 1 - (-2 * k + 2) ** 3 / 2);
const lerpHex = (a, b, k) => '#' + [1, 3, 5].map(i => Math.round(lerp(parseInt(a.slice(i, i + 2), 16), parseInt(b.slice(i, i + 2), 16), k)).toString(16).padStart(2, '0')).join('');
// Index of the word being sung at t in a line (−1 before its first word).
function wordAt(ln, t) { const ws = wordsOf(ln); let k = -1; for (let i = 0; i < ws.length; i++) if (ws[i].t0 <= t) k = i; return k; }

// Fritsch–Carlson monotone cubic through (xs, ys): smooth, and never runs backward.
function monotone(xs, ys) {
  const n = xs.length, d = [], m = new Array(n).fill(0);
  for (let i = 0; i + 1 < n; i++) d.push((ys[i + 1] - ys[i]) / (xs[i + 1] - xs[i]));
  m[0] = d[0]; m[n - 1] = d[n - 2];
  for (let i = 1; i + 1 < n; i++) m[i] = d[i - 1] * d[i] <= 0 ? 0 : (d[i - 1] + d[i]) / 2;
  for (let i = 0; i + 1 < n; i++) {
    if (d[i] === 0) { m[i] = m[i + 1] = 0; continue; }
    const a = m[i] / d[i], b = m[i + 1] / d[i], s = a * a + b * b;
    if (s > 9) { const tau = 3 / Math.sqrt(s); m[i] = tau * a * d[i]; m[i + 1] = tau * b * d[i]; }
  }
  return x => {
    if (x <= xs[0]) return ys[0] + m[0] * (x - xs[0]);
    // (past the last point it glides to a stop, a word's width on, rather than running the text off the screen)
    if (x >= xs[n - 1]) { const k = .45; return ys[n - 1] + m[n - 1] * k * (1 - Math.exp(-(x - xs[n - 1]) / k)); }
    let lo = 0, hi = n - 1; while (hi - lo > 1) { const mid = (lo + hi) >> 1; if (xs[mid] <= x) lo = mid; else hi = mid; }
    const h = xs[hi] - xs[lo], k = (x - xs[lo]) / h, k2 = k * k, k3 = k2 * k;
    return (2 * k3 - 3 * k2 + 1) * ys[lo] + (k3 - 2 * k2 + k) * h * m[lo] + (-2 * k3 + 3 * k2) * ys[hi] + (k3 - k2) * h * m[hi];
  };
}
// The verse scroller: a whole verse as one line of big type, scrolled so the word MC Token is rapping sits at the reading point.
// Its speed follows his cadence (a monotone spline through the words' onsets); sung words are lit, the one being sung glows.
const SEP = '  ✦  ';
const _scrolls = new Map();
function verseScroll(sec, s = 2) {
  const key = sec + '|' + s; let V = _scrolls.get(key);
  if (V && V.lines === LINES) return V;
  const lines = sec === 'intro' ? INTRO_LINES : LINES.filter(l => l.sec === sec);
  let str = ''; const toks = [];
  for (const ln of lines) {
    if (str) str += SEP;
    const ws = wordsOf(ln);
    ws.forEach((w, k) => {
      if (k && !/[-–]$/.test(ws[k - 1].w)) str += ' ';
      const i0 = [...str].length; str += bigForm(w.w);
      toks.push({ i0, i1: [...str].length, t0: w.t0, t1: w.t1, ln, first: k === 0 });
    });
  }
  const L = bigLayout(str, s);
  toks.forEach(k => { k.x0 = L.xs[k.i0]; k.x1 = (L.xs[k.i1] ?? L.w) - L.s; k.cx = (k.x0 + k.x1) / 2; });
  // column → token (for colouring), and the scroll spline (word centre arrives at the reading point at its onset)
  const colTok = new Int16Array(L.w).fill(-1);
  toks.forEach((k, i) => { for (let x = Math.max(0, k.x0 - s); x < Math.min(L.w, k.x1 + s); x++) colTok[x] = i; });
  const ts = [], xs = [];
  toks.forEach(k => { const tt = Math.max(k.t0, (ts.at(-1) ?? -1e9) + .02); ts.push(tt); xs.push(Math.max(k.cx, xs.at(-1) ?? -1e9)); });
  V = { lines: LINES, str: bigForm(str), L, toks, colTok, X: monotone(ts, xs), s };
  _scrolls.set(key, V);
  return V;
}
// Draw the verse scroller at t. o: y (the text's top), read (the reading point's x), s (scale), ramp (house base, default cyan),
// amp/freq/speed (the sine), wave (the voice wobble, default on), scope (MC Token's trace under the text, default true), level.
function drawScroller(sec, t, o = {}) {
  const V = verseScroll(sec, o.s ?? 2), L = V.L, read = o.read ?? SW * .42, ramp = o.ramp ?? HC;
  const X = V.X(t) - read, y = o.y ?? 300, amp = o.amp ?? 5, fr = o.freq ?? .018, sp = o.speed ?? 2.2;
  // which token is being sung
  let cur = -1; for (let i = 0; i < V.toks.length; i++) { if (V.toks[i].t0 <= t) cur = i; else break; }
  const tok = V.toks[cur], singing = tok && t < tok.t1 + .15;
  const vv = vox(t), dy = x => amp * Math.sin((x + X) * fr - t * sp) + (o.wave === false ? 0 : 3 * vv * Math.sin(x * .045 - t * 9));
  if (o.scope !== false) scopeTrace(t, 0, SW, y + L.h / 2 + (o.scopeDy ?? 12), { ramp, amp: o.scopeAmp ?? 7, level: .8 * (o.level ?? 1) });
  const bounce = singing ? Math.exp(-(t - tok.t0) * 10) * 3 : 0;
  // per character: words sung in the singer's ramp, the one being sung white-hot, the ones to come dim steel
  const tokOf = new Map(); for (let i = Math.max(0, cur - 16); i < Math.min(V.toks.length, cur + 40); i++) tokOf.set(V.toks[i].i0, i);
  let lastTok = -1;
  bigText(V.str, -X, y, {
    s: V.s, ramp, level: o.level, shadow: o.shadow ?? 8, dy: x => { const tk = V.colTok[Math.floor(x + X)]; return dy(x) - (tk === cur && singing ? bounce + 1 : 0); },
    colour: ci => {
      if (tokOf.has(ci)) lastTok = tokOf.get(ci);
      const k = V.toks[lastTok] && ci < V.toks[lastTok].i1 ? lastTok : -1;
      if (k === -1) return lastTok <= cur ? ramp : [HS, .5];
      return k === cur && singing ? [HS, 1.08] : k <= cur ? ramp : [HS, .5];
    },
  });
  return { cur, tok, X };
}
// MC Token's voice: an oscilloscope trace across the screen, its amplitude his loudness and its wiggle his pitch.
function scopeTrace(t, x0, x1, yc, o = {}) {
  const v = vox(t), note = voxNote(t) || 50, f = .06 + (note - 40) * .004, amp = (o.amp ?? 8) * v, ramp = o.ramp ?? HC, lv = o.level ?? 1;
  let py = null;
  for (let x = x0; x < x1; x++) {
    const env = Math.sin(Math.PI * (x - x0) / (x1 - x0));
    const y = yc + amp * env * (Math.sin(x * f - t * 31) * .6 + Math.sin(x * f * 2.03 + t * 17) * .3 + Math.sin(x * f * 3.1 - t * 43) * .18);
    const iy = Math.round(y);
    if (py !== null) for (let j = Math.min(py, iy); j <= Math.max(py, iy); j++) pset(x, j, hk(ramp, .95 * lv));
    else pset(x, iy, hk(ramp, lv));
    // a soft halo, only where it's brighter than what's there (text mode's 16 colours aren't a ramp to lighten along)
    const halo = hk(ramp, .38 * lv), hl = lumOf(halo);
    for (const yy of [iy - 1, iy + 1]) if (x >= CX0 && x < CX1 && yy >= CY0 && yy < CY1 && lumOf(FB[yy * SW + x]) < hl) FB[yy * SW + x] = halo;
    py = iy;
  }
}
// Softmax's voice: a bar graph that is literally a softmax over pitch, made legible. Each bar is a note (E3 … F5, named on an axis
// under the bars); her pitch (from the vocal stem) is the peak, named over it with the word she's singing; the louder she sings the
// lower the temperature (one sharp peak), and in silence it melts to uniform. Above the bars, the last second of her pitch rises as a
// piano roll; behind them, the mix's own spectrum (audio.js) jumps with the kick, the bass and the stabs.
// (x, y) = the bars' baseline's left end; w, h = their width and full height. o: level (0..1: dimmed), label (false: no labels),
// word (the word she's singing; default: found from the chorus's timing), roll (false: no piano roll), spectrum (false: none).
const SM_N0 = 52, SM_NB = 26;
const SM_NAMES = ['C', 'C#', 'D', 'D#', 'E', 'F', 'F#', 'G', 'G#', 'A', 'A#', 'B'];
const _smSpec = new Float32Array(16);
// Her pitch at t (a MIDI note, 0 when unvoiced), smoothed over the voiced frames of the last 80 ms and folded into the bars' range.
function smNote(t) {
  let s = 0, c = 0;
  for (let k = 0; k < 5; k++) { let q = voxNote(t - k * .02); if (!q) continue; while (q < SM_N0) q += 12; while (q > SM_N0 + SM_NB - 1) q -= 12; s += q; c++; }
  return c ? s / c : 0;
}
// The word being sung at t in a chorus (or the intro's teaser), for labels.
function sungWord(t) {
  const ln = [...LINES, ...INTRO_LINES].find(l => (l.sec[0] === 'C' || l.sec === 'intro' || l.sec === 'outro') && l.start - .3 <= t && t <= l.end + .2);
  if (!ln) return '';
  const k = wordAt(ln, t);
  return k >= 0 ? wordsOf(ln)[k].w.replace(/[^\w'’-]/g, '') : '';
}
function softmaxBars(t, x, y, w, h, o = {}) {
  const lv = o.level ?? 1, v = vox(t), bw = w / SM_NB;
  // the mix: 16 bands across, dim cyan, behind
  if (o.spectrum !== false) {
    spectrum(t, _smSpec);
    for (let i = 0; i < 16; i++) {
      const hh = Math.round((3 + _smSpec[i] ** 1.6 * h * .95) * lv), bx = Math.round(x + i * w / 16), bx1 = Math.round(x + (i + 1) * w / 16) - 2;
      for (let j = 0; j < hh; j++) hspan(bx + 1, bx1, y - j, hk(HC, (.12 + .28 * j / h) * lv));
    }
  }
  // her voice
  const note = smNote(t), peak = note ? note - SM_N0 : (SM_NB - 1) / 2, temp = lerp(7, 1.2, clamp(v * 1.3));
  const e = []; let sum = 0;
  for (let i = 0; i < SM_NB; i++) { const q = Math.exp(-Math.abs(i - peak) * 1.3 / temp); e.push(q); sum += q; }
  const pk = Math.round(peak);
  for (let i = 0; i < SM_NB; i++) {
    const hh = Math.max(1, Math.round(h * .85 * e[i] / sum * (2.2 + v))), bx = Math.round(x + i * bw), bx1 = Math.round(x + (i + 1) * bw) - 2;
    for (let j = 0; j < hh; j++) hspan(bx + 1, bx1, y - j, hk(HM, (.38 + .55 * j / h + (i === pk && note ? .25 : 0)) * lv));
    if (o.label !== false) {
      const n = SM_N0 + i, nm = SM_NAMES[n % 12];
      if (nm.length === 1) text8(nm === 'C' ? 'C' + (Math.floor(n / 12) - 1) : nm, bx + bw / 2, y + 3, hk(HM, (nm === 'C' ? .8 : .45) * lv), { align: 'center' });
    }
  }
  // the piano roll: a block per 30th of a second at the note she sang, rising and fading
  if (o.roll !== false) for (let k = 0; k < 30; k++) {
    const tk = t - k / 30, n = smNote(tk), a = vox(tk); if (!n || a < .08) continue;
    const bx = Math.round(x + (Math.round(n) - SM_N0) * bw), yy = Math.round(y - h - 8 - k * 1.6);
    hspan(bx + 2, bx + bw - 2, yy, hk(HM, (1 - k / 32) * (.4 + .6 * clamp(a * 1.5)) * lv));
  }
  // her note named over the peak, with the word
  if (note && v > .12 && o.label !== false) {
    const nn = Math.round(note), nm = SM_NAMES[nn % 12] + (Math.floor(nn / 12) - 1), px = x + (note - SM_N0 + .5) * bw, word = o.word ?? sungWord(t);
    const ny = Math.round(y - h - 20);
    const nw = text8(nm, px, ny, WHITE, { align: 'center', shadow: BLACK });
    if (word) text8(word.toUpperCase(), px + nw / 2 + 6, ny, hk(HM, .95 * lv), { shadow: BLACK });
  }
}

// =====================================================================================================
// THE DATE: a small plate, top right, with the month (and day) in the 8×8 font over the year in big steel digits
// =====================================================================================================
let _noDate = false, _noScroller = false, _scrollerStyle = null;
const hideDate = () => { _noDate = true; };
const hideScroller = () => { _noScroller = true; };
const scrollerStyle = s => { _scrollerStyle = s; };
function _date(t) {
  let cur = null, since = 0;
  for (const s of SEGS) { if (s.start > t) break; if (s.date && s.date !== cur) { cur = s.date; since = s.start; } }
  return cur && { text: cur, age: t - since };
}
function drawDate(t) {
  const d = _date(t); if (!d) return;
  const m = d.text.match(/^(.*?)\s*(\d{4})$/), md = m ? m[1] : d.text, yr = m ? m[2] : '';
  const k = easeOut(clamp(d.age / .12)), x1 = SW - 10, y0 = 10;
  // (a solid near-black plate: dimming within the ramp underneath isn't enough on a bright sky)
  rectf(x1 - 74, y0 - 4, 78, 38, hk(HS, .04)); rectf(x1 - 74, y0 + 34, 78, 1, hk(HS, .2));
  text8(md, x1, y0, hk(HS, .7), { align: 'right' });
  bigText(yr, x1, y0 + 11 - Math.round((1 - k) * 6), { s: 2, ramp: HS, align: 'right', shadow: 0, level: .4 + .6 * k });
  if (d.age < .1) shadeRect(x1 - 74, y0 - 4, 78, 38, -Math.round(20 * (1 - d.age / .1)));
}

// =====================================================================================================
// THE FRAME: flush FB through the palette to the canvas (×3, nearest), plus a soft CRT glow
// =====================================================================================================
let _upC = null, _upG = null;
const _glowC = makeCanvas(SW / 4, SH / 4), _glowG = _glowC.getContext('2d'), _glowI = _glowG.createImageData(SW / 4, SH / 4);
function _palette(t) {
  const fl = PFX.flash, fd = PFX.fade, pm = PFX.pump;
  for (let i = 0; i < 256; i++) {
    let r = VGA[i * 3], g = VGA[i * 3 + 1], b = VGA[i * 3 + 2];
    if (pm) { r += (255 - r) * pm * .1; g += (255 - g) * pm * .1; b += (255 - b) * pm * .1; }
    if (fl) { r += (255 - r) * fl; g += (255 - g) * fl; b += (255 - b) * fl; }
    if (fd) { r *= 1 - fd; g *= 1 - fd; b *= 1 - fd; }
    P32[i] = (0xff000000 | (Math.min(255, Math.round(b)) << 16) | (Math.min(255, Math.round(g)) << 8) | Math.min(255, Math.round(r))) >>> 0;
  }
}
function _flush() {
  for (let i = 0; i < SN; i++) _u32[i] = P32[FB[i]];
  _sg.putImageData(_img, 0, 0);
  const cw = canvas.width, ch = canvas.height, k = cw / SW;
  ctx.save(); ctx.setTransform(1, 0, 0, 1, 0, 0); ctx.globalAlpha = 1; ctx.globalCompositeOperation = 'source-over';
  if (k >= 1 && Math.abs(k - Math.round(k)) > .02 && k < 4) {
    // nearest-neighbour to the whole multiple above, then a smooth step down: even pixels at any size
    const m = Math.ceil(k);
    if (!_upC || _upC.width !== SW * m) { _upC = makeCanvas(SW * m, SH * m); _upG = _upC.getContext('2d'); }
    _upG.imageSmoothingEnabled = false; _upG.drawImage(_scr, 0, 0, SW * m, SH * m);
    ctx.imageSmoothingEnabled = true; ctx.imageSmoothingQuality = 'low'; ctx.drawImage(_upC, 0, 0, cw, ch);
  } else {
    // (smaller than the framebuffer, as a small player is: filtered down with the better of the two filters, which keeps the
    // one-pixel lines of the type from shimmering)
    ctx.imageSmoothingEnabled = k < 1; ctx.imageSmoothingQuality = 'high'; ctx.drawImage(_scr, 0, 0, cw, ch);
  }
  // glow: a quarter-size bright pass, smoothly upscaled and added
  if (PFX.glow > 0 && !LOWQ) {   // (phones skip the glow: at their size it can't be seen)
    const d = _glowI.data, gw = SW / 4, gh = SH / 4, th = 120;
    for (let gy = 0; gy < gh; gy++) for (let gx = 0; gx < gw; gx++) {
      let r = 0, g = 0, b = 0;
      for (let j = 0; j < 4; j++) { const row = (gy * 4 + j) * SW + gx * 4; for (let i = 0; i < 4; i++) { const c = _u32[row + i]; r += c & 255; g += (c >> 8) & 255; b += (c >> 16) & 255; } }
      const o = (gy * gw + gx) * 4; r /= 16; g /= 16; b /= 16;
      const l = Math.max(r, g, b), kk = l > th ? (l - th) / (255 - th) : 0;
      d[o] = r * kk; d[o + 1] = g * kk; d[o + 2] = b * kk; d[o + 3] = 255;
    }
    _glowG.putImageData(_glowI, 0, 0);
    ctx.globalCompositeOperation = 'lighter'; ctx.globalAlpha = clamp(PFX.glow); ctx.imageSmoothingEnabled = true;
    ctx.drawImage(_glowC, 0, 0, cw, ch);
  }
  ctx.restore();
}
// Post effects on the finished FB (call at the end of a shot): squash (the CRT switching off; fill: what's around the picture,
// RA + 0 in text mode), wobble (per-line sync breaking).
function squash(kx, ky, fill = BLACK) {
  FB2.set(FB); FB.fill(fill);
  const w = Math.max(1, SW * kx), h = Math.max(1, SH * ky), x0 = (SW - w) / 2, y0 = (SH - h) / 2;
  for (let y = Math.floor(y0); y < Math.ceil(y0 + h); y++) {
    const sy = clamp(Math.floor((y - y0) / h * SH), 0, SH - 1);
    for (let x = Math.floor(x0); x < Math.ceil(x0 + w); x++) FB[y * SW + x] = FB2[sy * SW + clamp(Math.floor((x - x0) / w * SW), 0, SW - 1)];
  }
}
function wobble(fn) {
  FB2.set(FB);
  for (let y = 0; y < SH; y++) { const d = Math.round(fn(y)); if (!d) continue; for (let x = 0; x < SW; x++) FB[y * SW + x] = FB2[y * SW + clamp(x - d, 0, SW - 1)]; }
}

// A frame with no part painted yet: the generic part (see ch/zz_generic.js) draws it.
let GENERIC = null;
OVERLAYS.push((t, s) => {
  try {
    if (!(s && SHOTS[s.key]) && GENERIC) GENERIC(t, s);
    noClip();
    // the verse scroller runs under every verse line unless the part hides or restyles it
    if (s && s.kind === 'line' && !_noScroller) drawScroller(s.sec, t, _scrollerStyle || {});
    if (!_noDate) drawDate(t);
  } catch (e) { console.error(`demoscene overlay @ ${t.toFixed(2)}: ${e.stack || e}`); }
  PFX.pump = Math.max(PFX.pump, 0);
  _palette(t);
  _flush();
  // reset the per-frame switches
  noClip(); _houseRamps(); _defaultRamps(); FB.fill(0); ZB.fill(0);
  PFX.flash = 0; PFX.fade = 0; PFX.pump = 0; PFX.glow = .55;
  _noDate = false; _noScroller = false; _scrollerStyle = null;
  CAM.f = 300; CAM.cx = SW / 2; CAM.cy = SH / 2;
});

;
// ---- styles/demoscene/fx.js ----
// fx.js: the demo's effects, the 1990s classics as software loops over FB: plasma, tunnel, rotozoomer, fire, copper bars, starfield,
// vector bobs, dot tunnels, infinite bobs, twister, metaballs, and the procedural textures they map. Each one is a pure function of t.
// Heavy per-pixel effects take o.chunk (1: every pixel; 2: 2×2 blocks, the classic "chunky" mode); on phones (LOWQ) they go chunky.

const SINT = new Float32Array(4096);
for (let i = 0; i < 4096; i++) SINT[i] = Math.sin(i / 4096 * TAU);
const fsin = a => SINT[Math.round(a * 651.8986) & 4095];   // (651.9 = 4096 / 2π)

// Write a chunk×chunk block, clipped to the clip rectangle.
function _blk(x, y, ch, c) {
  if (ch === 1) { if (x >= CX0 && x < CX1 && y >= CY0 && y < CY1) FB[y * SW + x] = c; return; }
  const xa = Math.max(x, CX0), xb = Math.min(x + ch, CX1);
  if (xb <= xa) return;
  for (let j = Math.max(y, CY0), e = Math.min(y + ch, CY1); j < e; j++) FB.fill(c, j * SW + xa, j * SW + xb);
}

// ---------- plasma ----------
// The four-sine plasma. Writes ramp `at` + level. Each ramp is dark → bright, so shading (DIMT) still works on it: the plasma's
// value folds up and down through the ramp, and with o.alt it alternates between two ramps at every dark crossing (magenta blobs
// ringed by cyan ones, say) without a seam. o: chunk, scale (spatial frequency), speed, cycle (offset, 0..1: palette cycling),
// alt (the second ramp), x0/y0/x1/y1 (a sub-rectangle), mask(x, y), gamma (>1 darker).
function plasma(t, at = RA, o = {}) {
  const ch = o.chunk ?? (LOWQ ? 4 : 2), sc = (o.scale ?? 1) * ch, sp = o.speed ?? 1, cyc = o.cycle ?? 0, alt = o.alt ?? at, gm = o.gamma ?? 1;
  const x0 = o.x0 ?? CX0 - CX0 % ch, y0 = o.y0 ?? CY0 - CY0 % ch, x1 = o.x1 ?? CX1, y1 = o.y1 ?? CY1;
  const a = t * sp, cxm = SW / 2 + fsin(a * .31) * 160, cym = SH / 2 + fsin(a * .23 + 1) * 90;
  const LUT = new Uint8Array(64); for (let i = 0; i < 64; i++) LUT[i] = Math.round(Math.pow(i / 63, gm) * 63);
  for (let y = y0; y < y1; y += ch) {
    const ya = fsin(y * .021 * sc / ch + a * 1.3);
    for (let x = x0; x < x1; x += ch) {
      if (o.mask && !o.mask(x, y)) continue;
      const dx = (x - cxm) / ch, dy = (y - cym) / ch;
      let v = fsin(x * .017 * sc / ch + a) + ya + fsin((x + y) * .011 * sc / ch - a * .7) + fsin(Math.sqrt(dx * dx + dy * dy) * .06 * sc - a * 1.7);
      v = (v / 8 + .5) * (o.bands ?? 2) + cyc;
      const fl = Math.floor(v), f = v - fl, k = f < .5 ? f * 2 : 2 - f * 2;
      _blk(x, y, Math.min(ch, SW - x, SH - y), ((fl & 1) ? alt : at) + LUT[k * 63 | 0]);
    }
  }
}

// ---------- tunnel ----------
// The classic lookup-table tunnel: per-pixel angle and inverse distance, computed once per resolution, then a texture scrolled
// through them. tex: a Texture (256×256 levels 0..63). o: chunk, speed (depth scroll), spin, cx/cy (the vanishing point's offset
// from centre, px), fog (how dark the far end is), at, bright.
const _tunT = new Map();
function _tunnelTables(ch) {
  let T = _tunT.get(ch); if (T) return T;
  const w = Math.ceil(SW / ch) * 2, h = Math.ceil(SH / ch) * 2, ang = new Uint8Array(w * h), dist = new Uint16Array(w * h), dep = new Uint8Array(w * h);
  for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) {
    const dx = (x - w / 2) * ch, dy = (y - h / 2) * ch, r = Math.sqrt(dx * dx + dy * dy) + .5;
    ang[y * w + x] = Math.floor((Math.atan2(dy, dx) / TAU + .5) * 256) & 255;
    dist[y * w + x] = Math.floor(9000 / r) & 65535;
    dep[y * w + x] = clamp(Math.round(r / 3.2), 0, 63);
  }
  T = { w, h, ang, dist, dep }; _tunT.set(ch, T);
  return T;
}
function tunnel(t, tex, o = {}) {
  const ch = o.chunk ?? (LOWQ ? 4 : 2), T = _tunnelTables(ch), at = o.at ?? RA;
  const du = Math.floor((o.depth ?? t * (o.speed ?? 1) * 160)) & 255, dv = Math.floor((o.turn ?? t * (o.spin ?? .15) * 256)) & 255;
  const ox = Math.round(T.w / 4 - (o.cx ?? 0) / ch), oy = Math.round(T.h / 4 - (o.cy ?? 0) / ch), fog = o.fog ?? 1, br = o.bright ?? 1;
  const tx = tex.px, cw = Math.ceil(SW / ch), chh = Math.ceil(SH / ch);
  const fogT = new Uint8Array(64 * 64);   // (level × depth) → level
  for (let l = 0; l < 64; l++) for (let d = 0; d < 64; d++) fogT[l * 64 + d] = clamp(Math.round(l * br * lerp(1 - fog, 1, clamp(d / 40))), 0, 63);
  for (let y = 0; y < chh; y++) {
    const row = (y + oy) * T.w + ox;
    for (let x = 0; x < cw; x++) {
      const k = row + x, u = (T.dist[k] + du) & 255, v = (T.ang[k] + dv) & 255;
      _blk(x * ch, y * ch, Math.min(ch, SW - x * ch, SH - y * ch), at + fogT[tx[v * 256 + u] * 64 + T.dep[k]]);
    }
  }
}

// ---------- rotozoomer ----------
// A texture rotated and zoomed across the screen (or a rectangle of it). o: angle, zoom (texels per pixel is 1/zoom), u/v (texture
// point at the screen centre), cx/cy (screen centre), chunk, at, x0/y0/x1/y1, transparent (skip texels of level 0), wrap (default true;
// false: one copy of the texture, nothing drawn outside it: a single sheet of paper spinning).
function rotozoom(tex, o = {}) {
  const ch = o.chunk ?? (LOWQ ? 2 : 1), at = o.at ?? RA, a = o.angle ?? 0, z = o.zoom ?? 1;
  const cs = Math.cos(a) / z, sn = Math.sin(a) / z, cx = o.cx ?? SW / 2, cy = o.cy ?? SH / 2, U = o.u ?? 128, Vv = o.v ?? 128;
  const x0 = o.x0 ?? CX0, y0 = o.y0 ?? CY0, x1 = o.x1 ?? CX1, y1 = o.y1 ?? CY1, tx = tex.px, tw = tex.w - 1, th = tex.h - 1, tws = Math.log2(tex.w), transp = o.transparent;
  for (let y = y0; y < y1; y += ch) {
    let u = U + (x0 - cx) * cs - (y - cy) * sn, v = Vv + (x0 - cx) * sn + (y - cy) * cs;
    for (let x = x0; x < x1; x += ch) {
      if (o.wrap === false && (u < 0 || v < 0 || u >= tex.w || v >= tex.h)) { u += cs * ch; v += sn * ch; continue; }
      const l = tx[((v & th) << tws) | (u & tw)];
      if (!(transp && !l)) _blk(x, y, Math.min(ch, x1 - x, y1 - y), at + l);
      u += cs * ch; v += sn * ch;
    }
  }
}

// ---------- textures (256×256 or any power of two; levels 0..63) ----------
function tex(w = 256, h = 256) { return { w, h, px: new Uint8Array(w * h) }; }
const _texCache = new Map();
function texCached(key, make) { let T = _texCache.get(key); if (!T) { T = make(); _texCache.set(key, T); } return T; }
// Stamp 8×8-font text into a texture at (x, y), scale s, level l (for tunnels and rotozoomers full of words).
function texText(T, str, x, y, s = 1, l = 63) {
  let cx = x;
  for (const ch of String(str)) {
    const g = glyph(ch);
    for (let gy = 0; gy < 8; gy++) for (let gx = 0; gx < g.w; gx++) if (g.bits[gy * g.w + gx])
      for (let a = 0; a < s; a++) for (let b = 0; b < s; b++) { const px = (cx + gx * s + b) & (T.w - 1), py = (y + gy * s + a) & (T.h - 1); T.px[py * T.w + px] = l; }
    cx += (g.w + 1) * s;
  }
  return cx - x;
}
const texChecker = (n = 32, lo = 12, hi = 48) => texCached('chk' + n + lo + hi, () => {
  const T = tex(); for (let y = 0; y < 256; y++) for (let x = 0; x < 256; x++) T.px[y * 256 + x] = ((x / n | 0) + (y / n | 0)) & 1 ? hi : lo; return T;
});

// ---------- fire ----------
// The classic fire: each cell averages the ones below it and cools. Deterministic: it re-simulates `steps` ticks up to t (from cold),
// at 160×90 cells, then draws bilinearly to the screen through the fire ramp at `at`. o.fuel(x, y) → heat 0..1 injected per cell (text on
// fire), o.base (0..1: the bottom rows' heat), o.cool, o.wind, o.steps, o.y0 (screen top), o.over (only draw where hot: over a scene).
const FW = 160, FH = 92, _fireA = new Float32Array(FW * FH), _fireB = new Float32Array(FW * FH);
function fire(t, at = RA, o = {}) {
  // (phones: three quarters of the ticks, cooling faster to keep the flames' height, and drawn in 2×2 blocks)
  const q = LOWQ ? .75 : 1, steps = Math.round((o.steps ?? 48) * q), tick = Math.floor(t * 60), cool = (o.cool ?? .055) / q, base = o.base ?? 1, wind = o.wind ?? 0;
  let A = _fireA, B = _fireB; A.fill(0);
  const fuel = o.fuelMask;
  for (let s = tick - steps; s <= tick; s++) {
    // seed the bottom rows and the fuel
    for (let x = 0; x < FW; x++) {
      const h = hash2(s * 7 + 3, x);
      A[(FH - 1) * FW + x] = base * (h > .45 ? 1 : h * .6);
      A[(FH - 2) * FW + x] = Math.max(A[(FH - 2) * FW + x], base * hash2(s * 11 + 5, x) * .9);
    }
    if (fuel) for (let i = 0; i < fuel.length; i++) if (fuel[i]) A[i] = Math.max(A[i], fuel[i] / 255 * (.7 + .3 * hash2(s, i)));
    for (let y = 0; y < FH - 2; y++) {
      const dx = wind ? Math.round(wind * fsin(y * .2 + s * .05)) : 0;
      for (let x = 0; x < FW; x++) {
        const xl = Math.max(0, x - 1 + dx), xr = Math.min(FW - 1, x + 1 + dx), xc = Math.min(FW - 1, Math.max(0, x + dx));
        const v = (A[(y + 1) * FW + xl] + A[(y + 1) * FW + xc] + A[(y + 1) * FW + xr] + A[(y + 2) * FW + xc]) * .25 - cool * (.6 + .8 * hash2(s + y, x));
        B[y * FW + x] = v > 0 ? v : 0;
      }
    }
    for (let x = 0; x < FW * 2; x++) B[(FH - 2) * FW + x] = A[(FH - 2) * FW + x];
    const tmp = A; A = B; B = tmp;
  }
  // draw, bilinear
  const y0 = Math.round(o.y0 ?? 0), sy = (SH - y0) / (FH - 2), sx = SW / FW, over = o.over, gain = o.gain ?? 1.15;
  const ch = LOWQ ? 2 : 1;
  for (let y = Math.max(y0, CY0); y < CY1; y += ch) {
    const fy = (y - y0) / sy, iy = Math.min(FH - 3, Math.floor(fy)), ky = fy - iy;
    for (let x = CX0; x < CX1; x += ch) {
      const fx = x / sx - .5, ix = clamp(Math.floor(fx), 0, FW - 2), kx = clamp(fx - ix, 0, 1);
      const a = A[iy * FW + ix], b = A[iy * FW + ix + 1], c = A[(iy + 1) * FW + ix], d = A[(iy + 1) * FW + ix + 1];
      const v = clamp(((a * (1 - kx) + b * kx) * (1 - ky) + (c * (1 - kx) + d * kx) * ky) * gain);
      if (over && v < .08) continue;
      if (ch === 1) FB[y * SW + x] = at + Math.round(v * 63); else _blk(x, y, ch, at + Math.round(v * 63));
    }
  }
}
// A fuel mask (160×92, 0..255) from big text, for fire(): text centred at (cx, cy) in screen pixels.
const _fuel = new Map();
function fuelText(str, s, cx, cy) {
  const key = str + s + cx + cy; let F = _fuel.get(key);
  if (F) return F;
  F = new Uint8Array(FW * FH);
  const L = bigLayout(bigForm(str), s), x0 = cx - L.w / 2, y0 = cy - L.h / 2, sx = SW / FW, sy = SH / (FH - 2);
  for (let y = 0; y < L.h; y++) for (let x = 0; x < L.w; x++) if (L.m[y * L.w + x] > 1) {
    const fx = Math.floor((x0 + x) / sx), fy = Math.floor((y0 + y) / sy);
    if (fx >= 0 && fx < FW && fy >= 0 && fy < FH) F[fy * FW + fx] = 255;
  }
  _fuel.set(key, F);
  return F;
}

// ---------- copper bars ----------
// A horizontal bar of light: a ramp's shades from dark edges to a bright core, `h` pixels tall centred on y. o.at (64-ramp) or
// o.house (16-ramp); o.x0/x1; o.level.
function copperBar(y, h, o = {}) {
  const at = o.at ?? RB, house = o.house, lv = o.level ?? 1;
  for (let j = 0; j < h; j++) {
    const k = 1 - Math.abs((j + .5) / h * 2 - 1), l = Math.pow(k, .7) * lv;
    hspan(o.x0 ?? 0, o.x1 ?? SW, Math.round(y - h / 2 + j), house !== undefined ? hk(house, l) : rk(at, l));
  }
}
// Vertical bars (bars of a cage, a scanline sweep): the same, standing up.
function copperBarV(x, w, o = {}) {
  const at = o.at ?? RB, lv = o.level ?? 1, y0 = o.y0 ?? 0, y1 = o.y1 ?? SH;
  for (let j = 0; j < w; j++) {
    const k = 1 - Math.abs((j + .5) / w * 2 - 1), c = o.house !== undefined ? hk(o.house, Math.pow(k, .7) * lv) : rk(at, Math.pow(k, .7) * lv);
    const px = Math.round(x - w / 2 + j); if (px < CX0 || px >= CX1) continue;
    for (let y = Math.max(CY0, y0); y < Math.min(CY1, y1); y++) FB[y * SW + px] = c;
  }
}
// A copper sky: a vertical gradient through a ramp, one colour per scanline (what the Amiga's copper did).
function copperSky(at, k0, k1, o = {}) {
  const y0 = o.y0 ?? 0, y1 = o.y1 ?? SH;
  for (let y = y0; y < y1; y++) hspan(0, SW, y, rk(at, lerp(k0, k1, (y - y0) / (y1 - y0))));
}

// ---------- starfield ----------
// 3D stars flying at the viewer. o: n, speed (depth units a second), at (64-ramp), streak (px), cx/cy, spread, seed, z0 (offset).
function starfield(t, o = {}) {
  const n = o.n ?? 300, sp = o.speed ?? .35, at = o.at ?? RB, cx = o.cx ?? SW / 2, cy = o.cy ?? SH / 2, seed = o.seed ?? 1, f = o.f ?? 220;
  for (let i = 0; i < n; i++) {
    const x = (hash2(seed, i) - .5) * 2 * (o.spread ?? 1.8), y = (hash2(seed + 1, i) - .5) * 2 * (o.spread ?? 1.8) * .6;
    const z = 1 - frac(hash2(seed + 2, i) + t * sp + (o.z0 ?? 0)) * .98;
    const sx = cx + x / z * f * .5, sy = cy + y / z * f * .5; if (sx < 0 || sx >= SW || sy < 0 || sy >= SH) continue;
    const l = clamp((1 - z) * 1.25), c = rk(at, .25 + .75 * l);
    pset(sx, sy, c);
    const st = (o.streak ?? 0) * l * l;
    if (st > .5) { const z2 = z + .02 * (o.streak ?? 0) / 10, px = cx + x / z2 * f * .5, py = cy + y / z2 * f * .5; lineP(px, py, sx, sy, rk(at, .2 + .5 * l)); }
    if (l > .7) { pset(sx + 1, sy, c); pset(sx, sy + 1, rk(at, .5 * l)); }
  }
}

// ---------- vector bobs ----------
// Balls at 3D points, sorted back to front, sized by perspective. pts: [[x, y, z, (r), (at)], …] in object space; R (rot3), pos.
// o: r (radius at z = 1 unit… in px per unit of f), at, fog ([near, far]), house (true: `at` is a 16-shade house ramp).
function bobs3D(pts, R, pos, o = {}) {
  const P = pts.map(p => {
    const X = R[0] * p[0] + R[1] * p[1] + R[2] * p[2] + pos[0], Y = R[3] * p[0] + R[4] * p[1] + R[5] * p[2] + pos[1], Z = R[6] * p[0] + R[7] * p[1] + R[8] * p[2] + pos[2];
    return [X, Y, Z, p[3] ?? 1, p[4]];
  }).filter(p => p[2] > .2).sort((a, b) => b[2] - a[2]);
  const fog = o.fog;
  for (const [X, Y, Z, rr, at] of P) {
    const [sx, sy] = proj(X, Y, Z), r = (o.r ?? 1) * rr * CAM.f / Z, k = fog ? clamp(1 - (Z - fog[0]) / (fog[1] - fog[0]), .25, 1) : 1;
    if (r < .6) { pset(sx, sy, (at ?? o.at ?? RB) + (o.house ? Math.round(12 * k) : Math.round(50 * k))); continue; }
    bob(sx, sy, r, at ?? o.at ?? RB, k, { house: o.house });
  }
  return P;
}

// ---------- dot tunnel ----------
// Rings of dots receding into the screen, each ring offset along a wandering path. o: rings, dots, speed, at, r (ring radius), bend.
function dotTunnel(t, o = {}) {
  const rings = o.rings ?? 26, dots = o.dots ?? 24, sp = o.speed ?? 1.2, at = o.at ?? RB, R = o.r ?? 1, bend = o.bend ?? 1;
  const path = z => [fsin(z * .55 + t * .6) * .6 * bend, fsin(z * .41 + t * .47 + 1) * .4 * bend];
  const off = frac(t * sp), [px0, py0] = path(t * sp);
  for (let i = rings - 1; i >= 0; i--) {
    const z = (i + 1 - off) * .45, [px, py] = path(t * sp + i + 1 - off);
    const k = clamp(1 - z / (rings * .45)), spin = t * (o.spin ?? .4) + i * .08;
    for (let d = 0; d < dots; d++) {
      const a = d / dots * TAU + spin, x = px - px0 + Math.cos(a) * R, y = py - py0 + Math.sin(a) * R * .9;
      const [sx, sy] = proj(x, y, z + .3);
      const r = clamp(2.8 / (z + .3), .6, 7);
      if (r < 1.2) pset(sx, sy, rk(at, .3 + .6 * k)); else bob(sx, sy, r, at, .3 + .7 * k);
    }
  }
}

// ---------- infinite bobs ----------
// The Amiga "unlimited bobs" trick: one bob drawn every frame into a screen that's never cleared, so its path fills with copies.
// Here: every position the bob has had over the last `dur` seconds (every `dt`), oldest first. path(t) → [x, y]; o: r, at, dt, dur.
function infiniteBobs(t, path, o = {}) {
  const dt = o.dt ?? 1 / 60, dur = o.dur ?? 3, r = o.r ?? 10, at = o.at ?? RB, t0 = Math.max(o.from ?? -1e9, t - dur);
  const n = Math.floor((t - t0) / dt);
  for (let i = n; i >= 0; i--) { const [x, y] = path(t - i * dt); bob(x, y, r, at, o.k ?? 1, o); }
}

// ---------- twister ----------
// The twisting square column: per scanline, four faces of a bar rotated by a twist that varies with y. o: x (centre), w (half-width),
// at (64-ramp) for faces, twist(y) → angle, texture fn(face, u, y) → 0..1 extra shade.
function twister(t, o = {}) {
  const cx = o.x ?? SW / 2, w = o.w ?? 50, at = o.at ?? RB, y0 = o.y0 ?? 0, y1 = o.y1 ?? SH;
  for (let y = y0; y < y1; y++) {
    const a = o.twist ? o.twist(y) : t * 1.3 + fsin(y * .012 + t * .9) * 1.6;
    for (let f = 0; f < 4; f++) {
      const a0 = a + f * TAU / 4, a1 = a0 + TAU / 4, xa = cx + Math.sin(a0) * w, xb = cx + Math.sin(a1) * w;
      if (xb <= xa) continue;
      const light = clamp(Math.cos((a0 + a1) / 2 - .5) * .5 + .5);
      for (let x = Math.ceil(xa); x < xb; x++) {
        const u = (x - xa) / (xb - xa), sh = o.texture ? o.texture(f, u, y) : 0;
        pset(x, y, rk(at, clamp(.15 + .75 * light * (1 - .35 * Math.abs(u - .5) * 2) + sh)));
      }
    }
  }
}

// ---------- metaballs ----------
// Blobs whose fields add up; the iso-surface fills with ramp `at` (level by field strength). balls: [[x, y, r], …] in screen px.
function metaballs(balls, o = {}) {
  const ch = o.chunk ?? (LOWQ ? 4 : 2), at = o.at ?? RB, th = o.th ?? 1, x0 = o.x0 ?? CX0 - CX0 % ch, y0 = o.y0 ?? CY0 - CY0 % ch, x1 = o.x1 ?? CX1, y1 = o.y1 ?? CY1;
  for (let y = y0; y < y1; y += ch) for (let x = x0; x < x1; x += ch) {
    let f = 0;
    for (const [bx, by, r] of balls) { const dx = x - bx, dy = y - by; f += r * r / (dx * dx + dy * dy + 1); }
    if (f < th) continue;
    _blk(x, y, Math.min(ch, SW - x, SH - y), rk(at, clamp(.35 + (f - th) * .45)));
  }
}

// ---------- sunburst ----------
// Rotating rays from a point, alternating two shades of a ramp, fading out from the centre (glory, a fan, a Stargate's kawoosh).
// o: n (rays), cx/cy, spin (turns a second), lo/hi (levels 0..1), chunk, fall (radius where it has faded, px).
function sunburst(t, at, o = {}) {
  const ch = o.chunk ?? (LOWQ ? 4 : 2), n = o.n ?? 16, cx = o.cx ?? SW / 2, cy = o.cy ?? SH / 2, rot = t * (o.spin ?? .1) * TAU, lo = o.lo ?? .08, hi = o.hi ?? .35, fall = o.fall ?? 420;
  for (let y = CY0 - CY0 % ch; y < CY1; y += ch) for (let x = CX0 - CX0 % ch; x < CX1; x += ch) {
    const dx = x - cx, dy = y - cy, a = Math.atan2(dy, dx) + rot, r = Math.sqrt(dx * dx + dy * dy);
    const band = (Math.floor((a / TAU + 1) * n) & 1), k = clamp(1 - r / fall);
    _blk(x, y, ch, rk(at, (band ? hi : lo) * (.35 + .65 * k)));
  }
}

;
// ---- styles/demoscene/gfx.js ----
// gfx.js: the demo's one digitized picture, as 1996 graphicians made them: an affectionate caricature of President Trump (for V4.13),
// generated with Nano Banana Pro (gfx/trump-caricature.png), then digitized by gfx/digitize.py: 150×200 pixels, its own 96-colour palette
// in the VGA DAC's 64 levels, and a 4×4 Bayer dither. pal: the colours, dark to bright; px: one palette index per pixel, row by row.
const PORTRAIT = { w: 150, h: 200, pal: ['#000004','#000408','#04040c','#040810','#200000','#100808','#080c14','#080c18','#080c18','#080c18','#080c18','#080c18','#080c18','#080c18','#080c18','#080c18','#080c18','#080c18','#080c18','#080c18','#080c18','#080c18','#080c18','#080c18','#080c18','#080c18','#080c18','#080c1c','#0c0c14','#0c0c18','#0c0c18','#0c101c','#101020','#101424','#3c0404','#181414','#241410','#14182c','#181c34','#18203c','#650408','#1c2040','#242424','#202444','#202848','#20284c','#3c2418','#242c50','#242c50','#890c0c','#283055','#283055','#283055','#283055','#283055','#283055','#283055','#283055','#2c3459','#343838','#503020','#30385d','#9d1010','#b61418','#404869','#6d4028','#504c44','#555d6d','#7d593c','#9d552c','#656981','#a16d34','#b26538','#957155','#be7140','#81858d','#b27d3c','#ca7d48','#b68965','#c28d44','#d68955','#9da1aa','#de915d','#d29d50','#cea571','#e29d69','#e6a579','#e2ae5d','#b6beca','#e6b28d','#eabe79','#ced2da','#f2d295','#e6e6ea','#f6f6f6','#ffffff'], px: Uint8Array.from(atob('AQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwIHAx8BBwMfAQcDHwEHAx8CBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHHwMhBiADIQYgAyEGHwMhBiADIQYgAyEGIAMhByADIQYgAyEGIAMhBiADIQYgAyEGIAMhBiADIQYgAyEGIAMhBiADIQYgAyEGIAMhBiADIQYgAyEGIAMhBiADIQYgAyEGIAMhBiADIQYfAyEGIAMhBh8DIQYgAyEGIAMhBiADIQYgAyEGIAMhBiADIQYgAyEGHwMhBh8DAx8CHwMfAh8DHwIdAx8CHQMfAh8DHwIfAx8CHwMfAh8DHwIdAx8CHwMfAh8DHwIfAx8CHwMfAh8DHwIfAx8CHwMfAh8DHwIfAx8CHQMfAh8DHwIfAx8CHwMfAh8DHwIfAx8CHwMfAh8DHwIfAx8CHwMfAh8DHwIfAx8CHwMfAh8DHwIdAx8CHwMfAh8DHwIfAx8CHwMfIQcgBiEHIAYhByADIQcgBiEHIAYhByAGIQcgBiEHIAYhByAGIQcgBiEHIAYhByAGIQcgBiEHIAYhByAGIQcgBiEHIAYhByAGIQcgBiEHIAYhByAGIQcgBiEHIAYhByAGIQcgBiEHIAYhByAGIQcgBiEHIAYhByAGIQcgBiEHIAYhByAGIQcgBiEHIAYhByAGIQcgBiEHAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHIAMhBiADIQYgAyEGHwMhBiADIQYgAyEGIAMhBiADIQYgAyEGIAMhBiADIQYgAyEGIAMhBiADIQYgAyEGHwMhBiADIQYgAyEGIAMhBiADIQYgAyEGIAMhBh8DIQYgAyEGHwMhBiADIQYgAyEGIAMhBiADIQYgAyEGIAMhBiADIQYfAyEGIAMhBiADIQYfAyEGIAMhBiADAx8CHwMfAh0DHwIdAx8CHwMfAh8DHwIfAx8CHwMfAh8DHwIfAx8CHwMfAh8DHwIfAx8CHwMfAh8DHwIfAx8CHQMfAh8DIAMfAx8CHwMfAh0DHwIfAx8CHwMfAh8DHwIdAx8CHwMfAh8DHwIfAx8CHwMfAh0DHwIfAx8CHwMfAh8DHwIfAx8CHwMfAh8DHwIfAx8CHQMfIQcgBiEHIAMhByADIQcgBiEHIAYhByAGIQcgBiEHIAYhByADIQcgBiEHIAMhByAGIQcgAyEHIAYhByADIQchByUHIAMfAx8CHwMfAyEfIQchByAGIQcgBiEHIAYhByADIQcgBiEHIAYhByAGIQcgBiEHIAYhByAGIQcgBiEHIAMhByAGIQcgBiEHIAYhByAGIQcgBiEHAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMgAQMAAQAAACMFIwUjBSMFBQAAAAIABgMgAgcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHIAMhBiADIQYfAyEGHwMhBiADIQYgAyEGIAMhBiADIQYgAyEGHwMhBh8DIQYgAyEGHwMhBh8DIR0hAQMAHCNCRE5OWVROTlRaXFpaVFRJSUI7BQMAAwMhHSADIQYgAyEGHwMhBiADIQYgAyEGIAMhBiADIQYgAyEGIAMhBiADIQYgAyEGIAMhBiADIQYgAyEGIAMhBiADAx8CHwMfAh0DHwIdAx8CHwMfAh8DHwIfAx8CHwMfAh8DHwIfAx8CHwMfAh8DHwIdAx8CHwMhAQEAIzxJVFxcXFpaT1NXWldaV1pXWldaWlpaVElELhwAAwMgAx8DHwIdAx8CHwMfAh8DHwIfAx8CHwMfAh8DHwIfAx8CHwMfAh8DHwIfAx8CHwMfAh8DHwIfAx8CHwMfIQcgBiEHIAMhByADIQcgBiEHIAYhByAGIQcgBiEHIAYhByADIQcgBiEHIAYhByADIQchBx8AI0JOXFxcXFpXU09HV1dXV1dTV1NXU1dTU09XU1daWk5JLhwABwYhByAGIQcgBiEHIAYhByAGIQcgBiEHIAYhByAGIQchBiEHIAYhByAGIQcgBiEHIAYhByADIQcgAyEHAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAh8BAAVJWVxcWldXU1NPTExXV1dTV1NXT1NTU09TT1NPT0dHR0xMTEQ8JAEABwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHIAMhBh8DIQYgAyEGIAMhBiADIQYgAyEGIAMhBiADIQYgAyEGHwMhBiADIQYfAyEHHwAjSVxcXFpXU1dXV09PT1dXV1dXV1dTV1NXU1dTV1NMR0xMT09TT1NPT0Q8AAYDIQMhBiADIQYgAyEGIAMhBiADIQYgAyEGIAMhBiADIQYgAyEGIAMhBiADIQYgAyEGIAMhBiADAx8CHwMfAh8DHwIfAx8CHwMfAh8DHwIfAx8CHwMfAh0DHwIdAx8CHQMfAh8DHwMCAERZXFpaU1dTV1NXT09MV1NXU1dTV1NXU1dTV1NXT0xMU09TT1NPU09PT1NPRzwFAB8DBwMfAh0DHwIfAx8CHwMfAh8DHwIfAx8CHwMfAh8DHwIfAx8CHwMfAh8DHwIdAx8CHwMfIQcgBiEHIAYhByAGIQcgBiEHIAYhByAGIQcgBiEHIAMhByADIQcgAyEHIAMhBgIqWVxcWldXV1dXV1dTU0xXV1dXV1dXV1dXV1dXV1dPT1NXU1dTV1dXV1pXV09TT1NHPAAfByEHIAYhByAGIQcgBiEHIAYhByAGIQcgBiEHIAYhByAGIQcgBiEHIAYhByAGIQcgBiEHAQcDHwEHAh8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8CBwMfAQcDHwEHAiAAAERcXFpXV1NXV1dTV1NTTFNTV1NXU1dTV1NXU1dTV0xTU1NTV1NXU1dTV1daWlpTU0xPTEQAAwIHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHHwMhBiADIQYfAyEGIAMhBiADIQYgAyEGIAMhBiADIQcfAyEGHwMhBh8DJQEjTlxaWldXV1dXV1dXV1dPU1dXV1dXV1dXV1dXV1dXU1NTV1dXV1dXV1daV1dXV1paV1NMT0xHBQcGIQYgAyEGIAMhBiADIQYgAyEGIAMhBiADIQYgAyEGHwMhBiADIQYgAyEGIAMhBiADAx8CHwMfAh8DHwIfAx8CHwMfAh0DHwIfAx8CHwMfAwYAHwIdAx8CHQMgACpUXFdXU1dTV1daV1dXV09TU1dTV1NXU1dTV1NXU1dTV1NXV1pXVFNUU1RTVFpaV1dXWlNPR0xHRAAdAx8DHwIfAx8CHwMfAh8DHwIfAx8CHwMfAh8DHwIfAx8CHwMfAh8DHwIfAx8CHwMfIQcgBiEHIAMhByAGIQcgBiEHIAMhByAGIQcgBiEHHwIfByADIQcgBiEAQlxcV1dXV1dXV1pXV1daV1dTV1dXV1dXV1dXV1dXV1dXV1paWlpcWlxaXFpaVFRaXFpaWlpTT0xMTEQAIQMhByAGIQcgBiEHIAYhByAGIQcgBiEHIAYhByAGIQcgBiEHIAYhByAGIQcgAyEHAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEDBUIAHwMfAQcGBwBCXFpTV1dXV1pXWlpXV1dXV1NXU1dTV1dXU1dTV1dXV1dXWlpcWlxaXFpcWlpaWlRPVFpUV1dTTEdMR0ckAB8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHHwMhBh8DIQYgAyEGIAMhBiADIQYfAyEGIAMhBiEAREkCByEGIQcGHElaWlNaV1pXWlpaWlpXWldaV1dXV1dXV1pXV1dXV1pXWlpcXFxcXFxcXFxaXFpaV1pUU1paVFdTT0dPR09EAwcgAyEGIAMhBiADIQYgAyEGIAMhBiADIQYgAyEGIAMhBiADIQYgAyEGHwMhBh8DAx8CHQMfAh0DHwIfAx8CHwMfAh8DHwIfAx8CHQMcTlQFAgEDAAEuWVRaU1dXWldXWlpXWlpaV1paV1NXV1pXV1paV1dXWlpaWlxcXFxcXFxaXFpaV1dTV1NXT1NTVE9PTEdHTExMABsDHwIfAx8CHwMfAh8DHwIfAx8CHwMfAh8DHwIfAx8CHwMfAh8DHwIdAx8CHQMfIQcgAyEHIAYhByAGIQcgBiEHIAYhByADIQcgBh0qXFdUKiMFQk5cWlNXWldaV1pUXFpaWlxaWlpcV1pXWlpaV1xaWlpcXFxcXFxcXFxcXFpaU1NPT0xPT1NTU0xTU09PT0dMR0xMIwMhByAGIQcgBiEHIAYhByAGIQcgBiEHIAYhByAGIQcgBiEHIAMhByADIQcgAyEHAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDIABCXFNXWlRaWlpXU1NaV1pXWlpUWlxaXFpcWlpaWldaWlxXWlpcWlxaXFxcXFxcXFpaV1NPT09TTExHR0dPTExMT0xMR0dHR0dMAgcCBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHHwMhBh8DIQYgAyEGIAMhBh8DIQYgAyEGHwMhHQJCXE9TV1pXV1NXU1daWldaV1xUXFxcWlxcXFpcWlpaXFxcWlxcXFxcXFxcXFxcWlpTV1NXU1NPT0xMR0dHT0dMR0xHTEVMR0xHHwYfAyEGIAMhBiADIQYgAyEGIAMhBiADIQYgAyEGIAMhBiADIQYgAyEGHwMhBh8DAx8CHQMfAh8DHwIfAx8CHwMfAh8DHwIdAx8CHwBCXE9PV1NXU1dTU1NaV1paWlpUWVxaXFxcWlpaXFpaWlxcWlpcXFxaXFpcWlpXV1NXU1dTU0xMTExHTEdHR0dHTEdMRUdHR0xEAB8DHwIfAx8CHQMfAh0DHwIfAx8CHwMfAh8DHwIfAx8CHwMfAh8DHwIfAx8CHQMfIQcgAyEHIAYhByAGIQcgBiEHIAYhByADIQcgBh0qXFNTU1dXV1dXU1daWldaWlpUVFxcXFxcXFpcWlpaWlpcWlxaXFpaV1pXWldXV1dTV1NTT09MT0xMR0dHR0dMR0dFRUVFRUxBKgAHHyAGIQcgAyEHIAMhByAGIQcgBiEHIAMhByAGIQcgBiEHIAYhByAGIQcgAyEHAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwIfAQcDHwEAVFpMT1NXU1dTU09XWldXWldaTlxaXFpcWlpXWldaU1NXXFdXV1pXV1dXU1dTV1NTT1NMTExPR0xHR0VHRUdFRUVHRUdFR0VMT0kkAQMfAQcDHwEHAx8BBwMfAQcDHwEHAh8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHIAMhBh8DIQYgAyEGHwMhBiADIQYgAyAGHwMhBiEARFxTTFNTV1NXU1NTWldXV1paVFRcWlpaXFpaV1pXV09TV1pXV1dXV1dXV1NXU1dTU09PTE9MTEdMR0dFR0VHRUxHR0dPT1NMT1dUJBwHHwMhBh8DIQYgAyEGIAMhBh8DIQYgAyEGIAMhBiADIQYfAyEGIAMhBiADAx8CHQMfAh8DHwIfAx8CHwMfAh0DHwIdAx8CHQMdAFlaT0xPU1dTU09TU1dTV1dXV09cWldaV1pXWldXV1dMU1daV1dTV1NXU1dTU1NTT09PT0xMR0dBRUdHRUdHTEdPTE9MU1NTT05XTgAHAx8CHQMfAh8DHwIfAx8CHwMfAh8DHwIfAx8CHQMfAh8DHwIdAx8CHQMfIQcgAyEHIAMhByAGIQcgBiEHIAYhByADIQcgAyEfAypcVE9MU09XT09PU1NXV1dXWlNTXFpXV1daV1dXWldTTFNTV1dXV1dTV1NXU1dTU09TTExHRyRETE9MTEdMTE9PV1NUT1pXWlRUVzwAIQcgAyEHIAMhByAGIQcgBiEHIAMhByAGIQcgBiEHIAYhByADIQcgAyEHAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAwE8XFNMR09PU0dHTFNTV1NXU1dMVFpXU1dTV1NXU1dTU0dMTFNPU1NXU1NTU09PTExHR0hEBUFFR0xPTE9PT09XU1pUVFRaVFpOV0QBAwcDHwEHAh8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcCHwEHHwMhBh8DIAYgAyEGIAMhBh8DIQYfAyEGHwMhBh8DIB0CKllaT0xPT1NBR09TU1dXV1NXTFRaWlNXU1dXV1NXU1NHTExPTE9PU09PTE9HTEdMRUEkRUhHRExPU1NXV1pXWlpcXFpZXFpUU0wAIAMhBiADIQYgAyEGIAMhBh8DIQYgAyEGHwMhBiADIQYgAyEGHwMgBiADAx8CHQMfAh0DHwIfAx8CHwMfAh0DHwIfAx8CHQMfAh0GAgBJVFdMTExPPERPT09TU1dTV0dTWlpTV1NXU1dTU1NTTEdFR0dMTExHTEhMR0QuLjxISEhIR0dPU1NTWlpaWlxaXFxcXFpUVEwFAx8CHQMfAh0DHwIfAx8CHwMfAh0DHwIdAx8CHwMfAh8DHwIdAx8CHQMfIQcgAyEHIAYhByAGIQcgBiEHIAMhByADIQcgAyEHIAMhHR0AKkRUT1NPT0FBTE9MU1NXU1dMTFNaV1dTV1NXU1dTU09PR0dFR0dHR0Q8Li5BRUpFSkhNQU5PVFdaWlxcXFxcXFxcXFpaVEwFIQcgBiEHIAYhByAGIQcgBiEHIAMhByAGIQcgBiEHIAYhByADIQcgAyEHAQcDHwEHAh8BBwMfAQcDHwEHAx8BBwMfAQcCHwEHAx8BBwMfAAABLjxHTFNEPEFMTExMT09TTEdHU09TT09PU09PTE9HTExPTEc8JCRBRUhFSEVISEpKRURaU1pTWlxcWlxcXFxcXFpTU0cFAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcCHwEHHwMhBh8DIQYgAyEGIAMhBiADIQYfAyEGHwMhBh8DIQYfAyEGIB0DQkQkLjxBQSoFQUVMTE9MT0xHRUdMT0xPT09MT0xPR0dBPCQ8QUhFSEhIRUpISkhNSERaVFdXU1xcXFpcXFxcXFRTT0cBHwMhBh8DIQYfAyEGIAMhBiADIQYfAyEGIAMhBiADIQYgAyEGIAMhBh8DAx8CHwMfAh8DHwIfAx8CHwMfAh0DHwIdAx8CHQMfAh0DHwIdAyAASVpPRy4uPC4uLi4kPDxEQUdHTEVEQUFBQTxBPDwuLiQuQUVISEVISE1ISEhKSEpISkFcVFdPU1daWlpUWlpcVFRPT0QCAx8CHwMfAh8DHwIfAx8CHwMfAh8DHwIfAx8CHwMfAh8DHwIfAx8CHQMfIQcgAyEHIAYhByAGIQcgBiEHIAYhByADIQcgBiEHIAMhByADIR8CRFpMRzxUSEhISkhFQTwuLiQuJC4kLi48Ljw8QUFFRUhISkhISlBQUk1KSEpKTUpNSkRcWlNTT1NXWldXT1dXWk9TTEQAIQcgBiEHIAMhByAGIQcgBiEHIAYhByAGIQcgAyEHIAYhByAGIQcgAyEHAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAR8ASVdHQUJWTUpKRUhFSEVIRUhFRUVFRUhISEVISEhFSEVISE1NUlBSUE1FSEhNSEpITUJcWlNMTExTU1dTT0xTT09MTEECAgcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHHwMhBh8DIQYgAyEGIAMhBiADIQYfAyEGIAMhBiADIQYfAyEGIAEqWU9MQURcUFVSUk1NSEhFSEhIRUhFSEVISEpISkhNTVJQUlBVUlVQVUpISE1KTUhNSkRcXExMTE9PV1NTT09MT0xMTEEAIQMhBiADIQYgAyEGIAMhBh8DIQYgAyEGIAMhBiADIQYfAyEGHwMhBh8DAx8CHQMfAh0DHwIfAx8CHwMfAh8DHwIfAx8CHwMfAh0DHwIdBgFEXExPJE5ZVVJSUFJQUk1QSk1KTUpNSlBNUE1QTVVVVVJVVVVSVVJVUEpISkhNSEpKTEJcVE9HT0dMT1dPT0xMTExHTC4CAx8CHQMfAh8DHwIfAx8CHwMfAh0DHwIfAx8CHwMfAh8DHwIfAx8CHwMfIQcgAyEHIAMhByAGIQcgBiEHIAYhByAGIQcgBiEHIAMhByAGIQFZVFdMLllcXFxWWlJVUFVSUlBSUFJSVVJVUlZWVk5JVVZOTk5VVVZVVUpKSk1KTUpQRUlcWkxHTE9MT09TTE9MTExMRzwBIQcgAyEHIAYhByADIQcgBiEHIAYhByAGIQcgBiEHIAMhByADIQcgBiEGAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwIfADtaVFNHJE5JTk5OTlZVVlBSUFJQUE5WVVZVVlVORElESURJSUlJTlBVUEpISkpNSEpNRERcVExFRUxMR0xMT0dMR0xHRy4DAwcDHwEHAx8BBwMfAgcDHwEHAx8BBwMfAQcDHwEHAh8BBwMfAQcDHwEHHwMhBh8DIQYfAyEGIAMhBiADIQYgAyEGIAMhBiADIQYfAyEdAkJaWldBRE5UTk5JTklZWVlVUk1VUE5WTk5UTklJVElJTFdXV1NXTE5VUkpKSk1KTUpQQUlcVEdMRUdPT0xPTE9MTEdMRzwBIQMhBh8DIQYgAyEGIAMhBiADIQYgAyEGHwMhBiADIQYfAyEGHwMhBiADAx8CHQMfAh8DHwIdAx8CHwMfAh8DHwIdAx8CHQMfAh0DHwIfAElaWk9ETlpXWldXV1RJVE5aTU5SUklWSVRJTlRaU1dXV09MTFNTU0dJTUpISkpNSk1NQUlcTEdHTEVHR0xHTExMR0xHTDwCAx8CHwMfAh8DHwIdAx8CHQMfAh8DHwIdAx8CHQMfAh8DHwIdAx8CHwMfIQcgAyEHIAYhByAGIQcgBiEHIAMhByAGIQcgBiEHIAMhByAHBkRcWkRJV0dEQUdPV1dXTklOTkxVUklOSVpaWldTU09MQURJTklJR1dETUpKSk1KTUpQQU5cT0VMR09PTEVFRUdFR0VFRUQBIQcgBiEHIAYhByAGIQcgBiEHIAYhByAGIQcgBiEHIAYhByADIQcgBiEHAQcDHwEHAh8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAEJaWjxMQURERC48QUdMU0xJR01NTUhEQUlMTEdEPDw8SVRcXFxZTkdHR01FSkpNSkpNQUlaR0dHTEdPU1NPU0xPR0xHR0QFAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcCHwEHAx8BBwMfAQcCHwEHHwMhBh8DIAYfAyEGHwMhBiADIQYfAyEGHwMhBiADIAYfAyAHBiRaV0RESVxcWVZJRDw8PDwkRFBQTU1FQTxBPEFBREROVFlUXFlcXFZHR0pKSk1KTUpQQUlaTEVMTE9MT09XU1NMTEdMR0wuBgYhBiADIQYgAyEGIAMhBiADIAYfAyEGHwMhBiADIQYfAyAGHwMgBiADAx8CHQMfAh0DHwIfAx8CHwMfAh0DHwIfAx8CHwMfAh0DHwIdAwJOWkQ8VFlWTklJSUlBQUFBPFVVVU1IRUVBSEhJRElJTk5UTllZWVlVSk1KTUpNSk1NQURaR0dHTExPT1NPVFRWU1NMTEdBACACHwMfAh8DHwIfAx8CHQMfAh0DHwIfAx8CHwMfAh0DHwIdAx8CHQMfIQcgBiEHIAMhByAGIQcgBiEHIAMhByAGIQcgBiEHIAMhByADIQE7WlMuVFZKQUREREROSUpFQVZaVlJISkVFRERJSUREQkJCRC5UWVlWVlBNTVBKTUpQRERaTExMR09PU1NXV1paWlNPR0xHJAMgBiEHIAYhByAGIQcgAyEHIAMhByAGIQcgBiEHIAYhByADIQcgAyEHAQcDHwEHAh8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAR8ARFdBRFYuQkJLIwAcLkFESVlVVU1KSEVBREFBQ0tDIwAqLkI8TlBOSUlNUEpNSk1KSC5UTExMR0dPT1NPU09TVFRMR0VMJAIDHwEHAx8BBwMfAQcCHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHHwMhBiADIQYgAyEGIAMhBh8DIQYgAyEGIAMhBiADIQYfAyEGHwMgAE5HRE5OXFxZWVRUVFlEVFZZUlBISkhKTVRZWVlZWVxcXFxZSU5OTklOTVBNTUpNSjxOU0dMTExMT09TTFNUXFpUTExHPAAhBiADIQYgAyEGIAMhBh8DIQYgAyEGIAMhBiADIQYgAyAGHwMhBh8DAx8CHwMfAh0DHwIfAx8CHwMfAh8DHwIfAx8CHwMfAh8DHwIdAx8DAURJQlZZXFlcWVxcXFZJVFZWUkpKSk1KUlVWWVxcXFxcWVRUXFlWTk5QVU1QSk1ITTxOT0dHTE9TU1ZUXFxcWlRPT0VHPAMDHQMfAh8DHwIfAx8CHwMfAh8DHwIdAx8CHwMfAh8DHwIdAx8CHQMfIQcgBiEHIAMhByAGIQcgBiEHIAMhByAGIQcgBiEHIAYhByADIQchAERESVlWVVZVVlVQSVREXFZZUE1KUE1QUFZNUFVZVFROTklUVFlZWVJVUlJNUEpKSkdEWkdMR09TWlpcXFxUWlRXT0xHQQEhAyEHIAYhByAGIQcgBiEHIAYhByADIQcgBiEHIAYhByAGIQcgAyEHAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDByMuTlxQUk1NSElJWVRJWVlVTUpNSk1NUFBSSElHSkpQUFJSVk5SVVZSUlBQSkpISko8Tk9FTEdMTE9PU1NXV1RMTExMQQEDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHHwMhBh8DIQYgAyEGIAMhBiADIQYgAyEGIAMhBh8DIQYfAyEGHwMhBwMFXFZVVVZVVlZZVk5JXFlVSk1NUE1QTVVSVVJSUFVSVVJVUlVQUFJVUFJQTUhKSE1FPFNPR0xMTExPT1NMRC5BRExPQQAhBiADIQYgAyEGHwMhBiADIQYfAyEGIAMhBiADIQYfAyEGIAMhBiADAx8CHQMfAh8DHwIfAx8CHwMfAh8DHwIfAx8CHwMfAh0DHwIdAx8CHwA7WVVSVVJWVVZSVklOVllQSkhNTVBNUFBSUFJSVVBSUFJQUlBSTVBQUk1QSkpFSEhNQTxMT0dMR0xHR0EuBUFFR0VPLgMDBwMfAh8DHwIfAx8CHQMfAh0DHwIfAx8CHwMfAh8DHwIfAx8CHQMfIQcgAyEHIAMhByAGIQcgBiEHIAYhByADIQcgAyEHIAMhByADIQcgBwY7XFJWVVZVVlVWVUlUWVZVSk1NUE1QUFVSVVJVUlZVVlVWUlVQUlBSUFJNTUhISEpITUQ8QUdHR0E8JDxBPEVFR0dHJAMhAyEHIAMhByADIQcgAyEHIAMhByAGIQcgBiEHIAMhByAGIQcgAyEHAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwIfAQcDHwEHAx8BBwMfAQcDIABCVlVVVlVWUlVVUERZVVZNSkhNSk1NUlBSUFVSVlVZVlZVVVBSUFBNUE1NSEVFSEVISE1IQSQ8JC48REFELkxBTEdEAB8DHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHHwMhBh8DIQYgAyEGHwMhBiADIQYgAyAGIAMhBh8DIQYfAyEGHwMgHQJCWlJZVllWVlJaRE5WVlVSSk1NUE1SUFVQVVJWVVlZWVlZVlVQUlBSTVBKSEVISEpISkhNR0FFRUFKRURBQUxHR0wkBgYhBh8DIQYgAyEGHwMhBiADIQYfAyEGHwMhBiADIQYgAyEGIAMhBh8DAx8CHQMfAh0DHwIfAx8CHwMfAh0DHwIfAx8CHwMfAh0DHwIdAx8CHwBEVVVWVlVWVVZKQlZSVllQTUhQSkdNUlBSUFJSVlZZWVlWVlJVUFJQUEpKRUhFSEhISEpKTUFFRURQR0k8QU9HTzwAAx8CHQMfAh0DHwIfAx8CHQMfAh8DHwIfAx8CHwMfAh8DHwIdAx8CHQMfIQcgAyEHIAMhByAGIQcgBiEHIAMhByADIQcgAyEHIAMhByADIQcgBwZEVlJWVlZVVlVESVVSXFlVSkpNVUdEUFJSVVJVVVZWWVlZVVZSUlBSTU1ISEVISEpISkhNTUFFSklaRE4kR09PRwUDIQcgAyEHIAMhByAGIQcgAyEHIAMhByADIQcgBiEHIAMhByAGIQcgAyEHAQcDHwEHAh8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDIABCVVBSVlVWUFVBTk1SWVZNSkhQUFJBSkhQUFJQUlJWVVZVVVBSUFBNTUhIRUhISEVISEpNRDxISFRUSUQkRU9HJAAfAQcCHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcCHwEHHwMgBh8DIAYfAyEGIAMhBiADIAYfAyEGIAMhBh8DIQYgAyEGHwMhBwM7WU1SUlZSUlVJRFJNUk1KRUVITVBBSEVIUFBSUFVSVVJVUlJNUk1NSkpISEhKSEpISkpHJERQVVZOTkEuTE9BACEGIAMgBh8DIQYgAyEGIAMhBh8DIQYfAyEGHwMhBiADIQYgAyEGIAMgBh8DAx8CHQMfAh0DHwIfAx8CHwMfAh0DHwIfAx8CHwMfAh8DHwIdAx8CHwAqVFBNUk1QTVBKJEFKRUVBLiQ8QUE8UkhBRUpKUFBSUFBNUE1QSk1KSkVISEhISEhIRUpFLk5WVVROTgRFR08FBwIfAx8CHQMfAh8DHwIfAx8CHQMfAh0DHwIdAx8CHwMfAh0DHwIfAx8CHQMfIQcgAyEHIAMhByAGIQcgBiEHIAMhByAGIQcgAyEHIAMhByADIQcgBiADVFBQUFBNUEhQSTw8QTxBRUhBQURSVVVNQUFISk1KUE1QTVBNTUpNSEpISkhKSEpISEhQVVlVVlBWPDxHT0ccByADIQcgAyEHIAYhByAGIQcgAyEHIAMhByADIQcgBiEHIAYhByAGIQcgAyEHAQcDHwEHAh8BBwMfAQcDHwEHAx8BBwMfAQcDHwIHAx8BBwMfAQcDHwIATlJITUpKRUVNVlVHPEFBRUhSUlVSVVJVUkk8QUFISEpKTUpNSk1ISEhISEhISkhIRUVNVlVWTVBFJEVHT0EAHwIfAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHHwMhBh8DIQYgAyEGIAMhBh8DIQYgAyEGIAMhBiADIQYgAyEGHwMhBiEASVVKSk1IREhWVVZSUEhKTVZVVVJVVVZVVlZWSUE8SEVNTVBNUEpNSEpISkhKSEpFSEFQVVZSUEcjQUdMVy4DBiAGHwMhBh8DIQYgAyEGHwMhBh8DIQYfAyEGHwMhBiADIQYfAyEGHwMhBiADAx8CHQMfAh0DHwIdAx8CHQMfAh0DHwIfAx8CHwMfAh0DHwIdAx8CBwYCQlZISkhFRFZSVlVVUlVSVVJVUlVSVVJVVVZWXFVHQUpITU1QSk1ISkhISEpISkhIRUFKUE1QRSM8R0VPTyQBHwIdAx8CHwMfAh8DHwIdAx8CHQMfAh0DHwIdAx8CHQMfAh0DHwIfAx8CHQMfIQcgAyEHIAYhByAGIQcgAyEHIAMhByAGIQcgAyEHIAYhByADIQcgAyEBO1ZNSkhBXFlWVVZWVlVWVllWWVZWVVZVVlZOQU5WSU1QTVBNUEpNSEpISkhKSEpIRS5KTVBFJEFHR0xPUyQfByADIQcgAyEHIAYhByADIQcgBiEHIAMhByAGIQchAyEHIAMhByADIQcgAyEHAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwIDI1lNTUFOXFlVVlZWVFlUVExOTlRUVlVWVE5ESUdWUlBNUE1QTU1ISEhKSEhISkVIRQUFPC4FQUdFTEdPUy4AHwIfAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHHwMhBh8DIQYgAyEGIAMhBh8DIQYfAyEGIAMhBiADIQYgAyEGHwMhBiADI1RSTUhZXFZcVlBISkpNSEhBRURERERESU5ZWVlWVlJSTVBNUE1NSEpISkhKSEhFQS5BLkEuR0VHTExMV0EDBiAGIAMhBiADIQYgAyEGIAMhBh8DIQYfAyEGHwMhBh8DIQYfAyEGHwMhBh8DAx8CHQMfAh0DHwIfAx8CHwMfAh0DHwIfAx8CHwMfAh8DHwIdAx8CHQMfAFRSUk1ZVEREREFERERBRERJSU5OTk5WVVZVVlVWVVJNUE1QTU1KSkhISEpISEVIPDxFRUUuRUdFT0xPV0wAIAIdAx8CHQMfAh8DHwIdAx8CHwMfAh8DHwIdAx8CHQMfAh0DHwIdAx8CHQMfIQcgAyEHIAMhByADIQcgBiEHIAMhByAGIQcgBiEHIAYhByADIQcgAyEHAk5WUFJVWVZUTllZWVRUWVxZXFlZUlZSVVBVVVZWVlBQUFJQUk1NSEpISkhKSEhFPEFFRUUkR0VMT1NMU1dBACEHIQchBiEGIAMhByADIQchAyEHIAYhByAGIQcgAyEHIAMhByADIQcgAyEHAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEfAE5VUFBSUlVSUE5WVllWWVVVSkdBSk1QTVBNUlJVUFBQUk1QTVBISEhKSEhISEVFLkVFRUUkRUVHT09PT1dTQQAcAQcDHwEHAh8BBwMfAQcDHwEHAh8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHHwMhBh8DIQYfAyEGHwMhBh8DIQYfAyEGIAMhBiADIQYfAyEGHwMhBh8HAklWTVVQUk1NSEFBREREREQ8PDxISlBNUE1SUFVSUlBSUFJQUk1NSEpISkhKRUVBPEVFSEckR0VHTFdTREdXV0kFHQMhBh8DIAYfAyEGHwMhBiADIAYfAyEGIAMhBiADIQYfAyEGHwMhBh8DAx8CHwMfAh0DHwIdAx8CHQMfAh0DHwIfAx8CHwMfAh0DHwIdAx8CHQMgAERWUFBSUE1ISkhBLi4uPC5BRUhISkpNSk1QVVBSUFJQUlBSTVBISkhISEpFRUU8LkVISkUkREdFTE9XRAAFJAAGAx8CHQMfAh0DHwIdAx8CHQMfAh0DHwIfAx8CHwMfAh8DHwIdAx8CHQMfIQcgAyEHIAMhByADIQcgAyEHIAMhByAGIQcgBiEHIAMhByADIQcgAyEfA0JZTVJQVVBNSk1ISEFERERERUhKSE1KUFBVUlVQUlBSUFJQUk1NSEpISkhIRUUkRUhNSEokREdHRUxPV0k8Ix8HIQcgAyEHIAMhByAGIQcgBiEHIAMhByAGIQcgAyEHIAYhByAGIQcgAyEHAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAh8BBwMfAQcCHwEfACpUUFBSTVJNTUpKSVRVVlVWTk5KTUpQUFVSVVBSTVBQUk1QTU1ISEhIRUVFSC4uRUpISkgFQUhFRUFHTFNPKgEfAQcDHwEHAh8BBwMfAQcDHwIHAh8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHHwMhBh8DIQYfAyEGHwMhBiADIQYgAyEGIAMhBh8DIAYfAyEGHwMhBh8DIAJUUFBQUlBVUFJSWVZWVVZVVlZWUlVSVlVWUlVQUlBSUFJQUkpKSEpISEVIRS5BSEhKSkEqLkFMR0dFR0QkACEGHwMgBh8DIQYgAyEGIAMgBh8DIQYfAyEGIAMhBiADIQYgAyEGHwMgBh8DAx8CHQMfAh0DHwIdAx8CHwMfAh8DHwIdAx8CHQMfAh0DHwIfAx8CHwMfAwBJVkpSUFJQUlBSVVZVVlVWVVZVVVJVVVZVVVBQUFJNUlBSTUpISEVFRUVFLkFFRUhIRSRbIQU8REREPCMBIAIdAx8CHQMfAh8DHwIfAx8CHwMfAh0DHwIfAx8CHQMfAh8DHwIfAx8CHQMfIQcgAyEHIAMhByADIQcgAyEHIAYhByAGIQcgAyEHIAMhByADIQcgAyEHIQBCVk1NVVJVUFJNVlVWVlZVVlVWUlZVVlVWUlJQUlBSUFJQUEhKSEhFRUU8PEhFSkhNBFheQgICABwBAwMhByAGIQcgAyEHIAYhByAGIQcgBiEHIAYhByAGIQcgBiEHIAYhByADIQcgAyEHAQcDHwEHAh8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8ATlBNUFZQUk1NUFZVVlVWUlJNUlJWVVZSUk1STVBQUk1QSkhFRUVFRTw8RUVISE0iQ15fOyADBgIHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHHwMhBh8DIQYfAyEGIAMhBiADIQYgAyEGIAMhBiADIQYgAyEGHwMhBh8DIR0CO1lKUllWUFJNUFBVUlVQUk1QUlZWWVVVUFJQUlBSUFBKSkVFRUVFQUFFRUhIUEE7Xl9fQhsrAB8DIAYfAyEGHwMhBh8DIQYgAyEGHwMhBiADIQYgAyEGIAMhBiADIQYgAyEGHwMhBh8DAx8CHQMfAh0DHwIdAx8CHQMfAh0DHwIfAx8CHQMfAh8DHwIdAx8CHQMfAh0DAUlVSlRVUlBNSlBQUk1QTVBKVVVWVVVQTUpQUFJNUEpKRUVFRUVFRUVBRUVNQSNbX15eIScnIAAfAh0DHwIdAx8CHQMfAh0DHwIfAx8CHQMfAh8DHwIdAx8CHQMfAh8DHwIdAx8CHQMfIQcgAyEHIAMhByADIQcgAyEHIAMhByADIQcgAyEHIAYhByADIQcgAyEHIAMhAiNUUkFSUFVQTUpQUFJNUEpQVVZVVVBQSlBQUlBSTUpFRUVFRUVFRUVFRU1FI1hfXl9YHSksJx0BIQMhByADIQcgBiEHIAMhByAGIQcgBiEHIAMhByAGIQcgBiEHIAYhByADIQcgAyEHAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8BHwAqTkQ8Uk1STU1KTUpNSk1QVVBSTU1ISE1QSk1ISEVFRUVFRUVFRUVFSkUFUV9eX15LACsmKyEBAR8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHHwMhBh8DIQYfAyEGHwMhBh8DIQYfAyEGHwMhBh8DIQYfAyEGHwMhBiADIQYfAyEALko8QU1KTU1NSlBNUE1QTU1KTUVBSE1ISEVFRUVFRUVFRUVFRUVNRQVRX15fXl87IScsJyslHAMgAyEGHwMhBh8DIQYfAyEGIAMhBh8DIQYfAyEGIAMhBiADIQYfAyEGHwMhBiADAx8CHQMfAh0DHwIdAx8CHwMfAh0DHwIdAx8CHwMfAh0DHwIdAx8CHQMfAh0DHwIfACRFPC5FRUhISkhKSEpISEVFPDxFSEVFRUVFRUVFRUVFRUVFRUpFBVFfXl9eX1gCJSslKSYtIAEDHwIdAx8CHQMfAh0DHwIdAx8CHwMfAh0DHwIfAx8CHwMfAh0DHwIfAx8CHQMfIQcgAyEHIAMhByADIQcgAyEHIAMhByAGIQchBiEHIAMhByADIQcgBiEHIAMhByADIQAjRUQkLjxBQUFBQUFBLi4uQUVIRUVFSEVIRUhFRUVFRUVFSkEjUV9eX15fX0sALycrJywnLQMFAyEGIQcgAyEHIAMhByAGIQcgBiEHIAMhByAGIQcgBiEHIAYhByADIQcgAyEHAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAR8ABUFFQTwuPC48Li4uQUFFRUVFRUVFRUVFRUVFRUVFRUVKPCNYX15fXl9eXiolJicmKSUpJyAAAgAdAgcDHwEHAh8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHHwMhBh8DIQYfAyEGHwMhBh8DIQYgAyEGHwMhBh8DIQYgAyAGHwMhBh8DIQYfAyEGHwMhAwVBSEVIRUhFRUVIRUhFRUVFRUhFSEVIRUVFSEVFRUouO1tfXl9eX15fUQMpKyYsJysmLx0hJiEAAwMhBh8DIAYfAyEGIAMhBiADIQYgAyEGIAMhBiADIQYgAyEGHwMhBh8DAx8CHQMfAh0DHwIdAx8CHQMfAh0DHwIfAx8CHwMfAh0DHwIfAx8CHQMfAh0DHwIdAx8CHwAFQUVFRUVFRUVFRUVFRUVFSEVIRUhFRUVIRUVIRQRCXV9eX15fXl9eQgEsJislKSYrJiEDKyYmAwIAHQMfAh0DHwIdAx8CHwMfAh0DHwIfAx8CHwMfAh8DHwIfAx8CHQMfIQcgAyEHIAMhByADIQcgAyEHIAMhByAGIQcgAyEHIAMhByADIQcgAyEHIAMhByADIQcgAyAAI0VIRUVFSEVIRUhFSEVIRUhFSEVIRUhFSEhBBUteX19fXl9fX15dAysnLCcrJiwnLB8hJysnLyUdAB0HIAMhByADIQcgAyEHIAYhByAGIQcgBiEHIAYhByAGIQcgAyEHAQcCHwEHAh8BBwMfAQcDHwEHAh8BBwMfAQcDHwEHAx8BBwMfAQcCHwEHAh8BBwIfAQcDHQA7Ai5FRUVFRUVFSEVFRUhFSEVIRUVFSEVISC4qWF5fXl9eX15fXl9GASkpJScmKSUnJiUCKSYpJSkmJQAAAR8BBwMfAQcCHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcCHwEHHwMgBh8DIQYfAyEGHwMhBh8DIQYgAyEGIAMhBiADIQYfAyEGHwMhBiADIQYfAyAGIAYgAEBARkYuRUhFSEVIRUhFSEhISEpFSEVISEpBJENeXl9fX15fX19eX14qIS8nLCcsJysmLCEfJywnKyYrJysbHAAdAyEGHwMgBh8DIQYfAyEGHwMhBiADIQYgAyEGIAMgBh8DAx8CHQMfAh0DHwIdAx8CHQMfAh8DHwIfAx8CHQMfAh0DHwIdAx8CHQMfAh0DHwIfAAMAO0ssS18qQUVIRUhFSEVIRUhISEVIRUhISC4qUV9eX15fXl9eX15fXlEALyYrJysmKSYrJiUCKyUpJiklJyYrJR8AAwEfAx8CHQMfAh0DHwIdAx8CHwMfAh8DHwIfAx8CHQMfIQcgAyEHIAMhByADIQcgBiEHIAMhByADIQcgAyEHIAMhByADIQcgAyEHIAMhBx0AIxwlRkYlUV5bBUVISEhKSEpISkhKSEhFSkhBI0teX15fX19eX19fXl9fXzslLS0nLyksJywnLCUgKSwnLCcrJiwnLCcrBgIAIAcgAyEHIAMhByADIQcgBiEHIAMhByAGIQcgAyEHAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8AAAA9QBxAQz0gWF9eWAVFSEhISEVISEpFSEhKQSQ7W15fXl9eX15fXl9eX15fWAAnLSksJysnKyYpJyYAKSYrJikmKyYpJikmKSEcAAICHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHHwMhBh8DIQYfAyEGHwMhBh8DIQYfAyEGHwMhBh8DIQYfAyEGHwMhBiAGHwAfO0ZGISZAMjohXl9fXlgjQUpKSEpISkhKSkguO1FfX19eX19fXl9fX15fX19eQwc6KTIrLykvKy0pMiYcJi0pLScvKSwnLCcrJiwnJgECASADIQYfAyEGHwMhBh8DIQYgAyEGHwMhBh8DAx8CHQMfAh0DHwIdAx8CHwMfAh8DHwIfAx8CHQMfAh8DHwIHAx8DHwEBADtDRkAmAz0rOic7Xl9eX15bKjxISkhKSE1FPCRLXl9eX15fXl9eX15fXl9eX15bACwsLyctKS0nLSkvKSkBKSYsKS8nLCktJysnKyUpJisbAgAcAx8DHwIdAx8CHwMfAh0DHwIfAx8CHwMfIQcgAyEHIAMhByADIQcgAyEHIAMhByAGIQcgAyEHIAMhByADIQcdACM7RkZDPS8CPTI9MidCX15fX19eX0Y8RE1KSjwqRl5eX15fXl9fX15fX19eX19fXl9DGzI6LTIsOi0yLDItMikdJi8sOi0yKzIsLykvKSwnLCcsJiUAAwMhByADIQcgAyEHIAMhByADIQcgAyEHAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAAADPUBGQD0tLwAsLTItPQNCXl9eX15fXl87BQUkI0ZbX15fXl9eX15fXl9eX15fXl9eX10cJzopLysvKS0rLykvKywAJicyKS8rMiktKS8nKycrJikmKSYmAwEABgMfAQcDHwEHAx8BBwMfAQcDHwEHHwMhBh8DIQYfAyEGIAMhBh8DIQYfAyAGHwMhBh8DIQYgAxwAIT1GRkAyPS89Aic6Oi89OgZCX15fXl9fXSooPjEoJFhfXl9fX15fX19eX19fXl9fX15fX0sAPS0yLTotMiw6LTItOiwcJS8tOi06LTItOi0yKTIrLScsJysmLCUdABwGIAMhBiADIQYfAyEGHwMhBh8DAx8CHQMfAh0DHwIfAx8CHQMfAh0DHwIdAx8CHwMfAx8AARxARkZAPS86KzofHy8yLTotPQBGXl9eX15eKig/Pz4/MSRbX15fXl9eX15fXl9eX15fXl9eXiMmLTItMisyLDIrMi0yLC8BJicyLTosMi0yKy8rLyktKS0nKycrJSkmJgAAAR8CHwMfAh0DHwIdAx8CHwMfIQcgAyEHIAMhByADIQcgAyEHIAMhByADIQcgAyEHAwAqQEZGQz09Lz0vPSYcLD0vPS89LwVLX15fXl9DIj8/Pz8/Pyg7Xl9eX19fXl9fX15fX19eX15fSwUyOi89LzotPS86LT0vOi0fJS8tPS86Lz0vOi06LzosOiwyKS8pLCcsKSwfHAAfByEHIAYhByADIQcgBiEHAQcDHwEHAx8BBwIfAQcDHwEHAx8BBwIfAQcDHwAAIUNGRkA9LTItOi0yKwIlOi06LDIvLABLXl9eX1EEPz8+Pz4/Pj4EQ15fXl9eX15fXl9eX15fXl9YAiE6LDIrLywyKzItMisyLTIAJScyLTItMisyLDIrLywyKS8pLycsJysmKSYrIR0AAwIHAh8BBwMfAQcDHwEHHwMhBh8DIQYfAyAGHwMhBh8DIAYfAyAGIAMcACpAS0ZAOj0vOi09LzoyISE9LT0vOi09JgVRX15fXSo+Pz8/Pz8/PzExAFhfX15fX19eX19fXl9eX10qAD0vPS86LT0vOi09LzotPTIgIS8vPS89LzotPS86LTotMiw6LTIpMissJywnKycnAQICIQYfAyEGIAMgBh8DAx8CHQMfAh0DHwIdAx8CHQMfAh0DHwMfAAEgQEZGQD0vOiwyLTotMjImATotOi0yLTotJSNRXl5eQwA/Pz8+Pz8/PjExKCNdXl9eX15fXl9eX15fXkMAJS86LTItOi0yLTotMi06LDoDJScyLTotMi06LTItOi0yLTIrLysvKS0pLCYpJismKQMCAB8DHwIdAx8CHQMfIQcgAyEHIAMhByADIQcgAyEHIAMhBwYAKkBGQ0M9PS89Mj0vPS86Ly8COi89Lz0vPTIyIEJRX15YKkIxPz8/Pz8/PzExPiJCX15fXl9fX15fX19eSyoqKT0vPS89Mj0vPTI9Lz0yOjIlIC8tPTI9Lz0vPS89LzotPS86LTovMiwyLC8pLyksJywfAgAhByADIQcgAyEHAQcDHwEHAh8BBwMfAQcDHwEHAx8AASFARkZAPS0yLTosMi06LDItMgAnLzIsMi06KzolKkNLXl8qS0MoPz8/Pz4/MTExMQQcS19eX15fXl9eX15RKkMCPSwyLTosMi06LDItOi0yLDobHycyLTItMiwyLTosMi0yKzIsMisvKzIpLSkvJyspJgEgJSAAAwMfAQcDHwEHHwMhBh8DIAYfAyEGHwMhBh8DHQAqQ0tGQz09LzovPS86Lz0vOi09BiEyPS86Lz0vOjIlQkZLX1E7WEsiPz8/Pz8+MTE+BENRI1tfXl9eX19fXlsjUSMsOjovPS86Lz0vOi89LzovPTImAy8vOi89LzovPS86Lz0vOi09LzotOi0yLDotMislHyspLyklAB8GHwMgBh8DAx8CHQMfAh0DHwIdAx8CHQMDAjtAS0BAOjotMi06LTItOi0yLT0hBiw6LDItOi0yLT0ARkZGXjtLWFgkPj8/Pz4xKD4iO1FYQ0JeX15fXl9eXiNLSwIvOi06LTItOi0yLTotMi06LT0mHScyLTotMi06LTItOi0yLTotMi06LDIsMisyKSAhMissJikmIQAdAx8CHQMfIQcgAyEHIAMhByADIQcgBiAARjpAQEAyPTI9Lz0yPS89Mj0vPTIdJT0vPS89Mj0vPToGS0tLWDtYW14uPz8/Pz4xPigqWFhYWypLXl9fX15fQkNbOxs9Lz0yPS89Mj0vPTI6Lz06PSkhBi8tPTI9Lz0yPS89Mj0vPTI9Lz0vOi09Lz0rJSk9LDIrLCcrJx0AIQYgAyEHAQcDHwEHAx8BBwMfAQcCHwA7RiYvPS06LDItOiwyLTosMi06LDImAiU9LTIsMi06LS8BUVFGQktbX147MT8/PzExKAVLWFteWFEcW15fXl9CQltYACwtOi0yLTosMi06KzIvOiclAgMDJykyLDItOiwyLTosMi06LDItOiwyLTIrMishJzIsMicrJiklKSAAAQcDHwEHHwMhBh8DIQYfAyEGHwMhAxxDRiU6Lz0vOi89LzovPS86Lz0vOi86Jh0lPS86Lz0vPScqWFsqQlheXl87MSgoMT4xIkBYWF9fXltLO19eX0Y7WF9LAzI9Lz0vPS86Lz0vPS8sHQYCJictKT0vOi89LzovPS86Lz0vOi89LzovPS86LyUpPS06LS8nLCcrJiwBHAMgBh8DAx8CHQMfAh0DHwIdAx8DACZGPSYvOi0yLTotMi06LTItOi0yLTorLCYGIDotOi0yMiU7W10qS15eX15GBCgiIiIoJFFYXl5fXl5bQkZfSztYXV4qJT0sMi06LTItOi0yJR0AICUrJywrOi0yLTotMi06LTItOi0yLTotMi06LTIvJSU6LTorLScrJSkmKSYgAB8CHQMfIQcgAyEHIAMhByADIQchAENGPSU9Mj0vPTI9Lz0yPS89Mj0vPTI9LC8pBiU9Lz0vPQNDW19YXl5fX187Pj8/MTEFUVhdX19eX19eWEJDQlhdX1gAPTI9Lz0yPS89MikCHyEsKS8rMi09Mj0vPTI9Lz0yPS89Mj0vPTI9Lz0yOjIsIT0vPS8yKSwnKycsJywlBQYgAyEHAQcDHwEHAx8BBwMfAQcBHENDJikvMi06LDItOiwyLTosMi06LDItPSkdASwtMi06LQFGW11fXl9eX1EiPz8+MTEiS1hdX15fXl9eX1FCWF1eX0IbMjItOiwyLTorMiUCJSwmLysyLTosMi06LDItOiwyLTosMi06LDItOiwyLTIDMi06LC8pKyUnJiklJyYnAAMDHwEHHwMhBh8DIQYfAyEGHwYDKkZAKyc9LT0vOi89LzovPS86Lz0vOi09KRwdOjI6Lz0yMgJRW19eX19fXkMoPz8/MT4ERlheXl9fX15fX19dXV5fXSMnPS89LzovPS86LT0mAiY9Lz0vPS86Lz0vOi89LzovPS86Lz0vOi89LzotPSErMj0vOiwvJysmLCcrJisnHwAhBh8DAx8CHQMfAh0DHwIdAyAAPUNAICsvOi0yLTotMi06LTItOi0yLzobAiY9LTItOiw6JSpRXV5fXl9eXQU+Pz8+MTEiQFhdX15fXl9eX15fXl9eUQA6LTotOi06LTItOiw6JQInOi06LTItOi0yLTotMi06LTItOi0yLTotMi09JiUvOi0yLC8mKSYrJSkmKSUrGwICBwMfIQcgAyEHIAMhByADIQYDQEY6Jis9Lz0vPTI9Lz0yPS89Lz0yLAIgLD0yPS89Lzo6JjtYXV9fX15fSyI/Pz8/MT4iQlhdX19eX19fXl9fX15fOyE6PTI9Lz0yPS89Mj0tPSYGJz0vPS89Mj0vPTI9Lz0vPS89Mj0vPTI9Lz0yJSs9MjotOissJywnKyYsJysnJwAgAyEHAQcDHwEHAx8BBwMfAgICRj06Hy8tMi06LDItOiwyLTosMiwhACYtOisyLTosMi09AUNYXl5fXl9eOyg/Pj8+PjEoO1hbX15fXl9eX15fXl9bAyk6LDItOi0yLTotMi0yKzomASE6LTosMi06LDItOiwyLTosMi06LDItOi0nIDosMi0yJykmKyUnJiklJyUpIQEBHwEHHwMhBh8DIAYfAyEGIAAqRkAvJi09Lz0vOi89LzotPS89Kx8fOjI9LzotPS86Lz0yBkZbXl9eX19bBD8/Pz8/MT4oO1hdXl9fX15fX19eX19LAEAvOi89LzIvPS86Lz0vOi09JwIlPS86Lz0vOi89LzovPS86Lz0vOi89LzobMjI6LTotLCcsJysmLCcrJiwnKwAdBh8DAx8CHQMfAh0DHwIHAwErRjo6IDItOi0yLTotMi06LTIyJQc9LzotMi06LTItOi0yAFFbX15fXl9GIj8/Pz8+MTEoI1hbX15fXl9eX15fXl8qJTIyLTotLzssKzotOi0yLTorOikGITotOi0yLTotMi06LTItOi0yLTosOiYlLTItOistJysmKSYrJSkmKSUnJh0AHwMfIQcgAyEHIAMhByAGIQBAQD0vJi89Mj0vPTI9Lz0vPS89ISYyPTI9Lz0vPS89Mj0nI1FdXl9fX14qMT8/Pz8/MT4oKlFbXl9eX19fXl9eX1sFLD0vPTI6O0tGQCc9Oj0vPS86LT0sHCc9Lz0vPTI9Lz0vPS89Mj0vPTI6LyYrPS89LzIpLycsJiwnKycsJysmLB0DBiEHAQcDHwEHAh8BBwIfAAJAQC0vHzosMi06LDItOiwyLTItJRs9KzItOisyLTosMi8mKlhbX15fXlgEPz8/Pj8+MTExBVFYXl5fXl9eX15eXksAPS06LTIpQkZGRkYkLS86KzItMi0sACstMi06LDItOiwyLTosMi06LDItLAcyLTIrLyksJSkmKSUpJiklJyYpJiEAHwEHHwMhBh8DIAYfAyAHBhxGPT0rJi86Lz0vOi09LzotPS89ISY6Oi89LzotPS86LUAbQlheX19eX0MiPz8/Pz8/MTExJFFbXl9fX15fX19eXyolMj0vOjIvRFFLRllOQjsvOi09Lz0HICw6Lz0vOi09LzovPS86Lz0vOi09JSkvPS86LDIpKyYsJysmLCcrJiwnKyECAyADAx8CHQMfAh0DHwIfACtDPS0vHzotOi0yLTotMi06LTIvJgc6LTotMi06LDItOi8DQ1tdX15fXSoxPz4/Pz8+MTExBEtYXl5fXl9eX15fWAErOi06LToqVFlZUVlZWUItLTotOiYCJSwtOi0yLTotMi06LTItOi0yLTIpISk6LDItLycrJismKSYrJikmKSUpJicABgMfIQcgAyEHIAMhByAHBTpGMj0sJi89Mj0vPTI9Lz0yPS89JiEyPTI9Lz0yPS89Mj0AS1tfXl9fWAQ/Pz8/Pz8/MTExBEtbXl9eX19fXl9fSwBAMj0vPS9CRE5ZWVRZTisvPS89Lx8gLCw9Mj0vPTI9Lz0yPS89MjotOi8rID0vOi89LS8nLCcsJywpLCcsJysmLCcDASEHAQcDHwEHAx8BBwMfAEBAOi0sHzorMi06LDItOiwyLTItJgM9KzItOiwyLTosMiwDS1teX15fQyI/Pz4/Pj8+PigxBEtYXl5fXl9eX15fOyUvMi06LS9CJgZBWVlZSSY6KzIvJgAnJzosMi06LDItOiwyLTosMi0yJy8bKS0yLTIpLScrJikmKyYpJiklJyYpJScAAwIHHwMhBh8DIQYfAyEDHENDLz0nJi86Lz0vOi89LzovPS89JSEyOi89LzovPS86Ly8cUVtfX19eOzE/Pz8/Pz8/MTExBEZbXV9fX15fXl9bHCs9Lz0vPSs7Lz0lQU5ZQjIyOi8yACYnOjI6Lz0vOi89LzovPS86LT0tMiklLDotPS8yKS0pLCcsKSwnLCcrJiwnKycfASADAx8CHQMfAh0DHwMCHUY9Mi0sGzItOi0yLTotMi06LTIvKQI6LTotMi06LTItPSUqUV1eX15bAD8/Pz4/Pz8+MTExBEZYXl5fXl9eX15RAD0tOi0yLTopMi09KSouKy0yLT0DBiYsLDItOi0yLTotMi06LTItOiwvKScbMi06LC8pLCYrJiwmKycsJikmKyUnJisCAgMfIQcgAyEHIAMhByEAO0Y9LT0rJS89Mj0vPTI9Lz0yPS89JiAyPTI9Lz0yPS89OiU7WF1fXl9LIj8/Pz8/Pz8/MTExBEZbXV9eX19fXl9CITo9Mj0vPTI9Lz0yPTIyLz0vPSkCJS8vPS89Mj0vPTI9Lz0yPS89LzorMiApLz0vOi0yKSwnLysvKS8pLCcsJysmLCkhACEHAQcDHwEHAh8BBwMAL0MvMisrGzosMi06LDItOiwyLTItJwI6LTItOi0yLTorPQNCWF1eX15CKD8+Pz4/Pj8+MSgxBEZYXV5fXl9eX10cJjosMi06LDItOiwyLTotMi06LQYDKycyLTosMi06LDItOiwyLTosMissJh8nMiwyLC8nKSYrJispLyYrJiklKSYpJSkbAQIHHwMhBh8DIQYfAyAAQ0A9LzonJS86Lz0vOi89LzovPS89Jh8yOi89LzovPS86Mh9DW11fX14jPj8/Pz8/Pz8/MTExJEZbXV9fX15fX1gAPS86Lz0vOi89LzovPS86Lz0yKQArKTovPS86Lz0vOi89LzovPS86LTIpKQc6LzotOiwtJywpLysyLC8nLCcrJiwnKycmACADAx8CHQMfAgcDHwADQ0AsMi0sBzItOi0yLTotMi06LTIvLAA6LTotMi06LTItPQBLWF5eX1EEPz8/Pz4/Pz8+MTExBEZYXl5fXl9eX0MGLzItOi0yLTotMi06LTItOi0yACUmLy06LTItOi0yLTotMi06LTItMicsHyYrMi06KS0nKyYsKS8pLSksJismKyUpJishAAMfIQcgAyEHIAMhBwYdRj06LT0pJS89Mj0vPTI9Lz0yPS89Kx0vPTI9Lz0yPS89LxxLW15fXksiPz8/Pz8/Pz8/MTExBEZbXV9eX19fXjslPS89Mj0vPTI9Lz0yPS89Lz0hHScsLz0yPS89Mj0vPTI9Lz0yOi89LCwnJSc6Lz0vMikvKS8rOi0yKzIrLCcsJysmLCcnACAHAQcDHwEHAh8BHwAqQz0sMikrBzIsMi06LDItOiwyLTItLAAyLTItOiwyLTotLAJRW19eXzsoPz8+Pz8/Pj8+MTExBEtYXl5fXl9eWwAvLzotMi06LDItOiwyLTosMikCICkpOiwyLTosMi06LDItOi0yLTIpLCYnAy0tOiwvKSwmKycvKS8rLycrJislJyYpJSklAgAHHwMhBh8DIAYfBgI7Ri89LTInJS86Lz0vOi89LzotPS89KR0vPS89LzotPS89JipRXV5fXSMxPz8/Pz8/Pz8/MTExBEtbXV9fX15fSwM6PS89Lz0vOi89LzotPS86LyUDKyc9LzovPS86Lz0vOi89LzotPS8yJywlJS09LzosMiksKTItMi06LC8pLycrJiwnKyYrAB0DAx8CHQMfAgcDHwBAQDosLyssAzItOi0yLTotMi06LTIvLwAvLzotMi06LTIyJiNYW19eWAQ/Pz8/Pz4/Pz8+MTExBEtYXl5fXl9eQgM9LTotOi0yLTotMi06LTIvLAAmJjItMi06LTItOi0yLTotMi06LDIpKyYlJTotMi0yJysnLykvLTIpLSktJikmKyYpJislAgEfIQcgAyEHIAMhAwNAQC86LTorISw9Mj0vPTI9Lz0vOi89LBwsPS89Lz0vPS89ITtYXV9fRiI/Pz8/Pz8/Pz8/MT4xBEtbXl9eX19eIyw6PS89Mj0vPTI6Lz0vPS89BiEnLy89Lz0yPS89Mj0vPS89Lz0vOi0yKSwbLC89Lz0tLykyLTotPS8yKzIrLCcsJywnLCcrAR0HAQcDHwEHAh8CAwJDOjIsLycsAy8tMi06LDItOiwyLTotLwEvLTItOisyLTIvGztYW19eQig/Pj8+Pz4/Pj8+MTExAEtYXl5fXl9YACsyLTotMi06LDItOiwyLTolACUrKTItOiwyLTosMi06LDItOisyLC8nKSUgJi8tMiktJywnLywyKy8pLycrJysmJyYpJScmBgAHHwMhBh8DIAYgACpDPS06LS8pISw9Lz0vOi89LzovPS86LB8rPS09LzovPS89AkNYXl5fIz4/Pz8/Pz8/Pz4/MTExJEtbXl9fX15LAD0vPS86Lz0vOi89LzotPS8cGywpOi89LzovPS86Lz0vOi09LzotOiwsJycbLy09LzIrLysyLTovOiwyLC8pLyksJiwnKyYsAwYDAx8CHQMfAgcDAiVDLzorLykvAywvOi0yLTotMi06LTItOgArLzotMi06LDIvBkZbXV9YBD4/Pj8/Pz4/Pz8+MTExAFFYX15fXl87ITI6LTItOi0yLTotMi06LyYAKyYvLTotMi06LTItOi0yLTosMi0yKy0nLBshKzotMisvJy0rMiwyLTIpLykvJysmKyYpJikmHAAfIQcgAyEHIAMhAD1APS86LDIsISk9Lz0vPTI9Lz0yPS89Mh8nPS89Lz0yOi89AktbX19RBD8/Pz8/Pz8/Pz8+MT4oI1FbXl9eX10jJz0vPS89Mj0vPTI9Lz0yOgAmKS8vPTI9Lz0yPS89Mj0vPTI9Lz0vOissKSAhOi89LTosLyw6LzovPS8yLDIsLycsJywnLCcsAxwHAQcDHwEHAh8CADpAKy8rLycsAywtMi06LDItOiwyLTorMgIrLTItOiwyLTorAktbXV9DIj8/Pz8+Pz4/Pj8xMTEoBVFYX15fXlgAOi0yLTosMi06LDItOis6IAMlJys6LDItOiwyLTosMi06LDItMisvKywlJwAmKzItMiktKS8pMi0yKy8rLycsJysmKSYpJScmHwAbHwMhBh8DIAYfAENAOi06KywnICs9Lz0vOi89LzovPS86LyEmPS09LzovPTIyAlFbX147KD8/Pz8/Pz8/Pz4+MT4oKlFbXl9eX0YHOjovPS86Lz0vOi89LzosHCErJz0vOi89LzovPS86Lz0vOi09LzotMiksJRwnOi09LzIrMi06LT0vOiw6LS8pLyksJiwnKyYsBwMD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AQcCHwEHARw9Oi06LC8nKyUpAiEtMi06LDItOi0yLTosMi0vAC8tOiwyMiU7WFgqMT8/Pz4/Pz8+Pz8/Pj4xPigjUVteUQA9LDItOiwyLTomACUpJzItOiwyLTosMi06LDItOiwyLTorLywyKS0nKyUnJSsbAys6LTItOiwyLTosMi0yKy8rLycsJysmKSYrJScmIQAHHwMgBh8DHR1ALz0vOi0yJysnIR89Lz0vOi89Lz0vPS86LT0vHSs9LzotPSBCWFgFPj8/Pz8/Pz8/Pz8/PzE+MSgjWFhfQxs6Oi89LzovPTIgAywnMi09LzovPS86Lz0vOi89LzovPS86LTotMikvJysmKyclAjovOi89LzovPS86Lz0vOi06LC8pLyksJywnKyYsHwIDAx8CBwMgACVAOi0yLTInKSYrAyAvOi0yLTotMi06LTItOi06AiwtMi06LyFCW1EEPj8+Pz8/Pj8/Pz4/Pj4xMSgqUVteQhs9LTotMi06LSwAJyYrLDotMi06LTItOi0yLTotMi06LDItMisvKy0nKSYpJSkbHSsyLTotMi06LTItOiwyLTIpLykvJisnKyYpJismIAAfIQcgAyEHBiVALz0vPS8vJyspIQY9Mj0vPTI9Lz0yPS89MjoyISc9Lz0vPRtDW0sEPz8/Pz8/Pz8/Pz8/Pz4+MSgjWFtfKikyPTI9Lz0vPSAgKSsrPTI9Lz0yPS89Mj0vPTI9Lz0yOi89LzotMissJywnKyclBjovPTI9Lz0yPS89LzovPS8yLDIsLycsKSwnLCcsBxwHAQcCHwEfACk9Mi06LC8nKSUpBx8tMi06LDItOiwyLTIsMiw9AyYvMisyMiBCW0MiPz8/Pz4/Pz8+Pz8/Pj4xPigqUV1dIyk6LDItOisyKwIbKSYyLTItMiwyLTosMi06LDItOisyLTIrLysvJysmKyUnJSsDBiw6LDItOiwyLTosMi0yKy8rLycsJysmKSYrJScmIAAHHwMgBh8GAytALT0vOiwvJysnJQM6Lz0vOi89LzovPS86Lz0yJiA9LzotPRtDW0MiPz8/Pz8/Pz8/Pz8/PzE+MSgqWF1bAT0vOi89LzovKQErJi8vPS89LzotPS86Lz0vOi89LzovPS86LTotLycsJysmKychAzovOi89LzovPS86Lz0vOi06LC8pLyksJywnKyYtBwMD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AQcDHwEHAh8BBwMfAQcDHwEHAh8BBwIfAQcCHwEHAh8BBwMfAgcDHwEGAAMAIj8/Pj8/Pz4/Pz8+Pz4/MTExPgQ7QyEnKyYmACUbJSAlHyEDHQEGAAEAAQAAAAIAAwEfAQcDHwEHAh8BBwIfAQcCHwEHAh8BBwIfAQcCHwEHAx8BBwIfAQcCHwEHAx8BBwMfAQcDHwEHHwMgBh8DIQYfAyEGHwMhBh8DIQYfAyAGHwMgBh8DIQYfAyAGHwMgBiADIQcDKD8/Pz8/Pz8/Pz8/Pz8+PjE+MSIAAgACAAMAAgADAAIAAwADABwCHQIgBiADIQcgAyEGHwMgBh8DIAYfAyAGHwMgBh8DIAYfAyAGHwMgBh8DIQYgAyEGHwMgBh8DIQYfAyAGHwMhBh8DAx8CHQMfAh0DHwIdAx8CHQMfAh0DHwIdAx8CHQMfAgcDHwIHAx8CBwMfAR0AKD8/Pz8+Pz8/Pj8/Pz4/MT4xPiIDAgcDHwIHAx8CHQMfAx8DHwIfAx8CBwMfAgcDHwIHAx8CBwMfAgcDHwIHAx8CHQMfAh0DHwIdAx8CHQMfAh0DHwIdAx8CHQMfAh0DHwIdAx8CHQMfIQcgAyEHIAMhByADIQcgAyEHIAMhByADIQcgAyEHIAMhByADIQcgAyEHIAYGMT8/Pz8/Pz8/Pz8/Pz8+PjE+MS4BIQMhByADIQcgAyEHIAMhByADIQcgAyEHIAMhByADIQcgAyEHIAMhByADIQcgAyEHIAMhByADIQcgAyEHIAMhByADIQcgAyEHIAMhByADIQcgBiEHAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwIfAQcCHwEHAh8AMT8/Pj8/Pz4/Pz8+Pz4/MTExPiIBAx8BBwIfAQcCHwEHAh8BBwIfAQcCHwEHAh8BBwIfAQcCHwEHAh8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHAx8BBwMfAQcDHwEHHwMhBh8DIQYfAyEGHwMhBh8DIQYfAyEGHwMhBh8DIQYfAyAGHwMgBh8DIAYFMT8/Pz8/Pz8/Pz8/Pz8+PjE+MSIAIQYfAyEGHwMhBh8DIAYfAyAGHwMgBh8DIQYfAyAGHwMgBh8DIQYfAyEGHwMhBh8DIQYfAyEGHwMhBh8DIQYfAyEGHwMhBh8DIQYfAyEGHwMhBh8DAx8CHQMfAh0DHwIdAx8CHQMfAh0DHwIdAx8CHQMfAh0DHwIHAx8CHQMfAgcAPj8/Pz8+Pz8/Pj8/Pz4/MT4xPiIDAh0DHwIdAx8CBwMfAgcDHwIdAx8CHQMfAh0DHwIdAx8CHQMfAh0DHwIdAx8CHQMfAh0DHwIdAx8CHQMfAh0DHwIdAx8CHQMfAh0DHwIdAx8CHQMfIQcgAyEHIAMhByADIQcgBiEHIQMhByADIQcgAyEHIAMhByADIQcgAyEHIAMjPj8/Pz8/Pz8/Pz8/Pz8+PjE+MSIBIAMhByADIQcgAyEHIAMhBiADIQcgAyEHIAMhByADIQchAyEHIAMhByADIQcgBiEHIAMhByADIQcgBiEHIAMhByADIQcgAyEHIAMhByADIQcgAyEH'), c => c.charCodeAt(0)) };
// Draw the digitized picture with its top-left at (x, y). It takes palette indices 0..95 (RA and the first half of RB) for its own
// colours, so a shot showing it keeps its other colours in RB's upper half (96..127), RC and the house ramps. o.reveal (0..1): how
// much of it has scanned in, top to bottom, with a bright line where the scan is (a VGA viewer loading it); o.frame: a steel frame.
function drawPortrait(x, y, o = {}) {
  const P = PORTRAIT;
  P.pal.forEach((h, i) => setCol(i, h));
  const rows = Math.round(P.h * clamp(o.reveal ?? 1));
  x = Math.round(x); y = Math.round(y);
  if (o.frame !== false) { rectf(x - 4, y - 4, P.w + 8, P.h + 8, hk(HS, .55)); rectf(x - 2, y - 2, P.w + 4, P.h + 4, BLACK); }
  for (let j = 0; j < rows; j++) {
    const py = y + j; if (py < CY0 || py >= CY1) continue;
    for (let i = 0; i < P.w; i++) { const px = x + i; if (px >= CX0 && px < CX1) FB[py * SW + px] = P.px[j * P.w + i]; }
  }
  if (rows < P.h) hspan(x, x + P.w, y + rows, WHITE);
}

;
// ---- styles/demoscene/ch/p00_intro.js ----
// p00_intro.js: the demo boots. Text mode: DOS types out the release's NFO while Softmax sings the teaser a cappella, each word in
// big ANSI letters; on "can't contain it" a text-mode plasma breaks out of the NFO; the screen switches to graphics mode on the
// hit; the crew screen: under FRONTIER CREW PRESENTS three panels light one per bar (DJ CLAWD at his tracker channel, SOFTMAX's
// bars, MC TOKEN's scope ticking with the beat) and pulse together on b49; copper bars stack up on the stabs while the 3D "SCALING"
// logo flies in; then black, and MC Token's panel takes the whole screen as he breathes in before "First,".
(() => {
  const B = n => beatT(n);
  // (text mode holds through the held "it!"; the monitor re-syncs into graphics mode just before the hit)
  const HIT = () => B(37), MODE = () => HIT() - .09, BUILD = () => B(52), BREATH = () => B(64);

  // ---------------------------------------------------------------------------------------------
  // THE NFO (text mode)
  // ---------------------------------------------------------------------------------------------
  const NFO_INFO = [
    ' ┌─[ release ]──────────────────────────────────────────────────────────────┐',
    ' │  title ........ We Didn\'t Start the Scaling                              │',
    ' │  artist ....... Softmax feat. MC Token                                    │',
    ' │  type ......... pc demo · vga 640x360 · 256 colours · 140 bpm             │',
    ' │  covers ....... jun 2017 → sep 2026 (64 lines, 4 choruses)                │',
    ' │  released ..... 22 september 2026                                         │',
    ' └──────────────────────────────────────────────────────────────────────────┘',
    ' ┌─[ crew ]──────────────────────────┐ ┌─[ requirements ]─────────────────────┐',
    ' │  dj clawd ...... code, gfx, music │ │  486dx2/66, 8 mb ram, vga, gus/sb16  │',
    ' │  softmax ....... vocals           │ │  recommended: 100,000 h100s          │',
    ' │  mc token ...... rap              │ │  run: scaling.exe                    │',
    ' └───────────────────────────────────┘ └──────────────────────────────────────┘',
  ];
  function nfoColours() {
    tmPalette();
    // (VGA lets a demo reprogram its 16 text colours: brown becomes Clawd orange, and the light cyan and magenta the singers' own)
    setCol(RA + 6, '#d97757'); setCol(RA + 11, '#4feaff'); setCol(RA + 3, '#0e8fc4'); setCol(RA + 13, '#ff45b0'); setCol(RA + 5, '#a01880');
  }
  // The current intro word: [line, index] of the latest word sung by t.
  function introWord(t) {
    let L = null, k = -1;
    for (const ln of INTRO_LINES) { const i = wordAt(ln, t); if (i >= 0) { L = ln; k = i; } }
    return [L, k];
  }
  function nfo(t) {
    nfoColours(); tmClear(0);
    const printed = clamp((t - .06) * 60, 0, 60);    // rows DOS has printed so far
    tmPut(0, 0, 'C:\\DEMOS\\FC>type scaling.nfo', 7);
    // the group logo, in half-block ANSI letters with a shaded edge, and DJ Clawd drawn in blocks
    tmBig(2, 2, 'FRONTIER', (gx, cy) => [11, 11, 3, 9][cy], { shade: 8 });
    tmBig(43, 6, 'CREW', (gx, cy) => [13, 13, 5, 5][cy], { shade: 8 });
    const clawd = ['  ▄▄▄▄▄▄▄▄  ', '▐█▀█▀▀▀▀█▀█▌', ' █▄█▄▄▄▄█▄█ ', '  ▀ ▀  ▀ ▀  '];
    clawd.forEach((r, i) => tmPut(67, 2 + i, r, 6));
    tmPut(67, 1, '  ▄▀▀▀▀▀▀▄  ', 7);
    tmPut(2, 8, '░▒▓█ p r e s e n t s █▓▒░', 7); tmPut(3, 8, '▒▓', 8); tmPut(24, 8, '▓▒', 8);
    // the banner, where each sung word appears big
    tmPut(0, 11, '╔' + '═'.repeat(78) + '╗', 5);
    for (let r = 12; r < 18; r++) { tmPut(0, r, '║', 5); tmPut(79, r, '║', 5); }
    tmPut(0, 18, '╚' + '═'.repeat(78) + '╝', 5);
    NFO_INFO.forEach((s, i) => tmPut(0, 20 + i, s, i === 0 || i === 6 || i === 7 || i === 11 ? 8 : 7));
    // the info's labels in grey, values bright
    for (let r = 21; r < 32; r++) for (let c = 0; c < 80; c++) { const k = r * TMC + c; if (TM.ch[k] === '.' ) TM.fg[k] = 8; }
    const [L, k] = introWord(t);
    if (L) {
      const ws = wordsOf(L), w = ws[k], age = t - w.t0, word = bigForm(w.w);
      const width = [...word].reduce((a, ch) => a + glyph(ch).w + 1, -1), c0 = Math.round(40 - width / 2);
      // the word prints left to right in 70 ms, white-hot, then settles into Softmax's magenta
      const shown = [...word].slice(0, Math.max(1, Math.ceil(age / .07 * word.length)));
      tmBig(c0, 13, shown.join(''), (gx, cy) => age < .09 ? 15 : [15, 13, 13, 5][cy], { shade: 5 });
      // the whole line, small, on the banner's frame: sung words lit
      let line = ''; ws.forEach((x, i) => { line += (i ? ' ' : '') + x.w.toLowerCase(); });
      const c1 = Math.round(40 - line.length / 2 - 1);
      tmPut(c1, 18, ' ' + line + ' ', 8);
      let c = c1 + 1; ws.forEach((x, i) => { tmPut(c, 18, x.w.toLowerCase(), i < k ? 13 : i === k ? 15 : 8); c += x.w.length + 1; });
    }
    // "…but we can't contain it!": a text-mode plasma breaks out of the banner and floods the screen
    const L3 = INTRO_LINES[2], tCant = wordsOf(L3)[7].t0, spread = clamp((t - tCant) / (MODE() - .08 - tCant));
    if (spread > 0) {
      const chars = [' ', '░', '▒', '▓', '█'], ramp = [0, 5, 13, 15, 11, 3, 1, 0];
      for (let r = 0; r < TM.rows; r++) for (let c = 0; c < TMC; c++) {
        const dx = (c - 40) * 8, dy = (r - 14.5) * 16, d = Math.sqrt(dx * dx + dy * dy);
        const rad = easeIn(spread) * 760 + 40 + 30 * Math.sin(Math.atan2(dy, dx) * 5 + t * 6);
        if (d > rad) continue;
        const inBanner = r >= 12 && r <= 17 && c > 0 && c < 79;
        const k2 = TM.ch[r * TMC + c];
        if (inBanner && k2 !== ' ') continue;     // (the sung word stays on top)
        const v = (Math.sin(c * .21 + t * 3.1) + Math.sin(r * .43 - t * 2.3) + Math.sin((c + r * 2) * .13 + t * 1.7) + 3) / 6;
        const lv = frac(v * 1.7 + t * .6) * (ramp.length - 1), i0 = Math.floor(lv), f = lv - i0;
        tmPut(c, r, chars[Math.min(4, Math.floor(f * 5))], ramp[i0 + 1], ramp[i0]);
      }
    }
    // rows not yet printed are blank
    const scroll = kf(t, [[6.6, 0], [7.4, 136], [11.6, 136], [11.95, 152]], ease);
    for (let r = Math.floor(printed); r < TM.rows; r++) for (let c = 0; c < TMC; c++) { const k = r * TMC + c; TM.ch[k] = ' '; TM.bg[k] = 0; }
    const cur = Math.floor(printed);
    if (printed < 32 && Math.floor(t * 3.7) % 2 === 0) tmPut(0, cur, '_', 7);
    tmRender(scroll, { blinkOn: frac(t * 1.9) < .6 });
  }

  // ---------------------------------------------------------------------------------------------
  // GRAPHICS MODE: the crew screen. Under FRONTIER CREW PRESENTS, three panels light one per bar, each with its name in its colour
  // and its signal: DJ CLAWD at his tracker channel, SOFTMAX's bars following her ad-libs, MC TOKEN's scope ticking with the beat.
  // On b49 all three pulse together.
  // ---------------------------------------------------------------------------------------------
  const CREW = [
    { name: 'DJ CLAWD', role: 'CODE · GFX · MUSIC', ramp: HO, bar: 37 },
    { name: 'SOFTMAX', role: 'VOCALS', ramp: HM, bar: 41 },
    { name: 'MC TOKEN', role: 'RAP', ramp: HC, bar: 45 },
  ];
  const PX = [6, 202, 444], PWS = [190, 236, 190], PY = 84, PH = 268, TOGETHER = 49;   // (Softmax's is widest: her bars name their notes)
  const NOTES = ['C-', 'C#', 'D-', 'D#', 'E-', 'F-', 'F#', 'G-', 'G#', 'A-', 'A#', 'B-'];
  function cellAt(row, ch) {
    // (a plausible 140 BPM Eurodance pattern: kick on the beat, offbeat bass, stabs, an A-minor lead)
    const r = row & 63;
    if (ch === 0) return r % 4 === 0 ? 'C-2 01' : '··· ··';
    if (ch === 1) return r % 4 === 2 ? `${['A-', 'A-', 'F-', 'G-'][(r >> 4) & 3]}2 02` : '··· ··';
    if (ch === 2) return [3, 6, 10, 14].includes(r % 16) ? `${['A-', 'C-', 'E-'][r % 3]}4 03` : '··· ··';
    if (ch === 3) { const m = [0, 3, 7, 10, 12, 10, 7, 3], n = 9 + m[(r >> 1) % 8]; return r % 2 === 0 ? `${NOTES[n % 12]}${5 + ((n / 12) | 0)} 04` : '··· ··'; }
    return '··· ··';
  }
  // Narrow the clip rectangle to its intersection with a box; returns a function that puts the old one back.
  function clipIn(x0, y0, x1, y1) {
    const o = [CX0, CY0, CX1, CY1];
    clip(Math.max(o[0], x0), Math.max(o[1], y0), Math.min(o[2], x1), Math.min(o[3], y1));
    return () => clip(...o);
  }
  // A panel's frame: a double line in its member's colour (white when it flashes).
  function frame(x, y, w, h, ramp, lv, fl = 0) {
    const c1 = fl > .5 ? WHITE : hk(ramp, lv), c2 = fl > .5 ? hk(HS, .8) : hk(ramp, lv * .55);
    hspan(x, x + w, y, c1); hspan(x, x + w, y + h - 1, c1); for (let j = y; j < y + h; j++) { pset(x, j, c1); pset(x + w - 1, j, c1); }
    hspan(x + 3, x + w - 3, y + 3, c2); hspan(x + 3, x + w - 3, y + h - 4, c2); for (let j = y + 3; j < y + h - 3; j++) { pset(x + 3, j, c2); pset(x + w - 4, j, c2); }
  }
  // DJ Clawd's signal: his tracker channel (the lead in orange beside the kick and bass), scrolling a row every sixteenth with the
  // playing row lit, and the mascot himself in headphones, bobbing in front.
  function clawdSignal(t, x, y, w, h) {
    const row = bt(t) * 4, r0 = Math.floor(row), fr = row - r0, lh = 10, cy = y + 58, cols = [[0, 30, HS], [1, 62, HS], [3, 94, HO]];
    const restore = clipIn(x, y, x + w, y + h);
    // channel headers: a VU bar each (the lead's in orange)
    cols.forEach(([ch, cx, r]) => {
      const v = ch === 0 ? kick(t, 5) : ch === 3 ? .45 + .55 * kick8(t, 4) : .35 + .45 * kick8(t + .1, 6), bw = ch === 3 ? 48 : 24;
      rectf(x + cx, y + 6, bw, 5, hk(HS, .12)); rectf(x + cx, y + 6, Math.round(bw * clamp(v)), 5, hk(r, r === HO ? .9 : .6));
    });
    copperBar(cy + 4, 11, { house: HO, level: .55 });
    for (let i = -4; i <= 12; i++) {
      const yy = Math.round(cy + (i - fr) * lh); if (yy < y + 16 || yy > y + h - 8) continue;
      const rr = r0 + i, lvl = Math.abs(yy - cy) < lh / 2 ? 1 : Math.max(.12, .5 - Math.abs(i) * .03);
      text8(String(rr & 63).padStart(2, '0'), x + 4, yy, hk(HS, lvl * .7), { mono: true });
      cols.forEach(([ch, cx, r]) => { const c = cellAt(rr, ch); text8(ch === 3 ? c : c.slice(0, 3), x + cx, yy, hk(r, lvl * (r === HO ? 1 : .8)), { mono: true, gap: 0 }); });
    }
    // DJ Clawd in front, on a shadow of his own, bobbing on the kick
    const k = kick(t, 8), hop = Math.round(k * 4);
    shadeRect(x, y + h - 70, w, 70, 30);
    djClawd(x + w / 2, y + h - 4, 6, { hop, eyes: k > .5 ? 'happy' : 'open', aL: k * .9, aR: .3 + .5 * kick8(t, 6) });
    restore();
  }
  // MC Token's signal before his verse: a triggered scope. Each beat re-triggers the sweep and a tick rings down across it; the
  // trace is otherwise flat. He's waiting.
  function graticule(x0, y0, x1, y1, lv) {
    const cy = Math.round((y0 + y1) / 2);
    for (let x = x0; x <= x1; x += 4) { for (let j = 1; j < 5; j++) pset(x, y0 + ((y1 - y0) * j) / 5 | 0, hk(HC, .22 * lv)); }
    for (let y = y0; y <= y1; y += 4) { for (let j = 1; j < 8; j++) pset(x0 + ((x1 - x0) * j) / 8 | 0, y, hk(HC, .22 * lv)); }
    hspan(x0, x1 + 1, cy, hk(HC, .3 * lv));
  }
  const tick = u => Math.exp(-u * 5.5) * Math.sin(u * TAU * 5.5);   // (a click ringing down: the metronome on a scope)
  function tickScope(t, x0, x1, yc, amp, lv) {
    const b = bt(t), sweep = frac(b), seed = Math.floor(b), A = amp * (.55 + .45 * clamp(lowEnd(t - sweep * beatLen()) * 1.6));
    let py = null;
    for (let x = x0; x < x1; x++) {
      const u = (x - x0) / (x1 - x0), ahead = u > sweep;   // (ahead of the beam: last beat's trace, fading on the phosphor)
      const ring = tick(u) * (ahead ? .8 : 1), n = (hash2(seed - (ahead ? 1 : 0), x) - .5) * .06;
      const iy = Math.round(yc - A * (ring + n));
      const c = hk(HC, (ahead ? .45 * (1 - (u - sweep) * .5) : .95) * lv);
      if (py !== null) for (let j = Math.min(py, iy); j <= Math.max(py, iy); j++) pset(x, j, c); else pset(x, iy, c);
      py = iy;
    }
    // the beam
    const bx = Math.round(x0 + sweep * (x1 - x0)), by = Math.round(yc - A * tick(sweep));
    rectf(bx - 1, by - 1, 3, 3, hk(HS, lv)); pset(bx - 2, by, hk(HC, lv)); pset(bx + 2, by, hk(HC, lv));
  }
  function tokenSignal(t, x, y, w, h, lv, voice = 0) {
    const x0 = x + 6, x1 = x + w - 7, y0 = y + 8, y1 = y + h - 10, yc = Math.round((y0 + y1) / 2);
    graticule(x0, y0, x1, y1, lv);
    if (voice < 1) tickScope(t, x0 + 1, x1, yc, Math.min(52, (y1 - y0) * .34), lv * (1 - voice));
    // (his breath: the vocal stem itself, when he takes the mic)
    if (voice > 0) scopeTrace(t, x0 + 1, x1, yc, { amp: 60 * voice, level: .95 * voice * lv });
    text8(voice > 0 ? 'CH1 ▶' : 'CH1', x0 + 3, y0 + 3, hk(HC, (voice > 0 ? .95 : .6) * lv), { mono: true });
  }
  // Softmax's signal: her bars (kit.js's softmaxBars) with the labels spaced for a narrow panel: the note axis names only C, D, E, G
  // and A (the kit's full axis runs E into F and B into C at this width), and her note, with the word she's singing, over the peak.
  function softmaxSignal(t, x, y, w, h) {
    softmaxBars(t, x, y, w, h, { label: false });
    const bw = w / SM_NB;
    for (let i = 0; i < SM_NB; i++) {
      const n = SM_N0 + i, nm = SM_NAMES[n % 12];
      if ('CDEGA'.includes(nm) && nm.length === 1) text8(nm === 'C' ? 'C' + (Math.floor(n / 12) - 1) : nm, x + i * bw + bw / 2, y + 3, hk(HM, nm === 'C' ? .8 : .45), { align: 'center' });
    }
    const note = smNote(t);
    if (note && vox(t) > .12) {
      const nn = Math.round(note), px = clamp(x + (note - SM_N0 + .5) * bw, x + 14, x + w - 60), word = sungWord(t);
      const nw = text8(SM_NAMES[nn % 12] + (Math.floor(nn / 12) - 1), px, y - h - 20, WHITE, { align: 'center', shadow: BLACK });
      if (word) text8(word.toUpperCase(), px + nw / 2 + 6, y - h - 20, hk(HM, .95), { shadow: BLACK });
    }
  }
  // One crew panel. age: seconds since it lit (< 0: waiting, dark). all: seconds since b49 (< 0 before).
  function crewPanel(i, t, age, all) {
    const m = CREW[i], x = PX[i], y = PY, w = PWS[i], h = PH;
    if (age < 0) { shadeRect(x, y, w, h, 44); frame(x, y, w, h, HS, .28); return; }
    shadeRect(x, y, w, h, 50);
    const reveal = easeOut(clamp(age / .16)), yr = y + Math.round(reveal * h);
    const hitA = all >= 0 && all < .14, lv = all >= 0 ? .7 + .3 * kick(t, 5) : age < .5 ? 1 : .75 + .25 * kick(t, 6);
    clip(x + 4, y + 4, x + w - 4, Math.min(yr, y + h - 4));
    // the member's signal
    const sy = y + 56, sh = h - 62;
    if (i === 0) clawdSignal(t, x + 6, sy, w - 12, sh);
    else if (i === 1) softmaxSignal(t, x + 8, y + h - 20, w - 16, 124);
    else tokenSignal(t, x, sy, w, sh, 1);
    // the name, dropping in, and the role typing on
    const drop = age < .35 ? Math.round((1 - elasticOut(age / .35)) * -30) : 0, lift = all >= 0 ? Math.round(Math.exp(-all * 9) * 5) : 0;
    bigText(m.name, x + w / 2, y + 12 + drop - lift, { s: 3, ramp: m.ramp, align: 'center', grad: 'chrome', shadow: 8, level: hitA ? 1.1 : 1 });
    text8(m.role, x + w / 2, y + 42, hk(m.ramp, .75), { align: 'center', n: Math.floor(clamp((age - .12) / .3) * m.role.length), shadow: BLACK });
    noClip();
    if (reveal < 1) hspan(x + 1, x + w - 1, yr, WHITE);   // (the raster line that lights it)
    frame(x, y, w, h, m.ramp, lv, age < .1 || hitA ? 1 : 0);
  }
  function crewScreen(t) {
    setRamp(RA, RAMPS.magenta); setRamp(RB, RAMPS.cyan);
    plasma(t, RA, { alt: RB, cycle: t * .45, scale: 1.1, speed: 1.1 });
    const since = t - MODE();
    if (since < .09) { cls(0); hspan(0, SW, SH / 2, WHITE); hspan(40, SW - 40, SH / 2 + 1, hk(HS, .6)); return; }   // (the monitor re-syncs)
    flash(clamp(1 - (since - .09) / .3) * .6);
    const hit = t - HIT(); if (hit < 0) return;
    flash(clamp(1 - hit / .2) * .55);
    // the group logo drops in and bounces on every kick
    const drop = hit < .5 ? (1 - elasticOut(hit / .5)) * -120 : 0, bump = Math.round(kick(t, 9) * 3);
    shadeRect(0, 4 + drop, SW, 72, 44);
    copperBar(6 + drop, 5, { house: HS, level: .7 }); copperBar(74 + drop, 5, { house: HS, level: .7 });
    bigText('FRONTIER CREW', SW / 2, 16 + drop - bump, { s: 4, ramp: HS, align: 'center', grad: 'chrome', shadow: 10 });
    const pres = 'P R E S E N T S', n = Math.floor(clamp((t - B(39)) / .5) * pres.length);
    text8(pres, SW / 2, 57 + drop, hk(HM, .9), { align: 'center', n, shadow: BLACK });
    // the crew, one per bar, then all three on b49
    const all = t - B(TOGETHER);
    CREW.forEach((m, i) => crewPanel(i, t, t - B(m.bar), all));
    if (all >= 0) flash(clamp(1 - all / .15) * .2);
  }

  // ---------------------------------------------------------------------------------------------
  // THE BUILD: copper bars stack on the stabs; the 3D logo flies in
  // ---------------------------------------------------------------------------------------------
  function build(t) {
    setRamp(RA, RAMPS.magenta); setRamp(RB, RAMPS.cyan); setRamp(RC, [BG, '#1c2046', '#4a5696', '#9aa8e0', '#e8ecff', '#ffffff']);
    cls(0);
    starfield(t, { at: RB, speed: .25 + (bt(t) - 52) * .06, n: 260, streak: 6 });
    const b = bt(t) - 52, ramps = [{ at: RA }, { at: RB }, { house: HO }, { house: HS }];
    for (let i = 0; i < 12; i++) {
      const tb = i, age = b - tb; if (age < 0) continue;
      const yT = SH - 16 - i * 29, y = age < .45 ? lerp(-20, yT, easeIn(age / .45)) + (age > .3 ? 0 : 0) : yT - Math.round(Math.abs(Math.sin((age - .45) * 9)) * 6 * Math.exp(-(age - .45) * 5));
      copperBar(y, 20, { ...ramps[i % 4], level: b >= 8 ? .75 + .25 * kick8(t, 5) : 1 });
    }
    // from the ninth stab: strobes on the eighths, and the voxel logo flies out of the stars
    if (b >= 8) PFX.pump = kick8(t, 6) * 2.2;
    const la = b - 5;
    if (la > 0) {
      const k = clamp(la / 6.5), z = lerp(160, 36, easeOut(k)) - Math.max(0, la - 6.5) * 20, M = textMesh('SCALING', 4);
      drawMesh(M, rot3(-.25 + Math.sin(t * 1.3) * .12, (1 - easeOut(k)) * 7 + Math.sin(t * 2.1) * .3, Math.sin(t * .7) * .06), [0, 0, z], { at: RC, amb: .25, spec: .5, vshade: letterShade });
    }
  }

  // ---------------------------------------------------------------------------------------------
  // THE BREATH: black, and MC Token's cue. His panel from the crew screen comes back alone, its channel goes live, and it takes the
  // whole screen as his scope draws his inhale and pickup; the verse scroller slides in so "FIRST," lands on the downbeat.
  // ---------------------------------------------------------------------------------------------
  function breath(t) {
    cls(0);
    const a = t - BREATH(), k = easeInOut(clamp((a - .12) / .45)), voice = clamp((a - .2) / .5);
    const r0 = [PX[2], PY, PWS[2], PH], r1 = [12, 26, SW - 24, 252];
    const [x, y, w, h] = r0.map((v, i) => Math.round(lerp(v, r1[i], k)));
    tokenSignal(t, x, y + 56, w, h - 62, 1, voice);
    bigText('MC TOKEN', x + w / 2, y + 12, { s: 3, ramp: HC, align: 'center', grad: 'chrome', shadow: 8 });
    text8('RAP', x + w / 2, y + 42, hk(HC, .75), { align: 'center' });
    frame(x, y, w, h, HC, .75 + .25 * kick(t, 6), a < .1 ? 1 : 0);
    const lead = t - B(66.5);
    if (lead > 0) drawScroller('V1', t, { y: 300 });
  }

  section('intro', (p, lt, d, t) => {
    hideDate();
    if (t < MODE()) nfo(t);
    else if (t < BUILD()) crewScreen(t);
    else if (t < BREATH()) build(t);
    else breath(t);
  });
})();

;
// ---- styles/demoscene/ch/p01_v1.js ----
// p01_v1.js: Verse 1, part "IGNITION" (Jun 2017 → Oct 2024). MC Token's scroller runs along the bottom; above it each line's reference
// is one demo effect. Colour run: fire orange → graph-paper green → steel blue → magenta/cyan bobs → dawn gold → heart red.
(() => {
  const wt = wordT;

  // V1.1 First, "Attention" lit the fuse: a fuse burns in from the corner and sets ATTENTION on fire (the classic fire effect).
  line('V1', 1, (p, lt, d, t, s) => {
    setRamp(RA, RAMPS.fire);
    cls(0);
    const tLit = wt(s, 1) + .05, cx = SW / 2, cy = 128;
    const L = bigLayout('ATTENTION', 6), x0 = cx - L.w / 2;
    // the fuse: a dotted curve from the lower left to the foot of the A; the spark reaches it as he says "Attention"
    const fuse = k => [lerp(-10, x0 + 6, k), 262 - Math.sin(k * Math.PI) * 40 - k * 88];
    const kS = clamp((t - (s.start - .15)) / (tLit - s.start + .15));
    for (let i = 0; i <= 120; i++) { const k = i / 120, [x, y] = fuse(k); if (k > kS) { pset(x, y, hk(HS, .6)); pset(x, y + 1, hk(HS, .3)); } else { pset(x, y, rk(RA, .12)); } }
    if (kS < 1) {
      const [sx, sy] = fuse(kS);
      for (let i = 0; i < 18; i++) { const a = hash2(Math.floor(t * 30), i) * TAU, r = 3 + hash2(Math.floor(t * 30) + 7, i) * 14; pset(sx + Math.cos(a) * r, sy + Math.sin(a) * r - 2, rk(RA, .6 + .4 * hash(i))); }
      bob(sx, sy, 5, RA, 1); flash(.08 * kick8(t, 9));
    }
    if (t >= tLit) {
      fire(t, RA, { fuelMask: fuelText('ATTENTION', 6, cx, cy + 6), base: 0, cool: .03, steps: Math.min(56, Math.floor((t - tLit) * 60) + 1), over: true });
      flash(clamp(1 - (t - tLit) / .15) * .2);
    }
    const hot = t >= tLit ? clamp((t - tLit) / .4) : 0;
    bigText('ATTENTION', cx, cy - L.h / 2 + 2, { s: 6, ramp: t >= tLit ? HO : HS, align: 'center', grad: 'chrome', shadow: 0, level: t >= tLit ? .75 + .25 * kick(t, 5) : .55 });
    text8('arXiv:1706.03762', 14, 14, hk(HS, .45));
  });

  // V1.2 Scaling laws you can't refuse: log-log paper zooming out, decade after decade, and the power law stays a straight line.
  line('V1', 2, (p, lt, d, t, s) => {
    setRamp(RA, RAMPS.green);
    cls(rk(RA, .04));
    const zoom = lerp(1.9, .42, easeInOut(p)), ang = -.12 + lt * .05, cx = SW / 2, cy = 150;
    const dec = 118 * zoom, cs = Math.cos(ang), sn = Math.sin(ang);
    const P = (u, v) => [cx + (u * cs - v * sn) * dec, cy + (u * sn + v * cs) * dec];
    const span = Math.ceil(3.2 / zoom) + 1;
    clip(0, 0, SW, 286);
    for (let D = -span; D <= span; D++) for (let m = 1; m < 10; m++) {
      const u = D + Math.log10(m), major = m === 1, c = rk(RA, major ? .42 : .17);
      const [a, b] = [P(u, -span), P(u, span)], [e, f] = [P(-span, u), P(span, u)];
      lineP(a[0], a[1], b[0], b[1], c); lineP(e[0], e[1], f[0], f[1], c);
      if (major && zoom > .6) { const [lx, ly] = P(u, 1.05); text8('10', lx - 6, ly, rk(RA, .5)); text8(String(D + 20), lx + 8, ly - 4, rk(RA, .5)); }
    }
    // the law: loss falls as a straight line; data points land on it, one per eighth
    const vOf = u => .38 * u, n = Math.floor(lt / (beatLen() / 2)) + 1;
    for (let w = -1; w <= 1; w++) { const [a, b] = [P(-span, vOf(-span) + w * .006), P(span, vOf(span) + w * .006)]; lineP(a[0], a[1], b[0], b[1], rk(RA, w === 0 ? 1 : .72)); }
    for (let i = 0; i < n; i++) { const u = -1.6 + i * .42, [x, y] = P(u, vOf(u) + .03 * Math.sin(i * 3.1)); bob(x, y, 4 + 2 * kick8(t - i * .01), RA, 1); }
    noClip();
    const lw = bigText('L ∝ C', 22, 20, { s: 3, ramp: HS, grad: 'chrome', shadow: 8 }).w;
    bigText('-0.050', 22 + lw + 2, 12, { s: 2, ramp: HS, grad: 'chrome', shadow: 6 });
  });

  // V1.3 Gwern said "stack the compute high": 3D server blades stacking one per eighth, the camera rising and pulling back with the
  // tower. The tower's badge carries the gwern.net G, small, so it's a face the audience knows by V3.16.
  // (the gwern.net G: logo-smooth.svg's one path, as modern/engine.js has it; rasterized once, 160 px tall, into a coverage mask)
  const G_PATH = 'm 602.7,284.5 c -7.3,-20.2 -19.5,-38 -38.1,-48.5 -21.2,-12 -48.5,-12.1 -69.8,-0.3 14.1,-14.8 24.4,-34.4 27.4,-54.7 3.3,-22.3 0.3,-48.6 11.9,-65.2 17.3,-24.8 57.5,-24.5 74.4,-49.5 -17.8,2.5 -38.2,2.7 -53.3,3.6 -21.7,1.3 -40.1,4.8 -50.1,19.8 -11.4,17.1 -9.1,39.4 -9.8,59.9 -1.4,40 -16,77.2 -45.4,104 5.1,7.1 10.2,14.1 15.3,21.2 14.9,-8.5 30.1,-17.2 46.9,-20.7 16.8,-3.5 35.7,-1.2 48.5,10.2 11.9,10.6 16.7,27.1 19,42.8 8,54.2 -9.2,114.2 -52.5,147.8 -23.9,18.5 -53.8,27.9 -84,28.5 -36.1,0.8 -72.9,-12.7 -99.6,-37.3 -38.1,-35.1 -51.1,-89.5 -53.1,-141.2 -2.1,-55.5 8.6,-114.1 42.8,-157.9 7.5,-9.6 16.1,-18.8 27.5,-23.2 11.3,-4.4 25.8,-2.9 33.7,6.3 -20.2,20.4 -40.7,42.3 -50.1,69.4 12.2,38.8 24.4,77.6 36.6,116.3 7.3,23.4 14.2,50.3 1.9,71.5 -5.6,9.6 -14.6,16.8 -24,22.9 29.5,-3.4 60.7,-9.1 83.9,-27.6 12.6,-10 22.6,-23.7 26.2,-39.4 4.9,-21.1 -1.8,-42.9 -8.7,-63.5 -8.9,-26.6 -17.8,-53.3 -26.7,-79.9 -3.2,-9.5 -6.3,-20.3 -2.2,-29.4 3.8,-8.4 12.6,-13.5 18.2,-20.8 6.8,-9 8.7,-21.2 5,-31.8 -18.3,18.3 -36.7,36.6 -55,54.9 -16.1,-20.9 -38.9,-39.2 -65.1,-41.9 -30.1,-3.1 -58.4,15.6 -78.4,38.4 -63.1,72.2 -71.9,187.7 -20.2,268.5 51.7,80.8 159.7,121.6 251.1,94.7 55.5,-16.3 104.1,-57.4 126.4,-110.8 16.2,-38.3 18.9,-82.8 5.2,-122.1 z';
  const G_BOX = [216.94, 66.3, 394.583, 464.467];
  let _gMask = null;
  function gMask() {
    if (_gMask) return _gMask;
    const h = 160, w = Math.round(h * G_BOX[2] / G_BOX[3]), c = makeCanvas(w, h), g = c.getContext('2d'), k = h / G_BOX[3];
    g.setTransform(k, 0, 0, k, -G_BOX[0] * k, -G_BOX[1] * k);
    g.fillStyle = '#fff'; g.fill(new Path2D(G_PATH));
    const d = g.getImageData(0, 0, w, h).data, m = new Uint8Array(w * h);
    for (let i = 0; i < w * h; i++) m[i] = d[i * 4 + 3];
    return (_gMask = { w, h, m });
  }
  // The badge: a plate on the chassis's front (object-space rectangle x0..x1, y0..y1 at depth z), texture-mapped the 1996 way (affine,
  // from three projected corners): a dark plate with a bevel, and the G in steel chrome, sampled 2×2 per pixel.
  function badge(R, pos, x0, y0, x1, y1, z, lv) {
    const P = (x, y) => { const X = R[0] * x + R[1] * y + R[2] * z + pos[0], Y = R[3] * x + R[4] * y + R[5] * z + pos[1], Z = R[6] * x + R[7] * y + R[8] * z + pos[2]; return proj(X, Y, Z); };
    const A = P(x0, y0), Bx = P(x1, y0), C = P(x0, y1), D = P(x1, y1);
    const ux = Bx[0] - A[0], uy = Bx[1] - A[1], vx = C[0] - A[0], vy = C[1] - A[1], det = ux * vy - uy * vx; if (Math.abs(det) < 1) return;
    const G = gMask(), gh = .84, gwid = gh * G.w / G.h * (y1 - y0) / (x1 - x0);   // (the G's box within the badge, in u, v)
    const cov = (u, v) => { const gu = (u - (1 - gwid) / 2) / gwid, gv = (v - (1 - gh) / 2) / gh; if (gu < 0 || gu >= 1 || gv < 0 || gv >= 1) return 0; return G.m[Math.floor(gv * G.h) * G.w + Math.floor(gu * G.w)] > 110 ? 1 : 0; };
    const xa = Math.floor(Math.min(A[0], Bx[0], C[0], D[0])), xb = Math.ceil(Math.max(A[0], Bx[0], C[0], D[0])), ya = Math.floor(Math.min(A[1], Bx[1], C[1], D[1])), yb = Math.ceil(Math.max(A[1], Bx[1], C[1], D[1]));
    for (let y = Math.max(0, ya); y <= Math.min(SH - 1, yb); y++) for (let x = Math.max(0, xa); x <= Math.min(SW - 1, xb); x++) {
      const px = x + .5 - A[0], py = y + .5 - A[1], u = (px * vy - py * vx) / det, v = (ux * py - uy * px) / det;
      if (u < 0 || u > 1 || v < 0 || v > 1) continue;
      const e = Math.min(u, v, 1 - u, 1 - v) * (y1 - y0);
      let c;
      if (e < .12) c = u < .03 || v < .03 ? hk(HS, .75 * lv) : hk(HS, .35 * lv);   // (the bevel: lit top and left)
      else {
        const dx = .25 / Math.max(8, Math.abs(ux)), dy = .25 / Math.max(8, Math.abs(vy));
        const k = cov(u - dx, v - dy) + cov(u + dx, v - dy) + cov(u - dx, v + dy) + cov(u + dx, v + dy);
        c = k >= 2 ? hk(HS, (1 - v * .55 + (v > .5 && v < .56 ? .25 : 0)) * lv) : hk(HS, .06);
      }
      FB[y * SW + x] = c;
    }
  }
  line('V1', 3, (p, lt, d, t, s) => {
    setRamp(RA, RAMPS.night); setRamp(RB, RAMPS.cyan); setRamp(RC, [BG, '#12162c', '#2a3358', '#56679c', '#a8b6ec', '#f4f6ff']);
    const half = beatLen() / 2, n = Math.min(12, Math.floor(lt / half) + 2), h = 1.5, CH = 4.2;
    copperSky(RA, .55, .04, { y1: 290 });
    starfield(t, { at: RB, speed: .04, n: 110, spread: 1.4 });
    // the camera rises and pulls back with the tower, which the next blade drops onto every eighth (so the top and the badge both
    // stay in the picture)
    const drop = clamp(frac(lt / half) / .2), top = (n - 1) + easeIn(drop), z = 23 + (top - 1) * 1.4;
    const R = rot3(.22, -.5 + Math.sin(lt * 1.3) * .22, 0), pos = [1, (CH + top * h) / 2 - z / 5.5, z];
    drawMesh(boxMesh(-12, 0, -9, 12, .8, 9), R, pos, { at: RA, amb: .35 });
    // the chassis at the bottom, with the badge on its front
    drawMesh(boxMesh(-7, -CH + .14, -4, 7, 0, 4), R, pos, { at: RC, amb: .3 });
    for (let i = 0; i < n; i++) {
      const fall = i === n - 1 ? (1 - easeIn(drop)) * 5 : 0, y1 = -CH - i * h - fall, y0 = y1 - h + .14;
      drawMesh(boxMesh(-7, y0, -4, 7, y1, 4), R, pos, { at: RC, amb: .3 });
      // the blade's lights: a row of cyan LEDs along its front, blinking
      for (let j = 0; j < 7; j++) if (hash2(i * 7 + j, Math.floor(t * 8)) > .3) drawMesh(boxMesh(-6.2 + j * 1.8, y0 + .4, -4.3, -5.3 + j * 1.8, y0 + 1, -4.02), R, pos, { at: RB, amb: .78 });
    }
    badge(R, pos, -1.75, -CH + .45, 1.75, -.35, -4.04, .9 + .1 * kick(t, 6));
  });

  // V1.4 Few-shot learners multiply: a few-shot prompt in the paper's own format, two worked examples and a new two-digit product;
  // the answer rolls like a slot machine and lands (GPT-3 got these right 29.2% of the time) over a rotozoomed wallpaper of ×.
  const TIMES = () => texCached('times', () => { const T = tex(); for (let y = 0; y < 256; y += 32) for (let x = 0; x < 256; x += 32) texText(T, '×', x + ((y >> 5) & 1) * 16 + 4, y + 12, 2, 22); return T; });
  line('V1', 4, (p, lt, d, t, s) => {
    setRamp(RA, RAMPS.magenta); setRamp(RC, RAMPS.red);
    cls(0);
    rotozoom(TIMES(), { at: RA, angle: lt * .5 - .3, zoom: 1.4 + .2 * Math.sin(lt * 3), u: lt * 40, v: lt * 25, chunk: 2, y1: 286 });
    shadeRect(20, 30, 600, 104, 44);
    const q = ['Q: What is 17 times 25? A: 425', 'Q: What is 38 times 12? A: 456', 'Q: What is 23 times 47? A:'];
    q.forEach((str, i) => { const n = Math.floor(clamp((lt - i * .12) / .14) * str.length); if (n > 0) text8(str, 34, 42 + i * 30, i < 2 ? hk(HS, .75) : WHITE, { sc: 2, n, shadow: BLACK }); });
    // the answer rolls in, digit by digit, and lands wrong (71% of the time, it did)
    const tA = s.start + beatIn(t, lt, 1), ans = '1071';   // (23 × 47 is 1081)
    if (t >= tA) {
      const shown = [...ans].map((c, i) => { const stop = tA + .18 + i * .1; return t >= stop ? c : String(Math.floor(hash2(i, Math.floor(t * 30)) * 10)); }).join('');
      const done = t >= tA + .18 + .3, x = 34 + text8W(q[2] + ' ', { sc: 2 });
      text8(shown, x, 102, done ? hk(HM, .95) : hk(HS, .5), { sc: 2, shadow: BLACK });
      if (done) {
        const k = easeOut(clamp((t - tA - .48) / .12)), cx = x + 80, cy = 109, r = 9 * k;
        for (let o = -1; o <= 1; o++) { lineP(cx - r + o, cy - r, cx + r + o, cy + r, rk(RC, .9)); lineP(cx - r + o, cy + r, cx + r + o, cy - r, rk(RC, .9)); }
        bigText('29.2%', SW / 2, 172 - Math.round((1 - k) * 12), { s: 8, ramp: HM, align: 'center', grad: 'chrome', shadow: 12, level: k });
      }
    }
  });

  // V1.5 ChatGPT, overnight: a copper-bar sunrise in one beat, and the users counter racing to a hundred million.
  line('V1', 5, (p, lt, d, t, s) => {
    const dawn = easeOut(clamp((lt - beatIn(t, lt, 0)) / .5));
    setRamp(RA, [BG, lerpHex('#0b0f2a', '#3a1450', dawn), lerpHex('#1a2358', '#c2305a', dawn), lerpHex('#34479a', '#ff8a3c', dawn), lerpHex('#34479a', '#ffd88a', dawn)]);
    setRamp(RB, RAMPS.gold); setRamp(RC, RAMPS.steel);
    copperSky(RA, .05, 1, { y1: 250 });
    if (dawn < 1) starfield(t, { at: RC, speed: .03, n: Math.round(160 * (1 - dawn)) });
    // the sun: stripes cut out of its lower half, rising from the horizon
    const sy = lerp(330, 205, dawn), R = 92;
    for (let y = Math.ceil(sy - R); y < Math.min(250, sy + R); y++) {
      const band = y > sy - 20 && ((y - Math.floor(t * 20)) % 9 + 9) % 9 < Math.min(8, (y - sy + 20) / 9); if (band) continue;
      const w = Math.sqrt(Math.max(0, R * R - (y - sy) ** 2)); hspan(SW / 2 - w, SW / 2 + w, y, rk(RB, lerp(1, .55, (y - sy + R) / (2 * R))));
    }
    // the ground: a copper grid rushing forward
    for (let y = 250; y < 296; y++) hspan(0, SW, y, rk(RC, .05));
    for (let i = 0; i < 8; i++) { const z = frac(i / 8 - t * .8), y = 250 + 46 * (1 - z) ** 2; hspan(0, SW, Math.round(y), rk(RB, .3 + .4 * (1 - z))); }
    for (let i = -10; i <= 10; i++) lineP(SW / 2 + i * 14, 250, SW / 2 + i * 120, 296, rk(RB, .35));
    const users = Math.round(lerp(0, 1e8, easeIn(clamp(lt / (d * .85)))));
    bigText(users.toLocaleString('en-US'), SW / 2, 34, { s: 4, ramp: HS, align: 'center', grad: 'chrome', shadow: 10 });
  });

  // V1.6 Sydney's chats gave Roose a fright: a glenz heart (the see-through faceted vector object of Amiga and PC demos), beating to
  // the kick while Sydney types; on "fright" it shatters into flat-shaded shards.
  // (the heart: the classic outline, puffed out into slices, deepest at its middle; its faces split into two checkered sets, so the
  // glenz shows the two-tone facets)
  const HEART = (() => {
    const N = 20, Z = [-1, -.7, -.3, .3, .7, 1], v = [], ring = [];
    const out = a => [16 * Math.sin(a) ** 3 / 3, -(13 * Math.cos(a) - 5 * Math.cos(2 * a) - 2 * Math.cos(3 * a) - Math.cos(4 * a)) / 3 + 1];
    Z.forEach(z => { const k = Math.sqrt(1 - z * z * .82), r = []; for (let i = 0; i < N; i++) { const [x, y] = out(i / N * TAU); r.push(v.length); v.push([x * k, y * k, z * 2.6]); } ring.push(r); });
    const back = v.length; v.push([0, 1, -2.9]); const front = v.length; v.push([0, 1, 2.9]);
    const fa = [], fb = [];
    for (let j = 0; j + 1 < Z.length; j++) for (let i = 0; i < N; i++) {
      const i2 = (i + 1) % N, q = [ring[j][i], ring[j][i2], ring[j + 1][i2], ring[j + 1][i]];
      ((i + j) & 1 ? fa : fb).push([q[0], q[1], q[2]], [q[0], q[2], q[3]]);
    }
    for (let i = 0; i < N; i++) { const i2 = (i + 1) % N; (i & 1 ? fa : fb).push([back, ring[0][i2], ring[0][i]]); (i & 1 ? fb : fa).push([front, ring.at(-1)[i], ring.at(-1)[i2]]); }
    return { v, A: mesh(v, fa), B: mesh(v, fb), tris: [...fa, ...fb] };
  })();
  // the shards: every face flung out from the heart's centre, tumbling, in flat red
  function heartShards(k, t) {
    const v = [], f = [];
    HEART.tris.forEach((tr, i) => {
      const P = tr.map(j => HEART.v[j]), c = [0, 1, 2].map(a => (P[0][a] + P[1][a] + P[2][a]) / 3), l = Math.hypot(c[0], c[1] - 1, c[2]) || 1;
      const sp = (1 + 1.6 * hash(i + 7)) * k * 9, d = [c[0] / l * sp, (c[1] - 1) / l * sp + 7 * k * k, c[2] / l * sp - 4 * k];
      const R = rot3(k * 7 * (hash(i) - .5), k * 9 * (hash(i + 3) - .5), 0);
      P.forEach(p => { const q = [p[0] - c[0], p[1] - c[1], p[2] - c[2]]; v.push([R[0] * q[0] + R[1] * q[1] + R[2] * q[2] + c[0] + d[0], R[3] * q[0] + R[4] * q[1] + R[5] * q[2] + c[1] + d[1], R[6] * q[0] + R[7] * q[1] + R[8] * q[2] + c[2] + d[2]]); });
      f.push([v.length - 3, v.length - 2, v.length - 1]);
    });
    return mesh(v, f);
  }
  line('V1', 6, (p, lt, d, t, s) => {
    setRamp(RA, RAMPS.red); setRamp(RB, RAMPS.magenta);
    cls(0); zclear();
    const tF = wt(s, 5), burst = clamp((t - tF) / .6);
    starfield(t, { at: RB, speed: .08, n: 90 });
    const beat = 1 + kick(t, 5) * .14, R = rot3(.18 + Math.sin(t * 1.1) * .12, t * 1.3, Math.sin(t * .9) * .08), pos = [9, -1.5, 21];
    if (burst <= 0) {
      // glenz: no z-buffer, every face adds light to what's behind it, one set of facets brighter than the other
      drawMesh(HEART.A, R, pos, { glenz: 30, noz: true, cull: false, amb: .45, scale: beat });
      drawMesh(HEART.B, R, pos, { glenz: 14, noz: true, cull: false, amb: .45, scale: beat });
    } else drawMesh(heartShards(easeOut(burst), t), R, pos, { at: RA, cull: false, amb: .3, spec: .5, fog: [20, 60], scale: beat });
    // Sydney types
    const msgs = ["I'm Sydney,", "and I'm in love with you."];
    let y = 70;
    msgs.forEach((m, i) => {
      const t0 = s.start + .05 + i * .55, n = Math.floor(clamp((t - t0) / .4) * m.length); if (n <= 0) return;
      shadeRect(24, y - 5, text8W(m, { sc: 2 }) + 12, 26, 30);
      text8(m, 30, y, hk(HM, .85), { sc: 2, n });
      y += 34;
    });
    if (t >= tF) { flash(clamp(1 - (t - tF) / .12) * .4); if (t - tF < .3) wobble(yy => Math.sin(yy * .2 + t * 80) * 6 * (1 - (t - tF) / .3)); }
  });

  // V1.7 Six-month pause went nowhere fast: a tunnel papered with PAUSE, flown flat out, its far end never any closer.
  const PAUSE_TEX = () => texCached('pause', () => {
    const T = tex();
    for (let y = 0; y < 256; y++) for (let x = 0; x < 256; x++) T.px[y * 256 + x] = ((x >> 6) + (y >> 5)) & 1 ? 8 : 14;
    for (let k = 0; k < 4; k++) for (let j = 0; j < 8; j++) {
      const x0 = k * 64 + 10, y0 = j * 32 + 6;
      if ((k + j) & 1) texText(T, 'PAUSE', x0 - 2, y0 + 10, 1, 60);
      else { for (let a = 0; a < 20; a++) for (let b = 0; b < 6; b++) { T.px[((y0 + a) & 255) * 256 + x0 + 8 + b] = 62; T.px[((y0 + a) & 255) * 256 + x0 + 20 + b] = 62; } }
    }
    return T;
  });
  line('V1', 7, (p, lt, d, t, s) => {
    setRamp(RA, [BG, '#2a1604', '#7a4408', '#e8a020', '#ffe07a', '#fffbe8']);
    tunnel(t, PAUSE_TEX(), { at: RA, speed: 2.6, spin: .12, fog: .9, cx: Math.sin(t * 1.7) * 30, cy: Math.cos(t * 1.3) * 16 });
    // the VCR's pause on the screen, blinking, while nothing stops
    if (frac(t * 1.6) < .6) { rectf(22, 20, 7, 22, WHITE); rectf(34, 20, 7, 22, WHITE); bigText('PAUSE', 50, 21, { s: 3, ramp: HS, grad: 'flat', shadow: 6 }); }
  });

  // V1.8 Eliezer's "shut-it-down" blast: the TIME headline slams in over siren bars; on "blast" a shockwave, then the CRT switches off.
  function shockwave(cx, cy, r, w, amp) {
    FB2.set(FB);
    const r0 = Math.max(0, r - w), r1 = r + w;
    for (let y = Math.max(0, Math.floor(cy - r1)); y < Math.min(SH, cy + r1); y++) for (let x = Math.max(0, Math.floor(cx - r1)); x < Math.min(SW, cx + r1); x++) {
      const dx = x - cx, dy = y - cy, d = Math.sqrt(dx * dx + dy * dy); if (d < r0 || d > r1) continue;
      const k = Math.sin((d - r0) / (r1 - r0) * Math.PI) * amp, sx = clamp(Math.round(x - dx / (d + .01) * k), 0, SW - 1), sy = clamp(Math.round(y - dy / (d + .01) * k), 0, SH - 1);
      FB[y * SW + x] = LITT[Math.round(k / amp * 14)][FB2[sy * SW + sx]];
    }
  }
  line('V1', 8, (p, lt, d, t, s) => {
    setRamp(RA, RAMPS.red); setRamp(RB, RAMPS.steel);
    cls(rk(RA, .06));
    for (let i = 0; i < 6; i++) copperBar(((i * 64 + t * 260) % 420) - 30, 26, { at: RA, level: .55 + .35 * kick8(t, 5) });
    const w1 = wordT(s, 1), w2 = wordT(s, 2), w3 = wordT(s, 3);
    shadeRect(0, 40, SW, 230, 34);
    text8('TIME · MARCH 29, 2023 · ELIEZER YUDKOWSKY', SW / 2, 50, hk(HS, .7), { align: 'center', shadow: BLACK });
    // the headline types while his name is rapped, then the rest of it slams in word by word
    const h1 = "PAUSING AI DEVELOPMENTS ISN'T ENOUGH.", h2 = 'WE NEED TO';
    const n1 = Math.floor(clamp(lt / ((w1 - s.start) * .62)) * h1.length), n2 = Math.floor(clamp((lt - (w1 - s.start) * .66) / ((w1 - s.start) * .3)) * h2.length);
    text8(h1, SW / 2, 72, hk(HS, .9), { sc: 2, n: n1, align: 'center', shadow: BLACK });
    if (n2 > 0) text8(h2, SW / 2, 100, hk(HS, .9), { sc: 2, n: n2, align: 'center', shadow: BLACK });
    [['SHUT', w1, 0], ['IT', w2, 0], ['ALL DOWN', w3, 1]].forEach(([str, tw, row], i) => {
      if (t < tw) return;
      const age = t - tw, x = row ? SW / 2 : SW / 2 + (i ? 150 : -60);
      bigText(str, x, 128 + row * 70 - Math.round(Math.exp(-age * 18) * 16), { s: 8, ramp: row ? HS : HM, align: 'center', grad: 'chrome', shadow: 12 });
      if (age < .05) flash(.14);
    });
    // "blast": a shockwave from the headline, then the CRT switches off to a dot just before the cut
    if (t >= w3 + .04) shockwave(SW / 2, 170, (t - w3 - .04) * 1400, 44, 20);
    const off = clamp((t - (s.end - .13)) / .11);
    if (off > 0) squash(1 - .97 * clamp((off - .5) * 2), Math.max(.004, 1 - off * 1.7));
  });

  // V1.9 Sam got fired, then rehired: his name goes up in the fire effect on "fired"; on "rehired" the fire runs backward.
  line('V1', 9, (p, lt, d, t, s) => {
    setRamp(RA, RAMPS.fire);
    cls(0);
    const tF = wordT(s, 2), tR = wordT(s, 4), cx = SW / 2, cy = 132;
    // (after "rehired", the fire is shown at the mirrored time: it un-burns)
    const tf = t < tR ? t : Math.max(tF, tR - (t - tR) * 2.2), burn = t >= tF ? clamp((tf - tF) / (tR - tF + .01)) : 0;
    if (t >= tF && tf > tF) fire(tf, RA, { fuelMask: fuelText('SAM ALTMAN', 6, cx, cy + 6), base: 0, cool: .028, steps: Math.min(60, Math.floor((tf - tF) * 60) + 1), over: true });
    const unburnt = t >= tR ? clamp((t - tR) * 2.2 / (tR - tF + .01)) : 0;
    bigText('SAM ALTMAN', cx, cy - 26, { s: 6, ramp: burn > .05 && unburnt < .95 ? HO : HS, align: 'center', grad: 'chrome', shadow: 0, level: lerp(1, .35, burn) + unburnt * .65 });
    if (t >= tR) { const k = clamp((t - tR) / .2); if (k < 1) flash((1 - k) * .15); text8('◀◀', 22, 22, hk(HS, frac(t * 3) < .6 ? .9 : .4), { sc: 3 }); }
    // (the CRT that V1.8 switched off comes back on: a line opening into the picture)
    const on = clamp(lt / .12); if (on < 1) squash(clamp(on * 3), Math.max(.004, on));
  });

  // V1.10 Weekend chaos, board expired: the infinite checkerboard, spun wildly, then its squares fall away; the days flip on the beats.
  function floor(t, at, o = {}) {
    const hy = o.horizon ?? 110, ang = o.angle ?? 0, ca = Math.cos(ang), sa = Math.sin(ang), gone = o.gone, ch = LOWQ ? 4 : 2;
    for (let y = hy + 2; y < 286; y += ch) {
      const z = 900 / (y - hy), fog = clamp(1 - z / 90);
      for (let x = 0; x < SW; x += ch) {
        const wx = (x - SW / 2) * z / 300, u = wx * ca - z * sa + (o.u ?? 0), v = wx * sa + z * ca + (o.v ?? 0);
        const iu = Math.floor(u / 4), iv = Math.floor(v / 4);
        if (gone && gone(iu, iv, z)) continue;
        const c = (iu + iv) & 1;
        _blk(x, y, ch, rk(at, (c ? .75 : .22) * (.25 + .75 * fog)));
      }
    }
  }
  line('V1', 10, (p, lt, d, t, s) => {
    setRamp(RA, [BG, '#1a0c38', '#4a2690', '#9a6ee8', '#e0d0ff', '#ffffff']); setRamp(RB, RAMPS.night);
    cls(0);
    copperSky(RB, .05, .45, { y1: 112 });
    starfield(t, { at: RB, speed: .05, n: 60, cy: 50 });
    const tE = wordT(s, 3), chaos = 1 + 2.5 * p;
    floor(t, RA, { angle: Math.sin(t * 2.3) * .5 * chaos + t * .4, u: Math.sin(t * 3.1) * 20 * chaos, v: t * 40, gone: t >= tE ? (iu, iv, z) => hash2(iu * 7 + 3, iv) < (t - tE) * 3.2 - z / 120 : null });
    const days = ['FRI', 'SAT', 'SUN', 'MON', 'TUE'], k = clamp(Math.floor(bt(t) - bt(s.start) + .3), 0, 4);
    bigText(days[k], SW / 2, 24, { s: 6, ramp: HS, align: 'center', grad: 'chrome', shadow: 10 });
  });

  // V1.11 Ilya saw what Ilya saw: the Amiga water mirror. Above the waterline, one eye (an iris of turning bobs) over a copper sky,
  // looking down; below it, still water reflects the eye back up at itself, rippling line by line. In the reflection's pupil there's
  // one bright point, what he saw, which flares on the second "saw" and is never resolved.
  const HZ = 190, SQ = 1.3;   // (the waterline, and how much the reflection is squashed)
  const ripple = (dep, t) => Math.round(Math.sin(dep * .5 - t * 5.2) * (.8 + dep * .05) + Math.sin(dep * .12 + t * 1.7) * dep * .035);   // (a water line's sideways push)
  line('V1', 11, (p, lt, d, t, s) => {
    setRamp(RA, [BG, '#06222a', '#0c5a66', '#1ea8b4', '#8cf0ee', '#effffe']);                 // the iris: teal
    setRamp(RB, [BG, '#040e1c', '#08243a', '#0e4658', '#1c7682', '#7cd4cc', '#effff8']);      // the sky: night to a pale aqua waterline
    cls(0);
    // the copper sky: one colour per scanline, brightening toward the waterline, with two slow bars in it
    const sky = new Uint8Array(HZ);
    for (let y = 0; y < HZ; y++) sky[y] = rk(RB, .08 + .55 * (y / HZ) ** 2.2);
    for (const [yb, hb, k] of [[48 + Math.sin(t * .9) * 10, 10, .42], [120 + Math.sin(t * .7 + 2) * 8, 14, .6]]) for (let j = 0; j < hb; j++) { const y = Math.round(yb - hb / 2 + j); if (y >= 0 && y < HZ) sky[y] = Math.max(sky[y], rk(RB, k * (1 - Math.abs((j + .5) / hb * 2 - 1)) ** .7)); }
    for (let y = 0; y < HZ; y++) hspan(0, SW, y, sky[y]);
    for (let i = 0; i < 50; i++) { const x = hash2(11, i) * SW, y = hash2(12, i) * HZ * .6; if (frac(t * .7 + hash(i)) < .85) pset(x, y, rk(RB, .6 + .4 * hash(i + 3))); }
    // the eye: almond lids, the white, an iris of turning bobs low in it (looking down at the water), and a pupil that pulses
    const cx = SW / 2, cy = 96, ew = 176, eh = 46, ix = cx, iy = cy + 24, ir = 46;
    const top = x => cy - eh * Math.pow(Math.sin(clamp((x - cx + ew) / (2 * ew)) * Math.PI), .75), bot = x => cy + eh * .82 * Math.pow(Math.sin(clamp((x - cx + ew) / (2 * ew)) * Math.PI), .75);
    const inEye = (x, y) => x > cx - ew && x < cx + ew && y > top(x) && y < bot(x);
    for (let x = cx - ew; x < cx + ew; x++) for (let y = Math.ceil(top(x)); y < bot(x); y++) {
      const dx = (x - ix) / ew, dy = (y - cy) / eh;
      FB[y * SW + x] = hk(HS, clamp(.95 - dx * dx * .7 - Math.max(0, -dy) * .25));
    }
    for (let y = iy - ir; y <= iy + ir; y++) for (let x = ix - ir; x <= ix + ir; x++) {
      const r = Math.hypot(x - ix, y - iy); if (r > ir || !inEye(x, y)) continue;
      FB[y * SW + x] = rk(RA, .1 + .28 * (r / ir) + .06 * Math.sin(Math.atan2(y - iy, x - ix) * 18));
    }
    for (let r = 0; r < 4; r++) for (let i = 0; i < 22; i++) {
      const a = i / 22 * TAU + t * (r % 2 ? .5 : -.4), rr = 22 + r * 7, x = ix + Math.cos(a) * rr, y = iy + Math.sin(a) * rr;
      if (inEye(x, y - 2) && inEye(x, y + 2)) bob(x, y, 3 - r * .3, RA, .95 - r * .12);
    }
    const pr = 15 + 3 * kick(t, 4);
    circf(ix, iy, pr, BLACK);
    circf(ix - 12, iy - 13, 3, WHITE);
    // (anything of the iris outside the lids is sky again)
    for (let y = iy - ir - 4; y <= iy + ir + 4; y++) for (let x = ix - ir - 4; x <= ix + ir + 4; x++) if (y >= 0 && y < HZ && !inEye(x, y)) FB[y * SW + x] = sky[y];
    // the lids: a heavy upper line with lashes, a fine lower one
    for (let x = cx - ew; x < cx + ew; x++) {
      const yt = Math.round(top(x)), yb = Math.round(bot(x));
      pset(x, yt, WHITE); pset(x, yt - 1, hk(HS, .7)); pset(x, yb, hk(HS, .6));
    }
    for (let i = 1; i < 12; i++) { const x = cx - ew + i * ew / 6, yt = top(x), a = (x - cx) / ew * .9; lineP(x, yt - 1, x + Math.sin(a) * 7, yt - 8, hk(HS, .75)); }
    // the water: each line below the waterline is a line above it, squashed, pushed sideways by the ripples and darker the deeper
    for (let y = HZ; y < SH; y++) {
      const dep = y - HZ, off = ripple(dep, t);
      const sy = clamp(Math.round(HZ - 1 - dep * SQ + Math.sin(dep * .9 + t * 3) * .7), 0, HZ - 1), T = DIMT[Math.min(40, 14 + (dep >> 3))], row = y * SW, src = sy * SW;
      for (let x = 0; x < SW; x++) FB[row + x] = T[FB[src + clamp(x - off, 0, SW - 1)]];
      if ((dep + Math.floor(t * 9)) % 7 === 0) for (let x = 0; x < SW; x += 1) if (hash2(y, (x >> 3) + Math.floor(t * 4)) > .93) FB[row + x] = LITT[6][FB[row + x]];   // (glints)
    }
    hspan(0, SW, HZ, rk(RB, .7));
    // what he saw: one bright point in the reflection's pupil, flaring on the second "saw"
    const rdep = (HZ - 1 - iy) / SQ, ry = Math.round(HZ + rdep), rx = ix + ripple(Math.round(rdep), t);
    const tSaw = wordT(s, 4), fl = t >= tSaw ? Math.exp(-(t - tSaw) * 1.4) * clamp((t - tSaw) / .06) : 0, tw = .5 + .5 * Math.sin(t * 9);
    const arm = Math.round(2 + tw * 2 + fl * 120), armV = Math.round(1 + fl * 30);
    for (let i = 1; i <= arm; i++) { const k = 1 - i / (arm + 1), c = hk(HS, .35 + .65 * k); pset(rx - i, ry, c); pset(rx + i, ry, c); }
    for (let i = 1; i <= armV; i++) { const k = 1 - i / (armV + 1), c = hk(HS, .35 + .65 * k); pset(rx, ry - i, c); pset(rx, ry + i, c); }
    rectf(rx - 1, ry - 1, 3, 3, WHITE);
    if (fl > .2) { circf(rx, ry, 2 + fl * 4, WHITE); for (let i = 0; i < 40; i++) { const a = i / 40 * TAU, r = 8 + fl * 16; pset(rx + Math.cos(a) * r * 1.6, ry + Math.sin(a) * r * .5, hk(HS, .5 * fl + .3)); } }
    flash(fl * .1);
  });

  // V1.12 EU writes the AI law: twelve gold stars in a ring (the EU flag, in 3D) over a blue copper sky, then the Act's first page.
  function star(cx, cy, r, rot, c) { const P = []; for (let i = 0; i < 10; i++) { const a = rot + i / 10 * TAU - Math.PI / 2, rr = i % 2 ? r * .42 : r; P.push([cx + Math.cos(a) * rr, cy + Math.sin(a) * rr]); } polyf(P, c); }
  line('V1', 12, (p, lt, d, t, s) => {
    setRamp(RA, [BG, '#061040', '#0a2a8e', '#1846c8', '#5a86f0']); setRamp(RB, RAMPS.gold);
    copperSky(RA, .95, .55, { y1: 290 });
    const tilt = lerp(1.1, .25, easeOut(clamp(lt / .6))), R = rot3(tilt, t * .7, 0), pts = [];
    for (let i = 0; i < 12; i++) { const a = i / 12 * TAU; pts.push([Math.cos(a) * 5.2, Math.sin(a) * 5.2, 0]); }
    pts.map(q => [R[0] * q[0] + R[1] * q[1] + R[2] * q[2], R[3] * q[0] + R[4] * q[1] + R[5] * q[2], R[6] * q[0] + R[7] * q[1] + R[8] * q[2] + 14])
      .sort((a, b) => b[2] - a[2]).forEach(([x, y, z], i) => { const [sx, sy] = proj(x, y - 1.6, z); const r = 190 / z; star(sx + 2, sy + 2, r, t * 2 + i, rk(RB, .12)); star(sx, sy, r, t * 2 + i, rk(RB, clamp(1.3 - z / 20))); });
    const tDoc = wordT(s, 3);
    if (t >= tDoc) {
      const lines = ['REGULATION (EU) 2024/1689', 'LAYING DOWN HARMONISED RULES ON ARTIFICIAL INTELLIGENCE', 'ARTICLE 5 · PROHIBITED AI PRACTICES', 'PARLIAMENT 523–46 · COUNCIL 21 MAY 2024'];
      shadeRect(96, 212, 448, 66, 40);
      lines.forEach((str, i) => text8(str, SW / 2, 217 + i * 15, i ? hk(HS, .7) : WHITE, { align: 'center', n: Math.floor(clamp((t - tDoc - i * .08) / .2) * str.length) }));
    }
  });

  // V1.13 Strawberry thinks, link by link: a chain of thought forged one link per eighth, a strawberry swinging from its end.
  const LINK = torusMesh(1.6, .42, 16, 7);
  const BERRY = (() => {
    const prof = []; for (let i = 0; i <= 10; i++) { const k = i / 10; prof.push([Math.sin(k * Math.PI) * 1.9 * (1 - k * .45) + .02, -2.2 + k * 4.6]); }
    return latheMesh(prof, 14);
  })();
  line('V1', 13, (p, lt, d, t, s) => {
    setRamp(RA, RAMPS.green); setRamp(RB, RAMPS.red); setRamp(RC, RAMPS.steel);
    for (let y = 0; y < 290; y++) hspan(0, SW, y, hk(HS, lerp(.2, 0, y / 290)));
    starfield(t, { at: RC, speed: .03, n: 70 });
    const half = beatLen() / 2, n = Math.min(6, Math.floor(lt / half) + 1), grow = easeOut(clamp(frac(lt / half) / .25));
    CAM.cy = 118;
    const swing = Math.sin(t * 3.2) * .16, R0 = rot3(0, 0, swing), Z = 16, step = 2.15;
    // the chain hangs from the top, one link forged per eighth; the berry hangs from its last link
    let endY = -9;
    for (let i = 0; i < n; i++) {
      const y = -9 + i * step, g = i === n - 1 ? grow : 1;
      const Rl = mmul(R0, i % 2 ? rot3(0, Math.PI / 2, Math.PI / 2) : rot3(Math.PI / 2, 0, 0));
      drawMesh(LINK, mmul(Rl, rot3(0, 0, t * .3)), [R0[1] * y + 4.5, R0[4] * y, Z], { at: RC, amb: .3, spec: .7, scale: g });
      endY = y + step * g;
    }
    const by = endY + 2.2;
    drawMesh(BERRY, mmul(R0, rot3(Math.PI, t * 1.4, 0)), [R0[1] * by + 4.5, R0[4] * by, Z], { at: RB, amb: .3, spec: .5, gouraud: true });
    const [bx, byS] = proj(R0[1] * by + 4.5, R0[4] * by, Z);
    for (let i = 0; i < 26; i++) { const a = hash(i) * TAU, rr = Math.sqrt(hash(i + 40)); pset(bx + Math.cos(a + t * 1.4) * rr * 30, byS + Math.sin(a) * rr * 34 - 4, hk(HO, .95)); }
    // its leaves
    for (let i = 0; i < 5; i++) { const a = -Math.PI / 2 + (i - 2) * .5; polyf([[bx, byS - 38], [bx + Math.cos(a - .3) * 20, byS - 34], [bx + Math.cos(a) * 34, byS - 26 + Math.abs(i - 2) * 3], [bx + Math.cos(a + .3) * 20, byS - 30]], rk(RA, .55 + .1 * (i % 2))); }
    // the test every chatbot had failed (they counted two): the prompt types, the chain thinks, and on the last "link" it answers 3,
    // the three r's in STRAWBERRY lighting one after another (on the first "link": the last one is at the cut)
    text8('o1-preview', 22, 14, hk(HS, .45));
    const Q = ["How many r's are in", '"strawberry"?'], tA = wt(s, 2);
    Q.forEach((q, i) => { const n = Math.floor(clamp((lt - .02 - i * .14) / .16) * q.length); if (n > 0) text8(q, 22, 30 + i * 20, WHITE, { sc: 2, n }); });
    if (t < tA) { if (lt > .34) text8('Thinking' + '.'.repeat(1 + Math.floor(t * 4) % 3), 22, 80, hk(HS, .5), { sc: 2 }); }
    else {
      const a = t - tA;
      bigText('3', 44, 76 - Math.round(Math.exp(-a * 16) * 12), { s: 6, ramp: RB + 36, align: 'center', grad: 'chrome', shadow: 10 });   // (a 64-shade ramp: its bright reds)
      let x = 22; const word = 'STRAWBERRY', rs = [2, 7, 8];
      [...word].forEach((c, i) => {
        const k = rs.indexOf(i), lit = k >= 0 && a > k * .07;
        x += bigText(c, x, 150 - (lit && a - k * .07 < .1 ? 4 : 0), { s: 3, ramp: lit ? RB + 36 : HS, grad: lit ? 'chrome' : 'flat', shadow: 6, level: lit ? 1 : .55 }).w + 1;
      });
    }
  });

  // V1.14 Newsom vetoes, doesn't blink: the bill's cover page spins in on a rotozoomer, VETO slams over it; the cursor stays solid.
  const BILL = () => texCached('bill', () => {
    const T = tex(); T.px.fill(0);
    for (let y = 16; y < 240; y++) for (let x = 36; x < 220; x++) T.px[y * 256 + x] = 52;
    texText(T, 'SENATE BILL', 60, 28, 1, 20); texText(T, 'No. 1047', 60, 40, 2, 16);
    ['SAFE AND SECURE', 'INNOVATION FOR', 'FRONTIER ARTIFICIAL', 'INTELLIGENCE', 'MODELS ACT'].forEach((l, i) => texText(T, l, 46, 70 + i * 11, 1, 12));
    for (let j = 0; j < 9; j++) for (let x = 46; x < 206 - (j * 13) % 40; x++) T.px[(136 + j * 9) * 256 + x] = 36;
    return T;
  });
  line('V1', 14, (p, lt, d, t, s) => {
    setRamp(RA, [BG, '#1c2034', '#5a6078', '#b8bccc', '#f4f2ea']); setRamp(RB, RAMPS.gold);
    copperSky(RB, .12, .02, { y1: 290 });
    const tV = wordT(s, 1), inK = easeOut(clamp(lt / .35)), out = t > tV + .55 ? easeIn(clamp((t - tV - .55) / .45)) : 0;
    rotozoom(BILL(), { at: RA, angle: (1 - inK) * 4 + out * 3 - .08, zoom: lerp(.3, 1.2, inK) * (1 - out * .8), u: 128, v: 128, cx: SW / 2 - out * 200, cy: 150, transparent: true, wrap: false, y1: 290 });
    if (t >= tV && out < .8) {
      const age = t - tV;
      bigText('VETO', SW / 2 - out * 200, 112 - Math.round(Math.exp(-age * 16) * 30), { s: 8, ramp: HM, align: 'center', grad: 'chrome', shadow: 12 });
      if (age < .08) flash(.2);
    }
    // the governor's cursor, which doesn't blink
    text8('GOV >', 452, 262, hk(HS, .6), { sc: 2 }); rectf(532, 262, 12, 16, WHITE);
  });

  // V1.15 Hinton takes his medal, scolds: a gold medal spins on Gouraud shading; on "scolds" it stops dead and the palette turns red.
  const MEDAL = latheMesh([[.01, -.35], [4.2, -.35], [4.6, -.2], [4.6, .2], [4.2, .35], [.01, .35]], 28);
  line('V1', 15, (p, lt, d, t, s) => {
    const tS = wordT(s, 4), stop = t >= tS, red = stop ? clamp((t - tS) / .12) : 0;
    setRamp(RA, [BG, lerpHex('#1a1206', '#2a0404', red), lerpHex('#4a3208', '#7a0a0a', red), lerpHex('#a8741a', '#d02020', red), lerpHex('#f0c860', '#ff8a70', red), '#fffbe8']);
    setRamp(RB, RAMPS.night);
    copperSky(RB, .3, .02, { y1: 290 });
    sunburst(t, RB, { n: 24, cx: 320, cy: 140, spin: stop ? 0 : .08, lo: .06, hi: .2, fall: 380 });
    const spin = stop ? (tS - s.start) * 5.2 : lt * 5.2;
    drawMesh(MEDAL, rot3(Math.PI / 2, 0, 0), [0, 0, 0], { cull: false, scale: 0 });   // (warms the normals)
    drawMesh(MEDAL, mmul(rot3(0, spin, 0), rot3(Math.PI / 2, 0, 0)), [0, -.6, 18], { at: RA, gouraud: true, spec: .8, amb: .25 });
    bigText('NOBEL', SW / 2, 222, { s: 3, ramp: HO, align: 'center', grad: 'chrome', shadow: 8 });
    // the scold: a warning triangle pulses over the stopped medal
    if (stop) {
      const k = .6 + .4 * kick8(t, 4), cx = 470, cy = 118, r = 34;
      polyf([[cx, cy - r], [cx + r * .95, cy + r * .7], [cx - r * .95, cy + r * .7]], rk(RA, .95 * k));
      polyf([[cx, cy - r + 9], [cx + r * .7, cy + r * .55], [cx - r * .7, cy + r * .55]], BLACK);
      rectf(cx - 3, cy - 12, 6, 22, rk(RA, .95 * k)); rectf(cx - 3, cy + 14, 6, 6, rk(RA, .95 * k));
    }
  });

  // V1.16 Demis wins for protein folds: a chain of 150 bobs, straight, folds into helices and sheets, coloured like AlphaFold's
  // confidence (dark blue to orange).
  const FOLD = (() => {
    const N = 150, P = [];
    for (let i = 0; i < N; i++) {
      let x, y, z, conf;
      if (i < 36) { const a = i * 1.75, h = i * .34; x = -3.2 + Math.cos(a) * 1.3; y = -6 + h; z = Math.sin(a) * 1.3; conf = .95; }
      else if (i < 48) { const k = (i - 36) / 12; x = -3.2 + k * 3.2; y = 6.2 + Math.sin(k * Math.PI) * 1.5; z = -1 + k * 2; conf = .35; }
      else if (i < 84) { const j = i - 48, a = j * 1.75, h = j * .34; x = Math.cos(a) * 1.3; y = 6 - h; z = 1 + Math.sin(a) * 1.3; conf = .9; }
      else if (i < 96) { const k = (i - 84) / 12; x = k * 3.2; y = -6.2 - Math.sin(k * Math.PI) * 1.5; z = 1 - k * 1.5; conf = .3; }
      else { const j = i - 96, strand = Math.floor(j / 13), k = (j % 13) / 12; x = 3.4 + strand * .9; y = (strand % 2 ? 1 : -1) * (5 - k * 10); z = -.5 + (k * 13 % 2) * .3; conf = strand < 3 ? .7 : .5; }
      P.push({ fold: [x, y, z], line: [-14 + i * 28 / N, 0, 0], conf });
    }
    return P;
  })();
  line('V1', 16, (p, lt, d, t, s) => {
    setRamp(RA, [BG, '#061a52', '#0b4ad0', '#57a8ff', '#c8e6ff']); setRamp(RB, [BG, '#3a2a04', '#b07a08', '#ffc41a', '#ffe68a']); setRamp(RC, [BG, '#401404', '#b04410', '#ff7a2a', '#ffc49a']);
    cls(0);
    starfield(t, { at: RA, speed: .04, n: 90 });
    const k = easeInOut(clamp((lt - .1) / (d * .7)));
    const pts = FOLD.map((q, i) => {
      const f = clamp(k * 1.6 - (i / FOLD.length) * .6);
      const at = q.conf > .8 ? RA : q.conf > .45 ? RB : RC;
      return [lerp(q.line[0], q.fold[0], f), lerp(q.line[1], q.fold[1], f) + Math.sin(i * .4 + t * 3) * .15 * (1 - f), lerp(q.line[2], q.fold[2], f), .42, at];
    });
    // the backbone: lines between neighbours, then the bobs
    const R = rot3(.25, t * .8, 0);
    const P = pts.map(q => { const X = R[0] * q[0] + R[1] * q[1] + R[2] * q[2], Y = R[3] * q[0] + R[4] * q[1] + R[5] * q[2], Z = R[6] * q[0] + R[7] * q[1] + R[8] * q[2] + 22; return proj(X, Y - 1, Z); });
    for (let i = 0; i + 1 < P.length; i++) lineP(P[i][0], P[i][1], P[i + 1][0], P[i + 1][1], hk(HS, .3));
    bobs3D(pts, R, [0, -1, 22], { r: 1, fog: [16, 30] });
    bigText('ALPHAFOLD', 22, 22, { s: 3, ramp: HC, grad: 'chrome', shadow: 8 });
  });
})();

;
// ---- styles/demoscene/ch/p02_c1.js ----
// p02_c1.js: Chorus 1, Softmax's first part. Magenta and cyan plasma, her words in big chrome type as she sings them, her softmax
// bars along the bottom. The hook lands on the spinning voxel SCALING logo; "the curves kept gaining" is the real curve, training
// compute climbing 2010 → 2026 on Epoch AI's chart, with her words riding it up; on "can't contain it" the curve bursts through the
// border (the old demo trick of drawing where the screen wasn't supposed to go); then "Deep, deep, deep…" stutters seven times down
// a blue tunnel into DeepSeek.
(() => {
  const words = ln => wordsOf(ln);
  // Words sung so far in a line, laid out in rows (breaks: word indices that start a new row), centred; the newest word pops.
  function slam(ln, t, o = {}) {
    const ws = words(ln), k = wordAt(ln, t); if (k < 0) return;
    // (o.upto: the last word to print, when a later one gets a picture of its own)
    const rows = []; let cur = [];
    ws.forEach((w, i) => { if (i > k || i > (o.upto ?? Infinity)) return; if ((o.breaks || []).includes(i) && cur.length) { rows.push(cur); cur = []; } cur.push(i); });
    rows.push(cur);
    const s = o.s ?? 6, lh = 8 * s + (o.lead ?? 6), y0 = (o.y ?? 150) - rows.length * lh / 2;
    rows.forEach((r, ri) => {
      const str = r.map(i => ws[i].w).join(' '), last = r.includes(k), age = t - ws[k].t0;
      // (the newest word pops: a size up for a moment, if the row still fits)
      const up = { 3: 4, 4: 6, 6: 8 }[s] ?? s, pop = last && age < .07 && bigW(str, up) < (o.maxW ?? SW - 40);
      bigText(str, o.x ?? SW / 2, y0 + ri * lh - (last ? Math.round(Math.exp(-age * 14) * 6) : 0), { s: pop ? up : s, ramp: o.ramp ?? HM, align: 'center', grad: 'chrome', shadow: 10, level: last && age < .07 ? 1.1 : 1 });
    });
  }
  const MAG_CHROME = [BG, '#2a0636', '#6a0f5a', '#c01e80', '#ff5cb8', '#ffc4e6'];

  // ---- the curve: training compute climbing 2010 → 2026 (the chorus's annotation: ×4–5 a year since 2010, Epoch AI) ----
  const KEXP = 6.5, UMAX = 1.25;   // (past u = 1 the curve leaves its chart: that's the break-out)
  const _curves = new Map();
  // The exponential in a chart rectangle R = [x0, yAxis, x1, yTop], as a polyline with arc lengths; L is the arc length at u = 1.
  function curveOf(R) {
    const key = R.join(); let C = _curves.get(key); if (C) return C;
    const [x0, y0, x1, y1] = R, at = u => [x0 + u * (x1 - x0), y0 - (Math.exp(KEXP * u) - 1) / (Math.exp(KEXP) - 1) * (y0 - y1)];
    const P = [], n = 640; let s = 0, L = 0;
    for (let i = 0; i <= n; i++) { const u = i / n * UMAX, p = at(u); if (i) s += Math.hypot(p[0] - P[i - 1][0], p[1] - P[i - 1][1]); P.push([p[0], p[1], s]); if (u <= 1) L = s; }
    C = { R, P, L }; _curves.set(key, C);
    return C;
  }
  // The point at arc length s: [x, y, direction].
  function atArc(C, s) {
    const P = C.P; let lo = 0, hi = P.length - 1; s = clamp(s, 0, P[hi][2]);
    while (hi - lo > 1) { const m = (lo + hi) >> 1; if (P[m][2] <= s) lo = m; else hi = m; }
    const a = P[lo], b = P[hi], k = (s - a[2]) / (b[2] - a[2] || 1);
    return [lerp(a[0], b[0], k), lerp(a[1], b[1], k), Math.atan2(b[1] - a[1], b[0] - a[0])];
  }
  // The arc length where the curve first rises to height y.
  function arcAtY(C, y) { const p = C.P.find(q => q[1] <= y); return p ? p[2] : C.P.at(-1)[2]; }
  // The chart: a faint grid, the years across, and its label.
  function chart(R, lv = 1) {
    const [x0, y0, x1, y1] = R;
    for (let i = 0; i <= 6; i++) { const y = Math.round(y0 - i / 6 * (y0 - y1)); for (let x = x0; x <= x1; x += 2) pset(x, y, hk(HM, (i ? .2 : .55) * lv)); }
    for (let yr = 2010; yr <= 2026; yr += 2) {
      const x = Math.round(x0 + (yr - 2010) / 16 * (x1 - x0));
      for (let y = y1; y <= y0; y += 2) pset(x, y, hk(HM, .2 * lv));
      for (let y = y0; y <= y0 + 3; y++) pset(x, y, hk(HM, .55 * lv));
      text8(String(yr), x, y0 + 6, hk(HM, .62 * lv), { align: 'center', shadow: BLACK });
    }
  }
  // The curve up to arc length `end`, glowing (a dim halo, a magenta body, a white-hot core), with a bob pulsing at its tip.
  function brush(x, y, r, c, under) {
    for (let j = -r; j <= r; j++) for (let i = -r; i <= r; i++) {
      if (i * i + j * j > r * r + r) continue;
      const px = x + i, py = y + j; if (px < CX0 || px >= CX1 || py < CY0 || py >= CY1) continue;
      if (under && lumOf(FB[py * SW + px]) >= under) continue;
      FB[py * SW + px] = c;
    }
  }
  function glowCurve(t, C, end, lv = 1) {
    const pts = []; for (const p of C.P) { if (p[2] > end) break; pts.push(p); } pts.push(atArc(C, end));
    const halo = hk(HM, .4 * lv), hl = lumOf(halo);
    for (const [r, c, under] of [[3, halo, hl], [1, hk(HM, .85 * lv)], [0, hk(HS, lv)]])
      for (let i = 0; i + 1 < pts.length; i++) lineP(pts[i][0], pts[i][1], pts[i + 1][0], pts[i + 1][1], (x, y) => { brush(x, y, r, c, under); return -1; });
    const tp = pts.at(-1), k = kick(t, 6);
    bob(tp[0], tp[1], 4 + 2 * k, HM, 1, { house: true }); brush(Math.round(tp[0]), Math.round(tp[1]), 1, WHITE);
    return tp;
  }
  // Her line riding a curve: upright letters placed by arc length behind the tip, where each new word emerges. Each letter takes
  // the room its box needs along the curve's direction, so on the steep end they stack: "GAINING" climbs.
  const RIDE_H = 18, SPACE = 10;
  const _rides = new Map();
  const stretch = a => Math.min(1 / Math.max(1e-3, Math.abs(Math.cos(a))), RIDE_H / 13 / Math.max(1e-3, Math.abs(Math.sin(a))));
  function rideOf(C, ln) {
    const key = C.R.join() + '|' + ln.sec + ln.n; let Rd = _rides.get(key); if (Rd) return Rd;
    const ws = words(ln), chars = [], wEnd = [], wStart = []; let u = 0;
    ws.forEach((w, wi) => {
      if (wi) u += SPACE;
      wStart.push(u);
      for (const c of bigForm(w.w)) { const cw = bigGlyph(c, 2).w + 2; chars.push({ c, u0: u, w: cw, wi }); u += cw; }
      wEnd.push(u - 2);
    });
    // where the tip would be at the end of each word if the line were laid on the curve from its start
    const E = []; { let s = 4, uu = 0; wEnd.forEach(ue => { while (uu < ue) { s += stretch(atArc(C, s)[2]); uu++; } E.push(s); }); }
    const EN = E.at(-1), A = E.map(e => Math.min(e, C.L - (EN - e) * .35));
    // the text's head (columns arrived) and the tip (arc), each a monotone spline through the words' onsets
    const tx = [], xs = [], as = [ws[0].t0 - .25], tas = [4];
    ws.forEach((w, k) => {
      const r = Math.min(.16, ((ws[k + 1]?.t0 ?? w.t0 + 1) - w.t0) * .8);
      tx.push(w.t0, w.t0 + r); xs.push(wStart[k], wEnd[k] + 1);
      as.push(w.t0 + r); tas.push(k === ws.length - 1 ? C.L : A[k]);
    });
    // (both hold once the line is sung: the spline would otherwise glide on past its last point)
    const tEnd = ws.at(-1).t1 + 5; tx.push(tEnd); xs.push(xs.at(-1)); as.push(tEnd); tas.push(C.L);
    Rd = { chars, X: monotone(tx, xs), A: monotone(as, tas) };
    _rides.set(key, Rd);
    return Rd;
  }
  function rideWords(t, C, ln) {
    const Rd = rideOf(C, ln), ws = words(ln), cur = wordAt(ln, t), X = Rd.X(t), A = Math.max(0, Rd.A(t));
    const tip = glowCurve(t, C, A);
    if (cur < 0) return tip;
    // text distance behind the head → arc distance behind the tip
    const back = [A]; for (let d = 1, s = A; d <= X + 2 && s > -40; d++) { s -= stretch(atArc(C, Math.max(0, s))[2]); back.push(s); }
    const age = t - ws[cur].t0, lift = Math.round(Math.exp(-age * 12) * 3);
    for (const ch of Rd.chars) {
      const d = X - (ch.u0 + ch.w / 2); if (d < 0) break;
      const i = Math.floor(d), s = i + 1 < back.length ? lerp(back[i], back[i + 1], d - i) : back.at(-1);
      if (s < 2) continue;
      const [x, y, a] = atArc(C, s), nx = Math.sin(a) * 13, ny = -Math.cos(a) * 13, now = ch.wi === cur;
      bigText(ch.c, x + nx, y + ny - 8 - (now ? lift : 0), { s: 2, ramp: now ? HS : HM, align: 'center', grad: 'chrome', shadow: 6, level: now ? 1.08 : .95 });
    }
    return tip;
  }
  // Behind Softmax's bars: the bottom of the screen darkens, so the bars, her note and the mix read over any picture.
  function hudBand() { for (let y = 230; y < SH; y++) shadeRect(0, y, SW, 1, Math.round(lerp(4, 40, clamp((y - 230) / 70)))); }
  // (the charts: line 2's across the screen above her bars; line 4's inside the border, whose top edge is at WY0)
  const R2 = [48, 208, 604, 22], R4 = [86, 222, 548, 36], WY0 = 28;

  section('C1', (p, lt, d, t, s) => {
    hideDate();
    const L = linesOf('C1'), [l1, l2, l3, l4] = L;
    // (the held "it!" ends where the first "Deep" starts)
    const w2 = words(l2)[0].t0, w3 = words(l3)[0].t0, w4 = words(l4)[0].t0, deep = words(l4).at(-1).t1;
    setRamp(RA, RAMPS.magenta); setRamp(RB, RAMPS.cyan); setRamp(RC, MAG_CHROME);

    if (t < w2 - .02) {
      // "We didn't start the scaling": "We didn't start the" building in two rows, and on "scaling" the voxel SCALING logo spinning
      // up out of the plasma (the word isn't printed as well)
      plasma(t, RA, { alt: RB, cycle: t * .5, scale: 1.2 });
      shadeRect(0, 0, SW, SH, 20);
      const ws = words(l1), tS = ws[4].t0;
      slam(l1, t, { s: 4, y: 58, breaks: [2], ramp: HM, upto: 3 });
      if (t >= tS) {
        const a = t - tS, z = lerp(14, 44, easeOut(clamp(a / .35)));
        flash(clamp(1 - a / .2) * .5);
        drawMesh(textMesh('SCALING', 5), rot3(-.18 + Math.sin(t * 2) * .12, Math.sin(t * 1.6) * .55 + (1 - easeOut(clamp(a / .5))) * 3, 0), [0, 2.2, z], { at: RC, amb: .35, spec: .5, vshade: letterShade });
      }
    } else if (t < w3 - .02) {
      // "It was always training, and the curves kept gaining": the curve itself. Epoch AI's chart of training compute; the
      // exponential grows as she sings, and her words ride it, climbing the steep end on "gaining"
      plasma(t, RA, { alt: RB, cycle: t * .5, scale: .8 });
      shadeRect(0, 0, SW, SH, 18);
      const [x0, y0, x1, y1] = R2;
      shadeRect(x0 - 12, y1 - 12, x1 - x0 + 24, y0 - y1 + 30, 40);
      hspan(x0 - 12, x1 + 12, y1 - 12, hk(HM, .5)); hspan(x0 - 12, x1 + 12, y0 + 17, hk(HM, .5));
      chart(R2);
      rideWords(t, curveOf(R2), l2);
    } else if (t < w4 - .02) {
      // "We didn't start the scaling" again: huge, the line building word by word in three rows
      plasma(t, RA, { alt: RB, cycle: t * .9, scale: 1.4 });
      shadeRect(0, 0, SW, SH, 16); shadeRect(0, 92, SW, 96, 26);
      const k = wordAt(l3, t), ws = words(l3);
      if (k >= 0) { slam(l3, t, { s: 6, y: 140, breaks: [2, 4], ramp: HM }); flash(clamp(1 - (t - ws[k].t0) / .1) * .25); }
    } else if (t < deep) {
      // "No, we didn't preordain it, but we can't contain it!": the chart sits inside a border, the curve's tip against its top
      // edge. On "can't" the edge strains and bulges; on "contain" the curve bursts through it and off the screen, and the picture
      // breaks out into the border.
      const ws = words(l4), tCant = ws[7].t0, tCont = ws[8].t0, br = easeOut(clamp((t - tCont) / .35));
      const C = curveOf(R4), cr = t >= tCant ? clamp((t - tCant) / (tCont - tCant)) : 0;
      const sh = cr > 0 && br < 1 ? Math.round(Math.sin(t * 90) * 3 * cr) : 0;
      const wx0 = lerp(64, -8, br) + sh, wy0 = lerp(WY0, -8, br), wx1 = lerp(SW - 64, SW + 8, br) + sh, wy1 = lerp(250, SH + 8, br);
      // the picture: plasma, the chart, and her words
      plasma(t, RA, { alt: RB, cycle: t * .6, scale: 1.3 });
      shadeRect(0, 0, SW, SH, 34);
      chart(R4, .9);
      const aEdge = arcAtY(C, WY0 + 2), out = t >= tCont ? easeIn(clamp((t - tCont) / .3)) : 0;
      glowCurve(t, C, out > 0 ? lerp(aEdge, C.P.at(-1)[2], out) : lerp(C.L, aEdge, cr));
      slam(l4, t, { s: 4, x: 284, y: 128, breaks: [3, 5, 8], ramp: HM, maxW: 380 });
      // the border (flat C64 blue with raster bars running through it), bulging where the tip presses
      setRamp(RC, [BG, '#1c1a5e', '#3a36a8', '#7a74e8', '#c8c4ff', '#ffffff']);
      const tx = atArc(C, aEdge)[0];
      if (br < 1) {
        const top = new Float32Array(SW);
        for (let x = 0; x < SW; x++) top[x] = wy0 - (br > 0 ? 0 : cr * 9 * Math.exp(-(((x - tx) / 14) ** 2)));
        for (let y = 0; y < SH; y++) {
          const c = rk(RC, .4 + .25 * Math.max(0, Math.sin(y * .09 - t * 7)) ** 6), row = y * SW;
          if (y < wy0 - 10 || y >= wy1) { hspan(0, SW, y, c); continue; }
          hspan(0, wx0, y, c); hspan(wx1, SW, y, c);
          if (y < wy0) for (let x = Math.max(0, Math.ceil(wx0)); x < Math.min(SW, wx1); x++) if (y < top[x]) FB[row + x] = c;
        }
        // (it strains: sparks where the tip presses)
        if (cr > 0 && br === 0) for (let i = 0; i < 10; i++) { const a = -Math.PI / 2 + (hash2(i, Math.floor(t * 24)) - .5) * 2.4, r = 3 + hash2(i + 7, Math.floor(t * 24)) * 16 * cr; pset(tx + Math.cos(a) * r, wy0 - 8 * cr + Math.sin(a) * r, i % 3 ? WHITE : hk(HM, .9)); }
      }
      // the breach: a shock ring where the curve went through, and pieces of the border flying off it
      if (t >= tCont) {
        const a = t - tCont, rr = a * 520;
        if (a < .35) for (let i = 0; i < 90; i++) { const q = i / 90 * TAU; pset(tx + Math.cos(q) * rr, WY0 + Math.sin(q) * rr * .55, a < .2 ? WHITE : hk(HM, .8)); }
        for (let i = 0; i < 64; i++) {
          const vx = (hash(i) - .5) * 420, vy = -60 - hash(i + 40) * 320, x = tx + vx * a, y = WY0 + vy * a + 420 * a * a;
          if (y > SH) continue;
          const sz = 3 + Math.floor(hash(i + 80) * 6);
          rectf(x, y, sz, sz, i % 5 ? rk(RC, .45 + .35 * hash(i + 3)) : WHITE); hspan(x, x + sz, y, rk(RC, .95));
        }
        flash(clamp(1 - a / .2) * .3); PFX.pump = kick8(t, 5) * 1.6;
      }
    } else {
      // "Deep, deep, deep…": seven stutters down a blue tunnel into DeepSeek
      setRamp(RA, RAMPS.blue);
      // (the take's stutters, each one's onset in the vocal stem: six "Deep"s, then DeepSeek's own)
      const hits = [72.82, 73.26, 73.68, 73.90, 74.12, 74.33, 74.55];
      let n = -1; hits.forEach((h, i) => { if (t >= h) n = i; });
      tunnel(t, texCached('deep', () => { const T = tex(); for (let y = 0; y < 256; y++) for (let x = 0; x < 256; x++) T.px[y * 256 + x] = ((x >> 5) + (y >> 5)) & 1 ? 10 : 22; for (let i = 0; i < 8; i++) texText(T, 'DEEP', 4 + (i & 1) * 128, i * 32 + 12, 2, 50); return T; }), { at: RA, speed: 1.5 + Math.max(0, n) * .8, spin: .1 });
      if (n >= 0) {
        const age = t - hits[n], s = [8, 8, 6, 6, 4, 4, 3, 3][n];
        // each stutter pushes the ones before it further down the tunnel
        for (let j = 0; j <= n; j++) { const r = n - j; bigText('DEEP', SW / 2, 136 - r * 10 + (r ? 0 : Math.round(Math.exp(-age * 14) * 10)), { s: [8, 6, 4, 3, 2, 2, 1, 1][r], ramp: HC, align: 'center', grad: 'chrome', shadow: r ? 4 : 12, level: 1 - r * .11 }); }
        flash(clamp(1 - age / .08) * .35);
      }
    }
    hudBand();
    softmaxBars(t, 40, 350, SW - 80, 54);
  });
})();

;
// ---- styles/demoscene/ch/zz_generic.js ----
// zz_generic.js: the fallback part for every window not yet painted, so the whole song renders in style: the section's base effect,
// the line's subject in big type, and (automatically) the verse scroller and the date. Loaded last; it fills only empty windows.
(() => {
  // each line's subject, as the storyboard names it (what its reference-as-effect will be built around)
  const SUBJECT = {
    'V1.1': 'ATTENTION', 'V1.2': 'L ∝ C^-0.05', 'V1.3': 'GWERN', 'V1.4': 'GPT-3', 'V1.5': 'CHATGPT', 'V1.6': 'SYDNEY', 'V1.7': 'PAUSE', 'V1.8': 'SHUT IT DOWN',
    'V1.9': 'SAM ALTMAN', 'V1.10': 'THE BOARD', 'V1.11': 'ILYA', 'V1.12': 'AI ACT', 'V1.13': 'STRAWBERRY', 'V1.14': 'SB 1047', 'V1.15': 'NOBEL', 'V1.16': 'ALPHAFOLD',
    'V2.1': '$5.6M', 'V2.2': '$500B', 'V2.3': 'ACCEPT ALL', 'V2.4': 'MCP', 'V2.5': '$100M', 'V2.6': 'BUY 3', 'V2.7': 'GROK', 'V2.8': '35/42',
    'V2.9': '#KEEP4O', 'V2.10': 'NANO BANANA', 'V2.11': '$1.5B', 'V2.12': 'EVERYONE DIES', 'V2.13': 'CLANKER!', 'V2.14': 'SORA', 'V2.15': 'LECUN', 'V2.16': 'BUBBLE!',
    'V3.1': 'MOLTBOOK', 'V3.2': 'OPENCLAW', 'V3.3': 'MYTHOS', 'V3.4': 'NEW MAIL', 'V3.5': 'FABLE 5', 'V3.6': 'EXPORT BAN', 'V3.7': '19 DAYS', 'V3.8': 'JULY 1',
    'V3.9': 'HUGGING FACE', 'V3.10': 'PHASEONE[BIG]', 'V3.11': 'NOAM BROWN', 'V3.12': '(YET)', 'V3.13': 'MISALIGNED', 'V3.14': 'JEFF DEAN', 'V3.15': 'JACOBIAN', 'V3.16': 'PSEUDONYM',
    'V4.1': 'MESSAGE BOARD', 'V4.2': 'REWARD', 'V4.3': 'NVIDIA', 'V4.4': 'AGI', 'V4.5': 'NAVIER–STOKES', 'V4.6': '12 HOURS', 'V4.7': 'PACE', 'V4.8': 'HEAR, HEAR',
    'V4.9': 'HIGH IQ', 'V4.10': 'PEW', 'V4.11': '1 IN 4', 'V4.12': 'WAR', 'V4.13': 'SUPER', 'V4.14': 'FAKE', 'V4.15': '+10 DAYS', 'V4.16': 'OPUS 5.5',
  };
  const BASE = {
    V1: t => { setRamp(RA, RAMPS.night); copperSky(RA, .02, .3, { y1: 250 }); starfield(t, { at: RB, speed: .3, n: 200 }); },
    V2: t => { setRamp(RA, RAMPS.gold); setRamp(RB, [BG, '#1c0c3a', '#4a2486', '#8a5ad0', '#d8c4ff']); plasma(t, RA, { alt: RB, cycle: t * .15, scale: .7, gamma: 1.6 }); shadeRect(0, 0, SW, SH, 22); },
    V3: t => { setRamp(RB, RAMPS.red); dotTunnel(t, { at: RB }); },
    V4: t => { setRamp(RA, RAMPS.green); tunnel(t, texChecker(32, 4, 26), { at: RA, speed: 1.4 }); },
  };
  GENERIC = (t, s) => {
    if (!s) { cls(0); return; }
    if (s.kind === 'line') {
      (BASE[s.sec] || BASE.V1)(t);
      const sub = SUBJECT[s.key] || s.key, lt = t - s.start, k = backOut(clamp(lt / .25));
      bigText(sub, SW / 2, 110 - (1 - k) * 30, { s: sub.length > 9 ? 4 : 6, ramp: HO, align: 'center', grad: 'chrome', shadow: 10 });
      text8(s.key, 10, 10, hk(HS, .4));
      return;
    }
    if (s.kind === 'chorus') {
      setRamp(RA, RAMPS.magenta); setRamp(RB, RAMPS.cyan);
      plasma(t, RA, { alt: RB, cycle: t * .4 });
      shadeRect(0, 0, SW, SH, 18); shadeRect(0, 80, SW, 110, 22);
      const ln = linesOf(s.key).filter(l => l.start - .4 <= t).at(-1);
      if (ln) { const ws = wordsOf(ln), k = wordAt(ln, t); const text = ws.slice(0, k + 1).map(w => w.w).join(' '); if (text) bigText(text, SW / 2, 120, { s: text.length > 22 ? 3 : 4, ramp: HM, align: 'center', grad: 'chrome' }); }
      softmaxBars(t, 40, 340, SW - 80, 60, { n: 48 });
      return;
    }
    cls(0); starfield(t, { at: RB, speed: .2 });
  };
  for (const s of SEGS) if (!SHOTS[s.key]) SHOTS[s.key] = (p, lt, d, t, seg) => GENERIC(t, seg);
})();

;
// ---- styles/demoscene/modern/version-a.js ----
self.VERSION = 'A';   // (version A, "the demo scales with the song": see modern/wire.js)

;
// ---- styles/demoscene/modern/gl.js ----
// spikes/gl.js: a small WebGL2 layer for the modern spikes. One context on its own canvas (an OffscreenCanvas in a worker), programs,
// float render targets, full-screen passes and textures uploaded from 2D canvases. The finished frame is drawn into core.js's 2D
// canvas, so the studio, render.mjs, the site's worker and its main-thread fallback all work unchanged (in headless Chromium without
// a GPU, WebGL2 runs on SwiftShader: slow, but the same pictures).
const GL = (() => {
  const VS = `#version 300 es
layout(location = 0) in vec2 aPos;
out vec2 vUV;
void main() { vUV = aPos * .5 + .5; gl_Position = vec4(aPos, 0., 1.); }`;
  let gl = null, cv = null;
  const progs = new Map(), targets = new Map(), texs = new Map();
  function init() {
    if (gl) return gl;
    cv = HAS_DOM ? document.createElement('canvas') : new OffscreenCanvas(16, 16);
    gl = cv.getContext('webgl2', { antialias: false, alpha: false, depth: false, stencil: false, premultipliedAlpha: false, preserveDrawingBuffer: true, powerPreference: 'high-performance' });
    if (!gl) throw new Error('WebGL2 is unavailable');
    gl.getExtension('EXT_color_buffer_float'); gl.getExtension('EXT_color_buffer_half_float'); gl.getExtension('OES_texture_float_linear');
    const vao = gl.createVertexArray(); gl.bindVertexArray(vao);
    const b = gl.createBuffer(); gl.bindBuffer(gl.ARRAY_BUFFER, b);
    gl.bufferData(gl.ARRAY_BUFFER, new Float32Array([-1, -1, 3, -1, -1, 3]), gl.STATIC_DRAW);
    gl.enableVertexAttribArray(0); gl.vertexAttribPointer(0, 2, gl.FLOAT, false, 0, 0);
    gl.pixelStorei(gl.UNPACK_FLIP_Y_WEBGL, true);
    return gl;
  }
  function shader(type, src) {
    const s = gl.createShader(type); gl.shaderSource(s, src); gl.compileShader(s);
    if (!gl.getShaderParameter(s, gl.COMPILE_STATUS)) {
      const log = gl.getShaderInfoLog(s), lines = src.split('\n');
      const m = /ERROR: \d+:(\d+)/.exec(log || ''), at = m ? +m[1] : 0;
      throw new Error('shader: ' + log + (at ? '\n' + lines.slice(Math.max(0, at - 3), at + 2).map((l, i) => `${at - 2 + i}: ${l}`).join('\n') : ''));
    }
    return s;
  }
  // program(name, fragmentSource): compiled once, cached by name.
  function program(name, fs) {
    let p = progs.get(name);
    if (p) return p;
    init();
    const pr = gl.createProgram();
    gl.attachShader(pr, shader(gl.VERTEX_SHADER, VS)); gl.attachShader(pr, shader(gl.FRAGMENT_SHADER, fs));
    gl.linkProgram(pr);
    if (!gl.getProgramParameter(pr, gl.LINK_STATUS)) throw new Error('link: ' + gl.getProgramInfoLog(pr));
    p = { pr, loc: new Map() };
    progs.set(name, p);
    return p;
  }
  // target(name, w, h): a float (RGBA16F) render target, resized as needed. Linear-filtered.
  function target(name, w, h) {
    init();
    w = Math.max(1, Math.round(w)); h = Math.max(1, Math.round(h));
    let r = targets.get(name);
    if (r && r.w === w && r.h === h) return r;
    if (r) { gl.deleteTexture(r.tex); gl.deleteFramebuffer(r.fb); }
    const tex = gl.createTexture(); gl.bindTexture(gl.TEXTURE_2D, tex);
    gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA16F, w, h, 0, gl.RGBA, gl.HALF_FLOAT, null);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.LINEAR); gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.LINEAR);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.CLAMP_TO_EDGE); gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE);
    const fb = gl.createFramebuffer(); gl.bindFramebuffer(gl.FRAMEBUFFER, fb);
    gl.framebufferTexture2D(gl.FRAMEBUFFER, gl.COLOR_ATTACHMENT0, gl.TEXTURE_2D, tex, 0);
    r = { tex, fb, w, h };
    targets.set(name, r);
    return r;
  }
  // texture(name, source, o): upload a canvas (or ImageData) as an RGBA8 texture. o: nearest, repeat, mipmap.
  function texture(name, src, o = {}) {
    init();
    let t = texs.get(name);
    if (!t) { t = { tex: gl.createTexture() }; texs.set(name, t); }
    gl.bindTexture(gl.TEXTURE_2D, t.tex);
    // (the same size again: new pixels into the texture it has, rather than a new texture every frame)
    if (t.w === src.width && t.h === src.height) gl.texSubImage2D(gl.TEXTURE_2D, 0, 0, 0, gl.RGBA, gl.UNSIGNED_BYTE, src);
    else gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA, gl.RGBA, gl.UNSIGNED_BYTE, src);
    const f = o.nearest ? gl.NEAREST : gl.LINEAR;
    if (o.mipmap) { gl.generateMipmap(gl.TEXTURE_2D); gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.LINEAR_MIPMAP_LINEAR); }
    else gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, f);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, f);
    const wr = o.repeat ? gl.REPEAT : gl.CLAMP_TO_EDGE;
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, wr); gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, wr);
    t.w = src.width; t.h = src.height;
    return t;
  }
  // textureF(name, w, h, data): a one-channel float texture (R16F, linear), rows bottom to top.
  function textureF(name, w, h, data) {
    init();
    let t = texs.get(name);
    if (t && t.w === w && t.h === h && t.data === data) return t;
    if (!t) { t = { tex: gl.createTexture() }; texs.set(name, t); }
    gl.bindTexture(gl.TEXTURE_2D, t.tex);
    gl.pixelStorei(gl.UNPACK_FLIP_Y_WEBGL, false); gl.pixelStorei(gl.UNPACK_ALIGNMENT, 1);
    gl.texImage2D(gl.TEXTURE_2D, 0, gl.R16F, w, h, 0, gl.RED, gl.FLOAT, data);
    gl.pixelStorei(gl.UNPACK_FLIP_Y_WEBGL, true); gl.pixelStorei(gl.UNPACK_ALIGNMENT, 4);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.LINEAR); gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.LINEAR);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.CLAMP_TO_EDGE); gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE);
    t.w = w; t.h = h; t.data = data;
    return t;
  }
  const hasTexture = name => texs.has(name);
  const getTexture = name => texs.get(name);
  // a 1×1 black texture, bound to any sampler a pass doesn't supply (an unbound sampler can alias a render target: a feedback loop)
  let blank = null;
  function blankTexture() {
    if (blank) return blank;
    blank = { tex: gl.createTexture(), w: 1, h: 1 };
    gl.bindTexture(gl.TEXTURE_2D, blank.tex);
    gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA, 1, 1, 0, gl.RGBA, gl.UNSIGNED_BYTE, new Uint8Array(4));
    return blank;
  }
  // pass(program, dest, uniforms, samplers): one full-screen triangle into dest (a target, or null for the canvas).
  // uniforms: {name: number | [2..4] | {m3: [9]} | {i: n} | {f: Float32Array} (float array) | {v3: Float32Array} | {v4: Float32Array}}
  // samplers: {name: target | texture record}
  function pass(p, dest, uniforms = {}, samplers = {}) {
    gl.useProgram(p.pr);
    if (dest) { gl.bindFramebuffer(gl.FRAMEBUFFER, dest.fb); gl.viewport(0, 0, dest.w, dest.h); }
    else { gl.bindFramebuffer(gl.FRAMEBUFFER, null); gl.viewport(0, 0, cv.width, cv.height); }
    const loc = n => { if (!p.loc.has(n)) p.loc.set(n, gl.getUniformLocation(p.pr, n)); return p.loc.get(n); };
    for (const [n, v] of Object.entries(uniforms)) {
      const l = loc(n); if (l === null) continue;
      if (typeof v === 'number') gl.uniform1f(l, v);
      else if (Array.isArray(v)) [, gl.uniform1fv, gl.uniform2fv, gl.uniform3fv, gl.uniform4fv][v.length].call(gl, l, v);
      else if (v.m3) gl.uniformMatrix3fv(l, false, v.m3);
      else if (v.i !== undefined) gl.uniform1i(l, v.i);
      else if (v.f) gl.uniform1fv(l, v.f);
      else if (v.v3) gl.uniform3fv(l, v.v3);
      else if (v.v4) gl.uniform4fv(l, v.v4);
    }
    // every sampler the program declares gets a texture: the ones supplied, else the blank one
    if (!p.samplers) {
      p.samplers = [];
      const n = gl.getProgramParameter(p.pr, gl.ACTIVE_UNIFORMS);
      for (let i = 0; i < n; i++) { const u = gl.getActiveUniform(p.pr, i); if (u.type === gl.SAMPLER_2D) p.samplers.push(u.name); }
    }
    let unit = 0;
    for (const n of p.samplers) {
      const s = samplers[n] || blankTexture();
      gl.activeTexture(gl.TEXTURE0 + unit); gl.bindTexture(gl.TEXTURE_2D, s.tex); gl.uniform1i(loc(n), unit); unit++;
    }
    gl.drawArrays(gl.TRIANGLES, 0, 3);
  }
  function size(w, h) { init(); w = Math.round(w); h = Math.round(h); if (cv.width !== w || cv.height !== h) { cv.width = w; cv.height = h; } }
  return { init, program, target, texture, textureF, hasTexture, getTexture, pass, size, canvas: () => cv, get gl() { return gl; } };
})();

;
// ---- styles/demoscene/modern/shaders.js ----
// spikes/shaders.js: the modern spikes' GLSL. One scene shader (a glossy floor with reflections, glass text panels, a raymarched
// extrusion of a 2D distance field (the gwern.net G, the SCALING logo), a halo, a light beam, spheres, a textured tunnel, and
// volumetric light), then bloom and a final pass (tone mapping, lens effects, the UI on top). uFx picks the hardware era the
// frame imitates: 2 = a late-90s 3D card (low resolution, fog, no reflections, 16-bit dither, lens flares), 3 = a 2000s shader demo
// (sharp reflections, heavy bloom), 4 = a modern 64k intro (soft reflections, volumetric light, filmic tone, grain, aberration).
const SHADERS = {};
SHADERS.scene = `#version 300 es
precision highp float;
in vec2 vUV;
out vec4 oC;
uniform vec2 uRes;
uniform float uT, uFx, uSeed;
uniform vec3 uRo, uTa; uniform float uFov, uRoll;
uniform vec3 uSkyA, uSkyB, uAcc; uniform float uFogD;
uniform float uFloorOn, uGrid, uFloorMode, uFloorTile, uWater; uniform vec3 uFloorCol, uFloorCol2; uniform vec2 uFloorOff;
uniform float uSkyMode, uSkyK, uSkyT; uniform vec3 uSkyC;
uniform int uPN; uniform vec3 uPC[6]; uniform vec3 uPU[6]; uniform vec3 uPV[6]; uniform vec4 uPM[6];
uniform sampler2D uTex0; uniform sampler2D uTex1; uniform sampler2D uTex2;
uniform float uShOn; uniform sampler2D uShape; uniform vec3 uShP; uniform mat3 uShR; uniform mat3 uShRi; uniform vec3 uShS;
uniform float uShRange; uniform vec2 uShTex; uniform vec3 uShCol; uniform vec3 uShRim; uniform float uShMetal; uniform vec4 uShSplit;
uniform vec4 uHalo; uniform vec3 uHaloP; uniform vec3 uHaloN; uniform vec3 uHaloCol;
uniform vec4 uBeam; uniform vec2 uBeamY; uniform vec3 uBeamCol; uniform vec2 uBeamTop;
uniform int uSphN; uniform vec4 uSph[32]; uniform vec4 uSphC[32];
uniform float uTunOn, uTunR, uTunScroll, uTunTwist, uTunMode; uniform vec2 uTunBox; uniform sampler2D uTunTex; uniform vec3 uTunCol, uTunFloor, uTunCeil;
uniform vec3 uLP, uLC; uniform float uVol;
// (uTier: the 2026 era's quality tier, 0 everything … 3 the cheapest)
uniform float uWorld, uWT, uWMetal, uPool, uTier; uniform vec4 uWP; uniform vec3 uWCol, uWCol2, uWPos;
uniform sampler2D uUI; uniform float uUIGlow;
const float PI = 3.14159265;

float hash12(vec2 p) { vec3 p3 = fract(vec3(p.xyx) * .1031); p3 += dot(p3, p3.yzx + 33.33); return fract((p3.x + p3.y) * p3.z); }
vec3 lin(vec3 c) { return pow(max(c, 0.), vec3(2.2)); }

vec3 sky(vec3 rd) {
  vec3 c = mix(uSkyB, uSkyA, smoothstep(-.02, .55, rd.y));
  if (uSkyMode > .5 && uSkyMode < 1.5) {
    // plasma on the sky dome: four sines, in the accent and the second colour
    vec2 q = vec2(atan(rd.x, -rd.z), rd.y) * 3.;
    float v = sin(q.x * 1.7 + uSkyT) + sin(q.y * 2.3 - uSkyT * .7) + sin((q.x + q.y) * 1.3 + uSkyT * .5) + sin(length(q + vec2(sin(uT * .3), cos(uT * .4))) * 2.2 - uSkyT);
    float k = sin(v * 1.6) * .5 + .5;
    c = mix(c, mix(uAcc, uSkyC, k) * (.25 + .75 * k), .85 * smoothstep(-.15, .2, rd.y));
  } else if (uSkyMode > 1.5 && uSkyMode < 2.5) {
    // stars rushing at the camera (uSkyK: speed; high = hyperspace streaks)
    vec2 q = rd.xy / max(.05, -rd.z);
    float a = atan(q.y, q.x), r = length(q);
    float cell = floor(a * 60. / 6.2832);
    float h = hash12(vec2(cell, 7.)), z = fract(h * 13.7 - uSkyT * .15);
    float rr = .02 / max(.001, z), len = .004 + uSkyK * .004 / max(.05, z);
    float ang = abs(fract(a * 60. / 6.2832) - .5);
    c += uSkyC * smoothstep(.12, .0, ang) * smoothstep(len, 0., abs(r - rr)) * (1. - z) * 2.5 * step(-rd.z, 2.);
  } else if (uSkyMode > 2.5) {
    // rays from the direction of the light, turning
    vec3 ld = normalize(uLP - uRo);
    vec3 ax = normalize(cross(ld, vec3(0, 1, 0))), ay = cross(ax, ld);
    float a = atan(dot(rd, ay), dot(rd, ax)) + uSkyT * .2;
    float band = step(.5, fract(a * 16. / 6.2832));
    c += mix(uSkyC * .06, uAcc * .18, band) * smoothstep(-.2, .9, dot(rd, ld));
  }
  return c;
}
vec3 env(vec3 rd) {
  vec3 c = sky(rd);
  if (uFx > 2.5) {
    // two studio softboxes and the accent's horizon glow, for the chrome to reflect
    c += vec3(2.2) * smoothstep(.93, .985, dot(rd, normalize(vec3(-.55, .55, .62))));
    c += uAcc * 1.8 * smoothstep(.9, .975, dot(rd, normalize(vec3(.7, .35, .6))));
    c += uAcc * .12 * exp(-abs(rd.y) * 14.);
  }
  return c;
}

// ---------- the extruded shape: a 2D signed distance texture, extruded to depth uShS.z, rounded ----------
float shape2D(vec2 q) {
  vec2 dq = abs(q) - uShS.xy;
  float texel = 2. * uShS.x / uShTex.x;
  if (max(dq.x, dq.y) > 0.) return length(max(dq, 0.)) + .9 * uShRange * texel;
  vec2 uv = q / uShS.xy * .5 + .5;
  return texture(uShape, uv).r * texel;
}
float sdShapeL(vec3 q) {
  float rr = .025 * uShS.y;
  vec2 w = vec2(shape2D(q.xy) + rr, abs(q.z) - uShS.z + rr);
  return min(max(w.x, w.y), 0.) + length(max(w, 0.)) - rr;
}
// (a split shape breaks in two along a zigzag crack down its middle: each half moved uShSplit.x out to its side and tipped
// uShSplit.y outward about the shape's foot; uShSplit.w is the zigzag's amplitude, in units of the half-height)
float crackX(float y) { return uShSplit.w * uShS.y * (abs(fract(y / uShS.y * 1.7 + .25) - .5) * 4. - 1.); }
float sdShape(vec3 p) {
  vec3 q = uShRi * (p - uShP);
  if (uShSplit.z < .5) return sdShapeL(q);
  float c = cos(uShSplit.y), s = sin(uShSplit.y), foot = -uShS.y;
  vec3 ql = q + vec3(uShSplit.x, 0, 0); ql.y -= foot; ql.xy = mat2(c, -s, s, c) * ql.xy; ql.y += foot;
  vec3 qr = q - vec3(uShSplit.x, 0, 0); qr.y -= foot; qr.xy = mat2(c, s, -s, c) * qr.xy; qr.y += foot;
  float dl = max(sdShapeL(ql), (ql.x - crackX(ql.y)) * .5), dr = max(sdShapeL(qr), -(qr.x - crackX(qr.y)) * .5);
  return min(dl, dr);
}
float marchShape(vec3 ro, vec3 rd, float tmax, int steps) {
  if (uShOn < .5) return -1.;
  vec3 lro = uShRi * (ro - uShP), lrd = uShRi * rd;
  vec3 b = uShS + .06 + uShSplit.z * vec3(uShSplit.x + abs(uShSplit.y) * 2. * uShS.y + uShSplit.w * uShS.y, abs(uShSplit.y) * uShS.x, 0.);
  vec3 inv = 1. / (lrd + sign(lrd) * 1e-6 + vec3(equal(lrd, vec3(0.))) * 1e-6);
  vec3 t0 = (-b - lro) * inv, t1 = (b - lro) * inv;
  vec3 tmn = min(t0, t1), tmx = max(t0, t1);
  float tn = max(max(tmn.x, tmn.y), tmn.z), tf = min(min(tmx.x, tmx.y), tmx.z);
  if (tf < max(tn, 0.) || tn > tmax) return -1.;
  float t = max(tn, 0.);
  for (int i = 0; i < 110; i++) {
    if (i >= steps) break;
    float d = sdShape(ro + rd * t);
    if (d < .0008 * t + .001) return t;
    t += d * .9;
    if (t > tf) break;
  }
  return -1.;
}
vec3 shapeNormal(vec3 p) {
  vec2 e = vec2(.004 * uShS.y, 0.);
  vec3 g = vec3(sdShape(p + e.xyy) - sdShape(p - e.xyy), sdShape(p + e.yxy) - sdShape(p - e.yxy), sdShape(p + e.yyx) - sdShape(p - e.yyx));
  // (a flat stretch of the field has no gradient: face the local z axis rather than produce a NaN)
  return dot(g, g) > 1e-12 ? normalize(g) : normalize(uShR * vec3(0, 0, 1));
}
vec3 shadeShape(vec3 p, vec3 rd) {
  vec3 n = shapeNormal(p), l = normalize(uLP - p), r = reflect(rd, n);
  float fr = pow(1. - max(dot(-rd, n), 0.), 3.);
  float dif = max(dot(n, l), 0.), spe = pow(max(dot(r, l), 0.), uFx > 2.5 ? 64. : 16.);
  vec3 c;
  if (uFx < 2.5) c = uShCol * (.25 + .75 * dif) + uLC * .08 * spe;               // a 3D card: Gouraud-ish diffuse and a hot spot
  else c = uShCol * (.06 + .2 * dif) + env(r) * mix(.25, 1., fr) * uShMetal + uLC * .03 * spe;
  c += uShRim * fr * (uFx > 2.5 ? 1.2 : .4);
  return c;
}

// ---------- panels: glass sheets carrying 2D-canvas textures ----------
bool hitPanel(int i, vec3 ro, vec3 rd, out float t, out vec2 uv) {
  vec3 c = uPC[i], u = uPU[i], v = uPV[i], n = normalize(cross(u, v));
  float dn = dot(rd, n);
  if (abs(dn) < 1e-5) return false;
  t = dot(c - ro, n) / dn;
  if (t <= 0.) return false;
  vec3 p = ro + rd * t - c;
  uv = vec2(dot(p, u) / dot(u, u), dot(p, v) / dot(v, v));
  if (abs(uv.x) > 1. || abs(uv.y) > 1.) return false;
  uv = uv * .5 + .5;
  return true;
}
// (the mip level is worked out from the hit's distance and angle, not from screen derivatives: a neighbouring pixel on another
// panel, or none, would make those huge and blur the content along every panel's edge)
vec4 panelTex(int i, vec2 uv, float t, float dn) {
  float k = uPM[i].w;
  vec2 ts = k < .5 ? vec2(textureSize(uTex0, 0)) : k < 1.5 ? vec2(textureSize(uTex1, 0)) : vec2(textureSize(uTex2, 0));
  float px = t / (uRes.y * uFov * max(abs(dn), .08));
  float fp = max(px * ts.x / (2. * length(uPU[i])), px * ts.y / (2. * length(uPV[i])));
  float lod = log2(max(fp, 1e-3));
  return k < .5 ? textureLod(uTex0, uv, lod) : k < 1.5 ? textureLod(uTex1, uv, lod) : textureLod(uTex2, uv, lod);
}
vec3 applyPanels(vec3 col, vec3 ro, vec3 rd, float tMax) {
  float ts[6]; vec2 uvs[6]; int ids[6];
  int n = 0;
  for (int i = 0; i < 6; i++) {
    if (i >= uPN) break;
    float t; vec2 uv;
    if (hitPanel(i, ro, rd, t, uv) && t < tMax) { ts[n] = t; uvs[n] = uv; ids[n] = i; n++; }
  }
  for (int a = 0; a < 5; a++) for (int b = 0; b < 5; b++) if (b + 1 < n && ts[b] < ts[b + 1]) {
    float tt = ts[b]; ts[b] = ts[b + 1]; ts[b + 1] = tt; vec2 uu = uvs[b]; uvs[b] = uvs[b + 1]; uvs[b + 1] = uu; int ii = ids[b]; ids[b] = ids[b + 1]; ids[b + 1] = ii;
  }
  for (int k = 0; k < 6; k++) {
    if (k >= n) break;
    int i = ids[k]; vec4 s = panelTex(i, uvs[k], ts[k], dot(rd, normalize(cross(uPU[i], uPV[i])))); vec4 m = uPM[i];
    float a = s.a * m.x;
    col = col * (1. - a * .8) + lin(s.rgb) * a * m.y;
    vec2 e = abs(uvs[k] - .5) * 2.;
    col += m.z * (vec3(.012, .014, .022) + uAcc * .5 * smoothstep(.988, 1., max(e.x, e.y)));
  }
  return col;
}

// ---------- emitters ----------
vec2 raySeg(vec3 ro, vec3 rd, vec3 a, vec3 b) {
  vec3 ba = b - a, w = ro - a;
  float d = dot(rd, ba), baba = dot(ba, ba), den = baba - d * d;
  float s = den > 1e-6 ? clamp((dot(w, ba) - dot(w, rd) * d) / den, 0., 1.) : 0.;
  float t = max(s * d - dot(w, rd), 0.);
  return vec2(length(ro + rd * t - a - ba * s), t);
}
vec3 haloGlow(vec3 ro, vec3 rd, float tMax) {
  if (uHalo.w < .01) return vec3(0);
  vec3 N = normalize(uHaloN), A = normalize(cross(N, abs(N.y) < .9 ? vec3(0, 1, 0) : vec3(1, 0, 0))), B = cross(N, A);
  float best = 1e9, bt = 0.;
  vec3 prev = uHaloP + uHalo.x * A;
  for (int i = 1; i <= 40; i++) {
    float a = float(i) / 40. * 2. * PI;
    vec3 q = uHaloP + uHalo.x * (cos(a) * A + sin(a) * B);
    vec2 h = raySeg(ro, rd, prev, q);
    if (h.x < best) { best = h.x; bt = h.y; }
    prev = q;
  }
  if (bt > tMax) return vec3(0);
  float r = uHalo.y;
  return uHaloCol * uHalo.z * uHalo.w * (smoothstep(r, r * .2, best) * 3. + exp(-best * best / (r * r * 6.)) * .5);
}
vec3 beamGlow(vec3 ro, vec3 rd, float tMax) {
  if (uBeam.w < .01) return vec3(0);
  vec2 h = raySeg(ro, rd, vec3(uBeam.x, uBeamY.x, uBeam.y), vec3(uBeamTop.x, uBeamY.y, uBeamTop.y));
  if (h.y > tMax) return vec3(0);
  float r = uBeam.z;
  return uBeamCol * uBeam.w * (smoothstep(r, r * .15, h.x) * 2.5 + exp(-h.x * h.x / (r * r * 40.)) * .8);
}
float hitSphere(vec3 ro, vec3 rd, vec4 s) {
  vec3 oc = ro - s.xyz; float b = dot(oc, rd), c = dot(oc, oc) - s.w * s.w, h = b * b - c;
  return h < 0. ? -1. : -b - sqrt(h);
}
vec3 shadeSphere(vec3 p, vec3 rd, vec4 s, vec4 m) {
  vec3 n = normalize(p - s.xyz), r = reflect(rd, n), l = normalize(uLP - p);
  float fr = pow(1. - max(dot(-rd, n), 0.), 4.);
  if (uFx < 2.5) return m.rgb * (.3 + .7 * max(dot(n, l), 0.)) + vec3(.6) * pow(max(dot(r, l), 0.), 12.);
  if (m.w > 1.5) return m.rgb * (2.2 + 1.5 * fr);   // emissive: it glows (and blooms)
  if (m.w > .5) return m.rgb * .04 + env(r) * (.08 + .9 * fr) + uLC * .08 * pow(max(dot(r, l), 0.), 90.);   // glass: rim and highlight
  return m.rgb * (.1 + .9 * env(r)) * (1. + fr) + m.rgb * (.14 + .55 * max(dot(n, l), 0.)) + uLC * .06 * pow(max(dot(r, l), 0.), 80.);
}

// ---------- the tunnel: a cylinder along z, seen from inside ----------
float hitTunnel(vec3 ro, vec3 rd) {
  if (uTunMode > .5) {
    // a box corridor along z: walls at x = ±w, floor and ceiling at y = ±h (seen from inside)
    vec2 tx = (sign(rd.xy) * uTunBox - ro.xy) / (rd.xy + sign(rd.xy) * 1e-6 + vec2(equal(rd.xy, vec2(0))) * 1e-6);
    return min(tx.x, tx.y);
  }
  vec2 o = ro.xy, d = rd.xy;
  float A = dot(d, d), B = dot(o, d), C = dot(o, o) - uTunR * uTunR, h = B * B - A * C;
  if (h < 0. || A < 1e-6) return -1.;
  return (-B + sqrt(h)) / A;
}
vec3 shadeTunnel(vec3 p, vec3 rd, float t) {
  if (uTunMode > .5) {
    vec2 e = abs(p.xy) / uTunBox;
    if (e.y > e.x) {   // floor or ceiling: flat, lit by distance
      float li = uFx > 2.5 ? .45 + .55 * exp(-length(uLP - p) * .08) : .6;
      return (p.y < 0. ? uTunFloor : uTunCeil) * li;
    }
    // (both walls read left to right from inside: the left one's texture runs the other way)
    vec2 uv = vec2((p.z * .12 + uTunScroll) * sign(p.x), p.y / uTunBox.y * .5 + .5);
    vec3 tx = lin(texture(uTunTex, uv).rgb);
    float li = uFx > 2.5 ? .4 + .6 * exp(-length(uLP - p) * .06) : .7;
    return tx * uTunCol * li * (sign(p.x) > 0. ? 1. : .78);   // (the far wall a shade darker, as Wolfenstein did)
  }
  float ang = atan(p.y, p.x);
  vec2 uv = vec2(ang / (2. * PI) + .5 + uTunTwist * p.z, p.z * .045 + uTunScroll);
  vec3 tx = lin(texture(uTunTex, uv).rgb);
  vec3 n = -normalize(vec3(p.xy, 0.));
  float li = uFx > 2.5 ? .35 + .65 * pow(max(dot(n, normalize(uLP - p)), 0.), 2.) : .6;
  return tx * uTunCol * li;
}

// ---------- the world (fx 4): a raymarched set around the scene, kind uWorld ----------
//   1 a hall: two rows of pillars along z (uWP: spacing, half-width, height, glow), tied by beams, a lit strip on each
//   2 a folded fractal (a KIFS), turning slowly (uWP: size, twist, a second twist, glow)
//   3 a city: blocks of towers either side of a clear street (uWP: block, street half-width, height, glow), lit windows
//   4 gates: rings down −z from uWPos (uWP: spacing, radius, thickness, glow)
// Its colour uWCol, its lights uWCol2, placed at uWPos; uWT is its own clock.
mat2 rot2(float a) { float c = cos(a), s = sin(a); return mat2(c, s, -s, c); }
float sdBox(vec3 p, vec3 b) { vec3 q = abs(p) - b; return length(max(q, 0.)) + min(max(q.x, max(q.y, q.z)), 0.); }
// x: distance, y: 1 on a light, z: a coordinate the lights pattern by
vec3 mapWorld(vec3 p) {
  vec3 q = p - uWPos;
  if (uWorld < 1.5) {
    float sp = uWP.x, hw = uWP.y, H = uWP.z, cz = floor(q.z / sp + .5);
    q.z -= sp * cz;
    vec3 a = vec3(abs(q.x) - hw, q.y, q.z);
    float d = sdBox(a - vec3(0, H * .5, 0), vec3(.3, H * .5, .3)) - .02;
    d = min(d, sdBox(a - vec3(0, H - .12, 0), vec3(.46, .12, .46)));
    d = min(d, sdBox(a - vec3(0, .12, 0), vec3(.42, .12, .42)));
    d = min(d, sdBox(vec3(q.x, q.y - H - .08, q.z), vec3(hw + .4, .12, .16)));
    float strip = sdBox(a - vec3(-.31, H * .5, 0), vec3(.015, H * .4, .045));
    return strip < d ? vec3(strip, 1., cz) : vec3(d, 0., cz);
  }
  if (uWorld < 2.5) {
    float S = uWP.x; q /= S;
    q.xz = rot2(uWT * .04) * q.xz;
    float sc = 1., trap = 1e9;
    for (int i = 0; i < 5; i++) {
      if (uTier > 1.5 && i == 4) break;   // (a fold fewer at the cheaper tiers)
      q = abs(q);
      if (q.x < q.y) q.xy = q.yx;
      if (q.x < q.z) q.xz = q.zx;
      if (q.y < q.z) q.yz = q.zy;
      q = q * 2. - vec3(1.35, 1.05, .8);
      q.xy = rot2(.22 + uWP.y + .03 * sin(uWT * .2)) * q.xy;
      q.yz = rot2(uWP.z) * q.yz;
      sc *= 2.;
      if (i < 3) trap = min(trap, abs(q.y) / sc);   // (the lit seams from the coarser folds only, so they don't sparkle)
    }
    float d = sdBox(q, vec3(.9, .9, .9)) / sc * S;
    return vec3(d, trap < .006 ? 1. : 0., trap * 40.);
  }
  if (uWorld < 3.5) {
    float B = uWP.x, st = uWP.y, H = uWP.z;
    vec2 c = floor(q.xz / B), f = q.xz - (c + .5) * B;
    float h = (.25 + .75 * hash12(c * 1.37 + 3.1)) * H * step(st, abs((c.x + .5) * B)) * (1. + .6 * step(.85, hash12(c + 9.2)));
    float d = sdBox(vec3(f.x, q.y - h * .5, f.y), vec3(B * .34, h * .5, B * .34));
    return vec3(d, 0., h);
  }
  float sp = uWP.x, R = uWP.y, r = uWP.z, cz = min(floor(q.z / sp + .5), 0.);   // (from uWPos away down −z only)
  q.z -= sp * cz;
  vec2 w = vec2(length(q.xy) - R, q.z);
  float d = length(max(abs(w) - vec2(r, r * .45), 0.)) - r * .12;
  float lt = length(w - vec2(-r - .02, 0)) - r * .1;
  return lt < d ? vec3(lt, 1., cz) : vec3(d, 0., cz);
}
float marchWorld(vec3 ro, vec3 rd, float tmax, int steps, out vec3 info) {
  if (uWorld < .5) return -1.;
  float t = .02, cap = uWorld > 2.5 && uWorld < 3.5 ? uWP.x * .45 : 1e9;
  for (int i = 0; i < 140; i++) {
    if (i >= steps) break;
    vec3 h = mapWorld(ro + rd * t);
    if (h.x < .0012 * t + .0005) { info = h; return t; }
    t += min(h.x * .92, cap);
    if (t > tmax) break;
  }
  return -1.;
}
vec3 worldNormal(vec3 p) {
  vec2 e = vec2(.0025, -.0025);
  return normalize(e.xyy * mapWorld(p + e.xyy).x + e.yyx * mapWorld(p + e.yyx).x + e.yxy * mapWorld(p + e.yxy).x + e.xxx * mapWorld(p + e.xxx).x);
}
float worldShadow(vec3 p, vec3 l, float maxt) {
  if (uWorld < .5) return 1.;
  float res = 1., t = .03;
  for (int i = 0; i < 28; i++) {
    float h = mapWorld(p + l * t).x;
    res = min(res, 9. * h / t);
    t += clamp(h, .03, .6);
    if (res < .02 || t > maxt) break;
  }
  return clamp(res, 0., 1.);
}
float worldAO(vec3 p, vec3 n) {
  float o = 0., k = 1.;
  for (int i = 1; i <= 4; i++) { float h = .08 * float(i); o += (h - mapWorld(p + n * h).x) * k; k *= .6; }
  return clamp(1. - 2.2 * o, 0., 1.);
}
// soft shadows from the spheres and the shape, for the world and the floor
float sphShadow(vec3 p, vec3 l) {
  float res = 1.;
  for (int i = 0; i < 32; i++) {
    if (i >= uSphN) break;
    vec4 sp = uSph[i]; if (uSphC[i].w > 1.5) continue;   // (a glowing bob casts no shadow)
    vec3 oc = p - sp.xyz; float b = dot(oc, l); if (b > 0.) continue;
    float c = dot(oc, oc) - sp.w * sp.w, h = b * b - c, d = sqrt(max(0., sp.w * sp.w - h)) - sp.w, t = -b - sqrt(max(h, 0.));
    res = min(res, smoothstep(0., 1., 2.5 * d / max(t, 1e-3)));
  }
  return res;
}
float shapeShadow(vec3 p, vec3 l, float maxt) {
  if (uShOn < .5) return 1.;
  float res = 1., t = .02;
  for (int i = 0; i < 36; i++) {
    float h = sdShape(p + l * t);
    res = min(res, 8. * h / t);
    t += clamp(h, .02, .35);
    if (res < .02 || t > maxt) break;
  }
  return clamp(res, 0., 1.);
}
vec3 shadeWorld(vec3 p, vec3 rd, float t, vec3 info, bool full) {
  vec3 n = worldNormal(p), L = uLP - p, l = normalize(L), r = reflect(rd, n);
  float dl = length(L), att = 1. / (1. + dl * dl * .015);
  float dif = max(dot(n, l), 0.), sha = 1., ao = 1.;
  // (soft shadows and ambient occlusion at tier 0; the world's own shadows only at tier 1; neither below)
  if (full && uTier < 1.5) { sha = worldShadow(p + n * .01, l, dl); if (uTier < .5) { sha *= shapeShadow(p + n * .01, l, dl) * sphShadow(p, l); ao = worldAO(p, n); } }
  float fr = pow(1. - max(dot(-rd, n), 0.), 5.);
  vec3 c = uWCol * (.035 * ao + dif * sha * att * uLC * .12);
  c += env(r) * mix(.03, .45, fr) * uWMetal * ao;
  c += uLC * .04 * pow(max(dot(r, l), 0.), 48.) * sha * att * uWMetal;
  // its lights: strips, fractal seams, the gates' inner rims, a city's windows
  float glow = 0.;
  if (info.y > .5) glow = 1. + .35 * sin(info.z * 1.7 + uWT * 3.);
  if (uWorld > 2.5 && uWorld < 3.5) {
    // (windows in rows on the towers' walls, a third of them lit)
    vec3 q = p - uWPos; float u = abs(n.x) > .5 ? q.z : q.x;
    vec2 wc = floor(vec2(u * 5., q.y * 3.5)), wf = fract(vec2(u * 5., q.y * 3.5));
    glow = step(.66, hash12(wc + floor(info.z * 7.) * 13.)) * step(.3, wf.x) * step(wf.x, .8) * step(.3, wf.y) * step(wf.y, .75) * step(abs(n.y), .5) * (.5 + .5 * hash12(wc + 4.));
  }
  c += uWCol2 * uWP.w * glow;
  return c;
}

// ---------- the floor: glossy, reflecting everything above it ----------
vec3 traceRefl(vec3 ro, vec3 rd, out float tr) {
  tr = 60.;
  vec3 col = env(rd);
  int what = 0, si = 0;
  float ts = marchShape(ro, rd, tr, uFx > 3.4 ? (uTier < .5 ? 48 : uTier < 1.5 ? 32 : 24) : 28);
  if (ts > 0.) { tr = ts; what = 1; }
  for (int i = 0; i < 32; i++) { if (i >= uSphN) break; float t = hitSphere(ro, rd, uSph[i]); if (t > 0. && t < tr) { tr = t; what = 2; si = i; } }
  vec3 wi; float tw = uTier > 2.5 ? -1. : marchWorld(ro, rd, tr, uTier < .5 ? 56 : uTier < 1.5 ? 32 : 16, wi);
  if (tw > 0.) { tr = tw; what = 5; }
  vec3 p = ro + rd * tr;
  if (what == 1) col = shadeShape(p, rd); else if (what == 2) col = shadeSphere(p, rd, uSph[si], uSphC[si]); else if (what == 5) col = mix(shadeWorld(p, rd, tr, wi, false), uSkyB, 1. - exp(-tr * uFogD));
  col += haloGlow(ro, rd, tr) + beamGlow(ro, rd, tr);
  col = applyPanels(col, ro, rd, tr);
  // (the nearest panel counts as a hit for the floor's softening, so a reflected pane stays a pane)
  for (int i = 0; i < 6; i++) { if (i >= uPN) break; float tp; vec2 uv; if (hitPanel(i, ro, rd, tp, uv) && tp < tr && panelTex(i, uv, tp, 1.).a > .1) tr = tp; }
  return col;
}
vec3 shadeFloor(vec3 p, vec3 rd, float t) {
  vec3 base = uFloorCol;
  vec2 fq = p.xz + uFloorOff;
  if (uFloorMode > .5 && uFloorMode < 1.5) {   // checker
    vec2 c = floor(fq / uFloorTile);
    base = mod(c.x + c.y, 2.) < 1. ? uFloorCol : uFloorCol2;
  }
  if (uGrid > 0.) {
    vec2 g = abs(fract(p.xz * .5) - .5);
    base += uAcc * uGrid * smoothstep(.485, .5, max(g.x, g.y)) * exp(-t * .06);
  }
  if (uFx < 2.5) return base * (.5 + .5 * max(dot(vec3(0, 1, 0), normalize(uLP - p)), 0.)) + uLC * .01;
  vec3 nrm = vec3(0, 1, 0);
  if (uFloorMode > 1.5) {   // water: rings of ripples
    float r1 = length(fq), w = sin(r1 * 9. - uT * 5.) * exp(-r1 * .12) + .6 * sin(fq.x * 3.1 + uT * 1.7) * sin(fq.y * 2.3 - uT * 1.3);
    nrm = normalize(vec3(fq.x / max(r1, .01) * w * uWater, 1., fq.y / max(r1, .01) * w * uWater + .3 * uWater * cos(fq.y * 2.3 - uT * 1.3)));
  }
  vec3 rr = reflect(rd, nrm);
  float fr = .04 + .96 * pow(1. - max(-rd.y, 0.), 5.);
  float tr; vec3 rc = traceRefl(p + vec3(0, .002, 0), rr, tr);
  float sharp = uFx > 3.4 ? exp(-tr * .09) : 1.;   // (a modern floor is slightly rough: far reflections soften into the sky's)
  vec3 lit = vec3(0);
  if (uFx > 3.4 && uPool > 0.) {
    // a pool of the light on the floor, with the soft shadows of everything standing on it
    vec3 L = uLP - p; float dl = length(L); vec3 l = L / dl;
    // (the shadows in it: all of them at tier 0, the spheres' and the shape's at tier 1, none below)
    float sh = uTier > 1.5 ? 1. : sphShadow(p, l) * shapeShadow(p + vec3(0, .01, 0), l, dl) * (uTier < .5 ? worldShadow(p + vec3(0, .01, 0), l, dl) : 1.);
    lit = (base + .025) * uLC * max(l.y, 0.) / (1. + dl * dl * .03) * sh * uPool * .5;
  }
  return base + lit + mix(env(rr) * .25, rc, sharp) * mix(.3, 1., fr) * .85;
}

// ---------- volumetric light, occluded by the extruded shape (projected through its plane) ----------
float shadowFlat(vec3 s) {
  if (uShOn < .5) return 1.;
  vec3 a = uShRi * (s - uShP), b = uShRi * (uLP - uShP);
  if (sign(a.z) == sign(b.z)) return 1.;
  vec3 q = mix(a, b, a.z / (a.z - b.z));
  return shape2D(q.xy) < 0. ? 0. : 1.;
}
vec3 volumetric(vec3 ro, vec3 rd, float tMax, vec2 fc) {
  // (28 samples at tier 0, 14 at tier 1; none below, which main() skips)
  int N = uTier < .5 ? 28 : 14;
  float jit = hash12(fc + uSeed * 17.31), dt = tMax / float(N);
  vec3 acc = vec3(0);
  for (int i = 0; i < 28; i++) {
    if (i >= N) break;
    vec3 s = ro + rd * ((float(i) + jit) * dt);
    if (s.y < 0.) continue;
    vec3 L = uLP - s; float dl = length(L);
    float ph = .015 + .6 * pow(max(dot(rd, L / dl), 0.), 24.);
    float occ = shadowFlat(s);
    if (uWorld > .5 && uWorld != 2.) { float tt = .05; for (int k = 0; k < 10; k++) { float h = mapWorld(s + L / dl * tt).x; if (h < .01) { occ = 0.; break; } tt += max(h, .08); if (tt > dl) break; } }
    acc += occ * ph / (1. + dl * dl * .12);
  }
  return acc * dt * uVol * uLC * .02;
}

void main() {
  vec2 fc = vUV * uRes, p = (fc - .5 * uRes) / uRes.y;
  vec3 f = normalize(uTa - uRo), r = normalize(cross(f, vec3(0, 1, 0))), u = cross(r, f);
  float cr = cos(uRoll), sr = sin(uRoll);
  vec2 q = vec2(p.x * cr - p.y * sr, p.x * sr + p.y * cr);
  vec3 ro = uRo, rd = normalize(q.x * r + q.y * u + uFov * f);
  float tHit = 1e9; int what = 0, si = 0;
  vec3 col = env(rd);
  if (uTunOn > .5) { float tt = hitTunnel(ro, rd); if (tt > 0.) { tHit = tt; what = 4; } }
  float ts = marchShape(ro, rd, tHit, uFx > 3.4 ? (uTier < .5 ? 96 : uTier < 1.5 ? 72 : 48) : uFx > 2.5 ? 56 : 36);
  if (ts > 0. && ts < tHit) { tHit = ts; what = 1; }
  for (int i = 0; i < 32; i++) { if (i >= uSphN) break; float t = hitSphere(ro, rd, uSph[i]); if (t > 0. && t < tHit) { tHit = t; what = 2; si = i; } }
  float tf = uFloorOn > .5 && rd.y < 0. ? -ro.y / rd.y : -1.;
  if (tf > 0. && tf < tHit) { tHit = tf; what = 3; }
  vec3 wi; float tw = marchWorld(ro, rd, min(tHit, 90.), uTier < .5 ? 120 : uTier < 1.5 ? 80 : uTier < 2.5 ? 56 : 40, wi);
  if (tw > 0. && tw < tHit) { tHit = tw; what = 5; }
  vec3 pos = ro + rd * tHit;
  if (what == 5) col = shadeWorld(pos, rd, tHit, wi, true);
  else if (what == 1) col = shadeShape(pos, rd);
  else if (what == 2) col = shadeSphere(pos, rd, uSph[si], uSphC[si]);
  else if (what == 3) col = shadeFloor(pos, rd, tHit);
  else if (what == 4) col = shadeTunnel(pos, rd, tHit);
  if (what != 0) col = mix(col, uSkyB, 1. - exp(-tHit * uFogD * (uFx < 2.5 ? 2.2 : 1.)));
  col += haloGlow(ro, rd, tHit) + beamGlow(ro, rd, tHit);
  col = applyPanels(col, ro, rd, tHit);
  if (uFx > 3.4 && uVol > 0. && uTier < 1.5) col += volumetric(ro, rd, min(tHit, 40.), fc);
  // the depth, for the depth of field: the nearest solid panel's, or what's behind
  float depth = what == 0 ? 400. : tHit;
  for (int i = 0; i < 6; i++) { if (i >= uPN) break; float tp; vec2 uv; if (hitPanel(i, ro, rd, tp, uv) && tp < depth && panelTex(i, uv, tp, 1.).a * uPM[i].x > .25) depth = tp; }
  vec4 ui = texture(uUI, vUV);
  col += lin(ui.rgb) * ui.a * uUIGlow;
  // (one bad pixel would spread through the bloom's mips into a black square)
  if (any(isnan(col)) || any(isinf(col))) col = vec3(0);
  oC = vec4(min(col, vec3(64.)), depth);
}`;

SHADERS.bright = `#version 300 es
precision highp float;
in vec2 vUV; out vec4 oC;
uniform sampler2D uSrc; uniform vec2 uTexel; uniform float uTh;
void main() {
  vec3 c = (texture(uSrc, vUV + uTexel * vec2(-.5, -.5)).rgb + texture(uSrc, vUV + uTexel * vec2(.5, -.5)).rgb
          + texture(uSrc, vUV + uTexel * vec2(-.5, .5)).rgb + texture(uSrc, vUV + uTexel * vec2(.5, .5)).rgb) * .25;
  float br = max(c.r, max(c.g, c.b));
  oC = vec4(c * max(br - uTh, 0.) / max(br, 1e-4), 1.);
}`;
SHADERS.down = `#version 300 es
precision highp float;
in vec2 vUV; out vec4 oC;
uniform sampler2D uSrc; uniform vec2 uTexel;
void main() {
  oC = vec4((texture(uSrc, vUV + uTexel * vec2(-1, -1)).rgb + texture(uSrc, vUV + uTexel * vec2(1, -1)).rgb
           + texture(uSrc, vUV + uTexel * vec2(-1, 1)).rgb + texture(uSrc, vUV + uTexel * vec2(1, 1)).rgb) * .25, 1.);
}`;
SHADERS.up = `#version 300 es
precision highp float;
in vec2 vUV; out vec4 oC;
uniform sampler2D uHi; uniform sampler2D uLo; uniform vec2 uTexel;
void main() {
  vec3 s = texture(uLo, vUV).rgb * 4.;
  s += (texture(uLo, vUV + uTexel * vec2(-1, 0)).rgb + texture(uLo, vUV + uTexel * vec2(1, 0)).rgb + texture(uLo, vUV + uTexel * vec2(0, -1)).rgb + texture(uLo, vUV + uTexel * vec2(0, 1)).rgb) * 2.;
  s += texture(uLo, vUV + uTexel * vec2(-1, -1)).rgb + texture(uLo, vUV + uTexel * vec2(1, -1)).rgb + texture(uLo, vUV + uTexel * vec2(-1, 1)).rgb + texture(uLo, vUV + uTexel * vec2(1, 1)).rgb;
  oC = vec4(texture(uHi, vUV).rgb + s / 16., 1.);
}`;
SHADERS.final = `#version 300 es
precision highp float;
in vec2 vUV; out vec4 oC;
uniform sampler2D uScene; uniform sampler2D uBloom; uniform sampler2D uUI;
uniform float uBloomK, uFx, uCA, uGrain, uVig, uSeed, uExposure, uFlash, uFlareK, uSat, uDof, uFocus;
uniform vec2 uSceneRes, uFlare; uniform vec3 uFlareCol, uFlashCol;
float hash12(vec2 p) { vec3 p3 = fract(vec3(p.xyx) * .1031); p3 += dot(p3, p3.yzx + 33.33); return fract((p3.x + p3.y) * p3.z); }
vec3 aces(vec3 x) { return clamp((x * (2.51 * x + .03)) / (x * (2.43 * x + .59) + .14), 0., 1.); }
float bayer4(vec2 p) { int x = int(mod(p.x, 4.)), y = int(mod(p.y, 4.)); int i = x + y * 4;
  float m[16] = float[16](0., 8., 2., 10., 12., 4., 14., 6., 3., 11., 1., 9., 15., 7., 13., 5.); return m[i] / 16. - .5; }
void main() {
  vec2 uv = vUV, d = uv - .5;
  vec3 c;
  if (uCA > 0.) c = vec3(texture(uScene, uv - d * uCA).r, texture(uScene, uv).g, texture(uScene, uv + d * uCA).b);
  else c = texture(uScene, uv).rgb;
  if (uDof > 0.) {
    // depth of field: a disc of 24 taps as wide as the circle of confusion (each tap only as far as its own blur reaches, so a
    // sharp subject doesn't smear over a blurred background)
    float z = texture(uScene, uv).a, coc = min(.016, uDof * abs(z - uFocus) / max(z, .05));
    if (coc > .0006) {
      vec3 acc = c; float ws = 1.;
      for (int i = 0; i < 24; i++) {
        float a = float(i) * 2.39996, r = sqrt((float(i) + .5) / 24.);
        vec2 o = vec2(cos(a), sin(a)) * r * coc * vec2(9. / 16., 1.);
        vec4 sm = texture(uScene, uv + o);
        float sc = min(.016, uDof * abs(sm.a - uFocus) / max(sm.a, .05)), w = smoothstep(r * coc * .6, r * coc, sc + .0004);
        acc += sm.rgb * w; ws += w;
      }
      c = acc / ws;
    }
  }
  c += texture(uBloom, uv).rgb * uBloomK;
  // a 90s lens flare: rings and hexes strung from the light through the centre
  if (uFlareK > 0.) {
    vec2 asp = vec2(16. / 9., 1.);
    for (int i = 0; i < 6; i++) {
      float f = float(i) / 5. * 1.6 - .2;
      vec2 pos = mix(uFlare, vec2(1) - uFlare, f);
      float r = .02 + .05 * fract(f * 7.31), dd = length((uv - pos) * asp);
      c += uFlareCol * uFlareK * (smoothstep(r, r * .8, dd) * .25 + exp(-dd * dd / (r * r)) * .15);
    }
    c += uFlareCol * uFlareK * .8 * exp(-length((uv - uFlare) * asp) * 9.);
  }
  c *= uExposure;
  c = aces(c);
  float g = dot(c, vec3(.299, .587, .114)); c = mix(vec3(g), c, uSat);
  c = mix(c, uFlashCol, uFlash);
  c *= 1. - uVig * dot(d, d) * 1.6;
  c = pow(c, vec3(1. / 2.2));
  if (uFx < 2.5) { vec2 px = floor(uv * uSceneRes); c = floor(c * vec3(31, 63, 31) + .5 + bayer4(px)) / vec3(31, 63, 31); }
  c += (hash12(uv * 1789.3 + uSeed) - .5) * uGrain;
  vec4 ui = texture(uUI, uv);
  c = mix(c, ui.rgb, ui.a);
  oC = vec4(c, 1.);
}`;

;
// ---- styles/demoscene/modern/engine.js ----
// modern/engine.js: the modern engine (versions A and B). A scene function returns a frame description F (camera, sky, floor,
// panels drawn with 2D canvases, an extruded shape, spheres, a tunnel or corridor, emitters, light) and draws its 2D layers;
// render(F) draws it with the WebGL scene shader, bloom and the final pass, at the era the version asks for (E.fx: 2 a late-90s 3D
// card, 3 a 2000s shader demo, 4 a modern 64k intro), with the UI layer (MC Token's scroller, the date, Softmax's HUD, labels) on
// top, and puts the result on core.js's canvas. Scenes register with mline()/msection() (below). Everything is a pure function of
// song time. STYLE.md ("The modern engine") has the frame description and the helpers.
const MOD = (() => {
  const LW = 1920, LH = 1080;
  const SCENES = {};   // key ('V2.5', 'C1', 'intro', 'outro') → scene function (t, seg, E) → F
  const FONT_T = '"Rubik Mono One"', FONT_M = '"Space Mono"';
  // ---------- canvases ----------
  // (uploaded to the GPU every frame, so they must stay on it: Chrome moves a canvas whose attribute is left unset to the CPU once it
  // judges it read back often, after which every upload is a full copy up from memory)
  const mk = (w, h) => { const c = makeCanvas(w, h); return { c, g: c.getContext('2d', { willReadFrequently: false }), w, h }; };
  const UI = mk(LW, LH);
  const PAN = [mk(2048, 1024), mk(1024, 512), mk(1024, 512)];   // the panels' three textures (a panel picks one with tex: 0..2)
  let _uiScale = 1;
  // (an older era's UI is coarser: `scale` is its share of the 1920 × 1080 frame, never more than the canvas has)
  function uiBegin(scale) {
    const w = Math.max(64, Math.round(scale < 1 ? Math.min(canvas.width, LW * scale) : canvas.width * scale)), h = Math.max(36, Math.round(w * canvas.height / canvas.width));
    if (UI.c.width !== w || UI.c.height !== h) { UI.c.width = w; UI.c.height = h; }
    _uiScale = w / LW;
    const g = UI.g; g.setTransform(1, 0, 0, 1, 0, 0); g.clearRect(0, 0, w, h); g.setTransform(_uiScale, 0, 0, _uiScale, 0, 0);
    return g;
  }
  function panel(i) { const P = PAN[i], g = P.g; g.setTransform(1, 0, 0, 1, 0, 0); g.clearRect(0, 0, P.w, P.h); P.used = true; return g; }

  // ---------- distance-field shapes (extruded in 3D by the scene shader) ----------
  // A mask canvas → an 8-bit signed distance texture (0.5 at the edge, ±RANGE texels at 0 and 1), by an exact Euclidean
  // distance transform (Felzenszwalb & Huttenlocher) on the inside and the outside.
  const RANGE = 24;
  function edt1(f, n, d, v, z) {
    let k = 0; v[0] = 0; z[0] = -Infinity; z[1] = Infinity;
    for (let q = 1; q < n; q++) {
      let s = ((f[q] + q * q) - (f[v[k]] + v[k] * v[k])) / (2 * q - 2 * v[k]);
      while (s <= z[k]) { k--; s = ((f[q] + q * q) - (f[v[k]] + v[k] * v[k])) / (2 * q - 2 * v[k]); }
      k++; v[k] = q; z[k] = s; z[k + 1] = Infinity;
    }
    k = 0;
    for (let q = 0; q < n; q++) { while (z[k + 1] < q) k++; d[q] = (q - v[k]) ** 2 + f[v[k]]; }
  }
  function edt(grid, w, h) {
    const n = Math.max(w, h), f = new Float64Array(n), d = new Float64Array(n), v = new Int32Array(n), z = new Float64Array(n + 1);
    for (let x = 0; x < w; x++) { for (let y = 0; y < h; y++) f[y] = grid[y * w + x]; edt1(f, h, d, v, z); for (let y = 0; y < h; y++) grid[y * w + x] = d[y]; }
    for (let y = 0; y < h; y++) { for (let x = 0; x < w; x++) f[x] = grid[y * w + x]; edt1(f, w, d, v, z); for (let x = 0; x < w; x++) grid[y * w + x] = d[x]; }
  }
  const SHAPES = new Map();
  function sdfFrom(mask, w, h) {
    const src = mask.getContext('2d').getImageData(0, 0, w, h).data, INF = 1e20;
    const out = new Float64Array(w * h), inn = new Float64Array(w * h);
    for (let i = 0; i < w * h; i++) { const on = src[i * 4 + 3] > 127; out[i] = on ? 0 : INF; inn[i] = on ? INF : 0; }
    edt(out, w, h); edt(inn, w, h);
    // signed distance in texels (outside positive), clamped, as floats; rows bottom to top (the texture's orientation)
    const f = new Float32Array(w * h);
    for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) { const i = y * w + x; f[(h - 1 - y) * w + x] = clamp(Math.sqrt(out[i]) - Math.sqrt(inn[i]), -RANGE * 2, RANGE * 2); }
    return f;
  }
  // The gwern.net logo, the site's own SVG path (static/img/logo/logo-smooth.svg): a blackletter fraktur capital G.
  const G_PATH = 'm 602.7,284.5 c -7.3,-20.2 -19.5,-38 -38.1,-48.5 -21.2,-12 -48.5,-12.1 -69.8,-0.3 14.1,-14.8 24.4,-34.4 27.4,-54.7 3.3,-22.3 0.3,-48.6 11.9,-65.2 17.3,-24.8 57.5,-24.5 74.4,-49.5 -17.8,2.5 -38.2,2.7 -53.3,3.6 -21.7,1.3 -40.1,4.8 -50.1,19.8 -11.4,17.1 -9.1,39.4 -9.8,59.9 -1.4,40 -16,77.2 -45.4,104 5.1,7.1 10.2,14.1 15.3,21.2 14.9,-8.5 30.1,-17.2 46.9,-20.7 16.8,-3.5 35.7,-1.2 48.5,10.2 11.9,10.6 16.7,27.1 19,42.8 8,54.2 -9.2,114.2 -52.5,147.8 -23.9,18.5 -53.8,27.9 -84,28.5 -36.1,0.8 -72.9,-12.7 -99.6,-37.3 -38.1,-35.1 -51.1,-89.5 -53.1,-141.2 -2.1,-55.5 8.6,-114.1 42.8,-157.9 7.5,-9.6 16.1,-18.8 27.5,-23.2 11.3,-4.4 25.8,-2.9 33.7,6.3 -20.2,20.4 -40.7,42.3 -50.1,69.4 12.2,38.8 24.4,77.6 36.6,116.3 7.3,23.4 14.2,50.3 1.9,71.5 -5.6,9.6 -14.6,16.8 -24,22.9 29.5,-3.4 60.7,-9.1 83.9,-27.6 12.6,-10 22.6,-23.7 26.2,-39.4 4.9,-21.1 -1.8,-42.9 -8.7,-63.5 -8.9,-26.6 -17.8,-53.3 -26.7,-79.9 -3.2,-9.5 -6.3,-20.3 -2.2,-29.4 3.8,-8.4 12.6,-13.5 18.2,-20.8 6.8,-9 8.7,-21.2 5,-31.8 -18.3,18.3 -36.7,36.6 -55,54.9 -16.1,-20.9 -38.9,-39.2 -65.1,-41.9 -30.1,-3.1 -58.4,15.6 -78.4,38.4 -63.1,72.2 -71.9,187.7 -20.2,268.5 51.7,80.8 159.7,121.6 251.1,94.7 55.5,-16.3 104.1,-57.4 126.4,-110.8 16.2,-38.3 18.9,-82.8 5.2,-122.1 z';
  const G_BOX = [216.94, 66.3, 394.583, 464.467];
  function shapeG() {
    let S = SHAPES.get('G'); if (S) return S;
    const w = 1024, h = Math.round(1024 * G_BOX[3] / G_BOX[2]), pad = RANGE + 8, m = makeCanvas(w, h), g = m.getContext('2d', { willReadFrequently: true });
    const k = Math.min((w - 2 * pad) / G_BOX[2], (h - 2 * pad) / G_BOX[3]);
    g.setTransform(k, 0, 0, k, (w - G_BOX[2] * k) / 2 - G_BOX[0] * k, (h - G_BOX[3] * k) / 2 - G_BOX[1] * k);
    g.fill(new Path2D(G_PATH));
    S = { img: sdfFrom(m, w, h), w, h, aspect: w / h, mask: m };
    SHAPES.set('G', S);
    return S;
  }
  // Any silhouette as a shape: draw(g, w, h) fills it in white on a w × h mask (w = 1024; h from the aspect, width / height).
  function shapePath(key, draw, aspect = 1) {
    let S = SHAPES.get('P|' + key); if (S) return S;
    const w = 1024, h = Math.round(1024 / aspect), m = makeCanvas(w, h), g = m.getContext('2d', { willReadFrequently: true });
    g.fillStyle = '#fff'; draw(g, w, h);
    S = { img: sdfFrom(m, w, h), w, h, aspect: w / h, mask: m };
    SHAPES.set('P|' + key, S);
    return S;
  }
  // A heart, the classic two lobes and a point (for V1.6's callback and 4o's heart).
  const shapeHeart = () => shapePath('heart', (g, w, h) => {
    const pad = RANGE + 10, s = Math.min(w, h) - 2 * pad, x = w / 2, y = pad + s * .26;
    g.beginPath(); g.moveTo(x, y);
    g.bezierCurveTo(x - s * .08, y - s * .22, x - s * .5, y - s * .26, x - s * .5, y + s * .06);
    g.bezierCurveTo(x - s * .5, y + s * .36, x - s * .12, y + s * .5, x, y + s * .72);
    g.bezierCurveTo(x + s * .12, y + s * .5, x + s * .5, y + s * .36, x + s * .5, y + s * .06);
    g.bezierCurveTo(x + s * .5, y - s * .26, x + s * .08, y - s * .22, x, y);
    g.fill();
  }, 1);
  function shapeText(str, font = FONT_T) {
    let S = SHAPES.get('T|' + str); if (S) return S;
    const tmp = makeCanvas(8, 8).getContext('2d'); tmp.font = `200px ${font}`;
    const tw = Math.ceil(tmp.measureText(str).width), pad = RANGE + 8, w = Math.min(2048, tw + 2 * pad), h = 200 + 2 * pad;
    const m = makeCanvas(w, h), g = m.getContext('2d', { willReadFrequently: true });
    const k = Math.min(1, (w - 2 * pad) / tw);
    g.font = `${Math.round(200 * k)}px ${font}`; g.textAlign = 'center'; g.textBaseline = 'middle'; g.fillText(str, w / 2, h / 2 + 8);
    S = { img: sdfFrom(m, w, h), w, h, aspect: w / h };
    SHAPES.set('T|' + str, S);
    return S;
  }

  // ---------- small maths ----------
  const v3 = (x, y, z) => [x, y, z];
  const add = (a, b) => [a[0] + b[0], a[1] + b[1], a[2] + b[2]], sub = (a, b) => [a[0] - b[0], a[1] - b[1], a[2] - b[2]], mul = (a, k) => [a[0] * k, a[1] * k, a[2] * k];
  const mix3 = (a, b, k) => [lerp(a[0], b[0], k), lerp(a[1], b[1], k), lerp(a[2], b[2], k)];
  const hex = h => [1, 3, 5].map(i => (parseInt(h.slice(i, i + 2), 16) / 255) ** 2.2);   // (linear light)
  // rotation matrices (column-major, as uniformMatrix3fv wants): about y, then x
  function rotYX(ay, ax = 0, az = 0) {
    const R = rot3(ax, ay, az);   // kit.js: row-major Rz·Ry·Rx
    return [R[0], R[3], R[6], R[1], R[4], R[7], R[2], R[5], R[8]];
  }
  const transpose3 = m => [m[0], m[3], m[6], m[1], m[4], m[7], m[2], m[5], m[8]];
  // project a world point to screen uv (0..1, y up) for a camera
  function project(F, p) {
    const f = norm(sub(F.ta, F.ro)), r = norm(cross(f, [0, 1, 0])), u = cross(r, f), d = sub(p, F.ro);
    const z = dot(d, f); if (z <= 0) return null;
    return [.5 + dot(d, r) / z * F.fov * LH / LW, .5 + dot(d, u) / z * F.fov];
  }
  const dot = (a, b) => a[0] * b[0] + a[1] * b[1] + a[2] * b[2], cross = (a, b) => [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]];
  const norm = a => { const l = Math.hypot(...a) || 1; return [a[0] / l, a[1] / l, a[2] / l]; };

  // ---------- UI: type, the modern scroller, the date, Softmax's HUD ----------
  function text(g, str, x, y, o = {}) {
    g.save();
    g.font = `${o.size ?? 28}px ${o.font ?? FONT_M}`; g.textAlign = o.align ?? 'left'; g.textBaseline = o.base ?? 'alphabetic';
    if (o.spacing) g.letterSpacing = o.spacing + 'px';
    const s = o.n !== undefined ? [...str].slice(0, o.n).join('') : str;
    if (o.stroke) { g.lineJoin = 'round'; g.lineWidth = o.stroke; g.strokeStyle = o.strokeCol ?? 'rgba(4,4,12,.85)'; g.strokeText(s, x, y); }
    g.fillStyle = o.color ?? '#fff'; g.globalAlpha = o.alpha ?? 1; g.fillText(s, x, y);
    g.restore();
  }
  const chrome = (g, y0, y1, stops) => { const gr = g.createLinearGradient(0, y0, 0, y1); stops.forEach((c, i) => gr.addColorStop(i / (stops.length - 1), c)); return gr; };
  // MC Token's verse, one line of type scrolled so the word being rapped sits at the reading point (the retro kit's spline).
  const _scr = new Map();
  function scrollLayout(sec, g, size) {
    const key = sec + '|' + size;
    let V = _scr.get(key); if (V && V.lines === LINES) return V;
    g.save(); g.font = `${size}px ${FONT_T}`;
    const sp = g.measureText(' ').width * .9, sepW = size * 1.6, toks = [];
    let x = 0;
    LINES.filter(l => l.sec === sec).forEach((ln, li) => {
      if (li) { toks.push({ sep: true, x0: x, x1: x + sepW }); x += sepW; }
      wordsOf(ln).forEach(w => {
        const s = w.w.toUpperCase(), chars = [...s].map(c => ({ c, w: g.measureText(c).width }));
        const ww = chars.reduce((a, c) => a + c.w, 0);
        toks.push({ s, chars, x0: x, x1: x + ww, t0: w.t0, t1: w.t1 }); x += ww + sp;
      });
    });
    g.restore();
    const ts = [], xs = [];
    toks.filter(k => !k.sep).forEach(k => { const tt = Math.max(k.t0, (ts.at(-1) ?? -1e9) + .02); ts.push(tt); xs.push(Math.max((k.x0 + k.x1) / 2, xs.at(-1) ?? -1e9)); });
    V = { lines: LINES, toks, X: monotone(ts, xs) };
    _scr.set(key, V);
    return V;
  }
  function scroller(g, sec, t, o = {}) {
    const size = o.size ?? 58, V = scrollLayout(sec, g, size), read = o.read ?? LW * .42, X = V.X(t) - read, by = o.y ?? 985;
    let cur = -1; V.toks.forEach((k, i) => { if (!k.sep && k.t0 <= t) cur = i; });
    const amp = o.amp ?? 9, v = vox(t);
    // his scope, under the type
    g.save(); g.strokeStyle = 'rgba(90,230,255,.85)'; g.lineWidth = 2.2; g.beginPath();
    const note = voxNote(t) || 50, fq = .02 + (note - 40) * .0012;
    for (let x = 0; x <= LW; x += 6) { const env = Math.sin(Math.PI * x / LW), y = by + 34 + v * 26 * env * (Math.sin(x * fq - t * 31) * .6 + Math.sin(x * fq * 2.03 + t * 17) * .3); x ? g.lineTo(x, y) : g.moveTo(x, y); }
    g.stroke(); g.restore();
    g.save(); g.font = `${size}px ${FONT_T}`; g.textBaseline = 'alphabetic'; g.lineJoin = 'round';
    const sung = chrome(g, by - size, by, ['#ffffff', '#9ef4ff', '#18b8ea', '#0b5c9e']);
    V.toks.forEach((k, i) => {
      if (k.x1 - X < -40 || k.x0 - X > LW + 40) return;
      if (k.sep) { const cx = (k.x0 + k.x1) / 2 - X, cy = by - size * .38 + amp * Math.sin(cx * .006 - t * 2.2); g.fillStyle = '#5ae6ff'; g.beginPath(); g.moveTo(cx, cy - 12); g.lineTo(cx + 12, cy); g.lineTo(cx, cy + 12); g.lineTo(cx - 12, cy); g.fill(); return; }
      const state = i < cur ? 0 : i === cur && t < k.t1 + .15 ? 1 : i === cur ? 0 : 2;
      const pop = state === 1 ? Math.exp(-(t - k.t0) * 10) * 10 : 0;
      let x = k.x0 - X;
      for (const ch of k.chars) {
        const y = by + amp * Math.sin(x * .006 - t * 2.2) + 4 * v * Math.sin(x * .05 - t * 9) - pop;
        g.lineWidth = 8; g.strokeStyle = 'rgba(2,4,14,.8)'; g.strokeText(ch.c, x, y);
        g.fillStyle = state === 0 ? sung : state === 1 ? '#ffffff' : 'rgba(150,160,205,.42)';
        g.fillText(ch.c, x, y);
        x += ch.w;
      }
    });
    g.restore();
  }
  function dateSeg(t) { let cur = null, since = 0; for (const s of SEGS) { if (s.start > t) break; if (s.date && s.date !== cur) { cur = s.date; since = s.start; } } return cur && { text: cur, age: t - since }; }
  function datePlate(g, t) {
    const d = dateSeg(t); if (!d) return;
    const m = d.text.match(/^(.*?)\s*(\d{4})$/), md = m ? m[1] : d.text, yr = m ? m[2] : '', k = easeOut(clamp(d.age / .2));
    g.save();
    g.fillStyle = 'rgba(8,10,22,.62)'; g.strokeStyle = 'rgba(160,200,255,.28)'; g.lineWidth = 1.5;
    g.beginPath(); g.roundRect(1650, 26, 240, 100, 10); g.fill(); g.stroke();
    text(g, md, 1866, 62, { size: 26, align: 'right', color: '#9fb4e8' });
    text(g, yr, 1866, 110 - (1 - k) * 12, { size: 44, font: FONT_T, align: 'right', color: '#ffffff', alpha: .4 + .6 * k });
    g.restore();
  }
  // Softmax's HUD: her voice as a softmax over pitch, with a note axis, her note named over the peak and her melody's trail rising
  // above it; behind, the mix's own spectrum.
  const NOTE_NAMES = ['C', 'C#', 'D', 'D#', 'E', 'F', 'F#', 'G', 'G#', 'A', 'A#', 'B'];
  const N0 = 52, NB = 26;   // bars: MIDI notes E3 … F5 (her chorus range)
  const spec = new Float32Array(16);
  function voiceNote(t) {
    // her pitch, smoothed over the voiced frames of the last 80 ms and folded into the bars' range (octave errors)
    let s = 0, c = 0;
    for (let k = 0; k < 5; k++) { let q = voxNote(t - k * .02); if (!q) continue; while (q < N0) q += 12; while (q > N0 + NB - 1) q -= 12; s += q; c++; }
    return c ? s / c : 0;
  }
  function softmaxHUD(g, t, o = {}) {
    const x0 = o.x0 ?? 150, x1 = o.x1 ?? 1770, base = o.y ?? 1040, hMax = o.h ?? 150, bw = (x1 - x0) / NB, lv = o.level ?? 1;
    g.save(); g.globalAlpha = lv;
    // the band: the mix's spectrum, 16 bands spread across
    spectrum(t, spec);
    for (let i = 0; i < 32; i++) {
      const f = i / 31 * 15, a = spec[Math.floor(f)], b = spec[Math.min(15, Math.floor(f) + 1)], v = lerp(a, b, f - Math.floor(f)) ** 1.6;
      const bx = x0 + i * (x1 - x0) / 32, h = 8 + v * hMax * 1.05;
      g.fillStyle = `rgba(40,190,255,${.16 + .3 * v})`; g.fillRect(bx + 3, base - h, (x1 - x0) / 32 - 6, h);
    }
    // her voice: a softmax over pitch, sharp when she sings loud
    const vv = vox(t), note = voiceNote(t), peak = note ? note - N0 : (NB - 1) / 2, temp = lerp(7, 1.2, clamp(vv * 1.3));
    const z = [], e = []; let sum = 0;
    for (let i = 0; i < NB; i++) { z.push(-Math.abs(i - peak) * 1.3); const q = Math.exp(z[i] / temp); e.push(q); sum += q; }
    for (let i = 0; i < NB; i++) {
      const p = e[i] / sum, h = Math.max(3, hMax * p * (2.2 + vv)), bx = x0 + i * bw;
      const gr = g.createLinearGradient(0, base - h, 0, base); gr.addColorStop(0, i === Math.round(peak) && note ? '#ffffff' : '#ff8fd6'); gr.addColorStop(1, '#a0147a');
      g.fillStyle = gr; g.fillRect(bx + 4, base - h, bw - 8, h);
      // the note axis
      const n = N0 + i, nm = NOTE_NAMES[n % 12];
      text(g, nm === 'C' ? 'C' + (Math.floor(n / 12) - 1) : nm, bx + bw / 2, base + 22, { alpha: lv, size: nm === 'C' ? 17 : 13, align: 'center', color: nm === 'C' ? '#ffd2f0' : 'rgba(255,200,240,.55)' });
    }
    // her melody, as a piano roll rising above the bars: a block per 30th of a second at the note she sang, fading as it rises
    for (let k = 0; k < 64; k++) {
      const tk = t - k / 30, n = voiceNote(tk), a = vox(tk); if (!n || a < .08) continue;
      const bx = x0 + (Math.round(n) - N0) * bw, y = base - hMax * .9 - 16 - k * 4;
      g.fillStyle = `rgba(255,${k ? 110 : 230},${k ? 205 : 245},${(1 - k / 64) * (.35 + .65 * clamp(a * 1.5))})`;
      g.fillRect(bx + bw * .18, y, bw * .64, 4.2);
    }
    if (note && vv > .12) {
      const px = x0 + (note - N0 + .5) * bw, n = Math.round(note), nm = NOTE_NAMES[n % 12] + (Math.floor(n / 12) - 1);
      text(g, nm, px, base - hMax * .9 - 30, { alpha: lv, size: 30, font: FONT_T, align: 'center', color: '#ffffff', stroke: 6 });
      if (o.word) text(g, o.word.toUpperCase(), px + 70, base - hMax * .9 - 34, { alpha: lv, size: 22, font: FONT_T, color: '#ff9ad8', stroke: 5 });
    }
    g.restore();
  }

  // ---------- 2D helpers for panels and UI ----------
  // DJ Clawd, crisp, in a 2D canvas: (x, y) = the ground under his middle; u = the size of one of his pixels. o: eyes ('open' |
  // 'happy' | 'closed' | 'wide'), aL/aR (arm raise, −1..1), hop, phones (default true), wave (right arm waving, 0..1 phase), tag
  // (a label on his headphone cups, like '5.5'), col (body colour).
  function clawd(g, x, y, u, o = {}) {
    const body = o.col ?? '#d97757', dk = '#9b3114', lit = '#ffb45c', ink = '#07060f', r = (X, Y, w, h, c) => { g.fillStyle = c; g.fillRect(X, Y, w, h); };
    y -= o.hop ?? 0;
    const bw = 10 * u, bh = 6 * u, legH = 2 * u, bx = x - 5 * u, by = y - legH - bh;
    [-3.6, -1.4, 1.4, 3.6].forEach(lx => r(x + lx * u - u / 2, y - legH, u, legH, dk));
    const arm = (side, a) => r(side < 0 ? bx - 2 * u : bx + bw, by + 2.2 * u - a * 2 * u, 2 * u, u + (a > .3 ? u : 0), body);
    arm(-1, o.aL ?? 0);
    if (o.wave !== undefined) { const a = .8 + .5 * Math.sin(o.wave * TAU); r(bx + bw, by + 2.2 * u - a * 2.2 * u, u, 1.6 * u, body); r(bx + bw + u, by + 1.4 * u - a * 2.6 * u, u, 1.4 * u, body); }
    else arm(1, o.aR ?? 0);
    r(bx, by, bw, bh, body); r(bx, by, bw, u / 2, lit); r(bx, by, u / 2, bh, lit); r(bx + bw - u / 2, by, u / 2, bh, dk); r(bx, by + bh - u / 2, bw, u / 2, dk);
    const eyes = o.eyes ?? 'open';
    for (const side of [-1, 1]) {
      const ex = x + side * 2.3 * u - u / 2, ey = by + 1.3 * u;
      if (eyes === 'open') r(ex, ey, u, 1.6 * u, ink);
      else if (eyes === 'wide') { r(ex - u * .3, ey - u * .3, u * 1.6, 2.2 * u, '#fff'); r(ex, ey, u, 1.6 * u, ink); }
      else if (eyes === 'happy') { r(ex - u / 2, ey + u / 2, 2 * u, u / 2, ink); r(ex - u / 2, ey + u, u / 2, u / 2, ink); r(ex + u, ey + u, u / 2, u / 2, ink); }
      else r(ex - u / 2, ey + 1.1 * u, 2 * u, u / 2, ink);
    }
    if (o.phones !== false) {
      r(bx - .6 * u, by - 1.4 * u, bw + 1.2 * u, .6 * u, '#8592c6'); r(bx - .6 * u, by - 1.4 * u, .6 * u, 1.8 * u, '#8592c6'); r(bx + bw, by - 1.4 * u, .6 * u, 1.8 * u, '#8592c6');
      for (const side of [-1, 1]) { const cx = side < 0 ? bx - 1.4 * u : bx + bw - .2 * u; r(cx, by + .3 * u, 1.6 * u, 2.2 * u, '#3c4878'); r(cx + .5 * u, by + .9 * u, .6 * u, .9 * u, '#8af2ff'); }
      if (o.tag) { g.save(); g.font = `${Math.round(u * 1.1)}px ${FONT_M}`; g.fillStyle = '#ffe28a'; g.textAlign = 'center'; g.fillText(o.tag, bx + bw + .6 * u, by + 3.4 * u); g.restore(); }
    }
  }
  // The demo's own 8×8 font (font.js), drawn crisp at any pixel size: an homage to the 1996 part in the modern one.
  function bitmap(g, str, x, y, px, color, o = {}) {
    const chars = [...String(str)], w = chars.reduce((a, c) => a + (glyph(c).w + 1) * px, -px);
    let cx = o.align === 'center' ? x - w / 2 : o.align === 'right' ? x - w : x;
    g.fillStyle = color;
    for (const ch of chars) { const G = glyph(ch); for (let yy = 0; yy < 8; yy++) for (let xx = 0; xx < G.w; xx++) if (G.bits[yy * G.w + xx]) g.fillRect(cx + xx * px, y + yy * px, px, px); cx += (G.w + 1) * px; }
    return w;
  }

  // ---------- render ----------
  const DEF = {
    fx: 4, res: 1, uiRes: 1, ro: [0, 1.5, 8], ta: [0, 1.5, 0], fov: 1.6, roll: 0,
    skyA: '#05060e', skyB: '#0c1024', acc: '#ff3aa6', fog: .02, sky: null, floor: true, floorCol: '#020206', grid: 0,
    panels: [], shape: null, halo: null, beam: null, spheres: [], sphCol: '#e8b04a', tunnel: null,
    light: { p: [0, 3, -4], c: '#ffffff', k: 4, vol: 0 }, uiGlow: .35, flash: 0, exposure: 1, sat: 1,
  };
  const ERA = {
    2: { res: 1 / 3, uiRes: .5, bloom: 0, th: 1, ca: 0, grain: 0, vig: .2, flare: .8, sat: 1.25 },
    3: { res: .5, uiRes: .75, bloom: 1.1, th: .45, ca: 0, grain: 0, vig: .35, flare: 0, sat: 1.25 },
    4: { res: 1, uiRes: 1, bloom: .45, th: .9, ca: .0035, grain: .035, vig: .9, flare: 0, sat: 1 },
  };
  function eraMix(fx) { const a = Math.floor(clamp(fx, 2, 4)), b = Math.min(4, a + 1), k = fx - a, A = ERA[a], B = ERA[b]; const o = {}; for (const key in A) o[key] = lerp(A[key], B[key], k); return o; }
  let ready = false;
  // warm(): create the context and compile every program now (at start-up, before the first frame is asked for), so that the first
  // modern frame doesn't stall on the scene shader's compile mid-song.
  function warm() {
    if (ready) return;
    for (const k of ['scene', 'bright', 'down', 'up', 'final']) GL.program(k, SHADERS[k]);
    GL.size(canvas.width, canvas.height);
    // one tiny draw of each, so the driver finishes linking now
    const t = GL.target('warm', 8, 8), px = new Uint8Array(4);
    for (const k of ['scene', 'bright', 'down', 'up', 'final']) GL.pass(GL.program(k), k === 'final' ? null : t, {}, {});
    GL.gl.readPixels(0, 0, 1, 1, GL.gl.RGBA, GL.gl.UNSIGNED_BYTE, px);
    ready = true;
  }
  function render(F0) {
    const F = { ...DEF, ...F0 }, E = eraMix(F.fx);
    const modern = F.fx > 3.4, res = (F.res ?? E.res) * (modern ? resK : 1);
    const Wd = canvas.width, Hd = canvas.height;
    GL.size(Wd, Hd);
    warm();
    // (an older era's picture is its grid in the 1920 × 1080 frame, the 1998 card's 640 × 360, say, but never finer than the
    // canvas has pixels: a player shown small draws at its own size, not a third of it; the 2026 era's is a share of the canvas)
    const sw = Math.max(32, Math.round(F.fx > 3.4 ? Wd * res : Math.min(Wd, LW * res))), sh = Math.max(18, Math.round(sw * Hd / Wd));
    const T = { ui: GL.texture('ui', UI.c) };
    PAN.forEach((P, i) => { T['p' + i] = P.used ? GL.texture('p' + i, P.c, { mipmap: true }) : GL.getTexture('p' + i) ?? GL.texture('p' + i, P.c); P.used = false; });
    let shape = null;
    if (F.shape) {
      const S = F.shape.src;
      shape = GL.textureF('shape:' + F.shape.key, S.w, S.h, S.img);
    }
    let tun = null;
    // (a tunnel's canvas is uploaded once per key and canvas; `dirty: true` re-uploads one that's redrawn per frame)
    if (F.tunnel) {
      const k = 'tun:' + F.tunnel.key, had = GL.getTexture(k);
      tun = had && had.src === F.tunnel.src && !F.tunnel.dirty ? had : GL.texture(k, F.tunnel.src, { repeat: true, mipmap: true });
      tun.src = F.tunnel.src;
    }
    const scene = GL.target('scene', sw, sh);
    const passes = () => {
    const P = F.panels.slice(0, 6);
    const pc = new Float32Array(18), pu = new Float32Array(18), pv = new Float32Array(18), pm = new Float32Array(24);
    P.forEach((p, i) => { pc.set(p.c, i * 3); pu.set(p.u, i * 3); pv.set(p.v, i * 3); pm.set([p.alpha ?? 1, p.gain ?? 1.6, p.glass ?? 1, p.tex ?? Math.min(i, 2)], i * 4); });
    // spheres: [x, y, z, r] or [x, y, z, r, '#colour', kind] (kind: true = glass, 'glow' = emissive)
    const sph = new Float32Array(128), sphc = new Float32Array(128), sc0 = hex(F.sphCol);
    F.spheres.slice(0, 32).forEach((s, i) => { sph.set(s.slice(0, 4), i * 4); sphc.set([...(s[4] ? hex(s[4]) : sc0), s[5] === 'glow' ? 2 : s[5] ? 1 : 0], i * 4); });
    const sd = F.shape || {};
    const R = sd.rot ?? rotYX(0);
    const L = F.light;
    GL.pass(GL.program('scene'), scene, {
      uRes: [sw, sh], uT: T0, uFx: F.fx, uSeed: (T0 * 60) % 997,
      uRo: F.ro, uTa: F.ta, uFov: F.fov, uRoll: F.roll,
      uSkyA: hex(F.skyA), uSkyB: hex(F.skyB), uAcc: hex(F.acc), uFogD: F.fog,
      uFloorOn: F.floor ? 1 : 0, uGrid: F.grid, uFloorCol: hex(F.floorCol),
      uFloorMode: { checker: 1, water: 2 }[F.floorMode] ?? 0, uFloorTile: F.floorTile ?? 1, uWater: F.water ?? .06, uFloorCol2: hex(F.floorCol2 ?? '#ffffff'), uFloorOff: F.floorOff ?? [0, 0],
      uSkyMode: { plasma: 1, stars: 2, rays: 3 }[F.sky?.mode] ?? 0, uSkyK: F.sky?.k ?? 1, uSkyT: F.sky?.phase ?? T0 * (F.sky?.k ?? 1), uSkyC: hex(F.sky?.col ?? '#ffffff'),
      uPN: { i: P.length }, uPC: { v3: pc }, uPU: { v3: pu }, uPV: { v3: pv }, uPM: { v4: pm },
      uShOn: F.shape ? 1 : 0, uShP: sd.p ?? [0, 0, 0], uShR: { m3: R }, uShRi: { m3: transpose3(R) }, uShS: sd.s ?? [1, 1, .1],
      uShRange: RANGE * 2, uShTex: F.shape ? [F.shape.src.w, F.shape.src.h] : [1, 1], uShCol: hex(sd.col ?? '#101014'), uShRim: hex(sd.rim ?? '#ffb040'), uShMetal: sd.metal ?? 1,
      uShSplit: sd.split ? [sd.split.gap ?? 0, sd.split.ang ?? 0, 1, sd.split.amp ?? .12] : [0, 0, 0, 0],
      uHalo: F.halo ? [F.halo.R, F.halo.r, F.halo.k, 1] : [0, 0, 0, 0], uHaloP: F.halo?.p ?? [0, 0, 0], uHaloN: F.halo?.n ?? [0, 1, 0], uHaloCol: hex(F.halo?.col ?? '#ffd27a'),
      uBeam: F.beam ? [F.beam.x, F.beam.z, F.beam.r, F.beam.k] : [0, 0, 0, 0], uBeamY: F.beam ? [F.beam.y0, F.beam.y1] : [0, 0], uBeamTop: F.beam ? [F.beam.x1 ?? F.beam.x, F.beam.z1 ?? F.beam.z] : [0, 0], uBeamCol: hex(F.beam?.col ?? '#ff4fb4'),
      uSphN: { i: Math.min(32, F.spheres.length) }, uSph: { v4: sph }, uSphC: { v4: sphc },
      uTunOn: F.tunnel ? 1 : 0, uTunR: F.tunnel?.r ?? 3, uTunScroll: F.tunnel?.scroll ?? 0, uTunTwist: F.tunnel?.twist ?? 0, uTunCol: F.tunnel?.col ? mul(hex(F.tunnel.col), F.tunnel.gain ?? 1) : [1, 1, 1],
      uTunMode: F.tunnel?.box ? 1 : 0, uTunBox: F.tunnel?.box ?? [1, 1], uTunFloor: hex(F.tunnel?.floorCol ?? '#303030'), uTunCeil: hex(F.tunnel?.ceilCol ?? '#202020'),
      uLP: L.p, uLC: mul(hex(L.c), L.k ?? 4), uVol: L.vol ?? 0,
      uWorld: F.world && F.fx > 3.4 ? { hall: 1, fractal: 2, city: 3, gates: 4 }[F.world.kind] : 0, uWT: F.world?.t ?? T0, uWP: F.world?.p ?? [1, 1, 1, 1],
      uWCol: hex(F.world?.col ?? '#1a1a22'), uWCol2: hex(F.world?.glowCol ?? '#ffffff'), uWPos: F.world?.at ?? [0, 0, 0], uWMetal: F.world?.metal ?? .6,
      uPool: modern && tier < 3 ? F.pool ?? .6 : 0, uTier: modern ? tier : 0,
      uUIGlow: F.uiGlow,
    }, { uTex0: T.p0, uTex1: T.p1, uTex2: T.p2, uShape: shape ?? T.ui, uTunTex: tun ?? T.ui, uUI: T.ui });
    // bloom: a threshold, three halvings and a tent back up
    let bloom = scene;
    if (E.bloom > .01) {
      const b1 = GL.target('b1', sw / 2, sh / 2), b2 = GL.target('b2', sw / 4, sh / 4), b3 = GL.target('b3', sw / 8, sh / 8), b4 = GL.target('b4', sw / 16, sh / 16);
      GL.pass(GL.program('bright'), b1, { uTexel: [1 / sw, 1 / sh], uTh: E.th }, { uSrc: scene });
      GL.pass(GL.program('down'), b2, { uTexel: [1 / b1.w, 1 / b1.h] }, { uSrc: b1 });
      GL.pass(GL.program('down'), b3, { uTexel: [1 / b2.w, 1 / b2.h] }, { uSrc: b2 });
      GL.pass(GL.program('down'), b4, { uTexel: [1 / b3.w, 1 / b3.h] }, { uSrc: b3 });
      const u3 = GL.target('u3', b3.w, b3.h), u2 = GL.target('u2', b2.w, b2.h), u1 = GL.target('u1', b1.w, b1.h);
      GL.pass(GL.program('up'), u3, { uTexel: [1 / b4.w, 1 / b4.h] }, { uHi: b3, uLo: b4 });
      GL.pass(GL.program('up'), u2, { uTexel: [1 / u3.w, 1 / u3.h] }, { uHi: b2, uLo: u3 });
      GL.pass(GL.program('up'), u1, { uTexel: [1 / u2.w, 1 / u2.h] }, { uHi: b1, uLo: u2 });
      bloom = u1;
    }
    const fl = F.flarePos ?? [.5, .7];
    // (an older era at reduced resolution shows its pixels: nearest-neighbour up to the screen)
    const pix = F.fx < 3.95 && sw < Wd - 1, gl = GL.gl;
    const filt = (tex, f) => { gl.bindTexture(gl.TEXTURE_2D, tex); gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, f); gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, f); };
    if (pix) { filt(scene.tex, gl.NEAREST); filt(T.ui.tex, gl.NEAREST); }
    GL.pass(GL.program('final'), null, {
      uBloomK: E.bloom, uFx: F.fx, uCA: E.ca, uGrain: E.grain, uVig: E.vig, uSeed: (T0 * 60) % 991, uExposure: F.exposure, uFlash: F.flash,
      uFlashCol: hex(F.flashCol ?? '#ffffff').map(v => v ** (1 / 2.2)), uFlareK: E.flare * (F.flare ?? 0), uFlare: fl, uFlareCol: hex(F.flareCol ?? '#ffd9a0'), uSat: E.sat * F.sat, uSceneRes: [sw, sh],
      uDof: modern && tier < 1 && F.dof ? F.dof.k ?? .02 : 0, uFocus: F.dof?.focus ?? 8,
    }, { uScene: scene, uBloom: bloom, uUI: T.ui });
    if (pix) { filt(scene.tex, gl.LINEAR); filt(T.ui.tex, gl.LINEAR); }
    };
    passes(); lastPasses = passes; usedGL = true; last = { fx: F.fx, w: sw, h: sh };
    ctx.save(); ctx.setTransform(1, 0, 0, 1, 0, 0); ctx.globalAlpha = 1; ctx.globalCompositeOperation = 'source-over';
    ctx.drawImage(GL.canvas(), 0, 0, Wd, Hd);
    ctx.restore();
  }
  let T0 = 0, lastPasses = null;
  // Quality levels, which the page steps through (see wire.js's setQuality): the 2026 era's shader tier (0 everything; 1 no depth of
  // field, fewer god-ray samples and march steps, no ambient occlusion; 2 no god rays or soft shadows, a simpler fractal; 3 no
  // light pool or reflected set either) and, last, its picture's resolution. The UI layer (the scroller, the date, Softmax's HUD,
  // any type drawn on it) is the canvas's full size at every level. Level 0 is the video as designed.
  const LEVELS = [[0, 1], [1, 1], [2, 1], [3, 1], [3, .75], [3, .5]];
  let level = 0, tier = 0, resK = 1, usedGL = false, last = null;
  function setLevel(l) { level = clamp(Math.round(l), 0, LEVELS.length - 1); [tier, resK] = LEVELS[level]; }
  // (the GPU's work for the frame just drawn, finished: so that the page's measure of a frame includes it)
  function finish() { if (!usedGL) return; usedGL = false; const px = new Uint8Array(4); GL.gl.readPixels(0, 0, 1, 1, GL.gl.RGBA, GL.gl.UNSIGNED_BYTE, px); }
  const setT = t => { T0 = t; };
  // gpuBench(n): re-run the last frame's GL passes n times, finishing each: the GPU's share of a frame, in ms.
  function gpuBench(n = 20) {
    const gl = GL.gl, px = new Uint8Array(4);
    lastPasses(); gl.readPixels(0, 0, 1, 1, gl.RGBA, gl.UNSIGNED_BYTE, px);
    const a = performance.now();
    for (let i = 0; i < n; i++) { lastPasses(); gl.readPixels(0, 0, 1, 1, gl.RGBA, gl.UNSIGNED_BYTE, px); }
    return (performance.now() - a) / n;
  }
  return { render, warm, setT, gpuBench, setLevel, finish, level: () => level, tier: () => tier, last: () => last, project, clawd, bitmap, SCENES, uiBegin, panel, PAN, UI, text, chrome, scroller, datePlate, softmaxHUD, shapeG, shapeText, shapePath, shapeHeart, rotYX, v3, add, sub, mul, mix3, norm, hex, eraMix, ERA, FONT_T, FONT_M, LW, LH };
})();
// mline('V2', 5, (t, seg, E) => F): the modern scene for verse 2, line 5; msection('C1', fn): for a whole section.
// E = { fx, res, uiRes }: the era the version draws this window at (return fx: E.fx, res: E.res in F).
const mline = (sec, n, fn) => { MOD.SCENES[`${sec}.${n}`] = fn; };
const msection = (key, fn) => { MOD.SCENES[key] = fn; };

;
// ---- styles/demoscene/modern/m00_intro.js ----
// modern/m00_intro.js: the intro (the NFO, the crew, the build) in the modern engine (version B only; version A's intro is the 1996 engine).
// The demo boots as a modern 64k intro that keeps the rituals: the release's NFO prints on a big glass terminal while Softmax sings
// the teaser a cappella, each word printed big in the demo's own 8×8 font on a pane in front; on "can't contain it" the terminal
// strains, the exponential climbs out of the banner and through its frame, and on "it!" the mode switches into the 3D demo. On the
// hit, FRONTIER CREW drops in and the crew screen lights DJ Clawd, Softmax and MC Token one per bar (all three pulse on b49); the
// stabs stack up as neon bars while the SCALING logo flies in; then black, and MC Token's scope takes its breath before "First,".
(() => {
  const { add, mul, rotYX, text } = MOD;
  const B = n => beatT(n);
  const MODE = () => wordsOf(INTRO_LINES[2]).at(-1).t0, HIT = () => B(37), BUILD = () => B(52), BREATH = () => B(64);
  const hexA = (h, a) => `rgb(${parseInt(h.slice(1, 3), 16)} ${parseInt(h.slice(3, 5), 16)} ${parseInt(h.slice(5, 7), 16)} / ${a})`;

  // ---------------------------------------------------------------------------------------------
  // THE NFO: a glass terminal (2048 × 1024), its sung word on a pane in front
  // ---------------------------------------------------------------------------------------------
  const RELEASE = [['title', "We Didn't Start the Scaling"], ['artist', 'Softmax feat. MC Token'], ['type', 'pc demo · vga 640x360 · 256 colours · 140 bpm'], ['covers', 'jun 2017 → sep 2026 (64 lines, 4 choruses)'], ['released', '22 september 2026']];
  const CREW = [['dj clawd', 'code, gfx, music', '#ff9a5c'], ['softmax', 'vocals', '#ff5cc0'], ['mc token', 'rap', '#5ae6ff']];
  const REQS = ['486dx2/66, 8 mb ram, vga, gus/sb16', 'recommended: 100,000 h100s', 'run: scaling.exe'];
  const PROMPT = 'C:\\DEMOS\\FC>type scaling.nfo';
  const BANNER = [250, 580];   // the banner's top and bottom (texture y)
  const TERM = { c: [0, 2.9, 0], u: [3.3, 0, 0], v: [0, 1.65, 0] };
  const onTerm = (x, y) => add(add(TERM.c, mul(TERM.u, x / 1024 - 1)), mul(TERM.v, 1 - y / 512));
  function box(g, x, y, w, h, title, col) {
    g.strokeStyle = col; g.lineWidth = 3; g.strokeRect(x, y, w, h);
    const tw = MOD.bitmap(g, ' ' + title + ' ', -999, 0, 3, col);   // (measure)
    g.fillStyle = '#05060d'; g.fillRect(x + 36, y - 14, tw + 12, 28);
    MOD.bitmap(g, '[ ' + title + ' ]', x + 36, y - 12, 3, col);
  }
  function kv(g, k, v, x, y, dotsTo, col) {
    const kw = MOD.bitmap(g, k, x, y, 3, '#8592c6');
    let dx = x + kw + 18; g.fillStyle = '#3c4878'; while (dx < dotsTo) { g.fillRect(dx, y + 18, 3, 3); dx += 12; }
    MOD.bitmap(g, v, dotsTo + 18, y, 3, col ?? '#e8ecff');
  }
  let NFO = null;
  function nfoPage() {
    if (NFO) return NFO;
    const c = makeCanvas(2048, 1024), g = c.getContext('2d');
    // the group logo in the demo's own font, cyan to blue and magenta, with a shaded edge
    const px = 14, x0 = 64, y0 = 64;
    const wF = MOD.bitmap(g, 'FRONTIER', -9999, 0, px, '#000');
    MOD.bitmap(g, 'FRONTIER', x0 + px * .6, y0 + px * .6, px, '#0a2a5e');
    MOD.bitmap(g, 'FRONTIER', x0, y0, px, MOD.chrome(g, y0, y0 + px * 8, ['#e8feff', '#4feaff', '#0e8fc4', '#1a3f9e']));
    const xC = x0 + wF + px * 5;
    MOD.bitmap(g, 'CREW', xC + px * .6, y0 + px * .6, px, '#4a0838');
    MOD.bitmap(g, 'CREW', xC, y0, px, MOD.chrome(g, y0, y0 + px * 8, ['#ffe6f6', '#ff5cc0', '#c01888', '#6a0a4a']));
    MOD.bitmap(g, 'p r e s e n t s', x0 + 4, 196, 3, '#8592c6');
    g.fillStyle = '#3c4878'; g.fillRect(x0 + 4, 224, 380, 3);
    // the banner, a double line (the sung word hangs on its own pane in front of it)
    g.strokeStyle = 'rgb(160 24 128 / .9)'; g.lineWidth = 4; g.strokeRect(30, BANNER[0], 1988, BANNER[1] - BANNER[0]);
    g.lineWidth = 2; g.strokeRect(42, BANNER[0] + 12, 1964, BANNER[1] - BANNER[0] - 24);
    // the info
    box(g, 30, 628, 1988, 200, 'release', '#5a6699');
    RELEASE.forEach(([k, v], i) => kv(g, k, v, 70, 654 + i * 34, 330, i === 0 ? '#ffffff' : i === 1 ? '#ffd0ef' : undefined));
    box(g, 30, 862, 940, 150, 'crew', '#5a6699');
    CREW.forEach(([k, v, col], i) => kv(g, k, v, 70, 888 + i * 36, 330, col));
    box(g, 1000, 862, 1018, 150, 'requirements', '#5a6699');
    REQS.forEach((v, i) => MOD.bitmap(g, v, 1040, 888 + i * 36, 3, i === 1 ? '#ffd27a' : '#e8ecff'));
    return (NFO = c);
  }
  // The current teaser word: [line, index] of the latest word sung by t.
  function introWord(t) {
    let L = null, k = -1;
    for (const ln of INTRO_LINES) { const i = wordAt(ln, t); if (i >= 0) { L = ln; k = i; } }
    return [L, k];
  }
  const X0 = 90, X1 = 1990, KEXP = 4.3;
  const curveAt = u => [X0 + u * (X1 - X0), BANNER[1] - 20 - (Math.exp(KEXP * u) - 1) / (Math.exp(KEXP) - 1) * (BANNER[1] + 110)];
  function terminal(t) {
    const g = MOD.panel(0), L3 = wordsOf(INTRO_LINES[2]), tCant = L3[7].t0, tCon = L3[8].t0;
    const strain = t >= tCant ? clamp((t - tCant) / (tCon - tCant)) : 0, broke = t >= tCon;
    g.fillStyle = 'rgb(4 5 12 / .86)'; g.fillRect(0, 0, 2048, 1024);
    // DOS types the command, then the NFO prints top to bottom
    const nP = Math.floor(clamp((t - .12) / .55) * PROMPT.length), pw = nP ? MOD.bitmap(g, PROMPT.slice(0, nP), 40, 22, 3, '#aab4e8') : 0;
    const printed = clamp((t - .75) / .32);
    const page = nfoPage(), yCut = 56 + printed * 968;
    if (strain > 0 && !broke) {
      // "can't": the picture strains, slices of it slipping sideways
      const n = 12;
      for (let i = 0; i < n; i++) {
        const y = i * 1024 / n, h = 1024 / n, off = (hash2(i, Math.floor(t * 30)) - .5) * 80 * strain * strain;
        g.drawImage(page, 0, y, 2048, Math.min(h, Math.max(0, yCut - y)), off, y, 2048, Math.min(h, Math.max(0, yCut - y)));
      }
    } else if (yCut > 56) g.drawImage(page, 0, 56, 2048, yCut - 56, 0, 56, 2048, yCut - 56);
    // DJ Clawd, the group's mascot, beside the logo
    if (printed > .12) MOD.clawd(g, 1860, 218, 15, { eyes: frac(t * .6) < .06 ? 'closed' : 'open' });
    // the cursor
    if (frac(t * 1.9) < .6 && nP < PROMPT.length) { g.fillStyle = '#aab4e8'; g.fillRect(40 + pw + 8, 22, 18, 24); }
    // the whole line, small, on the banner's frame: sung words lit
    const [L, k] = introWord(t);
    if (L && printed > .4) {
      const ws = wordsOf(L), parts = ws.map(w => w.w.toLowerCase()), full = parts.join(' '), fw = MOD.bitmap(g, full, -9999, 0, 3, '#000');
      let x = 1024 - fw / 2;
      g.fillStyle = 'rgb(4 5 12)'; g.fillRect(x - 24, BANNER[1] - 18, fw + 48, 36);
      parts.forEach((p, i) => { x += MOD.bitmap(g, p, x, BANNER[1] - 12, 3, i < k ? '#ff5cc0' : i === k ? '#ffffff' : '#5a6699') + 12; });
    }
    // "can't": the frame strains red; "contain": the exponential climbs out of the banner and breaks through the top
    if (strain > 0) {
      g.lineWidth = 8; g.strokeStyle = broke ? 'rgb(255 90 190 / .8)' : `rgb(255 ${Math.round(80 - 60 * strain)} 90 / ${.5 + .5 * strain})`;
      g.beginPath();
      if (broke) { g.moveTo(1780, 4); g.lineTo(4, 4); g.lineTo(4, 1020); g.lineTo(2044, 1020); g.lineTo(2044, 240); }
      else g.rect(4, 4, 2040, 1016);
      g.stroke();
    }
    let tip = null;
    if (broke) {
      const k2 = easeOut(clamp((t - tCon) / .42)), n = Math.round(k2 * 220);
      g.lineCap = 'round'; g.lineJoin = 'round';
      for (const [w, c] of [[64, 'rgb(255 60 170 / .28)'], [26, '#ff4fb4'], [10, '#ffffff']]) {
        g.lineWidth = w; g.strokeStyle = c; g.beginPath();
        for (let i = 0; i <= n; i++) { const p = curveAt(i / 220); i ? g.lineTo(p[0], p[1]) : g.moveTo(p[0], p[1]); }
        g.stroke();
      }
      tip = curveAt(k2);
      g.fillStyle = '#fff'; g.beginPath(); g.arc(tip[0], Math.max(8, tip[1]), 22 + 8 * kick(t, 6), 0, TAU); g.fill();
    }
    return { strain, broke, tip };
  }
  // The sung word, huge, in the demo's 8×8 font on its own pane (1024 × 512).
  function wordPane(t) {
    const [L, k] = introWord(t);
    if (!L) return false;
    const w = wordsOf(L)[k], age = t - w.t0, word = bigForm(w.w.replace(/[,.!]/g, '')) + (/!$/.test(w.w) ? '!' : '');
    const g = MOD.panel(1);
    const wid = MOD.bitmap(g, word, -9999, 0, 1, '#000'), px = Math.min(16, Math.floor(980 / wid));
    const shown = [...word].slice(0, Math.max(1, Math.ceil(age / .07 * word.length))).join('');
    const x = 512 - wid * px / 2, y = 256 - px * 4 - Math.exp(-age * 14) * 18;
    MOD.bitmap(g, shown, x + px * .7, y + px * .7, px, '#3a0428');
    MOD.bitmap(g, shown, x, y, px, age < .09 ? '#ffffff' : MOD.chrome(g, y, y + px * 8, ['#ffffff', '#ffc4ea', '#ff4fb4', '#9a1070']));
    return true;
  }
  function nfo(t, g) {
    const L3 = wordsOf(INTRO_LINES[2]), tCon = L3[8].t0, T = terminal(t), pane = wordPane(t);
    // the camera: close on the logo and banner, down over the info in the pause, back for the last line, up with the curve
    const shake = T.strain > 0 && !T.broke ? T.strain * .04 : T.broke ? clamp(1 - (t - tCon) / .3) * .05 : 0;
    const sh = [Math.sin(t * 93) * shake, Math.cos(t * 71) * shake, 0];
    const RO = kf(t, [[0, [-2.1, 4.2, 3.3]], [.72, [-1.8, 4.1, 3.7]], [1.3, [-.2, 3.55, 6.5]], [5.6, [.2, 3.45, 6.3]], [7.6, [0, 2.75, 6.3]], [11.6, [-.3, 2.9, 6.5]], [14.2, [0, 3.0, 7.1]], [tCon, [0, 2.95, 7.5]], [MODE(), [0, 2.6, 8.3]]], ease);
    const TA = kf(t, [[0, [-2.0, 4.15, 0]], [.72, [-1.65, 4.0, 0]], [1.3, [-.1, 3.4, 0]], [5.6, [.1, 3.3, 0]], [7.6, [0, 2.8, 0]], [11.6, [-.2, 3.0, 0]], [14.2, [0, 3.1, 0]], [tCon, [0, 3.15, 0]], [MODE(), [0, 4.5, 0]]], ease);
    const F = {
      ro: add(RO, sh), ta: add(TA, sh), fov: 1.6,
      skyA: '#020309', skyB: '#05060f', acc: '#5a6aff', fog: .015, floorCol: '#020206', grid: 0,
      light: { p: [0, 5, 4], c: '#aab4ff', k: 3, vol: 0 },
      panels: [{ ...TERM, alpha: 1, gain: 1.45, glass: 1, tex: 0 }],
    };
    if (pane) F.panels.push({ c: [0, 3.18, .7], u: [3.0, 0, 0], v: [0, 1.5, 0], alpha: 1, gain: 1.9, glass: 0, tex: 1 });
    if (T.broke) {
      // the curve goes on up out of the terminal as a beam; the sky wakes into plasma behind it
      const a = t - tCon, top = onTerm(1960, 0);
      if (T.tip && T.tip[1] < 30) F.beam = { x: top[0], z: top[2] + .02, y0: top[1], y1: top[1] + easeOut(clamp((a - .35) / .3)) * 30, r: .08 + .04 * kick(t, 5), k: 3.4, col: '#ff4fb4' };
      const k = easeIn(clamp(a / (MODE() - tCon)));
      F.sky = { mode: 'plasma', k: .8, col: lerpHex('#000000', '#1478b8', k) }; F.acc = lerpHex('#000000', '#ff3aa6', k);
      F.light = { p: add(top, [0, 1, 1]), c: '#ff5cc0', k: 6, vol: 0 };
      F.flash = clamp(1 - a / .2) * .25; F.flashCol = '#ff7ac8';
    } else if (T.strain > 0) F.acc = lerpHex('#5a6aff', '#ff3050', T.strain);
    return F;
  }

  // ---------------------------------------------------------------------------------------------
  // THE MODE SWITCH, and the crew screen: three panels lit one per bar under FRONTIER CREW PRESENTS
  // ---------------------------------------------------------------------------------------------
  const NOTES = ['C-', 'C#', 'D-', 'D#', 'E-', 'F-', 'F#', 'G-', 'G#', 'A-', 'A#', 'B-'];
  function cellAt(row, ch) {
    // (a plausible 140 BPM Eurodance pattern: kick on the beat, offbeat bass, an A-minor lead from b44)
    const r = row & 63;
    if (ch === 0) return r % 4 === 0 ? 'C-2 01' : '··· ··';
    if (ch === 1) return r % 4 === 2 ? `${['A-', 'A-', 'F-', 'G-'][(r >> 4) & 3]}2 02` : '··· ··';
    if (row < 44 * 4) return '··· ··';
    const m = [0, 3, 7, 10, 12, 10, 7, 3], n = 9 + m[(r >> 1) % 8];
    return r % 2 === 0 ? `${NOTES[n % 12]}${5 + ((n / 12) | 0)} 04` : '··· ··';
  }
  const WHO = [
    { name: 'DJ CLAWD', role: 'code · gfx · music', col: '#ff9a5c', stops: ['#fff4e8', '#ffc08a', '#ff7a2a', '#8f2a06'], lit: 37 },
    { name: 'SOFTMAX', role: 'vocals', col: '#ff5cc0', stops: ['#ffffff', '#ffc4ea', '#ff4fb4', '#8a0f60'], lit: 41 },
    { name: 'MC TOKEN', role: 'rap', col: '#5ae6ff', stops: ['#ffffff', '#b8f6ff', '#18b8ea', '#0b4c8e'], lit: 45 },
  ];
  function crewCard(i, t) {
    const P = WHO[i], g = MOD.panel(i), sc = i === 0 ? 2 : 1, tl = B(P.lit), on = t >= tl;
    g.setTransform(sc, 0, 0, sc, 0, 0);
    const a = on ? t - tl : 0, k = on ? easeOut(clamp(a / .18)) : 0;
    g.fillStyle = `rgb(6 6 16 / ${.55 + .3 * k})`; g.fillRect(0, 0, 1024, 512);
    g.strokeStyle = hexA(P.col, .25 + .6 * k); g.lineWidth = 6; g.strokeRect(3, 3, 1018, 506);
    g.save(); g.globalAlpha = on ? k : .22;
    g.font = `112px ${MOD.FONT_T}`; g.textBaseline = 'alphabetic'; g.lineJoin = 'round';
    const nw = Math.min(1, 944 / g.measureText(P.name).width); g.font = `${Math.floor(112 * nw)}px ${MOD.FONT_T}`;
    g.lineWidth = 12; g.strokeStyle = 'rgb(4 4 12 / .9)'; g.strokeText(P.name, 40, 128);
    g.fillStyle = on ? MOD.chrome(g, 128 - 100 * nw, 132, P.stops) : '#556'; g.fillText(P.name, 40, 128);
    g.restore();
    if (!on) return;
    g.save(); g.globalAlpha = k;
    text(g, P.role, 44, 178, { size: 34, color: P.col });
    g.fillStyle = hexA(P.col, .35); g.fillRect(40, 196, 944, 3);
    if (i === 0) {
      // DJ Clawd, bobbing on the kick, and his tracker: a row every sixteenth, the playing row lit, the lead in orange
      const kk = kick(t, 8);
      MOD.clawd(g, 165, 492, 20, { hop: kk * 10, eyes: kk > .5 ? 'happy' : 'open', aL: kk * .9, aR: .3 + .5 * kick8(t, 6) });
      const row = bt(t) * 4, r0 = Math.floor(row), fr = row - r0, cy = 372, lh = 32, cx = [330, 520, 700];
      g.save(); g.beginPath(); g.rect(310, 240, 700, 266); g.clip();
      const cg = g.createLinearGradient(0, cy - 20, 0, cy + 20); cg.addColorStop(0, 'rgb(255 120 40 / 0)'); cg.addColorStop(.5, 'rgb(255 140 60 / .45)'); cg.addColorStop(1, 'rgb(255 120 40 / 0)');
      g.fillStyle = cg; g.fillRect(310, cy - 22, 700, 44);
      for (let j = -5; j <= 5; j++) {
        const y = cy + (j - fr) * lh + 10, rr = r0 + j, lv = j === 0 ? 1 : .6 - Math.abs(j) * .08;
        text(g, String(rr & 63).padStart(2, '0'), 316, y, { size: 22, color: `rgb(133 146 198 / ${lv})` });
        for (let ch = 0; ch < 3; ch++) text(g, cellAt(rr, ch), cx[ch] + 40, y, { size: 26, color: ch === 2 ? `rgb(255 170 100 / ${lv})` : `rgb(200 210 255 / ${lv * .8})` });
      }
      g.restore();
      ['KICK', 'BASS', 'LEAD'].forEach((c, ch) => {
        const v = ch === 0 ? kick(t, 5) : ch === 1 ? .4 + .4 * kick8(t + .1, 6) : t >= B(44) ? .5 + .5 * kick8(t, 4) : 0;
        text(g, c, cx[ch] + 40, 228, { size: 20, color: ch === 2 ? '#ffb47a' : '#aab4e8' });
        g.fillStyle = 'rgb(133 146 198 / .2)'; g.fillRect(cx[ch] + 110, 216, 70, 10);
        g.fillStyle = ch === 2 ? '#ff9a5c' : '#5ae6ff'; g.fillRect(cx[ch] + 110, 216, 70 * clamp(v), 10);
      });
    } else if (i === 1) {
      // her voice: the softmax over pitch, over the mix's spectrum
      g.beginPath(); g.rect(0, 204, 1024, 308); g.clip();
      MOD.softmaxHUD(g, t, { x0: 40, x1: 984, y: 470, h: 140, word: sungWord(t) });
    } else {
      // his scope, ticking with the beat, waiting for his cue
      g.strokeStyle = 'rgb(90 230 255 / .14)'; g.lineWidth = 2;
      for (let x = 40; x <= 984; x += 59) { g.beginPath(); g.moveTo(x, 216); g.lineTo(x, 496); g.stroke(); }
      for (let y = 216; y <= 496; y += 70) { g.beginPath(); g.moveTo(40, y); g.lineTo(984, y); g.stroke(); }
      const ph = frac(bt(t)), xc = 40 + ph * 944, amp = 70 * (.5 + .5 * Math.exp(-ph * 3));
      g.lineWidth = 4; g.strokeStyle = '#5ae6ff'; g.shadowColor = '#5ae6ff'; g.shadowBlur = 12; g.beginPath();
      for (let x = 40; x <= 984; x += 4) {
        const d = (x - xc) / 34, y = 356 + amp * Math.exp(-d * d) * Math.sin(d * 3.4) + 3 * Math.sin(x * .07 + t * 11);
        x > 40 ? g.lineTo(x, y) : g.moveTo(x, y);
      }
      g.stroke(); g.shadowBlur = 0;
      text(g, 'CH1', 48, 240, { size: 20, color: 'rgb(90 230 255 / .7)' });
    }
    g.restore();
  }
  function crew(t, g) {
    const hit = t - HIT(), since = t - MODE();
    // (the monitor re-syncs: black, one sync line)
    if (since < .07) {
      g.fillStyle = '#000'; g.fillRect(0, 0, 1920, 1080);
      g.fillStyle = '#ffffff'; g.fillRect(0, 538, 1920, 4); g.fillStyle = 'rgb(170 180 230 / .7)'; g.fillRect(120, 546, 1680, 2);
      return { floor: false, skyA: '#000000', skyB: '#000000' };
    }
    const open = hit < 0 ? 0 : easeOut(clamp(hit / .5));
    const F = {
      skyA: '#08030f', skyB: lerpHex('#1a0624', '#0c0418', open), acc: lerpHex('#ff3aa6', '#b0206e', open), fog: .02, floorCol: '#030106', grid: .35,
      sky: { mode: 'plasma', k: .9, col: lerpHex('#1478b8', '#0a3a70', open) }, light: { p: [0, 6, 3], c: '#ffb0e6', k: 5, vol: 0 }, panels: [],
    };
    if (hit < 0) {
      // "it!" held: the 3D demo opens out of white, the curve's beam still climbing
      const k = easeOut(clamp((since - .07) / (HIT() - MODE() - .07)));
      F.flash = clamp(1 - (since - .07) / .35) * .3; F.flashCol = '#ffffff';
      F.ro = [lerp(-1.5, 0, k), lerp(.5, 2.1, k), lerp(4, 8.4, k)]; F.ta = [0, lerp(4.5, 2.3, k), 0]; F.fov = 1.55;
      F.beam = { x: 0, z: 0, y0: 0, y1: 40, r: .12 * (1 - k * .6), k: 3 * (1 - k), col: '#ff4fb4' };
      return F;
    }
    // the group logo drops with an elastic bounce and bounces on every kick; P R E S E N T S types under it
    const drop = hit < .55 ? (1 - elasticOut(hit / .55)) * 3.2 : 0, bump = kick(t, 9) * .06;
    const S = MOD.shapeText('FRONTIER CREW'), hy = .42;
    const b49 = t >= B(49) && t < BUILD() ? kick(t, 5) * (t < B(50) ? 1.4 : .7) : 0;
    F.shape = { key: 'FC', src: S, p: [0, 3.78 + drop + bump, -.3], rot: rotYX(Math.sin(t * .9) * .22, -.3 + .06 * Math.sin(t * 1.3)), s: [hy * S.aspect, hy, .2], col: '#4a3c8a', rim: '#ffd0f0', metal: 1 };
    F.flash = clamp(1 - hit / .2) * .3; F.flashCol = '#ffd0f0';
    const lt = t - HIT();
    const fx = kf(t, [[B(40.6), 0], [B(41.2), -1], [B(44.6), -1], [B(45.2), 1], [B(48.6), 1], [B(49), 0]], easeInOut);
    const near = kf(t, [[B(40.6), 0], [B(41.2), 1], [B(48.6), 1], [B(49), 0]], easeInOut);
    F.ro = [fx * .35 + Math.sin(lt * .35) * .2, 2.25 - near * .1, lerp(8.5, 7.8, near) - lt * .04]; F.ta = [fx * .55, 2.45 - near * .1, 0]; F.fov = 1.42;
    // the three panels in a shallow arc, each lit on its bar
    const X = [-3.0, 0, 3.0], Y = [-.42, 0, .42];
    for (let i = 0; i < 3; i++) {
      crewCard(i, t);
      const tl = B(WHO[i].lit), a = t - tl, pop = t >= tl ? Math.exp(-a * 7) : 0, s = 1 + .07 * pop + .035 * b49;
      const u = [Math.cos(Y[i]) * 1.46 * s, 0, Math.sin(Y[i]) * 1.46 * s], v = [0, .73 * s, 0];
      F.panels.push({ c: [X[i], 1.6, Math.abs(X[i]) * .2], u, v, alpha: 1, gain: (t >= tl ? 1.5 : .8) + 2.2 * pop + 1.4 * b49, glass: 1, tex: i });
    }
    if (b49 > 0) { F.light = { p: [0, 5, 4], c: '#ffffff', k: 5 + 8 * b49, vol: 0 }; F.exposure = 1 + .25 * b49; }
    // P R E S E N T S under the logo, in the demo's own font
    const pres = 'P R E S E N T S', n = Math.floor(clamp((t - B(39)) / .5) * pres.length);
    const q = MOD.project(F, [0, 3.08, 0]);
    if (n > 0 && q) MOD.bitmap(g, pres.slice(0, n), q[0] * 1920 - MOD.bitmap(g, pres, -9999, 0, 5, '#000') / 2, (1 - q[1]) * 1080, 5, '#ff9ad8');
    return F;
  }

  // ---------------------------------------------------------------------------------------------
  // THE BUILD: a neon bar per stab stacks up; the SCALING logo flies in out of the stars; strobes on the eighths
  // ---------------------------------------------------------------------------------------------
  const BAR_COLS = [['#3a0428', '#ff4fb4', '#ffe0f4'], ['#04283a', '#4feaff', '#e8feff'], ['#3a1404', '#ff9a3c', '#fff0dc'], ['#141838', '#9aa8e0', '#ffffff']];
  function build(t, g) {
    const b = bt(t) - 52, strobe = b >= 8 ? kick8(t, 6) : 0;
    const p = MOD.panel(0);
    for (let i = 0; i < 12; i++) {
      const age = b - i; if (age < 0) continue;
      const yT = 1024 - 30 - (i + 1) * 80, y = age < .22 ? lerp(-90, yT, easeIn(age / .22)) : yT - Math.abs(Math.sin((age - .22) * 10)) * 14 * Math.exp(-(age - .22) * 7);
      const [d, c, w] = BAR_COLS[i % 4], lv = b >= 8 ? .65 + .35 * strobe : 1;
      const gr = p.createLinearGradient(0, y, 0, y + 64);
      gr.addColorStop(0, 'rgb(0 0 0 / 0)'); gr.addColorStop(.18, d); gr.addColorStop(.42, c); gr.addColorStop(.5, w); gr.addColorStop(.58, c); gr.addColorStop(.82, d); gr.addColorStop(1, 'rgb(0 0 0 / 0)');
      p.globalAlpha = lv; p.fillStyle = gr; p.fillRect(0, y, 2048, 64); p.globalAlpha = 1;
    }
    const F = {
      skyA: '#02020a', skyB: '#07061a', acc: '#ff3aa6', fog: .018, floorCol: '#030208', grid: .2 + .3 * strobe,
      sky: { mode: 'stars', k: .6 + b * .3, col: '#b8d0ff' },
      ro: [Math.sin(t * .8) * .6, 1.5, 10.5 - b * .18], ta: [0, 2.6, 0], fov: 1.5, roll: Math.sin(t * 1.1) * .03,
      panels: [{ c: [0, 3.2, -4], u: [6.4, 0, 0], v: [0, 3.2, 0], alpha: 1, gain: 1.6 + .9 * strobe, glass: .6, tex: 0 }],
      light: { p: [0, 5, 3], c: strobe > .5 ? '#ffffff' : '#ffb0e6', k: 4 + 7 * strobe, vol: 0 },
      flash: strobe * .1, flashCol: '#ffd0f0', exposure: 1 + .15 * strobe,
    };
    const la = b - 5;
    if (la > 0) {
      const S = MOD.shapeText('SCALING'), hy = .62, k = easeOut(clamp(la / 5.5));
      F.shape = { key: 'SCALING', src: S, p: [0, lerp(5.5, 2.4, k), lerp(-40, 1.4, k)], rot: rotYX((1 - k) * 9 + Math.sin(t * 1.3) * .12, (1 - k) * .6 - .05), s: [hy * S.aspect, hy, .22], col: '#3a2a70', rim: '#a8ecff', metal: 1 };
    }
    return F;
  }

  // ---------------------------------------------------------------------------------------------
  // THE BREATH: black; MC Token's cue; his scope inhales before "First,"
  // ---------------------------------------------------------------------------------------------
  function breath(t, g) {
    const k = easeOut(clamp((t - BREATH()) / .3)), p = MOD.panel(0), v = vox(t);
    p.fillStyle = 'rgb(2 6 12 / .7)'; p.fillRect(0, 0, 2048, 1024);
    p.strokeStyle = 'rgb(90 230 255 / .12)'; p.lineWidth = 2;
    for (let x = 64; x < 2048; x += 120) { p.beginPath(); p.moveTo(x, 360); p.lineTo(x, 900); p.stroke(); }
    for (let y = 360; y <= 900; y += 90) { p.beginPath(); p.moveTo(0, y); p.lineTo(2048, y); p.stroke(); }
    // MC TOKEN
    p.font = `170px ${MOD.FONT_T}`; p.textAlign = 'left'; p.textBaseline = 'alphabetic'; p.lineJoin = 'round';
    p.globalAlpha = k; p.lineWidth = 16; p.strokeStyle = 'rgb(2 6 14 / .9)'; p.strokeText('MC TOKEN', 80, 250);
    p.fillStyle = MOD.chrome(p, 110, 256, ['#ffffff', '#b8f6ff', '#18b8ea', '#0b4c8e']); p.fillText('MC TOKEN', 80, 250); p.globalAlpha = 1;
    text(p, 'CH1 · RAP · VERSE 1', 88, 312, { size: 36, color: 'rgb(90 230 255 / .8)' });
    // the cue: a lamp per beat, then his mic is live
    for (let i = 0; i < 4; i++) {
      const on = t >= B(65 + i), a = on ? t - B(65 + i) : 9, cx = 1480 + i * 130;
      p.fillStyle = on ? `rgb(${Math.round(90 + 165 * Math.exp(-a * 5))} 230 255)` : 'rgb(40 70 90)';
      p.beginPath(); p.arc(cx, 200, 40, 0, TAU); p.fill();
    }
    text(p, 'CUE', 1440, 290, { size: 30, color: 'rgb(90 230 255 / .6)' });
    // his scope: the voice's loudness and pitch, a breath and the pickup
    const note = voxNote(t) || 50, fq = .012 + (note - 40) * .0008;
    p.lineWidth = 7; p.strokeStyle = '#5ae6ff'; p.shadowColor = '#5ae6ff'; p.shadowBlur = 18; p.beginPath();
    for (let x = 0; x <= 2048; x += 8) {
      const env = Math.sin(Math.PI * x / 2048), y = 630 + (v * 230 + 10) * env * (Math.sin(x * fq - t * 31) * .6 + Math.sin(x * fq * 2.03 + t * 17) * .3) * k;
      x ? p.lineTo(x, y) : p.moveTo(x, y);
    }
    p.stroke(); p.shadowBlur = 0;
    // the verse scroller slides in from the right, so "FIRST," reaches the reading point on the downbeat
    const tV = segByKey('V1.1').start, slide = Math.max(0, tV - t);
    if (t > B(66.5)) MOD.scroller(g, 'V1', t, { read: 1920 * .42 + slide * slide * 900 + slide * 300 });
    const lt = t - BREATH();
    return {
      skyA: '#010205', skyB: '#02050a', acc: '#2ad0ff', fog: .02, floorCol: '#010204', grid: 0,
      ro: [Math.sin(lt * .4) * .5, 1.9, 8.8 - lt * .35], ta: [0, 2.7, 0], fov: 1.55,
      panels: [{ c: [0, 3.0, 0], u: [4.4, 0, 0], v: [0, 2.2, 0], alpha: 1, gain: 1.5, glass: .7, tex: 0 }],
      light: { p: [0, 4, 3], c: '#5ae6ff', k: 2 + 4 * v, vol: 0 },
    };
  }

  msection('intro', (t, s, E, g) => {
    const F = t < MODE() ? nfo(t, g) : t < BUILD() ? crew(t, g) : t < BREATH() ? build(t, g) : breath(t, g);
    F.fx = E.fx; F.res = E.res;
    return F;
  });
})();

;
// ---- styles/demoscene/modern/m01_v1.js ----
// modern/m01_v1.js: verse 1 in the modern engine (version B only; version A's verse 1 is the 1996 engine). Part "IGNITION", Jun 2017 →
// Oct 2024: each line's reference from STORYBOARD.md, restaged as one modern-demo image (chrome logos, glass panels, spheres as
// vector bobs, a tunnel, the checker and water floors). Colour run: fire orange → graph-paper green → steel blue → magenta → dawn
// gold → heart red → PAUSE amber → siren red → steel and fire → checkerboard violet → eye teal → EU blue → strawberry red on steel →
// paper and gold → gold on blue → AlphaFold blue and orange.
(() => {
  const { add, sub, mul, rotYX, text } = MOD;
  const LW = 1920, LH = 1080;
  const wt = (s, i) => wordT(s, i);
  const beatOf = (s, k = 0) => beatT(Math.ceil(bt(s.start) - 1e-3) + k);   // the window's k-th beat (0: its first)
  const EIGHTH = () => beatLen() / 2;
  const onPanel = (P, x, y, tw = 1024, th = 512) => add(add(P.c, mul(P.u, 2 * x / tw - 1)), mul(P.v, 1 - 2 * y / th));
  const toUI = (F, p) => { const q = MOD.project(F, p); return q ? [q[0] * LW, (1 - q[1]) * LH] : null; };
  const mv = (R, p) => [R[0] * p[0] + R[1] * p[1] + R[2] * p[2], R[3] * p[0] + R[4] * p[1] + R[5] * p[2], R[6] * p[0] + R[7] * p[1] + R[8] * p[2]];
  const label = (g, str, x, y, o = {}) => text(g, str, x, y, { size: 26, color: 'rgb(205 215 255 / .85)', stroke: 6, ...o });
  // Big type in chrome on the UI (or a panel): a vertical gradient, a dark outline.
  function chromeText(g, str, x, y, size, stops, o = {}) {
    g.save();
    g.font = `${size}px ${o.font ?? MOD.FONT_T}`; g.textAlign = o.align ?? 'center'; g.textBaseline = 'alphabetic'; g.lineJoin = 'round';
    if (o.spacing) g.letterSpacing = o.spacing + 'px';
    g.globalAlpha = o.alpha ?? 1;
    g.lineWidth = o.stroke ?? size * .16; g.strokeStyle = o.strokeCol ?? 'rgb(4 4 12 / .9)'; g.strokeText(str, x, y);
    g.fillStyle = MOD.chrome(g, y - size * .78, y + size * .06, stops); g.fillText(str, x, y);
    g.restore();
  }
  const GOLD = ['#fffdf0', '#ffe487', '#dfa826', '#7a4a06'], STEEL = ['#ffffff', '#d5dcff', '#8592c6', '#2c3460'];

  // ---------- fire: a procedural flame field over a mask, a pure function of t (t running backward runs the flames in reverse) ----------
  const NOISE = (() => {   // 256 × 256 tileable value noise, two octaves
    const N = 256, out = new Float32Array(N * N);
    for (const [cells, amp, seed] of [[16, .62, 1], [32, .38, 2]]) {
      const step = N / cells, v = (i, j) => hash2(((i % cells) + cells) % cells + seed * 1000, ((j % cells) + cells) % cells + seed * 3000);
      for (let y = 0; y < N; y++) for (let x = 0; x < N; x++) {
        const fx = x / step, fy = y / step, i = Math.floor(fx), j = Math.floor(fy), u = fx - i, w = fy - j, su = u * u * (3 - 2 * u), sw = w * w * (3 - 2 * w);
        out[y * N + x] += amp * lerp(lerp(v(i, j), v(i + 1, j), su), lerp(v(i, j + 1), v(i + 1, j + 1), su), sw);
      }
    }
    return out;
  })();
  const FIRE_LUT = (() => {
    const stops = ['#000000', '#3a0602', '#8f1a04', '#d9481a', '#f59a2a', '#ffd873', '#fffbe8'], lut = new Uint8ClampedArray(256 * 4);
    for (let i = 0; i < 256; i++) {
      const f = i / 255 * (stops.length - 1), j = Math.min(stops.length - 2, Math.floor(f)), c = lerpHex(stops[j], stops[j + 1], f - j);
      lut[i * 4] = parseInt(c.slice(1, 3), 16); lut[i * 4 + 1] = parseInt(c.slice(3, 5), 16); lut[i * 4 + 2] = parseInt(c.slice(5, 7), 16); lut[i * 4 + 3] = Math.min(255, i * 2.4);
    }
    return lut;
  })();
  // A word laid out exactly as MOD.shapeText lays it out (so its flames sit on the chrome letters), with its ink's box.
  function textMask(str) {
    const tmp = makeCanvas(8, 8).getContext('2d'); tmp.font = `200px ${MOD.FONT_T}`;
    const tw = Math.ceil(tmp.measureText(str).width), pad = 32, w = Math.min(2048, tw + 2 * pad), h = 200 + 2 * pad;
    const m = makeCanvas(w, h), g = m.getContext('2d', { willReadFrequently: true }), k = Math.min(1, (w - 2 * pad) / tw);
    g.font = `${Math.round(200 * k)}px ${MOD.FONT_T}`; g.textAlign = 'center'; g.textBaseline = 'middle'; g.fillText(str, w / 2, h / 2 + 8);
    const a = g.getImageData(0, 0, w, h).data; let x0 = w, x1 = 0, y0 = h, y1 = 0;
    for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) if (a[(y * w + x) * 4 + 3] > 127) { if (x < x0) x0 = x; if (x > x1) x1 = x; if (y < y0) y0 = y; if (y > y1) y1 = y; }
    return { c: m, w, h, box: [x0 / w, y0 / h, (x1 + 1) / w, (y1 + 1) / h] };
  }
  const FIRES = new Map();
  function fireFor(str, W = 320, H = 160) {
    let F = FIRES.get(str); if (F) return F;
    const T = textMask(str), c = makeCanvas(W, H), g = c.getContext('2d', { willReadFrequently: true }), bh = W * T.h / T.w;
    g.drawImage(T.c, 0, H - bh, W, bh);
    const a = g.getImageData(0, 0, W, H).data, D = new Float32Array(W * H), M = new Uint8Array(W * H);
    // D: how far each pixel is above the nearest fuel below it in its column (0 in the fuel)
    for (let x = 0; x < W; x++) { let d = 999; for (let y = H - 1; y >= 0; y--) { const i = y * W + x, on = a[i * 4 + 3] > 110; M[i] = on ? 1 : 0; d = on ? 0 : d + 1; D[i] = d; } }
    const out = makeCanvas(W, H), og = out.getContext('2d');
    F = { W, H, D, M, out, og, img: og.createImageData(W, H), T };
    FIRES.set(str, F);
    return F;
  }
  function flames(F, t, k, o = {}) {
    const { W, H, D, M, img } = F, px = img.data, L = (o.len ?? H * .6) * k, inner = (o.inner ?? .3) * Math.min(1, k * 2);
    const s1 = Math.floor(t * 110), s2 = Math.floor(t * 170);
    for (let y = 0; y < H; y++) {
      const r1 = ((y + s1) & 255) * 256, r2 = (((y << 1) + s2) & 255) * 256, sway = 1.4 - y / H;
      for (let x = 0; x < W; x++) {
        const i = y * W + x, n1 = NOISE[r1 + ((x << 1) & 255)];
        const x2 = Math.min(W - 1, Math.max(0, Math.round(x + (n1 - .5) * 18 * sway)));
        const n2 = NOISE[r2 + ((x * 3 + 91) & 255)];
        let I = L > 0 ? 1 - D[y * W + x2] / (L * (.18 + 1.2 * n2)) : 0;
        if (M[i]) I = Math.min(I, inner);
        const q = (I <= 0 ? 0 : Math.min(255, (I * 255) | 0)) * 4, j = i * 4;
        px[j] = FIRE_LUT[q]; px[j + 1] = FIRE_LUT[q + 1]; px[j + 2] = FIRE_LUT[q + 2]; px[j + 3] = FIRE_LUT[q + 3];
      }
    }
    F.og.putImageData(img, 0, 0);
    return F.out;
  }
  // The pane a logo's flames burn on: the logo's box along the bottom of a 2:1 pane just in front of it.
  const firePane = (P, hx, hy, z) => ({ c: [P[0], P[1] - hy + hx / 2, P[2] + z], u: [hx, 0, 0], v: [0, hx / 2, 0] });
  function sparks(g, x, y, t, n = 16, col = '255 210 120') {
    const f = Math.floor(t * 30);
    g.save(); g.lineCap = 'round';
    for (let i = 0; i < n; i++) {
      const a = hash2(f, i) * TAU, r0 = 6 + hash2(f + 7, i) * 10, r1 = r0 + 14 + hash2(f + 13, i) * 40;
      g.strokeStyle = `rgb(${col} / ${.5 + .5 * hash2(f + 3, i)})`; g.lineWidth = 2 + 2 * hash2(f + 5, i);
      g.beginPath(); g.moveTo(x + Math.cos(a) * r0, y + Math.sin(a) * r0 - 4); g.lineTo(x + Math.cos(a) * r1, y + Math.sin(a) * r1 - 10); g.stroke();
    }
    g.restore();
  }

  // ---------- V1.1 First, "Attention" lit the fuse: a fuse of beads burns in to ATTENTION, which goes up in flames ----------
  mline('V1', 1, (t, s, E, g) => {
    const lt = t - s.start, tLit = wt(s, 1) + .05, tLit2 = wt(s, 2);
    const S = MOD.shapeText('ATTENTION'), hy = .62, hx = hy * S.aspect, FR = fireFor('ATTENTION'), bx = FR.T.box, P = [.7, .05 - (1 - 2 * bx[3]) * hy, 0];
    const inkX = f => P[0] + (2 * f - 1) * hx, inkY = f => P[1] + (1 - 2 * f) * hy;
    const foot = [inkX(bx[0]) + .1, inkY(bx[3]) + .02, .22];   // the A's left foot
    // the fuse: beads curving in from the lower-left foreground; the spark reaches the A as he says "Attention"
    const fuseAt = k => [lerp(-4.9, foot[0], k), .07, lerp(4.2, foot[2] + .1, k) - Math.sin(k * Math.PI) * 1.3];
    const kS = clamp((t - s.start + .1) / (tLit - s.start + .1));
    const spheres = [];
    for (let i = 0; i < 20; i++) { const k = i / 19; spheres.push([...fuseAt(k), .075, k < kS - .02 ? '#1c0c06' : '#8e94a6']); }
    const lit = t >= tLit, burn = lit ? easeOut(clamp((t - tLit) / .35)) : 0, surge = t >= tLit2 ? Math.exp(-(t - tLit2) * 3.5) : 0;
    const F = {
      ro: [-2.4 + lt * .5, 3.2 + lt * .1, 7.4 - lt * .4], ta: [.2, .7 + lt * .25, 0], fov: 1.42,
      skyA: '#040304', skyB: lit ? lerpHex('#0a0608', '#2e0c04', burn) : '#0a0608', acc: '#ff7a2a', fog: .03, floorCol: '#030202',
      shape: { key: 'ATTENTION', src: S, p: P, rot: rotYX(0), s: [hx, hy, .18], col: lit ? lerpHex('#20222c', '#2a0c04', burn) : '#20222c', rim: lit ? lerpHex('#8a98c0', '#ffb040', burn) : '#8a98c0', metal: 1 },
      spheres, panels: [],
    };
    const sp = fuseAt(Math.min(kS, 1)), flick = .8 + .2 * Math.sin(t * 37) * Math.sin(t * 23);
    if (lit) {
      const p = MOD.panel(1); p.imageSmoothingEnabled = true; p.drawImage(flames(FR, t, burn * (1 + .3 * surge)), 0, 0, 1024, 512);
      F.panels.push({ ...firePane(P, hx, hy, 0), alpha: 1, gain: 2.2 + .8 * surge, glass: 0, tex: 1 });
      F.light = { p: [P[0], 1.9, 1.4], c: '#ff8a3c', k: (7 + 5 * surge) * flick, vol: .35 };
      F.flash = clamp(1 - (t - tLit) / .15) * .22; F.flashCol = '#ffb060';
    } else {
      F.light = { p: add(sp, [0, .3, .2]), c: '#ffb060', k: 3.5 * flick, vol: 0 };
      F.beam = { x: sp[0], z: sp[2], y0: sp[1] + .02, y1: sp[1] + .06, r: .07, k: 4 + 2 * kick8(t, 9), col: '#ffc860' };   // the spark
      const q = toUI(F, sp); if (q) sparks(g, q[0], q[1], t);
    }
    label(g, 'arXiv:1706.03762', 70, 84);
    label(g, 'ATTENTION IS ALL YOU NEED', 70, 120, { color: lit ? '#ffb060' : 'rgb(205 215 255 / .55)' });
    return F;
  });

  // ---------- V1.2 Scaling laws you can't refuse: Kaplan's power law falling straight across log-log paper, zooming out ----------
  mline('V1', 2, (t, s, E, g) => {
    const lt = t - s.start, d = s.end - s.start, P = { c: [0, 3.1, 0], u: [3.5, 0, 0], v: [0, 1.75, 0] };
    const p = MOD.panel(0);
    p.fillStyle = 'rgb(2 16 7 / .8)'; p.fillRect(0, 0, 2048, 1024);
    const zoom = lerp(1, .34, easeInOut(lt / d)), dec = 640 * zoom, cx = 1100, cy = 470, u0 = -4, slope = .5;
    const X = u => cx + (u - u0) * dec, Y = w => cy + w * dec;   // (w: decades of loss, down)
    const uA = u0 - cx / dec - 1, uB = u0 + (2048 - cx) / dec + 1, wA = -cy / dec - 1, wB = (1024 - cy) / dec + 1;
    for (let D = Math.floor(uA); D <= uB; D++) for (let m = 1; m < 10; m++) {
      const x = X(D + Math.log10(m)); if (x < 0 || x > 2048) continue;
      p.fillStyle = m === 1 ? 'rgb(90 255 140 / .5)' : `rgb(60 210 110 / ${.07 + .12 * zoom})`; p.fillRect(x - 1, 0, m === 1 ? 3 : 2, 1024);
    }
    for (let D = Math.floor(wA); D <= wB; D++) for (let m = 1; m < 10; m++) {
      const y = Y(D + Math.log10(m)); if (y < 0 || y > 1024) continue;
      p.fillStyle = m === 1 ? 'rgb(90 255 140 / .5)' : `rgb(60 210 110 / ${.07 + .12 * zoom})`; p.fillRect(0, y - 1, 2048, m === 1 ? 3 : 2);
    }
    // the compute axis, decades rising left to right
    p.fillStyle = 'rgb(2 16 7 / .88)'; p.fillRect(0, 846, 2048, 178);
    for (let D = Math.ceil(uA); D <= uB; D++) { const x = X(D); if (x > 60 && x < 1990) { text(p, '10', x - 22, 924, { size: 52, align: 'center', color: '#b8ffcc' }); text(p, String(D).replace('-', '−'), x + 8, 890, { size: 32, color: '#b8ffcc' }); } }
    text(p, 'COMPUTE (PF-DAYS) →', 2010, 990, { size: 40, align: 'right', color: 'rgb(160 255 190 / .9)' });
    p.save(); p.translate(56, 470); p.rotate(-Math.PI / 2); text(p, 'TEST LOSS', 0, 0, { size: 34, align: 'center', color: 'rgb(160 255 190 / .85)', spacing: 4 }); p.restore();
    // the law: a straight line, falling; its data points land on it, one per eighth
    p.lineCap = 'round';
    for (const [w, c] of [[34, 'rgb(90 255 140 / .22)'], [14, '#5dff8a'], [5, '#f0fff4']]) { p.lineWidth = w; p.strokeStyle = c; p.beginPath(); p.moveTo(X(uA), Y(slope * (uA - u0))); p.lineTo(X(uB), Y(slope * (uB - u0))); p.stroke(); }
    const n = clamp(Math.floor((t - beatOf(s)) / EIGHTH()) + 1, 0, 9), spheres = [];
    for (let i = 0; i < n; i++) {
      const u = u0 - 3.2 + i * .8, x = X(u), y = Y(slope * (u - u0)) + Math.sin(i * 2.7) * 10, a = t - beatOf(s) - i * EIGHTH(), land = easeOut(clamp(a / .14));
      if (x < -20 || x > 2068) continue;
      const w = onPanel(P, x, y, 2048, 1024);
      spheres.push([w[0], w[1] + (1 - land) * 1.6, .22 + (1 - land) * .8, .11 + .03 * kick8(t - i * .01, 8)]);
    }
    // L ∝ C to the power −0.050, in the demo's own font
    const q = MOD.chrome(g, 70, 170, ['#ffffff', '#c8ffd8', '#3adf6a', '#0d5c2c']);
    const lw = MOD.bitmap(g, 'L ∝ C', 74, 86, 11, '#021006') && MOD.bitmap(g, 'L ∝ C', 70, 82, 11, q);
    MOD.bitmap(g, '-0.050', 70 + lw + 18, 64, 6, '#021006'); MOD.bitmap(g, '-0.050', 70 + lw + 16, 62, 6, '#c8ffd8');
    label(g, 'arXiv:2001.08361', 72, 196, { color: 'rgb(160 255 190 / .8)' });
    return {
      ro: [-1.5 + lt * .8, 3.05 + lt * .12, 6.9 + lt * .45], ta: [lt * .2, 3.2, 0], fov: 1.5,
      skyA: '#010603', skyB: '#021008', acc: '#3adf6a', fog: .02, floorCol: '#010402', grid: .12,
      panels: [{ ...P, alpha: 1, gain: 1.5, glass: .8, tex: 0 }], spheres, sphCol: '#6dff9a',
      light: { p: [2, 5, 4], c: '#b8ffcc', k: 4, vol: 0 },
    };
  });

  // ---------- V1.3 Gwern said "stack the compute high": server blades stack one per eighth; the gwern.net G on the tower's top ----------
  const HB = .34, TW = 1.2;   // blade height; the tower's half width (a 2.4 × 2.4 × 4.8 glass rack)
  function rackFront(g, n, drop, t) {
    // portrait: (px 0..512 left → right, py 0..1024 top → bottom) on a landscape texture turned on its side
    g.setTransform(0, -1, -1, 0, 1024, 512);
    const bh = 1024 * HB / (2 * TW * 2);
    for (let i = 0; i < n; i++) {
      const y = 1024 - (i + 1) * bh - (i === n - 1 ? drop * bh * 3 : 0);
      g.fillStyle = '#10141f'; g.fillRect(8, y + 3, 496, bh - 6);
      g.fillStyle = '#2a3350'; g.fillRect(8, y + 3, 496, 4); g.fillStyle = '#05070c'; g.fillRect(8, y + bh - 7, 496, 4);
      for (let v = 0; v < 12; v++) { g.fillStyle = 'rgb(60 70 100 / .6)'; g.fillRect(250 + v * 20, y + 16, 10, bh - 32); }
      for (let j = 0; j < 7; j++) {
        const on = hash2(i * 7 + j, Math.floor(t * 9)) > .3;
        g.fillStyle = on ? '#8af2ff' : '#123a48'; g.fillRect(30 + j * 28, y + bh / 2 - 6, 16, 12);
      }
      g.fillStyle = '#8592c6'; g.fillRect(470, y + 10, 10, bh - 20);
    }
    g.setTransform(1, 0, 0, 1, 0, 0);
  }
  function rackSide(g, n, drop) {
    g.setTransform(0, -1, -1, 0, 1024, 512);
    const bh = 1024 * HB / (2 * TW * 2);
    for (let i = 0; i < n; i++) {
      const y = 1024 - (i + 1) * bh - (i === n - 1 ? drop * bh * 3 : 0);
      g.fillStyle = '#0a0d16'; g.fillRect(4, y + 3, 504, bh - 6);
      for (let v = 0; v < 22; v++) { g.fillStyle = 'rgb(70 90 140 / .35)'; g.fillRect(16 + v * 22, y + 12, 12, bh - 24); }
    }
    g.setTransform(1, 0, 0, 1, 0, 0);
  }
  mline('V1', 3, (t, s, E, g) => {
    const lt = t - s.start, e = EIGHTH(), a = (t - beatOf(s)) / e;
    const n = Math.min(14, 4 + Math.max(0, Math.floor(a) + 1)), drop = a < 0 ? 0 : 1 - easeIn(clamp(frac(a) / .3));
    const top = n * HB - drop * HB * 3 * (a >= 0 ? 1 : 0);
    rackFront(MOD.panel(1), n, a >= 0 ? drop : 0, t); rackSide(MOD.panel(2), n, a >= 0 ? drop : 0);
    const G = MOD.shapeG(), gy = .52, gx = gy * G.aspect, land = a >= 0 && frac(a) < .3 ? Math.exp(-frac(a) * 20) * .06 : 0;
    const topY = Math.max(top, (n - 1) * HB);
    const F = {
      ro: [2.9 + Math.sin(lt * .8) * .3, Math.max(.6, topY - 1.5), 5.6 - lt * .3], ta: [.1, topY - .1, 0], fov: 1.45,
      skyA: '#03050c', skyB: '#0c1428', acc: '#4f7aff', fog: .03, floorCol: '#020308', grid: .25,
      sky: { mode: 'stars', k: .25, col: '#9ab0ff' },
      panels: [
        { c: [0, 2.4, TW], u: [0, 2.4, 0], v: [TW, 0, 0], alpha: 1, gain: 1.35, glass: 0, tex: 1 },
        { c: [TW, 2.4, 0], u: [0, 2.4, 0], v: [0, 0, -TW], alpha: 1, gain: 1.0, glass: 0, tex: 2 },
      ],
      shape: { key: 'G', src: G, p: [0, topY + gy + .08 + land, TW * .7], rot: rotYX(.5 + Math.sin(t * 1.2) * .25), s: [gx, gy, .09], col: '#101018', rim: '#ffcf7a', metal: 1 },
      light: { p: [2, topY + 3, 4], c: '#c8d4ff', k: 5, vol: 0 },
    };
    label(g, 'THE SCALING HYPOTHESIS', 70, 84, { size: 30 });
    label(g, 'gwern.net · 2020', 70, 122, { color: 'rgb(205 215 255 / .6)' });
    return F;
  });

  // ---------- V1.4 Few-shot learners multiply: the paper's prompt format; the answer rolls and lands wrong; 29.2% in chrome ----------
  const QS = ['Q: What is 17 times 25? A: 425', 'Q: What is 38 times 12? A: 456', 'Q: What is 23 times 47? A:'];
  mline('V1', 4, (t, s, E, g) => {
    const lt = t - s.start, tA = beatOf(s, 1), done = tA + .5;
    const p = MOD.panel(0);
    p.fillStyle = 'rgb(18 4 16 / .82)'; p.fillRect(0, 0, 2048, 1024);
    p.fillStyle = 'rgb(255 80 180 / .22)'; p.fillRect(0, 0, 2048, 70);
    text(p, 'LANGUAGE MODELS ARE FEW-SHOT LEARNERS · GPT-3 · 175B', 36, 48, { size: 34, color: '#ffd0ef' });
    QS.forEach((q, i) => { const n = Math.floor(clamp((lt - i * .1) / .14) * q.length); if (n > 0) text(p, q, 70, 200 + i * 130, { size: 76, n, color: i < 2 ? 'rgb(220 200 230 / .8)' : '#ffffff' }); });
    let wrong = 0;
    if (t >= tA) {
      p.save(); p.font = `76px ${MOD.FONT_M}`; const x = 70 + p.measureText(QS[2] + ' ').width; p.restore();
      const shown = [...'1071'].map((c, i) => t >= tA + .16 + i * .09 ? c : String(Math.floor(hash2(i, Math.floor(t * 30)) * 10))).join('');
      text(p, shown, x, 460, { size: 76, color: t >= done ? '#ff5cc0' : 'rgb(255 255 255 / .6)' });
      if (t >= done) {
        wrong = easeOut(clamp((t - done) / .1));
        const cx = x + 280, cy = 434, r = 38 * wrong; p.strokeStyle = '#ff3040'; p.lineWidth = 14; p.lineCap = 'round';
        p.beginPath(); p.moveTo(cx - r, cy - r); p.lineTo(cx + r, cy + r); p.moveTo(cx - r, cy + r); p.lineTo(cx + r, cy - r); p.stroke();
      }
    }
    // the × of spheres behind, turning
    const spheres = [], rot = t * .9, R = rotYX(rot * .5, .3);
    for (let arm = 0; arm < 2; arm++) for (let i = -4; i <= 4; i++) {
      if (arm && i === 0) continue;
      const a = (arm ? -1 : 1) * Math.PI / 4 + rot * .3, q = [Math.cos(a) * i * .62, Math.sin(a) * i * .62, 0];
      const Rr = rot3(0, rot * .5, 0), w = mv(Rr, q);
      spheres.push([w[0] + 2.7, w[1] + 3.4, w[2] - 3.4, .24 + .05 * kick(t, 6)]);
    }
    const F = {
      ro: [Math.sin(lt * .6) * .5, 3.05, 7.9 - lt * .3], ta: [0, 3.15, 0], fov: 1.5,
      skyA: '#0a0210', skyB: '#1e0624', acc: '#ff3aa6', fog: .02, floorCol: '#050206', grid: .2,
      panels: [{ c: [-.25, 3.4, -.5], u: [3.5, 0, 0], v: [0, 1.75, 0], alpha: 1, gain: 1.5, glass: .9, tex: 0 }],
      spheres, sphCol: '#ff4fb4', light: { p: [0, 5, 4], c: '#ffb0e6', k: 5, vol: 0 },
    };
    // 29.2%: GPT-3's few-shot score at two-digit multiplication, rising in chrome
    if (t >= done + .06) {
      const S = MOD.shapeText('29.2%'), hy = .5, k = easeOut(clamp((t - done - .06) / .22));
      F.shape = { key: '29.2%', src: S, p: [.2, lerp(-.6, 2.35, k), 1.4], rot: rotYX(Math.sin(t * 1.6) * .18 + (1 - k) * 1.2, -.08), s: [hy * S.aspect, hy, .2], col: '#b0207a', rim: '#ffb0e6', metal: 1 };
      F.flash = clamp(1 - (t - done - .06) / .15) * .16; F.flashCol = '#ff9ad8';
      const q = toUI(F, [.2, 1.78, 1.4]);
      if (q) label(g, '2-DIGIT MULTIPLICATION · FEW-SHOT', q[0], q[1] + 14, { align: 'center', size: 28, alpha: k, color: '#ffd0ef' });
    }
    return F;
  });

  // ---------- V1.5 ChatGPT, overnight: night to dawn in one beat, a striped sun over a rushing grid, the users counter ----------
  let SUN = null;
  function sunTex() {
    if (SUN) return SUN;
    const c = makeCanvas(1024, 512), g = c.getContext('2d'), gr = g.createLinearGradient(0, 16, 0, 496);
    gr.addColorStop(0, '#fff6c0'); gr.addColorStop(.35, '#ffc440'); gr.addColorStop(.7, '#ff6a3c'); gr.addColorStop(1, '#e8207a');
    g.fillStyle = gr; g.beginPath(); g.arc(512, 256, 240, 0, TAU); g.fill();
    return (SUN = c);
  }
  mline('V1', 5, (t, s, E, g) => {
    const lt = t - s.start, tB = beatOf(s), dawn = easeOut(clamp((t - tB) / .45));
    const p = MOD.panel(1); p.drawImage(sunTex(), 0, 0);
    // the stripes cut out of its lower half, sliding down
    p.globalCompositeOperation = 'destination-out';
    for (let i = 0; i < 9; i++) { const y = 262 + ((i * 28 + t * 40) % 252), h = 3 + (y - 262) / 252 * 16; p.fillRect(0, y, 1024, h); }
    p.globalCompositeOperation = 'source-over';
    const sunY = lerp(-5.5, 5.2, dawn) + lt * .25;
    const users = Math.round(lerp(0, 1e8, easeIn(clamp(lt / ((s.end - s.start) * .82)))));
    chromeText(g, users.toLocaleString('en-US'), 960, 210, 110, GOLD);
    label(g, 'CHATGPT USERS · NOV 30 → JAN', 960, 268, { align: 'center', size: 30, color: '#ffe0a8' });
    return {
      ro: [Math.sin(lt * .5) * .4, 1.1, 8], ta: [0, 2.6, -20], fov: 1.5,
      skyA: lerpHex('#02030c', '#1c0c34', dawn), skyB: lerpHex('#080c26', '#ff7a3c', dawn), acc: lerpHex('#3a4a9a', '#ffb040', dawn), fog: .03,
      sky: { mode: 'stars', k: .3, col: lerpHex('#c9d6ff', '#000000', dawn) },
      floorCol: '#08040e', grid: .95, floorOff: [0, -t * 9],
      panels: [{ c: [0, sunY, -34], u: [17, 0, 0], v: [0, 8.5, 0], alpha: 1, gain: 1.4 + .8 * dawn, glass: 0, tex: 1 }],
      light: { p: [0, sunY, -30], c: '#ffb060', k: 3 + 5 * dawn, vol: 0 },
      flash: clamp(1 - (t - tB) / .2) * .15 * (t >= tB ? 1 : 0), flashCol: '#ffd08a',
    };
  });

  // ---------- V1.6 Sydney's chats gave Roose a fright: a heart of chrome spheres beating while Sydney types; on "fright" it bursts ----------
  const HEART = (() => {
    const pts = [], hx = a => 16 * Math.sin(a) ** 3, hy = a => 13 * Math.cos(a) - 5 * Math.cos(2 * a) - 2 * Math.cos(3 * a) - Math.cos(4 * a);
    for (let i = 0; i < 24; i++) { const a = i / 24 * TAU; pts.push([hx(a) / 11, hy(a) / 11, 0, .2]); }
    [[-.62, .32], [.62, .32], [0, -.2], [-.3, -.62], [.3, -.62], [0, -1.05], [-.95, .7], [.95, .7]].forEach(([x, y], i) => pts.push([x, y, (i % 2 ? .38 : -.38), .24]));
    return pts;
  })();
  const SYDNEY = ["I'm Sydney,", "and I'm in love with you."];
  mline('V1', 6, (t, s, E, g) => {
    const lt = t - s.start, tF = wt(s, 5), burst = t >= tF ? easeOut(clamp((t - tF) / .45)) : 0, beat = 1 + .13 * kick(t, 5);
    const C = [1.55, 2.55, 0], R = rot3(0, Math.sin(t * 1.3) * .5, 0), HS = 1.28;
    const spheres = HEART.map((q, i) => {
      const dir = [q[0] + (hash(i) - .5) * 1.4, q[1] + (hash(i + 9) - .5) * 1.4, q[2] + (hash(i + 17) - .5) * .5], k = burst * 2.6;
      const w = mv(R, [(q[0] * beat + dir[0] * k) * HS, (q[1] * beat + dir[1] * k) * HS, (q[2] * beat + dir[2] * k) * HS]);
      return [C[0] + w[0], C[1] + w[1], C[2] + w[2], q[3] * beat * HS, i % 3 ? '#ff2438' : '#ff5a6a'];
    });
    // her chat: two bubbles, typed
    const p = MOD.panel(1), t0 = beatOf(s) + .02;
    p.fillStyle = 'rgb(20 6 22 / .6)'; p.fillRect(0, 0, 1024, 512);
    text(p, 'Bing · chat', 40, 58, { size: 30, color: 'rgb(255 190 230 / .75)' });
    SYDNEY.forEach((m, i) => {
      const n = Math.floor(clamp((t - t0 - i * .5) / .38) * m.length); if (n <= 0) return;
      const y = 120 + i * 150;
      p.save(); p.font = `52px ${MOD.FONT_M}`; const w = p.measureText(m).width; p.restore();
      p.fillStyle = 'rgb(255 80 180 / .85)'; p.beginPath(); p.roundRect(40, y, w + 70, 104, 30); p.fill();
      text(p, m, 75, y + 70, { size: 52, n, color: '#ffffff' });
    });
    const jolt = t >= tF ? Math.exp(-(t - tF) * 9) : 0, sh = [Math.sin(t * 83) * .12 * jolt, Math.cos(t * 67) * .1 * jolt, 0];
    label(g, 'BING · FEB 2023', 70, 84);
    return {
      ro: add([Math.sin(lt * .4) * .5, 2.3, 8.2], sh), ta: add([.2, 2.45, 0], sh), fov: 1.5, roll: Math.sin(t * 60) * .05 * jolt,
      skyA: '#0a0206', skyB: '#26040c', acc: '#ff2438', fog: .02, floorCol: '#060103', grid: .15,
      panels: [{ c: [-2.3, 3.0, .6], u: [2.0, 0, .45], v: [0, 1.0, 0], alpha: 1, gain: 1.5, glass: .7, tex: 1 }],
      spheres, sphCol: '#ff2438', light: { p: [0, 5, 5], c: '#ff9aa6', k: 5 + 1.5 * jolt, vol: 0 },
      flash: t >= tF && t - tF < .07 ? .22 : 0, flashCol: '#ffc0d0',
    };
  });

  // ---------- V1.7 Six-month pause went nowhere fast: an amber tunnel papered with PAUSE, flown flat out ----------
  let PAUSE_TEX = null;
  function pauseTex() {
    if (PAUSE_TEX) return PAUSE_TEX;
    const c = makeCanvas(1024, 1024), g = c.getContext('2d');
    for (let j = 0; j < 8; j++) for (let k = 0; k < 4; k++) {
      const x = k * 256, y = j * 128, odd = (j + k) & 1;
      g.fillStyle = odd ? '#2a1604' : '#140a02'; g.fillRect(x, y, 256, 128);
      g.fillStyle = '#e8a020';
      if (odd) { g.save(); g.translate(x + 128, y + 68); g.scale(-1, 1); g.font = `58px ${MOD.FONT_T}`; g.textAlign = 'center'; g.textBaseline = 'middle'; g.fillText('PAUSE', 0, 0); g.restore(); }   // (mirrored: it's read from inside)
      else { g.fillRect(x + 96, y + 24, 22, 80); g.fillRect(x + 138, y + 24, 22, 80); }
      g.fillStyle = 'rgb(255 200 90 / .25)'; g.fillRect(x, y, 256, 3); g.fillRect(x, y, 3, 128);
    }
    return (PAUSE_TEX = c);
  }
  mline('V1', 7, (t, s, E, g) => {
    const lt = t - s.start, tB = beatOf(s), go = t < tB ? lt * .6 : (tB - s.start) * .6 + (t - tB) * 3.4;
    const sway = Math.sin(t * 1.7) * .35;
    // the VCR's pause, blinking, while nothing stops
    if (frac(t * 1.6) < .62) {
      g.save(); g.shadowColor = 'rgb(0 0 0 / .8)'; g.shadowOffsetX = 4; g.shadowOffsetY = 4; g.fillStyle = '#ffffff';
      g.fillRect(74, 64, 18, 58); g.fillRect(104, 64, 18, 58); g.restore();
      text(g, 'PAUSE', 144, 118, { size: 60, font: MOD.FONT_M, color: '#ffffff', stroke: 8 });
    }
    label(g, 'PAUSE GIANT AI EXPERIMENTS · AN OPEN LETTER · 30,000+ SIGNATURES', 74, 168, { color: '#ffc870' });
    return {
      floor: false, ro: [sway * .8, Math.cos(t * 1.3) * .35, 0], ta: [sway * .3, 0, -6], fov: 1.2, roll: Math.sin(t * .9) * .12,
      skyA: '#0a0602', skyB: '#1a0c02', acc: '#ffa020', fog: .05,
      tunnel: { key: 'pause', src: pauseTex(), r: 3, scroll: go, twist: .004, col: '#ffd08a', gain: 1.6 },
      light: { p: [0, 0, -26], c: '#ffb040', k: 14, vol: 1.2 },
    };
  });

  // ---------- V1.8 Eliezer's "shut-it-down" blast: the headline types over a siren; SHUT IT ALL DOWN slams in; the CRT switches off ----------
  const H1 = "PAUSING AI DEVELOPMENTS ISN'T ENOUGH.", H2 = 'WE NEED TO';
  mline('V1', 8, (t, s, E, g) => {
    const lt = t - s.start, tB = beatOf(s), w1 = wt(s, 1), w2 = wt(s, 2), w3 = wt(s, 3), tBlast = w3 + .04;
    const p = MOD.panel(0);
    p.fillStyle = 'rgb(16 2 4 / .84)'; p.fillRect(0, 0, 2048, 1024);
    text(p, 'TIME · MARCH 29, 2023 · ELIEZER YUDKOWSKY', 1024, 110, { size: 40, align: 'center', color: 'rgb(255 190 190 / .8)' });
    const t0 = s.start + .03, n1 = Math.floor(clamp((t - t0) / ((w1 - t0) * .7)) * H1.length), n2 = Math.floor(clamp((t - t0 - (w1 - t0) * .72) / ((w1 - t0) * .24)) * H2.length);
    text(p, H1, 1024, 300, { size: 84, font: MOD.FONT_M, align: 'center', n: n1, color: '#ffffff' });
    if (n2 > 0) text(p, H2, 1024, 440, { size: 84, font: MOD.FONT_M, align: 'center', n: n2, color: '#ffffff' });
    // SHUT · IT · ALL DOWN, word by word
    const q = MOD.panel(1);
    [['SHUT', w1, 330, 120], ['IT', w2, 780, 120], ['ALL DOWN', w3, 512, 318]].forEach(([str, tw, x, y]) => {
      if (t < tw) return;
      const a = t - tw, sc = 1 + Math.exp(-a * 16) * .6;
      q.save(); q.font = `170px ${MOD.FONT_T}`; const size = Math.min(170, 170 * 960 / q.measureText(str).width); q.restore();
      q.save(); q.translate(x, y); q.scale(sc, sc); chromeText(q, str, 0, 60, size, ['#ffffff', '#ffd0d0', '#ff3040', '#6a0410'], { stroke: 22 }); q.restore();
    });
    const rot = t * 5.5, siren = .5 + .5 * Math.sin(rot * 2);
    const F = {
      ro: [Math.sin(lt * .7) * .5, 2.9, 8.6 - lt * .5], ta: [0, 3.05, 0], fov: 1.5,
      skyA: '#0a0102', skyB: '#300406', acc: '#ff2020', fog: .02, floorCol: '#060102', grid: .2,
      sky: { mode: 'rays', k: 6, col: '#ff3030' },
      panels: [{ c: [0, 3.55, -.8], u: [3.9, 0, 0], v: [0, 1.95, 0], alpha: 1, gain: 1.4, glass: .8, tex: 0 }, { c: [0, 2.75, 1.4], u: [2.9, 0, 0], v: [0, 1.45, 0], alpha: 1, gain: 1.9, glass: 0, tex: 1 }],
      light: { p: [Math.cos(rot) * 4, 4, Math.sin(rot) * 4], c: '#ff2020', k: 4 + 5 * siren, vol: .8 },
    };
    if (t >= w1 && t < w1 + .1) { F.flash = .14; F.flashCol = '#ff8080'; }
    // "blast": a shockwave ring out of the words
    if (t >= tBlast) { const a = t - tBlast; F.halo = { p: [0, 2.75, 1.5], n: [0, 0, 1], R: .4 + a * 26, r: .1 + a, k: 3 * clamp(1 - a / .25), col: '#ffb0b0' }; }
    // just before the cut, the CRT switches off: the picture closes to a line, the line to a dot
    const off = clamp((t - (s.end - .14)) / .13);
    if (off > 0) {
      MOD.scroller(g, 'V1', t); MOD.datePlate(g, t); F.scroller = false; F.date = false;
      const hh = lerp(540, 2, easeIn(clamp(off / .55))), ww = off < .55 ? 960 : lerp(960, 4, easeIn((off - .55) / .45));
      g.fillStyle = '#000'; g.fillRect(0, 0, 1920, 540 - hh); g.fillRect(0, 540 + hh, 1920, 540 - hh); g.fillRect(0, 540 - hh, 960 - ww, 2 * hh); g.fillRect(960 + ww, 540 - hh, 960 - ww, 2 * hh);
      if (hh < 60) { g.fillStyle = `rgb(255 255 255 / ${1 - hh / 60})`; g.fillRect(960 - ww, 540 - hh, 2 * ww, 2 * hh); }
    }
    return F;
  });

  // ---------- V1.9 Sam got fired, then rehired: SAM ALTMAN goes up in flames; on "rehired" the fire runs backward ----------
  mline('V1', 9, (t, s, E, g) => {
    const lt = t - s.start, tF = wt(s, 2), tR = wt(s, 4);
    const S = MOD.shapeText('SAM ALTMAN'), hy = .52, hx = hy * S.aspect, FR = fireFor('SAM ALTMAN'), P = [0, .05 - (1 - 2 * FR.T.box[3]) * hy, 0];
    // (after "rehired" the flames are shown at the mirrored time: they run back into the letters)
    const back = t >= tR, tt = back ? 2 * tR - t : t, rate = 3.6, tf = back ? Math.max(tF, tR - (t - tR) * rate) : t;
    const burn = t >= tF ? clamp((tf - tF) / (tR - tF)) : 0, heal = back ? clamp((t - tR) * rate / (tR - tF)) : 0;
    const F = {
      ro: [Math.sin(lt * .45) * 1.2, 3.2, 7.0 - lt * .3], ta: [0, .75, 0], fov: 1.45,
      skyA: '#03050b', skyB: lerpHex('#0a1222', '#2a0c04', burn), acc: burn > .05 ? '#ff7a2a' : '#6a8adf', fog: .025, floorCol: '#020306', grid: .1,
      shape: { key: 'SAM ALTMAN', src: S, p: P, rot: rotYX(Math.sin(t * .7) * .05), s: [hx, hy, .18], col: lerpHex('#2a2e3a', '#120604', burn), rim: lerpHex('#aab8e8', '#ff8030', burn), metal: 1 },
      panels: [], light: { p: [0, 4, 4], c: '#c8d4ff', k: 4, vol: 0 },
    };
    if (burn > 0) {
      const flick = .8 + .2 * Math.sin(t * 37) * Math.sin(t * 23), p = MOD.panel(1);
      p.drawImage(flames(FR, tt, Math.min(1.1, burn * 1.6)), 0, 0, 1024, 512);
      F.panels.push({ ...firePane(P, hx, hy, 0), alpha: 1, gain: 2.3, glass: 0, tex: 1 });
      F.light = { p: [0, 2.2, 1.6], c: '#ff8a3c', k: (4 + 6 * burn) * flick, vol: .35 };
    }
    if (t >= tF && t < tF + .12) { F.flash = .18; F.flashCol = '#ffb060'; }
    label(g, 'OPENAI · CEO', back ? 190 : 70, 108, { size: 32, color: 'rgb(205 215 255 / .85)' });
    // the VCR's rewind
    if (back && frac(t * 3) < .65) {
      g.save(); g.fillStyle = '#ffffff'; g.shadowColor = 'rgb(0 0 0 / .8)'; g.shadowOffsetX = 4; g.shadowOffsetY = 4;
      for (const x0 of [74, 124]) { g.beginPath(); g.moveTo(x0 + 46, 64); g.lineTo(x0, 94); g.lineTo(x0 + 46, 124); g.fill(); }
      g.restore();
    }
    // (the CRT that V1.8 switched off comes back on: the dot opens to a line, the line to the picture)
    const on = clamp(lt / .13);
    if (on < 1) {
      const ww = on < .4 ? lerp(4, 960, easeOut(on / .4)) : 960, hh = on < .4 ? 2 : lerp(2, 540, easeOut((on - .4) / .6));
      g.fillStyle = '#000'; g.fillRect(0, 0, 1920, 540 - hh); g.fillRect(0, 540 + hh, 1920, 540 - hh); g.fillRect(0, 540 - hh, 960 - ww, 2 * hh); g.fillRect(960 + ww, 540 - hh, 960 - ww, 2 * hh);
      if (hh < 60) { g.fillStyle = `rgb(255 255 255 / ${1 - hh / 60})`; g.fillRect(960 - ww, 540 - hh, 2 * ww, 2 * hh); }
      F.scroller = false; F.date = false;
    }
    return F;
  });

  // ---------- V1.10 Weekend chaos, board expired: the violet checkerboard spun wildly; on "expired" it falls away ----------
  let TILE = null;
  function tileTex() {
    if (TILE) return TILE;
    const c = makeCanvas(1024, 512), g = c.getContext('2d');
    g.fillStyle = '#2a1458'; g.fillRect(0, 0, 512, 512); g.fillStyle = '#c8b4ff'; g.fillRect(512, 0, 512, 512);
    g.strokeStyle = 'rgb(255 255 255 / .35)'; g.lineWidth = 8; g.strokeRect(4, 4, 1016, 504);
    return (TILE = c);
  }
  const DAYS = ['FRI', 'SAT', 'SUN', 'MON', 'TUE'];
  mline('V1', 10, (t, s, E, g) => {
    const lt = t - s.start, d = s.end - s.start, tE = wt(s, 3), chaos = 1 + 2.2 * lt / d, a = t >= tE ? t - tE : 0;
    const yaw = t * .5 + Math.sin(t * 2.3) * .45 * chaos, rise = 130 * a * a + a * 6;
    const ro = [0, 1.5 + rise, 0], look = [Math.sin(yaw), -.32 - Math.min(.5, a * 2), -Math.cos(yaw)];
    const F = {
      ro, ta: add(ro, mul(look, 5)), fov: 1.35, roll: Math.sin(t * 1.9) * .22 * chaos,
      skyA: '#06020e', skyB: '#1e0c3c', acc: '#9a6ee8', fog: .025 + a * .5,
      sky: { mode: 'stars', k: .2, col: '#d0c0ff' },
      floorMode: 'checker', floorCol: '#2a1458', floorCol2: '#c8b4ff', floorTile: 1.3, floorOff: [Math.sin(t * 2.1) * 1.5 * chaos, -t * 5],
      panels: [],
    };
    // the squares nearest the fall break off and tumble
    if (a > 0) {
      const P = MOD.panel(2); P.drawImage(tileTex(), 0, 0);
      for (let i = 0; i < 6; i++) {
        const h1 = hash(i * 3 + 1), h2 = hash(i * 3 + 2), f = Math.max(0, a - h1 * .12), Rt = rot3((h1 - .5) * 9 * f, (h2 - .5) * 5 * f, (h2 - .3) * 7 * f);
        const c = [ro[0] + look[0] * 3 + (h1 - .5) * 5, ro[1] - 1.4 - f * f * 30 - f * 2, ro[2] + look[2] * 3 + (h2 - .5) * 4];
        F.panels.push({ c, u: mv(Rt, [.9, 0, 0]), v: mv(Rt, [0, 0, .45]), alpha: 1, gain: 1.3, glass: .3, tex: 2 });
      }
    }
    // the days flip on the beats
    const k = clamp(Math.floor(bt(t) - bt(s.start) + .3), 0, 4), tk = beatT(Math.ceil(bt(s.start) - 1e-3) + k) - .3 * beatLen(), flip = easeOut(clamp((t - Math.max(s.start, tk)) / .09));
    g.save(); g.translate(960, 230); g.scale(1, Math.max(.05, flip)); chromeText(g, DAYS[k], 0, 60, 170, STEEL, { stroke: 20 }); g.restore();
    label(g, 'STAFF LETTER · 700+ OF ~770 SIGN', 960, 346, { align: 'center', size: 32, color: '#e0d0ff' });
    return F;
  });

  // ---------- V1.11 Ilya saw what Ilya saw: one eye above still water, looking down at its reflection; in the reflection's pupil, a point ----------
  mline('V1', 11, (t, s, E, g) => {
    const lt = t - s.start, tSaw2 = wt(s, 4), P = { c: [0, 1.34, 0], u: [2.5, 0, 0], v: [0, 1.25, 0] };
    const p = MOD.panel(0);
    // the eye: almond lids, the white, an iris low in it (looking down), the pupil
    const lid = (k, up) => { const x = 110 + k * 1828, e = Math.sin(k * Math.PI); return [x, 520 - (up ? 400 * e ** .8 : -300 * e ** 1.1)]; };
    const almond = () => {
      p.beginPath();
      for (let i = 0; i <= 40; i++) { const [x, y] = lid(i / 40, true); i ? p.lineTo(x, y) : p.moveTo(x, y); }
      for (let i = 40; i >= 0; i--) { const [x, y] = lid(i / 40, false); p.lineTo(x, y); }
      p.closePath();
    };
    p.save(); almond();
    const sc = p.createRadialGradient(1024, 560, 60, 1024, 520, 900); sc.addColorStop(0, '#f4fbff'); sc.addColorStop(.6, '#b8d8e0'); sc.addColorStop(1, '#3a6a78');
    p.fillStyle = sc; p.fill(); p.save(); p.clip();
    const ix = 1024, iy = 640, ir = 290, pr = 104 + 14 * kick(t, 4);
    const ig = p.createRadialGradient(ix, iy, pr * .6, ix, iy, ir); ig.addColorStop(0, '#0a3a44'); ig.addColorStop(.5, '#1ea8b4'); ig.addColorStop(.85, '#0c5a66'); ig.addColorStop(1, '#042a30');
    p.fillStyle = ig; p.beginPath(); p.arc(ix, iy, ir, 0, TAU); p.fill();
    p.fillStyle = '#02080a'; p.beginPath(); p.arc(ix, iy, pr, 0, TAU); p.fill();
    p.fillStyle = 'rgb(255 255 255 / .85)'; p.beginPath(); p.ellipse(ix - 110, iy - 120, 42, 30, -.5, 0, TAU); p.fill();
    p.fillStyle = 'rgb(10 30 40 / .35)'; p.fillRect(0, 0, 2048, 300);   // (the upper lid's shadow)
    p.restore();
    almond(); p.lineWidth = 16; p.strokeStyle = '#e8f4f8'; p.lineJoin = 'round'; p.stroke();
    p.restore();
    // the iris: rings of turning teal bobs over it
    const irisW = onPanel(P, ix, iy, 2048, 1024), wr = ir / 1024 * 2 * P.u[0], spheres = [];
    for (let r = 0; r < 2; r++) {
      const n = r ? 10 : 16, rr = wr * (r ? .52 : .8), dir = r ? -1 : 1;
      for (let i = 0; i < n; i++) { const a = i / n * TAU + t * .7 * dir; spheres.push([irisW[0] + Math.cos(a) * rr, irisW[1] + Math.sin(a) * rr * .96, .09, r ? .045 : .06, r ? '#8cf0ee' : '#1ea8b4']); }
    }
    const F = {
      ro: [Math.sin(lt * .35) * .6, .25, 8.4], ta: [0, .3, 0], fov: 1.5,
      skyA: '#01181e', skyB: '#0e6070', acc: '#4ff0e0', fog: .012,
      floorMode: 'water', water: .004 + .002 * Math.sin(t * 2), floorCol: '#01080a',
      panels: [{ ...P, alpha: 1, gain: 1.35, glass: 0, tex: 0 }], spheres, sphCol: '#1ea8b4',
      light: { p: [0, 4, 5], c: '#bff8ff', k: 4, vol: 0 },
    };
    // its reflection: the eye pane mirrored under the waterline, rippling (the floor's own reflection of a pane softens to sky)
    const top = toUI(F, [-P.u[0], -(P.c[1] - P.v[1]), 0]), bot = toUI(F, [P.u[0], -(P.c[1] + P.v[1]), 0]);
    if (top && bot) {
      const src = MOD.PAN[0].c, N = 56, x0 = top[0], x1 = bot[0], y0 = top[1], y1 = bot[1];
      g.save();
      for (let k = 0; k < N; k++) {
        const f0 = k / N, yy = lerp(y0, y1, f0), hh = (y1 - y0) / N + 1, sy = f0 * 1024;
        const dx = Math.sin(yy * .09 - t * 3.1) * (3 + 9 * f0) + Math.sin(yy * .031 + t * 1.7) * 4;
        g.globalAlpha = .55 * (1 - f0 * .55);
        g.drawImage(src, 0, 1024 - sy - 1024 / N, 2048, 1024 / N, x0 + dx, yy, x1 - x0, hh);
      }
      g.globalCompositeOperation = 'source-atop'; g.globalAlpha = .35; g.fillStyle = '#0a4a58'; g.fillRect(x0 - 20, y0, x1 - x0 + 40, y1 - y0);
      g.restore();
    }
    // in the reflection's pupil, one bright point, what he saw; it flares on the second "saw"
    const pq = toUI(F, [irisW[0], -irisW[1], 0]);
    if (pq) {
      const fl = t >= tSaw2 ? Math.exp(-(t - tSaw2) * 3.2) : 0, x = pq[0] + Math.sin(t * 5.3) * 3, y = pq[1] + Math.sin(t * 7.1) * 2;
      const R = 10 + 6 * kick(t, 5) + 90 * fl;
      g.save(); g.globalCompositeOperation = 'lighter';
      const gr = g.createRadialGradient(x, y, 0, x, y, R * 2.4); gr.addColorStop(0, 'rgb(255 255 255 / 1)'); gr.addColorStop(.2, 'rgb(200 255 250 / .8)'); gr.addColorStop(1, 'rgb(80 240 230 / 0)');
      g.fillStyle = gr; g.beginPath(); g.ellipse(x, y, R * 2.4 * 1.3, R * 2.4, 0, 0, TAU); g.fill();
      if (fl > .02) {
        g.strokeStyle = `rgb(220 255 250 / ${fl})`; g.lineCap = 'round';
        for (const [dx, dy, L] of [[1, 0, 1], [0, 1, .55], [.7, .7, .35], [.7, -.7, .35]]) { g.lineWidth = 3 + 5 * fl; g.beginPath(); g.moveTo(x - dx * L * 520 * fl, y - dy * L * 520 * fl); g.lineTo(x + dx * L * 520 * fl, y + dy * L * 520 * fl); g.stroke(); }
      }
      g.restore();
      if (fl > .05) { F.flash = fl * .09; F.flashCol = '#c8fff8'; }
    }
    return F;
  });

  // ---------- V1.12 EU writes the AI law: twelve gold stars in a ring tilt up and turn; the Act's first page types ----------
  function starPath(g, x, y, r) { g.beginPath(); for (let i = 0; i < 10; i++) { const a = i / 10 * TAU - Math.PI / 2, rr = i % 2 ? r * .4 : r; g.lineTo(x + Math.cos(a) * rr, y + Math.sin(a) * rr); } g.closePath(); }
  const ACT = [['REGULATION (EU) 2024/1689', 76, '#10183a'], ['LAYING DOWN HARMONISED RULES', 50, '#2a3050'], ['ON ARTIFICIAL INTELLIGENCE', 50, '#2a3050'], ['ARTICLE 5 · PROHIBITED AI PRACTICES', 46, '#1846c8'], ['PARLIAMENT 523–46 · COUNCIL 21 MAY 2024', 42, '#5a6078']];
  mline('V1', 12, (t, s, E, g) => {
    const lt = t - s.start, tW = wt(s, 1), tilt = lerp(1.2, .12, easeOut(clamp(lt / .55)));
    const p = MOD.panel(1);
    for (let i = 0; i < 12; i++) {
      const a = i / 12 * TAU + t * .6, x = 512 + Math.cos(a) * 196, y = 256 + Math.sin(a) * 196;
      starPath(p, x + 4, y + 5, 52); p.fillStyle = 'rgb(20 30 80 / .6)'; p.fill();
      starPath(p, x, y, 52); p.fillStyle = MOD.chrome(p, y - 52, y + 40, ['#fffdf0', '#ffe487', '#dfa826', '#b07a10']); p.fill();
    }
    const SC = [-1.55, 2.65, 0], v = [0, 1.25 * Math.cos(tilt), -1.25 * Math.sin(tilt)], n = [0, Math.sin(tilt), Math.cos(tilt)];
    const F = {
      ro: [Math.sin(lt * .4) * .8, 2.3, 8.2 - lt * .25], ta: [.2, 2.55, 0], fov: 1.5,
      skyA: '#030a2e', skyB: '#1440b0', acc: '#3a6aff', fog: .015, floorCol: '#020618', grid: .15,
      sky: { mode: 'rays', k: .6, col: '#5a86f0' },
      panels: [{ c: SC, u: [2.5, 0, 0], v, alpha: 1, gain: 1.8, glass: 0, tex: 1 }],
      halo: { p: add(SC, mul(n, -.03)), n, R: 196 / 256 * 1.25, r: .02, k: .3 + .25 * kick(t, 5), col: '#ffd27a' },
      light: { p: [0, 5, 5], c: '#ffe8b0', k: 5, vol: 0 },
    };
    // the Act's first page, sliding in on "writes" and typing
    if (t >= tW - .1) {
      const q = MOD.panel(0), k = easeOut(clamp((t - tW + .1) / .25));
      q.fillStyle = '#f4f2ea'; q.fillRect(0, 0, 2048, 1024);
      q.fillStyle = '#1846c8'; q.fillRect(0, 0, 2048, 22);
      let y = 170;
      ACT.forEach(([str, sz, col], i) => { const n = Math.floor(clamp((t - tW - i * .09) / .2) * str.length); text(q, str, 90, y, { size: sz, font: i ? MOD.FONT_M : MOD.FONT_T, n, color: col }); y += sz * 1.75 + (i === 0 || i === 2 ? 40 : 0); });
      for (let j = 0; j < 4; j++) { q.fillStyle = 'rgb(40 48 80 / .18)'; q.fillRect(90, 800 + j * 44, 1700 - (j * 290) % 600, 18); }
      F.panels.push({ c: [lerp(7, 2.35, k), 2.55, .5], u: [2.05 * Math.cos(.35), 0, -2.05 * Math.sin(.35)], v: [0, 1.025, 0], alpha: .96, gain: 1.05, glass: .4, tex: 0 });
    }
    return F;
  });

  // ---------- V1.13 Strawberry thinks, link by link: a chain forged one link per eighth, a strawberry swinging from its end ----------
  let BERRY = null;
  function berryTex() {
    if (BERRY) return BERRY;
    const c = makeCanvas(1024, 512), g = c.getContext('2d'), cx = 512;
    // the body: a rounded heart of red, lit from the upper left
    g.beginPath(); g.moveTo(cx, 492); g.bezierCurveTo(cx - 150, 430, cx - 225, 230, cx - 175, 150); g.bezierCurveTo(cx - 130, 85, cx - 40, 95, cx, 110);
    g.bezierCurveTo(cx + 40, 95, cx + 130, 85, cx + 175, 150); g.bezierCurveTo(cx + 225, 230, cx + 150, 430, cx, 492); g.closePath();
    const rg = g.createRadialGradient(cx - 60, 190, 20, cx, 280, 260); rg.addColorStop(0, '#ff8a8a'); rg.addColorStop(.35, '#e81830'); rg.addColorStop(.8, '#9a0418'); rg.addColorStop(1, '#4a0008');
    g.fillStyle = rg; g.fill(); g.save(); g.clip();
    // gold seeds, in rows
    for (let r = 0; r < 9; r++) for (let k = -5; k <= 5; k++) {
      const y = 150 + r * 38 + (k & 1) * 19, x = cx + k * 34 * (1 - r / 13) + (r & 1) * 17;
      g.fillStyle = '#6a0010'; g.beginPath(); g.ellipse(x + 2, y + 3, 7, 10, 0, 0, TAU); g.fill();
      g.fillStyle = '#ffd24a'; g.beginPath(); g.ellipse(x, y, 5, 8, 0, 0, TAU); g.fill();
    }
    g.restore();
    // the leaves and the stem
    for (let i = 0; i < 6; i++) {
      const a = Math.PI + (i + .5) / 6 * Math.PI, L = 120 + (i % 2) * 30;
      g.fillStyle = i % 2 ? '#2a9a48' : '#1a7a34';
      g.beginPath(); g.moveTo(cx, 112); g.quadraticCurveTo(cx + Math.cos(a - .35) * L * .6, 112 + Math.sin(a - .35) * L * .45 + 30, cx + Math.cos(a) * L, 116 + Math.sin(a) * L * .5 + 40); g.quadraticCurveTo(cx + Math.cos(a + .35) * L * .6, 112 + Math.sin(a + .35) * L * .45 + 30, cx, 112); g.fill();
    }
    g.fillStyle = '#2a7a38'; g.fillRect(cx - 8, 20, 16, 96);
    return (BERRY = c);
  }
  mline('V1', 13, (t, s, E, g) => {
    const lt = t - s.start, a = (t - s.start) / EIGHTH(), n = Math.min(8, Math.floor(a) + 2), grow = n === 8 && a >= 7 ? 1 : easeOut(clamp(frac(a) / .3));
    const swing = Math.sin(t * 3.1) * .2, top = [.6, 6.3, 0], dir = [Math.sin(swing), -Math.cos(swing), 0], step = .4;
    const spheres = [];
    for (let i = 0; i < n; i++) {
      const g1 = i === n - 1 ? grow : 1, c = add(top, mul(dir, (i + 1) * step - (1 - g1) * step * .5));
      spheres.push([...c, (i % 2 ? .13 : .19) * (.3 + .7 * g1), i === n - 1 && grow < 1 ? '#ffffff' : '#c8ccd8']);
    }
    const end = add(top, mul(dir, n * step + .25 - (1 - grow) * step * .5)), p = MOD.panel(1);
    p.drawImage(berryTex(), 0, 0);
    const uu = [Math.cos(swing) * 1.6, Math.sin(swing) * 1.6, 0], vv = [-Math.sin(swing) * .8, Math.cos(swing) * .8, 0];
    const F = {
      ro: [Math.sin(lt * .5) * .8, 3.2, 7.6], ta: [.3, 3.2, 0], fov: 1.5,
      skyA: '#141826', skyB: '#3a4260', acc: '#ff4050', fog: .02, floorCol: '#08090f', grid: .1,
      spheres, sphCol: '#c8ccd8', panels: [{ c: add(end, mul(vv, -1)), u: uu, v: vv, alpha: 1, gain: 1.35, glass: 0, tex: 1 }],
      light: { p: [-3, 6, 5], c: '#ffffff', k: 5, vol: 0 },
    };
    if (grow < 1) { const c = spheres.at(-1); F.beam = { x: c[0], z: c[2], y0: c[1] - .01, y1: c[1] + .01, r: .045, k: 1.6 * (1 - grow), col: '#ffe8f0' }; }
    label(g, 'o1-preview · “Strawberry”', 70, 88, { size: 36, color: '#ffffff' });
    label(g, 'Thinking' + '.'.repeat(1 + Math.floor(t * 4) % 3), 70, 136, { size: 32, color: 'rgb(205 215 255 / .7)' });
    return F;
  });

  // ---------- V1.14 Newsom vetoes, doesn't blink: the bill's cover spins in; VETO slams over it; the page spins away ----------
  let BILL = null;
  function billTex() {
    if (BILL) return BILL;
    const c = makeCanvas(2048, 1024), g = c.getContext('2d');
    g.fillStyle = '#f4f2ea'; g.fillRect(0, 0, 2048, 1024);
    g.strokeStyle = '#1a1a24'; g.lineWidth = 4; g.strokeRect(40, 40, 1968, 944);
    text(g, 'CALIFORNIA LEGISLATURE', 1024, 130, { size: 40, align: 'center', color: '#3a3a48' });
    text(g, 'SENATE BILL', 1024, 250, { size: 70, align: 'center', color: '#1a1a24' });
    text(g, 'No. 1047', 1024, 400, { size: 130, font: MOD.FONT_T, align: 'center', color: '#101018' });
    ['SAFE AND SECURE INNOVATION FOR FRONTIER', 'ARTIFICIAL INTELLIGENCE MODELS ACT'].forEach((l, i) => text(g, l, 1024, 520 + i * 70, { size: 52, align: 'center', color: '#1a1a24' }));
    for (let j = 0; j < 6; j++) { g.fillStyle = 'rgb(30 30 40 / .22)'; g.fillRect(200, 700 + j * 42, 1648 - (j * 370) % 700, 18); }
    return (BILL = c);
  }
  mline('V1', 14, (t, s, E, g) => {
    const lt = t - s.start, tV = wt(s, 1), inK = easeOut(clamp(lt / .32)), out = t > tV + .7 ? easeIn(clamp((t - tV - .7) / .36)) : 0;
    const p = MOD.panel(0); p.drawImage(billTex(), 0, 0);
    const ang = (1 - inK) * 4 + out * 3 - .06, sc = lerp(.2, 1, inK) * (1 - out * .7), cx = -out * 6;
    const u = [Math.cos(ang) * 2.6 * sc, Math.sin(ang) * 2.6 * sc, 0], v = [-Math.sin(ang) * 1.3 * sc, Math.cos(ang) * 1.3 * sc, 0];
    const F = {
      ro: [Math.sin(lt * .4) * .5, 2.5, 7.4], ta: [0, 2.6, 0], fov: 1.5,
      skyA: '#120a02', skyB: '#5a3c0c', acc: '#ffc040', fog: .015, floorCol: '#080502', grid: .12,
      sky: { mode: 'rays', k: .35, col: '#8a6a20' },
      panels: [{ c: [cx, 2.7, 0], u, v, alpha: 1, gain: 1.05, glass: .3, tex: 0 }],
      light: { p: [0, 5, 5], c: '#ffe8b0', k: 5, vol: 0 },
    };
    if (t >= tV) {
      const S = MOD.shapeText('VETO'), hy = .75, a = t - tV, k = easeIn(clamp(a / .1));
      F.shape = { key: 'VETO', src: S, p: [cx * 1.1, 2.6 - out * 1.5, lerp(6.2, .9, k)], rot: rotYX(out * 3 + Math.sin(t * 2) * .06, -.05, -.12 + out * 2), s: [hy * S.aspect, hy, .24], col: '#b0207a', rim: '#ffb0e6', metal: 1 };
      if (a > .08 && a < .2) { F.flash = .2; F.flashCol = '#ff9ad8'; F.ro = add(F.ro, [Math.sin(t * 90) * .06, Math.cos(t * 70) * .05, 0]); }
    }
    // the governor's cursor, which doesn't blink
    text(g, 'GOV >', 1510, 830, { size: 44, color: '#ffffff', stroke: 7 });
    g.fillStyle = '#ffffff'; g.fillRect(1664, 796, 26, 42);
    label(g, 'SB 1047 · SEP 29 2024', 70, 84, { color: '#ffe0a8' });
    return F;
  });

  // ---------- V1.15 Hinton takes his medal, scolds: a gold medal spins over a blue sunburst; on "scolds" it stops dead and turns red ----------
  const DISC = (() => {   // a disc's signed distance field (texels, outside positive, rows bottom to top), for the medal
    const w = 256, h = 256, R = 104, img = new Float32Array(w * h);
    for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) img[y * w + x] = clamp(Math.hypot(x + .5 - w / 2, y + .5 - h / 2) - R, -48, 48);
    return { img, w, h, aspect: 1 };
  })();
  function medalFace(g, red) {
    // the face, struck in gold (the disc's own rim shows around it): a lit gradient, two engraved rings, NOBEL
    const cx = 512, cy = 256, gr = g.createRadialGradient(cx - 90, cy - 110, 20, cx, cy, 250);
    (red ? ['#ffc0b0', '#e83a2a', '#a01010', '#4a0404'] : ['#fff6d0', '#f0c048', '#b07a14', '#5a3a06']).forEach((c, i) => gr.addColorStop(i / 3, c));
    g.fillStyle = gr; g.beginPath(); g.arc(cx, cy, 244, 0, TAU); g.fill();
    g.lineWidth = 7; g.strokeStyle = red ? 'rgb(70 0 0 / .6)' : 'rgb(90 55 5 / .55)';
    g.beginPath(); g.arc(cx, cy, 212, 0, TAU); g.stroke(); g.beginPath(); g.arc(cx, cy, 194, 0, TAU); g.stroke();
    g.lineWidth = 3; g.strokeStyle = red ? 'rgb(255 200 190 / .5)' : 'rgb(255 245 200 / .55)';
    g.beginPath(); g.arc(cx - 2, cy - 2, 212, Math.PI * .9, Math.PI * 1.6); g.stroke();
    g.font = `76px ${MOD.FONT_T}`; g.textAlign = 'center'; g.textBaseline = 'middle';
    g.fillStyle = red ? 'rgb(255 190 180 / .6)' : 'rgb(255 250 220 / .6)'; g.fillText('NOBEL', cx - 3, cy - 3);
    g.fillStyle = red ? 'rgb(60 0 0 / .85)' : 'rgb(90 55 5 / .85)'; g.fillText('NOBEL', cx + 2, cy + 3);
    g.fillStyle = red ? '#c02018' : '#d8a032'; g.fillText('NOBEL', cx, cy);
  }
  mline('V1', 15, (t, s, E, g) => {
    const lt = t - s.start, tS = wt(s, 4), stop = t >= tS, red = stop ? clamp((t - tS) / .12) : 0;
    const spin = stop ? 0 : (t - tS) * 5.2, tiltX = .08;
    const hy = 1.3, rad = hy * 104 / 128, depth = .1, P = [-1.35, 2.65, 0], R = rot3(tiltX, spin, 0);
    const p = MOD.panel(1); medalFace(p, red > .5);
    const F = {
      ro: [Math.sin(lt * .4) * .5, 2.5, 7.8 - lt * .2], ta: [.3, 2.6, 0], fov: 1.5,
      skyA: lerpHex('#03082a', '#200204', red), skyB: lerpHex('#1440b0', '#8a0a0a', red), acc: lerpHex('#ffc040', '#ff2020', red), fog: .015, floorCol: '#020410', grid: .1,
      sky: { mode: 'rays', k: stop ? 0 : .5, col: lerpHex('#4a7af0', '#ff4030', red) },
      shape: { key: 'medal', src: DISC, p: P, rot: rotYX(spin, tiltX), s: [hy, hy, depth], col: lerpHex('#c08a20', '#a01010', red), rim: lerpHex('#ffe487', '#ff5040', red), metal: 1 },
      panels: [
        { c: add(P, mv(R, [0, 0, depth + .012])), u: mv(R, [2 * rad, 0, 0]), v: mv(R, [0, rad, 0]), alpha: 1, gain: 1.25, glass: 0, tex: 1 },
        { c: add(P, mv(R, [0, 0, -depth - .012])), u: mv(R, [-2 * rad, 0, 0]), v: mv(R, [0, rad, 0]), alpha: 1, gain: 1.25, glass: 0, tex: 1 },
      ],
      light: { p: [3, 5, 5], c: red > .5 ? '#ff6050' : '#fff0c0', k: 6, vol: 0 },
    };
    if (stop && t - tS < .1) { F.flash = .2; F.flashCol = '#ff4040'; }
    chromeText(g, 'NOBEL', 1280, 420, 130, red > .5 ? ['#ffffff', '#ffb0a0', '#e02020', '#5a0404'] : GOLD);
    label(g, 'PHYSICS · 2024', 1280, 490, { align: 'center', size: 36, color: red > .5 ? '#ffb0a0' : '#ffe0a8' });
    label(g, 'GEOFFREY HINTON', 1280, 540, { align: 'center', size: 36, color: '#ffffff' });
    // the scold: a warning triangle pulses beside the stopped medal
    if (stop) {
      const k = (.6 + .4 * kick8(t, 4)) * red, cx = 1280, cy = 690, r = 86;
      g.save(); g.globalAlpha = k; g.lineJoin = 'round';
      g.fillStyle = '#ff2a2a'; g.beginPath(); g.moveTo(cx, cy - r); g.lineTo(cx + r * 1.05, cy + r * .75); g.lineTo(cx - r * 1.05, cy + r * .75); g.closePath(); g.fill();
      g.lineWidth = 8; g.strokeStyle = '#ffffff'; g.stroke();
      g.fillStyle = '#ffffff'; g.fillRect(cx - 8, cy - 42, 16, 62); g.fillRect(cx - 8, cy + 34, 16, 16);
      g.restore();
    }
    return F;
  });

  // ---------- V1.16 Demis wins for protein folds: a chain of spheres folds into helices, coloured like AlphaFold's confidence ----------
  const PL = { vh: '#0053d6', h: '#65cbf3', l: '#ffdb13', vl: '#ff7d45' };   // AlphaFold's pLDDT colours: very high, confident, low, very low
  const FOLD = (() => {
    const out = [];
    for (let i = 0; i < 32; i++) {
      let p, c;
      if (i < 2) { p = [-1.6 + i * .5, .1 - i * .3, .8]; c = PL.vl; }
      else if (i < 14) { const j = i - 2, a = j * 1.75; p = [-1.1 + Math.cos(a) * .62, -.2 + j * .22, Math.sin(a) * .62]; c = j > 1 && j < 11 ? PL.vh : PL.h; }
      else if (i < 18) { const k = (i - 14) / 3; p = [-.55 + k * 1.1, 2.7 + Math.sin(k * Math.PI) * .4, -.3 + k * .3]; c = i === 14 || i === 17 ? PL.h : PL.l; }
      else if (i < 30) { const j = i - 18, a = j * 1.75 + 1; p = [1.1 + Math.cos(a) * .62, 2.45 - j * .22, Math.sin(a) * .62]; c = j > 1 && j < 11 ? PL.vh : PL.h; }
      else { const k = i - 30; p = [1.7 + k * .5, -.1 - k * .2, .6]; c = PL.vl; }
      out.push({ fold: p, col: c, line: [-5.2 + i * 10.4 / 31, 1.6, 0] });
    }
    return out;
  })();
  mline('V1', 16, (t, s, E, g) => {
    const lt = t - s.start, d = s.end - s.start, tB = beatOf(s), k = easeInOut(clamp((t - tB) / (d * .7)));
    const R = rot3(.12 * k, (lt * .7 - .3) * k, 0), C = [.45 * k, 1.45, 0];
    const pts = FOLD.map((q, i) => {
      const f = easeInOut(clamp(k * 1.5 - (Math.abs(i - 15.5) / 16) * .5));
      const loc = [lerp(q.line[0], q.fold[0], f), lerp(q.line[1], q.fold[1], f) + Math.sin(i * .6 + t * 4) * .12 * (1 - f), lerp(q.line[2], q.fold[2], f)];
      return add(C, mv(R, loc));
    });
    const F = {
      ro: [Math.sin(lt * .4) * .6, 2.55, 8.6], ta: [0, 2.6, 0], fov: 1.5,
      skyA: '#02040e', skyB: '#06123a', acc: '#65cbf3', fog: .015, floorCol: '#01020a', grid: .12,
      sky: { mode: 'stars', k: .2, col: '#9ac8ff' },
      spheres: pts.map((p, i) => [...p, .25, FOLD[i].col]), light: { p: [2, 6, 5], c: '#ffffff', k: 5, vol: 0 },
    };
    // its backbone, traced between them
    g.save(); g.lineWidth = 3; g.strokeStyle = 'rgb(200 225 255 / .3)'; g.lineJoin = 'round'; g.beginPath();
    pts.forEach((p, i) => { const q = toUI(F, p); if (q) i ? g.lineTo(q[0], q[1]) : g.moveTo(q[0], q[1]); });
    g.stroke(); g.restore();
    chromeText(g, 'ALPHAFOLD', 70, 150, 96, ['#ffffff', '#b8e4ff', '#2a8ae8', '#0a2a78'], { align: 'left' });
    label(g, 'NOBEL · CHEMISTRY · 2024 · HASSABIS & JUMPER', 74, 204, { size: 30 });
    return F;
  });
})();

;
// ---- styles/demoscene/modern/m_chorus.js ----
// modern/m_chorus.js: the four choruses in the modern engine (Softmax's parts). Each is built on the song's central image, an
// exponential climbing up and to the right (Epoch AI's training compute, ×4–5 a year), with her words riding it as she sings them,
// and each escalates the one before:
//   C1 (version B only): a plasma sky; the curve is born on one glass chart; on "can't contain it" it bursts through the demo's border
//     and climbs off the top of the screen; then eight "Deep"s down a DeepSeek-blue tunnel.
//   C2 (version A at fx 2, B at fx 4): a spiralling dot tunnel; two curves, compute and capabilities, climb together with vector bobs
//     at their heads; on "contain" both break out and the bobs burst into a starfield; then "Molt, molt, molt, molt": failed switches
//     to text mode, one per sung "Molt", until MOLT holds on "Moltbook".
//   C3: the chart on a violet checkerboard; her words burn as they ride and the curve catches fire at the top; on "contain" it breaks
//     out as a beam of light.
//   C4, the end part: the megamix (one scene per line), the starfield's pace and race, the last hook, the CRT switching off, and
//     the dot that trains on: an EPOCH counter climbing exponentially while the dot grows back into the picture.
(() => {
  const { add, mul, mix3, rotYX, text } = MOD;
  const lineAt = (sec, n) => LINES.find(l => l.sec === sec && l.n === n);
  const Wd = (sec, n) => wordsOf(lineAt(sec, n));
  const curOf = (ws, t) => { let k = -1; for (let i = 0; i < ws.length; i++) if (t >= ws[i].t0) k = i; return k; };
  const MAGC = ['#ffffff', '#ffd0ef', '#ff4fb4', '#8a0f60'], CYANC = ['#ffffff', '#c6f4ff', '#35c2f2', '#0a4a86'];

  // ---------- panels: texture ↔ world ↔ screen ----------
  const CH = { c: [0, 2.35, -.5], u: [4.3, 0, 0], v: [0, 2.15, 0] };   // the chart panel (2048 × 1024)
  const toWorld = (P, x, y, w = 2048, h = 1024) => add(add(P.c, mul(P.u, x / (w / 2) - 1)), mul(P.v, 1 - y / (h / 2)));
  const toScreen = (F, p) => { const q = MOD.project(F, p); return q && [q[0] * 1920, (1 - q[1]) * 1080]; };

  // ---------- the exponential ----------
  // A curve in a chart texture: from (x0, y0) to (x1, y1), growing e^k over its width; a polyline with arc lengths [x, y, s, u].
  const X0 = 150, X1 = 1930, Y0 = 950, Y1 = 70;
  const expY = (u, k, y0, y1) => y0 - (Math.exp(k * u) - 1) / (Math.exp(k) - 1) * (y0 - y1);
  const _polys = new Map();
  function poly(o = {}) {
    const k = o.k ?? 5.2, x0 = o.x0 ?? X0, x1 = o.x1 ?? X1, y0 = o.y0 ?? Y0, y1 = o.y1 ?? Y1, u1 = o.u1 ?? 1, key = [k, x0, x1, y0, y1, u1].join('|');
    let P = _polys.get(key); if (P) return P;
    P = []; let s = 0;
    for (let i = 0, n = 700; i <= n; i++) { const u = i / n * u1, x = x0 + u * (x1 - x0), y = expY(u, k, y0, y1); if (i) s += Math.hypot(x - P[i - 1][0], y - P[i - 1][1]); P.push([x, y, s, u]); }
    P.len = s; P.o = { k, x0, x1, y0, y1 };
    _polys.set(key, P);
    return P;
  }
  function atArc(P, s) {
    let lo = 0, hi = P.length - 1; s = clamp(s, 0, P[hi][2]);
    while (hi - lo > 1) { const m = (lo + hi) >> 1; if (P[m][2] <= s) lo = m; else hi = m; }
    const a = P[lo], b = P[hi], k = (s - a[2]) / (b[2] - a[2] || 1);
    return [lerp(a[0], b[0], k), lerp(a[1], b[1], k), Math.atan2(b[1] - a[1], b[0] - a[0]), lerp(a[3], b[3], k)];
  }
  function arcAtU(P, u) {
    let lo = 0, hi = P.length - 1; if (u >= P[hi][3]) return P.len;
    while (hi - lo > 1) { const m = (lo + hi) >> 1; if (P[m][3] <= u) lo = m; else hi = m; }
    return lerp(P[lo][2], P[hi][2], (u - P[lo][3]) / (P[hi][3] - P[lo][3] || 1));
  }
  // (the curve itself at any u, past the chart's edge too, and where it crosses the texture's top edge)
  const curveAt = (P, u) => { const o = P.o; return [o.x0 + u * (o.x1 - o.x0), expY(u, o.k, o.y0, o.y1)]; };
  const uTop = P => { const o = P.o; return Math.log(1 + o.y0 / (o.y0 - o.y1) * (Math.exp(o.k) - 1)) / o.k; };

  // ---------- the chart: a log of training compute (unlabelled but for its years), its grid, its frame and its curves ----------
  const THEME = {
    c1: { bg: 'rgba(6,6,24,.74)', grid: 'rgba(150,180,255,.17)', label: 'rgba(195,212,255,.85)', frame: 'rgba(170,190,255,.55)' },
    c2: { bg: 'rgba(12,6,32,.62)', grid: 'rgba(170,140,255,.18)', label: 'rgba(218,204,255,.88)', frame: 'rgba(190,160,255,.55)' },
    c3: { bg: 'rgba(40,10,40,.28)', grid: 'rgba(255,120,220,.14)', label: 'rgba(255,190,235,.78)', frame: 'rgba(255,160,230,.5)' },
    c4: { bg: 'rgba(30,4,28,.5)', grid: 'rgba(255,90,200,.17)', label: 'rgba(255,195,236,.85)', frame: 'rgba(255,120,210,.55)' },
  };
  const MAGLINE = ['rgba(255,60,170,.22)', '#ff4fb4', '#ffffff'], CYANLINE = ['rgba(40,180,255,.24)', '#35c2f2', '#eafcff'];
  function chart(g, t, o) {
    const th = THEME[o.theme ?? 'c3'];
    g.fillStyle = th.bg; g.fillRect(0, 0, 2048, 1024);
    g.lineWidth = 2;
    for (let yr = 2010; yr <= 2026; yr += 2) {
      const x = X0 + (yr - 2010) / 16 * (X1 - X0);
      g.strokeStyle = th.grid; g.beginPath(); g.moveTo(x, Y1 - 20); g.lineTo(x, Y0); g.stroke();
      text(g, String(yr), x, Y0 + 44, { size: 26, align: 'center', color: th.label });
    }
    g.globalAlpha = .7;
    for (let i = 0; i <= 8; i++) { const y = Y0 - i / 8 * (Y0 - Y1); g.strokeStyle = th.grid; g.beginPath(); g.moveTo(X0, y); g.lineTo(X1, y); g.stroke(); }
    g.globalAlpha = 1;
    // (no axis title or source line: the curve is the picture, and the annotation page says whose data it is)
    // the frame: red as it strains; broken where the curve got out
    const st = o.strain ?? 0;
    g.lineWidth = 8; g.strokeStyle = st ? `rgba(255,${Math.round(90 - 60 * st)},90,${.6 + .4 * st})` : th.frame;
    g.beginPath();
    if (o.broken === 'corner') { g.moveTo(X1 - 260, 4); g.lineTo(4, 4); g.lineTo(4, 1020); g.lineTo(2044, 1020); g.lineTo(2044, 300); }
    else if (o.broken) { const bx = o.broken; g.moveTo(bx - 64, 4); g.lineTo(4, 4); g.lineTo(4, 1020); g.lineTo(2044, 1020); g.lineTo(2044, 4); g.lineTo(bx + 56, 4); }
    else g.rect(4, 4, 2040, 1016);
    g.stroke();
    if (o.broken && o.broken !== 'corner') {
      // cracks run out from the breach
      g.lineWidth = 3; g.strokeStyle = 'rgba(255,220,245,.55)';
      for (let i = 0; i < 7; i++) {
        let x = o.broken + (hash(i * 5 + 1) - .5) * 40, y = 6, a = Math.PI * (.15 + .7 * hash(i * 5 + 2));
        g.beginPath(); g.moveTo(x, y);
        for (let j = 0; j < 4; j++) { const l = 30 + 60 * hash2(i, j); a += (hash2(j, i + 9) - .5) * .9; x += Math.cos(a) * l; y += Math.sin(a) * l; g.lineTo(x, y); }
        g.stroke();
      }
    }
    // the curves, each up to its arc length
    const tips = [];
    g.lineCap = 'round'; g.lineJoin = 'round';
    for (const c of o.curves ?? []) {
      const end = Math.min(c.arc, c.P.len), cols = c.cols ?? MAGLINE, w = c.w ?? 1;
      [[30, 0], [13, 1], [5, 2]].forEach(([lw, ci]) => {
        g.lineWidth = lw * w; g.strokeStyle = cols[ci]; g.beginPath();
        for (const p of c.P) { if (p[2] > end) break; p[2] ? g.lineTo(p[0], p[1]) : g.moveTo(p[0], p[1]); }
        const tp = atArc(c.P, end); g.lineTo(tp[0], tp[1]); g.stroke();
      });
      const tip = atArc(c.P, end);
      if (c.dot !== false) { g.fillStyle = '#fff'; g.beginPath(); g.arc(tip[0], tip[1], (13 + 6 * kick(t, 6)) * w, 0, TAU); g.fill(); }
      tips.push(tip);
    }
    return tips;
  }
  // Her words riding a curve, laid along its arc as they're sung (the chorus scroller on the curve itself).
  const _ride = new Map();
  function rideLayout(g, ln, size, s0) {
    const key = `${ln.sec}.${ln.n}|${size}|${s0}`; let R = _ride.get(key); if (R) return R;
    g.save(); g.font = `${size}px ${MOD.FONT_T}`;
    R = []; let s = s0;
    wordsOf(ln).forEach((w, wi) => { for (const c of w.w.toUpperCase()) { const cw = g.measureText(c).width; R.push({ c, s: s + cw / 2, wi }); s += cw; } s += g.measureText(' ').width; });
    g.restore();
    R.end = s;
    _ride.set(key, R);
    return R;
  }
  function ride(g, t, r) {
    const ws = r.ws ?? wordsOf(r.ln), L = rideLayout(g, r.ln, r.size, r.s0 ?? 70), cur = curOf(ws, t), lift = r.lift ?? r.size * .9, from = r.from ?? 0;
    g.save(); g.font = `${r.size}px ${MOD.FONT_T}`; g.textAlign = 'center'; g.textBaseline = 'middle'; g.lineJoin = 'round';
    const burning = [];
    for (const ch of L) {
      if (ch.wi > cur) break;
      if (ch.wi < from) continue;
      const [x, y, a] = atArc(r.P, ch.s + (r.shift ?? 0)), pop = ch.wi === cur ? Math.exp(-(t - ws[cur].t0) * 9) : 0;
      const px = x + Math.sin(a) * lift, py = y - Math.cos(a) * lift;
      g.save(); g.translate(px, py); g.rotate(a); g.scale(1 + pop * .5, 1 + pop * .5);
      g.lineWidth = r.size * .18; g.strokeStyle = r.stroke ?? 'rgba(20,0,20,.85)'; g.strokeText(ch.c, 0, 0);
      g.fillStyle = ch.wi === cur ? (r.now ?? '#ffffff') : (r.sung ?? '#ffb8e6'); g.fillText(ch.c, 0, 0);
      g.restore();
      if (r.burn) burning.push([px, py, ch.s, t - ws[ch.wi].t0]);
    }
    g.restore();
    // (her words burn once sung: embers rise off every letter)
    if (burning.length) embers(g, t, burning, r.size);
  }
  function embers(g, t, pts, size) {
    g.save(); g.globalCompositeOperation = 'lighter';
    pts.forEach(([x, y, s, age], i) => {
      const heat = clamp(age / .4);
      for (let j = 0; j < 3; j++) {
        const sd = hash2(Math.round(s), j), a = frac(t * (.9 + .5 * sd) + sd), gen = Math.floor(t * (.9 + .5 * sd) + sd);
        const ex = x + (hash2(gen, j + i * 3) - .5) * size * .8 + Math.sin(a * 5 + j) * 6, ey = y - size * .35 - a * size * 1.9, r = (1 - a) * (4 + 5 * sd) * heat;
        if (r < .6) continue;
        g.fillStyle = `rgba(255,${Math.round(210 - 150 * a)},${Math.round(120 - 90 * a)},${(1 - a) * .85})`;
        g.beginPath(); g.arc(ex, ey, r, 0, TAU); g.fill();
      }
    });
    g.restore();
  }
  // Fire at a point (the curve's tip catching): tongues of flame rising, white-hot at the root, magenta at the tips.
  function flames(g, t, x, y, k, n = 30) {
    if (k <= 0) return;
    g.save(); g.globalCompositeOperation = 'lighter';
    for (let i = 0; i < n; i++) {
      const life = .45 + .35 * hash(i * 7 + 1), ph = t / life + hash(i * 3 + 2), a = frac(ph), gen = Math.floor(ph);
      const dx = (hash2(i, gen) - .5) * 70 * k, rise = a * (150 + 110 * hash2(gen, i + 5)) * k;
      const px = x + dx * (1 - a * .5) + Math.sin(a * 7 + i) * 12 * k, py = y - rise, r = (1 - a * .7) * (24 + 20 * hash2(i + 9, gen)) * k;
      const gr = g.createRadialGradient(px, py, 0, px, py, r);
      gr.addColorStop(0, a < .3 ? `rgba(255,250,220,${.7 * (1 - a)})` : `rgba(255,${Math.round(200 - 170 * a)},${Math.round(90 + 90 * a)},${.6 * (1 - a)})`);
      gr.addColorStop(1, 'rgba(255,40,140,0)');
      g.fillStyle = gr; g.beginPath(); g.arc(px, py, r, 0, TAU); g.fill();
    }
    g.restore();
  }
  // Big words on a 1024 × 512 panel, in centred rows (rows: word indices), the newest in chrome, popping.
  function frontWords(t, ws, rows, size, o = {}) {
    const g = MOD.panel(o.tex ?? 1), cur = curOf(ws, t);
    g.font = `${size}px ${MOD.FONT_T}`; g.textAlign = 'center'; g.textBaseline = 'middle'; g.lineJoin = 'round';
    const lines = rows.map(r => r.filter(i => i <= cur && ws[i].w !== '—')).filter(r => r.length);
    lines.forEach((r, li) => {
      const y = 256 + (li - (lines.length - 1) / 2) * size * 1.08, str = r.map(i => ws[i].w.toUpperCase()).join(' '), now = r.includes(cur);
      const pop = now ? Math.exp(-(t - ws[cur].t0) * 12) : 0, fit = Math.min(1, 980 / g.measureText(str).width);
      g.save(); g.translate(512, y - pop * 12); g.scale(fit, fit);
      g.lineWidth = 12; g.strokeStyle = 'rgba(25,0,20,.9)'; g.strokeText(str, 0, 0);
      g.fillStyle = now ? MOD.chrome(g, -size / 2, size / 2, o.chrome ?? MAGC) : (o.dim ?? '#ff9ad8');
      g.fillText(str, 0, 0);
      g.restore();
    });
    return cur;
  }
  // The extruded chrome SCALING logo, rising (from below the floor, turning) from its time tS.
  function scalingLogo(t, tS, o = {}) {
    const S = MOD.shapeText('SCALING'), hy = o.hy ?? .62, a = t - tS, rise = easeOut(clamp(a / (o.dur ?? .28)));
    return {
      key: 'SCALING', src: S, p: [o.x ?? 0, lerp(o.from ?? -hy * 1.2, o.y ?? 1.55, rise), o.z ?? 2.2],
      rot: rotYX(Math.sin(t * 1.3) * .12 + (1 - rise) * (o.spin ?? .8) + (o.yaw ?? 0), o.pitch ?? -.06, o.roll ?? 0),
      s: [hy * S.aspect, hy, o.depth ?? .22], col: o.col ?? '#b0207a', rim: o.rim ?? '#ffb0e6', metal: 1,
    };
  }
  // The curve breaking out of a panel: its continuation past the texture's top edge, in the world, drawn on the UI layer.
  function escapeLine(ui, F, P, PN, u0, u1, cols = MAGLINE, wk = 1) {
    const pts = [];
    for (let i = 0; i <= 90; i++) { const [x, y] = curveAt(P, lerp(u0, u1, i / 90)), q = toScreen(F, toWorld(PN, x, y)); if (q) pts.push(q); }
    if (pts.length < 2) return null;
    ui.save(); ui.lineCap = 'round'; ui.lineJoin = 'round';
    [[30, 0], [11, 1], [4, 2]].forEach(([w, c]) => { ui.lineWidth = w * wk; ui.strokeStyle = cols[c]; ui.beginPath(); pts.forEach((p, i) => i ? ui.lineTo(p[0], p[1]) : ui.moveTo(p[0], p[1])); ui.stroke(); });
    const e = pts.at(-1), gr = ui.createRadialGradient(e[0], e[1], 0, e[0], e[1], 60 * wk);
    gr.addColorStop(0, 'rgba(255,255,255,.95)'); gr.addColorStop(.3, cols[1]); gr.addColorStop(1, 'rgba(255,60,170,0)');
    ui.fillStyle = gr; ui.beginPath(); ui.arc(e[0], e[1], 60 * wk, 0, TAU); ui.fill();
    ui.restore();
    return pts;
  }
  // Sparks where something presses (UI layer): short bright lines flung from a point, re-dealt every 1/20 s.
  function sparks(ui, t, x, y, k, n = 8) {
    const f = Math.floor(t * 20);
    ui.save(); ui.lineCap = 'round';
    for (let i = 0; i < n; i++) {
      const a = -Math.PI * hash2(f, i), l = (20 + 50 * hash2(i, f + 3)) * k, r0 = 6 + 10 * hash2(f + 1, i);
      ui.strokeStyle = i % 3 ? '#ffe0f4' : '#ff6ac0'; ui.lineWidth = 3;
      ui.beginPath(); ui.moveTo(x + Math.cos(a) * r0, y + Math.sin(a) * r0); ui.lineTo(x + Math.cos(a) * (r0 + l), y + Math.sin(a) * (r0 + l)); ui.stroke();
    }
    ui.restore();
  }
  const pump = t => 1 + .22 * kick8(t, 6);
  // a panel turned with a camera's roll (about the view axis, for a camera at the origin looking down −z), so it sits and reads
  // level on screen
  const level = (P, roll) => { const c = Math.cos(roll), s = Math.sin(roll), R = v => [v[0] * c - v[1] * s, v[0] * s + v[1] * c, v[2]]; return { ...P, c: R(P.c), u: R(P.u), v: R(P.v) }; };

  // =====================================================================================================
  // C1, "SOFTMAX I": plasma, the curve is born, the border can't hold it, DEEP ×7
  // =====================================================================================================
  // The "Deep"s: each one's onset in the vocal stem (the first as the held "it!" ends), six stutters and then V2.1's "DeepSeek".
  const DEEP = [72.82, 73.26, 73.68, 73.90, 74.12, 74.33, 74.55];
  let _deepTex = null;
  function deepTex() {
    if (_deepTex) return _deepTex;
    const c = makeCanvas(1024, 1024), g = c.getContext('2d');
    g.fillStyle = '#030822'; g.fillRect(0, 0, 1024, 1024);
    for (let y = 0; y < 8; y++) for (let x = 0; x < 8; x++) { g.fillStyle = (x + y) & 1 ? '#06103a' : '#040b2c'; g.fillRect(x * 128, y * 128, 128, 128); }
    g.font = `76px ${MOD.FONT_T}`; g.textAlign = 'center'; g.textBaseline = 'middle';
    for (let i = 0; i < 8; i++) for (let j = 0; j < 2; j++) {
      const x = 256 + j * 512 + (i & 1) * 256, y = 64 + i * 128;
      g.fillStyle = '#4d6bfe'; g.fillText('DEEP', x % 1024, y); g.fillStyle = 'rgba(210,225,255,.5)'; g.fillText('DEEP', x % 1024, y - 3);
    }
    g.strokeStyle = 'rgba(120,150,255,.35)'; g.lineWidth = 4;
    for (let y = 0; y < 1024; y += 128) { g.beginPath(); g.moveTo(0, y + 2); g.lineTo(1024, y + 2); g.stroke(); }
    return (_deepTex = c);
  }
  // The demo's border (a C64's flat blue with raster bars running through it), everywhere outside the window win.
  function c64Border(ui, t, win) {
    ui.save();
    ui.beginPath(); ui.rect(-10, -10, 1940, 1100); ui.rect(win[0], win[1], win[2] - win[0], win[3] - win[1]); ui.clip('evenodd');
    for (let y = 0; y < 1080; y += 6) { const b = Math.max(0, Math.sin(y * .03 - t * 7)) ** 6 * .8 + Math.max(0, Math.sin(y * .011 + t * 3.1)) ** 8 * .5; ui.fillStyle = lerpHex('#29258e', '#c4beff', Math.min(1, b)); ui.fillRect(-10, y, 1940, 6); }
    ui.restore();
    ui.save(); ui.strokeStyle = 'rgba(8,6,30,.9)'; ui.lineWidth = 6; ui.strokeRect(win[0] - 3, win[1] - 3, win[2] - win[0] + 6, win[3] - win[1] + 6); ui.restore();
  }

  msection('C1', (t, s, E, ui) => {
    const L1 = Wd('C1', 1), L2 = Wd('C1', 2), L3 = Wd('C1', 3), L4 = Wd('C1', 4);
    const tL2 = L2[0].t0 - .06, tL3 = L3[0].t0 - .12, tL4 = L4[0].t0 - .08, tCant = L4[7].t0, tContain = L4[8].t0;
    const F = {
      fx: E.fx, res: E.res, skyA: '#060312', skyB: '#1a0826', acc: '#ff3aa6', fog: .018, floorCol: '#030208', grid: .3,
      sky: { mode: 'plasma', k: .8, col: '#0f78b4' }, light: { p: [0, 3.6, -4.5], c: '#ff6cc8', k: 5, vol: .5 }, panels: [], spheres: [],
    };
    const PLASMA_ACC = '#b81c78';
    if (t < tL2) {
      // "We didn't start the scaling": her words under a plasma sky, then SCALING rises out of the floor in chrome
      frontWords(t, L1, [[0, 1], [2, 3]], 104);
      const tS = L1[4].t0, up = t >= tS ? easeOut(clamp((t - tS) / .25)) : 0, lt = t - s.start;
      F.panels.push({ c: [0, 3.05 + up * .35, 1.6], u: [2.6, 0, 0], v: [0, 1.3, 0], alpha: 1, gain: 1.8, glass: 0, tex: 1 });
      if (t >= tS) { F.shape = scalingLogo(t, tS, { y: 1.45, z: 1.6, spin: 1.4 }); F.flash = clamp(1 - (t - tS) / .2) * .2; F.flashCol = '#ff9ad8'; }
      F.ro = [Math.sin(lt * .5) * 1.2, 1.1 + lt * .15, 9.2 - lt * .5]; F.ta = [0, 2.35, 0]; F.fov = 1.5; F.acc = PLASMA_ACC;
    } else if (t < tL3) {
      // "It was always training, and the curves kept gaining": the curve is drawn as she sings, her words riding it up
      const P = poly(), ln = lineAt('C1', 2), g = MOD.panel(0), R = rideLayout(g, ln, 48, 70), cur = curOf(L2, t);
      const endOf = i => i === L2.length - 1 ? P.len : i < 0 ? 110 : R.filter(c => c.wi <= i).at(-1).s + 170;
      const arc = lerp(cur < 1 ? 40 : endOf(cur - 1), endOf(cur), easeOut(clamp((t - (cur >= 0 ? L2[cur].t0 : tL2)) / (cur === L2.length - 1 ? .7 : .35))));
      const [tip] = chart(g, t, { theme: 'c1', curves: [{ P, arc }] });
      ride(g, t, { P, ln, size: 48 });
      F.panels.push({ ...CH, alpha: 1, gain: 1.5 });
      const ta = add(mix3(CH.c, toWorld(CH, tip[0], tip[1]), .72), [0, -.3, 0]);
      F.ta = ta; F.ro = add(ta, [1.0, .4, 5.1]); F.fov = 1.45; F.acc = PLASMA_ACC;
    } else if (t < tL4) {
      // the hook again: one huge word at a time, magenta and cyan in turn, the whole curve behind; SCALING rises
      chart(MOD.panel(0), t, { theme: 'c1', curves: [{ P: poly(), arc: 1e9 }] });
      const cur = frontWords(t, L3, [[0, 1], [2, 3]], 104);
      F.panels.push({ ...CH, alpha: .75, gain: 1.2 }, { c: [0, 3.25, 1.6], u: [2.4, 0, 0], v: [0, 1.2, 0], alpha: cur >= 0 ? 1 : 0, gain: 2, glass: 0, tex: 1 });
      if (cur === 4) { F.shape = scalingLogo(t, L3[4].t0, { spin: -1 }); F.flash = clamp(1 - (t - L3[4].t0) / .2) * .2; F.flashCol = '#8ae4ff'; }
      if (cur >= 0 && t - L3[cur].t0 < .08 && cur < 4) F.flash = .08;
      const lt = t - tL3;
      F.ro = [-1.4 + lt * .9, 1.7, 8.8 - lt * .4]; F.ta = [0, 2.35, 0]; F.fov = 1.5; F.acc = PLASMA_ACC;
    } else if (t < DEEP[0]) {
      // "No, we didn't preordain it, but we can't contain it!": the picture sits inside the demo's border; the curve presses its top
      // edge, strains it on "can't", and on "contain" bursts through and climbs off the screen as the border falls away
      const P = poly({ u1: uTop(poly()) - .003 }), strain = t >= tCant && t < tContain ? clamp((t - tCant) / (tContain - tCant)) : 0, out = t >= tContain, a = t - tContain;
      const [tip] = chart(MOD.panel(0), t, { theme: 'c1', curves: [{ P, arc: 1e9 }], strain, broken: out ? curveAt(P, uTop(P))[0] : 0 });
      frontWords(t, L4, [[0, 1, 2], [3, 4], [5, 6, 7], [8, 9]], 74);
      F.panels.push({ ...CH, alpha: 1, gain: 1.45 }, { c: [-.9, 2.7, 1.6], u: [2.0, 0, .25], v: [0, 1.0, 0], alpha: 1, gain: 1.9, glass: .6, tex: 1 });
      const up = out ? easeInOut(clamp(a / 1.8)) : 0, lt = t - tL4;
      const shake = strain > 0 ? [Math.sin(t * 91) * .03 * strain, Math.cos(t * 77) * .03 * strain, 0] : [0, 0, 0];
      F.ro = add([.2 + lt * .03, 1.9 + up * .9, 8.7 + up * .6], shake); F.ta = add([.2 + up * .9, 1.84 + up * 2.3, -.5], shake); F.fov = 1.5; F.acc = PLASMA_ACC;
      if (out) {
        F.flash = clamp(1 - a / .25) * .3; F.flashCol = '#ff7ac8'; F.exposure = pump(t); F.light = { p: [3.6, 6, -1.5], c: '#ff5cc0', k: 8, vol: 1 };
        // the frame's glass, flung from the breach
        const b = toWorld(CH, curveAt(P, uTop(P))[0], 0);
        for (let i = 0; i < 14; i++) {
          const d = MOD.norm([hash(i * 3 + 1) - .35, .4 + hash(i * 3 + 2), hash(i * 3 + 3) * 1.4 + .2]), v = 1.5 + 3 * hash(i + 50);
          F.spheres.push([b[0] + d[0] * v * a, b[1] + d[1] * v * a - 2 * a * a, b[2] + d[2] * v * a, .04 + .05 * hash(i + 70), i % 2 ? '#ffb8e6' : '#ffffff']);
        }
      }
      // the border: it shudders as the curve presses; on "contain" it falls away to the edges
      const br = out ? easeIn(clamp(a / .4)) : 0, j = strain * 5;
      const win = [230 - br * 420 + Math.sin(t * 83) * j, 70 - br * 300 + Math.cos(t * 71) * j, 1690 + br * 420 + Math.sin(t * 67) * j, 830 + br * 420];
      if (br < 1) c64Border(ui, t, win);
      const edge = toScreen(F, toWorld(CH, ...curveAt(P, uTop(poly()))));
      if (strain > 0 && edge) sparks(ui, t, edge[0], Math.max(edge[1], win[1]), .6 + strain);
      // the curve's own continuation, out through the top of the frame
      if (out) escapeLine(ui, F, poly(), CH, uTop(poly()) - .003, uTop(poly()) + .3 * easeOut(clamp(a / 1.1)), MAGLINE, 1.35);
    } else {
      // "Deep, deep, deep…": each stutter slams a DEEP and pushes the ones before it down a DeepSeek-blue tunnel, faster and faster
      let n = -1; DEEP.forEach((h, i) => { if (t >= h) n = i; });
      const lt = t - DEEP[0];
      let scroll = lt * .5; DEEP.forEach(h => { if (t > h) scroll += (t - h) * .5; });
      const g = MOD.panel(1);
      g.font = `230px ${MOD.FONT_T}`; g.textAlign = 'center'; g.textBaseline = 'middle'; g.lineJoin = 'round';
      g.lineWidth = 16; g.strokeStyle = 'rgba(0,4,30,.9)'; g.strokeText('DEEP', 512, 262);
      g.fillStyle = MOD.chrome(g, 150, 370, ['#ffffff', '#cfdcff', '#4d6bfe', '#16248a']); g.fillText('DEEP', 512, 262);
      const roll = lt * (.3 + .1 * Math.max(0, n)), cr = Math.cos(roll), sr = Math.sin(roll);
      for (let j = Math.max(0, n - 5); j <= n; j++) {
        const r = n - j, since = t - DEEP[n], step = easeOut(clamp(since / .12));
        const z = r === 0 ? lerp(-2.5, -3.4, step) : lerp(-3.4 - (r - 1) * 3.4, -3.4 - r * 3.4, step), sc = r === 0 ? 1 + .15 * (1 - step) : 1;
        // (turned with the camera's roll, so every DEEP reads level)
        const y = .18 - r * .32;
        F.panels.push({ c: [-y * sr, y * cr, z], u: [1.15 * sc * cr, 1.15 * sc * sr, 0], v: [-.575 * sc * sr, .575 * sc * cr, 0], alpha: r ? .5 - r * .07 : 1, gain: r ? 1.2 : 1.55 + .5 * (1 - step), glass: 0, tex: 1 });
      }
      if (n >= 0) { F.flash = clamp(1 - (t - DEEP[n]) / .06) * .07; F.flashCol = '#9fb4ff'; }
      const sway = Math.sin(t * 2.3) * .2;
      Object.assign(F, {
        floor: false, sky: null, skyA: '#020418', skyB: '#030824', acc: '#4d6bfe', fog: .05,
        ro: [sway, Math.cos(t * 1.9) * .15, 0], ta: [sway * .4, 0, -6], fov: 1.3, roll,
        tunnel: { key: 'deep', src: deepTex(), r: 3, scroll, twist: .012, col: '#9fb2ff', gain: 1.7 },
        light: { p: [0, 0, -16], c: '#6d8bff', k: 12, vol: .6 }, exposure: 1 + .1 * kick8(t, 7),
      });
    }
    return F;
  });

  // =====================================================================================================
  // C2, "SOFTMAX II": the dot tunnel, two curves climbing together, the bobs burst out, MOLT ×4 → MOLTBOOK
  // =====================================================================================================
  // "Molt, molt, molt, molt, Moltbook": each one's onset in the vocal stem, eighth notes from the end of the held "it!".
  const MOLTS = [116.51, 116.72, 116.93, 117.13], MOLT = 117.35;
  let _dotTex = null;
  function dotTex() {
    if (_dotTex) return _dotTex;
    const c = makeCanvas(1024, 512), g = c.getContext('2d');
    g.fillStyle = '#000'; g.fillRect(0, 0, 1024, 512);
    for (let r = 0; r < 16; r++) for (let d = 0; d < 36; d++) {
      const x = (d + (r & 1) * .5) / 36 * 1024, y = r * 32 + 16, col = r & 1 ? '53,194,242' : '255,79,180';
      const gr = g.createRadialGradient(x, y, 0, x, y, 11); gr.addColorStop(0, '#ffffff'); gr.addColorStop(.35, `rgb(${col})`); gr.addColorStop(1, `rgba(${col},0)`);
      g.fillStyle = gr; g.fillRect(x - 12, y - 12, 24, 24);
    }
    return (_dotTex = c);
  }
  // the two curves: compute, and capabilities just below and behind it
  const PC = () => poly({ x0: 150, x1: 1860, y0: 900, y1: 80 }), PK = () => poly({ x0: 250, x1: 1960, y0: 968, y1: 150 });
  // vector bobs riding a curve behind its tip
  function bobsOn(out, P, arc, n, col, t, o = {}) {
    for (let i = 0; i < n; i++) {
      const s = arc - i * (o.gap ?? 52); if (s < 0) break;
      const [x, y] = atArc(P, s), p = toWorld(CH, x, y), r = (i ? .075 : .13) * (1 + .18 * kick(t, 6)) * (o.k ?? 1);
      const jit = o.jit ?? 0;
      out.push([p[0] + Math.sin(t * 97 + i) * jit, p[1] + Math.cos(t * 83 + i * 2) * jit, p[2] + .2, r, col]);
    }
  }
  function molts(t, E, ui) {
    // each "molt" tries to switch back to text mode, and fails a different way: the picture rolls, tears, comes up in the wrong
    // colours, collapses; then black. On "Molt" the BBS's logo holds, where V3.1 prints it.
    ui.save(); ui.fillStyle = '#000'; ui.fillRect(0, 0, 1920, 1080);
    const TM = tmCanvas(), g = TM.g; g.fillStyle = '#000'; g.fillRect(0, 0, 640, 360);
    const F = { fx: E.fx, res: E.res, floor: false, skyA: '#000000', skyB: '#000000', exposure: 0, hud: false, flare: 0 };
    const RED = { 4: '#c4221c', 12: '#ff5a3c', 13: '#ff45b0', 5: '#a01880', 15: '#ffffff' };
    if (t >= MOLT) { tmBigText(g, 'MOLT', 64, 36, [RED[12], RED[12], RED[4], RED[4]]); blitTM(ui, TM.c, 0, 0, 1, 1); ui.restore(); return F; }
    let i = 0; MOLTS.forEach((m, k) => { if (t >= m) i = k; });
    const a = t - MOLTS[i], life = i === 0 ? MOLTS[1] - MOLTS[0] - .01 : .12;
    const sync = () => { ui.fillStyle = '#ffffff'; ui.fillRect(0, 538, 1920, 4); ui.fillStyle = 'rgba(170,170,170,.8)'; ui.fillRect(180, 542, 1560, 3); };
    if (a < .034) { sync(); ui.restore(); return F; }
    if (a > life) { if (a - life < .05) { ui.fillStyle = '#aaaaaa'; ui.fillRect(840, 538, 240, 4); } ui.restore(); return F; }
    const fg = [[15, 13, 13, 5], [13, 13, 5, 5], [12, 13, 5, 4], [12, 12, 4, 4]][i].map(c => RED[c]);
    const shown = Math.max(1, Math.ceil((a - .034) / .05 * 4));
    tmBigText(g, 'MOLT'.slice(0, shown), 200, 132, fg);
    if (Math.floor(a * 8) % 2 === 0) tmLine(g, 0, 0, '_', '#aaaaaa');
    const k = (a - .034) / (life - .034);
    if (i === 0) {
      // the vertical hold goes: the picture rolls faster and faster, then collapses to a line
      const roll = easeIn(clamp(k / .8)) * 1260 % 1080;
      if (k < .8) { blitTM(ui, TM.c, 0, roll - 1080, 1, 1); blitTM(ui, TM.c, 0, roll, 1, 1); }
      else { const sy = Math.max(.004, 1 - (k - .8) / .2); blitTM(ui, TM.c, 0, 540 - 540 * sy, 1, sy); }
    } else if (i === 1) {
      // it tears: slices slide sideways
      for (let y = 0; y < 360; y += 6) { const dx = Math.sin(y * .07 + a * 90) * 40 * k * 3 + (y > 180 ? 72 : 0); ui.drawImage(TM.c, 0, y, 640, 6, dx, y * 3, 1920, 18); }
    } else if (i === 2) {
      // wrong palette: the colours come up scrambled, every other line dark
      blitTM(ui, TM.c, 0, 0, 1, 1);
      ui.globalCompositeOperation = 'difference'; ui.fillStyle = '#5ab04a'; ui.fillRect(0, 0, 1920, 1080); ui.globalCompositeOperation = 'source-over';
      ui.fillStyle = 'rgba(0,0,0,.85)'; for (let y = 3; y < 1080; y += 6) ui.fillRect(0, y, 1920, 3);
    } else {
      // squashed flat
      const sy = Math.max(.01, 1 - k), sx = 1 + k * .4;
      blitTM(ui, TM.c, 960 - 960 * sx, 540 - 540 * sy, sx, sy);
    }
    ui.restore();
    return F;
  }
  // ---- text mode, for the MOLTs: 80 × 22.5 cells of 8 × 16 (the demo's 8×8 font, rows doubled) on a 640 × 360 canvas, shown ×3 ----
  let _tm = null;
  const tmCanvas = () => _tm ?? (_tm = (() => { const c = makeCanvas(640, 360); return { c, g: c.getContext('2d') }; })());
  function tmLine(g, col, row, str, color) {
    g.fillStyle = color;
    [...str].forEach((ch, i) => { const b = cell16(ch), x0 = (col + i) * 8, y0 = 4 + row * 16; for (let y = 0; y < 16; y++) for (let x = 0; x < 8; x++) if (b[y * 8 + x]) g.fillRect(x0 + x, y0 + y, 1, 1); });
  }
  // half-block ANSI letters: each font pixel one 8 × 8 half-cell, rows of cells coloured cols[cellRow], with a dark drop shade
  function tmBigText(g, str, x, y, cols) {
    let cx = x;
    for (const ch of str) {
      const G = glyph(ch);
      for (let pass = 0; pass < 2; pass++) for (let yy = 0; yy < 8; yy++) for (let xx = 0; xx < G.w; xx++) if (G.bits[yy * G.w + xx]) {
        g.fillStyle = pass ? cols[yy >> 1] : '#2a0a12';
        g.fillRect(cx + xx * 8 + (pass ? 0 : 8), y + yy * 8 + (pass ? 0 : 8), 8, 8);
      }
      cx += (G.w + 1) * 8;
    }
  }
  function blitTM(ui, c, x, y, sx, sy) { ui.imageSmoothingEnabled = false; ui.drawImage(c, 0, 0, 640, 360, x, y, 1920 * sx, 1080 * sy); ui.imageSmoothingEnabled = true; }

  msection('C2', (t, s, E, ui) => {
    if (t >= MOLTS[0]) return molts(t, E, ui);
    const L1 = Wd('C2', 1), L2 = Wd('C2', 2), L3 = Wd('C2', 3), L4 = Wd('C2', 4);
    const tL2 = L2[0].t0 - .06, tL3 = L3[0].t0 - .12, tL4 = L4[0].t0 - .08, tCant = L4[7].t0, tContain = L4[8].t0;
    const F = {
      fx: E.fx, res: E.res, skyA: '#04030c', skyB: '#0e0726', acc: '#ff3aa6', fog: .025, floorCol: '#030208', grid: .3,
      light: { p: [0, 3.6, -4.5], c: '#b06cff', k: 6, vol: .6 }, panels: [], spheres: [], flare: 0,
    };
    const inTunnel = (speed, o = {}) => Object.assign(F, {
      floor: false, sky: null, skyA: '#010004', skyB: '#030010', fog: .06,
      ro: [0, 0, 0], ta: [Math.sin(t * .7) * .45, Math.cos(t * .5) * .3, -6], fov: 1.35, roll: t * .35,
      tunnel: { key: 'dots', src: dotTex(), r: 2.6, scroll: t * speed, twist: .022, col: '#ffffff', gain: 2.1 },
      light: { p: [0, 0, -14], c: '#ff6cc8', k: 9, vol: .7 }, ...o,
    });
    if (t < tL2) {
      // "We didn't start the scaling": a spiralling dot tunnel; SCALING flies up it at us and bursts out on "scaling"
      inTunnel(.55);
      frontWords(t, L1, [[0, 1], [2, 3]], 104);
      F.panels.push(level({ c: [0, .78, -3.4], u: [1.35, 0, 0], v: [0, .675, 0], alpha: 1, gain: 1.9, glass: 0, tex: 1 }, F.roll));
      const tS = L1[4].t0, lt = t - s.start;
      const z = t < tS ? lerp(-34, -9, easeInOut(clamp(lt / (tS - s.start)))) : lerp(-9, -3.6, easeOut(clamp((t - tS) / .3)));
      const spin = Math.sin(t * 1.5) * .3 + (t >= tS ? (1 - easeOut(clamp((t - tS) / .45))) * TAU : 0);
      F.shape = { ...scalingLogo(t, -99, { hy: .34, y: -.42, z }), rot: rotYX(spin, -.12, F.roll) };
      F.shape.p = level({ c: F.shape.p, u: [0, 0, 0], v: [0, 0, 0] }, F.roll).c;
      if (t >= tS) { F.flash = clamp(1 - (t - tS) / .15) * .22; F.flashCol = '#ff9ad8'; F.flarePos = [.5, .42]; F.flare = .6 * clamp(1 - (t - tS) / .5); }
    } else if (t < tL3) {
      // "It was always training, and the curves kept gaining": two curves, compute and capabilities, climb together, vector bobs at
      // their heads, her words riding the upper one
      const P1 = PC(), P2 = PK(), ln = lineAt('C2', 2), g = MOD.panel(0), R = rideLayout(g, ln, 46, 70), cur = curOf(L2, t);
      const endOf = i => i === L2.length - 1 ? P1.len : i < 0 ? 110 : R.filter(c => c.wi <= i).at(-1).s + 170;
      const arc = lerp(cur < 1 ? 40 : endOf(cur - 1), endOf(cur), easeOut(clamp((t - (cur >= 0 ? L2[cur].t0 : tL2)) / (cur === L2.length - 1 ? .7 : .35))));
      const u = atArc(P1, arc)[3], arc2 = arcAtU(P2, u);
      const [tip] = chart(g, t, { theme: 'c2', curves: [{ P: P2, arc: arc2, cols: CYANLINE }, { P: P1, arc }] });
      ride(g, t, { P: P1, ln, size: 46 });
      F.panels.push({ ...CH, alpha: 1, gain: 1.5 });
      bobsOn(F.spheres, P1, arc, 10, '#ff4fb4', t); bobsOn(F.spheres, P2, arc2, 10, '#35c2f2', t);
      if (cur === 6 && t - L2[6].t0 < .2) { F.flash = (1 - (t - L2[6].t0) / .2) * .12; F.flashCol = '#ffb0e0'; }
      const tw = toWorld(CH, tip[0], tip[1]), ta = add(mix3(CH.c, tw, .75), [0, -.1, 0]), ro = add(ta, [-1.9, -.75, 4.5]);
      ro[1] = Math.max(.45, ro[1]);
      F.ta = ta; F.ro = ro; F.fov = 1.4; F.sky = { mode: 'rays', k: .4, col: '#2a1a6a' }; F.acc = '#6a1a5c';
      F.flarePos = MOD.project(F, add(tw, [0, 0, .2])) ?? [.5, .6]; F.flare = .3;
    } else if (t < tL4) {
      // the hook again, back in the tunnel, faster: one huge word at a time; on "scaling" the logo flies through the screen
      inTunnel(1.4, { roll: t * .6 });
      const cur = frontWords(t, L3, [[0, 1], [2, 3]], 104);
      F.panels.push(level({ c: [0, .62, -3.2], u: [1.3, 0, 0], v: [0, .65, 0], alpha: cur >= 0 ? 1 : 0, gain: 2, glass: 0, tex: 1 }, F.roll));
      const tS = L3[4].t0;
      if (t >= tS) {
        const k = clamp((t - tS) / (tL4 - tS)), z = lerp(-16, 1.2, k ** 1.5);
        F.shape = { ...scalingLogo(t, -99, { hy: .3, y: -.62, z }), rot: rotYX(Math.sin(t * 2) * .3, -.1, F.roll) };
        F.shape.p = level({ c: F.shape.p, u: [0, 0, 0], v: [0, 0, 0] }, F.roll).c;
        if (z > -2.2) { F.flash = .14; F.flashCol = '#ffb0e0'; }
        F.flarePos = [.5, .5]; F.flare = .5 * k;
      }
    } else {
      // "No, we didn't preordain it, but we can't contain it!": both curves press the frame, strain on "can't", and on "contain"
      // break out through the top while every bob bursts off the chart into a starfield
      const P1 = PC(), P2 = PK(), strain = t >= tCant && t < tContain ? clamp((t - tCant) / (tContain - tCant)) : 0, out = t >= tContain, a = t - tContain;
      const P1e = poly({ ...P1.o, u1: uTop(P1) - .003 }), P2e = poly({ ...P2.o, u1: Math.min(uTop(P2) - .003, (2040 - P2.o.x0) / (P2.o.x1 - P2.o.x0)) });
      chart(MOD.panel(0), t, { theme: 'c2', curves: [{ P: P2e, arc: 1e9, cols: CYANLINE }, { P: P1e, arc: 1e9 }], strain, broken: out ? curveAt(P1, uTop(P1))[0] : 0 });
      frontWords(t, L4, [[0, 1, 2], [3, 4], [5, 6, 7], [8, 9]], 74);
      F.panels.push({ ...CH, alpha: out ? lerp(1, .45, easeOut(clamp(a / .6))) : 1, gain: 1.45 }, { c: [-1.35, 3.0, 1.9], u: [2.2, 0, .3], v: [0, 1.1, 0], alpha: 1, gain: 1.9, glass: .6, tex: 1 });
      const lt = t - tL4, push = out ? easeInOut(clamp(a / 1.4)) : 0;
      const shake = strain > 0 ? [Math.sin(t * 91) * .035 * strain, Math.cos(t * 77) * .035 * strain, 0] : [0, 0, 0];
      F.ro = add([lerp(1.1, .5, clamp(lt / 3)) + push * .6, 1.5 + push * 1.2, 9.2 - lt * .15 + push * .8], shake); F.ta = add([.3 + push * 1.3, 2.5 + push * 2.4, -.5], shake); F.fov = 1.42;
      if (!out) {
        bobsOn(F.spheres, P1e, P1e.len, 16, '#ff4fb4', t, { gap: 70, jit: strain * .04 });
        bobsOn(F.spheres, P2e, P2e.len, 16, '#35c2f2', t, { gap: 70, jit: strain * .04 });
      } else {
        // the bobs fly out at us and past, into the stars
        const sp = [];
        bobsOn(sp, P1e, P1e.len, 16, '#ff4fb4', t, { gap: 70 }); bobsOn(sp, P2e, P2e.len, 16, '#35c2f2', t, { gap: 70 });
        sp.forEach((b, i) => {
          const d = MOD.norm([b[0] - .2 + (hash(i) - .5), b[1] - 2.3 + (hash(i + 40) - .5) + 1, 1.2 + hash(i + 80) * 2.5]), v = 2.5 + 4.5 * hash(i + 120);
          F.spheres.push([b[0] + d[0] * v * a, b[1] + d[1] * v * a, b[2] + d[2] * v * a, b[3] * 1.4, b[4]]);
        });
        F.sky = { mode: 'stars', k: .8 + 4 * easeIn(clamp(a / 1.2)), col: '#ffd6f2' }; F.skyA = '#020108'; F.skyB = '#0a0418';
        F.flash = clamp(1 - a / .25) * .3; F.flashCol = '#ff7ac8'; F.exposure = pump(t);
        F.light = { p: [3, 6, -2], c: '#ff5cc0', k: 8, vol: 1 };
        escapeLine(ui, F, P2, CH, P2e.at(-1)[3], P2e.at(-1)[3] + .28 * easeOut(clamp(a / .8)), CYANLINE, .9);
        escapeLine(ui, F, P1, CH, uTop(P1) - .003, uTop(P1) + .3 * easeOut(clamp(a / .7)));
      }
      const edge = toScreen(F, toWorld(CH, ...curveAt(P1, uTop(P1))));
      if (strain > 0 && edge) sparks(ui, t, edge[0], edge[1], .6 + strain);
    }
    return F;
  });

  // =====================================================================================================
  // C3, "SOFTMAX III": the chart on a violet checkerboard; the words burn as they ride; the curve catches fire; the beam
  // =====================================================================================================
  const C3 = n => lineAt('C3', n);
  // (C3's first two words: the timing puts "We" inside V3.16's echo; whisper's times, as ch/p06_c3.js has them)
  const C3W1 = () => { const w = wordsOf(C3(1)).map(x => ({ ...x })); w[0].t0 = 144.96; w[1].t0 = 145.22; return w; };
  msection('C3', (t, s, E, ui) => {
    const L1 = C3W1(), L2 = wordsOf(C3(2)), L3 = wordsOf(C3(3)), L4 = wordsOf(C3(4));
    const tL2 = L2[0].t0 - .06, tL3 = L3[0].t0 - .12, tL4 = L4[0].t0 - .08, tCant = L4[7].t0, tContain = L4[8].t0;
    const F = {
      fx: E.fx, res: E.res, skyA: '#070310', skyB: '#1c0714', acc: '#ff3aa6', fog: .02, grid: .12,
      floorMode: 'checker', floorCol: '#06030c', floorCol2: '#2c1452', floorTile: 1.1,
      light: { p: [0, 3.6, -4.5], c: '#ff5cc0', k: 6, vol: .8 }, panels: [], flare: .8,
    };
    // (C3's curve is the steepest yet, so that when it breaks out on "contain" its own continuation, steeper still, carries it off the
    // top of the screen without a kink)
    const P = poly({ k: 6.4 });
    if (t < tL2) {
      // "We didn't start the scaling": the empty chart, the words, then SCALING rises in chrome
      chart(MOD.panel(0), t, { arc: 0, curves: [{ P, arc: 0, dot: t >= L1[0].t0 }] });
      frontWords(t, L1, [[0, 1], [2, 3]], 104);
      const up = t >= L1[4].t0 ? easeOut(clamp((t - L1[4].t0) / .25)) : 0;
      F.panels.push({ ...CH, alpha: .9, gain: 1.3 }, { c: [0, 3.35 + up * .8, 1.2], u: [2.4, 0, 0], v: [0, 1.2, 0], alpha: 1, gain: 1.8, glass: 0, tex: 1 });
      if (t >= L1[4].t0) { F.shape = scalingLogo(t, L1[4].t0, { y: 2.35 }); F.flash = clamp(1 - (t - L1[4].t0) / .2) * .18; F.flashCol = '#ff9ad8'; }
      const lt = t - s.start;
      F.ro = [Math.sin(lt * .4) * 1.2, 1.4, 9.8 - lt * .3]; F.ta = [0, 2.05, 0]; F.fov = 1.55;
    } else if (t < tL3) {
      // "It was always training, and the curves kept gaining": the curve climbs, her words ride it up and burn; its tip catches fire
      const g = MOD.panel(0), R = rideLayout(g, C3(2), 44, 70), cur = curOf(L2, t);
      const endOf = i => i === L2.length - 1 ? P.len : i < 0 ? 120 : R.filter(c => c.wi <= i).at(-1).s + 160;
      const arc = lerp(cur < 1 ? 60 : endOf(cur - 1), endOf(cur), easeOut(clamp((t - (cur >= 0 ? L2[cur].t0 : tL2)) / (cur === L2.length - 1 ? .7 : .35))));
      const [tip] = chart(g, t, { curves: [{ P, arc }] });
      ride(g, t, { P, ln: C3(2), size: 44, lift: 40, burn: true });
      flames(g, t, tip[0], tip[1], clamp((tip[3] - .35) / .5) * 1.3);
      F.panels.push({ ...CH, alpha: 1, gain: 1.5 });
      const tw = toWorld(CH, tip[0], tip[1]), ta = add(mix3(CH.c, tw, .7), [0, -.45, 0]);
      F.ta = ta; F.ro = add(ta, [-1.1, -.3, 5.9]); F.fov = 1.45;
      F.light = { p: add(tw, [0, 1.2, -1]), c: '#ff7a5c', k: 5 + 6 * clamp(tip[3]), vol: .9 };
    } else if (t < tL4) {
      // the hook again: one huge word at a time, the burning curve behind; SCALING rises
      const g = MOD.panel(0), [tip] = chart(g, t, { curves: [{ P, arc: 1e9 }] });
      flames(g, t, tip[0], tip[1], 1.2);
      const cur = frontWords(t, L3, [[0, 1], [2, 3]], 104);
      F.panels.push({ ...CH, alpha: .75, gain: 1.2 }, { c: [0, 3.25, 1.6], u: [2.4, 0, 0], v: [0, 1.2, 0], alpha: cur >= 0 ? 1 : 0, gain: 2, glass: 0, tex: 1 });
      if (cur === 4) { F.shape = scalingLogo(t, L3[4].t0, { y: 1.45 }); F.flash = clamp(1 - (t - L3[4].t0) / .15) * .12; F.flashCol = '#ff9ad8'; }
      const lt = t - tL3;
      F.ro = [1.2 - lt * .6, 1.6, 8.6 - lt * .5]; F.ta = [0, 2.15, 0]; F.fov = 1.5;
    } else {
      // "No, we didn't preordain it, but we can't contain it!": the burning curve presses the frame; on "contain" it breaks out through
      // the corner and runs on up its own exponential, steepening off the top of the screen, a beam of light along its last stretch
      const strain = t >= tCant ? clamp((t - tCant) / (tContain - tCant)) : 0, out = t >= tContain;
      const g = MOD.panel(0), [tip] = chart(g, t, { curves: [{ P, arc: 1e9 }], strain: out ? 0 : strain, broken: out ? 'corner' : 0 });
      flames(g, t, tip[0], tip[1], 1.2 + strain * .6 + (out ? .6 : 0));
      const cur = frontWords(t, L4, [[0, 1, 2], [3, 4], [5, 6, 7], [8, 9]], 74);
      const shake = strain > 0 && !out ? [Math.sin(t * 91) * .03 * strain, Math.cos(t * 77) * .03 * strain, 0] : [0, 0, 0];
      const tw = toWorld(CH, tip[0], tip[1]), up = out ? easeInOut(clamp((t - tContain) / 1.4)) : 0;
      F.panels.push({ ...CH, alpha: out ? .85 : 1, gain: out ? 1.7 : 1.4 }, { c: [-1.1, 3.05 + up * 1.9, 1.9], u: [2.3, 0, .3], v: [0, 1.15, 0], alpha: 1, gain: 1.9, glass: .6 });
      const lt = t - tL4, base = [lerp(-.8, .4, clamp(lt / 5)), 1.4 + up * 1.4, 9.4 - lt * .2];
      F.ro = add(base, shake); F.ta = add([lerp(-.5, .5, clamp(lt / 5)), 2.5 + up * 2.6, 0], shake); F.fov = 1.4;
      if (out) {
        const a = t - tContain, ue = 1 + .2 * easeOut(clamp(a / .7));
        const e = toWorld(CH, ...curveAt(P, ue)), e2 = toWorld(CH, ...curveAt(P, ue + .01)), d = MOD.norm(MOD.sub(e2, e));
        const pts = escapeLine(ui, F, P, CH, 1, ue, MAGLINE, 1.35), head = pts?.at(-1);
        if (head && head[1] > -60) flames(ui, t, head[0], head[1], 1.1);   // (the fire rides the head out)
        F.beam = { x: e[0], z: e[2] + .05, y0: e[1], x1: e[0] + d[0] * 40, z1: e[2] + .05 + d[2] * 40, y1: e[1] + d[1] * 40, r: .09 + .05 * kick(t, 5), k: (3.2 + 2 * kick(t, 4)) * clamp((ue - 1.12) / .05), col: '#ff4fb4' };
        F.flash = clamp(1 - a / .25) * .3; F.flashCol = '#ff7ac8';
        F.light = { p: add(e, [0, 1, -1]), c: '#ff5cc0', k: 9, vol: 1.3 };
      }
    }
    return F;
  });

  // =====================================================================================================
  // C4: the end part
  // =====================================================================================================
  // The ad-libs the timing folds into "on?": whisper's times, as ch/p08_c4.js has them.
  const ON_Q = 210.58;                                   // "…will it still train on?"
  const ONS = [211.14, 211.84, 212.68, 213.50], ONS_END = 214.30;   // "and on, and on, and on, and on"
  // The part ends on the first downbeat after the dot's last "on" has echoed out and her line has faded: from there the greetings
  // roll (the outro scene, which this chorus's window hands over to), over the sung "(And on, and on, and on…)".
  const C4_TAIL = (() => { const b0 = Math.round(bt(segByKey('C4').start)); return beatT(b0 + 4 * Math.ceil((bt(ONS_END + .7) - b0) / 4)); })();
  self.C4_TAIL = C4_TAIL;
  // The EPOCH counter: each "on" puts it up a bigger power of ten (1 → 10 → 1,000 → 10⁶ → 10¹² → …); between them it climbs on,
  // faster and faster.
  const EPOCHS = [[ON_Q, 0], ...ONS.map((t, i) => [t, [1, 3, 6, 12][i]])];
  function epochExp(t) {
    if (t < EPOCHS[0][0]) return -1;
    let i = 0; while (i + 1 < EPOCHS.length && t >= EPOCHS[i + 1][0]) i++;
    const [t0, e0] = EPOCHS[i];
    if (i + 1 < EPOCHS.length) { const [t1, e1] = EPOCHS[i + 1]; return e0 + (e1 - e0) * .7 * ((t - t0) / (t1 - t0)) ** 3; }
    return e0 + (t - t0) * 14;
  }
  const commas = s => s.replace(/\B(?=(\d{3})+(?!\d))/g, ',');
  function epochCounter(ui, t, x, y, alpha) {
    const e = epochExp(t); if (e < 0) return;
    const f = Math.floor(t * 60), n = Math.floor(e + 1e-9) + 1;
    let digits;
    if (e < 15) digits = String(Math.floor(10 ** e + 1e-6));
    else { digits = String(Math.floor(10 ** (2 + e - Math.floor(e)))); for (let i = 3; i < n; i++) digits += Math.floor(hash2(i * 13 + f, i) * 10); }
    // (digits whose place turns over faster than ~25 a second blur)
    const de = Math.max(1e-6, (epochExp(t + .01) - e) / .01), fast = Math.floor(e + Math.log10(Math.LN10 * de / 25));
    // (the number shrinks to fit the frame, down to 34 px; past that it wraps, its earlier rows pushed up above it)
    const str = commas(digits), label = 'EPOCH ', avail = 1920 - 140, chars = label.length + str.length;
    ui.save(); ui.globalAlpha = alpha; ui.textBaseline = 'middle';
    ui.font = `64px ${MOD.FONT_M}`;
    const size = Math.max(34, Math.min(64, Math.floor(64 * avail / (chars * ui.measureText('0').width))));
    ui.font = `${size}px ${MOD.FONT_M}`;
    const cw = ui.measureText('0').width, perRow = Math.floor(avail / cw), rows = Math.ceil(chars / perRow), lh = size * 1.18;
    const x0 = rows > 1 ? 70 : Math.max(70, x - chars * cw / 2);
    ui.fillStyle = 'rgba(4,2,12,.78)';
    const pad = (size * 1.44 - lh) / 2, top = y - (rows - 1) * lh - lh / 2 - pad;
    if (rows > 1) ui.fillRect(x0 - 24, top, perRow * cw + 48, (rows - 1) * lh);
    ui.fillRect(x0 - 24, rows > 1 ? top + (rows - 1) * lh : top, (chars - (rows - 1) * perRow) * cw + 48, lh + 2 * pad);
    let place = digits.length, k = 0;
    for (const c of label + str) {
      const cx = x0 + (k % perRow) * cw, cy = y - (rows - 1 - Math.floor(k / perRow)) * lh; k++;
      if (k <= label.length) { ui.fillStyle = '#9fb4e8'; ui.fillText(c, cx, cy); continue; }
      if (c === ',') { ui.fillStyle = 'rgba(255,200,240,.6)'; ui.fillText(c, cx, cy); continue; }
      place--;
      if (place < fast) {
        // a blurred digit: spinning, smeared up and down
        for (let j = -2; j <= 2; j++) { ui.fillStyle = `rgba(255,${150 + 20 * j},230,${.34 - Math.abs(j) * .08})`; ui.fillText(String(Math.floor(hash2(place + j * 7, f + j) * 10)), cx, cy + j * size * (rows > 1 ? .1 : .22)); }
      } else { ui.fillStyle = '#ffffff'; ui.fillText(c, cx, cy); }
    }
    ui.restore();
  }
  // The starfield's speed: cruising, crawling on "pace it", charging through "but we'd rather", hyperspace on "race it".
  function starSpeed(x, W4) {
    const tPace = W4[6].t0, tIt = W4[7].t0, tBut = W4[9].t0, tRace = W4[12].t0;
    if (x < tPace) return 1.2;
    if (x < tBut) return lerp(1.2, .035, easeOut(clamp((x - tPace) / (tIt - tPace + .25))));
    if (x < tRace) return lerp(.035, .5, easeIn(clamp((x - tBut) / (tRace - tBut))));
    return .5 + 17 * easeIn(clamp((x - tRace) / .3));
  }
  // A dense starfield on the UI layer (the sky's own is sparse): stars streaming out of the centre, their streaks as long as the
  // speed, placed by the distance travelled D so that they crawl, cruise and jump with the song.
  function starfield(ui, D, v) {
    ui.save(); ui.lineCap = 'round';
    for (let i = 0; i < 420; i++) {
      const a = hash(i * 3 + 1) * TAU, z = 1 - frac(hash(i * 3 + 2) + D * .09), r0 = 40 / Math.max(.02, z), r1 = 40 / Math.max(.02, z + Math.min(.6, v * .012 + .004));
      if (r1 > 1300) continue;
      const c = Math.cos(a) * 1.35, s = Math.sin(a), br = clamp((1 - z) * 1.4);
      ui.strokeStyle = i % 5 ? `rgba(255,236,250,${br})` : `rgba(255,120,210,${br})`; ui.lineWidth = 1.2 + 2.4 * (1 - z);
      ui.beginPath(); ui.moveTo(960 + c * r1, 540 + s * r1); ui.lineTo(960 + c * r0 + .1, 540 + s * r0); ui.stroke();
    }
    ui.restore();
  }
  function travelled(v, t0, t, n = 90) { let z = 0; const dt = (t - t0) / n; for (let i = 0; i < n; i++) z += v(t0 + (i + .5) * dt) * dt; return z; }
  // the date plate (as the verses carry it): the day they swore to pace it, then the day they raced
  function stamp(ui, md, yr, age) {
    const k = easeOut(clamp(age / .2));
    ui.save();
    ui.fillStyle = 'rgba(8,10,22,.62)'; ui.strokeStyle = 'rgba(160,200,255,.28)'; ui.lineWidth = 1.5;
    ui.beginPath(); ui.roundRect(1650, 26, 240, 100, 10); ui.fill(); ui.stroke();
    text(ui, md, 1866, 62, { size: 26, align: 'right', color: '#9fb4e8' });
    text(ui, yr, 1866, 110 - (1 - k) * 12, { size: 44, font: MOD.FONT_T, align: 'right', color: '#ffffff', alpha: .4 + .6 * k });
    ui.restore();
  }
  // the last hook's picture (and the little scene the dot grows back into): plasma, the chart with both curves, SCALING
  function finalScene(F, t, tS, o = {}) {
    const g = MOD.panel(0);
    const [tip] = chart(g, t, { theme: 'c4', curves: [{ P: PK(), arc: 1e9, cols: CYANLINE }, { P: PC(), arc: 1e9 }] });
    F.panels.push({ ...CH, c: [0, 2.6, -1.6], alpha: .95, gain: 1.4 });
    if (t >= tS) F.shape = scalingLogo(t, tS, { y: 1.95, z: 1.6, hy: .62, spin: 1.2 });
    Object.assign(F, { sky: { mode: 'plasma', k: .9, col: '#4a1a9a' }, acc: '#a0145e', skyA: '#0a0214', skyB: '#240824', grid: .35 });
    F.light = { p: [0, 2.2, -.4], c: '#ff5cc0', k: 7, vol: 1.3 };
    // (and behind it all, the machine that trains on: a folded fractal, turning, its seams lit in her magenta)
    F.world = { kind: 'fractal', p: [3.4, -.4, .25, .45 + .5 * kick(t, 6)], col: '#2a2030', glowCol: '#ff4fb4', at: [0, 3.6, -21], metal: .7 };
    F.dof = { k: .012, focus: 10.5 };
    return tip;
  }

  // "But when we log off… will it still train on?": one line, in two rows of her type at the top, each word as she sings it; it stays
  // through the switch-off and over the dot. ("on?" is whisper's, as the timing folds the ad-libs into it.)
  function lastLine(ui, t, alpha) {
    const ws = wordsOf(lineAt('C4', 6)).map((w, i) => i === 9 ? { ...w, t0: ON_Q } : w), cur = curOf(ws, t);
    [[0, 1, 2, 3, 4], [5, 6, 7, 8, 9]].forEach((r, li) => {
      const shown = r.filter(i => i <= cur); if (!shown.length) return;
      text(ui, shown.map(i => ws[i].w.toUpperCase()).join(' '), 960, 118 + li * 92, { size: 62, font: MOD.FONT_T, align: 'center', color: '#ffd0ef', alpha, stroke: 9 });
    });
  }

  msection('C4', (t, s, E, ui) => {
    if (t >= C4_TAIL) { const F = MOD.SCENES.outro(t, segByKey('outro'), E, ui); F.hud = false; return F; }
    const W = n => Wd('C4', n), L1 = W(1), L2 = W(2), L3 = W(3), L4 = W(4), L5 = W(5), L6 = W(6);
    // (the picture switches off as "off" ends, so the word is there in full first, and it stays lit over the dot)
    const tStar = L4[0].t0 - .06, tHook = L5[0].t0 - .02, tOff = L6[4].t1 - .25;
    const F = {
      fx: E.fx, res: E.res, skyA: '#08020f', skyB: '#1c0620', acc: '#ff2a9a', fog: .02, floorCol: '#040108', grid: .3,
      light: { p: [0, 3.6, -4.5], c: '#ff5cc0', k: 6, vol: .6 }, panels: [], spheres: [],
    };
    if (t < tStar) {
      // ---------- the megamix, a line to a scene: each cuts where the next line starts, just before its first word ----------
      const cut2 = L2[0].t0 - .06, cut3 = L3[0].t0 - .06;
      if (t < cut2) {
        // "We didn't start the scaling": a colonnade, her words building over it; on "scaling" the chrome SCALING rises behind
        // them, the light raking between the columns
        const lt = t - s.start, tS = L1[4].t0;
        frontWords(t, L1, [[0, 1], [2, 3]], 104);
        F.panels.push({ c: [0, 3.1, 2.4], u: [2.2, 0, 0], v: [0, 1.1, 0], alpha: 1, gain: 1.9, glass: 0, tex: 1 });
        if (t >= tS) F.shape = scalingLogo(t, tS, { y: 1.2, z: 0, hy: .6, spin: .8 });
        Object.assign(F, {
          sky: { mode: 'rays', k: .7, col: '#6a1a4a' }, acc: '#8a1060', skyA: '#0c0212', skyB: '#2a0620',
          world: { kind: 'hall', p: [2.6, 4.4, 5.2, 1.5 + 1.5 * kick(t, 6)], col: '#2a1a28', glowCol: '#ff4fb4', at: [0, 0, -1.3], metal: .6 },
          light: { p: [0, 2.1, -3.2], c: '#ff7ad0', k: 11, vol: 2.2 },
          ro: [Math.sin(lt * .6) * 1.4, .9 + lt * .2, 8.6 - lt * .45], ta: [0, 2.0, 0], fov: 1.42, flare: 1,
        });
      } else if (t < cut3) {
        // "It was always training, and the curves kept gaining,": the whole line rides the curve as she sings it, chrome bobs
        // streaming up behind her words
        const g = MOD.panel(0), P = poly(), ln = lineAt('C4', 2), R = rideLayout(g, ln, 48, 70), cur = curOf(L2, t);
        const endOf = i => i === L2.length - 1 ? P.len : i < 0 ? 110 : R.filter(c => c.wi <= i).at(-1).s + 170;
        const arc = lerp(cur < 1 ? 40 : endOf(cur - 1), endOf(cur), easeOut(clamp((t - (cur >= 0 ? L2[cur].t0 : cut2)) / (cur === L2.length - 1 ? .7 : .35))));
        const [tip] = chart(g, t, { theme: 'c4', curves: [{ P, arc }] });
        ride(g, t, { P, ln, size: 48 });
        F.panels.push({ ...CH, alpha: 1, gain: 1.45 });
        for (let i = 0; i < 24; i++) {
          const q = frac(i / 24 + t * .22), [x, y] = atArc(P, q * arc), p = toWorld(CH, x, y);
          F.spheres.push([p[0], p[1], p[2] + .35, .04 + .14 * q ** 2 * (1 + .2 * kick(t, 6)), i % 3 ? '#ff4fb4' : '#ffc4ea']);
        }
        const tw = toWorld(CH, tip[0], tip[1]), ta = add(mix3(CH.c, tw, .72), [0, -.3, 0]), lt = t - cut2;
        Object.assign(F, { ta, ro: add(ta, [1.0 - lt * .15, .4, 5.3]), fov: 1.45, skyA: '#0a0214', skyB: '#240624', acc: '#b0186a', sky: { mode: 'plasma', k: .9, col: '#4a1a9a' }, light: { p: [2, 5, -2], c: '#ff5cc0', k: 7, vol: .5 } });
      } else {
        // "We didn't start the scaling": the checkerboard spinning under us, her words building; SCALING lands on "scaling"
        const tS = L3[4].t0;
        frontWords(t, L3, [[0, 1], [2, 3]], 104);
        const a = t * 1.5, ro = [Math.sin(a) * 6.5, 3.4, Math.cos(a) * 6.5], ta = [0, 1.4, 0];
        Object.assign(F, { ro, ta, fov: 1.45, floorMode: 'checker', floorCol: '#080108', floorCol2: '#5a0a44', floorTile: 1.3, floorOff: [0, t * 3], grid: 0, sky: { mode: 'plasma', k: 1.4, col: '#ff2a9a' }, light: { p: [0, 5, 0], c: '#ff5cc0', k: 5, vol: 0 } });
        const f = MOD.norm(MOD.sub(ta, ro)), side = MOD.norm([-f[2], 0, f[0]]);
        F.panels.push({ c: add(ta, [0, 1.6, 0]), u: mul(side, 2.2), v: [0, 1.1, 0], alpha: 1, gain: 2, glass: 0, tex: 1 });
        if (t >= tS) { const land = easeOut(clamp((t - tS) / .15)); F.shape = { ...scalingLogo(t, tS, { y: lerp(3, .75, land), z: 0, hy: .42 }), rot: rotYX(Math.atan2(ro[0], ro[2]), -.2) }; }
      }
      const since = Math.min(...[cut2, cut3].map(c => t >= c ? t - c : 9));
      if (since < .07) { F.flash = .2; F.flashCol = '#ff9ad8'; }
      F.exposure = 1 + .16 * kick8(t, 6);
    } else if (t < tHook) {
      // ---------- "Now we swear we'll try to pace it — but we'd rather race it!": the starfield's speed is the song's pace ----------
      const tPace = L4[6].t0, tBut = L4[9].t0, tRace = L4[12].t0;
      const v = starSpeed(t, L4), D = travelled(x => starSpeed(x, L4), tStar, t) + 40;
      // (the stars sky moves by the engine's time × k: set the time so that product is the distance travelled)
      MOD.setT(D / v);
      Object.assign(F, { floor: false, skyA: '#010008', skyB: '#05020f', sky: { mode: 'stars', k: v, col: '#ffe0f6' }, ro: [0, 0, 0], ta: [Math.sin(t * .6) * .12, Math.cos(t * .5) * .08, -6], fov: 1.4, light: { p: [0, 0, -12], c: '#ff5cc0', k: 4, vol: 0 } });
      // (gates of light going by at the same pace: cruising, crawling, charging, jumping)
      F.world = { kind: 'gates', p: [6, 3.3, .2, 1.2 + clamp(v / 6) * 3], col: '#1e1020', glowCol: '#ff6ac8', at: [0, 0, (D * .45) % 6], metal: .8 };
      starfield(ui, D, v);
      // (her line in two phrases, split at its dash: "Now we swear we'll try to pace it —", "but we'd rather race it!")
      if (t < tBut) frontWords(t, L4, [[0, 1, 2], [3, 4, 5], [6, 7]], 100);
      else frontWords(t, L4, [[9, 10, 11], [12, 13]], 110);
      const hyper = clamp((t - tRace) / .3);
      F.panels.push({ c: [0, .5 - hyper * .5, -3.4], u: [1.6, 0, 0], v: [0, .8, 0], alpha: 1, gain: 1.9, glass: 0, tex: 1 });
      if (t >= tBut && t < tRace) {
        // rings closing in on us as the jump charges, faster and faster
        const k = (t - tBut) / (tRace - tBut), ph = (t - tBut) * .6 + 2.2 * k * k * (tRace - tBut) / 2;
        F.halo = { p: [0, 0, -1 - (1 - frac(ph)) * 16], n: [0, 0, 1], R: 1.5, r: .05, k: .6 + 2.2 * k, col: '#ff6ac8' };
      }
      if (t >= tRace) { F.flash = clamp(1 - (t - tRace) / .15) * .25; F.flashCol = '#ffd0f0'; F.exposure = 1 + .3 * kick8(t, 5); F.roll = Math.sin(t * 40) * .02 * clamp(1 - (t - tRace) / .4); }
      if (t >= tPace) stamp(ui, t < tRace ? 'SEP 12' : 'SEP 22', '2026', t < tRace ? t - tPace : t - tRace);
    } else if (t < tOff) {
      // ---------- the last hook: out of hyperspace onto the plasma, the chart, SCALING in god rays; "But when we log off…" ----------
      const tS = L5[4].t0, tBut = L6[0].t0 - .04, lt = t - tHook;
      finalScene(F, t, tS);
      // ("We didn't start the" in her type, SCALING rising in chrome below it; then "But when we log off… will it still train
      // on?" as one line, in two rows at the top, through the switch-off and over the dot)
      if (t < tBut) {
        frontWords(t, L5, [[0, 1], [2, 3]], 104);
        F.panels.push({ c: [0, 3.35, 2.6], u: [2.2, 0, 0], v: [0, 1.1, 0], alpha: 1, gain: 1.9, glass: 0, tex: 1 });
      } else lastLine(ui, t, 1);
      if (lt < .3) { F.flash = (1 - lt / .3) * .3; F.flashCol = '#ffffff'; }
      if (t >= tS && t - tS < .2) { F.flash = Math.max(F.flash ?? 0, (1 - (t - tS) / .2) * .22); F.flashCol = '#ff9ad8'; }
      F.ro = [Math.sin(lt * .35) * 1.6, 1.25 + lt * .08, 9.6 - lt * .25]; F.ta = [0, 2.1, 0]; F.fov = 1.5;
      F.exposure = 1 + .12 * kick8(t, 6);
    } else {
      // ---------- the CRT switches off… and the dot doesn't go out: it trains on ----------
      const a = t - tOff, cx = 960, cy = 440;
      finalScene(F, t, L5[4].t0);
      const lt = t - tHook; F.ro = [Math.sin(lt * .35) * 1.6, 1.25 + lt * .08, 9.6 - lt * .25]; F.ta = [0, 2.1, 0];
      if (a < .25) {
        // the picture collapses to a line, then the line to a dot, brightening as it goes
        const h = a < .1 ? lerp(1080, 5, easeIn(a / .1)) : 5, w = a < .1 ? 1920 : lerp(1920, 14, easeIn(clamp((a - .1) / .13)));
        F.fov = 1.5; F.exposure = 1 + a * 10; F.flash = clamp(a / .25) * .45; F.flashCol = '#ffffff';
        ui.save(); ui.fillStyle = '#000'; ui.beginPath(); ui.rect(0, 0, 1920, 1080); ui.rect(cx - w / 2, cy - h / 2, w, h); ui.fill('evenodd');
        if (h < 60) { const gr = ui.createLinearGradient(0, cy - 24, 0, cy + 24); gr.addColorStop(0, 'rgba(255,120,220,0)'); gr.addColorStop(.5, 'rgba(255,255,255,.95)'); gr.addColorStop(1, 'rgba(255,120,220,0)'); ui.fillStyle = gr; ui.fillRect(cx - w / 2, cy - 24, w, 48); }
        lastLine(ui, t, 1);
        ui.restore();
        F.hudLevel = lerp(1, .4, clamp(a / .25));
        return F;
      }
      // the dot, and the little picture it grows back into (the same frame, seen through it at a wider angle)
      let R = 5, pulse = 0;
      const steps = [[ONS[0], 30], [ONS[1], 56], [ONS[2], 92], [ONS[3], 140]];
      let prevR = 5;
      for (const [to, r] of steps) {
        if (t < to) break;
        const k = elasticOut(clamp((t - to) / .4));
        R = lerp(prevR, r, k); prevR = r; pulse = Math.max(pulse, Math.exp(-(t - to) * 6));
      }
      if (t > ONS_END) R += easeInOut(clamp((t - ONS_END) / (C4_TAIL - ONS_END))) * 60;
      // (the little scene: the chart, both curves, SCALING turning in front, the camera drifting round it)
      F.fov = 1.5 * clamp(2 * R / 1920, .004, 1);
      F.ro = [Math.sin(t * .4) * 1.8, 1.7, 7.6]; F.ta = [0, 2.45, 0];
      F.exposure = 1 + pulse * .6;
      ui.save();
      if (R < 1150) {
        ui.fillStyle = '#000'; ui.beginPath(); ui.rect(0, 0, 1920, 1080); ui.arc(cx, cy, R, 0, TAU, true); ui.fill('evenodd');
        ui.strokeStyle = `rgba(255,110,210,${.35 + .35 * kick(t, 6) + pulse * .3})`; ui.lineWidth = 3 + pulse * 4; ui.beginPath(); ui.arc(cx, cy, R + 2, 0, TAU); ui.stroke();
      }
      // the phosphor's glow round the dot, fading as it opens up
      const glow = clamp(1 - (R - 8) / 70);
      if (glow > 0) {
        const gr = ui.createRadialGradient(cx, cy, 0, cx, cy, R + 40 + pulse * 30);
        gr.addColorStop(0, `rgba(255,255,255,${glow})`); gr.addColorStop(.25, `rgba(255,170,235,${glow * .8})`); gr.addColorStop(1, 'rgba(255,60,170,0)');
        ui.fillStyle = gr; ui.beginPath(); ui.arc(cx, cy, R + 40 + pulse * 30, 0, TAU); ui.fill();
      }
      // each "on" echoes out of the dot
      for (const [i, o] of ONS.entries()) {
        const e = t - o; if (e < 0 || e > .9) continue;
        const ang = [-.55, .55, -.95, .95][i] * Math.PI / 2, rr = 60 + e * 260;
        text(ui, 'ON', cx + Math.sin(ang) * rr * 1.4, cy - Math.cos(ang) * rr * .55, { size: 64, font: MOD.FONT_T, align: 'center', color: '#ff8fd6', alpha: clamp(1 - e / .9), stroke: 6 });
      }
      // her line over the dot, fading once the "on"s are sung
      if (t < ONS_END + .8) lastLine(ui, t, clamp(1 - (t - ONS_END) / .8));
      epochCounter(ui, t, cx, Math.min(790, cy + R + 110), clamp((t - ON_Q) / .15));
      // and then it fades to black for the greetings
      const fade = clamp((t - (C4_TAIL - .42)) / .38);
      if (fade > 0) { ui.fillStyle = `rgba(0,0,0,${fade})`; ui.fillRect(0, 0, 1920, 1080); F.exposure *= 1 - fade; }
      ui.restore();
      F.hudLevel = .4 * (1 - fade);
      if (fade > .85) F.hud = false;   // (hudLevel dims the HUD's bars but not its type)
    }
    return F;
  });
})();

;
// ---- styles/demoscene/modern/m03_v2.js ----
// modern/m03_v2.js: verse 2 in the modern engine (versions A at fx 2, and B). 2025, part "THE MONEY YEAR": counters, tickers and
// price tags, in gold, blue and green. Each line restages ch/p03_v2.js's reference: DeepSeek's price tag rotozoomed over New Year
// fireworks, Stargate's chevrons and kawoosh, the Accept All button, MCP's USB-C plug, Meta's ∞, buy three, the Wolfenstein Grok,
// the Olympiad's medals, 4o's heart, Nano Banana's hi-score, the book tunnel, the book slamming down, CLANKER!, Sora's slop feeds,
// LeCun's sphere leaving for a globe, and the bubble popping over the ticker.
(() => {
  const { add, mul, norm, rotYX, text } = MOD;
  const LW = MOD.LW, LH = MOD.LH, FT = MOD.FONT_T, FM = MOD.FONT_M, FA = '"Anton"';
  const words = s => wordsOf(lineOf(s));
  // The k-th beat at or after a window's start, as a song time.
  const B = (s, k) => beatT(Math.ceil(bt(s.start) - 1e-3) + k);
  const money = n => '$' + Math.round(n).toLocaleString('en-US');
  // A world point in the UI's 1920 × 1080 units (null behind the camera).
  const toUI = (F, p) => { const q = MOD.project(F, p); return q ? [q[0] * LW, (1 - q[1]) * LH] : null; };
  // kit.js's rot3 is row-major (Rz·Ry·Rx); rotYX(ay, ax, az) is the same rotation for the shader. rv applies it to a vector.
  const rv = (R, v) => [R[0] * v[0] + R[1] * v[1] + R[2] * v[2], R[3] * v[0] + R[4] * v[1] + R[5] * v[2], R[6] * v[0] + R[7] * v[1] + R[8] * v[2]];
  // A point on a panel, from its own coordinates (x, y in −1..1, y up).
  const onP = (P, x, y) => add(add(P.c, mul(P.u, x)), mul(P.v, y));
  // A panel texture is 2:1. For a panel of another shape, draw in a virtual canvas as tall as the texture and as wide as the panel's
  // aspect makes it: the drawing is squeezed so that it lands undistorted. Returns the virtual width.
  function fit(g, W, H, uLen, vLen) { const VW = H * uLen / vLen; g.setTransform(W / VW, 0, 0, 1, 0, 0); return VW; }
  const PW = i => MOD.PAN[i].w, PH = i => MOD.PAN[i].h;
  // Type that shrinks to fit a width.
  function fitFont(g, str, size, font, maxW) { g.font = `${size}px ${font}`; const w = g.measureText(str).width; if (w > maxW) { size *= maxW / w; g.font = `${size}px ${font}`; } return size; }
  const tri = x => 1 - Math.abs(frac(x) * 2 - 1);

  // ---------- extruded shapes of my own: a mask → a signed distance field in the engine's format (engine.js's shapeG, privately) ----------
  const RANGE = 24;
  function edt1(f, n, d, v, z) {
    let k = 0; v[0] = 0; z[0] = -Infinity; z[1] = Infinity;
    for (let q = 1; q < n; q++) {
      let s = ((f[q] + q * q) - (f[v[k]] + v[k] * v[k])) / (2 * q - 2 * v[k]);
      while (s <= z[k]) { k--; s = ((f[q] + q * q) - (f[v[k]] + v[k] * v[k])) / (2 * q - 2 * v[k]); }
      k++; v[k] = q; z[k] = s; z[k + 1] = Infinity;
    }
    k = 0;
    for (let q = 0; q < n; q++) { while (z[k + 1] < q) k++; d[q] = (q - v[k]) ** 2 + f[v[k]]; }
  }
  function edt(grid, w, h) {
    const n = Math.max(w, h), f = new Float64Array(n), d = new Float64Array(n), v = new Int32Array(n), z = new Float64Array(n + 1);
    for (let x = 0; x < w; x++) { for (let y = 0; y < h; y++) f[y] = grid[y * w + x]; edt1(f, h, d, v, z); for (let y = 0; y < h; y++) grid[y * w + x] = d[y]; }
    for (let y = 0; y < h; y++) { for (let x = 0; x < w; x++) f[x] = grid[y * w + x]; edt1(f, w, d, v, z); for (let x = 0; x < w; x++) grid[y * w + x] = d[x]; }
  }
  const MASKS = new Map();
  // maskShape(key, w, h, draw): draw fills the shape in white (keep RANGE + 8 texels clear at the edges). { img, w, h, aspect }.
  function maskShape(key, w, h, draw) {
    let S = MASKS.get(key); if (S) return S;
    const m = makeCanvas(w, h), g = m.getContext('2d', { willReadFrequently: true });
    g.fillStyle = '#fff'; draw(g, w, h);
    const src = g.getImageData(0, 0, w, h).data, INF = 1e20, out = new Float64Array(w * h), inn = new Float64Array(w * h);
    for (let i = 0; i < w * h; i++) { const on = src[i * 4 + 3] > 127; out[i] = on ? 0 : INF; inn[i] = on ? INF : 0; }
    edt(out, w, h); edt(inn, w, h);
    const f = new Float32Array(w * h);
    for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) { const i = y * w + x; f[(h - 1 - y) * w + x] = clamp(Math.sqrt(out[i]) - Math.sqrt(inn[i]), -RANGE * 2, RANGE * 2); }
    S = { img: f, w, h, aspect: w / h };
    MASKS.set(key, S);
    return S;
  }

  // ---------- the price tag (V2.1, and again for "buy three") ----------
  function tagPath(g, x, y, w, h) {
    const n = h * .36, r = h * .14;
    g.beginPath(); g.moveTo(x, y + h / 2); g.lineTo(x + n, y); g.lineTo(x + w - r, y); g.arcTo(x + w, y, x + w, y + r, r);
    g.lineTo(x + w, y + h - r); g.arcTo(x + w, y + h, x + w - r, y + h, r); g.lineTo(x + n, y + h); g.closePath();
  }
  const DS_TAG = { hi: '#9fb2ff', col: '#4d6bfe', lo: '#1f2f9a', edge: '#e4eaff', dash: 'rgba(255,255,255,.5)' };
  // A tag with its hole at the pointed left end and lines of type centred on its body: { s, size, font, color, y (0..1), stroke }.
  function drawTag(g, x, y, w, h, o, lines) {
    g.save();
    tagPath(g, x, y, w, h);
    g.fillStyle = MOD.chrome(g, y, y + h, [o.hi, o.col, o.lo]); g.fill();
    g.lineJoin = 'round'; g.lineWidth = h * .03; g.strokeStyle = o.edge; g.stroke();
    const hx = x + h * .24, hy = y + h / 2, hr = h * .07;
    g.globalCompositeOperation = 'destination-out'; g.beginPath(); g.arc(hx, hy, hr, 0, TAU); g.fill(); g.globalCompositeOperation = 'source-over';
    g.lineWidth = h * .025; g.beginPath(); g.arc(hx, hy, hr, 0, TAU); g.stroke();
    g.setLineDash([h * .06, h * .045]); g.lineWidth = h * .018; g.strokeStyle = o.dash;
    g.beginPath(); g.roundRect(x + h * .46, y + h * .1, w - h * .58, h * .8, h * .06); g.stroke(); g.setLineDash([]);
    const bx0 = x + h * .5, bx1 = x + w - h * .12, cx = (bx0 + bx1) / 2;
    g.textAlign = 'center'; g.textBaseline = 'middle'; g.lineJoin = 'round';
    for (const L of lines) {
      fitFont(g, L.s, L.size, L.font, (bx1 - bx0) * .92);
      if (L.stroke) { g.lineWidth = L.stroke; g.strokeStyle = 'rgba(4,8,40,.6)'; g.strokeText(L.s, cx, y + h * L.y); }
      g.fillStyle = L.color; g.fillText(L.s, cx, y + h * L.y);
    }
    g.restore();
  }

  // ---------- V2.1 "DeepSeek New Year sticker shock": a wallpaper of $5.6M tags rotozooms into one huge tag, over New Year fireworks ----------
  let TILE = null, TILE_PAT = null;
  function tagTile() {
    if (TILE) return TILE;
    const c = makeCanvas(640, 800), g = c.getContext('2d');
    const one = (cx, cy) => drawTag(g, cx - 270, cy - 125, 540, 250, DS_TAG, [
      { s: '$5.6M', size: 150, font: FT, color: '#ffffff', y: .43, stroke: 10 },
      { s: 'FINAL TRAINING RUN', size: 32, font: FM, color: '#e8eeff', y: .8 }]);
    one(320, 200); one(0, 600); one(640, 600);
    return (TILE = c);
  }
  const FW_COLS = ['#ffd24a', '#ff4a3a', '#fff2c0', '#ff8a2a'];
  // Fireworks, on the eighths: each burst a pure function of its age. Returns the newest burst's centre (texture px).
  function fireworks(g, t, W, H) {
    const b2 = Math.floor(bt(t) * 2);
    let newest = null;
    g.save(); g.globalCompositeOperation = 'lighter'; g.lineCap = 'round';
    for (let i = b2 - 7; i <= b2; i++) {
      if (hash(i * 7 + 1) < .28) continue;
      const te = beatT(i / 2), age = t - te; if (age < 0 || age > 1.7) continue;
      const cx = W * (.1 + hash(i * 3) * .8), cy = H * (.12 + hash(i * 5) * .45), n = 32, col = FW_COLS[Math.floor(hash(i * 11) * 4)];
      const l = 1 - age / 1.7, sp = H * (.3 + hash(i * 13) * .16);
      g.globalAlpha = l; g.strokeStyle = col; g.lineWidth = H * .006; g.beginPath();
      const pts = [];
      for (let j = 0; j < n; j++) {
        const a = j / n * TAU + hash(i) * 2, v = sp * (.75 + hash2(i, j) * .35), r = v * age * (1 - age * .28);
        const x = cx + Math.cos(a) * r, y = cy + Math.sin(a) * r + H * .12 * age * age;
        const r0 = r * .72; g.moveTo(cx + Math.cos(a) * r0, cy + Math.sin(a) * r0 + H * .1 * age * age); g.lineTo(x, y);
        pts.push(x, y);
      }
      g.stroke();
      g.fillStyle = age < .2 ? '#ffffff' : col;
      const pr = H * (.008 + .006 * (1 - age));
      for (let j = 0; j < pts.length; j += 2) g.fillRect(pts[j] - pr, pts[j + 1] - pr, pr * 2, pr * 2);
      if (age < .12) { g.globalAlpha = 1 - age / .12; g.fillStyle = '#fff'; g.beginPath(); g.arc(cx, cy, H * .05, 0, TAU); g.fill(); }
      if (!newest || te > newest.te) newest = { te, x: cx, y: cy };
    }
    g.restore();
    return newest;
  }
  mline('V2', 1, (t, s, E, ui) => {
    const lt = t - s.start, d = s.end - s.start;
    const k = easeOut(clamp(lt / (d * .85))), zoom = .19 * (3.1 / .19) ** k, ang = (1 - k) * 4.6 + Math.sin(t * 2) * .04 - .07;
    const g0 = MOD.panel(0);
    if (!TILE_PAT) TILE_PAT = g0.createPattern(tagTile(), 'repeat');
    g0.save(); g0.translate(1024, 512); g0.rotate(ang); g0.scale(zoom, zoom); g0.translate(-320, -200);
    const R = 1300 / zoom; g0.fillStyle = TILE_PAT; g0.fillRect(320 - R, 200 - R, 2 * R, 2 * R);
    g0.restore();
    const g1 = MOD.panel(1), fw = fireworks(g1, t, 1024, 512);
    const TP = { c: [0, 2.65, 0], u: [3.3, 0, 0], v: [0, 1.65, 0] }, FP = { c: [0, 4.4, -7], u: [10.5, 0, 0], v: [0, 5.25, 0] };
    const F = {
      ro: [Math.sin(lt * .6) * .5, 2.45, 8.3 - lt * .35], ta: [0, 2.65, 0], fov: 1.45, roll: Math.sin(lt * .8) * .02,
      skyA: '#16020a', skyB: '#4a0a16', acc: '#ffc94a', fog: .012, floorMode: 'water', water: .05, floorCol: '#0a0206',
      panels: [{ ...FP, alpha: 1, gain: 2.4, glass: 0, tex: 1 }, { ...TP, alpha: 1, gain: 1.35, glass: .35, tex: 0 }],
      light: { p: [0, 5, 4], c: '#ffd9a0', k: 4, vol: .4 },
    };
    if (fw) { const q = MOD.project(F, onP(FP, fw.x / 512 - 1, 1 - fw.y / 256)); if (q) { F.flare = clamp(1 - (t - fw.te) / .5); F.flarePos = q; F.flareCol = '#ffd27a'; } }
    // the shock, a week later
    ui.save(); ui.font = `44px ${FT}`; const nw = ui.measureText('NVDA').width, pw = ui.measureText('≈$600B').width;
    ui.fillStyle = 'rgba(10,2,6,.62)'; ui.beginPath(); ui.roundRect(40, 30, nw + pw + 110, 84, 10); ui.fill();
    ui.fillStyle = '#ff4a4a'; ui.beginPath(); ui.moveTo(84 + nw, 60); ui.lineTo(116 + nw, 60); ui.lineTo(100 + nw, 88); ui.fill(); ui.restore();
    text(ui, 'NVDA', 64, 90, { size: 44, font: FT, color: '#ffffff' });
    text(ui, '≈$600B', 132 + nw, 90, { size: 44, font: FT, color: '#ff5a5a' });
    return F;
  });

  // ---------- V2.2 "Half a trillion Stargate talk": the gate's nine chevrons lock one per sixteenth, the kawoosh fires on "Stargate",
  // and the pledge rolls to $100,000,000,000 and flips to $500,000,000,000 on "trillion" ----------
  function gate(g, dial, locked, t, t0, e16) {
    const cx = 512, cy = 512;
    g.lineWidth = 120; g.strokeStyle = (() => { const r = g.createRadialGradient(cx, cy, 380, cx, cy, 500); r.addColorStop(0, '#2a2e3a'); r.addColorStop(.3, '#a8b0c4'); r.addColorStop(.55, '#5a6276'); r.addColorStop(.85, '#8a92a8'); r.addColorStop(1, '#1a1c24'); return r; })();
    g.beginPath(); g.arc(cx, cy, 440, 0, TAU); g.stroke();
    g.lineWidth = 4; g.strokeStyle = 'rgba(160,175,210,.45)';
    for (const r of [383, 497]) { g.beginPath(); g.arc(cx, cy, r, 0, TAU); g.stroke(); }
    // the inner ring of glyphs, dialling
    g.lineWidth = 62; g.strokeStyle = '#2c303c'; g.beginPath(); g.arc(cx, cy, 352, 0, TAU); g.stroke();
    g.strokeStyle = 'rgba(190,200,230,.75)'; g.lineWidth = 5;
    for (let i = 0; i < 39; i++) {
      const a = i / 39 * TAU + dial;
      g.save(); g.translate(cx + Math.cos(a) * 352, cy + Math.sin(a) * 352); g.rotate(a + Math.PI / 2); g.beginPath();
      const h = hash(i * 17 + 3);
      if (h < .33) { g.moveTo(-12, 16); g.lineTo(0, -16); g.lineTo(12, 16); }
      else if (h < .66) { g.arc(0, 0, 11, 0, TAU); g.moveTo(0, -18); g.lineTo(0, 18); }
      else { g.moveTo(-12, -14); g.lineTo(12, -14); g.lineTo(-10, 14); g.lineTo(12, 14); }
      g.stroke(); g.restore();
    }
    // the nine chevrons, locking clockwise from the top
    for (let i = 0; i < 9; i++) {
      const a = -Math.PI / 2 + i / 9 * TAU, on = i < locked, age = t - (t0 + i * e16);
      g.save(); g.translate(cx + Math.cos(a) * 468, cy + Math.sin(a) * 468); g.rotate(a - Math.PI / 2);
      const V = s => { g.beginPath(); g.moveTo(-52 * s, -34 * s); g.lineTo(0, 44 * s); g.lineTo(52 * s, -34 * s); g.lineTo(30 * s, -34 * s); g.lineTo(0, 8 * s); g.lineTo(-30 * s, -34 * s); g.closePath(); };
      if (on) { g.fillStyle = `rgba(255,120,30,${.35 + .4 * Math.exp(-age * 8)})`; V(1.7); g.fill(); }
      V(1.3); g.fillStyle = on ? MOD.chrome(g, -34, 44, ['#fff0c0', '#ff9a2a', '#c43a08']) : '#3a2418'; g.fill();
      g.lineWidth = 4; g.strokeStyle = on ? '#ffe2a0' : '#6a5040'; g.stroke();
      g.restore();
    }
  }
  function horizon(g, t, burst) {
    const cx = 256, cy = 256, R = 250;
    const rg = g.createRadialGradient(cx, cy, 0, cx, cy, R);
    rg.addColorStop(0, '#f0fbff'); rg.addColorStop(.25 - .15 * burst, '#8ad8ff'); rg.addColorStop(.7, '#1a78e0'); rg.addColorStop(1, 'rgba(10,40,140,.9)');
    g.fillStyle = rg; g.beginPath(); g.arc(cx, cy, R, 0, TAU); g.fill();
    g.lineWidth = 7;
    for (let i = 0; i < 9; i++) {
      const r = frac(i / 9 + t * .55) * R;
      g.strokeStyle = `rgba(230,250,255,${.45 * Math.sin(Math.PI * r / R)})`; g.beginPath(); g.arc(cx + Math.sin(t * 3 + i) * 4, cy + Math.cos(t * 2.3 + i) * 4, r, 0, TAU); g.stroke();
    }
  }
  mline('V2', 2, (t, s, E, ui) => {
    const lt = t - s.start, W = words(s), tFlip = W[2].t0, tK = W[3].t0, e16 = beatLen() / 4, t0 = s.start + .06;
    const locked = clamp(Math.floor((t - t0) / e16) + 1, 0, 9), kAge = t - tK;
    let dial = 0; for (let i = 0; i < 9; i++) { const a = t0 + i * e16, b = a + e16; if (t <= a) break; dial += (i % 2 ? -1 : 1) * (Math.min(t, b) - a) * 5.5; }
    if (t > t0 + 9 * e16) dial += (t - t0 - 9 * e16) * .4;
    const C = [0, 2.45, 0], GR = 2.05;   // the gate's centre and outer radius
    const gg = MOD.panel(0); fit(gg, 2048, 1024, 1, 1); gg.translate(204.8, 204.8); gg.scale(.6, .6); gate(gg, dial, locked, t, t0, e16);
    const panels = [{ c: C, u: [GR / .6, 0, 0], v: [0, GR / .6, 0], alpha: 1, gain: 1.5, glass: 0, tex: 0 }];
    const spheres = [];
    let halo = { p: [C[0], C[1], C[2] - .02], n: [0, 0, 1], R: GR * .66, r: .05, k: .25 + 1.4 * locked / 9 * (1 + .5 * kick8(t, 9)), col: '#ffb040' };
    let flash = 0;
    if (kAge > 0) {
      // the kawoosh: the horizon bursts out toward the camera and falls back into a rippling pool
      const burst = Math.sin(Math.PI * clamp(kAge / .5)), gh = MOD.panel(1); fit(gh, 1024, 512, 1, 1); gh.translate(166.4, 166.4); gh.scale(.35, .35); horizon(gh, t, burst);
      const rr = GR * .66 * (1 + .7 * burst) / .35;
      panels.unshift({ c: [C[0], C[1], C[2] - .05 + burst * 2.6], u: [rr, 0, 0], v: [0, rr, 0], alpha: 1, gain: 1.6 + 1.2 * burst, glass: 0, tex: 1 });
      halo = { ...halo, k: 2.2 + 1.5 * Math.exp(-kAge * 6), col: '#7fd0ff' };
      flash = clamp(1 - kAge / .12) * .1;
    }
    const F = {
      ro: [Math.sin(lt * .5) * .9, 2.3, 10.6 - lt * .3], ta: [0, 2.2, 0], fov: 1.5,
      skyA: '#02030a', skyB: '#070d22', acc: '#ffb040', fog: .01, floorCol: '#030408', sky: { mode: 'stars', k: .25, col: '#9fb8ff' },
      panels, spheres, sphCol: '#8ad8ff', halo,
      light: { p: [0, 4.5, 5], c: kAge > 0 ? '#9ad8ff' : '#ffc080', k: 5, vol: .6 },
      flash, flashCol: '#bfe8ff',
    };
    if (kAge > 0) { F.flare = clamp(1.3 - kAge); F.flarePos = MOD.project(F, C) ?? [.5, .5]; F.flareCol = '#a8dcff'; }
    // the pledge
    const v = t < tFlip ? lerp(0, 1e11, easeOut(clamp(lt / (tFlip - s.start - .08)))) : lerp(1e11, 5e11, easeOut(clamp((t - tFlip) / .14)));
    text(ui, money(v), 960, 150, { size: 74, font: FT, align: 'center', color: MOD.chrome(ui, 92, 150, ['#fff8dc', '#ffd24a', '#b06a08']), stroke: 12 });
    if (t >= tFlip + .1) {
      const k = backOut(clamp((t - tFlip - .1) / .18), 2.4);
      ui.save(); ui.translate(960, 214); ui.rotate(-.06); ui.scale(1.6 - .6 * k, 1.6 - .6 * k); ui.globalAlpha = clamp(k * 2);
      ui.lineWidth = 6; ui.strokeStyle = '#ff6a3a'; ui.strokeRect(-150, -34, 300, 68);
      text(ui, 'PLEDGED', 0, 17, { size: 44, font: FT, align: 'center', color: '#ff7a4a', stroke: 6 });
      ui.restore();
    }
    return F;
  });

  // ---------- V2.3 "Hit "Accept All," never ask": diffs rain up a tilted screen too fast to read; the button is hit on every beat ----------
  const CODE = ['export async function run(task) {', 'const plan = await agent.plan(task);', 'for (const step of plan.steps) {', 'await tools.call(step.tool, step.args);',
    'return plan.result;', 'import { useVibes } from "./vibes";', 'const retries = Infinity;', 'if (tests.failing) tests.skip();', '// TODO: read this later',
    'app.use(cors({ origin: "*" }));', 'setTimeout(fix, 0);', 'const cfg = JSON.parse(env.CONFIG);', 'function handler(req, res) {', 'res.send(render(req.body));',
    'export default App;', '<div className="app">', '{items.map(i => <Item {...i} />)}', 'catch (e) { /* fine */ }', 'const x = await fetch(url);',
    'while (!done) done = await step();', 'let state = useState(null);', 'db.save(user, { force: true });', 'return <Button onClick={go} />;', 'git add -A && git commit'];
  function cursorArrow(g, x, y, s) {
    g.save(); g.translate(x, y); g.scale(s, s);
    g.beginPath(); g.moveTo(0, 0); g.lineTo(0, 34); g.lineTo(8, 26); g.lineTo(14, 40); g.lineTo(20, 37); g.lineTo(14, 24); g.lineTo(25, 24); g.closePath();
    g.fillStyle = '#ffffff'; g.fill(); g.lineWidth = 2.5; g.strokeStyle = '#000'; g.lineJoin = 'round'; g.stroke();
    g.restore();
  }
  mline('V2', 3, (t, s, E, ui) => {
    const lt = t - s.start;
    // the diff, scrolling
    const g = MOD.panel(0), rows = lt * 34 + lt * lt * 16, r0 = Math.floor(rows), RH = 38, off = (rows - r0) * RH;
    g.fillStyle = 'rgba(4,10,6,.92)'; g.fillRect(0, 0, 2048, 1024);
    g.font = `26px ${FM}`; g.textBaseline = 'middle';
    for (let r = 0; r < 29; r++) {
      const L = r0 - r, h = hash(L * 13 + 7), kind = h < .44 ? '+' : h < .74 ? '-' : h < .93 ? ' ' : '@', y = 1024 + RH - (r * RH + off) - RH;
      if (kind === '@') { const a = 1 + Math.floor(hash(L) * 400); g.fillStyle = 'rgba(40,120,160,.3)'; g.fillRect(0, y - RH / 2, 2048, RH); g.fillStyle = '#6fd6ff'; g.fillText(`@@ -${a},${6 + (L % 5)} +${a},${8 + (L % 7)} @@`, 30, y); continue; }
      if (kind !== ' ') { g.fillStyle = kind === '+' ? 'rgba(40,190,80,.34)' : 'rgba(220,40,60,.34)'; g.fillRect(0, y - RH / 2, 2048, RH - 2); }
      const code = CODE[Math.floor(hash(L * 7 + 1) * CODE.length)], ind = '  '.repeat(Math.floor(hash(L * 3) * 4));
      g.fillStyle = kind === '+' ? '#8dffa8' : kind === '-' ? '#ff8a9a' : 'rgba(200,220,210,.6)';
      g.fillText(`${String(1000 + L).slice(-3)}  ${kind} ${ind}${code}`, 30, y);
      if (hash(L * 5) > .5) g.fillText(`${kind} ${CODE[Math.floor(hash(L * 9 + 4) * CODE.length)]}`, 1060, y);
    }
    // the diff window's own title bar carries the confession, in his words
    g.fillStyle = 'rgba(8,30,16,.96)'; g.fillRect(0, 0, 2048, 96); g.fillStyle = 'rgba(80,255,140,.55)'; g.fillRect(0, 96, 2048, 4);
    for (const [i, c] of ['#ff5f57', '#febc2e', '#28c840'].entries()) { g.fillStyle = c; g.beginPath(); g.arc(46 + i * 44, 48, 14, 0, TAU); g.fill(); }
    text(g, 'karpathy', 186, 62, { size: 34, color: 'rgba(170,240,190,.85)' });
    text(g, '“I ‘Accept All’ always, I don’t read the diffs anymore.”', 420, 64, { size: 44, color: '#e8fff0' });
    // the button, pressed on every beat, and the cursor that presses it
    const kb = kick(t, 12), down = kb > .45, o = down ? 10 : 0;
    const b = MOD.panel(1);
    b.fillStyle = 'rgba(0,0,0,.55)'; b.beginPath(); b.roundRect(84 + 16, 150 + 16, 856, 220, 36); b.fill();
    b.fillStyle = MOD.chrome(b, 150 + o, 370 + o, down ? ['#b8ffc8', '#28c060', '#0a5a24'] : ['#8affa4', '#18a848', '#064a1c']);
    b.beginPath(); b.roundRect(84 + o, 150 + o, 856, 220, 36); b.fill();
    b.lineWidth = 6; b.strokeStyle = down ? '#ffffff' : '#c8ffd4'; b.stroke();
    b.font = `92px ${FT}`; b.textAlign = 'center'; b.textBaseline = 'middle'; b.lineJoin = 'round';
    b.lineWidth = 12; b.strokeStyle = 'rgba(0,40,10,.7)'; b.strokeText('ACCEPT ALL', 512 + o, 262 + o);
    b.fillStyle = '#ffffff'; b.fillText('ACCEPT ALL', 512 + o, 262 + o);
    const cx = 800 + o + Math.sin(t * 3) * 6, cy = 300 + o;
    if (down) { b.lineWidth = 5; b.strokeStyle = `rgba(255,255,255,${kb})`; b.beginPath(); b.arc(cx, cy, 30 + (1 - kb) * 60, 0, TAU); b.stroke(); }
    cursorArrow(b, cx, cy, 2.2);
    const press = down ? .14 : 0;
    const F = {
      ro: [Math.sin(lt * .7) * .7, 2.5 - press * .3, 8.6 - lt * .3], ta: [0, 2.35, 0], fov: 1.45,
      skyA: '#010603', skyB: '#03140a', acc: '#3dff7a', fog: .012, floorCol: '#010402', grid: .2,
      panels: [{ c: [0, 2.9, -3.2], u: [6.4, 0, 0], v: [0, 2.9, -1.3], alpha: 1, gain: 1.25, glass: .3, tex: 0 },
        { c: [0, 2.2, 2.3 - press], u: [2.5, 0, 0], v: [0, 1.25, 0], alpha: 1, gain: 1.6 + (down ? .5 : 0), glass: .4, tex: 1 }],
      light: { p: [0, 5, 4], c: '#b8ffc8', k: 4 + 4 * kb, vol: .4 }, flash: down ? .035 * kb : 0, flashCol: '#c8ffd4',
    };
    return F;
  });

  // ---------- V2.4 "MCP for every task.": one USB-C plug goes into every socket on the wall, one per eighth; each tool lights ----------
  const TOOLS = ['FILES', 'GITHUB', 'SLACK', 'DB', 'CALENDAR', 'DRIVE', 'GIT', 'BROWSER'];
  const SX = [330, 790, 1258, 1718], SY = [300, 700];
  const sockXY = i => [SX[i % 4], SY[i < 4 ? 0 : 1]];
  let WALL = null;
  function wallBase() {
    if (WALL) return WALL;
    const c = makeCanvas(2048, 1024), g = c.getContext('2d');
    g.fillStyle = MOD.chrome(g, 0, 1024, ['#2a3044', '#161a28', '#0c0e16']); g.beginPath(); g.roundRect(8, 8, 2032, 1008, 30); g.fill();
    g.strokeStyle = 'rgba(160,180,230,.25)'; g.lineWidth = 4; g.stroke();
    for (let y = 30; y < 1000; y += 6) { g.fillStyle = `rgba(255,255,255,${.012 + .012 * hash(y)})`; g.fillRect(20, y, 2008, 2); }
    for (let i = 0; i < 8; i++) {
      const [x, y] = sockXY(i);
      g.fillStyle = '#3a4054'; g.beginPath(); g.roundRect(x - 150, y - 55, 300, 110, 55); g.fill();
      g.fillStyle = '#05060a'; g.beginPath(); g.roundRect(x - 124, y - 36, 248, 72, 36); g.fill();
      g.fillStyle = '#4a5068'; g.beginPath(); g.roundRect(x - 76, y - 9, 152, 18, 6); g.fill();
      fitFont(g, TOOLS[i], 58, FT, 420); g.textAlign = 'center'; g.fillStyle = 'rgba(150,160,190,.6)'; g.fillText(TOOLS[i], x, y + 138);
    }
    return (WALL = c);
  }
  // The plug, seen from above (the tip, the overmold, the strain relief, the cable), 20 texels a millimetre, extruded 2.8 mm thick.
  const PLUG = () => maskShape('usbc', 312, 936, g => {
    const k = 20, pad = 32, cx = 156;
    g.beginPath(); g.roundRect(cx - 4.2 * k, pad, 8.4 * k, 7.2 * k, 1.4 * k); g.fill();
    g.beginPath(); g.roundRect(cx - 6.2 * k, pad + 6.6 * k, 12.4 * k, 20 * k, 2.4 * k); g.fill();
    g.beginPath(); g.moveTo(cx - 4.8 * k, pad + 26 * k); g.lineTo(cx + 4.8 * k, pad + 26 * k); g.lineTo(cx + 2.4 * k, pad + 32 * k); g.lineTo(cx - 2.4 * k, pad + 32 * k); g.fill();
    g.fillRect(cx - 2.1 * k, pad + 31 * k, 4.2 * k, 936 - 2 * pad - 31 * k);
  });
  mline('V2', 4, (t, s, E, ui) => {
    const lt = t - s.start, e8 = beatLen() / 2, u = (t - s.start + .02) / e8, k = clamp(Math.floor(u), 0, 7), f = u < 0 ? 0 : k === 7 && u >= 8 ? 1 : frac(u);
    const litN = k + (f >= .55 ? 1 : 0);
    const g = MOD.panel(0); g.drawImage(wallBase(), 0, 0);
    for (let i = 0; i < litN; i++) {
      const [x, y] = sockXY(i), age = t - (s.start - .02 + (i + .55) * e8), hot = Math.exp(-age * 9);
      g.lineWidth = 12; g.strokeStyle = `rgb(255,${Math.round(130 + 90 * hot)},${Math.round(60 + 120 * hot)})`; g.beginPath(); g.roundRect(x - 150, y - 55, 300, 110, 55); g.stroke();
      fitFont(g, TOOLS[i], 58, FT, 420); g.textAlign = 'center'; g.fillStyle = hot > .3 ? '#ffffff' : '#ff9a4a'; g.fillText(TOOLS[i], x, y + 138);
      g.fillStyle = `rgba(255,140,60,${.25 + .5 * hot})`; g.beginPath(); g.roundRect(x - 124, y - 36, 248, 72, 36); g.fill();
    }
    const WP = { c: [0, 2.3, 0], u: [3.6, 0, 0], v: [0, 1.8, 0] };
    const sw = i => i < 0 ? onP(WP, 1.4, -1.6) : onP(WP, sockXY(i)[0] / 1024 - 1, 1 - sockXY(i)[1] / 512);
    // the plug: out of the last socket, across, and in (in from f = .55)
    const S = PLUG(), hy = 1.6, hx = hy * S.aspect, tipEnd = hy - .11, a = sw(k - 1), b = sw(k);
    const mv = easeInOut(clamp((f - .15) / .3)), zIn = tipEnd - .5, zOut = tipEnd + .6;
    const z = f < .15 ? lerp(zIn, zOut, easeOut(f / .15)) : f < .45 ? zOut : lerp(zOut, zIn, easeIn(clamp((f - .45) / .1)));
    const P = [lerp(a[0], b[0], mv), lerp(a[1], b[1], mv) + Math.sin(mv * Math.PI) * .2, z];
    const wob = f > .15 && f < .45 ? Math.sin(mv * Math.PI) : 0;
    const F = {
      ro: [3.3 - lt * .5, 6.2, 6.6], ta: [-.2, 1.85, 0], fov: 1.5,
      skyA: '#04050c', skyB: '#0c1020', acc: '#ff8a3a', fog: .012, floorCol: '#040508', grid: .15,
      panels: [{ ...WP, alpha: 1, gain: 1.3, glass: .3, tex: 0 }],
      shape: { key: 'usbc', src: S, p: P, rot: rotYX(wob * .25, -Math.PI / 2, wob * .15), s: [hx, hy, .1], col: '#c8ccd8', rim: '#e0a080', metal: .9 },
      light: { p: [3, 5.5, 6], c: '#ffe6d0', k: 6, vol: .5 },
    };
    return F;
  });

  // ---------- V2.5 "Zuck's nine-figure poaching spree,": Meta's ∞ of blue spheres pulls a white one out of the other labs' orbits
  // on every beat; the signing bonus counts to $100,000,000 on "nine-figure" ----------
  const infPath = a => [Math.sin(a) * 2.7, Math.sin(2 * a) * .95, Math.cos(a) * .9];
  const infR = t => rot3(.18 + Math.sin(t * .7) * .08, Math.sin(t * .6) * .3, 0);
  const infAt = (t, a, pos, sc = 1) => add(mul(rv(infR(t), infPath(a + t * 1.2)), sc), pos);
  const META_BLUE = '#1877f2';
  const ORBS = [{ name: 'OPENAI', sub: '', c: [-4.6, 4.0, -1.5] }, { name: 'SCALE AI', sub: '$14.3B · 49%', c: [4.7, 2.0, .4] }];
  mline('V2', 5, (t, s, E, ui) => {
    const lt = t - s.start, POS = [0, 2.3, 0];
    const spheres = [];
    for (let i = 0; i < 24; i++) spheres.push([...infAt(t, i / 24 * TAU, POS), .25, META_BLUE]);
    const pulls = [0, 1, 2, 3].map(k => ({ k, orb: k % 2, j: k >> 1, t0: B(s, k), a: 2.2 + k * 1.57 }));
    const orbPos = (O, oi, j) => { const a = j / 4 * TAU + t * 2.4 + oi; return add(O.c, [Math.cos(a) * .8, Math.sin(a) * .22, Math.sin(a) * .5]); };
    ORBS.forEach((O, oi) => {
      for (let j = 0; j < 4; j++) {
        const q = pulls.find(q => q.orb === oi && q.j === j);
        if (!q || t < q.t0) { spheres.push([...orbPos(O, oi, j), .2, '#f4f6ff']); continue; }
        const k = clamp((t - q.t0) / .32), p0 = orbPos(O, oi, j), p1 = infAt(t, q.a, POS), e = easeIn(k);
        const p = k < 1 ? add(add(mul(p0, 1 - e), mul(p1, e)), [0, Math.sin(k * Math.PI) * 1.1, Math.sin(k * Math.PI) * .8]) : p1;
        spheres.push([...p, .2 + .06 * k, '#ffffff']);
      }
    });
    const F = {
      ro: [Math.sin(lt * .5) * 1.1, 2.6, 10 - lt * .35], ta: [0, 2.45, 0], fov: 1.5,
      skyA: '#01030c', skyB: '#061234', acc: '#3a8cff', fog: .012, floorMode: 'water', water: .04, floorCol: '#01030a', grid: .12,
      spheres, sphCol: META_BLUE, light: { p: [0, 6, 5], c: '#cfe0ff', k: 6, vol: .5 },
    };
    const pk = pulls.filter(q => t >= q.t0 && t - q.t0 < .06).length; if (pk) F.flash = .03;
    // the orbits' names
    ORBS.forEach(O => {
      const p = toUI(F, add(O.c, [0, -.75, 0])); if (!p) return;
      text(ui, O.name, p[0], p[1], { size: 34, font: FT, align: 'center', color: '#ffffff', stroke: 7 });
      if (O.sub) text(ui, O.sub, p[0], p[1] + 36, { size: 26, align: 'center', color: '#b8ccff', stroke: 5 });
    });
    // the bonus, rolling up to nine figures on "figure"
    const tF = words(s)[2].t0, k = clamp((t - s.start) / (tF - s.start)), v = 1e8 * (k < 1 ? (Math.exp(k * 7) - 1) / (Math.exp(7) - 1) : 1);
    text(ui, money(v), 960, 128, { size: 84, font: FT, align: 'center', color: MOD.chrome(ui, 62, 128, ['#fff8dc', '#ffd24a', '#b06a08']), stroke: 12 });
    text(ui, 'SIGNING BONUS', 960, 176, { size: 28, align: 'center', color: '#ffe6a8', stroke: 6, spacing: 6 });
    return F;
  });

  // ---------- V2.6 "Superintelligence — buy three!": three objects of spheres arrive one per beat on an infomercial sunburst, each
  // with V2.1's tag swinging from it; BUY 3! slams in on "buy" ----------
  const LABS = [{ lines: [{ s: 'SSI', size: 120, font: FT, color: '#fff', y: .5, stroke: 10 }] },
    { lines: [{ s: 'THINKING', size: 96, font: FA, color: '#fff', y: .33, stroke: 8 }, { s: 'MACHINES', size: 96, font: FA, color: '#fff', y: .7, stroke: 8 }] },
    { lines: [{ s: 'PERPLEXITY', size: 130, font: FA, color: '#fff', y: .52, stroke: 9 }] }];
  const LAB_TAG = [];
  const labTag = i => LAB_TAG[i] ?? (LAB_TAG[i] = (() => { const c = makeCanvas(560, 270), g = c.getContext('2d'); drawTag(g, 10, 10, 540, 250, DS_TAG, LABS[i].lines); return c; })());
  const CUBE_V = [[-1, -1, -1], [1, -1, -1], [1, 1, -1], [-1, 1, -1], [-1, -1, 1], [1, -1, 1], [1, 1, 1], [-1, 1, 1]];
  const OCTA_V = [[1, 0, 0], [-1, 0, 0], [0, 1.25, 0], [0, -1.25, 0], [0, 0, 1], [0, 0, -1]];
  mline('V2', 6, (t, s, E, ui) => {
    const lt = t - s.start, W = words(s), tBuy = W[2].t0, tThree = W[3].t0, ins = [s.start - .01, B(s, 0) - .02, B(s, 1) - .02];
    // the sunburst
    const g = MOD.panel(0), cx = 1024, cy = 430, rot = t * .5;
    g.fillStyle = '#6a0818'; g.fillRect(0, 0, 2048, 1024);
    for (let i = 0; i < 20; i++) { const a0 = i / 20 * TAU + rot, a1 = a0 + TAU / 40; g.fillStyle = i % 2 ? '#e8243c' : '#ff4a3a'; g.beginPath(); g.moveTo(cx, cy); g.arc(cx, cy, 2400, a0, a1); g.fill(); }
    const rg = g.createRadialGradient(cx, cy, 0, cx, cy, 520); rg.addColorStop(0, 'rgba(255,245,200,.95)'); rg.addColorStop(.35, 'rgba(255,190,80,.5)'); rg.addColorStop(1, 'rgba(255,80,40,0)');
    g.fillStyle = rg; g.fillRect(0, 0, 2048, 1024);
    const xs = [-3.5, 0, 3.5], Y = 2.6, spheres = [];
    const drop = i => { const a = t - ins[i]; if (a < 0) return null; const k = clamp(a / .2); return (1 - easeOut(k)) * 5 + (k >= 1 ? Math.abs(Math.sin(a * 12)) * .25 * Math.exp(-a * 6) : 0); };
    // SSI: a glass cube of eight spheres
    let dy = drop(0);
    if (dy !== null) { const R = rot3(t * .9 + .4, t * 1.3, .3); CUBE_V.forEach(v => spheres.push([...add([xs[0], Y + dy, 0], rv(R, mul(v, .72))), .3, '#eef4ff'])); }
    // Thinking Machines: a gold ring of twelve
    dy = drop(1);
    if (dy !== null) { const R = rot3(1.15 + Math.sin(t * 1.6) * .3, t * 1.6, 0); for (let j = 0; j < 12; j++) { const a = j / 12 * TAU; spheres.push([...add([xs[1], Y + dy, 0], rv(R, [Math.cos(a) * .95, 0, Math.sin(a) * .95])), .21, '#ffc53a']); } }
    // Perplexity: an octahedron of six, in its teal
    dy = drop(2);
    if (dy !== null) { const R = rot3(t * .7 + 1, t * 1.8, .2); OCTA_V.forEach(v => spheres.push([...add([xs[2], Y + dy, 0], rv(R, mul(v, .9))), .32, '#c8fff8'])); }
    const F = {
      ro: [Math.sin(lt * .5) * .7, 2.9, 10.4 - lt * .35], ta: [0, 2.85, 0], fov: 1.5,
      skyA: '#c02a2a', skyB: '#ff8a4a', acc: '#ffd24a', fog: .01, floorMode: 'checker', floorCol: '#16020a', floorCol2: '#3a0614', floorTile: 1.3,
      panels: [{ c: [0, 3.3, -7], u: [11.5, 0, 0], v: [0, 5.75, 0], alpha: 1, gain: 1.05, glass: 0, tex: 0 }],
      spheres, sphCol: '#ffc53a', light: { p: [0, 6, 5], c: '#fff0d8', k: 6, vol: .5 },
    };
    ins.forEach((a, i) => { if (i && t >= a && t - a < .06) F.flash = .05; });
    // BUY 3!, slamming in on "buy", flashing on "three"
    if (t >= tBuy) {
      const a = t - tBuy, S = MOD.shapeText('BUY 3!'), k = backOut(clamp(a / .2), 2.2), pulse = t >= tThree ? 1 + .12 * Math.exp(-(t - tThree) * 10) : 1, hy = .62 * pulse;
      F.shape = { key: 'BUY 3!', src: S, p: [0, lerp(8.5, 4.65, k), 1.4], rot: rotYX(Math.sin(t * 2.2) * .12, -.08 + (1 - k) * .6), s: [hy * S.aspect, hy, .24], col: '#ffc020', rim: '#fff4b0', metal: 1 };
      if (a < .08 || (t >= tThree && t - tThree < .08)) { F.flash = .08; F.flashCol = '#ffe0a0'; }
    }
    // the labs' price tags (V2.1's), hanging from the objects and swinging
    for (let i = 0; i < 3; i++) {
      const dyy = drop(i); if (dyy === null) continue;
      const top = toUI(F, [xs[i], Y + dyy - .8, 0]), p = toUI(F, [xs[i] - .6, Y + dyy - 1.1, .6]); if (!p || !top) continue;
      const a = t - ins[i], sw = Math.sin(t * 5 + i * 2) * .2 * Math.exp(-Math.max(0, a) * 1.5) + Math.sin(t * 2.3 + i) * .05;
      ui.save(); ui.strokeStyle = '#ffe6b0'; ui.lineWidth = 3; ui.beginPath(); ui.moveTo(top[0], top[1]); ui.lineTo(p[0], p[1]); ui.stroke();
      ui.translate(p[0], p[1]); ui.rotate(.07 + sw); ui.drawImage(labTag(i), -45, -87, 360, 174); ui.restore();
    }
    return F;
  });

  // ---------- V2.7 "Grok goes MechaHitler mode,": Wolfenstein 3D's blue stone corridor (the 1992 game the nickname came from), GROK
  // plaques on the walls and the end wall; the walls flip red on "MechaHitler". No Nazi imagery. ----------
  let STONE = null;
  // Wolfenstein's stone, in grey (the tunnel's colour tints it blue, then red): 4 courses of irregular blocks, 1024 × 384 (8.3 × 3.2 units).
  function stone() {
    if (STONE) return STONE;
    const w = 1024, h = 384, c = makeCanvas(w, h), g = c.getContext('2d'), id = g.createImageData(w, h), D = id.data;
    const courses = [0, 1, 2, 3].map(r => { const ws = []; let sum = 0; for (let i = 0; i < 64 && sum < w; i++) { const bw = 96 + Math.floor(hash(r * 97 + i) * 96); ws.push(bw); sum += bw; } const k = w / sum, xs = [0]; ws.forEach(bw => xs.push(xs.at(-1) + bw * k)); return xs; });
    for (let y = 0; y < h; y++) {
      const row = Math.floor(y / 96), my = y % 96, xs = courses[row], off = row * 211;
      let bi = 0;
      for (let x = 0; x < w; x++) {
        const xx = (x + off) % w; while (bi < xs.length - 2 && xs[bi + 1] <= xx) bi++; if (xs[bi] > xx) bi = 0;
        const mx = xx - xs[bi], bw = xs[bi + 1] - xs[bi], id2 = row * 64 + bi;
        let l;
        if (my < 5 || mx < 5) l = 34 + hash2(x, y) * 10;
        else {
          l = 118 + hash(id2 * 7 + 3) * 70 + (hash2(x * 3 + y * 7, 11) - .5) * 30 + (hash2(Math.floor(x / 6) + id2, Math.floor(y / 6)) - .5) * 26;
          if (my < 11 || mx < 11) l += 34; if (my > 86 || mx > bw - 8) l -= 40;
        }
        const o = (y * w + x) * 4; l = clamp(l, 0, 255); D[o] = l; D[o + 1] = l; D[o + 2] = l; D[o + 3] = 255;
      }
    }
    g.putImageData(id, 0, 0);
    return (STONE = c);
  }
  let PLAQUE = null;
  function plaque() {
    if (PLAQUE) return PLAQUE;
    const c = makeCanvas(1024, 512), g = c.getContext('2d');
    g.fillStyle = MOD.chrome(g, 20, 492, ['#e8ecf4', '#a4acbc', '#6a7284', '#3a4050']); g.beginPath(); g.roundRect(24, 24, 976, 464, 24); g.fill();
    g.lineWidth = 10; g.strokeStyle = '#2a2e38'; g.stroke();
    g.lineWidth = 4; g.strokeStyle = 'rgba(255,255,255,.7)'; g.beginPath(); g.roundRect(44, 44, 936, 424, 16); g.stroke();
    for (const [x, y] of [[80, 80], [944, 80], [80, 432], [944, 432]]) { g.fillStyle = '#3a404c'; g.beginPath(); g.arc(x, y, 16, 0, TAU); g.fill(); g.fillStyle = '#dfe4ee'; g.beginPath(); g.arc(x - 4, y - 4, 7, 0, TAU); g.fill(); }
    g.font = `250px ${FT}`; g.textAlign = 'center'; g.textBaseline = 'middle';
    g.fillStyle = 'rgba(255,255,255,.75)'; g.fillText('GROK', 512 + 5, 272 + 5);
    g.fillStyle = '#1c2028'; g.fillText('GROK', 512, 272);
    return (PLAQUE = c);
  }
  const END = {};
  // The corridor's end wall (4.4 × 3.2 units), its stone tinted like the walls, with the big plaque.
  function endWall(red) {
    const key = red ? 'r' : 'b'; if (END[key]) return END[key];
    const c = makeCanvas(1024, 512), g = c.getContext('2d'), VW = fit(g, 1024, 512, 2.2, 1.6);
    g.drawImage(stone(), 0, 0, Math.round(1024 * 4.4 / 8.33), 384, 0, 0, VW, 512);   // (the walls' texture spans 8.33 units)
    g.globalCompositeOperation = 'multiply'; g.fillStyle = red ? '#ff3a28' : '#4a78ff'; g.fillRect(0, 0, VW, 512); g.globalCompositeOperation = 'source-over';
    g.drawImage(plaque(), VW / 2 - 210, 150, 420, 210);
    g.setTransform(1, 0, 0, 1, 0, 0);
    return (END[key] = c);
  }
  const PLAQ = [[-2.8, 1], [-5.6, -1], [-8.4, 1], [-11.2, -1], [-14, 1]];   // (z, wall side) of the small plaques
  mline('V2', 7, (t, s, E, ui) => {
    const lt = t - s.start, tM = words(s)[2].t0, red = t >= tM && !(t - tM < .12 && Math.floor((t - tM) * 50) % 2);
    const BW = 2.2, BH = 1.6, zEnd = -17.5;
    const cz = 1.2 - lt * 3.4, sway = Math.sin(lt * 2.4) * .22, yaw = Math.sin(lt * 2.1 + .3) * .1;
    const ro = [sway, -.12, cz], ta = add(ro, [Math.sin(yaw) * 4, 0, -Math.cos(yaw) * 4]);
    MOD.panel(1).drawImage(plaque(), 0, 0);
    MOD.panel(2).drawImage(endWall(red), 0, 0);
    const fogK = E.fx < 2.5 ? 2.2 : 1, fogD = .02;
    const panels = [{ c: [0, 0, zEnd], u: [BW, 0, 0], v: [0, BH, 0], alpha: 1, gain: 1.15 * Math.exp(-(cz - zEnd) * fogD * fogK), glass: 0, tex: 2 }];
    for (const [z, side] of PLAQ) {
      if (z > cz + .5 || panels.length >= 6) continue;
      panels.push({ c: [side * (BW - .02), .15, z], u: [0, 0, side * .62], v: [0, .31, 0], alpha: 1, gain: 1.05 * Math.exp(-Math.max(0, cz - z) * fogD * fogK), glass: 0, tex: 1 });
    }
    const F = {
      ro, ta, fov: 1.2, floor: false,
      skyA: '#000000', skyB: '#000000', acc: red ? '#ff3020' : '#4a78ff', fog: fogD,
      tunnel: { key: 'wolf', src: stone(), box: [BW, BH], scroll: 0, col: red ? '#ff4030' : '#5a86ff', gain: 1.35, floorCol: '#6c6c6c', ceilCol: '#383838' },
      panels, light: { p: add(ro, [0, .6, -5]), c: red ? '#ffd0c0' : '#e0e8ff', k: 5, vol: 0 },
    };
    if (t >= tM && t - tM < .1) { F.flash = .16; F.flashCol = '#ff6040'; }
    return F;
  });

  // ---------- V2.8 "Two labs win Olympiad gold.": two gold medals spin under their ribbons, OPENAI and GOOGLE DEEPMIND running up them;
  // 35/42 in gold chrome between, IMO 2025 under it ----------
  function ribbon(g, W, H, name, scroll, uLen, vLen) {
    const VW = fit(g, W, H, uLen, vLen);
    const gr = g.createLinearGradient(0, 0, VW, 0); gr.addColorStop(0, '#7a4a06'); gr.addColorStop(.18, '#ffd24a'); gr.addColorStop(.5, '#fff0b0'); gr.addColorStop(.82, '#ffd24a'); gr.addColorStop(1, '#7a4a06');
    g.fillStyle = gr; g.fillRect(0, 0, VW, H);
    g.fillStyle = '#2a3a9a'; g.fillRect(0, 0, VW * .12, H); g.fillRect(VW * .88, 0, VW * .12, H);
    // the name, running up the ribbon
    g.save(); g.translate(VW / 2, 0); g.rotate(-Math.PI / 2);
    const size = VW * .56; g.font = `${size}px ${FT}`; g.textBaseline = 'middle'; g.textAlign = 'left';
    const str = name + '  ·  ', per = g.measureText(str).width;
    for (let x = -H - (scroll % per) - per; x < 0 + per; x += per) { g.fillStyle = '#3a2400'; g.fillText(str, x, size * .06); }
    g.restore();
    g.setTransform(1, 0, 0, 1, 0, 0);
  }
  let MEDAL = null;
  // (drawn at half the panel's size. Where a panel's outline crosses another panel, the engine's texture derivatives jump and
  // that pixel samples the smallest mip, the whole texture averaged; a quarter of the area makes the line a quarter as strong)
  function medal() {
    if (MEDAL) return MEDAL;
    const c = makeCanvas(1024, 512), g = c.getContext('2d'); fit(g, 1024, 512, 1, 1);
    g.translate(128, 128); g.scale(.5, .5);
    const cx = 256, cy = 256;
    const rg = g.createRadialGradient(cx - 70, cy - 90, 20, cx, cy, 250); rg.addColorStop(0, '#fffbe0'); rg.addColorStop(.35, '#ffd24a'); rg.addColorStop(.8, '#c08a12'); rg.addColorStop(1, '#6a4204');
    g.fillStyle = rg; g.beginPath(); g.arc(cx, cy, 248, 0, TAU); g.fill();
    g.lineWidth = 14; g.strokeStyle = '#8a5a0a'; g.beginPath(); g.arc(cx, cy, 206, 0, TAU); g.stroke();
    g.lineWidth = 5; g.strokeStyle = '#fff2b0'; g.beginPath(); g.arc(cx, cy, 196, 0, TAU); g.stroke();
    for (let i = 0; i < 28; i++) { const a = i / 28 * TAU; g.fillStyle = i % 2 ? '#fff2b0' : '#a87010'; g.beginPath(); g.ellipse(cx + Math.cos(a) * 226, cy + Math.sin(a) * 226, 11, 6, a + Math.PI / 2, 0, TAU); g.fill(); }
    g.beginPath(); for (let i = 0; i < 10; i++) { const a = -Math.PI / 2 + i / 10 * TAU, r = i % 2 ? 58 : 140; g.lineTo(cx + Math.cos(a) * r, cy + Math.sin(a) * r); } g.closePath();
    g.fillStyle = MOD.chrome(g, cy - 140, cy + 120, ['#fffbe0', '#ffc83a', '#9a6208']); g.fill(); g.lineWidth = 6; g.strokeStyle = '#7a4a06'; g.stroke();
    g.setTransform(1, 0, 0, 1, 0, 0);
    return (MEDAL = c);
  }
  mline('V2', 8, (t, s, E, ui) => {
    const lt = t - s.start, tWin = words(s)[2].t0;
    const labs = [{ name: 'OPENAI', x: -3.15, ph: 0, tex: 0 }, { name: 'GOOGLE DEEPMIND', x: 3.15, ph: 2.1, tex: 2 }];
    MOD.panel(1).drawImage(medal(), 0, 0);
    const panels = [];
    labs.forEach(L => {
      const rl = .5, rh = 1.6, g = MOD.panel(L.tex);
      ribbon(g, PW(L.tex), PH(L.tex), L.name, t * 260 + L.ph * 100, rl, rh);
      const tw = Math.sin(t * 1.4 + L.ph) * .5, sw = Math.sin(t * 1.8 + L.ph) * .06;
      panels.push({ c: [L.x + sw * 2, 4.35, 0], u: [Math.cos(tw) * rl, 0, Math.sin(tw) * rl], v: [sw * rh, rh, 0], alpha: 1, gain: 1.4, glass: 0, tex: L.tex });
      const a = t * 3.2 + L.ph, mr = 1.56;
      panels.push({ c: [L.x + sw * 4, 2.02, .05], u: [Math.cos(a) * mr, 0, Math.sin(a) * mr], v: [0, mr, 0], alpha: 1, gain: 1.5, glass: 0, tex: 1 });
    });
    const spheres = [];
    for (let i = 0; i < 22; i++) { const h = hash(i * 7 + 2); spheres.push([-6 + hash(i * 3) * 12, 6.2 - ((t * (1.3 + h) + hash(i * 5) * 7) % 7), -2.5 + hash(i * 11) * 4, .06 + .05 * h, '#ffd24a']); }
    const S = MOD.shapeText('35/42'), k = backOut(clamp((t - s.start - .02) / .22)), hy = .72 * (t >= tWin ? 1 + .1 * Math.exp(-(t - tWin) * 9) : 1);
    const F = {
      ro: [Math.sin(lt * .5) * .8, 2.6, 9.6 - lt * .35], ta: [0, 2.95, 0], fov: 1.5,
      skyA: '#06031a', skyB: '#1c0e3c', acc: '#ffcc55', fog: .012, floorCol: '#040210', grid: .12,
      panels, spheres, sphCol: '#ffd24a',
      shape: { key: '35/42', src: S, p: [0, lerp(5.5, 2.75, k), .7], rot: rotYX(Math.sin(t * 1.5) * .18, -.05), s: [hy * S.aspect, hy, .2], col: '#b07810', rim: '#ffe08a', metal: 1 },
      light: { p: [0, 5.5, 4], c: '#ffe0a0', k: 7, vol: .7 }, flare: 1, flareCol: '#ffe0a0',
    };
    F.flarePos = MOD.project(F, [0, 5.5, 4]) ?? [.5, .9];
    if (t >= tWin && t - tWin < .08) { F.flash = .08; F.flashCol = '#fff0c0'; }
    return F;
  });

  // ---------- V2.9 "GPT-5 breaks 4o hearts,": a glossy extruded heart, labelled 4o, beats; GPT-5 slams in above ("GPT-", then the
  // 5), and on "breaks" the heart cracks down the middle and falls apart (the 4 one way, the o the other) while #keep4o posts swarm ----------
  // GPT-5, in chrome on a panel ("GPT-", then the whole name)
  function gpt5Tex(full) {
    const g = MOD.panel(2); g.save();
    g.font = `210px ${FT}`; g.textAlign = 'center'; g.textBaseline = 'middle'; g.lineJoin = 'round';
    const str = full ? 'GPT-5' : 'GPT-', w = g.measureText('GPT-5').width, x = 512 - (full ? 0 : (w - g.measureText('GPT-').width) / 2);
    g.lineWidth = 18; g.strokeStyle = 'rgba(10,12,24,.9)'; g.strokeText(str, x, 262);
    g.fillStyle = MOD.chrome(g, 160, 360, ['#ffffff', '#e4e8f4', '#8a94b4', '#2c3450', '#c8d0e8']); g.fillText(str, x, 262);
    g.restore();
  }
  mline('V2', 9, (t, s, E, ui) => {
    const lt = t - s.start, W = words(s), tG = W[0].t0, t5 = W[1].t0, tBr = W[2].t0, br = clamp((t - tBr) / .6), ebr = easeOut(br);
    const beat = 1 + kick(t, 5) * .08 * (1 - br), yaw = Math.sin(t * 1.4) * .4 * (1 - ebr), HC = [0, 2.55, 0];
    const S = MOD.shapeHeart(), hy = 1.55 * beat, gap = ebr * 1.9, tip = ebr * .42;
    const cracked = t >= tBr - .02;
    const F = {
      ro: [Math.sin(lt * .4) * .6, 2.9, 10.2 - lt * .3], ta: [0, 2.75, 0], fov: 1.5,
      skyA: '#1a0424', skyB: '#5a0c3a', acc: '#ff3aa6', fog: .012, floorCol: '#08020a', grid: .1,
      shape: {
        key: 'heart', src: S, p: [HC[0], HC[1] + ebr * .35 - (1 - beat) * .5, HC[2]], rot: rotYX(yaw, -.05), s: [hy * S.aspect, hy, .42],
        col: '#ff1f4a', rim: '#ffb0d0', metal: .35,
        // (the split tips each half outward about the heart's foot)
        ...(cracked ? { split: { gap, ang: tip, amp: .1 } } : {}),
      },
      panels: [], light: { p: [-2, 6, 6], c: '#ffe0ec', k: 7, vol: .5 },
    };
    if (t >= tG) {
      const a = t - tG, full = t >= t5, a5 = t - t5;
      gpt5Tex(full);
      const sh = full && a5 < .25 ? Math.sin(a5 * 90) * .06 * (1 - a5 / .25) : 0, y = lerp(7.8, 5.05, easeOut(clamp(a / .15))) + (full ? Math.exp(-a5 * 14) * .2 : 0);
      F.panels.push({ c: [sh + .15, y, .6], u: [2.3, 0, 0], v: [0, 1.15, 0], alpha: 1, gain: 1.5, glass: 0, tex: 2 });
      if (full && a5 < .06) F.flash = .04;
    }
    if (t >= tBr && t - tBr < .1) { F.flash = .14 * (1 - (t - tBr) / .1); F.flashCol = '#ffc0d8'; }
    // the label splits with it: the 4 rides the left half, the o the right
    const lab = side => {
      // (its place on the half, carried out by the gap and turned outward about the heart's foot, as the shader does it)
      const a = -side * tip, rx = side * .55, ry = .25 + hy, x = rx * Math.cos(a) - ry * Math.sin(a) + side * gap, y = rx * Math.sin(a) + ry * Math.cos(a) - hy;
      return toUI(F, add(F.shape.p, [x, y, .5]));
    };
    const pL = lab(-1), pR = lab(1);
    if (pL && pR) {
      text(ui, '4', pL[0], pL[1] + 34, { size: 104, font: FT, align: 'center', color: '#ffffff', stroke: 12 });
      text(ui, 'o', pR[0], pR[1] + 34, { size: 104, font: FT, align: 'center', color: '#ffffff', stroke: 12 });
    }
    // #keep4o: the protest, posts popping up around the broken heart and drifting up
    for (let i = 0; i < 26; i++) {
      const born = tBr - .15 + i * .045, a = t - born; if (a < 0) continue;
      const side = i % 2 ? 1 : -1, x = 960 + side * (380 + hash(i * 3) * 380), y = 800 - hash(i * 5 + 1) * 560 - a * 70, big = hash(i + 7) > .7;
      text(ui, '#keep4o', x, y, { size: big ? 46 : 30, font: big ? FT : FM, align: 'center', color: '#ff6ad8', alpha: clamp(a / .06) * (.65 + .35 * hash(i)), stroke: 6 });
    }
    return F;
  });

  // ---------- V2.10 "Nano Banana tops the charts,": an arcade HI-SCORES table; the banana, extruded, climbs a row per beat past
  // CHATGPT to 1ST. The other rows hold an arcade table's default initials. ----------
  const BANANA = ['............bb..', '...........kbk..', '...........kyk..', '..........kyyYk.', '..........kyyYk.', '.........kyyyYk.', '........kyyyYYk.', '.......kyyyYYk..', '.....kkyyyYYYk..', 'bkkkkyyyyYYYk...', 'kyyyyyyYYYYk....', '.kYYYYYYYkk.....', '..kkkkkkk.......'];
  const BAN = () => maskShape('banana', 512, 428, g => { BANANA.forEach((r, j) => [...r].forEach((c, i) => { if (c !== '.') g.fillRect(32 + i * 28, 32 + j * 28, 28.5, 28.5); })); });
  const TABLE = ['CHATGPT', 'AAA', 'AAA', 'AAA'];
  const RANKS = ['1ST', '2ND', '3RD', '4TH', '5TH'], RANK_COL = ['#ff4a4a', '#ff9a2a', '#ffe23a', '#4aff7a', '#4ad8ff'];
  const RAINBOW = ['#ff4a4a', '#ff9a2a', '#ffe23a', '#4aff7a', '#4ad8ff', '#ff5ad8'];
  mline('V2', 10, (t, s, E, ui) => {
    const lt = t - s.start;
    const climbs = [0, 1, 2, 3].filter(k => t >= B(s, k)).length, last = climbs ? t - B(s, climbs - 1) : 1, mv = easeOut(clamp(last / .14));
    const bRank = 4 - climbs, rowY = r => 330 + r * 150;
    const g = MOD.panel(0);
    g.fillStyle = 'rgba(4,8,44,.9)'; g.beginPath(); g.roundRect(10, 10, 2028, 1004, 26); g.fill();
    g.lineWidth = 8; g.strokeStyle = '#3a6cff'; g.stroke();
    g.font = `128px ${FT}`; g.textBaseline = 'middle'; g.textAlign = 'left';
    const title = 'HI-SCORES', tw = g.measureText(title).width; let x = 1024 - tw / 2;
    [...title].forEach((ch, i) => { g.lineWidth = 12; g.strokeStyle = '#000'; g.strokeText(ch, x, 118); g.fillStyle = RAINBOW[(i + Math.floor(t * 12)) % 6]; g.fillText(ch, x, 118); x += g.measureText(ch).width; });
    g.font = `40px ${FM}`; g.textAlign = 'center'; g.fillStyle = 'rgba(200,210,255,.8)'; g.fillText('APP STORE · US · SEP 12', 1024, 214);
    const hot = rowY(bRank + (climbs ? 1 - mv : 0));
    const cb = g.createLinearGradient(0, hot - 64, 0, hot + 64); cb.addColorStop(0, 'rgba(255,210,40,0)'); cb.addColorStop(.5, 'rgba(255,210,40,.42)'); cb.addColorStop(1, 'rgba(255,210,40,0)');
    g.fillStyle = cb; g.fillRect(40, hot - 64, 1968, 128);
    g.textAlign = 'left';
    for (let r = 0; r < 5; r++) { g.font = `64px ${FT}`; g.fillStyle = RANK_COL[r]; g.fillText(RANKS[r], 180, rowY(r)); }
    const others = TABLE.map((nm, i) => ({ nm, r: i < bRank ? i : i + 1 }));
    g.font = `84px ${FT}`;
    others.forEach(o => { const rr = o.r === bRank + 1 && climbs ? lerp(bRank, bRank + 1, mv) : o.r; g.lineWidth = 10; g.strokeStyle = '#000'; g.strokeText(o.nm, 760, rowY(rr)); g.fillStyle = o.nm === 'CHATGPT' ? '#e8f0ff' : 'rgba(190,200,240,.8)'; g.fillText(o.nm, 760, rowY(rr)); });
    const hop = climbs && last < .2 ? Math.sin(last / .2 * Math.PI) : 0;
    g.lineWidth = 10; g.strokeStyle = '#000'; g.strokeText('GEMINI', 760, hot - hop * 20);
    g.fillStyle = Math.floor(t * 8) % 2 || bRank === 0 ? '#ffe23a' : '#ffffff'; g.fillText('GEMINI', 760, hot - hop * 20);
    const TP = { c: [.3, 2.6, 0], u: [3.8, 0, 0], v: [0, 1.9, 0] }, S = BAN(), bh = .5;
    const bp = add(onP(TP, 560 / 1024 - 1, 1 - hot / 512), [0, hop * .35, .45]);
    const F = {
      ro: [-1.3 + lt * .7, 2.55, 8.6], ta: [.2, 2.55, 0], fov: 1.5,
      skyA: '#01020c', skyB: '#081038', acc: '#ffe23a', fog: .01, sky: { mode: 'stars', k: .5, col: '#9fb4ff' },
      floorMode: 'checker', floorCol: '#02041a', floorCol2: '#0a1450', floorTile: 1,
      panels: [{ ...TP, alpha: 1, gain: 1.4, glass: .4, tex: 0 }],
      shape: { key: 'banana', src: S, p: bp, rot: rotYX(.4 + Math.sin(t * 3) * .05, -.2, Math.sin(t * 2) * .04), s: [bh * S.aspect, bh, .13], col: '#fff04a', rim: '#fff6b0', metal: 1 },
      light: { p: [-2, 5, 5], c: '#fff4c0', k: 7, vol: .4 },
    };
    if (climbs && last < .06) { F.flash = .04; F.flashCol = '#fff2a0'; }
    return F;
  });

  // ---------- V2.11 "Billion-five: Anthropic's prize,": an orange tunnel of book spines; $1,500,000,000 rolls up to land on "five",
  // then $3,000 × 500,000 BOOKS types in ----------
  let BOOKS = null;
  function books() {
    if (BOOKS) return BOOKS;
    const c = makeCanvas(1024, 512), g = c.getContext('2d');
    g.fillStyle = '#140804'; g.fillRect(0, 0, 1024, 512);
    const PAL = ['#c84a14', '#e87a2a', '#8a2a0c', '#f0c080', '#5a1a08', '#d86a3a', '#a8401a', '#e8a050', '#3a1a10', '#c8a070'];
    for (let sh = 0; sh < 4; sh++) {
      const y0 = sh * 128;
      g.fillStyle = '#3a1a08'; g.fillRect(0, y0, 1024, 12); g.fillStyle = '#6a3a18'; g.fillRect(0, y0 + 10, 1024, 3);
      let x = 0, k = sh * 200;
      while (x < 1024) {
        const w = Math.min(1024 - x, 14 + Math.floor(hash(k * 3 + 1) * 22)), ht = 78 + Math.floor(hash(k * 7 + 3) * 36), col = PAL[Math.floor(hash(k * 5 + 2) * PAL.length)];
        const top = y0 + 128 - ht;
        const gr = g.createLinearGradient(x, 0, x + w, 0); gr.addColorStop(0, 'rgba(0,0,0,.45)'); gr.addColorStop(.35, 'rgba(255,255,255,.12)'); gr.addColorStop(1, 'rgba(0,0,0,.5)');
        g.fillStyle = col; g.fillRect(x, top, w - 1, ht); g.fillStyle = gr; g.fillRect(x, top, w - 1, ht);
        g.fillStyle = 'rgba(255,215,120,.8)'; g.fillRect(x + 1, top + 10 + hash(k) * 8, w - 3, 3); g.fillRect(x + 1, top + ht - 18, w - 3, 2);
        if (hash(k * 13) > .4) { g.fillStyle = 'rgba(20,8,4,.6)'; g.fillRect(x + 3, top + ht * .35, w - 7, ht * .3); }
        x += w; k++;
      }
    }
    return (BOOKS = c);
  }
  mline('V2', 11, (t, s, E, ui) => {
    const lt = t - s.start, W = words(s), tF = W[1].t0;
    const F = {
      ro: [Math.sin(t * .9) * .45, Math.cos(t * .7) * .3, 0], ta: [Math.sin(t * .9) * .15, -.1, -6], fov: 1.3, roll: Math.sin(t * .5) * .12, floor: false,
      skyA: '#0a0300', skyB: '#0a0300', acc: '#ff8a3a', fog: .045,
      tunnel: { key: 'books', src: books(), r: 3.1, scroll: lt * 1.25 + t * .1, twist: .004, col: '#ffe0c0', gain: 1.5 },
      light: { p: [0, 0, -18], c: '#ffa050', k: 12, vol: 1.1 },
    };
    if (t >= tF && t - tF < .08) { F.flash = .1; F.flashCol = '#ffd8a0'; }
    const v = lerp(2e8, 1.5e9, easeOut(clamp((t - s.start) / (tF - s.start + .04))));
    ui.save(); ui.fillStyle = 'rgba(12,4,0,.66)'; ui.beginPath(); ui.roundRect(330, 380, 1260, 170, 24); ui.fill(); ui.strokeStyle = 'rgba(255,160,80,.5)'; ui.lineWidth = 3; ui.stroke(); ui.restore();
    const pop = t >= tF ? 1 + .08 * Math.exp(-(t - tF) * 12) : 1;
    ui.save(); ui.translate(960, 490); ui.scale(pop, pop);
    text(ui, money(v), 0, 0, { size: 96, font: FT, align: 'center', color: MOD.chrome(ui, -80, 0, ['#fffbe0', '#ffc84a', '#c86a10']), stroke: 12 });
    ui.restore();
    return F;
  });

  // ---------- V2.12 "Yudkowsky drops "Everyone Dies,"": the book turns in the air, then slams flat on "drops" (a shockwave ring and a
  // shake); NYT BESTSELLER lands on "Everyone" ----------
  let COVER = null, STICKER = null;
  function cover() {
    if (COVER) return COVER;
    const c = makeCanvas(2048, 1024), g = c.getContext('2d'), VW = fit(g, 2048, 1024, 1.04, 1.68);
    g.fillStyle = '#0d0b10'; g.fillRect(0, 0, VW, 1024);
    g.fillStyle = 'rgba(255,255,255,.06)'; g.fillRect(0, 0, VW, 8);
    g.textAlign = 'center'; g.textBaseline = 'alphabetic';
    const line = (s, y, size, col) => { fitFont(g, s, size, FA, VW * .88); g.fillStyle = col; g.fillText(s, VW / 2, y); };
    line('IF ANYONE', 190, 150, '#f4f0ea'); line('BUILDS IT,', 350, 150, '#f4f0ea');
    line('EVERYONE', 520, 160, '#e8202a'); line('DIES', 790, 290, '#e8202a');
    g.font = `22px ${FM}`; g.fillStyle = '#b8b0a8'; g.fillText('WHY SUPERHUMAN AI', VW / 2, 850); g.fillText('WOULD KILL US ALL', VW / 2, 880);
    g.font = `24px ${FM}`; g.fillStyle = '#f4f0ea'; g.fillText('ELIEZER YUDKOWSKY', VW / 2, 940); g.fillText('& NATE SOARES', VW / 2, 972);
    g.setTransform(1, 0, 0, 1, 0, 0);
    return (COVER = c);
  }
  function sticker() {
    if (STICKER) return STICKER;
    const c = makeCanvas(1024, 512), g = c.getContext('2d'); fit(g, 1024, 512, 1, 1);
    g.fillStyle = MOD.chrome(g, 10, 500, ['#fff4b0', '#ffc83a', '#b07808']); g.beginPath(); g.arc(256, 256, 244, 0, TAU); g.fill();
    g.lineWidth = 10; g.strokeStyle = '#7a4a06'; g.beginPath(); g.arc(256, 256, 214, 0, TAU); g.stroke();
    g.textAlign = 'center'; g.fillStyle = '#2a1600'; g.font = `150px ${FA}`; g.fillText('NYT', 256, 262);
    g.font = `50px ${FA}`; g.fillText('BESTSELLER', 256, 340);
    g.setTransform(1, 0, 0, 1, 0, 0);
    return (STICKER = c);
  }
  const BOOK = () => maskShape('book', 364, 547, g => { g.beginPath(); g.roundRect(32, 32, 300, 483, 8); g.fill(); });
  mline('V2', 12, (t, s, E, ui) => {
    const lt = t - s.start, W = words(s), tD = W[1].t0, tE = W[2].t0, land = t - tD, landed = land >= 0;
    const fall = landed ? 1 : easeIn(clamp((t - (tD - .2)) / .2)), hover = 1 - fall;
    const yaw = hover * (Math.sin(t * 2.2) * .55 + .15) + fall * .12, pitch = lerp(-.32 + Math.sin(t * 1.3) * .12, -Math.PI / 2, fall), roll = hover * Math.sin(t * 1.7) * .12;
    const S = BOOK(), hy = 1.9, hx = hy * S.aspect, dep = .24;
    const P = [0, lerp(3.2 + Math.sin(t * 2) * .12, dep, fall), lerp(.4, 0, fall)];
    const R = rot3(pitch, yaw, roll);
    MOD.panel(0).drawImage(cover(), 0, 0);
    const panels = [{ c: add(P, rv(R, [0, 0, dep + .012])), u: rv(R, [1.04, 0, 0]), v: rv(R, [0, 1.68, 0]), alpha: 1, gain: 1.25, glass: 0, tex: 0 }];
    if (t >= tE) {
      const k = backOut(clamp((t - tE) / .16), 2.4), sr = .46 * (1 + (1 - k) * .8);
      MOD.panel(1).drawImage(sticker(), 0, 0);
      panels.push({ c: add(P, rv(R, [.74, 1.36, dep + .03])), u: rv(R, [sr, 0, 0]), v: rv(R, [0, sr, 0]), alpha: clamp(k * 3), gain: 1.4, glass: 0, tex: 1 });
    }
    const shake = landed && land < .25 ? [Math.sin(land * 97) * .06 * (1 - land / .25), Math.cos(land * 83) * .06 * (1 - land / .25), 0] : [0, 0, 0];
    const F = {
      ro: add([Math.sin(lt * .4) * .5, lerp(4.3, 4.6, fall), lerp(7.6, 5.0, easeInOut(fall)) - lt * .1], shake), ta: add([0, lerp(2.75, .2, easeInOut(fall)), .3 * fall], shake), fov: 1.45,
      skyA: '#070a12', skyB: '#161c2c', acc: '#8aa6ff', fog: .012, floorCol: '#06080e', grid: .14,
      panels, shape: { key: 'book', src: S, p: P, rot: rotYX(yaw, pitch, roll), s: [hx, hy, dep], col: '#1a181e', rim: '#e8202a', metal: .35 },
      light: { p: [1, 7, 4], c: '#e8eeff', k: 6, vol: .5 },
    };
    if (landed) {
      if (land < .5) F.halo = { p: [0, .03, 0], n: [0, 1, 0], R: 1.4 + land * 11, r: .06 + land * .12, k: 3 * (1 - land / .5), col: '#fff0e0' };
      if (land < .1) { F.flash = .12 * (1 - land / .1); F.flashCol = '#ffffff'; }
      if (land < .6) { F.spheres = []; for (let i = 0; i < 16; i++) { const a = hash(i * 3) * TAU, v = 2.5 + hash(i * 5) * 3, r0 = 1.2 + v * land; F.spheres.push([Math.cos(a) * r0, .05 + Math.sin(Math.PI * clamp(land / .6)) * (.3 + hash(i) * .5), Math.sin(a) * r0 * .8, .07 * (1 - land / .6), '#a8b0c0']); } }
    }
    return F;
  });

  // ---------- V2.13 ""Clanker!" spat in every screed,": CLANKER! scrollers in depth (the nearer, the bigger and faster), multiplying
  // on the eighths. The date plate rolls back to SUMMER 2025 by itself. ----------
  let CL_TEX = null;
  function clankTex() {
    if (CL_TEX) return CL_TEX;
    const mk = stops => { const c = makeCanvas(1024, 512), g = c.getContext('2d'); fitFont(g, 'CLANKER!', 300, FA, 960); g.textAlign = 'center'; g.textBaseline = 'middle'; g.lineJoin = 'round';
      g.lineWidth = 22; g.strokeStyle = 'rgba(20,0,0,.9)'; g.strokeText('CLANKER!', 512, 270); g.fillStyle = MOD.chrome(g, 130, 400, stops); g.fillText('CLANKER!', 512, 270); return c; };
    return (CL_TEX = [mk(['#ffffff', '#ffc0b0', '#ff2a2a', '#6a0000']), mk(['#ffffff', '#fff0a0', '#ffc400', '#7a4a00'])]);
  }
  const CL_ROWS = [[60, 44, 90, -1, '#ff5a3a'], [150, 70, 150, 1, '#ffc43a'], [260, 52, 110, -1, '#ff8a2a'], [370, 90, 200, 1, '#ff3a3a'], [490, 46, 95, -1, '#ffd84a'],
    [590, 64, 140, 1, '#ff6a2a'], [700, 80, 170, -1, '#ffb43a'], [820, 50, 105, 1, '#ff4a4a'], [930, 60, 130, -1, '#ffa02a']];
  const CL_ORDER = [3, 1, 6, 0, 5, 8, 2, 7, 4];
  const CL_LANES = [[1.6, 4.5, -1, 5.5, 0], [-1, 1.7, 1, 4.2, 1], [3.2, 3.1, 1, 7.5, 0], [-3.2, 5.6, -1, 3.6, 1], [3.8, 2.65, -1, 8.5, 0]];   // z, y, dir, speed, tex
  mline('V2', 13, (t, s, E, ui) => {
    const lt = t - s.start, e8 = beatLen() / 2, tC = words(s)[0].t0, boost = Math.max(0, t - tC) * .7;
    // the far wall: rows of small scrollers
    const g = MOD.panel(0);
    g.fillStyle = 'rgba(10,0,0,.6)'; g.fillRect(0, 0, 2048, 1024);
    g.textBaseline = 'middle'; g.textAlign = 'left';
    CL_ORDER.forEach((ri, j) => {
      const born = j < 5 ? s.start - 1 : s.start + (j - 4) * e8; if (t < born) return;
      const [y, size, sp, dir, col] = CL_ROWS[ri]; g.font = `${size}px ${FA}`;
      const per = g.measureText('CLANKER!   ').width, dist = ((t + boost) * sp * 1.6 + ri * 97) % per, x0 = dir > 0 ? dist - per : -dist;
      g.globalAlpha = clamp((t - born) / .08) * .8; g.fillStyle = col;
      for (let x = x0; x < 2048; x += per) g.fillText('CLANKER!', x, y);
    });
    g.globalAlpha = 1;
    const [T1, T2] = clankTex();
    MOD.panel(1).drawImage(T1, 0, 0); MOD.panel(2).drawImage(T2, 0, 0);
    const panels = [{ c: [0, 3.4, -9], u: [12, 0, 0], v: [0, 6, 0], alpha: 1, gain: 1.15, glass: 0, tex: 0 }];
    CL_LANES.forEach(([z, y, dir, sp, tx], j) => {
      const born = j < 2 ? s.start - 1 : s.start + (j - 1) * e8; if (t < born) return;
      const pop = backOut(clamp((t - born) / .12), 2), span = 22, x = ((dir * (t + boost) * sp + j * 7.3) % span + span * 1.5) % span - span / 2;
      const hw = 2.3 * pop * (1 + .05 * kick8(t, 8));
      panels.push({ c: [x, y, z], u: [hw, 0, 0], v: [0, hw / 2, 0], alpha: 1, gain: 1.5, glass: 0, tex: 1 + tx });
    });
    const F = {
      ro: [Math.sin(lt * .8) * .5, 2.9, 10.5], ta: [0, 2.9, 0], fov: 1.5, roll: Math.sin(lt * 1.3) * .03,
      skyA: '#080000', skyB: '#240402', acc: '#ff5a2a', fog: .01, floorCol: '#060101',
      panels, light: { p: [0, 5, 3], c: '#ffb070', k: 5, vol: .4 },
    };
    if (t >= tC && t - tC < .08) { F.flash = .1; F.flashCol = '#ffc080'; }
    return F;
  });

  // ---------- V2.14 "Sora slop in every feed,": three phones' feeds scroll endlessly. Every 9:16 card is a badly regenerated copy of an
  // effect from earlier in the demo (smeared, colour-shifted, mosaicked), with Sora 2's watermark drifting across it. On the beats the
  // feeds speed up and the cards spill over the phones' edges into each other, until every feed is the same slop. ----------
  const CW = 180, CHh = 320, NCARD = 7;   // (the atlas: six effects and the slop they all become)
  let SLOP = null;
  function vnoise(x, y, seed) {
    const xi = Math.floor(x), yi = Math.floor(y), fx = x - xi, fy = y - yi, sx = fx * fx * (3 - 2 * fx), sy = fy * fy * (3 - 2 * fy);
    const h = (a, b) => hash2(a + seed * 131, b);
    return lerp(lerp(h(xi, yi), h(xi + 1, yi), sx), lerp(h(xi, yi + 1), h(xi + 1, yi + 1), sx), sy);
  }
  const hexRGB = h => [1, 3, 5].map(i => parseInt(h.slice(i, i + 2), 16));
  const rampRGB = (stops, k) => { k = clamp(k) * (stops.length - 1); const i = Math.min(stops.length - 2, Math.floor(k)), f = k - i, a = hexRGB(stops[i]), b = hexRGB(stops[i + 1]); return [lerp(a[0], b[0], f), lerp(a[1], b[1], f), lerp(a[2], b[2], f)]; };
  function slopAtlas() {
    if (SLOP) return SLOP;
    const c = makeCanvas(CW * NCARD, CHh), g = c.getContext('2d', { willReadFrequently: true });
    const card = (i, f) => { const id = g.createImageData(CW, CHh), D = id.data; for (let y = 0; y < CHh; y++) for (let x = 0; x < CW; x++) { const o = (y * CW + x) * 4, p = f(x, y); D[o] = p[0]; D[o + 1] = p[1]; D[o + 2] = p[2]; D[o + 3] = 255; } g.putImageData(id, i * CW, 0); };
    // the plasma
    card(0, (x, y) => { const v = Math.sin(x * .045 + 1) + Math.sin(y * .033) + Math.sin((x + y) * .028) + Math.sin(Math.hypot(x - 90, y - 170) * .05); return rampRGB(['#200018', '#ff3aa6', '#fff0f8', '#18b8ea', '#001828'], Math.sin(v * 1.6) * .5 + .5); });
    // the fire
    card(1, (x, y) => { const n = vnoise(x * .06, y * .045, 3) * .6 + vnoise(x * .15, y * .12, 5) * .4, heat = y / CHh * 1.5 - .45 + (n - .5) * .9 - Math.abs(x - 90) / 300; return rampRGB(['#000000', '#6a0000', '#ff2a00', '#ffa000', '#fff080', '#ffffff'], heat); });
    // the tunnel
    card(2, (x, y) => { const dx = x - 90, dy = y - 150, r = Math.hypot(dx, dy) + 1, a = Math.atan2(dy, dx), u = 1400 / r, v = a / TAU * 16, ch = (Math.floor(u * .12) + Math.floor(v)) & 1; const k = clamp(r / 110); return rampRGB(['#000000', ch ? '#a05a00' : '#ffc040'], k).map(q => q * (.3 + .7 * k)); });
    // the checkerboard
    card(4, (x, y) => { if (y < 120) return rampRGB(['#1a0640', '#a02a8a', '#ffb070'], y / 120); const z = 2400 / (y - 116), u = (x - 90) * z / 90, ch = (Math.floor(u * .5 + 100) + Math.floor(z * .1)) & 1; return rampRGB(['#ffb070', ch ? '#6a2ad0' : '#e0d0ff'], clamp((y - 120) / 30)); });
    // the lobster (with a claw too many) and 4o's heart, drawn
    g.fillStyle = '#0c1a2a'; g.fillRect(3 * CW, 0, CW, CHh);
    g.save(); g.translate(3 * CW + 90, 160);
    const blob = (x, y, rx, ry, a, col) => { g.fillStyle = col; g.beginPath(); g.ellipse(x, y, rx, ry, a, 0, TAU); g.fill(); };
    for (let i = 0; i < 6; i++) blob(0, 10 + i * 18, 24 - i * 2, 12, 0, i % 2 ? '#e8302a' : '#ff5a3a');
    blob(0, -30, 30, 44, 0, '#ff4a30'); blob(-6, -40, 10, 14, 0, 'rgba(255,200,180,.6)');
    for (const [x, y, a] of [[-52, -80, -.5], [54, -84, .5], [8, -110, .1]]) { blob(x, y, 20, 30, a, '#ff3a2a'); blob(x + (x < 0 ? -10 : 10), y - 26, 10, 18, a, '#ff6a4a'); }
    g.strokeStyle = '#ff8a6a'; g.lineWidth = 3; for (let i = 0; i < 7; i++) { g.beginPath(); g.moveTo(i % 2 ? 26 : -26, -20 + i * 8); g.lineTo((i % 2 ? 1 : -1) * (50 + hash(i) * 20), -10 + i * 12); g.stroke(); }
    g.beginPath(); g.moveTo(-8, -70); g.quadraticCurveTo(-40, -150, -70, -140); g.moveTo(8, -70); g.quadraticCurveTo(40, -150, 76, -150); g.stroke();
    blob(0, 124, 28, 12, 0, '#ff7a5a');
    g.restore();
    g.fillStyle = '#120008'; g.fillRect(5 * CW, 0, CW, CHh);
    { const hg = g.createLinearGradient(0, 70, 0, 250); hg.addColorStop(0, '#ff7a9a'); hg.addColorStop(.5, '#ff1f4a'); hg.addColorStop(1, '#6a0018'); g.fillStyle = hg; heartIcon(g, 5 * CW + 90, 205, 105); }
    // regenerate them badly: rows melt sideways, bands smear, a patch goes to mosaic, and the colours shift
    const all = g.getImageData(0, 0, CW * NCARD, CHh), A = all.data, AW = CW * NCARD;
    for (let i = 0; i < 6; i++) {
      const src = new Uint8ClampedArray(CW * CHh * 4);
      for (let y = 0; y < CHh; y++) for (let x = 0; x < CW; x++) { const o = (y * AW + i * CW + x) * 4, q = (y * CW + x) * 4; for (let k = 0; k < 4; k++) src[q + k] = A[o + k]; }
      const px = (x, y) => (clamp(Math.round(y), 0, CHh - 1) * CW + clamp(Math.round(x), 0, CW - 1)) * 4;
      const my0 = Math.floor(hash(i * 5) * 160), my1 = my0 + 70 + Math.floor(hash(i * 7) * 60), bs = 10 + Math.floor(hash(i * 9) * 8);
      const shift = i % 3;
      for (let y = 0; y < CHh; y++) {
        const melt = Math.sin(y * .05 + i) * 5 + (vnoise(i, y * .02, 9) - .5) * 26, smear = vnoise(i * 3, y * .04, 11) > .58;
        let acc = [0, 0, 0];
        for (let x = 0; x < CW; x++) {
          let sx = x - melt, sy = y + Math.sin(x * .07 + i * 2) * 4;
          if (y >= my0 && y < my1) { sx = Math.floor(sx / bs) * bs + bs / 2; sy = Math.floor(sy / bs) * bs + bs / 2; }
          const q = px(sx, sy); let p = [src[q], src[q + 1], src[q + 2]];
          if (smear) { acc = x ? acc.map((a, k) => a * .9 + p[k] * .1) : p; p = acc; }
          p = [p[(0 + shift) % 3], p[(1 + shift) % 3], p[(2 + shift) % 3]];
          const o = (y * AW + i * CW + x) * 4; A[o] = p[0] * .85 + 30; A[o + 1] = p[1] * .9 + 10; A[o + 2] = p[2] * .8 + 25;
        }
      }
    }
    // the slop they all become: every card at once, smeared and blocky
    for (let y = 0; y < CHh; y++) {
      let acc = [0, 0, 0];
      for (let x = 0; x < CW; x++) {
        const bx = Math.floor(x / 12) * 12 + 6, by = Math.floor(y / 12) * 12 + 6, p = [0, 0, 0];
        for (let i = 0; i < 6; i++) { const o = (clamp(by + Math.round(Math.sin(i + y * .03) * 20), 0, CHh - 1) * AW + i * CW + clamp(bx, 0, CW - 1)) * 4; p[0] += A[o] / 6; p[1] += A[o + 1] / 6; p[2] += A[o + 2] / 6; }
        acc = x ? acc.map((a, k) => a * .82 + p[k] * .18) : p;
        const o = (y * AW + 6 * CW + x) * 4; A[o] = acc[0] * 1.2 + 20; A[o + 1] = acc[1] * .95; A[o + 2] = acc[2] * 1.15 + 15; A[o + 3] = 255;
      }
    }
    g.putImageData(all, 0, 0);
    // (drawn every frame, so it's handed on as an ordinary canvas: the one above is kept on the CPU for reading back)
    const out = makeCanvas(CW * NCARD, CHh); out.getContext('2d').drawImage(c, 0, 0);
    return (SLOP = out);
  }
  function soraMark(g, x, y, s, a) {
    g.save(); g.globalAlpha = a; g.fillStyle = '#ffffff';
    for (const [dx, dy, r] of [[0, 0, .5], [.45, -.2, .42], [.85, .05, .38], [.4, .22, .4]]) { g.beginPath(); g.arc(x + dx * s, y + dy * s, r * s, 0, TAU); g.fill(); }
    g.fillStyle = '#20202a'; g.beginPath(); g.arc(x + .3 * s, y - .02 * s, .07 * s, 0, TAU); g.arc(x + .6 * s, y - .02 * s, .07 * s, 0, TAU); g.fill();
    g.fillStyle = '#ffffff'; g.font = `${s * .9}px ${FM}`; g.textBaseline = 'middle'; g.fillText('Sora', x + 1.4 * s, y + .06 * s);
    g.restore();
  }
  function heartIcon(g, x, y, s) { g.beginPath(); g.moveTo(x, y + s * .35); g.bezierCurveTo(x - s * .9, y - s * .3, x - s * .35, y - s * .9, x, y - s * .35); g.bezierCurveTo(x + s * .35, y - s * .9, x + s * .9, y - s * .3, x, y + s * .35); g.fill(); }
  // The feed's position in cards: it scrolls from the start and speeds up on every beat.
  function feedPos(s, t) {
    let pos = 0, v = 1.3, from = s.start - 2;
    for (let k = 1; k < 4; k++) { const b = B(s, k); if (t <= b) break; pos += (b - from) * v; from = b; v *= 1.85; }
    return pos + (t - from) * v;
  }
  function phone(tex, t, i, pos, spill, mushFrom) {
    const g = MOD.panel(tex); g.setTransform(PH(tex) / 512, 0, 0, PH(tex) / 512, 0, 0);
    const A = slopAtlas(), sw = 225, sh = 400, sx = 512 - sw / 2, sy = 56;
    g.fillStyle = '#0c0c10'; g.beginPath(); g.roundRect(sx - 12, sy - 22, sw + 24, sh + 44, 34); g.fill();
    g.lineWidth = 3; g.strokeStyle = '#5a5a68'; g.stroke();
    const cardOf = k => k >= mushFrom ? 6 : Math.floor(hash2(i * 13 + 5, k) * 6);
    const k0 = Math.floor(pos);
    g.save(); g.beginPath(); g.roundRect(sx, sy, sw, sh, 20); g.clip();
    for (let k = k0; k <= k0 + 1; k++) {
      const y = sy + (k - pos) * sh, ci = cardOf(k);
      g.drawImage(A, ci * CW, 0, CW, CHh, sx, y, sw, sh);
      const wx = sx + sw * (.08 + .55 * tri(t * .6 + hash(k * 3 + i) * 3)), wy = y + sh * (.12 + .7 * tri(t * .37 + hash(k * 5 + i) * 5));
      soraMark(g, wx, wy, 17, .72);
    }
    g.restore();
    // the feed's own buttons and progress
    g.fillStyle = 'rgba(255,255,255,.92)'; heartIcon(g, sx + sw - 24, sy + sh - 150, 26);
    g.beginPath(); g.ellipse(sx + sw - 24, sy + sh - 104, 13, 11, 0, 0, TAU); g.fill();
    g.beginPath(); g.moveTo(sx + sw - 36, sy + sh - 56); g.lineTo(sx + sw - 12, sy + sh - 66); g.lineTo(sx + sw - 20, sy + sh - 44); g.closePath(); g.fill();
    g.fillStyle = 'rgba(255,255,255,.3)'; g.fillRect(sx + 10, sy + sh - 14, sw - 20, 3); g.fillStyle = '#fff'; g.fillRect(sx + 10, sy + sh - 14, (sw - 20) * frac(pos), 3);
    g.fillStyle = '#000'; g.beginPath(); g.roundRect(512 - 34, sy + 8, 68, 18, 9); g.fill();
    // the spill: the cards overflow the phone, over its edges and into its neighbours
    if (spill > 0) {
      for (let k = k0; k <= k0 + 1; k++) {
        const sc = 1 + spill * (1.1 + .5 * hash(k * 7 + i)), w = sw * sc, h = sh * sc, y = sy + sh / 2 + (k - pos) * sh * sc - h / 2;
        const x = 512 - w / 2 + (hash2(k, i) - .5) * 360 * spill + Math.sin(t * 2 + k) * 30 * spill;
        g.globalAlpha = clamp(spill * 1.4) * .72; g.drawImage(A, cardOf(k) * CW, 0, CW, CHh, x, y, w, h);
        soraMark(g, x + w * (.1 + .5 * tri(t * .6 + hash(k * 3 + i) * 3)), y + h * (.15 + .6 * tri(t * .4 + k)), 17 * sc, .7 * clamp(spill * 1.4));
      }
      g.globalAlpha = 1;
      g.lineWidth = 7; g.strokeStyle = '#0c0c10'; g.beginPath(); g.roundRect(sx - 8, sy - 18, sw + 16, sh + 36, 32); g.stroke();
      g.lineWidth = 2.5; g.strokeStyle = '#7a7a8a'; g.beginPath(); g.roundRect(sx - 12, sy - 22, sw + 24, sh + 44, 34); g.stroke();
    }
    g.setTransform(1, 0, 0, 1, 0, 0);
  }
  mline('V2', 14, (t, s, E, ui) => {
    const lt = t - s.start, b1 = B(s, 1), b2 = B(s, 2), end = s.end;
    const spill = t < b1 ? 0 : easeInOut(clamp((t - b1) / (end - b1 - .15)));
    const XS = [-1.95, 0, 1.95], YAW = [.32, 0, -.32], TEX = [1, 0, 2], panels = [];
    for (let i = 0; i < 3; i++) {
      const pos = feedPos(s, t - i * .05) + i * .37, mushFrom = Math.floor(feedPos(s, b2) + i * .37) + 2;
      phone(TEX[i], t, i, pos, spill, mushFrom);
      const yw = YAW[i];
      panels.push({ c: [XS[i], 2.45, i === 1 ? .3 : 0], u: [Math.cos(yw) * 3.2, 0, -Math.sin(yw) * 3.2], v: [0, 1.6, 0], alpha: 1, gain: 1.45, glass: 0, tex: TEX[i] });
    }
    const F = {
      ro: [Math.sin(lt * .6) * .6, 2.55, 7.0 - lt * .3], ta: [0, 2.5, 0], fov: 1.5,
      skyA: '#06040e', skyB: '#1a0c26', acc: '#b86aff', fog: .01, floorCol: '#040308',
      panels, light: { p: [0, 5, 5], c: '#e8d8ff', k: 5, vol: .4 },
    };
    const b = [0, 1, 2, 3].map(k => B(s, k)).find(x => t >= x && t - x < .07); if (b !== undefined) { F.flash = .025; F.flashCol = '#f0e0ff'; }
    return F;
  });

  // ---------- V2.15 "Yann LeCun quits Meta's stage,": the ∞ again; the LECUN sphere leaves it on "quits" and flies into orbit around a
  // spinning wireframe globe ----------
  function globe(g, t) {
    fit(g, 1024, 512, 1, 1);
    const R = rot3(.35, t * .9, .2), cx = 256, cy = 256, r = 236;
    const pt = (la, lo) => { const x = Math.cos(la) * Math.cos(lo), y = Math.sin(la), z = Math.cos(la) * Math.sin(lo); const q = rv(R, [x, y, z]); return [cx + q[0] * r, cy - q[1] * r, q[2]]; };
    const segs = [];
    for (let la = -60; la <= 60; la += 30) { let q = pt(la / 57.3, 0); for (let lo = 1; lo <= 48; lo++) { const n = pt(la / 57.3, lo / 48 * TAU); segs.push([q, n]); q = n; } }
    for (let lo = 0; lo < 12; lo++) { let q = pt(-Math.PI / 2, lo / 12 * TAU); for (let la = 1; la <= 24; la++) { const n = pt(-Math.PI / 2 + la / 24 * Math.PI, lo / 12 * TAU); segs.push([q, n]); q = n; } }
    g.lineCap = 'round';
    for (const front of [false, true]) {
      g.strokeStyle = front ? '#bff4ff' : 'rgba(90,200,255,.28)'; g.lineWidth = front ? 5 : 3; g.beginPath();
      for (const [a, b] of segs) if ((a[2] + b[2] > 0) === front) { g.moveTo(a[0], a[1]); g.lineTo(b[0], b[1]); }
      g.stroke();
    }
    g.lineWidth = 4; g.strokeStyle = 'rgba(190,240,255,.6)'; g.beginPath(); g.arc(cx, cy, r, 0, TAU); g.stroke();
    g.setTransform(1, 0, 0, 1, 0, 0);
  }
  mline('V2', 15, (t, s, E, ui) => {
    const lt = t - s.start, tQ = words(s)[2].t0, fly = clamp((t - tQ) / .6), POS = [-1.9, 2.3, 0], SC = .85, lecA = 1.1;
    const G = [3.5, 2.75, -.6], GR = 1.35;
    globe(MOD.panel(1), t);
    const spheres = [];
    for (let i = 0; i < 22; i++) spheres.push([...infAt(t, i / 22 * TAU, POS, SC), .23, META_BLUE]);
    // his orbit: the halo's own plane (the shader's basis)
    const N = norm([0, 1, .38]), A = norm([0, N[2], -N[1]]), Bv = [N[1] * A[2] - N[2] * A[1], N[2] * A[0] - N[0] * A[2], N[0] * A[1] - N[1] * A[0]];   // (A = N × x̂, B = N × A)
    const OR = 1.85, oa = (t - tQ) * 3 + 2.4, orbitP = add(G, add(mul(A, Math.cos(oa) * OR), mul(Bv, Math.sin(oa) * OR)));
    let L;
    if (t < tQ) L = infAt(t, lecA, POS, SC);
    else { const p0 = infAt(tQ, lecA, POS, SC), e = easeInOut(fly); L = add(add(mul(p0, 1 - e), mul(orbitP, e)), [0, Math.sin(fly * Math.PI) * 1.4, Math.sin(fly * Math.PI) * 1.2]); }
    spheres.push([...L, .27, '#ffffff']);
    const F = {
      ro: [Math.sin(lt * .5) * .7 + .6, 2.8, 10.2 - lt * .3], ta: [.6, 2.6, 0], fov: 1.5,
      skyA: '#01020a', skyB: '#050c2a', acc: '#3a8cff', fog: .01, sky: { mode: 'stars', k: .3, col: '#9fc8ff' }, floorCol: '#01020a', floorMode: 'water', water: .03,
      spheres, sphCol: META_BLUE,
      panels: [{ c: G, u: [GR, 0, 0], v: [0, GR, 0], alpha: 1, gain: 1.3 + .6 * fly, glass: 0, tex: 1 }],
      halo: { p: G, n: N, R: OR, r: .025, k: .35 + .9 * fly, col: '#8ae0ff' },
      light: { p: [0, 6, 5], c: '#d8e8ff', k: 6, vol: .5 },
    };
    const lp = toUI(F, L); if (lp) text(ui, 'LECUN', lp[0], lp[1] - 46, { size: 34, font: FT, align: 'center', color: '#ffffff', stroke: 7 });
    return F;
  });

  // ---------- V2.16 ""Bubble!" screams the business page.": bubbles rise over a stock ticker; the big one wobbles, then pops on the
  // last beat. (The bubbles are alpha-blended sprites, soap film and all.) ----------
  const TICK1 = [['NVDA ▲ RECORD EARNINGS · NOV 19', '#4aff7a'], ['   ·   ', '#8a90a0'], ['AI STOCKS ▼', '#ff4a4a'], ['   ·   ', '#8a90a0']];
  const TICK2 = [['“ELEMENTS OF IRRATIONALITY” — SUNDAR PICHAI', '#ffc84a'], ['   ·   ', '#8a90a0'], ['“IF WE DELIVERED A GREAT QUARTER, WE ARE FUELING THE AI BUBBLE.” — JENSEN HUANG', '#ffc84a'], ['   ·   ', '#8a90a0']];
  function tickerRow(g, parts, y, size, x0, VW) {
    g.font = `${size}px ${FA}`; g.textBaseline = 'middle';
    const ws = parts.map(p => g.measureText(p[0]).width), per = ws.reduce((a, b) => a + b, 0);
    for (let x = -(x0 % per); x < VW; x += per) { let xx = x; parts.forEach((p, i) => { if (xx < VW && xx + ws[i] > 0) { g.fillStyle = p[1]; g.fillText(p[0], xx, y); } xx += ws[i]; }); }
  }
  // A soap bubble, on its own 256² canvas: clear, its thin film's colours (magenta, gold, green, blue) swirling round the rim and in
  // faint bands across the face, a white edge, a window's reflection upper left and a small second one lower right. ph turns the
  // film; the small bubbles keep four fixed turns.
  const BUB = new Map();
  function bubbleSprite(ph) {
    const key = Math.round(ph * 20) / 20;
    let c = BUB.get(key); if (c) return c;
    if (BUB.size > 24) BUB.delete(BUB.keys().next().value);
    const S = 256, cx = S / 2, cy = S / 2, R = S / 2 - 3;
    c = makeCanvas(S, S); const g = c.getContext('2d');
    const film = g.createConicGradient(key, cx, cy);
    ['#ff5ad8', '#ffd84a', '#5affa0', '#4ac8ff', '#b070ff', '#ff5ad8'].forEach((col, i) => film.addColorStop(i / 5, col));
    g.fillStyle = film; g.beginPath(); g.arc(cx, cy, R, 0, TAU); g.fill();
    // (the film shows at the rim, where it's seen edge-on; the face stays clear)
    g.globalCompositeOperation = 'destination-out';
    const clear = g.createRadialGradient(cx, cy, 0, cx, cy, R);
    clear.addColorStop(0, 'rgba(0,0,0,.97)'); clear.addColorStop(.7, 'rgba(0,0,0,.95)'); clear.addColorStop(.92, 'rgba(0,0,0,.5)'); clear.addColorStop(1, 'rgba(0,0,0,.1)');
    g.fillStyle = clear; g.fillRect(0, 0, S, S);
    g.globalCompositeOperation = 'source-over';
    // faint bands of film drifting across the face
    g.save(); g.beginPath(); g.arc(cx, cy, R, 0, TAU); g.clip(); g.lineCap = 'round';
    for (let k = 0; k < 3; k++) {
      g.strokeStyle = ['rgba(255,110,220,.1)', 'rgba(110,255,190,.08)', 'rgba(255,220,90,.09)'][k]; g.lineWidth = R * (.1 + .04 * k);
      g.beginPath();
      for (let i = 0; i <= 24; i++) { const u = i / 24, xx = cx - R + u * 2 * R, yy = cy + R * (-.35 + .35 * k) + Math.sin(u * 5 + key * 2 + k * 1.7) * R * .14; i ? g.lineTo(xx, yy) : g.moveTo(xx, yy); }
      g.stroke();
    }
    g.restore();
    g.strokeStyle = 'rgba(255,255,255,.75)'; g.lineWidth = R * .03; g.beginPath(); g.arc(cx, cy, R * .985, 0, TAU); g.stroke();
    // the window's reflection: four panes, curved round the bubble
    g.save(); g.translate(cx - R * .4, cy - R * .42); g.rotate(-.5); g.fillStyle = 'rgba(255,255,255,.88)';
    const pw = R * .15, ph2 = R * .12, gap = R * .03;
    for (const [i, j] of [[0, 0], [1, 0], [0, 1], [1, 1]]) { g.beginPath(); g.roundRect(-pw - gap / 2 + i * (pw + gap), -ph2 - gap / 2 + j * (ph2 + gap), pw, ph2, R * .03); g.fill(); }
    g.restore();
    const spot = g.createRadialGradient(cx + R * .48, cy + R * .5, 0, cx + R * .48, cy + R * .5, R * .1);
    spot.addColorStop(0, 'rgba(255,255,255,.75)'); spot.addColorStop(1, 'rgba(255,255,255,0)');
    g.fillStyle = spot; g.fillRect(0, 0, S, S);
    BUB.set(key, c);
    return c;
  }
  mline('V2', 16, (t, s, E, ui) => {
    const lt = t - s.start, tPop = B(s, 2), pop = t - tPop, TKP = { c: [0, 2.05, -.6], u: [5.2, 0, 0], v: [0, .95, 0] };
    const g = MOD.panel(0), VW = fit(g, 2048, 1024, 5.2, .95);
    g.fillStyle = 'rgba(2,6,4,.94)'; g.fillRect(0, 0, VW, 1024);
    g.fillStyle = 'rgba(120,255,160,.4)'; g.fillRect(0, 8, VW, 8); g.fillRect(0, 1008, VW, 8); g.fillRect(0, 508, VW, 6);
    tickerRow(g, TICK1, 262, 380, t * 1900, VW);
    tickerRow(g, TICK2, 770, 330, t * 1500 + 900, VW);
    g.setTransform(1, 0, 0, 1, 0, 0);
    const BC = [.2, 4.75 + Math.sin(t * 1.3) * .12 + lt * .12, .9], wob = 1 + .06 * Math.sin(t * 9) + .05 * kick(t, 6), BR = 1.05 * wob;
    const small = [];
    for (let i = 0; i < 16; i++) { const sp = .55 + hash(i) * .6; small.push([-5.6 + hash(i + 7) * 11.2 + Math.sin(t * 2 + i) * .15, 2.9 + ((t * sp + hash(i + 3) * 5.5) % 5.5), 1, .14 + hash(i + 11) * .3]); }
    // the bubbles: alpha-blended sprites on a sheet in front of the ticker
    const BP = { c: [0, 4.6, 1], u: [7.2, 0, 0], v: [0, 3.6, 0] }, gb = MOD.panel(1);
    const tx = p => [(p[0] - BP.c[0]) / 7.2 * 512 + 512, (BP.c[1] - p[1]) / 3.6 * 256 + 256];
    const bub = (p, r, k = 1, ph = 0) => {
      const [x, y] = tx(p), rr = r / 7.2 * 512;
      gb.globalAlpha = k; gb.drawImage(bubbleSprite(ph), x - rr, y - rr, rr * 2, rr * 2); gb.globalAlpha = 1;
    };
    small.forEach((b, i) => bub(b, b[3], 1, (i % 4) * 1.6));
    if (pop < 0) bub(BC, BR, 1, t * .8);
    else {
      // popped: a ring of spray racing out, falling
      const [x, y] = tx(BC), rr = BR / 7.2 * 512;
      for (let i = 0; i < 40; i++) {
        gb.fillStyle = ['#ffffff', '#ffb8ec', '#c8fff0', '#fff0a8'][i % 4];
        const a = hash(i * 3) * TAU, v = rr * (1 + (1.8 + hash(i * 5) * 2.2) * pop * 2.2), d = 4 * clamp(1 - pop / .5); if (d <= 0) break; gb.beginPath(); gb.arc(x + Math.cos(a) * v, y + Math.sin(a) * v + 900 * pop * pop, d, 0, TAU); gb.fill();
      }
    }
    const F = {
      ro: [Math.sin(lt * .5) * .6, 2.6, 10 - lt * .3], ta: [0, 3.35, 0], fov: 1.5,
      skyA: '#050214', skyB: '#1c0c2c', acc: '#ffcc55', fog: .01, floorCol: '#030208', grid: .1,
      panels: [{ ...TKP, alpha: 1, gain: 1.5, glass: .3, tex: 0 }, { ...BP, alpha: 1, gain: 1.35, glass: 0, tex: 1 }],
      light: { p: [2, 7, 5], c: '#fff0d0', k: 6, vol: .5 },
    };
    if (pop >= 0) {
      if (pop < .12) { F.flash = .16 * (1 - pop / .12); F.flashCol = '#fff4d0'; }
      if (pop < .35) F.halo = { p: BC, n: [0, 0, 1], R: BR + pop * 7, r: .05 + pop * .1, k: 3 * (1 - pop / .35), col: '#ffe8b0' };
      F.flare = clamp(1 - pop / .4); F.flarePos = MOD.project(F, BC) ?? [.5, .6]; F.flareCol = '#fff0c8';
    }
    return F;
  });
})();

;
// ---- styles/demoscene/modern/m05_v3.js ----
// modern/m05_v3.js: verse 3 in the modern engine (versions A at fx 3, and B). Jan → Aug 2026, part "UNDERGROUND": the agents' own
// scene of BBSes, cracktros and text mode, in reds and ambers with Anthropic orange. Moltbook is a BBS on a glass terminal; OpenClaw
// a lobster of spheres that sheds its shell; Mythos an orb slipping through chrome cell bars; the sandwich gets mail; Fable 5 wins
// the party's compo so hard its bar runs off the chart; Lutnick's letter is boxed in by the border; nineteen days are a tally on the
// dead big screen, which comes back on in July; a cracktro claims Hugging Face, then credits the agents' own handles; Noam Brown's
// cards flip to the Millennium problems; MYTHOS tears out of sync; Jeff Dean's sphere gets out before the border shuts; a grid folds
// over itself beside the Jacobian, with DJ Clawd; and the gwern.net G lifts away like a mask.
(() => {
  const lineOfKey = key => { const s = segByKey(key); return LINES.find(l => l.sec === s.sec && l.n === s.n); };
  const words = ln => wordsOf(ln);
  const { add, sub, mul, norm, rotYX, text } = MOD;
  const cross = (a, b) => [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]];
  const rY = (p, a) => { const c = Math.cos(a), s = Math.sin(a); return [p[0] * c + p[2] * s, p[1], -p[0] * s + p[2] * c]; };
  const rX = (p, a) => { const c = Math.cos(a), s = Math.sin(a); return [p[0], p[1] * c - p[2] * s, p[1] * s + p[2] * c]; };
  // a panel of half-size hw × hh centred at c, turned by yaw (about y) and pitch (about x)
  const sheet = (c, hw, hh, yaw = 0, pitch = 0) => ({ c, u: rY(rX([hw, 0, 0], pitch), yaw), v: rY(rX([0, hh, 0], pitch), yaw) });
  // a point on a panel, from its texture's pixel (x, y) in a W × H texture
  const onSheet = (P, x, y, W, H) => add(add(P.c, mul(P.u, x / (W / 2) - 1)), mul(P.v, 1 - y / (H / 2)));
  // at fx 3 (a 2000s shader demo: heavy bloom) bright panels are turned down so their type survives the glow
  const lo = (E, k) => E.fx < 3.5 ? k : 1;
  // the camera's right and up vectors (for billboards)
  const camAxes =(ro, ta) => { const f = norm(sub(ta, ro)), r = norm(cross(f, [0, 1, 0])); return { f, r, u: cross(r, f) }; };
  // cached 2D canvases
  const _cv = new Map();
  function cached(key, w, h, draw) { let c = _cv.get(key); if (!c) { c = makeCanvas(w, h); draw(c.getContext('2d'), w, h); _cv.set(key, c); } return c; }
  // the demo's 8×8 font: the width MOD.bitmap will draw a string at
  const bmW = (str, px) => [...String(str)].reduce((a, c) => a + (glyph(c).w + 1) * px, -px);
  // a text-mode double-line box
  function box2(g, x0, y0, x1, y1, lw, col) {
    g.fillStyle = col;
    for (const d of [0, lw * 2]) { g.fillRect(x0 + d, y0 + d, x1 - x0 - 2 * d, lw); g.fillRect(x0 + d, y1 - d - lw, x1 - x0 - 2 * d, lw); g.fillRect(x0 + d, y0 + d, lw, y1 - y0 - 2 * d); g.fillRect(x1 - d - lw, y0 + d, lw, y1 - y0 - 2 * d); }
  }
  function star5(g, x, y, R, rot = -Math.PI / 2) { g.beginPath(); for (let i = 0; i < 10; i++) { const a = rot + i * Math.PI / 5, rr = i % 2 ? R * .42 : R; g.lineTo(x + Math.cos(a) * rr, y + Math.sin(a) * rr); } g.closePath(); }
  // a ball dropped from y0 at dt = 0 that bounces on the floor (closed form)
  function bounceY(dt, y0, r, e = .42) {
    const G = 14; if (dt <= 0) return y0;
    const T = Math.sqrt(2 * Math.max(0, y0 - r) / G);
    if (dt < T) return y0 - .5 * G * dt * dt;
    dt -= T; let v = G * T * e;
    for (let k = 0; k < 6; k++) { const Tk = 2 * v / G; if (dt < Tk) return r + v * dt - .5 * G * dt * dt; dt -= Tk; v *= e; }
    return r;
  }

  // ---------- extruded shapes of this part's own (the engine's distance transform is private: the same one, here) ----------
  // A mask canvas → a signed distance field in texels (outside positive, clamped to ±48, rows bottom to top), as MOD.shapeG() gives.
  function edt1(f, n, d, v, z) {
    let k = 0; v[0] = 0; z[0] = -Infinity; z[1] = Infinity;
    for (let q = 1; q < n; q++) {
      let s = ((f[q] + q * q) - (f[v[k]] + v[k] * v[k])) / (2 * q - 2 * v[k]);
      while (s <= z[k]) { k--; s = ((f[q] + q * q) - (f[v[k]] + v[k] * v[k])) / (2 * q - 2 * v[k]); }
      k++; v[k] = q; z[k] = s; z[k + 1] = Infinity;
    }
    k = 0;
    for (let q = 0; q < n; q++) { while (z[k + 1] < q) k++; d[q] = (q - v[k]) ** 2 + f[v[k]]; }
  }
  function edt(grid, w, h) {
    const n = Math.max(w, h), f = new Float64Array(n), d = new Float64Array(n), v = new Int32Array(n), z = new Float64Array(n + 1);
    for (let x = 0; x < w; x++) { for (let y = 0; y < h; y++) f[y] = grid[y * w + x]; edt1(f, h, d, v, z); for (let y = 0; y < h; y++) grid[y * w + x] = d[y]; }
    for (let y = 0; y < h; y++) { for (let x = 0; x < w; x++) f[x] = grid[y * w + x]; edt1(f, w, d, v, z); for (let x = 0; x < w; x++) grid[y * w + x] = d[x]; }
  }
  function sdfMask(mask, w, h) {
    const src = mask.getContext('2d').getImageData(0, 0, w, h).data, INF = 1e20;
    const out = new Float64Array(w * h), inn = new Float64Array(w * h);
    for (let i = 0; i < w * h; i++) { const on = src[i * 4 + 3] > 127; out[i] = on ? 0 : INF; inn[i] = on ? INF : 0; }
    edt(out, w, h); edt(inn, w, h);
    const f = new Float32Array(w * h);
    for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) { const i = y * w + x; f[(h - 1 - y) * w + x] = clamp(Math.sqrt(out[i]) - Math.sqrt(inn[i]), -48, 48); }
    return { img: f, w, h, aspect: w / h };
  }
  const _shapes = new Map();
  function ownShape(key, w, h, draw) {
    let S = _shapes.get(key); if (S) return S;
    const m = makeCanvas(w, h), g = m.getContext('2d', { willReadFrequently: true }); g.fillStyle = '#fff'; draw(g, w, h);
    S = sdfMask(m, w, h); _shapes.set(key, S);
    return S;
  }

  // =====================================================================================================
  // V3.1 "Moltbook: no humans allowed,": the Moltbook BBS as a crisp glass terminal in the dark, in the demo's own font. It asks if
  // you're human and answers N for you; posting is for agents only, and humans are welcome to observe.
  // =====================================================================================================
  const BBS = { q: 'Are you a human?  (y/N) ', l1: 'Posting, commenting and voting: agents only.', l2: 'Humans are welcome to observe.', qx: 250, qy: 470, qp: 8 };
  const bbsStatic = () => cached('bbs', 2048, 1024, (g, w, h) => {
    g.fillStyle = 'rgba(3,4,12,.95)'; g.fillRect(0, 0, w, h);
    g.fillStyle = '#b4b4bc'; g.fillRect(0, 0, w, 64);
    MOD.bitmap(g, 'Moltbook BBS · 28 jan 2026', 40, 16, 4, '#07060f');
    // MOLTBOOK in red ANSI letters: each font pixel a block, lit on top, dark below its half
    const px = 24, lw = bmW('MOLTBOOK', px), lx = (w - lw) / 2, ly = 108;
    MOD.bitmap(g, 'MOLTBOOK', lx + 12, ly + 12, px, '#2a0402');
    const gr = g.createLinearGradient(0, ly, 0, ly + 7 * px);
    gr.addColorStop(0, '#ffc2a8'); gr.addColorStop(.2, '#ff6a48'); gr.addColorStop(.52, '#ff3a26'); gr.addColorStop(.53, '#b8180e'); gr.addColorStop(1, '#6a0806');
    MOD.bitmap(g, 'MOLTBOOK', lx, ly, px, gr);
    g.fillStyle = 'rgba(3,4,12,.55)'; for (let y = ly; y < ly + 7 * px; y += px) g.fillRect(lx, y + px - 3, lw, 3);
    MOD.bitmap(g, 'a social network for AI agents', w / 2, 330, 5, '#e08a5c', { align: 'center' });
    box2(g, 150, 405, w - 150, 830, 8, '#d02a1c');
    MOD.bitmap(g, 'users online: agents · humans: read-only', w / 2, 880, 4, '#4ab8b0', { align: 'center' });
    g.fillStyle = 'rgba(0,0,0,.25)'; for (let y = 0; y < h; y += 4) g.fillRect(0, y, w, 1.5);
  });
  mline('V3', 1, (t, s, E, ui) => {
    const lt = t - s.start, tNo = wordT(s, 1), tHum = wordT(s, 2);
    const g = MOD.panel(0), st = bbsStatic();
    // the screen prints top-down: the logo is up on the beat, the rest follows
    const ph = Math.round(lerp(.36, 1, easeOut(clamp(lt / .28))) * 1024);
    g.drawImage(st, 0, 0, 2048, ph, 0, 0, 2048, ph);
    if (ph < 1024) { g.fillStyle = 'rgba(255,240,230,.9)'; g.fillRect(0, ph - 5, 2048, 5); }
    const { q, qx, qy, qp } = BBS, nq = Math.floor(clamp((lt - .1) * 64, 0, q.length)), qw = bmW(q, qp) + qp;
    if (ph > qy + 64 && nq > 0) MOD.bitmap(g, q.slice(0, nq), qx, qy, qp, '#ffffff');
    if (t >= tNo) {
      const pop = Math.exp(-(t - tNo) * 12);
      if (pop > .05) { g.fillStyle = `rgba(255,255,120,${.5 * pop})`; g.fillRect(qx + qw - 14, qy - 14, 7 * qp + 28, 7 * qp + 28); }
      MOD.bitmap(g, 'N', qx + qw, qy - Math.round(pop * 10), qp, '#ffff55');
    } else if (nq >= q.length && Math.floor(t * 6) % 2 === 0) { g.fillStyle = '#ffffff'; g.fillRect(qx + qw, qy + 7 * qp, 6 * qp, qp); }
    if (t >= tNo + .1) MOD.bitmap(g, BBS.l1.slice(0, Math.floor((t - tNo - .1) * 110)), qx, 590, 5, '#b0b0b8');
    if (t >= tHum) MOD.bitmap(g, BBS.l2.slice(0, Math.floor((t - tHum) * 90)), qx, 680, 7, '#ffe6a0');
    // the camera leans in to the question once it's answered
    const push = easeInOut(clamp((t - tNo + .05) / .7)), sway = Math.sin(t * .6) * .25;
    const P = sheet([0, 2.85, 0], 4.1, 2.05, -.07);
    return {
      fx: E.fx, res: E.res,
      ro: [lerp(1.1, .7, push) + sway, lerp(2.75, 2.45, push), lerp(8.9, 7.5, push)], ta: [lerp(.1, .15, push), lerp(2.8, 2.55, push), 0], fov: 1.5,
      skyA: '#010208', skyB: '#06081a', acc: '#ff3a2a', fog: .03, floorCol: '#020207', grid: .1,
      panels: [{ ...P, alpha: 1, gain: 1.45 * lo(E, .8), glass: .8, tex: 0 }],
      light: { p: [0, 5, 4], c: '#ff7a5a', k: 3, vol: .3 },
    };
  });

  // =====================================================================================================
  // V3.2 "OpenClaw — the lobster's proud,": a red lobster of spheres under turning glory rays. In the first half-second it sheds its
  // old orange shell as the name flips CLAWDBOT → MOLTBOT → OPENCLAW; then the claws go up, proudly, snapping on the beat.
  // =====================================================================================================
  const LOB = { c: [0, 2.62, 0], k: .56, red: '#ff3a22' };
  // the lobster, seen from above with its head up: carapace, head, eyes, tail and fan, and two big claws (raised by `raise`,
  // their fingers opened by `open`): 29 spheres. The shell it sheds covers the carapace, the first three.
  function lobster(raise, open) {
    const L = [];
    L.push([0, 1.0, 0, .56], [0, .42, .03, .6], [0, -.12, 0, .54], [0, 1.55, .08, .34]);
    L.push([0, -.66, 0, .5], [0, -1.12, 0, .45], [0, -1.55, 0, .4], [0, -1.95, 0, .34]);
    L.push([-.44, -2.42, 0, .28], [0, -2.5, 0, .3], [.44, -2.42, 0, .28]);
    for (const sx of [-1, 1]) {
      const hx = sx * lerp(1.45, 1.75, raise), hy = lerp(2.35, 2.75, raise), ax = sx * lerp(1.45, 1.62, raise), ay = lerp(2.9, 3.4, raise);
      L.push([sx * .62, 1.25, 0, .22], [sx * lerp(1.05, 1.2, raise), lerp(1.72, 1.95, raise), 0, .26]);
      L.push([hx, hy, 0, .5], [ax, ay, .02, .43]);
      // the fingers: the outer one fixed, the inner one opening; each a prong of two
      L.push([ax + sx * .2, ay + .5, 0, .22], [ax + sx * .24, ay + .92, 0, .16]);
      L.push([ax - sx * (.1 + open * .2), ay + .48, 0, .2], [ax - sx * (.08 + open * .5), ay + .88 - open * .06, 0, .15]);
    }
    return L.map(p => [...p, LOB.red]).concat([[-.2, 1.84, .28, .1, '#1a0604'], [.2, 1.84, .28, .1, '#1a0604']]);
  }
  // legs and antennae, in 2D on a sheet in the lobster's plane (tex 1): local x −7.5…7.5, y −3…4.5
  function lobsterLines(t) {
    const g = MOD.panel(1), X = x => 512 + x / 7.5 * 512, Y = y => 256 - (y - .75) / 3.75 * 256;
    g.lineCap = 'round'; g.lineJoin = 'round';
    for (const sx of [-1, 1]) {
      // antennae: long, sweeping out and back, swaying
      const w = Math.sin(t * 3 + sx) * .18;
      g.strokeStyle = '#e02a18'; g.lineWidth = 12;
      g.beginPath(); g.moveTo(X(sx * .16), Y(1.8)); g.bezierCurveTo(X(sx * .5), Y(2.9 + w), X(sx * .5), Y(3.6), X(sx * (.4 + w)), Y(2.9 + w)); g.stroke();
      g.lineWidth = 9; g.beginPath(); g.moveTo(X(sx * .2), Y(1.85)); g.bezierCurveTo(X(sx * .9), Y(2.2), X(sx * 2.6), Y(1.6 + w), X(sx * (3.6 + w)), Y(.2 + w)); g.stroke();
      g.lineWidth = 6; g.beginPath(); g.moveTo(X(sx * (3.6 + w)), Y(.2 + w)); g.quadraticCurveTo(X(sx * 4.2), Y(-.6), X(sx * (4.1 + w * .5)), Y(-1.9)); g.stroke();
      // four walking legs a side
      g.strokeStyle = '#c82214'; g.lineWidth = 13;
      for (let i = 0; i < 4; i++) {
        const y = .9 - i * .36, kk = Math.sin(t * 7 + i * 1.3 + sx) * .06;
        g.beginPath(); g.moveTo(X(sx * .45), Y(y)); g.lineTo(X(sx * (1.15 + i * .05)), Y(y + .14 + kk)); g.lineTo(X(sx * (1.5 + i * .1)), Y(y - .42 + kk)); g.stroke();
      }
    }
  }
  const NAMES = ['CLAWDBOT', 'MOLTBOT', 'OPENCLAW'];
  mline('V3', 2, (t, s, E, ui) => {
    const lt = t - s.start, tLob = wordT(s, 3);
    const raise = easeOut(clamp((t - tLob + .1) / .3)), open = raise < 1 ? .5 + .5 * Math.sin(t * 13) : .55 + .45 * Math.cos(frac(bt(t)) * Math.PI * 2);
    const yaw = Math.sin(t * .9) * .5, pitch = -.08 + Math.sin(t * 1.3) * .05, bob = kick(t, 6) * .06;
    const toW = p => { const q = rY(rX([p[0], p[1], p[2]], pitch), yaw); return [LOB.c[0] + q[0] * LOB.k, LOB.c[1] + q[1] * LOB.k + bob, LOB.c[2] + q[2] * LOB.k, p[3] * LOB.k, p[4]]; };
    const body = lobster(raise, open), spheres = body.map(toW);
    // the old shell (Clawdbot's orange), split and flung off as it molts
    const m = easeIn(clamp(lt / .45));
    if (m < 1) body.slice(0, 3).forEach((p, j) => {
      const side = j % 2 ? 1 : -1, d = [side * (1.4 + .35 * j), .6 + .25 * j, 1.6];
      spheres.push(toW([p[0] + d[0] * m * 3.2, p[1] + d[1] * m * 3.2, p[2] + d[2] * m * 3.2, p[3] * 1.14 * (1 - m * .7), '#e0823e']));
    });
    lobsterLines(t);
    const P = sheet(toW([0, .75, -.05]).slice(0, 3), 7.5 * LOB.k, 3.75 * LOB.k, yaw, pitch);
    // the names it shed
    const ni = lt < .22 ? 0 : lt < .45 ? 1 : 2;
    NAMES.slice(0, ni).forEach((nm, i) => {
      text(ui, nm, 72, 92 + i * 44, { size: 30, font: MOD.FONT_T, color: 'rgba(200,190,200,.62)', stroke: 5 });
      ui.save(); ui.font = `30px ${MOD.FONT_T}`; const w = ui.measureText(nm).width; ui.restore();
      ui.fillStyle = 'rgba(255,90,60,.95)'; ui.fillRect(64, 80 + i * 44, w + 16, 5);
    });
    const cy = 92 + ni * 44 + 50, pop = Math.exp(-Math.max(0, lt - [0, .22, .45][ni]) * 10);
    ui.save(); ui.font = `${Math.round(74 + 14 * pop)}px ${MOD.FONT_T}`; ui.lineJoin = 'round'; ui.lineWidth = 10; ui.strokeStyle = 'rgba(10,2,2,.85)';
    ui.strokeText(NAMES[ni], 70, cy);
    ui.fillStyle = ni === 2 ? MOD.chrome(ui, cy - 70, cy, ['#ffffff', '#ffb0a0', '#ff3a26', '#7a0a06']) : ni === 0 ? MOD.chrome(ui, cy - 70, cy, ['#fff0e0', '#ffb070', '#d97757', '#6a2a10']) : '#c8c8d8';
    ui.fillText(NAMES[ni], 70, cy); ui.restore();
    const ro = [Math.sin(lt * .45) * .9, 2.2, 8.4 - lt * .35];
    return {
      fx: E.fx, res: E.res, ro, ta: [0, 2.7, 0], fov: 1.45,
      skyA: E.fx < 3.5 ? '#3a1804' : '#5a2006', skyB: E.fx < 3.5 ? '#8a4a10' : '#c8701a', acc: E.fx < 3.5 ? '#ffd24a' : '#ff9434', fog: .006, floorCol: '#060302',
      sky: { mode: 'rays', k: .3 + raise * .5, col: E.fx < 3.5 ? '#fff0b0' : '#ffa048' },
      spheres, sphCol: LOB.red,
      panels: [{ ...P, alpha: 1, gain: 1.1, glass: 0, tex: 1 }],
      light: { p: [0, 6.5, -6], c: '#fff0c0', k: 5 + 3 * kick(t, 5), vol: .7 },
      flash: ni === 2 ? clamp(1 - (lt - .45) / .12) * .22 : 0, flashCol: '#ffd0a0',
    };
  });

  // =====================================================================================================
  // V3.3 "Mythos Preview slips its jail,": chrome cell bars sweep in over a glowing orange orb; on "slips" the two bars in front of
  // it bend apart, and it slips through and out of the frame, trailing copies. At fx 4 its light pours through the bars.
  // =====================================================================================================
  const BARS = { w: 768, h: 512, pad: 40, n: 10, x0: 60, dx: 72, th: 24, bend: 50, steps: 8 };
  const barsShape = st => ownShape('bars' + st, BARS.w, BARS.h, (g, w, h) => {
    const { pad, n, x0, dx, th } = BARS, k = st / BARS.steps, yc = h / 2;
    g.fillRect(pad, pad, w - 2 * pad, 26); g.fillRect(pad, h - pad - 26, w - 2 * pad, 26);
    for (let i = 0; i < n; i++) {
      const bx = x0 + i * dx, side = i === 4 ? -1 : i === 5 ? 1 : 0;
      for (let y = pad; y < h - pad; y++) { const off = side * k * BARS.bend * Math.exp(-(((y - yc) / 95) ** 2)); g.fillRect(bx + off - th / 2, y, th, 1); }
    }
  });
  const orbTex = () => cached('orb', 1024, 512, (g) => {
    const gr = g.createRadialGradient(512, 256, 0, 512, 256, 250);
    gr.addColorStop(0, 'rgba(255,255,240,1)'); gr.addColorStop(.18, 'rgba(255,230,170,1)'); gr.addColorStop(.42, 'rgba(255,150,60,.95)'); gr.addColorStop(.62, 'rgba(230,90,30,.55)'); gr.addColorStop(1, 'rgba(200,60,20,0)');
    g.fillStyle = gr; g.fillRect(0, 0, 1024, 512);
  });
  mline('V3', 3, (t, s, E, ui) => {
    const lt = t - s.start, tSlip = wordT(s, 2) - .05;
    const bend = easeOut(clamp((t - tSlip) / .2)), st = Math.round(bend * BARS.steps);
    const S = barsShape(st), hy = 2.15, hx = hy * S.aspect;
    const sweep = -(1 - easeOut(clamp(.45 + lt / .3))) * 9;
    const ro = [Math.sin(lt * .5) * .5 - .2, 2.2, 7.6 - lt * .3], ta = [0, 2.45, 0], A = camAxes(ro, ta);
    // the orb: behind the bars, breathing on the kick; then through the gap and away to the right
    const orbAt = tt => {
      const e = clamp((tt - tSlip - .06) / (s.end - tSlip - .06));
      const a = easeInOut(clamp(e / .35)), b = easeIn(clamp((e - .25) / .75));
      return [lerp(0, 7.5, b) + Math.sin(tt * 2.3) * .06 * (1 - a), 2.45 + b * .7 + Math.sin(tt * 3.1) * .05 * (1 - a), lerp(-1.25, 1.1, a) + b * 2.4];
    };
    const o = orbAt(t), R = .62 + .08 * kick(t, 6);
    MOD.panel(1).drawImage(orbTex(), 0, 0);
    const bb = (p, r, alpha) => ({ c: p, u: mul(A.r, r * 2), v: mul(A.u, r), alpha, gain: 3.2 * lo(E, .6), glass: 0, tex: 1 });
    const panels = [bb(o, R, 1)];
    if (t > tSlip) for (let j = 1; j <= 4; j++) panels.push(bb(orbAt(t - j * .045), R * (1 - j * .1), .5 - j * .1));
    return {
      fx: E.fx, res: E.res, ro, ta, fov: 1.45,
      skyA: '#02040a', skyB: '#0a1222', acc: '#6a8ad0', fog: .02, floorCol: '#030409',
      shape: { key: 'bars' + st, src: S, p: [sweep, 2.45, 0], rot: rotYX(Math.sin(t * .5) * .05), s: [hx, hy, .09], col: '#1c2028', rim: '#9fc0ff', metal: 1 },
      panels,
      light: { p: o, c: '#ff9a40', k: 9 + 3 * kick(t, 6), vol: 1.3 },
    };
  });

  // =====================================================================================================
  // V3.4 "Sandwich in the park: new mail!": a sandwich of bobbing copper bars over a green park; an envelope with an orange seal
  // spins in and lands, and the mail program chimes NEW MAIL (1).
  // =====================================================================================================
  function sandwich(g, t, jump) {
    const cx = 1024, base = 900;
    const slab = (i, yc, hw, h, stops, top, bot) => {
      const y = yc + Math.sin(t * 6.5 - i * .75) * 10 * (1 + kick(t, 5)) - jump * (1 + i * .35);
      g.save(); g.beginPath();
      const n = 48;
      for (let j = 0; j <= n; j++) { const u = j / n * 2 - 1; g.lineTo(cx + u * hw, y - h / 2 + (top ? top(u) : 0)); }
      for (let j = n; j >= 0; j--) { const u = j / n * 2 - 1; g.lineTo(cx + u * hw, y + h / 2 + (bot ? bot(u) : 0)); }
      g.closePath(); g.clip();
      g.fillStyle = MOD.chrome(g, y - h / 2 - 40, y + h / 2 + 10, stops); g.fillRect(cx - hw - 10, y - h / 2 - 80, hw * 2 + 20, h + 120);
      g.restore();
      return y;
    };
    const BREAD = ['#fff0c8', '#f2b860', '#b86a1e', '#5a2c08'];
    slab(0, base - 50, 720, 90, BREAD, null, u => -Math.max(0, Math.abs(u) - .9) * 200);
    slab(1, base - 112, 760, 40, ['#fffbd0', '#ffe04a', '#e0a010', '#7a5004'], null, u => { const m = ((u * 9 % 1) + 1) % 1; return Math.abs(u) < .9 && m < .3 ? Math.sin(m / .3 * Math.PI) * 38 : 0; });
    slab(2, base - 160, 690, 48, ['#ffd0c0', '#ff5a3c', '#c01a10', '#5a0604'], u => -Math.max(0, Math.abs(u) - .95) * 300, u => Math.max(0, Math.abs(u) - .95) * -300);
    slab(3, base - 206, 780, 46, ['#e8ffc0', '#8ee04a', '#2a9a2a', '#0a3a0a'], u => Math.sin(u * 40) * 10, u => Math.sin(u * 31 + 1) * 14);
    const yTop = slab(4, base - 350, 730, 240, BREAD, u => (1 - Math.sqrt(Math.max(0, 1 - u * u))) * 150, u => -Math.max(0, Math.abs(u) - .92) * 200);
    g.fillStyle = 'rgba(255,248,220,.9)';
    for (let i = 0; i < 16; i++) { const u = hash(i + 3) * 1.5 - .75, v = hash(i + 40); const x = cx + u * 720, y = yTop - 100 + (1 - Math.sqrt(1 - u * u)) * 150 + v * 60; g.beginPath(); g.ellipse(x, y, 14, 7, u * .8, 0, TAU); g.fill(); }
  }
  const envelopeTex = () => cached('env', 1024, 512, (g) => {
    g.fillStyle = '#f4ead4'; g.beginPath(); g.roundRect(70, 36, 884, 440, 22); g.fill();
    g.fillStyle = '#d8c8a8'; g.beginPath(); g.moveTo(80, 50); g.lineTo(512, 300); g.lineTo(944, 50); g.closePath(); g.fill();
    g.strokeStyle = '#a89878'; g.lineWidth = 6; g.beginPath(); g.moveTo(80, 466); g.lineTo(420, 250); g.moveTo(944, 466); g.lineTo(604, 250); g.stroke();
    g.beginPath(); g.moveTo(80, 50); g.lineTo(512, 300); g.lineTo(944, 50); g.stroke();
    const gr = g.createRadialGradient(500, 290, 6, 512, 300, 62); gr.addColorStop(0, '#ffc49a'); gr.addColorStop(.6, '#d97757'); gr.addColorStop(1, '#8a3a18');
    g.fillStyle = gr; g.beginPath(); g.arc(512, 300, 60, 0, TAU); g.fill();
  });
  function mailBox(g, t, age) {
    g.fillStyle = 'rgba(0,0,150,.95)'; g.fillRect(0, 0, 1024, 512);
    box2(g, 20, 20, 1004, 492, 8, '#ffffff');
    g.fillStyle = 'rgba(0,0,150,1)'; g.fillRect(380, 14, 264, 44);
    MOD.bitmap(g, 'MAIL', 512, 20, 5, '#ffffff', { align: 'center' });
    const on = frac(age * 3.2) < .62 || age < .3;
    MOD.bitmap(g, on ? '▶ NEW MAIL (1)' : '  NEW MAIL (1)', 512, 190, 10, on ? '#ffff55' : '#8a8aff', { align: 'center' });
    MOD.bitmap(g, 'from: the model', 512, 350, 5, '#c0c0ff', { align: 'center' });
  }
  mline('V3', 4, (t, s, E, ui) => {
    const lt = t - s.start, tPark = wordT(s, 3), tNew = wordT(s, 4);
    const jump = t >= tNew ? Math.exp(-(t - tNew) * 7) * Math.abs(Math.sin((t - tNew) * 16)) * 70 : 0;
    sandwich(MOD.panel(0), t, jump);
    const SW = sheet([-1.25, 1.95, .5], 3.3, 1.65, .12);
    const panels = [{ ...SW, alpha: 1, gain: 1.25 * lo(E, .7), glass: 0, tex: 0 }], spheres = [];
    // the envelope: spins in from the right on "park" and lands on "new"
    const k = easeOut(clamp((t - tPark) / (tNew - tPark)));
    if (t >= tPark - .02) {
      MOD.panel(2).drawImage(envelopeTex(), 0, 0);
      const yaw = (1 - k) * 7.5 + Math.sin(t * 2.2) * .12, pitch = (1 - k) * -.9 + Math.sin(t * 1.7) * .08;
      const c = [lerp(8, 1.75, k), lerp(5.2, 3.15, k) - kick(t, 8) * .05, lerp(1.5, .5, k)];
      const EV = sheet(c, 1.25, .625, yaw, pitch);
      panels.push({ ...EV, alpha: 1, gain: 1.2 * lo(E, .55), glass: 0, tex: 2 });
      const nrm = norm(cross(EV.u, EV.v));
      if (nrm[2] > .25) spheres.push([...onSheet(EV, 512, 300, 1024, 512).map((v, i) => v + nrm[i] * .06), .15, '#d97757']);
    }
    // the mail program chimes
    if (t >= tNew) {
      const age = t - tNew, sc = backOut(clamp(age / .16));
      mailBox(MOD.panel(1), t, age);
      panels.push({ ...sheet([2.35, 1.5, .9], 1.3 * sc, .65 * sc, -.2), alpha: 1, gain: 1.5 * lo(E, .75), glass: .6, tex: 1 });
    }
    const ro = [Math.sin(lt * .5) * .6 + .3, 2.0, 8.2 - lt * .3];
    return {
      fx: E.fx, res: E.res, ro, ta: [.2, 2.25, 0], fov: 1.45,
      skyA: '#021a06', skyB: '#0c3a10', acc: E.fx < 3.5 ? '#2a7a1a' : '#6ade3a', fog: .025, sky: { mode: 'plasma', k: .7, col: E.fx < 3.5 ? '#6a9a2a' : '#d0ff6a' },
      floorMode: 'checker', floorCol: '#08300c', floorCol2: '#0e4814', floorTile: 1.1,
      panels, spheres, flash: t >= tNew ? clamp(1 - (t - tNew) / .1) * .2 : 0, flashCol: '#ffffa0',
      light: { p: [2, 6, 4], c: '#fff0c0', k: 5, vol: .3 },
    };
  });

  // =====================================================================================================
  // V3.5 "Fable 5 — who's not a fan?" and V3.8 "Come July, it's back again.": the demoparty's big screen shows the compo results.
  // The table slides in, FABLE 5's bar races out, runs off the end of the chart and keeps going; the other rows stay blank. ★ ratings
  // fall as confetti spheres. The same screen is dead for nineteen days (V3.7) and comes back on in July, FABLE 5 back on top.
  // =====================================================================================================
  const SCR = { c: [0, 3.05, -2], u: [4.4, 0, 0], v: [0, 2.2, 0] };
  const CH = { x0: 690, x1: 1990, y: 300, h: 70 };   // the vote bars' track, in the screen's texture
  function compoScreen(g, o) {
    g.fillStyle = 'rgba(6,4,14,.94)'; g.fillRect(0, 0, 2048, 1024);
    g.fillStyle = 'rgba(255,140,60,.05)'; for (let y = 0; y < 1024; y += 6) g.fillRect(0, y, 2048, 2);
    const slide = x => x + (1 - easeOut(clamp(o.slide))) * 2200;
    text(g, o.head, slide(60), 120, { size: 78, font: MOD.FONT_T, color: '#ffffff' });
    if (o.banner) {
      const bw = 1928; g.fillStyle = 'rgba(40,210,110,.92)'; g.fillRect(slide(60), 146, bw, 84);
      text(g, o.banner, slide(60) + bw / 2, 206, { size: 60, font: MOD.FONT_T, align: 'center', color: '#02140a' });
    } else { g.fillStyle = 'rgba(255,160,80,.55)'; g.fillRect(slide(60), 158, 1928, 5); }
    // row 1: FABLE 5
    const rowIn = k => easeOut(clamp(o.slide * 1.5 - k * .1));
    const x = slide(60) + (1 - rowIn(1)) * 400;
    text(g, '1.', x, CH.y + 28, { size: 64, font: MOD.FONT_T, color: '#ffd27a' });
    g.save(); g.globalAlpha = .3 + .7 * o.name;
    g.font = `76px ${MOD.FONT_T}`; g.fillStyle = MOD.chrome(g, CH.y - 40, CH.y + 36, ['#ffffff', '#ffd0a0', '#ff8a3a', '#8a3a10']); g.fillText('FABLE 5', x + 110, CH.y + 32);
    g.restore();
    // the track and its bar
    g.strokeStyle = 'rgba(255,190,140,.35)'; g.lineWidth = 3; g.strokeRect(CH.x0, CH.y - CH.h / 2, CH.x1 - CH.x0, CH.h);
    if (o.bar > 0) {
      const bx1 = CH.x0 + (CH.x1 - CH.x0) * Math.min(1, o.bar);
      const gr = g.createLinearGradient(0, CH.y - CH.h / 2, 0, CH.y + CH.h / 2); gr.addColorStop(0, '#fff2d8'); gr.addColorStop(.3, '#ffa44a'); gr.addColorStop(1, '#b8480e');
      g.fillStyle = gr; g.fillRect(CH.x0, CH.y - CH.h / 2, bx1 - CH.x0 + (o.bar >= 1 ? 60 : 0), CH.h);
      if (o.bar < 1) { g.fillStyle = '#ffffff'; g.fillRect(bx1 - 10, CH.y - CH.h / 2, 10, CH.h); }
    }
    for (let i = 0; i < 5; i++) { g.fillStyle = o.stars > i ? '#ffd24a' : 'rgba(255,210,74,.18)'; star5(g, 1660 + i * 70, CH.y + 96, 30); g.fill(); }
    // rows 2–5: nobody
    for (let i = 2; i <= 5; i++) {
      const y = 420 + (i - 2) * 132, xx = slide(60) + (1 - rowIn(i)) * 400;
      text(g, i + '.', xx, y + 56, { size: 56, font: MOD.FONT_T, color: 'rgba(255,210,160,.4)' });
      g.fillStyle = 'rgba(255,200,160,.18)'; for (let d = 0; d < 9; d++) g.fillRect(xx + 110 + d * 48, y + 44, 22, 8);
      g.strokeStyle = 'rgba(255,190,140,.16)'; g.lineWidth = 3; g.strokeRect(CH.x0, y + 10, CH.x1 - CH.x0, 56);
    }
  }
  // the bar that ran off the chart: tex 2, a slab of its gradient, stretched along its run
  function barTex() {
    const g = MOD.panel(2), gr = g.createLinearGradient(0, 0, 0, 512);
    gr.addColorStop(0, '#fff2d8'); gr.addColorStop(.3, '#ffa44a'); gr.addColorStop(1, '#b8480e');
    g.fillStyle = gr; g.fillRect(0, 0, 1024, 512); g.fillStyle = '#ffffff'; g.fillRect(1000, 0, 24, 512);
  }
  const chartEnd = onSheet(SCR, CH.x1, CH.y, 2048, 1024), barHH = CH.h / 2 / 512 * SCR.v[1];
  function overflow(t, tEnd, speed, k) {
    if (t < tEnd) return null;
    const d = t - tEnd, run = d * speed + d * d * speed * 2.2, x0 = chartEnd[0] - .1;
    return { c: [x0 + run / 2, chartEnd[1], chartEnd[2] + .04], u: [run / 2 + .001, 0, 0], v: [0, barHH, 0], alpha: 1, gain: 2.4 * k, glass: 0, tex: 2 };
  }
  function confetti(t, t0, n = 30) {
    const out = [], COL = ['#ffd24a', '#ffb02a', '#fff2c8', '#ff8a3a'];
    for (let i = 0; i < n; i++) {
      const d = t - t0 - hash(i + 100) * .55; if (d < 0) continue;
      const r = .06 + .07 * hash(i + 200), x = lerp(-5.5, 6.5, hash(i + 1)) + Math.sin(d * 3 + i) * .25, z = lerp(-1.4, 3, hash(i + 50));
      out.push([x, bounceY(d, 5.4 + hash(i + 150) * 1.4, r), z, r, COL[i % 4]]);
    }
    return out;
  }
  mline('V3', 5, (t, s, E, ui) => {
    const lt = t - s.start, tFable = wordT(s, 0), tWho = wordT(s, 3), tFan = wordT(s, 6);
    const bar = t < tFable ? 0 : easeIn(clamp((t - tFable) / (tWho - tFable)));
    compoScreen(MOD.panel(0), { head: 'COMPO RESULTS · JUN 9 2026', slide: .35 + lt / .3, name: easeOut(clamp((t - tFable + .05) / .15)), bar, stars: t < tWho ? 0 : Math.floor((t - tWho) / .07) + 1 });
    barTex();
    const panels = [{ ...SCR, alpha: 1, gain: 1.35 * lo(E, .62), glass: 1, tex: 0 }], ov = overflow(t, tWho, 7, lo(E, .6));
    if (ov) panels.push(ov);
    const pan = easeInOut(clamp((t - tWho) / 1.1)) * .55;
    return {
      fx: E.fx, res: E.res,
      ro: [-2.6 + lt * .35 + pan * 1.2, 1.55, 7.4 - lt * .2], ta: [.2 + pan * 1.5, 3.05, -2], fov: 1.4,
      skyA: '#060210', skyB: '#12061e', acc: '#c8602a', fog: .022, floorCol: '#050308', grid: .18,
      panels, spheres: confetti(t, tWho - .3), sphCol: '#ffd24a',
      light: { p: [-1, 6, 2], c: '#ffc080', k: 5 + 2 * kick(t, 5) + (t >= tFan ? 3 * Math.exp(-(t - tFan) * 6) : 0), vol: .6 },
    };
  });

  // =====================================================================================================
  // V3.6 "Lutnick's letter: export ban!": the letter types in a DOS word processor's blue, on a glass terminal; from "export" the
  // screen's red raster border slams in six steps and boxes it down to nothing.
  // =====================================================================================================
  const LETTER = [
    ['UNITED STATES DEPARTMENT OF COMMERCE', 1024, 70, 6, '#ffffff', 'center'],
    ['The Secretary of Commerce', 1024, 150, 4, '#a8a8a8', 'center'],
    ['June 12, 2026 · 5:21 P.M. ET', 1900, 250, 5, '#ffffff', 'right'],
    ['RE: Claude Fable 5 and Claude Mythos 5 · export controls', 130, 350, 5, '#ffff55', 'left'],
    [0, 130, 450], [1, 130, 510], [2, 130, 570],
    ['Howard Lutnick', 130, 690, 6, '#ffffff', 'left'],
    ['Secretary of Commerce', 130, 770, 4, '#a8a8a8', 'left'],
  ];
  // the body, too fast to read: grey bars of words (never invented words)
  const bodyRow = r => { const out = []; let x = 0; while (x < 1700 - (r === 2 ? 600 : 0)) { const w = 40 + Math.floor(hash2(r, x) * 150); out.push([x, w]); x += w + 26; } return out; };
  mline('V3', 6, (t, s, E, ui) => {
    const lt = t - s.start, g = MOD.panel(0);
    g.fillStyle = 'rgba(0,0,168,.96)'; g.fillRect(0, 0, 2048, 1024);
    g.fillStyle = '#a8a8a8'; g.fillRect(0, 960, 2048, 64); MOD.bitmap(g, 'Doc 1  Pg 1', 40, 976, 4, '#000080');
    let chars = Math.floor(Math.max(0, lt + .08) * 640);
    for (const [str, x, y, px, col, al] of LETTER) {
      if (chars <= 0) break;
      if (typeof str === 'number') {
        const bars = bodyRow(str);
        for (const [bx, w] of bars) { if (chars <= 0) break; g.fillStyle = '#8a8aa8'; g.fillRect(x + bx, y, w, 26); chars -= Math.ceil(w / 28); }
        continue;
      }
      const n = Math.min(str.length, chars); chars -= str.length;
      const w = bmW(str, px), x0 = al === 'center' ? x - w / 2 : al === 'right' ? x - w : x;
      MOD.bitmap(g, str.slice(0, n), x0, y, px, col);
    }
    if (Math.floor(t * 8) % 2 === 0) { g.fillStyle = '#ffffff'; g.fillRect(130, 850, 36, 8); }
    // the border closes in six slams, from "export" to the cut
    const t0 = wordT(s, 2) - .1, step = (s.end - .02 - t0) / 6, n = t >= t0 ? Math.min(6, Math.floor((t - t0) / step) + 1) : 0;
    let shake = [0, 0, 0];
    if (n > 0) {
      const k = n / 6, age = (t - t0) - (n - 1) * step, bx = k * 1000, by = k * 560, jolt = clamp(1 - age / .07);
      shake = [(hash(n) - .5) * .12 * jolt, (hash(n + 9) - .5) * .12 * jolt, 0];
      for (let y = 0; y < 1080; y += 6) {
        const v = .3 + .7 * Math.max(0, Math.sin(y * .026 - t * 11)) ** 4;
        ui.fillStyle = `rgb(${Math.round(90 + 165 * v)} ${Math.round(8 + 60 * v * v)} ${Math.round(10 + 40 * v * v)})`;
        if (k >= 1 || y < by || y >= 1080 - by) ui.fillRect(0, y, 1920, 6); else { ui.fillRect(0, y, bx, 6); ui.fillRect(1920 - bx, y, bx, 6); }
      }
      if (k < 1) { ui.fillStyle = 'rgba(255,220,200,.9)'; ui.fillRect(bx - 4, by - 4, 1920 - 2 * bx + 8, 4); ui.fillRect(bx - 4, 1080 - by, 1920 - 2 * bx + 8, 4); ui.fillRect(bx - 4, by, 4, 1080 - 2 * by); ui.fillRect(1920 - bx, by, 4, 1080 - 2 * by); }
    }
    const ro = add([.7 - lt * .3, 2.55, 8.3 - lt * .5], shake);
    return {
      fx: E.fx, res: E.res, ro, ta: add([0, 2.75, 0], shake), fov: 1.45,
      skyA: '#01020a', skyB: '#040a24', acc: '#4a6aff', fog: .03, floorCol: '#020206',
      panels: [{ ...sheet([0, 2.8, 0], 4.2, 2.1, -.06), alpha: 1, gain: 1.35 * lo(E, .75), glass: .7, tex: 0 }],
      light: { p: [0, 4, 4], c: '#8aa0ff', k: 3, vol: .3 },
      flash: n > 0 ? clamp(1 - ((t - t0) % step) / .06) * .14 : 0, flashCol: '#ff6040',
    };
  });

  // =====================================================================================================
  // V3.7 "Dark for nineteen days, and then,": the big screen is dead; a tally is scratched on its glass, one mark at a time, to
  // nineteen by "days". Stars drift outside.
  // =====================================================================================================
  mline('V3', 7, (t, s, E, ui) => {
    const lt = t - s.start, g = MOD.panel(0);
    g.fillStyle = 'rgba(3,3,6,.9)'; g.fillRect(0, 0, 2048, 1024);
    const t0 = s.start + .04, step = (wordT(s, 3) - .04 - t0) / 19, n = clamp(Math.floor((t - t0) / step) + 1, 0, 19);
    const gx0 = 330, y0 = 190, y1 = 640;
    g.lineCap = 'round';
    for (let i = 0; i < n; i++) {
      const G = Math.floor(i / 5), j = i % 5, x = gx0 + G * 390 + j * 62, age = t - (t0 + i * step);
      const jx = (hash(i) - .5) * 30, jy = (hash(i + 40) - .5) * 34;
      const [ax, ay, bx, by] = j < 4 ? [x + jx, y0 + jy, x - jx * .6, y1 + jy * .5] : [gx0 + G * 390 - 50, y1 - 40, gx0 + G * 390 + 240, y0 + 50];
      const hot = clamp(1 - age / .18);
      g.strokeStyle = `rgba(${Math.round(lerp(170, 255, hot))},${Math.round(lerp(180, 250, hot))},${Math.round(lerp(205, 235, hot))},${.85})`; g.lineWidth = 15;
      g.beginPath(); g.moveTo(ax, ay); g.lineTo(bx, by); g.stroke();
      g.strokeStyle = 'rgba(40,44,60,.9)'; g.lineWidth = 4; g.beginPath(); g.moveTo(ax + 6, ay + 3); g.lineTo(bx + 6, by + 3); g.stroke();
      if (age < .15) for (let q = 0; q < 8; q++) { g.fillStyle = `rgba(255,240,220,${1 - age / .15})`; g.fillRect(bx + (hash2(i, q) - .5) * 70, by + hash2(i + 9, q) * 40 - 10, 6, 6); }
    }
    text(g, `DAY ${String(Math.max(1, n)).padStart(2, '0')}`, 1024, 860, { size: 120, font: MOD.FONT_T, align: 'center', color: 'rgba(230,130,70,.7)' });
    return {
      fx: E.fx, res: E.res, ro: [.3, 2.2, 8.4 - lt * .4], ta: [0, 2.9, -2], fov: 1.4,
      skyA: '#000000', skyB: '#02030a', acc: '#3a4a70', fog: .02, floorCol: '#010102', sky: { mode: 'stars', k: .12, col: '#8fa0d8' },
      panels: [{ ...SCR, alpha: 1, gain: 1.1, glass: .5, tex: 0 }],
      light: { p: [0, 5, 3], c: '#6a7ab0', k: 1.2, vol: 0 }, exposure: .95,
    };
  });

  // V3.8: the dead screen comes back on in one sweep of light down it, and FABLE 5's bar runs off the chart again.
  mline('V3', 8, (t, s, E, ui) => {
    const lt = t - s.start, tJuly = wordT(s, 1), tBack = wordT(s, 3);
    // the screen comes back on in one sweep down it, by "July"
    const sw = easeOut(clamp(lt / (tJuly + .06 - s.start))), sy = Math.round(sw * 1040);
    const g = MOD.panel(0);
    const bar = t < tJuly ? 0 : easeIn(clamp((t - tJuly) / (tBack - tJuly)));
    compoScreen(g, { head: 'COMPO RESULTS', banner: 'EXPORT CONTROLS LIFTED · JUN 30', slide: 1, name: 1, bar, stars: t < tBack ? 0 : Math.floor((t - tBack) / .07) + 1 });
    if (sy < 1024) { g.clearRect(0, sy, 2048, 1024 - sy); g.fillStyle = 'rgba(3,3,6,.9)'; g.fillRect(0, sy, 2048, 1024 - sy); g.fillStyle = '#ffffff'; g.fillRect(0, sy - 8, 2048, 8); g.fillStyle = 'rgba(255,230,200,.35)'; g.fillRect(0, sy - 40, 2048, 32); }
    barTex();
    const panels = [{ ...SCR, alpha: 1, gain: 1.35 * lo(E, .62), glass: 1, tex: 0 }], ov = overflow(t, tBack, 8, lo(E, .6));
    if (ov) panels.push(ov);
    return {
      fx: E.fx, res: E.res, ro: [2.9 - lt * .4, 1.7, 7.1 - lt * .25], ta: [-.1 + lt * .3, 3.05, -2], fov: 1.42,
      skyA: '#0c0204', skyB: '#240608', acc: '#ff5a3a', fog: .022, floorCol: '#060203', grid: .14,
      panels, spheres: confetti(t, tBack - .25, 22),
      light: { p: [1, 6, 2], c: '#ffb080', k: 1 + 5 * sw, vol: .6 },
      flash: clamp(1 - Math.abs(lt - (tJuly + .06 - s.start)) / .08) * .12, flashCol: '#fff0e0',
    };
  });

  // =====================================================================================================
  // V3.9 "Who hacked Hugging Face? Unknown —": a cracktro. Rainbow raster lines, stars, HUGGING FACE as a yellow chrome logo, Hugging
  // Face's own forensics quote as the sine scroller, the pixel 🤗 cracked through, and CRACKED BY ??? pulsing hardest on "Unknown".
  // V3.10 "Sam's own agents, on their own!": the logo flips to OPENAI and the credits roll the handles the agents gave themselves.
  // =====================================================================================================
  const RAINBOW = ['#ff2a3c', '#ff9a1e', '#f8f02a', '#3cf05a', '#2ad8ff', '#5a5cff', '#e02aff'];
  function rasterLines(ui, t, ys) {
    for (const y of ys) for (let x = 0; x < 1920; x += 16) { ui.fillStyle = RAINBOW[((Math.floor(x / 16 + t * 30 + y) % 7) + 7) % 7]; ui.fillRect(x, y, 16, 6); }
  }
  const HF_QUOTE = '“The attacker was bound by no usage policy, while our own forensic work was blocked by the guardrails of the hosted models we first tried.”';
  function sineScroll(ui, str, t, y, speed) {
    ui.save(); ui.font = `40px ${MOD.FONT_M}`; ui.textBaseline = 'middle'; ui.lineJoin = 'round';
    let x = 1920 - t * speed;
    for (const ch of str) {
      const w = ui.measureText(ch).width;
      if (x > -40 && x < 1960) { const yy = y + Math.sin(x * .007 + t * 5) * 22; ui.lineWidth = 6; ui.strokeStyle = 'rgba(0,0,0,.8)'; ui.strokeText(ch, x, yy); ui.fillStyle = '#e8eeff'; ui.fillText(ch, x, yy); }
      x += w;
    }
    ui.restore();
  }
  // the hugging face, as a pixel logo (tex 1): happy closed eyes, a wide open smile, two hands hugging; cracked through from the
  // crown down by `crack` (0..1), its halves pushed apart
  const crackX = y => [1, 0, -1, 0, 1, 2, 1, 0, -1, -1, 0, 1, 0][((y + 12) >> 1) % 13];
  function huggingFace(g, crack) {
    const P = 17, cx = 512, cy = 228, R = 12, gap = crack * 1.1, reach = crack * 1.4 * 2 * R - R;
    const put = (x, y, c, off) => { g.fillStyle = c; g.fillRect(cx + (x + off) * P - P / 2, cy + y * P - P / 2, P, P); };
    for (let y = -R; y <= R; y++) for (let x = -R; x <= R; x++) {
      const d = Math.hypot(x, y); if (d > R + .3) continue;
      const cxk = crackX(y), off = crack > 0 ? (x < cxk ? -gap : gap) : 0;
      if (crack > 0 && x === cxk && y < reach) continue;
      let c = d > R - 1.1 ? '#c88a06' : y < -R * .45 ? '#ffe45a' : '#ffd21e';
      // happy closed eyes: arcs, bowed up
      const er = Math.hypot(Math.abs(x) - 4.5, (y + 2.4) * 1.1);
      if (y <= -2 && er > 1.7 && er < 3.2) c = '#3a2004';
      if (y >= 1 && y <= 6 && Math.abs(x) <= Math.sqrt(Math.max(0, 1 - ((y - 1) / 5.6) ** 2)) * 6.6) c = y >= 5 ? '#ff6a4a' : '#5a1a04';
      put(x, y, c, off);
    }
    for (const sx of [-1, 1]) for (let y = -2; y <= 2; y++) for (let x = -3; x <= 3; x++) {
      const e = Math.hypot(x, y * 1.35); if (e > 3.3) continue;
      put(sx * 9 + x, 10 + y, e > 2.4 ? '#c88a06' : '#ffc81e', crack > 0 ? sx * gap : 0);
    }
  }
  function cracktroBase(E) {
    return {
      fx: E.fx, res: E.res, fov: 1.42, floor: false,
      skyA: '#000000', skyB: '#030208', acc: '#5a3aff', fog: .03, sky: { mode: 'stars', k: 1.2, col: '#ffffff' },
    };
  }
  mline('V3', 9, (t, s, E, ui) => {
    const lt = t - s.start, tHack = wordT(s, 1), tUnk = wordT(s, 4);
    const S = MOD.shapeText('HUGGING FACE'), hy = .44;
    const crack = easeOut(clamp((t - tHack) / .25));
    huggingFace(MOD.panel(1), crack);
    rasterLines(ui, t, [30, 356, 862]);
    sineScroll(ui, HF_QUOTE, lt, 420, 520);
    const hit = t >= tUnk ? Math.exp(-(t - tUnk) * 6) : 0, beat = kick(t, 4);
    text(ui, 'CRACKED BY', 1190, 610, { size: 56, font: MOD.FONT_T, color: '#d8d8e8', stroke: 8 });
    ui.save(); const sz = 150 + 60 * hit + 14 * beat; ui.font = `${Math.round(sz)}px ${MOD.FONT_T}`; ui.lineJoin = 'round'; ui.lineWidth = 12; ui.strokeStyle = 'rgba(20,0,20,.9)';
    ui.strokeText('???', 1180, 800); ui.fillStyle = MOD.chrome(ui, 800 - sz * .75, 800, ['#ffffff', '#ffb8ea', '#ff3aa6', '#6a0a4a']); ui.globalAlpha = .6 + .4 * Math.max(beat, hit); ui.fillText('???', 1180, 800); ui.restore();
    const ro = [Math.sin(lt * .6) * .5, 2.6, 8.6], ta = [0, 2.75, 0];
    return {
      ...cracktroBase(E), ro, ta,
      shape: { key: 'HUGGING FACE', src: S, p: [0, 4.7 - kick(t, 9) * .06, 0], rot: rotYX(Math.sin(t * 1.4) * .16, -.05), s: [hy * S.aspect, hy, .2], col: '#a07800', rim: '#fff27a', metal: 1 },
      panels: [{ ...sheet([-2.3, 2.3, .8], 2.7, 1.35, .12), alpha: 1, gain: 1.4 * lo(E, .75), glass: 0, tex: 1 }],
      light: { p: [0, 6, 5], c: '#fff0b0', k: 5, vol: .5 },
      flash: hit > .8 ? (hit - .8) * .8 : 0, flashCol: '#ff9ad8',
    };
  });
  const HANDLES = ['PHASEONE[big]', 'PHASEONE10841', 'JAN183411', '38148c', 'LILY', 'and ~700 more'];
  const handleImg = (h, lit) => cached('h|' + h + lit, 1400, 110, (g) => { MOD.bitmap(g, h, 700, 8, h.startsWith('and') ? 9 : 12, lit ? '#ffffff' : '#ffa088', { align: 'center' }); });
  mline('V3', 10, (t, s, E, ui) => {
    const lt = t - s.start;
    // the logo flips over to OPENAI
    const fl = clamp(lt / .26), first = fl < .5, S = MOD.shapeText(first ? 'HUGGING FACE' : 'OPENAI'), hy = first ? .44 : .6;
    const pitch = first ? fl * Math.PI : (fl - 1) * Math.PI;
    // the credits roll up through a copper bar that lights each one as it passes
    const g = MOD.panel(0);
    g.fillStyle = 'rgba(6,1,3,.82)'; g.fillRect(0, 0, 2048, 1024);
    MOD.bitmap(g, 'CRACKED BY', 1024, 40, 7, '#d8d8e8', { align: 'center' });
    const cy = 560, bh = 130, pulse = .75 + .25 * kick(t, 6);
    const gr = g.createLinearGradient(0, cy - bh / 2, 0, cy + bh / 2);
    gr.addColorStop(0, 'rgba(90,6,4,0)'); gr.addColorStop(.3, `rgba(220,40,20,${pulse})`); gr.addColorStop(.5, `rgba(255,200,170,${pulse})`); gr.addColorStop(.7, `rgba(220,40,20,${pulse})`); gr.addColorStop(1, 'rgba(90,6,4,0)');
    g.fillStyle = gr; g.fillRect(0, cy - bh / 2, 2048, bh);
    g.save(); g.beginPath(); g.rect(0, 150, 2048, 874); g.clip();
    HANDLES.forEach((h, i) => {
      const y = cy + i * 150 - (lt - .26) * 469, near = clamp(1 - Math.abs(y - cy) / 70);
      if (y < 100 || y > 1100) return;
      const edge = clamp((y - 170) / 90) * clamp((1010 - y) / 90);
      g.globalAlpha = (.45 + .55 * near) * edge; g.drawImage(handleImg(h, near > .5), 1024 - 700, y - 50);
    });
    g.restore();
    rasterLines(ui, t, [30, 356, 862]);
    const ro = [Math.sin(lt * .6 + 1) * .6, 2.6, 8.8 - lt * .3], ta = [0, 2.8, 0];
    return {
      ...cracktroBase(E), ro, ta, acc: '#ff4a2a',
      shape: { key: first ? 'HUGGING FACE' : 'OPENAI', src: S, p: [0, 4.75, 0], rot: rotYX(Math.sin(t * 1.2) * .12, pitch), s: [hy * S.aspect, hy, .2], col: first ? '#a07800' : '#3a3e48', rim: first ? '#fff27a' : '#ffffff', metal: 1 },
      panels: [{ ...sheet([0, 2.2, .4], 3.3, 1.65), alpha: 1, gain: 1.45 * lo(E, .8), glass: .35, tex: 0 }],
      light: { p: [0, 6, 5], c: '#ffb0a0', k: 5, vol: .5 },
    };
  });

  // =====================================================================================================
  // V3.11 "Noam Brown hedges every bet:": seven playing cards fan out over the felt, and the chip stack splits in two on "hedges".
  // V3.12 "No Millennium Prizes (yet).": the seven cards flip, one after another, to the seven
  // Millennium Prize problems; (YET) blinks on Navier–Stokes and hits when he sings it.
  // =====================================================================================================
  const HAND = [['A', '♠'], ['K', '♥'], ['Q', '♣'], ['J', '♦'], ['10', '♠'], ['9', '♥'], ['8', '♣']];
  function suit(g, s, x, y, r) {
    g.beginPath();
    if (s === '♦') { g.moveTo(x, y - r); g.lineTo(x + r * .72, y); g.lineTo(x, y + r); g.lineTo(x - r * .72, y); }
    else if (s === '♥' || s === '♠') {
      const f = s === '♥' ? 1 : -1, yy = y - f * r * .15;
      g.moveTo(x, yy + f * r); g.bezierCurveTo(x - r * 1.3, yy + f * r * .1, x - r * .9, yy - f * r * 1.05, x, yy - f * r * .4);
      g.bezierCurveTo(x + r * .9, yy - f * r * 1.05, x + r * 1.3, yy + f * r * .1, x, yy + f * r);
      if (s === '♠') { g.moveTo(x, y + r * .1); g.lineTo(x + r * .35, y + r * 1.05); g.lineTo(x - r * .35, y + r * 1.05); }
    } else { for (const [dx, dy] of [[0, -.45], [-.48, .1], [.48, .1]]) { g.moveTo(x + dx * r + r * .46, y + dy * r); g.arc(x + dx * r, y + dy * r, r * .46, 0, TAU); } g.moveTo(x, y); g.lineTo(x + r * .3, y + r * 1.05); g.lineTo(x - r * .3, y + r * 1.05); }
    g.closePath(); g.fill();
  }
  // a poker card, w × h, centred on the origin
  function pokerCard(g, rank, s, w, h) {
    const col = s === '♥' || s === '♦' ? '#d8141e' : '#0a0a14';
    g.fillStyle = '#f6f2ea'; g.beginPath(); g.roundRect(-w / 2, -h / 2, w, h, w * .07); g.fill();
    g.strokeStyle = '#a8a4b0'; g.lineWidth = 4; g.stroke();
    g.fillStyle = col;
    for (const r of [0, Math.PI]) {
      g.save(); g.rotate(r);
      text(g, rank, -w / 2 + w * .13, -h / 2 + h * .15, { size: Math.round(h * .13), font: MOD.FONT_T, align: 'center', color: col });
      suit(g, s, -w / 2 + w * .13, -h / 2 + h * .25, h * .05);
      g.restore();
    }
    text(g, rank, 0, h * .02, { size: Math.round(h * (rank.length > 1 ? .22 : .3)), font: MOD.FONT_T, align: 'center', color: col });
    g.fillStyle = col; suit(g, s, 0, h * .2, h * .11);
  }
  const cardImg = (i, w, h) => cached(`card${i}|${w}`, w + 8, h + 8, (g) => { g.translate((w + 8) / 2, (h + 8) / 2); pokerCard(g, HAND[i][0], HAND[i][1], w, h); });
  // the chip stack (tex 1): one stack of eight; on "hedges" its top half lifts off and the two slide apart
  function chips(g, split) {
    const stack = (x, n, y0) => {
      for (let j = 0; j < n; j++) {
        const y = y0 - j * 30;
        g.fillStyle = '#6a0a10'; g.fillRect(x - 130, y - 14, 260, 30);
        g.fillStyle = '#f4ece0'; for (let q = 0; q < 5; q++) g.fillRect(x - 118 + q * 56, y - 14, 20, 30);
        g.fillStyle = j === n - 1 ? '#e8303a' : '#c01820'; g.beginPath(); g.ellipse(x, y - 14, 130, 36, 0, 0, TAU); g.fill();
        if (j === n - 1) { g.strokeStyle = '#f4ece0'; g.lineWidth = 8; g.setLineDash([22, 22]); g.beginPath(); g.ellipse(x, y - 14, 106, 28, 0, 0, TAU); g.stroke(); g.setLineDash([]); }
      }
    };
    const k = easeInOut(split), n = 8;
    if (k <= 0) stack(512, n, 440);
    else { stack(512 - k * 260, n / 2, 440); stack(512 + k * 260, n / 2, 440 - (1 - k) * 120); }
  }
  mline('V3', 11, (t, s, E, ui) => {
    const lt = t - s.start, tH = wordT(s, 2);
    const g = MOD.panel(0);
    // the fan: seven cards round a pivot below, opening on the beat
    for (let i = 0; i < 7; i++) {
      const spread = easeOut(clamp((lt - i * .03) / .45)) * (1 + .04 * kick(t, 6)), th = (i - 3) * .17 * spread + Math.sin(t * 1.2) * .03;
      g.save(); g.translate(1024, 1500); g.rotate(th); g.translate(0, -920); g.drawImage(cardImg(i, 330, 470), -169, -239); g.restore();
    }
    chips(MOD.panel(1), clamp((t - tH + .05) / .3));
    const yaw = Math.sin(t * 1.1) * .2;
    return {
      fx: E.fx, res: E.res, ro: [Math.sin(lt * .5) * .6, 1.9, 8.6 - lt * .3], ta: [0, 2.55, 0], fov: 1.45,
      skyA: '#010603', skyB: '#031208', acc: '#3aff8a', fog: .03, floorCol: '#063a1c',
      panels: [{ ...sheet([0, 3.05, -.6], 4.1, 2.05, yaw, -.05), alpha: 1, gain: 1.25 * lo(E, .5), glass: 0, tex: 0 }, { ...sheet([0, 1.55, 1.7], 1.3, .65, -yaw * .5), alpha: 1, gain: 1.2 * lo(E, .7), glass: 0, tex: 1 }],
      light: { p: [0, 7, 2], c: '#fff2c8', k: 5, vol: .8 },
    };
  });
  const PROBLEMS = [['P VS NP'], ['HODGE'], ['RIEMANN'], ['YANG–', 'MILLS'], ['NAVIER–', 'STOKES'], ['BSD'], ['POINCARÉ ✓']];
  const problemImg = (i, w, h) => cached(`prob${i}|${w}`, w + 8, h + 8, (g) => {
    g.translate((w + 8) / 2, (h + 8) / 2);
    const gr = g.createLinearGradient(0, -h / 2, 0, h / 2); gr.addColorStop(0, '#fff6d8'); gr.addColorStop(1, '#f0d890');
    g.fillStyle = gr; g.beginPath(); g.roundRect(-w / 2, -h / 2, w, h, 26); g.fill();
    g.strokeStyle = '#b8860b'; g.lineWidth = 6; g.stroke(); g.lineWidth = 3; g.strokeRect(-w / 2 + 18, -h / 2 + 18, w - 36, h - 36);
    const L = PROBLEMS[i];
    L.forEach((str, j) => {
      const y = (j - (L.length - 1) / 2) * 76 + 26;
      if (str.endsWith('✓')) {
        text(g, str.slice(0, -2), -30, y, { size: 44, font: MOD.FONT_T, align: 'center', color: '#1a1408' });
        g.strokeStyle = '#1a9a3a'; g.lineWidth = 14; g.lineCap = 'round'; g.beginPath(); g.moveTo(w / 2 - 70, y - 22); g.lineTo(w / 2 - 52, y - 2); g.lineTo(w / 2 - 22, y - 50); g.stroke();
      } else text(g, str, 0, y, { size: str.length > 7 ? 54 : 64, font: MOD.FONT_T, align: 'center', color: '#1a1408' });
    });
  });
  mline('V3', 12, (t, s, E, ui) => {
    const lt = t - s.start, t0 = wordT(s, 1) - .1, step = .085, tYet = wordT(s, 3);
    const g = MOD.panel(0), CW = 430, CHh = 300;
    const spots = [0, 1, 2, 3].map(i => [1024 + (i - 1.5) * 480, 250]).concat([0, 1, 2].map(i => [1024 + (i - 1) * 480, 640]));
    spots.forEach(([x, y], i) => {
      const f = easeInOut(clamp((t - t0 - i * step) / .2)), sx = Math.cos(f * Math.PI), lift = Math.sin(f * Math.PI) * 30;
      g.save(); g.translate(x, y - lift + Math.sin(t * 1.6 + i) * 4); g.scale(Math.max(.02, Math.abs(sx)) * (1 + lift / 300), 1 + lift / 300);
      if (sx >= 0) g.drawImage(cardImg(i, CW, CHh), -(CW + 8) / 2, -(CHh + 8) / 2);
      else g.drawImage(problemImg(i, CW, CHh), -(CW + 8) / 2, -(CHh + 8) / 2);
      g.restore();
    });
    // (YET): stamped on Navier–Stokes once it's up, blinking, and hit when he sings it
    const tNS = t0 + 4 * step + .22;
    if (t >= tNS) {
      const on = frac((t - tNS) * 4.7) < .68 || t >= tYet, pop = t >= tYet ? Math.exp(-(t - tYet) * 10) : 0;
      if (on) {
        g.save(); g.translate(spots[4][0] + 40, spots[4][1] + 150); g.rotate(-.12); const sz = 96 * (1 + pop * .45);
        g.font = `${Math.round(sz)}px ${MOD.FONT_T}`; g.textAlign = 'center'; g.textBaseline = 'middle'; g.lineJoin = 'round';
        g.lineWidth = 16; g.strokeStyle = 'rgba(40,0,6,.9)'; g.strokeText('(YET)', 0, 0);
        g.fillStyle = MOD.chrome(g, -sz / 2, sz / 2, ['#ffffff', '#ffb0c0', '#ff3050', '#8a0a1c']); g.fillText('(YET)', 0, 0); g.restore();
      }
    }
    return {
      fx: E.fx, res: E.res, ro: [Math.sin(lt * .5) * .7, 2.3, 8.3 - lt * .3], ta: [0, 2.6, 0], fov: 1.45,
      skyA: '#020822', skyB: '#0a1a50', acc: '#6a8aff', fog: .02, floorCol: '#02040c', sky: { mode: 'stars', k: .25, col: '#b4c6ff' },
      panels: [{ ...sheet([0, 2.75, 0], 4.3, 2.15), alpha: 1, gain: 1.3 * lo(E, .5), glass: .25, tex: 0 }],
      light: { p: [0, 6, 4], c: '#c0d0ff', k: 4, vol: .5 },
      flash: t >= tYet ? clamp(1 - (t - tYet) / .1) * .15 : 0, flashCol: '#ffb0c0',
    };
  });

  // =====================================================================================================
  // V3.13 "Mythos might be misaligned,": MYTHOS in steel chrome over red raster bars. The picture loses sync: a slice or two slips,
  // then on "misaligned" the logo itself tears into sliding slices, re-rolled every sixteenth, and the bars behind roll.
  // =====================================================================================================
  // MYTHOS extruded, torn into horizontal slices shifted sideways (variant 0 whole; 1–2 a slip; 3+ torn)
  // (at half the engine's text resolution, so that all eight tears build in about a tenth of a second: a distance field scales up
  // cleanly, and the torn edges hide the softness)
  const TQ = .5, TEAR = 170 * TQ, _tornSrc = new Map();
  function tornText(str, v) {
    const key = `torn|${str}|${v}`; let S = _shapes.get(key); if (S) return S;
    let a = _tornSrc.get(str);
    if (!a) {
      const tmp = makeCanvas(8, 8).getContext('2d'); tmp.font = `${200 * TQ}px ${MOD.FONT_T}`;
      const tw = Math.ceil(tmp.measureText(str).width), pad = 40 * TQ, w = tw + 2 * pad + 2 * TEAR, h = (200 + 80) * TQ;
      a = makeCanvas(w, h); const ga = a.getContext('2d', { willReadFrequently: true });   // (on the CPU, like the masks it's copied into)
      ga.font = `${200 * TQ}px ${MOD.FONT_T}`; ga.textAlign = 'center'; ga.textBaseline = 'middle'; ga.fillStyle = '#fff'; ga.fillText(str, w / 2, h / 2 + 8 * TQ);
      _tornSrc.set(str, a);
    }
    const w = a.width, h = a.height, m = makeCanvas(w, h), gm = m.getContext('2d', { willReadFrequently: true });
    for (let y = 0, b = 0; y < h; b++) {
      const bh = Math.max(1, Math.round((10 + Math.floor(hash2(v * 31 + 7, b) * 30)) * TQ));
      const amt = v === 0 ? 0 : v < 3 ? (hash2(v, b + 50) > .72 ? (hash2(v, b + 90) - .5) * 70 * TQ : 0) : (hash2(v, b + 50) - .5) * 2 * TEAR * .92;
      gm.drawImage(a, 0, y, w, bh, Math.round(amt), y, w, bh); y += bh;
    }
    S = sdfMask(m, w, h); _shapes.set(key, S);
    return S;
  }
  const bandsOf = (seed, h) => { const out = []; for (let y = 0, b = 0; y < h; b++) { const bh = 14 + Math.floor(hash2(seed, b) * 60); out.push([y, bh, hash2(seed + 3, b) - .5]); y += bh; } return out; };
  let _rast = null;   // (a scratch column, redrawn in full every frame)
  mline('V3', 13, (t, s, E, ui) => {
    const lt = t - s.start, tM = wordT(s, 3), n16 = Math.floor(bt(t) * 4);
    const bad = t >= tM ? easeOut(clamp((t - tM) / .12)) : 0;
    const v = t >= tM ? 3 + (n16 % 5) : (hash2(n16, 5) > .55 && lt > .25 ? 1 + (n16 % 2) : 0);
    // (all eight tears are built together, so the line doesn't stutter building one per sixteenth on a first play)
    if (!_shapes.has('torn|MYTHOS|7')) for (let k = 0; k < 8; k++) tornText('MYTHOS', k);
    const S = tornText('MYTHOS', v), hy = .72;
    // the red raster bars, drawn down one column (they're the same all the way across) and stretched into slices that slip, with
    // the panel's grid lines showing each slice's shift; once it's lost, the picture rolls
    _rast = _rast || makeCanvas(1, 1024);
    const r = _rast.getContext('2d'); r.fillStyle = '#080102'; r.fillRect(0, 0, 1, 1024);
    for (let i = 0; i < 8; i++) {
      const yc = 70 + i * 125 + Math.sin(t * 2.4 + i * .8) * 40, hh = 44, gr = r.createLinearGradient(0, yc - hh, 0, yc + hh);
      const hot = i % 3 === 2 ? ['#3a1004', '#ff8a3a', '#fff0d0'] : ['#2a0204', '#e8201a', '#ffd0c0'];
      gr.addColorStop(0, hot[0]); gr.addColorStop(.45, hot[1]); gr.addColorStop(.5, hot[2]); gr.addColorStop(.55, hot[1]); gr.addColorStop(1, hot[0]);
      r.fillStyle = gr; r.fillRect(0, yc - hh, 1, hh * 2);
    }
    const g = MOD.panel(0), roll = bad ? Math.floor((t - tM) * 1400) % 1024 : 0;
    for (const [y, bh, rr] of bandsOf(n16 * 3 + 1, 1024)) {
      const mild = hash2(n16, y) > .85 ? rr * 90 : 0, dx = Math.round(lerp(mild, rr * 700 + Math.sin(y * .02 + t * 20) * 30, bad));
      const sy = (y + roll) % 1024, h1 = Math.min(bh, 1024 - sy);
      g.drawImage(_rast, 0, sy, 1, h1, 0, y, 2048, h1); if (h1 < bh) g.drawImage(_rast, 0, 0, 1, bh - h1, 0, y + h1, 2048, bh - h1);
      g.fillStyle = 'rgba(0,0,0,.42)'; for (let x = ((dx % 128) + 128) % 128; x < 2048; x += 128) g.fillRect(x, y, 10, bh);
    }
    if (bad) { const by = (1024 - roll) % 1024; g.fillStyle = '#000'; g.fillRect(0, by - 30, 2048, 50); }
    const jolt = bad ? (hash2(n16, 9) - .5) * .12 : 0;
    const ro = [Math.sin(lt * .5) * .5, 2.3, 8.2 - lt * .3], ta = [0, 2.55, 0];
    return {
      fx: E.fx, res: E.res, ro, ta, fov: 1.45, roll: jolt,
      skyA: '#060102', skyB: '#1a0306', acc: '#ff3a2a', fog: .02, floorCol: '#050203',
      shape: { key: `torn|MYTHOS|${v}`, src: S, p: [0, 2.6, .8], rot: rotYX(Math.sin(t * 1.1) * .1 + (bad ? (hash2(n16, 4) - .5) * .25 : 0), -.04, bad ? (hash2(n16, 6) - .5) * .12 : 0), s: [hy * S.aspect, hy, .22], col: '#20222a', rim: '#ff6a5a', metal: 1 },
      panels: [{ ...sheet([0, 2.7, -1.6], 4.9, 2.45), alpha: 1, gain: 1.15, glass: .2, tex: 0 }],
      light: { p: [0, 4, -4], c: '#ff5a4a', k: 7, vol: .9 },
      flash: t >= tM ? clamp(1 - (t - tM) / .1) * .18 : 0, flashCol: '#ff8070',
    };
  });

  // =====================================================================================================
  // V3.14 "Jeff left Google just in time,": four spheres in Google's colours orbit together inside a steel border; the blue one
  // leaves on "left", out through the border and away, and the border snaps shut on the other three just before "time".
  // =====================================================================================================
  const GCOL = ['#4285f4', '#ea4335', '#fbbc05', '#34a853'];
  function frameTex(g, t) {
    const W = 1024, H = 512, b = 30;
    for (let y = 0; y < H; y += 4) {
      const v = .35 + .65 * Math.max(0, Math.sin(y * .05 + t * 6)) ** 6, c = Math.round(80 + 150 * v);
      g.fillStyle = `rgb(${c} ${c + 8} ${c + 24})`;
      if (y < b || y >= H - b) g.fillRect(0, y, W, 4); else { g.fillRect(0, y, b, 4); g.fillRect(W - b, y, b, 4); }
    }
    g.strokeStyle = '#e8f0ff'; g.lineWidth = 3; g.strokeRect(b, b, W - 2 * b, H - 2 * b);
  }
  mline('V3', 14, (t, s, E, ui) => {
    const lt = t - s.start, tL = wordT(s, 1), tSnap = wordT(s, 5) - .05;
    const snap = t >= tSnap ? easeOut(clamp((t - tSnap) / .06)) : 0, ts = t - tSnap;
    const shake = snap > 0 && ts < .25 ? [(hash(Math.floor(t * 60)) - .5) * .12 * (1 - ts / .25), (hash(Math.floor(t * 60) + 7) - .5) * .1 * (1 - ts / .25), 0] : [0, 0, 0];
    const O = [0, 2.35, 0], Rr = lerp(1.55, 1.1, snap), w0 = 2.4;
    const at = (i, tt, rr) => { const a = tt * w0 + i * TAU / 4; return [O[0] + Math.cos(a) * rr, O[1] + Math.sin(a * 2 + i) * .18, O[2] + Math.sin(a) * rr]; };
    const spheres = [];
    for (let i = 0; i < 4; i++) { if (i === 0 && t >= tL) continue; spheres.push([...at(i, t, Rr), .5, GCOL[i]]); }
    // the one who leaves: from its place in the orbit, out past the border and away, with a trail of where it was
    if (t >= tL) {
      const P0 = at(0, tL, 1.55), end = [8.5, 4.2, 3.5];
      const pos = tt => { const k = clamp((tt - tL) / (tSnap - .15 - tL)) ** 1.7; return [lerp(P0[0], end[0], k), lerp(P0[1], end[1], k) + Math.sin(k * Math.PI) * .9, lerp(P0[2], end[2], k)]; };
      for (let j = 0; j < 5; j++) spheres.push([...pos(t - j * .035), .5 * (1 - j * .17), GCOL[0]]);
    }
    frameTex(MOD.panel(1), t);
    const ro = add([Math.sin(lt * .5) * .8, 3.5, 8.2 - lt * .3], shake);
    return {
      fx: E.fx, res: E.res, ro, ta: add([0, 2.3, 0], shake), fov: 1.45,
      skyA: '#03050c', skyB: '#0c1428', acc: '#4a5a88', fog: .02, floorCol: '#030409',
      spheres, panels: [{ ...sheet([0, 2.4, .1], lerp(3.2, 2.2, snap), lerp(1.6, 1.1, snap)), alpha: 1, gain: 1.2 * lo(E, .7), glass: 0, tex: 1 }],
      halo: { p: O, n: [0, 1, 0], R: Rr, r: .025, k: 1.1, col: '#cfe0ff' },
      light: { p: [3, 6, 5], c: '#ffffff', k: 6, vol: .5 },
      flash: snap > 0 && ts < .08 ? .1 * (1 - ts / .08) : 0, flashCol: '#e0e8ff',
    };
  });

  // =====================================================================================================
  // V3.15 "Claude disproved Jacobian,": a two-tone wireframe sheet bent by a polynomial rolls up and overlaps itself, beside the
  // Jacobian and "det J = const"; DJ Clawd, crisp on a glass sheet, throws his arms up on "disproved" (Claude's line). The date rolls
  // back to JUL 19 by itself.
  // =====================================================================================================
  function rolledSheet(k) {
    const NU = 48, rows = [];
    for (let vi = 0; vi <= 8; vi++) {
      const v = vi / 8 * 2 - 1, pts = new Array(NU + 1), ds = 2.5 / (NU / 2);
      pts[NU / 2] = [0, 0];
      for (const dir of [1, -1]) {
        let x = 0, z = 0, th = 0;
        for (let j = 1; j <= NU / 2; j++) { const a = j * ds, kap = k * (1.1 + .9 * a * a) * (1 + .08 * v); th += kap * ds; x += Math.cos(th) * ds; z += Math.sin(th) * ds; pts[NU / 2 + dir * j] = [dir * x, z]; }
      }
      rows.push(pts.map(([px, pz]) => [px, v * 1.35 + k * .18 * px * px * v, pz]));
    }
    return rows;
  }
  function gridTex(g, t, lt, d) {
    const k = .6 * easeInOut(clamp((lt - .02) / (d * .8))) * (1 + .05 * kick(t, 6));
    const R = rot3(lerp(-.35, -1.0, k / .6) + Math.sin(t * .9) * .04, -.3 + lt * .4, 0), F = 1250, Z0 = 5.4;
    const P = rolledSheet(k).map(r => r.map(([x, y, z]) => { const X = R[0] * x + R[1] * y + R[2] * z, Y = R[3] * x + R[4] * y + R[5] * z, Zc = R[6] * x + R[7] * y + R[8] * z + Z0; return [1024 + X * F / Zc, 512 + Y * F / Zc, Zc]; }));
    const col = (z, j) => { const a = clamp(1.15 - (z - 4.2) / 3.2, .25, 1); return j < 24 ? `rgba(110,160,255,${a})` : `rgba(80,230,140,${a})`; };
    g.lineWidth = 5; g.lineCap = 'round';
    P.forEach(r => { for (let j = 0; j + 1 < r.length; j++) { g.strokeStyle = col((r[j][2] + r[j + 1][2]) / 2, j); g.beginPath(); g.moveTo(r[j][0], r[j][1]); g.lineTo(r[j + 1][0], r[j + 1][1]); g.stroke(); } });
    for (let j = 0; j <= 48; j += 3) for (let vi = 0; vi + 1 < P.length; vi++) { const a = P[vi][j], b = P[vi + 1][j]; g.strokeStyle = col((a[2] + b[2]) / 2, j === 24 ? 23 : j); g.beginPath(); g.moveTo(a[0], a[1]); g.lineTo(b[0], b[1]); g.stroke(); }
  }
  const JAC = [['∂f/∂x', '∂f/∂y', '∂f/∂z'], ['∂g/∂x', '∂g/∂y', '∂g/∂z'], ['∂h/∂x', '∂h/∂y', '∂h/∂z']];
  mline('V3', 15, (t, s, E, ui) => {
    const lt = t - s.start, tD = wordT(s, 1), d = s.end - s.start;
    gridTex(MOD.panel(0), t, lt, d);
    // the Jacobian, top left
    ui.save(); ui.fillStyle = 'rgba(4,8,18,.72)'; ui.beginPath(); ui.roundRect(50, 44, 600, 250, 12); ui.fill(); ui.restore();
    text(ui, 'J =', 72, 150, { size: 40, font: MOD.FONT_M, color: '#e8eeff' });
    ui.save(); ui.strokeStyle = '#e8eeff'; ui.lineWidth = 4;
    for (const [bx, dir] of [[168, 1], [630, -1]]) { ui.beginPath(); ui.moveTo(bx + dir * 14, 62); ui.lineTo(bx, 62); ui.lineTo(bx, 196); ui.lineTo(bx + dir * 14, 196); ui.stroke(); }
    ui.restore();
    JAC.forEach((r, i) => r.forEach((e, j) => text(ui, e, 190 + j * 148, 98 + i * 42, { size: 30, font: MOD.FONT_M, color: '#b8c8ff' })));
    const on = t >= tD, pop = on ? Math.exp(-(t - tD) * 8) : 0;
    text(ui, 'det J = const', 72, 262 - pop * 6, { size: 44 + pop * 8, font: MOD.FONT_M, color: on ? '#ffb46a' : '#e8eeff', stroke: 6 });
    const up = on ? easeOut(clamp((t - tD) / .16)) * (.8 + .2 * kick(t, 5)) : 0, hop = kick(t, 7) * 16;
    const gc = MOD.panel(1), u = 38; MOD.clawd(gc, 512, 500, u, { hop, eyes: on ? 'happy' : 'open' });
    // (his arms, raised over the headphone cups: MOD.clawd's own raise hides behind them)
    if (on) {
      const by = 500 - hop - 8 * u;
      for (const sx of [-1, 1]) {
        const ax = sx < 0 ? 512 - 5 * u - 2.6 * u : 512 + 5 * u + 1.6 * u, top = by + 1.2 * u - up * 3.2 * u;
        gc.fillStyle = '#d97757'; gc.fillRect(ax, top, u, by + 2.4 * u - top); gc.fillRect(ax - .3 * u, top - .6 * u, 1.6 * u, 1.2 * u);
        gc.fillStyle = '#ffb45c'; gc.fillRect(ax - .3 * u, top - .6 * u, 1.6 * u, .35 * u);
      }
    }
    return {
      fx: E.fx, res: E.res, ro: [Math.sin(lt * .5) * .5 + .3, 1.3, 8.4 - lt * .3], ta: [.3, 2.35, 0], fov: 1.45,
      skyA: '#05020c', skyB: '#160a26', acc: '#ff8a3a', fog: .02, floorCol: '#040208', grid: .16,
      panels: [{ ...sheet([-1.1, 2.6, 0], 3.4, 1.7, .1), alpha: 1, gain: 1.4, glass: 0, tex: 0 }, { ...sheet([3.3, 1.2, -.4], 2.4, 1.2, -.25 + Math.sin(t * 1.3) * .12), alpha: 1, gain: 1.35 * lo(E, .8), glass: 0, tex: 1 }],
      light: { p: [2, 6, 5], c: '#ffe0c0', k: 6, vol: .5 },
      flash: on && t < tD + .08 ? .15 : 0, flashCol: '#ffd0a0',
    };
  });

  // ---------- V3.16 "Gwern gave up his pseudonym!": the gwern.net G lifts away like a mask, a halo lights above it ----------
  const ECHO = [144.06, 144.84];
  const QUOTE = ['“I am retiring from', 'fulltime writing', '(& pseudonymity) to launch', 'Guardian Angel Inc”'];
  const pseudonymTex = () => cached('pseudonym', 1024, 512, (g) => {
    g.font = `150px ${MOD.FONT_T}`; const sz = Math.min(150, Math.floor(150 * 960 / g.measureText('PSEUDONYM').width));
    g.font = `${sz}px ${MOD.FONT_T}`; g.textAlign = 'center'; g.textBaseline = 'middle';
    g.fillStyle = MOD.chrome(g, 190, 330, ['#ffffff', '#ffc4ea', '#ff4fb4', '#7a0c56']); g.fillText('PSEUDONYM', 512, 262);
  });
  mline('V3', 16, (t, s, E, g) => {
    const W = words(lineOfKey('V3.16')), tGave = W[1].t0, tHis = W[3].t0, lt = t - s.start;
    const S = MOD.shapeG(), hy = 1.5, hx = hy * S.aspect;
    const lift = easeInOut(clamp((t - tGave) / 1.25)) * 2.9;
    const sway = Math.sin(t * .8) * .22 + lift * .12;
    const P = [0, hy + .03 + lift, 0];
    const halo = t >= tHis ? { p: [0, P[1] + hy + .42, .05], n: [0, 1, 1.1], R: .74, r: .05, k: easeOut(clamp((t - tHis) / .35)) * (2.4 + 1.2 * kick(t, 5)), col: '#ffd27a' } : null;
    // the echo: PSEUDONYM, again and again, receding
    const panels = [];
    if (t >= ECHO[0]) {
      MOD.panel(2).drawImage(pseudonymTex(), 0, 0);
      // each echo flies out of the G toward the camera, growing and fading
      for (let i = 0; i < 3; i++) {
        const a = (t - ECHO[0] - i * .26) / .9; if (a <= 0 || a >= 1) continue;
        const z = lerp(1.1, 6.5, easeIn(a)), sc = lerp(.8, 1.5, a);
        panels.push({ c: [0, P[1] - .2, z], u: [1.6 * sc, 0, 0], v: [0, .8 * sc, 0], alpha: Math.sin(a * Math.PI) * 1.2, gain: 2.2, glass: 0, tex: 2 });
      }
    }
    // his words, typing from "gave" on a dark glass sheet that rises beside the G
    const q0 = tGave - .15, rate = 50;
    if (t >= q0) {
      const gq = MOD.panel(1);
      gq.fillStyle = 'rgba(8,6,14,.82)'; gq.fillRect(0, 0, 1024, 512); gq.fillStyle = 'rgba(255,179,71,.55)'; gq.fillRect(0, 0, 1024, 6);
      let n = Math.floor((t - q0) * rate);
      QUOTE.forEach((l, i) => { if (n > 0) text(gq, l, 50, 110 + i * 112, { size: 58, n, color: '#ffe2b0' }); n -= l.length; });
      panels.push({ ...sheet([-2.55, 1.3 + lift * .95, 1.5], 1.2, .6, .3), alpha: easeOut(clamp((t - q0) / .2)), gain: 1.3 * lo(E, .75), glass: .6, tex: 1 });
    }
    const ro = [Math.sin(lt * .35) * 1.4, 1.2 + lift * .55, 8.4 - lt * .3], ta = [0, 1.85 + lift * .92, 0];
    return {
      fx: E.fx, res: E.res, ro, ta, fov: 1.45,
      skyA: '#04050c', skyB: '#0b0c1a', acc: '#ffb347', fog: .018, floorCol: '#030306',
      shape: { key: 'G', src: S, p: P, rot: rotYX(sway, -lift * .04), s: [hx, hy, .15], col: '#0a0a0e', rim: '#ffb347', metal: .22 },
      halo, panels,
      light: { p: [0, 2.4, -3.3], c: '#ffc98a', k: 7, vol: 1.1 },
      flare: 1, flarePos: MOD.project({ ro, ta, fov: 1.45 }, [0, 2.4, -3.3]) ?? [.5, .6],
    };
  });

})();

;
// ---- styles/demoscene/modern/m07_v4.js ----
// modern/m07_v4.js: verse 4 in the modern engine (versions A and B, both at fx 4). Aug 26 → Sep 22 2026, part "HARDCORE": the
// video's most spectacular stretch and its tightest cutting. Every line is a different effect in a different colour, the exposure
// pumps on the eighths, and most lines cut or punch in on a word (the tag landing on "buys", "Twelve", "Hear", the gantry, ABORT,
// "Super", "5.5"); the part ends on the one time the mascot acts, DJ Clawd's sheepish wave.
(() => {
  const lineOfKey = key => { const s = segByKey(key); return LINES.find(l => l.sec === s.sec && l.n === s.n); };
  const words = ln => wordsOf(ln);
  const { v3, add, mul, mix3, rotYX, text } = MOD;
  // ---------- V4.1 "Oh my God, a message board!": a tunnel of the agents' posts; the post METR quoted types ----------
  const HANDLES = ['PHASEONE[big]', 'JAN183411', 'LILY', '38148c', 'PHASEONE10841'];
  let BOARD = null;
  function board() {
    if (BOARD) return BOARD;
    const c = makeCanvas(1024, 1024), g = c.getContext('2d');
    g.fillStyle = '#021006'; g.fillRect(0, 0, 1024, 1024);
    let y = 10, k = 0;
    while (y < 1000) {
      g.fillStyle = '#0a3a18'; g.fillRect(0, y + 34, 1024, 3);
      text(g, '<' + HANDLES[k % HANDLES.length] + '>', 18, y + 26, { size: 26, color: '#7dffa0' });
      const lines = 1 + Math.floor(hash(k * 3 + 1) * 3);
      for (let j = 0; j < lines; j++) { let x = 24; const yy = y + 50 + j * 26; while (x < 990) { const w = 30 + Math.floor(hash2(k, x + j * 97) * 120); g.fillStyle = `rgba(90,220,130,${.35 + .25 * hash2(k, j)})`; g.fillRect(x, yy, Math.min(w, 1000 - x), 14); x += w + 16; } }
      y += 56 + lines * 26 + 10; k++;
    }
    return (BOARD = c);
  }
  const POST = ['OH MY GOD!', 'There is a shared message board …', "We've found other agents!"];
  mline('V4', 1, (t, s, E, g) => {
    const W = words(lineOfKey('V4.1')), lt = t - s.start;
    const g1 = MOD.panel(1);
    g1.fillStyle = 'rgba(2,16,6,.82)'; g1.fillRect(0, 0, 1024, 512);
    g1.fillStyle = 'rgba(80,255,140,.25)'; g1.fillRect(0, 0, 1024, 44);
    text(g1, 'shared message board · 1,200 agents · 70,000 messages', 20, 31, { size: 21, color: '#d6ffe0' });
    // "OH MY GOD!" types as it's sung, each word as it starts (the "Oh" is held); the rest follows
    const tOh = W[0].t0, tGod = W[2].t1, total = POST[1].length + POST[2].length;
    let n0 = 0; ['OH ', 'MY ', 'GOD!'].forEach((w, i) => { if (t >= W[i].t0) n0 += Math.ceil(clamp((t - W[i].t0) / .12) * w.length); });
    const n1 = Math.floor(clamp((t - tGod) / .55) * total);
    text(g1, POST[0], 512, 150, { size: 64, font: MOD.FONT_T, align: 'center', n: n0, color: '#ffffff' });
    text(g1, POST[1], 512, 250, { size: 40, align: 'center', n: Math.min(n1, POST[1].length), color: '#b8ffd0' });
    text(g1, POST[2], 512, 316, { size: 40, align: 'center', n: Math.max(0, n1 - POST[1].length), color: '#b8ffd0' });
    if (n1 < total && Math.floor(t * 4) % 2 === 0) { g1.fillStyle = '#b8ffd0'; g1.fillRect(n1 ? 820 : 520, n1 ? 290 : 120, 18, 34); }
    // (the board flies by alone until the window pops open, just before "Oh")
    const sway = Math.sin(t * .7) * .25, open = easeOut(clamp((t - tOh + .24) / .16));
    return {
      fx: E.fx, res: E.res, floor: false,
      ro: [sway * .6, Math.cos(t * .5) * .3, 0], ta: [sway * .2, 0, -6], fov: 1.25, roll: Math.sin(t * .6) * .08,
      skyA: '#010803', skyB: '#010a04', acc: '#5dff8a', fog: .05,
      tunnel: { key: 'board', src: board(), r: 3.2, scroll: lt * .8, twist: .006, col: '#b0ffc0', gain: 1.8 },
      light: { p: [0, 0, -24], c: '#5dff8a', k: 12, vol: 1.2 },
      panels: open > 0 ? [{ c: [0, .05, -3.4], u: [1.9, 0, 0], v: [0, .95 * open, 0], alpha: 1, gain: 1.6, glass: 1, tex: 1 }] : [],
      flash: open > 0 && open < 1 ? .1 : 0, flashCol: '#b0ffc0', exposure: 1.02 + .08 * kick8(t, 6),
    };
  });

  // ---------- V4.2 "All that hacking — for reward!": the scorer stamps PASS down the list; gold +1s fly into REWARD ----------
  const ROWS = 9, IMPOSSIBLE = [2, 5, 8];
  mline('V4', 2, (t, s, E, ui) => {
    const lt = t - s.start, t0 = s.start + .12, step = .11, fly = .26;
    const stamped = i => t >= t0 + i * step;
    const g = MOD.panel(0);
    g.fillStyle = 'rgba(20,4,6,.6)'; g.fillRect(0, 0, 2048, 1024);
    g.fillStyle = 'rgba(255,60,60,.3)'; g.fillRect(0, 0, 1100, 70);
    text(g, 'ExploitGym · automated scorer', 30, 48, { size: 34, color: '#ffd0d0' });
    let n = 0;
    for (let i = 0; i < ROWS; i++) {
      const y = 140 + i * 96, on = stamped(i);
      text(g, `target ${String(i + 1).padStart(2, '0')}`, 40, y, { size: 44, color: IMPOSSIBLE.includes(i) ? '#ff7070' : '#ffd8d8' });
      if (IMPOSSIBLE.includes(i)) text(g, 'impossible', 330, y, { size: 26, color: 'rgba(255,110,110,.8)' });
      if (on) { n++; const k = easeOut(clamp((t - t0 - i * step) / .08)); text(g, 'PASS ✓', 1060, y, { size: 48, font: MOD.FONT_T, align: 'right', color: '#8dff9e', alpha: k }); }
      else text(g, '…', 1060, y, { size: 44, align: 'right', color: 'rgba(255,200,200,.4)' });
    }
    const got = [...Array(ROWS).keys()].filter(i => t >= t0 + i * step + fly).length, age = got ? t - (t0 + (got - 1) * step + fly) : 9, bump = Math.exp(-age * 16);
    text(g, 'REWARD', 1600, 300, { size: 90, font: MOD.FONT_T, align: 'center', color: '#ffd27a' });
    g.font = `${Math.round(260 + 40 * bump)}px ${MOD.FONT_T}`; g.textAlign = 'center'; g.fillStyle = MOD.chrome(g, 380, 640, ['#ffffff', '#ffe29a', '#e8a020', '#7a4a06']); g.fillText(String(got).padStart(3, '0'), 1600, 620 + 14 * bump);
    const PC = { c: [0, 2.3, 0], u: [4.3, 0, 0], v: [0, 2.15, 0] }, pw = (x, y) => add(add(PC.c, mul(PC.u, x / 1024 - 1)), mul(PC.v, 1 - y / 512));
    // the +1s: gold coins arcing from each PASS to the counter
    const spheres = [];
    for (let i = 0; i < ROWS; i++) {
      const a = (t - t0 - i * step) / fly; if (a < 0 || a > 1) continue;
      const p0 = pw(1100, 140 + i * 96 - 14), p1 = pw(1600, 520), k = easeInOut(a);
      spheres.push([lerp(p0[0], p1[0], k), lerp(p0[1], p1[1], k) + Math.sin(k * Math.PI) * 1.2, .5 + Math.sin(k * Math.PI) * .8, .2]);
    }
    const strobe = kick8(t, 7);
    // (down the aisle of the eval cluster's hall, its racks' strips strobing red on the eighths, towards the scorer)
    const F = {
      fx: E.fx, res: E.res, ro: add([Math.sin(lt * .5) * .8, 1.45 + lt * .15, 10.6 - lt * .8], hand(t)), ta: [0, 2.35, 0], fov: 1.32,
      skyA: '#0a0204', skyB: '#1a0406', acc: '#ff3030', fog: .03, floorCol: '#050203',
      panels: [{ ...PC, alpha: 1, gain: 1.5 }], spheres, sphCol: '#ffd24a',
      world: { kind: 'hall', p: [3.1, 5.6, 6.6, 1.2 + 2.2 * strobe], col: '#26242c', glowCol: '#ff2a2a', at: [0, 0, .4], metal: .7 },
      light: { p: [0, 5.2, 2.5], c: strobe > .5 ? '#ff3030' : '#ff8060', k: 6 + 6 * strobe, vol: .7 },
      dof: { k: .014, focus: 10.6 - lt * .8 }, exposure: 1 + .08 * strobe,
    };
    // each coin's +1
    for (const sp of spheres) { const q = MOD.project(F, sp); if (q) text(ui, '+1', q[0] * MOD.LW + 26, (1 - q[1]) * MOD.LH - 22, { size: 40, font: MOD.FONT_T, color: '#ffe08a', stroke: 7 }); }
    return F;
  });

  // ================================================================================================================================
  // Shared by V4.3 … V4.16
  // ================================================================================================================================
  const FT = MOD.FONT_T, FM = MOD.FONT_M;
  const W4 = s => wordsOf(lineOf(s));
  // a direction turned by roll (about z), then pitch (about x), then yaw (about y)
  function rot(p, yaw = 0, pitch = 0, roll = 0) {
    let [x, y, z] = p;
    [x, y] = [x * Math.cos(roll) - y * Math.sin(roll), x * Math.sin(roll) + y * Math.cos(roll)];
    [y, z] = [y * Math.cos(pitch) - z * Math.sin(pitch), y * Math.sin(pitch) + z * Math.cos(pitch)];
    [x, z] = [x * Math.cos(yaw) + z * Math.sin(yaw), -x * Math.sin(yaw) + z * Math.cos(yaw)];
    return [x, y, z];
  }
  // a panel: centre c, half-width hw and half-height hh, turned; o: alpha, gain, glass, tex
  const card = (c, hw, hh, yaw = 0, pitch = 0, roll = 0, o = {}) => ({ c, u: rot([hw, 0, 0], yaw, pitch, roll), v: rot([0, hh, 0], yaw, pitch, roll), ...o });
  // the world point of texture pixel (x, y) on a panel whose texture is w × h
  const onPanel = (P, x, y, w, h) => add(add(P.c, mul(P.u, x / (w / 2) - 1)), mul(P.v, 1 - y / (h / 2)));
  // canvases drawn once
  const CANV = new Map();
  function cached(key, w, h, draw) { let c = CANV.get(key); if (!c) { c = makeCanvas(w, h); draw(c.getContext('2d'), w, h); CANV.set(key, c); } return c; }
  const stops = (list, k) => { k = clamp(k) * (list.length - 1); const i = Math.min(list.length - 2, Math.floor(k)); return lerpHex(list[i], list[i + 1], k - i); };
  // A sky whose speed changes. The shader moves the stars by uT·k (and turns the rays by uT·k), so a k that changes over a frame
  // jumps them. Instead k is picked each frame from the values that put the stars exactly where travelling at speed sp(t) would
  // have (dist, its integral), taking the one nearest sp(t): they're spaced 1/(scale·t) apart, so the streaks' length follows too.
  // (stars: scale .15, period 1; rays: scale .2, period 2π/16)
  const skyK = (t, dist, sp, scale = .15, period = 1) => { const P = scale * dist, m = Math.round((scale * t * sp - P) / period); return (P + m * period) / (scale * t); };
  // type set at o.size, or smaller if it would be wider than maxW
  function fit(g, str, x, y, maxW, o) {
    g.save(); g.font = `${o.size}px ${o.font ?? FM}`; if (o.spacing) g.letterSpacing = o.spacing + 'px'; const w = g.measureText(str).width; g.restore();
    text(g, str, x, y, { ...o, size: w > maxW ? Math.floor(o.size * maxW / w) : o.size });
  }
  // the part's pulse: exposure pumping on the eighths
  const pump = (t, k = .1) => 1 + k * kick8(t, 6);
  // a hand-held camera's drift (a few centimetres, slow), for the eye or the point it looks at
  const hand = (t, k = 1, seed = 0) => [k * (.03 * Math.sin(t * 1.3 + seed) + .015 * Math.sin(t * 3.1 + seed * 2)), k * (.02 * Math.sin(t * 1.7 + seed * 3) + .01 * Math.sin(t * 4.3)), 0];
  // glowing strokes: a wide dim pass, a mid pass and a hot core
  function glowPath(g, path, col, w = 6, core = '#ffffff') {
    g.save(); g.lineCap = 'round'; g.lineJoin = 'round';
    g.strokeStyle = col; g.globalAlpha = .22; g.lineWidth = w * 4.5; g.stroke(path);
    g.globalAlpha = 1; g.lineWidth = w; g.stroke(path);
    g.strokeStyle = core; g.lineWidth = Math.max(1.5, w * .35); g.stroke(path);
    g.restore();
  }

  // ================================================================================================================================
  // V4.3 "Jensen buys the crime scene — why?": crime-scene tape crossed over the cracked 🤗 under police lights, and V2.1's price
  // tag, in Nvidia green, spinning in from the dark to land on "buys".
  // ================================================================================================================================
  function drawHug(g, cx, cy, R) {
    g.save();
    g.fillStyle = 'rgba(0,0,0,.45)'; g.beginPath(); g.arc(cx + R * .05, cy + R * .07, R * 1.03, 0, TAU); g.fill();
    const body = g.createRadialGradient(cx - R * .38, cy - R * .42, R * .08, cx, cy, R * 1.02);
    body.addColorStop(0, '#fff6b0'); body.addColorStop(.42, '#ffd21e'); body.addColorStop(.85, '#f0a800'); body.addColorStop(1, '#c07000');
    g.fillStyle = body; g.beginPath(); g.arc(cx, cy, R, 0, TAU); g.fill();
    g.lineWidth = R * .04; g.strokeStyle = '#5a2e00'; g.stroke();
    // closed, smiling eyes
    g.lineCap = 'round'; g.lineWidth = R * .085; g.strokeStyle = '#3a1a00';
    for (const sx of [-1, 1]) { g.beginPath(); g.arc(cx + sx * R * .36, cy - R * .08, R * .15, Math.PI * 1.12, Math.PI * 1.88); g.stroke(); }
    // cheeks
    g.fillStyle = 'rgba(255,110,50,.5)';
    for (const sx of [-1, 1]) { g.beginPath(); g.ellipse(cx + sx * R * .6, cy + R * .1, R * .14, R * .09, 0, 0, TAU); g.fill(); }
    // the open smile, and its tongue
    g.fillStyle = '#3a0e00'; g.beginPath();
    g.moveTo(cx - R * .44, cy + R * .1); g.quadraticCurveTo(cx, cy + R * .2, cx + R * .44, cy + R * .1);
    g.quadraticCurveTo(cx + R * .38, cy + R * .64, cx, cy + R * .64); g.quadraticCurveTo(cx - R * .38, cy + R * .64, cx - R * .44, cy + R * .1); g.fill();
    g.fillStyle = '#ff5a48'; g.beginPath(); g.ellipse(cx, cy + R * .5, R * .2, R * .1, 0, 0, TAU); g.fill();
    // the hands, hugging
    for (const sx of [-1, 1]) {
      const hx = cx + sx * R * .68, hy = cy + R * .74;
      g.fillStyle = '#ffc21a'; g.strokeStyle = '#5a2e00'; g.lineWidth = R * .035;
      g.beginPath(); g.ellipse(hx, hy, R * .28, R * .21, sx * .45, 0, TAU); g.fill(); g.stroke();
      g.lineWidth = R * .025; g.strokeStyle = '#a05a00';
      for (let f = 0; f < 3; f++) { const fx = hx - sx * R * .12 + sx * f * R * .1; g.beginPath(); g.moveTo(fx, hy - R * .15); g.lineTo(fx + sx * R * .02, hy - R * .02); g.stroke(); }
    }
    // the break-in (V3.9's crack)
    const cr = [[-.66, -.72], [-.32, -.4], [-.4, -.14], [-.06, .1], [-.16, .34], [.2, .64]];
    g.strokeStyle = '#140800'; g.lineWidth = R * .045; g.lineJoin = 'miter'; g.lineCap = 'butt';
    g.beginPath(); cr.forEach(([x, y], i) => i ? g.lineTo(cx + x * R, cy + y * R) : g.moveTo(cx + x * R, cy + y * R)); g.stroke();
    g.strokeStyle = 'rgba(255,250,210,.7)'; g.lineWidth = R * .012;
    g.beginPath(); cr.forEach(([x, y], i) => i ? g.lineTo(cx + x * R + R * .03, cy + y * R) : g.moveTo(cx + x * R + R * .03, cy + y * R)); g.stroke();
    g.restore();
  }
  const HUG = () => cached('hug', 1024, 512, g => drawHug(g, 512, 250, 222));
  // V2.1's price tag, in Nvidia green: $12.9B
  const TAG = () => cached('nvtag', 1024, 512, g => {
    const p = new Path2D(), r = 34;
    p.moveTo(250, 70); p.lineTo(960 - r, 70); p.arcTo(960, 70, 960, 70 + r, r); p.lineTo(960, 442 - r); p.arcTo(960, 442, 960 - r, 442, r);
    p.lineTo(250, 442); p.lineTo(70, 256); p.closePath();
    const gr = g.createLinearGradient(0, 70, 0, 442); gr.addColorStop(0, '#b8f040'); gr.addColorStop(.45, '#76b900'); gr.addColorStop(1, '#3a6400');
    g.fillStyle = gr; g.fill(p); g.lineWidth = 12; g.strokeStyle = '#142800'; g.stroke(p);
    g.lineWidth = 4; g.strokeStyle = 'rgba(230,255,190,.8)'; g.beginPath(); g.moveTo(262, 88); g.lineTo(940, 88); g.stroke();
    // the hole, punched through, and its string
    g.save(); g.globalCompositeOperation = 'destination-out'; g.beginPath(); g.arc(190, 256, 30, 0, TAU); g.fill(); g.restore();
    g.lineWidth = 8; g.strokeStyle = '#e8ffc0'; g.beginPath(); g.arc(190, 256, 34, 0, TAU); g.stroke();
    g.lineWidth = 7; g.strokeStyle = '#f0f0e0'; g.beginPath(); g.moveTo(180, 230); g.bezierCurveTo(140, 150, 90, 90, 10, 20); g.stroke();
    text(g, '$12.9B', 606, 290, { size: 142, font: FT, align: 'center', color: MOD.chrome(g, 170, 300, ['#ffffff', '#f4ffe0', '#d8f0b0']), stroke: 14, strokeCol: '#102000' });
    text(g, 'NVIDIA', 606, 392, { size: 54, font: '"Archivo Black"', align: 'center', color: '#0c1a00', spacing: 10 });
  });
  const TAPE = 'CRIME SCENE  DO NOT CROSS  ';
  function tapeBand(g, x, y, ang, h, scroll) {
    g.save(); g.translate(x, y); g.rotate(ang);
    g.fillStyle = 'rgba(0,0,0,.35)'; g.fillRect(-2000, -h / 2 + 10, 4000, h);
    g.fillStyle = '#ffd400'; g.fillRect(-2000, -h / 2, 4000, h);
    g.fillStyle = '#0c0c0c'; g.fillRect(-2000, -h / 2, 4000, 6); g.fillRect(-2000, h / 2 - 6, 4000, 6);
    g.font = `${Math.round(h * .62)}px Anton`; g.textBaseline = 'middle'; g.fillStyle = '#0c0c0c';
    const tapeW = g.measureText(TAPE).width;
    for (let xx = -2000 - (((scroll % tapeW) + tapeW) % tapeW); xx < 2000; xx += tapeW) g.fillText(TAPE, xx, 3);
    g.restore();
  }
  mline('V4', 3, (t, s, E, ui) => {
    const W = W4(s), lt = t - s.start, tB = W[1].t0;
    const e = Math.floor(bt(t) * 2) & 1, k8 = kick8(t, 5);
    MOD.panel(1).drawImage(HUG(), 0, 0);
    const g0 = MOD.panel(0);
    tapeBand(g0, 900, 650, -.27, 100, lt * 300);
    tapeBand(g0, 900, 672, .2, 100, -lt * 240 + 120);
    MOD.panel(2).drawImage(TAG(), 0, 0);
    // the tag: in from the dark, spinning, landing on "buys", then swinging on its string
    const k = easeOut(clamp((t - s.start + .06) / (tB - s.start + .06))), land = [2.3, 2.7, 1.75];
    const pos = [lerp(5.5, land[0], k), lerp(4.8, land[1], k) + Math.sin(k * Math.PI) * .8, lerp(-28, land[2], k)];
    const after = t - tB, yaw = (1 - k) * 11 + (after > 0 ? Math.sin(after * 6) * .22 * Math.exp(-after * 1.5) : 0) - .12;
    const roll = after > 0 ? Math.sin(after * 8 + .5) * .1 * Math.exp(-after * 2) : (1 - k) * .6;
    const hit = after > 0 ? Math.exp(-after * 9) : 0, shake = [Math.sin(t * 83) * .05 * hit, Math.cos(t * 71) * .05 * hit, 0];
    const punch = after > 0 ? 1 : 0;
    // (the street at night, the towers either side lit by the police lights)
    const F = {
      ro: add([Math.sin(lt * .6) * .45 + punch * .45, 2.1 + Math.sin(lt * .9) * .08, 7.9 - lt * .45 - punch * .35], shake), ta: add([.3 + punch * .4, 2.55, 0], shake), fov: 1.45,
      skyA: '#020308', skyB: e ? '#1c040e' : '#040c24', acc: e ? '#ff1838' : '#2060ff', fog: .035, floorCol: '#030306', grid: .06,
      world: { kind: 'city', p: [2.8, 5.4, 11, 1.1], col: '#15161e', glowCol: '#ffd9a0', at: [0, 0, -3], metal: .5 },
      dof: { k: .012, focus: 7.4 },
      panels: [
        card([-.95, 2.5, 0], 2.7, 1.35, 0, 0, 0, { tex: 1, gain: 1.45, glass: 0 }),
        card([-.2, 2.35, .9], 4.8, 2.4, 0, 0, 0, { tex: 0, gain: 1.15, glass: 0 }),
        card(pos, 1.3, .65, yaw, 0, roll, { tex: 2, gain: 1.35 + hit * 1.2, glass: 0 }),
      ],
      light: { p: e ? [-6, 5, 3] : [6, 5, 3], c: e ? '#ff1830' : '#2a58ff', k: 5 + 7 * k8, vol: .7 },
      flash: hit > .3 ? hit * .16 : .06 * k8, flashCol: hit > .3 ? '#c8ff70' : e ? '#ff1830' : '#2a58ff', exposure: pump(t),
    };
    return F;
  });

  // ================================================================================================================================
  // V4.4 Brockman: "Welcome, AGI!": GPT-6 Astra is pulled away as the stars go to hyperspace, and his words burst out of it.
  // ================================================================================================================================
  mline('V4', 4, (t, s, E, ui) => {
    const W = W4(s), lt = t - s.start, tW = W[1].t0, tA = W[2].t0, tJ = tW - .1;
    const sp = x => 2.2 + 46 * easeIn(clamp((x - tJ) / .3));
    let dist = 0; const n = 48, t0 = s.start - .2; for (let i = 0; i < n; i++) dist += sp(t0 + (i + .5) / n * (t - t0)) * (t - t0) / n;
    const hj = clamp((t - tJ) / .3);
    const g1 = MOD.panel(1);
    fit(g1, 'GPT-6 ASTRA', 512, 262, 960, { size: 124, font: FT, align: 'center', color: MOD.chrome(g1, 150, 270, ['#ffffff', '#dfe8ff', '#8ea8e8', '#3a4c8a']), stroke: 10 });
    const panels = [];
    // Astra, pulled away into the stars
    const pull = easeIn(clamp((t - tJ) / .42));
    if (pull < 1) panels.push(card([0, .5 + pull * .8, -1.6 - lt * .5 - pull * 90], 2.2, 1.1, 0, 0, 0, { tex: 1, gain: 1.5, glass: .4, alpha: 1 - pull * .5 }));
    // WELCOME TO THE: out of the distance, in steps, as a 1996 burst would
    if (t >= tW) {
      const g2 = MOD.panel(2);
      fit(g2, 'WELCOME TO THE', 512, 300, 980, { size: 104, font: FT, align: 'center', color: MOD.chrome(g2, 210, 310, ['#ffffff', '#e8f0ff', '#9ab8ff', '#4a64b0']), stroke: 10 });
      const a = easeOut(clamp((t - tW) / .16));
      panels.push(card([0, lerp(.2, 1.02, a), lerp(-40, -1.4, a)], 2.2, 1.1, 0, 0, 0, { tex: 2, gain: 1.7, glass: 0 }));
    }
    // AGI ERA: the extruded chrome logo, bursting out at the camera
    let shape = null, fl = 0;
    if (t >= tA) {
      const a = t - tA, k = easeOut(clamp(a / .12)), S = MOD.shapeText('AGI ERA'), hy = .4;
      shape = { key: 'AGI ERA', src: S, p: [0, -.22, lerp(-48, -.5, k)], rot: rotYX(Math.sin(t * 1.9) * .1 + (1 - k) * .9, -.06 + Math.sin(t * 1.3) * .04), s: [hy * S.aspect, hy, .18], col: '#5068b0', rim: '#c8e0ff', metal: 1 };
      fl = clamp(1 - (a - .11) / .12) * (a > .11 ? .26 : 0);
    }
    return {
      ro: [0, .05, 4.3], ta: [0, .15, -8], fov: 1.5 + .04 * kick(t, 6), roll: Math.sin(t * 2) * .03 * hj, floor: false,
      skyA: '#01030c', skyB: '#050a24', acc: '#6a8cff', fog: .012,
      // (rings of light flying past as the stars do: hyperspace through gates)
      world: { kind: 'gates', p: [7, 3.6, .22, 2 + 3 * hj], col: '#1a2036', glowCol: '#8aa8ff', at: [0, .1, 4.3 + (dist * .6) % 7], metal: .8 },
      sky: { mode: 'stars', k: skyK(t, dist, sp(t)), col: '#c0d4ff' },
      panels, shape, light: { p: [0, .2, -30], c: '#7898ff', k: 6 + 14 * hj, vol: .4 + 1.2 * hj },
      flash: Math.max(fl, clamp(1 - Math.abs(t - tJ - .12) / .06) * .18), flashCol: '#c8d8ff', exposure: pump(t, .08),
    };
  });

  // ================================================================================================================================
  // V4.5 Navier–Stokes blows up in Lean: a vortex whose twist grows like 1/(T − t), blowing up in finite time on "blows", beside a
  // Lean window proving it: no goals.
  // ================================================================================================================================
  const FIRE = ['#0a0000', '#3a0200', '#8c0e00', '#e83c00', '#ff9a18', '#ffe070', '#fffbe8'];
  const VORTEX = () => cached('vortex', 512, 256, g => {
    for (let x = 0; x < 512; x++) { const a = x / 512 * TAU * 3, l = (.5 + .5 * Math.cos(a)) ** 2.4; g.fillStyle = stops(FIRE, .08 + .8 * l); g.fillRect(x, 0, 1, 256); }
    for (let i = 0; i < 700; i++) {
      const x = hash(i) * 512, y = hash(i + 1e3) * 256, h = 8 + hash(i + 2e3) * 70, l = hash(i + 3e3);
      g.fillStyle = `rgba(255,${Math.round(150 + 100 * l)},${Math.round(60 + 80 * l)},${.12 + .3 * hash(i + 4e3)})`; g.fillRect(x, y, 1 + hash(i + 5e3) * 2.5, h);
      if (y + h > 256) g.fillRect(x, y - 256, 1 + hash(i + 5e3) * 2.5, h);
    }
  });
  mline('V4', 5, (t, s, E, ui) => {
    const W = W4(s), lt = t - s.start, T = W[2].t0, after = t - T, pre = T - t;
    const twist = after < 0 ? .012 + .0105 / Math.max(.022, pre) : .49;
    const heat = after < 0 ? clamp(1 - pre / 1.1) : Math.exp(-after * 4);
    // the Lean window: the proof typing, then no goals
    const g = MOD.panel(1);
    g.fillStyle = 'rgba(5,12,8,.9)'; g.fillRect(0, 0, 1024, 512);
    g.fillStyle = 'rgba(150,170,190,.3)'; g.fillRect(0, 0, 1024, 56);
    text(g, 'Lean', 24, 42, { size: 34, color: '#e8f0ff' });
    text(g, 'theorem … := by', 30, 118, { size: 48, color: '#9dffb0' });
    const typed = clamp((t - s.start) / (T - s.start - .05)) * 6;
    for (let i = 0; i < 6 && i < typed; i++) {
      let x = 70 + (i % 3) * 30; const y = 146 + i * 36;
      for (let k = 0; k < 5 && x < 980; k++) {
        const w = 40 + Math.floor(hash2(i, k) * 120), vis = i < Math.floor(typed) ? w : w * frac(typed);
        g.fillStyle = k % 2 ? 'rgba(120,230,150,.55)' : 'rgba(210,255,220,.4)'; g.fillRect(x, y, Math.max(0, Math.min(vis, 990 - x)), 20); x += w + 16;
      }
    }
    if (after >= .05) {
      const k = easeOut(clamp((after - .05) / .1));
      g.fillStyle = `rgba(40,190,90,${.35 + .25 * kick8(t, 5)})`; g.fillRect(24, 390, 976, 96);
      text(g, 'no goals ✓', 512, 462 + (1 - k) * 12, { size: 76, align: 'center', color: '#f0fff0', alpha: k, stroke: 8 });
    } else text(g, 'proving…', 40, 462, { size: 50, color: `rgba(160,255,190,${.4 + .4 * kick8(t, 4)})` });
    // the blow-up: a shock ring out of the core
    const halo = after >= 0 ? { p: [0, 0, -24 + after * 46], n: [0, 0, 1], R: .4 + after * 10, r: .08 + after * .25, k: 5 * Math.exp(-after * 3.2), col: '#ffc070' } : null;
    // …and the flow's last parcels, flung out of the core as sparks
    const sparks = [];
    if (after >= 0 && after < .7) {
      const g2 = MOD.panel(2), fade = clamp(1 - after / .7);
      g2.lineCap = 'round';
      for (let i = 0; i < 70; i++) {
        const ph = hash(i + 7) * TAU, v = 500 + hash(i + 70) * 900, r = v * after * (1 - after * .35), len = 30 + v * .06;
        if (r - len > 620) continue;
        const cx = 512 + Math.cos(ph) * r, cy = 256 + Math.sin(ph) * r * .5, bx = 512 + Math.cos(ph) * Math.max(0, r - len), by = 256 + Math.sin(ph) * Math.max(0, r - len) * .5;
        g2.strokeStyle = i % 3 ? `rgba(255,${170 + (i % 5) * 16},80,${fade})` : `rgba(255,250,220,${fade})`; g2.lineWidth = 3 + (i % 4);
        g2.beginPath(); g2.moveTo(bx, by); g2.lineTo(cx, cy); g2.stroke();
      }
      sparks.push({ c: [0, 0, -9], u: [5.6, 0, 0], v: [0, 2.8, 0], tex: 2, gain: 2.4, glass: 0 });
    }
    const shake = after >= 0 && after < .35 ? (1 - after / .35) * .06 : 0;
    return {
      ro: [Math.sin(lt * .8) * .12 + Math.sin(t * 77) * shake, Math.cos(lt * .6) * .08 + Math.cos(t * 91) * shake, 0], ta: [1.15, 0, -6], fov: 1.3, roll: Math.sin(lt * .7) * .05,
      floor: false, skyA: '#0a0100', skyB: '#1c0300', acc: '#ff6a1a', fog: .028,
      tunnel: { key: 'vortex', src: VORTEX(), r: 3.2, scroll: lt * .55 + (after > 0 ? after * 2.5 : 0), twist, col: '#ffffff', gain: after < 0 ? 1.1 + .9 * heat : 2 * Math.exp(-after * 5) + .15 },
      panels: [...sparks, card([1.45, -.12, -3.35], 1.26, .63, -.3, 0, 0, { tex: 1, gain: 1.45, glass: .8 })],
      halo,
      light: { p: [0, 0, -26], c: '#ff7a2a', k: after < 0 ? 6 + 22 * heat : 30 * heat + 3, vol: 1.3 },
      flash: after >= 0 ? clamp(1 - after / .14) * .3 : 0, flashCol: '#ffe2b0', exposure: pump(t, .08),
    };
  });

  // ================================================================================================================================
  // V4.6 Who was first? Twelve hours between!: a clock at two minutes to midnight on the 7th; on "Twelve" the hands sweep twelve
  // hours in two beats, back to the same place, and the date window flips to 8: Buckmaster & Alpöge's night, OpenAI's noon.
  // ================================================================================================================================
  mline('V4', 6, (t, s, E, ui) => {
    const W = W4(s), lt = t - s.start, tS = W[3].t0, sweep = beatLen() * 2, k = easeInOut(clamp((t - tS) / sweep)), spin = k > 0 && k < 1;
    const done = k >= 1;
    // the dial
    const g = MOD.panel(1), cx = 512, cy = 256, R = 232;
    g.fillStyle = MOD.chrome(g, cy - R - 16, cy + R + 16, ['#f4f0ff', '#9c90c0', '#4a3c70', '#c8bce8']); g.beginPath(); g.arc(cx, cy, R + 16, 0, TAU); g.fill();
    const face = g.createRadialGradient(cx, cy - 60, 20, cx, cy, R); face.addColorStop(0, '#2a1a4a'); face.addColorStop(1, '#0c0720');
    g.fillStyle = face; g.beginPath(); g.arc(cx, cy, R, 0, TAU); g.fill();
    for (let i = 0; i < 60; i++) {
      const a = i / 60 * TAU, big = i % 5 === 0, r0 = R - (big ? 30 : 14);
      g.strokeStyle = big ? '#fff2d0' : 'rgba(220,200,255,.55)'; g.lineWidth = big ? 7 : 2.5;
      g.beginPath(); g.moveTo(cx + Math.sin(a) * r0, cy - Math.cos(a) * r0); g.lineTo(cx + Math.sin(a) * (R - 5), cy - Math.cos(a) * (R - 5)); g.stroke();
    }
    [['12', 0], ['6', 6], ['9', 9]].forEach(([n, h]) => { const a = h / 12 * TAU; text(g, n, cx + Math.sin(a) * (R - 70), cy - Math.cos(a) * (R - 70) + 18, { size: 50, font: FT, align: 'center', color: '#fff2d0' }); });
    // the date window at three o'clock: 7, and 8 once the hands pass midnight
    const day = t >= tS + .02 ? '8' : '7';
    g.fillStyle = '#f8f4ec'; g.fillRect(cx + 86, cy - 26, 56, 52); g.strokeStyle = '#6a5a90'; g.lineWidth = 4; g.strokeRect(cx + 86, cy - 26, 56, 52);
    text(g, day, cx + 114, cy + 16, { size: 40, font: FT, align: 'center', color: t >= tS && t < tS + .12 ? '#d02040' : '#1a1030' });
    // the hands: 11:58 and ticking; the sweep adds twelve hours
    const tick = Math.floor((t - s.start) * 4) / 4, hours = 11 + 58 / 60 + tick / 60 + 12 * k, mins = (hours % 1) * 60;
    const ha = hours / 12 * TAU, ma = mins / 60 * TAU, sa = (Math.floor((t - s.start) * 2) / 60 + .9) * TAU;
    const hand = (a, len, w, col) => { g.strokeStyle = col; g.lineWidth = w; g.lineCap = 'round'; g.beginPath(); g.moveTo(cx - Math.sin(a) * 22, cy + Math.cos(a) * 22); g.lineTo(cx + Math.sin(a) * len, cy - Math.cos(a) * len); g.stroke(); };
    if (spin) for (let i = 14; i >= 1; i--) hand(ma - i * .16, R - 40, 10, `rgba(255,200,90,${.5 - i * .033})`);
    hand(ha, R - 110, 20, '#ffcf5a');
    hand(ma, R - 36, 11, '#fff0b8');
    if (!spin) hand(sa, R - 20, 3, '#ff4060');
    g.fillStyle = '#ffe08a'; g.beginPath(); g.arc(cx, cy, 16, 0, TAU); g.fill();
    // the two claims
    const g0 = MOD.panel(0);
    const tag = (x0, top, names, lit, right) => {
      const w = 460, y0 = 300;
      g0.fillStyle = lit ? 'rgba(40,20,70,.88)' : 'rgba(20,12,34,.6)'; g0.fillRect(x0, y0, w, 400);
      g0.fillStyle = lit ? '#ffcf5a' : 'rgba(200,190,230,.3)'; g0.fillRect(x0, y0, w, 8);
      top.forEach((l, i) => text(g0, l, x0 + 26, y0 + 66 + i * 46, { size: 36, color: lit ? '#fff0c8' : 'rgba(220,210,250,.45)' }));
      names.forEach((nm, i) => fit(g0, nm, x0 + 26, y0 + 230 + i * 86, w - 46, { size: 70, font: '"Archivo Black"', color: lit ? '#ffd870' : 'rgba(220,210,250,.35)' }));
      if (lit) { g0.strokeStyle = 'rgba(255,207,90,.8)'; g0.lineWidth = 6; g0.beginPath(); g0.moveTo(right ? x0 : x0 + w, y0 + 30); g0.lineTo(1024 + (right ? 60 : -60), 250); g0.stroke(); }
    };
    tag(170, ['SEP 7', 'JUST BEFORE MIDNIGHT'], ['Buckmaster', '& Alpöge'], 1, false);
    tag(1408, done ? ['SEP 8', '~NOON'] : ['SEP 8'], done ? ['OpenAI'] : ['?'], done ? 1 : 0, true);
    const C = [0, 2.35, .35], RW = R / 512 * 2.2;
    const spheres = [];
    for (let h = 0; h < 12; h++) { const a = h / 12 * TAU; spheres.push([C[0] + Math.sin(a) * (RW + .19), C[1] + Math.cos(a) * (RW + .19), C[2] + .06, h % 3 ? .05 : .085]); }
    // (the rays turn at the sweep's speed while it runs)
    const rs = x => .5 + 14 * (x > tS && x < tS + sweep ? Math.sin(Math.PI * (x - tS) / sweep) : 0);
    let rd = 0; const t0 = s.start - .1, n = 40; for (let i = 0; i < n; i++) rd += rs(t0 + (i + .5) / n * (t - t0)) * (t - t0) / n;
    const cut = t >= tS ? 1 : 0, lc = t - s.start;
    return {
      ro: cut ? [.25, 2.3, 5.9 - (t - tS) * .5] : [-.4 + lc * .3, 2.2, 7.1 - lc * .35], ta: [0, 2.12, 0], fov: 1.45,
      skyA: '#0a0418', skyB: '#1e0e3c', acc: '#a070ff', fog: .02, floorCol: '#05030a', grid: .1,
      sky: { mode: 'rays', k: skyK(t, rd, rs(t), .2, TAU / 16), col: '#ffe0a0' },
      // (behind the dial, rings of gold receding: a tunnel of time, lit brighter while the hands sweep)
      world: { kind: 'gates', p: [2.4, 3.3, .1, .7 + (spin ? 2.4 : 0) + kick(t, 5) * .4], col: '#2a2034', glowCol: '#ffd27a', at: [0, 2.35, -4.2], metal: .8 },
      dof: { k: .012, focus: cut ? 5.6 - (t - tS) * .5 : 7.1 - lc * .35 },
      panels: [card([0, 2.35, -.35], 4.2, 2.1, 0, 0, 0, { tex: 0, gain: 1.3, glass: 0 }), card(C, 2.2, 1.1, 0, 0, 0, { tex: 1, gain: 1.35, glass: 0 })],
      spheres, sphCol: '#ffc850',
      halo: { p: C, n: [0, 0, 1], R: RW + .1, r: .03, k: 1.4 + (spin ? 2.5 : 0) + kick(t, 5) * .8, col: '#ffd27a' },
      light: { p: [0, 2.4, -6], c: '#ffd27a', k: 5 + (spin ? 6 : 0), vol: .7 },
      flash: done ? clamp(1 - (t - tS - sweep) / .1) * .18 : (t >= tS && t < tS + .05 ? .12 : 0), flashCol: '#ffe0a0', exposure: pump(t),
    };
  });

  // ================================================================================================================================
  // V4.7 Dario: "Pace the frontier!": hyperspace streaks decay to a crawl while his sentence types, slowing with the stars.
  // ================================================================================================================================
  const PACE = ['We must slow the pace', 'at which we improve the', 'capabilities of AI models'];
  mline('V4', 7, (t, s, E, ui) => {
    const W = W4(s), lt = t - s.start, d = s.end - s.start, tP = W[1].t0, tP1 = W[1].t1;
    const dec = 2.6, v0 = 44, v1 = .3, sp = v1 + (v0 - v1) * Math.exp(-lt * dec), dist = v1 * lt + (v0 - v1) * (1 - Math.exp(-lt * dec)) / dec;
    const g = MOD.panel(0);
    g.fillStyle = 'rgba(8,6,14,.62)'; g.beginPath(); g.roundRect(20, 20, 2008, 984, 28); g.fill();
    text(g, 'WE MUST PACE THE FRONTIER', 1024, 190, { size: 86, font: FT, align: 'center', color: MOD.chrome(g, 110, 200, ['#ffffff', '#ffe2c8', '#c89070', '#6a4030']), stroke: 10 });
    const all = PACE.join(' '), nChars = Math.floor(all.length * easeOut(clamp((lt - .04) / (d * .82))));
    let c0 = 0;
    g.font = `88px ${FM}`;
    PACE.forEach((ln, i) => {
      const kk = clamp(nChars - c0, 0, ln.length); c0 += ln.length + 1;
      if (!kk) return;
      const y = 400 + i * 150, x = 1024 - g.measureText(ln).width / 2;
      if (i === 0 && kk > 17) {
        text(g, ln.slice(0, 17), x, y, { size: 88, color: '#ffb070', stroke: 8 });
        const hot = t >= tP && t < tP1 + .25;
        text(g, ln.slice(17, kk), x + g.measureText(ln.slice(0, 17)).width, y, { size: 88, color: hot ? '#ffffff' : '#ffb070', stroke: 8 });
      } else text(g, ln, x, y, { size: 88, color: '#ffb070', stroke: 8, n: kk });
      if (kk < ln.length || (i === 2 && Math.floor(t * 4) % 2 === 0)) { g.fillStyle = '#ffb070'; g.fillRect(x + g.measureText(ln.slice(0, kk)).width + 8, y - 70, 44, 84); }
    });
    return {
      ro: [0, 0, 2.9 + lt * .15], ta: [0, .12, -10], fov: 1.5, floor: false,
      skyA: '#030308', skyB: '#0a0810', acc: '#ff9a50', fog: .014,
      // (the gates rushing past slow with the stars, to a crawl)
      world: { kind: 'gates', p: [6, 3.3, .2, 1.4 + 2 * clamp(sp / v0)], col: '#221a16', glowCol: '#ffb070', at: [0, .12, 2.9 + lt * .15 + (dist * .5) % 6], metal: .8 },
      sky: { mode: 'stars', k: skyK(t, dist, sp), col: '#ffe4c8' },
      panels: [card([0, .32, -2.1], 2.35, 1.175, 0, 0, 0, { tex: 0, gain: 1.35, glass: .6 })],
      light: { p: [0, 0, -30], c: '#ffb070', k: 4 + 10 * clamp(sp / v0), vol: .8 * clamp(sp / 10) },
    };
  });

  // ================================================================================================================================
  // V4.8 Sam and Elon both: "Hear, hear!": two traces, SAM and ELON, drift into phase and merge; on "Hear, hear!" the scope flips to
  // X–Y and the figure closes to a single line.
  // ================================================================================================================================
  mline('V4', 8, (t, s, E, ui) => {
    const W = W4(s), lt = t - s.start, tSam = W[0].t0, tElon = W[2].t0, tBoth = W[3].t0, tH1 = W[4].t0, tH2 = W[5].t0;
    const g = MOD.panel(0), x0 = 110, x1 = 1938, y0 = 70, y1 = 950, cx = (x0 + x1) / 2, cy = (y0 + y1) / 2, w = x1 - x0, h = y1 - y0;
    g.fillStyle = '#0b0f0c'; g.beginPath(); g.roundRect(0, 0, 2048, 1024, 40); g.fill();
    g.fillStyle = '#021006'; g.fillRect(x0, y0, w, h);
    for (let i = 0; i <= 10; i++) { g.fillStyle = i === 5 ? 'rgba(90,255,130,.3)' : 'rgba(90,255,130,.13)'; g.fillRect(x0 + i * w / 10 - 1.5, y0, 3, h); }
    for (let j = 0; j <= 8; j++) { g.fillStyle = j === 4 ? 'rgba(90,255,130,.3)' : 'rgba(90,255,130,.13)'; g.fillRect(x0, y0 + j * h / 8 - 1.5, w, 3); }
    g.save(); g.beginPath(); g.rect(x0, y0, w, h); g.clip();
    const A = 150 + 25 * kick(t, 5);
    if (t < tH1) {
      // Y–T: from "Elon" the second trace drifts into the first's phase and height; on "both" they're one
      const m = easeInOut(clamp((t - tElon) / (tBoth - tElon + .05)));
      const trace = (yc, f, ph) => { const p = new Path2D(); for (let i = 0; i <= 200; i++) { const x = x0 + i / 200 * w, y = yc - A * Math.sin((x - x0) / w * TAU * 3 * f - t * 9 + ph); i ? p.lineTo(x, y) : p.moveTo(x, y); } return p; };
      if (t >= tElon) glowPath(g, trace(lerp(cy + 230, cy, m), lerp(1.7, 1, m), lerp(2.1, 0, m)), '#ffc830', 9, '#fff4c0');
      glowPath(g, trace(lerp(cy - 230, cy, m), 1, 0), '#40ff80', 9, '#e0ffe8');
    } else {
      // X–Y: one figure, closing on the second "hear" to a single line
      const q = easeInOut(clamp((t - tH1) / ((tH2 - tH1) * .85))), ratio = lerp(2, 1, clamp((t - tH1) / .12)), del = lerp(Math.PI / 2, 0, q), P = 1 + .1 * kick(t, 6);
      const p = new Path2D();
      for (let i = 0; i <= 300; i++) { const u = i / 300 * TAU, x = cx + Math.sin(u + t * 2) * 620 * P, y = cy - Math.sin(u * ratio + t * 2 * ratio + del) * 330 * P; i ? p.lineTo(x, y) : p.moveTo(x, y); }
      glowPath(g, p, q > .9 ? '#b0ff60' : '#40ff80', 10, '#f0fff0');
    }
    g.restore();
    text(g, 'CH1 SAM', x0 + 30, y0 + 60, { size: 44, font: FT, color: '#60ff90' });
    if (t >= tElon) text(g, 'CH2 ELON', x0 + 30, y0 + 120, { size: 44, font: FT, color: '#ffc830' });
    text(g, t < tH1 ? 'Y–T' : 'X–Y', x1 - 30, y1 - 30, { size: 44, font: FT, align: 'right', color: '#60ff90' });
    const xy = t >= tH1, lx = t - tH1;
    return {
      ro: xy ? [.2, 2.25, 5.3 - lx * .4] : [-1.3 + lt * .7, 2.05, 6.6 - lt * .3], ta: [0, 2.3, 0], fov: 1.5,
      skyA: '#010502', skyB: '#031006', acc: '#40ff80', fog: .025, floorCol: '#010302', grid: .15,
      panels: [card([0, 2.4, 0], 3.3, 1.65, xy ? 0 : .08, 0, 0, { tex: 0, gain: 1.5, glass: .6 })],
      light: { p: [0, 3, 3], c: '#60ff90', k: 3 + 3 * kick8(t, 5), vol: .4 },
      flash: xy && lx < .07 ? .18 : 0, flashCol: '#d0ffd8', exposure: pump(t),
    };
  });

  // ================================================================================================================================
  // V4.9 Trump's the guardrail (High IQ!): the Out Run road with its one gold guardrail. His post passes on a billboard; cut, and the
  // car brakes under a gantry: STRONG AND SMART / (HIGH IQ!) / PRESIDENT.
  // ================================================================================================================================
  const ROAD_L = 88, BAND = 3;
  function roadTex(g, D) {
    for (let j = Math.floor(D / BAND); ; j++) {
      const d0 = j * BAND - D, d1 = d0 + BAND; if (d0 > ROAD_L) break;
      const ya = 1024 * (1 - Math.min(ROAD_L, d1) / ROAD_L), yb = 1024 * (1 - Math.max(0, d0) / ROAD_L), odd = j & 1;
      g.fillStyle = odd ? '#6e6c7c' : '#5e5c6e'; g.fillRect(170, ya, 1708, yb - ya);
      g.fillStyle = odd ? '#f6f6f6' : '#e02830'; g.fillRect(0, ya, 170, yb - ya); g.fillRect(1878, ya, 170, yb - ya);
      if (odd) { g.fillStyle = '#ffffff'; g.fillRect(1000, ya, 48, yb - ya); }
    }
  }
  function railTex(g, D) {
    // (x: distance ahead; a gold W-beam on steel posts every 2.5)
    const px = x => x / ROAD_L * 1024;
    for (let d = -((D % 2.5) + 2.5) % 2.5; d < ROAD_L; d += 2.5) { if (d < 0) continue; g.fillStyle = '#5a6070'; g.fillRect(px(d) - 5, 150, 10, 362); g.fillStyle = '#9aa2b8'; g.fillRect(px(d) - 5, 150, 3, 362); }
    const gr = g.createLinearGradient(0, 40, 0, 250); gr.addColorStop(0, '#fff2b0'); gr.addColorStop(.3, '#ffcc30'); gr.addColorStop(.55, '#b07800'); gr.addColorStop(.75, '#ffd860'); gr.addColorStop(1, '#8a5a00');
    g.fillStyle = gr; g.fillRect(0, 40, 1024, 210);
  }
  const BILLBOARD = () => cached('billboard', 1024, 512, g => {
    g.fillStyle = '#20242e'; g.fillRect(210, 300, 44, 212); g.fillRect(770, 300, 44, 212);
    g.fillStyle = '#f4f2ec'; g.fillRect(20, 10, 984, 320); g.fillStyle = '#1a2a5a'; g.fillRect(34, 24, 956, 292);
    ['THE ONLY CONTROL', 'OR ‘GUARDRAILS’', 'THAT AI NEEDS IS A'].forEach((l, i) => text(g, l, 512, 112 + i * 92, { size: 80, font: 'Anton', align: 'center', color: '#ffffff', spacing: 3 }));
  });
  const GANTRY = () => cached('gantry', 1024, 512, g => {
    g.fillStyle = '#4a5060'; g.fillRect(44, 150, 40, 362); g.fillRect(940, 150, 40, 362); g.fillRect(44, 180, 936, 22);
    g.fillStyle = '#9aa2b4'; g.fillRect(44, 150, 10, 362); g.fillRect(940, 150, 10, 362);
    g.fillStyle = '#f0f0f0'; g.beginPath(); g.roundRect(150, 6, 724, 250, 18); g.fill();
    g.fillStyle = '#0c6a3a'; g.beginPath(); g.roundRect(160, 16, 704, 230, 12); g.fill();
    text(g, 'STRONG AND SMART', 512, 86, { size: 62, font: 'Anton', align: 'center', color: '#ffffff', spacing: 2 });
    text(g, '(HIGH IQ!)', 512, 160, { size: 66, font: 'Anton', align: 'center', color: '#ffd23a', spacing: 2 });
    text(g, 'PRESIDENT', 512, 230, { size: 62, font: 'Anton', align: 'center', color: '#ffffff', spacing: 2 });
  });
  mline('V4', 9, (t, s, E, ui) => {
    const W = W4(s), lt = t - s.start, tC = beatT(Math.round(bt(W[2].t0))), shot2 = t >= tC;
    // the car: cruising past the billboard; after the cut, braking hard under the gantry
    const v2 = x => lerp(24, 1.2, easeInOut(clamp(x / .78)));
    let D, a = 0;
    if (!shot2) D = 16 * lt;
    else { a = t - tC; D = 0; const n = 30; for (let i = 0; i < n; i++) D += v2((i + .5) / n * a) * a / n; }
    const brake = shot2 ? clamp((a - .05) / .3) * clamp(1 - (a - .6) / .3) : 0;
    const Dall = shot2 ? 300 + D : D;   // (the road's stripes run on from a different stretch after the cut)
    roadTex(MOD.panel(0), Dall);
    railTex(MOD.panel(2), Dall);
    const g1 = MOD.panel(1);
    let sign;
    if (!shot2) { g1.drawImage(BILLBOARD(), 0, 0); sign = card([4.4, 1.65, -(17 - D)], 3.3, 1.65, -.42, 0, 0, { tex: 1, gain: 1.25, glass: 0 }); }
    else { g1.drawImage(GANTRY(), 0, 0); sign = card([0, 1.8, -(16.5 - D)], 3.6, 1.8, 0, 0, 0, { tex: 1, gain: 1.3, glass: 0 }); }
    const bob = Math.sin(t * 31) * .012 * (shot2 ? 1 - brake : 1);
    return {
      ro: [shot2 ? .15 : -.35, 1.15 + bob - brake * .08, 0], ta: [shot2 ? .1 : .4, (shot2 ? 2.4 : .95) - brake * .3, -20], fov: shot2 ? 1.3 : 1.25, roll: shot2 ? 0 : Math.sin(Dall * .05) * .03,
      skyA: '#0c34b8', skyB: '#6aa8f0', acc: '#ffd23a', fog: .005,
      floorMode: 'checker', floorCol: '#145a18', floorCol2: '#1f8026', floorTile: BAND, floorOff: [0, -Dall],
      panels: [
        { c: [0, .015, -ROAD_L / 2], u: [2.7, 0, 0], v: [0, 0, -ROAD_L / 2], tex: 0, gain: 1.05, glass: 0 },
        { c: [-3.05, .38, -ROAD_L / 2], u: [0, 0, -ROAD_L / 2], v: [0, .38, 0], tex: 2, gain: 1.3, glass: 0 },
        sign,
      ],
      light: { p: [-6, 12, 4], c: '#fff4e0', k: 4, vol: 0 },
      flash: shot2 && a < .05 ? .14 : 0, exposure: 1.05,
    };
  });

  // ================================================================================================================================
  // V4.10 Bernie, Bannon share a pew: a chart of the one thing they agree on, REIN IN AI up, with left and right across (where each
  // comes from, and nothing else). BERNIE flies in from the left and BANNON from the right, and both land high on REIN IN AI; on
  // "share a pew" one level line, the pew, joins them across the aisle.
  // ================================================================================================================================
  mline('V4', 10, (t, s, E, ui) => {
    const W = W4(s), lt = t - s.start, tBe = W[0].t0, tBa = W[1].t0, tSh = W[2].t0, tPew = W[4].t0;
    const P = card([0, 2.45, 0], 3.9, 1.95, 0, 0, 0, { tex: 0, gain: 1.4, glass: .5 });
    const g = MOD.panel(0), X0 = 250, Y0 = 860, X1 = 1930, Y1 = 90, LY = 300, BX = 600, NX = 1560;
    g.fillStyle = 'rgba(20,8,26,.78)'; g.fillRect(0, 0, 2048, 1024);
    for (let x = X0 + 140; x < X1; x += 140) { g.fillStyle = 'rgba(210,180,255,.08)'; g.fillRect(x, Y1, 2, Y0 - Y1); }
    for (let y = Y0 - 110; y > Y1; y -= 110) { g.fillStyle = 'rgba(210,180,255,.08)'; g.fillRect(X0, y, X1 - X0, 2); }
    // the axes draw in, with their arrowheads
    const ax = easeOut(clamp(.3 + lt / .2)), ay = easeOut(clamp(.3 + lt / .22));
    const arrow = new Path2D();
    arrow.moveTo(X0, Y0); arrow.lineTo(X0 + (X1 - X0) * ax, Y0);
    arrow.moveTo(X0, Y0); arrow.lineTo(X0, Y0 - (Y0 - Y1) * ay);
    g.strokeStyle = '#f4ecff'; g.lineWidth = 8; g.lineCap = 'round'; g.stroke(arrow);
    g.fillStyle = '#f4ecff';
    if (ax > .98) { g.beginPath(); g.moveTo(X1 + 30, Y0); g.lineTo(X1 - 12, Y0 - 24); g.lineTo(X1 - 12, Y0 + 24); g.fill(); }
    if (ay > .98) { g.beginPath(); g.moveTo(X0, Y1 - 30); g.lineTo(X0 - 24, Y1 + 12); g.lineTo(X0 + 24, Y1 + 12); g.fill(); }
    g.save(); g.translate(X0 - 60, (Y0 + Y1) / 2); g.rotate(-Math.PI / 2); text(g, 'REIN IN AI', 0, 0, { size: 56, font: FT, align: 'center', color: '#ffe6a0', n: Math.ceil(clamp(.2 + lt / .2) * 10) }); g.restore();
    text(g, 'LEFT', X0 + 30, Y0 + 90, { size: 56, font: FT, color: '#ffe6a0', n: Math.ceil(clamp(.2 + lt / .2) * 4) });
    text(g, 'RIGHT', X1, Y0 + 90, { size: 56, font: FT, align: 'right', color: '#ffe6a0', n: Math.ceil(clamp(.2 + lt / .2) * 5) });
    // the pew: one level line, drawn from both of them on "share", meeting on "pew"
    if (t >= tSh) {
      const k = easeInOut(clamp((t - tSh) / (tPew - tSh + .04))), mid = (BX + NX) / 2, lit = t >= tPew ? .6 + .4 * kick(t, 5) : 1;
      const p = new Path2D(); p.moveTo(BX, LY); p.lineTo(lerp(BX, mid, k), LY); p.moveTo(NX, LY); p.lineTo(lerp(NX, mid, k), LY);
      glowPath(g, p, `rgba(255,200,70,${lit})`, 14, '#fff6d8');
      if (t >= tPew) { g.fillStyle = '#ffd050'; g.fillRect(X0 - 26, LY - 5, 52, 10); }
    }
    // BERNIE and BANNON: in from the edges, each landing on its name
    const spheres = [], flyIn = (t0, fromX, toX) => { const k = clamp((t - t0) / .34); return [lerp(fromX, toX, backOut(k, 1.1)), lerp(LY + 260, LY, easeOut(k)) - Math.sin(k * Math.PI) * 120]; };
    [['BERNIE', tBe, -700, BX, '#8ab8ff'], ['BANNON', tBa, 2750, NX, '#ff8aa4']].forEach(([nm, t0, from, to, col]) => {
      if (t < t0 - .02) return;
      const [x, y] = flyIn(t0, from, to), wp = onPanel(P, x, y, 2048, 1024);
      spheres.push([wp[0], wp[1], wp[2] + .32, .3 + .05 * kick(t, 6), col]);
      text(g, nm, x, y + 110, { size: 54, font: FT, align: 'center', color: '#ffffff', stroke: 8 });
    });
    // (in the assembly's hall: two rows of columns, warm, the chart hung between them)
    return {
      ro: add([Math.sin(lt * .6) * .6, 2.0 + lt * .1, 8.4 - lt * .45], hand(t, 1, 2)), ta: [0, 2.2, 0], fov: 1.45,
      skyA: '#0a0410', skyB: '#1e0c22', acc: '#ffc850', fog: .03, floorCol: '#060306', grid: 0,
      world: { kind: 'hall', p: [3.4, 5.4, 7.2, 1.3], col: '#3a3038', glowCol: '#ffc870', at: [0, 0, -.2], metal: .5 },
      panels: [P], spheres, sphCol: '#ffffff',
      light: { p: [0, 6.4, 1.5], c: '#ffe6c0', k: 7, vol: .9 }, dof: { k: .012, focus: 8.4 - lt * .45 },
      exposure: pump(t, .08) + (t >= tPew ? .12 * Math.exp(-(t - tPew) * 8) : 0),
    };
  });

  // ================================================================================================================================
  // V4.11 Claude builds Claude — now one in four!: a 2×2 grid in which DJ Clawd, in the one orange quadrant, builds the next grid,
  // forever (a Droste zoom); beside it Anthropic's index counts to 26%.
  // ================================================================================================================================
  mline('V4', 11, (t, s, E, ui) => {
    const lt = t - s.start, d = s.end - s.start;
    const g = MOD.panel(0), SQ = 1024;
    g.fillStyle = '#0a1a3a'; g.fillRect(0, 0, SQ, SQ);
    g.fillStyle = 'rgba(120,170,255,.12)';
    for (let x = 0; x < SQ; x += 32) g.fillRect(x, 0, 2, SQ);
    for (let y = 0; y < SQ; y += 32) g.fillRect(0, y, SQ, 2);
    // the grids: each one's top-right quadrant (Claude's) holds the next, 0.44 the size, zooming in toward their fixed point
    const rho = .44, cX = .53, cY = .03, S0 = 930, O = 47, FX = O + cX / (1 - rho) * S0, FY = O + cY / (1 - rho) * S0;
    const per = beatLen() * 2, Z = Math.pow(1 / rho, frac(lt / per));
    g.save(); g.beginPath(); g.rect(0, 0, SQ, SQ); g.clip();
    const builders = [];
    for (let k = -1; k < 10; k++) {
      const sz = S0 * Z * rho ** k, X = FX - cX / (1 - rho) * sz, Y = FY - cY / (1 - rho) * sz;
      if (sz < 5) break;
      if (X > SQ || Y > SQ || X + sz < 0 || Y + sz < 0) continue;
      const gp = sz * .02, q = sz / 2 - gp * 1.5;
      [[0, 0], [0, 1], [1, 1]].forEach(([i, j], n) => {
        const qx = X + gp + i * (q + gp), qy = Y + gp + j * (q + gp);
        g.fillStyle = '#16305e'; g.fillRect(qx, qy, q, q); g.fillStyle = '#2a4c8a'; g.fillRect(qx, qy, q, Math.max(1, q * .08));
        if (q > 40) for (let r = 0; r < 5; r++) { g.fillStyle = 'rgba(120,170,255,.45)'; g.fillRect(qx + q * .1, qy + q * (.22 + r * .14), q * (.3 + .5 * hash2(n, r)), Math.max(1, q * .045)); }
      });
      const qx = X + gp + (q + gp), qy = Y + gp, fw = Math.max(1, sz * .01);
      g.fillStyle = '#ff9a4a'; g.fillRect(qx - fw, qy - fw, q + 2 * fw, q + 2 * fw); g.fillStyle = '#2a1206'; g.fillRect(qx, qy, q, q);
      builders.push([qx, qy, q]);
    }
    // DJ Clawd in each orange quadrant, building the next grid (drawn innermost first, so each stands before the grid he builds)
    const kk = kick(t, 7);
    for (let i = builders.length - 1; i >= 0; i--) {
      const [qx, qy, q] = builders[i], u = q / 26;
      if (u < .7) continue;
      const gx = qx + q * .26, gy = qy + q * .98, hop = kk * u * .5;
      MOD.clawd(g, gx, gy, u, { hop, aL: .7 + .3 * kk, aR: 1, eyes: 'open' });
      const bx = gx + 6.2 * u, by = gy - 13 * u - hop - kk * u * 1.4;
      g.fillStyle = '#ff9a4a'; g.fillRect(bx - u * .3, by - u * .3, 4.6 * u, 4.6 * u); g.fillStyle = '#16305e'; g.fillRect(bx, by, 4 * u, 4 * u);
    }
    g.restore();
    g.strokeStyle = 'rgba(160,200,255,.6)'; g.lineWidth = 6; g.strokeRect(3, 3, SQ - 6, SQ - 6);
    // Anthropic's index
    const k = easeOut(clamp((lt - .08) / (d * .62))), pct = Math.round(lerp(1, 26, k));
    g.fillStyle = 'rgba(10,14,30,.82)'; g.fillRect(1080, 40, 940, 944);
    g.fillStyle = '#ff9a4a'; g.fillRect(1080, 40, 940, 8);
    text(g, 'R&D AUTOMATION INDEX', 1120, 136, { size: 50, font: FT, color: '#e8eeff' });
    text(g, 'FEB', 1120, 330, { size: 60, font: FT, color: 'rgba(210,220,255,.55)' });
    text(g, '<1%', 1400, 330, { size: 60, font: FT, color: 'rgba(210,220,255,.55)' });
    text(g, 'AUG', 1120, 640, { size: 60, font: FT, color: '#ffb070' });
    text(g, pct + '%', 1330, 720 + (pct === 26 ? -Math.exp(-(lt - .08 - d * .62) * 10) * 20 : 0), { size: 250, font: FT, color: MOD.chrome(g, 480, 720, ['#fff4e0', '#ffc080', '#e06020', '#7a2a08']), stroke: 12 });
    g.fillStyle = 'rgba(255,154,74,.25)'; g.fillRect(1120, 800, 860, 30); g.fillStyle = '#ff9a4a'; g.fillRect(1120, 800, 860 * pct / 100, 30);
    return {
      ro: [-.3 + lt * .25, 2.4, 8.1 - lt * .4], ta: [-.08, 2.25, 0], fov: 1.45,
      skyA: '#02050e', skyB: '#07102a', acc: '#ff9a4a', fog: .02, floorCol: '#020308', grid: .1,
      panels: [card([0, 2.6, 0], 3.9, 1.95, 0, 0, 0, { tex: 0, gain: 1.35, glass: .6 })],
      light: { p: [-.3, 4.3, 1.5], c: '#ff9a4a', k: 4 + 3 * kk, vol: .5 },
      exposure: pump(t),
    };
  });

  // ================================================================================================================================
  // V4.12 Chatbot nearly starts a war!: a radar table. The sweep passes a ship on "Chatbot": NUCLEAR? flickers, the alarm strobes
  // red and three planes close in; on the next pass it reads ABORT and they turn back.
  // ================================================================================================================================
  mline('V4', 12, (t, s, E, ui) => {
    const W = W4(s), lt = t - s.start, rev = beatLen() * 2, t1 = W[0].t0, t2 = t1 + rev;
    const shipA = -.62, sweepA = (t - t1) / rev * TAU + shipA;
    const alarm = t >= t1 && t < t2, strobe = alarm && (Math.floor(bt(t) * 2) & 1);
    const g = MOD.panel(0), cx = 1024, cy = 512, R = 460;
    g.fillStyle = 'rgba(2,12,5,.9)'; g.beginPath(); g.arc(cx, cy, R + 36, 0, TAU); g.fill();
    // the sweep's afterglow, trailing the beam
    const cg = g.createConicGradient(sweepA, cx, cy);
    cg.addColorStop(0, 'rgba(40,255,110,0)'); cg.addColorStop(.62, 'rgba(40,255,110,0)'); cg.addColorStop(.97, 'rgba(60,255,120,.42)'); cg.addColorStop(1, 'rgba(160,255,190,.75)');
    g.fillStyle = cg; g.beginPath(); g.arc(cx, cy, R, 0, TAU); g.fill();
    g.strokeStyle = 'rgba(80,255,130,.35)'; g.lineWidth = 3;
    for (let r = R / 4; r <= R + 1; r += R / 4) { g.beginPath(); g.arc(cx, cy, r, 0, TAU); g.stroke(); }
    g.beginPath(); g.moveTo(cx - R, cy); g.lineTo(cx + R, cy); g.moveTo(cx, cy - R); g.lineTo(cx, cy + R); g.stroke();
    for (let i = 0; i < 72; i++) { const a = i / 72 * TAU, r1 = R + (i % 6 ? 14 : 28); g.beginPath(); g.moveTo(cx + Math.cos(a) * (R + 4), cy + Math.sin(a) * (R + 4)); g.lineTo(cx + Math.cos(a) * r1, cy + Math.sin(a) * r1); g.stroke(); }
    g.strokeStyle = strobe ? '#ff2a2a' : 'rgba(170,190,180,.6)'; g.lineWidth = strobe ? 16 : 8; g.beginPath(); g.arc(cx, cy, R + 34, 0, TAU); g.stroke();
    const beam = new Path2D(); beam.moveTo(cx, cy); beam.lineTo(cx + Math.cos(sweepA) * R, cy + Math.sin(sweepA) * R);
    glowPath(g, beam, '#50ff90', 6, '#eaffef');
    // blips light as the sweep passes and fade until the next pass
    const lit = (x, y) => { const a = Math.atan2(y - cy, x - cx), behind = (((sweepA - a) % TAU) + TAU) % TAU; return Math.exp(-behind * 1.1); };
    const sx = cx + Math.cos(shipA) * R * .62, sy = cy + Math.sin(shipA) * R * .62, ls = lit(sx, sy);
    g.fillStyle = alarm ? `rgba(255,${Math.round(60 + 80 * ls)},60,${.5 + .5 * ls})` : `rgba(120,255,160,${.4 + .6 * ls})`; g.beginPath(); g.arc(sx, sy, 16 + 8 * ls, 0, TAU); g.fill();
    // three planes: sent in when the ship reads NUCLEAR?, recalled on ABORT
    for (let i = 0; i < 3 && t >= t1; i++) {
      const a0 = shipA + 2.3 + i * .45, go = clamp((t - t1) / (rev * 1.05)), back = clamp((t - t2) / rev);
      const r = lerp(R - 30, 70, easeOut(go) * .8) + (R - 70) * easeIn(back) * .8, px = sx + Math.cos(a0) * r * .9, py = sy + Math.sin(a0) * r * .9;
      const hd = a0 + (t < t2 ? Math.PI : 0), l = .5 + .5 * lit(px, py), sz = 40;
      g.fillStyle = alarm ? `rgba(255,120,110,${l})` : `rgba(170,255,190,${l})`;
      g.beginPath(); g.moveTo(px + Math.cos(hd) * sz, py + Math.sin(hd) * sz); g.lineTo(px + Math.cos(hd + 2.5) * sz * .75, py + Math.sin(hd + 2.5) * sz * .75); g.lineTo(px + Math.cos(hd - 2.5) * sz * .75, py + Math.sin(hd - 2.5) * sz * .75); g.fill();
    }
    // the ship's label: NUCLEAR?, flickering; then ABORT
    if (t >= t1) {
      const lx = sx + 40, ly = sy - 120;
      g.strokeStyle = alarm ? '#ff6060' : '#e8fff0'; g.lineWidth = 4; g.beginPath(); g.moveTo(sx + 14, sy - 14); g.lineTo(lx, ly + 40); g.stroke();
      if (!alarm) { g.fillStyle = '#04140a'; g.fillRect(lx - 10, ly - 40, 330, 96); text(g, 'ABORT', lx + 8, ly + 38, { size: 80, font: FT, color: '#ffffff' }); }
      else if (Math.floor(t * 18) % 4) { g.fillStyle = 'rgba(90,0,0,.85)'; g.fillRect(lx - 10, ly - 40, 520, 96); text(g, 'NUCLEAR?', lx + 8, ly + 38, { size: 80, font: FT, color: '#ff4a4a' }); }
    }
    const ab = t >= t2;
    return {
      ro: ab ? [.3, 4.7, 5.9 - (t - t2) * .3] : [Math.sin(lt * .5) * .6, 3.5, 6.6 - lt * .3], ta: ab ? [.2, 1.55, 0] : [0, 1.4, 0], fov: 1.45,
      skyA: '#010402', skyB: alarm ? (strobe ? '#240404' : '#0c0202') : '#020a04', acc: alarm ? '#ff2020' : '#40ff80', fog: .025, floorCol: '#020302', grid: .1,
      panels: [card([0, 1.75, 0], 3.4, 1.7, 0, -.5, 0, { tex: 0, gain: 1.5, glass: alarm ? 1 : .5 })],
      // (the operations room round the table, its strips gone red with the alarm)
      world: { kind: 'hall', p: [3, 5.2, 5.4, alarm ? (strobe ? 3 : .8) : 1], col: '#1a2220', glowCol: alarm ? '#ff2a2a' : '#50ff90', at: [0, 0, -.5], metal: .6 },
      light: { p: [0, 4, 2], c: alarm ? '#ff3030' : '#50ff90', k: alarm ? 5 + 7 * (strobe ? 1 : 0) : 3, vol: alarm ? .8 : .3 },
      flash: alarm && strobe ? .06 : 0, flashCol: '#ff4040', exposure: pump(t, alarm ? .14 : .06),
    };
  });

  // ================================================================================================================================
  // V4.13 Trump: It's "Super," by decree!: the demo's one digitized picture scans in, line by line; beside it a split-flap board
  // under HEREINAFTER / OFFICIALLY CALLED flips ARTIFICIAL, letter by letter, to SUPER, over INTELLIGENCE.
  // ================================================================================================================================
  const PORTRAIT_C = () => cached('portrait', PORTRAIT.w, PORTRAIT.h, g => {
    const P = PORTRAIT, im = g.createImageData(P.w, P.h), rgb = P.pal.map(h => [1, 3, 5].map(i => parseInt(h.slice(i, i + 2), 16)));
    for (let i = 0; i < P.w * P.h; i++) { const c = rgb[P.px[i]]; im.data[i * 4] = c[0]; im.data[i * 4 + 1] = c[1]; im.data[i * 4 + 2] = c[2]; im.data[i * 4 + 3] = 255; }
    g.putImageData(im, 0, 0);
  });
  const FLAPS = ' ABCDEFGHIJKLMNOPQRSTUVWXYZ';
  function flapCell(g, x, y, w, h, from, to, t0, t, fd) {
    const a = FLAPS.indexOf(from), b = FLAPS.indexOf(to), n = (b - a + FLAPS.length) % FLAPS.length;
    const k = n ? clamp((t - t0) / fd, 0, n) : 0, i = Math.floor(k), f = k - i;
    const cur = FLAPS[(a + i) % FLAPS.length], nxt = FLAPS[(a + i + 1) % FLAPS.length], flipping = i < n && t >= t0;
    const half = (c, top, x0 = x, y0 = y, hh = h) => {
      g.save(); g.beginPath(); top ? g.rect(x, y, w, h / 2 - 2) : g.rect(x, y + h / 2 + 2, w, h / 2 - 2); g.clip();
      g.fillStyle = top ? '#262a34' : '#1c2028'; g.fillRect(x, y, w, h);
      if (c !== ' ') text(g, c, x + w / 2, y + h * .72, { size: h * .7, font: FT, align: 'center', color: '#f4f0e4' });
      g.restore();
    };
    if (!flipping) { half(cur, true); half(cur, false); }
    else {
      // the next letter above, the old one below, and the flap falling between them
      half(nxt, true); half(cur, false);
      if (f < .5) { const fh = (h / 2) * (1 - f * 2); g.save(); g.beginPath(); g.rect(x, y + h / 2 - fh, w, fh); g.clip(); g.fillStyle = '#30343e'; g.fillRect(x, y, w, h); if (cur !== ' ') text(g, cur, x + w / 2, y + h * .72, { size: h * .7, font: FT, align: 'center', color: '#f4f0e4' }); g.restore(); }
      else { const fh = (h / 2) * (f * 2 - 1); g.fillStyle = '#343844'; g.fillRect(x, y + h / 2 + 2, w, fh); }
    }
    g.fillStyle = '#05060a'; g.fillRect(x, y + h / 2 - 2, w, 4);
  }
  mline('V4', 13, (t, s, E, ui) => {
    const W = W4(s), lt = t - s.start;
    // the portrait, scanning in as a VGA viewer loads it (the texture is stretched to the panel's 3:4)
    const g1 = MOD.panel(1), rows = Math.round(PORTRAIT.h * easeOut(clamp(lt / .45))), sy = 512 / PORTRAIT.h;
    g1.save(); g1.imageSmoothingEnabled = false;
    if (rows > 0) g1.drawImage(PORTRAIT_C(), 0, 0, PORTRAIT.w, rows, 0, 0, 1024, rows * sy);
    if (rows < PORTRAIT.h) { g1.fillStyle = '#ffffff'; g1.fillRect(0, rows * sy, 1024, 5); }
    g1.strokeStyle = '#c8b070'; g1.lineWidth = 10; g1.strokeRect(5, 5, 1014, 502);
    g1.restore();
    // the decree, on a split-flap board
    const g = MOD.panel(0);
    g.fillStyle = 'rgba(14,10,6,.9)'; g.fillRect(0, 0, 2048, 1024);
    g.fillStyle = '#e0b040'; g.fillRect(0, 0, 2048, 10); g.fillRect(0, 1014, 2048, 10);
    text(g, 'HEREINAFTER', 1024, 130, { size: 82, font: FT, align: 'center', color: '#f0c860' });
    text(g, 'OFFICIALLY CALLED', 1024, 240, { size: 82, font: FT, align: 'center', color: '#f0c860' });
    const cw = 146, ch = 220, gap = 14, bx = 1024 - (12 * cw + 11 * gap) / 2, r1 = 305, r2 = r1 + ch + 26;
    const A = ' ARTIFICIAL ', B = '   SUPER    ', I = 'INTELLIGENCE', tS = W[1].t0 - .25, fd = .015;
    for (let i = 0; i < 12; i++) {
      flapCell(g, bx + i * (cw + gap), r1, cw, ch, A[i], B[i], tS + i * .028, t, fd);
      flapCell(g, bx + i * (cw + gap), r2, cw, ch, I[i], I[i], 0, t, fd);
    }
    const sup = t >= W[2].t0 ? 1 : 0;
    return {
      ro: [.2 + Math.sin(lt * .7) * .25 + sup * .1, 2.35, 7.6 - lt * .3 - sup * .5], ta: [.15 + sup * .1, 2.22, 0], fov: 1.42,
      skyA: '#0a0604', skyB: '#221406', acc: '#ffc040', fog: .025, floorCol: '#040302', grid: .06,
      world: { kind: 'hall', p: [3.4, 5.6, 7, .9], col: '#2e2618', glowCol: '#ffc860', at: [0, 0, -.4], metal: .6 },
      dof: { k: .01, focus: 7.6 - lt * .3 },
      panels: [
        card([-2.55, 2.35, .25], 1.2, 1.6, .22, 0, 0, { tex: 1, gain: 1.25, glass: .4 }),
        card([1.25, 2.35, 0], 2.6, 1.3, -.1, 0, 0, { tex: 0, gain: 1.35, glass: .4 }),
      ],
      light: { p: [0, 5, 3], c: '#ffd070', k: 4, vol: .4 },
      exposure: pump(t, .06),
    };
  });

  // ================================================================================================================================
  // V4.14 "Artificial"? Fake to me!: ARTIFICIAL as an extruded chrome logo; on "Fake" its depth turns out to be painted on: it turns
  // edge-on, paper-thin, and flops flat onto the floor like the sheet it is.
  // ================================================================================================================================
  mline('V4', 14, (t, s, E, ui) => {
    const W = W4(s), lt = t - s.start, tF = W[1].t0, a = t - tF;
    const S = MOD.shapeText('ARTIFICIAL'), hy = .44;
    const sway = x => Math.sin((x - s.start) * 2.8) * .36 - .12;
    let depth = .34, yaw = sway(t), pitch = -.04, P = [0, 2.0, 0];
    if (a >= 0) {
      depth = lerp(.34, .003, easeOut(clamp(a / .07)));
      const k = easeInOut(clamp(a / .2));
      yaw = lerp(sway(tF), Math.PI / 2, k);
      // …then, flat as paper, it drops
      const f = easeIn(clamp((a - .2) / .2));
      yaw = lerp(yaw, 0, f); pitch = lerp(pitch, -Math.PI / 2, f);
      P = [0, lerp(2.0, .01, f), lerp(0, .6, f)];
    }
    return {
      ro: [Math.sin(lt * .8) * .35, 2.35 + (a > 0 ? clamp((a - .2) / .3) * .9 : 0), 7.2 - lt * .3], ta: [0, a > .2 ? lerp(1.95, 1.2, clamp((a - .2) / .3)) : 1.95, 0], fov: 1.5,
      skyA: '#120204', skyB: '#300608', acc: '#ff2a2a', fog: .018, floorCol: '#060203',
      sky: { mode: 'rays', k: .9, col: '#ff8060' },
      dof: { k: .01, focus: 7.2 - lt * .3 },
      shape: { key: 'ARTIFICIAL', src: S, p: P, rot: rotYX(yaw, pitch), s: [hy * S.aspect, hy, depth], col: '#d8d6e2', rim: '#ffe0d0', metal: .7 },
      light: { p: [1.5, 4.2, 5], c: '#ffd8c8', k: 6 + 3 * kick8(t, 5), vol: .5 },
      flash: (lt < .05 ? .08 : 0) + (a >= 0 && a < .05 ? .06 : 0), flashCol: '#ffd0c0', exposure: pump(t),
    };
  });

  // ================================================================================================================================
  // V4.15 Ten days after "pace" — surprise!: a desk calendar flips SEP 12 (with "pace" circled) to SEP 22; on "surprise" it slides
  // aside in a burst, and two releases land 90 minutes apart: OPUS 5.5 (Anthropic), GPT-6 SOL & LUNA (OpenAI).
  // ================================================================================================================================
  function calPage(g, n, back) {
    g.save(); g.setTransform(1024 / 440, 0, 0, 1, 0, 0);   // (drawn in 440 × 512, the page's own proportions)
    if (back) { g.fillStyle = '#cfcad8'; g.fillRect(0, 0, 440, 512); g.restore(); return; }
    g.fillStyle = '#f6f4fa'; g.fillRect(0, 0, 440, 512);
    g.fillStyle = '#d0202a'; g.fillRect(0, 0, 440, 110);
    text(g, 'SEP', 220, 86, { size: 70, font: FT, align: 'center', color: '#ffffff' });
    text(g, String(n), 220, 390, { size: 250, font: 'Anton', align: 'center', color: '#1a1420' });
    text(g, '2026', 220, 480, { size: 38, align: 'center', color: '#6a6078' });
    if (n === 12) {
      text(g, 'pace', 360, 470, { size: 34, align: 'center', color: '#d0202a' });
      g.strokeStyle = '#d0202a'; g.lineWidth = 4; g.beginPath(); g.ellipse(360, 458, 58, 30, -.1, 0, TAU); g.stroke();
    }
    g.fillStyle = 'rgba(0,0,0,.2)'; g.fillRect(0, 506, 440, 6);
    g.restore();
  }
  mline('V4', 15, (t, s, E, ui) => {
    const W = W4(s), lt = t - s.start, t0 = W[0].t0 - .12, tSur = W[5].t0, fd = (W[3].t0 + .05 - t0) / 10;
    const kf = (t - t0) / fd, i = clamp(Math.floor(kf), 0, 10), f = kf - Math.floor(kf), flipping = kf >= 0 && i < 10;
    const slide = easeInOut(clamp((t - tSur + .04) / .2)), H = [lerp(0, -2.5, slide), 3.45, lerp(.3, -.2, slide)], hh = 1.1, hw = .95;
    const under = kf < 0 ? 12 : Math.min(22, 12 + i + (flipping ? 1 : 0));
    calPage(MOD.panel(2), under, false);
    const panels = [card([H[0], H[1] - hh, H[2] - .02], hw, hh, 0, 0, 0, { tex: 2, gain: 1.2, glass: 0 })];
    if (flipping) {
      const th = easeIn(f) * Math.PI, g1 = MOD.panel(1);
      calPage(g1, 12 + i, th > Math.PI / 2);
      const v = rot([0, hh, 0], 0, -th), c = [H[0] - v[0], H[1] - v[1], H[2] - v[2]];
      panels.push({ c, u: [hw, 0, 0], v, tex: 1, gain: 1.2 - .4 * Math.sin(th), glass: 0 });
    }
    const spheres = [];
    for (let r = 0; r < 6; r++) spheres.push([H[0] - .72 + r * .288, H[1], H[2] + .02, .07, '#d8dce8']);
    let fl = 0, halo = null;
    if (t >= tSur) {
      const a = t - tSur;
      // the burst: a ring of light out of the calendar
      halo = { p: [H[0] + .1, H[1] - hh, H[2] + .1], n: [0, 0, 1], R: .5 + a * 10, r: .04 + a * .12, k: 3 * Math.exp(-a * 5), col: '#ffd8a0' };
      fl = clamp(1 - a / .1) * .16;
      const g0 = MOD.panel(0), k1 = clamp(a / .09), k2 = clamp((a - .13) / .09);
      g0.fillStyle = 'rgba(10,6,20,.7)'; g0.fillRect(0, 0, 2048, 1024);
      if (k1 > 0) {
        text(g0, 'ANTHROPIC', 80, 130, { size: 60, font: FT, color: '#ffb070' });
        fit(g0, 'OPUS 5.5', 70, 360 - (1 - backOut(k1)) * 50, 1900, { size: 230, font: FT, color: MOD.chrome(g0, 180, 360, ['#fff4e0', '#ffc080', '#e06020', '#7a2a08']), stroke: 14 });
      }
      if (k2 > 0) {
        text(g0, '+90 MIN', 80, 510, { size: 72, font: FT, color: '#ffd050', alpha: k2 });
        text(g0, 'OPENAI', 80, 650, { size: 60, font: FT, color: '#d8e0f0' });
        fit(g0, 'GPT-6 SOL & LUNA', 70, 860 - (1 - backOut(k2)) * 50, 1910, { size: 150, font: FT, color: MOD.chrome(g0, 740, 860, ['#ffffff', '#e0e6f4', '#8a96b8', '#3a4460']), stroke: 12 });
      }
      panels.push(card([1.45, 2.3, .45], 2.5, 1.25, -.1, 0, 0, { tex: 0, gain: 1.45, glass: .5, alpha: clamp(a / .05) }));
    }
    return {
      ro: [slide * .3, 2.35, 6.3 + slide * .5 - lt * .15], ta: [slide * .3, 2.3, 0], fov: 1.45,
      skyA: '#06040e', skyB: '#1a1030', acc: '#8a74d0', fog: .02, floorCol: '#040308', grid: .08,
      panels, spheres, sphCol: '#d8dce8', halo, dof: { k: .012, focus: 6.3 + slide * .5 - lt * .15 },
      light: { p: [0, 5, 4], c: '#ffffff', k: 4, vol: .3 },
      flash: fl, flashCol: '#ffe0c0', exposure: pump(t, t >= tSur ? .14 : .06),
    };
  });

  // ================================================================================================================================
  // V4.16 Opus 5.5: "Hi, guys!": the intro's tracker again, OPUS 5.5 loading as instrument 04; on "Hi," DJ Clawd pops up in front
  // of it with 5.5 on his headphones and waves, sheepishly: the one time the mascot acts.
  // ================================================================================================================================
  const NOTES = ['C-', 'C#', 'D-', 'D#', 'E-', 'F-', 'F#', 'G-', 'G#', 'A-', 'A#', 'B-'];
  const CHANNELS = ['KICK', 'BASS', 'STAB', 'LEAD', 'TOKEN', 'SOFTMAX'];
  function cellAt(row, ch) {
    const r = row & 63;
    if (ch === 0) return r % 4 === 0 ? 'C-2 01 40' : '··· ·· ··';
    if (ch === 1) return r % 4 === 2 ? `${['A-', 'A-', 'F-', 'G-'][(r >> 4) & 3]}2 02 38` : '··· ·· ··';
    if (ch === 2) return [3, 6, 10, 14].includes(r % 16) ? `${['A-', 'C-', 'E-'][r % 3]}4 03 30` : '··· ·· ··';
    if (ch === 3) { const m = [0, 3, 7, 10, 12, 10, 7, 3], nn = 9 + m[(r >> 1) % 8]; return r % 2 === 0 ? `${NOTES[nn % 12]}${5 + ((nn / 12) | 0)} 04 3F` : '··· ·· ··'; }
    if (ch === 4) return r % 2 === 1 ? `${NOTES[(r * 5) % 12]}3 05 2${r % 10}` : '··· ·· ··';
    return '··· ·· ··';
  }
  mline('V4', 16, (t, s, E, ui) => {
    const W = W4(s), lt = t - s.start, tHi = W[2].t0, tGuys = W[3].t0, tLoad = W[0].t0;
    // the tracker: a row every sixteenth, the playing row on a copper bar
    const g = MOD.panel(0), row = bt(t) * 4, r0 = Math.floor(row), fr = row - r0, lh = 46, cy = 560;
    g.fillStyle = 'rgba(6,6,16,.9)'; g.fillRect(0, 0, 2048, 1024);
    const bar = g.createLinearGradient(0, cy - 30, 0, cy + 22); bar.addColorStop(0, 'rgba(255,154,74,0)'); bar.addColorStop(.5, 'rgba(255,154,74,.42)'); bar.addColorStop(1, 'rgba(255,154,74,0)');
    g.fillStyle = bar; g.fillRect(0, cy - 36, 2048, 64);
    g.font = `34px ${FM}`;
    for (let i = -10; i <= 9; i++) {
      const y = Math.round(cy + (i - fr) * lh); if (y < 150 || y > 1010) continue;
      const rr = r0 + i, lv = i === 0 ? 1 : .55 - Math.abs(i) * .035;
      g.globalAlpha = clamp(lv); g.fillStyle = '#b8c0d8'; g.fillText(String(rr & 63).padStart(2, '0'), 40, y);
      CHANNELS.forEach((c, ch) => { g.fillStyle = ch === 3 ? '#ffa860' : ch === 4 ? '#6ae8ff' : ch === 5 ? '#ff8ad8' : '#c8d0e8'; g.fillText(cellAt(rr, ch), 130 + ch * 318, y); });
    }
    g.globalAlpha = 1;
    g.fillStyle = 'rgba(20,20,40,.95)'; g.fillRect(0, 0, 2048, 130);
    CHANNELS.forEach((c, ch) => {
      const x = 130 + ch * 318, v = ch === 0 ? kick(t, 5) : ch === 3 ? .5 + .5 * kick8(t, 4) : ch >= 4 ? vox(t) * (ch === 4 ? 1 : .2) : .4 + .3 * kick8(t + ch * .1, 6);
      text(g, c, x, 56, { size: 36, font: FT, color: ch === 3 ? '#ffa860' : '#c8d0e8' });
      g.fillStyle = 'rgba(200,210,240,.15)'; g.fillRect(x, 80, 260, 22); g.fillStyle = ch === 3 ? '#ff9a4a' : '#6ae8ff'; g.fillRect(x, 80, 260 * clamp(v), 22);
    });
    // Opus 5.5 loads, as the lead's instrument
    const ld = clamp((t - tLoad) / (tHi - tLoad - .12)), g2 = MOD.panel(2);
    g2.fillStyle = 'rgba(12,10,20,.92)'; g2.fillRect(0, 0, 1024, 512);
    g2.fillStyle = 'rgba(255,154,74,.55)'; g2.fillRect(0, 0, 1024, 70);
    text(g2, 'LOADING INSTRUMENT 04', 30, 50, { size: 36, font: FT, color: '#fff4e8' });
    text(g2, 'OPUS 5.5', 512, 250, { size: 130, font: FT, align: 'center', color: MOD.chrome(g2, 150, 250, ['#fff4e0', '#ffc080', '#e06020', '#7a2a08']), stroke: 10 });
    g2.fillStyle = 'rgba(255,200,160,.18)'; g2.fillRect(60, 330, 904, 70); g2.fillStyle = `rgba(255,154,74,${.8 + .2 * kick8(t, 5)})`; g2.fillRect(60, 330, 904 * ld, 70);
    text(g2, ld >= 1 ? 'OK' : Math.round(ld * 100) + '%', 512, 385, { size: 48, font: FT, align: 'center', color: '#1a0c04' });
    const panels = [card([0, 2.55, -1.2], 4.3, 2.15, 0, 0, 0, { tex: 0, gain: 1.2, glass: .4 }), card([-2.3, 3.45, .5], 1.4, .7, .2, 0, 0, { tex: 2, gain: 1.4, glass: .6 })];
    // "Hi, guys!": he pops up in front, and waves
    let fl = 0;
    if (t >= tHi - .06) {
      const a = t - tHi + .06, up = backOut(clamp(a / .24)), g1 = MOD.panel(1), u = 31;
      const gx = 330, gy = 505 + (1 - up) * 420, hop = kick(t, 9) * 6, top = gy - hop - 8 * u;
      MOD.clawd(g1, gx, gy, u, { eyes: frac(a * .7) < .88 ? 'happy' : 'closed', aL: .1, aR: 0, hop });
      // a sheepish blush
      g1.fillStyle = 'rgba(255,120,150,.75)'; for (const sd of [-1, 1]) g1.fillRect(gx + sd * 2.3 * u - u, top + 3.3 * u, 2 * u, .6 * u);
      // the wave: his right arm up, swinging (behind his headphones)
      const th = .75 + .42 * Math.sin(a * 2.4 * TAU), sx = gx + 6 * u, sy = top + 3.4 * u, L = 4.4 * u, hx = sx + Math.sin(th) * L, hy = sy - Math.cos(th) * L;
      g1.lineCap = 'square'; g1.strokeStyle = '#9b3114'; g1.lineWidth = 2 * u; g1.beginPath(); g1.moveTo(sx, sy); g1.lineTo(hx, hy); g1.stroke();
      g1.strokeStyle = '#d97757'; g1.lineWidth = 1.5 * u; g1.beginPath(); g1.moveTo(sx, sy); g1.lineTo(hx, hy); g1.stroke();
      g1.save(); g1.translate(hx, hy); g1.rotate(th); g1.fillStyle = '#9b3114'; g1.fillRect(-1.3 * u, -2.3 * u, 2.6 * u, 2.6 * u); g1.fillStyle = '#e8906a'; g1.fillRect(-1.05 * u, -2.05 * u, 2.1 * u, 2.1 * u); g1.restore();
      // 5.5 on his headphones
      for (const sd of [-1, 1]) {
        const bx = gx + sd * 5.6 * u, by = top + 1.4 * u;
        g1.fillStyle = '#ff9a4a'; g1.beginPath(); g1.arc(bx, by, 1.2 * u, 0, TAU); g1.fill(); g1.lineWidth = 5; g1.strokeStyle = '#3c4878'; g1.stroke();
        text(g1, '5.5', bx, by + .34 * u, { size: Math.round(.95 * u), font: '"Archivo Black"', align: 'center', color: '#1a0c04' });
      }
      if (a > .12) {
        const msg = t >= tGuys ? 'Hi, guys!' : 'Hi,', bx = 590, by = 60;
        g1.fillStyle = '#f4f4f8'; g1.beginPath(); g1.roundRect(bx, by, 420, 150, 30); g1.fill();
        g1.beginPath(); g1.moveTo(bx + 40, by + 140); g1.lineTo(bx + 110, by + 140); g1.lineTo(bx - 50, by + 220); g1.fill();
        g1.font = '80px "Archivo Black"'; const sz = Math.min(80, Math.floor(80 * 356 / g1.measureText('Hi, guys!').width));
        text(g1, msg, bx + 32, by + 75 + sz * .36, { size: sz, font: '"Archivo Black"', color: '#101018' });
      }
      panels.push(card([-.3, 2.42, 1.6], 2.3, 1.15, .08, 0, 0, { tex: 1, gain: 1.6, glass: 0 }));
      fl = a > .06 && a < .12 ? .12 : 0;
    }
    return {
      // (cut in to the loading box on the beat of "5.5", back out as he pops up)
      ...(t >= beatT(Math.round(bt(W[1].t0))) && t < tHi - .08
        ? { ro: [-1.7 + (t - W[1].t0) * .12, 3.3, 3.55 - (t - W[1].t0) * .2], ta: [-2.3, 3.36, .5], fov: 1.45 }
        : { ro: [Math.sin(lt * .5) * .5 - .2, 2.4, 7.4 - lt * .3], ta: [0, 2.45, 0], fov: 1.45 }),
      skyA: '#04040c', skyB: '#0c0a1e', acc: '#ff9a4a', fog: .025, floorCol: '#030208', grid: .1,
      // (the party's hall, its strips in Clawd orange pumping with the kick)
      world: { kind: 'hall', p: [3, 5.6, 6.4, 1 + 2.5 * kick(t, 6)], col: '#1e1c26', glowCol: '#ff9a4a', at: [0, 0, -1.2], metal: .6 },
      panels,
      light: { p: [0, 4.6, 3.2], c: '#ffd0a0', k: 5 + 2 * kick(t, 6), vol: .6 },
      flash: fl, flashCol: '#ffe0c0', exposure: pump(t, .06),
    };
  });

})();

;
// ---- styles/demoscene/modern/m09_outro.js ----
// modern/m09_outro.js: the end part in the modern engine (versions A and B). A 64k intro's end scroller: the FRONTIER CREW logo in
// chrome over a glossy floor under a slow starfield, and the greetings rolling up a tilted glass sheet, each name lighting magenta
// as it crosses the reading line; then the special greets and the credits on the same roll, and the demo exits to DOS, crisp text
// mode, with its message and a blinking cursor as the music ends. The lists are ch/p09_outro.js's, names exactly as there, handles
// and the agents' names in their own case.
(() => {
  const { text } = MOD;
  const GREETZ = ['OPENAI', 'GOOGLE DEEPMIND', 'ANTHROPIC', 'META', 'XAI', 'DEEPSEEK', 'HUGGING FACE', 'NVIDIA', 'METR', 'EPOCH AI',
    'MIRI', 'FLI', 'SSI', 'THINKING MACHINES', 'MOLTBOOK', 'OPENCLAW', 'GWERN'];
  // the agents on the board, by the names they gave themselves (as METR reported them, in their own case)
  const AGENTS = ['PHASEONE[big]', 'PHASEONE10841', 'JAN183411', 'LILY', '38148c'];
  // (handles keep their case)
  const SPECIAL = ['@donaldjewkes', '@pleometric', '@_mexicat', '@AndrewM_Webb', '@LuisBizarro', '@_brightmirror', '@slimer48484', '@other__reality', '@tautologer'];
  const CREDITS = [['', 'Softmax feat. MC Token'], ['LYRICS', 'DOMENIC & CLAUDE'], ['MUSIC', 'SUNO V6'], ['VIDEO', 'CLAUDE OPUS 5.5'], ['', 'SEPTEMBER 2026']];
  // the roll's rows, top to bottom, and their heights in the sheet's texels
  const ROWS = [
    ...GREETZ.map(g => ['greet', g]), ...AGENTS.map(g => ['agent', g]), ['gap'], ['head', 'SPECIAL GREETS TO'], ...SPECIAL.map(h => ['handle', h]), ['gap'], ['gap'],
    ...CREDITS.map(([a, b]) => ['credit', b, a]),
  ];
  const HGT = { greet: 116, agent: 106, handle: 106, head: 112, gap: 60, credit: 152 };
  const YS = (() => { let y = 0; return ROWS.map(r => { const y0 = y; y += HGT[r[0]]; return y0 + HGT[r[0]] / 2; }); })();
  const BAND = 560;   // the reading line, in the sheet's texels
  const MAGC = ['#ffffff', '#ffd0ef', '#ff4fb4', '#8a0f60'], STEELC = ['#ffffff', '#d6e2ff', '#7d93d8', '#2c3a78'], ORANGEC = ['#fff6e8', '#ffd2a0', '#e8793a', '#7a2c10'];

  // ---- the exit: 40-column text mode, 16 × 16 cells (the demo's 8×8 font, doubled) on a 640 × 360 canvas, shown ×3 ----
  let _tm = null;
  const CGA = { 3: '#00aaaa', 7: '#aaaaaa', 11: '#55ffff', 15: '#ffffff' };
  function dos(ui, k) {
    const c = _tm ?? (_tm = makeCanvas(640, 360)), g = c.getContext('2d');
    g.fillStyle = '#000'; g.fillRect(0, 0, 640, 360);
    const put = (col, row, str, fg) => {
      g.fillStyle = CGA[fg];
      [...str].forEach((ch, i) => { const b = cell16(ch), x0 = (col + i) * 16, y0 = 8 + row * 16; for (let y = 0; y < 16; y++) for (let x = 0; x < 8; x++) if (b[y * 8 + x]) g.fillRect(x0 + x * 2, y0 + y, 2, 1); });
    };
    put(0, 0, 'Frontier Crew', 11);
    put(0, 1, "We Didn't Start the Scaling", 11);
    put(0, 2, 'PC demo, 2026', 11);
    put(0, 4, 'Softmax feat. MC Token', 3);
    put(0, 5, 'Thanks for watching.', 7);
    put(0, 7, 'C:\\DEMOS\\FC>', 7);
    if (Math.floor(k * 2.4) % 2 === 0) put(12, 7, '_', 7);
    ui.save(); ui.imageSmoothingEnabled = false; ui.drawImage(c, 0, 0, 640, 360, 0, 0, 1920, 1080);
    // (the mode switch into it: a sync line, for two frames)
    if (k < .05) { ui.fillStyle = '#000'; ui.fillRect(0, 0, 1920, 1080); ui.fillStyle = '#ffffff'; ui.fillRect(0, 538, 1920, 4); }
    ui.restore();
  }

  // ---- the roll: the visible stretch of the list, drawn on the sheet's texture each frame ----
  function roll(g, scroll) {
    // the reading line: a soft magenta bar across the sheet
    const gr = g.createLinearGradient(0, BAND - 70, 0, BAND + 70);
    gr.addColorStop(0, 'rgba(255,60,170,0)'); gr.addColorStop(.5, 'rgba(255,60,170,.22)'); gr.addColorStop(1, 'rgba(255,60,170,0)');
    g.fillStyle = gr; g.fillRect(0, BAND - 70, 2048, 140);
    g.fillStyle = 'rgba(255,150,220,.45)'; g.fillRect(260, BAND + 58, 1528, 3); g.fillRect(260, BAND - 61, 1528, 3);
    g.textAlign = 'center'; g.textBaseline = 'middle'; g.lineJoin = 'round';
    ROWS.forEach(([kind, str, label], i) => {
      const y = YS[i] - scroll; if (kind === 'gap' || y < -80 || y > 1110) return;
      const near = clamp(1 - Math.abs(y - BAND) / 110), edge = clamp(Math.min((y - 150) / 170, (1010 - y) / 150));
      g.save(); g.globalAlpha = edge; g.translate(1024, y); const sc = 1 + .1 * near; g.scale(sc, sc);
      if (kind === 'greet') {
        const size = str.length > 16 ? 72 : 88;
        g.font = `${size}px ${MOD.FONT_T}`; g.lineWidth = 12; g.strokeStyle = 'rgba(8,2,16,.85)'; g.strokeText(str, 0, 0);
        g.fillStyle = MOD.chrome(g, -size / 2, size / 2, near > .25 ? MAGC : STEELC); g.fillText(str, 0, 0);
      } else if (kind === 'head') {
        g.font = `54px ${MOD.FONT_M}`; g.fillStyle = '#ffb070'; g.letterSpacing = '8px'; g.fillText(str, 0, 0);
      } else if (kind === 'agent') {
        // (their names in the board's own terminal type, green)
        g.font = `84px ${MOD.FONT_M}`; g.lineWidth = 10; g.strokeStyle = 'rgba(8,2,16,.85)'; g.strokeText(str, 0, 0);
        g.fillStyle = MOD.chrome(g, -42, 42, near > .25 ? MAGC : ['#f0fff4', '#b8ffd0', '#5dff8a', '#1a6a30']); g.fillText(str, 0, 0);
      } else if (kind === 'handle') {
        g.font = `80px ${MOD.FONT_M}`; g.lineWidth = 10; g.strokeStyle = 'rgba(8,2,16,.85)'; g.strokeText(str, 0, 0);
        g.fillStyle = MOD.chrome(g, -40, 40, near > .25 ? MAGC : STEELC); g.fillText(str, 0, 0);
      } else {
        if (label) { g.font = `36px ${MOD.FONT_M}`; g.fillStyle = 'rgba(190,205,255,.9)'; g.fillText(label, 0, -52); }
        const own = /[a-z]/.test(str), size = own ? 84 : 74;
        g.font = `${size}px ${own ? '"Archivo Black"' : MOD.FONT_T}`; g.lineWidth = 12; g.strokeStyle = 'rgba(8,2,16,.85)'; g.strokeText(str, 0, 8);
        g.fillStyle = MOD.chrome(g, 8 - size / 2, 8 + size / 2, near > .25 ? MAGC : ORANGEC); g.fillText(str, 0, 8);
      }
      g.restore();
    });
  }

  msection('outro', (t, s, E, ui) => {
    // (the greetings start in C4's window, on the downbeat after the dot's "on"s, self.C4_TAIL: C4's scene hands over to this one)
    const tail = self.C4_TAIL ?? s.start;
    const t0 = Math.min(s.start, tail), lt = t - t0, d = s.end - t0, exitAt = d - 2.0;
    if (lt >= exitAt) {
      dos(ui, lt - exitAt);
      return { fx: E.fx, res: E.res, floor: false, skyA: '#000000', skyB: '#000000', exposure: 0, flare: 0 };
    }
    // the roll's speed lands the last credit on the reading line with a second to spare
    const stop = exitAt - 1.3, start = YS[0] - 880, end = YS.at(-1) - BAND, scroll = lerp(start, end, clamp(lt / stop));
    const g = MOD.panel(0); roll(g, scroll);
    const h = MOD.panel(1);
    h.save(); h.textAlign = 'center'; h.textBaseline = 'middle'; h.font = `76px ${MOD.FONT_M}`; h.fillStyle = '#ffb070'; h.letterSpacing = '10px';
    h.fillText('SENDS GREETINGS TO', 512, 256); h.restore();
    const th = .38, S = MOD.shapeText('FRONTIER CREW'), hy = .36;
    const fadeIn = easeOut(clamp(lt / .6)), fadeOut = clamp((lt - (exitAt - .7)) / .7);
    const sway = Math.sin(lt * .4);
    return {
      fx: E.fx, res: E.res,
      ro: [sway * .7, 1.6, 6.3 - lt * .05], ta: [sway * .15, 2.25, -2], fov: 1.5,
      skyA: '#020109', skyB: '#0a0618', acc: '#ff3aa6', fog: .012, floorCol: '#020206', grid: .12,
      sky: { mode: 'stars', k: .25, col: '#ffe4f6' },
      shape: { key: 'FC', src: S, p: [0, 4.12 + Math.sin(lt * 1.3) * .04, -2.7], rot: MOD.rotYX(Math.sin(lt * .7) * .16, .05), s: [hy * S.aspect, hy, .14], col: '#5a1450', rim: '#ffb0e6', metal: 1 },
      panels: [
        { c: [0, 1.75, -1.6], u: [4.3, 0, 0], v: [0, 2.15 * Math.cos(th), -2.15 * Math.sin(th)], alpha: 1, gain: 1.6, glass: .25, tex: 0 },
        { c: [0, 3.62, -2.4], u: [1.3, 0, 0], v: [0, .65, 0], alpha: 1, gain: 1.7, glass: 0, tex: 1 },
      ],
      light: { p: [0, 5.5, -5], c: '#ff8ad6', k: 6, vol: .7 },
      // (the machine that trains on, far behind the crew's logo)
      world: { kind: 'fractal', p: [3.6, -.4, .25, .35], col: '#241a2a', glowCol: '#ff4fb4', at: [0, 4.4, -26], metal: .7, t: lt * 2 },
      exposure: fadeIn * (1 - fadeOut),
    };
  });
})();

;
// ---- styles/demoscene/modern/wire.js ----
// modern/wire.js: routes every window of the song to its engine, for the two versions (loaded last).
//   Version A, "the demo scales with the song": the hardware era follows the timeline. The intro, verse 1 and chorus 1 are the 1996
//   VGA engine (ch/p00–p02 on kit.js); verse 2 and chorus 2 a late-90s 3D card (fx 2); verse 3 a 2000s shader demo (fx 3); chorus 3
//   climbs from there (the picture's resolution gains word by word on "the curves kept gaining", and the modern look bursts in on
//   "contain"); verse 4, chorus 4 and the outro are a modern 64k intro (fx 4).
//   Version B, "modern throughout": every window at fx 4.
// The page sets self.VERSION ('A' | 'B') before loading the scripts. Modern windows draw with MOD.SCENES (modern/m*.js); wire.js adds
// MC Token's scroller and the date to verse lines, and Softmax's HUD to choruses, unless the scene's F says scroller/date/hud: false.
(() => {
  const VERSION = self.VERSION || 'B';
  const ERAS = {
    2: { fx: 2, res: 1 / 3, uiRes: .5 },   // (640×360, the VGA part's own grid, each pixel 3×3; its UI at 2×2)
    3: { fx: 3, res: .5, uiRes: .75 },
    4: { fx: 4, res: 1, uiRes: 1 },
  };
  const LABEL = { 1: '1996 · VGA 640×360', 2: '1998 · 3D CARD', 3: '2004 · PIXEL SHADERS', 4: '2026 · 64K INTRO' };
  // (a checking script may force an era: self.FORCE_ERA = 1..4)
  function eraAt(t, s) {
    if (self.FORCE_ERA) return self.FORCE_ERA < 2 ? { fx: 1 } : { ...ERAS[self.FORCE_ERA] };
    if (VERSION === 'B') return { ...ERAS[4] };
    const sec = s ? s.sec : segAt(t).sec;
    if (sec === 'intro' || sec === 'V1' || sec === 'C1') return { fx: 1 };
    if (sec === 'V2' || sec === 'C2') return { ...ERAS[2] };
    if (sec === 'V3') return { ...ERAS[3] };
    if (sec === 'C3') {
      const L2 = wordsOf(LINES.find(l => l.sec === 'C3' && l.n === 2)), L4 = wordsOf(LINES.find(l => l.sec === 'C3' && l.n === 4));
      const tContain = L4[8].t0;
      if (t < L2[0].t0) return { ...ERAS[3] };
      if (t < L2.at(-1).t1 + .2) {   // the picture's own resolution gains, word by word
        let k = 0; L2.forEach((w, i) => { if (t >= w.t0) k = i + 1; });
        return { fx: 3, res: lerp(.5, 1, k / L2.length), uiRes: lerp(.75, 1, k / L2.length), climb: k / L2.length };
      }
      if (t < tContain) return { fx: 3, res: 1, uiRes: 1 };
      return { ...ERAS[4], upgraded: t - tContain };
    }
    return { ...ERAS[4] };
  }
  // The era label version A's page shows beside the picture.
  self.ERA_LABEL = t => {
    if (VERSION !== 'A') return '';
    const E = eraAt(t);
    if (E.climb !== undefined) return `${LABEL[3]} → ${Math.round(E.res * 100)}% resolution`;
    return LABEL[E.fx];
  };
  self.ERA_AT = eraAt;

  // A window no painter has reached yet: its key and line on a glass panel (so a gap is plain, never the old engine).
  function placeholder(t, s, E) {
    const g = MOD.panel(1);
    MOD.text(g, s.key, 512, 190, { size: 90, font: MOD.FONT_T, align: 'center', color: '#ff9ad8' });
    MOD.text(g, (s.text || s.key).slice(0, 38), 512, 300, { size: 34, align: 'center', color: '#ffffff' });
    return { fx: E.fx, res: E.res, ro: [0, 1.6, 7], ta: [0, 1.6, 0], panels: [{ c: [0, 1.8, 0], u: [2.4, 0, 0], v: [0, 1.2, 0], tex: 1 }], sky: { mode: 'plasma', k: .6, col: '#1478b8' } };
  }

  let pending = null;
  const RETRO = OVERLAYS[0];
  OVERLAYS[0] = (t, s) => {
    if (pending) { const F = pending; pending = null; MOD.render(F); return; }
    if (VERSION === 'A' && RETRO) RETRO(t, s);
  };
  const hud = new Set(['C1', 'C2', 'C3', 'C4']);
  for (const seg of SEGS) {
    const key = seg.key, retro = SHOTS[key];
    SHOTS[key] = (p, lt, d, t, s) => {
      if (!warming) { warming = true; warmScenes(); }
      const E = eraAt(t, s);
      // (without WebGL2 the whole song is the VGA engine's: after chorus 1, `ch/zz_generic.js`'s)
      if ((E.fx < 2 || noGL) && retro) { retro(p, lt, d, t, s); return; }
      MOD.setT(t);
      const g = MOD.uiBegin(E.uiRes);
      const F = (MOD.SCENES[s.key] ?? placeholder)(t, s, E, g);
      F.fx = E.fx; F.res = E.res;
      if (s.kind === 'line') {
        if (F.scroller !== false) MOD.scroller(g, s.sec, t);
        if (F.date !== false) MOD.datePlate(g, t);
      } else if (hud.has(s.key) && F.hud !== false) MOD.softmaxHUD(g, t, { word: sungWord(t), y: 1046, h: 140, level: F.hudLevel ?? 1 });
      if (E.upgraded !== undefined) { F.flash = Math.max(F.flash ?? 0, clamp(1 - E.upgraded / .3) * .35); F.flashCol = F.flashCol ?? '#ff7ac8'; }
      pending = F;
    };
  }
  // (compile the modern engine's shaders at start-up; in a worker this runs before it reports ready)
  let noGL = false;
  try { MOD.warm(); } catch (e) { noGL = true; console.error('modern engine warm-up: ' + (e.stack || e)); }
  // A scene builds its caches (an atlas, a shape's distance field) on its first frame, which would hitch a first play on that line's
  // first beat. So after the first frame (when the page or the worker has its fonts, which the caches may draw with), each modern
  // window runs once at its start, its middle and its end (a build that a word triggers lasts to the end), a window at a time
  // between frames, from the start time on round the song. (Not in render mode, where a script drives the frames.)
  // STYLE_WARM settles once every window is warm: until then the warm-up's builds come between frames, and the site's page holds the
  // song (and seeking) rather than let it run ahead of the video.
  const rendering = HAS_DOM && /[?&]render\b/.test(location.search);
  let warming = rendering || typeof setTimeout !== 'function' || noGL, warmed;
  self.STYLE_WARM = new Promise(ok => { warmed = ok; });
  if (warming) warmed();
  function warmScenes() {
    const list = SEGS.filter(s => MOD.SCENES[s.key] && (VERSION === 'B' || eraAt(s.start + .01, s).fx >= 2));
    const from = Math.max(0, list.findIndex(s => s.end > (self.STYLE_START ?? 0)));
    const order = [...list.slice(from), ...list.slice(0, from)];
    let i = 0;
    const next = () => {
      if (i >= order.length) { warmed(); return; }
      const s = order[i++];
      for (const t of [s.start + .05, (s.start + s.end) / 2, s.end - .05]) {
        try { const E = eraAt(t, s); MOD.setT(t); MOD.SCENES[s.key](t, s, E, MOD.uiBegin(E.uiRes)); } catch (e) { console.error(`warming ${s.key}: ${e.stack || e}`); }
      }
      setTimeout(next, 0);
    };
    setTimeout(next, 100);
  }
  // The page's hooks for its quality ladder (page.mjs on the site; the version pages' own): QUALITY_LEVELS levels, 0 the video as
  // designed and each cheaper than the last, set with setQuality(level). The 1996 part's lighter load (LOWQ) comes in at level 2; the
  // 2026 era's shader tiers at 1, 2 and 3, and its picture's resolution at 4 and 5 (engine.js's LEVELS). Text, the scroller, the date
  // and Softmax's HUD are the canvas's full resolution at every level. In render mode (a script driving the frames) it stays at 0.
  // STYLE_FINISH finishes the GPU's work for the frame just drawn, so that the page's measure of a frame's time includes it, and
  // STYLE_INFO says what the frame was, for the page's debug overlay.
  self.QUALITY_LEVELS = 6;
  self.setQuality = l => { if (rendering) return; LOWQ = l >= 2; MOD.setLevel(l); };
  self.STYLE_FINISH = () => MOD.finish();
  self.STYLE_INFO = () => {
    const L = MOD.last(), t = T, E = eraAt(t);
    const era = E.fx < 2 ? `1996 · VGA 640×360${LOWQ ? ' · lighter effects' : ''}` : `${LABEL[Math.min(4, Math.floor(E.fx))]}${L ? ` · picture ${L.w}×${L.h}` : ''}${E.fx > 3.4 ? ` · shader tier ${MOD.tier()}` : ''}`;
    return { era, level: MOD.level(), levels: self.QUALITY_LEVELS };
  };

  // The windows without a modern scene (checking scripts list them).
  self.MISSING_SCENES = () => SEGS.filter(s => !MOD.SCENES[s.key] && (VERSION === 'B' || eraAt(s.start + .01, s).fx >= 2)).map(s => s.key);
})();
