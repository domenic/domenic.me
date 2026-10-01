// The annotated zine: audio playback, the live-drawn video, lyric following, notes, docking, fullscreen, and the jukebox.
//
// All UI state lives in `S`; every transition goes through a named function below, and the DOM is
// synchronized from `S` rather than read back from it.

const data = JSON.parse(document.getElementById('scaling-data').textContent);
// The album's tracks play in the main player, with their videos and synced lyrics; the jukebox's genres are audio only.
const versions = new Map(data.versions.filter(v => v.group === 'album').map(v => [v.id, v]));
const jukeboxVersions = new Map(data.versions.filter(v => v.group === 'jukebox').map(v => [v.id, v]));
const abs = path => new URL(path, document.baseURI).href;
const reducedMotion = matchMedia('(prefers-reduced-motion: reduce)').matches;
const wide = matchMedia('(min-width: 1080px)');
const clamp = (v, a, b) => Math.max(a, Math.min(b, v));
const fmt = s => `${Math.floor(s / 60)}:${String(Math.floor(s % 60)).padStart(2, '0')}`;

const player = document.getElementById('player');
const poster = player.querySelector('.poster');
const slot = player.closest('.player-slot');
const sideTarget = document.querySelector('.dock-target');
const bottomDock = document.querySelector('.bottom-dock');
const lyricsGrid = document.querySelector('.lyrics-grid');
let canvas = document.getElementById('out');
const q = sel => player.querySelector(sel);
const scrub = q('.scrub input');
const timeNow = q('.now');
const timeDur = q('.dur');
const select = q('.version select');
const deckPlay = q('.deck-play');
const followBtn = q('.follow');
const allNotesBtn = document.querySelector('.all-notes');
const nowCard = document.querySelector('.now-card');
const screenEl = q('.screen');
const fsBtn = q('.fullscreen');
const exitBtn = q('.screen-exit');
const loadError = q('.load-error');
const root = document.documentElement;

const audio = new Audio();
audio.preload = 'metadata';
// Resolves once the current version's audio metadata and timing are loaded. Safari ignores seeks made
// before that, so every seek waits on it.
let versionReady = Promise.resolve();

const S = {
  version: null,
  timing: null,
  playback: 'idle',   // idle | playing | paused | ended
  audio: 'ok',        // ok | failed (the track's audio didn't load: an error, or a load that stalled before its metadata came)
  follow: 'off',      // off (manual: the reader scrolls) | on (the page keeps the line being sung in view)
  dock: 'none'        // none | side | bottom
};

// ---------- timing ----------
const timingCache = new Map();
function loadTiming(v) {
  if (!v.timing) return Promise.resolve(null);
  if (!timingCache.has(v.id)) timingCache.set(v.id, fetch(abs(v.timing)).then(r => r.json()).then(tm => (timeLines(tm), tm)));
  return timingCache.get(v.id);
}
// When each line is the line being sung. A line with its words' times (`words`: each word's start and end, in centiseconds from
// the line's start) takes over as the line before it finishes, its last word sung, or LEAD seconds before its own first word
// after a rest; so a word held into the next line's start isn't cut off. A line without them is up from its start to its end.
// Either way, a line goes when the next one comes up, or LINGER seconds after it's sung.
const LEAD = .5;
const LINGER = 1.2;
const lineTimes = new WeakMap();   // line → { on, first, last, starts, ends }
function timeLines(tm) {
  let before = -Infinity;
  for (const l of tm.lines) {
    const starts = l.words?.map(w => l.start + w[0] / 100);
    const ends = l.words?.map(w => l.start + w[1] / 100);
    const first = starts?.[0] ?? l.start;
    const last = ends?.at(-1) ?? l.end;
    lineTimes.set(l, { on: starts ? Math.min(first, Math.max(first - LEAD, before)) : l.start, first, last, starts, ends });
    before = last;
  }
}
function lineAt(t) {
  const L = S.timing?.lines;
  if (!L) return null;
  for (let i = L.length - 1; i >= 0; i--) {
    const k = lineTimes.get(L[i]);
    if (k.on <= t) return t < Math.min(L[i + 1] ? lineTimes.get(L[i + 1]).on : Infinity, k.last + LINGER) ? L[i] : null;
  }
  return null;
}

// ---------- renderer: a worker drawing to an OffscreenCanvas, else the main thread ----------
// Quality has one controller, the page's. It measures how long each frame really takes to reach the screen: from asking the
// engine for it to its being drawn, the GPU's work included (an engine that draws with WebGL finishes it in its STYLE_FINISH
// hook), while the song plays. It leaves out frames that did one-off work (an engine's STYLE_ONEOFF() says so: compiling a
// program, building a scene's caches, sizing its buffers), which say nothing about how fast the video goes, and it goes by frames
// over a stretch rather than any one, so that a stall it wasn't told of (a garbage collection) doesn't count either. When the
// median of the last dozen frames is over the budget (28 ms, under about 35 frames a second), it steps down a ladder, several
// steps at once the further over it is (each step saves very roughly a third). When the frames at a step have had room to spare
// for three seconds (nine in ten under two-thirds of the budget, room for the step up's third more), it steps back up one. A
// step it has to leave again soon after climbing to it is tried again only after a while, twice as long each time, so that it
// settles rather than oscillating. The ladder is the engine's own quality levels, if it has any (QUALITY_LEVELS of them, chosen
// with setQuality(level): 0 the video as designed, each cheaper than the last, its type always at the canvas's full resolution),
// then the canvas's own scale (QUALITY). An engine without levels has just the scale. An engine can also say from which of its
// levels the resolution drops (QUALITY_SHARP, the K-pop video's 3D scene): from there down, including the canvas's own steps, the
// ladder moves only for frames over a looser budget (40 ms, under 25 frames a second), since a soft picture shows more than fewer
// sparkles or a lower frame rate.
const QUALITY = [1, .75, .5];
const BUDGET = 28, SHARP_BUDGET = 40;
let renderer = null;
let rendererStarting = null;
let qi = 0;
let appliedScale = 0;
let lastDrawMs = 0;
let lastLowRes = 0;
let engineLevels = 0;       // (the running engine's QUALITY_LEVELS)
let engineSharp = null;     // (and its QUALITY_SHARP, if it has one)
let step = 0;               // (where on the ladder: the engine's levels first, then the canvas's scale steps)
let settling = 0;           // (frames to leave out after a step, while the engine settles into it: at least this many,
let settleUntil = 0;        //  and all those drawn before this time)
let frames = [];            // (the frames measured at this step: [ms, when drawn])
let stepAt = 0;             // (when the ladder last moved)
let climbedTo = -1;         // (the step last climbed to, and when)
let climbedAt = 0;
const backoff = new Map();  // (step → { until, wait }: a step that was left soon after climbing to it, not tried again until then)
const ladderLength = () => Math.max(1, engineLevels) + QUALITY.length - 1;
function applyStep() {
  const top = Math.max(0, engineLevels - 1);
  renderer?.setQuality?.(Math.min(step, top));
  qi = Math.max(0, step - top);
  settling = 2; settleUntil = performance.now() + 250; frames = []; stepAt = performance.now();
  updateScale();
}

function idealScale() {
  // Map the 1920×1080 scene exactly onto the canvas's device pixels; step down only if frames are slow.
  const w = canvas.clientWidth || 960;
  return clamp((w * devicePixelRatio) / 1920 * QUALITY[qi], .2, 2);
}
function updateScale() {
  if (!renderer) return;
  const s = idealScale();
  if (!appliedScale || Math.abs(s - appliedScale) / appliedScale > .01) {
    appliedScale = s;
    renderer.setScale(s);
    drawNow();
  }
}
// (ms: how long the frame took to reach the screen, as the page measured it; lowRes: how many pictures the frame drew as low-res
// stand-ins, in a style whose pictures are still loading; info: what the engine says the frame was, for the debug overlay;
// oneOff: whether it did one-off work, which the engine says in STYLE_ONEOFF())
function onDrawn(ms, lowRes = 0, info = null, oneOff = false) {
  lastDrawMs = ms;
  lastLowRes = lowRes;
  player.dataset.drawn = '';
  debugHUD?.(ms, info);
  if (S.playback !== 'playing') return;
  if (settling > 0 || performance.now() < settleUntil) { settling--; return; }
  if (oneOff) return;
  const now = performance.now();
  frames.push([ms, now]);
  if (frames.length > 600) frames.splice(0, 300);
  const move = qualityStep(frames, now);
  if (move) {
    // (leaving a step soon after climbing to it: it's tried again only after a while, twice as long each time)
    if (move > 0 && step === climbedTo && now - climbedAt < 15000) {
      const wait = Math.min(300000, (backoff.get(step)?.wait ?? 10000) * 2);
      backoff.set(step, { until: now + wait, wait });
    }
    step += move;
    if (move < 0) { climbedTo = step; climbedAt = now; }
    applyStep();
  }
}
// (the budget for moving down to step k: the looser one where k lowers the resolution, for an engine that says where that starts)
const budgetTo = k => engineSharp != null && engineSharp >= 0 && k >= engineSharp ? SHARP_BUDGET : BUDGET;
// (the steps to move, from the frames measured at this step: down by one or more when the median of the last dozen is over the
// budget for each step it moves to; up by one when for three seconds or more nine in ten have been under two-thirds of the budget
// that brought it down here, and the step above isn't waiting out a backoff; else 0)
function qualityStep(frames, now) {
  if (frames.length >= 12 && step < ladderLength() - 1) {
    const m = median(frames.slice(-12).map(f => f[0]));
    const n = Math.floor(Math.log(m / BUDGET) / Math.log(1.6));
    let to = step;
    for (let k = step + 1; k <= Math.min(step + Math.max(1, n), ladderLength() - 1) && m > budgetTo(k); k++) to = k;
    if (to > step) return to - step;
  }
  if (step > 0 && now - stepAt > 3000 && !(now < (backoff.get(step - 1)?.until ?? 0))) {
    const last = frames.filter(f => now - f[1] < 3000).map(f => f[0]).sort((a, b) => a - b);
    if (last.length >= 20 && last[Math.floor(last.length * .9)] < budgetTo(step) * 2 / 3) return -1;
  }
  return 0;
}
const median = a => { const s = [...a].sort((x, y) => x - y); return s[Math.floor(s.length / 2)]; };
// ?debug: an overlay on the player with what the video is drawing and how fast it reaches the screen
const debugHUD = new URLSearchParams(location.search).has('debug') ? (() => {
  const el = document.createElement('pre');
  el.className = 'debug-hud';
  el.style.cssText = 'position:fixed;left:6px;top:40px;z-index:99;margin:0;padding:6px 8px;max-width:calc(100vw - 12px);background:rgb(0 0 0 / 78%);color:#9ef;font:11px/1.35 ui-monospace,monospace;white-space:pre-wrap;user-select:text;cursor:text';
  document.body.append(el);
  const times = [];
  let shown = 0, info = null;
  return (ms, i) => {
    times.push(ms); if (times.length > 120) times.shift();
    if (i) info = i;
    const now = performance.now(); if (now - shown < 250) return; shown = now;
    const sorted = [...times].sort((a, b) => a - b), avg = times.reduce((a, b) => a + b, 0) / times.length;
    const dpr = devicePixelRatio, cw = canvas.clientWidth, ch = canvas.clientHeight;
    el.textContent = [
      `${renderer?.style ?? '—'} · ${renderer?.kind ?? 'no renderer'} · ${S.playback}`,
      info?.era ? `era: ${info.era}` : null,
      `quality: step ${step + 1} of ${ladderLength()}${engineLevels ? ` · engine level ${Math.min(step, engineLevels - 1)} of 0–${engineLevels - 1}` : ' · (no engine levels)'} · canvas scale step ${qi}`,
      `render scale ${appliedScale.toFixed(3)} · canvas ${Math.round(1920 * appliedScale)}×${Math.round(1080 * appliedScale)} for ${Math.round(cw * dpr)}×${Math.round(ch * dpr)} device px (${cw}×${ch} css × ${dpr})`,
      `frame to screen: ${avg.toFixed(1)} ms avg · p95 ${sorted[Math.floor(sorted.length * .95)]?.toFixed(1)} · last ${ms.toFixed(1)}`
    ].filter(Boolean).join('\n');
  };
})() : null;

// Each album track draws with its own video style's engine, named for the track. Every engine defines the same globals, so each
// style runs in its own worker (or, without OffscreenCanvas in workers, its own hidden iframe) and draws to its own canvas;
// switching styles builds the next one beneath the current canvas and swaps once it has drawn.
const styleOf = v => v.id;
// (each style's engine is one script, and it draws with some of the page's fonts)
const fontFile = new Map(data.fonts.map(f => [f.family, abs(f.file)]));
const engineOf = style => ({
  script: abs(data.engines[style].script),
  images: data.engines[style].images && abs(data.engines[style].images),
  fonts: data.engines[style].fonts.map(family => [family, fontFile.get(family)])
});
let workersOK = 'transferControlToOffscreen' in HTMLCanvasElement.prototype && !new URLSearchParams(location.search).has('mainthread');

function workerRenderer(el, style, tm, scale) {
  const off = el.transferControlToOffscreen();
  const worker = new Worker(new URL('worker.js', import.meta.url));
  let busy = false;
  let queued = null;
  let resolveReady, rejectReady, resolveDrawn, resolveWarm;
  const ready = new Promise((ok, bad) => { resolveReady = ok; rejectReady = bad; });
  const drawn = new Promise(ok => { resolveDrawn = ok; });
  const warm = new Promise(ok => { resolveWarm = ok; });
  let sentAt = 0;
  const send = t => { busy = true; sentAt = performance.now(); worker.postMessage({ type: 'frame', t, info: !!debugHUD }); };
  worker.onmessage = e => {
    const m = e.data;
    if (m.type === 'ready') { engineLevels = m.levels ?? 0; engineSharp = m.sharp ?? null; resolveReady(); }
    else if (m.type === 'warm') resolveWarm();
    else if (m.type === 'drawn') {
      busy = false;
      resolveDrawn();
      if (renderer?.worker === worker) onDrawn(performance.now() - sentAt, m.lowRes, m.info, m.oneOff);
      if (queued !== null) { const t = queued; queued = null; send(t); }
    } else if (m.type === 'stale') {
      // a picture the last frame drew as a stand-in has loaded: a paused video redraws (a playing one is about to anyway)
      if (renderer?.worker === worker && S.playback !== 'playing') drawNow();
    } else if (m.type === 'error') {
      // (a frame that failed doesn't hold up the next, or a switch of styles waiting for the first)
      console.error('scaling video worker:', m.message);
      busy = false;
      resolveDrawn();
      rejectReady(new Error(m.message));
    }
  };
  worker.onerror = e => rejectReady(e);
  worker.postMessage({
    type: 'init',
    canvas: off,
    scale,
    dpr: devicePixelRatio,
    timing: tm,
    ...engineOf(style),
    // (a style that loads pictures loads the ones for the playhead first)
    start: audio.currentTime
  }, [off]);
  return {
    kind: 'worker',
    worker,
    ready,
    drawn,
    warm,
    frame(t) { if (busy) queued = t; else send(t); },
    setScale(s) { worker.postMessage({ type: 'scale', scale: s, dpr: devicePixelRatio }); },
    setQuality(level) { worker.postMessage({ type: 'quality', level }); },
    setTiming(t) { worker.postMessage({ type: 'timing', timing: t }); },
    terminate() { worker.terminate(); }
  };
}

// The fallback runs the engine in a hidden same-origin iframe and copies each frame onto the page's canvas.
async function frameRenderer(el, style, tm, scale) {
  const host = document.createElement('iframe');
  host.hidden = true;
  host.srcdoc = '<canvas id="out" width="1920" height="1080"></canvas>';
  const loaded = new Promise(ok => host.addEventListener('load', ok, { once: true }));
  document.body.append(host);
  await loaded;
  const win = host.contentWindow;
  const doc = host.contentDocument;
  win.TIMING = tm;
  win.RENDER_SCALE = scale;
  win.STYLE_DPR = devicePixelRatio;
  const engine = engineOf(style);
  win.STYLE_BASE = engine.images;
  win.STYLE_START = audio.currentTime;
  const fonts = Promise.all(engine.fonts.map(async ([family, url]) => {
    const face = new win.FontFace(family, `url(${url})`);
    await face.load();
    doc.fonts.add(face);
  }));
  try {
    await new Promise((ok, bad) => {
      const s = doc.createElement('script');
      s.src = engine.script;
      s.onload = ok;
      s.onerror = bad;
      doc.head.append(s);
    });
    await fonts;
    if (win.STYLE_READY) await win.STYLE_READY;
  } catch (e) {
    host.remove();
    throw e;
  }
  const out = doc.getElementById('out');
  const g = el.getContext('2d');
  const r = {
    kind: 'main',
    ready: Promise.resolve(),
    drawn: Promise.resolve(),
    warm: Promise.resolve(win.STYLE_WARM).catch(() => {}),
    frame(t) {
      const t0 = performance.now();
      win.renderFrame(t);
      win.STYLE_FINISH?.();
      if (el.width !== out.width || el.height !== out.height) { el.width = out.width; el.height = out.height; }
      g.drawImage(out, 0, 0);
      onDrawn(performance.now() - t0, win.STYLE_LOWRES?.() ?? 0, debugHUD && win.STYLE_INFO?.(), win.STYLE_ONEOFF?.() ?? false);
    },
    setScale(s) { win.STYLE_DPR = devicePixelRatio; win.setRenderScale(s); },
    setQuality(level) { win.setQuality?.(level); },
    setTiming(t) { win.setTiming(t); },
    terminate() { host.remove(); }
  };
  win.STYLE_STALE = () => { if (renderer === r && S.playback !== 'playing') drawNow(); };
  engineLevels = win.QUALITY_LEVELS ?? 0;
  engineSharp = win.QUALITY_SHARP ?? null;
  return r;
}

// A new canvas beneath the current one (a canvas handed to a worker can't be reused).
function freshCanvas() {
  const el = canvas.cloneNode();
  canvas.before(el);
  return el;
}
function swapCanvas(el) {
  if (el === canvas) return;
  canvasObserver.unobserve(canvas);
  canvas.remove();
  canvas = el;
  canvasObserver.observe(canvas);
}

let rendererStyle = null;
function startRenderer() {
  const style = styleOf(S.version ?? versions.get(select.value));
  if (rendererStarting && rendererStyle === style) return rendererStarting;
  rendererStyle = style;
  const previous = rendererStarting;
  player.dataset.loading = '';
  delete player.dataset.noVideo;
  setSeekable();
  rendererStarting = (async () => {
    await previous?.catch(() => {});
    // The previous style's engine stops drawing right away (it doesn't know this take's timing); this version's poster
    // shows until its own engine, which can take a while to download, draws its first frame.
    const old = renderer;
    renderer = null;
    if (old) delete player.dataset.drawn;
    const tm = S.timing ?? await loadTiming(versions.get(select.value));
    appliedScale = idealScale();
    let el = old ? freshCanvas() : canvas;
    let r = null;
    let workerError = null;
    if (workersOK) {
      r = workerRenderer(el, style, tm, appliedScale);
      try {
        await r.ready;
      } catch (e) {
        // Fonts or OffscreenCanvas unavailable in workers here: use the iframe fallback from now on.
        workerError = e;
        r.terminate();
        r = null;
        workersOK = false;
        const used = el;
        el = freshCanvas();
        if (used !== canvas) used.remove(); else swapCanvas(el);
      }
    }
    if (!r) {
      try {
        r = await frameRenderer(el, style, tm, appliedScale);
      } catch (e) {
        // The engine can't run here at all (the K-pop video without WebGL2, say), so the worker wasn't to blame: the poster stays
        // up, with the reason in place of the loading label.
        console.error('scaling video:', e);
        if (workerError) workersOK = true;
        // (and the next engine gets a canvas no worker has taken)
        old?.terminate();
        swapCanvas(el);
        if (rendererStyle === style) {
          delete player.dataset.loading;
          player.dataset.noVideo = /WebGL2/.test(`${e?.message} ${workerError?.message}`) ? 'webgl2' : '';
          setSeekable();
        }
        return null;
      }
    }
    r.style = style;
    if (S.timing && S.timing !== tm) r.setTiming(S.timing);
    renderer = r;
    // (a new engine starts at the top of the ladder)
    step = 0; climbedTo = -1; backoff.clear(); qi = 0; frames = []; stepAt = performance.now();
    // the canvas may have been resized while the engine started (say, into fullscreen)
    updateScale();
    // Draw the first frame (underneath the previous style's video, if any), then uncover it. (A style that warms up after its first
    // frame, as the demoscene's scenes do, starts on that then, before the reader presses Play.)
    r.frame(audio.currentTime);
    await r.drawn;
    if (old) {
      swapCanvas(el);
      old.terminate();
    }
    r.warm.then(() => {
      if (renderer !== r) return;
      delete player.dataset.loading;
      setSeekable();
    });
    return r;
  })();
  return rendererStarting;
}
function drawNow() {
  renderer?.frame(audio.currentTime);
}
// The song waits for its video. While the track's video is loading, from its engine starting until it has drawn its first frame
// and, in a style that warms up after that (the demoscene), warmed up what the first few seconds need, the reader can't seek (the
// scrub bar and the ▶ beside each line are off), and Play shows the video loading and starts the song once it's in; otherwise the
// song would run on while the video stood still. (A style that streams its pictures, K-pop's, keeps up from its first frame: it
// loads the pictures by the playhead first, and draws low-resolution stand-ins for any still on their way.)
const fromHereButtons = document.querySelectorAll('.from-here');
let loadedWaiters = [];
const videoLoaded = () => ('loading' in player.dataset ? new Promise(ok => loadedWaiters.push(ok)) : Promise.resolve());
function setSeekable() {
  const off = 'loading' in player.dataset;
  scrub.disabled = off;
  for (const b of fromHereButtons) b.disabled = off;
  if (!off) {
    for (const ok of loadedWaiters) ok();
    loadedWaiters = [];
  }
}

// ---------- lyrics: the current line, following, notes ----------
const lineEls = new Map([...document.querySelectorAll('.line[data-sec]')].map(el => [`${el.dataset.sec}.${el.dataset.n}`, el]));
let nowEl = null;
let nowLine = null;
// The page scrolls itself (following, Back to top) with an animation of its own, so that it stops dead when the reader takes
// over (a browser's smooth scroll can't reliably be interrupted) and knows where it's headed. It notes where it last put the
// page: a scroll that lands anywhere else is the reader's, even one with no input event of its own, like a find-in-page jump.
// (Meanwhile the browser mustn't move the page itself to keep what's on screen in place as the layout changes: that's
// `overflow-anchor`.)
let pageScroll = 0;
let pageScrollTo = null;
let pageScrollAt = 0;
// (and the browser's own scrolls as it leaves fullscreen are ignored for a moment)
let programmaticUntil = 0;
const scrolledByReader = () => Math.abs(scrollY - pageScrollAt) > 1;

// What following keeps in view: the line being sung, or else the nearest one (the next to be sung; the first before the song
// starts; the last after it ends).
function followTarget() {
  if (nowEl) return nowEl;
  const L = S.timing?.lines;
  if (!L?.length) return lineEls.values().next().value ?? null;
  const t = audio.currentTime;
  const next = S.playback === 'ended' ? null : L.find(l => l.start > t);
  const ln = next ?? L.at(-1);
  return lineEls.get(`${ln.sec}.${ln.n}`) ?? null;
}

function inView(el, band = .85) {
  const r = el.getBoundingClientRect();
  const top = innerHeight * (1 - band) / 2;
  const bottom = innerHeight - top - (S.dock === 'bottom' ? bottomDock.offsetHeight : 0);
  return r.bottom > top && r.top < bottom;
}
function scrollPageTo(y) {
  stopPageScroll();
  const from = scrollY;
  const to = clamp(Math.round(y), 0, document.documentElement.scrollHeight - innerHeight);
  const dur = reducedMotion ? 0 : clamp(Math.abs(to - from) * .6, 250, 700);
  const t0 = performance.now();
  pageScrollTo = to;
  pageScrollAt = from;
  root.style.overflowAnchor = 'none';
  const step = now => {
    if (scrolledByReader()) {
      stopPageScroll();
      readerScrolled();
      return;
    }
    const k = dur ? clamp((now - t0) / dur, 0, 1) : 1;
    scrollTo({ top: from + (to - from) * (1 - (1 - k) ** 3), behavior: 'instant' });
    pageScrollAt = scrollY;
    if (k < 1) pageScroll = requestAnimationFrame(step);
    else stopPageScroll();
  };
  if (dur) pageScroll = requestAnimationFrame(step);
  else step(t0);
}
function stopPageScroll() {
  cancelAnimationFrame(pageScroll);
  pageScroll = 0;
  pageScrollTo = null;
  programmaticUntil = 0;
  root.style.removeProperty('overflow-anchor');
}
// A line goes in the middle of the screen, between the top and the bottom dock, less the margins `scroll-padding` gives in
// page.css.
function scrollToLine(el) {
  const r = el.getBoundingClientRect();
  const top = innerHeight * .2;
  const bottom = innerHeight * .9 - (S.dock === 'bottom' ? bottomDock.offsetHeight : 0);
  scrollPageTo(scrollY + r.top + r.height / 2 - (top + bottom) / 2);
}
function setNowLine(ln) {
  const el = ln ? lineEls.get(`${ln.sec}.${ln.n}`) ?? null : null;
  nowLine = el ? ln : null;
  if (el === nowEl) return;
  nowEl?.classList.remove('now', 'worded');
  for (const p of LINE_PROPS) nowEl?.style.removeProperty(p);
  el?.classList.add('now');
  nowEl = el;
  showLineProgress(audio.currentTime);
  renderNowCard();
  if (el && S.follow === 'on') scrollToLine(el);
}

// The karaoke themes fill the line being sung as it's sung. Its words are in spans, numbered in --i, split as the track's word
// times are (tools/word_timing.py splits the same way: at spaces, and after a hyphen or en dash inside a word).
for (const text of document.querySelectorAll('.line .lyric-text')) {
  const parts = [];
  let i = 0;
  for (const word of text.textContent.trim().split(/\s+/)) {
    if (parts.length) parts.push(' ');
    for (const piece of word.split(/(?<=[-–])(?=[A-Za-z0-9])/)) {
      const span = document.createElement('span');
      span.className = 'w';
      span.style.setProperty('--i', i++);
      span.textContent = piece;
      parts.push(span);
    }
  }
  text.replaceChildren(...parts);
}
const LINE_PROPS = ['--line-p', '--line-t', '--line-w', '--row-top', '--row-h', '--ball-x', '--ball-y', '--ball-hop', '--ball-s'];
// (the longest hop the karaoke marker (Eurodance's cursor) makes from one word to the next, in seconds)
const BALL_HOP = .3;
// An element's padding box's position on the page, as laid out: the line being sung is scaled and tilted, which bounding
// rectangles would take in.
function origin(el) {
  let x = 0, y = 0;
  for (let e = el; e; e = e.offsetParent) {
    x += e.offsetLeft + e.clientLeft;
    y += e.offsetTop + e.clientTop;
  }
  return [x, y];
}
// How far through the line being sung the audio is. They come from the audio's clock, so they freeze on pause and jump on seeks.
// --line-t counts seconds since the line came up. With its words' times (the line is .worded), --line-w counts how many words
// in it is, whole words sung plus the fraction of the one being sung, for fills of each word in turn (a wrapped line fills row by
// row); --line-p is how far across the line's card the fill has got in the row being sung (all the way, once the row's sung),
// whose band of the card --row-top and --row-h give; and a marker (Eurodance's text-mode cursor) hops from each word to the next
// as it's sung, like a sing-along's bouncing ball, at --ball-x and --ball-y, --ball-hop of its height up. Without them, --line-p
// runs from 0 at the line's start to 1 at its end.
function showLineProgress(t) {
  if (!nowEl || !nowLine) return;
  const k = lineTimes.get(nowLine);
  const style = nowEl.style;
  style.setProperty('--line-t', clamp(t - k.on, 0, 60).toFixed(3));
  const spans = nowEl.querySelectorAll('.lyric-text .w');
  const worded = k.starts?.length === spans.length;
  nowEl.classList.toggle('worded', worded);
  if (!worded) {
    style.setProperty('--line-p', clamp((t - nowLine.start) / Math.max(.05, nowLine.end - nowLine.start), 0, 1).toFixed(4));
    return;
  }
  const { starts, ends } = k;
  let i = -1;
  while (i + 1 < starts.length && starts[i + 1] <= t) i++;
  const f = i < 0 ? 0 : ends[i] > starts[i] ? clamp((t - starts[i]) / (ends[i] - starts[i]), 0, 1) : 1;
  style.setProperty('--line-w', (i + f).toFixed(4));
  // where the words are, in the card (.lyric) and in the text (.lyric-text), in rows
  const card = nowEl.querySelector('.lyric');
  const text = nowEl.querySelector('.lyric-text');
  const [cx, cy] = origin(card);
  const [tx, ty] = origin(text);
  const boxes = [...spans].map(s => {
    const [x, y] = origin(s);
    return { x0: x - cx, x1: x - cx + s.offsetWidth, top: y - cy, bottom: y - cy + s.offsetHeight, textX: x - tx, textY: y - ty, row: 0 };
  });
  const rows = [];
  boxes.forEach((b, j) => {
    const row = rows.at(-1);
    // (a word's box, the font's full height, can be taller than the row, so the rows' boxes overlap)
    if (row && b.top < (row.top + row.bottom) / 2) Object.assign(row, { bottom: Math.max(row.bottom, b.bottom), last: j });
    else rows.push({ top: b.top, bottom: b.bottom, last: j });
    b.row = rows.length - 1;
  });
  const r = i < 0 ? 0 : boxes[i].row;
  const row = rows[r];
  const bandTop = r ? (rows[r - 1].bottom + row.top) / 2 : 0;
  const bandBottom = r < rows.length - 1 ? (row.bottom + rows[r + 1].top) / 2 : card.clientHeight;
  const front = i < 0 ? 0 : i === row.last && f === 1 ? card.clientWidth : boxes[i].x0 + f * (boxes[i].x1 - boxes[i].x0);
  style.setProperty('--line-p', clamp(front / card.clientWidth, 0, 1).toFixed(4));
  style.setProperty('--row-top', `${bandTop.toFixed(1)}px`);
  style.setProperty('--row-h', `${(bandBottom - bandTop).toFixed(1)}px`);
  // The ball is a sing-along's: it sits on each word while it's sung (skipping a dash, which isn't), then hops to the next in at
  // most BALL_HOP s, as high as the hop is long, landing as that one starts. Before the first word it bounces on the beat; after
  // the last it rests. A wrapped line's next row is a fresh start: rather than arc back over the row, the ball shrinks away on
  // the row's last word and drops onto the next row's first.
  const stops = starts.map((s, j) => j).filter(j => ends[j] > starts[j]);
  if (!stops.length) return;
  const at = j => [boxes[j].textX + (boxes[j].x1 - boxes[j].x0) / 2, boxes[j].textY];
  let [x, y] = at(stops[0]);
  let hop = 0, size = 1;
  const n = stops.findLastIndex(j => starts[j] <= t);
  if (n < 0) {
    hop = Math.abs(Math.sin(Math.PI * (t - S.timing.beat0) * S.timing.bpm / 60)) * .6;
  } else if (n < stops.length - 1) {
    const a = stops[n], b = stops[n + 1];
    const d = Math.max(.05, Math.min(BALL_HOP, starts[b] - starts[a]));
    const u = clamp((t - (starts[b] - d)) / d, 0, 1);
    if (boxes[b].row !== boxes[a].row) {
      const v = 2 * u - 1;
      if (v < 0) { [x, y] = at(a); size = -v; }
      else { [x, y] = at(b); size = Math.min(1, 3 * v); hop = 1 - v * v; }
    } else {
      const [xa, ya] = at(a);
      const [xb, yb] = at(b);
      [x, y] = [xa + (xb - xa) * u, ya + (yb - ya) * u];
      hop = Math.sin(Math.PI * u) * Math.max(.4, d / BALL_HOP);
    }
  } else {
    [x, y] = at(stops[n]);
  }
  style.setProperty('--ball-x', `${x.toFixed(1)}px`);
  style.setProperty('--ball-y', `${y.toFixed(1)}px`);
  style.setProperty('--ball-hop', reducedMotion ? '0' : hop.toFixed(3));
  style.setProperty('--ball-s', size.toFixed(3));
}

// Two modes. Following docks the player and keeps the line being sung in view, whether or not the song is playing; turning it
// on goes straight to that line, or the nearest one. Otherwise the reader scrolls (manual mode, the default).
function setFollow(on) {
  S.follow = on ? 'on' : 'off';
  followBtn.setAttribute('aria-pressed', String(on));
  if (!on) {
    stopPageScroll();
    // (next frame, so that a scroll of the page's own that starts meanwhile, back to the top say, can say where it's headed)
    queuePlacement();
    return;
  }
  pageScrollAt = scrollY;
  // on phones the player docks at the bottom first, so that the line is centred above it
  if (!wide.matches) applyDock();
  const el = followTarget();
  if (el && !inView(el, .6)) scrollToLine(el);
  applyDock();
}
followBtn.addEventListener('click', () => setFollow(S.follow !== 'on'));

// Any scrolling by the reader (wheel, touch, keys, the scrollbar, a find-in-page jump) puts the page in manual mode for good,
// and stops any scroll of the page's own.
function readerScrolled() {
  if (fullscreenElement()) return;
  stopPageScroll();
  if (S.follow === 'on') setFollow(false);
}
addEventListener('wheel', readerScrolled, { passive: true });
addEventListener('touchmove', readerScrolled, { passive: true });
addEventListener('keydown', e => {
  const scrollKeys = ['ArrowUp', 'ArrowDown', 'PageUp', 'PageDown', 'Home', 'End', ' '];
  if (scrollKeys.includes(e.key) && !e.target.closest('input, select, textarea, button, [contenteditable]')) readerScrolled();
});
addEventListener('pointerdown', e => {
  const doc = document.documentElement;
  // the page's scrollbar, or the middle button's autoscroll
  if ((e.target === doc && (e.clientX >= doc.clientWidth || e.clientY >= doc.clientHeight)) || e.button === 1) readerScrolled();
});
addEventListener('scroll', () => {
  queuePlacement();
  // Scrolls with no input event to show for them (a find-in-page jump, say) count once they take the followed line away.
  if (S.follow !== 'on' || performance.now() < programmaticUntil || fullscreenElement() || !scrolledByReader()) return;
  const el = followTarget();
  if (el && !inView(el)) readerScrolled();
}, { passive: true });

function toggleNote(li, open) {
  const note = li.querySelector('.note');
  if (!note) return;
  open ??= note.hidden;
  note.hidden = !open;
  li.classList.toggle('open', open);
  li.querySelector('button.lyric')?.setAttribute('aria-expanded', String(open));
}
// "Unfold all" becomes "Collapse all" once every note is open.
const noteLines = [...lineEls.values()].filter(li => li.querySelector('.note'));
const showAllNotes = () => allNotesBtn.toggleAttribute('data-all-open', noteLines.every(li => li.classList.contains('open')));
document.querySelector('.lyrics').addEventListener('click', e => {
  const li = e.target.closest('.line');
  if (!li) return;
  if (e.target.closest('button.lyric')) {
    toggleNote(li);
    showAllNotes();
  } else if (e.target.closest('.from-here:not(:disabled)')) {
    playFromLine(li.dataset.sec, +li.dataset.n);
  }
});
// Every note opening or closing at once changes the page's height a lot. When following, the followed line goes back in view;
// otherwise the button stays put under the reader's pointer, rather than wherever the browser's scroll anchoring would take it.
allNotesBtn.addEventListener('click', () => {
  const open = !allNotesBtn.hasAttribute('data-all-open');
  const top = allNotesBtn.getBoundingClientRect().top;
  root.style.overflowAnchor = 'none';
  for (const li of noteLines) toggleNote(li, open);
  showAllNotes();
  if (S.follow === 'on' && followTarget()) {
    scrollToLine(followTarget());
  } else {
    scrollTo({ top: scrollY + allNotesBtn.getBoundingClientRect().top - top, behavior: 'instant' });
    pageScrollAt = scrollY;
    root.style.removeProperty('overflow-anchor');
  }
});

function renderNowCard() {
  const hint = nowCard.querySelector('.now-hint');
  const body = nowCard.querySelector('.now-body');
  const idle = S.playback === 'idle';
  hint.hidden = !idle;
  body.hidden = idle;
  if (idle) return;
  const el = nowEl;
  nowCard.querySelector('.now-stamp').textContent = el?.querySelector('.stamp')?.textContent ?? '';
  nowCard.querySelector('.now-line').textContent = el ? el.querySelector('.lyric-text').textContent : (S.playback === 'playing' ? '♪' : '');
  const note = el?.querySelector('.note');
  nowCard.querySelector('.now-note').replaceChildren(...(note ? [...note.cloneNode(true).childNodes] : []));
}
nowCard.querySelector('.side-play').addEventListener('click', () => play());

// ---------- transport ----------
function setPlayback(state) {
  S.playback = state;
  player.dataset.state = state;
  // for decorations that move only while the song plays (the Eurodance theme's blinking cursor)
  root.dataset.playback = state;
  deckPlay.setAttribute('aria-label', state === 'playing' ? 'Pause' : 'Play');
  renderNowCard();
  applyDock();
}
async function play() {
  if (S.audio === 'failed') retryAudio();
  if (!S.version) await switchVersion(select.value);
  await versionReady;
  if (S.playback === 'ended' || audio.ended) audio.currentTime = 0;
  setPlayback('playing');
  startRenderer().then(drawNow);
  await startSong();
}
// (once the track's video has loaded, unless the reader paused meanwhile)
async function startSong() {
  await videoLoaded();
  if (S.playback !== 'playing') return;
  try {
    await audio.play();
  } catch {
    setPlayback('paused');
  }
}
function pause() {
  // (a press of Play still waiting for the video is called off)
  if (audio.paused && S.playback === 'playing') setPlayback('paused');
  audio.pause();
}

audio.addEventListener('play', () => { if (S.playback !== 'playing') setPlayback('playing'); tick(); });
audio.addEventListener('pause', () => { if (!audio.ended) setPlayback('paused'); });
audio.addEventListener('ended', () => setPlayback('ended'));
audio.addEventListener('loadedmetadata', () => { scrub.max = audio.duration; timeDur.textContent = fmt(audio.duration); });
player.querySelector('.big-play').addEventListener('click', () => play());

// ---------- the audio failing to load ----------
// An error, or a load that stalls before the track's metadata comes, puts the player in its error state, with a Retry button in
// place of the Play button; Retry (or Play) loads the track again and plays it. Whatever was waiting for the track (a press of Play,
// a seek, a switch of tracks) goes ahead once it loads, from a retry or from a stalled load that comes through after all.
function setAudioState(state) {
  S.audio = state;
  player.dataset.audio = state;
  loadError.hidden = state !== 'failed';
}
function retryAudio() {
  // (a track that failed mid-song picks up where it stopped)
  const t = audio.currentTime;
  audio.load();
  if (t > 0) audio.addEventListener('loadedmetadata', () => { audio.currentTime = t; }, { once: true });
}
audio.addEventListener('loadstart', () => setAudioState('ok'));
audio.addEventListener('loadedmetadata', () => setAudioState('ok'));
audio.addEventListener('error', () => {
  // (a decoding error once the track has loaded isn't a failure to load it: Firefox reports one when it has no audio output, say,
  // and plays on)
  if (audio.readyState > HTMLMediaElement.HAVE_NOTHING && audio.error?.code === MediaError.MEDIA_ERR_DECODE) return;
  setAudioState('failed');
  if (!audio.paused) audio.pause();
});
audio.addEventListener('stalled', () => { if (audio.readyState === HTMLMediaElement.HAVE_NOTHING) setAudioState('failed'); });
loadError.querySelector('.retry').addEventListener('click', () => play());
deckPlay.addEventListener('click', () => (S.playback === 'playing' ? pause() : play()));

function showTime(t) {
  timeNow.textContent = fmt(t);
  scrub.value = t;
  scrub.style.setProperty('--pct', `${(t / (+scrub.max || 181)) * 100}%`);
}
function tick() {
  if (audio.paused) return;
  const t = audio.currentTime;
  showTime(t);
  setNowLine(lineAt(t));
  showLineProgress(t);
  drawNow();
  requestAnimationFrame(tick);
}
async function seek(t) {
  await versionReady;
  audio.currentTime = t;
  showTime(t);
  if (S.playback === 'idle' || S.playback === 'ended') setPlayback('paused');
  setNowLine(lineAt(t));
  showLineProgress(t);
  startRenderer().then(drawNow);
}
scrub.addEventListener('input', () => seek(+scrub.value));

async function playFromLine(sec, n) {
  if (!S.version) await switchVersion(select.value);
  const ln = S.timing?.lines.find(l => l.sec === sec && l.n === n);
  // ▶ beside a line follows the song from there (the line is already in view): from when it comes up, with its words' times,
  // since a little earlier the line before may still be being sung
  if (ln) await seek(Math.max(0, lineTimes.get(ln).starts ? lineTimes.get(ln).on : ln.start - .15));
  setFollow(true);
  await play();
}

function markUnsung() {
  const sung = S.timing && new Set(S.timing.lines.map(l => `${l.sec}.${l.n}`));
  for (const [key, el] of lineEls) el.classList.toggle('unsung', !!sung && !sung.has(key));
}

function drawTicks() {
  const ticks = player.querySelector('.ticks');
  ticks.replaceChildren();
  if (!S.timing) return;
  for (const s of S.timing.segs.filter(s => s.kind === 'chorus' || (s.kind === 'line' && s.n === 1))) {
    const span = document.createElement('span');
    span.style.left = `${(s.start / S.timing.dur) * 100}%`;
    span.textContent = s.kind === 'chorus' ? 'C' : s.sec;
    ticks.append(span);
  }
}

// ---------- page theme: the whole page dresses as the selected version's video ----------
// Each track's page arrives in its theme; switching cross-fades the old look into the new one.
root.dataset.playback = S.playback;
// A whole number of device pixels, close to one CSS pixel, for textures that must fall on whole pixels to stay sharp (the
// piano-rock theme's scanlines); it changes with the zoom level and when the window moves to a screen of another density.
function trackDevicePixel() {
  const dpr = devicePixelRatio;
  root.style.setProperty('--dpx', `${Math.max(1, Math.round(dpr)) / dpr}px`);
  matchMedia(`(resolution: ${dpr}dppx)`).addEventListener('change', trackDevicePixel, { once: true });
}
trackDevicePixel();
function setTheme(style) {
  if (root.dataset.theme === style) return;
  const apply = () => {
    root.dataset.theme = style;
    // The new look can move the lines; keep the followed one in view.
    const el = followTarget();
    if (S.follow === 'on' && el && !inView(el)) scrollToLine(el);
  };
  if (reducedMotion || !document.startViewTransition || document.hidden) apply();
  else document.startViewTransition(apply);
}

// The address bar and title name the track that's on, so that a link shared from here opens on it too. (Each track's page is the
// same page, opening on that track, so the address changes in place, without a page load or a history entry.)
function showTrackAddress(v) {
  const url = new URL(v.url, location.href);
  url.search = location.search;
  url.hash = location.hash;
  if (url.href !== location.href) history.replaceState(history.state, '', url);
  document.title = v.pageTitle + document.title.slice(document.title.lastIndexOf(' | '));
}

// Switching tracks starts the new one from the top: it plays on if the player was playing, or else waits at 0:00; following goes
// to its first line.
async function switchVersion(id) {
  const v = versions.get(id);
  if (!v || v === S.version) return;
  const wasPlaying = S.playback === 'playing';
  S.version = v;
  select.value = id;
  showTrackAddress(v);
  // until playback starts, the stage shows this version's own title card
  player.dataset.style = styleOf(v);
  setTheme(styleOf(v));
  if (poster.getAttribute('src') !== v.poster) poster.src = v.poster;
  for (const card of document.querySelectorAll('.tape-card')) card.classList.toggle('playing', card.dataset.version === id);
  versionReady = (async () => {
    const tm = await loadTiming(v);
    // (a switch to another track meanwhile has taken over)
    if (S.version !== v) return;
    S.timing = tm;
    const loaded = new Promise(ok => audio.addEventListener('loadedmetadata', ok, { once: true }));
    audio.src = abs(v.audioMP3 && !audio.canPlayType('audio/mp4; codecs="mp4a.40.2"') ? v.audioMP3 : v.audio);
    await loaded;
    // (a new source starts at 0:00 anyway, but without this seek, Firefox can stall on a later seek far into a track it has
    // loaded before)
    audio.currentTime = 0;
  })();
  await versionReady;
  if (S.version !== v) return;
  // a version in another style needs that style's engine; otherwise the current one just re-times itself
  if (rendererStarting && styleOf(v) !== rendererStyle) startRenderer().then(drawNow);
  else if (renderer && S.timing) renderer.setTiming(S.timing);
  drawTicks();
  markUnsung();
  showTime(audio.currentTime);
  if (!jukebox.playing()) showMediaMetadata(v);
  // (after a track that ended, the new one waits at its start)
  if (S.playback === 'ended') setPlayback('paused');
  setNowLine(lineAt(audio.currentTime));
  showLineProgress(audio.currentTime);
  const el = followTarget();
  if (S.follow === 'on' && el && !inView(el, .6)) scrollToLine(el);
  if (wasPlaying) {
    setPlayback('playing');
    await startSong();
  } else {
    drawNow();
  }
}
select.addEventListener('change', () => switchVersion(select.value));
for (const btn of document.querySelectorAll('.play-version')) {
  btn.addEventListener('click', async () => {
    // (the track that's already on starts over)
    if (versions.get(btn.dataset.version) === S.version) await seek(0);
    else await switchVersion(btn.dataset.version);
    play();
  });
}

// ---------- the jukebox: the other genres, audio only ----------
// Each cassette plays in place through a second, independent player that never touches the album's track, lyrics or
// theme. Only one of the two players plays at a time: starting either pauses the other, and the system's media controls
// drive whichever was started last.
let jukeboxLast = false;
function showMediaMetadata(v) {
  if (!('mediaSession' in navigator)) return;
  navigator.mediaSession.metadata = new MediaMetadata({
    title: `We Didn't Start the Scaling (${v.genre})`,
    artist: `Domenic & Claude, with ${v.model}`,
    // an album track's own poster; the jukebox's genres, which have no video, use the first track's
    artwork: [{ src: abs(v.poster ?? data.versions[0].poster), type: 'image/jpeg' }]
  });
}
const jukebox = (() => {
  const el = new Audio();
  el.preload = 'none';
  let card = null;   // the cassette in the deck
  const cards = new Map([...document.querySelectorAll('.cassette')].map(c => [c.dataset.version, c]));
  function render() {
    for (const [id, c] of cards) {
      const loaded = c === card;
      const playing = loaded && !el.paused;
      c.classList.toggle('loaded', loaded);
      c.classList.toggle('playing', playing);
      c.querySelector('.cassette-play').setAttribute('aria-label', `${playing ? 'Pause' : 'Play'} ${jukeboxVersions.get(id).title}`);
      c.querySelector('.cassette-seek').disabled = !loaded;
      if (!loaded) {
        c.querySelector('.cassette-now').textContent = '0:00';
        c.querySelector('.cassette-seek').value = 0;
        c.style.removeProperty('--pct');
      }
    }
  }
  function showTime() {
    if (!card) return;
    const seekEl = card.querySelector('.cassette-seek');
    card.querySelector('.cassette-now').textContent = fmt(el.currentTime);
    seekEl.value = el.currentTime;
    card.style.setProperty('--pct', `${(el.currentTime / +seekEl.max) * 100}%`);
  }
  function toggle(id) {
    const c = cards.get(id);
    if (c !== card) {
      card = c;
      el.src = abs(jukeboxVersions.get(id).audio);
      render();
    }
    if (el.paused) el.play().catch(render);
    else el.pause();
  }
  for (const [id, c] of cards) {
    c.querySelector('.cassette-play').addEventListener('click', () => toggle(id));
    c.querySelector('.cassette-seek').addEventListener('input', e => {
      if (c !== card) return;
      el.currentTime = +e.target.value;
      showTime();
    });
  }
  el.addEventListener('play', () => {
    jukeboxLast = true;
    pause();
    showMediaMetadata(jukeboxVersions.get(card.dataset.version));
    render();
  });
  el.addEventListener('pause', render);
  el.addEventListener('ended', render);
  el.addEventListener('timeupdate', showTime);
  return {
    audio: el,
    playing: () => !el.paused,
    resume: () => el.play().catch(render),
    pause: () => el.pause(),
    seek: t => { el.currentTime = t; showTime(); },
    state: () => ({ version: card?.dataset.version ?? null, playing: !el.paused, time: el.currentTime })
  };
})();
audio.addEventListener('play', () => {
  jukeboxLast = false;
  jukebox.pause();
  if (S.version) showMediaMetadata(S.version);
});
if ('mediaSession' in navigator) {
  navigator.mediaSession.setActionHandler('play', () => (jukeboxLast ? jukebox.resume() : play()));
  navigator.mediaSession.setActionHandler('pause', () => { pause(); jukebox.pause(); });
  navigator.mediaSession.setActionHandler('seekto', e => {
    if (jukeboxLast) jukebox.seek(e.seekTime);
    else if (!('loading' in player.dataset)) seek(e.seekTime);
  });
}

// ---------- fullscreen ----------
// The screen (the video, its poster and the play button) goes fullscreen, letterboxed on black; the stage it came from keeps
// its size in the page, and the player doesn't dock or undock meanwhile, so leaving fullscreen puts everything back as it was.
// The canvas re-renders at the fullscreen size through the resize observer. iPhone Safari can't make an element fullscreen,
// so there the button stays hidden.
const fullscreenElement = () => document.fullscreenElement ?? document.webkitFullscreenElement ?? null;
const fullscreenSupported = !!(document.fullscreenEnabled || document.webkitFullscreenEnabled);
let scrollBeforeFullscreen = 0;
let idleTimer = 0;
function enterFullscreen() {
  if (fullscreenElement()) return;
  scrollBeforeFullscreen = scrollY;
  const request = screenEl.requestFullscreen ?? screenEl.webkitRequestFullscreen;
  request?.call(screenEl, { navigationUI: 'hide' })?.catch?.(() => {});
}
function exitFullscreen() {
  if (fullscreenElement() !== screenEl) return;
  (document.exitFullscreen ?? document.webkitExitFullscreen)?.call(document)?.catch?.(() => {});
}
const toggleFullscreen = () => (fullscreenElement() === screenEl ? exitFullscreen() : enterFullscreen());
// In fullscreen the exit button and the pointer hide after a moment without movement.
function showScreenControls() {
  delete screenEl.dataset.idle;
  clearTimeout(idleTimer);
  idleTimer = setTimeout(() => { if (fullscreenElement() === screenEl) screenEl.dataset.idle = ''; }, 2500);
}
function fullscreenChanged() {
  const on = fullscreenElement() === screenEl;
  if (on === player.hasAttribute('data-fullscreen')) return;
  player.toggleAttribute('data-fullscreen', on);
  fsBtn.setAttribute('aria-pressed', String(on));
  if (on) {
    if (document.activeElement === fsBtn) exitBtn.focus();
    showScreenControls();
  } else {
    clearTimeout(idleTimer);
    delete screenEl.dataset.idle;
    if (screenEl.contains(document.activeElement)) fsBtn.focus({ preventScroll: true });
    // Put the page back where it was (the window may have resized in between), or, when following, where the song is now.
    // (The browser scrolls the page meanwhile too; that isn't the reader.)
    programmaticUntil = performance.now() + 250;
    requestAnimationFrame(() => {
      pageScrollAt = scrollY;
      if (S.follow === 'on') {
        applyDock();
        const el = followTarget();
        if (el && !inView(el)) scrollToLine(el);
      } else {
        scrollTo({ top: scrollBeforeFullscreen, behavior: 'instant' });
      }
      applyDock();
    });
  }
  requestAnimationFrame(() => { updateScale(); drawNow(); });
}
if (fullscreenSupported) fsBtn.hidden = false;
document.addEventListener('onfullscreenchange' in document ? 'fullscreenchange' : 'webkitfullscreenchange', fullscreenChanged);
fsBtn.addEventListener('click', toggleFullscreen);
exitBtn.addEventListener('click', exitFullscreen);
screenEl.addEventListener('dblclick', e => {
  if (fullscreenSupported && !e.target.closest('button')) toggleFullscreen();
});
screenEl.addEventListener('pointermove', () => { if (fullscreenElement() === screenEl) showScreenControls(); });
const textField = el => el.closest?.('textarea, select, [contenteditable]:not([contenteditable="false"])') ||
  (el.tagName === 'INPUT' && !['range', 'checkbox', 'radio', 'button', 'submit', 'reset', 'color', 'file', 'image'].includes(el.type));
addEventListener('keydown', e => {
  if (e.key.toLowerCase() !== 'f' || e.ctrlKey || e.metaKey || e.altKey || e.repeat || textField(e.target)) return;
  if (!fullscreenSupported) return;
  e.preventDefault();
  toggleFullscreen();
});

// ---------- docking ----------
// The player is always on screen. It sits in the cover while the cover's video is (nearly) in view; otherwise, or whenever
// the page is following, it docks (moving with a FLIP animation): beside the lyrics on wide screens while that sticky spot
// would show it, and in a bar at the bottom of the screen otherwise. Each boundary has a gap between the thresholds for
// leaving and coming back, so that scrolling to and fro near one can't bounce the player between places. It's judged from
// where a scroll of the page's own is headed, so following or going back to the top moves the player once, straight away.
let sidePlayerH = 0;
function desiredDock() {
  const dy = pageScrollTo === null ? 0 : scrollY - pageScrollTo;
  if (S.follow !== 'on') {
    // how much of the cover's video has scrolled off the top of the screen
    const r = slot.getBoundingClientRect();
    const videoH = (Math.min(r.width, 960) - 24) * 9 / 16;
    const hidden = clamp(-(r.top + dy + 12) / videoH, 0, 1);
    if (hidden < (S.dock === 'none' ? 1 / 3 : .1)) return 'none';
  }
  if (!wide.matches) return 'bottom';
  // Where the side panel would hold the player: it's sticky, but the end of the lyrics pushes it up and off the screen.
  const inner = sideTarget.parentElement;
  const css = getComputedStyle(inner);
  const h = S.dock === 'side' ? player.offsetHeight : sidePlayerH || inner.clientWidth * 9 / 16 + 160;
  const below = nowCard.offsetHeight + (parseFloat(css.rowGap) || 0);
  const g = lyricsGrid.getBoundingClientRect();
  const top = Math.min(Math.max(g.top + dy, parseFloat(css.top) || 0), g.bottom + dy - h - below);
  const shown = (Math.min(top + h, innerHeight) - Math.max(top, 0)) / h;
  return shown >= (S.dock === 'side' ? .75 : .95) ? 'side' : 'bottom';
}
function setBottomDockHeight() {
  document.documentElement.style.setProperty('--bottom-dock-h', S.dock === 'bottom' ? `${bottomDock.offsetHeight}px` : '0px');
}
function flipMove(el, target, mutate) {
  const first = el.getBoundingClientRect();
  target.append(el);
  mutate();
  const last = el.getBoundingClientRect();
  if (reducedMotion || !first.width || !last.width) return;
  const dx = first.left - last.left;
  const dy = first.top - last.top;
  const s = first.width / last.width;
  el.animate([
    { transformOrigin: 'top left', translate: `${dx}px ${dy}px`, scale: `${s}` },
    { transformOrigin: 'top left', translate: '0 0', scale: '1' }
  ], { duration: 420, easing: 'cubic-bezier(.2, .8, .2, 1)' });
}
function applyDock(scrolled = true) {
  const want = desiredDock();
  // Moving the player would take the video out of fullscreen; it docks when fullscreen ends instead.
  if (want === S.dock || fullscreenElement()) return;
  // A note changing size beside the lyrics can push the player out of the side panel, at the end of the lyrics, but only
  // scrolling brings it back, so that it can't bounce in and out as the song's notes come and go.
  if (!scrolled && want === 'side' && S.dock === 'bottom') return;
  if (S.dock === 'none') {
    slot.style.setProperty('--slot-h', getComputedStyle(slot).height);
    slot.classList.add('empty');
  }
  const target = want === 'side' ? sideTarget : want === 'bottom' ? bottomDock : slot;
  flipMove(player, target, () => {
    player.classList.toggle('docked-side', want === 'side');
    player.classList.toggle('docked-bottom', want === 'bottom');
  });
  if (want === 'none') slot.classList.remove('empty');
  S.dock = want;
  setBottomDockHeight();
  requestAnimationFrame(() => {
    if (S.dock === 'side') sidePlayerH = player.offsetHeight;
    updateScale();
    drawNow();
  });
}
// Placement follows scrolling and anything that moves the lyrics or the side panel (notes, themes, the now-playing card).
let placementQueued = false;
let placementScrolled = false;
function queuePlacement(scrolled = true) {
  placementScrolled ||= scrolled;
  if (placementQueued) return;
  placementQueued = true;
  requestAnimationFrame(() => {
    const scrolled = placementScrolled;
    placementQueued = placementScrolled = false;
    applyDock(scrolled);
  });
}
new ResizeObserver(() => queuePlacement(false)).observe(lyricsGrid);
new ResizeObserver(() => queuePlacement(false)).observe(nowCard);
addEventListener('resize', () => queuePlacement());
wide.addEventListener('change', () => applyDock());
// (the browser may have restored a scroll position further down the page)
queuePlacement();
// Back to top: the player returns to the cover, and the page to manual mode.
q('.undock').addEventListener('click', () => {
  setFollow(false);
  scrollPageTo(0);
  applyDock();
});
const canvasObserver = new ResizeObserver(() => { updateScale(); if (S.dock === 'bottom') setBottomDockHeight(); });
canvasObserver.observe(canvas);
addEventListener('resize', updateScale);

// A link to #changelog (the YouTube videos' descriptions have one, to each track's page) opens the track's history, which is
// otherwise folded, and brings it into view.
function openLinkedChangelog() {
  if (location.hash !== '#changelog') return;
  const log = document.querySelector(`.changelog .log[data-for="${select.value}"]`);
  if (!log) return;
  log.open = true;
  log.scrollIntoView({ block: 'start' });
}
openLinkedChangelog();
addEventListener('hashchange', openLinkedChangelog);

// Warm up once the page is idle, so pressing play is instant: the track's audio and its video's engine load side by side.
(window.requestIdleCallback ?? (f => setTimeout(f, 1500)))(() => {
  switchVersion(select.value);
  startRenderer();
});

// Hooks for the automated tests and for debugging (?debug shows render stats in the console).
window.__scaling = {
  state: () => ({ ...S, version: S.version?.id, timing: undefined, now: nowEl?.id ?? null, scale: appliedScale, quality: QUALITY[qi], qualityStep: step, engineLevels, renderer: renderer?.kind ?? null, style: renderer?.style ?? null, lastDrawMs, lowRes: lastLowRes, time: audio.currentTime, canvasCss: canvas.clientWidth, fullscreen: fullscreenElement() === screenEl }),
  audio,
  jukebox: () => jukebox.state(),
  jukeboxAudio: jukebox.audio,
  ready: () => startRenderer()
};
if (new URLSearchParams(location.search).has('debug')) setInterval(() => console.log(window.__scaling.state()), 2000);
