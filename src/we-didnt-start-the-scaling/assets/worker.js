// Renders the music video off the main thread. The page transfers an OffscreenCanvas and posts song times; this worker draws frames with the same engine the MP4 was rendered with.
// An engine's optional hooks: STYLE_READY (a promise to settle before the first frame), STYLE_LOWRES() (how many pictures the last
// frame drew as stand-ins), STYLE_STALE (set here: call it when a stand-in's picture arrives), QUALITY_LEVELS and setQuality(level)
// (the quality levels the page's controller steps through: 0 the video as designed, each cheaper than the last, its type always at
// full resolution), STYLE_FINISH() (finish the GPU's work for the frame just drawn, so that the page's measure of it includes that)
// and STYLE_INFO() (what the frame was, for the page's ?debug overlay), and STYLE_WARM (a promise that settles once a style that
// warms up after its first frame, building what its scenes need between frames, has finished: until then the page holds the song).
self.onmessage = async (e) => {
  const m = e.data;
  try {
    if (m.type === 'init') {
      self.OUT_CANVAS = m.canvas;
      self.RENDER_SCALE = m.scale;
      self.TIMING = m.timing;
      // the folder of the pictures a style loads itself, for styles that do (they set STYLE_READY, which must settle before
      // drawing); such a style loads the pictures for the playhead first, and says when one it drew as a stand-in has arrived
      self.STYLE_BASE = m.images;
      self.STYLE_START = m.start;
      self.STYLE_STALE = () => self.postMessage({ type: 'stale' });
      // The style's fonts download alongside its script, and are in before the first frame (the script draws no text as it loads).
      // (The script is fetched, then run: importScripts() would block this thread while it downloads, and the font loads with it.)
      const fonts = Promise.all(m.fonts.map(async ([family, url]) => {
        const face = new FontFace(family, `url(${url})`);
        await face.load();
        self.fonts.add(face);
      }));
      const r = await fetch(m.script);
      if (!r.ok) throw new Error(`${r.status} ${m.script}`);
      const code = URL.createObjectURL(new Blob([await r.text(), `\n//# sourceURL=${m.script}\n`], { type: 'text/javascript' }));
      importScripts(code);
      URL.revokeObjectURL(code);
      await fonts;
      if (self.STYLE_READY) await self.STYLE_READY;
      self.postMessage({ type: 'ready', levels: self.QUALITY_LEVELS ?? 0 });
      Promise.resolve(self.STYLE_WARM).catch(() => {}).then(() => self.postMessage({ type: 'warm' }));
    } else if (m.type === 'frame') {
      const t0 = performance.now();
      renderFrame(m.t);
      self.STYLE_FINISH?.();
      self.postMessage({ type: 'drawn', ms: performance.now() - t0, lowRes: self.STYLE_LOWRES?.() ?? 0, info: m.info ? self.STYLE_INFO?.() : undefined });
    } else if (m.type === 'scale') {
      setRenderScale(m.scale);
    } else if (m.type === 'quality') {
      self.setQuality?.(m.level);
    } else if (m.type === 'timing') {
      setTiming(m.timing);
    }
  } catch (err) {
    self.postMessage({ type: 'error', message: String(err?.stack ?? err) });
  }
};
