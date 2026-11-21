// Chord Whale engine, JavaScript port of whale_engine (Python).
// Same numbers, same decisions: params, chroma, templates, verify (incl. exact-note
// check), spectral-flux onsets and YIN tuner. Runs in the browser and in Node.
const WhaleEngine = (() => {
  const P = {
    sr: 16000, nfft_fast: 2048, nfft_full: 4096, onset_delay: 0.02, fmin: 70, fmax: 1400,
    peak_rel: 0.15, floor_mult: 1.5, bass_rel: 0.30, harmonics: 4, harm_decay: 0.6, bass_bonus: 0.03,
    verify_margin: 0.05, type_prior: { '5': -0.08 }, extra_harmonics: 10, extra_decay: 0.6,
    leak_alpha: 1.0, leak_harmonics: 5, leak_decay: 0.6,
    note_min_rel: 0.08, note_harmonics: 4, note_overtones: 8, note_cents: 35, note_fmax: 4000,
    missing_rel: 0.10, extra_ratio: 2.5, extra_add: 0.25, fast_confidence: 0.06,
    onset_ratio: 1.8, onset_min_flux: 1.0, onset_log_gain: 1.0, onset_fmax: 2000, onset_min_rise: 0.005,
    onset_history: 0.3, onset_min_gap: 0.2, tuner_threshold: 0.12, tuner_fmin: 60, tuner_fmax: 1000,
  };

  // ------------------------------------------------------------ theory
  const SHARPS = ['C', 'C#', 'D', 'D#', 'E', 'F', 'F#', 'G', 'G#', 'A', 'A#', 'B'];
  const DISPLAY = ['C', 'C#', 'D', 'Eb', 'E', 'F', 'F#', 'G', 'Ab', 'A', 'Bb', 'B'];
  const PC = {}; SHARPS.forEach((n, i) => PC[n] = i);
  Object.assign(PC, { Db: 1, Eb: 3, Gb: 6, Ab: 8, Bb: 10, Cb: 11, Fb: 4, 'E#': 5, 'B#': 0 });
  const OPEN_STRINGS = [40, 45, 50, 55, 59, 64];
  const TYPES = {
    '': [0, 4, 7], 'm': [0, 3, 7], '7': [0, 4, 7, 10], 'maj7': [0, 4, 7, 11], 'm7': [0, 3, 7, 10],
    'sus2': [0, 2, 7], 'sus4': [0, 5, 7], 'dim': [0, 3, 6], 'aug': [0, 4, 8], '5': [0, 7],
  };
  const TYPE_KEYS = Object.keys(TYPES);
  const ALIASES = {
    '': '', 'maj': '', 'M': '', 'major': '', 'm': 'm', 'min': 'm', '-': 'm', 'minor': 'm',
    '7': '7', 'dom7': '7', 'maj7': 'maj7', 'M7': 'maj7', 'Maj7': 'maj7', 'ma7': 'maj7', 'Δ': 'maj7', 'Δ7': 'maj7',
    'm7': 'm7', 'min7': 'm7', '-7': 'm7', 'mi7': 'm7', 'sus2': 'sus2', '2': 'sus2', 'sus4': 'sus4', 'sus': 'sus4',
    '4': 'sus4', 'dim': 'dim', 'o': 'dim', '°': 'dim', 'aug': 'aug', '+': 'aug', '5': '5',
    '6': '', 'add9': '', 'add2': '', '9': '7', 'm6': 'm', 'm9': 'm7', 'maj9': 'maj7', '7sus4': 'sus4',
    'dim7': 'dim', 'm7b5': 'dim',
  };
  const CHORD_RE = /^([A-G])([#b]?)([^/\s]*)(?:\/([A-G][#b]?))?$/;
  const mod = (a, n = 12) => ((a % n) + n) % n;

  class Chord {
    constructor(root, type, bass = null) { this.root = mod(root); this.type = type; this.bass = bass == null ? null : mod(bass); if (this.bass === this.root) this.bass = null; }
    get tones() { const t = new Set(TYPES[this.type].map(i => mod(this.root + i))); if (this.bass != null) t.add(this.bass); return t; }
    get name() { let s = DISPLAY[this.root] + this.type; if (this.bass != null) s += '/' + DISPLAY[this.bass]; return s; }
    transposed(n) { return new Chord(this.root + n, this.type, this.bass == null ? null : this.bass + n); }
  }
  const isChord = tok => { const m = CHORD_RE.exec(tok.trim()); return !!m && (m[3] in ALIASES); };
  function parse(tok) {
    if (tok instanceof Chord) return tok;
    const m = CHORD_RE.exec(String(tok).trim());
    if (!m || !(m[3] in ALIASES)) throw new Error('not a chord: ' + tok);
    return new Chord(PC[m[1] + m[2]], ALIASES[m[3]], m[4] ? PC[m[4]] : null);
  }

  const OPEN_SHAPES = {
    '0,': [-1, 3, 2, 0, 1, 0], '0,7': [-1, 3, 2, 3, 1, 0], '0,maj7': [-1, 3, 2, 0, 0, 0],
    '2,': [-1, -1, 0, 2, 3, 2], '2,m': [-1, -1, 0, 2, 3, 1], '2,7': [-1, -1, 0, 2, 1, 2],
    '2,sus4': [-1, -1, 0, 2, 3, 3], '2,sus2': [-1, -1, 0, 2, 3, 0], '2,m7': [-1, -1, 0, 2, 1, 1],
    '2,maj7': [-1, -1, 0, 2, 2, 2],
    '4,': [0, 2, 2, 1, 0, 0], '4,m': [0, 2, 2, 0, 0, 0], '4,7': [0, 2, 0, 1, 0, 0],
    '4,m7': [0, 2, 0, 0, 0, 0], '4,sus4': [0, 2, 2, 2, 0, 0], '4,5': [0, 2, 2, -1, -1, -1],
    '5,maj7': [-1, -1, 3, 2, 1, 0],
    '7,': [3, 2, 0, 0, 0, 3], '7,7': [3, 2, 0, 0, 0, 1],
    '9,': [-1, 0, 2, 2, 2, 0], '9,m': [-1, 0, 2, 2, 1, 0], '9,7': [-1, 0, 2, 0, 2, 0],
    '9,m7': [-1, 0, 2, 0, 1, 0], '9,maj7': [-1, 0, 2, 1, 2, 0], '9,sus4': [-1, 0, 2, 2, 3, 0],
    '9,sus2': [-1, 0, 2, 2, 0, 0], '9,5': [-1, 0, 2, 2, -1, -1],
    '11,7': [-1, 2, 1, 2, 0, 2],
  };
  const E_FORM = { '': [0, 2, 2, 1, 0, 0], 'm': [0, 2, 2, 0, 0, 0], '7': [0, 2, 0, 1, 0, 0], 'm7': [0, 2, 0, 0, 0, 0], 'maj7': [0, -1, 1, 1, 0, -1], 'sus4': [0, 2, 2, 2, 0, 0], '5': [0, 2, 2, -1, -1, -1] };
  const A_FORM = { '': [-1, 0, 2, 2, 2, 0], 'm': [-1, 0, 2, 2, 1, 0], '7': [-1, 0, 2, 0, 2, 0], 'm7': [-1, 0, 2, 0, 1, 0], 'maj7': [-1, 0, 2, 1, 2, 0], 'sus4': [-1, 0, 2, 2, 3, 0], 'sus2': [-1, 0, 2, 2, 0, 0], 'dim': [-1, 0, 1, 2, 1, -1], '5': [-1, 0, 2, 2, -1, -1] };
  const SMALL = { 'dim': [-1, 0, 1, 2, 1, -1], 'aug': [-1, 0, 3, 2, 2, 1] };

  function fingering(chIn) {
    const ch = parse(chIn);
    if (ch.bass != null) { const sl = slashShape(ch); if (sl) return sl; }
    const key = ch.root + ',' + ch.type;
    if (OPEN_SHAPES[key]) return OPEN_SHAPES[key].slice();
    const fe = mod(ch.root - 4), fa = mod(ch.root - 9);
    const c = [];
    if (E_FORM[ch.type]) c.push([fe || 12, E_FORM[ch.type]]);
    if (A_FORM[ch.type]) c.push([fa || 12, A_FORM[ch.type]]);
    if (SMALL[ch.type]) c.push([fa || 12, SMALL[ch.type]]);
    let best = c[0]; for (const x of c) if (x[0] < best[0]) best = x;
    return best[1].map(b => b < 0 ? -1 : b + best[0]);
  }
  function slashShape(ch) {
    const shape = fingering(new Chord(ch.root, ch.type));
    for (const s of [0, 1]) for (let f = 0; f < 5; f++) {
      if (mod(OPEN_STRINGS[s] + f) === ch.bass) {
        const n = shape.slice(); n[s] = f; if (s === 1) n[0] = -1;
        const fr = n.filter(x => x > 0);
        if (!fr.length || Math.max(...fr) - Math.min(...fr) <= 3) return n;
      }
    }
    return null;
  }
  const shapeTones = sh => new Set(sh.map((f, s) => f >= 0 ? mod(OPEN_STRINGS[s] + f) : null).filter(x => x != null));
  const shapeNotes = sh => sh.map((f, s) => f >= 0 ? [s, OPEN_STRINGS[s] + f] : null).filter(Boolean);

  // ------------------------------------------------------------ FFT (radix-2, in place)
  const fftCache = {};
  function fftTables(n) {
    if (fftCache[n]) return fftCache[n];
    const rev = new Uint32Array(n); const bits = Math.log2(n);
    for (let i = 0; i < n; i++) { let r = 0; for (let b = 0; b < bits; b++) r |= ((i >> b) & 1) << (bits - 1 - b); rev[i] = r; }
    const cos = new Float64Array(n / 2), sin = new Float64Array(n / 2);
    for (let i = 0; i < n / 2; i++) { cos[i] = Math.cos(2 * Math.PI * i / n); sin[i] = -Math.sin(2 * Math.PI * i / n); }
    const hann = new Float64Array(n); for (let i = 0; i < n; i++) hann[i] = 0.5 - 0.5 * Math.cos(2 * Math.PI * i / (n - 1));
    return (fftCache[n] = { rev, cos, sin, hann });
  }
  // |rfft(x * hann)|, length n/2+1
  function magSpectrum(x, n) {
    const { rev, cos, sin, hann } = fftTables(n);
    const re = new Float64Array(n), im = new Float64Array(n);
    for (let i = 0; i < n; i++) re[rev[i]] = (x[i] || 0) * hann[i];
    for (let size = 2; size <= n; size <<= 1) {
      const half = size >> 1, step = n / size;
      for (let i = 0; i < n; i += size) for (let j = 0; j < half; j++) {
        const k = j * step, a = i + j, b = a + half;
        const tr = re[b] * cos[k] - im[b] * sin[k], ti = re[b] * sin[k] + im[b] * cos[k];
        re[b] = re[a] - tr; im[b] = im[a] - ti; re[a] += tr; im[a] += ti;
      }
    }
    const out = new Float64Array(n / 2 + 1);
    for (let i = 0; i <= n / 2; i++) out[i] = Math.hypot(re[i], im[i]);
    return out;
  }
  const median = arr => { if (!arr.length) return 0; const s = Array.from(arr).sort((a, b) => a - b); const m = s.length >> 1; return s.length % 2 ? s[m] : (s[m - 1] + s[m]) / 2; };

  // ------------------------------------------------------------ features
  const tabCache = {};
  function tables(n) {
    if (tabCache[n]) return tabCache[n];
    const band = [], pcs = [], freqs = [];
    for (let i = 0; i <= n / 2; i++) { const f = i * P.sr / n; if (f > P.fmin && f < P.fmax) { band.push(i); freqs.push(f); pcs.push(mod(Math.round(12 * Math.log2(f / 440) + 69))); } }
    return (tabCache[n] = { band, pcs, freqs });
  }
  function analyse(frame, n) {
    const { band, pcs, freqs } = tables(n);
    const spec = magSpectrum(frame, n);
    let ss = 0; for (let i = 0; i < n; i++) ss += (frame[i] || 0) ** 2;
    const level = Math.sqrt(ss / n);
    const mag = band.map(i => Math.sqrt(spec[i]));
    const mx = Math.max(...mag);
    if (!(mx > 0)) return { chroma: new Float64Array(12), bass: -1, level, peaks: [], spectrum: spec };
    const floor = median(mag);
    const thr = Math.max(P.peak_rel * mx, P.floor_mult * floor);
    const c = new Float64Array(12); const keep = [];
    for (let i = 1; i < mag.length - 1; i++) if (mag[i] > mag[i - 1] && mag[i] > mag[i + 1] && mag[i] > thr) { keep.push(i); c[pcs[i]] += mag[i] - floor; }
    let nn = 0; for (const v of c) nn += v * v; nn = Math.sqrt(nn); if (nn > 0) for (let i = 0; i < 12; i++) c[i] /= nn;
    const strong = keep.filter(i => mag[i] > P.bass_rel * mx);
    return { chroma: c, bass: strong.length ? pcs[strong[0]] : -1, level, peaks: keep.map(i => [freqs[i], mag[i]]), spectrum: spec };
  }

  // ------------------------------------------------------------ templates
  const HSHIFT = h => Math.round(12 * Math.log2(h));
  function profile(pcset, harmonics = 4, decay = 0.6) {
    const v = new Float64Array(12);
    for (const n of pcset) for (let h = 1; h <= harmonics; h++) v[mod(n + HSHIFT(h))] += decay ** (h - 1);
    let s = 0; for (const x of v) s += x * x; s = Math.sqrt(s); for (let i = 0; i < 12; i++) v[i] /= s;
    return v;
  }
  const BANK = (() => {
    const names = [], roots = [], mats = [], tonesets = [], prior = [];
    for (let r = 0; r < 12; r++) for (const t of TYPE_KEYS) {
      names.push([r, t]); roots.push(r);
      const ts = new Set(TYPES[t].map(i => mod(r + i))); tonesets.push(ts);
      mats.push(profile(ts, P.harmonics, P.harm_decay)); prior.push(P.type_prior[t] || 0);
    }
    return { names, roots, mats, tonesets, prior };
  })();
  const LEAK = (() => {
    const H = Array.from({ length: 12 }, () => new Float64Array(12));
    for (let n = 0; n < 12; n++) for (let h = 2; h <= P.leak_harmonics; h++) H[n][mod(n + HSHIFT(h))] += P.leak_decay ** (h - 1);
    return H;
  })();
  const dot = (a, b) => { let s = 0; for (let i = 0; i < 12; i++) s += a[i] * b[i]; return s; };
  function scores(f) { return BANK.mats.map((m, i) => dot(m, f.chroma) + P.bass_bonus * (BANK.roots[i] === f.bass ? 1 : 0) + BANK.prior[i]); }
  function detect(f) {
    if (!f.chroma.some(x => x)) return { chord: null, score: 0, margin: 0 };
    const s = scores(f); const order = s.map((v, i) => i).sort((a, b) => s[b] - s[a]);
    const [r, t] = BANK.names[order[0]];
    return { chord: new Chord(r, t), score: s[order[0]], margin: s[order[0]] - s[order[1]],
      alternatives: order.slice(1, 4).map(i => [new Chord(...BANK.names[i]).name, s[i]]) };
  }

  // ------------------------------------------------------------ exact notes
  const hz = m => 440 * 2 ** ((m - 69) / 12);
  function bandMax(spec, f, n) {
    const a = Math.floor(f * 2 ** (-P.note_cents / 1200) * n / P.sr), b = Math.ceil(f * 2 ** (P.note_cents / 1200) * n / P.sr) + 1;
    if (b >= spec.length) return 0;
    let m = 0; for (let i = a; i < b; i++) if (spec[i] > m) m = spec[i]; return m;
  }
  function salience(spec, m, others, n) {
    const vals = [];
    for (let h = 1; h <= P.note_harmonics; h++) {
      const f = h * hz(m); if (f > P.note_fmax) break;
      let shared = false;
      for (const o of others) { for (let k = 1; k <= P.note_overtones; k++) if (Math.abs(1200 * Math.log2(f / (k * hz(o)))) < 50) { shared = true; break; } if (shared) break; }
      if (shared) continue;
      vals.push(bandMax(spec, f, n) * Math.sqrt(h));
    }
    return vals.length ? Math.max(...vals) : null;
  }
  function noteRatios(spec, voicing) {
    const n = 2 * (spec.length - 1);
    const notes = [...new Set(voicing)].sort((a, b) => a - b);
    const s = new Map(notes.map(m => [m, salience(spec, m, notes.filter(o => mod(o) !== mod(m)), n)]));
    const known = [...s.values()].filter(v => v != null);
    if (!known.length) return {};
    const ref = median(known) + 1e-12; const out = {};
    for (const [m, v] of s) { if (v == null) continue; const pc = mod(m); out[pc] = Math.max(out[pc] || 0, v / ref); }
    return out;
  }
  function missingNotes(spec, voicing) {
    if (!spec || P.note_min_rel <= 0 || new Set(voicing).size < 2) return [];
    const r = noteRatios(spec, voicing);
    return Object.keys(r).map(Number).filter(pc => r[pc] < P.note_min_rel).sort((a, b) => a - b);
  }

  // ------------------------------------------------------------ verify
  function verify(f, expected, shape = null, voicing = null) {
    const ch = parse(expected);
    const s = scores(f);
    let idx = BANK.names.findIndex(([r, t]) => r === ch.root && t === ch.type);
    if (idx < 0) idx = s.indexOf(Math.max(...s));
    const c = f.chroma;
    shape = shape || fingering(ch);
    const played = shapeTones(shape);
    const tones = ch.tones;
    let required = new Set([...tones].filter(x => played.has(x))); if (!required.size) required = tones;
    const allowed = new Set([...tones, ...played]);
    const cmax = c.some(x => x) ? Math.max(...c) : 1;
    const missing = [];
    for (const nn of required) {
      let leak = 0; for (const o of required) if (o !== nn) leak += c[o] * LEAK[o][nn];
      if (c[nn] - P.leak_alpha * leak < P.missing_rel * cmax) missing.push(nn);
    }
    if (!voicing) voicing = shapeNotes(shape).map(x => x[1]);
    for (const nn of missingNotes(f.spectrum, voicing)) if (!missing.includes(nn)) missing.push(nn);
    missing.sort((a, b) => mod(a - ch.root) - mod(b - ch.root));
    const prof = profile(required, P.extra_harmonics, P.extra_decay);
    const k = dot(c, prof);
    const extra = []; for (let q = 0; q < 12; q++) if (!allowed.has(q) && c[q] > P.extra_ratio * prof[q] * k + P.extra_add) extra.push(q);
    const rivals = []; BANK.tonesets.forEach((ts, i) => { const sub = ts.size < allowed.size && [...ts].every(x => allowed.has(x)); if (!sub) rivals.push(s[i]); });
    const best = rivals.length ? Math.max(...rivals) : Math.max(...s);
    const ok = c.some(x => x) && s[idx] >= best - P.verify_margin && !missing.length && !extra.length;
    const strings = ok ? [] : suspectStrings(shape, missing, extra, f.peaks);
    const heard = detect(f).chord;
    return { ok, expected: ch.name, missing: missing.map(x => DISPLAY[x]), extra: extra.map(x => DISPLAY[x]), strings, heard: heard ? heard.name : null, score: s[idx] };
  }
  function suspectStrings(shape, missing, extra, peaks) {
    const out = new Set(); const extraMidi = new Set();
    for (const [fq] of peaks || []) { const m = Math.round(69 + 12 * Math.log2(fq / 440)); if (extra.includes(mod(m))) extraMidi.add(m); }
    shape.forEach((fret, s) => {
      if (fret <= 0) return;
      const midi = OPEN_STRINGS[s] + fret, note = mod(midi), num = 6 - s;
      if (missing.includes(note)) out.add(num);
      else if (extraMidi.size) { for (const m of extraMidi) if (Math.abs(midi - m) === 1) out.add(num); }
      else if (extra.some(e => [1, 11].includes(mod(note - e)))) out.add(num);
    });
    if (!out.size) shape.forEach((fret, s) => { if (fret === 0 && missing.includes(mod(OPEN_STRINGS[s]))) out.add(6 - s); });
    return [...out].sort((a, b) => a - b);
  }
  function hintHe(v) {
    if (v.ok) return '✓ נכון';
    const parts = [];
    if (v.missing.length) parts.push('חסר ' + v.missing.join(', '));
    if (v.extra.length) parts.push('נשמע תו עודף: ' + v.extra.join(', '));
    if (v.strings.length) parts.push('בדוק מיתר ' + v.strings.join(', '));
    if (!parts.length && v.heard) parts.push('נשמע כמו ' + v.heard);
    return '✗ ' + parts.join(' · ');
  }

  // ------------------------------------------------------------ onsets (streaming)
  const WIN = 512, HOP = 128;
  class OnsetTracker {
    constructor() {
      this.histN = Math.max(8, Math.floor(P.onset_history * P.sr / HOP));
      this.gap = Math.floor(P.onset_min_gap * P.sr / HOP);
      this.flux = []; this.rms = []; this.last = -1e9; this.k = 0;
      this.buf = new Float64Array(0); this.prev = null;
      this.top = Math.floor(P.onset_fmax * WIN / P.sr) + 1;
    }
    _push(flux, rms) {
      this.flux.push(flux); this.rms.push(rms); this.k++;
      let found = null; const L = this.flux.length;
      if (L >= 3) {
        const i = this.k - 2, f = this.flux[L - 2];
        const a = Math.max(0, L - 2 - this.histN);
        const med = L - 2 > a ? median(this.flux.slice(a, L - 2)) : 0;
        const back = L - 2 > a ? median(this.rms.slice(a, L - 2)) : 0;
        const thr = P.onset_ratio * med + P.onset_min_flux;
        if (f >= this.flux[L - 3] && f > this.flux[L - 1] && f > thr &&
            Math.max(this.rms[L - 2], this.rms[L - 1]) > back + P.onset_min_rise && i - this.last >= this.gap) {
          let j = i, k = L - 2;
          while (k > 0 && j - 1 > this.last && i - j < 8 && this.flux[k - 1] > 0.5 * thr) { j--; k--; }
          found = j; this.last = i;
        }
      }
      if (this.flux.length > 4 * this.histN) { const cut = this.flux.length - 2 * this.histN; this.flux = this.flux.slice(cut); this.rms = this.rms.slice(cut); }
      return found;
    }
    feed(block) {
      const nb = new Float64Array(this.buf.length + block.length); nb.set(this.buf); nb.set(block, this.buf.length); this.buf = nb;
      const out = []; let off = 0;
      while (this.buf.length - off >= WIN) {
        const fr = this.buf.subarray(off, off + WIN);
        const sp = magSpectrum(fr, WIN); const mag = new Float64Array(this.top);
        for (let i = 0; i < this.top; i++) mag[i] = Math.log1p(P.onset_log_gain * sp[i]);
        let flux = 0; if (this.prev) for (let i = 0; i < this.top; i++) flux += Math.max(mag[i] - this.prev[i], 0);
        this.prev = mag;
        let ss = 0; for (let i = 0; i < WIN; i++) ss += fr[i] * fr[i];
        const i = this._push(flux, Math.sqrt(ss / WIN));
        if (i != null) out.push(i * HOP + WIN / 2);
        off += HOP;
      }
      this.buf = this.buf.slice(off);
      return out;
    }
  }

  // ------------------------------------------------------------ tuner (YIN)
  function yin(x0, sr, fmin, fmax, threshold) {
    const N = x0.length; let mean = 0; for (const v of x0) mean += v; mean /= N;
    const x = Float64Array.from(x0, v => v - mean);
    const tmin = Math.floor(sr / fmax), tmax = Math.min(Math.floor(sr / fmin), N >> 1);
    const w = N - tmax; if (w <= 0 || tmax <= tmin + 2) return null;
    const d = new Float64Array(tmax + 1);
    for (let t = 1; t <= tmax; t++) { let s = 0; for (let j = 0; j < w; j++) { const e = x[j] - x[j + t]; s += e * e; } d[t] = s; }
    const cm = new Float64Array(tmax + 1); cm[0] = 1; let cs = 0;
    for (let t = 1; t <= tmax; t++) { cs += d[t]; cm[t] = cs ? d[t] * t / cs : 1; }
    let tau = null;
    for (let t = tmin; t < tmax; t++) if (cm[t] < threshold) { while (t + 1 < tmax && cm[t + 1] < cm[t]) t++; tau = t; break; }
    if (tau == null) return null;
    let shift = 0;
    if (tau >= 1 && tau < tmax) { const a = d[tau - 1], b = d[tau], c = d[tau + 1], den = a - 2 * b + c; shift = den ? 0.5 * (a - c) / den : 0; }
    return sr / (tau + shift);
  }
  function tune(frame) {
    let ss = 0; for (const v of frame) ss += v * v;
    if (Math.sqrt(ss / frame.length) < 1e-4) return null;
    const f = yin(frame, P.sr, P.tuner_fmin, P.tuner_fmax, P.tuner_threshold);
    if (!f) return null;
    const midi = 69 + 12 * Math.log2(f / 440), m = Math.round(midi);
    let bi = 0; OPEN_STRINGS.forEach((o, i) => { if (Math.abs(midi - o) < Math.abs(midi - OPEN_STRINGS[bi])) bi = i; });
    return { freq: f, note: DISPLAY[mod(m)] + (Math.floor(m / 12) - 1), cents: (midi - m) * 100, string: 6 - bi, midi };
  }

  return { P, DISPLAY, OPEN_STRINGS, TYPES, Chord, parse, isChord, fingering, shapeNotes, shapeTones,
    analyse, detect, verify, hintHe, OnsetTracker, tune, magSpectrum, noteRatios, mod };
})();
if (typeof module !== 'undefined') module.exports = WhaleEngine;
