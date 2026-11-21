// Finger camera (experiment): maps fingertips on the video to (string, fret) and
// compares them with the expected chord shape. Pure functions, no DOM.
const WhaleCam = (() => {
  const D5 = 1 - 2 ** (-5 / 12);                     // distance nut→fret 5 as a share of scale length
  const fretPos = n => 1 - 2 ** (-n / 12);            // nut→fret n, same unit

  // calibration: 4 points in normalized video coords
  //   q[0] nut at string 6, q[1] nut at string 1, q[2] fret 5 at string 1, q[3] fret 5 at string 6
  // bilinear patch P(u,v): u along the neck (0 nut, 1 fret 5), v across (0 string 6, 1 string 1)
  function patch(q, u, v) {
    const a = [q[0][0] + (q[3][0] - q[0][0]) * u, q[0][1] + (q[3][1] - q[0][1]) * u];   // string-6 edge
    const b = [q[1][0] + (q[2][0] - q[1][0]) * u, q[1][1] + (q[2][1] - q[1][1]) * u];   // string-1 edge
    return [a[0] + (b[0] - a[0]) * v, a[1] + (b[1] - a[1]) * v];
  }
  // inverse of the patch by Newton steps (works a little outside the quad too)
  function toNeck(q, p) {
    let u = 0.5, v = 0.5;
    for (let it = 0; it < 20; it++) {
      const P = patch(q, u, v), e = 1e-4;
      const Pu = patch(q, u + e, v), Pv = patch(q, u, v + e);
      const J = [[(Pu[0] - P[0]) / e, (Pv[0] - P[0]) / e], [(Pu[1] - P[1]) / e, (Pv[1] - P[1]) / e]];
      const det = J[0][0] * J[1][1] - J[0][1] * J[1][0]; if (Math.abs(det) < 1e-12) break;
      const rx = p[0] - P[0], ry = p[1] - P[1];
      const du = (J[1][1] * rx - J[0][1] * ry) / det, dv = (-J[1][0] * rx + J[0][0] * ry) / det;
      u += du; v += dv; if (Math.abs(du) + Math.abs(dv) < 1e-7) break;
    }
    return [u, v];
  }
  // fingertip → {string 1..6, fret, du (how far behind the fret, 0..1), sv (distance to nearest string, in string gaps)}
  function place(q, p) {
    const [u, v] = toNeck(q, p);
    const t = u * D5;                                   // share of scale length from the nut
    if (t <= 0 || t >= 0.6) return null;
    const fret = Math.max(1, Math.ceil(-12 * Math.log2(1 - t)));
    const lo = fretPos(fret - 1), hi = fretPos(fret);
    const s6 = v * 5, si = Math.round(s6);
    if (si < -1 || si > 6) return null;
    return { string: 6 - Math.min(5, Math.max(0, si)), fret, inFret: (t - lo) / (hi - lo), off: Math.abs(s6 - si), u, v };
  }
  // where to draw fret n across string position v (for the overlay)
  const point = (q, fret, v) => patch(q, fretPos(fret) / D5, v);
  const stringV = s => (6 - s) / 5;                    // string number → v

  // compare tips with the shape; tips: [{finger:1..4, p:[x,y]}], shape: 6 frets low E→high E (-1 mute)
  function judge(q, tips, shape) {
    const want = [];                                    // fretted notes the shape needs
    shape.forEach((f, i) => { if (f > 0) want.push({ string: 6 - i, fret: f }); });
    const open = new Set(shape.map((f, i) => f === 0 ? 6 - i : null).filter(x => x));
    const seen = tips.map(t => ({ ...t, at: place(q, t.p) })).filter(t => t.at);
    // barre: several wanted notes on the same fret beside each other count as one finger's job
    const used = new Set(), hints = [], marks = [];
    const dist = (a, w) => Math.abs(a.at.fret - w.fret) * 1.0 + Math.abs(a.at.string - w.string) * 1.2;
    const order = want.map((w, i) => i);
    const matched = new Array(want.length).fill(null);
    // exact matches first, then nearest
    for (const pass of [0, 1]) for (const i of order) {
      if (matched[i]) continue; const w = want[i];
      let best = null, bd = 1e9;
      for (const t of seen) { if (used.has(t)) continue; const d = dist(t, w); if (pass === 0 && d > 0) continue; if (d < bd) { bd = d; best = t; } }
      if (best && (pass === 0 || bd <= 3)) { matched[i] = best; used.add(best); }
    }
    want.forEach((w, i) => {
      const t = matched[i];
      if (!t) { hints.push({ kind: 'missing', text: `חסרה אצבע על מיתר ${w.string} בשריג ${w.fret}`, want: w }); marks.push({ want: w }); return; }
      if (t.at.fret !== w.fret && t.at.string === w.string) hints.push({ kind: 'fret', text: `אצבע ${t.finger} בשריג ${t.at.fret} — הזיזו לשריג ${w.fret}`, finger: t.finger, want: w });
      else if (t.at.string !== w.string && t.at.fret === w.fret) hints.push({ kind: 'string', text: `אצבע ${t.finger} על מיתר ${t.at.string} — צריכה להיות על מיתר ${w.string}`, finger: t.finger, want: w });
      else if (t.at.string !== w.string || t.at.fret !== w.fret) hints.push({ kind: 'both', text: `אצבע ${t.finger} על מיתר ${t.at.string} שריג ${t.at.fret} — צריכה להיות במיתר ${w.string} שריג ${w.fret}`, finger: t.finger, want: w });
      else if (t.at.inFret < 0.45) hints.push({ kind: 'far', text: `קרבו את אצבע ${t.finger} אל השריג — הצליל יהיה נקי יותר`, finger: t.finger, want: w, soft: true });
      marks.push({ want: w, tip: t, ok: t.at.string === w.string && t.at.fret === w.fret });
    });
    // a spare finger lying right on a string that should ring open
    for (const t of seen) if (!used.has(t) && open.has(t.at.string) && t.at.off < 0.25 && t.at.fret <= 4)
      hints.push({ kind: 'open', text: `אצבע ${t.finger} אולי נוגעת במיתר ${t.at.string} שצריך להישמע פתוח — הרימו אותה מעט`, finger: t.finger, soft: true });
    const hard = hints.filter(h => !h.soft);
    return { ok: !hard.length && want.length > 0, hints, marks, seen };
  }
  return { place, toNeck, patch, point, stringV, judge, fretPos, D5 };
})();
if (typeof module !== 'undefined') module.exports = WhaleCam;
