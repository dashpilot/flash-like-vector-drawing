/**
 * Flash-like Vector Drawing App
 * Pen Tool + Selection Tool - matches Adobe Flash/Animate behavior
 *
 * - Draw by dragging only (mousedown → drag → mouseup = one segment)
 * - Shift: constrain to straight/45° angles during drag
 * - Each segment individually selectable
 * - Lines act as knives: crossing splits both into 4 pieces
 * - Shift+click: multi-select
 */

const canvas = document.getElementById('canvas');
const ctx = canvas.getContext('2d');
const toolSelect = document.getElementById('tool-select');
const toolPen = document.getElementById('tool-pen');
const toolRect = document.getElementById('tool-rect');
const toolOval = document.getElementById('tool-oval');
const toolPaintBucket = document.getElementById('tool-paintbucket');

canvas.width = 1000;
canvas.height = 650;

const DEFAULT_STROKE_WIDTH = 2;
const DEFAULT_STROKE_COLOR = '#171717';

const COLOR_SWATCHES = [
  '#000000', '#171717', '#44403c', '#78716c', '#a8a29e', '#d6d3d1',
  '#ffffff', '#fef2f2', '#fef3c7', '#ecfccb', '#d1fae5', '#dbeafe',
  '#e0e7ff', '#ede9fe', '#fce7f3', '#fef3c7',
  '#dc2626', '#ea580c', '#ca8a04', '#65a30d', '#059669', '#0891b2',
  '#2563eb', '#7c3aed', '#db2777', '#b91c1c', '#9a3412', '#854d0e'
];

// Segment format: { type: 'L'|'Q'|'C'|'E', x0, y0, x1, y1, cx?, cy?, c1x?, c1y?, c2x?, c2y?, strokeWidth?, strokeColor?, strokeDashArray? }
// E = ellipse: { type: 'E', cx, cy, rx, ry, ...props } — single closed shape, split only when crossed
let segments = [];
let fills = []; // { color, polygon: [[x,y],...] | segmentIndices: [...] }
let selectedIndices = new Set();
let selectedFillIndices = new Set();
let penPreview = null;
let dragState = null;
let marqueeRect = null;
let fillColor = '#3b82f6';
let tool = 'select';
let currentStrokeWidth = DEFAULT_STROKE_WIDTH;
let currentStrokeColor = DEFAULT_STROKE_COLOR;
let currentStrokeDash = null; // null = solid, [6, 4] = dashed

let undoStack = [];
let redoStack = [];
const MAX_UNDO = 50;

const SEGMENT_HIT_TOLERANCE = 8;
const SNAP_TO_ENDPOINT_RADIUS = 12;

// --- Line/segment intersection (for knife) ---
function lineLineIntersection(x1, y1, x2, y2, x3, y3, x4, y4) {
  const denom = (x1 - x2) * (y3 - y4) - (y1 - y2) * (x3 - x4);
  if (Math.abs(denom) < 1e-10) return null; // parallel
  const t = ((x1 - x3) * (y3 - y4) - (y1 - y3) * (x3 - x4)) / denom;
  const u = -((x1 - x2) * (y1 - y3) - (y1 - y2) * (x1 - x3)) / denom;
  if (t > 1e-6 && t < 1 - 1e-6 && u > 1e-6 && u < 1 - 1e-6) {
    return { x: x1 + t * (x2 - x1), y: y1 + t * (y2 - y1), t, u };
  }
  return null;
}

// Cubic Bézier coefficients: x(t) = bx[0]*t^3 + bx[1]*t^2 + bx[2]*t + bx[3]
function cubicBezierCoeffs(p0, p1, p2, p3) {
  return [
    -p0 + 3 * p1 - 3 * p2 + p3,
    3 * p0 - 6 * p1 + 3 * p2,
    -3 * p0 + 3 * p1,
    p0
  ];
}

function cubicRoots(P) {
  const eps = 1e-10;
  const sgn = (x) => (x < 0 ? -1 : x > 0 ? 1 : 0);
  let a = P[0], b = P[1], c = P[2], d = P[3];
  if (Math.abs(a) < eps) {
    if (Math.abs(b) < eps) {
      if (Math.abs(c) < eps) return [];
      const t = -d / c;
      return (t >= 0 && t <= 1) ? [t] : [];
    }
    const D = c * c - 4 * b * d;
    if (D < 0) return [];
    const sq = Math.sqrt(D);
    const roots = [];
    const t1 = (-c + sq) / (2 * b);
    const t2 = (-c - sq) / (2 * b);
    if (t1 >= 0 && t1 <= 1) roots.push(t1);
    if (t2 >= 0 && t2 <= 1 && Math.abs(t2 - t1) > eps) roots.push(t2);
    return roots;
  }
  const A = b / a, B = c / a, C = d / a;
  const Q = (3 * B - A * A) / 9;
  const R = (9 * A * B - 27 * C - 2 * A * A * A) / 54;
  const D = Q * Q * Q + R * R;
  const roots = [];
  if (D >= 0) {
    const S = sgn(R + Math.sqrt(D)) * Math.pow(Math.abs(R + Math.sqrt(D)), 1 / 3);
    const T = sgn(R - Math.sqrt(D)) * Math.pow(Math.abs(R - Math.sqrt(D)), 1 / 3);
    const t0 = -A / 3 + (S + T);
    if (t0 >= 0 && t0 <= 1) roots.push(t0);
    const im = Math.abs(Math.sqrt(3) * (S - T) / 2);
    if (im < eps) {
      const t1 = -A / 3 - (S + T) / 2;
      if (t1 >= 0 && t1 <= 1 && roots.every(r => Math.abs(r - t1) > eps)) roots.push(t1);
    }
  } else {
    const th = Math.acos(R / Math.sqrt(-Q * Q * Q));
    for (const k of [0, 1, 2]) {
      const t = 2 * Math.sqrt(-Q) * Math.cos((th + 2 * Math.PI * k) / 3) - A / 3;
      if (t >= 0 && t <= 1 && roots.every(r => Math.abs(r - t) > eps)) roots.push(t);
    }
  }
  return roots.sort((a, b) => a - b);
}

function lineCubicIntersection(lx0, ly0, lx1, ly1, seg) {
  const A = ly1 - ly0, B = lx0 - lx1;
  const C = lx0 * (ly0 - ly1) + ly0 * (lx1 - lx0);
  const bx = cubicBezierCoeffs(seg.x0, seg.c1x, seg.c2x, seg.x1);
  const by = cubicBezierCoeffs(seg.y0, seg.c1y, seg.c2y, seg.y1);
  const P = [
    A * bx[0] + B * by[0],
    A * bx[1] + B * by[1],
    A * bx[2] + B * by[2],
    A * bx[3] + B * by[3] + C
  ];
  const tRoots = cubicRoots(P);
  const results = [];
  const eps = 1e-6;
  for (const t of tRoots) {
    if (t <= eps || t >= 1 - eps) continue;
    const px = bx[0] * t * t * t + bx[1] * t * t + bx[2] * t + bx[3];
    const py = by[0] * t * t * t + by[1] * t * t + by[2] * t + by[3];
    let s;
    if (Math.abs(lx1 - lx0) > eps) s = (px - lx0) / (lx1 - lx0);
    else s = (py - ly0) / (ly1 - ly0);
    if (s <= eps || s >= 1 - eps) continue;
    results.push({ x: px, y: py, t: s, u: t });
  }
  return results;
}

function splitCubicAt(seg, t) {
  const props = withStrokeProps(seg);
  const p01x = seg.x0 + t * (seg.c1x - seg.x0), p01y = seg.y0 + t * (seg.c1y - seg.y0);
  const p12x = seg.c1x + t * (seg.c2x - seg.c1x), p12y = seg.c1y + t * (seg.c2y - seg.c1y);
  const p23x = seg.c2x + t * (seg.x1 - seg.c2x), p23y = seg.c2y + t * (seg.y1 - seg.c2y);
  const p012x = p01x + t * (p12x - p01x), p012y = p01y + t * (p12y - p01y);
  const p123x = p12x + t * (p23x - p12x), p123y = p12y + t * (p23y - p12y);
  const px = p012x + t * (p123x - p012x), py = p012y + t * (p123y - p012y);
  return [
    { type: 'C', x0: seg.x0, y0: seg.y0, c1x: p01x, c1y: p01y, c2x: p012x, c2y: p012y, x1: px, y1: py, ...props },
    { type: 'C', x0: px, y0: py, c1x: p123x, c1y: p123y, c2x: p23x, c2y: p23y, x1: seg.x1, y1: seg.y1, ...props }
  ];
}

function withStrokeProps(seg, overrides = {}) {
  return {
    strokeWidth: seg.strokeWidth ?? DEFAULT_STROKE_WIDTH,
    strokeColor: seg.strokeColor ?? DEFAULT_STROKE_COLOR,
    strokeDashArray: seg.strokeDashArray ?? null,
    ...overrides
  };
}

// --- Ellipse (single closed shape): 4 cubic arcs, split only when crossed ---
const OVAL_K = 4 / 3 * (Math.SQRT2 - 1);
function ellipseToCubicArcs(cx, cy, rx, ry, props = {}) {
  const k = OVAL_K;
  return [
    { type: 'C', x0: cx + rx, y0: cy, c1x: cx + rx, c1y: cy + ry * k, c2x: cx + rx * k, c2y: cy + ry, x1: cx, y1: cy + ry, ...props },
    { type: 'C', x0: cx, y0: cy + ry, c1x: cx - rx * k, c1y: cy + ry, c2x: cx - rx, c2y: cy + ry * k, x1: cx - rx, y1: cy, ...props },
    { type: 'C', x0: cx - rx, y0: cy, c1x: cx - rx, c1y: cy - ry * k, c2x: cx - rx * k, c2y: cy - ry, x1: cx, y1: cy - ry, ...props },
    { type: 'C', x0: cx, y0: cy - ry, c1x: cx + rx * k, c1y: cy - ry, c2x: cx + rx, c2y: cy - ry * k, x1: cx + rx, y1: cy, ...props }
  ];
}

function cubicCubicIntersection(c1, c2) {
  const results = [];
  const flatnessThreshold = 4;
  const maxDepth = 10;
  const cubicBBox = (c) => {
    const xs = [c.x0, c.c1x, c.c2x, c.x1];
    const ys = [c.y0, c.c1y, c.c2y, c.y1];
    return { minX: Math.min(...xs), maxX: Math.max(...xs), minY: Math.min(...ys), maxY: Math.max(...ys) };
  };
  const bboxOverlap = (a, b) => !(a.maxX < b.minX || b.maxX < a.minX || a.maxY < b.minY || b.maxY < a.minY);
  const chordDist = (c) => {
    const dx = c.x1 - c.x0, dy = c.y1 - c.y0;
    const len = Math.hypot(dx, dy) || 1;
    let maxD = 0;
    for (const p of [{ x: c.c1x, y: c.c1y }, { x: c.c2x, y: c.c2y }]) {
      const t = Math.max(0, Math.min(1, ((p.x - c.x0) * dx + (p.y - c.y0) * dy) / (len * len)));
      const projX = c.x0 + t * dx, projY = c.y0 + t * dy;
      maxD = Math.max(maxD, Math.hypot(p.x - projX, p.y - projY));
    }
    return maxD;
  };
  const eps = 1e-5;
  function recurse(a, ta0, ta1, b, tb0, tb1, depth) {
    if (depth > maxDepth) return;
    const bboxA = cubicBBox(a), bboxB = cubicBBox(b);
    if (!bboxOverlap(bboxA, bboxB)) return;
    const flatA = chordDist(a) < flatnessThreshold;
    const flatB = chordDist(b) < flatnessThreshold;
    if (flatA && flatB) {
      const isec = lineLineIntersection(a.x0, a.y0, a.x1, a.y1, b.x0, b.y0, b.x1, b.y1);
      if (isec) {
        const ta = (ta0 + ta1) / 2, tb = (tb0 + tb1) / 2;
        if (ta > eps && ta < 1 - eps && tb > eps && tb < 1 - eps) {
          if (results.every(r => Math.hypot(r.x - isec.x, r.y - isec.y) > 0.5)) {
            results.push({ x: isec.x, y: isec.y, tA: ta, tB: tb });
          }
        }
      }
      return;
    }
    if (!flatA || (!flatB && chordDist(b) < chordDist(a))) {
      const [left, right] = splitCubicAt(a, 0.5);
      const tmid = (ta0 + ta1) / 2;
      recurse(left, ta0, tmid, b, tb0, tb1, depth + 1);
      recurse(right, tmid, ta1, b, tb0, tb1, depth + 1);
    } else {
      const [left, right] = splitCubicAt(b, 0.5);
      const tmid = (tb0 + tb1) / 2;
      recurse(a, ta0, ta1, left, tb0, tmid, depth + 1);
      recurse(a, ta0, ta1, right, tmid, tb1, depth + 1);
    }
  }
  recurse(c1, 0, 1, c2, 0, 1, 0);
  return results;
}

function circleCircleIntersection(cx1, cy1, r1, cx2, cy2, r2) {
  const dx = cx2 - cx1, dy = cy2 - cy1;
  const d = Math.hypot(dx, dy);
  if (d > r1 + r2 || d < Math.abs(r1 - r2) - 1e-6 || d < 1e-6) return [];
  const a = (r1 * r1 - r2 * r2 + d * d) / (2 * d);
  const hSq = r1 * r1 - a * a;
  if (hSq < 0) return [];
  const h = Math.sqrt(hSq);
  const px = cx1 + a * dx / d, py = cy1 + a * dy / d;
  const p1 = { x: px + h * (-dy) / d, y: py + h * dx / d };
  const p2 = { x: px - h * (-dy) / d, y: py - h * dx / d };
  return [p1, p2];
}

function pointToCircleParam(cx, cy, r, px, py) {
  let theta = Math.atan2(py - cy, px - cx);
  if (theta < 0) theta += Math.PI * 2;
  const param = 2 * theta / Math.PI;
  const arcIdx = Math.floor(param) % 4;
  const t = param - Math.floor(param);
  return { arcIdx, t };
}

function ellipseEllipseIntersection(segA, segB) {
  if (Math.abs(segA.rx - segA.ry) < 1e-6 && Math.abs(segB.rx - segB.ry) < 1e-6) {
    const pts = circleCircleIntersection(segA.cx, segA.cy, segA.rx, segB.cx, segB.cy, segB.rx);
    if (pts.length < 2) return [];
    return pts.map(p => {
      const a = pointToCircleParam(segA.cx, segA.cy, segA.rx, p.x, p.y);
      const b = pointToCircleParam(segB.cx, segB.cy, segB.rx, p.x, p.y);
      return {
        x: p.x, y: p.y,
        ellipseAParam: a.arcIdx + a.t, ellipseBParam: b.arcIdx + b.t,
        arcIdxA: a.arcIdx, tA: a.t, arcIdxB: b.arcIdx, tB: b.t
      };
    }).sort((a, b) => a.ellipseAParam - b.ellipseAParam);
  }
  const arcsA = ellipseToCubicArcs(segA.cx, segA.cy, segA.rx, segA.ry, {});
  const arcsB = ellipseToCubicArcs(segB.cx, segB.cy, segB.rx, segB.ry, {});
  const results = [];
  for (let ai = 0; ai < 4; ai++) {
    for (let bi = 0; bi < 4; bi++) {
      for (const r of cubicCubicIntersection(arcsA[ai], arcsB[bi])) {
        results.push({
          ellipseAParam: ai + r.tA,
          ellipseBParam: bi + r.tB,
          arcIdxA: ai, tA: r.tA,
          arcIdxB: bi, tB: r.tB,
          x: r.x, y: r.y
        });
      }
    }
  }
  const eps = 1;
  const deduped = [];
  for (const r of results) {
    if (deduped.every(d => Math.hypot(d.x - r.x, d.y - r.y) > eps)) deduped.push(r);
  }
  return deduped.sort((a, b) => a.ellipseAParam - b.ellipseAParam);
}

function lineEllipseIntersection(lx0, ly0, lx1, ly1, seg) {
  const arcs = ellipseToCubicArcs(seg.cx, seg.cy, seg.rx, seg.ry, {});
  const results = [];
  for (let ai = 0; ai < 4; ai++) {
    const list = lineCubicIntersection(lx0, ly0, lx1, ly1, arcs[ai]);
    for (const r of list) {
      results.push({ arcIdx: ai, t: r.u, x: r.x, y: r.y, lineT: r.t, ellipseParam: ai + r.u });
    }
  }
  return results.sort((a, b) => a.ellipseParam - b.ellipseParam);
}

function splitEllipseAtCrossings(seg, crossings) {
  if (crossings.length < 2) return [seg];
  const arcs = ellipseToCubicArcs(seg.cx, seg.cy, seg.rx, seg.ry, withStrokeProps(seg));
  const props = withStrokeProps(seg);
  const pieces = [];
  for (let p = 0; p < crossings.length; p++) {
    const c1 = crossings[p];
    const c2 = crossings[(p + 1) % crossings.length];
    const segs = extractEllipseArc(arcs, c1.arcIdx, c1.t, c2.arcIdx, c2.t, props);
    pieces.push(...segs);
  }
  return pieces;
}

function extractEllipseArc(arcs, startArc, startT, endArc, endT, props) {
  const result = [];
  let curArc = startArc;
  let curT = startT;
  const endParam = endArc + endT;
  const targetParam = endParam <= startArc + startT ? endParam + 4 : endParam;
  let param = startArc + startT;
  while (param < targetParam - 1e-9) {
    const a = arcs[curArc % 4];
    const arcEnd = curArc + 1;
    if (arcEnd <= targetParam) {
      if (curT > 1e-9) {
        const [_, right] = splitCubicAt({ ...a, ...props }, curT);
        result.push(right);
      } else {
        result.push({ ...a, ...props });
      }
      curArc++;
      curT = 0;
      param = arcEnd;
    } else {
      const tEnd = targetParam - curArc;
      if (curT > 1e-9) {
        const [_, right] = splitCubicAt({ ...a, ...props }, curT);
        const tLoc = (tEnd - curT) / (1 - curT);
        if (tLoc > 1e-9) {
          if (tLoc < 1 - 1e-9) {
            const [left] = splitCubicAt(right, tLoc);
            result.push(left);
          } else {
            result.push(right);
          }
        }
      } else {
        if (tEnd > 1e-9) {
          if (tEnd < 1 - 1e-9) {
            const [left] = splitCubicAt({ ...a, ...props }, tEnd);
            result.push(left);
          } else {
            result.push({ ...a, ...props });
          }
        }
      }
      break;
    }
  }
  return result;
}

// --- Split all crossing segments at their intersections (L-L, L-C, C-L, L-E, E-L) ---
function splitSegmentsAtAllIntersections() {
  const splits = new Map(); // segIndex -> sorted list of { u, x, y }
  const eps = 1e-6;
  for (let i = 0; i < segments.length; i++) {
    const a = segments[i];
    for (let j = i + 1; j < segments.length; j++) {
      const b = segments[j];
      if (a.type === 'L' && b.type === 'L') {
        const isec = lineLineIntersection(a.x0, a.y0, a.x1, a.y1, b.x0, b.y0, b.x1, b.y1);
        if (!isec) continue;
        if (isec.t <= eps || isec.t >= 1 - eps || isec.u <= eps || isec.u >= 1 - eps) continue;
        const x = isec.x, y = isec.y;
        if (!splits.has(i)) splits.set(i, []);
        if (splits.get(i).every(s => Math.abs(s.u - isec.t) > eps)) splits.get(i).push({ u: isec.t, x, y });
        if (!splits.has(j)) splits.set(j, []);
        if (splits.get(j).every(s => Math.abs(s.u - isec.u) > eps)) splits.get(j).push({ u: isec.u, x, y });
      } else if (a.type === 'L' && b.type === 'C') {
        const list = lineCubicIntersection(a.x0, a.y0, a.x1, a.y1, b);
        for (const isec of list) {
          if (!splits.has(i)) splits.set(i, []);
          if (splits.get(i).every(s => Math.abs(s.u - isec.t) > eps)) splits.get(i).push({ u: isec.t, x: isec.x, y: isec.y });
          if (!splits.has(j)) splits.set(j, []);
          if (splits.get(j).every(s => Math.abs(s.u - isec.u) > eps)) splits.get(j).push({ u: isec.u, x: isec.x, y: isec.y });
        }
      } else if (a.type === 'C' && b.type === 'L') {
        const list = lineCubicIntersection(b.x0, b.y0, b.x1, b.y1, a);
        for (const isec of list) {
          if (!splits.has(i)) splits.set(i, []);
          if (splits.get(i).every(s => Math.abs(s.u - isec.u) > eps)) splits.get(i).push({ u: isec.u, x: isec.x, y: isec.y });
          if (!splits.has(j)) splits.set(j, []);
          if (splits.get(j).every(s => Math.abs(s.u - isec.t) > eps)) splits.get(j).push({ u: isec.t, x: isec.x, y: isec.y });
        }
      } else if (a.type === 'L' && b.type === 'E') {
        const list = lineEllipseIntersection(a.x0, a.y0, a.x1, a.y1, b);
        if (list.length >= 2) {
          for (const isec of list) {
            if (!splits.has(i)) splits.set(i, []);
            if (splits.get(i).every(s => Math.abs(s.u - isec.lineT) > eps)) splits.get(i).push({ u: isec.lineT, x: isec.x, y: isec.y });
          }
          if (!splits.has(j)) splits.set(j, []);
          splits.set(j, list);
        }
      } else if (a.type === 'E' && b.type === 'L') {
        const list = lineEllipseIntersection(b.x0, b.y0, b.x1, b.y1, a);
        if (list.length >= 2) {
          for (const isec of list) {
            if (!splits.has(j)) splits.set(j, []);
            if (splits.get(j).every(s => Math.abs(s.u - isec.lineT) > eps)) splits.get(j).push({ u: isec.lineT, x: isec.x, y: isec.y });
          }
          if (!splits.has(i)) splits.set(i, []);
          splits.set(i, list);
        }
      } else if (a.type === 'C' && b.type === 'C') {
        const list = cubicCubicIntersection(a, b);
        for (const isec of list) {
          if (!splits.has(i)) splits.set(i, []);
          if (splits.get(i).every(s => Math.abs(s.u - isec.tA) > eps)) splits.get(i).push({ u: isec.tA, x: isec.x, y: isec.y });
          if (!splits.has(j)) splits.set(j, []);
          if (splits.get(j).every(s => Math.abs(s.u - isec.tB) > eps)) splits.get(j).push({ u: isec.tB, x: isec.x, y: isec.y });
        }
      } else if (a.type === 'C' && b.type === 'E') {
        const arcs = ellipseToCubicArcs(b.cx, b.cy, b.rx, b.ry, {});
        const list = [];
        for (let bi = 0; bi < 4; bi++) {
          for (const r of cubicCubicIntersection(a, arcs[bi])) {
            list.push({ uCubic: r.tA, arcIdx: bi, t: r.tB, x: r.x, y: r.y, ellipseParam: bi + r.tB });
          }
        }
        const deduped = [];
        for (const r of list) {
          if (deduped.every(d => Math.hypot(d.x - r.x, d.y - r.y) > 0.1)) deduped.push(r);
        }
        if (deduped.length >= 2) {
          for (const r of deduped) {
            if (!splits.has(i)) splits.set(i, []);
            if (splits.get(i).every(s => Math.abs(s.u - r.uCubic) > eps)) splits.get(i).push({ u: r.uCubic, x: r.x, y: r.y });
          }
          splits.set(j, deduped.map(r => ({ arcIdx: r.arcIdx, t: r.t, x: r.x, y: r.y, ellipseParam: r.ellipseParam })));
        }
      } else if (a.type === 'E' && b.type === 'C') {
        const arcs = ellipseToCubicArcs(a.cx, a.cy, a.rx, a.ry, {});
        const list = [];
        for (let ai = 0; ai < 4; ai++) {
          for (const r of cubicCubicIntersection(arcs[ai], b)) {
            list.push({ arcIdx: ai, t: r.tA, x: r.x, y: r.y, ellipseParam: ai + r.tA, uCubic: r.tB });
          }
        }
        const deduped = [];
        for (const r of list) {
          if (deduped.every(d => Math.hypot(d.x - r.x, d.y - r.y) > 0.1)) deduped.push(r);
        }
        if (deduped.length >= 2) {
          splits.set(i, deduped.map(r => ({ arcIdx: r.arcIdx, t: r.t, x: r.x, y: r.y, ellipseParam: r.ellipseParam })));
          for (const r of deduped) {
            if (!splits.has(j)) splits.set(j, []);
            if (splits.get(j).every(s => Math.abs(s.u - r.uCubic) > eps)) splits.get(j).push({ u: r.uCubic, x: r.x, y: r.y });
          }
        }
      } else if (a.type === 'E' && b.type === 'E') {
        const list = ellipseEllipseIntersection(a, b);
        if (list.length >= 2) {
          const listA = list.map(r => ({ arcIdx: r.arcIdxA, t: r.tA, x: r.x, y: r.y, ellipseParam: r.ellipseAParam }));
          const listB = list.map(r => ({ arcIdx: r.arcIdxB, t: r.tB, x: r.x, y: r.y, ellipseParam: r.ellipseBParam }));
          splits.set(i, listA);
          splits.set(j, listB);
        }
      }
    }
  }
  if (splits.size === 0) return false;
  const toRemove = new Set();
  const newSegments = [];
  const indexMap = [];
  for (let i = 0; i < segments.length; i++) {
    const seg = segments[i];
    const segSplits = splits.get(i);
    if (!segSplits || segSplits.length === 0) {
      newSegments.push(seg);
      indexMap.push(i);
      continue;
    }
    toRemove.add(i);
    if (seg.type === 'E') segSplits.sort((a, b) => (a.ellipseParam ?? a.arcIdx + a.t) - (b.ellipseParam ?? b.arcIdx + b.t));
    else segSplits.sort((a, b) => a.u - b.u);
    let u0 = 0;
    const props = withStrokeProps(seg);
    if (seg.type === 'L') {
      for (const s of segSplits) {
        const x0 = seg.x0 + u0 * (seg.x1 - seg.x0);
        const y0 = seg.y0 + u0 * (seg.y1 - seg.y0);
        newSegments.push({ type: 'L', x0, y0, x1: s.x, y1: s.y, ...props });
        indexMap.push(i);
        u0 = s.u;
      }
      const x0 = seg.x0 + u0 * (seg.x1 - seg.x0);
      const y0 = seg.y0 + u0 * (seg.y1 - seg.y0);
      newSegments.push({ type: 'L', x0, y0, x1: seg.x1, y1: seg.y1, ...props });
      indexMap.push(i);
    } else if (seg.type === 'C') {
      let prev = seg;
      for (const s of segSplits) {
        const t = (s.u - u0) / (1 - u0);
        const [left, right] = splitCubicAt(prev, t);
        newSegments.push(left);
        indexMap.push(i);
        prev = right;
        u0 = s.u;
      }
      newSegments.push(prev);
      indexMap.push(i);
    } else if (seg.type === 'E') {
      const list = segSplits;
      const pieces = splitEllipseAtCrossings(seg, list);
      for (const p of pieces) {
        newSegments.push(p);
        indexMap.push(i);
      }
    }
  }
  segments = newSegments;
  const oldToNew = new Map();
  for (let j = 0; j < newSegments.length; j++) {
    const oldIdx = indexMap[j];
    if (!toRemove.has(oldIdx) && !oldToNew.has(oldIdx)) oldToNew.set(oldIdx, j);
  }
  fills = fills.filter(f => {
    if (!f.segmentIndices) return true;
    if (f.segmentIndices.some(idx => toRemove.has(idx))) return false;
    f.segmentIndices = f.segmentIndices.map(idx => oldToNew.get(idx) ?? idx);
    return true;
  });
  return true;
}

function splitSegmentAt(seg, splitX, splitY, t) {
  const props = withStrokeProps(seg);
  if (seg.type === 'L') {
    return [
      { type: 'L', x0: seg.x0, y0: seg.y0, x1: splitX, y1: splitY, ...props },
      { type: 'L', x0: splitX, y0: splitY, x1: seg.x1, y1: seg.y1, ...props }
    ];
  }
  if (seg.type === 'Q') {
    const mt = 1 - t;
    const midX = mt * mt * seg.x0 + 2 * mt * t * seg.cx + t * t * seg.x1;
    const midY = mt * mt * seg.y0 + 2 * mt * t * seg.cy + t * t * seg.y1;
    const c0x = seg.x0 + t * (seg.cx - seg.x0);
    const c0y = seg.y0 + t * (seg.cy - seg.y0);
    const c1x = seg.cx + t * (seg.x1 - seg.cx);
    const c1y = seg.cy + t * (seg.y1 - seg.cy);
    return [
      { type: 'Q', x0: seg.x0, y0: seg.y0, cx: c0x, cy: c0y, x1: midX, y1: midY, ...props },
      { type: 'Q', x0: midX, y0: midY, cx: c1x, cy: c1y, x1: seg.x1, y1: seg.y1, ...props }
    ];
  }
  return [seg];
}

function quadParametricPoint(seg, t) {
  const mt = 1 - t;
  return {
    x: mt * mt * seg.x0 + 2 * mt * t * seg.cx + t * t * seg.x1,
    y: mt * mt * seg.y0 + 2 * mt * t * seg.cy + t * t * seg.y1
  };
}

function distToSegment(px, py, x1, y1, x2, y2) {
  const A = px - x1, B = py - y1, C = x2 - x1, D = y2 - y1;
  const dot = A * C + B * D;
  const lenSq = C * C + D * D;
  let param = lenSq ? dot / lenSq : -1;
  if (param < 0) param = 0;
  if (param > 1) param = 1;
  const xx = x1 + param * C, yy = y1 + param * D;
  return Math.hypot(px - xx, py - yy);
}

function nearestPointOnSegment(px, py, x1, y1, x2, y2) {
  const A = px - x1, B = py - y1, C = x2 - x1, D = y2 - y1;
  const dot = A * C + B * D;
  const lenSq = C * C + D * D;
  let param = lenSq ? dot / lenSq : 0;
  if (param < 0) param = 0;
  if (param > 1) param = 1;
  return { x: x1 + param * C, y: y1 + param * D };
}

function nearestPointOnQuad(px, py, seg) {
  let best = { x: seg.x0, y: seg.y0 };
  let minD = Math.hypot(px - seg.x0, py - seg.y0);
  for (let i = 0; i <= 30; i++) {
    const t = i / 30;
    const pt = quadParametricPoint(seg, t);
    const d = Math.hypot(px - pt.x, py - pt.y);
    if (d < minD) { minD = d; best = pt; }
  }
  return best;
}

function nearestPointOnCubic(px, py, seg) {
  let best = { x: seg.x0, y: seg.y0 };
  let minD = Math.hypot(px - seg.x0, py - seg.y0);
  for (let i = 0; i <= 30; i++) {
    const t = i / 30;
    const pt = cubicParametricPoint(seg, t);
    const d = Math.hypot(px - pt.x, py - pt.y);
    if (d < minD) { minD = d; best = pt; }
  }
  return best;
}



// --- Rect / segment overlap for marquee ---
function rectContainsPoint(r, x, y) {
  const [x0, y0, x1, y1] = [Math.min(r.x0, r.x1), Math.min(r.y0, r.y1), Math.max(r.x0, r.x1), Math.max(r.y0, r.y1)];
  return x >= x0 && x <= x1 && y >= y0 && y <= y1;
}

function segmentIntersectsRect(seg, rx0, ry0, rx1, ry1) {
  const xMin = Math.min(rx0, rx1), xMax = Math.max(rx0, rx1);
  const yMin = Math.min(ry0, ry1), yMax = Math.max(ry0, ry1);
  if (seg.type === 'E') {
    const { cx, cy, rx, ry } = seg;
    if (cx + rx < xMin || cx - rx > xMax || cy + ry < yMin || cy - ry > yMax) return false;
    for (let t = 0; t < 1; t += 0.03) {
      const rad = t * Math.PI * 2;
      const px = cx + rx * Math.cos(rad), py = cy + ry * Math.sin(rad);
      if (px >= xMin && px <= xMax && py >= yMin && py <= yMax) return true;
    }
    const rectCorners = [[xMin, yMin], [xMax, yMin], [xMax, yMax], [xMin, yMax]];
    for (const [px, py] of rectCorners) {
      const dx = (px - cx) / rx, dy = (py - cy) / ry;
      if (dx * dx + dy * dy <= 1) return true;
    }
    const rectEdges = [[xMin, yMin, xMax, yMin], [xMax, yMin, xMax, yMax], [xMax, yMax, xMin, yMax], [xMin, yMax, xMin, yMin]];
    for (const [x0, y0, x1, y1] of rectEdges) {
      if (lineEllipseIntersection(x0, y0, x1, y1, seg).length >= 1) return true;
    }
    return false;
  }
  if (rectContainsPoint({ x0: rx0, y0: ry0, x1: rx1, y1: ry1 }, seg.x0, seg.y0)) return true;
  if (rectContainsPoint({ x0: rx0, y0: ry0, x1: rx1, y1: ry1 }, seg.x1, seg.y1)) return true;
  if (seg.type === 'Q' && rectContainsPoint({ x0: rx0, y0: ry0, x1: rx1, y1: ry1 }, seg.cx, seg.cy)) return true;
  if (seg.type === 'C' && (rectContainsPoint({ x0: rx0, y0: ry0, x1: rx1, y1: ry1 }, seg.c1x, seg.c1y) || rectContainsPoint({ x0: rx0, y0: ry0, x1: rx1, y1: ry1 }, seg.c2x, seg.c2y))) return true;
  if (seg.type === 'L') {
    const isec = lineLineIntersection(seg.x0, seg.y0, seg.x1, seg.y1, xMin, yMin, xMax, yMin);
    if (isec && isec.t > 0 && isec.t < 1) return true;
    const isec2 = lineLineIntersection(seg.x0, seg.y0, seg.x1, seg.y1, xMin, yMax, xMax, yMax);
    if (isec2 && isec2.t > 0 && isec2.t < 1) return true;
    const isec3 = lineLineIntersection(seg.x0, seg.y0, seg.x1, seg.y1, xMin, yMin, xMin, yMax);
    if (isec3 && isec3.t > 0 && isec3.t < 1) return true;
    const isec4 = lineLineIntersection(seg.x0, seg.y0, seg.x1, seg.y1, xMax, yMin, xMax, yMax);
    if (isec4 && isec4.t > 0 && isec4.t < 1) return true;
  } else if (seg.type === 'C') {
    for (let t = 0; t <= 1; t += 0.05) {
      const pt = cubicParametricPoint(seg, t);
      if (rectContainsPoint({ x0: rx0, y0: ry0, x1: rx1, y1: ry1 }, pt.x, pt.y)) return true;
    }
  } else {
    for (let t = 0; t <= 1; t += 0.05) {
      const pt = quadParametricPoint(seg, t);
      if (rectContainsPoint({ x0: rx0, y0: ry0, x1: rx1, y1: ry1 }, pt.x, pt.y)) return true;
    }
  }
  return false;
}

// --- Point in polygon (ray casting) ---
function pointInPolygon(x, y, poly) {
  let inside = false;
  for (let i = 0, j = poly.length - 1; i < poly.length; j = i++) {
    const [xi, yi] = poly[i], [xj, yj] = poly[j];
    if (((yi > y) !== (yj > y)) && (x < (xj - xi) * (y - yi) / (yj - yi) + xi)) inside = !inside;
  }
  return inside;
}

function fillToPolygon(fill) {
  if (fill.polygon) return fill.polygon;
  if (fill.segmentIndices) {
    const pts = [];
    const seen = new Set();
    const key = (x, y) => `${Math.round(x / 2)},${Math.round(y / 2)}`;
    for (const idx of fill.segmentIndices) {
      const s = segments[idx];
      if (!s) continue;
      if (s.type === 'E') {
        const arcs = ellipseToCubicArcs(s.cx, s.cy, s.rx, s.ry, {});
        for (const a of arcs) {
          for (const p of [[a.x0, a.y0], [a.x1, a.y1]]) {
            const k = key(p[0], p[1]);
            if (!seen.has(k)) { seen.add(k); pts.push(p); }
          }
        }
      } else {
        for (const p of [[s.x0, s.y0], [s.x1, s.y1]]) {
          const k = key(p[0], p[1]);
          if (!seen.has(k)) { seen.add(k); pts.push(p); }
        }
      }
    }
    if (pts.length < 3) return [];
    const cx = pts.reduce((s, p) => s + p[0], 0) / pts.length;
    const cy = pts.reduce((s, p) => s + p[1], 0) / pts.length;
    pts.sort((a, b) => Math.atan2(a[1] - cy, a[0] - cx) - Math.atan2(b[1] - cy, b[0] - cx));
    return pts;
  }
  return [];
}

function hitTestFill(canvasX, canvasY) {
  for (let i = fills.length - 1; i >= 0; i--) {
    const poly = fillToPolygon(fills[i]);
    if (poly.length >= 3 && pointInPolygon(canvasX, canvasY, poly)) return i;
  }
  return -1;
}

// --- Hit testing ---
function distToQuad(px, py, seg) {
  let minD = Infinity;
  for (let i = 0; i <= 25; i++) {
    const t = i / 25;
    const p = quadParametricPoint(seg, t);
    minD = Math.min(minD, Math.hypot(px - p.x, py - p.y));
  }
  return minD;
}

function cubicParametricPoint(seg, t) {
  const mt = 1 - t;
  const t2 = t * t, t3 = t2 * t, mt2 = mt * mt, mt3 = mt2 * mt;
  return {
    x: mt3 * seg.x0 + 3 * mt2 * t * seg.c1x + 3 * mt * t2 * seg.c2x + t3 * seg.x1,
    y: mt3 * seg.y0 + 3 * mt2 * t * seg.c1y + 3 * mt * t2 * seg.c2y + t3 * seg.y1
  };
}

function distToEllipse(px, py, seg) {
  const arcs = ellipseToCubicArcs(seg.cx, seg.cy, seg.rx, seg.ry, {});
  let minD = Infinity;
  for (const a of arcs) {
    minD = Math.min(minD, distToCubic(px, py, a));
  }
  return minD;
}

function distToCubic(px, py, seg) {
  let minD = Infinity;
  for (let i = 0; i <= 30; i++) {
    const t = i / 30;
    const p = cubicParametricPoint(seg, t);
    minD = Math.min(minD, Math.hypot(px - p.x, py - p.y));
  }
  return minD;
}

const ENDPOINT_HIT_RADIUS = 10;
const VERTEX_EPSILON = 2;

function getSegmentsAtVertex(x, y) {
  const result = [];
  for (let i = 0; i < segments.length; i++) {
    const seg = segments[i];
    if (Math.hypot(seg.x0 - x, seg.y0 - y) < VERTEX_EPSILON) result.push({ index: i, which: 'start' });
    else if (Math.hypot(seg.x1 - x, seg.y1 - y) < VERTEX_EPSILON) result.push({ index: i, which: 'end' });
  }
  return result;
}

function hitTestSegment(canvasX, canvasY) {
  for (let i = segments.length - 1; i >= 0; i--) {
    const seg = segments[i];
    const dToStart = Math.hypot(canvasX - seg.x0, canvasY - seg.y0);
    const dToEnd = Math.hypot(canvasX - seg.x1, canvasY - seg.y1);
    if (dToStart < ENDPOINT_HIT_RADIUS) {
      const atVertex = getSegmentsAtVertex(seg.x0, seg.y0);
      return { index: i, type: 'endpoint', which: 'start', atVertex };
    }
    if (dToEnd < ENDPOINT_HIT_RADIUS) {
      const atVertex = getSegmentsAtVertex(seg.x1, seg.y1);
      return { index: i, type: 'endpoint', which: 'end', atVertex };
    }
    let d;
    if (seg.type === 'L') {
      d = distToSegment(canvasX, canvasY, seg.x0, seg.y0, seg.x1, seg.y1);
    } else if (seg.type === 'E') {
      d = distToEllipse(canvasX, canvasY, seg);
    } else if (seg.type === 'C') {
      d = distToCubic(canvasX, canvasY, seg);
    } else {
      d = distToQuad(canvasX, canvasY, seg);
    }
    if (d < SEGMENT_HIT_TOLERANCE) return { index: i, type: 'segment' };
  }
  return null;
}

// --- Shift constrain: snap to 0° or 45° ---
function constrainToAngles(x0, y0, x1, y1) {
  const dx = x1 - x0, dy = y1 - y0;
  const len = Math.hypot(dx, dy);
  if (len < 1) return { x: x0, y: y0 };
  const angle = Math.atan2(dy, dx);
  const snap = Math.round(angle / (Math.PI / 4)) * (Math.PI / 4);
  return {
    x: x0 + Math.cos(snap) * len,
    y: y0 + Math.sin(snap) * len
  };
}

// --- White-dot pattern for selection (Flash-style) ---
let whiteDotPattern = null;
function getWhiteDotPattern() {
  if (whiteDotPattern) return whiteDotPattern;
  const size = 3;
  const pat = document.createElement('canvas');
  pat.width = size;
  pat.height = size;
  const pctx = pat.getContext('2d');
  pctx.fillStyle = '#ffffff';
  pctx.beginPath();
  pctx.arc(size / 2, size / 2, 0.35, 0, Math.PI * 2);
  pctx.fill();
  whiteDotPattern = ctx.createPattern(pat, 'repeat');
  return whiteDotPattern;
}

// --- Drawing ---
function drawSegment(seg, opts = {}) {
  const { selected = false } = opts;
  const w = seg.strokeWidth ?? DEFAULT_STROKE_WIDTH;
  const c = seg.strokeColor ?? DEFAULT_STROKE_COLOR;
  const dash = seg.strokeDashArray ?? null;
  ctx.beginPath();
  if (seg.type === 'L') {
    ctx.moveTo(seg.x0, seg.y0);
    ctx.lineTo(seg.x1, seg.y1);
  } else if (seg.type === 'E') {
    const arcs = ellipseToCubicArcs(seg.cx, seg.cy, seg.rx, seg.ry, {});
    ctx.moveTo(arcs[0].x0, arcs[0].y0);
    for (const a of arcs) {
      ctx.bezierCurveTo(a.c1x, a.c1y, a.c2x, a.c2y, a.x1, a.y1);
    }
  } else if (seg.type === 'C') {
    ctx.moveTo(seg.x0, seg.y0);
    ctx.bezierCurveTo(seg.c1x, seg.c1y, seg.c2x, seg.c2y, seg.x1, seg.y1);
  } else {
    ctx.moveTo(seg.x0, seg.y0);
    ctx.quadraticCurveTo(seg.cx, seg.cy, seg.x1, seg.y1);
  }
  ctx.lineCap = 'round';
  ctx.lineJoin = 'round';
  ctx.strokeStyle = c;
  ctx.lineWidth = w;
  if (dash && dash.length) ctx.setLineDash(dash);
  ctx.stroke();
  ctx.setLineDash([]);
  if (selected) {
    ctx.strokeStyle = '#ffffff';
    ctx.lineWidth = 1;
    ctx.setLineDash([1, 5]);
    ctx.lineCap = 'round';
    ctx.stroke();
    ctx.setLineDash([]);
  }
}

function render() {
  ctx.clearRect(0, 0, canvas.width, canvas.height);
  ctx.fillStyle = '#ffffff';
  ctx.fillRect(0, 0, canvas.width, canvas.height);
  fills.forEach((f, fi) => {
    const isFillSelected = selectedFillIndices.has(fi);
    if (f.segmentIndices) {
      ctx.beginPath();
      const segs = f.segmentIndices.map(i => segments[i]).filter(Boolean);
      if (segs.length > 0) {
        const ptEq = (a, b) => Math.hypot(a[0] - b[0], a[1] - b[1]) < 2;
        let px, py;
        const first = segs[0];
        if (first.type === 'E') {
          const arcs = ellipseToCubicArcs(first.cx, first.cy, first.rx, first.ry, {});
          ctx.moveTo(arcs[0].x0, arcs[0].y0);
          for (const a of arcs) ctx.bezierCurveTo(a.c1x, a.c1y, a.c2x, a.c2y, a.x1, a.y1);
          px = arcs[3].x1; py = arcs[3].y1;
        } else {
          px = first.x0; py = first.y0;
          ctx.moveTo(px, py);
          const ex = first.x1, ey = first.y1;
          if (first.type === 'L') ctx.lineTo(ex, ey);
          else if (first.type === 'C') ctx.bezierCurveTo(first.c1x, first.c1y, first.c2x, first.c2y, ex, ey);
          else ctx.quadraticCurveTo(first.cx, first.cy, ex, ey);
          px = ex; py = ey;
        }
        for (let i = 1; i < segs.length; i++) {
          const seg = segs[i];
          if (seg.type === 'E') {
            const arcs = ellipseToCubicArcs(seg.cx, seg.cy, seg.rx, seg.ry, {});
            if (ptEq([px, py], [arcs[0].x0, arcs[0].y0])) {
              for (const a of arcs) ctx.bezierCurveTo(a.c1x, a.c1y, a.c2x, a.c2y, a.x1, a.y1);
              px = arcs[3].x1; py = arcs[3].y1;
            } else {
              for (let j = 3; j >= 0; j--) {
                const a = arcs[j];
                ctx.bezierCurveTo(a.c2x, a.c2y, a.c1x, a.c1y, a.x0, a.y0);
              }
              px = arcs[0].x0; py = arcs[0].y0;
            }
          } else {
            const forward = ptEq([px, py], [seg.x0, seg.y0]);
            const ex = forward ? seg.x1 : seg.x0, ey = forward ? seg.y1 : seg.y0;
            if (seg.type === 'L') ctx.lineTo(ex, ey);
            else if (seg.type === 'C') {
              if (forward) ctx.bezierCurveTo(seg.c1x, seg.c1y, seg.c2x, seg.c2y, ex, ey);
              else ctx.bezierCurveTo(seg.c2x, seg.c2y, seg.c1x, seg.c1y, ex, ey);
            } else {
              if (forward) ctx.quadraticCurveTo(seg.cx, seg.cy, ex, ey);
              else ctx.quadraticCurveTo(seg.x0 + seg.x1 - seg.cx, seg.y0 + seg.y1 - seg.cy, ex, ey);
            }
            px = ex; py = ey;
          }
        }
        ctx.closePath();
        ctx.fillStyle = f.color;
        ctx.fill();
        if (isFillSelected) {
          ctx.fillStyle = getWhiteDotPattern();
          ctx.fill();
          ctx.strokeStyle = '#ffffff';
          ctx.lineWidth = 1;
          ctx.setLineDash([1, 6]);
          ctx.lineCap = 'round';
          ctx.stroke();
          ctx.setLineDash([]);
        }
      }
    } else if (f.polygon) {
      ctx.beginPath();
      ctx.moveTo(f.polygon[0][0], f.polygon[0][1]);
      for (let i = 1; i < f.polygon.length; i++) ctx.lineTo(f.polygon[i][0], f.polygon[i][1]);
      ctx.closePath();
      ctx.fillStyle = f.color;
      ctx.fill();
      if (isFillSelected) {
        ctx.fillStyle = getWhiteDotPattern();
        ctx.fill();
        ctx.strokeStyle = '#ffffff';
        ctx.lineWidth = 1;
        ctx.setLineDash([1, 6]);
        ctx.lineCap = 'round';
        ctx.stroke();
        ctx.setLineDash([]);
      }
    }
  });
  segments.forEach((seg, i) => drawSegment(seg, { selected: selectedIndices.has(i) }));
  if (penPreview) {
    ctx.beginPath();
    ctx.moveTo(penPreview.x0, penPreview.y0);
    if (penPreview.type === 'Q') {
      ctx.quadraticCurveTo(penPreview.cx, penPreview.cy, penPreview.x1, penPreview.y1);
    } else {
      ctx.lineTo(penPreview.x1, penPreview.y1);
    }
    ctx.strokeStyle = '#737373';
    ctx.lineWidth = 1.5;
    ctx.setLineDash([4, 4]);
    ctx.stroke();
    ctx.setLineDash([]);
  }
  if (dragState && dragState.type === 'rect') {
    const { x0, y0, x1, y1 } = dragState;
    let left = Math.min(x0, x1), right = Math.max(x0, x1), top = Math.min(y0, y1), bottom = Math.max(y0, y1);
    let w = right - left, h = bottom - top;
    if (dragState.shiftKey && w > 2 && h > 2) {
      const s = Math.max(w, h);
      const dx = x1 - x0, dy = y1 - y0;
      const xEnd = x0 + (dx >= 0 ? s : -s), yEnd = y0 + (dy >= 0 ? s : -s);
      left = Math.min(x0, xEnd); right = Math.max(x0, xEnd);
      top = Math.min(y0, yEnd); bottom = Math.max(y0, yEnd);
      w = right - left; h = bottom - top;
    }
    ctx.strokeStyle = '#737373';
    ctx.lineWidth = 1.5;
    ctx.setLineDash([4, 4]);
    ctx.strokeRect(left, top, w, h);
    ctx.setLineDash([]);
  }
  if (dragState && dragState.type === 'oval') {
    const { x0, y0, x1, y1 } = dragState;
    let rx = Math.abs(x1 - x0) / 2, ry = Math.abs(y1 - y0) / 2;
    const cx = (x0 + x1) / 2, cy = (y0 + y1) / 2;
    if (dragState.shiftKey) {
      rx = ry = Math.max(rx, ry);
    }
    if (rx > 1 && ry > 1) {
      ctx.beginPath();
      ctx.ellipse(cx, cy, rx, ry, 0, 0, Math.PI * 2);
      ctx.strokeStyle = '#737373';
      ctx.lineWidth = 1.5;
      ctx.setLineDash([4, 4]);
      ctx.stroke();
      ctx.setLineDash([]);
    }
  }
  if (marqueeRect) {
    const x0 = Math.min(marqueeRect.x0, marqueeRect.x1);
    const y0 = Math.min(marqueeRect.y0, marqueeRect.y1);
    const w = Math.abs(marqueeRect.x1 - marqueeRect.x0);
    const h = Math.abs(marqueeRect.y1 - marqueeRect.y0);
    ctx.fillStyle = 'rgba(0, 112, 243, 0.12)';
    ctx.fillRect(x0, y0, w, h);
    ctx.strokeStyle = '#0070f3';
    ctx.lineWidth = 1.5;
    ctx.setLineDash([4, 4]);
    ctx.strokeRect(x0, y0, w, h);
    ctx.setLineDash([]);
  }
  updatePropertiesPanel();
}

function screenToCanvas(e) {
  const rect = canvas.getBoundingClientRect();
  return { x: e.clientX - rect.left, y: e.clientY - rect.top };
}

// --- Paint bucket: find smallest enclosing cycle (Photoshop-like: slicing creates new boundaries) ---
// E segments are expanded to 4 arcs for cycle finding; cycles map back to original segment indices
function findFillContour(startX, startY) {
  const eps = 2;
  const key = (x, y) => `${Math.round(x / eps)},${Math.round(y / eps)}`;
  const expandedSegments = [];
  const expandedToOriginal = [];
  for (let i = 0; i < segments.length; i++) {
    const seg = segments[i];
    if (seg.type === 'E') {
      const arcs = ellipseToCubicArcs(seg.cx, seg.cy, seg.rx, seg.ry, {});
      for (const a of arcs) {
        expandedSegments.push(a);
        expandedToOriginal.push(i);
      }
    } else {
      expandedSegments.push(seg);
      expandedToOriginal.push(i);
    }
  }
  const segAtKey = new Map();
  for (let i = 0; i < expandedSegments.length; i++) {
    const seg = expandedSegments[i];
    const k0 = key(seg.x0, seg.y0), k1 = key(seg.x1, seg.y1);
    if (!segAtKey.has(k0)) segAtKey.set(k0, []);
    segAtKey.get(k0).push({ i, which: 'start' });
    if (!segAtKey.has(k1)) segAtKey.set(k1, []);
    segAtKey.get(k1).push({ i, which: 'end' });
  }
  const cyclesContainingPoint = [];
  const cycleKey = (path) => [...path].sort((a, b) => a - b).join(',');
  const seenCycles = new Set();
  const maxCycleLen = Math.min(expandedSegments.length + 2, 32);
  const maxStates = 12000;
  let statesProcessed = 0;
  function samplePointsOnSeg(seg, n) {
    const pts = [];
    for (let i = 0; i <= n; i++) {
      const t = i / n;
      if (seg.c1x !== undefined) {
        const p = cubicParametricPoint(seg, t);
        pts.push([p.x, p.y]);
      } else {
        pts.push([seg.x0 + t * (seg.x1 - seg.x0), seg.y0 + t * (seg.y1 - seg.y0)]);
      }
    }
    return pts;
  }
  function recordCycleIfValid(path, startX, startY) {
    if (path.length < 2) return;
    const ck = cycleKey(path);
    if (seenCycles.has(ck)) return;
    seenCycles.add(ck);
    const pts = [];
    for (const idx of path) {
      const sb = expandedSegments[idx];
      if (path.length === 2) {
        pts.push(...samplePointsOnSeg(sb, 8));
      } else {
        pts.push([sb.x0, sb.y0], [sb.x1, sb.y1]);
      }
    }
    const ptSeen = new Set();
    const poly = [];
    for (const p of pts) {
      const kp = key(p[0], p[1]);
      if (!ptSeen.has(kp)) { ptSeen.add(kp); poly.push(p); }
    }
    if (poly.length >= 3) {
      const cx = poly.reduce((s, p) => s + p[0], 0) / poly.length;
      const cy = poly.reduce((s, p) => s + p[1], 0) / poly.length;
      poly.sort((a, b) => Math.atan2(a[1] - cy, a[0] - cx) - Math.atan2(b[1] - cy, b[0] - cx));
      let inside = false;
      for (let i = 0, j = poly.length - 1; i < poly.length; j = i++) {
        const [xi, yi] = poly[i], [xj, yj] = poly[j];
        if (((yi > startY) !== (yj > startY)) && (startX < (xj - xi) * (startY - yi) / (yj - yi) + xi)) inside = !inside;
      }
      if (inside) {
        const area = Math.abs(poly.reduce((sum, p, i) => sum + p[0] * (poly[(i + 1) % poly.length][1] - poly[(i - 1 + poly.length) % poly.length][1]), 0) / 2);
        const originalPath = [];
        let last = -1;
        for (const idx of path) {
          const orig = expandedToOriginal[idx];
          if (orig !== last) { originalPath.push(orig); last = orig; }
        }
        cyclesContainingPoint.push({ path: originalPath, area });
      }
    }
  }
  for (let start = 0; start < expandedSegments.length && statesProcessed < maxStates; start++) {
    const seg = expandedSegments[start];
    const startPt = [seg.x0, seg.y0];
    const stack = [{ path: [start], cur: start, pt: [seg.x1, seg.y1] }];
    while (stack.length > 0 && statesProcessed < maxStates) {
      const { path, cur, pt } = stack.pop();
      statesProcessed++;
      if (path.length > maxCycleLen) continue;
      if (Math.hypot(pt[0] - startPt[0], pt[1] - startPt[1]) < eps * 2 && path.length >= 2) {
        recordCycleIfValid(path, startX, startY);
        continue;
      }
      const k = key(pt[0], pt[1]);
      const neighbors = segAtKey.get(k) || [];
      const candidates = neighbors.filter(n => n.i !== cur && !path.includes(n.i));
      for (const n of candidates) {
        const s = expandedSegments[n.i];
        const nextPt = n.which === 'start' ? [s.x1, s.y1] : [s.x0, s.y0];
        stack.push({ path: [...path, n.i], cur: n.i, pt: nextPt });
      }
    }
  }
  if (cyclesContainingPoint.length === 0) return null;
  cyclesContainingPoint.sort((a, b) => a.area - b.area);
  return cyclesContainingPoint[0].path;
}

function snapToNearestEndpoint(x, y) {
  return snapToNearestPoint(x, y);
}

function snapToNearestPoint(x, y, excludeSegIndices = new Set()) {
  let best = null;
  let minDist = SNAP_TO_ENDPOINT_RADIUS;
  for (let i = 0; i < segments.length; i++) {
    const seg = segments[i];
    const d0 = Math.hypot(x - seg.x0, y - seg.y0);
    const d1 = Math.hypot(x - seg.x1, y - seg.y1);
    if (d0 < minDist) { minDist = d0; best = { x: seg.x0, y: seg.y0 }; }
    if (d1 < minDist) { minDist = d1; best = { x: seg.x1, y: seg.y1 }; }
    if (!excludeSegIndices.has(i)) {
      let pt;
      if (seg.type === 'L') {
        pt = nearestPointOnSegment(x, y, seg.x0, seg.y0, seg.x1, seg.y1);
      } else if (seg.type === 'C') {
        pt = nearestPointOnCubic(x, y, seg);
      } else {
        pt = nearestPointOnQuad(x, y, seg);
      }
      const d = Math.hypot(x - pt.x, y - pt.y);
      if (d < minDist) { minDist = d; best = pt; }
    }
  }
  return best || { x, y };
}

function pushUndo() {
  undoStack.push({ segments: JSON.parse(JSON.stringify(segments)), fills: JSON.parse(JSON.stringify(fills)) });
  if (undoStack.length > MAX_UNDO) undoStack.shift();
  redoStack = [];
}

function undo() {
  if (undoStack.length === 0) return;
  redoStack.push({ segments: JSON.parse(JSON.stringify(segments)), fills: JSON.parse(JSON.stringify(fills)) });
  const state = undoStack.pop();
  segments = state.segments;
  fills = state.fills;
  selectedIndices.clear();
  selectedFillIndices.clear();
  render();
}

function redo() {
  if (redoStack.length === 0) return;
  undoStack.push({ segments: JSON.parse(JSON.stringify(segments)), fills: JSON.parse(JSON.stringify(fills)) });
  const state = redoStack.pop();
  segments = state.segments;
  fills = state.fills;
  selectedIndices.clear();
  selectedFillIndices.clear();
  render();
}

// --- Export to SVG ---
function exportToSVG() {
  const w = canvas.width;
  const h = canvas.height;
  const ptEq = (a, b) => Math.hypot(a[0] - b[0], a[1] - b[1]) < 2;
  let svg = `<?xml version="1.0" encoding="UTF-8"?>\n<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 ${w} ${h}" width="${w}" height="${h}">\n`;
  svg += `  <rect width="100%" height="100%" fill="#ffffff"/>\n`;
  fills.forEach((f) => {
    let d = '';
    if (f.segmentIndices) {
      const segs = f.segmentIndices.map((i) => segments[i]).filter(Boolean);
      if (segs.length > 0) {
        let px = segs[0].x0, py = segs[0].y0;
        d = `M ${px} ${py}`;
        for (const seg of segs) {
          const forward = ptEq([px, py], [seg.x0, seg.y0]);
          const ex = forward ? seg.x1 : seg.x0, ey = forward ? seg.y1 : seg.y0;
          if (seg.type === 'L') d += ` L ${ex} ${ey}`;
          else if (seg.type === 'C') d += ` C ${forward ? `${seg.c1x} ${seg.c1y} ${seg.c2x} ${seg.c2y}` : `${seg.c2x} ${seg.c2y} ${seg.c1x} ${seg.c1y}`} ${ex} ${ey}`;
          else {
            const cpx = forward ? seg.cx : seg.x0 + seg.x1 - seg.cx;
            const cpy = forward ? seg.cy : seg.y0 + seg.y1 - seg.cy;
            d += ` Q ${cpx} ${cpy} ${ex} ${ey}`;
          }
          px = ex; py = ey;
        }
        d += ' Z';
      }
    } else if (f.polygon) {
      d = `M ${f.polygon[0][0]} ${f.polygon[0][1]}`;
      for (let i = 1; i < f.polygon.length; i++) d += ` L ${f.polygon[i][0]} ${f.polygon[i][1]}`;
      d += ' Z';
    }
    if (d) svg += `  <path d="${d}" fill="${f.color}" stroke="none"/>\n`;
  });
  segments.forEach((seg) => {
    const w_ = seg.strokeWidth ?? DEFAULT_STROKE_WIDTH;
    const c = seg.strokeColor ?? DEFAULT_STROKE_COLOR;
    const dash = seg.strokeDashArray;
    let d;
    if (seg.type === 'L') d = `M ${seg.x0} ${seg.y0} L ${seg.x1} ${seg.y1}`;
    else if (seg.type === 'C') d = `M ${seg.x0} ${seg.y0} C ${seg.c1x} ${seg.c1y} ${seg.c2x} ${seg.c2y} ${seg.x1} ${seg.y1}`;
    else d = `M ${seg.x0} ${seg.y0} Q ${seg.cx} ${seg.cy} ${seg.x1} ${seg.y1}`;
    let strokeAttrs = `stroke="${c}" stroke-width="${w_}" fill="none" stroke-linecap="round" stroke-linejoin="round"`;
    if (dash && dash.length) strokeAttrs += ` stroke-dasharray="${dash.join(' ')}"`;
    svg += `  <path d="${d}" ${strokeAttrs}/>\n`;
  });
  svg += '</svg>';
  const blob = new Blob([svg], { type: 'image/svg+xml' });
  const url = URL.createObjectURL(blob);
  const a = document.createElement('a');
  a.href = url;
  a.download = 'drawing.svg';
  a.click();
  URL.revokeObjectURL(url);
}

// --- Pen tool: drag only, Shift = 0/45° ---
function penMouseDown(e) {
  const p = screenToCanvas(e);
  const snapped = snapToNearestEndpoint(p.x, p.y);
  dragState = {
    type: 'pen',
    x0: snapped.x,
    y0: snapped.y,
    x1: snapped.x,
    y1: snapped.y,
    shift: e.shiftKey
  };
  penPreview = { ...dragState, type: 'L' };
  render();
}

function penMouseMove(e) {
  const p = screenToCanvas(e);
  if (dragState && dragState.type === 'pen') {
    let x1 = p.x, y1 = p.y;
    if (e.shiftKey) {
      const constrained = constrainToAngles(dragState.x0, dragState.y0, p.x, p.y);
      x1 = constrained.x;
      y1 = constrained.y;
    }
    const snapped = snapToNearestPoint(x1, y1);
    x1 = snapped.x;
    y1 = snapped.y;
    const dist = Math.hypot(x1 - dragState.x0, y1 - dragState.y0);
    if (dist > 5) {
      penPreview = { x0: dragState.x0, y0: dragState.y0, x1, y1, type: 'L' };
    } else {
      penPreview = { x0: dragState.x0, y0: dragState.y0, x1: dragState.x0, y1: dragState.y0, type: 'L' };
    }
  }
  render();
}

function penMouseUp(e) {
  if (!dragState || dragState.type !== 'pen') return;
  const p = screenToCanvas(e);
  let x1 = p.x, y1 = p.y;
  if (e.shiftKey) {
    const constrained = constrainToAngles(dragState.x0, dragState.y0, p.x, p.y);
    x1 = constrained.x;
    y1 = constrained.y;
  }
  const snapped = snapToNearestPoint(x1, y1);
  x1 = snapped.x;
  y1 = snapped.y;
  const dist = Math.hypot(x1 - dragState.x0, y1 - dragState.y0);
  if (dist < 3) {
    dragState = null;
    penPreview = null;
    render();
    return;
  }

  pushUndo();
  const newLine = { type: 'L', x0: dragState.x0, y0: dragState.y0, x1, y1, strokeWidth: currentStrokeWidth, strokeColor: currentStrokeColor, strokeDashArray: currentStrokeDash };

  // 1. Find all intersections of new line with existing segments (L and C)
  const newLineIntersections = [];
  const segmentsToSplit = new Map();

  for (let i = 0; i < segments.length; i++) {
    const seg = segments[i];
    if (seg.type === 'L') {
      const isec = lineLineIntersection(newLine.x0, newLine.y0, newLine.x1, newLine.y1, seg.x0, seg.y0, seg.x1, seg.y1);
      if (isec && isec.t > 0.001 && isec.t < 0.999) {
        newLineIntersections.push({ t: isec.t, x: isec.x, y: isec.y });
        if (!segmentsToSplit.has(i)) segmentsToSplit.set(i, []);
        segmentsToSplit.get(i).push({ u: isec.u, x: isec.x, y: isec.y });
      }
    } else if (seg.type === 'C') {
      const list = lineCubicIntersection(newLine.x0, newLine.y0, newLine.x1, newLine.y1, seg);
      for (const isec of list) {
        newLineIntersections.push({ t: isec.t, x: isec.x, y: isec.y });
        if (!segmentsToSplit.has(i)) segmentsToSplit.set(i, []);
        segmentsToSplit.get(i).push({ u: isec.u, x: isec.x, y: isec.y });
      }
    } else if (seg.type === 'E') {
      const list = lineEllipseIntersection(newLine.x0, newLine.y0, newLine.x1, newLine.y1, seg);
      if (list.length >= 2) {
        for (const isec of list) {
          newLineIntersections.push({ t: isec.lineT, x: isec.x, y: isec.y });
        }
        segmentsToSplit.set(i, list);
      }
    }
  }

  // 2. Sort intersections by t, dedupe (same crossing from both segments), split new line into pieces
  newLineIntersections.sort((a, b) => a.t - b.t);
  const deduped = [];
  for (const isec of newLineIntersections) {
    if (deduped.length === 0 || Math.abs(deduped[deduped.length - 1].t - isec.t) > 0.001) {
      deduped.push(isec);
    }
  }
  const newPieces = [];
  let cur = { x0: newLine.x0, y0: newLine.y0, x1: newLine.x1, y1: newLine.y1 };
  const strokeProps = { strokeWidth: newLine.strokeWidth, strokeColor: newLine.strokeColor, strokeDashArray: newLine.strokeDashArray };
  for (const isec of deduped) {
    newPieces.push({ type: 'L', x0: cur.x0, y0: cur.y0, x1: isec.x, y1: isec.y, ...strokeProps });
    cur = { x0: isec.x, y0: isec.y, x1: newLine.x1, y1: newLine.y1 };
  }
  newPieces.push({ type: 'L', x0: cur.x0, y0: cur.y0, x1: cur.x1, y1: cur.y1, ...strokeProps });

  // 3. Split crossed segments and rebuild array (with fill index remapping)
  const result = [];
  const toRemove = new Set();
  const oldToNew = new Map();
  let newIdx = 0;
  for (let i = 0; i < segments.length; i++) {
    const seg = segments[i];
    const splits = segmentsToSplit.get(i);
    if (splits && seg.type === 'E') {
      toRemove.add(i);
      splits.sort((a, b) => (a.ellipseParam ?? a.arcIdx + a.t) - (b.ellipseParam ?? b.arcIdx + b.t));
      const pieces = splitEllipseAtCrossings(seg, splits);
      result.push(...pieces);
      newIdx += pieces.length;
    } else if (splits) {
      toRemove.add(i);
      splits.sort((a, b) => a.u - b.u);
      let u0 = 0;
      let prev = seg;
      for (const s of splits) {
        if (seg.type === 'L') {
          const props = withStrokeProps(seg);
          const x0 = seg.x0 + u0 * (seg.x1 - seg.x0);
          const y0 = seg.y0 + u0 * (seg.y1 - seg.y0);
          result.push({ type: 'L', x0, y0, x1: s.x, y1: s.y, ...props });
        } else if (seg.type === 'C') {
          const t = (s.u - u0) / (1 - u0);
          const [left, right] = splitCubicAt(prev, t);
          result.push(left);
          prev = right;
        }
        u0 = s.u;
      }
      if (seg.type === 'L') {
        const props = withStrokeProps(seg);
        const x0 = seg.x0 + u0 * (seg.x1 - seg.x0);
        const y0 = seg.y0 + u0 * (seg.y1 - seg.y0);
        result.push({ type: 'L', x0, y0, x1: seg.x1, y1: seg.y1, ...props });
      } else {
        result.push(prev);
      }
      newIdx = result.length;
    } else {
      oldToNew.set(i, newIdx);
      result.push(segments[i]);
      newIdx++;
    }
  }
  result.push(...newPieces);
  segments = result;

  fills = fills.filter(f => {
    if (!f.segmentIndices) return true;
    if (f.segmentIndices.some(idx => toRemove.has(idx))) return false;
    f.segmentIndices = f.segmentIndices.map(idx => oldToNew.get(idx) ?? idx);
    return true;
  });

  selectedIndices.clear();
  for (let i = segments.length - newPieces.length; i < segments.length; i++) selectedIndices.add(i);
  dragState = null;
  penPreview = null;
  render();
}

// --- Selection tool: click select, Shift+click multi-select, marquee, drag endpoint, drag segment = pull curve ---
function selectMouseDown(e) {
  const p = screenToCanvas(e);
  const hit = hitTestSegment(p.x, p.y);
  const fillHit = hitTestFill(p.x, p.y);
  if (hit) {
    selectedFillIndices.clear();
    if (e.shiftKey) {
      if (selectedIndices.has(hit.index)) selectedIndices.delete(hit.index);
      else selectedIndices.add(hit.index);
    } else {
      selectedIndices.clear();
      selectedIndices.add(hit.index);
    }
    const seg = segments[hit.index];
    if (hit.type === 'endpoint') {
      const vertices = hit.atVertex || [{ index: hit.index, which: hit.which }];
      pushUndo();
      dragState = {
        type: 'moveEndpoint',
        vertices
      };
    } else {
      const onSegment = seg.type === 'L' ? distToSegment(p.x, p.y, seg.x0, seg.y0, seg.x1, seg.y1) < SEGMENT_HIT_TOLERANCE : seg.type === 'C' ? distToCubic(p.x, p.y, seg) < SEGMENT_HIT_TOLERANCE : distToQuad(p.x, p.y, seg) < SEGMENT_HIT_TOLERANCE;
      if (onSegment && selectedIndices.size === 1) {
        pushUndo();
        dragState = {
          type: 'pull',
          segmentIndex: hit.index,
          startX: p.x,
          startY: p.y
        };
      } else if (onSegment && selectedIndices.size > 1) {
        pushUndo();
        dragState = {
          type: 'move',
          lastX: p.x,
          lastY: p.y,
          indices: [...selectedIndices]
        };
      } else {
        pushUndo();
        dragState = {
          type: 'move',
          lastX: p.x,
          lastY: p.y,
          indices: [...selectedIndices]
        };
      }
    }
  } else if (fillHit >= 0) {
    selectedIndices.clear();
    if (e.shiftKey) {
      if (selectedFillIndices.has(fillHit)) selectedFillIndices.delete(fillHit);
      else selectedFillIndices.add(fillHit);
    } else {
      selectedFillIndices.clear();
      selectedFillIndices.add(fillHit);
    }
  } else {
    if (!e.shiftKey) selectedIndices.clear();
    if (!e.shiftKey) selectedFillIndices.clear();
    dragState = { type: 'marquee', x0: p.x, y0: p.y, shiftKey: e.shiftKey };
    marqueeRect = { x0: p.x, y0: p.y, x1: p.x, y1: p.y };
  }
  render();
}

function selectMouseMove(e) {
  const p = screenToCanvas(e);
  if (dragState) {
    if (dragState.type === 'pull') {
      const seg = segments[dragState.segmentIndex];
      if (seg.type === 'L') {
        const props = withStrokeProps(seg);
        segments[dragState.segmentIndex] = {
          type: 'Q',
          x0: seg.x0, y0: seg.y0,
          cx: p.x, cy: p.y,
          x1: seg.x1, y1: seg.y1,
          ...props
        };
      } else if (seg.type === 'Q') {
        seg.cx = p.x;
        seg.cy = p.y;
      } else if (seg.type === 'C') {
        const dx = p.x - dragState.startX, dy = p.y - dragState.startY;
        seg.c1x += dx;
        seg.c1y += dy;
        seg.c2x += dx;
        seg.c2y += dy;
        dragState.startX = p.x;
        dragState.startY = p.y;
      }
    } else if (dragState.type === 'move') {
      const dx = p.x - dragState.lastX;
      const dy = p.y - dragState.lastY;
      dragState.lastX = p.x;
      dragState.lastY = p.y;
      for (const i of dragState.indices) {
        const seg = segments[i];
        seg.x0 += dx; seg.y0 += dy;
        seg.x1 += dx; seg.y1 += dy;
        if (seg.type === 'Q') { seg.cx += dx; seg.cy += dy; }
        if (seg.type === 'C') { seg.c1x += dx; seg.c1y += dy; seg.c2x += dx; seg.c2y += dy; }
      }
    } else if (dragState.type === 'moveEndpoint') {
      const exclude = new Set(dragState.vertices.map(v => v.index));
      let tx = p.x, ty = p.y;
      if (e.shiftKey && dragState.vertices.length > 0) {
        const { index, which } = dragState.vertices[0];
        const seg = segments[index];
        const anchorX = which === 'start' ? seg.x1 : seg.x0;
        const anchorY = which === 'start' ? seg.y1 : seg.y0;
        const constrained = constrainToAngles(anchorX, anchorY, p.x, p.y);
        tx = constrained.x;
        ty = constrained.y;
      }
      const snapped = snapToNearestPoint(tx, ty, exclude);
      for (const { index, which } of dragState.vertices) {
        const seg = segments[index];
        if (which === 'start') {
          seg.x0 = snapped.x;
          seg.y0 = snapped.y;
        } else {
          seg.x1 = snapped.x;
          seg.y1 = snapped.y;
        }
      }
    } else if (dragState.type === 'marquee') {
      marqueeRect = { x0: dragState.x0, y0: dragState.y0, x1: p.x, y1: p.y };
    }
  } else {
    const hit = hitTestSegment(p.x, p.y);
    canvas.classList.toggle('over-segment', !!hit);
  }
  render();
}

function selectMouseUp(e) {
  if (dragState && dragState.type === 'marquee' && marqueeRect) {
    const xMin = Math.min(marqueeRect.x0, marqueeRect.x1);
    const xMax = Math.max(marqueeRect.x0, marqueeRect.x1);
    const yMin = Math.min(marqueeRect.y0, marqueeRect.y1);
    const yMax = Math.max(marqueeRect.y0, marqueeRect.y1);
    const w = xMax - xMin, h = yMax - yMin;
    if (w > 4 && h > 4) {
      const inRect = [];
      for (let i = 0; i < segments.length; i++) {
        if (segmentIntersectsRect(segments[i], xMin, yMin, xMax, yMax)) inRect.push(i);
      }
      const fillsInRect = [];
      for (let i = 0; i < fills.length; i++) {
        const poly = fillToPolygon(fills[i]);
        const anyInside = poly.some(([px, py]) => px >= xMin && px <= xMax && py >= yMin && py <= yMax);
        if (anyInside) fillsInRect.push(i);
      }
      if (dragState.shiftKey) {
        inRect.forEach(i => selectedIndices.add(i));
        fillsInRect.forEach(i => selectedFillIndices.add(i));
      } else {
        selectedIndices.clear();
        selectedFillIndices.clear();
        inRect.forEach(i => selectedIndices.add(i));
        fillsInRect.forEach(i => selectedFillIndices.add(i));
      }
    }
  }
  if (dragState && (dragState.type === 'move' || dragState.type === 'moveEndpoint')) {
    let didSplit = false;
    while (splitSegmentsAtAllIntersections()) { didSplit = true; }
    if (didSplit) { selectedIndices.clear(); selectedFillIndices.clear(); }
  }
  dragState = null;
  marqueeRect = null;
  render();
}

// --- Rectangle tool: drag to draw, Shift = square ---
function rectMouseDown(e) {
  const p = screenToCanvas(e);
  const snapped = snapToNearestPoint(p.x, p.y);
  dragState = { type: 'rect', x0: snapped.x, y0: snapped.y, x1: snapped.x, y1: snapped.y, shift: e.shiftKey };
  render();
}

function rectMouseMove(e) {
  if (!dragState || dragState.type !== 'rect') return;
  const p = screenToCanvas(e);
  let x1 = p.x, y1 = p.y;
  if (e.shiftKey) {
    const w = Math.abs(p.x - dragState.x0);
    const h = Math.abs(p.y - dragState.y0);
    const s = Math.max(w, h);
    x1 = dragState.x0 + (p.x >= dragState.x0 ? s : -s);
    y1 = dragState.y0 + (p.y >= dragState.y0 ? s : -s);
  }
  dragState.x1 = x1;
  dragState.y1 = y1;
  render();
}

function rectMouseUp(e) {
  if (!dragState || dragState.type !== 'rect') return;
  const { x0, y0, x1, y1 } = dragState;
  let left, right, top, bottom;
  if (e.shiftKey) {
    const dx = x1 - x0, dy = y1 - y0;
    const s = Math.max(Math.abs(dx), Math.abs(dy));
    const xEnd = x0 + (dx >= 0 ? s : -s), yEnd = y0 + (dy >= 0 ? s : -s);
    left = Math.min(x0, xEnd);
    right = Math.max(x0, xEnd);
    top = Math.min(y0, yEnd);
    bottom = Math.max(y0, yEnd);
  } else {
    left = Math.min(x0, x1);
    right = Math.max(x0, x1);
    top = Math.min(y0, y1);
    bottom = Math.max(y0, y1);
  }
  const w = right - left, h = bottom - top;
  if (w < 3 || h < 3) {
    dragState = null;
    render();
    return;
  }
  pushUndo();
  const props = { strokeWidth: currentStrokeWidth, strokeColor: currentStrokeColor, strokeDashArray: currentStrokeDash };
  const segs = [
    { type: 'L', x0: left, y0: top, x1: left + w, y1: top, ...props },
    { type: 'L', x0: left + w, y0: top, x1: left + w, y1: top + h, ...props },
    { type: 'L', x0: left + w, y0: top + h, x1: left, y1: top + h, ...props },
    { type: 'L', x0: left, y0: top + h, x1: left, y1: top, ...props }
  ];
  segments.push(...segs);
  while (splitSegmentsAtAllIntersections()) { /* repeat until no more intersections */ }
  selectedIndices.clear();
  for (let i = segments.length - 4; i < segments.length; i++) selectedIndices.add(i);
  dragState = null;
  render();
}

// --- Oval tool: drag to draw, Shift = circle. Single E segment until crossed by another line. ---
function ovalMouseDown(e) {
  const p = screenToCanvas(e);
  const snapped = snapToNearestPoint(p.x, p.y);
  dragState = { type: 'oval', x0: snapped.x, y0: snapped.y, x1: snapped.x, y1: snapped.y, shift: e.shiftKey };
  render();
}

function ovalMouseMove(e) {
  if (!dragState || dragState.type !== 'oval') return;
  const p = screenToCanvas(e);
  let x1 = p.x, y1 = p.y;
  if (e.shiftKey) {
    const w = Math.abs(p.x - dragState.x0);
    const h = Math.abs(p.y - dragState.y0);
    const s = Math.max(w, h);
    x1 = dragState.x0 + (p.x >= dragState.x0 ? s : -s);
    y1 = dragState.y0 + (p.y >= dragState.y0 ? s : -s);
  }
  dragState.x1 = x1;
  dragState.y1 = y1;
  dragState.shiftKey = e.shiftKey;
  render();
}

function ovalMouseUp(e) {
  if (!dragState || dragState.type !== 'oval') return;
  const { x0, y0, x1, y1 } = dragState;
  let rx = Math.abs(x1 - x0) / 2, ry = Math.abs(y1 - y0) / 2;
  if (e.shiftKey) {
    const r = Math.max(rx, ry);
    rx = r;
    ry = r;
  }
  const cx = (x0 + x1) / 2, cy = (y0 + y1) / 2;
  if (rx < 2 || ry < 2) {
    dragState = null;
    render();
    return;
  }
  pushUndo();
  const props = { strokeWidth: currentStrokeWidth, strokeColor: currentStrokeColor, strokeDashArray: currentStrokeDash };
  segments.push({ type: 'E', cx, cy, rx, ry, ...props });
  while (splitSegmentsAtAllIntersections()) { /* repeat until no more intersections */ }
  selectedIndices.clear();
  if (segments.length > 0) selectedIndices.add(segments.length - 1);
  dragState = null;
  render();
}

// --- Paint bucket tool ---
function paintBucketMouseDown(e) {
  try {
    const p = screenToCanvas(e);
    pushUndo();
    let splitCount = 0;
    while (splitSegmentsAtAllIntersections() && splitCount < 20) {
      splitCount++;
    }
    const contour = findFillContour(p.x, p.y);
    if (contour) {
      fills.push({ color: fillColor, segmentIndices: contour });
      render();
    } else {
      undo();
    }
  } catch (err) {
    if (undoStack.length > 0) undo();
    render();
  }
}

// --- Event routing ---
function onMouseDown(e) {
  if (tool === 'pen') penMouseDown(e);
  else if (tool === 'rect') rectMouseDown(e);
  else if (tool === 'oval') ovalMouseDown(e);
  else if (tool === 'paintbucket') paintBucketMouseDown(e);
  else selectMouseDown(e);
}

function onMouseMove(e) {
  if (tool === 'pen') penMouseMove(e);
  else if (tool === 'rect') rectMouseMove(e);
  else if (tool === 'oval') ovalMouseMove(e);
  else if (tool !== 'paintbucket') selectMouseMove(e);
}

function onMouseUp(e) {
  if (tool === 'pen') penMouseUp(e);
  else if (tool === 'rect') rectMouseUp(e);
  else if (tool === 'oval') ovalMouseUp(e);
  else selectMouseUp(e);
}

canvas.addEventListener('mousedown', onMouseDown);
canvas.addEventListener('mousemove', onMouseMove);
canvas.addEventListener('mouseup', onMouseUp);
canvas.addEventListener('mouseleave', onMouseUp);

function setTool(t) {
  tool = t;
  toolSelect.classList.toggle('active', t === 'select');
  toolPen.classList.toggle('active', t === 'pen');
  toolRect.classList.toggle('active', t === 'rect');
  toolOval.classList.toggle('active', t === 'oval');
  toolPaintBucket.classList.toggle('active', t === 'paintbucket');
  canvas.classList.toggle('tool-select', t === 'select');
  canvas.classList.toggle('tool-pen', t === 'pen');
  canvas.classList.toggle('tool-rect', t === 'rect');
  canvas.classList.toggle('tool-oval', t === 'oval');
  canvas.classList.toggle('tool-paintbucket', t === 'paintbucket');
  penPreview = null;
  dragState = null;
  render();
}

toolSelect.addEventListener('click', () => setTool('select'));
toolPen.addEventListener('click', () => setTool('pen'));
toolRect.addEventListener('click', () => setTool('rect'));
toolOval.addEventListener('click', () => setTool('oval'));
toolPaintBucket.addEventListener('click', () => setTool('paintbucket'));

document.getElementById('btn-export-svg').addEventListener('click', exportToSVG);

document.addEventListener('keydown', (e) => {
  if (e.target.tagName === 'INPUT' || e.target.tagName === 'TEXTAREA') return;
  if (e.key === 'v' || e.key === 'V') toolSelect.click();
  else if (e.key === 'p' || e.key === 'P') toolPen.click();
  else if (e.key === 'r' || e.key === 'R') toolRect.click();
  else if (e.key === 'o' || e.key === 'O') toolOval.click();
  else if (e.key === 'b' || e.key === 'B') toolPaintBucket.click();
  else if (e.key === 'Delete' || e.key === 'Backspace') {
    if (selectedIndices.size > 0) {
      pushUndo();
      const toRemove = new Set([...selectedIndices].sort((a, b) => b - a));
      toRemove.forEach(i => segments.splice(i, 1));
      fills = fills.filter(f => {
        if (!f.segmentIndices) return true;
        const refsDeleted = f.segmentIndices.some(idx => toRemove.has(idx));
        if (refsDeleted) return false;
        f.segmentIndices = f.segmentIndices.map(idx => {
          let newIdx = idx;
          for (const r of toRemove) if (r < idx) newIdx--;
          return newIdx;
        });
        return true;
      });
      selectedIndices.clear();
      render();
      e.preventDefault();
    } else if (selectedFillIndices.size > 0) {
      pushUndo();
      const toRemove = new Set([...selectedFillIndices].sort((a, b) => b - a));
      fills = fills.filter((_, i) => !toRemove.has(i));
      selectedFillIndices.clear();
      render();
      e.preventDefault();
    }
  } else if ((e.metaKey || e.ctrlKey) && e.key === 'd') {
    if (selectedIndices.size > 0) {
      pushUndo();
      const offset = 20;
      const sorted = [...selectedIndices].sort((a, b) => a - b);
      const oldToNew = new Map();
      for (const i of sorted) {
        const seg = segments[i];
        const copy = JSON.parse(JSON.stringify(seg));
        copy.x0 += offset; copy.y0 += offset;
        copy.x1 += offset; copy.y1 += offset;
        if (copy.type === 'Q') { copy.cx += offset; copy.cy += offset; }
        if (copy.type === 'C') { copy.c1x += offset; copy.c1y += offset; copy.c2x += offset; copy.c2y += offset; }
        const newIdx = segments.length;
        segments.push(copy);
        oldToNew.set(i, newIdx);
      }
      selectedIndices.clear();
      sorted.forEach(i => selectedIndices.add(oldToNew.get(i)));
      render();
      e.preventDefault();
    } else if (selectedFillIndices.size > 0) {
      pushUndo();
      const offset = 20;
      const count = selectedFillIndices.size;
      for (const fi of selectedFillIndices) {
        const f = fills[fi];
        if (f.segmentIndices) {
          const newIndices = [];
          for (const i of f.segmentIndices) {
            const seg = segments[i];
            if (!seg) continue;
            const copy = JSON.parse(JSON.stringify(seg));
            copy.x0 += offset; copy.y0 += offset;
            copy.x1 += offset; copy.y1 += offset;
            if (copy.type === 'Q') { copy.cx += offset; copy.cy += offset; }
            if (copy.type === 'C') { copy.c1x += offset; copy.c1y += offset; copy.c2x += offset; copy.c2y += offset; }
            segments.push(copy);
            newIndices.push(segments.length - 1);
          }
          fills.push({ color: f.color, segmentIndices: newIndices });
        } else if (f.polygon) {
          const poly = f.polygon.map(([x, y]) => [x + offset, y + offset]);
          fills.push({ color: f.color, polygon: poly });
        }
      }
      selectedFillIndices.clear();
      for (let i = fills.length - count; i < fills.length; i++) selectedFillIndices.add(i);
      render();
      e.preventDefault();
    }
  } else if ((e.metaKey || e.ctrlKey) && e.key === 'z') {
    if (e.shiftKey) {
      redo();
      e.preventDefault();
    } else {
      undo();
      e.preventDefault();
    }
  } else if (['ArrowUp', 'ArrowDown', 'ArrowLeft', 'ArrowRight'].includes(e.key) && selectedIndices.size > 0) {
    const step = e.shiftKey ? 20 : 1;
    let dx = 0, dy = 0;
    if (e.key === 'ArrowUp') dy = -step;
    else if (e.key === 'ArrowDown') dy = step;
    else if (e.key === 'ArrowLeft') dx = -step;
    else if (e.key === 'ArrowRight') dx = step;
    if (dx || dy) {
      pushUndo();
      for (const i of selectedIndices) {
        const seg = segments[i];
        seg.x0 += dx; seg.y0 += dy;
        seg.x1 += dx; seg.y1 += dy;
        if (seg.type === 'Q') { seg.cx += dx; seg.cy += dy; }
        if (seg.type === 'C') { seg.c1x += dx; seg.c1y += dy; seg.c2x += dx; seg.c2y += dy; }
      }
      render();
      e.preventDefault();
    }
  }
});

// --- Properties panel ---
const strokeWidthInput = document.getElementById('stroke-width');
const strokeWidthValue = document.getElementById('stroke-width-value');
const strokeStyleSelect = document.getElementById('stroke-style');
const colorSwatchBtn = document.getElementById('color-swatch');
const colorPopover = document.getElementById('color-popover');
const colorGrid = document.getElementById('color-grid');
const fillSwatchBtn = document.getElementById('fill-swatch');
const fillEditSwatchBtn = document.getElementById('fill-edit-swatch');
const fillEditPopover = document.getElementById('fill-edit-popover');
const fillEditColorGrid = document.getElementById('fill-edit-color-grid');

COLOR_SWATCHES.forEach(hex => {
  const btn = document.createElement('button');
  btn.style.background = hex;
  btn.addEventListener('click', (e) => {
    e.stopPropagation();
    currentStrokeColor = hex;
    colorSwatchBtn.style.background = hex;
    if (selectedIndices.size > 0) {
      pushUndo();
      for (const i of selectedIndices) segments[i].strokeColor = hex;
    }
    colorPopover.classList.remove('visible');
    render();
  });
  colorGrid.appendChild(btn);
});

const fillPopover = document.getElementById('fill-popover');
const fillColorGrid = document.getElementById('fill-color-grid');
COLOR_SWATCHES.forEach(hex => {
  const btn = document.createElement('button');
  btn.style.background = hex;
  btn.addEventListener('click', (e) => {
    e.stopPropagation();
    fillColor = hex;
    fillSwatchBtn.style.background = hex;
    fillPopover.classList.remove('visible');
  });
  fillColorGrid.appendChild(btn);
});

let strokeWidthDragStart = false;
function applyStrokeWidth(v, isFinal = false) {
  v = Math.max(0.5, Math.min(50, parseFloat(v) || 2));
  if (isFinal) strokeWidthDragStart = false;
  else if (selectedIndices.size > 0 && !strokeWidthDragStart) {
    strokeWidthDragStart = true;
    pushUndo();
  }
  currentStrokeWidth = v;
  strokeWidthInput.value = v;
  if (strokeWidthValue) strokeWidthValue.textContent = v;
  if (strokeWidthInput) {
    const pct = ((v - 0.5) / 49.5) * 100;
    strokeWidthInput.style.setProperty('--slider-pct', pct + '%');
  }
  if (selectedIndices.size > 0) {
    for (const i of selectedIndices) segments[i].strokeWidth = v;
  }
  render();
}

strokeWidthInput.addEventListener('input', () => applyStrokeWidth(strokeWidthInput.value, false));
strokeWidthInput.addEventListener('change', () => applyStrokeWidth(strokeWidthInput.value, true));

strokeStyleSelect.addEventListener('change', () => {
  const val = strokeStyleSelect.value;
  currentStrokeDash = val === 'dashed' ? [6, 4] : null;
  if (selectedIndices.size > 0) {
    pushUndo();
    for (const i of selectedIndices) segments[i].strokeDashArray = currentStrokeDash;
  }
  render();
});

if (fillEditColorGrid) {
  COLOR_SWATCHES.forEach(hex => {
    const btn = document.createElement('button');
    btn.style.background = hex;
    btn.addEventListener('click', (e) => {
      e.stopPropagation();
      if (selectedFillIndices.size > 0) {
        pushUndo();
        for (const i of selectedFillIndices) fills[i].color = hex;
        fillEditSwatchBtn.style.background = hex;
      }
      fillEditPopover.classList.remove('visible');
      render();
    });
    fillEditColorGrid.appendChild(btn);
  });
}

if (fillEditSwatchBtn) {
  fillEditSwatchBtn.addEventListener('click', (e) => {
    e.stopPropagation();
    fillEditPopover.classList.toggle('visible');
    colorPopover.classList.remove('visible');
    fillPopover.classList.remove('visible');
  });
}

colorSwatchBtn.addEventListener('click', (e) => {
  e.stopPropagation();
  colorPopover.classList.toggle('visible');
  fillPopover.classList.remove('visible');
  if (fillEditPopover) fillEditPopover.classList.remove('visible');
});

fillSwatchBtn.addEventListener('click', (e) => {
  e.stopPropagation();
  fillPopover.classList.toggle('visible');
  colorPopover.classList.remove('visible');
  if (fillEditPopover) fillEditPopover.classList.remove('visible');
});

document.addEventListener('click', (e) => {
  if (!e.target.closest('.properties-panel') && !e.target.closest('.color-popover')) {
    colorPopover.classList.remove('visible');
    fillPopover.classList.remove('visible');
    if (fillEditPopover) fillEditPopover.classList.remove('visible');
  }
});

function updatePropertiesPanel() {
  const aboutSection = document.getElementById('panel-about');
  const strokeSection = document.getElementById('stroke-section');
  const fillBucketSection = document.getElementById('fill-bucket-section');
  const fillEditSection = document.getElementById('fill-edit-section');
  const showStroke = tool === 'pen' || tool === 'rect' || tool === 'oval' || selectedIndices.size > 0;
  const showFillBucket = tool === 'paintbucket';
  const showFillEdit = selectedFillIndices.size > 0;
  const showAbout = !showStroke && !showFillBucket && !showFillEdit;
  if (aboutSection) aboutSection.style.display = showAbout ? 'block' : 'none';
  if (strokeSection) strokeSection.style.display = showStroke ? 'block' : 'none';
  if (fillBucketSection) fillBucketSection.style.display = showFillBucket ? 'block' : 'none';
  if (fillEditSection) fillEditSection.style.display = showFillEdit ? 'block' : 'none';
  if (showStroke) {
    const v = selectedIndices.size > 0
      ? (segments[[...selectedIndices][0]].strokeWidth ?? DEFAULT_STROKE_WIDTH)
      : currentStrokeWidth;
    strokeWidthInput.value = v;
    if (strokeWidthValue) strokeWidthValue.textContent = v;
    const pct = ((v - 0.5) / 49.5) * 100;
    strokeWidthInput.style.setProperty('--slider-pct', pct + '%');
    if (selectedIndices.size > 0) {
      const seg = segments[[...selectedIndices][0]];
      colorSwatchBtn.style.background = seg.strokeColor ?? DEFAULT_STROKE_COLOR;
      strokeStyleSelect.value = (seg.strokeDashArray && seg.strokeDashArray.length) ? 'dashed' : 'solid';
      currentStrokeWidth = seg.strokeWidth ?? DEFAULT_STROKE_WIDTH;
      currentStrokeColor = seg.strokeColor ?? DEFAULT_STROKE_COLOR;
      currentStrokeDash = seg.strokeDashArray ?? null;
    } else {
      colorSwatchBtn.style.background = currentStrokeColor;
      strokeStyleSelect.value = currentStrokeDash ? 'dashed' : 'solid';
    }
  }
  if (showFillBucket) fillSwatchBtn.style.background = fillColor;
  if (showFillEdit && fillEditSwatchBtn) {
    const firstIdx = [...selectedFillIndices][0];
    fillEditSwatchBtn.style.background = fills[firstIdx]?.color ?? fillColor;
  }
}

setTool('select');
colorSwatchBtn.style.background = DEFAULT_STROKE_COLOR;
fillSwatchBtn.style.background = fillColor;
if (strokeWidthValue) strokeWidthValue.textContent = currentStrokeWidth;
if (strokeWidthInput) {
  const v = parseFloat(strokeWidthInput.value) || 2;
  const pct = ((v - 0.5) / 49.5) * 100;
  strokeWidthInput.style.setProperty('--slider-pct', pct + '%');
}
render();
