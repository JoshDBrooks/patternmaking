"""
Patternmaking app.

A 2D drafting tool for clothes patternmaking. Place labeled points, connect
them with straight lines or cubic Bezier curves, group segments into named
parts (e.g. "Front panel") with seam-allowance offsets, mark internal
segments as dotted (darts and fold lines), and export the result as a tiled
A4 PDF at true 1:1 scale for printing, cutting, and assembly.

Units throughout the data model are centimeters (cm).
"""

from __future__ import annotations

import json
import math
import os
import string
import subprocess
import sys
import tkinter as tk
from dataclasses import dataclass, field, asdict
from tkinter import filedialog, messagebox, ttk
from typing import Optional


# ---------- geometry ----------

def cubic_bezier_point(p0, p1, p2, p3, t):
    u = 1.0 - t
    x = u * u * u * p0[0] + 3 * u * u * t * p1[0] + 3 * u * t * t * p2[0] + t * t * t * p3[0]
    y = u * u * u * p0[1] + 3 * u * u * t * p1[1] + 3 * u * t * t * p2[1] + t * t * t * p3[1]
    return (x, y)


def cubic_bezier_samples(p0, p1, p2, p3, n=64):
    return [cubic_bezier_point(p0, p1, p2, p3, i / n) for i in range(n + 1)]


def polyline_length(pts):
    total = 0.0
    for i in range(1, len(pts)):
        total += math.hypot(pts[i][0] - pts[i - 1][0], pts[i][1] - pts[i - 1][1])
    return total


def label_for_index(i):
    letters = string.ascii_uppercase
    if i < 26:
        return letters[i]
    return letters[i // 26 - 1] + letters[i % 26]


def chain_segments_into_loop(segments):
    """Try to order segments end-to-end into a single closed loop.
    Returns a list of (segment, reversed_bool) or None if it isn't a
    single closed chain. `reversed_bool` means traverse from .b to .a."""
    if not segments:
        return None
    remaining = list(segments)
    first = remaining.pop(0)
    chain = [(first, False)]
    start_pid = first.a
    current_pid = first.b
    while remaining:
        found_i = None
        for i, seg in enumerate(remaining):
            if seg.a == current_pid:
                found_i = (i, False)
                break
            if seg.b == current_pid:
                found_i = (i, True)
                break
        if found_i is None:
            return None
        i, rev = found_i
        seg = remaining.pop(i)
        chain.append((seg, rev))
        current_pid = seg.a if rev else seg.b
    if current_pid != start_pid:
        return None
    return chain


def polyline_of_chain(chain, points, samples_per_curve=48):
    pts = []
    for seg, rev in chain:
        pa = points[seg.a]; pb = points[seg.b]
        if seg.kind == 'line':
            segpts = [(pa.x, pa.y), (pb.x, pb.y)]
        else:
            segpts = cubic_bezier_samples((pa.x, pa.y), seg.c1, seg.c2, (pb.x, pb.y), n=samples_per_curve)
        if rev:
            segpts = list(reversed(segpts))
        if pts and abs(pts[-1][0] - segpts[0][0]) < 1e-9 and abs(pts[-1][1] - segpts[0][1]) < 1e-9:
            pts.extend(segpts[1:])
        else:
            pts.extend(segpts)
    return pts


def chain_segments_into_loop_with_ids(id_seg_pairs):
    """Like chain_segments_into_loop but each input is (segment_id, segment).
    Returns list of (segment_id, segment, reversed_bool) or None."""
    if not id_seg_pairs:
        return None
    remaining = list(id_seg_pairs)
    first_id, first_seg = remaining.pop(0)
    chain = [(first_id, first_seg, False)]
    start_pid = first_seg.a
    current_pid = first_seg.b
    while remaining:
        found = None
        for i, (sid, s) in enumerate(remaining):
            if s.a == current_pid:
                found = (i, False); break
            if s.b == current_pid:
                found = (i, True); break
        if found is None:
            return None
        i, rev = found
        sid, s = remaining.pop(i)
        chain.append((sid, s, rev))
        current_pid = s.a if rev else s.b
    if current_pid != start_pid:
        return None
    return chain


def polyline_of_chain_with_ids(chain, points, samples_per_curve=24):
    """Build a polyline plus a parallel list mapping each polyline edge
    (between pts[i] and pts[i+1]) to its source segment id."""
    pts = []
    edge_ids = []
    for sid, seg, rev in chain:
        pa = points[seg.a]; pb = points[seg.b]
        if seg.kind == 'line':
            segpts = [(pa.x, pa.y), (pb.x, pb.y)]
        else:
            segpts = cubic_bezier_samples((pa.x, pa.y), seg.c1, seg.c2,
                                          (pb.x, pb.y), n=samples_per_curve)
        if rev:
            segpts = list(reversed(segpts))
        if pts and abs(pts[-1][0] - segpts[0][0]) < 1e-9 \
                and abs(pts[-1][1] - segpts[0][1]) < 1e-9:
            new_pts = segpts[1:]
        else:
            new_pts = segpts
        pts.extend(new_pts)
        edge_ids.extend([sid] * len(new_pts) if pts and len(new_pts) > 0 else [])
    # The first segment contributes len(segpts) points but only
    # len(segpts)-1 edges, so trim one tag.
    if edge_ids:
        edge_ids.pop(0)
    return pts, edge_ids


def offset_closed_polyline_variable(points, distances):
    """Variable-distance outward offset of a closed polyline. Each polyline
    edge (between points[i] and points[i+1]) is offset by distances[i].
    At each vertex the new position is the intersection of the two adjacent
    offset edges (true variable-offset behaviour); when those edges are
    near-parallel, falls back to the bisector miter used by the uniform
    offset. Outward is determined by signed-area winding."""
    if len(points) < 3:
        return points
    if (points[0][0], points[0][1]) != (points[-1][0], points[-1][1]):
        points = list(points) + [points[0]]
    n = len(points) - 1
    if len(distances) < n:
        distances = list(distances) + [distances[-1] if distances else 0] * (n - len(distances))
    elif len(distances) > n:
        distances = distances[:n]
    if not any(d > 0 for d in distances):
        return points

    sign = 1.0 if polyline_signed_area(points) > 0 else -1.0
    out = []
    for i in range(n):
        prev = points[(i - 1) % n]
        curr = points[i]
        nxt = points[(i + 1) % n]
        e1x, e1y = curr[0] - prev[0], curr[1] - prev[1]
        e2x, e2y = nxt[0] - curr[0], nxt[1] - curr[1]
        l1 = math.hypot(e1x, e1y) or 1.0
        l2 = math.hypot(e2x, e2y) or 1.0
        e1x /= l1; e1y /= l1
        e2x /= l2; e2y /= l2
        n1x = sign * e1y; n1y = -sign * e1x
        n2x = sign * e2y; n2y = -sign * e2x

        d1 = distances[(i - 1) % n]
        d2 = distances[i]
        p1x = curr[0] + n1x * d1; p1y = curr[1] + n1y * d1
        p2x = curr[0] + n2x * d2; p2y = curr[1] + n2y * d2

        cross = e1x * e2y - e1y * e2x
        if abs(cross) < 1e-6:
            # near-parallel edges: bisector miter with averaged distance
            bx, by = n1x + n2x, n1y + n2y
            bl = math.hypot(bx, by)
            if bl < 1e-9:
                bx, by = n1x, n1y; bl = 1.0
            bx /= bl; by /= bl
            avg_d = 0.5 * (d1 + d2)
            cos_half = max(0.2, abs(bx * n1x + by * n1y))
            miter = avg_d / cos_half
            out.append((curr[0] + bx * miter, curr[1] + by * miter))
        else:
            dxp = p2x - p1x; dyp = p2y - p1y
            t = (dxp * e2y - dyp * e2x) / cross
            ox = p1x + t * e1x
            oy = p1y + t * e1y
            # Clamp absurd spikes at very acute corners
            spike = math.hypot(ox - curr[0], oy - curr[1])
            cap = max(d1, d2) * 5.0
            if spike > cap and cap > 0:
                bx, by = n1x + n2x, n1y + n2y
                bl = math.hypot(bx, by) or 1.0
                bx /= bl; by /= bl
                cos_half = max(0.2, abs(bx * n1x + by * n1y))
                out.append((curr[0] + bx * (max(d1, d2) / cos_half),
                            curr[1] + by * (max(d1, d2) / cos_half)))
            else:
                out.append((ox, oy))
    out.append(out[0])
    return out


def segment_point_and_tangent(seg, points, t):
    """Return (x, y, tx, ty) at parameter t in [0,1] along a segment.
    (tx, ty) is a unit tangent pointing from a toward b."""
    pa = points[seg.a]; pb = points[seg.b]
    if seg.kind == 'line':
        x = pa.x + (pb.x - pa.x) * t
        y = pa.y + (pb.y - pa.y) * t
        dx = pb.x - pa.x; dy = pb.y - pa.y
    else:
        p0 = (pa.x, pa.y); p1 = seg.c1; p2 = seg.c2; p3 = (pb.x, pb.y)
        x, y = cubic_bezier_point(p0, p1, p2, p3, t)
        # derivative of cubic bezier
        u = 1.0 - t
        dx = (3 * u * u * (p1[0] - p0[0]) + 6 * u * t * (p2[0] - p1[0])
              + 3 * t * t * (p3[0] - p2[0]))
        dy = (3 * u * u * (p1[1] - p0[1]) + 6 * u * t * (p2[1] - p1[1])
              + 3 * t * t * (p3[1] - p2[1]))
    d = math.hypot(dx, dy) or 1.0
    return (x, y, dx / d, dy / d)


def segment_to_polyline(seg, points, samples_per_curve=80):
    pa = points[seg.a]; pb = points[seg.b]
    if seg.kind == 'line':
        return [(pa.x, pa.y), (pb.x, pb.y)]
    return cubic_bezier_samples((pa.x, pa.y), seg.c1, seg.c2, (pb.x, pb.y),
                                n=samples_per_curve)


def polyline_crossings_vertical(poly, x_target):
    out = []
    for i in range(1, len(poly)):
        x0, y0 = poly[i - 1]; x1, y1 = poly[i]
        if (x0 - x_target) * (x1 - x_target) <= 0 and x0 != x1:
            t = (x_target - x0) / (x1 - x0)
            out.append((x_target, y0 + t * (y1 - y0)))
    return out


def polyline_crossings_horizontal(poly, y_target):
    out = []
    for i in range(1, len(poly)):
        x0, y0 = poly[i - 1]; x1, y1 = poly[i]
        if (y0 - y_target) * (y1 - y_target) <= 0 and y0 != y1:
            t = (y_target - y0) / (y1 - y0)
            out.append((x0 + t * (x1 - x0), y_target))
    return out


def point_in_polygon(x, y, poly):
    """Ray-casting test. `poly` is a polyline (closed if first == last,
    otherwise treated as implicitly closed). Returns True if (x, y) is
    strictly inside the polygon."""
    n = len(poly)
    if n < 3:
        return False
    if poly[0] == poly[-1]:
        n -= 1
    inside = False
    j = n - 1
    for i in range(n):
        xi, yi = poly[i]
        xj, yj = poly[j]
        if (yi > y) != (yj > y):
            denom = (yj - yi) or 1e-30
            x_cross = (xj - xi) * (y - yi) / denom + xi
            if x < x_cross:
                inside = not inside
        j = i
    return inside


def polyline_signed_area(points):
    """Shoelace signed area of a closed polyline in math (y-up) coords.
    Positive = CCW. Assumes first==last point or treats it as closed."""
    n = len(points)
    if n < 3:
        return 0.0
    if (points[0][0], points[0][1]) == (points[-1][0], points[-1][1]):
        n -= 1
    s = 0.0
    for i in range(n):
        x0, y0 = points[i]
        x1, y1 = points[(i + 1) % n]
        s += x0 * y1 - x1 * y0
    return 0.5 * s


def offset_closed_polyline(points, distance):
    """Offset a closed polyline outward by `distance` (cm). Outward
    direction is derived from the polygon's signed area (winding), which
    is geometrically robust for any closed shape — convex, concave, or
    L-shaped — rather than relying on a centroid heuristic."""
    if len(points) < 3 or distance <= 0:
        return points
    if (points[0][0], points[0][1]) != (points[-1][0], points[-1][1]):
        points = list(points) + [points[0]]
    n = len(points) - 1

    sign = 1.0 if polyline_signed_area(points) > 0 else -1.0
    # For CCW (sign=+1) in y-up coords, outward = right-of-travel: (ey, -ex)
    # For CW  (sign=-1), outward flips to (-ey, ex).
    out = []
    for i in range(n):
        prev = points[(i - 1) % n]
        curr = points[i]
        nxt = points[(i + 1) % n]
        e1x, e1y = curr[0] - prev[0], curr[1] - prev[1]
        e2x, e2y = nxt[0] - curr[0], nxt[1] - curr[1]
        l1 = math.hypot(e1x, e1y) or 1.0
        l2 = math.hypot(e2x, e2y) or 1.0
        e1x /= l1; e1y /= l1
        e2x /= l2; e2y /= l2
        n1x = sign * e1y; n1y = -sign * e1x
        n2x = sign * e2y; n2y = -sign * e2x
        bx, by = n1x + n2x, n1y + n2y
        bl = math.hypot(bx, by)
        if bl < 1e-9:
            bx, by = n1x, n1y
            bl = 1.0
        bx /= bl; by /= bl
        cos_half = max(0.2, abs(bx * n1x + by * n1y))
        miter = distance / cos_half
        out.append((curr[0] + bx * miter, curr[1] + by * miter))
    out.append(out[0])
    return out


# ---------- data model ----------

@dataclass
class Point:
    id: int
    label: str
    x: float
    y: float


@dataclass
class Segment:
    kind: str            # 'line' or 'curve'
    a: int               # point id
    b: int               # point id
    c1: Optional[tuple] = None
    c2: Optional[tuple] = None
    style: str = 'solid'  # 'solid' (cutting line) or 'dotted' (dart, fold line, marking)
    seam_allowance: Optional[float] = None  # cm; None = inherit from containing part
    length_locked: bool = False  # when True, dragging an endpoint moves the other end too
    seam_label: Optional[str] = None  # named seam; matching labels join across parts


@dataclass
class Dart:
    """Metadata linking a dart's four points together so the dart can be
    moved as one rigid shape. The dotted V segments themselves live in
    Pattern.segments like any other segment — this record just remembers
    which boundary point is the anchor and which three points belong to
    the dart's mouth and apex."""
    anchor_id: int
    mouth_a_id: int
    apex_id: int
    mouth_b_id: int

    def all_point_ids(self):
        return (self.anchor_id, self.mouth_a_id, self.apex_id, self.mouth_b_id)

    def dart_only_ids(self):
        """The three points that belong to the dart shape itself, not the
        boundary anchor."""
        return (self.mouth_a_id, self.apex_id, self.mouth_b_id)


@dataclass
class Part:
    id: int
    name: str
    segment_ids: list = field(default_factory=list)   # indices into Pattern.segments
    seam_allowance: float = 0.0                       # cm; 0 = none drawn
    label_pos: Optional[tuple] = None                 # (x, y) cm; None = auto centroid
    grain_line: Optional[tuple] = None                # (x1, y1, x2, y2) in cm; None = no grain line


@dataclass
class Notch:
    """A perpendicular alignment tick on a segment at parameter t in [0, 1]
    from endpoint a to b. Rendered as a small line crossing the segment."""
    segment_id: int
    t: float


@dataclass
class Pattern:
    points: dict = field(default_factory=dict)
    segments: list = field(default_factory=list)
    parts: list = field(default_factory=list)
    darts: list = field(default_factory=list)
    notches: list = field(default_factory=list)
    next_id: int = 1
    next_label: int = 0
    next_part_id: int = 1

    # points
    def add_point(self, x, y, label=None):
        p = Point(id=self.next_id, label=label or label_for_index(self.next_label), x=x, y=y)
        self.points[p.id] = p
        self.next_id += 1
        if label is None:
            self.next_label += 1
        return p

    def remove_point(self, pid):
        if pid not in self.points:
            return
        del self.points[pid]
        # remove segments touching this point, and patch up parts
        keep = []
        index_map = {}  # old index -> new index
        for old_i, s in enumerate(self.segments):
            if s.a == pid or s.b == pid:
                continue
            index_map[old_i] = len(keep)
            keep.append(s)
        self.segments = keep
        for part in self.parts:
            part.segment_ids = [index_map[i] for i in part.segment_ids if i in index_map]
        # drop parts left empty
        self.parts = [p for p in self.parts if p.segment_ids]
        # remap notches; drop those on removed segments
        self.notches = [Notch(segment_id=index_map[n.segment_id], t=n.t)
                        for n in self.notches if n.segment_id in index_map]
        # drop any darts that referenced the removed point — the V no longer
        # makes sense without all four points
        self.darts = [d for d in self.darts if pid not in d.all_point_ids()]

    # segments
    def add_line(self, a, b):
        self.segments.append(Segment(kind='line', a=a, b=b))
        return len(self.segments) - 1

    def add_curve(self, a, b):
        pa, pb = self.points[a], self.points[b]
        c1 = (pa.x + (pb.x - pa.x) / 3.0, pa.y + (pb.y - pa.y) / 3.0)
        c2 = (pa.x + 2 * (pb.x - pa.x) / 3.0, pa.y + 2 * (pb.y - pa.y) / 3.0)
        self.segments.append(Segment(kind='curve', a=a, b=b, c1=c1, c2=c2))
        return len(self.segments) - 1

    def remove_segments(self, indices):
        idxs = set(indices)
        keep = []
        index_map = {}
        for old_i, s in enumerate(self.segments):
            if old_i in idxs:
                continue
            index_map[old_i] = len(keep)
            keep.append(s)
        self.segments = keep
        for part in self.parts:
            part.segment_ids = [index_map[i] for i in part.segment_ids if i in index_map]
        self.parts = [p for p in self.parts if p.segment_ids]
        self.notches = [Notch(segment_id=index_map[n.segment_id], t=n.t)
                        for n in self.notches if n.segment_id in index_map]

    # parts
    def add_part(self, name, segment_ids, seam_allowance=0.0):
        p = Part(id=self.next_part_id, name=name, segment_ids=list(segment_ids),
                 seam_allowance=seam_allowance)
        self.parts.append(p)
        self.next_part_id += 1
        return p

    def remove_part(self, part_id):
        self.parts = [p for p in self.parts if p.id != part_id]

    # darts
    def add_dart(self, anchor_id, mouth_a_id, apex_id, mouth_b_id):
        d = Dart(anchor_id=anchor_id, mouth_a_id=mouth_a_id,
                 apex_id=apex_id, mouth_b_id=mouth_b_id)
        self.darts.append(d)
        return d

    def find_dart_by_anchor(self, point_id):
        return next((d for d in self.darts if d.anchor_id == point_id), None)

    # serialization
    def to_json(self):
        return {
            'points': [asdict(p) for p in self.points.values()],
            'segments': [asdict(s) for s in self.segments],
            'parts': [asdict(p) for p in self.parts],
            'darts': [asdict(d) for d in self.darts],
            'notches': [asdict(n) for n in self.notches],
            'next_id': self.next_id,
            'next_label': self.next_label,
            'next_part_id': self.next_part_id,
        }

    @classmethod
    def from_json(cls, data):
        pat = cls()
        for pd in data.get('points', []):
            p = Point(**pd)
            pat.points[p.id] = p
        for sd in data.get('segments', []):
            sa_override = sd.get('seam_allowance')
            s = Segment(
                kind=sd['kind'],
                a=sd['a'],
                b=sd['b'],
                c1=tuple(sd['c1']) if sd.get('c1') else None,
                c2=tuple(sd['c2']) if sd.get('c2') else None,
                style=sd.get('style', 'solid'),
                seam_allowance=float(sa_override) if sa_override is not None else None,
                length_locked=bool(sd.get('length_locked', False)),
                seam_label=sd.get('seam_label'),
            )
            pat.segments.append(s)
        for pd in data.get('parts', []):
            label_pos = pd.get('label_pos')
            grain_line = pd.get('grain_line')
            pat.parts.append(Part(
                id=pd['id'], name=pd['name'],
                segment_ids=list(pd.get('segment_ids', [])),
                seam_allowance=float(pd.get('seam_allowance', 0.0)),
                label_pos=tuple(label_pos) if label_pos else None,
                grain_line=tuple(grain_line) if grain_line else None,
            ))
        for dd in data.get('darts', []):
            pat.darts.append(Dart(
                anchor_id=dd['anchor_id'],
                mouth_a_id=dd['mouth_a_id'],
                apex_id=dd['apex_id'],
                mouth_b_id=dd['mouth_b_id'],
            ))
        for nd in data.get('notches', []):
            pat.notches.append(Notch(
                segment_id=nd['segment_id'],
                t=float(nd['t']),
            ))
        pat.next_id = data.get('next_id', max([p.id for p in pat.points.values()], default=0) + 1)
        pat.next_label = data.get('next_label', len(pat.points))
        pat.next_part_id = data.get('next_part_id',
                                    max([p.id for p in pat.parts], default=0) + 1)
        return pat


# ---------- app ----------

class App:
    PPC_DEFAULT = 12.0
    HIT_RADIUS_PX = 8
    POINT_RADIUS_PX = 4
    DRAG_THRESHOLD_PX = 3

    def __init__(self, root):
        self.root = root
        self.root.title("Patternmaking")
        self.root.geometry("1300x820")

        self.pattern = Pattern()
        self.file_path: Optional[str] = None
        self.dirty = False

        self.mode = tk.StringVar(value='select')
        self.zoom = 1.0
        self.pan_x = 0.0
        self.pan_y = 0.0
        self.show_grid = tk.BooleanVar(value=True)
        self.show_lengths = tk.BooleanVar(value=True)
        self.show_part_labels = tk.BooleanVar(value=True)
        self.show_angles = tk.BooleanVar(value=True)

        # Selection: sets of ids. selected_part is a single id or None.
        self.selected_points: set = set()
        self.selected_segments: set = set()
        self.selected_part: Optional[int] = None

        # Pending first-click for line/curve creation
        self.pending_a: Optional[int] = None

        # Undo / redo stacks of pattern snapshots (JSON dicts).
        self._undo_stack: list = []
        self._redo_stack: list = []
        self._undo_limit = 100

        # Map of part_id -> (x1, y1, x2, y2) screen bbox, populated each redraw,
        # used to hit-test clicks on part labels.
        self._part_label_bboxes: dict = {}
        # seg_idx -> (x1, y1, x2, y2) bbox of the line-length label (line segments only).
        self._length_label_bboxes: dict = {}
        # seg_idx -> (x1, y1, x2, y2) bbox of the padlock icon next to a line's length label.
        self._padlock_bboxes: dict = {}
        # point_id -> (x1, y1, x2, y2, seg_idx_fixed, seg_idx_rotate) for corner angles.
        self._angle_label_bboxes: dict = {}
        # In-progress inline edit (length/angle label clicked on canvas)
        self._inline_edit: Optional[dict] = None
        # Current snap state while placing a new point (Add Point / Line / Curve).
        # None = no snap active. Updated on mouse move; cleared on mode change.
        self._snap_state: Optional[dict] = None

        # Active drag state
        # ('point_group', start_world_xy, {pid: (x0, y0)}) for moving points
        # ('handle', seg_idx, which, ...)
        # ('rubber', start_screen_xy, additive_bool)
        self.drag = None
        self.press_pos: Optional[tuple] = None
        self._pan_anchor = None

        self._build_ui()
        self._bind_events()
        self.root.after(50, self._center_origin)
        self.redraw()

    # ---- UI scaffolding ----

    def _build_ui(self):
        menubar = tk.Menu(self.root)
        filemenu = tk.Menu(menubar, tearoff=0)
        filemenu.add_command(label="New", command=self.new_file, accelerator="Ctrl+N")
        filemenu.add_command(label="Open...", command=self.open_file, accelerator="Ctrl+O")
        filemenu.add_command(label="Save", command=self.save_file, accelerator="Ctrl+S")
        filemenu.add_command(label="Save As...", command=self.save_file_as)
        filemenu.add_separator()
        filemenu.add_command(label="Export Tiled A4 PDF...", command=self.export_pdf,
                             accelerator="Ctrl+E")
        filemenu.add_separator()
        filemenu.add_command(label="Quit", command=self.root.quit)
        menubar.add_cascade(label="File", menu=filemenu)

        editmenu = tk.Menu(menubar, tearoff=0)
        editmenu.add_command(label="Undo", command=self.undo, accelerator="Ctrl+Z")
        editmenu.add_command(label="Redo", command=self.redo, accelerator="Ctrl+Y")
        editmenu.add_separator()
        editmenu.add_command(label="Delete selection", command=self.delete_selected,
                             accelerator="Del")
        editmenu.add_command(label="Select all points", command=self._select_all_points,
                             accelerator="Ctrl+A")
        menubar.add_cascade(label="Edit", menu=editmenu)

        viewmenu = tk.Menu(menubar, tearoff=0)
        viewmenu.add_command(label="Zoom In",
                             command=lambda: self.zoom_at(self._canvas_center(), 1.25))
        viewmenu.add_command(label="Zoom Out",
                             command=lambda: self.zoom_at(self._canvas_center(), 0.8))
        viewmenu.add_command(label="Fit to Pattern", command=self.zoom_fit)
        viewmenu.add_command(label="Reset View (1:1)", command=self.reset_view)
        viewmenu.add_separator()
        viewmenu.add_checkbutton(label="Show Grid", variable=self.show_grid, command=self.redraw)
        viewmenu.add_checkbutton(label="Show Lengths", variable=self.show_lengths,
                                 command=self.redraw)
        viewmenu.add_checkbutton(label="Show Part Labels", variable=self.show_part_labels,
                                 command=self.redraw)
        viewmenu.add_checkbutton(label="Show Corner Angles", variable=self.show_angles,
                                 command=self.redraw)
        menubar.add_cascade(label="View", menu=viewmenu)
        self.root.config(menu=menubar)

        main = ttk.PanedWindow(self.root, orient=tk.HORIZONTAL)
        main.pack(fill=tk.BOTH, expand=True)

        # Left toolbar
        left = ttk.Frame(main, padding=4)
        main.add(left, weight=0)

        ttk.Label(left, text="Mode").pack(anchor='w')
        for mode_id, label, key in [
            ('select', 'Select / Move', 'S'),
            ('point', 'Add Point', 'P'),
            ('line', 'Connect Line', 'L'),
            ('curve', 'Connect Curve', 'C'),
        ]:
            ttk.Radiobutton(left, text=f"{label}  ({key})",
                            value=mode_id, variable=self.mode,
                            command=self._mode_changed).pack(anchor='w', fill='x')

        ttk.Separator(left, orient='horizontal').pack(fill='x', pady=6)
        ttk.Button(left, text="Draw rectangle...  (R)",
                   command=self.draw_rectangle_dialog).pack(fill='x')
        ttk.Button(left, text="Construct line from point...",
                   command=self.construct_line_dialog).pack(fill='x', pady=(2, 0))
        ttk.Button(left, text="Create part from selection...",
                   command=self.create_part_dialog).pack(fill='x', pady=(4, 0))
        ttk.Button(left, text="Add dart at selected point...  (D)",
                   command=self.add_dart_dialog).pack(fill='x', pady=(4, 0))
        ttk.Button(left, text="Mark selected segments dotted",
                   command=lambda: self._set_selected_segment_style('dotted')).pack(fill='x', pady=(4, 0))
        ttk.Button(left, text="Mark selected segments solid",
                   command=lambda: self._set_selected_segment_style('solid')).pack(fill='x', pady=(2, 0))
        ttk.Button(left, text="Delete selection",
                   command=self.delete_selected).pack(fill='x', pady=(8, 0))

        ttk.Separator(left, orient='horizontal').pack(fill='x', pady=6)
        ttk.Label(left, text="View").pack(anchor='w')
        ttk.Button(left, text="Fit", command=self.zoom_fit).pack(fill='x')
        ttk.Button(left, text="Reset 1:1", command=self.reset_view).pack(fill='x')

        ttk.Label(left, text="\nShift-click to add to selection.\n"
                  "Drag empty space to rubber-band select points.\n"
                  "Two-finger drag (or mouse wheel) = pan.\n"
                  "Shift + wheel = horizontal pan.\n"
                  "Ctrl + wheel = zoom. Middle-drag also pans.",
                  foreground='#888', justify='left',
                  wraplength=160).pack(anchor='w', pady=(8, 0))

        # Center canvas
        center = ttk.Frame(main)
        main.add(center, weight=1)
        self.canvas = tk.Canvas(center, bg='white', highlightthickness=0)
        self.canvas.pack(fill=tk.BOTH, expand=True)

        # Right panel
        right = ttk.Frame(main, padding=6, width=280)
        main.add(right, weight=0)

        self.props_frame = ttk.LabelFrame(right, text="Properties", padding=6)
        self.props_frame.pack(fill='x')
        self._props_placeholder()

        notebook = ttk.Notebook(right)
        notebook.pack(fill='both', expand=True, pady=(8, 0))

        pf = ttk.Frame(notebook)
        notebook.add(pf, text='Points')
        self.points_list = tk.Listbox(pf, exportselection=False)
        self.points_list.pack(fill='both', expand=True)
        self.points_list.bind('<<ListboxSelect>>', self._on_points_list_select)

        partf = ttk.Frame(notebook)
        notebook.add(partf, text='Parts')
        self.parts_list = tk.Listbox(partf, exportselection=False)
        self.parts_list.pack(fill='both', expand=True)
        self.parts_list.bind('<<ListboxSelect>>', self._on_parts_list_select)

        self.status_var = tk.StringVar()
        ttk.Label(self.root, textvariable=self.status_var, anchor='w',
                  relief='sunken', padding=(4, 2)).pack(side='bottom', fill='x')
        self._set_status("Ready.")

    def _bind_events(self):
        c = self.canvas
        c.bind('<Configure>', lambda e: self.redraw())
        c.bind('<Motion>', self.on_mouse_move)
        c.bind('<ButtonPress-1>', self.on_left_press)
        c.bind('<Shift-ButtonPress-1>', lambda e: self.on_left_press(e, shift=True))
        c.bind('<B1-Motion>', self.on_left_drag)
        c.bind('<Shift-B1-Motion>', self.on_left_drag)
        c.bind('<ButtonRelease-1>', self.on_left_release)
        c.bind('<Shift-ButtonRelease-1>', self.on_left_release)
        c.bind('<ButtonPress-3>', self.on_right_press)
        c.bind('<ButtonPress-2>', self.on_middle_press)
        c.bind('<B2-Motion>', self.on_middle_drag)
        # Two-finger trackpad drag → MouseWheel events on Windows.
        # Plain wheel pans; Ctrl+wheel zooms (standard modern-app convention).
        c.bind('<MouseWheel>', self.on_wheel_pan_v)
        c.bind('<Shift-MouseWheel>', self.on_wheel_pan_h)
        c.bind('<Control-MouseWheel>', self.on_wheel_zoom)

        self.root.bind('<Control-n>', lambda e: self.new_file())
        self.root.bind('<Control-o>', lambda e: self.open_file())
        self.root.bind('<Control-s>', lambda e: self.save_file())
        self.root.bind('<Control-e>', lambda e: self.export_pdf())
        self.root.bind('<Delete>', lambda e: self.delete_selected())
        self.root.bind('<Escape>', lambda e: self._cancel_pending())
        self.root.bind('<Control-a>', lambda e: self._select_all_points())
        self.root.bind('<Control-z>', self.undo)
        self.root.bind('<Control-y>', self.redo)
        self.root.bind('<Control-Z>', self.redo)  # Ctrl+Shift+Z

        # Mode shortcuts (ignored while a text entry has focus)
        for key, mode_id in [('s', 'select'), ('p', 'point'),
                             ('l', 'line'), ('c', 'curve')]:
            self.root.bind(f'<KeyPress-{key}>',
                           lambda e, m=mode_id: self._key_set_mode(m))
            self.root.bind(f'<KeyPress-{key.upper()}>',
                           lambda e, m=mode_id: self._key_set_mode(m))
        self.root.bind('<KeyPress-d>', lambda e: self._key_add_dart())
        self.root.bind('<KeyPress-D>', lambda e: self._key_add_dart())
        self.root.bind('<KeyPress-r>', lambda e: self._key_draw_rectangle())
        self.root.bind('<KeyPress-R>', lambda e: self._key_draw_rectangle())

    # ---- coordinate transforms ----

    def ppc(self):
        return self.PPC_DEFAULT * self.zoom

    def world_to_screen(self, x, y):
        return (x * self.ppc() + self.pan_x, self.pan_y - y * self.ppc())

    def screen_to_world(self, sx, sy):
        return ((sx - self.pan_x) / self.ppc(), (self.pan_y - sy) / self.ppc())

    def _canvas_center(self):
        return (self.canvas.winfo_width() / 2, self.canvas.winfo_height() / 2)

    def _center_origin(self):
        self.pan_x = 60
        self.pan_y = self.canvas.winfo_height() - 60
        self.redraw()

    # ---- selection helpers ----

    def _clear_selection(self):
        self.selected_points.clear()
        self.selected_segments.clear()
        self.selected_part = None

    def _select_only_point(self, pid):
        self._clear_selection()
        self.selected_points.add(pid)

    def _select_only_segment(self, idx):
        self._clear_selection()
        self.selected_segments.add(idx)

    def _select_part(self, part_id):
        self._clear_selection()
        self.selected_part = part_id
        # also highlight its segments
        part = next((p for p in self.pattern.parts if p.id == part_id), None)
        if part:
            self.selected_segments.update(part.segment_ids)

    def _toggle_point(self, pid):
        if pid in self.selected_points:
            self.selected_points.remove(pid)
        else:
            self.selected_points.add(pid)
        self.selected_part = None

    def _toggle_segment(self, idx):
        if idx in self.selected_segments:
            self.selected_segments.remove(idx)
        else:
            self.selected_segments.add(idx)
        self.selected_part = None

    def _select_all_points(self):
        self._clear_selection()
        self.selected_points = set(self.pattern.points.keys())
        self.redraw()

    def _selection_count(self):
        return len(self.selected_points) + len(self.selected_segments)


    # ---- undo / redo ----

    def _push_undo(self):
        """Snapshot the pattern before a mutation. Call once per discrete
        user action (one click, one drag start, one property commit)."""
        snap = self.pattern.to_json()
        if self._undo_stack and self._undo_stack[-1] == snap:
            return
        self._undo_stack.append(snap)
        if len(self._undo_stack) > self._undo_limit:
            self._undo_stack.pop(0)
        self._redo_stack.clear()

    def _clear_undo(self):
        self._undo_stack.clear()
        self._redo_stack.clear()

    def undo(self, event=None):
        # Don't steal Ctrl+Z from text entries (they have their own undo)
        focused = self.root.focus_get()
        if isinstance(focused, (tk.Entry, tk.Text)):
            return
        if not self._undo_stack:
            self._set_status("Nothing to undo.")
            return
        self._redo_stack.append(self.pattern.to_json())
        snap = self._undo_stack.pop()
        self.pattern = Pattern.from_json(snap)
        self._clear_selection()
        self.pending_a = None
        self.drag = None
        self.dirty = True
        self.redraw()
        self._set_status("Undo.")

    def redo(self, event=None):
        focused = self.root.focus_get()
        if isinstance(focused, (tk.Entry, tk.Text)):
            return
        if not self._redo_stack:
            self._set_status("Nothing to redo.")
            return
        self._undo_stack.append(self.pattern.to_json())
        snap = self._redo_stack.pop()
        self.pattern = Pattern.from_json(snap)
        self._clear_selection()
        self.pending_a = None
        self.drag = None
        self.dirty = True
        self.redraw()
        self._set_status("Redo.")

    # ---- drawing ----

    def redraw(self):
        c = self.canvas
        c.delete('all')
        self._part_label_bboxes.clear()
        self._length_label_bboxes.clear()
        self._padlock_bboxes.clear()
        self._angle_label_bboxes.clear()
        w = c.winfo_width(); h = c.winfo_height()

        if self.show_grid.get():
            self._draw_grid(w, h)

        # Seam allowance offsets first (under everything)
        for part in self.pattern.parts:
            if part.seam_allowance > 0:
                self._draw_seam_allowance(part)

        # Grain lines (under segments, over SA)
        for part in self.pattern.parts:
            if part.grain_line is not None:
                self._draw_grain_line(part)

        # Segments
        for idx, seg in enumerate(self.pattern.segments):
            self._draw_segment(idx, seg)

        # Notches on top of segments
        for notch in self.pattern.notches:
            self._draw_notch(notch)

        # Seam labels along segments
        self._draw_seam_labels()

        # Corner angle annotations (between solid segments only)
        if self.show_angles.get():
            self._draw_corner_angles()

        # Points
        for p in self.pattern.points.values():
            self._draw_point(p)

        # Pending first-click marker
        if self.pending_a is not None and self.pending_a in self.pattern.points:
            pa = self.pattern.points[self.pending_a]
            sx, sy = self.world_to_screen(pa.x, pa.y)
            c.create_oval(sx - 9, sy - 9, sx + 9, sy + 9, outline='#0a84ff', width=2)

        # Part labels on top
        if self.show_part_labels.get():
            for part in self.pattern.parts:
                self._draw_part_label(part)

        # Rubber-band overlay (drawn last so it's visible)
        if self.drag and self.drag[0] == 'rubber':
            self._draw_rubber_band()

        # Snap overlay (active in point/line/curve modes)
        if self._snap_state:
            self._draw_snap_overlay()

        self._refresh_points_list()
        self._refresh_parts_list()
        self._refresh_properties()

    def _draw_grid(self, w, h):
        c = self.canvas
        ppc = self.ppc()
        x0 = (0 - self.pan_x) / ppc
        x1 = (w - self.pan_x) / ppc
        y0 = (self.pan_y - h) / ppc
        y1 = (self.pan_y - 0) / ppc

        minor_step, major_step = 1.0, 5.0
        if ppc < 4:
            minor_step, major_step = 5.0, 10.0
        if ppc < 1.5:
            minor_step, major_step = 10.0, 50.0

        def xrange(step):
            x = math.floor(x0 / step) * step
            end = math.ceil(x1 / step) * step
            while x <= end + 1e-9:
                yield x; x += step

        def yrange(step):
            y = math.floor(y0 / step) * step
            end = math.ceil(y1 / step) * step
            while y <= end + 1e-9:
                yield y; y += step

        for x in xrange(minor_step):
            sx, _ = self.world_to_screen(x, 0)
            c.create_line(sx, 0, sx, h, fill='#eef1f4')
        for y in yrange(minor_step):
            _, sy = self.world_to_screen(0, y)
            c.create_line(0, sy, w, sy, fill='#eef1f4')
        for x in xrange(major_step):
            sx, _ = self.world_to_screen(x, 0)
            c.create_line(sx, 0, sx, h, fill='#dde3ea')
        for y in yrange(major_step):
            _, sy = self.world_to_screen(0, y)
            c.create_line(0, sy, w, sy, fill='#dde3ea')

        sx0, sy0 = self.world_to_screen(0, 0)
        c.create_line(0, sy0, w, sy0, fill='#b8c1cc')
        c.create_line(sx0, 0, sx0, h, fill='#b8c1cc')
        c.create_text(sx0 + 4, sy0 + 4, text='0', anchor='nw',
                      fill='#7a8693', font=('Segoe UI', 8))

    def _draw_point(self, p: Point):
        c = self.canvas
        sx, sy = self.world_to_screen(p.x, p.y)
        is_sel = p.id in self.selected_points
        r = self.POINT_RADIUS_PX + (2 if is_sel else 0)
        fill = '#0a84ff' if is_sel else '#222'
        c.create_oval(sx - r, sy - r, sx + r, sy + r, fill=fill, outline='')
        c.create_text(sx + 8, sy - 8, text=p.label, anchor='sw',
                      fill='#0a84ff' if is_sel else '#333',
                      font=('Segoe UI', 10, 'bold'))

    def _draw_segment(self, idx, seg: Segment):
        c = self.canvas
        is_sel = idx in self.selected_segments
        color = '#0a84ff' if is_sel else '#222'
        width = 2 if is_sel else 1.5
        dash = (4, 3) if seg.style == 'dotted' else None
        pa = self.pattern.points.get(seg.a)
        pb = self.pattern.points.get(seg.b)
        if not pa or not pb:
            return

        if seg.kind == 'line':
            sxa, sya = self.world_to_screen(pa.x, pa.y)
            sxb, syb = self.world_to_screen(pb.x, pb.y)
            kwargs = {'fill': color, 'width': width}
            if dash:
                kwargs['dash'] = dash
            c.create_line(sxa, sya, sxb, syb, **kwargs)
            if self.show_lengths.get():
                length = math.hypot(pb.x - pa.x, pb.y - pa.y)
                mx, my = (sxa + sxb) / 2, (sya + syb) / 2
                bbox = self._draw_measurement_label(mx, my, sxb - sxa, syb - sya,
                                                    f"{length:.2f} cm")
                self._length_label_bboxes[idx] = bbox
                # Padlock for length-lock to the right of the label
                lock_cx = bbox[2] + 10
                lock_cy = (bbox[1] + bbox[3]) / 2
                self._padlock_bboxes[idx] = self._draw_padlock(
                    lock_cx, lock_cy, seg.length_locked)
        else:
            p0 = (pa.x, pa.y); p3 = (pb.x, pb.y)
            pts = cubic_bezier_samples(p0, seg.c1, seg.c2, p3, n=48)
            flat = []
            for x, y in pts:
                sx, sy = self.world_to_screen(x, y)
                flat += [sx, sy]
            kwargs = {'fill': color, 'width': width}
            if dash:
                kwargs['dash'] = dash
            c.create_line(*flat, **kwargs)

            if is_sel:
                for cp in (seg.c1, seg.c2):
                    sx, sy = self.world_to_screen(*cp)
                    c.create_rectangle(sx - 4, sy - 4, sx + 4, sy + 4,
                                       outline='#0a84ff', fill='white')
                sxa, sya = self.world_to_screen(*p0)
                sxb, syb = self.world_to_screen(*p3)
                sxc1, syc1 = self.world_to_screen(*seg.c1)
                sxc2, syc2 = self.world_to_screen(*seg.c2)
                c.create_line(sxa, sya, sxc1, syc1, fill='#b3d4ff', dash=(3, 3))
                c.create_line(sxb, syb, sxc2, syc2, fill='#b3d4ff', dash=(3, 3))

            if self.show_lengths.get():
                arc = polyline_length(pts)
                mid_i = len(pts) // 2
                mid = pts[mid_i]
                # tangent direction at mid (for perpendicular offset)
                prev = pts[max(0, mid_i - 1)]
                nxt = pts[min(len(pts) - 1, mid_i + 1)]
                mx, my = self.world_to_screen(*mid)
                psx, psy = self.world_to_screen(*prev)
                nsx, nsy = self.world_to_screen(*nxt)
                self._draw_measurement_label(mx, my, nsx - psx, nsy - psy,
                                             f"{arc:.2f} cm")

    def _draw_corner_angles(self):
        """At each point that's a corner of two solid segments, draw either
        a small square (~90° corners) or an angle label. Also registers the
        bbox of each so clicks on the canvas can open an inline editor."""
        adj: dict = {}  # point_id -> list of ((tx, ty), seg_idx)
        for i, seg in enumerate(self.pattern.segments):
            if seg.style != 'solid':
                continue
            pa = self.pattern.points.get(seg.a)
            pb = self.pattern.points.get(seg.b)
            if not pa or not pb:
                continue
            if seg.kind == 'line':
                ta = (pb.x - pa.x, pb.y - pa.y)
                tb = (pa.x - pb.x, pa.y - pb.y)
            else:
                ta = (seg.c1[0] - pa.x, seg.c1[1] - pa.y)
                tb = (seg.c2[0] - pb.x, seg.c2[1] - pb.y)
            adj.setdefault(seg.a, []).append((ta, i))
            adj.setdefault(seg.b, []).append((tb, i))

        for pid, items in adj.items():
            if len(items) != 2:
                continue
            p = self.pattern.points.get(pid)
            if not p:
                continue
            (t1, sid1), (t2, sid2) = items
            l1 = math.hypot(*t1); l2 = math.hypot(*t2)
            if l1 < 1e-9 or l2 < 1e-9:
                continue
            u1 = (t1[0] / l1, t1[1] / l1)
            u2 = (t2[0] / l2, t2[1] / l2)
            cos_a = max(-1.0, min(1.0, u1[0] * u2[0] + u1[1] * u2[1]))
            angle_deg = math.degrees(math.acos(cos_a))
            if angle_deg < 5 or angle_deg > 178:
                continue

            sx, sy = self.world_to_screen(p.x, p.y)
            bx = u1[0] + u2[0]; by = u1[1] + u2[1]
            bl = math.hypot(bx, by)
            if bl < 1e-9:
                continue
            bx /= bl; by /= bl
            sbx, sby = bx, -by

            # Fix lower-index segment, rotate higher-index segment when edited.
            fixed_sid, rotate_sid = (sid1, sid2) if sid1 < sid2 else (sid2, sid1)

            if abs(angle_deg - 90) < 1.0:
                size_px = 11
                su1 = (u1[0], -u1[1]); su2 = (u2[0], -u2[1])
                p1 = (sx + su1[0] * size_px, sy + su1[1] * size_px)
                p_corner = (p1[0] + su2[0] * size_px, p1[1] + su2[1] * size_px)
                p3 = (sx + su2[0] * size_px, sy + su2[1] * size_px)
                self.canvas.create_line(p1[0], p1[1], p_corner[0], p_corner[1],
                                        fill='#888', width=1.2)
                self.canvas.create_line(p_corner[0], p_corner[1], p3[0], p3[1],
                                        fill='#888', width=1.2)
                # Hit area = the square the marker frames
                xs = [sx, p1[0], p_corner[0], p3[0]]
                ys = [sy, p1[1], p_corner[1], p3[1]]
                self._angle_label_bboxes[pid] = (
                    min(xs), min(ys), max(xs), max(ys), fixed_sid, rotate_sid)
            else:
                if abs(angle_deg - round(angle_deg)) < 0.05:
                    text = f"{int(round(angle_deg))}°"
                else:
                    text = f"{angle_deg:.1f}°"
                offset = 24
                lx = sx + sbx * offset
                ly = sy + sby * offset
                w_est = max(26, len(text) * 6)
                x1 = lx - w_est / 2 - 2; y1 = ly - 8
                x2 = lx + w_est / 2 + 2; y2 = ly + 8
                self.canvas.create_rectangle(x1, y1, x2, y2,
                                             fill='white', outline='')
                self.canvas.create_text(lx, ly, text=text, fill='#666',
                                        font=('Segoe UI', 9))
                self._angle_label_bboxes[pid] = (
                    x1, y1, x2, y2, fixed_sid, rotate_sid)

    # ---- inline (on-canvas) editing of length / angle labels ----

    def _open_inline_editor(self, screen_x, screen_y, initial_text, on_commit, width=8):
        """Show a small Entry on the canvas, pre-filled and selected.
        Return commits and runs on_commit(text). Escape cancels. Clicking
        elsewhere also commits via FocusOut. Any existing inline edit is
        committed first."""
        if self._inline_edit:
            self._close_inline_editor(commit=True)
        entry = tk.Entry(self.canvas, width=width, font=('Segoe UI', 10),
                         justify='center', relief='solid', borderwidth=1)
        entry.insert(0, initial_text)
        entry.select_range(0, tk.END)
        win = self.canvas.create_window(screen_x, screen_y,
                                        window=entry, anchor='center')
        self._inline_edit = {'entry': entry, 'window_id': win,
                             'on_commit': on_commit}

        def do_commit(_e=None):
            self._close_inline_editor(commit=True)

        def do_cancel(_e=None):
            self._close_inline_editor(commit=False)

        entry.bind('<Return>', do_commit)
        entry.bind('<KP_Enter>', do_commit)
        entry.bind('<Escape>', do_cancel)
        entry.bind('<FocusOut>', do_commit)
        entry.focus_set()

    def _close_inline_editor(self, commit=True):
        if not self._inline_edit:
            return
        state = self._inline_edit
        self._inline_edit = None  # prevent re-entry from FocusOut firing again
        text = state['entry'].get()
        try:
            self.canvas.delete(state['window_id'])
        except Exception:
            pass
        try:
            state['entry'].destroy()
        except Exception:
            pass
        if commit:
            try:
                state['on_commit'](text)
            except Exception:
                pass

    def _hit_padlock(self, sx, sy):
        for seg_idx, (x1, y1, x2, y2) in self._padlock_bboxes.items():
            if x1 <= sx <= x2 and y1 <= sy <= y2:
                return seg_idx
        return None

    def _toggle_length_lock(self, seg_idx):
        if seg_idx >= len(self.pattern.segments):
            return
        seg = self.pattern.segments[seg_idx]
        if seg.kind != 'line':
            return
        self._push_undo()
        seg.length_locked = not seg.length_locked
        self.dirty = True
        self.redraw()
        self._set_status(
            f"Length {'locked' if seg.length_locked else 'unlocked'}.")

    def _expand_locked_drag_set(self, initial_pids):
        """BFS through length-locked line segments: any point connected to
        the initial set by a chain of locked lines must translate by the
        same delta so all locked lengths are preserved."""
        in_set = set(initial_pids)
        queue = list(initial_pids)
        while queue:
            pid = queue.pop(0)
            for seg in self.pattern.segments:
                if seg.kind != 'line' or not seg.length_locked:
                    continue
                other = None
                if seg.a == pid:
                    other = seg.b
                elif seg.b == pid:
                    other = seg.a
                if other is not None and other not in in_set:
                    in_set.add(other)
                    queue.append(other)
        return in_set

    def _propagate_lock_translation(self, moved_pid, delta_x, delta_y,
                                     fixed_pids=None):
        """After a length/angle/coord edit has just moved `moved_pid` by
        (delta_x, delta_y), translate every other point reachable from it
        via length-locked lines by the same delta — so locked lines stay
        rigid sticks regardless of how the move was triggered.

        `fixed_pids` are barriers: BFS doesn't propagate past them, and they
        themselves are never translated. Use this to mark pivots (e.g. the
        anchor of an angle rotation) and the fixed endpoint of an edited
        line. Any locked line that bridges across a barrier necessarily has
        its length broken (the geometry can't satisfy all locks in a closed
        loop) — that's expected.

        Also carries darts whose anchor is in the moving chain, and
        translates curve handles for curves whose both endpoints translate.
        """
        if delta_x == 0 and delta_y == 0:
            return
        stops = set(fixed_pids or [])
        visited = {moved_pid}
        chain = {moved_pid}
        queue = [moved_pid]
        while queue:
            pid = queue.pop(0)
            if pid in stops:
                continue
            for seg in self.pattern.segments:
                if seg.kind != 'line' or not seg.length_locked:
                    continue
                other = None
                if seg.a == pid:
                    other = seg.b
                elif seg.b == pid:
                    other = seg.a
                if other is None or other in visited:
                    continue
                visited.add(other)
                chain.add(other)
                queue.append(other)
        # carry darts whose anchor is in the moving chain
        for pid in list(chain):
            dart = self.pattern.find_dart_by_anchor(pid)
            if dart:
                for dp in dart.dart_only_ids():
                    chain.add(dp)
        # translate everything in chain except the moved point (caller has
        # already moved it) and except stops (they are fixed)
        for pid in chain:
            if pid == moved_pid or pid in stops:
                continue
            p = self.pattern.points.get(pid)
            if p:
                p.x += delta_x
                p.y += delta_y
        # curves where both endpoints translated by the same delta
        for seg in self.pattern.segments:
            if seg.kind != 'curve':
                continue
            a_moved = (seg.a in chain and seg.a not in stops) or seg.a == moved_pid
            b_moved = (seg.b in chain and seg.b not in stops) or seg.b == moved_pid
            if a_moved and b_moved:
                if seg.c1:
                    seg.c1 = (seg.c1[0] + delta_x, seg.c1[1] + delta_y)
                if seg.c2:
                    seg.c2 = (seg.c2[0] + delta_x, seg.c2[1] + delta_y)

    def _hit_length_label(self, sx, sy):
        for seg_idx, (x1, y1, x2, y2) in self._length_label_bboxes.items():
            if x1 <= sx <= x2 and y1 <= sy <= y2:
                return seg_idx
        return None

    def _hit_angle_label(self, sx, sy):
        for pid, (x1, y1, x2, y2, fixed_sid, rot_sid) in self._angle_label_bboxes.items():
            if x1 <= sx <= x2 and y1 <= sy <= y2:
                return (pid, fixed_sid, rot_sid)
        return None

    def _begin_length_edit(self, seg_idx):
        if seg_idx >= len(self.pattern.segments):
            return
        seg = self.pattern.segments[seg_idx]
        if seg.kind != 'line':
            return  # arc length isn't directly settable
        pa = self.pattern.points.get(seg.a)
        pb = self.pattern.points.get(seg.b)
        if not pa or not pb:
            return
        cur_len = math.hypot(pb.x - pa.x, pb.y - pa.y)
        x1, y1, x2, y2 = self._length_label_bboxes[seg_idx]
        sx = (x1 + x2) / 2; sy = (y1 + y2) / 2

        def commit(text):
            text = text.strip().lower().rstrip('cm').strip()
            try:
                new_len = float(text)
            except ValueError:
                return
            if new_len <= 0 or abs(new_len - cur_len) < 1e-9:
                return
            self._push_undo()
            dx, dy = pb.x - pa.x, pb.y - pa.y
            d = math.hypot(dx, dy) or 1.0
            old_x, old_y = pb.x, pb.y
            pb.x = pa.x + dx / d * new_len
            pb.y = pa.y + dy / d * new_len
            self._propagate_lock_translation(
                pb.id, pb.x - old_x, pb.y - old_y,
                fixed_pids={pa.id})
            self.dirty = True
            self.redraw()

        self._open_inline_editor(sx, sy, f"{cur_len:.2f}", commit, width=8)

    def _begin_angle_edit(self, pid, fixed_sid, rotate_sid):
        if (fixed_sid >= len(self.pattern.segments)
                or rotate_sid >= len(self.pattern.segments)):
            return
        seg_fix = self.pattern.segments[fixed_sid]
        seg_rot = self.pattern.segments[rotate_sid]
        p = self.pattern.points.get(pid)
        if not p:
            return

        def tangent_at(seg, anchor_id):
            if seg.kind == 'line':
                other_id = seg.b if seg.a == anchor_id else seg.a
                other = self.pattern.points[other_id]
                return (other.x - p.x, other.y - p.y)
            ctrl = seg.c1 if seg.a == anchor_id else seg.c2
            return (ctrl[0] - p.x, ctrl[1] - p.y)

        t1 = tangent_at(seg_fix, pid)
        t2 = tangent_at(seg_rot, pid)
        l1 = math.hypot(*t1) or 1.0
        l2 = math.hypot(*t2) or 1.0
        u1 = (t1[0] / l1, t1[1] / l1)
        u2 = (t2[0] / l2, t2[1] / l2)
        cos_a = max(-1.0, min(1.0, u1[0] * u2[0] + u1[1] * u2[1]))
        cur_deg = math.degrees(math.acos(cos_a))

        x1, y1, x2, y2, _, _ = self._angle_label_bboxes[pid]
        sx = (x1 + x2) / 2; sy = (y1 + y2) / 2

        def commit(text):
            text = text.strip().rstrip('°').rstrip('o').strip()
            try:
                new_deg = float(text)
            except ValueError:
                return
            if not (0 < new_deg < 180):
                return
            if abs(new_deg - cur_deg) < 1e-6:
                return
            # Recompute current tangents in case state changed
            tt1 = tangent_at(seg_fix, pid)
            tt2 = tangent_at(seg_rot, pid)
            ll1 = math.hypot(*tt1) or 1.0
            ll2 = math.hypot(*tt2) or 1.0
            v1 = (tt1[0] / ll1, tt1[1] / ll1)
            v2 = (tt2[0] / ll2, tt2[1] / ll2)
            cross = v1[0] * v2[1] - v1[1] * v2[0]
            dot = v1[0] * v2[0] + v1[1] * v2[1]
            cur_signed = math.atan2(cross, dot)  # in (-pi, pi]
            sign = 1.0 if cur_signed >= 0 else -1.0
            new_signed = sign * math.radians(new_deg)
            delta = new_signed - cur_signed
            cos_d = math.cos(delta); sin_d = math.sin(delta)

            def rot(x, y):
                dx = x - p.x; dy = y - p.y
                return (p.x + dx * cos_d - dy * sin_d,
                        p.y + dx * sin_d + dy * cos_d)

            self._push_undo()
            far_id = seg_rot.b if seg_rot.a == pid else seg_rot.a
            far = self.pattern.points[far_id]
            old_fx, old_fy = far.x, far.y
            far.x, far.y = rot(far.x, far.y)
            if seg_rot.kind == 'curve':
                seg_rot.c1 = rot(*seg_rot.c1)
                seg_rot.c2 = rot(*seg_rot.c2)
            # Propagate to length-locked chain so locked lines stay rigid.
            # Stops: the pivot point and the fixed segment's other endpoint
            # (they must not move).
            other_fix_id = seg_fix.b if seg_fix.a == pid else seg_fix.a
            self._propagate_lock_translation(
                far_id, far.x - old_fx, far.y - old_fy,
                fixed_pids={pid, other_fix_id})
            self.dirty = True
            self.redraw()

        self._open_inline_editor(sx, sy, f"{cur_deg:.1f}", commit, width=6)

    def _draw_padlock(self, cx, cy, locked):
        """Small vector padlock centred at (cx, cy). Solid blue = locked,
        outlined grey = unlocked. Returns its screen bbox for hit testing."""
        c = self.canvas
        color = '#0a84ff' if locked else '#9aa5b1'
        fill = color if locked else 'white'
        bw, bh = 8, 7      # body rect
        sh = 5             # shackle height above body
        # Body
        c.create_rectangle(cx - bw / 2, cy, cx + bw / 2, cy + bh,
                           fill=fill, outline=color, width=1)
        # Shackle arc (closed when locked, slightly clipped when unlocked)
        if locked:
            c.create_arc(cx - 3, cy - sh + 0.5, cx + 3, cy + 1.5,
                         start=0, extent=180,
                         outline=color, style='arc', width=1.5)
        else:
            # Open shackle: arc not joined to body on the right side
            c.create_arc(cx - 3, cy - sh + 0.5, cx + 3, cy + 1.5,
                         start=30, extent=170,
                         outline=color, style='arc', width=1.5)
        # Keyhole tick for locked state
        if locked:
            c.create_line(cx, cy + 2, cx, cy + 5, fill='white', width=1)
        # Hit area, padded a bit so it's easy to click
        return (cx - bw / 2 - 3, cy - sh - 1, cx + bw / 2 + 3, cy + bh + 2)

    def _draw_measurement_label(self, mx, my, dx, dy, text):
        """Draw a length label at (mx, my) on the canvas, offset
        perpendicular to the (dx, dy) tangent direction so it sits
        beside the line rather than overlapping it. Returns the screen
        bbox of the label box for hit-testing."""
        c = self.canvas
        dlen = math.hypot(dx, dy) or 1.0
        # right-hand perpendicular (rotate -90° in screen coords where y goes down)
        nx, ny = -dy / dlen, dx / dlen
        offset = 14
        ox = mx + nx * offset
        oy = my + ny * offset
        w_est = max(8, len(text) * 5.5)
        x1 = ox - w_est / 2 - 2; y1 = oy - 8
        x2 = ox + w_est / 2 + 2; y2 = oy + 7
        c.create_rectangle(x1, y1, x2, y2, fill='white', outline='')
        c.create_text(ox, oy, text=text, fill='#444',
                      font=('Segoe UI', 9))
        return (x1, y1, x2, y2)

    def _draw_seam_allowance(self, part: Part):
        id_pairs = [(i, self.pattern.segments[i]) for i in part.segment_ids
                    if i < len(self.pattern.segments)
                    and self.pattern.segments[i].style == 'solid']
        chain = chain_segments_into_loop_with_ids(id_pairs)
        if not chain:
            return
        poly, edge_ids = polyline_of_chain_with_ids(
            chain, self.pattern.points, samples_per_curve=24)
        # Per-edge SA: segment override if set, else the part's SA
        distances = []
        for sid in edge_ids:
            seg = self.pattern.segments[sid]
            distances.append(seg.seam_allowance
                             if seg.seam_allowance is not None
                             else part.seam_allowance)
        if not any(d > 0 for d in distances):
            return
        offset = offset_closed_polyline_variable(poly, distances)
        if len(offset) < 3:
            return
        flat = []
        for x, y in offset:
            sx, sy = self.world_to_screen(x, y)
            flat += [sx, sy]
        is_sel = self.selected_part == part.id
        color = '#0a84ff' if is_sel else '#7a8693'
        self.canvas.create_line(*flat, fill=color, width=1.2, dash=(5, 4))

    def _part_label_world_pos(self, part: Part):
        """World coords for the part's label: explicit label_pos if set,
        else the centroid of the part's segment endpoints."""
        if part.label_pos:
            return part.label_pos
        pid_set = set()
        for i in part.segment_ids:
            if i < len(self.pattern.segments):
                s = self.pattern.segments[i]
                pid_set.add(s.a); pid_set.add(s.b)
        coords = [(self.pattern.points[pid].x, self.pattern.points[pid].y)
                  for pid in pid_set if pid in self.pattern.points]
        if not coords:
            return None
        cx = sum(p[0] for p in coords) / len(coords)
        cy = sum(p[1] for p in coords) / len(coords)
        return (cx, cy)

    def _part_label_text(self, part: Part):
        label = part.name
        if part.seam_allowance > 0:
            label += f"  (SA {part.seam_allowance:g}cm)"
        return label

    def _draw_part_label(self, part: Part):
        pos = self._part_label_world_pos(part)
        if pos is None:
            return
        sx, sy = self.world_to_screen(*pos)
        is_sel = self.selected_part == part.id
        color = '#0a84ff' if is_sel else '#7a8693'
        label = self._part_label_text(part)
        w_est = max(60, len(label) * 7)
        half_w = w_est / 2 + 4
        half_h = 10
        self.canvas.create_rectangle(sx - half_w, sy - half_h,
                                     sx + half_w, sy + half_h,
                                     fill='white', outline='')
        self.canvas.create_text(sx, sy, text=label, fill=color,
                                font=('Segoe UI', 12, 'italic'))
        # Remember screen bbox so click handling can hit-test the label
        self._part_label_bboxes[part.id] = (sx - half_w, sy - half_h,
                                            sx + half_w, sy + half_h)

    def _seam_join_map(self):
        """Return {seam_label: [part_name, ...]} — for each seam label, the
        distinct part names that carry a segment with that label. Used to
        tell the user which parts a labelled edge joins."""
        joins = {}
        for si, seg in enumerate(self.pattern.segments):
            if not seg.seam_label:
                continue
            owner = self._segment_owner_part(si)
            name = owner.name if owner else '(loose)'
            joins.setdefault(seg.seam_label, [])
            if name not in joins[seg.seam_label]:
                joins[seg.seam_label].append(name)
        return joins

    def _draw_seam_labels(self):
        joins = self._seam_join_map()
        for si, seg in enumerate(self.pattern.segments):
            if not seg.seam_label:
                continue
            pa = self.pattern.points.get(seg.a); pb = self.pattern.points.get(seg.b)
            if not pa or not pb:
                continue
            wx, wy, tx, ty = segment_point_and_tangent(seg, self.pattern.points, 0.5)
            sx, sy = self.world_to_screen(wx, wy)
            # offset toward the interior side a little (perp to screen tangent)
            stx, sty = tx, -ty
            px, py = -sty, stx
            ox = sx + px * 12; oy = sy + py * 12
            owner = self._segment_owner_part(si)
            others = [n for n in joins.get(seg.seam_label, [])
                      if not owner or n != owner.name]
            text = seg.seam_label
            if others:
                text += " ↔ " + ", ".join(others)
            w_est = max(30, len(text) * 6)
            self.canvas.create_rectangle(ox - w_est / 2 - 2, oy - 7,
                                         ox + w_est / 2 + 2, oy + 7,
                                         fill='#fff7e6', outline='#e0a800')
            self.canvas.create_text(ox, oy, text=text, fill='#a06800',
                                    font=('Segoe UI', 8))

    def _draw_notch(self, notch: Notch):
        if notch.segment_id >= len(self.pattern.segments):
            return
        seg = self.pattern.segments[notch.segment_id]
        pa = self.pattern.points.get(seg.a); pb = self.pattern.points.get(seg.b)
        if not pa or not pb:
            return
        wx, wy, tx, ty = segment_point_and_tangent(seg, self.pattern.points, notch.t)
        sx, sy = self.world_to_screen(wx, wy)
        # perpendicular in screen space (world y is up, screen y is down)
        # tangent in screen: (tx, -ty); perpendicular: (-(-ty), tx) = (ty, tx)... derive directly
        stx, sty = tx, -ty
        plen = math.hypot(stx, sty) or 1.0
        # perpendicular to screen tangent
        px, py = -sty / plen, stx / plen
        half = 7  # px, notch half-length
        self.canvas.create_line(sx - px * half, sy - py * half,
                                sx + px * half, sy + py * half,
                                fill='#c026d3', width=1.6)

    def _draw_grain_line(self, part: Part):
        x1, y1, x2, y2 = part.grain_line
        s1 = self.world_to_screen(x1, y1)
        s2 = self.world_to_screen(x2, y2)
        is_sel = self.selected_part == part.id
        color = '#0a84ff' if is_sel else '#555'
        self.canvas.create_line(s1[0], s1[1], s2[0], s2[1],
                                fill=color, width=1.4)
        self._draw_arrowhead(s1, s2, color)
        self._draw_arrowhead(s2, s1, color)

    def _draw_arrowhead(self, tip, tail, color):
        """Draw an arrowhead at `tip` pointing away from `tail`."""
        dx = tip[0] - tail[0]; dy = tip[1] - tail[1]
        d = math.hypot(dx, dy) or 1.0
        ux, uy = dx / d, dy / d
        size = 9
        spread = 0.5  # radians half-angle
        cos_s = math.cos(spread); sin_s = math.sin(spread)
        # two barbs
        b1 = (tip[0] - size * (ux * cos_s - uy * sin_s),
              tip[1] - size * (uy * cos_s + ux * sin_s))
        b2 = (tip[0] - size * (ux * cos_s + uy * sin_s),
              tip[1] - size * (uy * cos_s - ux * sin_s))
        self.canvas.create_line(tip[0], tip[1], b1[0], b1[1], fill=color, width=1.4)
        self.canvas.create_line(tip[0], tip[1], b2[0], b2[1], fill=color, width=1.4)

    def _draw_rubber_band(self):
        _, (sx0, sy0), additive = self.drag
        sx1, sy1 = self.canvas.winfo_pointerxy()
        # convert to canvas-relative
        cx = self.canvas.winfo_rootx()
        cy = self.canvas.winfo_rooty()
        sx1 -= cx; sy1 -= cy
        x1, y1 = min(sx0, sx1), min(sy0, sy1)
        x2, y2 = max(sx0, sx1), max(sy0, sy1)
        outline = '#0a84ff'
        self.canvas.create_rectangle(x1, y1, x2, y2,
                                     outline=outline, dash=(2, 2),
                                     fill='#0a84ff', stipple='gray12')

    # ---- properties panel ----

    def _clear_props(self):
        for w in self.props_frame.winfo_children():
            w.destroy()

    def _props_placeholder(self):
        self._clear_props()
        ttk.Label(self.props_frame, text="Nothing selected.",
                  foreground='#666').pack(anchor='w')
        ttk.Label(self.props_frame,
                  text="Click an item, or drag in empty space to select multiple points.",
                  foreground='#888', wraplength=240, justify='left').pack(anchor='w')

    def _refresh_properties(self):
        # priority: part > single point > single segment > multi
        if self.selected_part is not None:
            part = next((p for p in self.pattern.parts if p.id == self.selected_part), None)
            if part:
                self._build_part_props(part)
                return
        n_pts = len(self.selected_points)
        n_segs = len(self.selected_segments)
        if n_pts == 1 and n_segs == 0:
            pid = next(iter(self.selected_points))
            p = self.pattern.points.get(pid)
            if p:
                self._build_point_props(p)
                return
        if n_pts == 0 and n_segs == 1:
            idx = next(iter(self.selected_segments))
            if idx < len(self.pattern.segments):
                self._build_segment_props(idx, self.pattern.segments[idx])
                return
        if n_pts == 0 and n_segs == 0:
            self._props_placeholder()
            return
        self._build_multi_props(n_pts, n_segs)

    def _build_point_props(self, p: Point):
        self._clear_props()
        f = self.props_frame
        ttk.Label(f, text=f"Point {p.label}", font=('Segoe UI', 10, 'bold')).pack(anchor='w')

        row = ttk.Frame(f); row.pack(fill='x', pady=2)
        ttk.Label(row, text="Label:", width=8).pack(side='left')
        label_var = tk.StringVar(value=p.label)
        e = ttk.Entry(row, textvariable=label_var); e.pack(side='left', fill='x', expand=True)
        def commit_label(*_):
            v = label_var.get().strip()
            if v and v != p.label:
                self._push_undo()
                p.label = v; self.dirty = True; self.redraw()
        e.bind('<Return>', commit_label); e.bind('<FocusOut>', commit_label)

        for axis, getter, setter in [
            ('X (cm):', lambda: p.x, lambda v: setattr(p, 'x', v)),
            ('Y (cm):', lambda: p.y, lambda v: setattr(p, 'y', v)),
        ]:
            row = ttk.Frame(f); row.pack(fill='x', pady=2)
            ttk.Label(row, text=axis, width=8).pack(side='left')
            var = tk.StringVar(value=f"{getter():.3f}")
            e = ttk.Entry(row, textvariable=var); e.pack(side='left', fill='x', expand=True)
            def commit(_e=None, var=var, setter=setter, getter=getter):
                try:
                    new_val = float(var.get())
                except ValueError:
                    return
                if abs(new_val - getter()) < 1e-9:
                    return
                self._push_undo()
                old_x, old_y = p.x, p.y
                setter(new_val)
                self._propagate_lock_translation(
                    p.id, p.x - old_x, p.y - old_y, fixed_pids=set())
                self.dirty = True; self.redraw()
            e.bind('<Return>', commit); e.bind('<FocusOut>', commit)

        ttk.Button(f, text="Delete point",
                   command=self.delete_selected).pack(fill='x', pady=(8, 0))

    def _build_segment_props(self, idx: int, seg: Segment):
        self._clear_props()
        f = self.props_frame
        pa = self.pattern.points[seg.a]; pb = self.pattern.points[seg.b]
        title = "Line" if seg.kind == 'line' else "Curve"
        ttk.Label(f, text=f"{title} {pa.label}–{pb.label}",
                  font=('Segoe UI', 10, 'bold')).pack(anchor='w')

        if seg.kind == 'line':
            cur = math.hypot(pb.x - pa.x, pb.y - pa.y)
            angle = math.degrees(math.atan2(pb.y - pa.y, pb.x - pa.x))

            row = ttk.Frame(f); row.pack(fill='x', pady=2)
            ttk.Label(row, text="Length:", width=8).pack(side='left')
            length_var = tk.StringVar(value=f"{cur:.3f}")
            e = ttk.Entry(row, textvariable=length_var); e.pack(side='left', fill='x', expand=True)
            ttk.Label(row, text="cm").pack(side='left')
            def commit_length(*_):
                try:
                    new_len = float(length_var.get())
                except ValueError:
                    return
                if new_len <= 0:
                    return
                if abs(new_len - cur) < 1e-9:
                    return
                self._push_undo()
                dx, dy = pb.x - pa.x, pb.y - pa.y
                d = math.hypot(dx, dy) or 1.0
                old_x, old_y = pb.x, pb.y
                pb.x = pa.x + dx / d * new_len
                pb.y = pa.y + dy / d * new_len
                self._propagate_lock_translation(
                    pb.id, pb.x - old_x, pb.y - old_y,
                    fixed_pids={pa.id})
                self.dirty = True; self.redraw()
            e.bind('<Return>', commit_length); e.bind('<FocusOut>', commit_length)

            row = ttk.Frame(f); row.pack(fill='x', pady=2)
            ttk.Label(row, text="Angle:", width=8).pack(side='left')
            angle_var = tk.StringVar(value=f"{angle:.2f}")
            e = ttk.Entry(row, textvariable=angle_var); e.pack(side='left', fill='x', expand=True)
            ttk.Label(row, text="°").pack(side='left')
            def commit_angle(*_):
                try:
                    new_a_deg = float(angle_var.get())
                except ValueError:
                    return
                if abs(new_a_deg - angle) < 1e-9:
                    return
                self._push_undo()
                new_a = math.radians(new_a_deg)
                d = math.hypot(pb.x - pa.x, pb.y - pa.y)
                old_x, old_y = pb.x, pb.y
                pb.x = pa.x + math.cos(new_a) * d
                pb.y = pa.y + math.sin(new_a) * d
                self._propagate_lock_translation(
                    pb.id, pb.x - old_x, pb.y - old_y,
                    fixed_pids={pa.id})
                self.dirty = True; self.redraw()
            e.bind('<Return>', commit_angle); e.bind('<FocusOut>', commit_angle)

            ttk.Label(f,
                      text=(f"Moves {pb.label}; {pa.label} stays put. "
                            "Other points don't move — use Construct-line "
                            "or Move-along-line for accurate construction."),
                      foreground='#888', wraplength=240, justify='left').pack(
                anchor='w', pady=(4, 0))

            lock_var = tk.BooleanVar(value=seg.length_locked)
            def commit_lock(*_):
                if lock_var.get() == seg.length_locked:
                    return
                self._push_undo()
                seg.length_locked = lock_var.get()
                self.dirty = True; self.redraw()
            ttk.Checkbutton(f, text="Lock length (rigid stick on drag)",
                            variable=lock_var, command=commit_lock).pack(
                anchor='w', pady=(6, 0))
        else:
            p0 = (pa.x, pa.y); p3 = (pb.x, pb.y)
            arc = polyline_length(cubic_bezier_samples(p0, seg.c1, seg.c2, p3, n=96))
            chord = math.hypot(pb.x - pa.x, pb.y - pa.y)
            ttk.Label(f, text=f"Arc length: {arc:.3f} cm").pack(anchor='w')
            ttk.Label(f, text=f"Chord: {chord:.3f} cm").pack(anchor='w')
            ttk.Label(f, text="Drag the square handles to reshape.",
                      foreground='#888').pack(anchor='w', pady=(4, 0))
            ttk.Button(f, text="Reset handles to straight",
                       command=lambda: self._reset_curve_handles(idx)).pack(fill='x', pady=(6, 0))

        # Style toggle (dart / fold line) for any segment
        row = ttk.Frame(f); row.pack(fill='x', pady=(8, 0))
        ttk.Label(row, text="Style:", width=8).pack(side='left')
        style_var = tk.StringVar(value=seg.style)
        cb = ttk.Combobox(row, textvariable=style_var,
                          values=['solid', 'dotted'], state='readonly')
        cb.pack(side='left', fill='x', expand=True)
        def commit_style(_e=None):
            new_style = style_var.get()
            if new_style == seg.style:
                return
            self._push_undo()
            seg.style = new_style
            self.dirty = True; self.redraw()
        cb.bind('<<ComboboxSelected>>', commit_style)
        ttk.Label(f, text="Dotted = dart, fold line, or other non-cutting marking.",
                  foreground='#888', wraplength=240, justify='left').pack(anchor='w', pady=(2, 0))

        # Per-segment seam allowance override
        row = ttk.Frame(f); row.pack(fill='x', pady=(8, 0))
        ttk.Label(row, text="SA:", width=8).pack(side='left')
        cur_sa = '' if seg.seam_allowance is None else f"{seg.seam_allowance:g}"
        sa_var = tk.StringVar(value=cur_sa)
        sa_entry = ttk.Entry(row, textvariable=sa_var)
        sa_entry.pack(side='left', fill='x', expand=True)
        ttk.Label(row, text="cm").pack(side='left')

        def commit_seg_sa(*_):
            text = sa_var.get().strip()
            if text == '':
                new_val = None
            else:
                try:
                    new_val = float(text)
                    if new_val < 0:
                        return
                except ValueError:
                    return
            if new_val == seg.seam_allowance:
                return
            self._push_undo()
            seg.seam_allowance = new_val
            self.dirty = True; self.redraw()
        sa_entry.bind('<Return>', commit_seg_sa)
        sa_entry.bind('<FocusOut>', commit_seg_sa)
        ttk.Label(f, text="Override the part's seam allowance for this edge only. "
                          "Leave blank to inherit from the part.",
                  foreground='#888', wraplength=240, justify='left').pack(
            anchor='w', pady=(2, 0))

        ttk.Button(f, text="Delete segment",
                   command=self.delete_selected).pack(fill='x', pady=(8, 0))

    def _build_multi_props(self, n_pts, n_segs):
        self._clear_props()
        f = self.props_frame
        parts = []
        if n_pts: parts.append(f"{n_pts} point{'s' if n_pts != 1 else ''}")
        if n_segs: parts.append(f"{n_segs} segment{'s' if n_segs != 1 else ''}")
        ttk.Label(f, text=" + ".join(parts) + " selected",
                  font=('Segoe UI', 10, 'bold')).pack(anchor='w')
        ttk.Label(f, text="Drag any selected point to move them together.",
                  foreground='#888', wraplength=240, justify='left').pack(anchor='w', pady=(4, 0))

        # Convenience: create part from selected segments
        if n_segs >= 1:
            ttk.Button(f, text=f"Create part from {n_segs} selected segments...",
                       command=self.create_part_dialog).pack(fill='x', pady=(8, 0))
        ttk.Button(f, text="Delete selection",
                   command=self.delete_selected).pack(fill='x', pady=(4, 0))

    def _build_part_props(self, part: Part):
        self._clear_props()
        f = self.props_frame
        ttk.Label(f, text=f"Part: {part.name}",
                  font=('Segoe UI', 10, 'bold')).pack(anchor='w')
        ttk.Label(f, text=f"{len(part.segment_ids)} segments",
                  foreground='#888').pack(anchor='w')

        row = ttk.Frame(f); row.pack(fill='x', pady=4)
        ttk.Label(row, text="Name:", width=12).pack(side='left')
        name_var = tk.StringVar(value=part.name)
        e = ttk.Entry(row, textvariable=name_var); e.pack(side='left', fill='x', expand=True)
        def commit_name(*_):
            v = name_var.get().strip()
            if v and v != part.name:
                self._push_undo()
                part.name = v; self.dirty = True; self.redraw()
        e.bind('<Return>', commit_name); e.bind('<FocusOut>', commit_name)

        row = ttk.Frame(f); row.pack(fill='x', pady=4)
        ttk.Label(row, text="Seam allow:", width=12).pack(side='left')
        sa_var = tk.StringVar(value=f"{part.seam_allowance:g}")
        e = ttk.Entry(row, textvariable=sa_var); e.pack(side='left', fill='x', expand=True)
        ttk.Label(row, text="cm").pack(side='left')
        def commit_sa(*_):
            try:
                v = float(sa_var.get())
                if v < 0: v = 0
            except ValueError:
                return
            if abs(v - part.seam_allowance) < 1e-9:
                return
            self._push_undo()
            part.seam_allowance = v
            self.dirty = True; self.redraw()
        e.bind('<Return>', commit_sa); e.bind('<FocusOut>', commit_sa)

        ttk.Label(f, text="Set to 0 to hide the dotted seam line. "
                          "Only solid segments are used to compute the offset.",
                  foreground='#888', wraplength=240, justify='left').pack(anchor='w', pady=(2, 0))

        if part.label_pos is not None:
            ttk.Button(f, text="Reset label position",
                       command=lambda: self._reset_part_label_pos(part.id)).pack(
                fill='x', pady=(8, 0))
        else:
            ttk.Label(f, text="Drag the part name on canvas to reposition it.",
                      foreground='#888').pack(anchor='w', pady=(8, 0))

        ttk.Button(f, text="Delete part (keeps segments)",
                   command=lambda: self._delete_part(part.id)).pack(fill='x', pady=(4, 0))

    def _reset_part_label_pos(self, part_id):
        for p in self.pattern.parts:
            if p.id == part_id and p.label_pos is not None:
                self._push_undo()
                p.label_pos = None
                self.dirty = True
                self.redraw()
                return

    def _reset_curve_handles(self, idx):
        self._push_undo()
        seg = self.pattern.segments[idx]
        pa = self.pattern.points[seg.a]; pb = self.pattern.points[seg.b]
        seg.c1 = (pa.x + (pb.x - pa.x) / 3.0, pa.y + (pb.y - pa.y) / 3.0)
        seg.c2 = (pa.x + 2 * (pb.x - pa.x) / 3.0, pa.y + 2 * (pb.y - pa.y) / 3.0)
        self.dirty = True; self.redraw()

    def _refresh_points_list(self):
        self.points_list.delete(0, tk.END)
        ordered = sorted(self.pattern.points.values(), key=lambda p: p.label)
        self._points_list_ids = [p.id for p in ordered]
        for p in ordered:
            self.points_list.insert(tk.END, f"{p.label}   ({p.x:+.2f}, {p.y:+.2f})")
        self.points_list.selection_clear(0, tk.END)
        for i, pid in enumerate(self._points_list_ids):
            if pid in self.selected_points:
                self.points_list.selection_set(i)

    def _refresh_parts_list(self):
        self.parts_list.delete(0, tk.END)
        self._parts_list_ids = [p.id for p in self.pattern.parts]
        for p in self.pattern.parts:
            sa = f"  SA {p.seam_allowance:g}cm" if p.seam_allowance > 0 else ""
            self.parts_list.insert(tk.END, f"{p.name}  ({len(p.segment_ids)} segs){sa}")
        self.parts_list.selection_clear(0, tk.END)
        if self.selected_part is not None and self.selected_part in self._parts_list_ids:
            self.parts_list.selection_set(self._parts_list_ids.index(self.selected_part))

    def _on_points_list_select(self, event):
        sel = self.points_list.curselection()
        if not sel:
            return
        pid = self._points_list_ids[sel[0]]
        self._select_only_point(pid)
        self.redraw()

    def _on_parts_list_select(self, event):
        sel = self.parts_list.curselection()
        if not sel:
            return
        part_id = self._parts_list_ids[sel[0]]
        self._select_part(part_id)
        self.redraw()

    # ---- hit testing ----

    def _hit_test(self, sx, sy):
        for p in self.pattern.points.values():
            psx, psy = self.world_to_screen(p.x, p.y)
            if math.hypot(psx - sx, psy - sy) <= self.HIT_RADIUS_PX:
                return ('point', p.id)
        # handles of any selected curve segment
        for idx in self.selected_segments:
            if idx >= len(self.pattern.segments):
                continue
            seg = self.pattern.segments[idx]
            if seg.kind == 'curve':
                for which, cp in enumerate([seg.c1, seg.c2], start=1):
                    csx, csy = self.world_to_screen(*cp)
                    if math.hypot(csx - sx, csy - sy) <= self.HIT_RADIUS_PX:
                        return ('handle', idx, which)
        # part labels (drawn over segments, so they hit first)
        for part_id, (x1, y1, x2, y2) in self._part_label_bboxes.items():
            if x1 <= sx <= x2 and y1 <= sy <= y2:
                return ('part_label', part_id)
        for idx, seg in enumerate(self.pattern.segments):
            if self._point_on_segment(sx, sy, seg):
                return ('segment', idx)
        return None

    def _point_on_segment(self, sx, sy, seg):
        pa = self.pattern.points.get(seg.a); pb = self.pattern.points.get(seg.b)
        if not pa or not pb:
            return False
        if seg.kind == 'line':
            sxa, sya = self.world_to_screen(pa.x, pa.y)
            sxb, syb = self.world_to_screen(pb.x, pb.y)
            return self._dist_point_segment(sx, sy, sxa, sya, sxb, syb) <= self.HIT_RADIUS_PX
        pts = cubic_bezier_samples((pa.x, pa.y), seg.c1, seg.c2, (pb.x, pb.y), n=48)
        for i in range(1, len(pts)):
            sxa, sya = self.world_to_screen(*pts[i - 1])
            sxb, syb = self.world_to_screen(*pts[i])
            if self._dist_point_segment(sx, sy, sxa, sya, sxb, syb) <= self.HIT_RADIUS_PX:
                return True
        return False

    SNAP_PX = 10

    def _compute_snap(self, sx, sy):
        """Decide where a click at screen (sx, sy) should actually land,
        relative to existing geometry. Returns a dict with snapped world
        coords plus optional snap targets:

        - point_id: snap exactly onto this existing point
        - segment_idx / segment_t / segment_kind: split this segment
        - snap_x_pid / snap_y_pid: X/Y aligned with this point

        Snap precedence: existing point > segment split > axis alignment.
        Falls through to free placement (raw cursor coords) when nothing
        is in range.
        """
        result = {
            'point_id': None,
            'segment_idx': None, 'segment_t': None, 'segment_kind': None,
            'snap_x_pid': None, 'snap_y_pid': None,
            'wx': 0.0, 'wy': 0.0,
        }

        # 1. Existing point in hit range
        best_pt = None
        best_pt_dist = self.HIT_RADIUS_PX + 0.01
        for p in self.pattern.points.values():
            psx, psy = self.world_to_screen(p.x, p.y)
            d = math.hypot(psx - sx, psy - sy)
            if d <= best_pt_dist:
                best_pt_dist = d
                best_pt = p
        if best_pt is not None:
            result['point_id'] = best_pt.id
            result['wx'] = best_pt.x
            result['wy'] = best_pt.y
            return result

        # 2. Segment split (uses existing helper, same hit radius)
        split = self._find_segment_to_split(sx, sy)
        if split is not None:
            seg_idx, wx, wy, t, kind = split
            result['segment_idx'] = seg_idx
            result['segment_t'] = t
            result['segment_kind'] = kind
            result['wx'] = wx
            result['wy'] = wy
            return result

        # 3. Axis alignment: snap X and/or Y to align with the closest
        #    existing point whose screen X/Y is within SNAP_PX of the cursor.
        snap_x_pt = None; snap_x_dist = self.SNAP_PX
        snap_y_pt = None; snap_y_dist = self.SNAP_PX
        for p in self.pattern.points.values():
            psx, psy = self.world_to_screen(p.x, p.y)
            dx = abs(psx - sx)
            if dx <= snap_x_dist:
                snap_x_dist = dx
                snap_x_pt = p
            dy = abs(psy - sy)
            if dy <= snap_y_dist:
                snap_y_dist = dy
                snap_y_pt = p

        wx, wy = self.screen_to_world(sx, sy)
        if snap_x_pt is not None:
            wx = snap_x_pt.x
            result['snap_x_pid'] = snap_x_pt.id
        if snap_y_pt is not None:
            wy = snap_y_pt.y
            result['snap_y_pid'] = snap_y_pt.id
        result['wx'] = wx
        result['wy'] = wy
        return result

    def _draw_snap_overlay(self):
        """Render snap indicators on the canvas using a tag so they can be
        cleared/redrawn without a full redraw."""
        self.canvas.delete('snap_overlay')
        if not self._snap_state:
            return
        snap = self._snap_state
        c = self.canvas
        color = '#ff7a00'

        if snap.get('point_id') is not None:
            p = self.pattern.points.get(snap['point_id'])
            if p:
                sx, sy = self.world_to_screen(p.x, p.y)
                c.create_oval(sx - 10, sy - 10, sx + 10, sy + 10,
                              outline=color, width=2, tags='snap_overlay')
            return

        if snap.get('segment_idx') is not None:
            sx, sy = self.world_to_screen(snap['wx'], snap['wy'])
            c.create_oval(sx - 6, sy - 6, sx + 6, sy + 6,
                          outline=color, width=1.5, tags='snap_overlay')
            return

        if snap.get('snap_x_pid') is None and snap.get('snap_y_pid') is None:
            return
        cursor_sx, cursor_sy = self.world_to_screen(snap['wx'], snap['wy'])
        if snap.get('snap_x_pid') is not None:
            p = self.pattern.points[snap['snap_x_pid']]
            psx, psy = self.world_to_screen(p.x, p.y)
            c.create_line(psx, psy, cursor_sx, cursor_sy,
                          fill=color, dash=(3, 3), width=1,
                          tags='snap_overlay')
        if snap.get('snap_y_pid') is not None:
            p = self.pattern.points[snap['snap_y_pid']]
            psx, psy = self.world_to_screen(p.x, p.y)
            c.create_line(psx, psy, cursor_sx, cursor_sy,
                          fill=color, dash=(3, 3), width=1,
                          tags='snap_overlay')
        # Small crosshair at the snapped cursor position
        c.create_line(cursor_sx - 6, cursor_sy, cursor_sx + 6, cursor_sy,
                      fill=color, width=1.4, tags='snap_overlay')
        c.create_line(cursor_sx, cursor_sy - 6, cursor_sx, cursor_sy + 6,
                      fill=color, width=1.4, tags='snap_overlay')

    def _find_segment_to_split(self, sx, sy):
        """If the screen click is on (or near) an existing segment, return
        (seg_idx, world_x, world_y, t, 'line'|'curve') for splitting it.
        Avoids splits right at existing endpoints."""
        best = None
        best_dist = self.HIT_RADIUS_PX + 0.01
        endpoint_tol = 10  # px
        for idx, seg in enumerate(self.pattern.segments):
            pa = self.pattern.points.get(seg.a); pb = self.pattern.points.get(seg.b)
            if not pa or not pb:
                continue
            sxa, sya = self.world_to_screen(pa.x, pa.y)
            sxb, syb = self.world_to_screen(pb.x, pb.y)
            if math.hypot(sx - sxa, sy - sya) < endpoint_tol:
                continue
            if math.hypot(sx - sxb, sy - syb) < endpoint_tol:
                continue
            if seg.kind == 'line':
                dx, dy = sxb - sxa, syb - sya
                if dx == 0 and dy == 0:
                    continue
                t = max(0.0, min(1.0,
                                 ((sx - sxa) * dx + (sy - sya) * dy) / (dx * dx + dy * dy)))
                cx_s = sxa + t * dx; cy_s = sya + t * dy
                d = math.hypot(sx - cx_s, sy - cy_s)
                if d <= best_dist and 0.0 < t < 1.0:
                    best_dist = d
                    best = (idx,
                            pa.x + t * (pb.x - pa.x),
                            pa.y + t * (pb.y - pa.y),
                            t, 'line')
            else:
                N = 128
                pts = cubic_bezier_samples((pa.x, pa.y), seg.c1, seg.c2,
                                           (pb.x, pb.y), n=N)
                for i, (wx, wy) in enumerate(pts):
                    if i == 0 or i == N:
                        continue
                    psx, psy = self.world_to_screen(wx, wy)
                    d = math.hypot(sx - psx, sy - psy)
                    if d <= best_dist:
                        best_dist = d
                        best = (idx, wx, wy, i / N, 'curve')
        return best

    def _split_segment_at(self, seg_idx, wx, wy, t, kind):
        """Split the segment so the existing curve/line shape is preserved
        and a new point sits at parameter t. Returns the new point id."""
        seg = self.pattern.segments[seg_idx]
        pb_id = seg.b
        style = seg.style
        if kind == 'line':
            new_pt = self.pattern.add_point(wx, wy)
            seg.b = new_pt.id
            new_idx = self.pattern.add_line(new_pt.id, pb_id)
            self.pattern.segments[new_idx].style = style
        else:
            pa = self.pattern.points[seg.a]; pb = self.pattern.points[pb_id]
            P0 = (pa.x, pa.y); P1 = seg.c1; P2 = seg.c2; P3 = (pb.x, pb.y)

            def lerp(A, B):
                return (A[0] + t * (B[0] - A[0]), A[1] + t * (B[1] - A[1]))

            Q1 = lerp(P0, P1); Q2 = lerp(P1, P2); Q3 = lerp(P2, P3)
            R1 = lerp(Q1, Q2); R2 = lerp(Q2, Q3)
            S = lerp(R1, R2)
            new_pt = self.pattern.add_point(S[0], S[1])
            seg.b = new_pt.id
            seg.c1 = Q1; seg.c2 = R1
            new_idx = len(self.pattern.segments)
            self.pattern.segments.append(Segment(
                kind='curve', a=new_pt.id, b=pb_id,
                c1=R2, c2=Q3, style=style,
            ))
        for part in self.pattern.parts:
            if seg_idx in part.segment_ids and new_idx not in part.segment_ids:
                part.segment_ids.append(new_idx)
        return new_pt.id

    @staticmethod
    def _dist_point_segment(px, py, x1, y1, x2, y2):
        dx, dy = x2 - x1, y2 - y1
        if dx == 0 and dy == 0:
            return math.hypot(px - x1, py - y1)
        t = max(0.0, min(1.0, ((px - x1) * dx + (py - y1) * dy) / (dx * dx + dy * dy)))
        return math.hypot(px - (x1 + t * dx), py - (y1 + t * dy))

    # ---- mouse handling ----

    def _mode_changed(self):
        self._cancel_pending()
        self._snap_state = None
        self.canvas.delete('snap_overlay')
        self._set_status(f"Mode: {self.mode.get()}")

    def _typing_in_entry(self):
        focused = self.root.focus_get()
        return isinstance(focused, (tk.Entry, tk.Text))

    def _key_set_mode(self, mode_id):
        if self._typing_in_entry():
            return
        self.mode.set(mode_id)
        self._mode_changed()

    def _key_add_dart(self):
        if self._typing_in_entry():
            return
        self.add_dart_dialog()

    def _key_draw_rectangle(self):
        if self._typing_in_entry():
            return
        self.draw_rectangle_dialog()

    def _cancel_pending(self):
        self.pending_a = None
        self.drag = None
        self.redraw()

    def on_mouse_move(self, event):
        wx, wy = self.screen_to_world(event.x, event.y)
        self._set_status(f"x={wx:+.2f} cm   y={wy:+.2f} cm   mode={self.mode.get()}")
        # Update snap visuals only while in a point-placement mode
        if self.mode.get() in ('point', 'line', 'curve'):
            self._snap_state = self._compute_snap(event.x, event.y)
            self._draw_snap_overlay()
        elif self._snap_state is not None:
            self._snap_state = None
            self.canvas.delete('snap_overlay')
        if self.drag and self.drag[0] == 'rubber':
            self.redraw()

    def on_left_press(self, event, shift=False):
        self.press_pos = (event.x, event.y)
        # Padlock clicks toggle the lock; they take priority over the inline
        # length editor since the padlock sits right next to it.
        pad_seg = self._hit_padlock(event.x, event.y)
        if pad_seg is not None and not shift:
            self._toggle_length_lock(pad_seg)
            return
        # Length / angle label clicks open an inline editor in any mode —
        # they take precedence over the regular point/segment hit-tests so
        # the user can always click a label to edit it.
        seg_idx = self._hit_length_label(event.x, event.y)
        if seg_idx is not None and not shift:
            self._begin_length_edit(seg_idx)
            return
        angle_hit = self._hit_angle_label(event.x, event.y)
        if angle_hit is not None and not shift:
            pid, fixed_sid, rot_sid = angle_hit
            self._begin_angle_edit(pid, fixed_sid, rot_sid)
            return
        hit = self._hit_test(event.x, event.y)
        mode = self.mode.get()

        if mode == 'select':
            if hit is None:
                # Empty space → start rubber band
                if not shift:
                    self._clear_selection()
                self.drag = ('rubber', (event.x, event.y), shift)
                self.redraw()
                return
            kind = hit[0]
            if kind == 'point':
                pid = hit[1]
                if shift:
                    self._toggle_point(pid)
                    self.drag = None
                else:
                    if pid not in self.selected_points:
                        self._select_only_point(pid)
                    # Prepare group drag. The set expands in three passes:
                    #   1. dart anchors carry their dart's own 3 points
                    #   2. length-locked lines drag their other endpoint
                    #      (transitively — BFS through all locked lines)
                    #   3. dart pass again, in case step 2 added a new anchor
                    drag_ids = set(self.selected_points)
                    for sel_pid in list(drag_ids):
                        dart = self.pattern.find_dart_by_anchor(sel_pid)
                        if dart:
                            drag_ids.update(dart.dart_only_ids())
                    drag_ids = self._expand_locked_drag_set(drag_ids)
                    for sel_pid in list(drag_ids):
                        dart = self.pattern.find_dart_by_anchor(sel_pid)
                        if dart:
                            drag_ids.update(dart.dart_only_ids())
                    starts = {p: (self.pattern.points[p].x, self.pattern.points[p].y)
                              for p in drag_ids if p in self.pattern.points}
                    # Capture curve handle starting positions for any curve
                    # whose BOTH endpoints are in the drag set — otherwise
                    # the endpoints move but the handles stay put and the
                    # curve warps.
                    handle_starts = []
                    for si, sg in enumerate(self.pattern.segments):
                        if sg.kind == 'curve' and sg.a in drag_ids and sg.b in drag_ids:
                            if sg.c1:
                                handle_starts.append((si, 'c1', sg.c1))
                            if sg.c2:
                                handle_starts.append((si, 'c2', sg.c2))
                    self._push_undo()
                    self.drag = ('point_group', (event.x, event.y),
                                 starts, handle_starts)
                self.redraw()
            elif kind == 'handle':
                _, seg_idx, which = hit
                self._push_undo()
                self.drag = ('handle', seg_idx, which)
            elif kind == 'part_label':
                part_id = hit[1]
                self._select_part(part_id)
                part = next((p for p in self.pattern.parts if p.id == part_id), None)
                if part is None:
                    self.redraw()
                    return
                if shift:
                    # Shift-drag: reposition ONLY the label, leave the part
                    # geometry in place. Old default behaviour.
                    start_world = self._part_label_world_pos(part) or (0, 0)
                    self._push_undo()
                    self.drag = ('part_label', part_id,
                                 (event.x, event.y), start_world)
                else:
                    # Default: drag the whole part as a rigid unit —
                    # boundary points, dart points, curve handles, and
                    # the label (if explicitly positioned) all translate.
                    pids = set()
                    for sid in part.segment_ids:
                        if sid < len(self.pattern.segments):
                            s = self.pattern.segments[sid]
                            pids.add(s.a); pids.add(s.b)
                    for pid in list(pids):
                        dart = self.pattern.find_dart_by_anchor(pid)
                        if dart:
                            pids.update(dart.dart_only_ids())
                    starts = {p: (self.pattern.points[p].x,
                                  self.pattern.points[p].y)
                              for p in pids if p in self.pattern.points}
                    handle_starts = []
                    for si, sg in enumerate(self.pattern.segments):
                        if sg.kind == 'curve' and sg.a in pids and sg.b in pids:
                            if sg.c1:
                                handle_starts.append((si, 'c1', sg.c1))
                            if sg.c2:
                                handle_starts.append((si, 'c2', sg.c2))
                    label_start = self._part_label_world_pos(part)
                    self._push_undo()
                    self.drag = ('part', part_id, (event.x, event.y),
                                 starts, handle_starts, label_start)
                self.redraw()
            elif kind == 'segment':
                idx = hit[1]
                if shift:
                    self._toggle_segment(idx)
                else:
                    self._select_only_segment(idx)
                self.drag = None
                self.redraw()

        elif mode == 'point':
            snap = self._compute_snap(event.x, event.y)
            if snap['point_id'] is not None:
                # Click landed on an existing point: just select it instead
                # of placing a duplicate.
                self._select_only_point(snap['point_id'])
                self.redraw()
            elif snap['segment_idx'] is not None:
                self._push_undo()
                pid = self._split_segment_at(
                    snap['segment_idx'], snap['wx'], snap['wy'],
                    snap['segment_t'], snap['segment_kind'])
                self._select_only_point(pid)
                self.dirty = True
                self.redraw()
            else:
                self._push_undo()
                pid = self.pattern.add_point(snap['wx'], snap['wy']).id
                self._select_only_point(pid)
                self.dirty = True
                self.redraw()

        elif mode in ('line', 'curve'):
            pushed = False
            snap = self._compute_snap(event.x, event.y)
            if snap['point_id'] is not None:
                pid = snap['point_id']
            else:
                self._push_undo(); pushed = True
                if snap['segment_idx'] is not None:
                    pid = self._split_segment_at(
                        snap['segment_idx'], snap['wx'], snap['wy'],
                        snap['segment_t'], snap['segment_kind'])
                else:
                    pid = self.pattern.add_point(snap['wx'], snap['wy']).id
                self.dirty = True
            if self.pending_a is None:
                self.pending_a = pid
            else:
                if pid != self.pending_a:
                    if not pushed:
                        self._push_undo()
                    if mode == 'line':
                        idx = self.pattern.add_line(self.pending_a, pid)
                    else:
                        idx = self.pattern.add_curve(self.pending_a, pid)
                    self._select_only_segment(idx)
                    self.dirty = True
                self.pending_a = None
            self.redraw()

    def on_left_drag(self, event):
        if not self.drag:
            return
        kind = self.drag[0]
        if kind == 'point_group':
            _, (start_sx, start_sy), starts, handle_starts = self.drag
            # screen delta -> world delta
            ppc = self.ppc()
            dx_world = (event.x - start_sx) / ppc
            dy_world = -(event.y - start_sy) / ppc
            for pid, (x0, y0) in starts.items():
                p = self.pattern.points.get(pid)
                if p:
                    p.x = x0 + dx_world
                    p.y = y0 + dy_world
            for seg_idx, which, (h0x, h0y) in handle_starts:
                if seg_idx < len(self.pattern.segments):
                    seg = self.pattern.segments[seg_idx]
                    new_xy = (h0x + dx_world, h0y + dy_world)
                    if which == 'c1':
                        seg.c1 = new_xy
                    else:
                        seg.c2 = new_xy
            self.dirty = True
            self.redraw()
        elif kind == 'handle':
            _, idx, which = self.drag
            wx, wy = self.screen_to_world(event.x, event.y)
            seg = self.pattern.segments[idx]
            if which == 1:
                seg.c1 = (wx, wy)
            else:
                seg.c2 = (wx, wy)
            self.dirty = True
            self.redraw()
        elif kind == 'part_label':
            _, part_id, (start_sx, start_sy), (start_wx, start_wy) = self.drag
            ppc = self.ppc()
            dx_world = (event.x - start_sx) / ppc
            dy_world = -(event.y - start_sy) / ppc
            part = next((p for p in self.pattern.parts if p.id == part_id), None)
            if part is not None:
                part.label_pos = (start_wx + dx_world, start_wy + dy_world)
                self.dirty = True
                self.redraw()
        elif kind == 'part':
            _, part_id, (start_sx, start_sy), starts, handle_starts, label_start = self.drag
            ppc = self.ppc()
            dx_world = (event.x - start_sx) / ppc
            dy_world = -(event.y - start_sy) / ppc
            for pid, (x0, y0) in starts.items():
                p = self.pattern.points.get(pid)
                if p:
                    p.x = x0 + dx_world
                    p.y = y0 + dy_world
            for seg_idx, which, (h0x, h0y) in handle_starts:
                if seg_idx < len(self.pattern.segments):
                    seg = self.pattern.segments[seg_idx]
                    new_xy = (h0x + dx_world, h0y + dy_world)
                    if which == 'c1':
                        seg.c1 = new_xy
                    else:
                        seg.c2 = new_xy
            if label_start is not None:
                part = next((p for p in self.pattern.parts if p.id == part_id), None)
                if part is not None and part.label_pos is not None:
                    part.label_pos = (label_start[0] + dx_world,
                                      label_start[1] + dy_world)
            self.dirty = True
            self.redraw()
        elif kind == 'rubber':
            self.redraw()

    def on_left_release(self, event):
        if self.drag and self.drag[0] == 'rubber':
            _, (sx0, sy0), additive = self.drag
            self.drag = None
            sx1, sy1 = event.x, event.y
            # If the rect is tiny, treat as a click on empty space (already deselected if not shift)
            if abs(sx1 - sx0) <= self.DRAG_THRESHOLD_PX and abs(sy1 - sy0) <= self.DRAG_THRESHOLD_PX:
                self.redraw()
                return
            x1, y1 = min(sx0, sx1), min(sy0, sy1)
            x2, y2 = max(sx0, sx1), max(sy0, sy1)
            picked = set()
            for p in self.pattern.points.values():
                psx, psy = self.world_to_screen(p.x, p.y)
                if x1 <= psx <= x2 and y1 <= psy <= y2:
                    picked.add(p.id)
            if additive:
                self.selected_points |= picked
            else:
                self.selected_points = picked
                self.selected_segments.clear()
                self.selected_part = None
            self.redraw()
        else:
            self.drag = None

    def on_right_press(self, event):
        """Pop up a context menu whose items depend on the current selection.
        If the right-click lands on something not selected, that item is
        selected first so the menu reflects what the user clicked."""
        hit = self._hit_test(event.x, event.y)
        if hit:
            kind = hit[0]
            if kind == 'point' and hit[1] not in self.selected_points:
                self._select_only_point(hit[1])
                self.redraw()
            elif kind == 'segment' and hit[1] not in self.selected_segments:
                self._select_only_segment(hit[1])
                self.redraw()
            elif kind == 'part_label':
                self._select_part(hit[1])
                self.redraw()

        menu = tk.Menu(self.root, tearoff=0)
        n_pts = len(self.selected_points)
        n_segs = len(self.selected_segments)

        if self.selected_part is not None and n_pts == 0 and n_segs == 0:
            part_id = self.selected_part
            part = next((p for p in self.pattern.parts if p.id == part_id), None)
            if part:
                menu.add_command(label="Resize part...",
                                 command=lambda pid=part_id: self.resize_part_dialog(pid))
                menu.add_command(label="Rotate part...",
                                 command=lambda pid=part_id: self.rotate_part_dialog(pid))
                menu.add_command(label="Mirror part...",
                                 command=lambda pid=part_id: self.mirror_part_dialog(pid))
                menu.add_command(label="Duplicate part",
                                 command=lambda pid=part_id: self.duplicate_part_dialog(pid))
                gl_label = ("Edit grain line..." if part.grain_line is not None
                            else "Add grain line...")
                menu.add_command(label=gl_label,
                                 command=lambda pid=part_id: self.grain_line_dialog(pid))
                if part.label_pos is not None:
                    menu.add_command(label="Reset label position",
                                     command=lambda: self._reset_part_label_pos(part_id))
                menu.add_separator()
                menu.add_command(label="Delete part (keeps segments)",
                                 command=lambda: self._delete_part(part_id))
        elif n_pts == 1 and n_segs == 0:
            pid_only = next(iter(self.selected_points))
            menu.add_command(label="Add dart at this point...",
                             command=self.add_dart_dialog)
            menu.add_command(label="Move to location along line...",
                             command=self.move_point_along_line_dialog)
            # SA override applies to adjacent boundary segments
            n_incident = sum(1 for s in self.pattern.segments
                             if (s.a == pid_only or s.b == pid_only)
                             and s.style == 'solid')
            if n_incident:
                menu.add_command(
                    label=f"Override seam allowance on adjacent edge(s)...",
                    command=lambda p=pid_only: self.override_sa_for_point(p))
            menu.add_separator()
            menu.add_command(label="Delete point", command=self.delete_selected)
        elif n_pts == 0 and n_segs == 1:
            idx = next(iter(self.selected_segments))
            seg = self.pattern.segments[idx]
            if seg.style == 'solid':
                menu.add_command(label="Mark as dotted (dart / fold line)",
                                 command=lambda: self._set_selected_segment_style('dotted'))
                menu.add_command(
                    label="Override seam allowance for this edge...",
                    command=lambda i=idx: self.override_segments_sa_dialog([i]))
            else:
                menu.add_command(label="Mark as solid",
                                 command=lambda: self._set_selected_segment_style('solid'))
            menu.add_command(label="Split at midpoint",
                             command=lambda i=idx: self._split_at_midpoint(i))
            menu.add_command(label="Add notch here",
                             command=lambda i=idx, ex=event.x, ey=event.y:
                                 self._add_notch_at(i, ex, ey))
            seam_lbl = ("Edit seam label..." if seg.seam_label
                        else "Set seam label...")
            menu.add_command(label=seam_lbl,
                             command=lambda i=idx: self.seam_label_dialog([i]))
            if seg.kind == 'curve':
                menu.add_command(label="Reset curve handles",
                                 command=lambda i=idx: self._reset_curve_handles(i))
            menu.add_separator()
            menu.add_command(label="Delete segment", command=self.delete_selected)
        elif n_pts + n_segs >= 2:
            menu.add_command(label="Create part from selection...",
                             command=self.create_part_dialog)
            if n_pts >= 2 and n_segs == 0:
                menu.add_command(label="Resize selection...",
                                 command=self.resize_selection_dialog)
            if n_pts == 4 and n_segs == 0:
                menu.add_command(label="Square as rectangle...",
                                 command=self.square_selection_as_rectangle)
            solid_seg_ids = [i for i in self.selected_segments
                             if i < len(self.pattern.segments)
                             and self.pattern.segments[i].style == 'solid']
            if solid_seg_ids:
                menu.add_command(
                    label=f"Override SA on {len(solid_seg_ids)} selected edge(s)...",
                    command=lambda ids=list(solid_seg_ids):
                        self.override_segments_sa_dialog(ids))
            if n_segs == 2 and n_pts == 0:
                menu.add_command(
                    label="Mark as joined seam...",
                    command=lambda ids=list(self.selected_segments):
                        self.seam_label_dialog(ids, add_notches=True))
            menu.add_separator()
            menu.add_command(label="Delete selection", command=self.delete_selected)
        else:
            menu.add_command(label="Add point here",
                             command=lambda: self._add_point_at_screen(event.x, event.y))

        menu.add_separator()
        if self._undo_stack:
            menu.add_command(label="Undo", command=self.undo)
        if self._redo_stack:
            menu.add_command(label="Redo", command=self.redo)

        try:
            menu.tk_popup(event.x_root, event.y_root)
        finally:
            menu.grab_release()

    def _split_at_midpoint(self, seg_idx):
        if seg_idx >= len(self.pattern.segments):
            return
        seg = self.pattern.segments[seg_idx]
        pa = self.pattern.points[seg.a]; pb = self.pattern.points[seg.b]
        if seg.kind == 'line':
            wx = (pa.x + pb.x) / 2; wy = (pa.y + pb.y) / 2
            self._push_undo()
            self._split_segment_at(seg_idx, wx, wy, 0.5, 'line')
        else:
            pts = cubic_bezier_samples((pa.x, pa.y), seg.c1, seg.c2, (pb.x, pb.y), n=128)
            wx, wy = pts[64]
            self._push_undo()
            self._split_segment_at(seg_idx, wx, wy, 0.5, 'curve')
        self.dirty = True
        self.redraw()

    def _add_notch_at(self, seg_idx, sx, sy):
        if seg_idx >= len(self.pattern.segments):
            return
        seg = self.pattern.segments[seg_idx]
        # Find the parameter t closest to the click on this segment
        best_t = 0.5; best_d = float('inf')
        N = 64
        for i in range(N + 1):
            t = i / N
            wx, wy, _, _ = segment_point_and_tangent(seg, self.pattern.points, t)
            psx, psy = self.world_to_screen(wx, wy)
            d = math.hypot(psx - sx, psy - sy)
            if d < best_d:
                best_d = d; best_t = t
        self._push_undo()
        self.pattern.notches.append(Notch(segment_id=seg_idx, t=best_t))
        self.dirty = True
        self.redraw()
        self._set_status("Notch added.")

    def _add_point_at_screen(self, sx, sy):
        self._push_undo()
        split = self._find_segment_to_split(sx, sy)
        if split:
            seg_idx, wx, wy, t, kind = split
            pid = self._split_segment_at(seg_idx, wx, wy, t, kind)
        else:
            wx, wy = self.screen_to_world(sx, sy)
            pid = self.pattern.add_point(wx, wy).id
        self._select_only_point(pid)
        self.dirty = True
        self.redraw()

    def on_middle_press(self, event):
        self._pan_anchor = (event.x, event.y, self.pan_x, self.pan_y)

    def on_middle_drag(self, event):
        if not self._pan_anchor:
            return
        ax, ay, px, py = self._pan_anchor
        self.pan_x = px + (event.x - ax)
        self.pan_y = py + (event.y - ay)
        self.redraw()

    def on_wheel_zoom(self, event):
        factor = 1.1 if event.delta > 0 else 1 / 1.1
        self.zoom_at((event.x, event.y), factor)

    def on_wheel_pan_v(self, event):
        # delta = 120 per notch on Windows; trackpad sends smaller continuous values
        self.pan_y += event.delta * 0.5
        self.redraw()

    def on_wheel_pan_h(self, event):
        self.pan_x += event.delta * 0.5
        self.redraw()

    def zoom_at(self, screen_xy, factor):
        sx, sy = screen_xy
        wx, wy = self.screen_to_world(sx, sy)
        self.zoom = max(0.05, min(20.0, self.zoom * factor))
        self.pan_x = sx - wx * self.ppc()
        self.pan_y = sy + wy * self.ppc()
        self.redraw()

    def zoom_fit(self):
        if not self.pattern.points:
            return
        xs = [p.x for p in self.pattern.points.values()]
        ys = [p.y for p in self.pattern.points.values()]
        for seg in self.pattern.segments:
            if seg.kind == 'curve':
                pa = self.pattern.points[seg.a]; pb = self.pattern.points[seg.b]
                for x, y in cubic_bezier_samples((pa.x, pa.y), seg.c1, seg.c2, (pb.x, pb.y), n=24):
                    xs.append(x); ys.append(y)
        minx, maxx = min(xs), max(xs); miny, maxy = min(ys), max(ys)
        pad = 2.0
        w_cm = (maxx - minx) + 2 * pad; h_cm = (maxy - miny) + 2 * pad
        cw = max(50, self.canvas.winfo_width()); ch = max(50, self.canvas.winfo_height())
        zoom = min(cw / (w_cm * self.PPC_DEFAULT), ch / (h_cm * self.PPC_DEFAULT))
        self.zoom = max(0.05, min(20.0, zoom))
        cx = (minx + maxx) / 2; cy = (miny + maxy) / 2
        self.pan_x = cw / 2 - cx * self.ppc()
        self.pan_y = ch / 2 + cy * self.ppc()
        self.redraw()

    def reset_view(self):
        self.zoom = 1.0
        self._center_origin()

    # ---- commands ----

    def construct_line_dialog(self):
        if not self.pattern.points:
            messagebox.showinfo("Construct line", "Add at least one point first.")
            return
        dlg = ConstructLineDialog(self.root, self.pattern)
        self.root.wait_window(dlg.top)
        if not dlg.result:
            return
        self._push_undo()
        mode = dlg.result[0]
        from_id = dlg.result[1]
        pa = self.pattern.points[from_id]
        new_label = dlg.result[-1]
        if mode == 'offset':
            _, _, dx, dy, _ = dlg.result
            pb = self.pattern.add_point(pa.x + dx, pa.y + dy,
                                        label=(new_label.strip() or None))
        else:
            _, _, angle_deg, length, _ = dlg.result
            angle = math.radians(angle_deg)
            pb = self.pattern.add_point(
                pa.x + math.cos(angle) * length,
                pa.y + math.sin(angle) * length,
                label=(new_label.strip() or None))
        idx = self.pattern.add_line(from_id, pb.id)
        self._select_only_segment(idx)
        self.dirty = True; self.redraw()

    def create_part_dialog(self):
        # gather candidate segments
        seg_ids = list(self.selected_segments)
        if not seg_ids and self.selected_points:
            # infer: any segment whose both endpoints are in selected points
            seg_ids = [i for i, s in enumerate(self.pattern.segments)
                       if s.a in self.selected_points and s.b in self.selected_points]
        if not seg_ids:
            messagebox.showinfo(
                "Create part",
                "Select the segments that form the part's outline first "
                "(or select all its points and use this command).",
            )
            return
        dlg = NamePartDialog(self.root, default_name=f"Part {len(self.pattern.parts) + 1}",
                             default_sa=0.0, n_segs=len(seg_ids))
        self.root.wait_window(dlg.top)
        if not dlg.result:
            return
        name, sa = dlg.result
        self._push_undo()

        # Determine whether any selected segment already belongs to a part.
        owned_seg_ids = set()
        for p in self.pattern.parts:
            owned_seg_ids.update(p.segment_ids)
        any_owned = any(si in owned_seg_ids for si in seg_ids)

        if any_owned:
            # Source geometry is already part of another piece — produce an
            # independent copy offset to the side so both are visible.
            xs = []
            for si in seg_ids:
                if si < len(self.pattern.segments):
                    s = self.pattern.segments[si]
                    for pid in (s.a, s.b):
                        p = self.pattern.points.get(pid)
                        if p:
                            xs.append(p.x)
            width = (max(xs) - min(xs)) if xs else 10.0
            offset = width + 2.0

            def transform(x, y, _o=offset):
                return (x + _o, y)
            _pmap, seg_map = self._copy_segment_set(seg_ids, transform)
            new_seg_ids = [seg_map[i] for i in seg_ids if i in seg_map]
            part = self.pattern.add_part(name=name, segment_ids=new_seg_ids,
                                         seam_allowance=sa)
            self._set_status(f"Created '{name}' as an independent copy.")
        else:
            # Pure loose draft — claim it directly into the part (no copy).
            part = self.pattern.add_part(name=name, segment_ids=seg_ids,
                                         seam_allowance=sa)
            self._set_status(f"Created part '{name}'.")

        self._select_part(part.id)
        self.dirty = True
        self.redraw()

    def move_point_along_line_dialog(self):
        if len(self.selected_points) != 1 or self.selected_segments:
            return
        pid = next(iter(self.selected_points))
        dlg = MovePointAlongLineDialog(self.root, self.pattern, pid)
        if dlg.top is None:
            return
        self.root.wait_window(dlg.top)
        if not dlg.result:
            return
        other_id, dist = dlg.result
        p = self.pattern.points[pid]
        other = self.pattern.points[other_id]
        dx = p.x - other.x; dy = p.y - other.y
        d = math.hypot(dx, dy) or 1.0
        self._push_undo()
        old_x, old_y = p.x, p.y
        p.x = other.x + dx / d * dist
        p.y = other.y + dy / d * dist
        delta_x = p.x - old_x; delta_y = p.y - old_y
        # If this point anchors a dart, slide the dart's own points by the
        # same delta so the dart shape moves with its anchor.
        dart = self.pattern.find_dart_by_anchor(pid)
        if dart:
            for dp_id in dart.dart_only_ids():
                dp = self.pattern.points.get(dp_id)
                if dp:
                    dp.x += delta_x
                    dp.y += delta_y
        self.dirty = True
        self.redraw()
        self._set_status(f"Moved {p.label} to {dist:.2f} cm from {other.label}.")

    def add_dart_dialog(self):
        if len(self.selected_points) != 1 or self.selected_segments:
            messagebox.showinfo(
                "Add dart",
                "Select exactly one point on a boundary first "
                "(no segments selected).",
            )
            return
        pid = next(iter(self.selected_points))
        dlg = AddDartDialog(self.root, self.pattern, pid)
        if dlg.top is None:
            return
        self.root.wait_window(dlg.top)
        if not dlg.result:
            return
        depth, width, direction = dlg.result
        anchor = self.pattern.points[pid]

        incident = [(i, s) for i, s in enumerate(self.pattern.segments)
                    if (s.a == pid or s.b == pid) and s.style == 'solid']
        # Tangent along boundary at anchor
        if len(incident) == 1:
            s = incident[0][1]
            other_id = s.b if s.a == pid else s.a
            other = self.pattern.points[other_id]
            tx = other.x - anchor.x; ty = other.y - anchor.y
        else:
            # Two (or more) incident solid segments — use the chord between the
            # two "other" endpoints as the local boundary direction. For a
            # collinear mid-edge point this is the boundary itself; for a corner
            # it spans across the corner.
            s1, s2 = incident[0][1], incident[1][1]
            o1 = s1.b if s1.a == pid else s1.a
            o2 = s2.b if s2.a == pid else s2.a
            p1 = self.pattern.points[o1]; p2 = self.pattern.points[o2]
            tx = p2.x - p1.x; ty = p2.y - p1.y
        tlen = math.hypot(tx, ty) or 1.0
        tx /= tlen; ty /= tlen
        # right-hand perpendicular as initial normal candidate
        nx, ny = ty, -tx

        # Orient the normal toward the part's interior. Use a point-in-polygon
        # test on the part's actual closed boundary rather than a centroid
        # heuristic — robust for L-shaped and concave parts.
        containing_part = next(
            (p for p in self.pattern.parts
             if any(idx in p.segment_ids for idx, _ in incident)),
            None,
        )
        if containing_part:
            part_segs = [self.pattern.segments[i] for i in containing_part.segment_ids
                         if i < len(self.pattern.segments)
                         and self.pattern.segments[i].style == 'solid']
            chain = chain_segments_into_loop(part_segs)
            if chain:
                poly = polyline_of_chain(chain, self.pattern.points, samples_per_curve=32)
                test_d = 0.5  # cm — small probe inward of the boundary
                # Two candidate normals at the anchor
                pos_pt = (anchor.x + nx * test_d, anchor.y + ny * test_d)
                neg_pt = (anchor.x - nx * test_d, anchor.y - ny * test_d)
                pos_in = point_in_polygon(pos_pt[0], pos_pt[1], poly)
                neg_in = point_in_polygon(neg_pt[0], neg_pt[1], poly)
                if neg_in and not pos_in:
                    nx, ny = -nx, -ny
                # If both or neither, leave the right-hand default — user can flip.
        # nx, ny now points "internal". External is the opposite.
        if direction == 'external':
            nx, ny = -nx, -ny

        self._push_undo()
        mouth_a = self.pattern.add_point(anchor.x + tx * (width / 2),
                                         anchor.y + ty * (width / 2))
        apex = self.pattern.add_point(anchor.x + nx * depth,
                                      anchor.y + ny * depth)
        mouth_b = self.pattern.add_point(anchor.x - tx * (width / 2),
                                         anchor.y - ty * (width / 2))
        i1 = self.pattern.add_line(mouth_a.id, apex.id)
        i2 = self.pattern.add_line(apex.id, mouth_b.id)
        self.pattern.segments[i1].style = 'dotted'
        self.pattern.segments[i2].style = 'dotted'
        # Record the four-point dart so it can be moved as a group with its anchor
        self.pattern.add_dart(anchor_id=pid,
                              mouth_a_id=mouth_a.id,
                              apex_id=apex.id,
                              mouth_b_id=mouth_b.id)

        self._clear_selection()
        self.selected_segments.update([i1, i2])
        self.dirty = True
        self.redraw()
        self._set_status(f"Dart added at point {anchor.label}.")

    def draw_rectangle_dialog(self):
        """Create a fresh rectangle (4 points + 4 lines). If exactly one
        point is selected, uses it as the bottom-left corner; otherwise
        centres the rectangle at the current view's centre."""
        # Default dimensions: nice round numbers
        default_w, default_h = 20.0, 30.0
        anchor = None
        if len(self.selected_points) == 1 and not self.selected_segments:
            pid = next(iter(self.selected_points))
            anchor = self.pattern.points.get(pid)
        dlg = RectangleDialog(self.root, default_w, default_h,
                              title="Draw rectangle")
        self.root.wait_window(dlg.top)
        if not dlg.result:
            return
        w, h = dlg.result

        self._push_undo()
        if anchor:
            bl_x, bl_y = anchor.x, anchor.y
            bl = anchor
        else:
            # Centre on the current view's middle, snapped to 0.1 cm
            cw = max(50, self.canvas.winfo_width())
            ch = max(50, self.canvas.winfo_height())
            wx, wy = self.screen_to_world(cw / 2, ch / 2)
            bl_x = round(wx - w / 2, 1)
            bl_y = round(wy - h / 2, 1)
            bl = self.pattern.add_point(bl_x, bl_y)
        br = self.pattern.add_point(bl_x + w, bl_y)
        tr = self.pattern.add_point(bl_x + w, bl_y + h)
        tl = self.pattern.add_point(bl_x, bl_y + h)
        self.pattern.add_line(bl.id, br.id)
        self.pattern.add_line(br.id, tr.id)
        self.pattern.add_line(tr.id, tl.id)
        self.pattern.add_line(tl.id, bl.id)

        self._clear_selection()
        self.selected_points = {bl.id, br.id, tr.id, tl.id}
        self.dirty = True
        self.redraw()
        self._set_status(f"Drew {w:g}×{h:g} cm rectangle.")

    def _scale_point_set(self, point_ids, new_w, new_h, part=None):
        """Scale every point in `point_ids` around the centroid of that set
        to a bounding box of new_w × new_h. Carries curve handles (for any
        segment whose both endpoints are in the set) and an optional part's
        label_pos. Returns True on success."""
        # Pull in dart points whose anchor is in the set so attached darts
        # scale rigidly with the boundary they live on.
        ids = set(point_ids)
        for pid in list(ids):
            dart = self.pattern.find_dart_by_anchor(pid)
            if dart:
                for dp_id in dart.dart_only_ids():
                    ids.add(dp_id)

        pts = [self.pattern.points[pid] for pid in ids
               if pid in self.pattern.points]
        if not pts:
            return False
        minx = min(p.x for p in pts); maxx = max(p.x for p in pts)
        miny = min(p.y for p in pts); maxy = max(p.y for p in pts)
        cur_w = max(1e-6, maxx - minx)
        cur_h = max(1e-6, maxy - miny)
        sx = new_w / cur_w
        sy = new_h / cur_h
        cx = (minx + maxx) / 2
        cy = (miny + maxy) / 2

        self._push_undo()
        for pid in ids:
            p = self.pattern.points.get(pid)
            if p:
                p.x = cx + (p.x - cx) * sx
                p.y = cy + (p.y - cy) * sy
        # Curve handles: scale when both endpoints scaled together
        for seg in self.pattern.segments:
            if seg.kind != 'curve':
                continue
            if seg.a in ids and seg.b in ids:
                if seg.c1:
                    seg.c1 = (cx + (seg.c1[0] - cx) * sx,
                              cy + (seg.c1[1] - cy) * sy)
                if seg.c2:
                    seg.c2 = (cx + (seg.c2[0] - cx) * sx,
                              cy + (seg.c2[1] - cy) * sy)
        if part is not None and part.label_pos is not None:
            lx, ly = part.label_pos
            part.label_pos = (cx + (lx - cx) * sx, cy + (ly - cy) * sy)
        if part is not None and part.grain_line is not None:
            gx1, gy1, gx2, gy2 = part.grain_line
            part.grain_line = (cx + (gx1 - cx) * sx, cy + (gy1 - cy) * sy,
                               cx + (gx2 - cx) * sx, cy + (gy2 - cy) * sy)
        self.dirty = True
        self.redraw()
        return True

    def _part_point_ids(self, part):
        """All point ids belonging to a part: boundary endpoints plus the
        own points of any dart anchored on the boundary."""
        pids = set()
        for sid in part.segment_ids:
            if sid < len(self.pattern.segments):
                s = self.pattern.segments[sid]
                pids.add(s.a); pids.add(s.b)
        for pid in list(pids):
            dart = self.pattern.find_dart_by_anchor(pid)
            if dart:
                pids.update(dart.dart_only_ids())
        return pids

    def _part_bbox(self, part):
        """World-space (minx, miny, maxx, maxy) of a part, including curve
        samples so the bulge counts. Returns None if empty."""
        pts = []
        for pid in self._part_point_ids(part):
            p = self.pattern.points.get(pid)
            if p:
                pts.append((p.x, p.y))
        for sid in part.segment_ids:
            if sid < len(self.pattern.segments):
                s = self.pattern.segments[sid]
                if s.kind == 'curve':
                    pa = self.pattern.points[s.a]; pb = self.pattern.points[s.b]
                    pts.extend(cubic_bezier_samples(
                        (pa.x, pa.y), s.c1, s.c2, (pb.x, pb.y), n=24))
        if not pts:
            return None
        return (min(p[0] for p in pts), min(p[1] for p in pts),
                max(p[0] for p in pts), max(p[1] for p in pts))

    def grain_line_dialog(self, part_id=None):
        if part_id is None:
            part_id = self.selected_part
        if part_id is None:
            messagebox.showinfo("Grain line",
                                "Select a part first (Parts tab on the right).")
            return
        part = next((p for p in self.pattern.parts if p.id == part_id), None)
        if part is None:
            return
        bbox = self._part_bbox(part)
        if bbox is None:
            return
        # Sensible defaults from existing grain line or the part's height
        if part.grain_line is not None:
            gx1, gy1, gx2, gy2 = part.grain_line
            cur_angle = math.degrees(math.atan2(gy2 - gy1, gx2 - gx1))
            cur_len = math.hypot(gx2 - gx1, gy2 - gy1)
        else:
            cur_angle = 90.0  # vertical is the usual grain direction
            cur_len = 0.7 * (bbox[3] - bbox[1])
        dlg = GrainLineDialog(self.root, cur_angle, cur_len,
                              part.grain_line is not None)
        self.root.wait_window(dlg.top)
        if dlg.result is None:
            return
        self._push_undo()
        if dlg.result[0] == 'remove':
            part.grain_line = None
            self._set_status(f"Removed grain line from '{part.name}'.")
        else:
            _, angle, length = dlg.result
            cx = (bbox[0] + bbox[2]) / 2
            cy = (bbox[1] + bbox[3]) / 2
            rad = math.radians(angle)
            hx = math.cos(rad) * length / 2
            hy = math.sin(rad) * length / 2
            part.grain_line = (cx - hx, cy - hy, cx + hx, cy + hy)
            self._set_status(f"Set grain line on '{part.name}'.")
        self.dirty = True
        self.redraw()

    def duplicate_part_dialog(self, part_id=None):
        if part_id is None:
            part_id = self.selected_part
        if part_id is None:
            messagebox.showinfo("Duplicate part",
                                "Select a part first.")
            return
        part = next((p for p in self.pattern.parts if p.id == part_id), None)
        if part is None:
            return
        bbox = self._part_bbox(part)
        if bbox is None:
            return
        offset = (bbox[2] - bbox[0]) + 2.0  # shift right by width + 2 cm
        self._push_undo()
        new_part = self._clone_part(part, dx=offset, dy=0.0,
                                    mirror_axis=None,
                                    new_name=f"{part.name} (copy)")
        self._select_part(new_part.id)
        self.dirty = True
        self.redraw()
        self._set_status(f"Duplicated '{part.name}'.")

    def mirror_part_dialog(self, part_id=None):
        if part_id is None:
            part_id = self.selected_part
        if part_id is None:
            messagebox.showinfo("Mirror part", "Select a part first.")
            return
        part = next((p for p in self.pattern.parts if p.id == part_id), None)
        if part is None:
            return
        bbox = self._part_bbox(part)
        if bbox is None:
            return
        dlg = MirrorPartDialog(self.root, part.name)
        self.root.wait_window(dlg.top)
        if dlg.result is None:
            return
        axis, keep_original, new_name = dlg.result
        self._push_undo()
        # Mirror axis position: reflect across the chosen bbox edge so the
        # mirrored copy sits flush against the original along that edge.
        minx, miny, maxx, maxy = bbox
        if axis in ('left', 'right'):
            axis_x = maxx if axis == 'right' else minx
            new_part = self._clone_part(part, mirror_axis=('x', axis_x),
                                        new_name=new_name)
        else:
            axis_y = maxy if axis == 'top' else miny
            new_part = self._clone_part(part, mirror_axis=('y', axis_y),
                                        new_name=new_name)
        if not keep_original:
            self._delete_part_and_geometry(part_id)
        self._select_part(new_part.id)
        self.dirty = True
        self.redraw()
        self._set_status(f"Mirrored '{part.name}'.")

    def _copy_segment_set(self, seg_ids, transform):
        """Deep-copy a set of segments (and their endpoint points, plus any
        dart segments/darts and notches involving them) into fresh geometry,
        applying `transform(x, y) -> (x, y)` to every coordinate. Returns
        (pid_map, seg_map) mapping old ids/indices to new ones."""
        seg_ids = set(seg_ids)
        # Gather all endpoint point ids
        old_pids = set()
        for si in seg_ids:
            if si < len(self.pattern.segments):
                s = self.pattern.segments[si]
                old_pids.add(s.a); old_pids.add(s.b)
        # Pull in dart-own points whose anchor is among these points, and the
        # dart's two dotted segments, so darts copy intact.
        for pid in list(old_pids):
            dart = self.pattern.find_dart_by_anchor(pid)
            if dart:
                old_pids.update(dart.dart_only_ids())
        # Any segment whose both endpoints are now in old_pids (e.g. dart legs)
        for si, s in enumerate(self.pattern.segments):
            if s.a in old_pids and s.b in old_pids:
                seg_ids.add(si)

        pid_map = {}
        for old_pid in old_pids:
            op = self.pattern.points.get(old_pid)
            if not op:
                continue
            nx, ny = transform(op.x, op.y)
            pid_map[old_pid] = self.pattern.add_point(nx, ny).id

        seg_map = {}
        for old_si in sorted(seg_ids):
            if old_si >= len(self.pattern.segments):
                continue
            s = self.pattern.segments[old_si]
            if s.a not in pid_map or s.b not in pid_map:
                continue
            new_seg = Segment(
                kind=s.kind, a=pid_map[s.a], b=pid_map[s.b],
                c1=transform(*s.c1) if s.c1 else None,
                c2=transform(*s.c2) if s.c2 else None,
                style=s.style,
                seam_allowance=s.seam_allowance,
                length_locked=s.length_locked,
                seam_label=s.seam_label,
            )
            self.pattern.segments.append(new_seg)
            seg_map[old_si] = len(self.pattern.segments) - 1

        for dart in self.pattern.darts:
            ids = dart.all_point_ids()
            if all(i in pid_map for i in ids):
                self.pattern.add_dart(
                    anchor_id=pid_map[dart.anchor_id],
                    mouth_a_id=pid_map[dart.mouth_a_id],
                    apex_id=pid_map[dart.apex_id],
                    mouth_b_id=pid_map[dart.mouth_b_id],
                )

        for notch in self.pattern.notches:
            if notch.segment_id in seg_map:
                self.pattern.notches.append(Notch(
                    segment_id=seg_map[notch.segment_id], t=notch.t))

        return pid_map, seg_map

    def _clone_part(self, part, dx=0.0, dy=0.0, mirror_axis=None, new_name=None):
        """Deep-copy a part's geometry with an optional translation or
        mirror transform. Returns the new Part. `mirror_axis` is
        ('x', x0) to reflect across the vertical line x=x0, or ('y', y0)
        for the horizontal line y=y0."""
        def transform(x, y):
            if mirror_axis is not None:
                kind, v = mirror_axis
                if kind == 'x':
                    x = 2 * v - x
                else:
                    y = 2 * v - y
            return (x + dx, y + dy)

        _pid_map, seg_map = self._copy_segment_set(part.segment_ids, transform)

        new_label_pos = None
        if part.label_pos is not None:
            new_label_pos = transform(*part.label_pos)
        new_grain = None
        if part.grain_line is not None:
            gx1, gy1, gx2, gy2 = part.grain_line
            t1 = transform(gx1, gy1); t2 = transform(gx2, gy2)
            new_grain = (t1[0], t1[1], t2[0], t2[1])

        new_seg_ids = [seg_map[i] for i in part.segment_ids if i in seg_map]
        new_part = self.pattern.add_part(
            name=new_name or f"{part.name} (copy)",
            segment_ids=new_seg_ids,
            seam_allowance=part.seam_allowance)
        new_part.label_pos = new_label_pos
        new_part.grain_line = new_grain
        return new_part

    def _delete_part_and_geometry(self, part_id):
        """Delete a part AND its geometry (points + segments), unlike
        _delete_part which keeps the segments."""
        part = next((p for p in self.pattern.parts if p.id == part_id), None)
        if part is None:
            return
        pids = self._part_point_ids(part)
        self.pattern.remove_part(part_id)
        for pid in pids:
            self.pattern.remove_point(pid)
        if self.selected_part == part_id:
            self.selected_part = None

    def rotate_part_dialog(self, part_id=None):
        if part_id is None:
            part_id = self.selected_part
        if part_id is None:
            messagebox.showinfo("Rotate part",
                                "Select a part first (Parts tab on the right).")
            return
        part = next((p for p in self.pattern.parts if p.id == part_id), None)
        if part is None:
            return
        # Gather part's boundary points + attached dart points
        pids = set()
        for sid in part.segment_ids:
            if sid < len(self.pattern.segments):
                s = self.pattern.segments[sid]
                pids.add(s.a); pids.add(s.b)
        for pid in list(pids):
            dart = self.pattern.find_dart_by_anchor(pid)
            if dart:
                pids.update(dart.dart_only_ids())
        pts = [self.pattern.points[pid] for pid in pids
               if pid in self.pattern.points]
        if not pts:
            return
        cx = sum(p.x for p in pts) / len(pts)
        cy = sum(p.y for p in pts) / len(pts)

        dlg = RotatePartDialog(self.root, part.name)
        self.root.wait_window(dlg.top)
        if dlg.result is None:
            return
        theta = math.radians(dlg.result)
        cos_t = math.cos(theta); sin_t = math.sin(theta)

        def rot(x, y):
            dx = x - cx; dy = y - cy
            return (cx + dx * cos_t - dy * sin_t,
                    cy + dx * sin_t + dy * cos_t)

        self._push_undo()
        for pid in pids:
            p = self.pattern.points.get(pid)
            if p:
                p.x, p.y = rot(p.x, p.y)
        for seg in self.pattern.segments:
            if seg.kind != 'curve':
                continue
            if seg.a in pids and seg.b in pids:
                if seg.c1: seg.c1 = rot(*seg.c1)
                if seg.c2: seg.c2 = rot(*seg.c2)
        if part.label_pos is not None:
            part.label_pos = rot(*part.label_pos)
        if part.grain_line is not None:
            gx1, gy1, gx2, gy2 = part.grain_line
            r1 = rot(gx1, gy1); r2 = rot(gx2, gy2)
            part.grain_line = (r1[0], r1[1], r2[0], r2[1])
        self.dirty = True
        self.redraw()
        self._set_status(f"Rotated '{part.name}' by {dlg.result:g}°.")

    def resize_part_dialog(self, part_id=None):
        if part_id is None:
            part_id = self.selected_part
        if part_id is None:
            messagebox.showinfo("Resize part",
                                "Select a part first (Parts tab on the right).")
            return
        part = next((p for p in self.pattern.parts if p.id == part_id), None)
        if part is None:
            return
        # Gather all boundary points of the part
        pids = set()
        for sid in part.segment_ids:
            if sid < len(self.pattern.segments):
                s = self.pattern.segments[sid]
                pids.add(s.a); pids.add(s.b)
        if not pids:
            return
        pts = [self.pattern.points[pid] for pid in pids
               if pid in self.pattern.points]
        # Include curve sampled points in the bbox so handles aren't clipped
        bbox_pts = [(p.x, p.y) for p in pts]
        for sid in part.segment_ids:
            if sid < len(self.pattern.segments):
                s = self.pattern.segments[sid]
                if s.kind == 'curve':
                    pa = self.pattern.points[s.a]; pb = self.pattern.points[s.b]
                    bbox_pts.extend(cubic_bezier_samples(
                        (pa.x, pa.y), s.c1, s.c2, (pb.x, pb.y), n=24))
        minx = min(p[0] for p in bbox_pts); maxx = max(p[0] for p in bbox_pts)
        miny = min(p[1] for p in bbox_pts); maxy = max(p[1] for p in bbox_pts)
        cur_w = maxx - minx; cur_h = maxy - miny

        dlg = ResizeDialog(self.root, round(cur_w, 2), round(cur_h, 2),
                           title=f"Resize part: {part.name}")
        self.root.wait_window(dlg.top)
        if not dlg.result:
            return
        new_w, new_h = dlg.result
        if self._scale_point_set(pids, new_w, new_h, part=part):
            self._set_status(
                f"Resized '{part.name}' to {new_w:g}×{new_h:g} cm.")

    def resize_selection_dialog(self):
        if len(self.selected_points) < 2 or self.selected_segments:
            messagebox.showinfo("Resize selection",
                                "Select at least 2 points first.")
            return
        pids = set(self.selected_points)
        pts = [self.pattern.points[pid] for pid in pids]
        minx = min(p.x for p in pts); maxx = max(p.x for p in pts)
        miny = min(p.y for p in pts); maxy = max(p.y for p in pts)
        cur_w = max(0.01, maxx - minx); cur_h = max(0.01, maxy - miny)
        dlg = ResizeDialog(self.root, round(cur_w, 2), round(cur_h, 2),
                           title="Resize selection")
        self.root.wait_window(dlg.top)
        if not dlg.result:
            return
        new_w, new_h = dlg.result
        if self._scale_point_set(pids, new_w, new_h):
            self._set_status(
                f"Resized {len(pids)} points to {new_w:g}×{new_h:g} cm.")

    def square_selection_as_rectangle(self):
        """Reposition exactly 4 selected points to form an axis-aligned
        rectangle. Pre-fills the dimension dialog with the current
        bounding-box width/height. Sort-based assignment maps each point
        to the nearest corner so existing connecting lines still form a
        sensible boundary."""
        if len(self.selected_points) != 4 or self.selected_segments:
            messagebox.showinfo(
                "Square as rectangle",
                "Select exactly 4 points first.",
            )
            return
        pts = [self.pattern.points[pid] for pid in self.selected_points]
        minx = min(p.x for p in pts); maxx = max(p.x for p in pts)
        miny = min(p.y for p in pts); maxy = max(p.y for p in pts)
        cur_w = max(0.1, maxx - minx)
        cur_h = max(0.1, maxy - miny)
        cx = (minx + maxx) / 2; cy = (miny + maxy) / 2
        dlg = RectangleDialog(self.root, round(cur_w, 2), round(cur_h, 2),
                              title="Square selection as rectangle")
        self.root.wait_window(dlg.top)
        if not dlg.result:
            return
        w, h = dlg.result

        sorted_x = sorted(pts, key=lambda p: p.x)
        left = sorted_x[:2]; right = sorted_x[2:]
        bl = min(left, key=lambda p: p.y)
        tl = max(left, key=lambda p: p.y)
        br = min(right, key=lambda p: p.y)
        tr = max(right, key=lambda p: p.y)

        self._push_undo()
        bl.x = cx - w / 2; bl.y = cy - h / 2
        br.x = cx + w / 2; br.y = cy - h / 2
        tr.x = cx + w / 2; tr.y = cy + h / 2
        tl.x = cx - w / 2; tl.y = cy + h / 2
        self.dirty = True
        self.redraw()
        self._set_status(f"Squared selection to {w:g}×{h:g} cm rectangle.")

    def override_segments_sa_dialog(self, seg_ids):
        """Open the SA override dialog for the given segment ids and apply
        the chosen value (or clear) to all of them as one undo step."""
        seg_ids = [s for s in seg_ids if s < len(self.pattern.segments)
                   and self.pattern.segments[s].style == 'solid']
        if not seg_ids:
            messagebox.showinfo(
                "Override SA",
                "No solid boundary segments to override.",
            )
            return
        # Use the first segment's current value as the dialog's default
        cur = self.pattern.segments[seg_ids[0]].seam_allowance
        dlg = SegmentSADialog(self.root, cur, len(seg_ids))
        self.root.wait_window(dlg.top)
        if not dlg.result:
            return
        self._push_undo()
        if dlg.result[0] == 'clear':
            for sid in seg_ids:
                self.pattern.segments[sid].seam_allowance = None
            self._set_status(f"Cleared SA override on {len(seg_ids)} segment(s).")
        else:
            v = dlg.result[1]
            for sid in seg_ids:
                self.pattern.segments[sid].seam_allowance = v
            self._set_status(f"Set SA override = {v:g} cm on {len(seg_ids)} segment(s).")
        self.dirty = True
        self.redraw()

    def override_sa_for_point(self, point_id):
        """Apply an SA override to all solid boundary segments incident to
        a given point. Useful from the right-click menu when the user has
        a vertex selected and wants to bump SA on both adjacent edges."""
        incident = [i for i, s in enumerate(self.pattern.segments)
                    if (s.a == point_id or s.b == point_id) and s.style == 'solid']
        self.override_segments_sa_dialog(incident)

    def _delete_part(self, part_id):
        self._push_undo()
        self.pattern.remove_part(part_id)
        if self.selected_part == part_id:
            self.selected_part = None
        self.dirty = True; self.redraw()

    def _set_selected_segment_style(self, style):
        if not self.selected_segments:
            return
        if all(self.pattern.segments[idx].style == style
               for idx in self.selected_segments
               if idx < len(self.pattern.segments)):
            return
        self._push_undo()
        for idx in self.selected_segments:
            if idx < len(self.pattern.segments):
                self.pattern.segments[idx].style = style
        self.dirty = True; self.redraw()

    def _segment_owner_part(self, seg_idx):
        """Return the Part that owns a segment index, or None."""
        for p in self.pattern.parts:
            if seg_idx in p.segment_ids:
                return p
        return None

    def _all_seam_labels(self):
        return {s.seam_label for s in self.pattern.segments
                if s.seam_label}

    def seam_label_dialog(self, seg_ids, add_notches=False):
        """Set (or clear) a seam label on the given segments. When
        `add_notches` and setting a label, drop a balance notch at each
        segment's midpoint so the joined edges align visually too."""
        seg_ids = [s for s in seg_ids if s < len(self.pattern.segments)]
        if not seg_ids:
            return
        cur = self.pattern.segments[seg_ids[0]].seam_label
        dlg = SeamLabelDialog(self.root, self._all_seam_labels(), cur, len(seg_ids))
        self.root.wait_window(dlg.top)
        if not dlg.result:
            return
        self._push_undo()
        if dlg.result[0] == 'clear':
            for si in seg_ids:
                self.pattern.segments[si].seam_label = None
            self._set_status("Cleared seam label.")
        else:
            label = dlg.result[1]
            for si in seg_ids:
                self.pattern.segments[si].seam_label = label
                if add_notches:
                    # avoid duplicate midpoint notches
                    has_mid = any(n.segment_id == si and abs(n.t - 0.5) < 0.02
                                  for n in self.pattern.notches)
                    if not has_mid:
                        self.pattern.notches.append(Notch(segment_id=si, t=0.5))
            self._set_status(f"Marked seam '{label}'.")
        self.dirty = True
        self.redraw()

    def delete_selected(self):
        if not self.selected_segments and not self.selected_points:
            return
        self._push_undo()
        if self.selected_segments:
            self.pattern.remove_segments(self.selected_segments)
        if self.selected_points:
            for pid in list(self.selected_points):
                self.pattern.remove_point(pid)
        self._clear_selection()
        self.dirty = True
        self.redraw()

    # ---- file ops ----

    def _check_dirty(self):
        if not self.dirty:
            return True
        r = messagebox.askyesnocancel("Unsaved changes",
                                      "You have unsaved changes. Save first?")
        if r is None:
            return False
        if r:
            return self.save_file()
        return True

    def new_file(self):
        if not self._check_dirty():
            return
        self.pattern = Pattern()
        self.file_path = None
        self.dirty = False
        self._clear_selection()
        self._clear_undo()
        self.pending_a = None
        self.root.title("Patternmaking")
        self.redraw()

    def open_file(self):
        if not self._check_dirty():
            return
        path = filedialog.askopenfilename(
            title="Open pattern",
            filetypes=[("Pattern JSON", "*.json"), ("All files", "*.*")],
            initialdir=os.path.dirname(__file__),
        )
        if not path:
            return
        try:
            with open(path, 'r', encoding='utf-8') as f:
                data = json.load(f)
            self.pattern = Pattern.from_json(data)
            self.file_path = path
            self.dirty = False
            self._clear_selection()
            self._clear_undo()
            self.root.title(f"Patternmaking — {os.path.basename(path)}")
            self._offer_separate_shared_parts()
            self.zoom_fit()
        except Exception as exc:
            messagebox.showerror("Open failed", str(exc))

    def _offer_separate_shared_parts(self):
        """If any two parts share a segment, offer to split them into
        independent pieces (older files built before parts owned their own
        geometry). Duplicates are offset so both become visible."""
        seg_owner_count = {}
        for p in self.pattern.parts:
            for si in p.segment_ids:
                seg_owner_count[si] = seg_owner_count.get(si, 0) + 1
        shared = any(c > 1 for c in seg_owner_count.values())
        if not shared:
            return
        if not messagebox.askyesno(
                "Separate shared parts?",
                "This file has parts that share the same lines, so moving or "
                "mirroring one affects the others.\n\n"
                "Separate them into independent pieces now? Copies are offset "
                "so you can see and arrange each piece.",
                parent=self.root):
            return
        # Keep the first owner of each segment as-is; rebuild every part that
        # shares any segment with an earlier part as an independent copy.
        claimed = set()
        parts_snapshot = list(self.pattern.parts)
        offset_step = 0.0
        # Precompute a spacing offset from overall width
        xs = [p.x for p in self.pattern.points.values()]
        span = (max(xs) - min(xs)) if xs else 20.0
        for part in parts_snapshot:
            if not any(si in claimed for si in part.segment_ids):
                # First unshared owner — keep it
                claimed.update(part.segment_ids)
                continue
            # Shared — replace with an independent, offset copy
            offset_step += span + 5.0
            off = offset_step

            def transform(x, y, _o=off):
                return (x + _o, y)
            _pmap, seg_map = self._copy_segment_set(part.segment_ids, transform)
            new_seg_ids = [seg_map[i] for i in part.segment_ids if i in seg_map]
            part.segment_ids = new_seg_ids
            if part.label_pos is not None:
                part.label_pos = transform(*part.label_pos)
            if part.grain_line is not None:
                gx1, gy1, gx2, gy2 = part.grain_line
                part.grain_line = (gx1 + off, gy1, gx2 + off, gy2)
            claimed.update(new_seg_ids)
        self.dirty = True
        self.redraw()
        self._set_status("Separated shared parts into independent pieces.")

    def save_file(self):
        if not self.file_path:
            return self.save_file_as()
        try:
            with open(self.file_path, 'w', encoding='utf-8') as f:
                json.dump(self.pattern.to_json(), f, indent=2)
            self.dirty = False
            self.root.title(f"Patternmaking — {os.path.basename(self.file_path)}")
            self._set_status(f"Saved to {self.file_path}")
            return True
        except Exception as exc:
            messagebox.showerror("Save failed", str(exc))
            return False

    def save_file_as(self):
        path = filedialog.asksaveasfilename(
            title="Save pattern", defaultextension=".json",
            filetypes=[("Pattern JSON", "*.json")],
            initialdir=os.path.dirname(__file__),
        )
        if not path:
            return False
        self.file_path = path
        return self.save_file()

    def export_pdf(self):
        if not self.pattern.points:
            messagebox.showinfo("Export", "Nothing to export yet.")
            return
        if not _ensure_reportlab(self.root):
            return
        path = filedialog.asksaveasfilename(
            title="Export tiled A4 PDF", defaultextension=".pdf",
            filetypes=[("PDF", "*.pdf")],
            initialdir=os.path.dirname(__file__),
        )
        if not path:
            return
        try:
            export_tiled_pdf(self.pattern, path)
            self._set_status(f"Exported {path}")
            messagebox.showinfo("Export complete",
                                f"Saved to:\n{path}\n\nPrint at 100% scale (no shrink-to-fit).")
        except Exception as exc:
            messagebox.showerror("Export failed", str(exc))

    def _set_status(self, msg):
        self.status_var.set(msg)


# ---------- dialogs ----------

class ConstructLineDialog:
    def __init__(self, parent, pattern: Pattern):
        self.result = None
        top = self.top = tk.Toplevel(parent)
        top.title("Construct line from point")
        top.transient(parent); top.grab_set()

        ordered = sorted(pattern.points.values(), key=lambda p: p.label)
        self._labels = [f"{p.label}  ({p.x:+.2f}, {p.y:+.2f})" for p in ordered]
        self._ids = [p.id for p in ordered]

        ttk.Label(top, text="From point:").grid(row=0, column=0, sticky='w', padx=8, pady=4)
        self.from_var = tk.StringVar(value=self._labels[0])
        ttk.OptionMenu(top, self.from_var, self._labels[0], *self._labels).grid(
            row=0, column=1, sticky='ew', padx=8, pady=4)

        # Mode toggle — default to Offset (Δx, Δy) since that's more natural
        # for the orthogonal work patternmaking mostly involves.
        self.mode_var = tk.StringVar(value='offset')
        mode_frame = ttk.Frame(top)
        mode_frame.grid(row=1, column=0, columnspan=2, sticky='w', padx=8, pady=(6, 4))
        ttk.Radiobutton(mode_frame, text="Offset (Δx, Δy)",
                        value='offset', variable=self.mode_var,
                        command=self._update_mode).pack(side='left', padx=(0, 12))
        ttk.Radiobutton(mode_frame, text="Angle + length",
                        value='angle', variable=self.mode_var,
                        command=self._update_mode).pack(side='left')

        # Offset fields (default visible)
        self.offset_frame = ttk.Frame(top)
        ttk.Label(self.offset_frame, text="ΔX (cm):").grid(row=0, column=0, sticky='w', padx=8, pady=4)
        self.dx_var = tk.StringVar(value="10")
        self.dx_entry = ttk.Entry(self.offset_frame, textvariable=self.dx_var)
        self.dx_entry.grid(row=0, column=1, sticky='ew', padx=8, pady=4)
        ttk.Label(self.offset_frame, text="ΔY (cm):").grid(row=1, column=0, sticky='w', padx=8, pady=4)
        self.dy_var = tk.StringVar(value="0")
        ttk.Entry(self.offset_frame, textvariable=self.dy_var).grid(
            row=1, column=1, sticky='ew', padx=8, pady=4)
        ttk.Label(self.offset_frame, text="+ΔX = right, +ΔY = up",
                  foreground='#888').grid(row=2, column=0, columnspan=2,
                                          padx=8, pady=(2, 0), sticky='w')

        # Angle + length fields (hidden by default)
        self.angle_frame = ttk.Frame(top)
        ttk.Label(self.angle_frame, text="Angle (°):").grid(row=0, column=0, sticky='w', padx=8, pady=4)
        self.angle_var = tk.StringVar(value="0")
        ttk.Entry(self.angle_frame, textvariable=self.angle_var).grid(
            row=0, column=1, sticky='ew', padx=8, pady=4)
        ttk.Label(self.angle_frame, text="Length (cm):").grid(row=1, column=0, sticky='w', padx=8, pady=4)
        self.length_var = tk.StringVar(value="10")
        ttk.Entry(self.angle_frame, textvariable=self.length_var).grid(
            row=1, column=1, sticky='ew', padx=8, pady=4)
        ttk.Label(self.angle_frame, text="0° = right, 90° = up",
                  foreground='#888').grid(row=2, column=0, columnspan=2,
                                          padx=8, pady=(2, 0), sticky='w')

        # New point label
        label_row = ttk.Frame(top)
        label_row.grid(row=3, column=0, columnspan=2, sticky='ew', padx=0, pady=(8, 0))
        ttk.Label(label_row, text="New point label:").grid(
            row=0, column=0, sticky='w', padx=8, pady=4)
        self.label_var = tk.StringVar(value="")
        ttk.Entry(label_row, textvariable=self.label_var).grid(
            row=0, column=1, sticky='ew', padx=8, pady=4)
        ttk.Label(label_row, text="(blank = auto)",
                  foreground='#888').grid(row=1, column=1, sticky='w', padx=8)

        btns = ttk.Frame(top); btns.grid(row=4, column=0, columnspan=2, pady=10)
        ttk.Button(btns, text="Create", command=self._ok).pack(side='left', padx=4)
        ttk.Button(btns, text="Cancel", command=top.destroy).pack(side='left', padx=4)
        top.bind('<Return>', lambda e: self._ok())
        top.bind('<Escape>', lambda e: top.destroy())

        self._update_mode()
        self.dx_entry.focus_set(); self.dx_entry.select_range(0, tk.END)

    def _update_mode(self):
        if self.mode_var.get() == 'offset':
            self.angle_frame.grid_remove()
            self.offset_frame.grid(row=2, column=0, columnspan=2, sticky='ew')
        else:
            self.offset_frame.grid_remove()
            self.angle_frame.grid(row=2, column=0, columnspan=2, sticky='ew')

    def _ok(self):
        try:
            chosen = self.from_var.get()
            from_id = next(
                (pid for pid, lbl in zip(self._ids, self._labels) if lbl == chosen),
                self._ids[0],
            )
            if self.mode_var.get() == 'offset':
                dx = float(self.dx_var.get())
                dy = float(self.dy_var.get())
                if dx == 0 and dy == 0:
                    raise ValueError("Offset can't be (0, 0).")
                self.result = ('offset', from_id, dx, dy, self.label_var.get())
            else:
                angle = float(self.angle_var.get())
                length = float(self.length_var.get())
                if length <= 0:
                    raise ValueError("Length must be positive.")
                self.result = ('angle', from_id, angle, length, self.label_var.get())
            self.top.destroy()
        except Exception as exc:
            messagebox.showerror("Invalid input", str(exc), parent=self.top)


class AddDartDialog:
    def __init__(self, parent, pattern: Pattern, point_id: int):
        self.result = None
        p = pattern.points[point_id]
        incident = [(i, s) for i, s in enumerate(pattern.segments)
                    if (s.a == point_id or s.b == point_id) and s.style == 'solid']
        if not incident:
            messagebox.showerror(
                "Add dart",
                f"Point {p.label} isn't connected to any solid boundary segment.\n"
                "Place a point on a boundary line first.",
                parent=parent,
            )
            self.top = None
            return

        top = self.top = tk.Toplevel(parent)
        top.title("Add dart at point")
        top.transient(parent); top.grab_set()

        ttk.Label(top, text=f"Anchor point: {p.label}").grid(
            row=0, column=0, columnspan=2, padx=8, pady=(10, 6), sticky='w')

        ttk.Label(top, text="Depth (cm):").grid(row=1, column=0, padx=8, pady=4, sticky='w')
        self.depth_var = tk.StringVar(value="8")
        ttk.Entry(top, textvariable=self.depth_var).grid(
            row=1, column=1, padx=8, pady=4, sticky='ew')

        ttk.Label(top, text="Width (cm):").grid(row=2, column=0, padx=8, pady=4, sticky='w')
        self.width_var = tk.StringVar(value="2")
        ttk.Entry(top, textvariable=self.width_var).grid(
            row=2, column=1, padx=8, pady=4, sticky='ew')

        ttk.Label(top, text="Direction:").grid(row=3, column=0, padx=8, pady=4, sticky='w')
        self.direction_var = tk.StringVar(value='internal')
        dir_frame = ttk.Frame(top); dir_frame.grid(row=3, column=1, padx=8, pady=4, sticky='w')
        ttk.Radiobutton(dir_frame, text="Internal (into part)",
                        value='internal', variable=self.direction_var).pack(anchor='w')
        ttk.Radiobutton(dir_frame, text="External (away from part)",
                        value='external', variable=self.direction_var).pack(anchor='w')

        ttk.Label(top,
                  text=("Depth = how far the apex sits in from the boundary.\n"
                        "Width = how wide the dart mouth is, centred on the anchor.\n"
                        "Boundary direction is detected from the incident lines."),
                  foreground='#888', justify='left').grid(
            row=4, column=0, columnspan=2, padx=8, pady=(6, 0), sticky='w')

        btns = ttk.Frame(top); btns.grid(row=5, column=0, columnspan=2, pady=10)
        ttk.Button(btns, text="Create", command=self._ok).pack(side='left', padx=4)
        ttk.Button(btns, text="Cancel", command=top.destroy).pack(side='left', padx=4)
        top.bind('<Return>', lambda e: self._ok())
        top.bind('<Escape>', lambda e: top.destroy())

    def _ok(self):
        try:
            depth = float(self.depth_var.get())
            width = float(self.width_var.get())
            if depth <= 0 or width <= 0:
                raise ValueError("Depth and width must be positive.")
        except ValueError as exc:
            messagebox.showerror("Invalid input", str(exc), parent=self.top)
            return
        self.result = (depth, width, self.direction_var.get())
        self.top.destroy()


class GrainLineDialog:
    def __init__(self, parent, default_angle, default_length, has_existing):
        self.result = None  # ('set', angle, length) or ('remove',)
        top = self.top = tk.Toplevel(parent)
        top.title("Grain line")
        top.transient(parent); top.grab_set()

        ttk.Label(top, text="Angle (°):").grid(row=0, column=0, padx=12, pady=(12, 4), sticky='w')
        self.angle_var = tk.StringVar(value=f"{default_angle:g}")
        e = ttk.Entry(top, textvariable=self.angle_var, width=10)
        e.grid(row=0, column=1, padx=12, pady=(12, 4), sticky='ew')
        e.focus_set(); e.select_range(0, tk.END)

        ttk.Label(top, text="Length (cm):").grid(row=1, column=0, padx=12, pady=4, sticky='w')
        self.length_var = tk.StringVar(value=f"{default_length:g}")
        ttk.Entry(top, textvariable=self.length_var, width=10).grid(
            row=1, column=1, padx=12, pady=4, sticky='ew')

        ttk.Label(top, text="0° = horizontal, 90° = vertical.\n"
                            "Centred on the part; arrow both ends.",
                  foreground='#888', justify='left').grid(
            row=2, column=0, columnspan=2, padx=12, pady=(4, 0), sticky='w')

        btns = ttk.Frame(top); btns.grid(row=3, column=0, columnspan=2, pady=12)
        ttk.Button(btns, text="Set", command=self._ok).pack(side='left', padx=4)
        if has_existing:
            ttk.Button(btns, text="Remove", command=self._remove).pack(side='left', padx=4)
        ttk.Button(btns, text="Cancel", command=top.destroy).pack(side='left', padx=4)
        top.bind('<Return>', lambda _e: self._ok())
        top.bind('<Escape>', lambda _e: top.destroy())

    def _ok(self):
        try:
            angle = float(self.angle_var.get())
            length = float(self.length_var.get())
            if length <= 0:
                raise ValueError("Length must be positive.")
        except ValueError as exc:
            messagebox.showerror("Invalid", str(exc), parent=self.top)
            return
        self.result = ('set', angle, length)
        self.top.destroy()

    def _remove(self):
        self.result = ('remove',)
        self.top.destroy()


class MirrorPartDialog:
    def __init__(self, parent, part_name):
        self.result = None  # (axis, keep_original, new_name)
        top = self.top = tk.Toplevel(parent)
        top.title(f"Mirror {part_name}")
        top.transient(parent); top.grab_set()

        ttk.Label(top, text="Mirror across:").grid(
            row=0, column=0, padx=12, pady=(12, 4), sticky='w')
        self.axis_var = tk.StringVar(value='right')
        axis_frame = ttk.Frame(top)
        axis_frame.grid(row=0, column=1, padx=12, pady=(12, 4), sticky='w')
        for val, lab in [('right', 'Right edge'), ('left', 'Left edge'),
                         ('top', 'Top edge'), ('bottom', 'Bottom edge')]:
            ttk.Radiobutton(axis_frame, text=lab, value=val,
                            variable=self.axis_var).pack(anchor='w')

        self.keep_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(top, text="Keep original (creates a mirrored copy)",
                        variable=self.keep_var).grid(
            row=1, column=0, columnspan=2, padx=12, pady=6, sticky='w')

        ttk.Label(top, text="New part name:").grid(
            row=2, column=0, padx=12, pady=4, sticky='w')
        self.name_var = tk.StringVar(value=f"{part_name} (mirror)")
        ttk.Entry(top, textvariable=self.name_var, width=20).grid(
            row=2, column=1, padx=12, pady=4, sticky='ew')

        btns = ttk.Frame(top); btns.grid(row=3, column=0, columnspan=2, pady=12)
        ttk.Button(btns, text="Mirror", command=self._ok).pack(side='left', padx=4)
        ttk.Button(btns, text="Cancel", command=top.destroy).pack(side='left', padx=4)
        top.bind('<Return>', lambda _e: self._ok())
        top.bind('<Escape>', lambda _e: top.destroy())

    def _ok(self):
        name = self.name_var.get().strip()
        if not name:
            messagebox.showerror("Invalid", "Name required.", parent=self.top)
            return
        self.result = (self.axis_var.get(), self.keep_var.get(), name)
        self.top.destroy()


class SeamLabelDialog:
    def __init__(self, parent, existing_labels, default, n_segs):
        self.result = None  # ('set', label) or ('clear',)
        top = self.top = tk.Toplevel(parent)
        top.title("Seam label")
        top.transient(parent); top.grab_set()

        msg = (f"Name the seam for {n_segs} selected edges."
               if n_segs > 1 else "Name this seam.")
        ttk.Label(top, text=msg, foreground='#555').grid(
            row=0, column=0, columnspan=2, padx=12, pady=(12, 6), sticky='w')

        ttk.Label(top, text="Seam:").grid(row=1, column=0, padx=12, pady=4, sticky='w')
        self.label_var = tk.StringVar(value=default or "")
        combo = ttk.Combobox(top, textvariable=self.label_var,
                             values=sorted(existing_labels), width=22)
        combo.grid(row=1, column=1, padx=12, pady=4, sticky='ew')
        combo.focus_set()

        ttk.Label(top,
                  text="Edges sharing a seam name are joined; the printout "
                       "cross-references which part each connects to.",
                  foreground='#888', wraplength=300, justify='left').grid(
            row=2, column=0, columnspan=2, padx=12, pady=(4, 0), sticky='w')

        btns = ttk.Frame(top); btns.grid(row=3, column=0, columnspan=2, pady=12)
        ttk.Button(btns, text="Set", command=self._ok).pack(side='left', padx=4)
        ttk.Button(btns, text="Clear label", command=self._clear).pack(side='left', padx=4)
        ttk.Button(btns, text="Cancel", command=top.destroy).pack(side='left', padx=4)
        top.bind('<Return>', lambda _e: self._ok())
        top.bind('<Escape>', lambda _e: top.destroy())

    def _ok(self):
        label = self.label_var.get().strip()
        if not label:
            messagebox.showerror("Invalid", "Enter a seam name (or Clear).",
                                 parent=self.top)
            return
        self.result = ('set', label)
        self.top.destroy()

    def _clear(self):
        self.result = ('clear',)
        self.top.destroy()


class RotatePartDialog:
    def __init__(self, parent, part_name):
        self.result = None
        top = self.top = tk.Toplevel(parent)
        top.title(f"Rotate {part_name}")
        top.transient(parent); top.grab_set()

        ttk.Label(top, text="Rotation (degrees):").grid(
            row=0, column=0, padx=12, pady=(12, 4), sticky='w')
        self.deg_var = tk.StringVar(value="90")
        e = ttk.Entry(top, textvariable=self.deg_var, width=10)
        e.grid(row=0, column=1, padx=12, pady=(12, 4), sticky='ew')
        e.focus_set(); e.select_range(0, tk.END)

        ttk.Label(top,
                  text="Rotates around the part's centroid.\n"
                       "Positive = counter-clockwise.",
                  foreground='#888', justify='left').grid(
            row=1, column=0, columnspan=2, padx=12, pady=(4, 0), sticky='w')

        btns = ttk.Frame(top); btns.grid(row=2, column=0, columnspan=2, pady=12)
        ttk.Button(btns, text="Rotate", command=self._ok).pack(side='left', padx=4)
        ttk.Button(btns, text="90° ↺", command=lambda: self._quick(90)).pack(side='left', padx=4)
        ttk.Button(btns, text="90° ↻", command=lambda: self._quick(-90)).pack(side='left', padx=4)
        ttk.Button(btns, text="Cancel", command=top.destroy).pack(side='left', padx=4)
        top.bind('<Return>', lambda _e: self._ok())
        top.bind('<Escape>', lambda _e: top.destroy())

    def _ok(self):
        try:
            deg = float(self.deg_var.get())
        except ValueError as exc:
            messagebox.showerror("Invalid", str(exc), parent=self.top)
            return
        self.result = deg
        self.top.destroy()

    def _quick(self, deg):
        self.result = deg
        self.top.destroy()


class RectangleDialog:
    def __init__(self, parent, default_w, default_h, title="Rectangle"):
        self.result = None
        top = self.top = tk.Toplevel(parent)
        top.title(title)
        top.transient(parent); top.grab_set()

        ttk.Label(top, text="Width (cm):").grid(row=0, column=0, padx=10, pady=(10, 4), sticky='w')
        self.w_var = tk.StringVar(value=f"{default_w:g}")
        w_entry = ttk.Entry(top, textvariable=self.w_var, width=12)
        w_entry.grid(row=0, column=1, padx=10, pady=(10, 4), sticky='ew')
        w_entry.focus_set(); w_entry.select_range(0, tk.END)

        ttk.Label(top, text="Height (cm):").grid(row=1, column=0, padx=10, pady=4, sticky='w')
        self.h_var = tk.StringVar(value=f"{default_h:g}")
        ttk.Entry(top, textvariable=self.h_var, width=12).grid(
            row=1, column=1, padx=10, pady=4, sticky='ew')

        btns = ttk.Frame(top); btns.grid(row=2, column=0, columnspan=2, pady=10)
        ttk.Button(btns, text="OK", command=self._ok).pack(side='left', padx=4)
        ttk.Button(btns, text="Cancel", command=top.destroy).pack(side='left', padx=4)
        top.bind('<Return>', lambda _e: self._ok())
        top.bind('<Escape>', lambda _e: top.destroy())

    def _ok(self):
        try:
            w = float(self.w_var.get())
            h = float(self.h_var.get())
            if w <= 0 or h <= 0:
                raise ValueError("Dimensions must be positive.")
        except ValueError as exc:
            messagebox.showerror("Invalid input", str(exc), parent=self.top)
            return
        self.result = (w, h)
        self.top.destroy()


class ResizeDialog:
    def __init__(self, parent, default_w, default_h, title="Resize"):
        self.result = None
        top = self.top = tk.Toplevel(parent)
        top.title(title)
        top.transient(parent); top.grab_set()

        ttk.Label(top, text=f"Current: {default_w:.2f} × {default_h:.2f} cm",
                  foreground='#555').grid(row=0, column=0, columnspan=2,
                                          padx=12, pady=(12, 8))

        ttk.Label(top, text="New width (cm):").grid(
            row=1, column=0, padx=12, pady=4, sticky='w')
        self.w_var = tk.StringVar(value=f"{default_w:g}")
        w_entry = ttk.Entry(top, textvariable=self.w_var, width=12)
        w_entry.grid(row=1, column=1, padx=12, pady=4, sticky='ew')
        w_entry.focus_set(); w_entry.select_range(0, tk.END)

        ttk.Label(top, text="New height (cm):").grid(
            row=2, column=0, padx=12, pady=4, sticky='w')
        self.h_var = tk.StringVar(value=f"{default_h:g}")
        ttk.Entry(top, textvariable=self.h_var, width=12).grid(
            row=2, column=1, padx=12, pady=4, sticky='ew')

        ttk.Label(top, text="Scaled around the selection's centroid. Curve "
                            "handles, attached darts, and the part label all "
                            "scale along.",
                  foreground='#888', wraplength=280, justify='left').grid(
            row=3, column=0, columnspan=2, padx=12, pady=(6, 0), sticky='w')

        btns = ttk.Frame(top); btns.grid(row=4, column=0, columnspan=2, pady=12)
        ttk.Button(btns, text="Resize", command=self._ok).pack(side='left', padx=4)
        ttk.Button(btns, text="Cancel", command=top.destroy).pack(side='left', padx=4)
        top.bind('<Return>', lambda _e: self._ok())
        top.bind('<Escape>', lambda _e: top.destroy())

    def _ok(self):
        try:
            w = float(self.w_var.get())
            h = float(self.h_var.get())
            if w <= 0 or h <= 0:
                raise ValueError("Dimensions must be positive.")
        except ValueError as exc:
            messagebox.showerror("Invalid input", str(exc), parent=self.top)
            return
        self.result = (w, h)
        self.top.destroy()


class SegmentSADialog:
    def __init__(self, parent, current_value, count):
        self.result = None  # set to ('clear',) or ('value', float)
        top = self.top = tk.Toplevel(parent)
        top.title("Override seam allowance")
        top.transient(parent); top.grab_set()

        ttk.Label(top, text=f"Override the part's SA on {count} segment(s).",
                  foreground='#555').grid(row=0, column=0, columnspan=2,
                                          padx=10, pady=(10, 4), sticky='w')

        ttk.Label(top, text="Seam allowance:").grid(row=1, column=0, padx=10, pady=4, sticky='w')
        default_text = '' if current_value is None else f"{current_value:g}"
        self.value_var = tk.StringVar(value=default_text if default_text else "2")
        e = ttk.Entry(top, textvariable=self.value_var)
        e.grid(row=1, column=1, padx=10, pady=4, sticky='ew')
        e.focus_set(); e.select_range(0, tk.END)
        ttk.Label(top, text="cm").grid(row=1, column=2, padx=(0, 10), pady=4)

        ttk.Label(top,
                  text="Tip: use 'Clear' to fall back to the part's default SA.",
                  foreground='#888', wraplength=320, justify='left').grid(
            row=2, column=0, columnspan=3, padx=10, pady=(4, 0), sticky='w')

        btns = ttk.Frame(top); btns.grid(row=3, column=0, columnspan=3, pady=10)
        ttk.Button(btns, text="Apply", command=self._ok).pack(side='left', padx=4)
        ttk.Button(btns, text="Clear override", command=self._clear).pack(side='left', padx=4)
        ttk.Button(btns, text="Cancel", command=top.destroy).pack(side='left', padx=4)
        top.bind('<Return>', lambda _e: self._ok())
        top.bind('<Escape>', lambda _e: top.destroy())

    def _ok(self):
        try:
            v = float(self.value_var.get())
            if v < 0:
                raise ValueError("Must be non-negative.")
        except ValueError as exc:
            messagebox.showerror("Invalid", str(exc), parent=self.top)
            return
        self.result = ('value', v)
        self.top.destroy()

    def _clear(self):
        self.result = ('clear',)
        self.top.destroy()


class MovePointAlongLineDialog:
    def __init__(self, parent, pattern: Pattern, point_id: int):
        self.result = None
        p = pattern.points[point_id]
        incident = [(i, s) for i, s in enumerate(pattern.segments)
                    if s.a == point_id or s.b == point_id]
        if not incident:
            messagebox.showerror(
                "Move point",
                f"Point {p.label} isn't connected to any line.",
                parent=parent,
            )
            self.top = None
            return

        top = self.top = tk.Toplevel(parent)
        top.title(f"Move point {p.label}")
        top.transient(parent); top.grab_set()

        ttk.Label(top, text=f"Move point {p.label} along…").grid(
            row=0, column=0, columnspan=2, padx=8, pady=(10, 6), sticky='w')

        self._seg_indices = []
        self._other_ids = []
        labels = []
        for i, s in incident:
            other_id = s.b if s.a == point_id else s.a
            other = pattern.points[other_id]
            kind = "line" if s.kind == 'line' else "chord"
            cur_d = math.hypot(other.x - p.x, other.y - p.y)
            labels.append(f"{kind} from {other.label}   (currently {cur_d:.2f} cm)")
            self._seg_indices.append(i)
            self._other_ids.append(other_id)
        self._labels = labels

        ttk.Label(top, text="From:").grid(row=1, column=0, padx=8, pady=4, sticky='w')
        self.from_var = tk.StringVar(value=labels[0])
        ttk.OptionMenu(top, self.from_var, labels[0], *labels).grid(
            row=1, column=1, padx=8, pady=4, sticky='ew')

        ttk.Label(top, text="Distance (cm):").grid(row=2, column=0, padx=8, pady=4, sticky='w')
        self.dist_var = tk.StringVar(value="")
        e = ttk.Entry(top, textvariable=self.dist_var)
        e.grid(row=2, column=1, padx=8, pady=4, sticky='ew')
        e.focus_set()

        ttk.Label(top,
                  text=("The point moves along the straight line connecting it "
                        "to the selected adjacent point."),
                  foreground='#888', wraplength=280, justify='left').grid(
            row=3, column=0, columnspan=2, padx=8, pady=(4, 0), sticky='w')

        btns = ttk.Frame(top); btns.grid(row=4, column=0, columnspan=2, pady=10)
        ttk.Button(btns, text="Move", command=self._ok).pack(side='left', padx=4)
        ttk.Button(btns, text="Cancel", command=top.destroy).pack(side='left', padx=4)
        top.bind('<Return>', lambda _e: self._ok())
        top.bind('<Escape>', lambda _e: top.destroy())

    def _ok(self):
        try:
            dist = float(self.dist_var.get())
            if dist <= 0:
                raise ValueError("Distance must be positive.")
        except ValueError as exc:
            messagebox.showerror("Invalid input", str(exc), parent=self.top)
            return
        idx = self._labels.index(self.from_var.get())
        other_id = self._other_ids[idx]
        self.result = (other_id, dist)
        self.top.destroy()


class NamePartDialog:
    def __init__(self, parent, default_name, default_sa, n_segs):
        self.result = None
        top = self.top = tk.Toplevel(parent)
        top.title("Create part")
        top.transient(parent); top.grab_set()

        ttk.Label(top, text=f"{n_segs} segments will form this part.",
                  foreground='#555').grid(row=0, column=0, columnspan=2, padx=8, pady=(8, 4))

        ttk.Label(top, text="Name:").grid(row=1, column=0, sticky='w', padx=8, pady=4)
        self.name_var = tk.StringVar(value=default_name)
        e = ttk.Entry(top, textvariable=self.name_var)
        e.grid(row=1, column=1, sticky='ew', padx=8, pady=4)
        e.focus_set(); e.select_range(0, tk.END)

        ttk.Label(top, text="Seam allowance:").grid(row=2, column=0, sticky='w', padx=8, pady=4)
        self.sa_var = tk.StringVar(value=str(default_sa))
        ttk.Entry(top, textvariable=self.sa_var).grid(row=2, column=1, sticky='ew', padx=8, pady=4)
        ttk.Label(top, text="cm  (0 = none)", foreground='#888').grid(
            row=3, column=1, sticky='w', padx=8)

        btns = ttk.Frame(top); btns.grid(row=4, column=0, columnspan=2, pady=8)
        ttk.Button(btns, text="Create", command=self._ok).pack(side='left', padx=4)
        ttk.Button(btns, text="Cancel", command=top.destroy).pack(side='left', padx=4)
        top.bind('<Return>', lambda _e: self._ok())
        top.bind('<Escape>', lambda _e: top.destroy())

    def _ok(self):
        name = self.name_var.get().strip()
        if not name:
            messagebox.showerror("Invalid", "Name required.", parent=self.top); return
        try:
            sa = float(self.sa_var.get())
            if sa < 0: sa = 0
        except ValueError:
            messagebox.showerror("Invalid", "Seam allowance must be a number.",
                                 parent=self.top)
            return
        self.result = (name, sa)
        self.top.destroy()


# ---------- reportlab availability ----------

def _ensure_reportlab(parent):
    try:
        import reportlab  # noqa: F401
        return True
    except ImportError:
        pass
    interp = sys.executable
    msg = (
        "reportlab is needed for PDF export but it isn't installed "
        f"for this Python:\n\n  {interp}\n\nInstall it now?"
    )
    if not messagebox.askyesno("Install reportlab?", msg, parent=parent):
        return False
    try:
        proc = subprocess.run(
            [interp, "-m", "pip", "install", "reportlab"],
            capture_output=True, text=True, timeout=180,
        )
        if proc.returncode != 0:
            messagebox.showerror(
                "Install failed",
                "pip exited with an error:\n\n"
                + (proc.stderr or proc.stdout or "(no output)")[-2000:],
                parent=parent,
            )
            return False
    except Exception as exc:
        messagebox.showerror("Install failed", str(exc), parent=parent)
        return False
    try:
        import reportlab  # noqa: F401
        messagebox.showinfo("Installed",
                            "reportlab is ready. Try the export again.", parent=parent)
        return True
    except ImportError as exc:
        messagebox.showerror("Install failed",
                             f"Installed but still can't import:\n{exc}",
                             parent=parent)
        return False


# ---------- PDF export ----------

A4_W_CM = 21.0
A4_H_CM = 29.7
PRINT_MARGIN_CM = 1.0
TILE_OVERLAP_CM = 1.0
POINTS_PER_CM = 72.0 / 2.54


def export_tiled_pdf(pattern: Pattern, path: str):
    try:
        from reportlab.pdfgen import canvas as rl_canvas
        from reportlab.lib.pagesizes import A4
    except ImportError as exc:
        raise RuntimeError(
            "reportlab is required for the Python at:\n  "
            f"{sys.executable}\nInstall with:\n  \"{sys.executable}\" -m pip install reportlab"
        ) from exc

    # Points referenced by drawn geometry. Anything not referenced (orphan
    # points left over from editing) is excluded from the bounding box and
    # from per-tile rendering — otherwise a stray point at the edge of the
    # world expands the tile grid and produces useless pages.
    referenced_pids: set = set()
    for seg in pattern.segments:
        referenced_pids.add(seg.a)
        referenced_pids.add(seg.b)
    for dart in pattern.darts:
        referenced_pids.update(dart.all_point_ids())

    # Segment -> owning part name, and seam label -> list of part names, so
    # each labelled edge on the printout can name the part(s) it joins.
    seg_owner_names = {}
    for part in pattern.parts:
        for si in part.segment_ids:
            seg_owner_names[si] = part.name
    seam_join_map = {}
    for si, seg in enumerate(pattern.segments):
        if seg.seam_label:
            name = seg_owner_names.get(si, '(loose)')
            seam_join_map.setdefault(seg.seam_label, [])
            if name not in seam_join_map[seg.seam_label]:
                seam_join_map[seg.seam_label].append(name)

    # Precompute seam-allowance polylines so they're included in the bounding box.
    # Each edge uses its segment's seam_allowance override if set, else the part's.
    sa_polys = []  # list of (closed polyline in world cm, part)
    for part in pattern.parts:
        id_pairs = [(i, pattern.segments[i]) for i in part.segment_ids
                    if i < len(pattern.segments)
                    and pattern.segments[i].style == 'solid']
        chain = chain_segments_into_loop_with_ids(id_pairs)
        if not chain:
            continue
        poly, edge_ids = polyline_of_chain_with_ids(
            chain, pattern.points, samples_per_curve=48)
        distances = [
            (pattern.segments[sid].seam_allowance
             if pattern.segments[sid].seam_allowance is not None
             else part.seam_allowance)
            for sid in edge_ids
        ]
        if not any(d > 0 for d in distances):
            continue
        sa_polys.append((offset_closed_polyline_variable(poly, distances), part))

    xs, ys = [], []
    for pid in referenced_pids:
        p = pattern.points.get(pid)
        if p is not None:
            xs.append(p.x); ys.append(p.y)
    for seg in pattern.segments:
        if seg.kind == 'curve':
            pa = pattern.points[seg.a]; pb = pattern.points[seg.b]
            for x, y in cubic_bezier_samples((pa.x, pa.y), seg.c1, seg.c2, (pb.x, pb.y), n=64):
                xs.append(x); ys.append(y)
    for poly, _part in sa_polys:
        for x, y in poly:
            xs.append(x); ys.append(y)
    if not xs:
        raise RuntimeError("Nothing to export.")

    # No extra padding around the bounding box: each tile already has a 1 cm
    # print margin that provides whitespace around the content. Adding padding
    # here can push the pattern past the content-area boundary and force an
    # unnecessary extra tile.
    min_x = min(xs); min_y = min(ys)
    max_x = max(xs); max_y = max(ys)
    total_w = max_x - min_x; total_h = max_y - min_y

    content_w = A4_W_CM - 2 * PRINT_MARGIN_CM
    content_h = A4_H_CM - 2 * PRINT_MARGIN_CM
    step_x = content_w - TILE_OVERLAP_CM
    step_y = content_h - TILE_OVERLAP_CM
    # First tile covers a full content area; each additional tile adds step_x/step_y.
    # So N tiles cover (N-1)*step + content. Solving for the minimum N:
    cols = 1 if total_w <= content_w + 1e-9 else 1 + math.ceil((total_w - content_w) / step_x)
    rows = 1 if total_h <= content_h + 1e-9 else 1 + math.ceil((total_h - content_h) / step_y)

    # Compute matching labels where any drawn polyline (segment or SA outline)
    # crosses an interior tile-cut line. Each crossing gets a sequential number;
    # both pages that include the crossing in their content area render the same
    # number so the user can align pages by matching numbers.
    all_polys = [segment_to_polyline(s, pattern.points) for s in pattern.segments]
    for poly, _part in sa_polys:
        all_polys.append(poly)
    crossings_global: list = []  # (label, world_x, world_y)
    label_n = 1
    for cc in range(cols - 1):
        cut_x = min_x + (cc + 1) * step_x
        pts = []
        for poly in all_polys:
            pts.extend(polyline_crossings_vertical(poly, cut_x))
        pts.sort(key=lambda p: p[1])
        dedup = []
        for x, y in pts:
            if not dedup or abs(y - dedup[-1][1]) > 0.25:
                dedup.append((x, y))
        for x, y in dedup:
            crossings_global.append((str(label_n), x, y))
            label_n += 1
    for rr in range(rows - 1):
        cut_y = min_y + (rr + 1) * step_y
        pts = []
        for poly in all_polys:
            pts.extend(polyline_crossings_horizontal(poly, cut_y))
        pts.sort(key=lambda p: p[0])
        dedup = []
        for x, y in pts:
            if not dedup or abs(x - dedup[-1][0]) > 0.25:
                dedup.append((x, y))
        for x, y in dedup:
            crossings_global.append((str(label_n), x, y))
            label_n += 1

    c = rl_canvas.Canvas(path, pagesize=A4)
    total_pages = cols * rows + 1

    _draw_cover_page(c, cols, rows, min_x, min_y, step_x, step_y,
                     content_w, content_h, total_w, total_h,
                     pattern, referenced_pids, 1, total_pages)
    c.showPage()

    page_num = 1
    for row in range(rows):
        for col in range(cols):
            tile_x0 = min_x + col * step_x
            tile_y0 = min_y + row * step_y

            x_left_pt = PRINT_MARGIN_CM * POINTS_PER_CM
            y_bot_pt = PRINT_MARGIN_CM * POINTS_PER_CM
            x_right_pt = (A4_W_CM - PRINT_MARGIN_CM) * POINTS_PER_CM
            y_top_pt = (A4_H_CM - PRINT_MARGIN_CM) * POINTS_PER_CM

            c.setStrokeColorRGB(0.7, 0.7, 0.7)
            c.setLineWidth(0.3)
            c.rect(x_left_pt, y_bot_pt, x_right_pt - x_left_pt, y_top_pt - y_bot_pt,
                   stroke=1, fill=0)
            _draw_crop_marks(c, x_left_pt, y_bot_pt, x_right_pt, y_top_pt)

            def wx_to_pt(wx, _tx=tile_x0):
                return (PRINT_MARGIN_CM + (wx - _tx)) * POINTS_PER_CM

            def wy_to_pt(wy, _ty=tile_y0):
                return (PRINT_MARGIN_CM + (wy - _ty)) * POINTS_PER_CM

            c.saveState()
            clip = c.beginPath()
            clip.rect(x_left_pt, y_bot_pt, x_right_pt - x_left_pt, y_top_pt - y_bot_pt)
            c.clipPath(clip, stroke=0, fill=0)

            # Seam-allowance dashed offsets
            c.setStrokeColorRGB(0.4, 0.4, 0.4)
            c.setLineWidth(0.5)
            c.setDash(5, 4)
            for poly, _part in sa_polys:
                if len(poly) < 2:
                    continue
                path_obj = c.beginPath()
                path_obj.moveTo(wx_to_pt(poly[0][0]), wy_to_pt(poly[0][1]))
                for x, y in poly[1:]:
                    path_obj.lineTo(wx_to_pt(x), wy_to_pt(y))
                c.drawPath(path_obj, stroke=1, fill=0)
            c.setDash()  # solid

            # Segments (solid black for cutting, dashed for dotted)
            c.setStrokeColorRGB(0, 0, 0)
            for seg in pattern.segments:
                pa = pattern.points.get(seg.a); pb = pattern.points.get(seg.b)
                if not pa or not pb:
                    continue
                if seg.style == 'dotted':
                    c.setDash(3, 2); c.setLineWidth(0.5)
                else:
                    c.setDash(); c.setLineWidth(0.7)
                if seg.kind == 'line':
                    c.line(wx_to_pt(pa.x), wy_to_pt(pa.y),
                           wx_to_pt(pb.x), wy_to_pt(pb.y))
                else:
                    pts = cubic_bezier_samples((pa.x, pa.y), seg.c1, seg.c2, (pb.x, pb.y), n=80)
                    path_obj = c.beginPath()
                    path_obj.moveTo(wx_to_pt(pts[0][0]), wy_to_pt(pts[0][1]))
                    for x, y in pts[1:]:
                        path_obj.lineTo(wx_to_pt(x), wy_to_pt(y))
                    c.drawPath(path_obj, stroke=1, fill=0)
            c.setDash()

            # Grain lines (with arrowheads at both ends)
            c.setStrokeColorRGB(0, 0, 0); c.setLineWidth(0.7)
            for part in pattern.parts:
                if part.grain_line is None:
                    continue
                gx1, gy1, gx2, gy2 = part.grain_line
                p1 = (wx_to_pt(gx1), wy_to_pt(gy1))
                p2 = (wx_to_pt(gx2), wy_to_pt(gy2))
                c.line(p1[0], p1[1], p2[0], p2[1])
                _pdf_arrowhead(c, p1, p2)
                _pdf_arrowhead(c, p2, p1)

            # Notches (perpendicular ticks crossing the boundary)
            c.setStrokeColorRGB(0, 0, 0); c.setLineWidth(0.7)
            for notch in pattern.notches:
                if notch.segment_id >= len(pattern.segments):
                    continue
                seg = pattern.segments[notch.segment_id]
                if seg.a not in pattern.points or seg.b not in pattern.points:
                    continue
                wx, wy, tx, ty = segment_point_and_tangent(
                    seg, pattern.points, notch.t)
                # perpendicular in world coords
                perp_x, perp_y = -ty, tx
                half = 0.3  # cm
                a = (wx - perp_x * half, wy - perp_y * half)
                b = (wx + perp_x * half, wy + perp_y * half)
                c.line(wx_to_pt(a[0]), wy_to_pt(a[1]),
                       wx_to_pt(b[0]), wy_to_pt(b[1]))

            # Seam labels along edges, cross-referencing the joined part(s)
            c.setFillColorRGB(0.1, 0.1, 0.1)
            for si, seg in enumerate(pattern.segments):
                if not seg.seam_label:
                    continue
                if seg.a not in pattern.points or seg.b not in pattern.points:
                    continue
                wx, wy, tx, ty = segment_point_and_tangent(
                    seg, pattern.points, 0.5)
                owner = seg_owner_names.get(si)
                others = [n for n in seam_join_map.get(seg.seam_label, [])
                          if n != owner]
                text = seg.seam_label.upper()
                if others:
                    text += "  (joins " + ", ".join(others) + ")"
                # place text just inside the edge, along its direction
                perp_x, perp_y = -ty, tx
                lx = wx + perp_x * 0.5
                ly = wy + perp_y * 0.5
                ang = math.degrees(math.atan2(ty, tx))
                if ang > 90 or ang < -90:
                    ang += 180  # keep text upright
                c.saveState()
                c.translate(wx_to_pt(lx), wy_to_pt(ly))
                c.rotate(ang)
                c.setFont("Helvetica", 7)
                c.drawCentredString(0, 0, text)
                c.restoreState()

            # Point dots + labels
            c.setFillColorRGB(0, 0, 0)
            for pt in pattern.points.values():
                if pt.id not in referenced_pids:
                    continue  # skip orphans
                px = wx_to_pt(pt.x); py = wy_to_pt(pt.y)
                if x_left_pt - 5 <= px <= x_right_pt + 5 and y_bot_pt - 5 <= py <= y_top_pt + 5:
                    c.circle(px, py, 1.4, stroke=0, fill=1)
                    c.setFont("Helvetica-Bold", 8)
                    c.drawString(px + 4, py + 4, pt.label)

            # Part labels at explicit label_pos, or at centroid otherwise
            for part in pattern.parts:
                if part.label_pos:
                    cx_pt, cy_pt = part.label_pos
                else:
                    pid_set = set()
                    for i in part.segment_ids:
                        if i < len(pattern.segments):
                            s = pattern.segments[i]
                            pid_set.add(s.a); pid_set.add(s.b)
                    pts = [(pattern.points[pid].x, pattern.points[pid].y)
                           for pid in pid_set if pid in pattern.points]
                    if not pts:
                        continue
                    cx_pt = sum(p[0] for p in pts) / len(pts)
                    cy_pt = sum(p[1] for p in pts) / len(pts)
                label = part.name
                if part.seam_allowance > 0:
                    label += f"   (SA {part.seam_allowance:g} cm)"
                c.setFont("Helvetica-BoldOblique", 11)
                lx = wx_to_pt(cx_pt); ly = wy_to_pt(cy_pt)
                tw = c.stringWidth(label, "Helvetica-BoldOblique", 11)
                c.setFillColorRGB(1, 1, 1)
                c.rect(lx - tw / 2 - 3, ly - 4, tw + 6, 14, stroke=0, fill=1)
                c.setFillColorRGB(0.25, 0.25, 0.25)
                c.drawCentredString(lx, ly, label)

            c.restoreState()

            # Tile-edge matching labels (drawn outside the clip so they're
            # always fully visible, even at the page edge).
            for label_text, wx, wy in crossings_global:
                if not (tile_x0 - 0.05 <= wx <= tile_x0 + content_w + 0.05
                        and tile_y0 - 0.05 <= wy <= tile_y0 + content_h + 0.05):
                    continue
                px = wx_to_pt(wx); py = wy_to_pt(wy)
                box_w = max(12, len(label_text) * 5 + 8)
                bx = px + 9; by = py + 9
                c.setFillColorRGB(1, 1, 1)
                c.setStrokeColorRGB(0, 0, 0); c.setLineWidth(0.4)
                c.rect(bx - box_w / 2, by - 6, box_w, 12, stroke=1, fill=1)
                c.setStrokeColorRGB(0.3, 0.3, 0.3); c.setLineWidth(0.3)
                c.line(px, py, bx - box_w / 2 + 1, by)
                c.setFillColorRGB(0, 0, 0); c.setLineWidth(0.4)
                c.circle(px, py, 1.1, stroke=1, fill=1)
                c.setFont("Helvetica-Bold", 8)
                c.drawCentredString(bx, by - 3, label_text)

            c.setFillColorRGB(0.4, 0.4, 0.4)
            c.setFont("Helvetica", 9)
            label = f"Row {row + 1} / {rows}  ·  Col {col + 1} / {cols}"
            c.drawString(x_left_pt, y_bot_pt - 12, label)
            c.drawRightString(x_right_pt, y_bot_pt - 12,
                              f"Page {page_num + 1} of {total_pages}  ·  print at 100%")
            c.showPage()
            page_num += 1
    c.save()


def _pdf_arrowhead(c, tip, tail):
    """Draw an arrowhead at `tip` (in PDF points) pointing away from `tail`."""
    dx = tip[0] - tail[0]; dy = tip[1] - tail[1]
    d = math.hypot(dx, dy) or 1.0
    ux, uy = dx / d, dy / d
    size = 7
    spread = 0.5
    cos_s = math.cos(spread); sin_s = math.sin(spread)
    b1 = (tip[0] - size * (ux * cos_s - uy * sin_s),
          tip[1] - size * (uy * cos_s + ux * sin_s))
    b2 = (tip[0] - size * (ux * cos_s + uy * sin_s),
          tip[1] - size * (uy * cos_s - ux * sin_s))
    c.line(tip[0], tip[1], b1[0], b1[1])
    c.line(tip[0], tip[1], b2[0], b2[1])


def _draw_crop_marks(c, x_left, y_bot, x_right, y_top):
    c.setStrokeColorRGB(0, 0, 0)
    c.setLineWidth(0.5)
    L = 14
    for x in (x_left, x_right):
        for y in (y_bot, y_top):
            c.line(x - L, y, x + L, y)
            c.line(x, y - L, x, y + L)


def _draw_cover_page(c, cols, rows, min_x, min_y, step_x, step_y,
                     content_w, content_h, total_w, total_h,
                     pattern: Pattern, referenced_pids,
                     page_idx, total_pages):
    page_h_pt = A4_H_CM * POINTS_PER_CM
    page_w_pt = A4_W_CM * POINTS_PER_CM

    c.setFont("Helvetica-Bold", 16)
    c.drawString(50, page_h_pt - 60, "Pattern — Assembly map")
    c.setFont("Helvetica", 10)
    c.drawString(50, page_h_pt - 80,
                 f"Pattern size: {total_w:.1f} cm wide x {total_h:.1f} cm tall")
    c.drawString(50, page_h_pt - 95,
                 f"Tiles: {cols} columns x {rows} rows ({cols * rows} pages)")
    c.drawString(50, page_h_pt - 110,
                 "Print at 100% scale (NO 'fit to page' or 'shrink to fit').")
    c.drawString(50, page_h_pt - 125,
                 "Each tile has a 1 cm overlap. Align overlap and tape.")
    c.drawString(50, page_h_pt - 140,
                 "Numbered boxes at tile edges match across adjacent pages — "
                 "align same-number marks to register pages precisely.")

    y = page_h_pt - 150
    if pattern.parts:
        c.setFont("Helvetica-Bold", 11)
        c.drawString(50, y, "Parts:")
        y -= 14
        c.setFont("Helvetica", 10)
        for part in pattern.parts:
            extra = f"  (seam allowance {part.seam_allowance:g} cm)" if part.seam_allowance > 0 else ""
            c.drawString(60, y, f"• {part.name}{extra}")
            y -= 13

    # Scale verification ruler (horizontal only; home printers don't scale axes
    # independently, so one axis is enough to prove 100% scale).
    ruler_y = max(140, y - 60)
    c.setFont("Helvetica-Bold", 10)
    c.drawString(50, ruler_y + 22,
                 "Verify print scale: a real ruler should match this to the millimetre.")
    rx = 50
    ry = ruler_y
    c.setStrokeColorRGB(0, 0, 0); c.setLineWidth(0.6)
    c.line(rx, ry, rx + 10 * POINTS_PER_CM, ry)
    c.setFont("Helvetica", 7)
    for i in range(11):
        x = rx + i * POINTS_PER_CM
        tick = 8 if i % 5 == 0 else 5
        c.line(x, ry, x, ry - tick)
        c.drawCentredString(x, ry - tick - 7, str(i))
    for i in range(101):
        x = rx + i * POINTS_PER_CM / 10
        if i % 10 == 0:
            continue
        h = 3 if i % 5 == 0 else 2
        c.line(x, ry, x, ry - h)
    c.setFont("Helvetica", 8)
    c.drawString(rx + 10 * POINTS_PER_CM + 8, ry - 2, "= 10 cm")

    # Assembly preview: whole pattern fitted into the available space, with
    # dashed tile boundary lines overlaid and a label in each tile region
    # matching the R{n}C{n} on the printed tile pages. Row 0 sits at the
    # bottom of the preview because in world coords row 0 is the bottom set
    # of tiles — that way the preview mirrors the physical assembled layout.
    map_x = 50; map_y = 60
    map_w = page_w_pt - 100
    map_h = max(80, ruler_y - 100)
    pattern_w_pt = max(0.1, total_w) * POINTS_PER_CM
    pattern_h_pt = max(0.1, total_h) * POINTS_PER_CM
    fit_scale = min(map_w / pattern_w_pt, map_h / pattern_h_pt)
    mini_w = pattern_w_pt * fit_scale
    mini_h = pattern_h_pt * fit_scale
    mini_x = map_x + (map_w - mini_w) / 2
    mini_y = map_y + (map_h - mini_h) / 2

    def wx_to_mini(wx):
        return mini_x + (wx - min_x) * POINTS_PER_CM * fit_scale

    def wy_to_mini(wy):
        return mini_y + (wy - min_y) * POINTS_PER_CM * fit_scale

    # Faint frame around the whole preview
    c.setStrokeColorRGB(0.75, 0.75, 0.75); c.setLineWidth(0.4)
    c.rect(mini_x, mini_y, mini_w, mini_h, stroke=1, fill=0)

    # Pattern segments, clipped to the preview area
    c.saveState()
    clip = c.beginPath()
    clip.rect(mini_x, mini_y, mini_w, mini_h)
    c.clipPath(clip, stroke=0, fill=0)
    for seg in pattern.segments:
        pa = pattern.points.get(seg.a); pb = pattern.points.get(seg.b)
        if not pa or not pb:
            continue
        if seg.style == 'dotted':
            c.setDash(2, 1.5); c.setLineWidth(0.4)
        else:
            c.setDash(); c.setLineWidth(0.6)
        c.setStrokeColorRGB(0, 0, 0)
        if seg.kind == 'line':
            c.line(wx_to_mini(pa.x), wy_to_mini(pa.y),
                   wx_to_mini(pb.x), wy_to_mini(pb.y))
        else:
            pts = cubic_bezier_samples((pa.x, pa.y), seg.c1, seg.c2,
                                       (pb.x, pb.y), n=32)
            path = c.beginPath()
            path.moveTo(wx_to_mini(pts[0][0]), wy_to_mini(pts[0][1]))
            for px, py in pts[1:]:
                path.lineTo(wx_to_mini(px), wy_to_mini(py))
            c.drawPath(path, stroke=1, fill=0)
    c.setDash()

    # Tile boundary lines (between adjacent tiles)
    c.setStrokeColorRGB(0.35, 0.5, 0.8); c.setLineWidth(0.5)
    c.setDash(3, 2)
    for col in range(1, cols):
        gx = wx_to_mini(min_x + col * step_x)
        c.line(gx, mini_y, gx, mini_y + mini_h)
    for row in range(1, rows):
        gy = wy_to_mini(min_y + row * step_y)
        c.line(mini_x, gy, mini_x + mini_w, gy)
    c.setDash()
    c.restoreState()

    # Tile labels in each region's bottom-left corner
    c.setFillColorRGB(0.25, 0.4, 0.7)
    c.setFont("Helvetica-Bold", 8)
    for row in range(rows):
        for col in range(cols):
            tile_left = min_x + col * step_x
            tile_bottom = min_y + row * step_y
            lx = wx_to_mini(tile_left) + 3
            ly = wy_to_mini(tile_bottom) + 3
            c.drawString(lx, ly, f"R{row + 1}C{col + 1}")

    c.setFillColorRGB(0.4, 0.4, 0.4); c.setFont("Helvetica", 9)
    c.drawRightString((A4_W_CM - 1) * POINTS_PER_CM, 20,
                      f"Page {page_idx} of {total_pages}")


# ---------- entry point ----------

def main():
    root = tk.Tk()
    try:
        style = ttk.Style(root)
        if 'vista' in style.theme_names():
            style.theme_use('vista')
    except Exception:
        pass
    App(root)
    root.mainloop()


if __name__ == '__main__':
    main()
