# Patternmaking

A 2D drafting tool for clothes patternmaking. Place labelled points, connect them with
straight lines or cubic Bezier curves, group segments into named parts, apply seam
allowances, and export the result as a tiled A4 PDF at true 1:1 scale for printing,
cutting and assembly.

I wrote it because the existing options didn't fit: commercial CAD patternmaking software
is expensive and aimed at industry workflows, and general vector editors have no concept
of a seam allowance, a dart, or printing at a guaranteed physical scale. I wanted to draft
a rugby short, print it on a home A4 printer, and have the printed pieces measure what the
screen said they measured.

Python 3, Tkinter, ~5,000 lines. `examples/` contains a drafted rugby short front panel
and the tiled PDF it exports to.

## Features

**Drafting**
- Points, straight segments and cubic Bezier segments with draggable handles
- Undo/redo across all editing operations
- Split a segment at its midpoint, move a point to a measured distance along a line,
  square a selection into a rectangle
- Grid, corner angles, and live segment lengths displayed on canvas

**Garment concepts**
- Named parts built from a closed loop of segments (e.g. "Front panel")
- Seam allowances per part, with per-edge overrides
- Darts, notches, grain lines, and fold lines marked as dotted internal segments
- Mirror, rotate, resize and duplicate a part
- Seams labelled as joined so matching edges stay consistent

**Output**
- Export to tiled A4 PDF at true 1:1 scale
- 1 cm tile overlap and crop marks so pages can be aligned and taped by hand
- Cover sheet showing the tile grid and assembly order
- Patterns saved and loaded as JSON

## How it works

**Data model** - `Point`, `Segment`, `Dart`, `Part`, `Notch` and `Pattern` are dataclasses
serialised to JSON with `asdict`. Units are centimetres throughout; conversion to points
(72/2.54) happens only at PDF export, so the model never carries display or print state.

**Geometry** - the interesting problems were:

- *Seam allowances.* A seam allowance is an outward offset of a closed loop, and the
  allowance can differ per edge, which rules out a simple uniform offset.
  `offset_closed_polyline_variable` offsets each edge by its own distance and places the new
  vertex at the intersection of the two adjacent offset edges, falling back to a bisector
  miter when those edges are near-parallel. Outward is resolved from the winding direction.
  So a part can carry 1.5 cm on one edge and 1 cm on the next and the corner still closes
  correctly.
- *Loop detection.* Segments are drawn in whatever order the user likes, so
  `chain_segments_into_loop` reassembles an arbitrary set of segments end-to-end and reports
  whether they form a single closed chain, which is what makes a valid part.
- *Orientation.* `polyline_signed_area` determines winding direction, so "outward" is
  outward regardless of which way round the loop was drawn.
- Cubic Bezier segments are sampled to polylines before any geometric operation, at a
  higher resolution for export than for on-screen rendering.

**Rendering** is a Tkinter canvas with its own pan/zoom transform. **Export** uses reportlab
to lay the pattern across as many A4 tiles as it needs, with overlap and crop marks.

## Running it

```
git clone https://github.com/JoshDBrooks/patternmaking.git
cd patternmaking
pip install -r requirements.txt
python pattern.py
```

Python 3.11+. Tkinter ships with CPython on Windows and macOS; on Linux install
`python3-tk`. reportlab is only needed for PDF export.

## Layout

```
pattern.py      the application - data model, geometry, UI, PDF export
make_icon.py    generates pattern.ico
examples/       a drafted rugby short front panel and its exported tiled PDF
```

## What I'd do differently

Honest notes, since this grew from a personal tool rather than being designed up front:

- **It's one 5,000-line module.** The geometry functions, the data model, the Tkinter UI and
  the PDF exporter have no dependencies on each other in principle, and should be four
  packages. They aren't, because the file grew feature by feature as I needed things.
- **There are no automated tests.** The geometry is the part that most deserves them.
  Offsetting and loop chaining have edge cases that I currently find by drawing a shape and
  looking at it.
- **PDF export offers to `pip install` reportlab from inside the GUI.** Convenient when the
  only user is me; not something that belongs in software other people run.
- Self-intersection on inward offsets isn't handled, so very tight concave corners can
  produce a crossed outline that needs manual correction.

## License

MIT — see [LICENSE](LICENSE).
