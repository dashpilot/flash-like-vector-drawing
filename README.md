# Flash-like Vector Drawing App

A minimal vector drawing app that mimics Adobe Flash/Animate behavior. Built with vanilla JavaScript.

## Features

### Tools
- **Selection (V)** — Select, move, reshape segments
- **Pen / Line (P)** — Draw vector lines
- **Paint Bucket (B)** — Fill closed shapes with color

### Pen / Line Tool (P)
- **Drag only** — you must press and hold the mouse button to draw; each drag creates one segment
- **Shift held during drag** — constrains to straight lines or 45° angles (0°, 45°, 90°, etc.)
- Each segment is created only while the mouse button is held (no click-to-place)

### Selection Tool (V)
- **Click** on a segment to select it (blue dashed highlight)
- **Shift + click** — add or remove segments from selection (multi-select)
- **Drag on empty space** — marquee selection; draws a rectangle and selects all segments within it (blue semi-transparent fill)
- **Drag near an endpoint** (within 10px) — move only that point of the line
- **Drag on segment body** — pull/reshape the curve; straight lines become curves
- **Drag on shared vertex** (where two+ lines meet) — moves that point for all connected segments
- **Command-Z** (Ctrl-Z) — undo | **Command-Shift-Z** — redo
- **Properties panel** — Right side: stroke width, stroke color (swatches), paint bucket fill color

### Line as Knife
- When a new line crosses an existing line, both are split at the intersection
- All 4 resulting pieces become individually selectable segments

### Keyboard Shortcuts
- **V** — Selection tool
- **P** — Pen/Line tool
- **Delete / Backspace** — Delete selected segment(s)

## Run locally

Open `index.html` in a browser, or use a local server:

```bash
python3 -m http.server 3333
```

Then visit http://localhost:3333

## Styling

The UI uses a Vercel-inspired light mode with Geist font.
