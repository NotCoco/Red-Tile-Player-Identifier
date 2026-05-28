# Red Tile Player Identifier

A small computer-vision experiment for identifying red square tile outlines in a captured window region.

The goal is to detect squares viewed at different angles on a plane, outline them in a live preview, and report a confidence score for each candidate. The script is focused only on image capture, thresholding, shape filtering, and visual feedback.

## Demo

![Red tile detection demo](demos/red_tile_demo.gif)

## Additional Detection Demo

![Red tile detection demo](demos/red_demo_2.gif)

## What It Does

- Captures a selected window area.
- Lets you select a region of interest.
- Builds a red-score mask in HSV color space.
- Fits rotated rectangles to candidate contours.
- Scores candidates by edge density, rectangularity, aspect ratio, and low interior fill.
- Draws the detected square outline, center point, and confidence/edge-density values.
- Provides an optional tuning panel for threshold and filter parameters.

## Usage

Install the usual OpenCV/Numpy capture dependencies, then run:

```bash
python red_tile_identifier.py --window-title "Window title"
```

Useful options:

```bash
python red_tile_identifier.py --debug
python red_tile_identifier.py --window-title-mode contains
python red_tile_identifier.py --scale 0.75
```

Preview keys:

- `Shift`: toggle the tuning panel.
- `R`: reselect the region of interest.
- `Q` or `Esc`: quit from the preview window.
- `Alt`: quit globally on Windows.
