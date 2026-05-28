#!/usr/bin/env python3
# red_tile_identifier.py - red square outline detector with ROI calibration and confidence overlays.

import argparse
import json
import re
import sys
import time
from pathlib import Path

import cv2
import numpy as np

try:
    import mss
    HAVE_MSS = True
except Exception:
    HAVE_MSS = False

try:
    from PIL import ImageGrab
    HAVE_IMAGEGRAB = True
except Exception:
    HAVE_IMAGEGRAB = False

try:
    import psutil
    HAVE_PSUTIL = True
except Exception:
    HAVE_PSUTIL = False

IS_WINDOWS = sys.platform.startswith("win")
if IS_WINDOWS:
    try:
        import ctypes
        ctypes.windll.user32.SetProcessDPIAware()
    except Exception:
        pass

CFG_PATH = "red_tile_identifier.cal.json"


def clamp_roi_rel_to_window(roi_rel, win_rect):
    rx, ry, rw, rh = roi_rel
    _, _, ww, wh = win_rect
    rx = max(0, min(rx, max(0, ww - 1)))
    ry = max(0, min(ry, max(0, wh - 1)))
    rw = max(1, min(rw, max(1, ww - rx)))
    rh = max(1, min(rh, max(1, wh - ry)))
    return (rx, ry, rw, rh)


def select_box(title: str, img_bgr):
    print(f"[select] {title} (ENTER=save, C=keep/cancel)")
    sel = cv2.selectROI(title, img_bgr, False, False)
    cv2.destroyWindow(title)
    if sel is None or sel[2] <= 0 or sel[3] <= 0:
        return None
    return tuple(map(int, sel))


def parse_args():
    parser = argparse.ArgumentParser(description="Detect red square tile outlines in a selected window region.")
    parser.add_argument("--window-title", type=str, required=True, help="title text for the window to inspect")
    parser.add_argument(
        "--window-title-mode",
        type=str,
        default="contains",
        choices=["contains", "equals", "startswith", "regex"],
    )
    parser.add_argument("--window-index", type=int, default=0)
    parser.add_argument("--no-window-prompt", action="store_true")

    parser.add_argument("--debug", action="store_true", help="show the binary red mask alongside the overlay")
    parser.add_argument("--scale", type=float, default=1.00)
    parser.add_argument("--red-hue-tol", type=float, default=0.58)
    parser.add_argument("--red-min-score", type=float, default=0.56)
    parser.add_argument("--band-px", type=int, default=2)
    parser.add_argument("--min-area", type=float, default=70.0)
    parser.add_argument("--max-area", type=float, default=1_000_000.0)
    parser.add_argument("--fill-max-score", type=float, default=0.61)
    parser.add_argument("--min-confidence", type=float, default=0.41)
    parser.add_argument("--edge-min", type=float, default=0.56)
    parser.add_argument("--connect-iter", type=int, default=3)
    parser.add_argument("--detect-every-n", type=int, default=1)

    return parser.parse_args()


def alt_down() -> bool:
    if not IS_WINDOWS:
        return False
    try:
        import ctypes
        user32 = ctypes.windll.user32
        return any((user32.GetAsyncKeyState(vk) & 0x8000) for vk in (0x12, 0xA4, 0xA5))
    except Exception:
        return False


def shift_down() -> bool:
    if not IS_WINDOWS:
        return False
    try:
        import ctypes
        user32 = ctypes.windll.user32
        return any((user32.GetAsyncKeyState(vk) & 0x8000) for vk in (0x10, 0xA0, 0xA1))
    except Exception:
        return False


def _client_rect(hwnd):
    import ctypes
    from ctypes import wintypes

    user32 = ctypes.windll.user32
    rect = wintypes.RECT()
    if not user32.GetClientRect(hwnd, ctypes.byref(rect)):
        return None
    p0 = wintypes.POINT(0, 0)
    p1 = wintypes.POINT(rect.right, rect.bottom)
    if not user32.ClientToScreen(hwnd, ctypes.byref(p0)):
        return None
    if not user32.ClientToScreen(hwnd, ctypes.byref(p1)):
        return None
    left, top = p0.x, p0.y
    width, height = max(0, p1.x - p0.x), max(0, p1.y - p0.y)
    if width < 32 or height < 32:
        return None
    return (left, top, width, height)


def _proc_name(pid):
    if not HAVE_PSUTIL:
        return None
    try:
        return psutil.Process(pid).name()
    except Exception:
        return None


def list_windows_matching(title_text, mode="contains"):
    if not IS_WINDOWS:
        return []
    import ctypes
    from ctypes import wintypes

    user32 = ctypes.windll.user32
    enum_proc = ctypes.WINFUNCTYPE(ctypes.c_bool, wintypes.HWND, wintypes.LPARAM)

    def match(title):
        title = title or ""
        needle = title_text or ""
        a, b = title.lower(), needle.lower()
        if mode == "contains":
            return b in a
        if mode == "equals":
            return a == b
        if mode == "startswith":
            return a.startswith(b)
        if mode == "regex":
            try:
                return re.search(title_text, title) is not None
            except Exception:
                return False
        return False

    results = []

    def callback(hwnd, _lparam):
        if not user32.IsWindowVisible(hwnd):
            return True
        length = user32.GetWindowTextLengthW(hwnd)
        if length == 0:
            return True
        buffer = ctypes.create_unicode_buffer(length + 1)
        user32.GetWindowTextW(hwnd, buffer, length + 1)
        title = buffer.value
        if not match(title):
            return True
        rect = _client_rect(hwnd)
        if not rect:
            return True
        pid = ctypes.c_ulong()
        user32.GetWindowThreadProcessId(hwnd, ctypes.byref(pid))
        results.append({
            "hwnd": hwnd,
            "title": title,
            "rect": rect,
            "pid": pid.value,
            "proc": _proc_name(pid.value),
        })
        return True

    user32.EnumWindows(enum_proc(callback), 0)
    return results


def pick_window_interactive(matches):
    if not matches:
        return None
    print("\n[window] Multiple matches. Choose one:")
    for i, match in enumerate(matches, 1):
        width, height = match["rect"][2], match["rect"][3]
        print(f"  [{i}] {match['title']}  {width}x{height}  pid={match['pid']} exe={match['proc'] or '?'}")
    try:
        raw = input(f"Select [1..{len(matches)}] (default 1): ").strip()
    except EOFError:
        raw = ""
    index = 1 if not raw else max(1, min(int(raw), len(matches)))
    return matches[index - 1]


def wait_for_valid_capture(hwnd, timeout=2.0, min_brightness=5.0):
    started = time.time()
    while time.time() - started < timeout:
        rect = _client_rect(hwnd)
        if not rect:
            time.sleep(0.05)
            continue
        frame, _, _ = capture_window(rect)
        if frame is not None and frame.size > 0 and float(frame.mean()) >= min_brightness:
            return rect
        time.sleep(0.05)
    return _client_rect(hwnd)


def load_cfg():
    path = Path(CFG_PATH)
    if not path.exists():
        return {}
    try:
        return json.loads(path.read_text())
    except Exception:
        return {}


def save_cfg(data):
    try:
        Path(CFG_PATH).write_text(json.dumps(data, indent=2))
    except Exception:
        pass


def capture_window(rect):
    left, top, width, height = rect
    if HAVE_MSS:
        with mss.mss() as sct:
            grab = sct.grab({"left": left, "top": top, "width": width, "height": height})
            frame = np.array(grab)[:, :, :3]
            return frame, left, top
    if HAVE_IMAGEGRAB:
        image = ImageGrab.grab(bbox=(left, top, left + width, top + height))
        frame = cv2.cvtColor(np.array(image), cv2.COLOR_RGB2BGR)
        return frame, left, top
    raise RuntimeError("screen capture requires either mss or Pillow ImageGrab")


def _noop(_value):
    pass


class KnobPanel:
    def __init__(self, args):
        self.win = "vision tuning"
        cv2.namedWindow(self.win, cv2.WINDOW_AUTOSIZE)

        def f2i(value, scale=100):
            return int(round(value * scale))

        cv2.createTrackbar("hue_deg", self.win, int(round(args.red_hue_tol)), 60, _noop)
        cv2.createTrackbar("scale_%", self.win, int(args.scale * 100), 100, _noop)
        cv2.createTrackbar("min_sc_%", self.win, f2i(args.red_min_score), 100, _noop)
        cv2.createTrackbar("band_px", self.win, int(args.band_px), 8, _noop)
        cv2.createTrackbar("fill_max_%", self.win, f2i(args.fill_max_score), 100, _noop)
        cv2.createTrackbar("min_conf_%", self.win, f2i(args.min_confidence), 100, _noop)
        cv2.createTrackbar("edge_min_%", self.win, f2i(args.edge_min), 100, _noop)
        cv2.createTrackbar("connect_iter", self.win, int(args.connect_iter), 3, _noop)
        cv2.createTrackbar("detect_every_n", self.win, int(args.detect_every_n), 60, _noop)
        max_area_k = int(max(1, min(1000, round(args.max_area / 1000.0))))
        cv2.createTrackbar("min_area", self.win, int(args.min_area), 5000, _noop)
        cv2.createTrackbar("max_area_k", self.win, max_area_k, 1000, _noop)
        cv2.setTrackbarPos("scale_%", self.win, max(40, min(100, int(args.scale * 100))))

    def apply_to(self, args):
        i2f = lambda value: float(value) / 100.0
        args.red_hue_tol = float(cv2.getTrackbarPos("hue_deg", self.win))
        args.scale = max(0.40, min(1.00, cv2.getTrackbarPos("scale_%", self.win) / 100.0))
        args.red_min_score = i2f(cv2.getTrackbarPos("min_sc_%", self.win))
        args.band_px = max(1, cv2.getTrackbarPos("band_px", self.win))
        args.fill_max_score = i2f(cv2.getTrackbarPos("fill_max_%", self.win))
        args.min_confidence = i2f(cv2.getTrackbarPos("min_conf_%", self.win))
        args.edge_min = i2f(cv2.getTrackbarPos("edge_min_%", self.win))
        args.connect_iter = max(0, int(cv2.getTrackbarPos("connect_iter", self.win)))
        args.detect_every_n = max(1, int(cv2.getTrackbarPos("detect_every_n", self.win)))
        args.min_area = max(1.0, float(cv2.getTrackbarPos("min_area", self.win)))
        args.max_area = float(max(1, int(cv2.getTrackbarPos("max_area_k", self.win))) * 1000)


def _to_hsv(bgr):
    hsv = cv2.cvtColor(bgr, cv2.COLOR_BGR2HSV)
    hue, saturation, value = cv2.split(hsv)
    return hue.astype(np.float32), saturation.astype(np.float32) / 255.0, value.astype(np.float32) / 255.0


def _red_score_map(bgr, hue_tol_deg=16.0):
    hue, saturation, value = _to_hsv(bgr)
    distance = np.minimum(np.abs(hue - 0.0), np.abs(180.0 - hue))
    preference = np.clip(1.0 - distance / float(max(1e-6, hue_tol_deg)), 0.0, 1.0)
    return preference * saturation * value


def detect_red_rectangles_simple(
    frame_bgr,
    *,
    red_hue_tol=0.0,
    red_min_score=0.64,
    band_px=4,
    connect_iter=1,
    fill_max_score=0.22,
    min_confidence=0.50,
    edge_min=0.60,
    min_area=70.0,
    max_area=1e6,
):
    score = _red_score_map(frame_bgr, hue_tol_deg=red_hue_tol)
    mask = (score >= red_min_score).astype(np.uint8) * 255
    kernel_size = max(1, int(band_px))
    kernel = cv2.getStructuringElement(cv2.MORPH_RECT, (kernel_size, kernel_size))
    if connect_iter > 0:
        mask = cv2.morphologyEx(mask, cv2.MORPH_CLOSE, kernel, iterations=1)
        mask = cv2.dilate(mask, kernel, iterations=int(connect_iter))

    contours, _ = cv2.findContours(mask, cv2.RETR_LIST, cv2.CHAIN_APPROX_SIMPLE)
    results = []
    height, width = frame_bgr.shape[:2]

    for contour in contours:
        if len(contour) < 5:
            continue
        rect = cv2.minAreaRect(contour)
        (cx, cy), (rw, rh), _angle = rect
        area_rect = float(rw * rh)
        if area_rect < min_area or area_rect > max_area:
            continue

        box = cv2.boxPoints(rect).astype(np.int32)
        polygon_mask = np.zeros((height, width), np.uint8)
        cv2.fillPoly(polygon_mask, [box], 255)
        fill = float((score * (polygon_mask > 0)).sum() / max(1, int((polygon_mask > 0).sum())))

        edge_mask = np.zeros((height, width), np.uint8)
        thickness = max(1, int(round(band_px)))
        cv2.polylines(edge_mask, [box], True, 255, thickness=thickness, lineType=cv2.LINE_AA)
        edge_pixels = int((edge_mask > 0).sum())
        edge_hits = int(((mask > 0) & (edge_mask > 0)).sum())
        edge_density = 0.0 if edge_pixels == 0 else edge_hits / float(edge_pixels)

        area_contour = float(cv2.contourArea(contour))
        rectangularity = 0.0 if area_rect <= 1e-6 else max(0.0, min(1.0, area_contour / area_rect))
        short_side, long_side = min(rw, rh), max(rw, rh)
        aspect_score = max(0.0, min(1.0, short_side / max(1.0, long_side)))
        low_fill = max(0.0, 1.0 - (fill / max(1e-6, fill_max_score)))
        confidence = max(
            0.0,
            min(1.0, 0.30 * rectangularity + 0.25 * aspect_score + 0.20 * low_fill + 0.25 * edge_density),
        )

        if edge_density < edge_min or confidence < min_confidence or fill > fill_max_score:
            continue
        results.append((float(cx), float(cy), confidence, rect, float(fill), float(edge_density)))

    results.sort(key=lambda item: (item[2] * (item[3][1][0] * item[3][1][1])), reverse=True)
    return results, mask


def draw_overlay(base_bgr, candidates, header_text=None):
    view = base_bgr.copy()
    for cx, cy, confidence, rotated_rect, _fill, edge_density in candidates:
        box = cv2.boxPoints(rotated_rect).astype(np.int32)
        color = (0, 80 + int(175 * confidence), 0)
        cv2.polylines(view, [box], True, color, 2)
        cv2.circle(view, (int(cx), int(cy)), 3, (255, 0, 0), -1)
        cv2.putText(
            view,
            f"{confidence:.2f}/{edge_density:.2f}",
            (int(cx) + 6, int(cy) - 6),
            cv2.FONT_HERSHEY_SIMPLEX,
            0.5,
            color,
            1,
            cv2.LINE_AA,
        )
    if header_text:
        cv2.rectangle(view, (0, 0), (view.shape[1], 26), (30, 30, 30), -1)
        cv2.putText(view, header_text, (8, 18), cv2.FONT_HERSHEY_SIMPLEX, 0.55, (255, 255, 255), 1, cv2.LINE_AA)
    return view


def main():
    args = parse_args()
    args.red_hue_tol = float(args.red_hue_tol) * 60.0 if args.red_hue_tol <= 1.0 else float(args.red_hue_tol)
    cfg = load_cfg()

    matches = list_windows_matching(args.window_title, args.window_title_mode)
    if not matches:
        print(f"[window] No visible windows match {args.window_title_mode} '{args.window_title}'.", file=sys.stderr)
        sys.exit(1)
    if args.window_index > 0 and args.window_index <= len(matches):
        chosen = matches[args.window_index - 1]
    elif len(matches) == 1 or args.no_window_prompt:
        chosen = max(matches, key=lambda item: item["rect"][2] * item["rect"][3])
    else:
        chosen = pick_window_interactive(matches)
        if chosen is None:
            print("[window] No selection made.", file=sys.stderr)
            sys.exit(1)

    hwnd = chosen["hwnd"]
    print(f"[window] Found: '{chosen['title']}' pid={chosen['pid']} exe={chosen.get('proc') or '?'}")
    win_rect = wait_for_valid_capture(hwnd, timeout=2.0) or chosen["rect"]
    print(f"[window] Using capture area: {win_rect}")

    def prompt_or_keep(name, previous):
        if previous:
            print(f"[{name}] Existing: {previous}. Select a new box or press C to keep.")
        image, _, _ = capture_window(win_rect)
        selected = select_box(f"{name} - ENTER=save, C=keep", image)
        if selected:
            return clamp_roi_rel_to_window(selected, win_rect)
        return previous

    roi_rel_previous = tuple(cfg.get("ROI_REL")) if cfg.get("ROI_REL") else None
    while True:
        roi_rel = prompt_or_keep("Select ROI", roi_rel_previous)
        if roi_rel:
            break
        print("[roi] ROI is required. Please select again.")

    cfg["ROI_REL"] = list(roi_rel)
    save_cfg(cfg)
    print(f"[roi] Active ROI (relative): {roi_rel}")
    print("[keys] ALT=quit, SHIFT=tuning panel, R=reselect ROI, Q/Esc=quit preview")

    knobs = None
    tuning_mode = False
    previous_shift = False
    frame_index = 0
    last_found = []
    last_mask = None
    last_overlay = None

    try:
        while True:
            if alt_down():
                print("[stop] ALT pressed.")
                break

            current_shift = shift_down()
            if current_shift and not previous_shift:
                tuning_mode = not tuning_mode
                print(f"[mode] Tuning panel {'ON' if tuning_mode else 'OFF'}")
                if tuning_mode and knobs is None:
                    knobs = KnobPanel(args)
                    cv2.setTrackbarPos("hue_deg", knobs.win, int(round(args.red_hue_tol)))
                elif not tuning_mode and knobs is not None:
                    try:
                        cv2.destroyWindow(knobs.win)
                    except Exception:
                        pass
                    knobs = None
                    if not args.debug:
                        try:
                            cv2.destroyWindow("red mask")
                        except Exception:
                            pass
            previous_shift = current_shift

            if knobs is not None:
                knobs.apply_to(args)

            new_rect = _client_rect(hwnd)
            if new_rect and new_rect != win_rect:
                win_rect = new_rect

            frame_window, window_x, window_y = capture_window(win_rect)
            if float(frame_window.mean()) < 3.0:
                win_rect = wait_for_valid_capture(hwnd, timeout=1.0) or win_rect
                frame_window, window_x, window_y = capture_window(win_rect)

            rx, ry, rw, rh = roi_rel
            x0 = max(0, min(rx, frame_window.shape[1] - 1))
            y0 = max(0, min(ry, frame_window.shape[0] - 1))
            x1 = max(x0 + 1, min(rx + rw, frame_window.shape[1]))
            y1 = max(y0 + 1, min(ry + rh, frame_window.shape[0]))
            frame_roi = frame_window[y0:y1, x0:x1]

            scale = args.scale
            frame_proc = (
                cv2.resize(
                    frame_roi,
                    (int(frame_roi.shape[1] * scale), int(frame_roi.shape[0] * scale)),
                    interpolation=cv2.INTER_AREA,
                )
                if scale != 1.0
                else frame_roi
            )

            if frame_index % max(1, args.detect_every_n) == 0:
                last_found, last_mask = detect_red_rectangles_simple(
                    frame_bgr=frame_proc,
                    red_hue_tol=args.red_hue_tol,
                    red_min_score=args.red_min_score,
                    band_px=args.band_px,
                    connect_iter=args.connect_iter,
                    fill_max_score=args.fill_max_score,
                    min_confidence=args.min_confidence,
                    edge_min=args.edge_min,
                    min_area=args.min_area * (scale * scale),
                    max_area=args.max_area * (scale * scale),
                )
                mode_label = "TUNING" if tuning_mode else "Detection view"
                last_overlay = draw_overlay(frame_proc, last_found, header_text=f"{mode_label} - {len(last_found)} candidates")

            frame_index += 1

            cv2.imshow("red_tile_identifier (view)", last_overlay if last_overlay is not None else frame_proc)
            if args.debug or tuning_mode:
                if last_mask is not None:
                    cv2.imshow("red mask", last_mask)

            key = cv2.waitKey(1) & 0xFF
            if key in (ord("q"), 27):
                break
            if key == ord("r"):
                image, _, _ = capture_window(win_rect)
                selected = select_box("Select ROI (ENTER=save, C=cancel)", image)
                if selected:
                    roi_rel = clamp_roi_rel_to_window(selected, win_rect)
                    cfg["ROI_REL"] = list(roi_rel)
                    save_cfg(cfg)
                    frame_index = 0
                    print(f"[roi] Updated: {roi_rel}")

            if not HAVE_MSS:
                time.sleep(0.01)

    except KeyboardInterrupt:
        pass
    finally:
        for window_name in ["vision tuning", "red_tile_identifier (view)", "red mask"]:
            try:
                cv2.destroyWindow(window_name)
            except Exception:
                pass
        try:
            cv2.destroyAllWindows()
        except Exception:
            pass


if __name__ == "__main__":
    main()
