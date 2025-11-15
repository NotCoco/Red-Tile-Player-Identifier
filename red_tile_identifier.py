#!/usr/bin/env python3
# red_tile_clicker.py — red-outline detector + ROI + WS commands + action boxes (logout/login)

import argparse, time, sys, json, re, math, random, threading
from pathlib import Path
from queue import SimpleQueue, Empty
import numpy as np
import cv2

# Fast screen grab
try:
    import mss
    HAVE_MSS = True
except Exception:
    HAVE_MSS = False

import pyautogui
pyautogui.PAUSE = 0.0
pyautogui.FAILSAFE = False  # IMPORTANT: never re-enable later

try:
    import psutil
    HAVE_PSUTIL = True
except Exception:
    HAVE_PSUTIL = False

# Optional WebSocket server
HAVE_WS = False
try:
    import websockets  # pip install websockets
    HAVE_WS = True
except Exception:
    HAVE_WS = False

IS_WINDOWS = sys.platform.startswith("win")
if IS_WINDOWS:
    try:
        import ctypes
        ctypes.windll.user32.SetProcessDPIAware()
    except Exception:
        pass

CFG_PATH = "red_tile_clicker.cal.json"

# ------------------ helpers ------------------
def exe_dir() -> Path:
    if getattr(sys, "frozen", False):
        return Path(sys.executable).resolve().parent
    return Path(__file__).resolve().parent

def assets_dir() -> Path:
    if getattr(sys, "frozen", False) and hasattr(sys, "_MEIPASS"):
        return Path(sys._MEIPASS) / "assets"
    elif getattr(sys, "frozen", False):
        return Path(sys.executable).resolve().parent / "assets"
    else:
        return Path(__file__).resolve().parent / "assets"

def clamp_roi_rel_to_window(roi_rel, win_rect):
    rx, ry, rw, rh = roi_rel
    _, _, ww, wh = win_rect
    rx = max(0, min(rx, max(0, ww-1)))
    ry = max(0, min(ry, max(0, wh-1)))
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

def rect_center_abs(rel_rect, win_rect):
    if not rel_rect or not win_rect: return None
    rx, ry, rw, rh = rel_rect
    wx, wy, _, _ = win_rect
    return (int(wx + rx + rw/2), int(wy + ry + rh/2))

# ------------------ CLI ------------------
def parse_args():
    p = argparse.ArgumentParser()
    # window
    p.add_argument("--window-title", type=str, default="Roat Pkz")
    p.add_argument("--window-title-mode", type=str, default="contains",
                   choices=["contains","equals","startswith","regex"])
    p.add_argument("--window-index", type=int, default=0)
    p.add_argument("--no-window-prompt", action="store_true")

    # mouse / timing
    p.add_argument("--rate", type=float, default=1.0)
    p.add_argument("--move-duration", type=float, default=0.02)
    p.add_argument("--hover-delay", type=float, default=0.20)
    p.add_argument("--down-up-gap", type=float, default=0.02)
    p.add_argument("--button", type=str, default="left", choices=["left","right","middle"])
    p.add_argument("--double", action="store_true")

    # display
    p.add_argument("--debug", action="store_true")
    p.add_argument("--dry-run", action="store_true")

    # detection defaults
    p.add_argument("--scale", type=float, default=1.00)
    p.add_argument("--red-hue-tol", type=float, default=0.58)   # <=1 → fraction of 60°, else degrees
    p.add_argument("--red-min-score", type=float, default=0.56)
    p.add_argument("--band-px", type=int, default=2)

    # filters
    p.add_argument("--min-area", type=float, default=70.0)
    p.add_argument("--max-area", type=float, default=1_000_000.0)
    p.add_argument("--fill-max-score", type=float, default=0.61)
    p.add_argument("--min-confidence", type=float, default=0.41)
    p.add_argument("--edge-min", type=float, default=0.56)
    p.add_argument("--connect-iter", type=int, default=3)

    # target/anti-repeat
    p.add_argument("--min-switch-px", type=int, default=28)
    p.add_argument("--target-cooldown", type=float, default=1.5)
    p.add_argument("--grid", type=int, default=20)
    p.add_argument("--skip-when-no-new", dest="skip_when_no_new", action="store_true", default=True)
    p.add_argument("--no-skip-when-no-new", dest="skip_when_no_new", action="store_false")

    # frequency
    p.add_argument("--detect-every-n", type=int, default=1)

    # websocket (remote control)
    p.add_argument("--ws-host", type=str, default="0.0.0.0")
    p.add_argument("--ws-port", type=int, default=8765)
    p.add_argument("--no-ws", action="store_true", help="disable websocket server")
    p.add_argument("--ws-token", type=str, default="", help="optional shared secret; require {'token':...}")

    return p.parse_args()

# ------------------ Keys ------------------
def alt_down() -> bool:
    if not IS_WINDOWS: return False
    try:
        import ctypes
        u = ctypes.windll.user32
        return any((u.GetAsyncKeyState(vk) & 0x8000) for vk in (0x12, 0xA4, 0xA5))
    except Exception:
        return False

def shift_down() -> bool:
    if not IS_WINDOWS: return False
    try:
        import ctypes
        u = ctypes.windll.user32
        return any((u.GetAsyncKeyState(vk) & 0x8000) for vk in (0x10, 0xA0, 0xA1))
    except Exception:
        return False

# ------------------ Window helpers ------------------
def _client_rect(hwnd):
    import ctypes
    from ctypes import wintypes
    u = ctypes.windll.user32
    r = wintypes.RECT()
    if not u.GetClientRect(hwnd, ctypes.byref(r)):
        return None
    p0 = wintypes.POINT(0,0); p1 = wintypes.POINT(r.right, r.bottom)
    if not u.ClientToScreen(hwnd, ctypes.byref(p0)): return None
    if not u.ClientToScreen(hwnd, ctypes.byref(p1)): return None
    left, top = p0.x, p0.y
    w, h = max(0, p1.x - p0.x), max(0, p1.y - p0.y)
    if w < 32 or h < 32: return None
    return (left, top, w, h)

def _proc_name(pid):
    if not HAVE_PSUTIL: return None
    try: return psutil.Process(pid).name()
    except Exception: return None

def list_windows_matching(title_text, mode="contains"):
    if not IS_WINDOWS: return []
    import ctypes
    from ctypes import wintypes
    u = ctypes.windll.user32
    EnumWindows = u.EnumWindows
    EnumProc = ctypes.WINFUNCTYPE(ctypes.c_bool, wintypes.HWND, wintypes.LPARAM)
    IsVisible = u.IsWindowVisible
    GetTextW = u.GetWindowTextW
    GetTextLenW = u.GetWindowTextLengthW
    GetThreadProcessId = u.GetWindowThreadProcessId

    def match(t):
        t = t or ""
        s = title_text or ""
        a, b = t.lower(), s.lower()
        if mode == "contains":    return b in a
        if mode == "equals":      return a == b
        if mode == "startswith":  return a.startswith(b)
        if mode == "regex":
            try: return re.search(title_text, t) is not None
            except Exception: return False
        return False

    results = []
    def cb(hwnd, lparam):
        if not IsVisible(hwnd): return True
        n = GetTextLenW(hwnd)
        if n == 0: return True
        buf = ctypes.create_unicode_buffer(n+1)
        GetTextW(hwnd, buf, n+1)
        title = buf.value
        if not match(title): return True
        rect = _client_rect(hwnd)
        if not rect: return True
        pid = ctypes.c_ulong()
        GetThreadProcessId(hwnd, ctypes.byref(pid))
        results.append({"hwnd": hwnd, "title": title, "rect": rect, "pid": pid.value, "proc": _proc_name(pid.value)})
        return True

    EnumWindows(EnumProc(cb), 0)
    return results

def pick_window_interactive(matches):
    if not matches: return None
    print("\n[window] Multiple matches. Choose one:")
    for i, m in enumerate(matches, 1):
        w, h = m["rect"][2], m["rect"][3]
        print(f"  [{i}] {m['title']}  {w}x{h}  pid={m['pid']} exe={m['proc'] or '?'}")
    try:
        sel = input(f"Select [1..{len(matches)}] (default 1): ").strip()
    except EOFError:
        sel = ""
    idx = 1 if not sel else max(1, min(int(sel), len(matches)))
    return matches[idx-1]

def focus_window(hwnd):
    if not IS_WINDOWS: return False
    import ctypes
    u = ctypes.windll.user32
    SW_RESTORE = 9
    try:
        u.ShowWindowAsync(hwnd, SW_RESTORE)
        u.SetForegroundWindow(hwnd)
        u.BringWindowToTop(hwnd)
        u.SetFocus(hwnd)
        u.SetWindowPos(hwnd, -1, 0,0,0,0, 0x0002 | 0x0001)
        u.SetWindowPos(hwnd, -2, 0,0,0,0, 0x0002 | 0x0001)
        u.SetForegroundWindow(hwnd)
        return True
    except Exception:
        return False

def wait_for_valid_capture(hwnd, timeout=2.0, min_brightness=5.0):
    t0 = time.time()
    while time.time() - t0 < timeout:
        rect = _client_rect(hwnd)
        if not rect:
            time.sleep(0.05); continue
        frame, _, _ = capture_window(rect)
        if frame is None or frame.size == 0:
            time.sleep(0.05); continue
        if float(frame.mean()) >= min_brightness:
            return rect
        time.sleep(0.05)
    return _client_rect(hwnd)

# ------------------ Config ------------------
def load_cfg():
    if Path(CFG_PATH).exists():
        try: return json.loads(Path(CFG_PATH).read_text())
        except Exception: return {}
    return {}

def save_cfg(data):
    try: Path(CFG_PATH).write_text(json.dumps(data, indent=2))
    except Exception: pass

# ------------------ Capture ------------------
def capture_window(rect):
    left, top, width, height = rect
    if HAVE_MSS:
        with mss.mss() as sct:
            grab = sct.grab({"left": left, "top": top, "width": width, "height": height})
            frame = np.array(grab)[:, :, :3]  # BGR
            return frame, left, top
    im = pyautogui.screenshot(region=(left, top, width, height))
    frame = cv2.cvtColor(np.array(im), cv2.COLOR_RGB2BGR)
    return frame, left, top

# ------------------ Controls panel (Testing Mode only) ------------------
def _noop(x): pass

class KnobPanel:
    def __init__(self, args):
        self.win = "controls"
        cv2.namedWindow(self.win, cv2.WINDOW_AUTOSIZE)
        def f2i(val, scale=100): return int(round(val*scale))
        cv2.createTrackbar("hue_deg",        self.win, int(round(args.red_hue_tol)), 60, _noop)
        cv2.createTrackbar("scale_%",        self.win, int(args.scale*100), 100, _noop)
        cv2.createTrackbar("min_sc_%",       self.win, f2i(args.red_min_score), 100, _noop)
        cv2.createTrackbar("band_px",        self.win, int(args.band_px), 8, _noop)
        cv2.createTrackbar("fill_max_%",     self.win, f2i(args.fill_max_score), 100, _noop)
        cv2.createTrackbar("min_conf_%",     self.win, f2i(args.min_confidence), 100, _noop)
        cv2.createTrackbar("edge_min_%",     self.win, f2i(args.edge_min), 100, _noop)
        cv2.createTrackbar("connect_iter",   self.win, int(args.connect_iter), 3, _noop)
        cv2.createTrackbar("detect_every_n", self.win, int(args.detect_every_n), 60, _noop)
        max_k_default = int(max(1, min(1000, round(args.max_area / 1000.0))))
        cv2.createTrackbar("min_area",       self.win, int(args.min_area), 5000, _noop)
        cv2.createTrackbar("max_area_k",     self.win, max_k_default, 1000, _noop)
        cv2.setTrackbarPos("scale_%", self.win, max(40, min(100, int(args.scale*100))))

    def apply_to(self, args):
        i2f = lambda i: float(i)/100.0
        args.red_hue_tol = float(cv2.getTrackbarPos("hue_deg", self.win))
        args.scale = max(0.40, min(1.00, cv2.getTrackbarPos("scale_%", self.win)/100.0))
        args.red_min_score = i2f(cv2.getTrackbarPos("min_sc_%", self.win))
        args.band_px = max(1, cv2.getTrackbarPos("band_px", self.win))
        args.fill_max_score = i2f(cv2.getTrackbarPos("fill_max_%", self.win))
        args.min_confidence = i2f(cv2.getTrackbarPos("min_conf_%", self.win))
        args.edge_min = i2f(cv2.getTrackbarPos("edge_min_%", self.win))
        args.connect_iter = max(0, int(cv2.getTrackbarPos("connect_iter", self.win)))
        args.detect_every_n = max(1, int(cv2.getTrackbarPos("detect_every_n", self.win)))
        args.min_area = max(1.0, float(cv2.getTrackbarPos("min_area", self.win)))
        max_area_k = max(1, int(cv2.getTrackbarPos("max_area_k", self.win)))
        args.max_area = float(max_area_k * 1000)

# ------------------ Red detection ------------------
def _to_hsv(bgr):
    hsv = cv2.cvtColor(bgr, cv2.COLOR_BGR2HSV)
    H, S, V = cv2.split(hsv)
    return H.astype(np.float32), S.astype(np.float32)/255.0, V.astype(np.float32)/255.0

def _red_score_map(bgr, hue_tol_deg=16.0):
    H, S, V = _to_hsv(bgr)
    d = np.minimum(np.abs(H - 0.0), np.abs(180.0 - H))
    pref = np.clip(1.0 - d / float(max(1e-6, hue_tol_deg)), 0.0, 1.0)
    return pref * S * V

def detect_red_rectangles_simple(
    frame_bgr, *,
    red_hue_tol=0.0, red_min_score=0.64, band_px=4, connect_iter=1,
    fill_max_score=0.22, min_confidence=0.50, edge_min=0.60,
    min_area=70.0, max_area=1e6
):
    score = _red_score_map(frame_bgr, hue_tol_deg=red_hue_tol)
    mask = (score >= red_min_score).astype(np.uint8) * 255
    ksz = max(1, int(band_px))
    kernel = cv2.getStructuringElement(cv2.MORPH_RECT, (ksz, ksz))
    if connect_iter > 0:
        mask = cv2.morphologyEx(mask, cv2.MORPH_CLOSE, kernel, iterations=1)
        mask = cv2.dilate(mask, kernel, iterations=int(connect_iter))
    contours, _ = cv2.findContours(mask, cv2.RETR_LIST, cv2.CHAIN_APPROX_SIMPLE)
    results = []
    h, w = frame_bgr.shape[:2]
    score_map = score  # reuse
    for c in contours:
        if len(c) < 5: continue
        rect = cv2.minAreaRect(c)
        (cx, cy), (rw, rh), _ang = rect
        area_rect = float(rw * rh)
        if area_rect < min_area or area_rect > max_area: continue
        box = cv2.boxPoints(rect).astype(np.int32)
        pmask = np.zeros((h, w), np.uint8)
        cv2.fillPoly(pmask, [box], 255)
        fill = float((score_map * (pmask > 0)).sum() / max(1, int((pmask > 0).sum())))
        edge_mask = np.zeros((h, w), np.uint8)
        thickness = max(1, int(round(band_px)))
        cv2.polylines(edge_mask, [box], True, 255, thickness=thickness, lineType=cv2.LINE_AA)
        edge_pixels = int((edge_mask > 0).sum())
        edge_hits = int(((mask > 0) & (edge_mask > 0)).sum())
        edge_density = 0.0 if edge_pixels == 0 else edge_hits / float(edge_pixels)
        area_cont = float(cv2.contourArea(c))
        rectangularity = 0.0 if area_rect <= 1e-6 else max(0.0, min(1.0, area_cont / area_rect))
        short, long = (min(rw, rh), max(rw, rh))
        aspect_score = max(0.0, min(1.0, short / max(1.0, long)))
        low_fill = max(0.0, 1.0 - (fill / max(1e-6, fill_max_score)))
        conf = max(0.0, min(1.0, 0.30*rectangularity + 0.25*aspect_score + 0.20*low_fill + 0.25*edge_density))
        if edge_density < edge_min or conf < min_confidence or fill > fill_max_score:
            continue
        results.append((float(cx), float(cy), conf, rect, float(fill), float(edge_density)))
    results.sort(key=lambda r: (r[2] * (r[3][1][0]*r[3][1][1])), reverse=True)
    return results, mask

# ------------------ Overlay ------------------
def draw_overlay(base_bgr, candidates, header_text=None, extra_boxes=None):
    view = base_bgr.copy()
    for (cx, cy, conf, rot, fill, ed) in candidates:
        box = cv2.boxPoints(rot).astype(np.int32)
        color = (0, 80 + int(175*conf), 0)
        cv2.polylines(view, [box], True, color, 2)
        cv2.circle(view, (int(cx), int(cy)), 3, (255, 0, 0), -1)
        cv2.putText(view, f"{conf:.2f}/{ed:.2f}", (int(cx)+6, int(cy)-6),
                    cv2.FONT_HERSHEY_SIMPLEX, 0.5, color, 1, cv2.LINE_AA)
    if extra_boxes:
        for eb in extra_boxes:
            (x, y), (w, h) = eb["pt"], eb["wh"]
            color = eb.get("color",(0,255,255))
            label = eb.get("label","")
            cv2.rectangle(view, (x, y), (x+w, y+h), color, 2)
            if label:
                cv2.putText(view, label, (x, max(15, y-6)), cv2.FONT_HERSHEY_SIMPLEX, 0.5, color, 1, cv2.LINE_AA)
    if header_text:
        cv2.rectangle(view, (0,0), (view.shape[1], 26), (30,30,30), -1)
        cv2.putText(view, header_text, (8, 18), cv2.FONT_HERSHEY_SIMPLEX, 0.55, (255,255,255), 1, cv2.LINE_AA)
    return view

# ------------------ Human-like, clamped mouse ------------------
SAFE_MARGIN = 6
def _safe_pt(px, py):
    try:
        w, h = pyautogui.size()
    except Exception:
        return int(px), int(py)
    px = max(SAFE_MARGIN, min(int(px), w - SAFE_MARGIN))
    py = max(SAFE_MARGIN, min(int(py), h - SAFE_MARGIN))
    return px, py

def safe_click(x, y, button="left"):
    x, y = _safe_pt(x, y)
    pyautogui.click(x=x, y=y, button=button)

def _ease_in_out(t: float) -> float: return t*t*(3 - 2*t)

def _bezier(p0, p1, p2, p3, t):
    u = 1.0 - t
    return (u*u*u*p0[0] + 3*u*u*t*p1[0] + 3*u*t*t*p2[0] + t*t*t*p3[0],
            u*u*u*p0[1] + 3*u*u*t*p1[1] + 3*u*t*t*p2[1] + t*t*t*p3[1])

def human_move_to(x, y, base_duration=0.02):
    pyautogui.FAILSAFE = False
    x, y = _safe_pt(x, y)
    try:
        sx, sy = pyautogui.position()
        sx, sy = _safe_pt(sx, sy)
    except Exception:
        pyautogui.moveTo(*_safe_pt(x, y), duration=max(0.0, base_duration))
        return
    dx, dy = x - sx, y - sy
    dist = math.hypot(dx, dy)
    if dist < 1.0:
        pyautogui.moveTo(*_safe_pt(x, y), duration=0)
        return
    dur = max(0.012, base_duration + (dist / 900.0)) * random.uniform(0.9, 1.2)
    do_overshoot = (random.random() < 0.25 and dist > 80)
    overshoot_vec = (0.0, 0.0)
    if do_overshoot:
        ang = math.atan2(dy, dx) + random.uniform(-0.25, 0.25)
        mag = random.uniform(5.0, 18.0)
        overshoot_vec = (math.cos(ang)*mag, math.sin(ang)*mag)
    nx, ny = -dy / (dist + 1e-6), dx / (dist + 1e-6)
    curve_amp = min(60.0, 0.15 * dist) * random.choice([-1, 1])
    c1 = (sx + dx*0.33 + nx*curve_amp*random.uniform(0.3,0.9),
          sy + dy*0.33 + ny*curve_amp*random.uniform(0.3,0.9))
    c2 = (sx + dx*0.66 - nx*curve_amp*random.uniform(0.3,0.9),
          sy + dy*0.66 - ny*curve_amp*random.uniform(0.3,0.9))
    p0 = (sx, sy)
    p3 = _safe_pt(x + overshoot_vec[0], y + overshoot_vec[1])
    steps = max(12, int(dur * 120))
    t0 = time.time()
    for i in range(1, steps + 1):
        t = _ease_in_out(i / steps)
        px, py = _bezier(p0, c1, c2, p3, t)
        pyautogui.moveTo(*_safe_pt(px, py), duration=0)
        elapsed = time.time() - t0
        target = dur * (i / steps)
        if target > elapsed:
            time.sleep(target - elapsed)
    if do_overshoot:
        pyautogui.moveTo(*_safe_pt(x, y), duration=random.uniform(0.015, 0.045))
    for _ in range(random.randint(0, 2)):
        jx = x + random.randint(-1, 1)
        jy = y + random.randint(-1, 1)
        pyautogui.moveTo(*_safe_pt(jx, jy), duration=random.uniform(0.008, 0.020))
    pyautogui.moveTo(*_safe_pt(x, y), duration=random.uniform(0.008, 0.020))

# ------------------ WS server ------------------
def start_ws_server(host: str, port: int, token: str, set_idle_cb, enqueue_cb, set_base_cb):
    if not HAVE_WS:
        print("[ws] websockets package not installed; server disabled.")
        return None
    import asyncio
    BASE_NAMES = {"gemcrab","skotizo","avatar","jad","50s","nexmulti","callistomulti","vetmulti","venmulti"}
    ACTION_CMDS = {"logout","login"}
    async def handler(websocket):
        await websocket.send(json.dumps({
            "type":"hello","msg":"connected",
            "requires_token": bool(token),
            "commands":["idle_on","idle_off","idle","regear"] + sorted(list(BASE_NAMES)) + ["set_base"] + sorted(list(ACTION_CMDS))
        }))
        async for msg in websocket:
            try: data = json.loads(msg)
            except Exception:
                await websocket.send(json.dumps({"type":"error","error":"bad_json"})); continue
            if token and data.get("token") != token:
                await websocket.send(json.dumps({"type":"error","error":"bad_token"})); continue
            cmd = (data.get("cmd") or "").lower()
            if cmd == "idle_on":
                set_idle_cb(True);  await websocket.send(json.dumps({"type":"ack","ok":True,"cmd":"idle_on"}))
            elif cmd == "idle_off":
                set_idle_cb(False); await websocket.send(json.dumps({"type":"ack","ok":True,"cmd":"idle_off"}))
            elif cmd == "idle":
                v = data.get("value", None)
                if isinstance(v, bool):
                    set_idle_cb(v); await websocket.send(json.dumps({"type":"ack","ok":True,"cmd":"idle","value":v}))
                else:
                    await websocket.send(json.dumps({"type":"error","error":"idle_value_missing_or_not_bool"}))
            elif cmd == "regear":
                enqueue_cb("regear", data); await websocket.send(json.dumps({"type":"ack","ok":True,"cmd":"regear"}))
            elif cmd in BASE_NAMES:
                set_base_cb(cmd); enqueue_cb(cmd, data)
                await websocket.send(json.dumps({"type":"ack","ok":True,"cmd":cmd,"base":True}))
            elif cmd == "set_base":
                name = (data.get("name") or "").lower()
                if name in BASE_NAMES:
                    set_base_cb(name); await websocket.send(json.dumps({"type":"ack","ok":True,"cmd":"set_base","name":name}))
                else:
                    await websocket.send(json.dumps({"type":"error","error":"unknown_base","got":name}))
            elif cmd in ACTION_CMDS:
                enqueue_cb(cmd, data); await websocket.send(json.dumps({"type":"ack","ok":True,"cmd":cmd}))
            else:
                await websocket.send(json.dumps({"type":"error","error":"unsupported_cmd","got":cmd}))
    async def main():
        async with websockets.serve(handler, host, port, ping_interval=20, close_timeout=1):
            print(f"[ws] listening on ws://{host}:{port}")
            await asyncio.Future()
    def run_loop():
        import asyncio
        asyncio.set_event_loop(asyncio.new_event_loop())
        loop = asyncio.get_event_loop()
        try: loop.run_until_complete(main())
        finally: loop.close()
    t = threading.Thread(target=run_loop, daemon=True); t.start()
    return t

# ------------------ Main ------------------
def main():
    args = parse_args()
    if args.red_hue_tol <= 1.0: args.red_hue_tol = float(args.red_hue_tol) * 60.0
    else: args.red_hue_tol = float(args.red_hue_tol)

    cfg = load_cfg()

    idle_mode = True
    def set_idle(val_or_toggle):
        nonlocal idle_mode
        if val_or_toggle is None: idle_mode = not idle_mode
        elif isinstance(val_or_toggle, bool): idle_mode = val_or_toggle
        print(f"[idle] {'ON' if idle_mode else 'OFF'}")

    base_cmd = "gemcrab"
    def set_base_cmd(name: str):
        nonlocal base_cmd
        base_cmd = name
        print(f"[base] set to: {base_cmd}")

    control_q: SimpleQueue = SimpleQueue()
    def enqueue_cmd(cmd, data=None): control_q.put((cmd, data or {}))

    if not args.no_ws:
        if HAVE_WS: start_ws_server(args.ws_host, args.ws_port, args.ws_token or "", set_idle, enqueue_cmd, set_base_cmd)
        else: print("[ws] websockets not installed. To enable: pip install websockets")

    # Window discovery
    matches = list_windows_matching(args.window_title, args.window_title_mode)
    if not matches:
        print(f"[window] No visible windows match {args.window_title_mode} '{args.window_title}'.", file=sys.stderr); sys.exit(1)
    if args.window_index > 0 and args.window_index <= len(matches):
        chosen = matches[args.window_index - 1]
    elif len(matches) == 1 or args.no_window_prompt:
        chosen = max(matches, key=lambda m: m["rect"][2]*m["rect"][3])
    else:
        chosen = pick_window_interactive(matches)
        if chosen is None: print("[window] No selection made.", file=sys.stderr); sys.exit(1)

    hwnd = chosen["hwnd"]
    print(f"[window] Found: '{chosen['title']}' pid={chosen['pid']} exe={chosen.get('proc') or '?'}")
    focus_window(hwnd)
    win_rect = wait_for_valid_capture(hwnd, timeout=2.0) or chosen["rect"]
    print(f"[window] Using client area: {win_rect}")

    # ===== ALWAYS PROMPT: ROI + action boxes =====
    base_img, _, _ = capture_window(win_rect)

    def prompt_or_keep(name, prev_rel):
        nonlocal base_img, win_rect
        if prev_rel:
            print(f"[{name}] Existing: {prev_rel}. Select new box or press C to keep.")
        img, _, _ = capture_window(win_rect)
        sel = select_box(f"{name} — ENTER=save, C=keep", img)
        if sel:
            return clamp_roi_rel_to_window(sel, win_rect)
        return prev_rel

    roi_rel_prev = tuple(cfg.get("ROI_REL")) if cfg.get("ROI_REL") else None
    while True:
        roi_rel = prompt_or_keep("Select ROI", roi_rel_prev)
        if roi_rel: break
        print("[roi] ROI is required. Please select again.")

    logout1_rel_prev = tuple(cfg.get("LOGOUT1_REL")) if cfg.get("LOGOUT1_REL") else None
    logout2_rel_prev = tuple(cfg.get("LOGOUT2_REL")) if cfg.get("LOGOUT2_REL") else None
    login_rel_prev   = tuple(cfg.get("LOGIN_REL"))   if cfg.get("LOGIN_REL")   else None

    logout1_rel = prompt_or_keep("Select Logout Button #1", logout1_rel_prev)
    logout2_rel = prompt_or_keep("Select Logout Button #2", logout2_rel_prev)
    login_rel   = prompt_or_keep("Select Login Button",     login_rel_prev)

    cfg["ROI_REL"] = list(roi_rel)
    cfg["LOGOUT1_REL"] = list(logout1_rel) if logout1_rel else None
    cfg["LOGOUT2_REL"] = list(logout2_rel) if logout2_rel else None
    cfg["LOGIN_REL"]   = list(login_rel)   if login_rel   else None
    save_cfg(cfg)

    print(f"[roi] Active ROI (relative): {roi_rel}")
    print(f"[logout] Btn#1: {logout1_rel}  Btn#2: {logout2_rel}")
    print(f"[login ] Btn  : {login_rel}")

    # Controls panel (Testing Mode only)
    knobs = None

    last_click_t = 0.0
    last_xy = None
    cooldown = {}
    testing_mode = False
    prev_shift = False
    frame_idx = 0

    last_found_proc = []
    last_mask = None
    last_proc_shape = None
    last_overlay_view = None
    last_targets_screen = []

    pyautogui.PAUSE = 0.0
    pyautogui.FAILSAFE = False
    print("[keys] ALT=quit, SHIFT=Testing Mode toggle, R=reselect ROI+Buttons, W=refocus window")
    print("[state] Idle is ON by default. Use WebSocket to toggle.")

    # Chat/macro helpers
    COMMAND_TEXT = {
        "gemcrab": "::gemcrab",
        "skotizo": "::skotizo",
        "avatar": "::avatar",
        "jad": "::jad",
        "50s": "::50s",
        "nexmulti": "::nexmulti",
        "callistomulti": "::callistomulti",
        "vetmulti": "::vetmulti",
        "venmulti": "::venmulti",
    }

    def run_chat_command(cmd_name: str):
        txt = COMMAND_TEXT.get(cmd_name)
        if not txt:
            print(f"[chat] unknown command '{cmd_name}'"); return
        try:
            focus_window(hwnd)
            pyautogui.write(txt, interval=0.01)
            pyautogui.press('enter')
            time.sleep(0.60)
            pyautogui.press('1')
            time.sleep(0.10)
            # Flip Idle OFF after teleport so it can act
            set_idle(False)
        except Exception as e:
            print(f"[chat:{cmd_name}] ERROR: {e}", file=sys.stderr)

    def do_regear():
        try:
            focus_window(hwnd)
            pyautogui.keyDown('ctrl'); time.sleep(0.10); pyautogui.press('1'); time.sleep(0.03); pyautogui.keyUp('ctrl')
        except Exception as e:
            print(f"[macro:regear] ERROR: {e}", file=sys.stderr)

    def do_named_command(name: str):
        run_chat_command(name)

    def do_base():
        do_named_command(base_cmd)

    # Logout/Login clickers
    def do_logout():
        nonlocal win_rect
        if not logout1_rel or not logout2_rel:
            print("[logout] Buttons not set."); return
        wr = _client_rect(hwnd) or win_rect
        c1 = rect_center_abs(logout1_rel, wr)
        c2 = rect_center_abs(logout2_rel, wr)
        if not c1 or not c2:
            print("[logout] Could not compute centers."); return
        try:
            focus_window(hwnd)
            human_move_to(c1[0], c1[1], base_duration=max(0.0, args.move_duration))
            time.sleep(0.05)
            safe_click(c1[0], c1[1], button="left")
            time.sleep(0.30)
            human_move_to(c2[0], c2[1], base_duration=max(0.0, args.move_duration))
            time.sleep(0.05)
            safe_click(c2[0], c2[1], button="left")
            print("[logout] Clicked #1 then #2")
        except Exception as e:
            print(f"[logout] ERROR: {e}", file=sys.stderr)

    def do_login():
        nonlocal win_rect
        if not login_rel:
            print("[login] Button not set."); return
        wr = _client_rect(hwnd) or win_rect
        c = rect_center_abs(login_rel, wr)
        if not c:
            print("[login] Could not compute center."); return
        try:
            focus_window(hwnd)
            human_move_to(c[0], c[1], base_duration=max(0.0, args.move_duration))
            time.sleep(0.05)
            safe_click(c[0], c[1], button="left")
            print("[login] Clicked login")
        except Exception as e:
            print(f"[login] ERROR: {e}", file=sys.stderr)

    def overlay_action_boxes(roi_rel, scale):
        boxes = []
        rx, ry, rw, rh = roi_rel
        def add_if_visible(rel_rect, label, color):
            if not rel_rect: return
            x,y,w,h = rel_rect
            ix0 = max(x, rx); iy0 = max(y, ry)
            ix1 = min(x+w, rx+rw); iy1 = min(y+h, ry+rh)
            if ix1 <= ix0 or iy1 <= iy0: return
            ox = int(round((ix0 - rx) * scale))
            oy = int(round((iy0 - ry) * scale))
            ow = int(round((ix1 - ix0) * scale))
            oh = int(round((iy1 - iy0) * scale))
            boxes.append({"pt": (ox, oy), "wh": (ow, oh), "color": color, "label": label})
        add_if_visible(logout1_rel, "Logout #1", (0,255,255))
        add_if_visible(logout2_rel, "Logout #2", (0,200,255))
        add_if_visible(login_rel,   "Login",     (255,255,0))
        return boxes

    try:
        while True:
            if alt_down():
                print("[stop] ALT pressed."); break

            # queued macro commands
            try:
                while True:
                    cmd, data = control_q.get_nowait()
                    if cmd == "regear":
                        do_regear()
                    elif cmd in COMMAND_TEXT:
                        set_base_cmd(cmd)
                        do_named_command(cmd)
                    elif cmd == "logout":
                        do_logout()
                    elif cmd == "login":
                        do_login()
            except Empty:
                pass

            # SHIFT toggles testing mode
            cur_shift = shift_down()
            if cur_shift and not prev_shift:
                testing_mode = not testing_mode
                print(f"[mode] Testing Mode {'ON' if testing_mode else 'OFF'}")
                if testing_mode and knobs is None:
                    knobs = KnobPanel(args)
                    cv2.setTrackbarPos("hue_deg", knobs.win, int(round(args.red_hue_tol)))
                if not testing_mode and knobs is not None:
                    try: cv2.destroyWindow(knobs.win)
                    except Exception: pass
                    knobs = None
                    for wname in ["red_tile_clicker (view)", "tile mask"]:
                        try: cv2.destroyWindow(wname)
                        except Exception: pass
            prev_shift = cur_shift

            if knobs is not None:
                knobs.apply_to(args)

            new_rect = _client_rect(hwnd)
            if new_rect and new_rect != win_rect:
                win_rect = new_rect

            frame_win, wx, wy = capture_window(win_rect)
            if float(frame_win.mean()) < 3.0:
                focus_window(hwnd)
                win_rect = wait_for_valid_capture(hwnd, timeout=1.0) or win_rect
                frame_win, wx, wy = capture_window(win_rect)

            rx, ry, rw, rh = roi_rel
            x0 = max(0, min(rx, frame_win.shape[1]-1))
            y0 = max(0, min(ry, frame_win.shape[0]-1))
            x1 = max(x0+1, min(rx+rw, frame_win.shape[1]))
            y1 = max(y0+1, min(ry+rh, frame_win.shape[0]))
            frame_roi = frame_win[y0:y1, x0:x1]
            roi_origin_abs = (wx + rx, wy + ry)

            scale = args.scale
            frame_proc = cv2.resize(frame_roi, (int(frame_roi.shape[1]*scale), int(frame_roi.shape[0]*scale)),
                                    interpolation=cv2.INTER_AREA) if scale != 1.0 else frame_roi

            ran_detector = (frame_idx % max(1, args.detect_every_n) == 0)

            if ran_detector:
                found_proc, mask = detect_red_rectangles_simple(
                    frame_bgr=frame_proc,
                    red_hue_tol=args.red_hue_tol,
                    red_min_score=args.red_min_score,
                    band_px=args.band_px,
                    connect_iter=args.connect_iter,
                    fill_max_score=args.fill_max_score,
                    min_confidence=args.min_confidence,
                    edge_min=args.edge_min,
                    min_area=args.min_area * (scale*scale),
                    max_area=args.max_area * (scale*scale)
                )
                last_found_proc = found_proc
                last_mask = mask
                last_proc_shape = frame_proc.shape[:2]
                header = []
                if testing_mode: header.append("TESTING MODE (no clicks)")
                if idle_mode:    header.append("IDLE")
                title = " — ".join(header) if header else "Detection view"
                extras = overlay_action_boxes(roi_rel, scale)
                last_overlay_view = draw_overlay(
                    frame_proc, found_proc,
                    header_text=f"{title} — {len(found_proc)} targets",
                    extra_boxes=extras
                )
                last_targets_screen = []
                for (cx, cy, conf, rot, fill, ed) in found_proc:
                    if scale != 1.0:
                        cx, cy = cx/scale, cy/scale
                        rot = ((rot[0][0]/scale, rot[0][1]/scale),
                               (rot[1][0]/scale, rot[1][1]/scale), rot[2])
                    sx = int(round(roi_origin_abs[0] + cx))
                    sy = int(round(roi_origin_abs[1] + cy))
                    w, h = rot[1]
                    sel_score = float(w*h) * (0.5 + 0.5*conf)
                    last_targets_screen.append((sx, sy, conf, 0.0, 0.0, rot, sel_score))

            frame_idx += 1

            # auto-clicking of red tiles
            can_autoclick = (not idle_mode) and last_targets_screen and not (args.dry_run or testing_mode)
            if can_autoclick:
                now = time.time()
                chosen_pt = None
                cands = list(last_targets_screen)
                cands.sort(key=lambda c: c[6], reverse=True)
                min_switch = max(0, args.min_switch_px)
                for (sx, sy, conf, fill, ed, rot, _sel) in cands:
                    gx = sx // max(1, args.grid); gy = sy // max(1, args.grid)
                    if now - cooldown.get((gx,gy), 0.0) < args.target_cooldown: continue
                    if last_xy is not None and np.hypot(sx-last_xy[0], sy-last_xy[1]) < min_switch: continue
                    chosen_pt = (sx, sy, conf, fill); break
                if chosen_pt is None and not args.skip_when_no_new:
                    sx, sy, conf, fill, *_ = cands[0]
                    chosen_pt = (sx, sy, conf, fill)
                if chosen_pt is not None and (time.time() - last_click_t) >= max(0.001, 1.0 / max(args.rate, 0.0001)):
                    sx, sy, conf, fill = chosen_pt
                    try:
                        human_move_to(sx, sy, base_duration=max(0.0, args.move_duration))
                        time.sleep(max(0.0, args.hover_delay))
                        pyautogui.mouseDown(x=_safe_pt(sx, sy)[0], y=_safe_pt(sx, sy)[1], button=args.button)
                        time.sleep(max(0.0, args.down_up_gap))
                        pyautogui.mouseUp(x=_safe_pt(sx, sy)[0], y=_safe_pt(sx, sy)[1], button=args.button)
                        if args.double:
                            time.sleep(0.05)
                            pyautogui.mouseDown(x=_safe_pt(sx, sy)[0], y=_safe_pt(sx, sy)[1], button=args.button)
                            time.sleep(max(0.0, args.down_up_gap))
                            pyautogui.mouseUp(x=_safe_pt(sx, sy)[0], y=_safe_pt(sx, sy)[1], button=args.button)
                    except Exception as e:
                        print(f"[click] ERROR: {e}", file=sys.stderr)
                    last_click_t = time.time()
                    last_xy = (sx, sy)
                    cooldown[(sx // max(1, args.grid), sy // max(1, args.grid))] = last_click_t

            # Testing/Debug windows & hotkeys
            if testing_mode or args.debug:
                overlay_to_show = last_overlay_view if last_overlay_view is not None else frame_proc
                cv2.imshow("red_tile_clicker (view)", overlay_to_show)
                if last_mask is not None: cv2.imshow("tile mask", last_mask)
                key = cv2.waitKey(1) & 0xFF
                if key in (ord('q'), 27): break
                if key == ord('r'):
                    # reselect all
                    focus_window(hwnd)
                    win_rect = wait_for_valid_capture(hwnd, timeout=1.0) or win_rect
                    roi_rel = clamp_roi_rel_to_window(
                        select_box("Select ROI (ENTER=save, C=cancel)", capture_window(win_rect)[0]) or roi_rel,
                        win_rect
                    )
                    nb1 = select_box("Select Logout Button #1 (ENTER=save, C=cancel)", capture_window(win_rect)[0])
                    nb2 = select_box("Select Logout Button #2 (ENTER=save, C=cancel)", capture_window(win_rect)[0])
                    nb3 = select_box("Select Login Button (ENTER=save, C=cancel)", capture_window(win_rect)[0])
                    if nb1: logout1_rel = clamp_roi_rel_to_window(nb1, win_rect)
                    if nb2: logout2_rel = clamp_roi_rel_to_window(nb2, win_rect)
                    if nb3: login_rel   = clamp_roi_rel_to_window(nb3, win_rect)
                    cfg["ROI_REL"] = list(roi_rel)
                    cfg["LOGOUT1_REL"] = list(logout1_rel) if logout1_rel else None
                    cfg["LOGOUT2_REL"] = list(logout2_rel) if logout2_rel else None
                    cfg["LOGIN_REL"]   = list(login_rel)   if login_rel   else None
                    save_cfg(cfg)
                    print(f"[roi] Updated: {roi_rel}")
                    print(f"[logout] Btn#1: {logout1_rel}  Btn#2: {logout2_rel}")
                    print(f"[login ] Btn  : {login_rel}")
                    frame_idx = 0
                if key == ord('w'):
                    focus_window(hwnd)

            if not HAVE_MSS: time.sleep(0.01)

    except KeyboardInterrupt:
        pass
    finally:
        for wname in ["controls","red_tile_clicker (view)","tile mask"]:
            try: cv2.destroyWindow(wname)
            except Exception: pass
        try: cv2.destroyAllWindows()
        except Exception: pass

if __name__ == "__main__":
    main()
