import os
import io
import json
import time
import base64
import threading
import hashlib
import tkinter as tk
from tkinter import ttk, messagebox
import tkinter.font as tkfont

import numpy as np
from PIL import Image, ImageTk
import mss

from openai import OpenAI
import keyboard
import mouse
import pytesseract

import ctypes
from ctypes import wintypes

try:
    import win32gui  # type: ignore
    import win32con  # type: ignore
    import win32api  # type: ignore
except Exception:
    win32gui = None
    win32con = None
    win32api = None

# Helper for layered border-only window on Windows
if win32gui and win32con and win32api:
    import win32ui  # type: ignore

    class BLENDFUNCTION(ctypes.Structure):
        _fields_ = [
            ("BlendOp", ctypes.c_byte),
            ("BlendFlags", ctypes.c_byte),
            ("SourceConstantAlpha", ctypes.c_byte),
            ("AlphaFormat", ctypes.c_byte),
        ]


    def set_layered_border(hwnd: int, w: int, h: int, border_color: str, border_width: int) -> None:
        from win32gui import GetDC, ReleaseDC
        import win32ui

        hdc_screen = GetDC(0)
        hdc_screen_ui = win32ui.CreateDCFromHandle(hdc_screen)
        hdc_mem = hdc_screen_ui.CreateCompatibleDC()

        bmp = win32ui.CreateBitmap()
        bmp.CreateCompatibleBitmap(hdc_screen_ui, w, h)
        old_bmp = hdc_mem.SelectObject(bmp)

        # Clear transparent
        hdc_mem.FillSolidRect((0, 0, w, h), 0x00000000)

        r = int(border_color[1:3], 16)
        g = int(border_color[3:5], 16)
        b = int(border_color[5:7], 16)
        color_bgr = (b << 16) | (g << 8) | r

        # Draw border
        hdc_mem.FillSolidRect((0, 0, w, border_width), color_bgr)  # top
        hdc_mem.FillSolidRect((0, h - border_width, w, h), color_bgr)  # bottom
        hdc_mem.FillSolidRect((0, 0, border_width, h), color_bgr)  # left
        hdc_mem.FillSolidRect((w - border_width, 0, w, h), color_bgr)  # right

        blend = (
            win32con.AC_SRC_OVER,
            0,
            255,
            win32con.AC_SRC_ALPHA
        )

        win32gui.UpdateLayeredWindow(
            hwnd,
            hdc_screen,
            None,
            (w, h),
            hdc_mem.GetSafeHdc(),
            (0, 0),
            0,
            blend,
            win32con.ULW_ALPHA
        )

        # restore object before deleting DC
        try:
            hdc_mem.SelectObject(old_bmp)
        except Exception:
            pass

        # delete GDI objects / DCs (safe)
        try:
            win32gui.DeleteObject(bmp.GetHandle())
        except Exception:
            pass

        try:
            hdc_mem.DeleteDC()
        except Exception:
            pass

        try:
            hdc_screen_ui.DeleteDC()
        except Exception:
            pass

        try:
            ReleaseDC(0, hdc_screen)
        except Exception:
            pass

# ================= PATHS =================
BASE_DIR = os.path.dirname(os.path.abspath(__file__))
API_KEY_FILE = os.path.join(BASE_DIR, "api-key.txt")
HOTKEY_FILE = os.path.join(BASE_DIR, "hotkeys.json")

# ================= CONFIG =================
MODEL = "gpt-4.1-mini"
REALTIME_INTERVAL = 0.25
OVERLAY_ALPHA = 0.86
STABLE_SECONDS = 0.25
PAD_X = 8
PAD_Y = 6
OUTLINE_PX = 1
OUTLINE_COLOR = "#000000"
FONT_FAMILY_PRIMARY = "Meiryo"
FONT_FAMILY_FALLBACK = "Segoe UI"
FONT_MIN = 10
FONT_MAX = 34
OCR_SAFE_MARGIN = 4   # px
BORDER_COLOR = "#FF0000"  # Red border for region outline
BORDER_WIDTH = 2
pytesseract.pytesseract.tesseract_cmd = r"C:\Program Files\Tesseract-OCR\tesseract.exe"

PROMPT_TEMPLATE = (
    "Translate ALL visible text in the image into {target_lang}.\n"
    "Rules: keep line breaks; do not summarize; do not add extra text; output only the translation."
)

# ================= LANG =================
INPUT_LANG_MAP = {
    "Auto (Detect)": None,
    "Japanese": "Japanese",
    "English": "English",
    "Chinese": "Chinese",
    "Korean": "Korean",
}
TARGET_LANG_MAP = {
    "Tiếng Việt": "Vietnamese",
    "English": "English",
    "日本語": "Japanese",
    "中文": "Chinese",
    "한국어": "Korean",
}

# ================= HOTKEY DEFAULTS =================
DEFAULT_HOTKEYS = {
    "select_region": "ctrl+shift+1",
    "translate_once": "ctrl+shift+2",
    "toggle_realtime": "ctrl+shift+3",
}

# ================= WINDOW TRACKING (optional) =================
try:
    import win32gui  # type: ignore
    import win32con  # type: ignore
    import win32api  # type: ignore
except Exception:
    win32gui = None
    win32con = None
    win32api = None

# ================= GLOBAL STATE =================
selected_region = None  # (x, y, w, h) in virtual screen coords
tracked_hwnd = None
tracked_rel = None  # (rel_x, rel_y) from window top-left

overlay_text_items = []   # list[int] – id của text trên canvas
overlay_last_geometry = None
overlay_last_text = None

last_full_image_hash = None
last_full_image = None

# debounce nhanh hơn
FAST_STABLE_SECONDS = 0.2
SLOW_STABLE_SECONDS = 0.6

last_translated_text_hash = None

client = None

realtime_running = False
last_image_hash = None
last_displayed_text = None
last_text_hash = None

translation_cache = {}  # hash -> text

# overlay widgets
translation_overlay = None
translation_canvas = None

# debug widgets
debug_label = None
debug_image_label = None

# hotkey management
registered_hotkeys = []
hotkeys_suspended = False
is_recording_hotkey = False
mouse_listener_enabled = False

# mouse click detection
mouse_click_listener = None
click_detection_enabled = False

last_ocr = ""
last_ocr_change_time = 0.0

# translation modes
TRANSLATION_MODES = {
    "Auto Below Region": "below",
    "Click to Translate": "click",
}
current_translation_mode = "below"

# region border display
show_region_border = False
region_border_window = None

last_translated_key = None

# ================= HELPERS =================
def load_api_key() -> str:
    """
    Priority:
    1. api-key.txt
    2. ENV: OPENAI_API_KEY
    3. Base64 fallback (hidden text)
    """

    # 1️⃣ File api-key.txt
    if os.path.exists(API_KEY_FILE):
        try:
            with open(API_KEY_FILE, "r", encoding="utf-8") as f:
                key = f.read().strip()
            if key:
                print("🔑 API key loaded from api-key.txt")
                return key
        except Exception:
            pass

    # 2️⃣ Environment variable
    env_key = os.getenv("OPENAI_API_KEY")
    if env_key:
        print("🔑 API key loaded from ENV")
        return env_key

    # 3️⃣ Base64 fallback (KHÔNG lộ trực tiếp)
    try:
        encoded = "c2stcHJvai10Z3VqdlhrR3RCWkh4Q2pDbmtqUTNHbTE0V2t0VS1Fdng0cFpKQm5KR0JtcFN5NGdRdjU3LTltREZESlc0R01GeGF1YkstNUZYcVQzQmxia0ZKMFNQNEVPdkxldEJvZVR6Y2RPYm1JMEhpTW1NQVFYWVI3WEgtelZ1V25pV000eWxpOU1mVkxvRm1XRVo4ek9vMnR3TVBOeC1Ba0E="
        key = base64.b64decode(encoded).decode("utf-8")
        print("⚠️ API key loaded from base64 fallback")
        return key
    except Exception:
        pass

    raise RuntimeError(
        "No API key found.\n"
        "Provide api-key.txt or set OPENAI_API_KEY."
    )

def load_hotkeys() -> dict:
    if os.path.exists(HOTKEY_FILE):
        try:
            with open(HOTKEY_FILE, "r", encoding="utf-8") as f:
                data = json.load(f)
            merged = DEFAULT_HOTKEYS.copy()
            merged.update({k: str(v) for k, v in data.items()})
            return merged
        except Exception:
            return DEFAULT_HOTKEYS.copy()
    return DEFAULT_HOTKEYS.copy()


def save_hotkeys(hotkeys: dict) -> None:
    with open(HOTKEY_FILE, "w", encoding="utf-8") as f:
        json.dump(hotkeys, f, indent=2)
def should_hide_overlay_for_capture() -> bool:
    # ❌ BELOW MODE: tuyệt đối KHÔNG ẩn overlay
    if current_translation_mode == "below":
        return False
    return True


def calc_image_hash(img: Image.Image) -> str:
    # More sensitive hash so small UI text changes are detected
    small = img.resize((320, 120)).convert("L")
    arr = np.asarray(small)
    return hashlib.md5(arr.tobytes()).hexdigest()


def capture_detection_strip() -> Image.Image | None:
    if not selected_region:
        return None

    overlay_was_visible = False
    if should_hide_overlay_for_capture():
        if translation_overlay and translation_overlay.winfo_exists():
            overlay_was_visible = True
            translation_overlay.withdraw()
            time.sleep(0.02)

    x, y, w, h = selected_region
    strip_height = min(30, h // 3)
    strip_y = y + (h - strip_height) // 2

    with mss.mss() as sct:
        shot = sct.grab({
            "left": int(x),
            "top": int(strip_y),
            "width": int(w),
            "height": strip_height
        })

    img = Image.frombytes("RGB", shot.size, shot.rgb)

    if overlay_was_visible:
        translation_overlay.deiconify()

    return img

def capture_region_for_ocr() -> Image.Image | None:
    if not selected_region:
        return None

    overlay_was_visible = False
    if should_hide_overlay_for_capture():
        if translation_overlay and translation_overlay.winfo_exists():
            overlay_was_visible = True
            translation_overlay.withdraw()
            time.sleep(0.03)

    x, y, w, h = selected_region

    top_cut = int(h * 0.15)
    bottom_cut = int(h * 0.35)

    x += OCR_SAFE_MARGIN
    y += top_cut
    w -= OCR_SAFE_MARGIN * 2
    h = h - top_cut - bottom_cut

    if w < 10 or h < 10:
        if overlay_was_visible:
            translation_overlay.deiconify()
        return None

    with mss.mss() as sct:
        shot = sct.grab({
            "left": int(x),
            "top": int(y),
            "width": int(w),
            "height": int(h)
        })

    img = Image.frombytes("RGB", shot.size, shot.rgb)

    if overlay_was_visible:
        translation_overlay.deiconify()

    return img


def capture_region() -> Image.Image | None:
    if not selected_region:
        return None

    overlay_was_visible = False
    if should_hide_overlay_for_capture():
        if translation_overlay and translation_overlay.winfo_exists():
            overlay_was_visible = True
            translation_overlay.withdraw()
            time.sleep(0.02)

    x, y, w, h = selected_region
    if w < 4 or h < 4:
        if overlay_was_visible:
            translation_overlay.deiconify()
        return None

    with mss.mss() as sct:
        shot = sct.grab({
            "left": int(x),
            "top": int(y),
            "width": int(w),
            "height": int(h)
        })

    img = Image.frombytes("RGB", shot.size, shot.rgb)

    # ✅ GIẢM KÍCH THƯỚC ẢNH (rất quan trọng)
    img = img.resize((w // 2, h // 2), Image.BILINEAR)

    if overlay_was_visible:
        translation_overlay.deiconify()

    return img


def image_to_data_url_png(img: Image.Image) -> str:
    buf = io.BytesIO()
    img.save(buf, format="PNG")
    b64 = base64.b64encode(buf.getvalue()).decode("ascii")
    return f"data:image/png;base64,{b64}"


def estimate_bg_fg(img: Image.Image) -> tuple[str, str]:
    small = img.resize((140, 70)).convert("RGB")
    arr = np.asarray(small, dtype=np.float32)
    avg = arr.mean(axis=(0, 1))
    r, g, b = [int(x) for x in avg]
    luminance = 0.299 * r + 0.587 * g + 0.114 * b
    fg = (255, 255, 255) if luminance < 140 else (0, 0, 0)
    bg_hex = f"#{r:02x}{g:02x}{b:02x}"
    fg_hex = f"#{fg[0]:02x}{fg[1]:02x}{fg[2]:02x}"
    return bg_hex, fg_hex
def get_stable_seconds(text: str) -> float:
    """
    Text ngắn → dịch nhanh
    Text dài → chờ ổn định lâu hơn
    """
    if len(text) < 40:
        return FAST_STABLE_SECONDS
    return SLOW_STABLE_SECONDS


def estimate_original_font_size(img: Image.Image) -> int:
    """Estimate the font size of text in the original image using OCR data"""
    try:
        # Get detailed OCR data with bounding boxes
        data = pytesseract.image_to_data(img, output_type=pytesseract.Output.DICT)

        heights = []
        for i, conf in enumerate(data['conf']):
            if int(conf) > 30:  # Only consider confident detections
                h = data['height'][i]
                if h > 5:  # Filter out noise
                    heights.append(h)

        if heights:
            # Use median height to avoid outliers
            median_height = sorted(heights)[len(heights) // 2]
            # Approximate font size (text height is usually ~0.7 of font size)
            estimated_size = int(median_height / 0.7)
            # Clamp between min and max
            return max(FONT_MIN, min(estimated_size, FONT_MAX))
    except Exception as e:
        print(f"⚠️ Font size estimation failed: {e}")

    return 14  # Default fallback


def choose_font_family() -> str:
    try:
        fams = set(tkfont.families())
        if FONT_FAMILY_PRIMARY in fams:
            return FONT_FAMILY_PRIMARY
    except Exception:
        pass
    return FONT_FAMILY_FALLBACK


def fit_font_size(text: str, w: int, h: int, family: str) -> int:
    # ✅ FIX: never use split("") – that causes ValueError: empty separator
    if not text:
        return FONT_MIN
    if w <= 20 or h <= 20:
        return FONT_MIN

    lines = text.split("\n") if "\n" in text else [text]
    lines = [ln.rstrip() for ln in lines]

    def fits(sz: int) -> bool:
        fnt = tkfont.Font(family=family, size=sz, weight="bold")
        line_h = fnt.metrics("linespace")
        total_h = line_h * max(1, len(lines)) + 2 * PAD_Y
        if total_h > h:
            return False
        for ln in lines:
            if fnt.measure(ln) + 2 * PAD_X > w:
                return False
        return True

    lo, hi = FONT_MIN, FONT_MAX
    best = FONT_MIN
    while lo <= hi:
        mid = (lo + hi) // 2
        if fits(mid):
            best = mid
            lo = mid + 1
        else:
            hi = mid - 1
    return best


def draw_text_canvas(parent: tk.Toplevel, text: str, fg: str, bg: str, family: str, size: int) -> tk.Canvas:
    cv = tk.Canvas(parent, bg=bg, highlightthickness=0)
    cv.pack(fill="both", expand=True)

    fnt = tkfont.Font(family=family, size=size, weight="bold")
    line_h = fnt.metrics("linespace")

    x = PAD_X
    y = PAD_Y

    # ✅ FIX: split by newline, not empty separator
    for line in (text.split("\n") if text else [""]):
        for dx, dy in [(-OUTLINE_PX, 0), (OUTLINE_PX, 0), (0, -OUTLINE_PX), (0, OUTLINE_PX)]:
            cv.create_text(
                x + dx, y + dy,
                text=line,
                anchor="nw",
                fill=OUTLINE_COLOR,
                font=fnt
            )
        cv.create_text(
            x, y,
            text=line,
            anchor="nw",
            fill=fg,
            font=fnt
        )
        y += line_h

    return cv


def get_hwnd_from_point(px: int, py: int):
    if not win32gui:
        return None
    try:
        return win32gui.WindowFromPoint((int(px), int(py)))
    except Exception:
        return None


def get_window_rect(hwnd):
    if not win32gui or not hwnd:
        return None
    try:
        return win32gui.GetWindowRect(hwnd)
    except Exception:
        return None


def update_tracked_window_from_region():
    global tracked_hwnd, tracked_rel
    if not selected_region:
        tracked_hwnd = None
        tracked_rel = None
        return
    x, y, w, h = selected_region
    cx, cy = x + w // 2, y + h // 2
    hwnd = get_hwnd_from_point(cx, cy)
    tracked_hwnd = hwnd
    rect = get_window_rect(hwnd)
    if rect:
        wl, wt, wr, wb = rect
        tracked_rel = (int(x - wl), int(y - wt))
    else:
        tracked_rel = None


def compute_overlay_xy() -> tuple[int, int]:
    if not selected_region:
        return 0, 0
    x, y, w, h = selected_region
    if tracked_hwnd and tracked_rel:
        rect = get_window_rect(tracked_hwnd)
        if rect:
            wl, wt, wr, wb = rect
            nx = wl + tracked_rel[0]
            ny = wt + tracked_rel[1]
            nx = max(wl, min(nx, wr - w))
            ny = max(wt, min(ny, wb - h))
            return int(nx), int(ny)
    return int(x), int(y)

def normalize_ocr_text(s: str) -> str:
    s = (s or "").strip()
    s = s.replace("ー", "-")
    s = s.replace("–", "-")
    s = s.replace("—", "-")
    s = " ".join(s.split())
    return s

def quick_ocr_text(img: Image.Image) -> str:
    gray = img.convert("L")

    text = pytesseract.image_to_string(
        gray,
        lang="jpn+eng",
        config="--psm 6"
    )
    return normalize_ocr_text(text)


def calc_text_hash(text: str) -> str:
    return hashlib.md5((text or "").encode("utf-8")).hexdigest()

# ================= OPENAI TRANSLATE =================
def vision_translate(
    img: Image.Image,
    target_lang: str,
    input_lang: str | None,
    text_hash: str
) -> str:
    """
    Dịch bằng vision model.
    Cache PHẢI phân biệt theo:
    (text_hash, target_lang, input_lang)
    """

    cache_key = (text_hash, target_lang, input_lang)

    if cache_key in translation_cache:
        return translation_cache[cache_key]

    prompt = PROMPT_TEMPLATE.format(target_lang=target_lang)
    if input_lang:
        prompt = f"Input language is {input_lang}.\n" + prompt

    resp = client.responses.create(
        model=MODEL,
        input=[{
            "role": "user",
            "content": [
                {"type": "input_text", "text": prompt},
                {
                    "type": "input_image",
                    "image_url": image_to_data_url_png(img)
                },
            ],
        }],
    )

    text = (resp.output_text or "").strip() or "(No text detected)"
    translation_cache[cache_key] = text
    return text

# Removed old make_window_clickthrough - using make_window_click_through instead



# ================= OVERLAY =================
def show_text_overlay(text: str):
    global translation_overlay, translation_canvas
    global overlay_last_text, overlay_last_geometry
    global overlay_text_id, overlay_outline_ids

    if not selected_region or not text:
        return

    # ❌ Text giống → không update
    if text == overlay_last_text:
        return
    overlay_last_text = text

    x, y, w, h = selected_region

    # ======================
    # 1️⃣ TÍNH VỊ TRÍ + SIZE
    # ======================
    if current_translation_mode == "below":
        ox = int(x)
        oy = int(y + h)
        overlay_w = int(w)
        bg = "#111111"
        fg = "#FFFFFF"
    else:
        ox, oy = compute_overlay_xy()
        overlay_w = int(w)

        img = capture_region()
        if img is None:
            return
        bg, fg = estimate_bg_fg(img)

    max_text_width = overlay_w - PAD_X * 2
    family = choose_font_family()
    font_size = 16
    fnt = tkfont.Font(family=family, size=font_size, weight="bold")

    # ======================
    # 2️⃣ TẠO WINDOW (1 LẦN)
    # ======================
    if translation_overlay is None or not translation_overlay.winfo_exists():
        translation_overlay = tk.Toplevel(root)
        translation_overlay.overrideredirect(True)
        translation_overlay.attributes("-topmost", True)
        translation_overlay.attributes("-alpha", OVERLAY_ALPHA)

        translation_canvas = tk.Canvas(
            translation_overlay,
            bg=bg,
            highlightthickness=0
        )
        translation_canvas.pack(fill="both", expand=True)

        overlay_text_id = None
        overlay_outline_ids = []

    translation_canvas.config(bg=bg)

    # ======================
    # 3️⃣ UPDATE TEXT (WRAP)
    # ======================
    if overlay_text_id is None:
        # Outline
        for dx, dy in [(-1, 0), (1, 0), (0, -1), (0, 1)]:
            oid = translation_canvas.create_text(
                PAD_X + dx,
                PAD_Y + dy,
                text=text,
                anchor="nw",
                width=max_text_width,      # ✅ wrap
                fill="#000000",
                font=fnt
            )
            overlay_outline_ids.append(oid)

        # Text chính
        overlay_text_id = translation_canvas.create_text(
            PAD_X,
            PAD_Y,
            text=text,
            anchor="nw",
            width=max_text_width,          # ✅ wrap
            fill=fg,
            font=fnt
        )
    else:
        # Chỉ update nội dung (không recreate)
        for oid in overlay_outline_ids:
            translation_canvas.itemconfig(oid, text=text, width=max_text_width)

        translation_canvas.itemconfig(
            overlay_text_id,
            text=text,
            width=max_text_width,
            fill=fg,
            font=fnt
        )

    # ======================
    # 4️⃣ AUTO RESIZE HEIGHT
    # ======================
    bbox = translation_canvas.bbox(overlay_text_id)
    if bbox:
        needed_h = bbox[3] + PAD_Y
    else:
        needed_h = h

    geom = f"{overlay_w}x{needed_h}+{ox}+{oy}"
    if geom != overlay_last_geometry:
        translation_overlay.geometry(geom)
        overlay_last_geometry = geom

def make_window_click_through(window):
    """Làm overlay HOÀN TOÀN click-through - click xuyên thẳng qua"""
    if not win32gui or not win32con or not win32api:
        print("⚠️ No win32 - click-through disabled")
        return

    try:
        window.update_idletasks()
        hwnd = window.winfo_id()

        # Lấy extended style hiện tại
        ex_style = win32api.GetWindowLong(hwnd, win32con.GWL_EXSTYLE)

        # ✅ BẮT BUỘC: WS_EX_TRANSPARENT (0x20) + WS_EX_LAYERED (0x80000)
        new_style = ex_style | win32con.WS_EX_TRANSPARENT | win32con.WS_EX_LAYERED

        # Set style
        win32api.SetWindowLong(hwnd, win32con.GWL_EXSTYLE, new_style)

        # Force Windows áp dụng style mới
        win32gui.SetWindowPos(
            hwnd,
            win32con.HWND_TOPMOST,
            0, 0, 0, 0,
            win32con.SWP_NOMOVE | win32con.SWP_NOSIZE | win32con.SWP_FRAMECHANGED
        )

        print(f"✅ Click-through enabled: {hex(ex_style)} → {hex(new_style)}")
    except Exception as e:
        print(f"❌ Click-through failed: {e}")
        import traceback
        traceback.print_exc()


def hide_text_overlay():
    global translation_overlay, translation_canvas
    if translation_overlay is not None:
        try:
            translation_overlay.destroy()
        except Exception:
            pass
    translation_overlay = None
    translation_canvas = None


def show_region_border_window():
    """Display a red border around the selected region using a layered transparent window."""
    global region_border_window

    if not selected_region or not show_region_border:
        hide_region_border_window()
        return

    x, y, w, h = selected_region

    # Track window movement if attached to a window
    if tracked_hwnd and tracked_rel:
        rect = get_window_rect(tracked_hwnd)
        if rect:
            wl, wt, wr, wb = rect
            x = wl + tracked_rel[0]
            y = wt + tracked_rel[1]
            x = max(wl, min(x, wr - w))
            y = max(wt, min(y, wb - h))

    if region_border_window is None:
        region_border_window = tk.Toplevel(root)
        region_border_window.overrideredirect(True)
        region_border_window.attributes("-topmost", True)
        region_border_window.configure(bg="black")

        region_border_window.update_idletasks()
        hwnd = region_border_window.winfo_id()

        ex_style = win32api.GetWindowLong(hwnd, win32con.GWL_EXSTYLE)
        ex_style |= win32con.WS_EX_LAYERED | win32con.WS_EX_TRANSPARENT
        win32api.SetWindowLong(hwnd, win32con.GWL_EXSTYLE, ex_style)

    # Move/resize window to region
    region_border_window.geometry(f"{int(w)}x{int(h)}+{int(x)}+{int(y)}")

    # Clear any Tk child widgets – we'll draw purely via layered window
    for widget in region_border_window.winfo_children():
        widget.destroy()

    # Draw border-only via Win32 layered window (center fully transparent)
    if win32gui and win32con and win32api and 'set_layered_border' in globals():
        region_border_window.update_idletasks()
        hwnd = region_border_window.winfo_id()
        try:
            set_layered_border(hwnd, int(w), int(h), BORDER_COLOR, BORDER_WIDTH)
        except Exception:
            # Fallback: at least show a simple border frame if something fails
            frame = tk.Frame(region_border_window, bg=BORDER_COLOR)
            frame.pack(fill="both", expand=True)

    region_border_window.deiconify()

    # Schedule next update to track window movement
    if show_region_border:
        root.after(50, show_region_border_window)


def hide_region_border_window():
    """Hide the region border window"""
    global region_border_window
    if region_border_window is not None:
        try:
            region_border_window.destroy()
        except Exception:
            pass
        region_border_window = None


def toggle_region_border():
    """Toggle the visibility of region border"""
    global show_region_border
    show_region_border = not show_region_border

    if show_region_border:
        show_region_border_window()
        border_toggle_btn.config(text="🟢 Border", bg="#1f7a1f", fg="white")
    else:
        hide_region_border_window()
        border_toggle_btn.config(text="⚫ Border", bg="#7a7a7a", fg="white")


def update_debug_ui(img: Image.Image = None, status: str = ""):
    """Cập nhật UI debug với ảnh capture và status"""
    global debug_label, debug_image_label

    if debug_label:
        debug_label.config(text=status)

    if debug_image_label and img:
        # Resize ảnh để hiển thị nhỏ gọn
        thumb = img.copy()
        thumb.thumbnail((200, 100), Image.Resampling.LANCZOS)
        photo = ImageTk.PhotoImage(thumb)
        debug_image_label.config(image=photo)
        debug_image_label.image = photo  # Keep reference


def on_mouse_click(x, y, button, pressed):
    """Xử lý click chuột - Đơn giản: Click anywhere → OCR → Dịch nếu có text mới"""

    if not pressed:  # Chỉ xử lý khi click down
        return

    if not click_detection_enabled or not selected_region:
        return

    # ✅ ĐƠN GIẢN: Click bất kỳ đâu cũng trigger (không check vùng)
    root.after(0, lambda: update_debug_ui(None, "🖱️ Click detected"))

    def process_click():
        global last_text_hash, last_displayed_text

        try:
            time.sleep(0.15)  # Chờ text render

            # Capture và OCR
            img_ocr = capture_region_for_ocr()
            if not img_ocr:
                root.after(0, lambda: update_debug_ui(None, "No capture"))
                return

            raw = quick_ocr_text(img_ocr)

            # ✅ KHÔNG CÓ TEXT → ẨN OVERLAY
            if not raw or len(raw.strip()) < 2:
                root.after(0, lambda: update_debug_ui(None, "⚪ No text → hide overlay"))
                hide_text_overlay()
                return

            root.after(0, lambda r=raw: update_debug_ui(None, f"OCR: {r[:40]}"))

            # Check hash
            th = calc_text_hash(raw)

            # ✅ TEXT GIỐNG → SKIP
            if th == last_text_hash:
                root.after(0, lambda: update_debug_ui(None, "Same text → skip"))
                return

            last_text_hash = th
            root.after(0, lambda: update_debug_ui(None, "🌐 Translating new text..."))

            # Capture full để translate
            img_full = capture_region()
            if not img_full:
                return

            # Translate
            input_lang = INPUT_LANG_MAP.get(input_lang_combo.get())
            target_lang = TARGET_LANG_MAP.get(target_lang_combo.get(), "Vietnamese")

            text = vision_translate(
                img_full,
                target_lang=target_lang,
                input_lang=input_lang,
                text_hash=th
            )

            # ✅ HIỆN OVERLAY VỚI TEXT MỚI - PHẢI GỌI TỪ MAIN THREAD!
            last_displayed_text = text
            root.after(0, lambda t=text: [
                output.delete("1.0", tk.END),
                output.insert(tk.END, t),
                update_debug_ui(None, f"✅ Translated!"),
                show_text_overlay(t)  # ✅ GỌI TỪ MAIN THREAD
            ])

        except Exception as ex:
            import traceback
            print(f"Click process error: {traceback.format_exc()}")
            root.after(0, lambda e=str(ex): update_debug_ui(None, f"❌ {e}"))

    threading.Thread(target=process_click, daemon=True).start()


def start_mouse_listener():
    """Bắt đầu listen mouse click"""
    global mouse_click_listener, click_detection_enabled

    if mouse_click_listener is None:
        from pynput import mouse as pynput_mouse
        mouse_click_listener = pynput_mouse.Listener(on_click=on_mouse_click)
        mouse_click_listener.start()
        click_detection_enabled = True
        root.after(0, lambda: update_debug_ui(None, "🖱️ Click detection enabled"))


def stop_mouse_listener():
    """Dừng listen mouse click"""
    global mouse_click_listener, click_detection_enabled

    click_detection_enabled = False
    if mouse_click_listener:
        mouse_click_listener.stop()
        mouse_click_listener = None
        root.after(0, lambda: update_debug_ui(None, "🛑 Click detection disabled"))


# ================= REALTIME =================
def realtime_loop():
    global last_displayed_text, last_text_hash
    global last_ocr, last_ocr_change_time
    global last_translated_key
    global last_full_image_hash, last_full_image

    last_strip_hash = None
    loop_count = 0

    while realtime_running:
        try:
            loop_count += 1

            # 1️⃣ Detect thay đổi nhẹ
            strip = capture_detection_strip()
            if strip is None:
                time.sleep(REALTIME_INTERVAL)
                continue

            strip_hash = calc_image_hash(strip)
            if last_strip_hash == strip_hash:
                time.sleep(REALTIME_INTERVAL)
                continue
            last_strip_hash = strip_hash

            # 2️⃣ OCR
            img_ocr = capture_region_for_ocr()
            if img_ocr is None:
                time.sleep(REALTIME_INTERVAL)
                continue

            raw = quick_ocr_text(img_ocr)
            if not raw:
                time.sleep(REALTIME_INTERVAL)
                continue

            now = time.time()

            # 3️⃣ debounce thông minh
            if raw != last_ocr:
                last_ocr = raw
                last_ocr_change_time = now
                time.sleep(REALTIME_INTERVAL)
                continue

            stable_required = get_stable_seconds(raw)
            if now - last_ocr_change_time < stable_required:
                time.sleep(REALTIME_INTERVAL)
                continue

            # 4️⃣ HASH THEO TEXT
            text_hash = calc_text_hash(raw)
            input_lang = INPUT_LANG_MAP.get(input_lang_combo.get())
            target_lang = TARGET_LANG_MAP.get(target_lang_combo.get(), "Vietnamese")

            translated_key = (text_hash, target_lang, input_lang)

            # ✅ KHÔNG ĐỔI → SKIP TẤT CẢ
            if translated_key == last_translated_key:
                time.sleep(REALTIME_INTERVAL)
                continue

            # ⚡ PHẢN HỒI UI
            root.after(0, lambda: show_text_overlay("⏳ Translating…"))

            # ✅ CHỈ CAPTURE KHI TEXT HASH KHÁC
            if text_hash == last_full_image_hash:
                img_full = last_full_image
            else:
                img_full = capture_region()
                if img_full is None:
                    time.sleep(REALTIME_INTERVAL)
                    continue
                last_full_image_hash = text_hash
                last_full_image = img_full

            last_translated_key = translated_key

            if img_full is None:
                time.sleep(REALTIME_INTERVAL)
                continue

            input_lang = INPUT_LANG_MAP.get(input_lang_combo.get())
            target_lang = TARGET_LANG_MAP.get(target_lang_combo.get(), "Vietnamese")

            text = vision_translate(
                img_full,
                target_lang=target_lang,
                input_lang=input_lang,
                text_hash=text_hash
            )

            # 6️⃣ Update UI
            if text != last_displayed_text:
                last_displayed_text = text
                root.after(0, lambda t=text: [
                    output.delete("1.0", tk.END),
                    output.insert(tk.END, t),
                    show_text_overlay(t)
                ])

            time.sleep(REALTIME_INTERVAL)

        except Exception:
            import traceback
            print(traceback.format_exc())
            time.sleep(REALTIME_INTERVAL)

def update_realtime_button():
    if realtime_running:
        if current_translation_mode == "below":
            realtime_btn.config(text="🟢 Auto Below", bg="#1f7a1f", fg="white")
        else:
            realtime_btn.config(text="🟢 Click Mode", bg="#1f7a1f", fg="white")
    else:
        if current_translation_mode == "below":
            realtime_btn.config(text="🔴 Auto Below", bg="#7a1f1f", fg="white")
        else:
            realtime_btn.config(text="🔴 Click Mode", bg="#7a1f1f", fg="white")


def toggle_realtime():
    global realtime_running, last_image_hash, last_displayed_text, last_text_hash
    global last_ocr, last_ocr_change_time

    realtime_running = not realtime_running
    last_image_hash = None
    last_displayed_text = None
    last_text_hash = None

    last_ocr = ""
    last_ocr_change_time = 0.0

    update_realtime_button()

    if realtime_running:
        if not selected_region:
            messagebox.showwarning("No region", "Select a region first")
            realtime_running = False
            update_realtime_button()
            return

        # Handle different translation modes
        if current_translation_mode == "click":
            output.delete("1.0", tk.END)
            output.insert(tk.END, "🖱️ Click Mode: ON\n\nClick anywhere to translate!\n")
            start_mouse_listener()
            root.after(0, lambda: update_debug_ui(None, "✅ Click mode started - click anywhere!"))
        elif current_translation_mode == "below":
            output.delete("1.0", tk.END)
            output.insert(tk.END, "🔄 Auto Below Mode: ON\n\nTranslating in realtime...\n")
            # In "below" mode, show border automatically
            if not show_region_border:
                toggle_region_border()
            # Start realtime loop instead of click detection
            threading.Thread(target=realtime_loop, daemon=True).start()
            root.after(0, lambda: update_debug_ui(None, "✅ Auto below mode started!"))

    else:
        output.delete("1.0", tk.END)
        output.insert(tk.END, "⏹ Detection stopped.\n")
        stop_mouse_listener()
        hide_text_overlay()  # ✅ Ẩn overlay khi tắt
        # Hide border when stopping (unless manually enabled)
        if current_translation_mode == "below":
            hide_region_border_window()



# ================= REGION SELECT (MULTI MONITOR) =================
def on_target_lang_change(event=None):
    global last_translated_key, overlay_last_text

    last_translated_key = None      # reset đúng key
    overlay_last_text = None        # cho phép overlay update

    if last_ocr:
        root.after(0, lambda: show_text_overlay("⏳ Translating…"))

def select_region():
    global selected_region

    root.withdraw()

    with mss.mss() as sct:
        monitor = sct.monitors[0]
        shot = sct.grab(monitor)
        img = Image.frombytes("RGB", shot.size, shot.rgb)
        sw, sh = img.size
        ox, oy = monitor["left"], monitor["top"]

    overlay = tk.Toplevel(root)
    overlay.overrideredirect(True)
    overlay.attributes("-topmost", True)
    overlay.geometry(f"{sw}x{sh}+{ox}+{oy}")

    canvas = tk.Canvas(overlay, cursor="cross", highlightthickness=0)
    canvas.pack(fill="both", expand=True)

    bg = ImageTk.PhotoImage(img)
    canvas.create_image(0, 0, image=bg, anchor="nw")
    canvas.image = bg

    canvas.create_rectangle(0, 0, sw, sh, fill="black", stipple="gray50")

    sx = sy = 0
    rect_id = None

    def on_down(e):
        nonlocal sx, sy, rect_id
        sx, sy = e.x, e.y
        rect_id = canvas.create_rectangle(sx, sy, sx, sy, outline="red", width=2)

    def on_move(e):
        if rect_id is not None:
            canvas.coords(rect_id, sx, sy, e.x, e.y)

    def on_up(e):
        x1, y1 = sx, sy
        x2, y2 = e.x, e.y
        rx = min(x1, x2) + ox
        ry = min(y1, y2) + oy
        rw = abs(x2 - x1)
        rh = abs(y2 - y1)

        if rw < 10 or rh < 10:
            overlay.destroy()
            root.deiconify()
            return

        nonlocal rect_id
        global selected_region
        selected_region = (int(rx), int(ry), int(rw), int(rh))

        overlay.destroy()
        root.deiconify()
        update_tracked_window_from_region()

        # Show border if in "below" mode and realtime is running
        if current_translation_mode == "below" and realtime_running:
            if not show_region_border:
                root.after(100, toggle_region_border)

    canvas.bind("<ButtonPress-1>", on_down)
    canvas.bind("<B1-Motion>", on_move)
    canvas.bind("<ButtonRelease-1>", on_up)


# ================= MANUAL TRANSLATE =================
def start_translate():
    img = capture_region()
    if img is None:
        messagebox.showwarning("Translator", "Chưa chọn vùng text")
        return

    input_lang = INPUT_LANG_MAP.get(input_lang_combo.get())
    target_lang = TARGET_LANG_MAP.get(target_lang_combo.get(), "Vietnamese")

    def task():
        raw = quick_ocr_text(img)
        th = calc_text_hash(raw) if raw else calc_text_hash(calc_image_hash(img))  # fallback

        text = vision_translate(
            img,
            target_lang=target_lang,
            input_lang=input_lang,
            text_hash=th
        )
        output.delete("1.0", tk.END)
        output.insert(tk.END, text)


    threading.Thread(target=task, daemon=True).start()


# ================= MOUSE HOTKEY SUPPORT =================
def normalize_combo(parts: list[str]) -> str:
    order = {"ctrl": 1, "shift": 2, "alt": 3, "win": 4}

    def key_fn(x: str):
        return (order.get(x, 99), x)

    return "+".join(sorted(parts, key=key_fn))


def current_modifiers() -> list[str]:
    mods = []
    if keyboard.is_pressed("ctrl"):
        mods.append("ctrl")
    if keyboard.is_pressed("shift"):
        mods.append("shift")
    if keyboard.is_pressed("alt"):
        mods.append("alt")
    if keyboard.is_pressed("windows") or keyboard.is_pressed("win"):
        mods.append("win")
    return mods


def mouse_event_handler(e):
    if getattr(e, "event_type", "") != "down":
        return
    if hotkeys_suspended or is_recording_hotkey:
        return

    btn = getattr(e, "button", None)
    if not btn:
        return

    parts = current_modifiers() + [f"mouse_{btn}"]
    combo = normalize_combo(parts)

    if HOTKEYS.get("select_region") == combo:
        select_region()
    elif HOTKEYS.get("translate_once") == combo:
        start_translate()
    elif HOTKEYS.get("toggle_realtime") == combo:
        toggle_realtime()


def ensure_mouse_listener():
    global mouse_listener_enabled
    if mouse_listener_enabled:
        return
    mouse.hook(mouse_event_handler)
    mouse_listener_enabled = True


# ================= HOTKEY REGISTER (KEYBOARD + MOUSE) =================
def suspend_hotkeys_full():
    global hotkeys_suspended
    hotkeys_suspended = True
    for hk in list(registered_hotkeys):
        try:
            keyboard.remove_hotkey(hk)
        except Exception:
            pass
    registered_hotkeys.clear()


def resume_hotkeys_full():
    global hotkeys_suspended
    hotkeys_suspended = False
    register_hotkeys_full()


def register_hotkeys_full():
    ensure_mouse_listener()
    suspend_hotkeys_full()

    def add_if_keyboard(action_key: str, callback):
        hk = HOTKEYS.get(action_key, "")
        if hk and ("mouse_" not in hk):
            registered_hotkeys.append(keyboard.add_hotkey(hk, callback))

    add_if_keyboard("select_region", select_region)
    add_if_keyboard("translate_once", start_translate)
    add_if_keyboard("toggle_realtime", toggle_realtime)

    global hotkeys_suspended
    hotkeys_suspended = False


# ================= HOTKEY CONFIG UI (RECORD + ESC CANCEL) =================
def open_hotkey_config():
    win = tk.Toplevel(root)
    win.title("Hotkey Configuration")
    win.geometry("560x250")
    win.resizable(False, False)

    hint = tk.Label(win, text="Bấm Map rồi nhấn tổ hợp phím/chuột. ESC để huỷ.", anchor="w")
    hint.pack(fill="x", padx=10, pady=(10, 6))

    def make_row(label: str, key: str):
        row = tk.Frame(win)
        row.pack(fill="x", padx=10, pady=6)

        tk.Label(row, text=label, width=18, anchor="w").pack(side="left")
        display = tk.Label(row, text=HOTKEYS.get(key, ""), width=28, relief="sunken", anchor="w")
        display.pack(side="left", padx=8)

        def record():
            global is_recording_hotkey
            if is_recording_hotkey:
                return

            is_recording_hotkey = True
            suspend_hotkeys_full()
            display.config(text="Recording... (ESC to cancel)")

            captured = {"done": False, "cancel": False, "combo": None}
            modifier_keys = {"ctrl", "shift", "alt", "windows", "win"}

            def finalize(parts: list[str]):
                if captured["done"]:
                    return
                captured["done"] = True
                captured["combo"] = normalize_combo(parts)

            def cancel():
                if captured["done"]:
                    return
                captured["done"] = True
                captured["cancel"] = True

            def on_key_event(e):
                name = getattr(e, "name", "")
                if not name:
                    return False
                if name == "esc":
                    cancel()
                    return False
                if name in modifier_keys:
                    return False
                parts = current_modifiers() + [name]
                finalize(parts)
                return False

            def on_mouse_event(e):
                if getattr(e, "event_type", "") != "down":
                    return
                btn = getattr(e, "button", None)
                if not btn:
                    return
                parts = current_modifiers() + [f"mouse_{btn}"]
                finalize(parts)

            keyboard.hook(on_key_event, suppress=True)
            mouse.hook(on_mouse_event)

            start_time = time.time()

            def poll():
                if not captured["done"] and (time.time() - start_time) > 6.0:
                    cancel()

                if captured["done"]:
                    try:
                        keyboard.unhook_all()
                    except Exception:
                        pass
                    try:
                        mouse.unhook_all()
                        ensure_mouse_listener()
                    except Exception:
                        pass

                    if captured["cancel"] or not captured["combo"]:
                        display.config(text=HOTKEYS.get(key, ""))
                    else:
                        HOTKEYS[key] = captured["combo"]
                        display.config(text=captured["combo"])
                        save_hotkeys(HOTKEYS)

                    resume_hotkeys_full()
                    global is_recording_hotkey
                    is_recording_hotkey = False
                    return

                win.after(30, poll)

            win.after(30, poll)

        tk.Button(row, text="Map", width=8, command=record).pack(side="left")

    make_row("Chọn vùng", "select_region")
    make_row("Dịch 1 lần", "translate_once")
    make_row("Realtime toggle", "toggle_realtime")

    foot = tk.Label(win, text="Hotkey sẽ lưu vào hotkeys.json", anchor="w")
    foot.pack(fill="x", padx=10, pady=(8, 10))


# ================= UI =================
client = OpenAI(api_key=load_api_key())

root = tk.Tk()
root.title("On-Screen Translator (Realtime Overlay)")
root.geometry("1040x650")

bar = tk.Frame(root)
bar.pack(pady=8)

tk.Button(bar, text="📐 Chọn vùng", command=select_region).pack(side="left", padx=5)
tk.Button(bar, text="🌐 Dịch", command=start_translate).pack(side="left", padx=5)
tk.Button(bar, text="⌨ Hotkey", command=open_hotkey_config).pack(side="left", padx=5)

input_lang_combo = ttk.Combobox(bar, values=list(INPUT_LANG_MAP.keys()), state="readonly", width=14)
input_lang_combo.set("Auto (Detect)")
input_lang_combo.pack(side="left", padx=6)

target_lang_combo = ttk.Combobox(bar, values=list(TARGET_LANG_MAP.keys()), state="readonly", width=12)
target_lang_combo.set("Tiếng Việt")
target_lang_combo.pack(side="left", padx=6)
target_lang_combo.bind("<<ComboboxSelected>>", on_target_lang_change)

realtime_btn = tk.Button(bar, text="🔴 Click Mode", bg="#7a1f1f", fg="white", command=toggle_realtime)
realtime_btn.pack(side="left", padx=8)

# Translation mode selector
translation_mode_combo = ttk.Combobox(bar, values=list(TRANSLATION_MODES.keys()), state="readonly", width=16)
translation_mode_combo.set("Auto Below Region")
translation_mode_combo.pack(side="left", padx=6)

def on_translation_mode_change(event=None):
    global current_translation_mode
    selected = translation_mode_combo.get()
    current_translation_mode = TRANSLATION_MODES.get(selected, "click")
    print(f"🔄 Translation mode changed to: {current_translation_mode}")

    # Update button text immediately
    update_realtime_button()

    # If switching to "below" mode and realtime is on, show border
    if current_translation_mode == "below" and realtime_running:
        if not show_region_border:
            toggle_region_border()

translation_mode_combo.bind("<<ComboboxSelected>>", on_translation_mode_change)

# Border toggle button
border_toggle_btn = tk.Button(bar, text="⚫ Border", bg="#7a7a7a", fg="white", command=toggle_region_border, width=10)
border_toggle_btn.pack(side="left", padx=6)

# Debug frame
debug_frame = tk.LabelFrame(root, text="🔍 Debug Info", padx=10, pady=5)
debug_frame.pack(fill="x", padx=12, pady=(0, 5))

debug_label = tk.Label(debug_frame, text="Ready...", anchor="w", fg="#555")
debug_label.pack(side="left", fill="x", expand=True)

debug_image_label = tk.Label(debug_frame, text="No image", bg="#f0f0f0", width=25, height=5)
debug_image_label.pack(side="right", padx=(10, 0))

output = tk.Text(root, wrap="word")
output.pack(expand=True, fill="both", padx=12, pady=10)

HOTKEYS = load_hotkeys()
register_hotkeys_full()
update_realtime_button()

root.mainloop()
