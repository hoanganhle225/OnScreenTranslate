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

# ================= PATHS =================
BASE_DIR = os.path.dirname(os.path.abspath(__file__))
API_KEY_FILE = os.path.join(BASE_DIR, "api-key.txt")
HOTKEY_FILE = os.path.join(BASE_DIR, "hotkeys.json")

# ================= CONFIG =================
MODEL = "gpt-4.1-mini"
REALTIME_INTERVAL = 0.25
OVERLAY_ALPHA = 0.86
STABLE_SECONDS = 0.4
PAD_X = 8
PAD_Y = 6
OUTLINE_PX = 1
OUTLINE_COLOR = "#000000"
FONT_FAMILY_PRIMARY = "Meiryo"
FONT_FAMILY_FALLBACK = "Segoe UI"
FONT_MIN = 10
FONT_MAX = 34
OCR_SAFE_MARGIN = 4   # px
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
except Exception:
    win32gui = None

# ================= GLOBAL STATE =================
selected_region = None  # (x, y, w, h) in virtual screen coords
tracked_hwnd = None
tracked_rel = None  # (rel_x, rel_y) from window top-left

client = None

realtime_running = False
last_image_hash = None
last_displayed_text = None
last_text_hash = None

translation_cache = {}  # hash -> text

# overlay widgets
translation_overlay = None
translation_canvas = None

# hotkey management
registered_hotkeys = []
hotkeys_suspended = False
is_recording_hotkey = False
mouse_listener_enabled = False

last_ocr = ""
last_ocr_change_time = 0.0
# ================= HELPERS =================
def load_api_key() -> str:
    if not os.path.exists(API_KEY_FILE):
        raise FileNotFoundError(f"Missing {API_KEY_FILE}. Put your API key in api-key.txt")
    with open(API_KEY_FILE, "r", encoding="utf-8") as f:
        key = f.read().strip()
    if not key:
        raise ValueError("api-key.txt is empty")
    return key


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


def calc_image_hash(img: Image.Image) -> str:
    # More sensitive hash so small UI text changes are detected
    small = img.resize((320, 120)).convert("L")
    arr = np.asarray(small)
    return hashlib.md5(arr.tobytes()).hexdigest()


def capture_region_for_ocr() -> Image.Image | None:
    if not selected_region:
        return None

    x, y, w, h = selected_region

    # Cắt chỉ vùng giữa (tránh overlay text)
    top_cut = int(h * 0.15)
    bottom_cut = int(h * 0.35)

    x += OCR_SAFE_MARGIN
    y += top_cut
    w -= OCR_SAFE_MARGIN * 2
    h = h - top_cut - bottom_cut

    if w < 10 or h < 10:
        return None

    with mss.mss() as sct:
        shot = sct.grab({
            "left": int(x),
            "top": int(y),
            "width": int(w),
            "height": int(h)
        })
    return Image.frombytes("RGB", shot.size, shot.rgb)


def capture_region() -> Image.Image | None:
    if not selected_region:
        return None
    x, y, w, h = selected_region
    if w < 4 or h < 4:
        return None
    with mss.mss() as sct:
        shot = sct.grab({"left": int(x), "top": int(y), "width": int(w), "height": int(h)})
    return Image.frombytes("RGB", shot.size, shot.rgb)


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
    # gộp khoảng trắng để tránh “text đổi giả”
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
    # ✅ Cache theo TEXT, không theo ảnh
    if text_hash in translation_cache:
        return translation_cache[text_hash]

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

    text = (resp.output_text or "").strip()
    if not text:
        text = "(No text detected)"

    # ✅ Lưu cache theo text_hash
    translation_cache[text_hash] = text
    return text



# ================= OVERLAY =================
def show_text_overlay(text: str):
    global translation_overlay, translation_canvas

    if not realtime_running or not selected_region:
        return

    x, y, w, h = selected_region
    ox, oy = compute_overlay_xy()

    img = capture_region()
    if img is None:
        return

    bg, fg = estimate_bg_fg(img)
    family = choose_font_family()
    size = fit_font_size(text, int(w), int(h), family)

    if translation_overlay is None:
        translation_overlay = tk.Toplevel(root)
        translation_overlay.overrideredirect(True)
        translation_overlay.attributes("-topmost", True)
        translation_overlay.attributes("-alpha", OVERLAY_ALPHA)
        translation_overlay.geometry(f"{int(w)}x{int(h)}+{int(ox)}+{int(oy)}")

        translation_canvas = tk.Canvas(
            translation_overlay,
            bg=bg,
            highlightthickness=0
        )
        translation_canvas.pack(fill="both", expand=True)

    else:
        translation_overlay.geometry(f"{int(w)}x{int(h)}+{int(ox)}+{int(oy)}")
        translation_canvas.config(bg=bg)

    # ✅ QUAN TRỌNG: clear toàn bộ text cũ
    translation_canvas.delete("all")

    # vẽ lại text mới
    fnt = tkfont.Font(family=family, size=size, weight="bold")
    line_h = fnt.metrics("linespace")

    draw_x = PAD_X
    draw_y = PAD_Y

    for line in (text.split("\n") if text else [""]):
        for dx, dy in [(-OUTLINE_PX, 0), (OUTLINE_PX, 0), (0, -OUTLINE_PX), (0, OUTLINE_PX)]:
            translation_canvas.create_text(
                draw_x + dx, draw_y + dy,
                text=line,
                anchor="nw",
                fill=OUTLINE_COLOR,
                font=fnt
            )
        translation_canvas.create_text(
            draw_x, draw_y,
            text=line,
            anchor="nw",
            fill=fg,
            font=fnt
        )
        draw_y += line_h

        


def hide_text_overlay():
    global translation_overlay, translation_canvas
    if translation_overlay is not None:
        try:
            translation_overlay.destroy()
        except Exception:
            pass
    translation_overlay = None
    translation_canvas = None


# ================= REALTIME =================
def realtime_loop():
    global last_displayed_text, last_text_hash
    global last_ocr, last_ocr_change_time

    while realtime_running:
        try:
            # 1️⃣ OCR dùng vùng riêng (không ăn overlay)
            img_ocr = capture_region_for_ocr()
            if img_ocr is None:
                time.sleep(REALTIME_INTERVAL)
                continue

            raw = quick_ocr_text(img_ocr)
            if not raw:
                time.sleep(REALTIME_INTERVAL)
                continue

            # 2️⃣ Debounce typing effect
            now = time.time()
            if raw != last_ocr:
                last_ocr = raw
                last_ocr_change_time = now
                time.sleep(REALTIME_INTERVAL)
                continue

            if now - last_ocr_change_time < STABLE_SECONDS:
                time.sleep(REALTIME_INTERVAL)
                continue

            # 3️⃣ Hash theo text, fallback theo ảnh
            img_full = capture_region()
            
            if img_full is None:
                time.sleep(REALTIME_INTERVAL)
                continue

            if len(raw) < 3:
                th = calc_image_hash(img_full)
            else:
                th = calc_text_hash(raw)

            if th == last_text_hash:
                time.sleep(REALTIME_INTERVAL)
                continue

            last_text_hash = th

            # 4️⃣ Translate
            input_lang = INPUT_LANG_MAP.get(input_lang_combo.get())
            target_lang = TARGET_LANG_MAP.get(target_lang_combo.get(), "Vietnamese")

            text = vision_translate(
                img_full,
                target_lang=target_lang,
                input_lang=input_lang,
                text_hash=th
            )

            # 5️⃣ Update UI + overlay
            if text != last_displayed_text:
                last_displayed_text = text
                output.delete("1.0", tk.END)
                output.insert(tk.END, text)
                show_text_overlay(text)

            time.sleep(REALTIME_INTERVAL)

        except Exception as ex:
            output.delete("1.0", tk.END)
            output.insert(tk.END, f"[Realtime error] {ex}\n")
            time.sleep(REALTIME_INTERVAL)




def update_realtime_button():
    if realtime_running:
        realtime_btn.config(text="🟢 Realtime", bg="#1f7a1f", fg="white")
    else:
        realtime_btn.config(text="🔴 Realtime", bg="#7a1f1f", fg="white")


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
        update_tracked_window_from_region()
        threading.Thread(target=realtime_loop, daemon=True).start()
    else:
        hide_text_overlay()



# ================= REGION SELECT (MULTI MONITOR) =================
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
root.geometry("1040x600")

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

realtime_btn = tk.Button(bar, text="🔴 Realtime", bg="#7a1f1f", fg="white", command=toggle_realtime)
realtime_btn.pack(side="left", padx=8)

output = tk.Text(root, wrap="word")
output.pack(expand=True, fill="both", padx=12, pady=10)

HOTKEYS = load_hotkeys()
register_hotkeys_full()
update_realtime_button()

root.mainloop()
