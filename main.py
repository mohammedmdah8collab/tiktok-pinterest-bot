# -*- coding: utf-8 -*-
"""
بوت تيليجرام سريع لتحميل فيديوهات وصور تيك توك وبنترست
المكتبات: pyTelegramBotAPI، requests، yt-dlp (احتياط)
ffmpeg اختياري: الضغط التلقائي وصوت MP3 لفيديوهات بنترست
"""

import os
import re
import copy
import html
import json
import glob
import time
import shutil
import socket
import secrets
import tempfile
import threading
import subprocess
from contextlib import contextmanager, ExitStack
from concurrent.futures import ThreadPoolExecutor
from concurrent.futures import TimeoutError as FuturesTimeout
from datetime import datetime

import requests
from requests.adapters import HTTPAdapter
import telebot
from telebot import types
from telebot.apihelper import ApiTelegramException

# ==========================================================
#                    الإعدادات الأساسية
# ==========================================================
BOT_TOKEN = os.getenv("BOT_TOKEN", "PUT_YOUR_BOT_TOKEN_HERE")
ADMIN_ID = int(os.getenv("ADMIN_ID", "0") or 0)

USERS_FILE = "users.json"
CONFIG_FILE = "config.json"
FILEIDS_FILE = "cache_ids.json"
CACHE_DIR = "media_cache"
os.makedirs(CACHE_DIR, exist_ok=True)

TIKWM_API = "https://www.tikwm.com/api/"
UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/124.0 Safari/537.36")
MEDIA_HEADERS = {"Referer": "https://www.tiktok.com/", "Accept": "*/*"}

# ---- المهل الزمنية (بالثواني) ----
CONNECT_TIMEOUT = 5
API_READ_TIMEOUT = 10
MEDIA_READ_TIMEOUT = 10
PAGE_READ_TIMEOUT = 8
REQUEST_BUDGET = 60        # أقصى زمن كامل للطلب الواحد قبل إعلان الخطأ
YTDLP_BUDGET = 25          # أقصى زمن لمحاولة yt-dlp
TIKWM_MIN_INTERVAL = 1.0
TELEGRAM_READ_TIMEOUT = 180

# ---- الحدود ----
MAX_BYTES = 50 * 1024 * 1024           # حد رفع الملفات عبر Bot API
PHOTO_MAX_BYTES = 10 * 1024 * 1024     # الصورة الأكبر منه تُرسل كملف
DOWNLOAD_CAP = 2 * 1024 * 1024 * 1024  # أقصى حجم نقبله من المصدر
MAX_ALBUM = 30
DL_WORKERS = 6
TOKEN_TTL = 3600
SUB_CACHE_TTL = 60

telebot.apihelper.READ_TIMEOUT = TELEGRAM_READ_TIMEOUT

FFMPEG = shutil.which("ffmpeg")
FFPROBE = shutil.which("ffprobe")
HAS_FFMPEG = bool(FFMPEG)

PLATFORM_PATTERNS = [
    ("tiktok", re.compile(r"https?://(?:[\w-]+\.)?tiktok\.com/[^\s]+", re.I)),
    ("pinterest", re.compile(r"https?://(?:[\w-]+\.)?(?:pinterest\.[a-z.]+|pin\.it)/[^\s]+", re.I)),
]

VIDEO_EXT = {".mp4", ".webm", ".mkv", ".mov", ".m4v"}
PHOTO_EXT = {".jpg", ".jpeg", ".png", ".webp"}
AUDIO_EXT = {".m4a", ".mp3", ".aac", ".opus", ".ogg", ".webm"}

DEFAULT_CONFIG = {
    "bot_active": True,
    "force_sub_enabled": False,
    "force_channels": [],
    "stats": {"downloads": 0},
    "texts": {
        "welcome": "🎬 <b>أهلاً بك في بوت تحميل الفيديوهات</b>\n\nأرسل رابط فيديو أو صور من تيك توك أو بنترست، وسأرسله لك بأعلى جودة.",
        "loading": "⏳ جاري التحميل...",
        "done": "✅ تم التحميل بنجاح",
        "subscribe": "⚠️ يجب الاشتراك في القنوات التالية أولاً، ثم اضغط «تحققت من الاشتراك».",
        "maintenance": "🛠 البوت في وضع الصيانة حالياً، يرجى المحاولة لاحقاً.",
        "invalid": "❌ أرسل رابط تيك توك أو بنترست صحيح.",
        "error": "❌ حدث خطأ غير متوقع، حاول مرة أخرى.",
        "too_big": "❌ حجم الملف أكبر من الحد المسموح (50 ميغابايت).",
        "compressed": "⚠️ الفيديو الأصلي أكبر من 50 ميغابايت، لذلك تم ضغطه ليصل إليك، وقد تقل الجودة قليلاً.",
        "partial": "⚠️ بعض الملفات فشل تحميلها أو تجاوزت الحد، وتم تخطيها.",
        "no_media": "❌ لم أجد وسائط قابلة للتحميل في هذا الرابط.",
        "options": "⬇️ خيارات التحميل",
        "err_timeout": "⏱ المصدر لم يستجب بسرعة، حاول مرة أخرى بعد لحظات.",
        "err_network": "🌐 تعذر الاتصال بالمصدر، تأكد من الشبكة وحاول مرة أخرى.",
        "err_private": "🔒 هذا المحتوى خاص ولا يمكن تحميله.",
        "err_unavailable": "🚫 المحتوى غير متوفر أو تم حذفه.",
    },
    "buttons": {
        "sub_channel": {"text": "📢 اشترك هنا", "style": "primary", "icon": ""},
        "sub_check": {"text": "✅ تحققت من الاشتراك", "style": "success", "icon": ""},
        "hd": {"text": "🎬 تحميل الفيديو بجودة HD", "style": "primary", "icon": ""},
        "original": {"text": "📁 تحميل بجودة أصلية", "style": "primary", "icon": ""},
        "mp3": {"text": "🎵 تحويل الفيديو إلى MP3", "style": "", "icon": ""},
    },
}

TEXT_LABELS = {
    "welcome": "الترحيب",
    "loading": "جاري التحميل",
    "done": "تم التحميل",
    "subscribe": "الاشتراك الإجباري",
    "maintenance": "الصيانة",
    "invalid": "رابط غير صالح",
    "error": "خطأ عام",
    "too_big": "حجم كبير",
    "compressed": "رسالة الضغط",
    "partial": "ملفات متخطاة",
    "no_media": "لا توجد وسائط",
    "options": "عنوان الخيارات",
    "err_timeout": "خطأ: مهلة",
    "err_network": "خطأ: اتصال",
    "err_private": "خطأ: خاص",
    "err_unavailable": "خطأ: غير متوفر",
}

BUTTON_LABELS = {
    "sub_channel": "زر قناة الاشتراك",
    "sub_check": "زر التحقق من الاشتراك",
    "hd": "زر HD",
    "original": "زر الجودة الأصلية",
    "mp3": "زر MP3",
}

COLOR_NAMES = {
    "primary": "🔵 أزرق",
    "success": "🟢 أخضر",
    "danger": "🔴 أحمر",
    "": "⚪ بدون لون",
}


# ==========================================================
#                    الاستثناءات وتصنيف الأخطاء
# ==========================================================
class TooBigError(Exception):
    pass


class NoMediaError(Exception):
    pass


class SourceError(Exception):
    """kind: timeout / network / private / unavailable / other"""

    def __init__(self, kind):
        super().__init__(kind)
        self.kind = kind


SOURCE_TEXT = {
    "timeout": "err_timeout",
    "network": "err_network",
    "private": "err_private",
    "unavailable": "err_unavailable",
    "other": "error",
}


class Budget:
    """ميزانية زمنية واحدة يشترك فيها كل خطوات الطلب."""

    def __init__(self, seconds):
        self.end = time.time() + seconds

    def left(self):
        return self.end - time.time()

    def check(self):
        if self.left() <= 0:
            raise SourceError("timeout")


def failure_kind(exc):
    if exc is None:
        return "other"
    if isinstance(exc, SourceError):
        return exc.kind
    if isinstance(exc, NoMediaError):
        return "nomedia"
    if isinstance(exc, (requests.Timeout, socket.timeout, TimeoutError)):
        return "timeout"
    if isinstance(exc, (requests.ConnectionError, socket.gaierror)):
        return "network"
    msg = str(exc).lower()
    if "timed out" in msg or "timeout" in msg:
        return "timeout"
    if any(w in msg for w in ("name or service not known", "failed to resolve", "connection refused",
                              "network is unreachable", "connection reset", "temporary failure")):
        return "network"
    if any(w in msg for w in ("private", "login", "sign in", "members only", "cookies")):
        return "private"
    if any(w in msg for w in ("http error 403", "http error 404", "http error 410",
                              "unavailable", "removed", "deleted", "does not exist")):
        return "unavailable"
    return "other"


def pick_failure(errors):
    """يختار أوضح سبب فشل من قائمة الأخطاء."""
    kinds = {"nomedia" if isinstance(e, NoMediaError) else failure_kind(e) for e in errors}
    for k in ("timeout", "network", "private", "unavailable"):
        if k in kinds:
            return SourceError(k)
    if kinds == {"nomedia"}:
        return NoMediaError()
    return SourceError("other")


def report_error(chat_id, reply_to, exc):
    if isinstance(exc, TooBigError):
        key = "too_big"
    elif isinstance(exc, NoMediaError):
        key = "no_media"
    elif isinstance(exc, SourceError):
        key = SOURCE_TEXT.get(exc.kind, "error")
    else:
        print(f"[error] {type(exc).__name__}: {exc}")
        key = "error"
    try:
        bot.send_message(chat_id, CONFIG["texts"][key], reply_to_message_id=reply_to)
    except Exception as e:
        print(f"[report] تعذر إرسال رسالة الخطأ: {e}")


# ==========================================================
#                    التخزين (JSON)
# ==========================================================
_file_lock = threading.RLock()


def load_json(path, default):
    with _file_lock:
        if not os.path.exists(path):
            data = copy.deepcopy(default)
            save_json(path, data)
            return data
        try:
            with open(path, "r", encoding="utf-8") as f:
                return json.load(f)
        except (json.JSONDecodeError, OSError) as e:
            print(f"[WARN] تعذر قراءة {path}: {e}")
            return copy.deepcopy(default)


def save_json(path, data):
    with _file_lock:
        tmp = path + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False, indent=2)
        os.replace(tmp, path)


def load_config():
    cfg = load_json(CONFIG_FILE, DEFAULT_CONFIG)
    for key, value in DEFAULT_CONFIG.items():
        if key not in cfg:
            cfg[key] = copy.deepcopy(value)
    for key, value in DEFAULT_CONFIG["texts"].items():
        cfg["texts"].setdefault(key, value)
    for key, value in DEFAULT_CONFIG["buttons"].items():
        cfg["buttons"].setdefault(key, copy.deepcopy(value))
    cfg["stats"].setdefault("downloads", 0)
    return cfg


def save_config():
    with _file_lock:
        save_json(CONFIG_FILE, CONFIG)


def save_users():
    with _file_lock:
        save_json(USERS_FILE, USERS)


def save_file_ids():
    with _file_lock:
        save_json(FILEIDS_FILE, FILE_IDS)


CONFIG = load_config()
USERS = load_json(USERS_FILE, {})
FILE_IDS = load_json(FILEIDS_FILE, {})

bot = telebot.TeleBot(BOT_TOKEN, parse_mode="HTML", num_threads=16)

SESSION = requests.Session()
SESSION.headers.update({"User-Agent": UA})
SESSION.mount("https://", HTTPAdapter(pool_connections=20, pool_maxsize=40, max_retries=0))
SESSION.mount("http://", HTTPAdapter(pool_connections=20, pool_maxsize=40, max_retries=0))

TOKENS = {}
SUB_CACHE = {}
ADMIN_STATE = {}
_tikwm_lock = threading.Lock()
_tikwm_last = [0.0]
YTDLP_POOL = ThreadPoolExecutor(max_workers=4)


# ==========================================================
#        تحويل النص + الإيموجيات البريميوم إلى HTML
# ==========================================================
SIMPLE_TAGS = {
    "bold": "b",
    "italic": "i",
    "underline": "u",
    "strikethrough": "s",
    "code": "code",
    "pre": "pre",
    "spoiler": "tg-spoiler",
    "blockquote": "blockquote",
    "expandable_blockquote": "blockquote",
}


def _wrap_entity(ent, inner):
    if ent.type == "custom_emoji":
        emoji_id = html.escape(str(ent.custom_emoji_id), quote=True)
        return f'<tg-emoji emoji-id="{emoji_id}">{inner}</tg-emoji>'
    if ent.type == "text_link" and ent.url:
        return f'<a href="{html.escape(ent.url, quote=True)}">{inner}</a>'
    tag = SIMPLE_TAGS.get(ent.type)
    if tag:
        return f"<{tag}>{inner}</{tag}>"
    return inner


def entities_to_html(text, entities):
    """يحوّل النص ومعه message.entities إلى HTML. تيليجرام يحسب الإزاحات بوحدات UTF-16."""
    if not text:
        return ""
    units = text.encode("utf-16-le")
    total = len(units) // 2

    def seg(a, b):
        return units[a * 2:b * 2].decode("utf-16-le")

    def render(start, end, ents):
        out = []
        pos = start
        inside = sorted(
            [e for e in ents if e.offset >= start and e.offset + e.length <= end],
            key=lambda e: (e.offset, -e.length),
        )
        for ent in inside:
            if ent.offset < pos or ent.length <= 0:
                continue
            out.append(html.escape(seg(pos, ent.offset), quote=False))
            ent_end = ent.offset + ent.length
            inner = render(ent.offset, ent_end, [x for x in ents if x is not ent])
            out.append(_wrap_entity(ent, inner))
            pos = ent_end
        out.append(html.escape(seg(pos, end), quote=False))
        return "".join(out)

    return render(0, total, list(entities or []))


# ==========================================================
#                    الأزرار المُلوّنة
# ==========================================================
class StyledButton:
    """زر إنلاين يدعم اللون (style) والإيموجي البريميوم (icon_custom_emoji_id)."""

    def __init__(self, text, url=None, callback_data=None, style=None, icon_custom_emoji_id=None):
        self.text = text
        self.url = url
        self.callback_data = callback_data
        self.style = style
        self.icon_custom_emoji_id = icon_custom_emoji_id

    def to_dict(self):
        data = {"text": self.text}
        if self.url:
            data["url"] = self.url
        if self.callback_data:
            data["callback_data"] = self.callback_data
        if self.style in ("primary", "success", "danger"):
            data["style"] = self.style
        if self.icon_custom_emoji_id:
            data["icon_custom_emoji_id"] = str(self.icon_custom_emoji_id)
        return data


def make_btn(key, url=None, callback_data=None, text=None):
    b = CONFIG["buttons"][key]
    return StyledButton(
        text or b.get("text") or key,
        url=url,
        callback_data=callback_data,
        style=b.get("style") or None,
        icon_custom_emoji_id=b.get("icon") or None,
    )


# ==========================================================
#                    أدوات عامة
# ==========================================================
def is_admin(user_id):
    return ADMIN_ID != 0 and user_id == ADMIN_ID


def register_user(user):
    uid = str(user.id)
    with _file_lock:
        if uid in USERS:
            return
        USERS[uid] = {
            "name": user.first_name or "",
            "username": user.username or "",
            "joined": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
        }
        save_users()


def bump_downloads():
    with _file_lock:
        CONFIG["stats"]["downloads"] = CONFIG["stats"].get("downloads", 0) + 1
        save_config()


def new_token(**data):
    if len(TOKENS) > 2000:
        TOKENS.clear()
    token_id = secrets.token_urlsafe(9)
    data["created"] = time.time()
    TOKENS[token_id] = data
    return token_id


def cache_key(platform, url):
    base = url.split("?")[0].split("#")[0].rstrip("/")
    return f"{platform}|{base}"


def detect_platform(text):
    for name, pattern in PLATFORM_PATTERNS:
        match = pattern.search(text or "")
        if match:
            return name, match.group(0)
    return None


def media_kind(path):
    ext = os.path.splitext(path)[1].lower()
    if ext in VIDEO_EXT:
        return "video"
    if ext in PHOTO_EXT:
        return "photo"
    return None


# ==========================================================
#                    الاشتراك الإجباري
# ==========================================================
def is_subscribed(user_id):
    """يرجع (True/False, القنوات الناقصة). التحقق متوازٍ ومخزن لدقيقة."""
    if not CONFIG["force_sub_enabled"] or not CONFIG["force_channels"]:
        return True, []

    cached = SUB_CACHE.get(user_id)
    if cached and time.time() - cached[0] < SUB_CACHE_TTL:
        return cached[1], cached[2]

    channels = list(CONFIG["force_channels"])

    def check(ch):
        try:
            member = bot.get_chat_member(ch, user_id)
            return ch if member.status in ("left", "kicked") else None
        except Exception as e:
            print(f"[force-sub] تعذر التحقق من {ch}: {e}")
            return None

    with ThreadPoolExecutor(max_workers=min(8, len(channels))) as ex:
        results = list(ex.map(check, channels))

    missing = [c for c in results if c]
    ok = not missing
    SUB_CACHE[user_id] = (time.time(), ok, missing)
    return ok, missing


def subscribe_markup(channels):
    kb = types.InlineKeyboardMarkup()
    b = CONFIG["buttons"]["sub_channel"]
    for ch in channels:
        if ch.startswith("@"):
            kb.row(StyledButton(
                f"{b.get('text', '📢')} {ch}",
                url=f"https://t.me/{ch[1:]}",
                style=b.get("style") or None,
                icon_custom_emoji_id=b.get("icon") or None,
            ))
    kb.row(make_btn("sub_check", callback_data="check_sub"))
    return kb


def check_access(user_id, chat_id):
    if is_admin(user_id):
        return True
    if not CONFIG["bot_active"]:
        bot.send_message(chat_id, CONFIG["texts"]["maintenance"])
        return False
    ok, missing = is_subscribed(user_id)
    if not ok:
        bot.send_message(chat_id, CONFIG["texts"]["subscribe"], reply_markup=subscribe_markup(missing))
        return False
    return True


# ==========================================================
#                    التنزيل السريع
# ==========================================================
def _stream_to_file(url, dest, budget, headers=None):
    with SESSION.get(url, headers={**MEDIA_HEADERS, **(headers or {})}, stream=True,
                     timeout=(CONNECT_TIMEOUT, MEDIA_READ_TIMEOUT)) as r:
        if r.status_code in (401, 403, 404, 410):
            raise SourceError("unavailable")
        r.raise_for_status()
        declared = int(r.headers.get("Content-Length") or 0)
        if declared > DOWNLOAD_CAP:
            raise TooBigError()
        total = 0
        with open(dest, "wb") as f:
            for chunk in r.iter_content(chunk_size=512 * 1024):
                budget.check()
                if not chunk:
                    continue
                total += len(chunk)
                if total > DOWNLOAD_CAP:
                    raise TooBigError()
                f.write(chunk)
    if total == 0:
        raise SourceError("unavailable")
    return dest


def download_to(url, dest, budget, headers=None, attempts=2):
    """تنزيل ملف واحد. يعيد المحاولة مرة واحدة فقط عند تعطل الاتصال العابر."""
    last = None
    for _ in range(attempts):
        budget.check()
        try:
            return _stream_to_file(url, dest, budget, headers)
        except (TooBigError, SourceError) as e:
            if isinstance(e, TooBigError) or e.kind in ("unavailable", "private", "timeout"):
                raise
            last = e
        except Exception as e:
            last = e
        if budget.left() < 3:
            break
    raise SourceError(failure_kind(last))


def download_first(urls, dest, budget):
    """يجرب الروابط البديلة بالترتيب ويرجع أول نجاح."""
    if not urls:
        raise NoMediaError()
    errors = []
    for url in urls:
        try:
            return download_to(url, dest, budget)
        except TooBigError:
            raise
        except Exception as e:
            errors.append(e)
            print(f"[download] فشل الرابط، أجرب البديل: {e}")
    raise pick_failure(errors)


def download_many(urls, work_dir, prefix, budget):
    """تنزيل متوازٍ للصور ضمن الميزانية الزمنية. يرجع الناجح فقط."""
    urls = urls[:MAX_ALBUM]

    def job(item):
        i, url = item
        ext = os.path.splitext(url.split("?")[0])[1].lower()
        if ext not in PHOTO_EXT:
            ext = ".jpg"
        dest = os.path.join(work_dir, f"{prefix}_{i:03d}{ext}")
        try:
            return download_to(url, dest, budget)
        except Exception as e:
            print(f"[download] تخطي الصورة {i}: {e}")
            return e

    with ThreadPoolExecutor(max_workers=DL_WORKERS) as ex:
        results = list(ex.map(job, enumerate(urls)))

    ok = [r for r in results if isinstance(r, str)]
    if ok:
        return ok
    errors = [r for r in results if isinstance(r, Exception)]
    if any(isinstance(e, TooBigError) for e in errors):
        raise TooBigError()
    raise pick_failure(errors) if errors else NoMediaError()


# ==========================================================
#                    تيك توك (TikWM)
# ==========================================================
def abs_tikwm(u):
    if not u:
        return None
    return u if u.startswith("http") else "https://www.tikwm.com" + u


def tikwm_info(url, budget):
    with _tikwm_lock:
        wait = TIKWM_MIN_INTERVAL - (time.time() - _tikwm_last[0])
        if wait > 0:
            time.sleep(max(0, min(wait, budget.left())))
        _tikwm_last[0] = time.time()
    budget.check()

    r = SESSION.post(TIKWM_API, data={"url": url, "hd": 1},
                     timeout=(CONNECT_TIMEOUT, API_READ_TIMEOUT))
    r.raise_for_status()
    payload = r.json()
    data = payload.get("data")
    if payload.get("code") != 0 or not data:
        raise NoMediaError()

    images = [u for u in (abs_tikwm(x) for x in (data.get("images") or [])) if u]
    videos = []
    if not images:
        for key in ("hdplay", "play"):
            u = abs_tikwm(data.get(key))
            if u and u not in videos:
                videos.append(u)
    if not images and not videos:
        raise NoMediaError()
    return {"videos": videos, "images": images, "music": abs_tikwm(data.get("music"))}


def fetch_tiktok(url, work_dir, budget):
    errors = []
    try:
        info = tikwm_info(url, budget)
        if info["images"]:
            files = download_many(info["images"], work_dir, "tt", budget)
        else:
            files = [download_first(info["videos"], os.path.join(work_dir, "tiktok.mp4"), budget)]
        if info["music"]:
            audio = {"direct": info["music"]}
        else:
            audio = {"local": True} if HAS_FFMPEG else None
        return files, audio
    except TooBigError:
        raise
    except Exception as e:
        print(f"[tiktok] TikWM فشل: {e}")
        errors.append(e)

    return _ytdlp_fallback(url, work_dir, budget, errors)


# ==========================================================
#                    yt-dlp (احتياط)
# ==========================================================
def _ytdlp_run(url, work_dir, audio_only):
    import yt_dlp  # استيراد كسول حتى لا يتعطل البوت عند غياب المكتبة

    if audio_only:
        fmt, merge = "bestaudio[ext=m4a]/bestaudio/best", None
    elif HAS_FFMPEG:
        fmt, merge = "bestvideo[ext=mp4]+bestaudio[ext=m4a]/bestvideo+bestaudio/best", "mp4"
    else:
        fmt, merge = "best[ext=mp4]/best", None

    opts = {
        "format": fmt,
        "outtmpl": os.path.join(work_dir, "%(id)s.%(ext)s"),
        "quiet": True,
        "no_warnings": True,
        "noplaylist": True,
        "restrictfilenames": True,
        "socket_timeout": 10,
        "retries": 0,
        "fragment_retries": 0,
        "concurrent_fragment_downloads": 4,
        "geo_bypass": True,
    }
    if merge:
        opts["merge_output_format"] = merge

    with yt_dlp.YoutubeDL(opts) as ydl:
        ydl.extract_info(url, download=True)

    files = [
        p for p in glob.glob(os.path.join(work_dir, "*"))
        if os.path.isfile(p) and os.path.splitext(p)[1].lower() in (VIDEO_EXT | PHOTO_EXT | AUDIO_EXT)
    ]
    return sorted(files)


def ytdlp_download(url, work_dir, budget, audio_only=False):
    left = min(budget.left(), YTDLP_BUDGET)
    if left <= 1:
        raise SourceError("timeout")
    future = YTDLP_POOL.submit(_ytdlp_run, url, work_dir, audio_only)
    try:
        return future.result(timeout=left)
    except FuturesTimeout:
        raise SourceError("timeout")
    except ImportError:
        print("[yt-dlp] المكتبة غير مثبتة: pip3 install -U yt-dlp")
        raise SourceError("other")


def _ytdlp_fallback(url, work_dir, budget, errors):
    try:
        files = ytdlp_download(url, work_dir, budget)
    except TooBigError:
        raise
    except Exception as e:
        errors.append(e)
        raise pick_failure(errors)
    if not files:
        raise pick_failure(errors or [NoMediaError()])
    has_video = any(media_kind(f) == "video" for f in files)
    return files, ({"ytdlp": url} if has_video else None)


# ==========================================================
#                    بنترست
# ==========================================================
META_RE = re.compile(r"<meta\s[^>]*>", re.IGNORECASE)
ATTR_RE = re.compile(r"([\w:-]+)\s*=\s*[\"']([^\"']*)[\"']")
PIN_MP4_RE = re.compile(r"https://v\d*\.pinimg\.com/videos/[^\s\"'<>]+?\.mp4")


def pinterest_original(u):
    """يرفع دقة صور بنترست من 736px وأقل إلى النسخة الأصلية."""
    return re.sub(r"/(?:236x|474x|564x|736x)/", "/originals/", u)


def _res_score(u):
    m = re.search(r"/(\d{3,4})p/", u) or re.search(r"(\d{3,4})p", u)
    return int(m.group(1)) if m else 0


def pinterest_page(url, budget):
    budget.check()
    r = SESSION.get(url, timeout=(CONNECT_TIMEOUT, PAGE_READ_TIMEOUT),
                    headers={"Accept-Language": "en,ar;q=0.8"})
    r.raise_for_status()
    text = r.text[:900000].replace("\\/", "/")

    images, videos = [], []
    for tag in META_RE.findall(text):
        attrs = {k.lower(): html.unescape(v) for k, v in ATTR_RE.findall(tag)}
        prop = (attrs.get("property") or attrs.get("name") or "").lower()
        content = attrs.get("content", "")
        if not content:
            continue
        if prop in ("og:image", "og:image:secure_url"):
            images.append(content)
        elif prop in ("og:video", "og:video:url", "og:video:secure_url"):
            videos.append(content)
    videos += PIN_MP4_RE.findall(text)

    videos = [v for v in set(videos) if v.startswith("http") and ".mp4" in v]
    videos.sort(key=_res_score, reverse=True)
    images = list(dict.fromkeys(images))
    return {"videos": videos, "images": images}


def fetch_pinterest(url, work_dir, budget):
    errors = []
    try:
        info = pinterest_page(url, budget)
        if info["videos"]:
            path = download_first(info["videos"], os.path.join(work_dir, "pin.mp4"), budget)
            return [path], ({"local": True} if HAS_FFMPEG else None)
        if info["images"]:
            hi = [pinterest_original(u) for u in info["images"]]
            try:
                return download_many(hi, work_dir, "pin", budget), None
            except TooBigError:
                raise
            except Exception:
                return download_many(info["images"], work_dir, "pin", budget), None
        raise NoMediaError()
    except TooBigError:
        raise
    except Exception as e:
        print(f"[pinterest] الصفحة فشلت: {e}")
        errors.append(e)

    return _ytdlp_fallback(url, work_dir, budget, errors)


def fetch_media(url, platform, work_dir, budget):
    """يرجع (قائمة الملفات الأصلية, معلومات الصوت أو None)."""
    if platform == "tiktok":
        return fetch_tiktok(url, work_dir, budget)
    return fetch_pinterest(url, work_dir, budget)


# ==========================================================
#                    معالجة الفيديو (ffmpeg اختياري)
# ==========================================================
def ffprobe_duration(path):
    if not FFPROBE:
        return None
    try:
        r = subprocess.run(
            [FFPROBE, "-v", "error", "-show_entries", "format=duration",
             "-of", "default=noprint_wrappers=1:nokey=1", path],
            capture_output=True, text=True, timeout=30,
        )
        return float(r.stdout.strip())
    except Exception:
        return None


def ensure_mp4(path):
    """يرجع (المسار, هل هو mp4). بدون ffmpeg تُرسل الصيغة كما هي كملف."""
    if path.lower().endswith(".mp4"):
        return path, True
    if not HAS_FFMPEG:
        return path, False
    out = os.path.splitext(path)[0] + "_conv.mp4"
    ok = subprocess.run(
        [FFMPEG, "-y", "-i", path, "-c", "copy", "-movflags", "+faststart", out],
        capture_output=True, timeout=300,
    ).returncode == 0
    if not ok or not os.path.exists(out) or os.path.getsize(out) == 0:
        ok = subprocess.run(
            [FFMPEG, "-y", "-i", path, "-c:v", "libx264", "-preset", "veryfast", "-crf", "18",
             "-c:a", "aac", "-b:a", "192k", "-movflags", "+faststart", out],
            capture_output=True, timeout=900,
        ).returncode == 0
    if ok and os.path.exists(out):
        return out, True
    return path, False


def compress_video(src, dst):
    """يضغط الفيديو ليقع تحت الحد مع أفضل جودة ممكنة ضمنه."""
    duration = ffprobe_duration(src)
    audio_kbps = 96
    if duration and duration > 0:
        total_kbps = (MAX_BYTES * 0.95) * 8 / duration / 1000
        video_kbps = max(int(total_kbps - audio_kbps), 200)
    else:
        video_kbps = 1200
    vf = ["-vf", "scale=-2:'min(720,ih)'"] if video_kbps < 700 else []
    cmd = [
        FFMPEG, "-y", "-i", src, *vf,
        "-c:v", "libx264", "-preset", "veryfast",
        "-b:v", f"{video_kbps}k", "-maxrate", f"{int(video_kbps * 1.3)}k",
        "-bufsize", f"{video_kbps * 2}k",
        "-c:a", "aac", "-b:a", f"{audio_kbps}k",
        "-movflags", "+faststart", dst,
    ]
    r = subprocess.run(cmd, capture_output=True, timeout=900)
    if r.returncode != 0 or not os.path.exists(dst):
        raise RuntimeError("ffmpeg compression failed")
    return dst


def extract_audio_local(video_path, out_path):
    """يستخرج الصوت الأصلي من الفيديو بدون إعادة ترميز إن أمكن."""
    if not HAS_FFMPEG:
        raise NoMediaError()
    r = subprocess.run([FFMPEG, "-y", "-i", video_path, "-vn", "-c:a", "copy", out_path],
                       capture_output=True, timeout=120)
    if r.returncode != 0 or not os.path.exists(out_path):
        r = subprocess.run([FFMPEG, "-y", "-i", video_path, "-vn", "-c:a", "aac", "-b:a", "192k", out_path],
                           capture_output=True, timeout=300)
        if r.returncode != 0:
            raise NoMediaError()
    return out_path


def build_items(files):
    """يجهز الملفات للإرسال. يرجع (العناصر, هل تم ضغط شيء, هل تم تخطي شيء)."""
    items, compressed, skipped = [], False, False
    for path in files:
        kind = media_kind(path)
        size = os.path.getsize(path)

        if kind == "photo":
            if size > MAX_BYTES:
                skipped = True
                continue
            ext = os.path.splitext(path)[1].lower()
            if ext in (".jpg", ".jpeg", ".png") and size <= PHOTO_MAX_BYTES:
                items.append({"type": "photo", "path": path, "original": path})
            else:
                items.append({"type": "document", "path": path, "original": path})

        elif kind == "video":
            try:
                ready, is_mp4 = ensure_mp4(path)
                ready_size = os.path.getsize(ready)
                original = path if size <= MAX_BYTES else None
                if ready_size <= MAX_BYTES:
                    items.append({
                        "type": "video" if is_mp4 else "document",
                        "path": ready,
                        "original": original,
                    })
                elif HAS_FFMPEG:
                    small = os.path.splitext(ready)[0] + "_small.mp4"
                    compress_video(ready, small)
                    if os.path.getsize(small) > MAX_BYTES:
                        skipped = True
                        continue
                    items.append({"type": "video", "path": small, "original": None})
                    compressed = True
                else:
                    skipped = True
            except Exception as e:
                print(f"[build] تعذر تجهيز {path}: {e}")
                skipped = True
    return items, compressed, skipped


def originals_map(items):
    out = {"video": [], "photo": []}
    for item in items:
        orig = item.get("original")
        if not orig:
            continue
        kind = media_kind(orig)
        if kind in out:
            out[kind].append(orig)
    return out


def audio_usable(audio):
    return bool(audio) and ("local" not in audio or HAS_FFMPEG)


# ==========================================================
#                    الإرسال والتخزين المؤقت
# ==========================================================
MEDIA_CLASSES = {
    "video": types.InputMediaVideo,
    "photo": types.InputMediaPhoto,
    "document": types.InputMediaDocument,
}


@contextmanager
def _source(item):
    if item.get("file_id"):
        yield item["file_id"]
    else:
        with open(item["path"], "rb") as fh:
            yield fh


def extract_file_id(msg):
    if msg is None:
        return None
    if getattr(msg, "video", None):
        return {"type": "video", "file_id": msg.video.file_id}
    if getattr(msg, "photo", None):
        return {"type": "photo", "file_id": msg.photo[-1].file_id}
    if getattr(msg, "document", None):
        return {"type": "document", "file_id": msg.document.file_id}
    return None


def _send_one(chat_id, reply_to, item, caption, markup, kind):
    with _source(item) as src:
        common = dict(caption=caption, reply_markup=markup, reply_to_message_id=reply_to, parse_mode="HTML")
        if kind == "video":
            return bot.send_video(chat_id, src, supports_streaming=True, **common)
        if kind == "photo":
            return bot.send_photo(chat_id, src, **common)
        return bot.send_document(chat_id, src, **common)


def send_single(chat_id, reply_to, item, caption, markup):
    kind = item["type"]
    try:
        return _send_one(chat_id, reply_to, item, caption, markup, kind)
    except ApiTelegramException as e:
        if kind == "photo":
            return _send_one(chat_id, reply_to, item, caption, markup, "document")
        if getattr(e, "error_code", 0) == 413 or "too large" in str(e).lower():
            raise TooBigError()
        raise


def _send_album_chunk(chat_id, reply_to, chunk, caption):
    with ExitStack() as stack:
        media = []
        for idx, item in enumerate(chunk):
            src = stack.enter_context(_source(item))
            kwargs = {}
            if idx == 0 and caption:
                kwargs.update(caption=caption, parse_mode="HTML")
            if item["type"] == "video":
                kwargs["supports_streaming"] = True
            media.append(MEDIA_CLASSES[item["type"]](media=src, **kwargs))
        return bot.send_media_group(chat_id, media, reply_to_message_id=reply_to)


def send_album(chat_id, reply_to, items, caption):
    msgs = []
    for start in range(0, len(items), 10):
        chunk = items[start:start + 10]
        first = start == 0
        try:
            msgs.extend(_send_album_chunk(
                chat_id, reply_to if first else None, chunk, caption if first else None,
            ))
        except ApiTelegramException as e:
            # إذا فشل الألبوم نرسل كل عنصر منفرداً حتى لا يضيع أي ملف
            print(f"[album] فشل الألبوم، الإرسال المنفرد: {e}")
            for idx, item in enumerate(chunk):
                head = first and idx == 0
                msgs.append(send_single(
                    chat_id, reply_to if head else None, item,
                    caption if head else None, None,
                ))
    return msgs


def deliver(chat_id, reply_to, items, caption, markup):
    """يرسل العناصر ويرجع قائمة {type, file_id} للتخزين المؤقت."""
    if len(items) == 1:
        found = extract_file_id(send_single(chat_id, reply_to, items[0], caption, markup))
        return [found] if found else []

    msgs = send_album(chat_id, reply_to, items, caption)
    if markup is not None:
        bot.send_message(chat_id, CONFIG["texts"]["options"], reply_markup=markup, reply_to_message_id=reply_to)
    return [f for f in (extract_file_id(m) for m in msgs) if f]


def build_caption(compressed):
    text = CONFIG["texts"]["done"]
    if compressed:
        text += "\n\n" + CONFIG["texts"]["compressed"]
    return text


def build_markup(token_id, flags):
    kb = types.InlineKeyboardMarkup()
    if flags.get("hd"):
        kb.row(make_btn("hd", callback_data=f"hd:{token_id}"))
    if flags.get("orig"):
        kb.row(make_btn("original", callback_data=f"orig:{token_id}"))
    if flags.get("mp3"):
        kb.row(make_btn("mp3", callback_data=f"mp3:{token_id}"))
    return kb if kb.keyboard else None


def store_cache(key, sent, flags, audio, compressed):
    with _file_lock:
        rec = FILE_IDS.get(key, {})
        rec.update({"items": sent, "flags": flags, "audio": audio, "compressed": compressed})
        FILE_IDS[key] = rec
    save_file_ids()


# ==========================================================
#                    المعالجة الرئيسية للرابط
# ==========================================================
def process_link(message, platform, url):
    chat_id = message.chat.id
    reply_to = message.message_id
    key = cache_key(platform, url)
    loading = None
    work_dir = None
    budget = Budget(REQUEST_BUDGET)
    try:
        loading = bot.send_message(chat_id, CONFIG["texts"]["loading"], reply_to_message_id=reply_to)
        rec = FILE_IDS.get(key)

        if rec and rec.get("items"):
            # رابط أُرسل سابقاً: نرسله فوراً بالـ file_id بدون تنزيل
            token_id = new_token(key=key, url=url, platform=platform, dir=None,
                                 originals={}, audio=rec.get("audio"))
            deliver(chat_id, reply_to, rec["items"],
                    build_caption(rec.get("compressed")),
                    build_markup(token_id, rec.get("flags", {})))
        else:
            work_dir = tempfile.mkdtemp(dir=CACHE_DIR)
            files, audio = fetch_media(url, platform, work_dir, budget)
            items, compressed, skipped = build_items(files)
            if not items:
                raise TooBigError() if skipped else NoMediaError()

            originals = originals_map(items)
            flags = {
                "hd": bool(originals["video"]),
                "orig": bool(originals["photo"]),
                "mp3": audio_usable(audio),
            }
            token_id = new_token(key=key, url=url, platform=platform, dir=work_dir,
                                 originals=originals, audio=audio)
            sent = deliver(chat_id, reply_to, items, build_caption(compressed),
                           build_markup(token_id, flags))
            if skipped:
                bot.send_message(chat_id, CONFIG["texts"]["partial"], reply_to_message_id=reply_to)
            if sent:
                store_cache(key, sent, flags, audio, compressed)
            work_dir = None  # نُبقي المجلد لأن أزرار الجودة الأصلية تحتاجه

        bump_downloads()
    except Exception as e:
        report_error(chat_id, reply_to, e)
    finally:
        if work_dir:
            shutil.rmtree(work_dir, ignore_errors=True)
        if loading is not None:
            try:
                bot.delete_message(chat_id, loading.message_id)
            except Exception:
                pass


# ==========================================================
#                    أزرار الجودة والصوت
# ==========================================================
def send_originals(action, token, chat_id, reply_to):
    """يرسل الملفات الأصلية كملفات بدون أي معالجة. HD للفيديو، والزر الآخر للصور."""
    kind = "video" if action == "hd" else "photo"
    rec = FILE_IDS.get(token["key"], {})
    cached = (rec.get("docs") or {}).get(kind)
    if cached:
        deliver(chat_id, reply_to, [{"type": "document", "file_id": fid} for fid in cached],
                CONFIG["texts"]["done"], None)
        return

    paths = [p for p in token.get("originals", {}).get(kind, []) if os.path.exists(p)]
    tmp_dir = None
    try:
        if not paths:
            tmp_dir = tempfile.mkdtemp(dir=CACHE_DIR)
            files, _ = fetch_media(token["url"], token["platform"], tmp_dir, Budget(REQUEST_BUDGET))
            paths = [f for f in files if media_kind(f) == kind and os.path.getsize(f) <= MAX_BYTES]
        if not paths:
            raise TooBigError() if kind == "video" else NoMediaError()

        sent = deliver(chat_id, reply_to, [{"type": "document", "path": p} for p in paths],
                       CONFIG["texts"]["done"], None)
        ids = [s["file_id"] for s in sent]
        if ids:
            with _file_lock:
                rec = FILE_IDS.setdefault(token["key"], {})
                rec.setdefault("docs", {})[kind] = ids
            save_file_ids()
    finally:
        if tmp_dir:
            shutil.rmtree(tmp_dir, ignore_errors=True)


def local_video_path(token, tmp_dir):
    paths = [p for p in token.get("originals", {}).get("video", []) if os.path.exists(p)]
    if paths:
        return paths[0]
    files, _ = fetch_media(token["url"], token["platform"], tmp_dir, Budget(REQUEST_BUDGET))
    videos = [f for f in files if media_kind(f) == "video" and os.path.getsize(f) <= MAX_BYTES]
    if not videos:
        raise NoMediaError()
    return videos[0]


def send_mp3(token, chat_id, reply_to):
    key = token["key"]
    rec = FILE_IDS.get(key, {})
    if rec.get("audio_id"):
        if rec.get("audio_kind") == "document":
            bot.send_document(chat_id, rec["audio_id"], reply_to_message_id=reply_to)
        else:
            bot.send_audio(chat_id, rec["audio_id"], reply_to_message_id=reply_to)
        return

    audio = token.get("audio") or rec.get("audio")
    if not audio:
        raise NoMediaError()

    tmp_dir = tempfile.mkdtemp(dir=CACHE_DIR)
    try:
        if "direct" in audio:
            path = download_to(audio["direct"], os.path.join(tmp_dir, "audio.mp3"), Budget(30))
        elif "ytdlp" in audio:
            files = ytdlp_download(audio["ytdlp"], tmp_dir, Budget(YTDLP_BUDGET), audio_only=True)
            if not files:
                raise NoMediaError()
            path = max(files, key=os.path.getsize)
        elif "local" in audio:
            video = local_video_path(token, tmp_dir)
            path = extract_audio_local(video, os.path.join(tmp_dir, "audio.m4a"))
        else:
            raise NoMediaError()

        # يُرسل الصوت الأصلي بدون تحويل. إذا رفضه تيليجرام كـ audio نرسله كملف
        with open(path, "rb") as fh:
            try:
                msg = bot.send_audio(chat_id, fh, reply_to_message_id=reply_to)
                kind = "audio"
                file_id = getattr(getattr(msg, "audio", None), "file_id", None)
            except ApiTelegramException:
                fh.seek(0)
                msg = bot.send_document(chat_id, fh, reply_to_message_id=reply_to)
                kind = "document"
                file_id = getattr(getattr(msg, "document", None), "file_id", None)

        if file_id:
            with _file_lock:
                entry = FILE_IDS.setdefault(key, {})
                entry["audio_id"] = file_id
                entry["audio_kind"] = kind
            save_file_ids()
    finally:
        shutil.rmtree(tmp_dir, ignore_errors=True)


def run_media_action(action, token, chat_id, reply_to):
    try:
        if action == "mp3":
            send_mp3(token, chat_id, reply_to)
        else:
            send_originals(action, token, chat_id, reply_to)
    except Exception as e:
        report_error(chat_id, reply_to, e)


@bot.callback_query_handler(func=lambda call: bool(call.data) and call.data.split(":")[0] in ("hd", "orig", "mp3"))
def cb_media(call):
    chat_id = call.message.chat.id
    if not check_access(call.from_user.id, chat_id):
        bot.answer_callback_query(call.id)
        return
    action, token_id = call.data.split(":", 1)
    token = TOKENS.get(token_id)
    if not token:
        bot.answer_callback_query(call.id, CONFIG["texts"]["err_unavailable"], show_alert=True)
        return
    bot.answer_callback_query(call.id, "⏳ جاري التجهيز...")
    threading.Thread(
        target=run_media_action,
        args=(action, token, chat_id, call.message.message_id),
        daemon=True,
    ).start()


# ==========================================================
#                    أوامر المستخدمين
# ==========================================================
@bot.message_handler(commands=["start"], chat_types=["private"])
def cmd_start(message):
    register_user(message.from_user)
    if not check_access(message.from_user.id, message.chat.id):
        return
    bot.send_message(message.chat.id, CONFIG["texts"]["welcome"])


@bot.callback_query_handler(func=lambda call: call.data == "check_sub")
def cb_check_sub(call):
    ok, _ = is_subscribed(call.from_user.id)
    if not ok:
        bot.answer_callback_query(call.id, "❌ لم تشترك في جميع القنوات بعد", show_alert=True)
        return
    bot.answer_callback_query(call.id, "✅ تم التحقق، أرسل الرابط الآن")
    try:
        bot.delete_message(call.message.chat.id, call.message.message_id)
    except Exception:
        pass
    bot.send_message(call.message.chat.id, CONFIG["texts"]["welcome"])


# ==========================================================
#                    لوحة تحكم الأدمن
# ==========================================================
def admin_panel_text():
    return "🛠 <b>لوحة التحكم</b>\nاختر ما تريد إدارته:"


def admin_markup():
    kb = types.InlineKeyboardMarkup(row_width=2)
    sub = "🟢 مفعّل" if CONFIG["force_sub_enabled"] else "🔴 معطّل"
    state = "✅ نشط" if CONFIG["bot_active"] else "🛠 صيانة"

    kb.row(types.InlineKeyboardButton(f"🔒 الاشتراك الإجباري: {sub}", callback_data="adm:toggle_sub"))
    kb.row(
        types.InlineKeyboardButton("➕ إضافة قناة", callback_data="adm:add_ch"),
        types.InlineKeyboardButton("➖ حذف قناة", callback_data="adm:del_ch"),
    )
    keys = list(TEXT_LABELS.keys())
    for i in range(0, len(keys), 2):
        kb.row(*[
            types.InlineKeyboardButton(f"✏️ {TEXT_LABELS[k]}", callback_data=f"adm:edit:{k}")
            for k in keys[i:i + 2]
        ])
    kb.row(types.InlineKeyboardButton("🎨 تخصيص الأزرار", callback_data="adm:btns"))
    kb.row(
        types.InlineKeyboardButton("📊 الإحصائيات", callback_data="adm:stats"),
        types.InlineKeyboardButton("📣 الإذاعة", callback_data="adm:broadcast"),
    )
    kb.row(types.InlineKeyboardButton(f"🛠 حالة البوت: {state}", callback_data="adm:toggle_bot"))
    kb.row(types.InlineKeyboardButton("❌ إغلاق", callback_data="adm:close"))
    return kb


def buttons_menu_markup():
    kb = types.InlineKeyboardMarkup(row_width=1)
    for key, label in BUTTON_LABELS.items():
        kb.add(types.InlineKeyboardButton(f"🎨 {label}", callback_data=f"adm:bk:{key}"))
    kb.add(types.InlineKeyboardButton("🔙 رجوع", callback_data="adm:back"))
    return kb


def button_detail_text(key):
    b = CONFIG["buttons"][key]
    color = COLOR_NAMES.get(b.get("style", ""), COLOR_NAMES[""])
    icon = "✅ مضاف" if b.get("icon") else "❌ لا يوجد"
    return (
        f"🎨 <b>{BUTTON_LABELS[key]}</b>\n\n"
        f"النص الحالي: {html.escape(b.get('text', ''))}\n"
        f"اللون: {color}\n"
        f"الإيموجي: {icon}\n\n"
        "اختر ما تريد تعديله:"
    )


def button_detail_markup(key):
    kb = types.InlineKeyboardMarkup(row_width=2)
    kb.row(
        types.InlineKeyboardButton("✏️ النص", callback_data=f"adm:bt:{key}"),
        types.InlineKeyboardButton("🎨 اللون", callback_data=f"adm:bc:{key}"),
    )
    kb.row(
        types.InlineKeyboardButton("🖼 الإيموجي", callback_data=f"adm:bi:{key}"),
        types.InlineKeyboardButton("🗑 حذف الإيموجي", callback_data=f"adm:bx:{key}"),
    )
    kb.row(types.InlineKeyboardButton("🔙 رجوع", callback_data="adm:btns"))
    return kb


def color_markup(key):
    kb = types.InlineKeyboardMarkup(row_width=2)
    kb.add(*[
        types.InlineKeyboardButton(name, callback_data=f"adm:bs:{key}:{code}")
        for code, name in COLOR_NAMES.items()
    ])
    kb.add(types.InlineKeyboardButton("🔙 رجوع", callback_data=f"adm:bk:{key}"))
    return kb


def safe_edit(chat_id, message_id, text, markup):
    try:
        bot.edit_message_text(text, chat_id, message_id, reply_markup=markup)
    except Exception:
        pass


def edit_admin_panel(chat_id, message_id):
    safe_edit(chat_id, message_id, admin_panel_text(), admin_markup())


@bot.message_handler(commands=["admin"], chat_types=["private"])
def cmd_admin(message):
    if not is_admin(message.from_user.id):
        return
    bot.send_message(message.chat.id, admin_panel_text(), reply_markup=admin_markup())


@bot.message_handler(commands=["cancel"], chat_types=["private"])
def cmd_cancel(message):
    if is_admin(message.from_user.id):
        ADMIN_STATE.pop(message.from_user.id, None)
        bot.send_message(message.chat.id, "✅ تم الإلغاء.")


@bot.callback_query_handler(func=lambda call: bool(call.data) and call.data.startswith("adm:"))
def cb_admin(call):
    if not is_admin(call.from_user.id):
        bot.answer_callback_query(call.id, "⛔ غير مصرح لك", show_alert=True)
        return

    bot.answer_callback_query(call.id)
    parts = call.data.split(":")
    action = parts[1]
    chat_id = call.message.chat.id
    msg_id = call.message.message_id
    uid = call.from_user.id

    if action == "back":
        edit_admin_panel(chat_id, msg_id)

    elif action == "toggle_sub":
        with _file_lock:
            CONFIG["force_sub_enabled"] = not CONFIG["force_sub_enabled"]
            save_config()
        SUB_CACHE.clear()
        edit_admin_panel(chat_id, msg_id)

    elif action == "toggle_bot":
        with _file_lock:
            CONFIG["bot_active"] = not CONFIG["bot_active"]
            save_config()
        edit_admin_panel(chat_id, msg_id)

    elif action == "add_ch":
        ADMIN_STATE[uid] = {"action": "add_channel"}
        bot.send_message(
            chat_id,
            "➕ أرسل معرف القناة بصيغة <code>@channel</code>.\n\n"
            "⚠️ تذكير: يجب رفع البوت مشرفاً في القناة لكي يعمل التحقق من الاشتراك.\n"
            "لإلغاء العملية أرسل /cancel",
        )

    elif action == "del_ch":
        if not CONFIG["force_channels"]:
            bot.send_message(chat_id, "⚠️ لا توجد قنوات مضافة.")
            return
        kb = types.InlineKeyboardMarkup(row_width=1)
        for i, ch in enumerate(CONFIG["force_channels"]):
            kb.add(types.InlineKeyboardButton(f"🗑 {ch}", callback_data=f"adm:rm:{i}"))
        kb.add(types.InlineKeyboardButton("🔙 رجوع", callback_data="adm:back"))
        safe_edit(chat_id, msg_id, "اختر القناة التي تريد حذفها:", kb)

    elif action == "rm":
        idx = int(parts[2])
        with _file_lock:
            if 0 <= idx < len(CONFIG["force_channels"]):
                CONFIG["force_channels"].pop(idx)
                save_config()
        SUB_CACHE.clear()
        edit_admin_panel(chat_id, msg_id)

    elif action == "edit":
        key = parts[2]
        ADMIN_STATE[uid] = {"action": "edit_text", "key": key}
        bot.send_message(
            chat_id,
            f"✏️ أرسل النص الجديد لـ «{TEXT_LABELS[key]}».\n"
            "يمكنك استخدام الإيموجيات البريميوم مباشرة وسيتم حفظها تلقائياً.\n"
            "لإلغاء العملية أرسل /cancel\n\nالنص الحالي:",
        )
        bot.send_message(chat_id, CONFIG["texts"][key])

    elif action == "btns":
        safe_edit(chat_id, msg_id, "🎨 <b>تخصيص الأزرار</b>\nاختر الزر الذي تريد تعديله:", buttons_menu_markup())

    elif action == "bk":
        key = parts[2]
        safe_edit(chat_id, msg_id, button_detail_text(key), button_detail_markup(key))

    elif action == "bc":
        key = parts[2]
        safe_edit(chat_id, msg_id, f"🎨 اختر لون <b>{BUTTON_LABELS[key]}</b>:", color_markup(key))

    elif action == "bs":
        key, color = parts[2], parts[3]
        with _file_lock:
            CONFIG["buttons"][key]["style"] = color
            save_config()
        safe_edit(chat_id, msg_id, button_detail_text(key), button_detail_markup(key))

    elif action == "bt":
        key = parts[2]
        ADMIN_STATE[uid] = {"action": "btn_text", "key": key}
        bot.send_message(
            chat_id,
            f"✏️ أرسل النص الجديد لـ «{BUTTON_LABELS[key]}».\n"
            "ملاحظة: نص الزر يقبل الإيموجي العادي، أما البريميوم فيُضاف عبر «🖼 الإيموجي».\n"
            "لإلغاء العملية أرسل /cancel",
        )

    elif action == "bi":
        key = parts[2]
        ADMIN_STATE[uid] = {"action": "btn_icon", "key": key}
        bot.send_message(
            chat_id,
            f"🖼 أرسل إيموجي بريميوم ليكون أيقونة «{BUTTON_LABELS[key]}».\n"
            "لإلغاء العملية أرسل /cancel",
        )

    elif action == "bx":
        key = parts[2]
        with _file_lock:
            CONFIG["buttons"][key]["icon"] = ""
            save_config()
        safe_edit(chat_id, msg_id, button_detail_text(key), button_detail_markup(key))

    elif action == "stats":
        bot.send_message(
            chat_id,
            "📊 <b>الإحصائيات</b>\n\n"
            f"👥 عدد المستخدمين: {len(USERS)}\n"
            f"🎬 التحميلات الناجحة: {CONFIG['stats'].get('downloads', 0)}\n"
            f"🗂 الروابط المخزنة مؤقتاً: {len(FILE_IDS)}",
        )

    elif action == "broadcast":
        ADMIN_STATE[uid] = {"action": "broadcast"}
        bot.send_message(
            chat_id,
            "📣 أرسل الرسالة التي تريد إذاعتها لجميع المستخدمين (نص أو إعلان أو صورة).\n"
            "لإلغاء العملية أرسل /cancel",
        )

    elif action == "close":
        try:
            bot.delete_message(chat_id, msg_id)
        except Exception:
            pass


def run_broadcast(admin_chat, from_chat, message_id):
    ok = fail = 0
    for uid in list(USERS.keys()):
        try:
            bot.copy_message(int(uid), from_chat, message_id)
            ok += 1
        except Exception:
            fail += 1
        time.sleep(0.04)
    bot.send_message(admin_chat, f"📣 انتهت الإذاعة\n✅ نجاح: {ok}\n❌ فشل: {fail}")


def handle_admin_input(message):
    uid = message.from_user.id
    chat_id = message.chat.id
    state = ADMIN_STATE.get(uid)
    if not state:
        return
    action = state["action"]
    text = (message.text or "").strip()

    if action == "edit_text":
        ADMIN_STATE.pop(uid, None)
        new_html = entities_to_html(message.text, message.entities or [])
        with _file_lock:
            CONFIG["texts"][state["key"]] = new_html
            save_config()
        bot.send_message(chat_id, f"✅ تم حفظ نص «{TEXT_LABELS[state['key']]}». معاينة:")
        bot.send_message(chat_id, new_html)

    elif action == "add_channel":
        if not text.startswith("@") or len(text) < 2:
            bot.send_message(chat_id, "❌ صيغة غير صحيحة. أرسل المعرف بصيغة @username.")
            return
        if text in CONFIG["force_channels"]:
            ADMIN_STATE.pop(uid, None)
            bot.send_message(chat_id, "⚠️ هذه القناة مضافة مسبقاً.")
            return
        try:
            chat = bot.get_chat(text)
        except Exception:
            bot.send_message(chat_id, "❌ تعذر الوصول للقناة. تأكد أنها موجودة وأن البوت مشرف فيها.")
            return
        ADMIN_STATE.pop(uid, None)
        with _file_lock:
            CONFIG["force_channels"].append(text)
            save_config()
        SUB_CACHE.clear()
        bot.send_message(chat_id, f"✅ تمت إضافة: {html.escape(chat.title or text)}")

    elif action == "btn_text":
        if not text:
            bot.send_message(chat_id, "❌ النص فارغ، أرسل نصاً صحيحاً.")
            return
        ADMIN_STATE.pop(uid, None)
        with _file_lock:
            CONFIG["buttons"][state["key"]]["text"] = text
            save_config()
        bot.send_message(chat_id, f"✅ تم تحديث نص «{BUTTON_LABELS[state['key']]}».")

    elif action == "btn_icon":
        icon = next((e.custom_emoji_id for e in (message.entities or []) if e.type == "custom_emoji"), None)
        if not icon:
            bot.send_message(chat_id, "❌ أرسل إيموجي بريميوم تحديداً من لوحة الإيموجي في تيليجرام.")
            return
        ADMIN_STATE.pop(uid, None)
        with _file_lock:
            CONFIG["buttons"][state["key"]]["icon"] = icon
            save_config()
        bot.send_message(chat_id, f"✅ تم تعيين الإيموجي لزر «{BUTTON_LABELS[state['key']]}».")

    elif action == "broadcast":
        ADMIN_STATE.pop(uid, None)
        bot.send_message(chat_id, "⏳ بدأت الإذاعة، سأخبرك عند الانتهاء.")
        threading.Thread(
            target=run_broadcast,
            args=(chat_id, chat_id, message.message_id),
            daemon=True,
        ).start()


# ==========================================================
#                    معالج الرسائل النصية
# ==========================================================
@bot.message_handler(content_types=["text"], chat_types=["private"])
def on_text(message):
    uid = message.from_user.id
    chat_id = message.chat.id
    register_user(message.from_user)

    if is_admin(uid) and uid in ADMIN_STATE:
        handle_admin_input(message)
        return

    if not check_access(uid, chat_id):
        return

    detected = detect_platform(message.text)
    if not detected:
        bot.send_message(chat_id, CONFIG["texts"]["invalid"], reply_to_message_id=message.message_id)
        return

    platform, url = detected
    threading.Thread(target=process_link, args=(message, platform, url), daemon=True).start()


# ==========================================================
#                    تنظيف الملفات المؤقتة
# ==========================================================
def cleanup_loop():
    while True:
        time.sleep(300)
        now = time.time()
        for token_id in list(TOKENS.keys()):
            info = TOKENS.get(token_id)
            if info and now - info["created"] > TOKEN_TTL:
                TOKENS.pop(token_id, None)
                if info.get("dir"):
                    shutil.rmtree(info["dir"], ignore_errors=True)
        for name in os.listdir(CACHE_DIR):
            path = os.path.join(CACHE_DIR, name)
            try:
                if now - os.path.getmtime(path) > TOKEN_TTL * 2:
                    if os.path.isdir(path):
                        shutil.rmtree(path, ignore_errors=True)
                    else:
                        os.remove(path)
            except OSError:
                pass


# ==========================================================
#                    التشغيل
# ==========================================================
if __name__ == "__main__":
    if BOT_TOKEN.startswith("PUT_") or ADMIN_ID == 0:
        raise SystemExit("⚠️ عيّن BOT_TOKEN و ADMIN_ID في متغيرات البيئة أو في أعلى الملف.")

    if HAS_FFMPEG:
        print("✅ ffmpeg متوفر: الدمج والضغط وصوت MP3 لبنترست مفعّلة.")
    else:
        print("ℹ️ ffmpeg غير متوفر: الضغط التلقائي معطّل.")

    try:
        import yt_dlp  # noqa: F401
        print("✅ yt-dlp جاهز (احتياط لتيك توك وبنترست).")
    except ImportError:
        print("⚠️ yt-dlp غير مثبت. ثبّته بالأمر: pip3 install -U yt-dlp")

    threading.Thread(target=cleanup_loop, daemon=True).start()
    print("🚀 Bot is running...")
    bot.remove_webhook()
    bot.infinity_polling(skip_pending=True, timeout=30, long_polling_timeout=30)
