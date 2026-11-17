#!/usr/bin/env python3
"""MTProto Proxy Aggregator Bot, version 3.

What it does
  * Collects MTProto proxy links from owner-approved HTTPS sources.
  * Checks each proxy's TCP reachability. A TCP check does NOT prove that the MTProto handshake
    works, nor privacy, nor speed. The bot labels results accordingly.
  * Shows only proxies whose latest check succeeded, to users in Arabic, behind a
    mandatory-subscription gate.
  * Bootstraps to an initial target of verified working proxies, then keeps maintaining them.
  * Publishes exactly one verified proxy to the owner's channel per publishing cycle.
  * Lets the owner customize messages, button labels, button order and layout, custom buttons,
    and Telegram Premium custom emoji, all from inside the bot (/panel).

Sections
    1.  Configuration
    2.  Runtime helpers
    3.  Proxy link parsing
    4.  Network safety (public addresses, pinned connections)
    5.  Database and migrations
    6.  Repository (all SQL)
    7.  Runtime tunables
    8.  Rich text, customization store and default texts
    9.  Source collection
    10. Reachability validation
    11. Mandatory subscription
    12. Channel publishing
    13. Background jobs, bootstrap and scheduler
    14. Owner panel views
    15. User handlers
    16. Owner handlers
    17. Application wiring and entry point

Run:  python bot.py   (Python 3.11+, packages from requirements.txt)
Set BOT_TOKEN and OWNER_ID as environment variables on the host (or edit the defaults at the top of this file).
"""
from __future__ import annotations

# =============================================================================
# >>> EDIT THESE TWO VALUES <<<  (single source of truth for the whole project)
# =============================================================================
# Read from the hosting environment variables (BOT_TOKEN and OWNER_ID). The values after the comma
# are only used when the variable is not set (for example when running locally).
import os as _os

BOT_TOKEN = (_os.getenv("BOT_TOKEN", "YOUR_BOT_TOKEN").strip())
OWNER_ID = (int(_os.getenv("OWNER_ID", "123456789").strip()) if _os.getenv("OWNER_ID", "123456789").strip().isdigit() else 0)
# =============================================================================

import asyncio
import functools
import hashlib
import html
import ipaddress
import logging
import math
import os
import re
import secrets
import shutil
import socket
import sqlite3
import time
from collections import defaultdict, deque
from dataclasses import dataclass, field
from datetime import datetime, timedelta, timezone
from logging.handlers import RotatingFileHandler
from pathlib import Path
from typing import Any, Awaitable, Callable
from urllib.parse import parse_qs, urljoin, urlsplit
from zoneinfo import ZoneInfo

import aiosqlite
import httpx
from apscheduler.schedulers.asyncio import AsyncIOScheduler
from apscheduler.triggers.interval import IntervalTrigger
from dotenv import load_dotenv
from telegram import InlineKeyboardButton as _TgButton
from telegram import InlineKeyboardMarkup, LinkPreviewOptions, MessageEntity, Update
from telegram.error import BadRequest, TelegramError
from telegram.ext import (
    Application,
    CallbackQueryHandler,
    CommandHandler,
    ContextTypes,
    MessageHandler,
    filters,
)

load_dotenv()
log = logging.getLogger("proxy_bot")


# ----- Premium custom emoji on buttons ---------------------------------------------------------
# Telegram button TEXT cannot carry message entities, so a custom emoji inside a button label is
# impossible. The Bot API instead offers a separate field, InlineKeyboardButton.icon_custom_emoji_id,
# which shows one custom emoji before the label. Telegram only honours it for bots whose owner has
# Telegram Premium (or that own extra Fragment usernames) and only in private/group chats, never in
# channel posts. When Telegram rejects it, the bot falls back to the plain emoji character.
BUTTON_ICONS_ENABLED = True
_icons_off_until = 0.0  # monotonic time until which icons are skipped after Telegram rejected them


class LabelStr(str):
    """A button label that remembers the custom emoji (icon) and plain fallback character it carries."""

    icon: str | None = None
    fallback: str = ""


def with_icon(text: str, icon: str | None, fallback: str = "") -> str:
    if not icon:
        return text
    label = LabelStr(text)
    label.icon = icon
    label.fallback = fallback
    return label


def _icons_usable() -> bool:
    return BUTTON_ICONS_ENABLED and time.monotonic() >= _icons_off_until


def Button(text: str, *args: Any, **kwargs: Any) -> _TgButton:  # noqa: N802 - keeps the old call sites unchanged
    """Builds an inline button. A LabelStr with an icon becomes a real custom-emoji icon button."""
    icon = getattr(text, "icon", None)
    plain = str(text)
    if not icon:
        return _TgButton(plain, *args, **kwargs)
    if _icons_usable():
        try:
            return _TgButton(plain, *args, icon_custom_emoji_id=icon, **kwargs)
        except TypeError:  # installed python-telegram-bot predates the field: send it as a raw API field
            try:
                extra = {**kwargs.pop("api_kwargs", {}), "icon_custom_emoji_id": icon}
                return _TgButton(plain, *args, api_kwargs=extra, **kwargs)
            except TypeError:
                pass
    fallback = getattr(text, "fallback", "")
    return _TgButton(f"{fallback} {plain}".strip() if fallback else plain, *args, **kwargs)


def _button_icon(button: Any) -> str | None:
    icon = getattr(button, "icon_custom_emoji_id", None)
    if icon:
        return icon
    return (getattr(button, "api_kwargs", None) or {}).get("icon_custom_emoji_id")


def markup_has_icons(markup: Any) -> bool:
    return bool(markup) and any(_button_icon(b) for row in markup.inline_keyboard for b in row)


def markup_without_icons(markup: Any) -> Any:
    """Same keyboard with every icon replaced by its plain fallback character."""
    rows = []
    for row in markup.inline_keyboard:
        new_row = []
        for b in row:
            icon = _button_icon(b)
            text = f"{STORE.fallback_for(icon)} {b.text}".strip() if icon else b.text
            new_row.append(_TgButton(text, url=b.url, callback_data=b.callback_data))
        rows.append(new_row)
    return InlineKeyboardMarkup(rows)


# =============================================================================
# 1. Configuration
# =============================================================================

@dataclass(frozen=True)
class Settings:
    """Values read from environment variables (or a local .env file)."""

    bot_token: str
    owner_ids: frozenset[int]
    db_path: str
    log_file: str
    backup_dir: str
    backup_keep: int
    timezone: str
    channel_link: str
    target_working: int
    initial_target: int
    min_daily_working: int
    initial_sources: tuple[str, ...]
    validate_interval_min: int
    collect_interval_min: int
    publish_interval_min: int
    validate_timeout_sec: float
    validate_concurrency: int
    failure_threshold: int
    recheck_hours: int


class ConfigError(RuntimeError):
    """Raised at startup when the environment is missing or contains invalid values."""


_CHANNEL_LINK_RE = re.compile(r"^https://t\.me/(?:\+[A-Za-z0-9_-]{8,}|joinchat/[A-Za-z0-9_-]{8,}|[A-Za-z][A-Za-z0-9_]{3,})$")


def valid_channel_link(link: str) -> bool:
    """Accepts public t.me usernames and private invite links only."""
    return bool(_CHANNEL_LINK_RE.match(link.strip()))


def load_settings() -> Settings:
    """Reads every setting and reports ALL problems at once. Numbers are parsed before the check."""
    problems: list[str] = []

    def number(name: str, default: float, cast: type, lo: float, hi: float) -> Any:
        raw = os.getenv(name, "").strip()
        if not raw:
            return cast(default)
        try:
            value = cast(raw)
        except ValueError:
            problems.append(f"{name} يجب أن يكون رقماً (القيمة الحالية: {raw!r})")
            return cast(default)
        if not lo <= value <= hi:
            problems.append(f"{name} يجب أن يكون بين {lo:g} و {hi:g}")
        return value

    token = str(BOT_TOKEN).strip()
    if token == "YOUR_BOT_TOKEN" or not re.fullmatch(r"\d{5,}:[A-Za-z0-9_-]{20,}", token):
        problems.append("BOT_TOKEN غير صالح: أضفه كمتغير بيئة في الاستضافة باسم BOT_TOKEN (توكن @BotFather ويحتوي على :)")

    owners: set[int] = set()
    if isinstance(OWNER_ID, int) and not isinstance(OWNER_ID, bool) and OWNER_ID > 0 and OWNER_ID != 123456789:
        owners.add(OWNER_ID)
    else:
        problems.append("OWNER_ID غير صالح: أضفه كمتغير بيئة في الاستضافة باسم OWNER_ID (أرقام فقط)")

    tz_name = os.getenv("TIMEZONE", "UTC").strip() or "UTC"
    try:
        ZoneInfo(tz_name)
    except Exception:  # noqa: BLE001 - any failure means the zone name is unusable
        problems.append(f"TIMEZONE ليس اسم منطقة زمنية صالحاً: {tz_name!r}")

    channel = os.getenv("CHANNEL_LINK", "").strip()
    if channel and not valid_channel_link(channel):
        problems.append("CHANNEL_LINK يجب أن يكون رابطاً مثل https://t.me/channel_name")

    initial_sources = tuple(p.strip() for p in os.getenv("INITIAL_SOURCES", "").split(",") if p.strip())
    for url in initial_sources:
        reason = valid_source_syntax(url)
        if reason:
            problems.append(f"INITIAL_SOURCES يحتوي على رابط غير صالح ({reason}): {url}")

    values = dict(
        backup_keep=number("BACKUP_KEEP", 7, int, 1, 365),
        target_working=number("TARGET_WORKING", 100, int, 1, 1000),
        initial_target=number("INITIAL_TARGET", 20, int, 1, 1000),
        min_daily_working=number("MIN_DAILY_WORKING", 20, int, 0, 1000),
        validate_interval_min=number("VALIDATE_INTERVAL_MIN", 30, int, 1, 1440),
        collect_interval_min=number("COLLECT_INTERVAL_MIN", 60, int, 5, 1440),
        publish_interval_min=number("PUBLISH_INTERVAL_MIN", 10, int, 5, 1440),
        validate_timeout_sec=number("VALIDATE_TIMEOUT_SEC", 5.0, float, 1.0, 30.0),
        validate_concurrency=number("VALIDATE_CONCURRENCY", 40, int, 1, 500),
        failure_threshold=number("FAILURE_THRESHOLD", 2, int, 1, 10),
        recheck_hours=number("RECHECK_HOURS", 24, int, 1, 168),
    )

    if problems:
        raise ConfigError("\n".join(f"- {p}" for p in problems))

    return Settings(
        bot_token=token,
        owner_ids=frozenset(owners),
        db_path=os.getenv("DB_PATH", "data/proxy_bot.db").strip() or "data/proxy_bot.db",
        log_file=os.getenv("LOG_FILE", "data/bot.log").strip() or "data/bot.log",
        backup_dir=os.getenv("BACKUP_DIR", "data/backups").strip() or "data/backups",
        timezone=tz_name,
        channel_link=channel,
        initial_sources=initial_sources,
        **values,
    )


# =============================================================================
# 2. Runtime helpers
# =============================================================================

def iso(moment: datetime) -> str:
    """UTC ISO-8601 text. It sorts correctly as a string, which the SQL comparisons rely on."""
    return moment.astimezone(timezone.utc).isoformat(timespec="seconds")


def now_iso() -> str:
    return iso(datetime.now(timezone.utc))


def parse_iso(stamp: str | None) -> datetime | None:
    if not stamp:
        return None
    try:
        return datetime.fromisoformat(stamp)
    except (TypeError, ValueError):
        return None


def elapsed_since(stamp: str | None) -> timedelta | None:
    moment = parse_iso(stamp)
    return None if moment is None else datetime.now(timezone.utc) - moment


def day_start_iso(tz_name: str) -> str:
    local = datetime.now(ZoneInfo(tz_name))
    return iso(local.replace(hour=0, minute=0, second=0, microsecond=0))


def fmt_time(value: str | None, tz_name: str) -> str:
    moment = parse_iso(value)
    if moment is None:
        return "لم يتم بعد"
    return moment.astimezone(ZoneInfo(tz_name)).strftime("%Y-%m-%d %H:%M")


def chat_key(value: str) -> int | str:
    """Numeric chat IDs are sent as integers; @usernames stay as strings."""
    text = str(value).strip()
    return int(text) if text.lstrip("-").isdigit() else text


def utf16_len(text: str) -> int:
    """Telegram measures entity offsets and lengths in UTF-16 code units, not characters."""
    return len(text.encode("utf-16-le")) // 2


class TTLCache:
    """Small in-memory cache for values that may be a few seconds stale."""

    MAX_ENTRIES = 5_000

    def __init__(self) -> None:
        self._items: dict[str, tuple[float, Any]] = {}

    async def get_or_load(self, key: str, ttl: float, loader: Callable[[], Awaitable[Any]]) -> Any:
        now = time.monotonic()
        hit = self._items.get(key)
        if hit is not None and now - hit[0] < ttl:
            return hit[1]
        value = await loader()
        if len(self._items) >= self.MAX_ENTRIES:
            self._items.clear()
        self._items[key] = (now, value)
        return value

    def clear(self) -> None:
        self._items.clear()


class Metrics:
    """Rolling response-time samples, so the owner sees measured values only."""

    def __init__(self, window: int = 300) -> None:
        self._samples: dict[str, deque[float]] = defaultdict(lambda: deque(maxlen=window))

    def record(self, name: str, ms: float) -> None:
        self._samples[name].append(ms)

    def summary(self, name: str) -> dict[str, float]:
        data = sorted(self._samples.get(name, ()))
        if not data:
            return {"count": 0, "avg": 0.0, "p95": 0.0}
        p95 = data[min(len(data) - 1, int(len(data) * 0.95))]
        return {"count": len(data), "avg": sum(data) / len(data), "p95": p95}


def timed(name: str, slow_ms: float = 500.0):
    """Records a handler's wall-clock time and logs any call slower than slow_ms."""

    def decorator(handler):
        @functools.wraps(handler)
        async def wrapper(update, context, *args, **kwargs):
            started = time.perf_counter()
            try:
                return await handler(update, context, *args, **kwargs)
            finally:
                elapsed = (time.perf_counter() - started) * 1000.0
                svc = context.application.bot_data.get("svc")
                if svc is not None:
                    svc.metrics.record(name, elapsed)
                if elapsed > slow_ms:
                    log.warning("slow handler %s took %.0f ms", name, elapsed)

        return wrapper

    return decorator


BUSY = object()  # returned by JobGuard when the same job is already running


class JobGuard:
    """Ensures a named job never runs twice at once. A second trigger gets BUSY, not a silent skip."""

    def __init__(self) -> None:
        self._locks: dict[str, asyncio.Lock] = {}

    def is_running(self, name: str) -> bool:
        lock = self._locks.get(name)
        return bool(lock and lock.locked())

    async def run(self, name: str, factory: Callable[[], Awaitable[Any]]) -> Any:
        lock = self._locks.setdefault(name, asyncio.Lock())
        if lock.locked():
            return BUSY
        async with lock:
            return await factory()


def _log_task_failure(task: asyncio.Task) -> None:
    """Every background task reports its exception. Nothing fails silently."""
    if task.cancelled():
        return
    exc = task.exception()
    if exc is not None:
        log.error("background task failed: %s", exc, exc_info=exc)


@dataclass
class Services:
    """Everything handlers and jobs share. Created once in on_startup."""

    settings: Settings
    db: "Database"
    repo: "Repository"
    http: httpx.AsyncClient
    bot: Any = None
    bot_username: str = ""
    cache: TTLCache = field(default_factory=TTLCache)
    metrics: Metrics = field(default_factory=Metrics)
    guard: JobGuard = field(default_factory=JobGuard)
    owner_lock: asyncio.Lock = field(default_factory=asyncio.Lock)
    member_cache: dict = field(default_factory=dict)  # unused: membership is never cached (kept for compatibility)
    owner_premium: bool | None = None  # last seen is_premium flag of an owner account
    scheduler: Any = None
    jobs: Any = None
    background: set = field(default_factory=set)

    def spawn(self, coro: Any) -> None:
        """Runs a coroutine in the background. Its exception, if any, is logged."""
        task = asyncio.create_task(coro)
        self.background.add(task)
        task.add_done_callback(self.background.discard)
        task.add_done_callback(_log_task_failure)


# =============================================================================
# 3. Proxy link parsing
# =============================================================================

_LINK_RE = re.compile(r"(?:tg://proxy|https?://t\.me/proxy)\?[^\s\"'<>)\]]+", re.IGNORECASE)
_SECRET_RE = re.compile(r"^(?:[0-9a-f]{32}|dd[0-9a-f]{32}|ee[0-9a-f]{32}[0-9a-f]*)$")
_DOMAIN_RE = re.compile(r"^(?:[a-z0-9](?:[a-z0-9-]{0,61}[a-z0-9])?\.)+[a-z]{2,63}$")


@dataclass(frozen=True, slots=True)
class ProxyRecord:
    host: str
    port: int
    secret: str

    @property
    def key(self) -> tuple[str, int, str]:
        return (self.host, self.port, self.secret)

    @property
    def deep_link(self) -> str:
        return f"tg://proxy?server={self.host}&port={self.port}&secret={self.secret}"


def parse_link(raw: str) -> ProxyRecord | None:
    """Returns a normalised ProxyRecord, or None when the link is malformed or unsafe."""
    try:
        query = parse_qs(urlsplit(raw.strip()).query)
    except ValueError:
        return None
    host = query.get("server", [""])[0].strip().lower()
    port_text = query.get("port", [""])[0].strip()
    secret = query.get("secret", [""])[0].strip().lower()
    if not port_text.isdigit() or not 1 <= int(port_text) <= 65535:
        return None
    if not _SECRET_RE.match(secret):
        return None
    if not (_DOMAIN_RE.match(host) or _is_ip_literal(host)):
        return None
    if not _host_is_public_literal(host):
        return None
    return ProxyRecord(host, int(port_text), secret)


def extract_proxies(text: str) -> list[ProxyRecord]:
    """Finds every proxy link in a block of text and returns each unique proxy once."""
    seen: set[tuple[str, int, str]] = set()
    unique: list[ProxyRecord] = []
    for match in _LINK_RE.findall(html.unescape(text)):
        record = parse_link(match)
        if record is not None and record.key not in seen:
            seen.add(record.key)
            unique.append(record)
    return unique


# =============================================================================
# 4. Network safety (public addresses, pinned connections)
# =============================================================================

class UnsafeTarget(Exception):
    """A host resolves to a private, loopback, link-local, reserved or otherwise non-public address."""


def _is_ip_literal(host: str) -> bool:
    try:
        ipaddress.ip_address(host.split("%")[0])
    except ValueError:
        return False
    return True


def _ip_is_public(address: Any) -> bool:
    if isinstance(address, ipaddress.IPv6Address) and address.ipv4_mapped is not None:
        address = address.ipv4_mapped
    return bool(address.is_global) and not address.is_multicast


def _host_is_public_literal(host: str) -> bool:
    """For IP literals only. Domain names are checked by resolution, not here."""
    try:
        address = ipaddress.ip_address(host.split("%")[0])
    except ValueError:
        return True
    return _ip_is_public(address)


async def resolve_public_ips(host: str) -> list[str]:
    """Returns every address for host, IPv4 first. Raises UnsafeTarget if ANY address is not public."""
    if _is_ip_literal(host):
        address = ipaddress.ip_address(host.split("%")[0])
        if not _ip_is_public(address):
            raise UnsafeTarget(host)
        return [str(address)]
    infos = await asyncio.get_running_loop().getaddrinfo(host, 443, type=socket.SOCK_STREAM)
    addresses = {ipaddress.ip_address(info[4][0].split("%")[0]) for info in infos}
    if not addresses:
        raise socket.gaierror(f"no address for {host}")
    if not all(_ip_is_public(a) for a in addresses):
        raise UnsafeTarget(host)
    return [str(a) for a in sorted(addresses, key=lambda a: a.version)]


async def resolve_public_ip(host: str) -> str:
    return (await resolve_public_ips(host))[0]


def pinned_target(url: str, ip: str) -> tuple[str, str, str]:
    """Builds a request that connects to a VALIDATED IP address.

    Returns (request_url, host_header, sni_hostname). The connection goes to the IP we checked,
    so DNS cannot change its answer in between (no DNS rebinding). The TLS certificate is still
    verified against the real host name, which is sent as SNI and as the Host header.
    """
    parts = urlsplit(url)
    host = parts.hostname or ""
    path = parts.path or "/"
    if parts.query:
        path += "?" + parts.query
    netloc_ip = f"[{ip}]" if ":" in ip else ip
    return f"https://{netloc_ip}{path}", host, host


# =============================================================================
# 5. Database and migrations
# =============================================================================

BASE_SCHEMA = """
CREATE TABLE IF NOT EXISTS sources (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    name TEXT NOT NULL,
    url TEXT NOT NULL UNIQUE,
    enabled INTEGER NOT NULL DEFAULT 1,
    created_at TEXT NOT NULL,
    last_fetch_at TEXT,
    last_status TEXT,
    last_found INTEGER NOT NULL DEFAULT 0,
    success_count INTEGER NOT NULL DEFAULT 0,
    failure_count INTEGER NOT NULL DEFAULT 0,
    total_found INTEGER NOT NULL DEFAULT 0
);

CREATE TABLE IF NOT EXISTS proxies (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    host TEXT NOT NULL,
    port INTEGER NOT NULL,
    secret TEXT NOT NULL,
    source_id INTEGER REFERENCES sources(id) ON DELETE SET NULL,
    discovered_at TEXT NOT NULL,
    status TEXT NOT NULL DEFAULT 'pending',
    enabled INTEGER NOT NULL DEFAULT 1,
    consecutive_failures INTEGER NOT NULL DEFAULT 0,
    last_checked_at TEXT,
    last_ok_at TEXT,
    last_latency_ms REAL,
    hidden_at TEXT,
    UNIQUE (host, port, secret)
);
CREATE INDEX IF NOT EXISTS idx_proxies_visible ON proxies (enabled, status, last_ok_at, last_latency_ms);
CREATE INDEX IF NOT EXISTS idx_proxies_discovered ON proxies (discovered_at);
CREATE INDEX IF NOT EXISTS idx_proxies_check_queue ON proxies (enabled, status, last_checked_at);

CREATE TABLE IF NOT EXISTS checks (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    proxy_id INTEGER NOT NULL REFERENCES proxies(id) ON DELETE CASCADE,
    checked_at TEXT NOT NULL,
    ok INTEGER NOT NULL,
    latency_ms REAL,
    error TEXT
);
CREATE INDEX IF NOT EXISTS idx_checks_time ON checks (checked_at);
CREATE INDEX IF NOT EXISTS idx_checks_proxy ON checks (proxy_id, id);

CREATE TABLE IF NOT EXISTS source_links (
    source_id INTEGER NOT NULL REFERENCES sources(id) ON DELETE CASCADE,
    proxy_id INTEGER NOT NULL REFERENCES proxies(id) ON DELETE CASCADE,
    seen_at TEXT NOT NULL,
    PRIMARY KEY (source_id, proxy_id)
);
CREATE INDEX IF NOT EXISTS idx_source_links_proxy ON source_links (proxy_id);

CREATE TABLE IF NOT EXISTS required_channels (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    chat_ref TEXT NOT NULL UNIQUE,
    title TEXT NOT NULL,
    join_url TEXT NOT NULL,
    enabled INTEGER NOT NULL DEFAULT 1,
    position INTEGER NOT NULL DEFAULT 0
);

CREATE TABLE IF NOT EXISTS users (
    user_id INTEGER PRIMARY KEY,
    first_seen TEXT NOT NULL,
    last_seen TEXT NOT NULL
);
CREATE INDEX IF NOT EXISTS idx_users_last_seen ON users (last_seen);

CREATE TABLE IF NOT EXISTS settings (
    key TEXT PRIMARY KEY,
    value TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS events (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    created_at TEXT NOT NULL,
    level TEXT NOT NULL,
    component TEXT NOT NULL,
    message TEXT NOT NULL
);
CREATE INDEX IF NOT EXISTS idx_events_time ON events (created_at);

CREATE TABLE IF NOT EXISTS publish_log (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    created_at TEXT NOT NULL,
    channel TEXT,
    message_id INTEGER,
    outcome TEXT NOT NULL,
    detail TEXT
);
CREATE INDEX IF NOT EXISTS idx_publish_log_time ON publish_log (created_at);

CREATE TABLE IF NOT EXISTS emojis (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    custom_emoji_id TEXT NOT NULL UNIQUE,
    fallback TEXT NOT NULL,
    created_at TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS custom_buttons (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    label TEXT NOT NULL,
    body TEXT NOT NULL,
    created_at TEXT NOT NULL
);
"""

# Columns added to tables created by older versions. Each is added only when missing, so existing
# data is never deleted and the migration is safe to run on every start.
MIGRATION_COLUMNS: dict[str, dict[str, str]] = {
    "sources": {
        "last_ok_at": "TEXT",
        "last_error": "TEXT",
        "etag": "TEXT",
        "last_modified": "TEXT",
        "content_hash": "TEXT",
    },
    "proxies": {
        "last_failure_at": "TEXT",
        "last_error": "TEXT",
        "success_count": "INTEGER NOT NULL DEFAULT 0",
        "first_ok_at": "TEXT",
        "last_published_at": "TEXT",
        "publish_count": "INTEGER NOT NULL DEFAULT 0",
    },
    "users": {"blocked": "INTEGER NOT NULL DEFAULT 0"},
    "publish_log": {"proxy_id": "INTEGER"},
}
SCHEMA_VERSION = 3
REQUIRED_TABLES = {"proxies", "sources", "settings", "users", "events"}


class Database:
    """One shared SQLite connection in WAL mode. Writes are serialised with an asyncio lock."""

    def __init__(self, path: str, slow_query_ms: float = 100.0) -> None:
        self.path = path
        self.slow_query_ms = slow_query_ms
        self.slow_queries = 0
        self._conn: aiosqlite.Connection | None = None
        self._read_conn: aiosqlite.Connection | None = None  # WAL lets reads run while a write is in progress
        self._write_lock = asyncio.Lock()

    async def connect(self) -> None:
        Path(self.path).parent.mkdir(parents=True, exist_ok=True)
        self._conn = await aiosqlite.connect(self.path, timeout=15)
        self._conn.row_factory = aiosqlite.Row
        await self._conn.execute("PRAGMA journal_mode=WAL")
        await self._conn.execute("PRAGMA foreign_keys=ON")
        await self._conn.execute("PRAGMA synchronous=NORMAL")
        await self._conn.execute("PRAGMA busy_timeout=15000")
        await self._conn.execute("PRAGMA temp_store=MEMORY")
        await self._conn.execute("PRAGMA cache_size=-32768")
        await self._migrate()
        # A second, read-only connection: reads never queue behind a long write transaction.
        self._read_conn = await aiosqlite.connect(self.path, timeout=15)
        self._read_conn.row_factory = aiosqlite.Row
        await self._read_conn.execute("PRAGMA busy_timeout=15000")
        await self._read_conn.execute("PRAGMA cache_size=-32768")
        await self._read_conn.execute("PRAGMA temp_store=MEMORY")
        await self._read_conn.execute("PRAGMA query_only=ON")

    async def _migrate(self) -> None:
        conn = self._require()
        await conn.executescript(BASE_SCHEMA)
        for table, columns in MIGRATION_COLUMNS.items():
            cursor = await conn.execute(f"PRAGMA table_info({table})")
            existing = {row[1] for row in await cursor.fetchall()}
            await cursor.close()
            for name, declaration in columns.items():
                if name not in existing:
                    await conn.execute(f"ALTER TABLE {table} ADD COLUMN {name} {declaration}")
        await conn.execute("CREATE INDEX IF NOT EXISTS idx_proxies_first_ok ON proxies (first_ok_at)")
        await conn.execute("CREATE INDEX IF NOT EXISTS idx_proxies_published ON proxies (last_published_at)")
        # Back-fill data that v2 did not record: the first successful check, and which sources listed each proxy.
        await conn.execute(
            "UPDATE proxies SET first_ok_at = last_ok_at WHERE first_ok_at IS NULL AND last_ok_at IS NOT NULL"
        )
        await conn.execute(
            "INSERT OR IGNORE INTO source_links (source_id, proxy_id, seen_at) "
            "SELECT source_id, id, discovered_at FROM proxies WHERE source_id IS NOT NULL"
        )
        await conn.execute(f"PRAGMA user_version = {SCHEMA_VERSION}")
        await conn.commit()

    async def close(self) -> None:
        if self._read_conn is not None:
            await self._read_conn.close()
            self._read_conn = None
        if self._conn is not None:
            await self._conn.close()
            self._conn = None

    def _require(self) -> aiosqlite.Connection:
        if self._conn is None:
            raise RuntimeError("Database is not connected")
        return self._conn

    def _track(self, sql: str, started: float) -> None:
        elapsed = (time.perf_counter() - started) * 1000.0
        if elapsed > self.slow_query_ms:
            self.slow_queries += 1
            log.warning("slow query (%.0f ms): %s", elapsed, sql.strip().splitlines()[0][:120])

    async def fetchall(self, sql: str, params: tuple | list = ()) -> list[dict[str, Any]]:
        started = time.perf_counter()
        args = params if isinstance(params, dict) else tuple(params)
        cursor = await (self._read_conn or self._require()).execute(sql, args)
        try:
            rows = await cursor.fetchall()
        finally:
            await cursor.close()
        self._track(sql, started)
        return [dict(row) for row in rows]

    async def fetchone(self, sql: str, params: tuple | list = ()) -> dict[str, Any] | None:
        rows = await self.fetchall(sql, params)
        return rows[0] if rows else None

    async def execute(self, sql: str, params: tuple | list = ()) -> int:
        """Runs one write in its own transaction and returns the number of affected rows."""
        conn = self._require()
        async with self._write_lock:
            try:
                cursor = await conn.execute(sql, tuple(params))
                rowcount = cursor.rowcount
                await cursor.close()
                await conn.commit()
            except Exception:
                await conn.rollback()
                raise
        return max(rowcount, 0)

    async def write_batch(self, ops: list[tuple[str, tuple | list]]) -> list[int]:
        """Runs many writes in one transaction. Either all of them apply or none do.

        Returns the affected-row count of each statement, in order."""
        conn = self._require()
        counts: list[int] = []
        async with self._write_lock:
            try:
                for sql, params in ops:
                    cursor = await conn.execute(sql, tuple(params))
                    counts.append(max(cursor.rowcount, 0))
                    await cursor.close()
                await conn.commit()
            except Exception:
                await conn.rollback()
                raise
        return counts

    async def backup_to(self, target: str) -> None:
        """Consistent online copy using SQLite's backup API, run in a thread so the loop stays free."""

        def run() -> None:
            src = sqlite3.connect(self.path, timeout=30)
            try:
                dst = sqlite3.connect(target)
                try:
                    src.backup(dst)
                finally:
                    dst.close()
            finally:
                src.close()

        await asyncio.to_thread(run)


def check_backup_file(path: str) -> str:
    """Returns '' when the file is a usable bot database, otherwise the reason in Arabic."""
    try:
        con = sqlite3.connect(f"file:{path}?mode=ro", uri=True)
    except sqlite3.Error:
        return "الملف ليس قاعدة بيانات صالحة"
    try:
        integrity = con.execute("PRAGMA integrity_check").fetchone()[0]
        tables = {row[0] for row in con.execute("SELECT name FROM sqlite_master WHERE type = 'table'")}
    except sqlite3.DatabaseError:
        return "تعذّر فحص الملف"
    finally:
        con.close()
    if integrity != "ok":
        return "الملف تالف"
    missing = REQUIRED_TABLES - tables
    return f"جداول ناقصة: {', '.join(sorted(missing))}" if missing else ""


def apply_staged_restore(db_path: str) -> str:
    """Runs before the database is opened. Swaps in a restore file the owner uploaded earlier.

    The current database is kept next to it as '<name>.pre-restore-<time>', so nothing is lost.
    Returns a short message for the log, or '' when nothing was staged.
    """
    staged = db_path + ".restore"
    if not os.path.exists(staged):
        return ""
    problem = check_backup_file(staged)
    if problem:
        os.remove(staged)
        return f"تم تجاهل ملف الاستعادة: {problem}"
    if os.path.exists(db_path):
        stamp = datetime.now(timezone.utc).strftime("%Y%m%d-%H%M%S")
        keep = sqlite3.connect(db_path)
        try:
            copy = sqlite3.connect(f"{db_path}.pre-restore-{stamp}")
            try:
                keep.backup(copy)
            finally:
                copy.close()
        finally:
            keep.close()
    for suffix in ("-wal", "-shm"):
        Path(db_path + suffix).unlink(missing_ok=True)
    os.replace(staged, db_path)
    return "تمت استعادة قاعدة البيانات من الملف الذي رفعه المالك"


# =============================================================================
# 6. Repository (all SQL)
# =============================================================================

# A proxy is shown to users only when its LATEST check succeeded. A proxy that failed its latest
# check is not presented as working, even while it has not yet reached the hiding threshold.
VISIBLE = "enabled = 1 AND status = 'working' AND last_ok_at IS NOT NULL"


class Repository:
    """Every SQL statement the bot runs. Other code calls these methods instead of writing SQL."""

    def __init__(self, db: Database) -> None:
        self.db = db
        self._channels: list[dict[str, Any]] | None = None  # required-channel CONFIG only, never membership
        self._channels_ver = 0

    # ----- settings and events -----

    async def get_setting(self, key: str, default: str | None = None) -> str | None:
        row = await self.db.fetchone("SELECT value FROM settings WHERE key = ?", (key,))
        return row["value"] if row else default

    async def set_setting(self, key: str, value: Any) -> None:
        await self.db.execute(
            "INSERT INTO settings (key, value) VALUES (?, ?) "
            "ON CONFLICT(key) DO UPDATE SET value = excluded.value",
            (key, str(value)),
        )

    async def delete_setting(self, key: str) -> None:
        await self.db.execute("DELETE FROM settings WHERE key = ?", (key,))

    async def settings_with_prefix(self, prefix: str) -> dict[str, str]:
        rows = await self.db.fetchall(
            "SELECT key, value FROM settings WHERE key >= ? AND key < ?", (prefix, prefix + "\uffff")
        )
        return {row["key"]: row["value"] for row in rows}

    async def settings_all(self) -> dict[str, str]:
        rows = await self.db.fetchall("SELECT key, value FROM settings")
        return {row["key"]: row["value"] for row in rows}

    async def claim_slot(self, slot: str) -> bool:
        """Atomically records that a publishing slot is used. Returns False if it was already used."""
        await self.db.execute("INSERT OR IGNORE INTO settings (key, value) VALUES ('publish_slot', '')")
        changed = await self.db.execute(
            "UPDATE settings SET value = ? WHERE key = 'publish_slot' AND value <> ?", (slot, slot)
        )
        return changed == 1

    async def add_event(self, level: str, component: str, message: str) -> None:
        await self.db.execute(
            "INSERT INTO events (created_at, level, component, message) VALUES (?, ?, ?, ?)",
            (now_iso(), level, component, message[:500]),
        )

    async def recent_events(self, limit: int = 15) -> list[dict[str, Any]]:
        return await self.db.fetchall("SELECT * FROM events ORDER BY id DESC LIMIT ?", (limit,))

    async def count_events(self, level: str, since: str) -> int:
        row = await self.db.fetchone(
            "SELECT COUNT(*) AS n FROM events WHERE level = ? AND created_at >= ?", (level, since)
        )
        return int(row["n"]) if row else 0

    async def events_mentioning(self, component: str, text: str, limit: int = 5) -> list[dict[str, Any]]:
        return await self.db.fetchall(
            "SELECT * FROM events WHERE component = ? AND message LIKE ? ORDER BY id DESC LIMIT ?",
            (component, f"%{text}%", limit),
        )

    async def log_publish(self, outcome: str, channel: str | None, message_id: int | None,
                          proxy_id: int | None, detail: str = "") -> None:
        await self.db.execute(
            "INSERT INTO publish_log (created_at, channel, message_id, outcome, detail, proxy_id) "
            "VALUES (?, ?, ?, ?, ?, ?)",
            (now_iso(), channel, message_id, outcome, detail[:300], proxy_id),
        )

    async def recent_publish_log(self, limit: int = 10) -> list[dict[str, Any]]:
        return await self.db.fetchall("SELECT * FROM publish_log ORDER BY id DESC LIMIT ?", (limit,))

    async def prune(self, checks_before: str, events_before: str, publish_before: str) -> None:
        await self.db.execute("DELETE FROM checks WHERE checked_at < ?", (checks_before,))
        await self.db.execute("DELETE FROM events WHERE created_at < ?", (events_before,))
        await self.db.execute("DELETE FROM publish_log WHERE created_at < ?", (publish_before,))

    # ----- users -----

    async def touch_user(self, user_id: int) -> None:
        ts = now_iso()
        await self.db.execute(
            "INSERT INTO users (user_id, first_seen, last_seen) VALUES (?, ?, ?) "
            "ON CONFLICT(user_id) DO UPDATE SET last_seen = excluded.last_seen",
            (user_id, ts, ts),
        )

    async def is_blocked(self, user_id: int) -> bool:
        row = await self.db.fetchone("SELECT blocked FROM users WHERE user_id = ?", (user_id,))
        return bool(row and row["blocked"])

    async def user_counts(self, day_start: str, day_ago: str) -> dict[str, int]:
        row = await self.db.fetchone(
            """SELECT COUNT(*) AS total,
                   COALESCE(SUM(CASE WHEN last_seen >= ? THEN 1 ELSE 0 END), 0) AS active,
                   COALESCE(SUM(CASE WHEN first_seen >= ? THEN 1 ELSE 0 END), 0) AS new_today,
                   COALESCE(SUM(blocked), 0) AS blocked
               FROM users""",
            (day_ago, day_start),
        )
        return row or {"total": 0, "active": 0, "new_today": 0, "blocked": 0}

    async def get_user(self, user_id: int) -> dict[str, Any] | None:
        return await self.db.fetchone("SELECT * FROM users WHERE user_id = ?", (user_id,))

    async def set_blocked(self, user_id: int, blocked: bool) -> bool:
        return await self.db.execute(
            "UPDATE users SET blocked = ? WHERE user_id = ?", (1 if blocked else 0, user_id)
        ) > 0

    async def list_blocked(self, limit: int = 20) -> list[dict[str, Any]]:
        return await self.db.fetchall(
            "SELECT user_id, last_seen FROM users WHERE blocked = 1 ORDER BY last_seen DESC LIMIT ?", (limit,)
        )

    # ----- sources -----

    async def list_sources(self) -> list[dict[str, Any]]:
        return await self.db.fetchall("SELECT * FROM sources ORDER BY id")

    async def enabled_sources(self) -> list[dict[str, Any]]:
        return await self.db.fetchall("SELECT * FROM sources WHERE enabled = 1 ORDER BY id")

    async def get_source(self, source_id: int) -> dict[str, Any] | None:
        return await self.db.fetchone("SELECT * FROM sources WHERE id = ?", (source_id,))

    async def source_counts(self) -> dict[str, int]:
        row = await self.db.fetchone(
            "SELECT COUNT(*) AS total, COALESCE(SUM(enabled), 0) AS active FROM sources"
        )
        return row or {"total": 0, "active": 0}

    async def add_source(self, name: str, url: str) -> int | None:
        """Returns the new source id, or None when the URL already exists."""
        try:
            await self.db.execute(
                "INSERT INTO sources (name, url, enabled, created_at) VALUES (?, ?, 1, ?)",
                (name, url, now_iso()),
            )
        except sqlite3.IntegrityError:
            return None
        row = await self.db.fetchone("SELECT id FROM sources WHERE url = ?", (url,))
        return int(row["id"]) if row else None

    async def update_source(self, source_id: int, name: str, url: str) -> bool:
        """Changes a source's name and URL. Returns False when the URL belongs to another source."""
        try:
            await self.db.execute("UPDATE sources SET name = ?, url = ? WHERE id = ?", (name, url, source_id))
        except sqlite3.IntegrityError:
            return False
        return True

    async def toggle_source(self, source_id: int) -> None:
        await self.db.execute("UPDATE sources SET enabled = 1 - enabled WHERE id = ?", (source_id,))

    async def delete_source(self, source_id: int) -> None:
        await self.db.execute("DELETE FROM sources WHERE id = ?", (source_id,))

    async def source_stats(self, source_id: int) -> dict[str, int]:
        """Statistics that mean what they say.

        listed: proxies this source listed (whether or not it was the first to list them).
        first_found: proxies this source was the FIRST to list.
        working_now: proxies this source listed that are working right now.
        verified_24h: proxies this source listed that first passed verification in the last 24 hours.
        """
        since = iso(datetime.now(timezone.utc) - timedelta(hours=24))
        row = await self.db.fetchone(
            """SELECT
                   (SELECT COUNT(*) FROM source_links WHERE source_id = :s) AS listed,
                   (SELECT COUNT(*) FROM proxies WHERE source_id = :s) AS first_found,
                   (SELECT COUNT(*) FROM source_links l JOIN proxies p ON p.id = l.proxy_id
                        WHERE l.source_id = :s AND p.enabled = 1 AND p.status = 'working') AS working_now,
                   (SELECT COUNT(*) FROM source_links l JOIN proxies p ON p.id = l.proxy_id
                        WHERE l.source_id = :s AND p.first_ok_at >= :since) AS verified_24h""",
            {"s": source_id, "since": since},
        )
        return row or {"listed": 0, "first_found": 0, "working_now": 0, "verified_24h": 0}

    async def record_source_result(
        self,
        source_id: int,
        status: str,
        found: int,
        error: str | None = None,
        etag: str | None = None,
        last_modified: str | None = None,
        content_hash: str | None = None,
    ) -> None:
        """status is 'ok', 'unchanged' or 'error'. Conditional-request headers are kept for the next fetch."""
        ok = status != "error"
        ts = now_iso()
        await self.db.execute(
            """UPDATE sources SET last_fetch_at = ?, last_status = ?, last_found = ?, last_error = ?,
                   last_ok_at = COALESCE(?, last_ok_at),
                   success_count = success_count + ?, failure_count = failure_count + ?,
                   total_found = total_found + ?,
                   etag = COALESCE(?, etag), last_modified = COALESCE(?, last_modified),
                   content_hash = COALESCE(?, content_hash)
               WHERE id = ?""",
            (
                ts, status if ok else (error or "error"), found, None if ok else error,
                ts if ok else None,
                1 if ok else 0, 0 if ok else 1,
                found if status == "ok" else 0,
                etag, last_modified, content_hash,
                source_id,
            ),
        )

    # ----- proxies -----

    async def insert_proxies(self, records: list[ProxyRecord], source_id: int) -> int:
        """Inserts new proxies and records that this source listed every one of them.

        Returns how many proxies were new. UNIQUE(host, port, secret) makes duplicates a no-op."""
        if not records:
            return 0
        ts = now_iso()
        added = await self.db.write_batch([
            (
                "INSERT OR IGNORE INTO proxies (host, port, secret, source_id, discovered_at) "
                "VALUES (?, ?, ?, ?, ?)",
                (r.host, r.port, r.secret, source_id, ts),
            )
            for r in records
        ])
        await self.db.write_batch([
            (
                "INSERT OR IGNORE INTO source_links (source_id, proxy_id, seen_at) "
                "SELECT ?, id, ? FROM proxies WHERE host = ? AND port = ? AND secret = ?",
                (source_id, ts, r.host, r.port, r.secret),
            )
            for r in records
        ])
        return sum(added)

    async def count_visible(self) -> int:
        row = await self.db.fetchone(f"SELECT COUNT(*) AS n FROM proxies WHERE {VISIBLE}")
        return int(row["n"]) if row else 0

    async def visible_page(self, mode: str, offset: int, limit: int) -> list[dict[str, Any]]:
        order = (
            "last_ok_at DESC, last_latency_ms ASC, id ASC" if mode == "all" else "first_ok_at DESC, id DESC"
        )
        return await self.db.fetchall(
            f"SELECT id, host, port, secret, status, last_ok_at, first_ok_at FROM proxies "
            f"WHERE {VISIBLE} ORDER BY {order} LIMIT ? OFFSET ?",
            (limit, offset),
        )

    async def count_working(self) -> int:
        row = await self.db.fetchone(
            "SELECT COUNT(*) AS n FROM proxies WHERE enabled = 1 AND status = 'working' AND last_ok_at IS NOT NULL"
        )
        return int(row["n"]) if row else 0

    async def verified_since(self, since: str) -> int:
        """Proxies that passed verification for the first time at or after `since`."""
        row = await self.db.fetchone(
            "SELECT COUNT(*) AS n FROM proxies WHERE first_ok_at >= ?", (since,)
        )
        return int(row["n"]) if row else 0

    async def proxy_counts(self, day_start: str) -> dict[str, int]:
        row = await self.db.fetchone(
            """SELECT COUNT(*) AS total,
                   COALESCE(SUM(CASE WHEN enabled = 1 AND status = 'working' THEN 1 ELSE 0 END), 0) AS working,
                   COALESCE(SUM(CASE WHEN enabled = 1 AND status = 'failing' THEN 1 ELSE 0 END), 0) AS failing,
                   COALESCE(SUM(CASE WHEN enabled = 1 AND status = 'hidden' THEN 1 ELSE 0 END), 0) AS hidden,
                   COALESCE(SUM(CASE WHEN enabled = 0 THEN 1 ELSE 0 END), 0) AS disabled,
                   COALESCE(SUM(CASE WHEN discovered_at >= ? THEN 1 ELSE 0 END), 0) AS added_today
               FROM proxies""",
            (day_start,),
        )
        return row or {"total": 0, "working": 0, "failing": 0, "hidden": 0, "disabled": 0, "added_today": 0}

    async def checks_since(self, since: str) -> int:
        row = await self.db.fetchone("SELECT COUNT(*) AS n FROM checks WHERE checked_at >= ?", (since,))
        return int(row["n"]) if row else 0

    async def get_proxy(self, proxy_id: int) -> dict[str, Any] | None:
        return await self.db.fetchone(
            "SELECT p.*, COALESCE(s.name, '-') AS source_name FROM proxies p "
            "LEFT JOIN sources s ON s.id = p.source_id WHERE p.id = ?",
            (proxy_id,),
        )

    async def proxy_sources(self, proxy_id: int) -> list[str]:
        rows = await self.db.fetchall(
            "SELECT s.name FROM source_links l JOIN sources s ON s.id = l.source_id "
            "WHERE l.proxy_id = ? ORDER BY s.id",
            (proxy_id,),
        )
        return [row["name"] for row in rows]

    async def browse_proxies(self, offset: int, limit: int) -> list[dict[str, Any]]:
        return await self.db.fetchall(
            "SELECT id, host, port, status, enabled FROM proxies ORDER BY id DESC LIMIT ? OFFSET ?",
            (limit, offset),
        )

    async def count_all_proxies(self) -> int:
        row = await self.db.fetchone("SELECT COUNT(*) AS n FROM proxies")
        return int(row["n"]) if row else 0

    async def search_proxies(self, text: str, limit: int = 10) -> list[dict[str, Any]]:
        cleaned = re.sub(r"[%_]", "", text.strip().lower())[:200]
        columns = "id, host, port, status, enabled FROM proxies"
        if cleaned.isdigit():
            return await self.db.fetchall(f"SELECT {columns} WHERE id = ?", (int(cleaned),))
        return await self.db.fetchall(
            f"SELECT {columns} WHERE host LIKE ? ORDER BY id DESC LIMIT ?", (f"%{cleaned}%", limit)
        )

    async def inactive_proxies(self, limit: int = 10) -> list[dict[str, Any]]:
        return await self.db.fetchall(
            "SELECT id, host, port, status, enabled, hidden_at FROM proxies "
            "WHERE enabled = 0 OR status = 'hidden' "
            "ORDER BY COALESCE(hidden_at, discovered_at) DESC LIMIT ?",
            (limit,),
        )

    async def proxy_checks(self, proxy_id: int, limit: int = 5) -> list[dict[str, Any]]:
        return await self.db.fetchall(
            "SELECT checked_at, ok, latency_ms, error FROM checks WHERE proxy_id = ? ORDER BY id DESC LIMIT ?",
            (proxy_id, limit),
        )

    async def toggle_proxy(self, proxy_id: int) -> None:
        """Disabling keeps history and records when. Re-enabling puts the proxy back in the check queue."""
        await self.db.execute(
            """UPDATE proxies SET
                   enabled = CASE WHEN enabled = 1 THEN 0 ELSE 1 END,
                   hidden_at = CASE WHEN enabled = 1 THEN ? ELSE NULL END,
                   status = CASE WHEN enabled = 1 THEN status ELSE 'pending' END,
                   consecutive_failures = CASE WHEN enabled = 1 THEN consecutive_failures ELSE 0 END
               WHERE id = ?""",
            (now_iso(), proxy_id),
        )

    async def delete_proxy(self, proxy_id: int) -> None:
        await self.db.execute("DELETE FROM proxies WHERE id = ?", (proxy_id,))

    async def proxies_to_check(self, recheck_before: str) -> list[dict[str, Any]]:
        """Every enabled proxy that is not hidden, plus hidden ones not checked since recheck_before."""
        return await self.db.fetchall(
            """SELECT id, host, port, status, consecutive_failures, hidden_at FROM proxies
               WHERE enabled = 1
                 AND (status != 'hidden' OR last_checked_at IS NULL OR last_checked_at < ?)""",
            (recheck_before,),
        )

    async def apply_check_results(self, results: list[dict[str, Any]], threshold: int) -> None:
        """Stores every check and updates proxy state in one transaction.

        One failure marks a proxy 'failing' (not shown as working). Reaching the threshold of
        consecutive failures hides it. A success restores it to 'working'.
        """
        ts = now_iso()
        ops: list[tuple[str, tuple]] = []
        for r in results:
            ops.append((
                "INSERT INTO checks (proxy_id, checked_at, ok, latency_ms, error) VALUES (?, ?, ?, ?, ?)",
                (r["id"], ts, 1 if r["ok"] else 0, r["latency_ms"], r["error"]),
            ))
            if r["ok"]:
                ops.append((
                    "UPDATE proxies SET status = 'working', consecutive_failures = 0, last_checked_at = ?, "
                    "last_ok_at = ?, first_ok_at = COALESCE(first_ok_at, ?), last_latency_ms = ?, "
                    "hidden_at = NULL, success_count = success_count + 1, last_error = NULL WHERE id = ?",
                    (ts, ts, ts, r["latency_ms"], r["id"]),
                ))
            else:
                failures = int(r["consecutive_failures"] or 0) + 1
                hidden = failures >= threshold
                hidden_at = r["hidden_at"] or (ts if hidden else None)
                ops.append((
                    "UPDATE proxies SET status = ?, consecutive_failures = ?, last_checked_at = ?, "
                    "hidden_at = ?, last_failure_at = ?, last_error = ? WHERE id = ?",
                    ("hidden" if hidden else "failing", failures, ts, hidden_at, ts, r["error"], r["id"]),
                ))
        if ops:
            await self.db.write_batch(ops)

    async def pick_publish_candidate(self) -> dict[str, Any] | None:
        """The verified working proxy that was published least recently (never-published first)."""
        return await self.db.fetchone(
            f"SELECT id, host, port, secret, last_ok_at, last_latency_ms FROM proxies WHERE {VISIBLE} "
            "ORDER BY (last_published_at IS NOT NULL), last_published_at ASC, last_latency_ms ASC, id ASC LIMIT 1"
        )

    async def mark_published(self, proxy_id: int) -> None:
        await self.db.execute(
            "UPDATE proxies SET last_published_at = ?, publish_count = publish_count + 1 WHERE id = ?",
            (now_iso(), proxy_id),
        )

    # ----- required channels -----

    async def list_channels(self) -> list[dict[str, Any]]:
        return await self.db.fetchall("SELECT * FROM required_channels ORDER BY position, id")

    def _drop_channels(self) -> None:
        self._channels_ver += 1
        self._channels = None

    async def enabled_channels(self) -> list[dict[str, Any]]:
        """The configured required channels. Only the list is cached (it changes only through the
        methods below, which drop the cache); who is a member is always asked from Telegram."""
        cached = self._channels
        if cached is None:
            version = self._channels_ver
            cached = await self.db.fetchall(
                "SELECT * FROM required_channels WHERE enabled = 1 ORDER BY position, id"
            )
            if version == self._channels_ver:
                self._channels = cached
        return list(cached)

    async def add_channel(self, chat_ref: str, title: str, join_url: str) -> bool:
        self._drop_channels()
        try:
            await self.db.execute(
                "INSERT INTO required_channels (chat_ref, title, join_url, enabled) VALUES (?, ?, ?, 1)",
                (chat_ref, title, join_url),
            )
        except sqlite3.IntegrityError:
            return False
        finally:
            self._drop_channels()
        return True

    async def toggle_channel(self, channel_id: int) -> None:
        self._drop_channels()
        try:
            await self.db.execute(
                "UPDATE required_channels SET enabled = 1 - enabled WHERE id = ?", (channel_id,)
            )
        finally:
            self._drop_channels()

    async def delete_channel(self, channel_id: int) -> None:
        self._drop_channels()
        try:
            await self.db.execute("DELETE FROM required_channels WHERE id = ?", (channel_id,))
        finally:
            self._drop_channels()

    # ----- Premium custom emoji library -----

    async def save_emoji(self, custom_emoji_id: str, fallback: str) -> int:
        """Stores a custom emoji once and returns its library id (re-sending the same emoji reuses it)."""
        await self.db.execute(
            "INSERT OR IGNORE INTO emojis (custom_emoji_id, fallback, created_at) VALUES (?, ?, ?)",
            (custom_emoji_id, fallback[:8] or "⭐", now_iso()),
        )
        row = await self.db.fetchone("SELECT id FROM emojis WHERE custom_emoji_id = ?", (custom_emoji_id,))
        return int(row["id"])

    async def list_emojis(self) -> list[dict[str, Any]]:
        return await self.db.fetchall("SELECT * FROM emojis ORDER BY id")

    async def delete_emoji(self, emoji_id: int) -> None:
        await self.db.execute("DELETE FROM emojis WHERE id = ?", (emoji_id,))

    # ----- custom buttons -----

    async def list_custom_buttons(self) -> list[dict[str, Any]]:
        return await self.db.fetchall("SELECT * FROM custom_buttons ORDER BY id")

    async def add_custom_button(self, label: str, body: str) -> int:
        await self.db.execute(
            "INSERT INTO custom_buttons (label, body, created_at) VALUES (?, ?, ?)", (label, body, now_iso())
        )
        row = await self.db.fetchone("SELECT MAX(id) AS id FROM custom_buttons")
        return int(row["id"])

    async def update_custom_button(self, button_id: int, *, label: str | None = None, body: str | None = None) -> None:
        if label is not None:
            await self.db.execute("UPDATE custom_buttons SET label = ? WHERE id = ?", (label, button_id))
        if body is not None:
            await self.db.execute("UPDATE custom_buttons SET body = ? WHERE id = ?", (body, button_id))

    async def delete_custom_button(self, button_id: int) -> None:
        await self.db.execute("DELETE FROM custom_buttons WHERE id = ?", (button_id,))


# =============================================================================
# 7. Runtime tunables
# =============================================================================

# Values the owner can change from the panel. Each one falls back to its environment value.
TUNABLES: dict[str, dict[str, Any]] = {
    "validate_interval_min": {"label": "فترة الفحص (بالدقائق)", "cast": int, "lo": 1, "hi": 1440},
    "collect_interval_min": {"label": "فترة الجمع (بالدقائق)", "cast": int, "lo": 5, "hi": 1440},
    "publish_interval_min": {"label": "فترة النشر (بالدقائق)", "cast": int, "lo": 5, "hi": 1440},
    "validate_timeout_sec": {"label": "مهلة الاتصال (بالثواني)", "cast": float, "lo": 1, "hi": 30},
    "validate_concurrency": {"label": "عدد الفحوص المتزامنة", "cast": int, "lo": 1, "hi": 500},
    "failure_threshold": {"label": "عدد الإخفاقات المتتالية قبل الإخفاء", "cast": int, "lo": 1, "hi": 10},
    "recheck_hours": {"label": "فترة إعادة فحص المخفية (بالساعات)", "cast": int, "lo": 1, "hi": 168},
    "target_working": {"label": "الهدف العام (عدد البروكسيات العاملة)", "cast": int, "lo": 1, "hi": 1000},
    "min_daily_working": {"label": "الهدف اليومي (بروكسيات جديدة تم التحقق منها خلال 24 ساعة)",
                          "cast": int, "lo": 0, "hi": 1000},
    "initial_target": {"label": "هدف التهيئة الأولية (عدد البروكسيات العاملة)", "cast": int, "lo": 1, "hi": 1000},
}


async def tune(svc: Services, key: str) -> Any:
    """Owner's saved value if it is valid, otherwise the environment value."""
    spec = TUNABLES[key]
    raw = await svc.repo.get_setting(f"cfg:{key}")
    if raw is not None:
        try:
            value = spec["cast"](raw)
            if spec["lo"] <= value <= spec["hi"]:
                return value
        except ValueError:
            pass
    return spec["cast"](getattr(svc.settings, key))


def parse_tunable(key: str, text: str) -> Any | None:
    """Returns the number if it is valid for this setting, otherwise None."""
    spec = TUNABLES[key]
    try:
        value = spec["cast"](text.strip())
    except ValueError:
        return None
    return value if spec["lo"] <= value <= spec["hi"] else None


# =============================================================================
# 8. Rich text, customization store and default texts
# =============================================================================
# Every message and button label the owner can edit lives here with its default. Messages are
# stored as text with simple tags (<b>, <i>, <code>), slot tokens ([[ok]]) and emoji tokens
# ([[e12]]). They are converted to plain text plus Telegram entities, so no parse mode is needed
# and user-supplied text cannot break formatting.

DEFAULT_WELCOME = (
    "أهلاً بك في بوت بروكسيات MTProto [[wave]]\n\n"
    "نجمع البروكسيات العامة ونفحصها باستمرار، ونعرض لك الفعّال منها فقط.\n\n"
    "[[warn]] البروكسيات العامة تديرها جهات خارجية، ولا يمكن ضمان الخصوصية أو الأمان عند استخدامها."
)
DEFAULT_FOOTER = "[[channel]] قناة رابعيون"
PROXY_WARNING = "[[warn]] البروكسيات العامة تديرها جهات خارجية، ولا يمكن ضمان الخصوصية."

DEFAULT_TEXTS: dict[str, str] = {
    "welcome": DEFAULT_WELCOME,
    "footer": DEFAULT_FOOTER,
    "proxy_warning": PROXY_WARNING,
    "list_title_all": "[[list]] البروكسيات العاملة",
    "list_title_new": "[[new]] أحدث البروكسيات الناجحة",
    "list_page": "الصفحة {page} من {pages}",
    "proxy_item": "[[item]] بروكسي MTProto رقم {id}\nالحالة: {status}\nآخر فحص ناجح: {last_ok}{discovered}",
    "proxy_discovered": "\nتاريخ الاكتشاف: {disc_time}",
    "list_footer": "ملاحظة: الفحص يتحقق من إمكانية الوصول إلى المنفذ فقط، ولا يقيس سرعة التحميل.\n{warning}",
    "no_proxies": (
        "لا توجد بروكسيات عاملة مؤكدة حالياً. يجري البحث عن بروكسيات جديدة تلقائياً، يرجى المحاولة لاحقاً."
    ),
    "status_text": (
        "[[stats]] <b>حالة الخدمة</b>\n\n"
        "[[ok]] البروكسيات العاملة حالياً: {working} من الهدف {target}\n"
        "[[stats]] عمليات الفحص اليوم: {checked_today}\n"
        "[[star]] تم التحقق من {verified_24h} بروكسي جديد خلال 24 ساعة (الهدف اليومي: {daily_goal})\n"
        "[[clock]] آخر فحص للبروكسيات: {last_check}\n\n"
        "الفحص يتحقق من إمكانية الوصول إلى المنفذ، ولا يضمن أن البروكسي يعمل بنسبة 100%."
    ),
    "channel_text": "[[channel]] قناتنا: رابعيون",
    "channel_post": (
        "[[proxy]] <b>بروكسي MTProto عامل</b>\n\n"
        "بروكسي رقم {id}\n"
        "[[clock]] آخر فحص ناجح: {last_ok}\n\n"
        "{warning}\n\n"
        "{footer}"
    ),
    "sub_prompt": "[[lock]] للوصول إلى الخدمة، يرجى الاشتراك في جميع القنوات التالية، ثم اضغط «تحقق من الاشتراك».",
    "sub_still_missing": "لم تكتمل الاشتراكات بعد. يرجى الاشتراك في القنوات المتبقية ثم التحقق مجدداً.",
    "sub_ok": "[[ok]] تم التحقق من اشتراكك، أهلاً بك!",
    "sub_unverifiable": "[[warn]] تعذّر التحقق من الاشتراك في: {names}. يرجى المحاولة لاحقاً.",
    "blocked": "[[block]] تم تقييد وصولك إلى هذا البوت.",
    "error_generic": "[[warn]] حدث خطأ مؤقت، يرجى المحاولة مرة أخرى.",
    "msg_saved": "[[ok]] تم الحفظ.",
    "msg_cancelled": "تم الإلغاء.",
    "msg_invalid": "[[warn]] القيمة غير صالحة. تحقق من المطلوب وأعد الإرسال.",
    "msg_not_found": "[[warn]] لم يعد هذا العنصر موجوداً.",
    "msg_busy": "[[wait]] هذه المهمة تعمل الآن بالفعل، انتظر انتهاءها ثم أعد المحاولة.",
    "msg_started": "[[go]] بدأت المهمة في الخلفية. تابع النتيجة في لوحة المعلومات أو السجل.",
    "msg_confirm_delete": "هل أنت متأكد من الحذف؟\nلا يمكن التراجع عن هذا الإجراء.",
    "msg_confirm_block": "هل أنت متأكد من حظر المستخدم {id}؟",
    "alert_sources_failed": "⚠️ فشلت جميع مصادر الجمع في آخر دورة. راجع المصادر من لوحة التحكم.",
    "alert_daily_short": "⚠️ تم التحقق من {count} بروكسي جديد خلال 24 ساعة، والهدف اليومي {goal}.",
    "alert_bootstrap_done": "✅ اكتملت التهيئة الأولية: {count} بروكسي عامل تم التحقق منه (الهدف {target}).",
    "alert_bootstrap_short": (
        "⚠️ انتهت التهيئة الأولية بنقص: تم التحقق من {count} بروكسي عامل فقط من أصل {target}. "
        "أضف مصادر موثوقة أو راجع المصادر الحالية."
    ),
    "alert_no_sources": (
        "⚠️ لا توجد مصادر جمع مفعّلة. أضف مصادر HTTPS موثوقة من لوحة التحكم "
        "(📡 مصادر الجمع ← ➕ إضافة مصدر) ليبدأ الجمع."
    ),
}

TEXT_TITLES: dict[str, str] = {
    "welcome": "رسالة الترحيب",
    "footer": "تذييل القناة",
    "proxy_warning": "تحذير البروكسيات العامة",
    "list_title_all": "عنوان قائمة البروكسيات",
    "list_title_new": "عنوان قائمة أحدث البروكسيات",
    "list_page": "سطر رقم الصفحة",
    "proxy_item": "رسالة كل بروكسي (داخل القائمة)",
    "proxy_discovered": "سطر تاريخ الاكتشاف",
    "list_footer": "ذيل قائمة البروكسيات",
    "no_proxies": "رسالة عدم وجود بروكسيات",
    "status_text": "رسالة حالة الخدمة",
    "channel_text": "رسالة زر قناتنا",
    "channel_post": "منشور البروكسي في القناة",
    "sub_prompt": "رسالة الاشتراك الإجباري",
    "sub_still_missing": "رسالة الاشتراك الناقص",
    "sub_ok": "رسالة نجاح التحقق من الاشتراك",
    "sub_unverifiable": "رسالة تعذّر التحقق من الاشتراك",
    "blocked": "رسالة الحظر",
    "error_generic": "رسالة الخطأ العام",
    "msg_saved": "رسالة الحفظ",
    "msg_cancelled": "رسالة الإلغاء",
    "msg_invalid": "رسالة القيمة غير الصالحة",
    "msg_not_found": "رسالة العنصر غير الموجود",
    "msg_busy": "رسالة المهمة الجارية",
    "msg_started": "رسالة بدء المهمة",
    "msg_confirm_delete": "رسالة تأكيد الحذف",
    "msg_confirm_block": "رسالة تأكيد الحظر",
    "alert_sources_failed": "تنبيه فشل المصادر (للمالك)",
    "alert_daily_short": "تنبيه الهدف اليومي (للمالك)",
    "alert_bootstrap_done": "تنبيه اكتمال التهيئة (للمالك)",
    "alert_bootstrap_short": "تنبيه نقص التهيئة (للمالك)",
    "alert_no_sources": "تنبيه عدم وجود مصادر (للمالك)",
}

DEFAULT_LABELS: dict[str, str] = {
    # user-facing buttons
    "menu_all": "البروكسيات",
    "menu_new": "أحدث البروكسيات",
    "menu_status": "حالة الخدمة",
    "menu_channel": "قناتنا",
    "btn_prev": "⬅️ السابق",
    "btn_next": "التالي ➡️",
    "btn_home": "🏠 القائمة الرئيسية",
    "btn_refresh": "🔄 تحديث",
    "btn_check_sub": "تحقق من الاشتراك",
    "btn_join": "➕ اشترك في {title}",
    "btn_joined": "✅ {title}",
    "btn_connect": "🔗 اتصال بالبروكسي رقم {id}",
    "btn_more": "🤖 المزيد من البروكسيات",
    "btn_open_channel": "📢 فتح القناة",
    # owner panel buttons
    "o_dash": "📊 لوحة المعلومات",
    "o_proxies": "🛠 إدارة البروكسيات",
    "o_sources": "📡 مصادر الجمع",
    "o_validation": "⚙️ إعدادات الفحص",
    "o_publishing": "📤 إدارة النشر",
    "o_subscription": "🔒 الاشتراك الإجباري",
    "o_users": "👥 المستخدمون",
    "o_logs": "🧾 السجل والأخطاء",
    "o_system": "🔧 إعدادات النظام",
    "o_ui": "🎨 تخصيص الواجهة",
    "o_back": "↩️ رجوع",
    "o_check": "🔄 فحص الآن",
    "o_collect": "🔄 جمع الآن",
    "o_publish_now": "🚀 نشر بروكسي الآن",
    "o_pub_toggle": "⏯ تشغيل / إيقاف النشر التلقائي",
    "o_pub_preview": "👀 معاينة البروكسي التالي",
    "o_pub_history": "🧾 سجل النشر والأخطاء",
    "o_add_source": "➕ إضافة مصدر",
    "o_edit_source": "✏️ تعديل الاسم والرابط",
    "o_test_source": "🧪 اختبار المصدر",
    "o_add_channel": "➕ إضافة قناة",
    "o_check_channels": "🔍 فحص القنوات وصلاحيات البوت",
    "o_search": "🔍 بحث برقم أو عنوان",
    "o_browse": "📋 تصفح البروكسيات",
    "o_inactive": "⛔ المخفية والمعطّلة",
    "o_recheck": "🔄 فحص هذا البروكسي",
    "o_toggle": "⏯ تفعيل / تعطيل",
    "o_delete": "🗑 حذف",
    "o_block": "⛔ حظر المستخدم",
    "o_unblock": "✅ رفع الحظر",
    "o_find_user": "🔎 بحث عن مستخدم بالمعرّف",
    "o_blocked_list": "⛔ عرض المحظورين",
    "o_backup": "💾 نسخة احتياطية",
    "o_restore": "♻️ استعادة من نسخة",
    "o_bootstrap": "🚀 إعادة التهيئة الأولية",
    "o_messages": "💬 تخصيص الرسائل",
    "o_buttons": "🔘 أزرار المستخدمين",
    "o_owner_buttons": "🛠 أزرار لوحة المالك",
    "o_emoji": "🎭 الإيموجي المميزة",
    "o_edit": "✏️ تعديل",
    "o_preview": "👀 معاينة",
    "o_restore_default": "♻️ استعادة الافتراضي",
    "o_apply": "✅ تطبيق",
    "o_cancel": "❌ إلغاء",
    "o_confirm": "✅ نعم، نفّذ",
    "o_up": "⬆️",
    "o_down": "⬇️",
    "o_show_hide": "👁 إظهار / إخفاء",
    "o_rename": "✏️ الاسم",
    "o_add_button": "➕ إضافة زر مخصص",
    "o_layout": "📐 عدد الأعمدة: {cols}",
    "o_assign": "🎯 تعيين",
    "o_clear": "🚫 إزالة التعيين",
    "o_add_content": "✏️ المحتوى",
    "o_sub_toggle": "⏯ تشغيل / إيقاف الاشتراك الإجباري",
    "o_cfg_validate_interval_min": "✏️ فترة الفحص",
    "o_cfg_collect_interval_min": "✏️ فترة الجمع",
    "o_cfg_validate_timeout_sec": "✏️ مهلة الاتصال",
    "o_cfg_validate_concurrency": "✏️ الفحوص المتزامنة",
    "o_cfg_failure_threshold": "✏️ عدد الإخفاقات",
    "o_cfg_recheck_hours": "✏️ إعادة فحص المخفية",
    "o_cfg_target_working": "🎯 الهدف العام",
    "o_cfg_min_daily_working": "📅 الهدف اليومي",
    "o_cfg_initial_target": "🚀 هدف التهيئة",
    "o_cfg_publish_interval_min": "✏️ فترة النشر",
    "o_pub_channel": "📢 تحديد القناة",
    "o_refresh": "🔄 تحديث",
    "o_ui_channel": "🔗 رابط زر قناتنا",
}

# Visual slots a Premium custom emoji can be assigned to, with the plain emoji used when none is set.
DEFAULT_SLOTS: dict[str, str] = {
    "star": "⭐", "ok": "✅", "warn": "⚠️", "link": "🔗", "clock": "🕒",
    "stats": "📊", "lock": "🔒", "proxy": "🛰", "bell": "🔔", "user": "👤",
    "wave": "👋", "list": "📡", "new": "🆕", "item": "🔹", "channel": "📢",
    "block": "⛔", "wait": "⏳", "go": "▶️",
}
SLOT_TITLES: dict[str, str] = {
    "star": "نجمة", "ok": "علامة صح", "warn": "تحذير", "link": "رابط", "clock": "وقت",
    "stats": "إحصائيات", "lock": "قفل / اشتراك", "proxy": "بروكسي", "bell": "تنبيه", "user": "مستخدم",
    "wave": "ترحيب", "list": "قائمة البروكسيات", "new": "الأحدث", "item": "عنصر بروكسي", "channel": "القناة",
    "block": "حظر", "wait": "انتظار", "go": "بدء المهمة",
}
TAG_TYPES = {"b": "bold", "i": "italic", "code": "code"}
_LEAD_ICON_RE = re.compile(r"^\[\[e(\d+)\]\]\s*")
_INLINE_TOKEN_RE = re.compile(r"\[\[([^\[\]\n]{1,40})\]\]")
_TOKEN_RE = re.compile(r"(\[\[[^\[\]\n]{1,40}\]\]|\{[a-z_]{1,24}\}|</?(?:b|i|code)>)")


class SafeDict(dict):
    """Lets label templates use {names} safely: a missing name is kept as written, never raises."""

    def __missing__(self, key: str) -> str:
        return "{" + key + "}"


class Ref:
    """A variable whose value is another message template, so it can carry its own formatting."""

    __slots__ = ("key",)

    def __init__(self, key: str) -> None:
        self.key = key


@dataclass
class Rendered:
    text: str
    entities: list[dict[str, Any]]


class UIStore:
    """In-memory copy of every owner customization.

    It is loaded once at startup and reloaded after every owner change, so rendering a message or
    keyboard reads memory and never the database.
    """

    def __init__(self, default_channel_link: str) -> None:
        self.default_channel_link = default_channel_link
        self.settings: dict[str, str] = {}
        self.emojis: dict[int, tuple[str, str]] = {}   # library id -> (custom_emoji_id, fallback char)
        self._fallback_by_cid: dict[str, str] = {}     # custom_emoji_id -> fallback char
        self.slots: dict[str, int] = {}                # slot name -> library id
        self.custom: list[dict[str, Any]] = []          # custom buttons

    async def reload(self, repo: Repository) -> None:
        self.settings = await repo.settings_all()
        self.emojis = {int(r["id"]): (r["custom_emoji_id"], r["fallback"]) for r in await repo.list_emojis()}
        self._fallback_by_cid = {cid: char for cid, char in self.emojis.values()}
        self.custom = await repo.list_custom_buttons()
        self.slots = {}
        for name in DEFAULT_SLOTS:
            raw = self.settings.get(f"slot:{name}", "")
            if raw.isdigit() and int(raw) in self.emojis:
                self.slots[name] = int(raw)

    def text(self, key: str) -> str:
        return self.settings.get(f"tpl:{key}") or DEFAULT_TEXTS[key]

    def has_custom_text(self, key: str) -> bool:
        return bool(self.settings.get(f"tpl:{key}"))

    def fallback_for(self, custom_emoji_id: str | None) -> str:
        return self._fallback_by_cid.get(custom_emoji_id or "", "")

    def parse_label(self, raw: str, **values: Any) -> str:
        """Turns a stored label into button text. A leading [[e<id>]] becomes the button's custom-emoji
        icon; any other token is replaced by its plain character (button text cannot hold entities)."""
        icon: str | None = None
        fallback = ""
        match = _LEAD_ICON_RE.match(raw)
        if match:
            row = self.emojis.get(int(match.group(1)))
            if row:
                icon, fallback = row
            raw = raw[match.end():]
        raw = _INLINE_TOKEN_RE.sub(lambda m: (self.emoji_for(m.group(1))[1] or m.group(0)), raw)
        text = raw.format_map(SafeDict({k: str(v) for k, v in values.items()}))
        return with_icon(text, icon, fallback)

    def label(self, key: str, **values: Any) -> str:
        return self.parse_label(self.settings.get(f"btn:{key}") or DEFAULT_LABELS[key], **values)

    @property
    def channel_link(self) -> str:
        return self.settings.get("channel_link") or self.default_channel_link

    def cols(self) -> int:
        return 1 if self.settings.get("layout_cols") == "1" else 2

    def emoji_for(self, name: str) -> tuple[str | None, str | None]:
        """Returns (custom_emoji_id, character) for a token name, or (None, None) when unknown."""
        if name.startswith("e") and name[1:].isdigit():
            row = self.emojis.get(int(name[1:]))
            return row if row else (None, "⭐")
        if name in DEFAULT_SLOTS:
            ref = self.slots.get(name)
            if ref:
                return self.emojis[ref]
            return None, DEFAULT_SLOTS[name]
        return None, None


STORE = UIStore("")  # replaced at startup with the environment's channel link


def render_template(template: str, variables: dict[str, Any] | None = None, depth: int = 0) -> Rendered:
    """Turns a stored message into plain text plus Telegram entities."""
    variables = variables or {}
    out: list[str] = []
    entities: list[dict[str, Any]] = []
    state = {"off": 0}
    stack: list[tuple[str, int]] = []

    def emit(piece: str) -> None:
        out.append(piece)
        state["off"] += utf16_len(piece)

    def close(tag: str) -> None:
        for idx in range(len(stack) - 1, -1, -1):
            if stack[idx][0] == tag:
                _, start = stack.pop(idx)
                length = state["off"] - start
                if length > 0:
                    entities.append({"type": TAG_TYPES[tag], "offset": start, "length": length})
                return

    for part in _TOKEN_RE.split(template):
        if not part:
            continue
        if part.startswith("[[") and part.endswith("]]"):
            name = part[2:-2].strip()
            custom_id, char = STORE.emoji_for(name)
            if char is None:
                emit(part)  # unknown slot names stay visible, so the owner can spot the typo
                continue
            start = state["off"]
            emit(char)
            if custom_id:
                entities.append({"type": "custom_emoji", "offset": start,
                                 "length": utf16_len(char), "custom_emoji_id": custom_id})
        elif part.startswith("{") and part.endswith("}") and part[1:-1] in variables:
            value = variables[part[1:-1]]
            if isinstance(value, Ref):
                if depth < 3:
                    nested = render_template(STORE.text(value.key), variables, depth + 1)
                    base = state["off"]
                    out.append(nested.text)
                    state["off"] += utf16_len(nested.text)
                    entities.extend({**e, "offset": e["offset"] + base} for e in nested.entities)
            else:
                emit(str(value))
        elif part in ("<b>", "<i>", "<code>"):
            stack.append((part[1:-1], state["off"]))
        elif part in ("</b>", "</i>", "</code>"):
            close(part[2:-1])
        else:
            emit(part)
    while stack:
        close(stack[-1][0])
    return Rendered("".join(out), [e for e in entities if e["length"] > 0])


def tg_entities(entities: list[dict[str, Any]]) -> list[MessageEntity] | None:
    if not entities:
        return None
    return [
        MessageEntity(type=e["type"], offset=e["offset"], length=e["length"],
                      custom_emoji_id=e.get("custom_emoji_id"))
        for e in entities
    ]


def rich_text(key: str, variables: dict[str, Any] | None = None) -> Rendered:
    return render_template(STORE.text(key), variables)


def msg(key: str, **variables: Any) -> str:
    """A plain-text message (alerts, short replies). Formatting tags are removed and values filled in."""
    return render_template(STORE.text(key), variables).text


alert_text = msg


def concat_rendered(items: list[str | Rendered], sep: str = "\n\n") -> Rendered:
    """Joins texts (plain or rich) into one message. Entity offsets are recalculated in UTF-16 units."""
    pieces: list[str] = []
    entities: list[dict[str, Any]] = []
    offset = 0
    for index, item in enumerate(items):
        rendered = item if isinstance(item, Rendered) else Rendered(item, [])
        if index and sep:
            pieces.append(sep)
            offset += utf16_len(sep)
        pieces.append(rendered.text)
        entities.extend({**e, "offset": e["offset"] + offset} for e in rendered.entities)
        offset += utf16_len(rendered.text)
    return Rendered("".join(pieces), entities)


def with_prefix(prefix: str | Rendered, content: str | Rendered) -> str | Rendered:
    """Puts text in front of a message while keeping its formatting and entity offsets correct."""
    if isinstance(prefix, Rendered):
        return concat_rendered([prefix, content], sep="")
    if isinstance(content, Rendered):
        shift = utf16_len(prefix)
        return Rendered(prefix + content.text, [{**e, "offset": e["offset"] + shift} for e in content.entities])
    return prefix + content


async def tokenize_custom_emojis(repo: Repository, text: str, entities: list | None) -> str:
    """Replaces each Premium custom emoji in an owner's message with a stored token, [[e<id>]].

    Telegram offsets count UTF-16 units, so slicing is done on the UTF-16 bytes."""
    spans = sorted((e for e in entities or [] if e.type == "custom_emoji" and e.custom_emoji_id),
                   key=lambda e: e.offset)
    if not spans:
        return text
    raw = text.encode("utf-16-le")
    pieces: list[str] = []
    pos = 0
    for e in spans:
        start, end = e.offset * 2, (e.offset + e.length) * 2
        if start < pos:
            continue
        pieces.append(raw[pos:start].decode("utf-16-le"))
        fallback = raw[start:end].decode("utf-16-le") or "⭐"
        emoji_id = await repo.save_emoji(e.custom_emoji_id, fallback)
        pieces.append(f"[[e{emoji_id}]]")
        pos = end
    pieces.append(raw[pos:].decode("utf-16-le"))
    return "".join(pieces)


def shown(label: str) -> str:
    """A label as plain text for owner messages: the icon's fallback emoji, then the text."""
    fallback = getattr(label, "fallback", "")
    return f"{fallback} {label}".strip() if fallback else str(label)


def normalize_label(text: str) -> tuple[str, str]:
    """Splits owner input into (stored icon token, plain label text). Only a custom emoji at the very
    start can become the button icon (Telegram shows one icon before the label); every other emoji token
    is flattened to its plain character because button text cannot carry entities."""
    text = text.strip()
    prefix = ""
    lead = _LEAD_ICON_RE.match(text)
    if lead and int(lead.group(1)) in STORE.emojis:
        prefix = f"[[e{lead.group(1)}]]"
        text = text[lead.end():]
    return prefix, render_template(text, {}).text.strip()


def connect_url(row: dict[str, Any]) -> str:
    return ProxyRecord(row["host"], int(row["port"]), row["secret"]).deep_link


# ----- menu model -----

USER_BUILTINS = ["all", "new", "status", "channel"]
OTHER_USER_LABELS = ["btn_prev", "btn_next", "btn_home", "btn_refresh", "btn_check_sub", "btn_join",
                     "btn_joined", "btn_connect", "btn_more", "btn_open_channel"]
OWNER_SECTION_KEYS = ["dash", "proxies", "sources", "validation", "publishing", "subscription",
                      "users", "logs", "system", "ui"]
PAGE_SIZE = 5
OWNER_PAGE_SIZE = 8


@dataclass(frozen=True)
class MenuItem:
    key: str
    label: str
    callback: str | None
    url: str | None


def ordered_keys(valid: list[str], raw_order: str) -> list[str]:
    order = [k for k in (raw_order or "").split(",") if k in valid]
    order += [k for k in valid if k not in order]
    return order


def user_menu_items() -> list[MenuItem]:
    """Visible main-menu buttons in the owner's order."""
    customs = {f"c{row['id']}": row for row in STORE.custom}
    valid = USER_BUILTINS + list(customs)
    items: list[MenuItem] = []
    for key in ordered_keys(valid, STORE.settings.get("menu_order", "")):
        if STORE.settings.get(f"menu_hidden:{key}") == "1":
            continue
        if key in customs:
            items.append(MenuItem(key, STORE.parse_label(customs[key]["label"]), f"m:cb:{customs[key]['id']}", None))
            continue
        label = STORE.label(f"menu_{key}")
        if key == "all":
            items.append(MenuItem(key, label, "m:all:0", None))
        elif key == "new":
            items.append(MenuItem(key, label, "m:new:0", None))
        elif key == "status":
            items.append(MenuItem(key, label, "m:status", None))
        elif key == "channel":
            link = STORE.channel_link
            items.append(MenuItem(key, label, None if link else "m:channel", link or None))
    return items


def main_menu_markup(items: list[MenuItem]) -> InlineKeyboardMarkup:
    buttons = [
        Button(item.label, url=item.url) if item.url else Button(item.label, callback_data=item.callback)
        for item in items
    ]
    cols = STORE.cols()
    rows = [buttons[i:i + cols] for i in range(0, len(buttons), cols)]
    return InlineKeyboardMarkup(rows)


def home_only() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([[Button(STORE.label("btn_home"), callback_data="m:home")]])


def channel_keyboard(link: str) -> InlineKeyboardMarkup:
    rows = [[Button(STORE.label("btn_home"), callback_data="m:home")]]
    if link:
        rows.insert(0, [Button(STORE.label("btn_open_channel"), url=link)])
    return InlineKeyboardMarkup(rows)


def proxy_list_rendered(title_key: str, rows: list[dict[str, Any]], page: int, pages: int,
                        tz_name: str, show_discovery: bool) -> Rendered:
    """Builds the list message. Every proxy item uses the owner's 'proxy_item' template."""
    parts_text: list[str] = []
    entities: list[dict[str, Any]] = []
    offset = 0

    def add(rendered: Rendered) -> None:
        nonlocal offset
        parts_text.append(rendered.text)
        entities.extend({**e, "offset": e["offset"] + offset} for e in rendered.entities)
        offset += utf16_len(rendered.text)

    add(rich_text(title_key))
    add(plain_text("\n" + rich_text("list_page", {"page": page + 1, "pages": pages}).text + "\n"))
    for row in rows:
        variables = {
            "id": row["id"],
            "status": "✅ عامل",
            "last_ok": fmt_time(row["last_ok_at"], tz_name),
            "discovered": Ref("proxy_discovered") if show_discovery else "",
            "disc_time": fmt_time(row["first_ok_at"] or row["last_ok_at"], tz_name),
        }
        add(render_template(STORE.text("proxy_item"), variables))
        add(plain_text("\n\n"))
    add(rich_text("list_footer", {"warning": Ref("proxy_warning")}))
    return Rendered("".join(parts_text), entities)


def plain_text(text: str) -> Rendered:
    """A plain piece of text with no formatting."""
    return Rendered(text, [])


def proxy_list_keyboard(rows: list[dict[str, Any]], mode: str, page: int, pages: int) -> InlineKeyboardMarkup:
    buttons = [[Button(STORE.label("btn_connect", id=row["id"]), url=connect_url(row))] for row in rows]
    nav = []
    if page > 0:
        nav.append(Button(STORE.label("btn_prev"), callback_data=f"m:{mode}:{page - 1}"))
    if page < pages - 1:
        nav.append(Button(STORE.label("btn_next"), callback_data=f"m:{mode}:{page + 1}"))
    if nav:
        buttons.append(nav)
    buttons.append([Button(STORE.label("btn_refresh"), callback_data=f"m:{mode}:{page}")])
    buttons.append([Button(STORE.label("btn_home"), callback_data="m:home")])
    return InlineKeyboardMarkup(buttons)


def subscription_keyboard(channels: list[dict[str, Any]], missing_ids: set[int]) -> InlineKeyboardMarkup:
    rows = []
    for ch in channels:
        key = "btn_join" if ch["id"] in missing_ids else "btn_joined"
        label = STORE.label(key, title=ch["title"])
        rows.append([Button(with_icon(label[:60], getattr(label, "icon", None), getattr(label, "fallback", "")),
                            url=ch["join_url"])])
    rows.append([Button(STORE.label("btn_check_sub"), callback_data="sub:check")])
    return InlineKeyboardMarkup(rows)


def post_keyboard(row: dict[str, Any], bot_username: str) -> InlineKeyboardMarkup:
    def plain(label: str) -> str:
        fallback = getattr(label, "fallback", "")
        return f"{fallback} {label}".strip() if fallback else str(label)

    buttons = [[Button(plain(STORE.label("btn_connect", id=row["id"])), url=connect_url(row))]]
    if bot_username:
        buttons.append([Button(plain(STORE.label("btn_more")), url=f"https://t.me/{bot_username}")])
    return InlineKeyboardMarkup(buttons)


# =============================================================================
# 9. Source collection
# =============================================================================

_SOURCE_NAME_BLOCKLIST = ("localhost", ".local", ".internal", ".localhost", ".lan")


def valid_source_syntax(url: str) -> str:
    """Checks the URL's shape without touching the network. Returns '' or the Arabic reason."""
    if not url or len(url) > 500:
        return "الرابط فارغ أو طويل جداً"
    try:
        parts = urlsplit(url)
        port = parts.port
    except ValueError:
        return "الرابط غير صالح"
    if parts.scheme != "https":
        return "يجب أن يبدأ الرابط بـ https://"
    if not parts.hostname:
        return "الرابط لا يحتوي على اسم مضيف"
    if parts.username or parts.password:
        return "لا يُقبل رابط يحتوي على بيانات دخول"
    if port not in (None, 443):
        return "المنفذ المسموح به هو 443 فقط"
    host = parts.hostname.lower()
    if host.endswith(_SOURCE_NAME_BLOCKLIST) or host == "localhost":
        return "عنوان داخلي غير مسموح"
    if not (_DOMAIN_RE.match(host) or _is_ip_literal(host)):
        return "اسم المضيف غير صالح"
    return ""


async def validate_source_url(url: str) -> str:
    """Syntax checks plus resolution: every address the host name points to must be public."""
    reason = valid_source_syntax(url)
    if reason:
        return reason
    host = (urlsplit(url).hostname or "").lower()
    try:
        await resolve_public_ips(host)
    except UnsafeTarget:
        return "المضيف يشير إلى عنوان داخلي أو غير عام"
    except OSError:
        return "تعذّر حل اسم المضيف (DNS)"
    return ""


class SourceError(Exception):
    """A source could not be downloaded or is not acceptable. The message is shown to the owner."""


class Collector:
    """Downloads owner-approved sources and stores the valid, de-duplicated proxies they list.

    Each request connects to an IP address that was validated just before the request (see
    pinned_target). Redirects are followed by hand, and each hop is validated again. Conditional
    requests (ETag / Last-Modified) and a content hash avoid re-processing unchanged sources.
    """

    MAX_BYTES = 5 * 1024 * 1024
    FETCH_TIMEOUT = 20.0
    MAX_REDIRECTS = 3
    MAX_PARALLEL = 4

    def __init__(self, svc: Services) -> None:
        self.svc = svc

    async def fetch(self, source: dict[str, Any], conditional: bool = True) -> tuple[str | None, str | None, str | None]:
        """Returns (text, etag, last_modified). text is None when the server says nothing changed."""
        url = source["url"]
        first_headers: dict[str, str] = {}
        if conditional:
            if source.get("etag"):
                first_headers["If-None-Match"] = source["etag"]
            if source.get("last_modified"):
                first_headers["If-Modified-Since"] = source["last_modified"]

        for hop in range(self.MAX_REDIRECTS + 1):
            reason = valid_source_syntax(url)
            if reason:
                raise SourceError(reason)
            host = urlsplit(url).hostname or ""
            try:
                addresses = await resolve_public_ips(host)
            except UnsafeTarget:
                raise SourceError("المضيف يشير إلى عنوان داخلي أو غير عام") from None
            except OSError:
                raise SourceError("تعذّر حل اسم المضيف (DNS)") from None

            target, host_header, sni = pinned_target(url, addresses[0])
            headers = {"Host": host_header, **(first_headers if hop == 0 else {})}
            async with self.svc.http.stream(
                "GET", target, headers=headers, extensions={"sni_hostname": sni}, timeout=self.FETCH_TIMEOUT,
            ) as response:
                if response.status_code in (301, 302, 303, 307, 308):
                    location = response.headers.get("location", "")
                    if not location:
                        raise SourceError("تحويل بدون عنوان وجهة")
                    url = urljoin(url, location)
                    continue
                if response.status_code == 304:
                    return None, source.get("etag"), source.get("last_modified")
                if response.status_code >= 400:
                    raise SourceError(f"خطأ HTTP {response.status_code}")
                body = bytearray()
                async for chunk in response.aiter_bytes():
                    body.extend(chunk)
                    if len(body) > self.MAX_BYTES:
                        raise SourceError("حجم المصدر أكبر من 5 ميغابايت")
                return (
                    body.decode("utf-8", errors="ignore"),
                    response.headers.get("etag"),
                    response.headers.get("last-modified"),
                )
        raise SourceError("تحويلات كثيرة جداً")

    async def _collect_one(self, source: dict[str, Any]) -> dict[str, int]:
        repo = self.svc.repo
        empty = {"found": 0, "added": 0, "failed": 0, "unchanged": 0}
        try:
            text, etag, last_modified = await self.fetch(source)
        except (httpx.HTTPError, SourceError, ValueError) as exc:
            reason = str(exc) if isinstance(exc, SourceError) else type(exc).__name__
            await repo.record_source_result(source["id"], "error", 0, error=reason)
            await repo.add_event("WARNING", "collect", f"تعذّر جلب «{source['name']}»: {reason}")
            return {**empty, "failed": 1}

        if text is None:
            await repo.record_source_result(source["id"], "unchanged", source["last_found"], etag=etag,
                                            last_modified=last_modified)
            return {**empty, "unchanged": 1}

        digest = hashlib.sha256(text.encode("utf-8")).hexdigest()
        if digest == source.get("content_hash"):
            await repo.record_source_result(source["id"], "unchanged", source["last_found"], etag=etag,
                                            last_modified=last_modified, content_hash=digest)
            return {**empty, "unchanged": 1}

        records = extract_proxies(text)
        added = await repo.insert_proxies(records, source["id"])
        await repo.record_source_result(source["id"], "ok", len(records), etag=etag,
                                        last_modified=last_modified, content_hash=digest)
        return {"found": len(records), "added": added, "failed": 0, "unchanged": 0}

    async def collect_all(self) -> dict[str, int]:
        sources = await self.svc.repo.enabled_sources()
        gate = asyncio.Semaphore(self.MAX_PARALLEL)

        async def run(source: dict[str, Any]) -> dict[str, int]:
            async with gate:
                return await self._collect_one(source)

        results = await asyncio.gather(*(run(s) for s in sources), return_exceptions=True)
        summary = {"sources": len(sources), "found": 0, "added": 0, "failed": 0, "unchanged": 0}
        for source, item in zip(sources, results):
            if isinstance(item, BaseException):
                log.error("collecting from %s crashed", source["name"], exc_info=item)
                summary["failed"] += 1
                continue
            for key in ("found", "added", "failed", "unchanged"):
                summary[key] += item[key]
        return summary

    async def test_source(self, source: dict[str, Any]) -> str:
        """Downloads a source and reports what it contains. Nothing is saved."""
        try:
            text, _, _ = await self.fetch(source, conditional=False)
        except (httpx.HTTPError, SourceError, ValueError) as exc:
            reason = str(exc) if isinstance(exc, SourceError) else type(exc).__name__
            return f"❌ فشل الاختبار: {reason}"
        count = len(extract_proxies(text or ""))
        return f"✅ الاتصال ناجح. عدد البروكسيات الصالحة في المصدر: {count} (لم يُحفظ شيء)."


# =============================================================================
# 10. Reachability validation
# =============================================================================

class Validator:
    """TCP reachability checks for stored proxies.

    Latency is the time to open a TCP connection, including DNS. It is NOT download speed, and a
    successful connection does NOT prove that the MTProto handshake will work. A host whose address
    is not public is treated as a failure, so the bot never probes internal networks.
    """

    def __init__(self, svc: Services) -> None:
        self.svc = svc

    @staticmethod
    async def probe(host: str, port: int, timeout: float) -> tuple[bool, float | None, str | None]:
        started = time.perf_counter()

        async def connect() -> asyncio.StreamWriter:
            address = await resolve_public_ip(host)
            _, writer = await asyncio.open_connection(address, port)
            return writer

        writer = None
        try:
            writer = await asyncio.wait_for(connect(), timeout=timeout)
            return True, (time.perf_counter() - started) * 1000.0, None
        except asyncio.TimeoutError:
            return False, None, "timeout"
        except UnsafeTarget:
            return False, None, "unsafe-address"
        except socket.gaierror:
            return False, None, "dns"
        except OSError as exc:
            return False, None, type(exc).__name__
        finally:
            if writer is not None:
                writer.close()

    async def check_rows(self, rows: list[dict[str, Any]]) -> dict[str, int]:
        summary = {"checked": 0, "working": 0, "failed": 0}
        if not rows:
            return summary
        timeout = float(await tune(self.svc, "validate_timeout_sec"))
        concurrency = int(await tune(self.svc, "validate_concurrency"))
        threshold = int(await tune(self.svc, "failure_threshold"))
        gate = asyncio.Semaphore(concurrency)

        async def one(row: dict[str, Any]) -> dict[str, Any]:
            async with gate:
                ok, latency, error = await self.probe(row["host"], int(row["port"]), timeout)
            return {**row, "ok": ok, "latency_ms": latency, "error": error}

        outcomes = await asyncio.gather(*(one(r) for r in rows), return_exceptions=True)
        clean: list[dict[str, Any]] = []
        for item in outcomes:
            if isinstance(item, dict):
                clean.append(item)
            else:
                log.warning("probe raised unexpectedly: %r", item)
        await self.svc.repo.apply_check_results(clean, threshold)
        working = sum(1 for r in clean if r["ok"])
        return {"checked": len(clean), "working": working, "failed": len(clean) - working}


# =============================================================================
# 11. Mandatory subscription
# =============================================================================

JOINED_STATUSES = {"creator", "administrator", "member"}


async def membership(svc: Services, chat_ref: str, user_id: int, fresh: bool = True) -> bool | None:
    """True or False when known; None when the check itself failed (the user then counts as not subscribed).

    Membership is NEVER cached: every gated command, button press and deep link asks Telegram, so a
    user who leaves a required channel is blocked on their very next interaction. (`fresh` is kept
    only so older callers still work; the answer is always fresh.)"""
    try:
        member = await svc.bot.get_chat_member(chat_key(chat_ref), user_id)
    except TelegramError as exc:
        log.warning("cannot verify membership in %s: %s", chat_ref, exc)
        return None
    if member.status in JOINED_STATUSES:
        return True
    if member.status == "restricted":
        return bool(member.is_member)
    return False


async def check_subscription(svc: Services, user_id: int, channels: list[dict[str, Any]],
                             fresh: bool = True) -> tuple[list, list]:
    """Returns (missing, unverifiable) lists of channel rows. Channels are checked in parallel."""
    results = await asyncio.gather(*(membership(svc, ch["chat_ref"], user_id) for ch in channels))
    missing = [ch for ch, joined in zip(channels, results) if joined is not True]
    unverifiable = [ch for ch, joined in zip(channels, results) if joined is None]
    return missing, unverifiable


async def bot_permissions(bot: Any, chat_ref: str) -> tuple[bool, str, dict[str, Any] | None]:
    """Checks that the bot is an admin of a required channel (needed to verify members)."""
    try:
        chat = await bot.get_chat(chat_key(chat_ref))
        me = await bot.get_chat_member(chat.id, bot.id)
    except TelegramError as exc:
        return False, f"تعذّر الوصول إلى القناة ({type(exc).__name__})", None
    info = {"id": chat.id, "title": chat.title or chat_ref, "username": chat.username}
    if me.status in ("administrator", "creator"):
        return True, "✅ البوت مشرف في القناة", info
    return False, "⚠️ البوت ليس مشرفاً في القناة", info


async def publish_permissions(bot: Any, chat_ref: str) -> tuple[bool, str, dict[str, Any] | None]:
    """Checks that the bot is allowed to POST in the publishing channel."""
    try:
        chat = await bot.get_chat(chat_key(chat_ref))
        me = await bot.get_chat_member(chat.id, bot.id)
    except TelegramError as exc:
        return False, f"تعذّر الوصول إلى القناة ({type(exc).__name__})", None
    info = {"id": chat.id, "title": chat.title or chat_ref, "username": chat.username}
    if me.status == "creator":
        return True, "✅ البوت مالك القناة ويمكنه النشر", info
    if me.status != "administrator":
        return False, "⚠️ البوت ليس مشرفاً في القناة", info
    if getattr(me, "can_post_messages", False) is not True:
        return False, "⚠️ البوت مشرف لكن ليست لديه صلاحية نشر الرسائل", info
    return True, "✅ البوت يملك صلاحية نشر الرسائل", info


# =============================================================================
# 12. Channel publishing (one verified proxy per cycle)
# =============================================================================

PREVIEW_OFF = LinkPreviewOptions(is_disabled=True)


class Publisher:
    """Publishes exactly one verified proxy per publishing cycle, as its own channel message.

    Only proxies whose latest check succeeded are eligible. The least recently published proxy
    goes first, so the same proxy is not repeated until every verified proxy has been published.
    Each cycle claims a time slot in the database before sending. A restart inside the same slot
    therefore cannot publish a second proxy for that cycle.
    """

    def __init__(self, svc: Services) -> None:
        self.svc = svc

    def _variables(self, row: dict[str, Any]) -> dict[str, Any]:
        tz = self.svc.settings.timezone
        return {
            "id": row["id"],
            "last_ok": fmt_time(row["last_ok_at"], tz),
            "warning": Ref("proxy_warning"),
            "footer": Ref("footer"),
        }

    async def preview(self) -> tuple[Rendered | None, InlineKeyboardMarkup | None]:
        row = await self.svc.repo.pick_publish_candidate()
        if row is None:
            return None, None
        return render_template(STORE.text("channel_post"), self._variables(row)), post_keyboard(
            row, self.svc.bot_username)

    async def publish_one(self, *, manual: bool, slot: str | None = None) -> str:
        """Returns 'published', 'skipped', 'disabled', 'no-channel', 'slot-taken' or 'error:<name>'."""
        svc, repo = self.svc, self.svc.repo
        channel = await repo.get_setting("publish_channel")
        if not channel:
            return "no-channel"
        if not manual:
            if await repo.get_setting("publish_enabled", "0") != "1":
                return "disabled"
            if slot is not None and not await repo.claim_slot(slot):
                return "slot-taken"
        row = await repo.pick_publish_candidate()
        if row is None:
            await repo.log_publish("skipped", channel, None, None, "لا توجد بروكسيات عاملة مؤكدة")
            return "skipped"

        rendered = render_template(STORE.text("channel_post"), self._variables(row))
        async def send(t: str, e: Any, m: Any) -> Any:
            return await svc.bot.send_message(chat_id=chat_key(channel), text=t, entities=e, reply_markup=m,
                                              link_preview_options=PREVIEW_OFF)

        try:
            message = await send_safely(send, rendered.text, tg_entities(rendered.entities),
                                        post_keyboard(row, svc.bot_username))
        except TelegramError as exc:
            await repo.log_publish("error", channel, None, row["id"], f"{type(exc).__name__}: {exc}")
            return f"error:{type(exc).__name__}"
        await repo.mark_published(row["id"])
        await repo.log_publish("published", channel, message.message_id, row["id"], "manual" if manual else "scheduled")
        await repo.set_setting("last_publish_at", now_iso())
        return "published"


# =============================================================================
# 13. Background jobs, bootstrap and scheduler
# =============================================================================

BOOTSTRAP_MAX_ROUNDS = 10  # 10 rounds at a 2-minute interval, then the shortage is reported honestly


class Jobs:
    """Collection, validation, bootstrap, publishing and maintenance.

    Each job runs through JobGuard, so it never overlaps with itself. Manual triggers that find the
    job already running receive BUSY and tell the owner, instead of silently doing nothing.
    """

    REPLACEMENT_COOLDOWN = timedelta(minutes=10)
    ALERT_COOLDOWN = timedelta(hours=6)
    BACKUP_EVERY = timedelta(hours=24)

    def __init__(self, svc: Services) -> None:
        self.svc = svc
        self.collector = Collector(svc)
        self.validator = Validator(svc)
        self.publisher = Publisher(svc)

    async def _alert_owners(self, key: str, text: str) -> None:
        """At most one alert per key every few hours, so owners are not flooded."""
        repo = self.svc.repo
        elapsed = elapsed_since(await repo.get_setting(f"alert:{key}"))
        if elapsed is not None and elapsed < self.ALERT_COOLDOWN:
            return
        await repo.set_setting(f"alert:{key}", now_iso())
        for owner_id in self.svc.settings.owner_ids:
            try:
                await self.svc.bot.send_message(owner_id, text)
            except TelegramError as exc:
                log.warning("could not notify owner %s: %s", owner_id, exc)

    async def _guarded(self, name: str, factory: Callable[[], Awaitable[Any]]) -> Any:
        try:
            return await self.svc.guard.run(name, factory)
        except Exception as exc:  # noqa: BLE001 - a failed job must never stop the scheduler
            log.exception("job %s failed", name)
            try:
                await self.svc.repo.add_event("ERROR", name, f"فشلت المهمة: {type(exc).__name__}: {exc}"[:300])
            except Exception:  # noqa: BLE001
                log.exception("could not record the failure event")
            return None

    async def bootstrap_active(self) -> bool:
        return await self.svc.repo.get_setting("bootstrap_state", "pending") in ("pending", "running")

    # ----- collect -----

    async def collect(self) -> Any:
        return await self._guarded("collect", self._collect)

    async def _collect(self) -> dict[str, int] | None:
        svc = self.svc
        if await self.bootstrap_active():
            await svc.repo.add_event("INFO", "collect", "تأجّل الجمع الدوري لأن التهيئة الأولية تعمل")
            return None
        summary = await self.collector.collect_all()
        await svc.repo.set_setting("last_collect_at", now_iso())
        await svc.repo.add_event(
            "INFO", "collect",
            f"دورة جمع: مصادر {summary['sources']}، مكتشف {summary['found']}، جديد {summary['added']}، "
            f"بدون تغيير {summary['unchanged']}، فاشل {summary['failed']}",
        )
        if summary["sources"] and summary["failed"] == summary["sources"]:
            await self._alert_owners("sources_failed", alert_text("alert_sources_failed"))
        if summary["added"] > 0:
            svc.spawn(self.validate())
        svc.cache.clear()
        return summary

    # ----- validate and replace -----

    async def validate(self) -> Any:
        return await self._guarded("validate", self._validate)

    async def _validate(self) -> dict[str, int]:
        svc, repo = self.svc, self.svc.repo
        recheck_hours = int(await tune(svc, "recheck_hours"))
        cutoff = iso(datetime.now(timezone.utc) - timedelta(hours=recheck_hours))
        candidates = await repo.proxies_to_check(cutoff)
        summary = await self.validator.check_rows(candidates)
        await repo.set_setting("last_validation_at", now_iso())

        working = await repo.count_working()
        target = int(await tune(svc, "target_working"))
        verified_24h = await repo.verified_since(iso(datetime.now(timezone.utc) - timedelta(hours=24)))
        await repo.add_event(
            "INFO", "validate",
            f"فحص {summary['checked']} بروكسي: ناجح {summary['working']}، فاشل {summary['failed']}، "
            f"العاملة الآن {working} من الهدف {target}، تم التحقق منه خلال 24 ساعة: {verified_24h}",
        )
        if working < target and not await self.bootstrap_active():
            await self._maybe_replace()
        daily_goal = int(await tune(svc, "min_daily_working"))
        if not await self.bootstrap_active() and verified_24h < daily_goal:
            await self._alert_owners("daily_short", alert_text(
                "alert_daily_short", count=verified_24h, goal=daily_goal))
        svc.cache.clear()
        return summary

    async def _maybe_replace(self) -> None:
        """Starts a collection when working proxies are below target, at most once per cooldown."""
        elapsed = elapsed_since(await self.svc.repo.get_setting("last_replacement_at"))
        if elapsed is not None and elapsed < self.REPLACEMENT_COOLDOWN:
            return
        await self.svc.repo.set_setting("last_replacement_at", now_iso())
        self.svc.spawn(self.collect())

    # ----- bootstrap: reach the initial target of verified working proxies -----

    async def bootstrap_tick(self) -> None:
        """One bootstrap round, guarded so a scheduled tick and a manual restart never overlap."""
        await self._guarded("bootstrap", self._bootstrap_round)

    async def _bootstrap_round(self) -> None:
        """Collect, validate every candidate, and count verified working proxies."""
        svc, repo = self.svc, self.svc.repo
        if not await self.bootstrap_active():
            return
        target = int(svc.settings.initial_target)
        working = await repo.count_working()
        if working >= target:
            await self._bootstrap_finish("done", working, target)
            return
        if not await repo.enabled_sources():
            # Waiting for the owner to add sources. The state stays 'pending', so it resumes by itself.
            await self._alert_owners("no_sources", alert_text("alert_no_sources"))
            return

        rnd = int(await repo.get_setting("bootstrap_round", "0") or 0) + 1
        await repo.set_setting("bootstrap_state", "running")
        await repo.set_setting("bootstrap_round", rnd)
        await self._guarded_inline("bootstrap-collect", "collect", self.collector.collect_all)
        result = await self._guarded_inline(
            "bootstrap-validate", "validate",
            lambda: self._bootstrap_validate(),
        )
        if result is BUSY:
            await repo.set_setting("bootstrap_round", rnd - 1)  # a scheduled check was running; retry next tick
            return
        working = await repo.count_working()
        await repo.set_setting("bootstrap_verified", working)
        await repo.add_event("INFO", "bootstrap", f"التهيئة الأولية: الجولة {rnd}، عاملة {working} من {target}")
        if working >= target:
            await self._bootstrap_finish("done", working, target)
        elif rnd >= BOOTSTRAP_MAX_ROUNDS:
            await self._bootstrap_finish("shortage", working, target)

    async def _bootstrap_validate(self) -> dict[str, int]:
        cutoff = iso(datetime.now(timezone.utc) - timedelta(hours=int(await tune(self.svc, "recheck_hours"))))
        candidates = await self.svc.repo.proxies_to_check(cutoff)
        return await self.validator.check_rows(candidates)

    async def _guarded_inline(self, label: str, guard_name: str, factory: Callable[[], Awaitable[Any]]) -> Any:
        try:
            return await self.svc.guard.run(guard_name, factory)
        except Exception as exc:  # noqa: BLE001
            log.exception("%s failed", label)
            await self.svc.repo.add_event("ERROR", "bootstrap", f"فشلت خطوة {label}: {type(exc).__name__}"[:300])
            return None

    async def _bootstrap_finish(self, state: str, working: int, target: int) -> None:
        repo = self.svc.repo
        await repo.set_setting("bootstrap_state", state)
        await repo.set_setting("bootstrap_verified", working)
        if state == "done":
            text = alert_text("alert_bootstrap_done", count=working, target=target)
            level = "INFO"
        else:
            text = alert_text("alert_bootstrap_short", count=working, target=target)
            level = "WARNING"
        await repo.add_event(level, "bootstrap", text[:300])
        for owner_id in self.svc.settings.owner_ids:
            try:
                await self.svc.bot.send_message(owner_id, text)
            except TelegramError as exc:
                log.warning("could not notify owner %s: %s", owner_id, exc)

    # ----- publish and maintain -----

    async def publish(self, manual: bool = False, slot: str | None = None) -> Any:
        return await self._guarded("publish", lambda: self._publish(manual, slot))

    async def _publish(self, manual: bool, slot: str | None) -> str:
        result = await self.publisher.publish_one(manual=manual, slot=slot)
        if result.startswith("error:"):
            await self.svc.repo.add_event("ERROR", "publish", f"فشل النشر في القناة: {result[6:]}")
        elif result == "published":
            await self.svc.repo.add_event("INFO", "publish", "تم نشر بروكسي في القناة")
        return result

    async def maintain(self) -> Any:
        return await self._guarded("maintain", self._maintain)

    async def _maintain(self) -> None:
        now = datetime.now(timezone.utc)
        await self.svc.repo.prune(iso(now - timedelta(days=7)), iso(now - timedelta(days=30)),
                                  iso(now - timedelta(days=60)))
        last_backup = elapsed_since(await self.svc.repo.get_setting("last_backup_at"))
        if last_backup is None or last_backup >= self.BACKUP_EVERY:
            await self.make_backup()

    async def make_backup(self) -> Path:
        svc = self.svc
        backup_dir = Path(svc.settings.backup_dir)
        backup_dir.mkdir(parents=True, exist_ok=True)
        name = f"proxy_bot-{datetime.now(timezone.utc).strftime('%Y%m%d-%H%M%S')}.db"
        path = backup_dir / name
        await svc.db.backup_to(str(path))
        copies = sorted(backup_dir.glob("proxy_bot-*.db"))
        for old in copies[:-svc.settings.backup_keep]:
            old.unlink(missing_ok=True)
        await svc.repo.set_setting("last_backup_at", now_iso())
        await svc.repo.add_event("INFO", "maintain", f"نسخة احتياطية للقاعدة: {name}")
        return path


async def publish_scheduled(svc: Services) -> Any:
    """Scheduled publishing: one slot per cycle, so a restart cannot publish twice in one cycle."""
    interval = int(await tune(svc, "publish_interval_min"))
    slot = str(int(time.time() // (interval * 60)))
    return await svc.jobs.publish(manual=False, slot=slot)


def scheduled_publish_job(svc: Services) -> Callable[[], Awaitable[None]]:
    """Wraps the publishing cycle in a real coroutine function, which APScheduler awaits correctly."""

    async def job() -> None:
        await publish_scheduled(svc)

    return job


SCHEDULED_TUNABLES = {
    "collect": "collect_interval_min",
    "validate": "validate_interval_min",
    "publish": "publish_interval_min",
}


def start_scheduler(svc: Services) -> AsyncIOScheduler:
    """Registers every recurring job. Intervals are applied right after by apply_intervals()."""
    jobs = Jobs(svc)
    svc.jobs = jobs
    sched = AsyncIOScheduler(timezone="UTC")
    now = datetime.now(timezone.utc)
    shared = dict(max_instances=1, coalesce=True, misfire_grace_time=300, replace_existing=True)
    sched.add_job(jobs.collect, IntervalTrigger(minutes=1), id="collect",
                  next_run_time=now + timedelta(seconds=20), **shared)
    sched.add_job(jobs.validate, IntervalTrigger(minutes=1), id="validate",
                  next_run_time=now + timedelta(seconds=40), **shared)
    sched.add_job(scheduled_publish_job(svc), IntervalTrigger(minutes=1), id="publish",
                  next_run_time=now + timedelta(minutes=2), **shared)
    sched.add_job(jobs.bootstrap_tick, IntervalTrigger(minutes=2), id="bootstrap",
                  next_run_time=now + timedelta(seconds=5), **shared)
    sched.add_job(jobs.maintain, IntervalTrigger(hours=6), id="maintain",
                  next_run_time=now + timedelta(minutes=5), **shared)
    sched.start()
    svc.scheduler = sched
    return sched


async def apply_intervals(svc: Services) -> None:
    """Applies the saved interval values to the running scheduler (called after an owner change)."""
    if svc.scheduler is None:
        return
    for job_id, tunable in SCHEDULED_TUNABLES.items():
        minutes = int(await tune(svc, tunable))
        svc.scheduler.reschedule_job(job_id, trigger=IntervalTrigger(minutes=minutes))


def stop_scheduler(svc: Services) -> None:
    if svc.scheduler is not None:
        svc.scheduler.shutdown(wait=False)


# =============================================================================
# 14. Owner panel views
# =============================================================================
# Each view returns (text, rows). Buttons take their labels from the customization store.

MENU_TEXT = "🛠 لوحة التحكم، اختر القسم:"
STATUS_AR = {"working": "عامل", "failing": "قيد المراجعة", "hidden": "مخفي", "pending": "بانتظار الفحص"}
COMPONENT_AR = {
    "collect": "الجمع", "validate": "الفحص", "publish": "النشر", "maintain": "الصيانة",
    "bot": "البوت", "start": "التشغيل", "bootstrap": "التهيئة الأولية",
}
LEVEL_ICON = {"INFO": "ℹ️", "WARNING": "⚠️", "ERROR": "❌"}


def ob(label_key: str, callback: str, **values: Any) -> Button:
    """An owner-panel button whose label comes from the customization store."""
    return Button(STORE.label(label_key, **values), callback_data=callback)


def owner_markup(rows: list[list[Button]], back_to: str = "o:menu") -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([*rows, [ob("o_back", back_to)]])


def owner_sections_in_order() -> list[str]:
    return ordered_keys(OWNER_SECTION_KEYS, STORE.settings.get("owner_order", ""))


def menu_markup() -> InlineKeyboardMarkup:
    rows: list[list[Button]] = []
    row: list[Button] = []
    for key in owner_sections_in_order():
        row.append(ob(f"o_{key}", f"o:s:{key}"))
        if len(row) == 2:
            rows.append(row)
            row = []
    if row:
        rows.append(row)
    return InlineKeyboardMarkup(rows)


def latency_text(value: float | None) -> str:
    return f"{value:.0f} ms" if value is not None else "-"


def bootstrap_text(state: str, verified: int, target: int, rnd: int) -> str:
    names = {"pending": "بانتظار البدء", "running": "جارية", "done": "مكتملة", "shortage": "انتهت بنقص"}
    return f"{names.get(state, state)}: {verified} من {target} (الجولة {rnd})"


async def _dashboard(svc: Services) -> tuple[str, list[list[Button]]]:
    r, tz = svc.repo, svc.settings.timezone
    now = datetime.now(timezone.utc)
    day = day_start_iso(tz)
    day_ago = iso(now - timedelta(hours=24))
    (p, s, u, errors, verified_24h, daily_goal, target, state, verified_now, rnd_raw,
     last_collect, last_validation, last_publish) = await asyncio.gather(
        r.proxy_counts(day), r.source_counts(), r.user_counts(day, day_ago), r.count_events("ERROR", day_ago),
        r.verified_since(day_ago), tune(svc, "min_daily_working"), tune(svc, "target_working"),
        r.get_setting("bootstrap_state", "pending"), r.count_working(), r.get_setting("bootstrap_round", "0"),
        r.get_setting("last_collect_at"), r.get_setting("last_validation_at"), r.get_setting("last_publish_at"))
    daily_goal, target, rnd = int(daily_goal), int(target), int(rnd_raw or 0)
    system = "🟢 يعمل بشكل طبيعي" if errors == 0 else f"🟡 حدثت {errors} أخطاء خلال 24 ساعة، راجع السجل"
    text = "\n".join([
        "📊 لوحة المعلومات", "",
        f"الحالة: {system}",
        f"التهيئة الأولية: {bootstrap_text(state, verified_now, int(svc.settings.initial_target), rnd)}",
        f"الهدف العام: {verified_now} من {target} عاملة",
        f"الهدف اليومي: {verified_24h} من {daily_goal} بروكسي جديد تم التحقق منه خلال 24 ساعة",
        "",
        f"🗂 البروكسيات: {p['total']}",
        f"✅ عاملة (آخر فحص ناجح): {p['working']}",
        f"⚠️ فشلت آخر مرة (تحت المراجعة): {p['failing']}",
        f"🚫 مخفية بسبب الفشل: {p['hidden']}",
        f"⛔ معطّلة يدوياً: {p['disabled']}",
        "",
        f"📡 المصادر: {s['total']} (مفعّلة {s['active']})",
        f"👥 المستخدمون: {u['total']} (نشطون خلال 24 ساعة: {u['active']})",
        "",
        f"🕒 آخر جمع: {fmt_time(last_collect, tz)}",
        f"🕒 آخر فحص: {fmt_time(last_validation, tz)}",
        f"🕒 آخر نشر: {fmt_time(last_publish, tz)}",
    ])
    return text, [[ob("o_check", "o:chk")], [ob("o_bootstrap", "o:bootstrap")]]


async def _proxies(svc: Services) -> tuple[str, list[list[Button]]]:
    r, tz = svc.repo, svc.settings.timezone
    p = await r.proxy_counts(day_start_iso(tz))
    text = "\n".join([
        "🛠 إدارة البروكسيات", "",
        f"✅ عاملة (آخر فحص ناجح): {p['working']}",
        f"⚠️ فشلت آخر مرة: {p['failing']}",
        f"🚫 مخفية: {p['hidden']}",
        f"⛔ معطّلة يدوياً: {p['disabled']}",
        f"➕ أُضيفت اليوم: {p['added_today']}",
        f"🕒 آخر فحص: {fmt_time(await r.get_setting('last_validation_at'), tz)}",
        "",
        "الفحص يتحقق من إمكانية الوصول إلى المنفذ فقط، ولا يثبت صحة بروتوكول MTProto كاملاً.",
    ])
    rows = [
        [ob("o_check", "o:chk")],
        [ob("o_browse", "o:pg:0"), ob("o_search", "o:in:px_in")],
        [ob("o_inactive", "o:inactive")],
    ]
    return text, rows


async def _sources(svc: Services) -> tuple[str, list[list[Button]]]:
    tz = svc.settings.timezone
    sources = await svc.repo.list_sources()
    lines = ["📡 مصادر الجمع", ""]
    if not sources:
        lines.append("لا توجد مصادر مضافة بعد. أضف روابط HTTPS موثوقة تعرض روابط بروكسيات MTProto.")
    rows: list[list[Button]] = []
    for s in sources:
        mark = "✅" if s["enabled"] else "⛔"
        lines += [
            f"{mark} #{s['id']} {s['name']}",
            f"   آخر نجاح: {fmt_time(s['last_ok_at'], tz)} | الحالة: {s['last_status'] or '-'}",
        ]
        rows.append([Button(f"📄 #{s['id']} {s['name']}"[:60], callback_data=f"o:src_v:{s['id']}")])
    rows.append([ob("o_add_source", "o:in:src_in")])
    rows.append([ob("o_collect", "o:collect")])
    return "\n".join(lines), rows


async def render_source(svc: Services, source_id: int) -> tuple[str, InlineKeyboardMarkup]:
    tz = svc.settings.timezone
    s = await svc.repo.get_source(source_id)
    if s is None:
        return msg("msg_not_found"), owner_markup([], "o:s:sources")
    stats = await svc.repo.source_stats(source_id)
    events = await svc.repo.events_mentioning("collect", s["name"], 5)
    lines = [
        f"📡 المصدر #{s['id']}", "",
        f"الاسم: {s['name']}",
        f"الرابط: {s['url']}",
        f"مفعّل: {'نعم' if s['enabled'] else 'لا'}",
        f"آخر محاولة: {fmt_time(s['last_fetch_at'], tz)}",
        f"آخر نجاح: {fmt_time(s['last_ok_at'], tz)}",
        f"الحالة الأخيرة: {s['last_status'] or '-'}",
        "",
        "الإحصائيات (بمعنى واضح):",
        f"• بروكسيات أدرجها هذا المصدر: {stats['listed']}",
        f"• بروكسيات كان هذا المصدر أول من أدرجها: {stats['first_found']}",
        f"• من بروكسياته، عاملة الآن: {stats['working_now']}",
        f"• من بروكسياته، تم التحقق منها خلال 24 ساعة: {stats['verified_24h']}",
        "",
        "آخر الأحداث:",
    ]
    if not events:
        lines.append("لا توجد أحداث مسجلة لهذا المصدر.")
    for ev in events:
        lines.append(f"• {fmt_time(ev['created_at'], tz)}: {ev['message']}")
    rows = [
        [ob("o_toggle", f"o:src_t:{s['id']}"), ob("o_test_source", f"o:src_test:{s['id']}")],
        [ob("o_edit_source", f"o:in:src_edit:{s['id']}")],
        [ob("o_delete", f"o:ask:src:{s['id']}")],
    ]
    return "\n".join(lines), owner_markup(rows, "o:s:sources")


async def _validation(svc: Services) -> tuple[str, list[list[Button]]]:
    r, tz = svc.repo, svc.settings.timezone
    values = {key: await tune(svc, key) for key in TUNABLES}
    working = await r.count_working()
    lines = [
        "⚙️ إعدادات الفحص والجمع", "",
        f"🔁 فترة الفحص: كل {values['validate_interval_min']} دقيقة",
        f"📥 فترة الجمع: كل {values['collect_interval_min']} دقيقة",
        f"⏱ مهلة الاتصال: {values['validate_timeout_sec']:g} ثانية",
        f"🧵 الفحوص المتزامنة: {values['validate_concurrency']}",
        f"❌ الإخفاقات المتتالية قبل الإخفاء: {values['failure_threshold']}",
        f"♻️ إعادة فحص المخفية كل: {values['recheck_hours']} ساعة",
        f"🎯 الهدف العام: {values['target_working']} (الحالي: {working})",
        f"📅 الهدف اليومي: {values['min_daily_working']} بروكسي جديد خلال 24 ساعة",
        f"🚀 هدف التهيئة الأولية: {values['initial_target']}",
        "",
        "نوع الفحص: TCP فقط (إمكانية الوصول إلى المنفذ). لا يتم التحقق من بروتوكول MTProto كاملاً.",
        f"🕒 آخر فحص: {fmt_time(await r.get_setting('last_validation_at'), tz)}",
    ]
    rows = [
        [ob("o_check", "o:chk")],
        [ob("o_bootstrap", "o:bootstrap")],
        [ob("o_cfg_validate_interval_min", "o:in:cfg:validate_interval_min"),
         ob("o_cfg_collect_interval_min", "o:in:cfg:collect_interval_min")],
        [ob("o_cfg_validate_timeout_sec", "o:in:cfg:validate_timeout_sec"),
         ob("o_cfg_validate_concurrency", "o:in:cfg:validate_concurrency")],
        [ob("o_cfg_failure_threshold", "o:in:cfg:failure_threshold"),
         ob("o_cfg_recheck_hours", "o:in:cfg:recheck_hours")],
        [ob("o_cfg_target_working", "o:in:cfg:target_working"),
         ob("o_cfg_min_daily_working", "o:in:cfg:min_daily_working")],
        [ob("o_cfg_initial_target", "o:in:cfg:initial_target")],
    ]
    return "\n".join(lines), rows


async def _publishing(svc: Services) -> tuple[str, list[list[Button]]]:
    r, tz = svc.repo, svc.settings.timezone
    enabled = await r.get_setting("publish_enabled", "0") == "1"
    channel = await r.get_setting("publish_channel") or "غير محددة"
    interval = await tune(svc, "publish_interval_min")
    last = (await r.recent_publish_log(1) or [{"outcome": "-", "detail": ""}])[0]
    text = "\n".join([
        "📤 إدارة النشر", "",
        f"الحالة: {'🟢 مفعّل' if enabled else '🔴 متوقف'}",
        f"القناة: {channel}",
        f"سياسة النشر: بروكسي واحد من البروكسيات العاملة المؤكدة كل {interval} دقيقة",
        f"آخر نشر: {fmt_time(await r.get_setting('last_publish_at'), tz)}",
        f"آخر نتيجة: {last['outcome']} {last.get('detail') or ''}".rstrip(),
    ])
    rows = [
        [ob("o_pub_toggle", "o:pub_t")],
        [ob("o_pub_channel", "o:in:pub_ch"),
         ob("o_cfg_publish_interval_min", "o:in:cfg:publish_interval_min")],
        [ob("o_pub_preview", "o:pub_prev"), ob("o_publish_now", "o:pub_now")],
        [ob("o_pub_history", "o:pub_hist")],
    ]
    return text, rows


async def _subscription(svc: Services) -> tuple[str, list[list[Button]]]:
    r = svc.repo
    channels = await r.list_channels()
    lines = ["🔒 الاشتراك الإجباري", "",
             "الحالة: 🟢 مفعّل دائماً (يُفحص الاشتراك من تيليجرام عند كل أمر وزر ورابط)", ""]
    if not channels:
        lines.append("لا توجد قنوات مضافة. بدون قنوات مفعّلة لن يُطلب من أحد الاشتراك.")
    rows: list[list[Button]] = []
    for ch in channels:
        mark = "✅" if ch["enabled"] else "⛔"
        lines.append(f"{mark} #{ch['id']} {ch['title']} ({ch['chat_ref']})")
        rows.append([
            Button(f"⏯ #{ch['id']}", callback_data=f"o:ch_t:{ch['id']}"),
            Button(f"🗑 #{ch['id']}", callback_data=f"o:ask:ch:{ch['id']}"),
        ])
    rows.append([ob("o_add_channel", "o:in:ch_in")])
    rows.append([ob("o_check_channels", "o:ch_chk")])
    return "\n".join(lines), rows


async def _users(svc: Services) -> tuple[str, list[list[Button]]]:
    day = day_start_iso(svc.settings.timezone)
    day_ago = iso(datetime.now(timezone.utc) - timedelta(hours=24))
    counts = await svc.repo.user_counts(day, day_ago)
    text = "\n".join([
        "👥 إحصائيات المستخدمين", "",
        f"إجمالي المستخدمين: {counts['total']}",
        f"نشطون خلال 24 ساعة: {counts['active']}",
        f"مستخدمون جدد اليوم: {counts['new_today']}",
        f"محظورون: {counts['blocked']}",
    ])
    rows = [
        [ob("o_find_user", "o:in:usr_find")],
        [ob("o_blocked_list", "o:usr_list")],
    ]
    return text, rows


async def _logs(svc: Services) -> tuple[str, list[list[Button]]]:
    tz = svc.settings.timezone
    events = await svc.repo.recent_events(15)
    user_ms = svc.metrics.summary("user_callback")
    owner_ms = svc.metrics.summary("owner_callback")
    lines = [
        "🧾 السجل والأخطاء", "",
        "⚡ زمن استجابة الأزرار:",
        f"المستخدمون: متوسط {user_ms['avg']:.0f} ms، و95% منها تحت {user_ms['p95']:.0f} ms "
        f"(من {user_ms['count']} نقرة)",
        f"لوحة التحكم: متوسط {owner_ms['avg']:.0f} ms (من {owner_ms['count']} نقرة)",
        f"استعلامات بطيئة منذ التشغيل: {svc.db.slow_queries}",
        "",
    ]
    if not events:
        lines.append("لا توجد سجلات بعد.")
    for ev in events:
        icon = LEVEL_ICON.get(ev["level"], "•")
        component = COMPONENT_AR.get(ev["component"], ev["component"])
        lines.append(f"{icon} {fmt_time(ev['created_at'], tz)} — {component}: {ev['message']}")
    return "\n".join(lines), [[ob("o_refresh", "o:s:logs")]]


async def _system(svc: Services) -> tuple[str, list[list[Button]]]:
    s = svc.settings
    r = svc.repo
    db_size = Path(s.db_path).stat().st_size if Path(s.db_path).exists() else 0
    backups = len(list(Path(s.backup_dir).glob("proxy_bot-*.db"))) if Path(s.backup_dir).exists() else 0
    text = "\n".join([
        "🔧 إعدادات النظام", "",
        f"المنطقة الزمنية: {s.timezone}",
        f"عدد المالكين المصرّح لهم: {len(s.owner_ids)}",
        f"رابط القناة: {'مضبوط' if STORE.channel_link else 'غير مضبوط'}",
        f"حجم قاعدة البيانات: {db_size / 1024:.0f} KB",
        f"النسخ الاحتياطية المحفوظة: {backups} (الاحتفاظ بـ {s.backup_keep})",
        f"آخر نسخة: {fmt_time(await r.get_setting('last_backup_at'), s.timezone)}",
        f"عدد المصادر المبدئية في الإعدادات: {len(s.initial_sources)}",
        "",
        "الاستعادة تتم عبر رفع ملف النسخة هنا؛ تُطبَّق الاستعادة عند إعادة تشغيل البوت، "
        "والقاعدة الحالية تُحفظ بجانبها قبل الاستبدال.",
    ])
    rows = [
        [ob("o_collect", "o:collect")],
        [ob("o_backup", "o:bak"), ob("o_restore", "o:restore")],
    ]
    return text, rows


async def _ui(svc: Services) -> tuple[str, list[list[Button]]]:
    text = "\n".join([
        "🎨 تخصيص الواجهة", "",
        "من هنا تعدّل كل رسالة، وكل زر، وترتيب القوائم، والإيموجي المميزة.",
        "الإيموجي المميزة (Premium): داخل نصوص الرسائل كإيموجي حقيقية، وفي الأزرار كأيقونة واحدة قبل الاسم",
        "(تيليجرام لا يسمح بإيموجي مميزة وسط نص الزر نفسه، وهي لا تعمل في أزرار منشورات القنوات).",
        "صيغ النص المدعومة: <b>عريض</b>، <i>مائل</i>، <code>كود</code>، والإيموجي العادية كما هي.",
    ])
    rows = [
        [ob("o_messages", "o:ui_msgs:0")],
        [ob("o_buttons", "o:ui_btns")],
        [ob("o_owner_buttons", "o:ui_owner")],
        [ob("o_emoji", "o:ui_emoji")],
        [ob("o_ui_channel", "o:in:ui_chan")],
        [ob("o_restore_default", "o:ask:uireset:0")],
    ]
    return text, rows


SECTIONS = {
    "dash": _dashboard,
    "proxies": _proxies,
    "sources": _sources,
    "validation": _validation,
    "publishing": _publishing,
    "subscription": _subscription,
    "users": _users,
    "logs": _logs,
    "system": _system,
    "ui": _ui,
}


async def render_section(svc: Services, key: str) -> tuple[str, InlineKeyboardMarkup]:
    text, rows = await SECTIONS[key](svc)
    return text, owner_markup(rows)


async def render_proxy(svc: Services, proxy_id: int) -> tuple[str, InlineKeyboardMarkup]:
    tz = svc.settings.timezone
    proxy = await svc.repo.get_proxy(proxy_id)
    if proxy is None:
        return msg("msg_not_found"), owner_markup([], "o:pg:0")
    checks = await svc.repo.proxy_checks(proxy_id, 5)
    sources = await svc.repo.proxy_sources(proxy_id)
    lines = [
        f"🔎 بروكسي رقم {proxy['id']}", "",
        f"المضيف: {proxy['host']}:{proxy['port']}",
        f"أول من أدرجه: {proxy['source_name']}",
        f"أدرجه أيضاً: {', '.join(sources) if sources else '-'}",
        f"تاريخ الاكتشاف: {fmt_time(proxy['discovered_at'], tz)}",
        f"أول تحقق ناجح: {fmt_time(proxy['first_ok_at'], tz)}",
        f"الحالة: {STATUS_AR.get(proxy['status'], proxy['status'])}",
        f"مفعّل: {'نعم' if proxy['enabled'] else 'لا'}",
        f"الإخفاقات المتتالية: {proxy['consecutive_failures']}",
        f"عدد الفحوص الناجحة: {proxy['success_count']}",
        f"آخر فحص ناجح: {fmt_time(proxy['last_ok_at'], tz)}",
        f"آخر فشل: {fmt_time(proxy['last_failure_at'], tz)} {proxy['last_error'] or ''}".rstrip(),
        f"آخر نشر في القناة: {fmt_time(proxy['last_published_at'], tz)} (مرات: {proxy['publish_count']})",
        f"زمن الاتصال الأخير: {latency_text(proxy['last_latency_ms'])}",
        "",
        "آخر الفحوص:",
    ]
    if not checks:
        lines.append("لا يوجد سجل فحص بعد.")
    for c in checks:
        outcome = f"نجح ({latency_text(c['latency_ms'])})" if c["ok"] else f"فشل ({c['error'] or 'خطأ'})"
        lines.append(f"• {fmt_time(c['checked_at'], tz)}: {outcome}")
    rows = [
        [ob("o_recheck", f"o:chkp:{proxy['id']}"), ob("o_toggle", f"o:pt:{proxy['id']}")],
        [ob("o_delete", f"o:ask:px:{proxy['id']}")],
    ]
    return "\n".join(lines), owner_markup(rows, "o:pg:0")


async def render_browse(svc: Services, page: int) -> tuple[str, InlineKeyboardMarkup]:
    page = max(page, 0)
    total, rows = await asyncio.gather(svc.repo.count_all_proxies(),
                                       svc.repo.browse_proxies(page * OWNER_PAGE_SIZE, OWNER_PAGE_SIZE))
    pages = max(1, math.ceil(total / OWNER_PAGE_SIZE))
    if page > pages - 1:
        page = pages - 1
        rows = await svc.repo.browse_proxies(page * OWNER_PAGE_SIZE, OWNER_PAGE_SIZE)
    lines = [f"📋 تصفح البروكسيات (الصفحة {page + 1} من {pages})", ""]
    if not rows:
        lines.append("لا توجد بروكسيات بعد.")
    buttons: list[list[Button]] = []
    for p in rows:
        status = STATUS_AR.get(p["status"], p["status"]) if p["enabled"] else "معطّل"
        lines.append(f"• #{p['id']} {p['host']}:{p['port']} — {status}")
        buttons.append([Button(f"عرض #{p['id']}", callback_data=f"o:pv:{p['id']}")])
    nav = []
    if page > 0:
        nav.append(ob("btn_prev", f"o:pg:{page - 1}"))
    if page < pages - 1:
        nav.append(ob("btn_next", f"o:pg:{page + 1}"))
    if nav:
        buttons.append(nav)
    return "\n".join(lines), owner_markup(buttons, "o:s:proxies")


async def render_inactive(svc: Services) -> tuple[str, InlineKeyboardMarkup]:
    rows = await svc.repo.inactive_proxies(OWNER_PAGE_SIZE)
    lines = ["⛔ البروكسيات المخفية والمعطّلة", ""]
    if not rows:
        lines.append("لا توجد بروكسيات مخفية أو معطّلة.")
    for p in rows:
        reason = "معطّل يدوياً" if not p["enabled"] else "مخفي بسبب الفشل"
        lines.append(f"• #{p['id']} {p['host']}:{p['port']}: {reason}")
    buttons = [[Button(f"عرض #{p['id']}", callback_data=f"o:pv:{p['id']}")] for p in rows]
    return "\n".join(lines), owner_markup(buttons, "o:s:proxies")


async def render_search(svc: Services, query: str) -> tuple[str, InlineKeyboardMarkup]:
    rows = await svc.repo.search_proxies(query)
    if not rows:
        return "لا توجد نتائج مطابقة.", owner_markup([], "o:s:proxies")
    lines = [f"نتائج البحث ({len(rows)}):"]
    buttons = []
    for p in rows:
        lines.append(f"• #{p['id']} {p['host']}:{p['port']}: {STATUS_AR.get(p['status'], p['status'])}")
        buttons.append([Button(f"عرض #{p['id']}", callback_data=f"o:pv:{p['id']}")])
    return "\n".join(lines), owner_markup(buttons, "o:s:proxies")


async def render_user(svc: Services, user_id: int) -> tuple[str, InlineKeyboardMarkup]:
    tz = svc.settings.timezone
    user = await svc.repo.get_user(user_id)
    if user is None:
        return "لم يُعثر على هذا المستخدم. لم يستخدم البوت بعد.", owner_markup([], "o:s:users")
    blocked = bool(user["blocked"])
    text = "\n".join([
        f"👤 المستخدم {user['user_id']}", "",
        f"أول ظهور: {fmt_time(user['first_seen'], tz)}",
        f"آخر ظهور: {fmt_time(user['last_seen'], tz)}",
        f"الحالة: {'⛔ محظور' if blocked else '✅ نشط'}",
    ])
    action = (ob("o_unblock", f"o:unb:{user_id}") if blocked
              else ob("o_block", f"o:ask:blk:{user_id}"))
    return text, owner_markup([[action]], "o:s:users")


async def render_blocked(svc: Services) -> tuple[str, InlineKeyboardMarkup]:
    rows = await svc.repo.list_blocked()
    lines = ["⛔ المستخدمون المحظورون", ""]
    if not rows:
        lines.append("لا يوجد مستخدمون محظورون.")
    buttons = []
    for row in rows:
        lines.append(f"• {row['user_id']}")
        buttons.append([Button(f"عرض {row['user_id']}", callback_data=f"o:usr_v:{row['user_id']}")])
    return "\n".join(lines), owner_markup(buttons, "o:s:users")


# ----- customization views -----

def _preview_rows(apply_token: str) -> list[list[Button]]:
    return [[ob("o_apply", f"o:apply:{apply_token}"), ob("o_cancel", "o:cancel")]]


async def view_messages(svc: Services, page: int) -> tuple[str, InlineKeyboardMarkup]:
    keys = list(TEXT_TITLES)
    pages = max(1, math.ceil(len(keys) / 8))
    page = min(max(page, 0), pages - 1)
    rows = []
    for key in keys[page * 8:(page + 1) * 8]:
        marker = "✏️" if STORE.has_custom_text(key) else "•"
        rows.append([Button(f"{marker} {TEXT_TITLES[key]}"[:60], callback_data=f"o:ui_msg:{key}")])
    nav = []
    if page > 0:
        nav.append(ob("btn_prev", f"o:ui_msgs:{page - 1}"))
    if page < pages - 1:
        nav.append(ob("btn_next", f"o:ui_msgs:{page + 1}"))
    if nav:
        rows.append(nav)
    text = f"💬 تخصيص الرسائل (الصفحة {page + 1} من {pages})\n✏️ = معدّلة من المالك"
    return text, owner_markup(rows, "o:s:ui")


async def view_message(svc: Services, key: str) -> tuple[str | Rendered, InlineKeyboardMarkup]:
    rows = [
        [ob("o_edit", f"o:in:tpl:{key}"), ob("o_preview", f"o:ui_prev_tpl:{key}")],
        [ob("o_restore_default", f"o:ui_reset_tpl:{key}")],
    ]
    current = render_template(STORE.text(key), SAMPLE_VARIABLES)
    header = f"💬 {TEXT_TITLES[key]}\nكما يظهر للمستخدم (بيانات تجريبية):\n\n"
    return with_prefix(header, current), owner_markup(rows, "o:ui_msgs:0")


async def view_user_buttons(svc: Services) -> tuple[str, InlineKeyboardMarkup]:
    customs = {f"c{row['id']}": row for row in STORE.custom}
    order = ordered_keys(USER_BUILTINS + list(customs), STORE.settings.get("menu_order", ""))
    lines = ["🔘 أزرار القائمة الرئيسية للمستخدمين", "", f"عدد الأعمدة: {STORE.cols()}", ""]
    rows: list[list[Button]] = []
    for key in order:
        hidden = STORE.settings.get(f"menu_hidden:{key}") == "1"
        label = shown(STORE.parse_label(customs[key]["label"])) if key in customs else shown(STORE.label(f"menu_{key}"))
        lines.append(f"{'🙈' if hidden else '✅'} {label}")
        callback_key = key
        rows.append([
            Button(STORE.label("o_up"), callback_data=f"o:ui_mv:{callback_key}:-1"),
            Button(STORE.label("o_down"), callback_data=f"o:ui_mv:{callback_key}:1"),
            Button(STORE.label("o_show_hide"), callback_data=f"o:ui_vis:{callback_key}"),
            Button(STORE.label("o_rename"),
                   callback_data=(f"o:ui_cb:{customs[key]['id']}" if key in customs else f"o:in:lbl:menu_{key}")),
        ])
    lines.append("")
    lines.append("أزرار أخرى:")
    for key in OTHER_USER_LABELS:
        rows.append([Button(f"✏️ {shown(STORE.label(key))}"[:60], callback_data=f"o:in:lbl:{key}")])
    rows.append([Button(STORE.label("o_layout", cols=STORE.cols()), callback_data="o:ui_lay")])
    rows.append([ob("o_add_button", "o:in:cb_new")])
    return "\n".join(lines), owner_markup(rows, "o:s:ui")


async def view_custom_button(svc: Services, button_id: int) -> tuple[str, InlineKeyboardMarkup]:
    row = next((b for b in STORE.custom if b["id"] == button_id), None)
    if row is None:
        return msg("msg_not_found"), owner_markup([], "o:ui_btns")
    body = render_template(row["body"], {})
    text_header = f"🔘 الزر المخصص: {shown(STORE.parse_label(row['label']))}\n\nالمحتوى كما يظهر للمستخدم:\n\n"
    rows = [
        [ob("o_edit", f"o:in:cb_body:{button_id}"), ob("o_rename", f"o:in:cb_label:{button_id}")],
        [ob("o_show_hide", f"o:ui_vis:c{button_id}"), ob("o_delete", f"o:ask:cb:{button_id}")],
    ]
    return with_prefix(text_header, body), owner_markup(rows, "o:ui_btns")


async def view_owner_buttons(svc: Services) -> tuple[str, InlineKeyboardMarkup]:
    lines = ["🛠 أزرار لوحة المالك وترتيبها", ""]
    rows: list[list[Button]] = []
    for key in owner_sections_in_order():
        lines.append(f"• {shown(STORE.label(f'o_{key}'))}")
        rows.append([
            Button(STORE.label("o_up"), callback_data=f"o:ui_omv:{key}:-1"),
            Button(STORE.label("o_down"), callback_data=f"o:ui_omv:{key}:1"),
            Button(STORE.label("o_rename"), callback_data=f"o:in:lbl:o_{key}"),
        ])
    return "\n".join(lines), owner_markup(rows, "o:s:ui")


EMOJI_LIST_LIMIT = 40


async def view_emojis(svc: Services) -> tuple[Rendered, InlineKeyboardMarkup]:
    premium = {True: "نعم", False: "لا", None: "غير معروف بعد"}[svc.owner_premium]
    lines = [
        "🎭 الإيموجي المميزة (Premium)", "",
        "لإضافة إيموجي: أرسل الإيموجي المميزة نفسها إلى البوت (داخل رسالة، أو ملصق إيموجي مميز).",
        "يُقرأ معرّفها الحقيقي (custom_emoji_id) من تيليجرام ويُحفظ في قاعدة البيانات ويُحمَّل بعد كل إعادة تشغيل.",
        "ثم عيّنها لأحد المواضع أدناه، أو استخدمها داخل أي رسالة من قسم تخصيص الرسائل.",
        f"حساب المالك Premium (من آخر رسالة): {premium}",
        "ملاحظة: يعرض تيليجرام الإيموجي المميزة التي يرسلها البوت فقط إذا كان مالك البوت مشتركاً في Premium "
        "أو يملك البوت أسماء مستخدم إضافية من Fragment، وإلا تظهر الإيموجي العادية البديلة.",
        "استخدم زر «اختبار الظهور» للتأكد من أن تيليجرام يقبلها.",
        "", "المواضع (تظهر في الرسائل بدلاً من الرمز العادي):",
    ]
    slot_buttons: list[Button] = []
    for name in DEFAULT_SLOTS:
        emoji_id = STORE.slots.get(name)
        if emoji_id:
            lines.append(f"• {SLOT_TITLES[name]}: [[e{emoji_id}]] #{emoji_id}")
            cid, fallback = STORE.emojis[emoji_id]
            slot_buttons.append(Button(with_icon(SLOT_TITLES[name], cid, fallback), callback_data=f"o:ui_slot:{name}"))
        else:
            lines.append(f"• {SLOT_TITLES[name]}: {DEFAULT_SLOTS[name]} (افتراضي)")
            slot_buttons.append(Button(f"🎯 {SLOT_TITLES[name]}", callback_data=f"o:ui_slot:{name}"))
    rows: list[list[Button]] = [slot_buttons[i:i + 2] for i in range(0, len(slot_buttons), 2)]
    lines += ["", "المحفوظة في المكتبة:"]
    library = sorted(STORE.emojis.items())[-EMOJI_LIST_LIMIT:]
    delete_buttons: list[Button] = []
    for emoji_id, (cid, fallback) in library:
        lines.append(f"• #{emoji_id} [[e{emoji_id}]]")
        delete_buttons.append(Button(with_icon(f"🗑 #{emoji_id}", cid, fallback), callback_data=f"o:ask:emo:{emoji_id}"))
    if not STORE.emojis:
        lines.append("لا توجد إيموجي محفوظة بعد.")
    elif len(STORE.emojis) > EMOJI_LIST_LIMIT:
        lines.append(f"(يُعرض آخر {EMOJI_LIST_LIMIT} فقط من {len(STORE.emojis)})")
    rows += [delete_buttons[i:i + 3] for i in range(0, len(delete_buttons), 3)]
    rows.append([Button("🧪 اختبار الظهور", callback_data="o:ui_emotest")])
    return render_template("\n".join(lines)), owner_markup(rows, "o:s:ui")


async def view_slot_choice(svc: Services, name: str) -> tuple[str, InlineKeyboardMarkup]:
    choices: list[Button] = []
    for emoji_id, (cid, fallback) in sorted(STORE.emojis.items())[-EMOJI_LIST_LIMIT:]:
        choices.append(Button(with_icon(f"#{emoji_id}", cid, fallback), callback_data=f"o:ui_slotset:{name}:{emoji_id}"))
    rows = [choices[i:i + 4] for i in range(0, len(choices), 4)]
    rows.append([ob("o_clear", f"o:ui_slotclr:{name}")])
    text = (f"اختر الإيموجي المميزة لموضع «{SLOT_TITLES[name]}».\n"
            "إذا لم تظهر إيموجي هنا، أرسل إيموجي مميزة إلى البوت أولاً.")
    return text, owner_markup(rows, "o:ui_emoji")


async def _emoji_test(svc: Services, query: Any) -> None:
    """Sends every slot with its real custom emoji, then reports what Telegram actually accepted."""
    rendered = render_template("\n".join(f"[[{name}]] {SLOT_TITLES[name]}" for name in DEFAULT_SLOTS))
    wanted = sum(1 for e in rendered.entities if e["type"] == "custom_emoji")
    if wanted == 0:
        await query.message.reply_text("لم تُعيَّن أي إيموجي مميزة لأي موضع بعد. أرسل إيموجي مميزة ثم عيّنها لموضع.")
        return
    sent = await reply_rendered(query.message, rendered)
    accepted = sum(1 for e in (sent.entities or ()) if e.type == "custom_emoji")
    if accepted == wanted:
        verdict = (f"✅ قبل تيليجرام {accepted} إيموجي مميزة في الرسالة أعلاه. "
                   "إن رأيتها كإيموجي عادية فالسبب في تطبيقك، لا في البوت.")
    else:
        verdict = (f"⚠️ أُرسل {wanted} إيموجي مميزة لكن تيليجرام قبل {accepted} فقط. "
                   "يحدث هذا عندما لا يكون مالك البوت مشتركاً في Premium ولا يملك البوت أسماء Fragment إضافية؛ "
                   "هذا قيد من تيليجرام لا يمكن تجاوزه من البوت.")
    await query.message.reply_text(verdict)


# =============================================================================
# 15. User handlers
# =============================================================================

SEEN_TTL = 600.0


def _svc(context: ContextTypes.DEFAULT_TYPE) -> Services:
    return context.application.bot_data["svc"]


async def send_safely(send: Callable[..., Awaitable[Any]], text: str, entities: Any, markup: Any) -> Any:
    """Calls send(text, entities, markup). If Telegram rejects the message, retries without button
    icons and then without custom-emoji entities (the plain emoji characters stay in the text), so a
    Premium restriction never leaves the user with no message. "Message is not modified" is re-raised."""
    global _icons_off_until
    icons = markup_has_icons(markup)
    custom = any(e.type == "custom_emoji" for e in entities or ())
    plain_markup = markup_without_icons(markup) if icons else markup
    variants: list[tuple[Any, Any]] = [(entities, markup)]
    if icons:
        variants.append((entities, plain_markup))
    if custom:
        variants.append(([e for e in entities if e.type != "custom_emoji"] or None, plain_markup))
    last: BadRequest | None = None
    for index, (ents, mk) in enumerate(variants):
        try:
            result = await send(text, ents, mk)
        except BadRequest as exc:
            if "not modified" in str(exc).lower():
                raise
            last = exc
            log.warning("Telegram rejected a message (%s); retrying in a simpler form", exc)
            continue
        if index == 1 and icons:
            _icons_off_until = time.monotonic() + 600.0
            log.warning("Telegram rejected button custom-emoji icons; using plain emoji for 10 minutes")
        return result
    assert last is not None
    raise last


async def reply_rendered(message: Any, content: str | Rendered, markup: Any = None) -> Any:
    """Replies with text or rich text, keeping real custom-emoji entities (with safe fallbacks)."""
    if isinstance(content, Rendered):
        text, entities = content.text, tg_entities(content.entities)
    else:
        text, entities = content, None

    async def send(t: str, e: Any, m: Any) -> Any:
        return await message.reply_text(t, entities=e, reply_markup=m)

    return await send_safely(send, text, entities, markup)


async def _ack(query: Any, text: str | None = None) -> None:
    """Answers a callback query. It runs in the background, in parallel with the real work."""
    try:
        await query.answer(text)
    except TelegramError as exc:
        log.debug("callback answer failed: %s", exc)


async def render(update: Update, context: ContextTypes.DEFAULT_TYPE, content: str | Rendered,
                 markup: InlineKeyboardMarkup | None) -> None:
    """Edits the message behind a button press. Replies instead for commands or when editing fails."""
    if isinstance(content, Rendered):
        text, entities = content.text, tg_entities(content.entities)
    else:
        text, entities = content, None
    query = update.callback_query
    if query is None:
        await reply_rendered(update.effective_message, content, markup)
        return

    async def edit(t: str, e: Any, m: Any) -> Any:
        return await query.edit_message_text(text=t, entities=e, reply_markup=m)

    try:
        await send_safely(edit, text, entities, markup)
    except BadRequest as exc:
        if "not modified" in str(exc).lower():
            return
        log.info("edit failed (%s); sending a new message instead", exc)
        await reply_rendered(query.message, content, markup)


async def _touch(svc: Services, user_id: int) -> None:
    """Records activity at most once per TTL per user, to keep writes low."""

    async def save() -> bool:
        await svc.repo.touch_user(user_id)
        return True

    await svc.cache.get_or_load(f"seen:{user_id}", SEEN_TTL, save)


async def gate(update: Update, context: ContextTypes.DEFAULT_TYPE, note: str | Rendered = "",
               fresh: bool = False) -> bool:
    """True when the user may use the service. Blocks and missing subscriptions are answered here."""
    svc = _svc(context)
    user = update.effective_user
    if user is None:
        return False
    if user.id in svc.settings.owner_ids:
        return True
    # Subscription is always enforced (there is no off switch). Membership is asked from Telegram on
    # EVERY call, in parallel for all channels and in parallel with the block check; nothing is cached.
    channels = await svc.repo.enabled_channels()
    if channels:
        blocked, (missing, unverifiable) = await asyncio.gather(
            svc.repo.is_blocked(user.id), check_subscription(svc, user.id, channels))
    else:
        blocked, missing, unverifiable = await svc.repo.is_blocked(user.id), [], []
    if blocked:
        await render(update, context, rich_text("blocked"), None)
        return False
    if not missing:
        return True
    parts: list[str | Rendered] = [note] if note else []
    parts.append(rich_text("sub_prompt"))
    if unverifiable:
        names = "، ".join(ch["title"] for ch in unverifiable)
        parts.append(rich_text("sub_unverifiable", {"names": names}))
    await render(update, context, concat_rendered(parts),
                 subscription_keyboard(channels, {ch["id"] for ch in missing}))
    return False


async def show_home(update: Update, context: ContextTypes.DEFAULT_TYPE, prefix: str | Rendered = "") -> None:
    welcome = rich_text("welcome")
    content = concat_rendered([prefix, welcome]) if isinstance(prefix, Rendered) else with_prefix(prefix, welcome)
    await render(update, context, content, main_menu_markup(user_menu_items()))


async def show_list(update: Update, context: ContextTypes.DEFAULT_TYPE, mode: str, page: int) -> None:
    svc = _svc(context)
    page = max(page, 0)

    async def load() -> tuple[int, list[dict[str, Any]], int]:
        total, rows = await asyncio.gather(svc.repo.count_visible(),
                                           svc.repo.visible_page(mode, page * PAGE_SIZE, PAGE_SIZE))
        pages = max(1, math.ceil(total / PAGE_SIZE)) if total else 1
        if total and not rows and page > 0:  # page past the end: show the last page instead
            rows = await svc.repo.visible_page(mode, (pages - 1) * PAGE_SIZE, PAGE_SIZE)
        return total, rows, pages

    # Proxy data (not subscription state) may be a few seconds old, so page flips cost no queries.
    total, rows, pages = await svc.cache.get_or_load(f"list:{mode}:{page}", 5.0, load)
    page = min(page, pages - 1)
    if not rows:
        await render(update, context, rich_text("no_proxies"), home_only())
        return
    title_key = "list_title_all" if mode == "all" else "list_title_new"
    content = proxy_list_rendered(title_key, rows, page, pages, svc.settings.timezone,
                                  show_discovery=mode == "new")
    await render(update, context, content, proxy_list_keyboard(rows, mode, page, pages))


async def show_status(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    svc = _svc(context)
    tz = svc.settings.timezone
    day = day_start_iso(tz)
    day_ago = iso(datetime.now(timezone.utc) - timedelta(hours=24))

    async def load() -> dict[str, Any]:
        working, checked, verified, goal, target = await asyncio.gather(
            svc.repo.count_working(), svc.repo.checks_since(day), svc.repo.verified_since(day_ago),
            tune(svc, "min_daily_working"), tune(svc, "target_working"))
        return {"working": working, "checked_today": checked, "verified_24h": verified,
                "daily_goal": int(goal), "target": int(target)}

    stats, last = await asyncio.gather(svc.cache.get_or_load(f"stats:{day}", 20.0, load),
                                       svc.repo.get_setting("last_validation_at"))
    variables = {**stats, "last_check": fmt_time(last, tz)}
    await render(update, context, rich_text("status_text", variables), home_only())


@timed("start")
async def cmd_start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    svc = _svc(context)
    if update.effective_user is None:
        return
    svc.spawn(_touch(svc, update.effective_user.id))
    if await gate(update, context):
        await show_home(update, context)


@timed("user_callback")
async def on_user_callback(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    svc = _svc(context)
    svc.spawn(_ack(query))  # acknowledge at once, in parallel with the work, so the button stops spinning
    svc.spawn(_touch(svc, update.effective_user.id))

    parts = (query.data or "").split(":")
    if parts[:2] == ["sub", "check"]:
        if await gate(update, context, note=rich_text("sub_still_missing"), fresh=True):
            await show_home(update, context, prefix=rich_text("sub_ok"))
        return

    if not await gate(update, context):
        return

    action = parts[1] if len(parts) > 1 else ""
    if action in ("all", "new"):
        page = int(parts[2]) if len(parts) > 2 and parts[2].isdigit() else 0
        await show_list(update, context, action, page)
    elif action == "status":
        await show_status(update, context)
    elif action == "channel":
        await render(update, context, rich_text("channel_text"), channel_keyboard(STORE.channel_link))
    elif action == "cb" and len(parts) > 2 and parts[2].isdigit():
        row = next((b for b in STORE.custom if b["id"] == int(parts[2])), None)
        if row is None:
            await render(update, context, msg("msg_not_found"), home_only())
        else:
            await render(update, context, render_template(row["body"]), home_only())
    elif action == "home":
        await show_home(update, context)


# =============================================================================
# 16. Owner handlers
# =============================================================================
# Every entry point is wrapped in owner_only. Non-owners get no reply at all. Owner changes run one
# at a time (svc.owner_lock), and every preview carries a token so an old preview cannot apply.

TOASTS = {"chk": "بدأ الفحص في الخلفية", "collect": "بدأ الجمع في الخلفية", "pub_now": "بدأ النشر",
          "bootstrap": "أُعيدت التهيئة الأولية"}

INPUT_PROMPTS = {
    "px_in": "أرسل رقم البروكسي أو جزءاً من عنوان المضيف للبحث.\n(/cancel للإلغاء)",
    "src_in": "أرسل المصدر بالصيغة:\nالاسم | https://الرابط\nيُقبل رابط https فقط، ولا تُقبل عناوين داخلية.\n(/cancel للإلغاء)",
    "ch_in": (
        "أرسل القناة بالصيغة:\n@username\n"
        "أو للقناة الخاصة:\n-100xxxxxxxxxx | https://t.me/+رابط_الدعوة\n"
        "يجب أن يكون البوت مشرفاً فيها.\n(/cancel للإلغاء)"
    ),
    "pub_ch": "أرسل معرّف قناة النشر، مثل @channel.\nيجب أن يكون البوت مشرفاً فيها ولديه صلاحية النشر.\n(/cancel للإلغاء)",
    "usr_find": "أرسل معرّف المستخدم الرقمي في تيليجرام.\n(/cancel للإلغاء)",
    "ui_chan": "أرسل رابط القناة الذي يفتحه زر «قناتنا»، مثل https://t.me/channel_name.\n(/cancel للإلغاء)",
    "cb_new": "أرسل الزر الجديد بالصيغة:\nاسم الزر | المحتوى الذي يظهر عند الضغط\n(/cancel للإلغاء)",
    "restore": "أرسل ملف النسخة الاحتياطية (.db) كمستند.\nستُطبَّق الاستعادة عند إعادة تشغيل البوت.\n(/cancel للإلغاء)",
}


def prompt_for(verb: str, arg: str) -> str:
    if verb == "cfg":
        spec = TUNABLES[arg]
        return f"أرسل قيمة «{spec['label']}» (بين {spec['lo']:g} و {spec['hi']:g}).\n(/cancel للإلغاء)"
    if verb == "src_edit":
        return "أرسل الاسم الجديد والرابط الجديد بالصيغة:\nالاسم | https://الرابط\n(/cancel للإلغاء)"
    if verb == "tpl":
        return (f"أرسل النص الجديد لـ «{TEXT_TITLES.get(arg, arg)}».\n"
                "يمكنك استخدام <b>عريض</b> و<i>مائل</i> و<code>كود</code>، وإرسال إيموجي مميزة داخل النص مباشرة.\n"
                "(/cancel للإلغاء)")
    if verb == "lbl":
        return ("أرسل الاسم الجديد للزر (حتى 40 حرفاً). يمكن أن يحتوي على إيموجي عادية.\n"
                "لإيموجي مميزة (Premium) على الزر: ابدأ الاسم بها مباشرة ثم اكتب النص، "
                "وستظهر كأيقونة قبل اسم الزر (تيليجرام يسمح بأيقونة واحدة فقط لكل زر).\n(/cancel للإلغاء)")
    if verb in ("cb_body", "cb_label"):
        what = "المحتوى" if verb == "cb_body" else "الاسم"
        return f"أرسل {what} الجديد للزر المخصص.\n(/cancel للإلغاء)"
    return INPUT_PROMPTS[verb]


def owner_only(handler):
    """Lets the call through only for owner IDs. Everyone else is silently ignored."""

    @functools.wraps(handler)
    async def wrapper(update: Update, context: ContextTypes.DEFAULT_TYPE):
        user = update.effective_user
        if user is None or user.id not in _svc(context).settings.owner_ids:
            if update.callback_query is not None:
                await update.callback_query.answer()
            return None
        _svc(context).owner_premium = bool(getattr(user, "is_premium", False))
        return await handler(update, context)

    return wrapper


def _numeric(arg: str) -> int | None:
    return int(arg) if arg.isdigit() else None


DELETE_QUESTIONS = {
    "uireset": "استعادة كل تخصيص الواجهة إلى الافتراضي",
    "src": "حذف مصدر الجمع",
    "ch": "حذف القناة من الاشتراك الإجباري",
    "px": "حذف هذا البروكسي نهائياً",
    "cb": "حذف هذا الزر المخصص",
    "emo": "حذف هذه الإيموجي من المكتبة",
    "blk": "حظر هذا المستخدم",
}


async def _ask_confirm(kind: str, arg: str) -> tuple[str, InlineKeyboardMarkup]:
    question = DELETE_QUESTIONS[kind]
    if kind == "blk":
        text = msg("msg_confirm_block", id=arg)
        yes_data = f"o:blk:{arg}"
        back = "o:s:users"
    else:
        text = f"{question}\n{msg('msg_confirm_delete')}"
        yes_data = f"o:del:{kind}:{arg}"
        back = {"src": "o:s:sources", "ch": "o:s:subscription", "px": "o:pg:0",
                "cb": "o:ui_btns", "emo": "o:ui_emoji", "uireset": "o:s:ui"}[kind]
    markup = InlineKeyboardMarkup([
        [ob("o_confirm", yes_data)],
        [ob("o_cancel", back)],
    ])
    return text, markup


async def _delete_confirmed(svc: Services, kind: str, pid: int) -> tuple[str, InlineKeyboardMarkup]:
    r = svc.repo
    if kind == "src":
        await r.delete_source(pid)
        return await render_section(svc, "sources")
    if kind == "ch":
        await r.delete_channel(pid)
        return await render_section(svc, "subscription")
    if kind == "px":
        await r.delete_proxy(pid)
        return await render_browse(svc, 0)
    if kind == "cb":
        await r.delete_custom_button(pid)
        await r.delete_setting(f"menu_hidden:c{pid}")
        await STORE.reload(r)
        return await view_user_buttons(svc)
    if kind == "uireset":
        for key in list(STORE.settings):
            if key.startswith(("tpl:", "btn:", "menu_", "slot:")) or key in ("owner_order", "layout_cols", "channel_link"):
                await r.delete_setting(key)
        await STORE.reload(r)
        await r.add_event("INFO", "bot", "أُعيد ضبط تخصيص الواجهة إلى الافتراضي")
        return await view_user_buttons(svc)
    if kind == "emo":
        await r.delete_emoji(pid)
        for name in DEFAULT_SLOTS:
            if STORE.settings.get(f"slot:{name}") == str(pid):
                await r.delete_setting(f"slot:{name}")
        await STORE.reload(r)
        return await view_emojis(svc)
    return await render_section(svc, "sources")


async def _act(svc: Services, context: ContextTypes.DEFAULT_TYPE, verb: str,
               args: list[str]) -> tuple[str | Rendered, InlineKeyboardMarkup] | None:
    """Applies one owner action and returns the view to show afterwards, or None for unknown actions."""
    r = svc.repo
    arg = args[0] if args else ""
    pid = _numeric(arg)

    # ----- background work: trigger, report BUSY honestly -----
    if verb in ("chk", "collect", "pub_now", "bootstrap"):
        guard_name = {"chk": "validate", "collect": "collect", "pub_now": "publish", "bootstrap": "bootstrap"}[verb]
        if svc.guard.is_running(guard_name) and verb != "bootstrap":
            return msg("msg_busy"), owner_markup([], "o:s:proxies")
        if verb == "chk":
            svc.spawn(svc.jobs.validate())
            return await render_section(svc, "proxies")
        if verb == "collect":
            svc.spawn(svc.jobs.collect())
            return await render_section(svc, "sources")
        if verb == "pub_now":
            svc.spawn(svc.jobs.publish(manual=True))
            return await render_section(svc, "publishing")
        if verb == "bootstrap":
            await r.set_setting("bootstrap_state", "pending")
            await r.set_setting("bootstrap_round", "0")
            await r.add_event("INFO", "bootstrap", "أعاد المالك بدء التهيئة الأولية")
            svc.spawn(svc.jobs.bootstrap_tick())
            return await render_section(svc, "dash")

    if verb == "pub_t":
        await _toggle(r, "publish_enabled", "0")
        return await render_section(svc, "publishing")
    if verb == "sub_t":  # old buttons may still send this: the subscription cannot be switched off
        return await render_section(svc, "subscription")
    if verb == "bak":
        path = await svc.jobs.make_backup()
        owner = update_owner_id(context)
        if owner is not None:
            with open(path, "rb") as fh:
                await svc.bot.send_document(chat_id=owner, document=fh, filename=path.name,
                                            caption="💾 نسخة احتياطية من قاعدة البيانات")
        return await render_section(svc, "system")

    # ----- channel checks -----
    if verb == "ch_chk":
        lines = ["🔍 فحص القنوات وصلاحيات البوت", ""]
        channels = await r.list_channels()
        if not channels:
            lines.append("لا توجد قنوات مضافة.")
        checks = await asyncio.gather(*(bot_permissions(svc.bot, ch["chat_ref"]) for ch in channels))
        for ch, (_, status, _) in zip(channels, checks):
            lines.append(f"• {ch['title']} ({ch['chat_ref']}): {status}")
        pub = await r.get_setting("publish_channel")
        if pub:
            _, status, _ = await publish_permissions(svc.bot, pub)
            lines.append(f"• قناة النشر: {status}")
        return "\n".join(lines), owner_markup([], "o:s:subscription")

    if verb == "ch_t" and pid is not None:
        await r.toggle_channel(pid)
        return await render_section(svc, "subscription")
    if verb == "src_t" and pid is not None:
        await r.toggle_source(pid)
        return await render_source(svc, pid)
    if verb == "src_v" and pid is not None:
        return await render_source(svc, pid)
    if verb == "src_test" and pid is not None:
        source = await r.get_source(pid)
        if source is None:
            return await render_section(svc, "sources")
        result = await svc.jobs.collector.test_source(source)
        text, markup = await render_source(svc, pid)
        return f"{result}\n\n{text}", markup

    if verb == "pt" and pid is not None:
        await r.toggle_proxy(pid)
        return await render_proxy(svc, pid)
    if verb == "pv" and pid is not None:
        return await render_proxy(svc, pid)
    if verb == "chkp" and pid is not None:
        row = await r.get_proxy(pid)
        if row is not None:
            if svc.guard.is_running("validate"):
                return msg("msg_busy"), owner_markup([], f"o:pv:{pid}")
            await svc.guard.run("validate", lambda: svc.jobs.validator.check_rows([row]))
        return await render_proxy(svc, pid)
    if verb == "pg":
        return await render_browse(svc, int(arg) if arg.isdigit() else 0)
    if verb == "inactive":
        return await render_inactive(svc)

    if verb == "pub_prev":
        rendered, _ = await svc.jobs.publisher.preview()
        if rendered is None:
            return msg("no_proxies"), owner_markup([], "o:s:publishing")
        return with_prefix("👀 معاينة المنشور كما سيظهر في القناة:\n\n", rendered), \
            owner_markup([], "o:s:publishing")
    if verb == "pub_hist":
        tz = svc.settings.timezone
        rows = await r.recent_publish_log(12)
        lines = ["🧾 سجل النشر والأخطاء", ""]
        if not rows:
            lines.append("لا يوجد سجل نشر بعد.")
        for row in rows:
            lines.append(f"• {fmt_time(row['created_at'], tz)} — {row['outcome']}"
                         f"{' (بروكسي ' + str(row['proxy_id']) + ')' if row['proxy_id'] else ''}"
                         f" {row['detail'] or ''}".rstrip())
        return "\n".join(lines), owner_markup([], "o:s:publishing")

    if verb == "usr_v" and pid is not None:
        return await render_user(svc, pid)
    if verb == "usr_list":
        return await render_blocked(svc)
    if verb == "blk" and pid is not None:
        await r.set_blocked(pid, True)
        await r.add_event("INFO", "bot", f"تم حظر المستخدم {pid} من لوحة التحكم")
        return await render_user(svc, pid)
    if verb == "unb" and pid is not None:
        await r.set_blocked(pid, False)
        await r.add_event("INFO", "bot", f"تم رفع الحظر عن المستخدم {pid}")
        return await render_user(svc, pid)

    # ----- customization -----
    if verb == "ui_msgs":
        return await view_messages(svc, int(arg) if arg.isdigit() else 0)
    if verb == "ui_msg" and arg in TEXT_TITLES:
        return await view_message(svc, arg)
    if verb == "ui_reset_tpl" and arg in TEXT_TITLES:
        await r.delete_setting(f"tpl:{arg}")
        await STORE.reload(r)
        await r.add_event("INFO", "bot", f"أُعيدت رسالة «{TEXT_TITLES[arg]}» إلى الافتراضي")
        return await view_message(svc, arg)
    if verb == "ui_btns":
        return await view_user_buttons(svc)
    if verb == "ui_mv" and len(args) == 2:
        valid = USER_BUILTINS + [f"c{b['id']}" for b in STORE.custom]
        return await _move_item(svc, "menu_order", valid, arg, int(args[1]), view_user_buttons)
    if verb == "ui_vis" and arg:
        return await _toggle_visible(svc, arg)
    if verb == "ui_lay":
        await r.set_setting("layout_cols", "1" if STORE.cols() == 2 else "2")
        await STORE.reload(r)
        return await view_user_buttons(svc)
    if verb == "ui_cb" and pid is not None:
        return await view_custom_button(svc, pid)
    if verb == "ui_owner":
        return await view_owner_buttons(svc)
    if verb == "ui_omv" and len(args) == 2:
        return await _move_item(svc, "owner_order", OWNER_SECTION_KEYS, arg, int(args[1]), view_owner_buttons)
    if verb == "ui_emoji":
        return await view_emojis(svc)
    if verb == "ui_slot" and arg in DEFAULT_SLOTS:
        return await view_slot_choice(svc, arg)
    if verb == "ui_slotset" and len(args) == 2 and args[0] in DEFAULT_SLOTS and args[1].isdigit():
        if int(args[1]) in STORE.emojis:
            await r.set_setting(f"slot:{args[0]}", args[1])
            await STORE.reload(r)
        return await view_emojis(svc)
    if verb == "ui_slotclr" and arg in DEFAULT_SLOTS:
        await r.delete_setting(f"slot:{arg}")
        await STORE.reload(r)
        return await view_emojis(svc)

    if verb == "ask" and len(args) == 2 and args[0] in DELETE_QUESTIONS:
        return await _ask_confirm(args[0], args[1])
    if verb == "del" and len(args) == 2 and args[1].isdigit():
        return await _delete_confirmed(svc, args[0], int(args[1]))

    if verb == "reset_all_ui":
        for key in ("layout_cols", "menu_order", "owner_order", "channel_link"):
            await r.delete_setting(key)
        for key in list(STORE.settings):
            if key.startswith(("tpl:", "btn:", "menu_hidden:", "slot:")):
                await r.delete_setting(key)
        await STORE.reload(r)
        await r.add_event("INFO", "bot", "أُعيد ضبط تخصيص الواجهة إلى الافتراضي")
        return await view_user_buttons(svc)
    return None


def update_owner_id(context: ContextTypes.DEFAULT_TYPE) -> int | None:
    svc = _svc(context)
    return min(svc.settings.owner_ids) if svc.settings.owner_ids else None


async def _toggle(repo: Repository, key: str, default: str) -> None:
    current = await repo.get_setting(key, default)
    await repo.set_setting(key, "0" if current == "1" else "1")


async def _move_item(svc: Services, setting: str, valid: list[str], key: str, step: int,
                     view: Callable[[Services], Awaitable[tuple]]) -> tuple:
    """Moves one entry up (-1) or down (+1) in an order list, then shows the list again."""
    if key in valid:
        keys = ordered_keys(valid, STORE.settings.get(setting, ""))
        if key in keys:
            index = keys.index(key)
            target = index + step
            if 0 <= target < len(keys):
                keys[index], keys[target] = keys[target], keys[index]
                await svc.repo.set_setting(setting, ",".join(keys))
                await STORE.reload(svc.repo)
    return await view(svc)


async def _toggle_visible(svc: Services, key: str) -> tuple:
    """Shows or hides a main-menu button. The last visible button cannot be hidden."""
    r = svc.repo
    hidden_now = STORE.settings.get(f"menu_hidden:{key}") == "1"
    if not hidden_now:
        visible_now = [item.key for item in user_menu_items()]
        if visible_now == [key]:
            return await view_user_buttons(svc)
    await r.set_setting(f"menu_hidden:{key}", "0" if hidden_now else "1")
    await STORE.reload(r)
    return await view_user_buttons(svc)


async def apply_preview(svc: Services, kind: str, target: str, value: str) -> str:
    """Saves a previewed change and returns the Arabic confirmation."""
    r = svc.repo
    if kind == "tpl":
        await r.set_setting(f"tpl:{target}", value)
    elif kind == "btn":
        await r.set_setting(f"btn:{target}", value)
    elif kind == "obtn":
        await r.set_setting(f"btn:o_{target}", value)
    elif kind == "cb_body":
        await r.update_custom_button(int(target), body=value)
    elif kind == "cb_label":
        await r.update_custom_button(int(target), label=value)
    elif kind == "channel_link":
        await r.set_setting("channel_link", value)
    await STORE.reload(r)
    await r.add_event("INFO", "bot", f"تم تحديث {kind} من لوحة التحكم")
    return msg("msg_saved")


@timed("owner_callback")
@owner_only
async def on_owner_callback(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    parts = (query.data or "").split(":")
    verb = parts[1] if len(parts) > 1 else ""
    args = parts[2:]
    svc = _svc(context)
    svc.spawn(_ack(query, TOASTS.get(verb)))  # answered in parallel with the work

    if verb == "menu":
        await render(update, context, MENU_TEXT, menu_markup())
        return
    if verb == "s":
        key = args[0] if args else ""
        if key in SECTIONS:
            text, keyboard = await render_section(svc, key)
            await render(update, context, text, keyboard)
        return
    if verb == "cancel":
        context.user_data.pop("preview", None)
        context.user_data.pop("await", None)
        await render(update, context, MENU_TEXT, menu_markup())
        return
    if verb == "apply" and args:
        preview = context.user_data.get("preview")
        if not preview or preview.get("token") != args[0]:
            await render(update, context, msg("msg_invalid") + "\n\n" + MENU_TEXT, menu_markup())
            return
        context.user_data.pop("preview", None)
        async with svc.owner_lock:
            message = await apply_preview(svc, preview["kind"], preview["target"], preview["value"])
            view = await _back_view_after_apply(svc, preview["kind"], preview["target"])
        await render(update, context, with_prefix(message + "\n\n", view[0]), view[1])
        return
    if verb == "ui_prev_tpl" and args:
        key = args[0]
        if key in TEXT_TITLES:
            preview = rich_text(key, SAMPLE_VARIABLES)
            await query.message.reply_text(
                "👀 هكذا ستظهر الرسالة للمستخدم (بيانات تجريبية):",
            )
            await reply_rendered(query.message, preview)
        return
    if verb == "ui_emotest":
        await _emoji_test(svc, query)
        return
    if verb == "ui_reset_tpl" and args and args[0] in TEXT_TITLES:
        async with svc.owner_lock:
            view = await _act(svc, context, verb, args)
        await render(update, context, *view)
        return
    if verb in ("ui_slot", "ui_slotset", "ui_slotclr"):
        if verb == "ui_slot":  # read-only view: no lock needed
            view = await _act(svc, context, verb, args)
        else:
            async with svc.owner_lock:
                view = await _act(svc, context, verb, args)
        if view is not None:
            await render(update, context, *view)
        return
    if verb == "restore":
        context.user_data["await"] = {"verb": "restore", "arg": ""}
        await query.message.reply_text(INPUT_PROMPTS["restore"])
        return
    if verb == "in":
        if not args:
            return
        input_verb = args[0]
        input_arg = args[1] if len(args) > 1 else ""
        if input_verb == "cfg" and input_arg not in TUNABLES:
            return
        if input_verb == "tpl" and input_arg not in TEXT_TITLES:
            return
        if input_verb == "lbl" and input_arg not in DEFAULT_LABELS:
            return
        if input_verb not in INPUT_PROMPTS and input_verb not in (
                "cfg", "tpl", "lbl", "src_edit", "cb_body", "cb_label"):
            return
        context.user_data["await"] = {"verb": input_verb, "arg": input_arg}
        await query.message.reply_text(prompt_for(input_verb, input_arg))
        return

    if verb in READ_ONLY_VERBS:  # navigation never waits for another owner change
        view = await _act(svc, context, verb, args)
    else:
        async with svc.owner_lock:
            view = await _act(svc, context, verb, args)
    if view is not None:
        await render(update, context, *view)


READ_ONLY_VERBS = frozenset({
    "ch_chk", "src_v", "src_test", "pv", "pg", "inactive", "pub_prev", "pub_hist", "usr_v", "usr_list",
    "ui_msgs", "ui_msg", "ui_btns", "ui_cb", "ui_owner", "ui_emoji", "ask", "chkp",
})


SAMPLE_VARIABLES: dict[str, Any] = {
    "id": "12", "status": "✅ عامل", "last_ok": "2026-11-16 10:00", "discovered": Ref("proxy_discovered"),
    "disc_time": "2026-11-15 08:00", "page": "1", "pages": "3", "warning": Ref("proxy_warning"),
    "footer": Ref("footer"), "working": "20", "target": "100", "checked_today": "45",
    "verified_24h": "7", "daily_goal": "20", "last_check": "2026-11-16 10:00",
    "names": "قناة مثال", "count": "20", "goal": "20", "target_count": "20",
}


async def _back_view_after_apply(svc: Services, kind: str, target: str) -> tuple:
    if kind in ("tpl",):
        return await view_message(svc, target)
    if kind in ("cb_body", "cb_label"):
        return await view_custom_button(svc, int(target))
    if kind in ("btn",):
        return await view_user_buttons(svc)
    if kind == "obtn":
        return await view_owner_buttons(svc)
    return await render_section(svc, "ui")


# ----- guided text inputs -----
# Each input handler returns (reply, keyboard). The reply may be plain text or Rendered text.

async def _in_proxy_search(svc, context, text, arg):
    return await render_search(svc, text)


async def _in_source(svc, context, text, arg):
    if "|" in text:
        name, url = (part.strip() for part in text.split("|", 1))
    else:
        name, url = "", text.strip()
    problem = await validate_source_url(url)
    if problem:
        return f"⚠️ الرابط غير مقبول: {problem}.", owner_markup([], "o:s:sources")
    name = (name or urlsplit(url).netloc)[:80]
    new_id = await svc.repo.add_source(name, url)
    if new_id is None:
        return "⚠️ هذا الرابط مضاف مسبقاً.", owner_markup([], "o:s:sources")
    await svc.repo.add_event("INFO", "collect", f"أُضيف مصدر جديد: {name}")
    return "✅ تمت إضافة المصدر، وسيُجمع منه في الدورة القادمة.", owner_markup([], "o:s:sources")


async def _in_source_edit(svc, context, text, arg):
    source_id = int(arg) if arg.isdigit() else None
    if source_id is None or await svc.repo.get_source(source_id) is None:
        return msg("msg_not_found"), owner_markup([], "o:s:sources")
    if "|" not in text:
        return "⚠️ أرسل الاسم والرابط بالصيغة: الاسم | https://الرابط", owner_markup([], f"o:src_v:{source_id}")
    name, url = (part.strip() for part in text.split("|", 1))
    if not name or len(name) > 80:
        return "⚠️ الاسم يجب أن يكون بين حرف و80 حرفاً.", owner_markup([], f"o:src_v:{source_id}")
    problem = await validate_source_url(url)
    if problem:
        return f"⚠️ الرابط غير مقبول: {problem}.", owner_markup([], f"o:src_v:{source_id}")
    if not await svc.repo.update_source(source_id, name, url):
        return "⚠️ هذا الرابط مستخدم بالفعل في مصدر آخر.", owner_markup([], f"o:src_v:{source_id}")
    await svc.repo.add_event("INFO", "collect", f"عُدّل المصدر إلى: {name}")
    return msg("msg_saved"), owner_markup([], f"o:src_v:{source_id}")


async def _in_channel(svc, context, text, arg):
    if "|" in text:
        ref, link = (part.strip() for part in text.split("|", 1))
    else:
        ref, link = text.strip(), ""
    ok, status, info = await bot_permissions(svc.bot, ref)
    if info is None:
        return f"⚠️ تعذّر الوصول إلى القناة. تأكد من المعرّف. ({status})", owner_markup([], "o:s:subscription")
    if not ok:
        return f"⚠️ {status}. أضف البوت مشرفاً ثم أعد المحاولة.", owner_markup([], "o:s:subscription")
    join_url = link or (f"https://t.me/{info['username']}" if info["username"] else "")
    if not join_url:
        return "⚠️ القناة الخاصة تحتاج رابط دعوة بعد علامة |", owner_markup([], "o:s:subscription")
    if not valid_channel_link(join_url):
        return "⚠️ رابط القناة غير صالح. استخدم https://t.me/name أو رابط الدعوة https://t.me/+...", \
            owner_markup([], "o:s:subscription")
    if not await svc.repo.add_channel(str(info["id"]), info["title"][:60], join_url):
        return "⚠️ هذه القناة مضافة مسبقاً.", owner_markup([], "o:s:subscription")
    return f"✅ تمت إضافة القناة: {info['title']}", owner_markup([], "o:s:subscription")


async def _in_publish_channel(svc, context, text, arg):
    ok, status, info = await publish_permissions(svc.bot, text.strip())
    if info is None or not ok:
        return f"⚠️ {status}", owner_markup([], "o:s:publishing")
    r = svc.repo
    await r.set_setting("publish_channel", str(info["id"]))
    return f"✅ تم تحديد قناة النشر: {info['title']}", owner_markup([], "o:s:publishing")


async def _in_tunable(svc, context, text, arg):
    value = parse_tunable(arg, text)
    spec = TUNABLES[arg]
    back = "o:s:publishing" if arg == "publish_interval_min" else "o:s:validation"
    if value is None:
        return (f"⚠️ القيمة غير صالحة. أدخل رقماً بين {spec['lo']:g} و {spec['hi']:g}.",
                owner_markup([], back))
    await svc.repo.set_setting(f"cfg:{arg}", value)
    await apply_intervals(svc)
    return f"✅ تم حفظ «{spec['label']}»: {value:g}", owner_markup([], back)


async def _in_user_find(svc, context, text, arg):
    if not text.isdigit():
        return "⚠️ أدخل معرّفاً رقمياً صحيحاً.", owner_markup([], "o:s:users")
    return await render_user(svc, int(text))


async def _in_channel_link(svc, context, text, arg):
    if not valid_channel_link(text):
        return "⚠️ أرسل رابطاً مثل https://t.me/channel_name", owner_markup([], "o:ui_msgs:0")
    return await _stage_preview(context, "channel_link", "channel_link", text, "o:s:ui")


async def _stage_preview(context, kind: str, target: str, value: str, back: str):
    """Shows what the change will look like, with Apply and Cancel. Nothing is saved yet."""
    token = secrets.token_hex(4)
    context.user_data["preview"] = {"token": token, "kind": kind, "target": target, "value": value}
    preview = render_template(value, SAMPLE_VARIABLES)
    return with_prefix("👀 معاينة قبل الحفظ:\n\n", preview), InlineKeyboardMarkup(
        _preview_rows(token) + [[ob("o_back", back)]])


async def _in_template(svc, context, text, arg):
    if not text:
        return msg("msg_invalid"), owner_markup([], "o:ui_msgs:0")
    if len(text) > 3000:
        return "⚠️ النص طويل جداً (الحد 3000 حرف).", owner_markup([], f"o:ui_msg:{arg}")
    preview = render_template(text, SAMPLE_VARIABLES)
    token = secrets.token_hex(4)
    context.user_data["preview"] = {"token": token, "kind": "tpl", "target": arg, "value": text}
    header = f"👀 معاينة «{TEXT_TITLES[arg]}» (بيانات تجريبية) قبل الحفظ:\n\n"
    shifted = [{**e, "offset": e["offset"] + utf16_len(header)} for e in preview.entities]
    return Rendered(header + preview.text, shifted), InlineKeyboardMarkup(
        _preview_rows(token) + [[ob("o_back", f"o:ui_msg:{arg}")]])


async def _in_label(svc, context, text, arg, kind: str, back: str):
    prefix, body = normalize_label(text)
    if not body or len(body) > 40:
        return "⚠️ الاسم يجب أن يكون بين حرف و40 حرفاً (مع نص بعد الإيموجي).", owner_markup([], back)
    return await _stage_preview(context, kind, arg, prefix + body, back)


async def _in_any_label(svc, context, text, arg):
    if arg not in DEFAULT_LABELS:
        return msg("msg_not_found"), owner_markup([], "o:ui_btns")
    back = "o:ui_owner" if arg.startswith("o_") else "o:ui_btns"
    return await _in_label(svc, context, text, arg, "btn", back)


async def _in_owner_label(svc, context, text, arg):
    if arg not in OWNER_SECTION_KEYS:
        return msg("msg_not_found"), owner_markup([], "o:ui_owner")
    return await _in_label(svc, context, text, arg, "obtn", "o:ui_owner")


async def _in_cb_new(svc, context, text, arg):
    if "|" not in text:
        return "⚠️ الصيغة: اسم الزر | المحتوى", owner_markup([], "o:ui_btns")
    label, body = (part.strip() for part in text.split("|", 1))
    icon, label = normalize_label(label)
    if not label or len(label) > 40 or not body or len(body) > 2000:
        return "⚠️ الاسم حتى 40 حرفاً، والمحتوى حتى 2000 حرف.", owner_markup([], "o:ui_btns")
    new_id = await svc.repo.add_custom_button(icon + label, body)
    await STORE.reload(svc.repo)
    await svc.repo.add_event("INFO", "bot", f"أُضيف زر مخصص: {label}")
    return f"✅ تمت إضافة الزر «{label}». يمكنك تعديل محتواه ومكانه من القائمة.", \
        owner_markup([[ob("o_edit", f"o:ui_cb:{new_id}")]], "o:ui_btns")


async def _in_cb_body(svc, context, text, arg):
    if not arg.isdigit() or not text or len(text) > 2000:
        return "⚠️ المحتوى حتى 2000 حرف.", owner_markup([], "o:ui_btns")
    return await _stage_preview(context, "cb_body", arg, text, f"o:ui_cb:{arg}")


async def _in_cb_label(svc, context, text, arg):
    prefix, body = normalize_label(text)
    if not arg.isdigit() or not body or len(body) > 40:
        return "⚠️ الاسم حتى 40 حرفاً.", owner_markup([], "o:ui_btns")
    return await _stage_preview(context, "cb_label", arg, prefix + body, f"o:ui_cb:{arg}")


async def _in_src_edit_dispatch(svc, context, text, arg):
    return await _in_source_edit(svc, context, text, arg)


TEXT_ACTIONS: dict[str, Callable[..., Awaitable[tuple]]] = {
    "px_in": _in_proxy_search,
    "src_in": _in_source,
    "src_edit": _in_src_edit_dispatch,
    "ch_in": _in_channel,
    "pub_ch": _in_publish_channel,
    "cfg": _in_tunable,
    "usr_find": _in_user_find,
    "ui_chan": _in_channel_link,
    "tpl": _in_template,
    "lbl": _in_any_label,
    "cb_new": _in_cb_new,
    "cb_body": _in_cb_body,
    "cb_label": _in_cb_label,
}


@owner_only
async def on_owner_text(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    message = update.effective_message
    if message is None:
        return
    svc = _svc(context)
    text = message.text or ""
    has_premium = any(e.type == "custom_emoji" for e in (message.entities or []))
    pending = context.user_data.get("await")

    if pending is None:
        if has_premium:
            # No input is waiting: read each custom_emoji_id from the MessageEntity and store it.
            tokenized = await tokenize_custom_emojis(svc.repo, text, message.entities)
            await STORE.reload(svc.repo)
            saved = list(dict.fromkeys(re.findall(r"\[\[e(\d+)\]\]", tokenized)))
            shown_ids = " ".join(f"[[e{i}]] #{i}" for i in saved)
            await reply_rendered(
                message,
                render_template(
                    f"✅ تم حفظ {len(saved)} إيموجي مميزة في المكتبة (معرّفها الحقيقي من تيليجرام):\n{shown_ids}\n\n"
                    "افتح 🎭 الإيموجي المميزة لتعيينها إلى المواضع أو استخدامها داخل الرسائل."),
                InlineKeyboardMarkup([[ob("o_emoji", "o:ui_emoji")]]),
            )
        return

    if pending["verb"] == "restore":
        await message.reply_text(INPUT_PROMPTS["restore"])
        return

    context.user_data.pop("await", None)
    if has_premium:
        text = await tokenize_custom_emojis(svc.repo, text, message.entities)
        await STORE.reload(svc.repo)
    handler = TEXT_ACTIONS.get(pending["verb"])
    if handler is None:
        return
    reply, keyboard = await handler(svc, context, text.strip(), pending["arg"])
    await reply_rendered(message, reply, keyboard)


@owner_only
async def on_owner_sticker(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """A Premium custom emoji sent as a sticker (e.g. from an emoji pack) is stored the same way."""
    message = update.effective_message
    sticker = message.sticker if message is not None else None
    if sticker is None or not getattr(sticker, "custom_emoji_id", None):
        return
    svc = _svc(context)
    emoji_id = await svc.repo.save_emoji(sticker.custom_emoji_id, sticker.emoji or "⭐")
    await STORE.reload(svc.repo)
    await reply_rendered(
        message,
        render_template(f"✅ تم حفظ الإيموجي المميزة في المكتبة:\n[[e{emoji_id}]] #{emoji_id}\n\n"
                        "افتح 🎭 الإيموجي المميزة لتعيينها."),
        InlineKeyboardMarkup([[ob("o_emoji", "o:ui_emoji")]]),
    )


@owner_only
async def on_owner_document(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Receives a backup file for restore. The file is checked before it is staged."""
    message = update.effective_message
    pending = context.user_data.get("await")
    if message is None or message.document is None or pending is None or pending["verb"] != "restore":
        return
    svc = _svc(context)
    doc = message.document
    if not (doc.file_name or "").lower().endswith((".db", ".sqlite", ".sqlite3")):
        await message.reply_text("⚠️ الملف يجب أن يكون قاعدة بيانات بامتداد .db")
        return
    if (doc.file_size or 0) > 50 * 1024 * 1024:
        await message.reply_text("⚠️ الملف أكبر من 50 ميغابايت.")
        return
    staged = svc.settings.db_path + ".restore"
    tg_file = await doc.get_file()
    await tg_file.download_to_drive(staged)
    problem = check_backup_file(staged)
    if problem:
        Path(staged).unlink(missing_ok=True)
        await message.reply_text(f"⚠️ لم تُستخدم هذه النسخة: {problem}.")
        return
    context.user_data.pop("await", None)
    await svc.repo.add_event("WARNING", "bot", "رفع المالك ملف استعادة. ستُطبَّق عند إعادة التشغيل.")
    await message.reply_text(
        "✅ تم استلام ملف الاستعادة وفحصه. ستُطبَّق الاستعادة عند إعادة تشغيل البوت، "
        "والقاعدة الحالية تُحفظ بجانبها قبل الاستبدال.",
    )


# ----- commands -----

@owner_only
async def cmd_panel(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    context.user_data.pop("await", None)
    await update.effective_message.reply_text(MENU_TEXT, reply_markup=menu_markup())


@owner_only
async def cmd_cancel(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    context.user_data.pop("await", None)
    context.user_data.pop("preview", None)
    await update.effective_message.reply_text(msg("msg_cancelled"))


# =============================================================================
# 17. Application wiring and entry point
# =============================================================================

def setup_logging(log_file: str) -> None:
    Path(log_file).parent.mkdir(parents=True, exist_ok=True)
    logging.basicConfig(
        level=logging.INFO,
        format="%(asctime)s %(levelname)s %(name)s: %(message)s",
        handlers=[
            logging.StreamHandler(),
            RotatingFileHandler(log_file, maxBytes=5_000_000, backupCount=3, encoding="utf-8"),
        ],
    )
    logging.getLogger("httpx").setLevel(logging.WARNING)


async def _seed_initial_sources(svc: Services) -> None:
    """On the very first start only (no sources yet), adds the sources listed in INITIAL_SOURCES.

    These are the owner's own approved sources from the environment. The bot never invents sources."""
    if (await svc.repo.source_counts())["total"]:
        return
    for url in svc.settings.initial_sources:
        name = urlsplit(url).netloc[:80]
        await svc.repo.add_source(name, url)
        await svc.repo.add_event("INFO", "collect", f"أُضيف مصدر مبدئي من الإعدادات: {name}")


async def _archive_old_channel_post(svc: Services) -> None:
    """Version 2 kept one post that it edited in place. Version 3 posts one proxy per cycle instead.

    The old post is replaced with a neutral note, so it cannot keep showing a stale proxy list."""
    old = await svc.repo.get_setting("last_publish_message_id")
    channel = await svc.repo.get_setting("publish_channel")
    if not old or not channel:
        return
    try:
        await svc.bot.edit_message_text(
            chat_id=chat_key(channel), message_id=int(old),
            text="ℹ️ لم يعد هذا المنشور يُحدَّث. تُنشر البروكسيات الآن واحداً كل فترة، ويظهر كل بروكسي في منشور مستقل.",
        )
        await svc.repo.add_event("INFO", "publish", "أُرشف منشور القائمة القديم في القناة")
    except TelegramError as exc:
        await svc.repo.add_event("WARNING", "publish", f"تعذّر أرشفة المنشور القديم: {type(exc).__name__}")
    await svc.repo.delete_setting("last_publish_message_id")
    await svc.repo.delete_setting("last_publish_hash")


async def on_startup(app: Application) -> None:
    global STORE
    settings: Settings = app.bot_data["settings"]
    db = Database(settings.db_path)
    await db.connect()
    repo = Repository(db)
    http = httpx.AsyncClient(
        timeout=20.0,
        follow_redirects=False,  # redirects are followed by hand, with a safety check on each hop
        headers={"User-Agent": "proxy-aggregator-bot/3.0"},
    )
    svc = Services(settings=settings, db=db, repo=repo, http=http, bot=app.bot)
    me = await app.bot.get_me()
    svc.bot_username = me.username or ""
    app.bot_data["svc"] = svc

    STORE = UIStore(settings.channel_link)
    await STORE.reload(repo)
    await _seed_initial_sources(svc)
    await _archive_old_channel_post(svc)

    start_scheduler(svc)
    await apply_intervals(svc)
    if not await repo.get_setting("bootstrap_state"):
        await repo.set_setting("bootstrap_state", "pending")
    await repo.add_event("INFO", "start", "بدأ تشغيل البوت وأُعيدت جدولة المهام")
    log.info("bot started as @%s", svc.bot_username)


async def on_shutdown(app: Application) -> None:
    svc: Services | None = app.bot_data.get("svc")
    if svc is None:
        return
    stop_scheduler(svc)
    pending = list(svc.background)
    for task in pending:
        task.cancel()
    if pending:
        await asyncio.gather(*pending, return_exceptions=True)
    await svc.http.aclose()
    await svc.db.close()


async def on_error(update: object, context) -> None:
    log.error("unhandled error", exc_info=context.error)
    svc: Services | None = context.application.bot_data.get("svc")
    if svc is not None:
        try:
            await svc.repo.add_event("ERROR", "bot", f"خطأ غير متوقع: {type(context.error).__name__}")
        except Exception:  # noqa: BLE001
            log.exception("could not record the error event")
    if isinstance(update, Update) and update.callback_query is not None:
        try:
            await update.callback_query.answer(msg("error_generic"))
        except TelegramError:
            pass


def build_application(settings: Settings) -> Application:
    app = (
        Application.builder()
        .token(settings.bot_token)
        .concurrent_updates(True)  # one slow handler must never block other users
        .connection_pool_size(256)
        .post_init(on_startup)
        .post_shutdown(on_shutdown)
        .build()
    )
    app.bot_data["settings"] = settings
    app.add_handler(CommandHandler("start", cmd_start))
    app.add_handler(CommandHandler("panel", cmd_panel))
    app.add_handler(CommandHandler("cancel", cmd_cancel))
    app.add_handler(CallbackQueryHandler(on_user_callback, pattern=r"^(m|sub):"))
    app.add_handler(CallbackQueryHandler(on_owner_callback, pattern=r"^o:"))
    app.add_handler(MessageHandler(filters.Document.ALL, on_owner_document))
    app.add_handler(MessageHandler(filters.Sticker.ALL, on_owner_sticker))
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, on_owner_text))
    app.add_error_handler(on_error)
    return app


def main() -> None:
    try:
        settings = load_settings()
    except ConfigError as exc:
        raise SystemExit(f"إعدادات غير صالحة:\n{exc}\nأصلح المتغيرات في البيئة ثم أعد التشغيل.") from None
    setup_logging(settings.log_file)
    restored = apply_staged_restore(settings.db_path)
    if restored:
        logging.getLogger("proxy_bot").warning(restored)
    build_application(settings).run_polling(allowed_updates=Update.ALL_TYPES)


if __name__ == "__main__":
    main()
