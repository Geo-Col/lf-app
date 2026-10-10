#!/usr/bin/env python3
"""
Loot Farmer - Clash of Clans farming bot for BlueStacks (ADB).

How it works
------------
Every loop it takes ONE screenshot, works out which screen the game is on
(home, attack menu, army, scouting, battle, surrender dialog, battle end)
from your captured button templates, and does the right thing for that
screen. Because it always looks before it taps, it can pick up from any
screen - after a popup, a lag spike, a game restart or an emulator restart.

Unrecognised screen for a while -> press Back -> relaunch the game ->
(if enabled) restart the emulator. It never gives up, it just backs off.

Run:           python bot.py
Self-check:    python bot.py --selftest
Old version:   bot_old.py (untouched backup)
"""
import importlib.util
import subprocess
import sys


def _ensure(pkgs):
    missing = [pip for mod, pip in pkgs.items() if importlib.util.find_spec(mod) is None]
    if missing:
        print("Installing:", ", ".join(missing))
        subprocess.check_call([sys.executable, "-m", "pip", "install", *missing])


_ensure({"cv2": "opencv-python", "PIL": "Pillow", "numpy": "numpy", "sv_ttk": "sv-ttk",
         "pytesseract": "pytesseract"})

import base64
import collections
import ctypes
import difflib
import glob
import hashlib
import http.server
import json
import logging
import logging.handlers
import os
import platform
import queue
import re
import secrets
import shutil
import socket
import struct
import tempfile
import threading
import time
import traceback
import tkinter as tk
import tkinter.font as tkfont
import urllib.error
import urllib.request
import zipfile
from tkinter import messagebox, ttk

import cv2
import numpy as np
import sv_ttk
from PIL import Image, ImageTk

try:
    import pytesseract
    HAVE_TESS = True
except ImportError:
    HAVE_TESS = False

# ---------------------------------------------------------------------------
# Paths, constants, config
# ---------------------------------------------------------------------------
APP_VERSION = 50  # bumped by `python bot.py --publish`; friends get an Update button when GitHub has a higher one
APP_ID = "GeoCol.LootFarmer"  # Windows taskbar identity (window + Start menu / desktop shortcuts)
UPDATE_REPO = "Geo-Col/lf-app"  # was Geo-Col/LootFarmer (GitHub redirects the old name)
BASE_DIR = os.path.dirname(os.path.abspath(__file__))
TEMPLATE_DIR = os.path.join(BASE_DIR, "templates")
CONFIG_FILE = os.path.join(BASE_DIR, "config.json")
LOG_FILE = os.path.join(BASE_DIR, "bot.log")
# Shipped inside the bot folder so nothing needs installing (used when the configured path doesn't exist)
BUNDLED = {"adb_path": os.path.join(BASE_DIR, "platform-tools", "adb.exe"),
           "tesseract_path": os.path.join(BASE_DIR, "Tesseract-OCR", "tesseract.exe")}
os.makedirs(TEMPLATE_DIR, exist_ok=True)
NO_WINDOW = 0x08000000 if os.name == "nt" else 0  # no console flash per adb call

BUTTONS = [
    ("attack_button", "Attack! (home screen)"),
    ("find_match_button", "Find a Match"),
    ("confirm_attack_button", "Attack! (green, army screen)"),
    ("next_button", "Next (skip base)"),
    ("surrender_button", "Surrender / End Battle"),
    ("surrender_confirm_button", "Okay (confirm surrender)"),
    ("return_home_button", "Return Home"),
    ("upgrade_more_button", "Upgrade More (wall selected)  - walls"),
    ("upgrade_more_disabled", "Upgrade More greyed out (only wall of its level)  - walls"),
    ("wall_upgrade_hammers", "Upgrade More bar: double-hammer icon  - walls"),
    ("wall_okay_button", "Upgrade Walls dialog: Okay  - walls"),
    ("confirm_wall_upgrade_button", "Upgrade window: green Confirm  - upgrades"),
    ("building_upgrade_button", "Selected building's Upgrade button  - upgrades"),
    ("settings_cog_button", "Settings cog (home)  - accounts"),
    ("switch_account_button", "Blue switch-account button  - accounts"),
    ("supercell_id_header", "Supercell ID panel logo  - accounts"),
    ("lab_picker_title", "Lab 'Choose what to upgrade' title  - upgrades"),
    ("guardians_title", "'Guardians' window title  - upgrades"),
    ("reload_game", "'Anyone there?' disconnect: RELOAD GAME  - recovery"),
    ("bb_boat", "Boat's sail bubble (both villages)  - builder base"),
    ("bb_attack_button", "Builder Base Attack! (axes)  - builder base"),
    ("bb_find_now", "Builder Base Find Now!  - builder base"),
    ("bb_return_home", "Builder Base Return Home  - builder base"),
    ("bb_elixir_bubble", "Builder Base elixir bubble  - builder base"),
    ("bb_gold_bubble", "Builder Base gold bubble  - builder base"),
    ("bb_cart", "Elixir Cart, full (by the dock)  - builder base"),
    ("chest_room", "Chest event: the chest room (left wall)  - events"),
    ("loading_logo", "Loading screen: Clash of Clans logo  - recovery"),
    ("loading_text", "Loading screen: 'Loading' bar text  - recovery"),
    ("popup_close", "A window's red X close button  - recovery"),
    ("all_upgrades_complete", "'All Upgrades Complete' (maxed village)  - upgrades"),
    ("live_replay", "'Live Replay' (an attack on us, shown at login)  - recovery"),
    ("replay_return_home", "Return Home after that replay  - recovery"),
    ("chest_skip", "Chest event: the chest room's Skip  - events"),
    ("chest_continue", "Chest event: reward Continue  - events"),
    ("bb_cart_title", "Elixir Cart window title  - builder base"),
    ("bb_cart_collect", "Elixir Cart green Collect  - builder base"),
    ("bb_bonus_title", "'Star Bonus!' popup title  - builder base"),
    ("bb_bonus_okay", "Star Bonus popup Okay  - builder base"),
    ("bb_gem_bubble", "Gem Mine gem bubble  - builder base"),
    ("bb_clock_bubble", "Clock Tower boost-ready bubble  - builder base"),
    ("bb_free_boost", "Clock Tower 'Free Boost!' button  - builder base"),
    ("bb_boost_title", "'Free Boost!' window title  - builder base"),
    ("bb_boost_button", "'Free Boost!' window green Boost  - builder base"),
]
REQUIRED_BUTTONS = [n for n, _ in BUTTONS[:7]]
OCR_REGIONS = [
    ("loot_gold_region", "Available loot - gold"),
    ("loot_elixir_region", "Available loot - elixir"),
    ("damage_percent_region", "Overall damage %"),
    ("bank_gold_region", "Your storage - gold"),
    ("bank_elixir_region", "Your storage - elixir"),
    ("bank_dark_region", "Your storage - dark elixir"),
]
POINTS = [
    ("deploy_point", "Troop drop point (line start)"),
    ("deploy_line_end", "Troop line end (same side of the base)"),
    ("spell_point", "Spell line start (optional)"),
    ("spell_line_end", "Spell line end (optional)"),
]
# Checked in this order; first template above the confidence wins. Overlays
# and more specific screens come before the screens they sit on top of
# (e.g. scouting shows Next AND End Battle, so Next must win).
STATES = [
    ("return_home_button", "END"),
    ("next_button", "SCOUT"),
    ("confirm_attack_button", "ARMY"),
    ("find_match_button", "MENU"),
    ("surrender_button", "BATTLE"),
    ("attack_button", "HOME"),
    ("bb_return_home", "BBEND"),   # started / restarted while on the Builder Base: finish up and sail home
    ("bb_attack_button", "BBHOME"),
]
STATE_LABELS = {
    None: "Unknown screen", "HOME": "Home village", "MENU": "Attack menu", "ARMY": "Army screen",
    "SCOUT": "Scouting base", "BATTLE": "In battle", "CONFIRM": "Surrendering", "END": "Battle over",
    "BBHOME": "Builder Base", "BBEND": "Builder Base battle over",
}

DEFAULTS = {
    "adb_path": r"C:\Program Files\platform-tools\adb.exe",
    "device": "",
    "auto_connect_target": "127.0.0.1:5555",
    "match_confidence": 0.7,
    "min_screenshot_interval": 0.4,
    "tap_delay": 0.5,
    "loot_force_attack": False,
    "loot_gold_threshold": 700000,
    "loot_elixir_threshold": 700000,
    "loot_require_both": False,
    "loot_settle_delay": 2.5,
    "loot_recheck_delay": 1.5,
    "loot_max_plausible": 20000000,
    "surrender_damage_threshold": 50,
    "damage_confirm_count": 2,
    "battle_max_wait": 180,
    "damage_stall_seconds": 20,
    "timer_poll_interval": 2.0,
    "hold_deploy": True,
    "deploy_pan": "top-left",  # pan the camera into this corner before deploying ("off" to disable)
    "hero_abilities": True,
    "hero_ability_delay": 10,
    "deploy_spells": False,
    "rotate_accounts": False,
    "stop_when_all_busy": True,
    "accounts": "",
    "hold_ms_per_troop": 120,
    "deploy_speed": "Fastest",  # troop/spell placing: see DEPLOY_SPEEDS
    "matchmaking_settle_delay": 2.0,
    "return_home_delay": 3.0,
    "bank_spend_enabled": False,
    "builder_upgrades_enabled": False,
    "skip_town_hall": True,
    "lab_upgrades_enabled": False,
    "builder_base_enabled": False,  # visit the Builder Base on every account: collect, cart, upgrades, daily stars
    "bb_visit_hours": 3,
    "bb_attacks_enabled": True,
    "bb_builder_upgrades": True,
    "bb_lab_upgrades": True,
    "bb_bonus_days": {},  # account -> date its daily Star Bonus was collected (no more attacks that day)
    "bank_spend_threshold": 15000000,
    "bank_scroll_duration_ms": 600,
    "bank_scroll_delay": 0.6,
    "bank_post_spend_delay": 1.0,
    "watchdog_enabled": True,
    "gfx_profile": 0,  # which GFX_PROFILES entry BlueStacks runs with; moved on automatically after crashes
    "emulator_exe_path": "",
    "discord_webhook": "https://discord.com/api/webhooks/1541513961076293833/CtGCtGAaIJxf-MD68mBWdj6uZJ0Sf6x_E4Cj5bKIlmOsAoBgg91-1_IIqJ5s8V1olDQ7",  # the Anywhere link is posted here on every start
    "emulator_launch_args": "",
    "coc_package_name": "com.supercell.clashofclans",
    "coc_activity_name": "com.supercell.titan.GameApp",
    "watchdog_attack_timeout": 60,
    "game_launch_wait": 25,
    "emulator_boot_wait": 40,
    "adb_ready_timeout": 90,
    "tesseract_path": r"C:\Program Files\Tesseract-OCR\tesseract.exe",
    "ocr_region_padding_px": 4,
    "ocr_min_digits": 3,
    "groq_api_key": "",
    "groq_model": "",
    "use_groq_for_loot": True,
    "use_groq_for_bank": True,
    "groq_supervisor": True,
    "phone_view_enabled": True,
    "phone_view_port": 8765,
    "phone_view_key": "",  # random secret generated on first run; the phone link must include it
    "public_link_enabled": True,  # needs cloudflared.exe next to bot.py
    "coords": {},
    "ocr_regions": {},
    "fixed_points": {},
}

# Troop / spell placing speed: (pause between taps, pause after picking a card) in seconds. 'Fastest' = the army
# down in ~1 s; slower ones help a slow PC / emulator that drops taps.
DEPLOY_SPEEDS = {"Fastest": (0.0, 0.1), "Fast": (0.05, 0.15), "Normal": (0.12, 0.25), "Slow": (0.25, 0.4)}
# (group, blurb, [(key, label, type)]) - type: bool/int/float/str/"secret", or a tuple of choices (dropdown)
SETTINGS = [
    ("Loot", "Which bases are worth attacking.", [
        ("loot_force_attack", "Attack every base (skip loot check)", bool),
        ("loot_require_both", "Require gold AND elixir (off = either)", bool),
        ("loot_gold_threshold", "Minimum gold", int),
        ("loot_elixir_threshold", "Minimum elixir", int),
        ("loot_settle_delay", "Wait before first read (s)", float),
        ("loot_recheck_delay", "Wait after Next (s)", float),
        ("loot_max_plausible", "Ignore reads above", int),
    ]),
    ("Battle", "Deploying and surrendering.", [
        ("deploy_spells", "Also drop spells at the drop point", bool),
        ("deploy_speed", "Troop & spell placing speed", tuple(DEPLOY_SPEEDS)),
        ("deploy_pan", "Camera corner before deploying", ("top-left", "top-right", "bottom-left", "bottom-right", "off")),
        ("hero_abilities", "Use hero abilities", bool),
        ("hero_ability_delay", "Use abilities this long after deploying (s)", float),
        ("hold_deploy", "Hold-to-deploy (single drop spot only)", bool),
        ("surrender_damage_threshold", "Surrender at damage %", float),
        ("damage_confirm_count", "Damage reads in a row", int),
        ("damage_stall_seconds", "Surrender if damage stalls for (s)", float),
        ("battle_max_wait", "Surrender after (s) regardless", float),
        ("timer_poll_interval", "Damage check every (s)", float),
        ("hold_ms_per_troop", "Hold time per troop (ms)", int),
    ]),
    ("Upgrades", "From the home screen: free builders and the lab take the most expensive thing you can "
                 "afford; walls use storage above the threshold.", [
        ("builder_upgrades_enabled", "Builders: upgrade buildings / heroes", bool),
        ("skip_town_hall", "Never upgrade the Town Hall (don't rush)", bool),
        ("lab_upgrades_enabled", "Lab: research troops / spells", bool),
        ("bank_spend_enabled", "Buy walls when storage is full", bool),
        ("bank_spend_threshold", "Spend when storage >=", int),
        ("bank_scroll_duration_ms", "List swipe duration (ms)", int),
        ("bank_scroll_delay", "Pause after swipe (s)", float),
        ("bank_post_spend_delay", "Pause after purchase (s)", float),
    ]),
    ("Builder Base", "Each account gets a visit by boat: collect the collectors and the Elixir Cart, then the "
                     "switches below. Same on/off as the dashboard's Builder Base switch.", [
        ("builder_base_enabled", "Visit the Builder Base", bool),
        ("bb_attacks_enabled", "Attack until the daily Star Bonus", bool),
        ("bb_builder_upgrades", "Builders: upgrade buildings / Battle Machine", bool),
        ("bb_lab_upgrades", "Star Lab: research", bool),
        ("bb_visit_hours", "Revisit each account every (h)", float),
    ]),
    ("Accounts", "When every enabled builder + lab slot is busy (and walls are spent), switch to the next "
                 "Supercell ID account. All busy everywhere = keep farming here and re-check in 30 min.", [
        ("rotate_accounts", "Rotate accounts", bool),
        ("stop_when_all_busy", "Stop the bot when every account is busy", bool),
        ("accounts", "Only these (comma list, blank = all)", str),
    ]),
    ("Recovery", "Game relaunch is always on. Emulator restart needs the .exe path.", [
        ("watchdog_enabled", "Allow emulator restart", bool),
        ("gfx_profile", "BlueStacks graphics fallback (0 = as set; rises after crashes)", int),
        ("emulator_exe_path", "Emulator .exe", str),
        ("emulator_launch_args", "Emulator launch args", str),
        ("coc_package_name", "Game package", str),
        ("coc_activity_name", "Game activity", str),
        ("watchdog_attack_timeout", "Stuck-screen timeout (s)", float),
        ("game_launch_wait", "Game load wait (s)", float),
        ("emulator_boot_wait", "Emulator boot wait (s)", float),
        ("adb_ready_timeout", "ADB ready timeout (s)", float),
    ]),
    ("Engine", "Recognition, OCR and connection.", [
        ("groq_supervisor", "Groq fixes unknown screens and popups", bool),
        ("use_groq_for_loot", "Groq reads base loot (Tesseract backup)", bool),
        ("use_groq_for_bank", "Groq reads your storage (Tesseract backup)", bool),
        ("match_confidence", "Button match confidence (0-1)", float),
        ("min_screenshot_interval", "Min gap between screenshots (s)", float),
        ("tap_delay", "Pause after button tap (s)", float),
        ("ocr_region_padding_px", "OCR box padding (px)", int),
        ("ocr_min_digits", "OCR minimum digits", int),
        ("tesseract_path", "tesseract.exe", str),
        ("phone_view_enabled", "Phone live view (restart app to apply)", bool),
        ("phone_view_port", "Phone view port", int),
        ("public_link_enabled", "Public phone link (restart app)", bool),
        ("adb_path", "adb.exe", str),
        ("auto_connect_target", "Auto-connect address", str),
        ("groq_api_key", "Groq API key", "secret"),
        ("groq_model", "Groq vision model", str),
    ]),
]

RUNTIME_KEYS = ("scans", "plans", "account_tags", "_last_account_idx", "loot_rate", "line_view", "ui_mode",
                "sc_of_tag", "shortcuts_v", "sc_accounts")  # saved by the bot, not settings
# Rarely-touched tuning: shown under 'Show advanced settings'
ADVANCED = {"loot_settle_delay", "loot_recheck_delay", "loot_max_plausible", "hold_deploy", "damage_confirm_count",
            "timer_poll_interval", "hold_ms_per_troop",
            "bank_scroll_duration_ms", "bank_scroll_delay", "bank_post_spend_delay", "gfx_profile",
            "emulator_launch_args", "coc_package_name", "coc_activity_name", "watchdog_attack_timeout",
            "game_launch_wait", "emulator_boot_wait", "adb_ready_timeout", "match_confidence",
            "min_screenshot_interval", "tap_delay", "ocr_region_padding_px", "ocr_min_digits", "tesseract_path",
            "phone_view_port", "adb_path", "auto_connect_target", "groq_model"}
_cfg_lock = threading.Lock()


def load_config():
    cfg, err = json.loads(json.dumps(DEFAULTS)), None
    try:
        if os.path.exists(CONFIG_FILE):
            with open(CONFIG_FILE, encoding="utf-8") as f:
                cfg.update(json.load(f))
    except Exception as e:  # keep a copy: the next save would otherwise replace it with defaults
        try:
            shutil.copy2(CONFIG_FILE, CONFIG_FILE + ".broken")
        except OSError:
            pass
        err = f"config.json couldn't be read ({e}); running on defaults. The old file is kept as config.json.broken."
    for k in [k for k in cfg if k not in DEFAULTS and k not in RUNTIME_KEYS]:
        del cfg[k]  # settings of removed features: dropped on the next save
    tagged = set((cfg.get("account_tags") or {}).values())
    misread = lambda a: a not in tagged and difflib.get_close_matches(a, tagged, 1, 0.75)
    for k in ("scans", "plans", "bb_bonus_days"):  # nothing filed under an unreadable / misread account name
        cfg[k] = {a: v for a, v in (cfg.get(k) or {}).items() if a not in ("", "?") and not misread(a)}
    for k in ("coords", "ocr_regions", "fixed_points"):
        cfg[k] = cfg.get(k) or {}
    for k, path in BUNDLED.items():
        if not (cfg.get(k) and os.path.exists(cfg[k])) and os.path.exists(path):
            cfg[k] = path
    cfg["bb_bonus_days"] = dict(cfg.get("bb_bonus_days") or {})
    cfg["discord_webhook"] = cfg.get("discord_webhook") or DEFAULTS["discord_webhook"]  # blank saved = the built-in
    player = r"C:\Program Files\BlueStacks_nxt\HD-Player.exe"
    if not os.path.isfile(cfg.get("emulator_exe_path") or "") and os.path.isfile(player):
        cfg["emulator_exe_path"] = player  # so crash recovery can restart BlueStacks
    return cfg, err


def save_config(cfg):
    """Atomic write: a kill mid-save can't corrupt config.json. The day's first save keeps yesterday's file in
    backups/ (last 7 days), so settings / drop lines / plans can always be got back."""
    with _cfg_lock:
        try:
            bdir = os.path.join(BASE_DIR, "backups")
            day = os.path.join(bdir, f"config-{time.strftime('%Y-%m-%d')}.json")
            if os.path.exists(CONFIG_FILE) and not os.path.exists(day):
                os.makedirs(bdir, exist_ok=True)
                shutil.copy2(CONFIG_FILE, day)
                for old in sorted(f for f in os.listdir(bdir) if f.startswith("config-"))[:-7]:
                    os.remove(os.path.join(bdir, old))
        except OSError:
            pass  # a backup problem must never stop the save
        tmp = CONFIG_FILE + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(cfg, f, indent=2)
        for i in range(10):  # antivirus / OneDrive can hold the file for a moment
            try:
                return os.replace(tmp, CONFIG_FILE)
            except PermissionError:
                if i == 9:
                    raise
                time.sleep(0.3)


def tpath(name):
    return os.path.join(TEMPLATE_DIR, f"{name}.png")


log_file = logging.getLogger("lootfarmer")
log_file.setLevel(logging.INFO)
_fh = logging.handlers.RotatingFileHandler(LOG_FILE, maxBytes=2_000_000, backupCount=2, encoding="utf-8")
_fh.setFormatter(logging.Formatter("%(asctime)s %(levelname)s %(message)s"))
log_file.addHandler(_fh)


# ---------------------------------------------------------------------------
# ADB
# ---------------------------------------------------------------------------
class ADBError(Exception):
    pass


def decode_raw(data):
    """Raw `screencap` output: 12 or 16 byte header (w, h, fmt[, colorspace]) + RGBA.
    Skipping the device-side PNG encode is the single biggest speed/CPU win."""
    if not data or len(data) < 16:
        return None
    w, h = struct.unpack_from("<II", data)
    n = w * h * 4
    if not w or not h or len(data) - n not in (12, 16):
        return None
    rgba = np.frombuffer(data, np.uint8, n, len(data) - n).reshape(h, w, 4)
    return cv2.cvtColor(rgba, cv2.COLOR_RGBA2BGR)


def _pipe_reader(pipe, q):
    for line in iter(pipe.readline, b""):
        q.put(line)
    q.put(None)


class ADB:
    """Screenshots via exec-out raw; input via ONE persistent `adb shell`
    instead of spawning adb.exe for every tap."""

    def __init__(self, path, device):
        self.path, self.device = path, device
        self._sh = self._q = None
        self._n = 0
        self._lock = threading.Lock()
        self._persist_ok = True
        self._persist_fails = 0

    def _cmd(self, *a):
        return [self.path, *(["-s", self.device] if self.device else []), *a]

    def run(self, *a, timeout=15):
        try:
            return subprocess.run(self._cmd(*a), capture_output=True, timeout=timeout, creationflags=NO_WINDOW)
        except FileNotFoundError:
            raise ADBError(f"adb.exe not found at '{self.path}'")
        except OSError as e:
            raise ADBError(f"couldn't run adb.exe: {e}")
        except subprocess.TimeoutExpired:
            raise ADBError(f"adb {' '.join(a[:2])} timed out")

    def host(self, *a, timeout=15):
        try:
            r = subprocess.run([self.path, *a], capture_output=True, text=True, timeout=timeout,
                               creationflags=NO_WINDOW)
        except FileNotFoundError:
            raise ADBError(f"adb.exe not found at '{self.path}'")
        except OSError as e:
            raise ADBError(f"couldn't run adb.exe: {e}")
        except subprocess.TimeoutExpired:
            raise ADBError(f"adb {a[0]} timed out")
        return (r.stdout + r.stderr).strip()

    def devices(self):
        lines = self.host("devices", timeout=10).splitlines()[1:]
        return [p[0] for p in (ln.split() for ln in lines) if len(p) >= 2 and p[1] == "device"]

    def connect(self, target):
        return self.host("connect", target, timeout=10)

    def close_shell(self):
        with self._lock:
            self._kill()

    def _kill(self):
        if self._sh:
            try:
                self._sh.kill()
            except Exception:
                pass
        self._sh = None

    def _persistent(self, cmd, timeout):
        with self._lock:
            if self._sh is None or self._sh.poll() is not None:
                try:
                    self._sh = subprocess.Popen(self._cmd("shell"), stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                                stderr=subprocess.STDOUT, creationflags=NO_WINDOW)
                except OSError as e:
                    raise ADBError(f"couldn't start adb shell: {e}")
                self._q = queue.Queue()
                threading.Thread(target=_pipe_reader, args=(self._sh.stdout, self._q), daemon=True).start()
            self._n += 1
            tag = f"@@{self._n}@@"  # sent as "@@"N"@@" so a tty echo of the command can't match it
            try:
                self._sh.stdin.write(f'{cmd}; echo "@@"{self._n}"@@"\n'.encode())
                self._sh.stdin.flush()
            except OSError:
                self._kill()
                raise ADBError("adb shell closed")
            out, deadline = [], time.time() + timeout
            while True:
                try:
                    line = self._q.get(timeout=max(0.05, deadline - time.time()))
                except queue.Empty:
                    if time.time() >= deadline:
                        self._kill()
                        raise ADBError(f"adb shell timed out ({cmd[:40]})")
                    continue
                if line is None:
                    self._kill()
                    raise ADBError("adb shell disconnected")
                s = line.decode(errors="replace").rstrip("\r\n")
                if tag in s:
                    return "\n".join(out)
                out.append(s)

    def shell(self, cmd, timeout=10):
        if self._persist_ok:
            try:
                out = self._persistent(cmd, timeout)
                self._persist_fails = 0
                return out
            except ADBError:
                self._persist_fails += 1
        r = self.run("shell", cmd, timeout=timeout)
        if r.returncode != 0 and not r.stdout:
            raise ADBError((r.stderr or b"adb shell failed").decode(errors="replace").strip()[:120])
        if self._persist_fails >= 3:  # device answers, persistent shell doesn't: stop using it
            self._persist_ok = False
        return r.stdout.decode(errors="replace")

    def screenshot(self):
        img = decode_raw(self.run("exec-out", "screencap", timeout=20).stdout)  # slow while the emulator boots
        if img is None:
            png = self.run("exec-out", "screencap", "-p", timeout=10).stdout
            img = cv2.imdecode(np.frombuffer(png, np.uint8), cv2.IMREAD_COLOR) if png else None
        if img is None:
            raise ADBError("screenshot failed - is the emulator running?")
        return img

    def tap(self, x, y):
        self.shell(f"input tap {int(x)} {int(y)}")

    def swipe(self, x1, y1, x2, y2, ms):
        self.shell(f"input swipe {int(x1)} {int(y1)} {int(x2)} {int(y2)} {int(ms)}", timeout=10 + ms / 1000)

    def back(self):
        self.shell("input keyevent 4")

    def ready(self):
        try:
            return "ok" in self.run("shell", "echo", "ok", timeout=5).stdout.decode(errors="replace")
        except ADBError:
            return False


# ---------------------------------------------------------------------------
# Vision + OCR
# ---------------------------------------------------------------------------
SCALE = 0.5  # match at half resolution: ~4x faster, still precise to a couple of px


class Vision:
    def __init__(self, tdir=TEMPLATE_DIR):
        self.tdir = tdir
        self._t, self._alts = {}, {}
        self._frame = self._small = None

    def template(self, name):
        p = os.path.join(self.tdir, f"{name}.png")
        try:
            m = os.path.getmtime(p)
        except OSError:
            return None
        c = self._t.get(name)
        if c is None or c[0] != m:
            img = cv2.imread(p, cv2.IMREAD_COLOR)
            if img is None:
                return None
            c = (m, img.shape[:2], cv2.resize(img, None, fx=SCALE, fy=SCALE, interpolation=cv2.INTER_AREA))
            self._t[name] = c
        return c

    def score(self, frame, name):
        """(score, cx, cy) of the best match in full-res coords, or None if no template. '<name>_alt*' templates
        are other looks of the same button (Attack! with an event chest on it, Claim Reward for Return Home...)."""
        alts = [n[:-4] for n in self._alts.setdefault(name, sorted(
            os.path.basename(f) for f in glob.glob(os.path.join(self.tdir, name + "_alt*.png"))))]
        found = [r for r in [self._score(frame, name)] + [self._score(frame, n) for n in alts] if r]
        return max(found) if found else None

    def _score(self, frame, name):
        t = self.template(name)
        if t is None:
            return None
        if self._frame is not frame:
            self._frame, self._small = frame, cv2.resize(frame, None, fx=SCALE, fy=SCALE,
                                                         interpolation=cv2.INTER_AREA)
        s, tt = self._small, t[2]
        if tt.shape[0] > s.shape[0] or tt.shape[1] > s.shape[1]:
            return None
        _, v, _, loc = cv2.minMaxLoc(cv2.matchTemplate(s, tt, cv2.TM_CCOEFF_NORMED))
        (h, w) = t[1]
        return v, int(loc[0] / SCALE + w / 2), int(loc[1] / SCALE + h / 2)

    def find(self, frame, name, conf):
        r = self.score(frame, name)
        return (r[1], r[2]) if r and r[0] >= conf else None

    def undimmed(self, frame, name, hit):
        """Template matching ignores brightness, so a button under a popup's dark overlay still 'matches'.
        Clean screens measure 0.97-1.0 of the template's brightness, overlaid ones 0.3-0.5."""
        t = self.template(name)
        h, w = t[1]
        x, y = hit[0] - w // 2, hit[1] - h // 2
        patch = frame[max(0, y):y + h, max(0, x):x + w]
        return patch.size > 0 and patch.mean() >= 0.8 * t[2].mean()


def crop(frame, bbox, pad=0):
    x0, y0, x1, y1 = bbox
    h, w = frame.shape[:2]
    x0, y0, x1, y1 = max(0, x0 - pad), max(0, y0 - pad), min(w, x1 + pad), min(h, y1 + pad)
    return frame[y0:y1, x0:x1] if x1 > x0 and y1 > y0 else None


def ocr_number(frame, bbox, pad=4, min_digits=1, thorough=True):
    """Digits-only OCR. One cheap Tesseract pass; if that fails, a 12-pass vote
    (thorough) or just one inverted pass (fast polling, e.g. damage %)."""
    c = crop(frame, bbox, pad)
    if not HAVE_TESS or c is None:
        return None
    gray = cv2.cvtColor(cv2.resize(c, None, fx=4, fy=4, interpolation=cv2.INTER_CUBIC), cv2.COLOR_BGR2GRAY)
    gray = cv2.bilateralFilter(gray, 5, 40, 40)
    otsu = cv2.threshold(gray, 0, 255, cv2.THRESH_BINARY + cv2.THRESH_OTSU)[1]

    def read(img, psm):
        try:
            txt = pytesseract.image_to_string(
                img, config=f"--psm {psm} -c tessedit_char_whitelist=0123456789", timeout=5)
        except Exception:
            return None
        d = re.sub(r"\D", "", txt)
        return int(d) if len(d) >= min_digits else None

    v = read(otsu, 7)
    if v is not None or not thorough:
        return v if v is not None else read(cv2.bitwise_not(otsu), 7)
    variants = [otsu, cv2.bitwise_not(otsu),
                cv2.adaptiveThreshold(gray, 255, cv2.ADAPTIVE_THRESH_GAUSSIAN_C, cv2.THRESH_BINARY, 31, 5),
                cv2.dilate(otsu, np.ones((2, 2), np.uint8))]
    results = [r for img in variants for psm in (7, 8, 6) if (r := read(img, psm)) is not None]
    if not results:
        return None
    counts = {r: results.count(r) for r in results}
    best = max(counts.values())
    return max((r for r, n in counts.items() if n == best), key=lambda r: len(str(r)))


_groq = {}
GROQ_W = 960  # screenshots go to Groq at 960px wide: fast upload, still readable

GROQ_SCREENS = {"home": "HOME", "attack_menu": "MENU", "army": "ARMY", "scouting": "SCOUT",
                "battle": "BATTLE", "battle_end": "END"}  # dialogs are never auto-confirmed
# Never let the AI tap anything that could spend gems/money.
GROQ_BLOCKED = ("gem", "buy", "purchase", "shop", "offer", "boost", "upgrade", "train", "pass", "spend",
                "$", "\u00a3", "\u20ac", "pay", "store")

RESCUE_PROMPT = """This is a WxH screenshot of Clash of Clans running in an emulator, sent by a bot that \
farms loot. The bot doesn't recognise this screen. Reply with ONLY this JSON:
{"screen": "home|attack_menu|army|scouting|battle|surrender_dialog|battle_end|loading|popup|other",
 "button": [x, y] or null, "action": "tap|back|wait|relaunch", "target": "text on what to tap", "reason": "few words"}
"button" is in this image's pixels. For these screens give the centre of the key button: home = orange \
"Attack!" (bottom-left); attack_menu = "Find a Match"; army = green "Attack!"; scouting = "Next"; \
battle = "Surrender" or "End Battle"; surrender_dialog = "Okay"; battle_end = "Return Home".
Loading / connecting / clouds: action "wait". Any popup, news, reward, event, offer or dialog: action "tap" \
on its close "X", "Okay", "Close", "Later", "Continue", "Reload" or "Try Again". Exit-game dialog: tap "Cancel".
NEVER tap anything that spends gems or money or says Buy, Purchase, Shop, Boost, Upgrade or Train.
Black, frozen, Android home screen, crash dialog or not Clash of Clans: action "relaunch"."""
LOOT_PROMPT = """Clash of Clans scouting screen. Read the "Available Loot" numbers at the top-left: first row \
is gold (yellow coin), second row is elixir (pink drop). Reply with ONLY JSON \
{"gold": integer or null, "elixir": integer or null} - digits only, no separators."""
STORAGE_PROMPT = """Clash of Clans home village. Read the player's own storage totals at the top-right: \
gold (yellow coin) and elixir (pink drop). Reply with ONLY JSON {"gold": integer or null, "elixir": integer or null}."""
def groq_ask(cfg, frame, prompt, max_tokens=250):
    """Send a downscaled screenshot + prompt to a Groq vision model; returns the JSON dict or None."""
    key, model = cfg.get("groq_api_key"), cfg.get("groq_model")
    if not key or not model:
        return None
    try:
        from groq import Groq
    except ImportError:
        return None
    h = int(frame.shape[0] * GROQ_W / frame.shape[1])
    img = cv2.resize(frame, (GROQ_W, h), interpolation=cv2.INTER_AREA)
    try:
        client = _groq.get(key) or _groq.setdefault(key, Groq(api_key=key, timeout=15, max_retries=1))
        b64 = base64.b64encode(cv2.imencode(".jpg", img, [cv2.IMWRITE_JPEG_QUALITY, 85])[1].tobytes()).decode()
        r = client.chat.completions.create(
            model=model, temperature=0, max_completion_tokens=max_tokens, response_format={"type": "json_object"},
            messages=[{"role": "user", "content": [
                {"type": "text", "text": prompt.replace("WxH", f"{GROQ_W}x{h}")},
                {"type": "image_url", "image_url": {"url": f"data:image/jpeg;base64,{b64}"}}]}])
        out = json.loads(r.choices[0].message.content)
        return out if isinstance(out, dict) else None
    except Exception as e:
        log_file.warning(f"Groq request failed: {e}")
        _groq["last_error"] = str(e)
        return None


def as_int(v):
    try:
        return int(str(v).replace(",", "").replace(" ", "")) if v is not None else None
    except ValueError:
        return None


_DIGITS = {}


def digit_glyphs():
    """templates/digits.png: the game's own 0-9, 20x28 each, averaged from real screenshots."""
    if "t" not in _DIGITS:
        strip = cv2.imread(tpath("digits"), cv2.IMREAD_GRAYSCALE)
        _DIGITS["t"] = None if strip is None else [strip[:, i * 20:(i + 1) * 20].astype(np.float32) / 255
                                                    for i in range(10)]
    return _DIGITS["t"]


def read_digit_blobs(mask, suffix_ok=False):
    """Keep only digit-shaped blobs sitting in one row (drops icons, bar shine, stray highlights), then
    recognise each blob against the game's own digit shapes. No Tesseract: exact on every storage bar,
    list price and Confirm button tested (25/25, cross-validated), and ~100x faster."""
    n, lab, st, _ = cv2.connectedComponentsWithStats(mask.astype(np.uint8), 8)
    H, W = mask.shape
    comps = [i for i in range(1, n) if st[i, 3] >= H * 0.15 and st[i, 2] <= st[i, 3] * 1.3  # digit-shaped
             and st[i, 0] > 0 and st[i, 1] > 0 and st[i, 0] + st[i, 2] < W and st[i, 1] + st[i, 3] < H]
    glyphs = digit_glyphs()
    if not comps or glyphs is None:
        return None
    h = np.median([st[i, 3] for i in comps])
    comps = [i for i in comps if 0.6 * h <= st[i, 3] <= 1.4 * h]
    if not comps:
        return None
    cy = np.median([st[i, 1] + st[i, 3] / 2 for i in comps])  # one text line: drop shapes above/below it
    comps = sorted((i for i in comps if abs(st[i, 1] + st[i, 3] / 2 - cy) <= 0.5 * h), key=lambda i: st[i, 0])
    if not comps:  # nothing on one line (e.g. the loot numbers not drawn yet)
        return None
    runs, cur = [], [comps[0]]
    for a, b in zip(comps, comps[1:]):  # split where the gap is wider than a digit (e.g. before the icon)
        if st[b, 0] - (st[a, 0] + st[a, 2]) <= h:
            cur.append(b)
        else:
            runs.append(cur)
            cur = [b]
    runs.append(cur)
    out = ""
    for i in max(runs, key=len):
        x, y, w, hh = st[i, :4]
        g = cv2.resize((lab[y:y + hh, x:x + w] == i).astype(np.float32), (20, 28), interpolation=cv2.INTER_AREA)
        dist = [float(np.abs(g - glyphs[k]).mean()) for k in range(10)]
        if min(dist) > 0.15:  # not a digit (e.g. the 'd'/'H' of a timer): real digits match within ~0.06
            if suffix_ok and out:
                break  # a trailing '%' after the number
            return None
        out += str(dist.index(min(dist)))
    return int(out)


def damage_percent(frame, bbox):
    """'Overall Damage' number: white digits followed by '%'."""
    c = crop(frame, bbox, 0)
    if c is None:
        return None
    hsv = cv2.cvtColor(c, cv2.COLOR_BGR2HSV)
    v = read_digit_blobs((hsv[:, :, 2] > hsv[:, :, 2].max() * 0.8) & (hsv[:, :, 1] < 70), suffix_ok=True)
    return v if v is not None and v <= 100 else None


def white_number(frame, bbox):
    """The game's white counter digits (storage bars). Near-white is relative to the brightest pixel, so
    dimmed screens work too. 10/10 on real screenshots."""
    c = crop(frame, bbox, 0)
    if c is None:
        return None
    hsv = cv2.cvtColor(c, cv2.COLOR_BGR2HSV)
    return read_digit_blobs((hsv[:, :, 2] > hsv[:, :, 2].max() * 0.8) & (hsv[:, :, 1] < 70))


def panel_box(frame):
    """The builder/lab dropdown list has a pure-white 2px border: columns white for a long vertical run.
    Returns (x0, x1, y0, y1) of its inside, or None if no list is open."""
    g = cv2.cvtColor(frame, cv2.COLOR_BGR2GRAY)
    cols = np.where((g >= 245).sum(axis=0) > g.shape[0] * 0.3)[0]
    if len(cols) < 2:
        return None
    right = cols[cols - cols[0] >= 250]  # the list's right border is the NEXT long white column, not the last
    if len(right) == 0:                  # (the Builder Base has a white edge at the far right of the screen)
        return None
    x0, x1 = int(cols[0]), int(right[0])
    ys = np.where(g[:, x0] >= 245)[0]
    # the longest unbroken run is the list's own border (a button card below can line up with it)
    runs = np.split(ys, np.where(np.diff(ys) > 3)[0] + 1)
    run = max(runs, key=len)
    return x0 + 3, x1 - 2, int(run[0]) + 3, int(run[-1]) - 2


# Top bar counters sit in fixed places (1920x1080 layout) whatever icon/skin shows (builder, goblin, ...).
TOP_BAR = {"lab": ((662, 61), (680, 30, 820, 95), (600, 20, 680, 105)),
           "builder": ((902, 70), (955, 30, 1060, 95), (840, 20, 920, 105)),  # tap point, counter, icon
           "bb_lab": ((860, 60), (840, 30, 940, 95), (750, 20, 830, 105)),
           "bb_builder": ((1040, 60), (1080, 30, 1185, 95), (990, 20, 1075, 105))}
KIND_NAMES = {"builder": "Builder", "lab": "Lab", "bb_builder": "Builder Base builder", "bb_lab": "Star Lab"}
BB_STARS = (95, 866, 200, 910)  # the 'x/y' daily star counter on the Builder Base Attack button


def top_bar(frame, kind):
    """(tap point, counter box) of the lab or builder counter, scaled to this screen."""
    k = frame.shape[1] / 1920
    (x, y), box, _ = TOP_BAR[kind]
    return (int(x * k), int(y * k)), tuple(int(v * k) for v in box)


def goblin_icon(frame, kind):
    """The game shows the green goblin face on a counter only when the normal builders / researcher are all
    busy and just the goblin (costs gems) is free. Measured: goblin 0.33-0.36 green, normal icons <=0.12."""
    k = frame.shape[1] / 1920
    c = crop(frame, tuple(int(v * k) for v in TOP_BAR[kind][2]), 0)
    if c is None:
        return False
    hsv = cv2.cvtColor(c, cv2.COLOR_BGR2HSV)
    return float(((hsv[:, :, 0] >= 30) & (hsv[:, :, 0] <= 80) & (hsv[:, :, 1] > 90) & (hsv[:, :, 2] > 90)).mean()) > 0.22


def read_counter(frame, box):
    """'3/5' -> (3, 5). Anything that isn't a digit (the icon, the '/') splits the groups."""
    glyphs = digit_glyphs()
    c = crop(frame, box, 0)
    if c is None or glyphs is None:
        return None
    hsv = cv2.cvtColor(c, cv2.COLOR_BGR2HSV)
    m = ((hsv[:, :, 2] > hsv[:, :, 2].max() * 0.8) & (hsv[:, :, 1] < 70)).astype(np.uint8)
    n, lab, st, _ = cv2.connectedComponentsWithStats(m, 8)
    groups, cur = [], ""
    for i in sorted((i for i in range(1, n) if st[i, 3] >= m.shape[0] * 0.3), key=lambda i: st[i, 0]):
        x, y, w, h = st[i, :4]
        g = cv2.resize((lab[y:y + h, x:x + w] == i).astype(np.float32), (20, 28), interpolation=cv2.INTER_AREA)
        dist = [float(np.abs(g - glyphs[k]).mean()) for k in range(10)]
        if min(dist) <= 0.15:
            cur += str(dist.index(min(dist)))
        elif cur:
            groups.append(cur)
            cur = ""
    if cur:
        groups.append(cur)
    return (int(groups[0]), int(groups[1])) if len(groups) == 2 else None


def troop_bar(frame):
    """Cards on the battle bar, left to right: [(x, y, kind, count)]. Each card is found by its dark
    outline (two tall vertical edges one card-width apart). kind: 'troop' (blue card with a count),
    'spell' (purple card with a count), 'hero' (purple card, no count), 'single' (Clan Castle / siege machine:
    light blue, no count), 'used' (greyed x0),
    'empty' (dashed slot)."""
    glyphs = digit_glyphs()
    if glyphs is None:
        return []  # templates/digits.png missing
    H, W = frame.shape[:2]
    ya, yb = int(H * 0.833), int(H * 0.972)
    g = cv2.cvtColor(frame[ya:yb], cv2.COLOR_BGR2GRAY).astype(np.float32)
    col = (np.abs(cv2.Sobel(g, cv2.CV_32F, 1, 0, ksize=3)) > 60).mean(axis=0)
    peaks = []
    for x in range(1, W - 1):
        if col[x] > 0.55 and col[x] >= col[x - 1] and col[x] >= col[x + 1] and (not peaks or x - peaks[-1] >= 8):
            peaks.append(x)
    cw = int(W * 0.0685)  # card width, ~131px at 1920
    cards, end = [], -1
    bar_hsv = cv2.cvtColor(frame[ya:yb], cv2.COLOR_BGR2HSV)
    for a in peaks:
        if a <= end:
            continue
        inside = bar_hsv[:, a + 5:a + 12]
        if inside[:, :, 1].mean() > 100 and inside[:, :, 2].mean() < 110:
            continue  # dark blue bar background, not a card (e.g. a selected card's thick border)
        b = next((p for p in peaks if cw - 6 <= p - a <= cw + 16), None)  # +16: a selected card's white border
        if b:
            cards.append((a, b))
            end = b
    top = int(H * 0.826)

    def number(y0, y1, x0, x1, min_h):
        """White digits in this box (e.g. the 'x16' count, or the level badge), or None."""
        cc = cv2.cvtColor(frame[y0:y1, x0:x1], cv2.COLOR_BGR2HSV)
        cm = ((cc[:, :, 2] > 200) & (cc[:, :, 1] < 60)).astype(np.uint8)
        n, lab, st, _ = cv2.connectedComponentsWithStats(cm, 8)
        digits = ""
        for i in sorted((i for i in range(1, n) if st[i, 3] >= min_h), key=lambda i: st[i, 0]):
            x, y, w, h = st[i, :4]
            gl = cv2.resize((lab[y:y + h, x:x + w] == i).astype(np.float32), (20, 28), interpolation=cv2.INTER_AREA)
            dist = [float(np.abs(gl - glyphs[k]).mean()) for k in range(10)]
            if min(dist) <= 0.15:
                digits += str(dist.index(min(dist)))
            elif digits:
                break
        return int(digits) if digits else None

    def level_badge(a, b):
        """Every real card has a dark level badge bottom-left with white digits (a smaller font than the
        count, so just look for a digit-sized white blob on dark). A dashed empty slot showing the base doesn't."""
        x0, y0 = a + 2, int(H * 0.91)
        cc = cv2.cvtColor(frame[y0:int(H * 0.985), x0:a + (b - a) // 2], cv2.COLOR_BGR2HSV)
        white = ((cc[:, :, 2] > 200) & (cc[:, :, 1] < 60)).astype(np.uint8)
        n, _, st, _ = cv2.connectedComponentsWithStats(white, 8)
        for i in range(1, n):
            x, y, w, h = st[i, :4]
            if 0.013 * H <= h <= 0.02 * H and 3 <= w <= 0.016 * W:
                around = cc[max(0, y - 4):y + h + 4, max(0, x - 4):x + w + 4]
                dark = around[:, :, 2][around[:, :, 2] <= 200]
                if dark.size and float(dark.mean()) < 110:
                    return True
        return False

    out = []
    for a, b in cards:
        hsv = cv2.cvtColor(frame[ya:yb, a + 4:b - 4], cv2.COLOR_BGR2HSV)
        hue, sat, val = hsv[:, :, 0], hsv[:, :, 1], hsv[:, :, 2]
        colored = (sat > 90) & (val > 90) & ~((hue >= 30) & (hue <= 85))  # any card colour, not grass
        grey = (sat < 40) & (val > 60)
        cnt = number(top, top + 50, a + (b - a) // 3, b - 4, 18)  # 'x16' at the top-right, after the 'x'
        if cnt is None:  # a selected card sits ~15px higher
            cnt = number(top - int(H * 0.017), top + 35, a + (b - a) // 3, b - 4, 18)
        if cnt is None:  # busy card art (Lightning's bolts) can put an 'edge' inside the card, cutting the count
            cnt = number(top, top + 50, a + (b - a) // 3, min(W, b + int(W * 0.007)), 18)  # off: a spell without a
            # count would pass for a hero (tapped once as an 'ability' instead of cast)
        if grey.mean() > 0.4:
            kind = "used"
        elif cnt is None and (colored.mean() < 0.2 or not level_badge(a, b)):  # a count = a real card (event
            # troops have a grey card + an orange level badge)
            kind = "empty"
        elif cnt is None:  # no count: a hero (purple card) or the Clan Castle / siege machine (light blue card)
            edge = cv2.cvtColor(frame[int(H * 0.85):int(H * 0.95), a + 5:a + 14], cv2.COLOR_BGR2HSV)
            e = edge[:, :, 0][(edge[:, :, 1] > 90) & (edge[:, :, 2] > 90)]
            kind = "hero" if len(e) and 112 <= np.median(e) <= 160 else "single"  # CC ~94, heroes ~122-146
        else:
            hh = cv2.cvtColor(frame[top:top + 45, a + 6:a + (b - a) // 3], cv2.COLOR_BGR2HSV)
            hdr = hh[:, :, 0][(hh[:, :, 1] > 90) & (hh[:, :, 2] > 90)]
            hue = np.median(hdr) if len(hdr) else 0  # blue troop ~104, purple spell ~126, red SUPER troop ~179
            kind = "spell" if 115 <= hue <= 150 else "troop"
        out.append(((a + b) // 2, (ya + yb) // 2, kind, cnt))
    return out


def confirm_price(frame, hit):
    """Price on the upgrade window's green Confirm (hit = its 'Confirm' label). White normally; yellow when a
    discount applies - then the old price is printed struck-out underneath, so only the line right under the
    label is read."""
    k = frame.shape[1] / 1920
    v = white_number(frame, (hit[0] - int(160 * k), hit[1] + int(12 * k), hit[0] + int(130 * k), hit[1] + int(75 * k)))
    if v:
        return v
    c = crop(frame, (hit[0] - int(160 * k), hit[1] + int(8 * k), hit[0] + int(130 * k), hit[1] + int(56 * k)), 0)
    if c is None:
        return None
    hsv = cv2.cvtColor(c, cv2.COLOR_BGR2HSV)
    return read_digit_blobs((hsv[:, :, 0] >= 18) & (hsv[:, :, 0] <= 35) & (hsv[:, :, 1] > 120) & (hsv[:, :, 2] > 200))


# Built-in categories (lower-case, matched fuzzily). Anything not here is 'other'.
UPGRADE_CATEGORIES = {
    "heroes": ["barbarian king", "archer queen", "grand warden", "royal champion", "minion prince", "dragon duke", "hero hall",
               "battle machine", "battle copter"],
    "guardians": ["longshot", "smasher", "logger"],
    "army": ["laboratory", "army camp", "barracks", "dark barracks", "spell factory", "dark spell factory",
             "clan castle", "workshop", "pet house", "blacksmith", "builder barracks", "star laboratory",
             "reinforcement camp", "healing hut", "clock tower", "ottos outpost"],
    "defences": ["cannon", "archer tower", "mortar", "air defense", "wizard tower", "air sweeper", "hidden tesla",
                 "bomb tower", "x bow", "inferno tower", "eagle artillery", "scattershot", "builders hut",
                 "spell tower", "monolith", "multi archer tower", "ricochet cannon", "firespitter",
                 "multi gear tower", "double cannon", "firecrackers", "crusher", "guard post", "multi mortar",
                 "roaster", "giant cannon", "mega tesla", "lava launcher", "air bombs"],
    "traps": ["bomb", "spring trap", "giant bomb", "giga bomb", "air bomb", "seeking air mine", "skeleton trap", "tornado trap",
              "push trap", "mine", "mega mine"],
    "resources": ["gold mine", "elixir collector", "dark elixir drill", "gold storage", "elixir storage",
                  "dark elixir storage", "gem mine"],
    "town hall": ["town hall", "builder hall"],
}
# Builder Base without a plan of your own: these key buildings first (then the priciest affordable)
BB_DEFAULT_ROWS = [{"name": n, "base": "builder", "th": ""} for n in
                   ("builder hall", "ottos outpost", "battle machine", "battle copter", "builder barracks",
                    "star laboratory", "clock tower")]


def norm_name(s):
    """'Archer Tower x3' / 'Lonashot&' / 'Builder's Hut (lvl 5)' -> 'archer tower' / 'lonashot' / 'builders hut'."""
    s = re.sub(r"\(.*?\)", " ", str(s).lower())
    s = re.sub(r"(?<=[a-z.])0|0(?=[a-z.'])", "o", s)  # OCR reads O as 0 inside words: '0.T.T.0's' = O.T.T.O's
    s = re.sub(r"\b(x\s*\d+|lvl\s*\d+|level\s*\d+|to\s*\d+|\d+)\b", " ", s)
    s = re.sub(r"[^a-z ]", "", s.replace("-", " ").replace(".", ""))
    return re.sub(r"\s+", " ", s).strip()


def name_match(a, b):
    """Fuzzy: OCR turns Longshot into 'Lonashot&' and Storage into 'Storaae'."""
    a, b = (re.sub(r"^new ", "", norm_name(x)) for x in (a, b))  # the lab list tags fresh items 'New'
    if not a or not b:
        return False
    if a == b:
        return True
    if len(a.split()) != len(b.split()):  # 'dark elixir storage' is not 'elixir storage'
        return False
    if [w[0] for w in a.split()] != [w[0] for w in b.split()]:  # OCR keeps first letters; 'hog rider' != 'hog glider'
        return False
    # short names need a closer match ('miner' is not 'mine'); longer ones survive OCR slips ('scabbershot')
    return difflib.SequenceMatcher(None, a, b).ratio() >= (0.9 if min(len(a), len(b)) <= 6 else 0.8)


def category_of(name):
    exact = next((c for c, ns in UPGRADE_CATEGORIES.items() if norm_name(name) in ns), None)
    if exact:
        return exact
    best = ("other", 0)
    for cat, names in UPGRADE_CATEGORIES.items():
        for n in names:
            if name_match(name, n) and len(n) > best[1]:  # longest match: 'dark elixir storage' over 'elixir storage'
                best = (cat, len(n))
    return best[0]


WIKI_DIR = os.path.join(BASE_DIR, "wiki")
_WIKI = {}
# Hammer Jam (50% off), Gold Pass (up to 20% off), both at once...: every price on one list has the same discount
DISCOUNTS = (1.0, 0.95, 0.9, 0.85, 0.8, 0.75, 0.7, 0.65, 0.6, 0.55, 0.5, 0.45, 0.4, 0.35, 0.3)


def wiki_data():
    """wiki/buildings.json (made by build_wiki_data.py): per building its levels with cost + required hall level."""
    if "d" not in _WIKI:
        try:
            with open(os.path.join(WIKI_DIR, "buildings.json"), encoding="utf-8") as f:
                _WIKI["d"] = json.load(f)
        except (OSError, ValueError):
            _WIKI["d"] = {}
    return _WIKI["d"]


def wiki_key(name, base):
    """'home:cannon' for an OCR'd list name like 'Cannon x4' (fuzzy), or None."""
    k = (norm_name(name), base)
    if k not in _WIKI:
        hits = [key for key, v in wiki_data().items() if v["base"] == base and name_match(k[0], key.split(":", 1)[1])]
        # several fuzzy hits ('Giaa Bomb': Giga Bomb / Giant Bomb): the closest one
        _WIKI[k] = max(hits, key=lambda key: difflib.SequenceMatcher(None, k[0], key.split(":", 1)[1]).ratio(),
                       default=None)
    return _WIKI[k]


def level_for_price(key, price, factor=1.0):
    """Current level of a building whose next upgrade costs `price` (after `factor` discount), or None."""
    e = wiki_data().get(key)
    if not e or not price:
        return None
    full = price / factor
    hits = [lv["level"] - 1 for lv in e["levels"]
            if lv["cost"] and abs(lv["cost"] - full) <= max(lv["cost"] * 0.012, 600)]
    return hits[0] if len(hits) == 1 else None  # two levels with that price: unknown (the scan then reads it)


def infer_discount(rows, base):
    """The discount that makes the most list prices line up with real wiki prices (smallest discount on a tie)."""
    best = (0, 1.0)
    for f in DISCOUNTS:
        n = sum(1 for nm, p in rows if (k := wiki_key(nm, base)) and level_for_price(k, p, f) is not None)
        if n > best[0]:
            best = (n, f)
    return best[1]


def max_level(key, hall_level, hero_hall=None):
    """Highest level of this building allowed at that Town Hall / Builder Hall (heroes: by Hero Hall level)."""
    e = wiki_data().get(key)
    if not e:
        return None
    hall = e["levels"][-1].get("hall", "town hall")
    if hall == "hero hall":
        if hero_hall is None and hall_level is not None:  # not scanned: the most the Hero Hall can be at this TH
            hero_hall = max_level("home:hero hall", hall_level)
        hall_level = hero_hall
    if hall == "none" or hall_level is None:
        return e["levels"][-1]["level"]
    ok = [lv["level"] for lv in e["levels"] if lv["req"] <= hall_level]
    return max(ok) if ok else 0


NO_WIKI = ("blacksmith", "reinforcement camp")  # real buildings without wiki data: level read from the game


def is_wall(name):
    """'Wall', 'Wall x28', "': Wall x2" - never bought from the builder list (walls have their own routine)."""
    return bool(re.fullmatch(r"walls?( x\w*)?", norm_name(name)))  # 'Wall xI50' = OCR'd 'Wall x150'


def count_of(name):
    m = re.search(r"x\s*(\d+)\s*$", name.strip(), re.I)
    return int(m.group(1)) if m else 1


def time_to_max(sd, base):
    """(builder-seconds of upgrades left until everything is max for this hall, upgrades left, builders) from a
    planner scan. Upgrade times from the wiki data; walls aren't counted, nor what's upgrading right now."""
    hall, hero = sd.get("hall"), sd.get("hero_hall")
    total = n = 0
    for r in sd.get("items", []):
        e = wiki_data().get(r.get("key")) if r.get("key") != "home:wall" else None  # walls: their own card
        mx = max_level(r["key"], hall, hero) if e else None
        if mx is None or r.get("level") is None:
            continue
        for lv in e["levels"]:
            if r["level"] < lv["level"] <= mx:
                total += lv.get("time", 0) * r.get("count", 1)
                n += r.get("count", 1)
    huts = sum(r.get("count", 1) for r in sd.get("items", []) if r.get("key") == "home:builders hut")
    return total, n, (huts or 5) if base == "home" else 3  # Builder Base: its top bar shows x/3


def walls_left(sd):
    """Home walls from a planner scan: ({level: count}, max level at this Town Hall, walls below it, gold/elixir
    needed to bring every one of them to max - each wall priced level by level from where it is now)."""
    e = wiki_data().get("home:wall")
    mx = max_level("home:wall", sd.get("hall")) if e else None
    counts, todo, cost = {}, 0, 0
    for r in sd.get("items", []):
        if r.get("key") == "home:wall" and r.get("level") is not None:
            counts[r["level"]] = counts.get(r["level"], 0) + r.get("count", 1)
            if mx and r["level"] < mx:
                todo += r.get("count", 1)
                cost += r.get("count", 1) * sum(x["cost"] for x in e["levels"] if r["level"] < x["level"] <= mx)
    return counts, mx, todo, cost


def clipboard_usable():
    """False while Windows can't hand out its clipboard - e.g. the PC is locked (then the export can't arrive)."""
    try:
        return subprocess.run(["powershell", "-NoProfile", "-Command", "Get-Clipboard -Raw"], capture_output=True,
                              text=True, timeout=15, creationflags=NO_WINDOW).returncode == 0
    except Exception:
        return False


def read_clipboard():
    """Windows clipboard text ('' if none). BlueStacks copies Android's clipboard here."""
    try:
        return subprocess.run(["powershell", "-NoProfile", "-Command", "Get-Clipboard -Raw"], capture_output=True,
                              text=True, timeout=15, creationflags=NO_WINDOW).stdout or ""
    except Exception:
        return ""


def settings_drag_start(f):
    """y of a grey section-header band low in More Settings' list (rows are blue), or None."""
    k = f.shape[1] / 1920
    y0 = int(240 * k)
    col = f[y0:int(900 * k), int(500 * k)].astype(int)
    grey = (np.abs(col[:, 0] - col[:, 2]) < 25) & (col.mean(axis=1) > 170)
    runs, start = [], None
    for i, g in enumerate(list(grey) + [False]):
        if g and start is None:
            start = i
        elif not g and start is not None:
            if i - start >= 20 * k:
                runs.append(y0 + (start + i) // 2)
            start = None
    low = [y for y in runs if y >= 300 * k]  # room to drag at least ~280px up
    return max(low) if low else None


def settings_tag(frame):
    """Player tag under the name in the Settings window ('#V9GJCRCL'), or None. Q and 0 look alike: compare tags
    with same_tag()."""
    if not HAVE_TESS:
        return None
    k = frame.shape[1] / 1920
    g = cv2.cvtColor(frame[int(226 * k):int(262 * k), int(860 * k):int(1120 * k)], cv2.COLOR_BGR2GRAY)
    try:
        t = pytesseract.image_to_string(cv2.resize(g, None, fx=3, fy=3), timeout=5,
                                        config="--psm 7 -c tessedit_char_whitelist=#0289PYLQGRJCUV").strip()
    except Exception:
        return None
    return t if re.fullmatch(r"#[0289PYLQGRJCUV]{6,10}", t) else None


same_tag = lambda a, b: bool(a and b) and a.replace("Q", "0") == b.replace("Q", "0")


def settings_name(frame):
    """Player name beside the avatar in the Settings window (white on blue), or None."""
    if not HAVE_TESS:
        return None
    k = frame.shape[1] / 1920
    g = cv2.cvtColor(frame[int(188 * k):int(228 * k), int(860 * k):int(1180 * k)], cv2.COLOR_BGR2GRAY)
    try:  # plain greyscale reads this chunky font best (binarising it made 'GeoCol2' into 'GeaCol2d')
        words = pytesseract.image_to_string(cv2.resize(g, None, fx=3, fy=3), config="--psm 7", timeout=5).split()
    except Exception:
        return None
    return words[0] if words and len(words[0]) >= 2 else None


def export_items(data):
    """The game's 'Export Village data' JSON -> {'home': items, 'builder': items} in the planner's scan format.
    Exact levels of everything built (an upgrading one counts as its next level, like plan_progress does)."""
    ids = {i: k for k, e in wiki_data().items() for i in e.get("ids", [])}
    out = {}
    for base, parts in (("home", ("buildings", "traps", "heroes", "guardians")),
                        ("builder", ("buildings2", "traps2", "heroes2"))):
        items = {}
        for part in parts:
            for x in data.get(part) or []:
                k = ids.get(x.get("data"))
                if k and isinstance(x.get("lvl"), int):
                    up = "timer" in x
                    r = items.setdefault((k, x["lvl"] + up, up), {"key": k, "name": wiki_data()[k]["name"],
                                                                  "level": x["lvl"] + up, "count": 0, "upgrading": up})
                    r["count"] += x.get("cnt", 1)  # supercharged copies come as separate rows
        out[base] = list(items.values())
    return out


def available_slots(frame):
    """(normal, goblin) free slots from an open builder/lab list's 'Available!' rows. The goblin builder /
    researcher (costs gems) has a green face next to its row; the normal builder/researcher doesn't."""
    box = panel_box(frame)
    if not box or not HAVE_TESS:
        return 0, 0
    x0, x1, y0, y1 = box
    c = frame[y0:y1, x0:x1]
    try:
        d = pytesseract.image_to_data(cv2.cvtColor(c, cv2.COLOR_BGR2GRAY), config="--psm 11",
                                      output_type=pytesseract.Output.DICT, timeout=10)
    except Exception:
        return 0, 0
    normal = goblin = 0
    for i, t in enumerate(d["text"]):
        if t.lower().startswith("availab"):
            x, y, h = d["left"][i], d["top"][i], d["height"][i]
            face = cv2.cvtColor(c[max(0, y - 15):y + h + 15, max(0, x - 80):max(1, x - 8)], cv2.COLOR_BGR2HSV)
            green = ((face[:, :, 0] >= 30) & (face[:, :, 0] <= 85) & (face[:, :, 1] > 80) & (face[:, :, 2] > 80))
            if green.size and green.mean() > 0.15:  # measured: goblin ~0.3, normal faces <0.05
                goblin += 1
            else:
                normal += 1
    return normal, goblin


def list_rows(frame):
    """Rows of an open builder/lab list: [(name, price, affordable, (x, y))]. Prices are white when you can
    afford them and red when you can't; section headers are green; in-progress rows show a timer next to a
    green progress bar and are skipped."""
    box = panel_box(frame)
    if not box or not HAVE_TESS:
        return []
    x0, x1, py0, py1 = box
    c = frame[py0:py1, x0:x1]
    hsv = cv2.cvtColor(c, cv2.COLOR_BGR2HSV)
    b, g, r = (c[:, :, i].astype(int) for i in range(3))
    white = (hsv[:, :, 2] > 190) & (hsv[:, :, 1] < 60)
    red = (r > 170) & (r - g > 90) & (r - b > 60)
    green = (g > 170) & (g - r > 40) & (g - b > 60)
    W, H = x1 - x0, py1 - py0
    split = int(W * 0.62)
    prof = (white | red)[:, :split].sum(axis=1)
    out, y = [], 0
    while y < H:
        if prof[y] <= 3:
            y += 1
            continue
        yb = y
        while yb < H and prof[yb] > 3:
            yb += 1
        ya, y = y, yb + 1
        if not 16 <= yb - ya <= 70 or green[ya:yb].sum() > white[ya:yb].sum():  # noise / section header
            continue
        a, bb = max(0, ya - 8), min(H, yb + 8)
        if green[a:bb, split - 60:].sum() > 50:  # upgrade in progress
            continue
        pw, pr = white[a:bb, split - 60:], red[a:bb, split - 60:]
        is_red = pr.sum() > pw.sum()
        price = read_digit_blobs(pr if is_red else pw)
        nm = (white | red)[ya:yb, :split].astype(np.uint8) * 255
        k = 48 / nm.shape[0]
        nm = cv2.resize(nm, None, fx=k, fy=k, interpolation=cv2.INTER_LINEAR)
        try:
            name = pytesseract.image_to_string(cv2.copyMakeBorder(255 - nm, 30, 30, 30, 30, cv2.BORDER_CONSTANT,
                                                                  value=255), config="--psm 7", timeout=5).strip()
        except Exception:
            name = ""
        if price and price >= 1000 and name and ya > 6:  # ya>6: skip the half-cut row at the top edge
            out.append((name, price, not is_red, (x0 + W // 4, py0 + (ya + yb) // 2)))
    return out


def icon_empty(frame, x, y, half=14):
    """A used-up troop slot turns grey: low saturation at its centre."""
    p = frame[max(0, y - half):y + half, max(0, x - half):x + half]
    return p.size > 0 and float(cv2.cvtColor(p, cv2.COLOR_BGR2HSV)[:, :, 1].mean()) < 35


# ---------------------------------------------------------------------------
# The bot (runs on its own thread; never touches Tk - talks to the UI via emit)
# ---------------------------------------------------------------------------
class Abort(Exception):
    pass


class Bot:
    def __init__(self, cfg, adb, emit, mode="farm"):
        # "farm", "loot" (attack only), "walls", "bb_loot" / "bb_farm" (Builder Base only, without / with upgrades)
        self.cfg, self.adb, self.emit, self.mode = cfg, adb, emit, mode
        self.stop_evt = threading.Event()
        self.v = Vision()
        self.stats = dict(attacks=0, skipped=0, walls=0, upgrades=0, switches=0, recoveries=0, errors=0)
        self.hits = {}
        self._last_shot = self._last_preview = 0.0
        self._bank_backoff = {}
        self._upgrade_backoff = {}
        self._busy_until = {}  # kind -> time: 'only the goblin is free' counts as busy for account rotation
        self._bb_next = {}     # account -> time of its next Builder Base visit
        self._acc_idx = -1
        self.loot = {}        # account -> [gold, elixir, dark, attacks] farmed this session
        self._names = list(dict.fromkeys((cfg.get("account_tags") or {}).values()))  # misreads snap to these
        self._saving_home = None  # account farming for its next home plan target: no Builder Base trips meanwhile
        self._bb_saving = None  # resource the Builder Base plan is saving up (the Star Lab leaves it alone)
        self._view = None  # background zoom + pan for the base being scouted
        self._last_name = None
        self._cur = self._pre = None  # (account, (gold, elixir, dark)) now / just before the attack
        self._switch_streak = 0
        self._rotate_pause_until = 0.0
        self._n_accounts = 0
        self._emu_restarts = []
        self._unreadable = 0
        self.game_relaunches = 0
        self._last_groq = 0.0
        self._groq_paused_until = 0.0
        self._warned = set()
        if HAVE_TESS:
            pytesseract.pytesseract.tesseract_cmd = cfg["tesseract_path"]

    # --- plumbing ---
    def log(self, msg, level="info"):
        getattr(log_file, {"ok": "info", "warn": "warning", "err": "error"}.get(level, "info"))(msg)
        self.emit("log", (level, msg))

    def bump(self, key, n=1):
        self.stats[key] += n
        self.emit("stats", dict(self.stats))

    def sleep(self, s):
        if self.stop_evt.wait(max(0.0, s)):
            raise Abort()

    def shot(self):
        if self.stop_evt.is_set():
            raise Abort()
        self.sleep(self.cfg["min_screenshot_interval"] - (time.time() - self._last_shot))
        frame = self.adb.screenshot()
        self._last_shot = time.time()
        if self._last_shot - self._last_preview > 1.0:
            self._last_preview = self._last_shot
            self.emit("frame", cv2.resize(frame, (960, int(960 * frame.shape[0] / frame.shape[1])),
                                          interpolation=cv2.INTER_AREA))
        return frame

    def find(self, frame, name):
        hit = self.v.find(frame, name, self.cfg["match_confidence"])
        if hit and name in ("attack_button", "bb_attack_button") and not self.v.undimmed(frame, name, hit):
            return None  # a popup/panel is darkening the village: not really on the home screen
        return hit

    def tap(self, xy, delay=None):
        self.adb.tap(*xy)
        self.sleep(self.cfg["tap_delay"] if delay is None else delay)

    def wait_for(self, name, timeout, poll=0.8):
        end = time.time() + timeout
        while True:
            hit = self.find(self.shot(), name)
            if hit or time.time() >= end:
                return hit
            self.sleep(poll)

    def detect(self, frame):
        if self.find(frame, "wall_okay_button"):  # an Okay/Cancel dialog covers whatever screen is behind it
            return None
        for name, state in STATES:
            hit = self.find(frame, name)
            if hit:
                self.hits[name] = hit
                return state
        return None

    # --- main loop ---
    def run(self):
        self.log("Farming started.", "ok")
        self.emit("stats", dict(self.stats))
        prev, unknown_since, backs, adb_fails, online = "START", None, 0, 0, None
        awake = lambda on: os.name == "nt" and ctypes.windll.kernel32.SetThreadExecutionState(
            0x80000000 | (0x1 if on else 0))  # ES_CONTINUOUS | ES_SYSTEM_REQUIRED: no sleeping while farming
        awake(True)
        try:
            while True:
                try:
                    if getattr(self, "relaunch_req", False):  # asked from the phone
                        self.relaunch_req = False
                        self.recover_game("restart requested from the phone")
                    frame = self.shot()
                    if online is not True:
                        online = True
                        self.emit("device", True)
                    adb_fails = 0
                    if frame.shape[:2] != (1080, 1920):
                        self.fix_resolution(frame)
                        continue
                    self.hits = {}
                    state = self.detect(frame)
                    if state != prev:
                        self.emit("state", STATE_LABELS[state])
                    if state is None:
                        unknown_since = unknown_since or time.time()
                        stuck = time.time() - unknown_since
                        # the Supercell logo / loading clouds after a (re)start aren't 'stuck': a slow PC can take
                        # minutes there, and relaunching mid-load would just loop
                        loading = time.time() - getattr(self, "_launched_at", 0) < 180
                        if stuck > (180 if loading else self.cfg["watchdog_attack_timeout"]):
                            self.recover_game(f"stuck on an unrecognised screen for {stuck:.0f}s")
                            unknown_since, backs = None, 0
                        elif self.reload_if_disconnected(frame):
                            unknown_since = None
                        elif self.bb_bonus(self._last_name or "?"):  # the Star Bonus popup (home or Builder
                            unknown_since = None                     # Base) - known, so no need to ask Groq
                        elif self.event_chest(frame):  # chest event: open it, take the reward
                            unknown_since = None
                        elif self.loading_screen(frame):  # Supercell logo / loading art / clouds / a live replay
                            self.sleep(1.0)                # of an attack on us: only waiting helps (watchdog still on)
                        elif self.v.find(frame, "replay_return_home", 0.9):  # that replay ended (opening the game
                            self.log("Leaving the replay of an attack on this village.")  # mid-attack shows it)
                            self.tap(self.v.find(frame, "replay_return_home", 0.9), 2.0)
                            unknown_since = None
                        elif self.close_popup(frame):  # a window's red X: always just closes it
                            unknown_since = None
                        elif self.find(frame, "wall_okay_button"):
                            self.log("Closing an Okay/Cancel dialog with Back (never confirms).")
                            self.adb.back()
                            self.sleep(1.0)
                        elif stuck >= 3 and backs == 0:  # most popups close with Back: try that before asking Groq
                            self.log("Unrecognised screen - pressing Back once.")
                            self.adb.back()
                            backs += 1
                            self.sleep(1.0)
                        elif (self.groq_on("groq_supervisor") and stuck >= 6 and time.time() - self._last_groq >= 5
                              and (state := self.groq_rescue(frame))):
                            unknown_since = None
                            getattr(self, "on_" + state.lower())(frame, prev)
                            prev = state
                            continue
                        elif stuck > 10 * (backs + 1) and backs < 3:  # also when Groq is down or unsure
                            self.log("Unrecognised screen - pressing Back to clear any popup.", "warn")
                            self.adb.back()
                            backs += 1
                        self.sleep(1.0)
                    else:
                        unknown_since, backs = None, 0
                        getattr(self, "on_" + state.lower())(frame, prev)
                    prev = state
                except ADBError as e:
                    adb_fails += 1
                    online = False
                    self.emit("device", False)
                    self.log(f"ADB problem: {e}", "warn")
                    prev = "START"
                    try:
                        self.recover_adb(adb_fails)
                    except Abort:
                        raise
                    except Exception as e2:  # recovery must never kill the loop
                        self.log(f"Recovery error: {e2}", "err")
                        self.sleep(10)
                except Abort:
                    raise
                except Exception:
                    self.bump("errors")
                    self.log("Unexpected error, carrying on:\n" + traceback.format_exc(limit=4), "err")
                    self.sleep(3)
        except Abort:
            pass
        finally:
            awake(False)
        self.log("Farming stopped.", "ok")
        self.emit("state", "Stopped")

    # --- screen handlers ---
    def account_name(self, frame):
        """Player name at the top-left of the home screen (e.g. 'GeoCol3'), snapped to names already seen."""
        k = frame.shape[1] / 1920
        c = frame[int(8 * k):int(52 * k), int(140 * k):int(520 * k)]
        hsv = cv2.cvtColor(c, cv2.COLOR_BGR2HSV)
        raw = ((hsv[:, :, 2] > 170) & (hsv[:, :, 1] < 60)).astype(np.uint8)
        n, lab, st, _ = cv2.connectedComponentsWithStats(raw, 8)
        # letters: 8-24px tall, not touching the crop edge, sitting on one baseline. Decorations behind the name
        # (cakes, statues, snow) are taller / elsewhere - picking by 'tallest shape' dropped the lower-case letters.
        cand = [i for i in range(1, n) if 8 * k <= st[i, 3] <= 24 * k and st[i, 2] <= 30 * k
                and st[i, 1] > 0 and st[i, 1] + st[i, 3] < c.shape[0]]
        base = np.median([st[i, 1] + st[i, 3] for i in cand]) if cand else 0
        keep = [i for i in cand if abs(st[i, 1] + st[i, 3] - base) <= 3 * k]
        if keep:  # one word: drop shapes far to the right of the name (a gap wider than two letters)
            keep.sort(key=lambda i: st[i, 0])
            word = [keep[0]]
            for i in keep[1:]:
                if st[i, 0] - (st[word[-1], 0] + st[word[-1], 2]) > 30 * k:
                    break
                word.append(i)
            keep = word
        m = cv2.resize(np.isin(lab, keep).astype(np.uint8) * 255, None, fx=3, fy=3)
        try:
            words = pytesseract.image_to_string(cv2.copyMakeBorder(255 - m, 20, 20, 20, 20, cv2.BORDER_CONSTANT,
                                                                   value=255), config="--psm 7", timeout=5).split()
        except Exception:
            words = []
        name = words[0] if words else ""
        digits = re.sub(r"\D", "", name)  # GeoCol2 vs GeoCol3 are different accounts: never snap across digits
        near = difflib.get_close_matches(name, [n for n in self._names if re.sub(r"\D", "", n) == digits], 1, 0.7)
        if near:
            self._last_name = near[0]
        elif len(name) >= 3:
            self._names.append(name)
            self._last_name = name
        key = getattr(self, "_sc_key", None)
        if key and self._last_name and key.startswith(self._last_name + " ("):
            self._last_name = key  # one of two accounts sharing an in-game name
        # unreadable (e.g. the XP bar animating over it just after a battle): the account hasn't changed
        return self._last_name or "?"

    def track_loot(self, frame, storage):
        """Credit the storage gained since just before the last attack to this account."""
        k = frame.shape[1] / 1920
        dark = white_number(frame, self.cfg["ocr_regions"].get(
            "bank_dark_region", tuple(int(v * k) for v in (1560, 225, 1830, 300))))
        now = (storage.get("gold"), storage.get("elixir"), dark)
        name = self.account_name(frame)
        pre, self._pre = self._pre, None
        if pre and pre[0] == name and None not in now[:2] and None not in pre[1][:2]:
            gain = [max(0, (n or 0) - (p or 0)) if n is not None and p is not None else 0 for n, p in zip(now, pre[1])]
            if any(gain) and max(gain) <= 20_000_000:  # sanity: no single attack brings more
                row = self.loot.setdefault(name, [0, 0, 0, 0])
                for i, g in enumerate(gain):
                    row[i] += g
                row[3] += 1
                self.emit("loot", {a: list(r) for a, r in self.loot.items()})
                self.log(f"{name}: +{gain[0]:,} gold, +{gain[1]:,} elixir, +{gain[2]:,} dark")
        self._cur = (name, now)
        return storage

    def attack_now(self):
        self._pre = self._cur  # storage right before this attack
        self.tap(self.hits["attack_button"])

    def ambiguous(self):
        """True while the top-left name is one that two accounts share ('GeoCol2' and 'GeoCol2 (GeoCol2)') and
        nothing yet says which of them this is - e.g. after switching accounts by hand."""
        n = self._last_name
        return bool(n) and " (" not in n and n != getattr(self, "_tag_ok", None) and any(k.startswith(n + " (") for k in self.cfg.get("scans") or {})

    def read_accounts(self):
        """Open the Supercell ID list just to note the accounts on it (for the phone view's picker), then close it."""
        self.back_to_village()
        f = self.shot()
        self.tap(self.find(f, "settings_cog_button") or (int(1842 * f.shape[1] / 1920), int(765 * f.shape[1] / 1920)), 2.0)
        sw = self.wait_for("switch_account_button", 5)
        if sw:
            self.tap(sw, 2.5)
            if self.wait_for("supercell_id_header", 6):
                rows = self.all_accounts()
                self.log(f"Accounts on this device: {', '.join(r['sc'] for r in rows)}.", "ok")
        self.back_to_village()
        if not self.at_village(self.shot()):  # the Supercell ID panel can need a couple of Backs
            for _ in range(3):
                self.adb.back()
                self.sleep(1.2)
                if self.at_village(self.shot()):
                    break

    def phone_switch(self):
        """An account picked on the phone view: switch now (we're on a village). True if one was waiting."""
        if getattr(self, "list_req", False):
            self.list_req = False
            self.read_accounts()
            return True
        sc, self.switch_req = getattr(self, "switch_req", None), None
        if not sc:
            return False
        self.log(f"Phone: switching to {sc}.", "ok")
        self.switch_account(target=sc)
        return True

    def on_home(self, frame, prev):
        self.game_relaunches = 0
        self._view = None
        if self.phone_switch():
            return
        self.account_name(frame)
        if self.ambiguous() and self.mode != "loot" and time.time() >= getattr(self, "_amb_try", 0):
            self._amb_try = time.time() + 600  # the export's player tag says which one (then account_name knows)
            if self.scan_export():
                return
        storage = self.track_loot(frame, self.read_storage(frame))
        if self.mode == "loot":  # Loot only: no upgrades, walls or account switching - just attack
            return self.attack_now()
        if self.mode.startswith("bb_"):  # Builder Base only: never stays home
            if not self.take_boat("builder"):
                self.log("Builder Base only: couldn't find the boat - trying again in 2 min.", "warn")
                self.sleep(120)
            return
        if self.mode == "walls":  # Walls only: farm, and every time the next wall level is affordable, buy it
            if self.maybe_rescan("builder", hours=1):  # keeps the dashboard's wall count current
                return
            price = self.wall_price()
            if price == 0:
                self.log("Every wall is max for this Town Hall - nothing left to buy. Stopping.", "ok")
                self.stop_evt.set()
                raise Abort()
            if self.spend_bank(storage, price):
                return
            return self.attack_now()
        for kind in ("builder", "lab"):
            if self.cfg[f"{kind}_upgrades_enabled"] and time.time() >= self._upgrade_backoff.get(kind, 0):
                sv = self._saving_home if kind == "builder" else None
                have = {"gold": storage.get("gold"), "elixir": storage.get("elixir"), "dark": self._cur[1][2]}
                if sv and sv[0] == self._last_name and time.time() < sv[3] and have.get(sv[2]) is not None \
                        and have[sv[2]] < sv[1]:
                    continue  # still short of the plan's next target: no need to open the list
                if self.free_slots(frame, kind) == 0:
                    if kind == "builder":
                        self._saving_home = None  # every builder busy: nothing to save up for right now
                    if self.maybe_rescan(kind):  # all busy: still refresh the planner's view now and then
                        return
                    continue  # all busy: no need to open the list
                self.upgrade_from_list(kind)
                return  # screen changed; look again
        if self.cfg["bank_spend_enabled"] and self.spend_bank(storage):
            return  # screen changed while buying; look again
        if self.cfg["builder_base_enabled"] and (self._saving_home or (None,))[0] != self._last_name \
                and self.builder_base():
            return  # back home; look again (one side at a time: not while saving up for a home target)
        if self.account_done(frame) and self.switch_account():
            return
        self.attack_now()

    def on_menu(self, frame, prev):
        if self.mode.startswith("bb_"):  # Builder Base only: never start a home-village attack - back out
            return self.back_to_village()
        self.tap(self.hits["find_match_button"], self.cfg["matchmaking_settle_delay"])

    def on_army(self, frame, prev):
        if self.mode.startswith("bb_"):
            return self.back_to_village()
        self.tap(self.hits["confirm_attack_button"], self.cfg["matchmaking_settle_delay"])

    def on_bbend(self, frame, prev):
        self.tap(self.hits["bb_return_home"], 3.0)

    def on_bbhome(self, frame, prev):
        """On the Builder Base outside a visit (a restart, a crash, a stray boat tap): collect and sail home."""
        if self.phone_switch():
            return
        if self.mode.startswith("bb_"):
            return self.bb_only()
        self.bb_bonus(self._last_name or "?")
        if not self.take_boat("home"):  # collects (cart too) first
            self.log("On the Builder Base and couldn't take the boat home - relaunching the game.", "warn")
            self.recover_game("stuck on the Builder Base")

    def on_end(self, frame, prev):
        self.tap(self.hits["return_home_button"], self.cfg["return_home_delay"])

    def on_battle(self, frame, prev):
        # A fresh base shows 'End Battle' a moment before 'Next' appears: give it a few seconds to be scouting -
        # also with only heroes on the bar (troops/spells still training), which used to pass for a running battle
        nxt = self.wait_for("next_button", 3, poll=0.5)
        if nxt:
            self.hits["next_button"] = nxt
            return self.on_scout(self.shot(), "BATTLE")
        left = [c for c in troop_bar(frame) if c[3] and (c[2] == "troop" or c[2] == "spell" and self.cfg["deploy_spells"])]
        if left:
            # the scouting timer ran out before we deployed: the battle started with our army unused
            self.log(f"Battle running with {len(left)} unused troop/spell cards - deploying now.", "warn")
            return self.attack(None, None)
        self.log("Found a battle in progress - watching damage.")
        self.finish_battle()

    def start_view(self):
        """Zoom fully out + pan to the drop corner in the background while the loot is read, so the deploy can
        start straight away (it took ~6 s at deploy time). The adb shell is locked: a Next tap simply waits."""
        if self._view is None and self.cfg.get("deploy_pan", "off") in PAN_DIRS:
            def work():
                try:
                    zoom_out(self.adb, times=2)  # two pinches reach the limit from any zoom (measured)
                    pan_view(self.adb, self.cfg["deploy_pan"])
                except Exception as e:
                    log_file.info(f"view prep: {e}")
            self._view = threading.Thread(target=work, daemon=True)
            self._view.start()

    def on_scout(self, frame, prev):
        c = self.cfg
        if self.mode.startswith("bb_"):  # Builder Base only: leave a home search (End Battle before deploying is free)
            hit = self.find(frame, "surrender_button")
            return self.tap(hit, 3.0) if hit else self.back_to_village()
        self.start_view()
        if c["loot_force_attack"]:
            return self.attack(None, None)
        if prev != "SCOUT":  # loot numbers count up as the base loads
            self.sleep(c["loot_settle_delay"])
            frame = self.shot()
            if not (self.find(frame, "next_button") or self.hits.get("next_button")):
                return
        gold, elixir = self.read_loot(frame)
        if gold is None or elixir is None:  # one retry on a fresh frame
            self.sleep(0.8)
            gold, elixir = self.read_loot(self.shot())
        self.emit("base", (gold, elixir))
        if gold is None or elixir is None:
            self._unreadable += 1
            if self._unreadable >= 5:
                self.log("Can't read loot on 5 bases in a row - attacking anyway so Next doesn't burn "
                         "gold. Re-capture the loot regions in Setup.", "warn")
                self._unreadable = 0
                return self.attack(gold, elixir)
            self.log(f"Loot unreadable (gold={gold}, elixir={elixir}) - next base.", "warn")
        else:
            self._unreadable = 0
            g_ok, e_ok = gold >= c["loot_gold_threshold"], elixir >= c["loot_elixir_threshold"]
            if (g_ok and e_ok) if c["loot_require_both"] else (g_ok or e_ok):
                return self.attack(gold, elixir)
            self.log(f"Skip: gold {gold:,} / elixir {elixir:,}")
        hit = self.find(self.shot(), "next_button") or self.hits.get("next_button")
        if hit:
            self.bump("skipped")
            if self._view:
                self._view.join(15)
            self._view = None  # the next base gets its own zoom + pan
            self.tap(hit, c["loot_recheck_delay"])

    # --- Groq (AI vision) ---
    def groq_on(self, key):
        return bool(self.cfg.get(key) and self.cfg.get("groq_api_key") and self.cfg.get("groq_model")
                    and time.time() >= self._groq_paused_until)

    def groq(self, frame, prompt, tokens=250):
        self._last_groq = time.time()
        _groq.pop("last_error", None)
        r = groq_ask(self.cfg, frame, prompt, tokens)
        if r is None and "429" in _groq.get("last_error", ""):
            self._groq_paused_until = time.time() + 900
            self.log("Groq's free daily limit is used up - pausing AI for 15 min (the bot keeps farming "
                     "without it).", "warn")
        elif r is None and "groq_fail" not in self._warned:
            self._warned.add("groq_fail")
            self.log("Groq didn't answer (key, model, internet or 'pip install groq'?) - using the "
                     "non-AI fallback. Details in bot.log.", "warn")
        return r

    def groq_rescue(self, frame):
        """Ask Groq what's on screen and act on it. Returns a known state (with its button in
        self.hits) for the normal handler to take over, or None after doing a safe action itself."""
        r = self.groq(frame, RESCUE_PROMPT)
        if not r:
            return None
        k = frame.shape[1] / GROQ_W
        screen, action = str(r.get("screen", "other")).lower(), str(r.get("action", "wait")).lower()
        target, reason = str(r.get("target") or ""), str(r.get("reason") or "")
        b = r.get("button")
        xy = (int(b[0] * k), int(b[1] * k)) if isinstance(b, list) and len(b) == 2 and all(
            isinstance(v, (int, float)) for v in b) else None
        if xy and not (0 <= xy[0] < frame.shape[1] and 0 <= xy[1] < frame.shape[0]):
            xy = None
        self.log(f"Groq: {screen} -> {action} {target!r} ({reason})")
        try:  # keep the screens Groq had to explain (the last 60): each one is a case to teach the bot
            d = os.path.join(BASE_DIR, "groq_screens")
            os.makedirs(d, exist_ok=True)
            tag = re.sub(r"[^a-z0-9]+", "-", f"{screen} {action} {target}".lower())[:50]
            cv2.imwrite(os.path.join(d, time.strftime("%m%d_%H%M%S_") + tag + ".jpg"), frame)
            for old in sorted(os.listdir(d))[:-60]:
                os.remove(os.path.join(d, old))
        except Exception:
            pass
        state = GROQ_SCREENS.get(screen)
        if state and xy:
            name = next(n for n, st in STATES if st == state)
            self.hits[name] = xy
            sc = self.v.score(frame, name)
            if sc and name not in self._warned:
                self._warned.add(name)
                self.log(f"'{name}' image only matched {sc[0]:.2f} here - Groq recognised the screen instead. "
                         f"Re-capture it in Setup if you see this often.", "warn")
            self.emit("state", STATE_LABELS[state] + " (AI)")
            return state
        if action == "tap" and xy:
            if any(w in (target + " " + reason).lower() for w in GROQ_BLOCKED):
                self.log(f"Refused Groq tap on {target!r} - could spend gems. Pressing Back instead.", "warn")
                self.adb.back()
            else:
                self.tap(xy, 1.5)
        elif action == "back":
            self.adb.back()
            self.sleep(1.0)
        elif action == "relaunch":
            self.recover_game(f"Groq: {reason or 'game looks broken'}")
        else:
            self.sleep(2.0)
        return None

    # --- reading numbers ---
    def read(self, frame, region, min_digits=None, thorough=True):
        box = self.cfg["ocr_regions"].get(region)
        if not box:
            return None
        md = self.cfg["ocr_min_digits"] if min_digits is None else min_digits
        v = ocr_number(frame, box, self.cfg["ocr_region_padding_px"], md, thorough)
        return None if v is not None and v > self.cfg["loot_max_plausible"] else v

    def read_pair(self, frame, prompt, groq_key, regions, thorough, cap=None):
        """Local white-text read first (free, ~0.4s); Groq only if that fails (it has a daily limit)."""
        cap = cap or self.cfg["loot_max_plausible"]
        ok = lambda v: v is not None and v <= cap
        boxes = [self.cfg["ocr_regions"].get(r) for r in regions]
        g, e = (white_number(frame, b) if b else None for b in boxes)
        if ok(g) and ok(e):
            return g, e
        if self.groq_on(groq_key):
            r = self.groq(frame, prompt, 60) or {}
            rg, re_ = as_int(r.get("gold")), as_int(r.get("elixir"))
            if ok(rg) and ok(re_):
                return rg, re_
        return tuple(v if ok(v) else self.read(frame, reg, thorough=thorough) for v, reg in zip((g, e), regions))

    def read_loot(self, frame):
        return self.read_pair(frame, LOOT_PROMPT, "use_groq_for_loot",
                              ("loot_gold_region", "loot_elixir_region"), True)

    def read_storage(self, frame, village="home"):
        g, e = self.read_pair(frame, STORAGE_PROMPT, "use_groq_for_bank",
                              ("bank_gold_region", "bank_elixir_region"), False,
                              cap=99_999_999)  # storages hold far more than any base's loot
        s = {"gold": g, "elixir": e}
        if g is not None or e is not None:
            self.emit("storage", dict(s, village=village))
        self.log(("Builder Base storage" if village == "builder" else "Storage") + f": gold {g if g is None else f'{g:,}'} / elixir {e if e is None else f'{e:,}'}")
        return s

    # --- attacking ---
    def attack(self, gold, elixir):
        loot = f" - gold {gold:,} / elixir {elixir:,}" if gold is not None and elixir is not None else ""
        self.log(f"Attacking{loot}", "ok")
        self.bump("attacks")
        if self.deploy():
            self.finish_battle()

    def deploy(self):
        c = self.cfg
        self._ability_cards = []
        if self._view:  # zoomed out + panned while scouting (normally done by now)
            self._view.join(15)
        elif c.get("deploy_pan", "off") in PAN_DIRS:  # each account/village keeps its own zoom: zoom fully out
            zoom_out(self.adb, times=2)             # first, so the pan lands on the same view every time
            pan_view(self.adb, c["deploy_pan"])
        self._view = None
        self.sleep(0.3)
        a, b = self.line()
        bar = None
        try:  # what the bot saw + where it will drop: send this file if placement looks wrong
            dbg = self.shot().copy()
            bar = troop_bar(dbg)
            fp = c["fixed_points"]
            cv2.line(dbg, tuple(a), tuple(b), (0, 210, 255), 6)
            if fp.get("spell_point"):
                cv2.line(dbg, tuple(fp["spell_point"]), tuple(fp.get("spell_line_end") or fp["spell_point"]),
                         (255, 80, 220), 6)
            for x, y, kind, n in bar:
                cv2.putText(dbg, f"{kind} {n or ''}", (x - 60, y - 90), cv2.FONT_HERSHEY_SIMPLEX, 0.8, (255, 255, 255), 2)
            cv2.imwrite(os.path.join(BASE_DIR, "debug_deploy.png"), dbg)
        except Exception as e:
            log_file.info(f"debug_deploy.png: {e}")
        if self.auto_deploy(a, b, bar):
            return True
        # no troop bar: often the game was still / again searching (white clouds) - wait for the screen to settle
        for _ in range(8):
            self.sleep(1.0)
            f = self.shot()
            if self.find(f, "next_button"):  # a base to scout (again): the main loop checks its loot first
                self.log("The game was still searching when the army was due - checking this base's loot again.",
                         "warn")
                self._view = None
                return False
            if troop_bar(f):
                if self.auto_deploy(a, b):
                    return True
                break
        self.log("Couldn't read the troop bar - no troops deployed (see debug_deploy.png).", "err")
        return True  # in a battle we can't use: finish_battle surrenders it

    def finish_battle(self):
        c = self.cfg
        start, best, streak = time.time(), 0, 0
        last_rise = last_read = start  # troops dead/stuck = damage stops rising while we can still read it
        abilities = list(getattr(self, "_ability_cards", [])) if c["hero_abilities"] else []
        while time.time() - start < c["battle_max_wait"]:
            if abilities and time.time() - start >= c["hero_ability_delay"]:
                for xy in abilities:  # a dead hero's greyed card just ignores the tap
                    self.adb.tap(*xy)
                    self.sleep(0.25)
                self.log(f"Used {len(abilities)} hero abilities.")
                abilities = []
            frame = self.shot()
            if self.pick_reward(frame):
                continue
            if self.find(frame, "return_home_button"):
                self.log("Battle ended on its own.")
                return
            box = c["ocr_regions"].get("damage_percent_region")
            dmg = (damage_percent(frame, box) if box else None)
            if dmg is None or dmg > 100:
                dmg = self.read(frame, "damage_percent_region", min_digits=1, thorough=False)
            if dmg is not None and dmg <= 100 and dmg >= best - 5:  # damage never goes down
                last_read = time.time()
                if dmg > best:
                    last_rise = last_read
                best = max(best, dmg)
                streak = streak + 1 if dmg >= c["surrender_damage_threshold"] else 0
                self.emit("state", f"In battle - {dmg}% damage")
                if streak >= c["damage_confirm_count"]:
                    self.log(f"{dmg}% damage reached - surrendering.", "ok")
                    break
            stalled = time.time() - last_rise
            limit = c["damage_stall_seconds"] if best > 0 else max(45, c["damage_stall_seconds"])  # troops still walking in
            if stalled > limit and time.time() - last_read < 3 * c["timer_poll_interval"] + 2:
                self.log(f"Damage stuck at {best}% for {stalled:.0f}s - troops are done, surrendering.", "ok")
                break
            self.sleep(c["timer_poll_interval"])
        else:
            self.log(f"{c['battle_max_wait']:.0f}s battle limit - surrendering.")
        self.pick_reward(self.shot())
        for name in ("surrender_button", "surrender_confirm_button"):
            hit = self.wait_for(name, 6) or c["coords"].get(name)
            if not hit:
                self.log(f"Couldn't find '{name}'.", "warn")
                return
            self.tap(hit, 0.8)

    def loading_screen(self, frame):
        """Screens where the only right move is to wait: the black Supercell logo, the Clash loading art, and the
        white clouds between screens ('Searching for opponents...' - Back there would cancel the search)."""
        m = float(frame.mean())
        if m < 30:
            return True
        if m > 165 and float(cv2.cvtColor(frame, cv2.COLOR_BGR2HSV)[:, :, 1].mean()) < 60:
            return True
        return bool(self.v.find(frame, "loading_text", 0.8) or self.v.find(frame, "loading_logo", 0.8)
                    or self.v.find(frame, "live_replay", 0.85))

    def close_popup(self, frame):
        """A window's red X (events, league overview, settings, news...): tap it. Only a bright red one near the
        top right - a dimmed X sits under another layer. True if it tapped."""
        H, W = frame.shape[:2]
        hit = self.find_any_zoom(frame, "popup_close", 0.6)
        if not hit or hit[0] < 0.7 * W or hit[1] > 0.3 * H:
            return False
        c = frame[max(0, hit[1] - 30):hit[1] + 30, max(0, hit[0] - 30):hit[0] + 30].astype(int)
        if ((c[:, :, 2] > 160) & (c[:, :, 2] - c[:, :, 1] > 90) & (c[:, :, 2] - c[:, :, 0] > 90)).mean() < 0.45:
            return False
        self.log("Closing a popup (its X).")
        self.tap(hit, 1.2)
        return True

    def event_chest(self, frame):
        """Chest event (after a 'Claim Reward' victory): the chest room - tap the chest until it opens (4 hammer
        taps for a common one), then the reward's Continue. Never Skip: that asks 'Skip Chest opening?' and needs a
        Yes. The room is told by its scenery (Skip only shows sometimes). True if it was showing."""
        in_room = lambda f: self.v.find(f, "chest_room", 0.78) or self.v.find(f, "chest_skip", 0.8)
        hit = self.find(frame, "chest_continue")
        if hit:
            self.log("Event chest opened.", "ok")
            self.tap(hit, 1.5)
            return True
        if not in_room(frame):
            return False
        for _ in range(10):
            self.tap((960, 600), 0.8)
            f = self.shot()
            hit = self.find(f, "chest_continue")
            if hit:
                self.log("Event chest opened.", "ok")
                self.tap(hit, 1.5)
                return True
            if not in_room(f):
                return True  # moved on by itself
        return True

    def pick_reward(self, frame):
        """'Pick a Reward!' (shown mid-battle at star milestones) covers Surrender until a card is taken. Take the
        resource card (elixir / gold / dark elixir pile), else the middle one. True if it was showing."""
        if not self.v.find(frame, "pick_reward_title", 0.85):
            return False
        k = frame.shape[1] / 1920
        hsv = cv2.cvtColor(frame, cv2.COLOR_BGR2HSV)
        best, pick = 1500 * k * k, (int(964 * k), int(560 * k))  # a troop card scores ~300 (its level badge)
        for x in (578, 964, 1350):
            c = hsv[int(440 * k):int(600 * k), int((x - 120) * k):int((x + 120) * k)]
            h, s, v = c[:, :, 0], c[:, :, 1], c[:, :, 2]
            n = (((h >= 135) & (h <= 165) & (s > 120) & (v > 150)).sum()  # elixir
                 + ((h >= 18) & (h <= 32) & (s > 150) & (v > 180)).sum()  # gold
                 + ((h >= 120) & (h <= 170) & (s > 80) & (v >= 40) & (v <= 120)).sum())  # dark elixir
            if n > best:
                best, pick = n, (int(x * k), int(560 * k))
        self.tap(pick, 1.0)
        self.log("Picked a battle reward.")
        return True

    # --- walls ---
    def walls_progress(self, paid):
        """Walls just bought: move that many of the lowest walls up a level in this account's scan, so the
        dashboard's Walls card is current without waiting for the next export (price / one wall = how many)."""
        sd = ((self.cfg.get("scans") or {}).get(self._last_name) or {}).get("home") or {}
        counts, mx, todo, _ = walls_left(sd)
        low = min((lv for lv in counts if mx and lv < mx), default=None)
        if low is None or not paid:
            return
        n = min(counts[low], max(1, round(paid / wiki_data()["home:wall"]["levels"][low]["cost"])))
        rows = [r for r in sd["items"] if r.get("key") == "home:wall"]
        for r in rows:
            if r["level"] == low:
                r["count"] -= n
                break
        up = next((r for r in rows if r["level"] == low + 1), None)
        if up:
            up["count"] += n
        else:
            sd["items"].append({"key": "home:wall", "name": "Wall", "level": low + 1, "count": n, "upgrading": False})
        sd["items"] = [r for r in sd["items"] if r.get("count", 1) > 0]
        save_config(self.cfg)
        self.emit("scan", self._last_name)

    def wall_price(self):
        """Cost of the next wall upgrade (the lowest wall that isn't max), 0 if every wall is max, None if this
        account's walls haven't been scanned."""
        if self.ambiguous():
            return None  # not sure whose walls these are
        sd = ((self.cfg.get("scans") or {}).get(self._last_name) or {}).get("home") or {}
        counts, mx, todo, _ = walls_left(sd)
        if not counts or not mx:
            return None
        if not todo:
            return 0
        return wiki_data()["home:wall"]["levels"][min(lv for lv in counts if lv < mx)]["cost"]

    def spend_bank(self, storage, threshold=None):
        thr = threshold or self.cfg["bank_spend_threshold"]
        if not any((storage.get(c) or 0) >= thr for c in ("gold", "elixir")):
            return False
        if time.time() < self._bank_backoff.get("builder", 0):
            return False
        if self.free_slots(self.shot(), "builder") == 0:  # walls are instant but still need a free builder
            self._bank_backoff["builder"] = time.time() + 600
            self.log("Walls: every builder is busy (the game needs a free one even for walls) - farming on, "
                     "checking again in 10 min.")
            return False
        did = False
        for cur in ("gold", "elixir"):
            val = storage.get(cur)
            if val is None or val < (threshold or self.cfg["bank_spend_threshold"]):
                continue
            if time.time() < self._bank_backoff.get(cur, 0):
                continue
            self.sleep(0.5)
            region = self.cfg["ocr_regions"].get(f"bank_{cur}_region") or (0, 0, 1, 1)
            again = white_number(self.shot(), region)
            if again is None:  # the counter mid-animation (just after a battle): one more look
                self.sleep(1.0)
                again = white_number(self.shot(), region)
            if again != val:  # a one-off misread (e.g. 1.7M read as 17M) must never trigger a purchase
                self.log(f"{cur.title()} read {val:,} then {again} - not sure, skipping this time.", "warn")
                continue
            did = True
            if self.buy_wall(cur, val):
                self.walls_progress(getattr(self, "_wall_paid", 0))
            elif getattr(self, "_no_wall_rows", False):  # no 'Wall' row on the list: they're all max here
                self._bank_backoff.update(gold=time.time() + 6 * 3600, elixir=time.time() + 6 * 3600)
                self.log("Walls: every wall on this account is max - not looking again for 6 h.", "ok")
                break
            else:
                self._bank_backoff[cur] = time.time() + 300
                self.log(f"Couldn't buy a {cur} wall - trying again in 5 min.", "warn")
        return did

    def find_wall_rows(self, frame):
        """'Wall' rows in the open builder list, via Tesseract word search (clean white-on-dark text). Only inside
        the list: a selected wall's own bar says 'Remove Wall' / 'Add Wall', and those must never be tapped."""
        box = panel_box(frame)
        if not HAVE_TESS or not box:
            return []
        x0, x1, y0, y1 = box
        gray = cv2.cvtColor(frame[y0:y1, x0:x1], cv2.COLOR_BGR2GRAY)
        try:
            d = pytesseract.image_to_data(gray, config="--psm 11", output_type=pytesseract.Output.DICT, timeout=8)
        except Exception:
            return []
        return [(x0 + d["left"][i] + d["width"][i] // 2, y0 + d["top"][i] + d["height"][i] // 2)
                for i, t in enumerate(d["text"]) if t.strip().lower().startswith("wall")]

    def wall_fail(self, why, frame):
        cv2.imwrite(os.path.join(BASE_DIR, "debug_wall.png"), frame)
        self.log(f"Wall upgrade: {why}. Screen saved as debug_wall.png.", "warn")
        self.close_popups()
        return False

    def bar_price(self, frame, btn):
        """Price printed above an Upgrade button: white when affordable, red when not."""
        k = frame.shape[1] / 1920
        c = crop(frame, (btn[0] - int(100 * k), btn[1] - int(78 * k), btn[0] + int(60 * k), btn[1] - int(33 * k)), 0)
        if c is None:
            return None
        hsv = cv2.cvtColor(c, cv2.COLOR_BGR2HSV)
        b, g, r = (c[:, :, i].astype(int) for i in range(3))
        white = (hsv[:, :, 2] > hsv[:, :, 2].max() * 0.8) & (hsv[:, :, 1] < 70)
        red = (r > 170) & (r - g > 70) & (r - b > 50)
        return read_digit_blobs(white | red)

    def upgrade_pair(self, frame):
        """The Upgrade More bar's two double-hammer Upgrade buttons as (gold, elixir) - gold is always the left one.
        Matched on the hammers only, so the price (1,500,000 / 5,000,000 ...) doesn't matter. None if not showing."""
        hits = self.wall_hammers(frame)
        if len(hits) != 2 or abs(hits[0][0] - hits[1][0]) < 80 * frame.shape[1] / 1920:
            return None
        return tuple(hits)

    def wall_hammers(self, frame):
        """The Upgrade More bar's double-hammer Upgrade buttons, left to right: home has gold + elixir, the Builder
        Base just Builder Gold (until its walls take Builder Elixir too)."""
        t = self.v.template("wall_upgrade_hammers")
        if t is None:
            return []
        small = cv2.resize(frame, None, fx=SCALE, fy=SCALE, interpolation=cv2.INTER_AREA)
        res = cv2.matchTemplate(small, t[2], cv2.TM_CCOEFF_NORMED)
        th, tw = t[1]
        hits = []
        for _ in range(2):
            _, v, _, loc = cv2.minMaxLoc(res)
            if v < 0.8:
                break
            hits.append((int(loc[0] / SCALE + tw / 2), int(loc[1] / SCALE + th / 2)))
            x0, y0 = loc
            res[max(0, y0 - th // 4):y0 + th // 4, max(0, x0 - tw // 2):x0 + tw // 2] = -1  # next peak elsewhere
        return sorted(h for h in hits if abs(h[1] - hits[0][1]) < 40)  # same bar row

    def select_wall(self, kind="builder"):
        """Open the builder list (kind 'bb_builder': the Builder Base's), tap a 'Wall' row once the list has stopped
        sliding, close the list. Returns the Upgrade More button if a wall really is selected, else None."""
        icon = top_bar(self.shot(), kind)[0]
        frame = self.shot()
        rows = self.find_wall_rows(frame)
        opened = bool(rows)
        if not rows:  # list not open yet
            self.tap(icon, 1.2)
            prev = None
            for _ in range(10):
                frame = self.shot()
                rows = self.find_wall_rows(frame)
                if rows:
                    break
                box = panel_box(frame)
                if not box:  # not open (yet): never swipe then - it would drag the village (onto the boat...)
                    if self.v.find(frame, "all_upgrades_complete", 0.85):  # a fully maxed village: no list at all
                        opened = True
                        break
                    self.sleep(0.6)
                    continue
                opened = True
                roi = cv2.cvtColor(frame, cv2.COLOR_BGR2GRAY)[150:-150:4, ::4]
                if prev is not None and cv2.absdiff(roi, prev).mean() < 2:
                    break  # list stopped moving: reached the bottom
                prev = roi
                self.scroll_panel(box)  # inside the list only
        self._no_wall_rows = opened and not rows  # the list opened, scrolled to the end: no 'Wall' row = all max
        if not rows:
            if panel_box(self.shot()):
                self.tap(icon, 1.0)
            return None
        for _ in range(6):  # wait until two reads agree on where the row is (the list glides after a swipe)
            self.sleep(0.4)
            again = self.find_wall_rows(self.shot())
            if again and abs(again[0][1] - rows[0][1]) <= 4:
                rows = again
                break
            rows = again or rows
        # one 'Wall xN' row per level, not in price order ('Wall x112 1,500,000' above 'Wall x184 1,000,000'):
        # take the cheapest affordable one. A row at the bottom edge may have another just under it - nudge up.
        box = panel_box(self.shot())
        if box and max(y for _, y in rows) > box[3] - 90:
            cx = (box[0] + box[1]) // 2
            self.adb.swipe(cx, box[3] - 60, cx, box[3] - 260, 700)
            self.sleep(1.2)
            rows = self.find_wall_rows(self.shot()) or rows
        f = self.shot()
        box = panel_box(f)
        if box and len(rows) > 1:  # unaffordable prices are red, read as None: those go last
            rows = sorted(rows, key=lambda r: white_number(f, (box[1] - 200, r[1] - 20, box[1] - 10, r[1] + 20))
                          or 10 ** 12)
        self.tap(rows[0], 1.2)
        f = self.shot()
        if panel_box(f):  # the list sometimes stays open over the buttons: its icon closes it
            self.tap(icon, 1.2)
        name = self.selected_label(self.shot())[0]
        other = (wiki_key(name, "home") if kind == "builder" else None if is_wall(name) else name) if name else None
        if other and other != "home:wall":  # only walls have Upgrade More - this catches a clearly different
            # building ('Cannon (Level 21)')
            self.log(f"Wall upgrade: the tap selected '{name}', not a wall.", "warn")
            return None
        end = time.time() + 3  # only walls have 'Upgrade More' (greyed/red when it's the only wall of its level)
        while True:
            f = self.shot()
            if (self.upgrade_pair(f) if kind == "builder" else self.wall_hammers(f)):  # Upgrade More bar already
                # open: its greyed 'Remove Wall' isn't Upgrade More
                return "open"
            hit = self.find(f, "upgrade_more_button") or self.find(f, "upgrade_more_disabled")
            if hit or time.time() > end:
                return hit
            self.sleep(0.5)

    def buy_wall(self, cur, balance=None, kind="builder"):
        """Builder list -> 'Wall' row (selects a wall) -> close list -> Upgrade More -> Upgrade in `cur`
        -> Okay, but only if the dialog really says it upgrades Walls for `cur` (never gems). kind 'bb_builder':
        the Builder Base's walls (its Upgrade More bar starts at 1 wall: Add Wall until it's what we can pay)."""
        bb = kind == "bb_builder"
        region = self.cfg["ocr_regions"].get(f"bank_{cur}_region")
        frame = self.shot()
        if balance is None and region:
            balance = white_number(frame, region)
        for attempt in range(3):  # a slid list can land the tap on the wrong building: just try again
            # always a fresh pick from the list: a bar left from the last purchase holds walls a level higher now
            more = self.select_wall(kind)
            if more or self._no_wall_rows:  # no wall on the list at all: retrying won't help
                break
            self.log(f"Wall upgrade: didn't get a wall selected (attempt {attempt + 1}/3) - retrying.")
        else:
            return self.wall_fail("couldn't select a wall", self.shot())
        if not more:
            return False  # every wall is max (the caller says so)
        f = self.shot()
        lab = f[more[1] + 10:more[1] + 50, more[0] - 70:more[0] + 70].astype(int) if more != "open" else None
        disabled = lab is not None and ((lab[:, :, 2] > 170) & (lab[:, :, 2] - lab[:, :, 1] > 70) & (lab[:, :, 2] - lab[:, :, 0] > 50)).mean() > 0.08
        if disabled:
            # Only one wall of this level: 'Upgrade More' is greyed out (red text), so upgrade this single wall with
            # the bar's own gold (left) / elixir (right) Upgrade button, which sits a fixed distance to the right.
            k = f.shape[1] / 1920
            bx = int(more[0] + (211 if cur == "gold" else 425) * k)
            want = white_number(f, (bx - int(100 * k), more[1] - int(134 * k), bx + int(60 * k), more[1] - int(89 * k)))
            if not want:
                return self.wall_fail("single wall: couldn't read its price (can't afford it?)", f)
            if balance is not None and want > balance:
                return self.wall_fail(f"single wall costs {want:,} but storage is {balance:,} - not buying", f)
            self.log(f"Only one wall at this level - upgrading it on its own ({want:,} {cur}).")
            self.tap((bx, more[1] - int(40 * k)), 1.5)
        else:
            want = None
            if more != "open":
                self.tap(more, 1.2)
            pair, end = None, time.time() + 4
            while not pair and time.time() < end:
                pair = self.wall_hammers(self.shot()) if bb else self.upgrade_pair(self.shot())
                if not pair:
                    self.sleep(0.4)
            if not pair or (cur != "gold" and len(pair) < 2):
                return self.wall_fail("Upgrade More bar's Upgrade buttons not found", self.shot())
            btn = pair[0] if cur == "gold" else pair[1]
            k = f.shape[1] / 1920
            # bar layout: home - Remove Wall, Add +10, Add +1, gold, elixir; Builder Base - Remove Wall, Add Wall, gold..
            remove = (pair[0][0] - int((424 if bb else 612) * k), pair[0][1] + int(12 * k))
            if bb and balance:  # Builder Base: it starts with 1 wall - add walls while the next one is affordable
                unit = self.bar_price(self.shot(), btn)
                add = (pair[0][0] - int(212 * k), pair[0][1] + int(12 * k))
                cost, same = unit, 0
                while unit and cost and cost + unit <= balance and same < 2:  # quick bursts, then re-read the total
                    for _ in range(min((balance - cost) // unit, 20)):     # (taps that fast can drop a few)
                        self.adb.tap(*add)
                        time.sleep(0.15)
                    self.sleep(0.6)
                    new = self.bar_price(self.shot(), btn)
                    same = same + 1 if new == cost else 0  # no more walls of this level to add
                    cost = new
            for _ in range(20):  # home: Upgrade More selects a whole row - drop walls (-1) until it's affordable
                f = self.shot()
                cost = self.bar_price(f, btn)
                if cost is None or balance is None or cost <= balance:
                    break
                self.tap(remove, 0.7)
            self.tap(btn, 1.2)
        ok = self.wait_for("wall_okay_button", 3 if want is None else 1)  # it animates in (slower at 30 FPS)
        frame = self.shot()
        if ok:  # 'Upgrade Walls' dialog: check it says Walls + this currency + a price, never gems
            h, w = frame.shape[:2]
            try:
                text = pytesseract.image_to_string(cv2.cvtColor(frame[h * 2 // 5:h * 11 // 20, w // 4:w * 3 // 4],
                                                                cv2.COLOR_BGR2GRAY), timeout=8).lower()
            except Exception:
                text = ""
            price = max((int(x) for x in re.findall(r"\d{4,}", text.replace(" ", "").replace(",", ""))), default=None)
            if "wall" not in text or cur not in text or "gem" in text or price is None:
                return self.wall_fail(f"upgrade dialog didn't check out ({text.strip()[:80]!r})", frame)
        else:  # single wall: the normal upgrade window - the green resource Confirm must show the same price
            ok = self.wait_for("confirm_wall_upgrade_button", 4)
            shown = white_number(self.shot(), (ok[0] - 160, ok[1] + 12, ok[0] + 130, ok[1] + 75)) if ok else None
            if not ok or not want or shown != want:
                return self.wall_fail(f"upgrade window didn't check out (price {shown} vs {want})", self.shot())
            price = want
        if balance is not None and price > balance:
            return self.wall_fail(f"costs {price:,} but storage is {balance:,} - not buying", frame)
        self.tap(ok, self.cfg["bank_post_spend_delay"])
        after = white_number(self.shot(), region) if region else None
        if balance is not None and after is not None and after > balance - price * 0.9:
            self.sleep(1.5)  # the counter animates down; look once more
            after = white_number(self.shot(), region)
        if balance is not None and after is not None and after > balance - price * 0.9:
            return self.wall_fail(f"{cur} didn't drop ({balance:,} -> {after:,}), so it didn't go through",
                                  self.shot())
        self.bump("walls")
        self._wall_paid = price
        self.log(f"Bought a wall upgrade for {price:,} {cur}"
                 + (f" ({balance:,} -> {after:,})." if balance is not None and after is not None else "."), "ok")
        return True  # the wall bar left open doesn't block Attack

    # --- Builder Base ---
    def at_village(self, f):
        return self.find(f, "attack_button") or self.find(f, "bb_attack_button")

    def matches(self, frame, name, conf=0.8):
        """Every place a (small) template shows, e.g. all collector bubbles - at the zoom levels a village is
        seen at (the boat trip leaves the Builder Base a little zoomed out: bubbles ~0.9x)."""
        t = self.v.template(name)
        if t is None:
            return []
        small = cv2.resize(frame, None, fx=SCALE, fy=SCALE, interpolation=cv2.INTER_AREA)
        hits = []
        for z in (1.0, 0.92, 0.85):
            tt = cv2.resize(t[2], None, fx=z, fy=z, interpolation=cv2.INTER_AREA)
            r = cv2.matchTemplate(small, tt, cv2.TM_CCOEFF_NORMED)
            hits += [(r[y, x], int((x + tt.shape[1] / 2) / SCALE), int((y + tt.shape[0] / 2) / SCALE))
                     for y, x in zip(*np.where(r >= conf))]
        out = []
        for _, x, y in sorted(hits, reverse=True):
            if all(abs(x - a) > 30 or abs(y - b) > 30 for a, b in out):
                out.append((x, y))
        return out

    def find_any_zoom(self, frame, name, conf=0.75):
        """Like find(), but also at the smaller/larger sizes things have when the camera is zoomed out/in
        (Clash remembers each village's zoom, so it differs between accounts and PCs)."""
        t = self.v.template(name)
        if t is None:
            return None
        small = cv2.resize(frame, None, fx=SCALE, fy=SCALE, interpolation=cv2.INTER_AREA)
        best = (0, None)
        for z in (1.0, 0.92, 0.85, 0.72, 0.62, 1.15):
            tt = cv2.resize(t[2], None, fx=z, fy=z, interpolation=cv2.INTER_AREA)
            if tt.shape[0] > small.shape[0] or tt.shape[1] > small.shape[1] or min(tt.shape[:2]) < 6:
                continue
            _, v, _, loc = cv2.minMaxLoc(cv2.matchTemplate(small, tt, cv2.TM_CCOEFF_NORMED))
            if v > best[0]:
                best = (v, (int((loc[0] + tt.shape[1] / 2) / SCALE), int((loc[1] + tt.shape[0] / 2) / SCALE)))
        return best[1] if best[0] >= conf else None

    def take_boat(self, to):
        """Home <-> Builder Base: find the boat's sail bubble and tap it. True once the other village shows.
        Where the boat is depends on the village and its level (a big Builder Base has it bottom-right, by the
        Outpost), and the camera may be anywhere after an upgrade - so pan the usual way first, then sweep."""
        want = "bb_attack_button" if to == "builder" else "attack_button"
        L, R, U, D = (600, 500, 1300, 500), (1300, 500, 600, 500), (960, 300, 960, 700), (960, 700, 960, 300)
        usual = [(700, 450, 1300, 250)] * 3 if to == "builder" else [(1300, 300, 800, 600)] * 3
        sweep = usual + [L] * 3 + [U] * 2 + [R] * 5 + [D] * 4 + [L] * 5 + [U] * 2
        if to == "home":
            self.bb_collect()  # collectors + the Elixir Cart before leaving (it moves the camera, so first)
        for _ in range(2):
            boat = self.find_any_zoom(self.shot(), "bb_boat")
            if not boat:  # zoomed in (e.g. after an upgrade on the far village): zoom out so the sweep covers the map
                zoom_out(self.adb)
                self.sleep(0.8)
                boat = self.find_any_zoom(self.shot(), "bb_boat")
            for mv in sweep:
                if boat:
                    break
                self.adb.swipe(*mv, 450)
                self.sleep(0.9)
                boat = self.find_any_zoom(self.shot(), "bb_boat")
            if boat:
                if boat[1] < 200 or boat[0] > 1500:  # under the resource bars: a tap there opens the bar's
                    # tooltip (which then hides the boat) - drag the map to bring the boat toward the middle
                    self.adb.swipe(960, 540, 960 + (960 - boat[0]) // 2, 540 + (540 - boat[1]) // 2, 600)
                    self.sleep(1.0)
                    boat = self.find_any_zoom(self.shot(), "bb_boat") or boat
                self.tap(boat, 2.0)
                if self.wait_for(want, 25, poll=1.0):
                    self.sleep(1.0)
                    return True
            self.back_to_village()
        cv2.imwrite(os.path.join(BASE_DIR, "debug_boat.png"), self.shot())
        return False

    def bb_collect(self):
        """Tap every gold / elixir / gem bubble. One of the elixir bubbles is the Elixir Cart: its window gets Collect."""
        f = self.shot()
        H, W = f.shape[:2]
        # only bubbles in the open middle: one sitting over the edge buttons (Season Pass, Attack, Shop, the
        # resource bars...) would tap that button instead. It gets collected another time.
        safe = lambda p: 0.13 * W < p[0] < 0.87 * W and 0.11 * H < p[1] < 0.76 * H
        for xy in filter(safe, self.matches(f, "bb_elixir_bubble", 0.7) + self.matches(f, "bb_gold_bubble", 0.7)
                         + self.matches(f, "bb_gem_bubble", 0.7)):
            self.tap(xy, 1.0)
            if self.find(self.shot(), "bb_cart_title"):  # that bubble was the cart's
                self.cart_window()
        self.bb_cart()

    def cart_window(self):
        """The Elixir Cart window is open: Collect if the button is green (grey = nothing in it), then close."""
        f = self.shot()
        btn = self.find(f, "bb_cart_collect")
        if btn:
            hsv = cv2.cvtColor(f[btn[1] - 25:btn[1] + 25, btn[0] - 90:btn[0] + 90], cv2.COLOR_BGR2HSV)
            if ((hsv[:, :, 0] > 30) & (hsv[:, :, 0] < 90) & (hsv[:, :, 1] > 120)).mean() > 0.25:
                self.tap(btn, 1.2)
                self.log("Builder Base: collected the Elixir Cart.", "ok")
        self.adb.back()
        self.sleep(1.0)

    def bb_cart(self):
        """The Elixir Cart stands by the dock, next to the boat - often off the top of the screen. Bring the dock
        into the middle, then tap the cart (found by its bubble / look / usual spot)."""
        zoom_out(self.adb)
        self.sleep(0.8)
        boat = self.find_any_zoom(self.shot(), "bb_boat")
        for _ in range(4):  # the dock is at the top right of the island: look that way (as the boat trip does)
            if boat:
                break
            self.adb.swipe(1300, 300, 800, 600, 450)
            self.sleep(0.9)
            boat = self.find_any_zoom(self.shot(), "bb_boat")
        if not boat:  # the boat hides behind the side buttons at the map's edge - but the cart's bubble may show
            f = self.shot()
            for xy in [p for p in self.matches(f, "bb_elixir_bubble", 0.7) if 250 < p[0] < 1650 and 150 < p[1] < 820]:
                self.tap(xy, 1.2)
                if self.find(self.shot(), "bb_cart_title"):
                    return self.cart_window()
            return
        if abs(boat[0] - 1150) > 120 or abs(boat[1] - 520) > 120:  # dock into the middle: the cart is beside it
            self.adb.swipe(960, 540, 960 + 1150 - boat[0], 540 + 520 - boat[1], 900)
        self.sleep(1.5)  # the map glides on after a drag
        f = self.shot()
        boat = self.find_any_zoom(f, "bb_boat") or boat
        near = lambda p: (abs(p[0] - boat[0]) < 650 and abs(p[1] - boat[1]) < 450 and 250 < p[0] and 120 < p[1] < 820
                          and (p[0] < 1450 or p[1] > 320))  # ...and clear of the resource bars / buttons
        # where the cart is: its bubble (shows when there's elixir in it - an empty cart has nothing to collect) or
        # its full look. Never a guessed spot: the dock's layout differs by Builder Hall level, and a blind tap can
        # select an obstacle ('Remove').
        spots = sorted(filter(near, self.matches(f, "bb_elixir_bubble", 0.7)),
                       key=lambda p: abs(p[0] - boat[0]) + abs(p[1] - boat[1]))
        spots += list(filter(near, filter(None, [self.find_any_zoom(f, "bb_cart", 0.75)])))
        for xy in spots[:3]:
            self.tap(xy, 1.2)
            if self.find(self.shot(), "bb_cart_title"):
                return self.cart_window()

    def bb_bonus(self, name):
        """Collect the 'Star Bonus!' popup if it's showing. True if one was collected just now."""
        f = self.shot()
        if not self.find(f, "bb_bonus_title"):
            return False
        ok = self.find(f, "bb_bonus_okay")
        if ok:
            self.tap(ok, 1.5)
        else:  # never a blind tap: Back closes the popup (the bonus is already credited)
            self.adb.back()
            self.sleep(1.5)
        self.log(f"Star Bonus collected ({name}).", "ok")
        return True

    def bb_clock_boost(self):
        """The Clock Tower's free boost (everything 10x faster for ~30 min, free once per 22h). Its bubble only
        shows when it's ready; only a button that says 'Free Boost!' is pressed - never the gem one."""
        bub = self.find_any_zoom(self.shot(), "bb_clock_bubble", 0.8)
        if not bub:
            return
        self.tap(bub, 1.5)
        free = self.wait_for("bb_free_boost", 3)
        if free:
            self.tap(free, 1.5)
            if self.wait_for("bb_boost_title", 3):
                btn = self.find(self.shot(), "bb_boost_button")
                if btn:
                    self.tap(btn, 1.5)
                    self.log("Builder Base: Clock Tower free boost started (10x speed).", "ok")
        self.back_to_village()

    def bb_stars(self, f):
        """(earned, needed) of today's star bonus from the Builder Base Attack button, or None."""
        return read_counter(f, BB_STARS)

    def bb_attack(self):
        """One Builder Base battle: Attack -> Find Now -> drop every card on the open ground at the left ->
        Battle Machine ability -> wait for Return Home. Builder Base bases can't be skipped; loot isn't read."""
        for _ in range(2):  # the first tap only deselects a building that's still selected
            self.tap(self.find(self.shot(), "bb_attack_button") or (125, 955), 1.5)
            find = self.wait_for("bb_find_now", 4)
            if find:
                break
        if not find:
            return self.log("Builder Base: Find Now didn't show.", "warn")
        self.tap(find, 1.0)
        cards, end = [], time.time() + 40
        while not cards and time.time() < end:  # matchmaking, then the battle screen with the troop bar
            self.sleep(1.5)
            cards = [c for c in troop_bar(self.shot()) if c[2] in ("hero", "single", "troop")]
        if not cards:
            return self.log("Builder Base: no battle screen after Find Now.", "warn")
        self.bump("attacks")
        self.bb_deploy(cards)
        self.log(f"Builder Base: attacking with {len(cards)} cards.", "ok")
        end = time.time() + 420  # up to two stages of 3 min each
        while time.time() < end:  # the battle ends by itself once every troop is down (or the timer runs out)
            self.sleep(6)
            f = self.shot()
            done = self.find(f, "bb_return_home")
            if done:
                self.tap(done, 3.0)
                if not self.wait_for("bb_attack_button", 15):
                    return None
                if self.mode.startswith("bb_"):  # the session's Builder Base loot / hour: storage after every battle
                    self.sleep(1.5)
                    f = self.shot()
                    self.track_bb(self.account_name(f), self.read_storage(f, village="builder"))
                return True
            # 100% on stage 1 starts stage 2 with extra cards (+ the survivors): drop everything not used up.
            # Tapping an already-deployed card is harmless (the Battle Machine's = its ability).
            self.bb_deploy([c for c in troop_bar(f) if c[2] in ("hero", "single", "troop")])
        self.log("Builder Base: battle didn't finish in time.", "warn")

    def bb_deploy(self, cards):
        a, b = (390, 380), (260, 600)  # left edge of the map: always outside the base, clear of the Boost buttons
        for k, (x, y, kind, n) in enumerate(cards):
            self.tap((x, y), self.speed()[1])
            for i in range(n or 1):
                self.adb.tap(*self.along(a, b, (k + i) % len(cards), len(cards)))
            self.sleep(0.2)

    def builder_base(self):
        """Once per account every few hours: boat over, collect (incl. the Elixir Cart), keep the builders and
        Star Lab busy, attack until today's star bonus is complete, collect again, boat back."""
        name = self._last_name
        for _ in range(3):  # just after arriving / switching, popups and the XP bar can hide the name for a moment
            if name and name != "?":
                break
            self.sleep(1.0)
            name = self.account_name(self.shot())
        if time.time() < self._bb_next.get(name, 0):
            return False
        # unreadable name: visit anyway, but only block re-visits briefly (it may be a different account next time)
        self._bb_next[name] = time.time() + (600 if name == "?" else 3600 * self.cfg["bb_visit_hours"])
        self.log(f"Builder Base visit ({name}).", "ok")
        if not self.take_boat("builder"):
            self._bb_next[name] = time.time() + 1800
            self.log("Builder Base: couldn't take the boat - trying again in 30 min (screen: debug_boat.png).", "warn")
            return True
        self.emit("state", f"Builder Base ({name})")
        self.bb_collect()
        self.bb_clock_boost()  # first, while the arrival view shows the whole base (its bubble is on the tower)
        self.bb_session(name, upgrades=True)
        self.take_boat("home")  # collects again first: the session's attacks filled the Elixir Cart
        return True

    def bb_session(self, name, upgrades=True):
        """On the Builder Base: upgrades, attacks until today's Star Bonuses are collected, upgrades again (the loot
        may pay for more). Builder Base attacks only pay out through the Star Bonus - after that, nothing."""
        c = self.cfg
        for rnd in range(2):
            if upgrades:
                self.bb_upgrades()
            if rnd or not (c["bb_attacks_enabled"] or self.mode.startswith("bb_")):
                break
            self.bb_attacks(name)
            self._upgrade_backoff.pop("bb_builder", None)
            self._upgrade_backoff.pop("bb_lab", None)

    def bb_upgrades(self):
        """Keep the Builder Base builders + Star Lab busy: the next target in this account's plan (or wait for it),
        else the most expensive thing affordable. True if any builder / the Star Lab is still free afterwards."""
        free, self._bb_saving = False, None
        for kind in ("bb_builder", "bb_lab"):
            if not self.cfg["bb_builder_upgrades" if kind == "bb_builder" else "bb_lab_upgrades"]:
                continue
            if kind == "bb_lab" and self._bb_saving == "elixir":
                self.log("Star Lab: waiting - the Builder Base plan is saving Builder Elixir for its next upgrade.")
                continue
            for _ in range(3):
                if not self.free_slots(self.shot(), kind):
                    self.maybe_rescan(kind)
                    break
                n = self.stats["upgrades"]
                self.upgrade_from_list(kind)
                if self.stats["upgrades"] == n:
                    free = True  # a slot is free but nothing was bought: saving up for it
                    break
        return free

    def bb_done_today(self, name):
        return self.cfg["bb_bonus_days"].get(name) == time.strftime("%Y-%m-%d")

    def bb_attacks(self, name):
        """Attack until today's Star Bonuses are all collected."""
        last = None
        # Star Bonus: a popup each time the counter fills, several times a day. Once they're used up the counter
        # just rolls over with no popup - then this account is done until tomorrow.
        for _ in range(12):
            if self.bb_done_today(name):
                if not self.mode.startswith("bb_"):
                    self.log("Builder Base: no Star Bonus left today - no attacks.")
                break
            if self.bb_bonus(name):
                last = None  # the counter restarts after a bonus: that's not a 'rolled over without one'
            f = self.shot()
            if not self.find(f, "bb_attack_button"):  # still in a battle / its end screen: never press Back here
                done = self.wait_for("bb_return_home", 240, poll=3)
                if done:
                    self.tap(done, 3.0)
                if not self.wait_for("bb_attack_button", 15):
                    self.log("Builder Base: not back on the village - stopping the attacks.", "warn")
                    break
                f = self.shot()
            st = self.bb_stars(f)
            if not st:  # the counter disappears from the Attack button once today's bonuses are all used
                if name != "?":
                    self.cfg["bb_bonus_days"][name] = time.strftime("%Y-%m-%d")
                    save_config(self.cfg)
                self.log("Builder Base: all of today's Star Bonuses collected - done until tomorrow.", "ok")
                break
            if last and st[0] < last[0]:  # rolled over with no popup: today's bonus was already taken
                if name != "?":
                    self.cfg["bb_bonus_days"][name] = time.strftime("%Y-%m-%d")
                    save_config(self.cfg)
                self.log("Builder Base: star counter rolled over without a bonus - done for today.", "ok")
                break
            last = st
            self.log(f"Builder Base: stars {st[0]}/{st[1]} - attacking.")
            self.bb_attack()

    def track_bb(self, name, s):
        """Builder Base loot this session: what the storages gained since the last read on this account (battles,
        Star Bonuses, the Elixir Cart, collectors) - read after every battle. ponytail: an upgrade bought in
        between hides that stretch's gain."""
        now, n, ups = (s.get("gold"), s.get("elixir")), self.stats["attacks"], self.stats["upgrades"]
        pre = getattr(self, "_bb_pre", None)
        if None in now or "?" in name:
            return  # unreadable: keep the last good read as the baseline
        if not pre or pre[0] != name:
            self._bb_pre = (name, now, n, ups)
            return
        # a drop with nothing bought = a misread (e.g. a lost digit): keep the old baseline, or the read after it
        # would count the 'recovery' as loot
        drop = ups == pre[3] and any(a < b * 0.9 for a, b in zip(now, pre[1]))
        self._bb_drops = getattr(self, "_bb_drops", 0) + 1 if drop else 0
        if drop and self._bb_drops < 2:  # twice in a row: it's real (spent by hand) - take it as the new baseline
            return
        self._bb_pre = (name, now, n, ups)
        gain = [max(0, a - b) for a, b in zip(now, pre[1])]
        if max(gain) > 5_000_000 or not (any(gain) or n > pre[2]):  # more in one go = a misread
            return
        row = self.loot.setdefault(name, [0, 0, 0, 0])
        row[0], row[1], row[3] = row[0] + gain[0], row[1] + gain[1], row[3] + n - pre[2]
        self.emit("loot", {a: list(r) for a, r in self.loot.items()})
        if any(gain):
            self.log(f"{name}: +{gain[0]:,} Builder Gold, +{gain[1]:,} Builder Elixir")

    def bb_walls(self, name):
        """'BB walls': upgrade Builder Base walls whenever Builder Gold (or Builder Elixir, for walls that take it)
        pays for one; otherwise attack a round to farm more. Stops once every wall is max."""
        f = self.shot()
        store = self.read_storage(f, village="builder")
        bought = False
        if self.free_slots(f, "bb_builder") == 0:
            self.log("BB walls: every Builder Base builder is busy (walls need a free one) - farming a round.")
        else:
            for cur in ("gold", "elixir"):
                bal = store.get(cur)
                if not bal or time.time() < self._bank_backoff.get("bb_" + cur, 0):
                    continue
                if self.buy_wall(cur, bal, "bb_builder"):  # counts + logs it
                    bought = True
                    store = self.read_storage(self.shot(), village="builder")
                elif getattr(self, "_no_wall_rows", False):
                    self.log("BB walls: no walls left to upgrade on the Builder Base - stopping.", "ok")
                    self.stop_evt.set()
                    raise Abort()
                else:  # can't afford one in this resource (or its walls don't take it): farm, look again later
                    self._bank_backoff["bb_" + cur] = time.time() + (600 if cur == "gold" else 3600)
        if bought:
            return  # look again: there may be enough for more
        for _ in range(5):
            self.bb_bonus(name)
            if not self.find(self.shot(), "bb_attack_button") and not self.wait_for("bb_attack_button", 20):
                return
            self.bb_attack()
        self._bank_backoff.pop("bb_gold", None)  # new loot: try again
        self.bb_collect()

    def bb_only(self):
        """'Builder Base only' modes: stay on the Builder Base.
        bb_loot: attack non-stop on this account, claiming the Elixir Cart every 10 attacks.
        bb_farm: builders + Star Lab follow the planner (or upgrade anything, with no plan); attacks for today's
        Star Bonuses, then rounds of 5 attacks + the Elixir Cart, checking the upgrades after each round - it stays
        on the account until its next upgrade is bought, and only moves on (when rotating) once all are busy."""
        f = self.shot()
        name = self.account_name(f)
        self.emit("state", f"Builder Base only ({name})")
        self.track_bb(name, self.read_storage(f, village="builder"))
        self.bb_bonus(name)
        self.bb_collect()
        self.bb_clock_boost()
        if self.mode == "bb_walls":
            return self.bb_walls(name)
        if self.mode == "bb_loot":  # loot only: a plain loop on this account - attack, attack, attack; claim the
            for _ in range(10):     # Elixir Cart every 10 attacks. No Star Bonus counting, upgrades or switching.
                self.bb_bonus(name)  # a Star Bonus popup can still show up: collect it and carry on
                if not self.find(self.shot(), "bb_attack_button") and not self.wait_for("bb_attack_button", 20):
                    return  # not back on the village: the main loop sorts the screen out
                self.bb_attack()
            return  # next round: collect (the cart) + boost, then 10 more
        self.bb_session(name, upgrades=True)
        if not self.bb_done_today(name):
            return  # attacks stopped for another reason (screen, battle): look again
        if getattr(self, "_bb_on_logged", None) != name:
            self._bb_on_logged = name
            self.log(f"Builder Base farm: Star Bonuses done ({name}) - farming on for the next upgrade.")
        # farm in short rounds, checking the upgrades after each: buys the plan's next target the moment it's
        # affordable (or anything, with no plan)
        for _ in range(5):
            if not self.find(self.shot(), "bb_attack_button") and not self.wait_for("bb_attack_button", 20):
                return  # not back on the village: the main loop sorts the screen out
            self.bb_attack()
        self.bb_collect()  # the Elixir Cart (and collectors)
        self._upgrade_backoff.pop("bb_builder", None)
        self._upgrade_backoff.pop("bb_lab", None)
        saving = self.bb_upgrades()
        # next account only once every builder + the Star Lab here is busy - never while saving up for an upgrade
        if not saving and self.cfg["rotate_accounts"] and time.time() >= self._rotate_pause_until:
            self._switch_streak = 0  # there's always more to farm on the Builder Base: never 'all done'
            self.switch_account()

    def reload_if_disconnected(self, frame):
        """'Anyone there? You have been disconnected due to inactivity' -> RELOAD GAME, then wait for it to load."""
        hit = self.find(frame, "reload_game")
        if not hit:
            return False
        self.log("Disconnected for inactivity - reloading the game.", "warn")
        self.tap(hit, 2.0)
        self._launched_at = time.time()  # loading screens next: don't count them as stuck
        for _ in range(30):
            if self.at_village(self.shot()):
                break
            self.sleep(2.0)
        return True

    def storage_total(self, frame):
        """Gold + elixir + dark elixir, for checking an upgrade really took the resources."""
        regions = {"bank_dark_region": (1560, 225, 1830, 300), **self.cfg["ocr_regions"]}  # default: 1920x1080 bar
        vals = [white_number(frame, regions[r]) for r in
                ("bank_gold_region", "bank_elixir_region", "bank_dark_region") if r in regions]
        return None if not vals or None in vals else vals

    def back_to_village(self, icon=None):
        """Close windows/lists/dialogs until the plain village shows. Back closes game windows and
        cancels dialogs; a dropdown list is closed by tapping its icon."""
        for _ in range(6):
            f = self.shot()
            if self.reload_if_disconnected(f):
                continue
            if (self.find(f, "wall_okay_button") or self.find(f, "lab_picker_title")
                    or not self.at_village(f)):  # dialogs / game windows (they hide Attack)
                self.adb.back()
            elif panel_box(f) and icon:  # a dropdown list leaves Attack visible; its icon closes it
                self.adb.tap(*icon)
            else:
                return
            self.sleep(0.9)

    def scroll_panel(self, box):
        x0, x1, y0, y1 = box
        cx = (x0 + x1) // 2
        self.adb.swipe(cx, y1 - 90, cx, max(y0 + 90, y1 - 90 - 380), self.cfg["bank_scroll_duration_ms"])
        self.sleep(self.cfg["bank_scroll_delay"])

    def upgrade_from_list(self, kind):
        """Open the builder or lab list, read every row, start the MOST EXPENSIVE upgrade you can afford
        (white price; walls are left to the wall routine), and confirm with the green resource button only.
        Busy builders/lab just produce a gem prompt, which is backed out of - so the attempt is the check."""
        frame = self.shot()
        icon = top_bar(frame, kind)[0]
        before = self.storage_total(frame)
        free_before = self.free_slots(frame, kind)
        if not panel_box(frame):
            self.tap(icon, 1.3)
        self.sleep(0.5)  # let the list finish sliding open before reading its 'Available!' rows
        normal, goblin = available_slots(self.shot())
        # Only refuse when the top bar agrees (goblin face / 0 free): one read of a still-moving list isn't enough.
        if kind.startswith("bb_") and free_before:
            normal = free_before  # the Builder Base list has no 'Available!' rows: trust the top bar counter
        if normal == 0 and not free_before:  # nothing free, or only the goblin (it costs gems) - never use it
            self._busy_until[kind] = self._upgrade_backoff[kind] = time.time() + 1800
            self.back_to_village(icon)
            return self.log(f"{KIND_NAMES[kind]}: " + ("only the goblin is free (costs gems) - not using it"
                                                   if goblin else "no free slot") + ". Checking again in 30 min.")
        if kind == "builder":
            self._saving_home = None
        self._maxed = False
        seen = self.read_list()  # the whole list first: the discount and levels are worked out from all of it
        if self._maxed:
            self._upgrade_backoff[kind] = time.time() + 6 * 3600
            self.back_to_village(icon)
            return self.log(f"{KIND_NAMES[kind]}: All Upgrades Complete on this account - not looking again for 6 h.",
                            "ok")
        plan, levels = self.plan_positions(kind, seen)
        other = None  # saving up for the plan's next target: the resource it does NOT need (spare builders use it)
        if plan:  # this account has a plan: stick to it - the next target in order, or wait (keep farming) for it
            i = min(plan.values())
            rows = [(nm, p, ok) for nm, p, ok in seen if plan.get((nm, p)) == i]
            buy = [r for r in rows if r[2]]
            it = self.plan_items(kind)[i]
            res = wiki_data()[it["key"]]["levels"][0]["res"]
            if not buy and kind == "bb_builder":
                self._bb_saving = res  # the Star Lab won't spend it meanwhile
                if (free_before or 0) >= 2:  # a builder to spare (one stays free for the target): spend the
                    other = res              # other resource instead of letting it sit at max
            if not buy and other is None:
                self._upgrade_backoff[kind] = time.time() + 900
                if kind == "builder":  # farm home until it's bought - the Builder Base waits, the list stays shut
                    self._saving_home = (self._last_name, min(p for _, p, _ in rows), res, time.time() + 3600)
                self.back_to_village(icon)
                return self.log(f"{KIND_NAMES[kind]}: next in the plan is {wiki_data()[it['key']]['name']} -> "
                                f"{it['to']} ({min(p for _, p, _ in rows):,}) - farming until it's affordable"
                                + (" (Builder Base visits wait till then)." if kind == "builder" else "."))
        best = None
        for nm, price, ok in seen:
            skip = is_wall(nm) or (  # walls: the wall routine; TH: optional no-rush
                self.cfg.get("skip_town_hall", True) and re.search(r"t[o0]wn\s*ha", nm.lower()))
            if skip or not ok or levels.get((nm, price)) == 0 or nm.lower().startswith("new "):
                continue  # 'New ...' rows build a new one: that's placing it from the shop, not an upgrade
            if kind.endswith("builder") and wiki_key(nm, "builder" if kind.startswith("bb_") else "home") is None \
                    and norm_name(nm) not in NO_WIKI:
                continue  # event Crafting Station defenses (Hot Candle, Cake-A-Pult...): a 3-way stat window
            if plan and other is not None:  # saving up: only things paid in the other resource
                k = wiki_key(nm, "builder")
                if not k or wiki_data()[k]["levels"][0]["res"] == other:
                    continue
            elif plan and plan.get((nm, price)) != min(plan.values()):
                continue
            bb = next((i for i, r in enumerate(BB_DEFAULT_ROWS) if name_match(nm, r["name"])), 99) \
                if kind == "bb_builder" else 99
            rank = (plan.get((nm, price), 10 ** 6), bb, -price)  # 1) your plan 2) key BB buildings 3) priciest
            if not best or rank < best[3]:
                best = (nm, price, 0, rank)
        if not best:
            self._upgrade_backoff[kind] = time.time() + 1200
            self.back_to_village(icon)
            return self.log(f"{KIND_NAMES[kind]}: nothing affordable right now - checking again in 20 min.")
        nm, price = best[:2]
        r = best[3][1:]
        lv = levels.get((nm, price))
        self.log(f"{KIND_NAMES[kind]}: choosing '{nm}'" + (f" (level {lv} -> {lv + 1})" if lv is not None else "")
                 + f" for {price:,} - "
                 + (f"#{best[3][0] + 1} in your upgrade plan." if best[3][0] < 10 ** 6
                    else "a key Builder Base building first (hall, heroes, barracks, labs, clock)." if r[0] < 99
                    else "the most expensive one you can afford."))
        self._started = (kind, nm, price, lv)
        self.tap(icon, 1.0)  # close + reopen = back at the top, then page down until it's on screen
        self.tap(icon, 1.3)  # (scrolling never lands in the same place twice, so search, don't count)
        match, prev = [], None
        for _ in range(8):
            frame = self.shot()
            rows = list_rows(frame)
            # name AND price: two rows can cost the same (Builder Base Cannon / Elixir Storage: 2,500,000)
            match = [r for r in rows if r[1] == price and r[2] and name_match(r[0], nm)]
            box = panel_box(frame)
            if match or not box or rows == prev:
                break
            prev = rows
            self.scroll_panel(box)
        if not match:
            self._upgrade_backoff[kind] = time.time() + 600
            self.back_to_village(icon)
            return self.log(f"{KIND_NAMES[kind]}: lost '{nm}' after re-opening the list - will retry.", "warn")
        for _ in range(6):  # the list glides on after a swipe: tap only once two reads agree where the row is
            self.sleep(0.4)
            again = [r for r in list_rows(self.shot()) if r[1] == price and r[2] and name_match(r[0], nm)]
            if again and abs(again[0][3][1] - match[0][3][1]) <= 4:
                match = again
                break
            match = again or match
        self.tap(match[0][3], 1.6)
        if self.find(self.shot(), "guardians_title"):
            f, k = self.shot(), self.shot().shape[1] / 1920
            btn = next(((int(cx * k), int(823 * k)) for cx in (432, 960, 1490)
                        if white_number(f, (int((cx - 130) * k), int(818 * k), int((cx + 95) * k), int(862 * k))) == price),
                       None)
            if not btn:
                self._upgrade_backoff[kind] = time.time() + 1800
                self.back_to_village(icon)
                return self.log(f"{KIND_NAMES[kind]}: no Guardian shows {price:,} - backed out.", "warn")
            self.tap(btn, 1.6)
        hit, shown = self.resource_confirm(kind)  # heroes/research: the window opens directly
        if not hit:  # a building: the row only selected it - close the list, then its own Upgrade button
            if panel_box(self.shot()):
                self.tap(icon, 1.2)
            got, glv = self.selected_label(self.shot())  # is the selected building really the one chosen?
            want = re.sub(r"(?i)\s*x\s*\d+\s*$", "", nm)
            base = "builder" if kind.startswith("bb_") else "home"
            gk, wk = wiki_key(got, base) if got else None, wiki_key(want, base)
            if gk and wk and gk != wk:  # clearly another building; OCR noise in the label doesn't count
                self._upgrade_backoff[kind] = time.time() + 600
                self.back_to_village(icon)
                return self.log(f"{KIND_NAMES[kind]}: the list selected '{got}' (level {glv}), not '{want}' - "
                                "backed out.", "warn")
            up = self.wait_for("building_upgrade_button", 4)
            if up:
                self.tap(up, 1.6)
            end = time.time() + 4
            while not hit and time.time() < end:
                hit, shown = self.resource_confirm(kind)  # the GREEN resource Confirm only
        if not hit:
            self._upgrade_backoff[kind] = time.time() + 600
            cv2.imwrite(os.path.join(BASE_DIR, "debug_upgrade.png"), self.shot())
            self.back_to_village(icon)
            return self.log(f"{KIND_NAMES[kind]}: no green Confirm for '{nm}' - backed out "
                            "(screen: debug_upgrade.png).", "warn")
        if shown != price:
            self._upgrade_backoff[kind] = time.time() + 600
            self.back_to_village(icon)
            return self.log(f"{KIND_NAMES[kind]}: Confirm shows {shown}, list said {price:,} - not risking it.", "warn")
        self.tap(hit, 2.0)
        self.back_to_village(icon)  # also cancels any 'all builders busy - use gems?' prompt
        for _ in range(3):  # the counters can lag (or a selected building's bar hides them) for a moment
            frame = self.shot()
            after, free_after = self.storage_total(frame), self.free_slots(frame, kind)
            spent = (before and after and any(b - a >= price * 0.9 for b, a in zip(before, after))) or (
                free_before is not None and free_after is not None and free_after < free_before)
            if spent:
                break
            self.sleep(1.5)
        if spent:
            self.bump("upgrades")
            self.log(f"{'Research' if kind.endswith('lab') else 'Upgrade'} started"
                     f"{' (Builder Base)' if kind.startswith('bb_') else ''}: {nm} for {price:,}.", "ok")
            self._upgrade_backoff[kind] = 0  # another builder may be free - check next time home
            self.plan_progress(*self._started)
        else:
            self._upgrade_backoff[kind] = time.time() + 1800
            self.log(f"{KIND_NAMES[kind]}: '{nm}' didn't start (all {'builders' if kind == 'builder' else 'lab slots'} "
                     f"busy?) - checking again in 30 min.")

    # --- upgrade planner: per-account scans + targets ---
    def read_list(self):
        """Every row of the open builder / lab list, page by page: [(name, price, affordable)]."""
        if self.v.find(self.shot(), "all_upgrades_complete", 0.85):
            self._maxed = True  # 'All Upgrades Complete' instead of a list
            return []
        seen, pages = {}, []
        for _ in range(8):
            frame = self.shot()
            box = panel_box(frame)
            if not box:
                break
            rows = list_rows(frame)
            for nm, price, ok, xy in rows:
                seen.setdefault((nm, price), ok)
            sig = [(nm, p) for nm, p, _, _ in rows]
            if pages and sig == pages[-1]:
                break  # didn't move: bottom of the list
            pages.append(sig)
            self.scroll_panel(box)
        return [(nm, p, ok) for (nm, p), ok in seen.items()]

    def plan_items(self, kind):
        if kind.endswith("lab"):
            return []
        base = "builder" if kind.startswith("bb_") else "home"
        return ((self.cfg.get("plans") or {}).get(self._last_name or "?") or {}).get(base) or []

    def plan_positions(self, kind, seen):
        """Record this account's scan, then ({(name, price): position in its plan}, {(name, price): level})."""
        if kind.endswith("lab"):
            return {}, {}
        base = "builder" if kind.startswith("bb_") else "home"
        sd = ((self.cfg.get("scans") or {}).get(self._last_name) or {}).get(base) or {}
        if sd.get("source") == "export":  # exact levels already known: the list only gives names + prices
            f = infer_discount([(n, p) for n, p, _ in seen], base)
            rows = [{"name": nm, "price": p, "key": wiki_key(nm, base)} for nm, p, _ in seen]
            for r in rows:
                r["level"] = level_for_price(r["key"], r["price"], f) if r["key"] else None
            exact = sd["items"]
        else:
            rows = exact = self.record_scan(base, seen)["items"]
        levels = {(r["name"], r["price"]): r["level"] for r in rows}
        pos = {}
        for i, it in enumerate(self.plan_items(kind)):
            if not any(r["key"] == it["key"] and not r.get("upgrading") and (r["level"] is None or r["level"] < it["to"])
                       for r in exact):
                continue  # every copy is there already (or upgrading to it)
            for r in rows:
                if r["key"] == it["key"] and (r["level"] is None or r["level"] < it["to"]):
                    pos.setdefault((r["name"], r["price"]), i)
        return pos, levels

    def record_scan(self, base, seen):
        """What this account can still upgrade, with levels worked out from the prices (discounts included)."""
        f = infer_discount([(n, p) for n, p, _ in seen], base)
        items, dup = [], {}
        for nm, p, ok in seen:
            k = wiki_key(nm, base)
            if is_wall(nm) or "supercharge" in nm.lower() or (k is None and norm_name(nm) not in NO_WIKI):
                continue  # walls, Supercharges and event items (Cake-A-Pult...) aren't planned
            r = {"name": nm, "price": p, "ok": ok, "key": k, "count": count_of(nm),
                 "level": level_for_price(k, p, f) if k else None}
            same = dup.get((k or norm_name(nm), p))  # the same row read twice across pages ('Storaqe' / 'SGoraqe')
            if same:
                same["count"] = max(same["count"], r["count"])
                continue
            dup[(k or norm_name(nm), p)] = r
            items.append(r)
        hall = next((r["level"] for r in items if r["key"] in ("home:town hall", "builder:builder hall")
                     and r["level"] is not None), None)
        if hall is None:  # no hall row (maxed / upgrading): the list only offers what this hall allows
            reqs = [wiki_data()[r["key"]]["levels"][r["level"]]["req"] for r in items
                    if r["key"] and r["level"] is not None and r["level"] < len(wiki_data()[r["key"]]["levels"])
                    and wiki_data()[r["key"]]["levels"][-1].get("hall") in ("town hall", "builder hall")
                    and wiki_data()[r["key"]]["levels"][0]["level"] == 1]
            hall = max(reqs) if reqs else None
        hero = next((r["level"] for r in items if r["key"] == "home:hero hall" and r["level"] is not None), None)
        acc = self._last_name
        if not acc or acc == "?" or self.ambiguous():  # never file a scan under an unknown account - it'd mix
            self.log("Upgrade planner: not sure which account this is - scan not saved.", "warn")  # them up
            return {"items": items, "discount": f, "hall": hall}
        scans = self.cfg.setdefault("scans", {}).setdefault(acc, {})
        old = scans.get(base) or {}
        has_row = any(r["key"] in ("home:town hall", "builder:builder hall") for r in items)
        if not has_row:  # estimated: a rushed base's pending upgrades need less than its real hall - and a hall
            hall = max([h for h in (hall, old.get("hall")) if h] or [None])  # never goes down; manual stays
        hero = hero if hero is not None else old.get("hero_hall")
        scan = {"time": time.strftime("%Y-%m-%d %H:%M"), "discount": f, "items": items, "hall": hall,
                "hero_hall": hero}
        scans[base] = scan
        if f < 1:
            self.log(f"Prices are {round((1 - f) * 100)}% off right now (Hammer Jam / Gold Pass) - levels "
                     "worked out with that.")
        self.prune_plan(acc, base)
        save_config(self.cfg)
        self.emit("scan", acc)
        return scan

    def prune_plan(self, acc, base):
        """Drop plan targets this account has reached (every copy seen on the list is at or past the target)."""
        plans = (self.cfg.get("plans") or {}).get(acc) or {}
        items = ((self.cfg.get("scans") or {}).get(acc) or {}).get(base, {}).get("items", [])
        keep = []
        for it in plans.get(base) or []:
            mine = [r for r in items if r["key"] == it["key"]]
            if mine and all(r["level"] is not None and r["level"] >= it["to"] for r in mine):
                self.log(f"Upgrade plan: {wiki_data()[it['key']]['name']} -> level {it['to']} done "
                         f"({acc}).", "ok")
                continue
            keep.append(it)
        if plans.get(base) is not None and len(keep) != len(plans[base]):
            plans[base] = keep

    def plan_progress(self, kind, nm, price, lv):
        """An upgrade just started: one copy of that row moves up a level; targets reached leave the plan."""
        if kind.endswith("lab"):
            return
        base = "builder" if kind.startswith("bb_") else "home"
        acc = self._last_name or "?"
        scan = ((self.cfg.get("scans") or {}).get(acc) or {}).get(base)
        if not scan:
            return
        if scan.get("source") == "export":  # exact rows: the lowest copy of that building (at lv if known)
            k = wiki_key(nm, base)
            mine = sorted((r for r in scan["items"] if r["key"] == k and not r.get("upgrading")),
                          key=lambda r: (lv is not None and r["level"] != lv, r["level"]))
        else:
            mine = [r for r in scan["items"] if r.get("name") == nm and r.get("price") == price]
        for r in mine[:1]:
            r["count"] -= 1
            lv = r["level"] if lv is None and scan.get("source") == "export" else lv
            if lv is not None:
                scan["items"].append({"name": r["name"] if scan.get("source") == "export" else nm + " (upgrading)",
                                      "price": 0, "ok": False, "key": r["key"], "count": 1, "level": lv + 1,
                                      "upgrading": True})
        scan["items"] = [r for r in scan["items"] if r["count"] > 0]
        self.prune_plan(acc, base)
        save_config(self.cfg)
        self.emit("scan", acc)

    def level_label(self, frame):
        """'Cannon (Level 21)' shown under a selected building -> 21, else None."""
        return self.selected_label(frame)[1]

    def selected_label(self, frame):
        """'Cannon (Level 21)' shown under a selected building -> ('Cannon', 21); (None, None) if unreadable."""
        k = frame.shape[1] / 1920
        c = frame[int(640 * k):int(790 * k), int(360 * k):int(1560 * k)]
        hsv = cv2.cvtColor(c, cv2.COLOR_BGR2HSV)
        m = cv2.resize(((hsv[:, :, 2] > 200) & (hsv[:, :, 1] < 80)).astype(np.uint8) * 255, None, fx=1.5, fy=1.5)
        try:
            t = pytesseract.image_to_string(cv2.copyMakeBorder(255 - m, 20, 20, 20, 20, cv2.BORDER_CONSTANT,
                                                               value=255), config="--psm 6", timeout=6)
        except Exception:
            return None, None
        hit = re.search(r"(?i)([A-Za-z0-9.'& -]*?)\s*\(?\s*l[e3]v[e3]l\s*([0-9]{1,3})", t)
        return (hit.group(1).strip() or None, int(hit.group(2))) if hit else (None, None)

    def resolve_levels(self, kind, base, limit=10):
        """Rows the price didn't settle (duplicate prices, OCR slips, no wiki data): tap each one in the list and
        read 'Name (Level N)' under the building. Saves the scan."""
        acc = self._last_name
        scan = ((self.cfg.get("scans") or {}).get(acc) or {}).get(base)
        todo = [r for r in (scan or {}).get("items", []) if r.get("level") is None and not r.get("upgrading")]
        if not todo:
            return
        icon = top_bar(self.shot(), kind)[0]
        for r in todo[:limit]:
            self.back_to_village(icon)
            self.tap(icon, 1.3)
            hit = None
            for _ in range(8):  # page down until the row shows
                f = self.shot()
                box = panel_box(f)
                if not box:
                    break
                hit = next((xy for nm, p, ok, xy in list_rows(f) if p == r["price"] and name_match(nm, r["name"])),
                           None)
                if hit:
                    break
                self.scroll_panel(box)
            if not hit:
                continue
            self.tap(hit, 1.4)
            if panel_box(self.shot()):
                self.tap(icon, 1.0)
            lv = None
            for _ in range(3):
                lv = self.level_label(self.shot())
                if lv is not None:
                    break
                self.sleep(0.6)
            if lv is not None:
                r["level"] = lv
                self.log(f"Upgrade planner: {r['name']} is level {lv} (read from the game).")
        self.back_to_village(icon)
        self.prune_plan(acc, base)
        save_config(self.cfg)
        self.emit("scan", acc)

    def export_village(self):
        """Settings > More Settings > Data Export 'Copy': the game's own JSON with every level, both villages.
        Read back from the Windows clipboard. None if any step didn't work (then the list is read instead)."""
        if not clipboard_usable():
            if not getattr(self, "_clip_warned", False):
                self._clip_warned = True
                self.log("Upgrade planner: Windows' clipboard isn't available (is the PC locked?) - reading the "
                         "builder lists instead of the game's data export until it is.", "warn")
            return None
        self._clip_warned = False
        self.back_to_village()
        f = self.shot()
        k = f.shape[1] / 1920
        self.tap(self.find(f, "settings_cog_button") or (int(1842 * k), int(765 * k)), 0.6)
        # strict matches only: a looser one takes look-alike green buttons (Credits, Change Name...)
        more = None
        for _ in range(6):
            sf = self.shot()
            more = self.v.find(sf, "more_settings_button", 0.9)
            if more:
                n = settings_name(sf)  # the name, big and clean, beside the avatar: trusted as read (only the
                self._settings_name = next((x for x in self._names if n and x.lower() == n.lower()), n)  # case
                # follows a known name) - it's what corrects a slipped top-left read ('GecCol' -> 'GeoCol')
                break
            self.sleep(0.5)
        data, hit = None, None
        if more:
            self.tap(more, 0.8)
            for _ in range(8):  # touch nothing until the More Settings window has finished opening
                if self.v.find(self.shot(), "more_settings_button", 0.9) is None:
                    break
                self.sleep(0.3)
            self.sleep(0.5)
            hit = None
            for _ in range(10):  # the page opens wherever it was last scrolled to (the top after a game start)
                f = self.shot()
                hit = self.v.find(f, "export_copy_row", 0.9)  # the Change Name row scores ~0.75
                if hit:
                    break
                # SLOW drag from a grey section header if one is low on the page, else from the setting NAMES at
                # the rows' left (plain text) - never the buttons on the right, which a touch would press
                y = settings_drag_start(f) or int(880 * k)
                self.adb.swipe(int(500 * k), y, int(500 * k), max(int(160 * k), y - int(650 * k)), 700)
                self.sleep(0.8)
            before = read_clipboard() if hit else ""  # only a NEW export counts - never another account's old one
            for attempt in range(2) if hit else ():  # a 2nd Copy if the clipboard didn't get it (slow to sync)
                self.sleep(0.6)  # the page glides on after a drag: tap where the row has settled
                hit = self.v.find(self.shot(), "export_copy_row", 0.9) or hit
                self.tap((hit[0] + int(398 * k), hit[1]), 1.0)  # the green Copy button at the row's right
                for _ in range(5):
                    try:
                        raw = read_clipboard()
                        d = json.loads(raw) if raw != before else {}
                        if d.get("tag") and d.get("buildings") and abs(time.time() - d.get("timestamp", 0)) < 900:
                            data = d
                            break
                    except (ValueError, AttributeError):
                        pass
                    self.sleep(1.0)
                if data:
                    break
        if not data:  # which step: for the debug report
            cv2.imwrite(os.path.join(BASE_DIR, "debug_export.png"), self.shot())
            log_file.info("export failed: " + ("no More Settings button" if not more else "no Copy row found"
                                               if not hit else "clipboard had no fresh export"))
        self.back_to_village()
        return data

    def scan_export(self):
        """Fill this account's planner scans (home + Builder Base) from the data export. True if it worked.
        The export carries the player tag, so an account whose name OCR slips ('GeoCo!3') still files right."""
        data = self.export_village()
        if not data:
            self.log("Upgrade planner: the game's data export didn't come through - reading the builder list "
                     "instead.", "warn")
            return False
        tags = self.cfg.setdefault("account_tags", {})
        # 1) a tag seen before  2) the top-left name  3) the Settings window's name  4) the tag itself - a scan
        # never fails just because a name couldn't be read (a fancy name / font / layout on another PC)
        clean = getattr(self, "_settings_name", None)  # the Settings window's big, clean name
        last = self._last_name if self._last_name not in (None, "?") else None
        if not tags.get(data["tag"]) and clean and last and clean != last and self.same_game_name(clean, last):
            if last in self._names:  # first time this account is seen: the top-left read slipped ('GecCol' for
                self._names.remove(last)  # 'GeoCol') - file it under the clean name, and snap future reads to it
            self._names.append(clean)
            last = clean
        acc = tags.get(data["tag"]) or last or clean or data["tag"]
        bases = export_items(data)
        if data["tag"] not in tags and acc in tags.values():
            # a new tag under a name another account already has (two accounts called 'GeoCol2'): never file it
            # over that one - its own 'name (...)' entry with this Town Hall, else a new one keyed by the tag
            hall = next((r["level"] - r["upgrading"] for r in bases.get("home") or [] if r["key"] == "home:town hall"),
                        None)
            acc = next((k for k, s in (self.cfg.get("scans") or {}).items() if k.startswith(acc + " (")
                        and k not in tags.values() and ((s or {}).get("home") or {}).get("hall") == hall),
                       f"{acc} ({data['tag']})")
        self._sc_key = acc if " (" in acc else None  # what account_name() reports for a shared in-game name
        self._tag_ok = acc  # the export's tag settled which account this is
        tags[data["tag"]] = self._last_name = acc
        scans = self.cfg.setdefault("scans", {}).setdefault(acc, {})
        for base, items in bases.items():
            if not items:
                continue
            hall = next((r["level"] - r["upgrading"] for r in items
                         if r["key"] in ("home:town hall", "builder:builder hall")), None)
            hero = next((r["level"] - r["upgrading"] for r in items if r["key"] == "home:hero hall"), None)
            scans[base] = {"time": time.strftime("%Y-%m-%d %H:%M"), "discount": 1.0, "items": items, "hall": hall,
                           "hero_hall": hero, "source": "export"}
            self.prune_plan(acc, base)
        save_config(self.cfg)
        self.emit("scan", acc)
        self.log(f"Upgrade planner: read {acc}'s exact levels from the game's data export.", "ok")
        return True

    def maybe_rescan(self, kind, hours=6):
        """Builders all busy: read the list anyway if this account's planner scan is missing or old. True if it did."""
        if kind.endswith("lab") or not self._last_name or self._last_name == "?":
            return False
        base = "builder" if kind.startswith("bb_") else "home"
        sd = ((self.cfg.get("scans") or {}).get(self._last_name) or {}).get(base) or {}
        try:
            age = time.time() - time.mktime(time.strptime(sd["time"], "%Y-%m-%d %H:%M"))
        except (KeyError, ValueError):
            age = 10 ** 9
        if age < hours * 3600:
            return False
        if self.scan_export():
            return True
        icon = top_bar(self.shot(), kind)[0]
        self.tap(icon, 1.3)
        self.sleep(0.5)
        seen = self.read_list()
        self.tap(icon, 1.0)
        self.back_to_village(icon)
        if seen:
            self.record_scan(base, seen)
            self.resolve_levels(kind, base)
            self.log(f"Upgrade planner: refreshed {self._last_name}'s {'Builder Base' if base == 'builder' else 'home'}"
                     f" scan ({len(seen)} upgrades left).")
        return True

    def scan_now(self):
        """Planner's 'Scan': open this account's builder list (home or Builder Base, whichever is showing), read it."""
        self.back_to_village()
        f = self.shot()
        if not self.at_village(f):
            raise RuntimeError("the game isn't on the home village or Builder Base")
        kind = "bb_builder" if self.find(f, "bb_attack_button") else "builder"
        self._last_name = None
        for _ in range(4):  # a popup / the XP bar animating can hide the name for a moment
            if self.account_name(f) != "?":
                break
            self.sleep(1.0)
            f = self.shot()
        if self.scan_export():  # exact levels of both villages, straight from the game
            return self._last_name, kind
        if not self._last_name or self._last_name == "?":
            raise RuntimeError("the game's data export didn't come through (Settings > More Settings > Data Export) "
                               "and the account name couldn't be read - close any popup and try again")
        icon = top_bar(f, kind)[0]
        if not panel_box(f):
            self.tap(icon, 1.3)
        self.sleep(0.5)
        seen = self.read_list()
        self.tap(icon, 1.0)
        self.back_to_village(icon)
        if not seen:
            raise RuntimeError("the builder list didn't open")
        base = "builder" if kind.startswith("bb_") else "home"
        self.record_scan(base, seen)
        self.resolve_levels(kind, base)
        return self._last_name, kind

    def resource_confirm(self, kind):
        """(button, price shown on it) of the upgrade window's green resource button, else (None, None).
        Home: the captured Confirm image. Builder Base (purple elixir icon, so the image doesn't match): the big
        green button in the bottom part of the screen. Either way the caller only taps it if the price equals the
        list price, so a gem button can never be pressed."""
        f = self.shot()
        if not kind.startswith("bb_"):
            hit = self.find(f, "confirm_wall_upgrade_button")
            return (hit, confirm_price(f, hit)) if hit else (None, None)
        H = f.shape[0]
        hsv = cv2.cvtColor(f[int(H * 0.6):], cv2.COLOR_BGR2HSV)
        m = ((hsv[:, :, 0] >= 35) & (hsv[:, :, 0] <= 75) & (hsv[:, :, 1] > 150) & (hsv[:, :, 2] > 150)).astype(np.uint8)
        n, _, st, _ = cv2.connectedComponentsWithStats(m, 8)
        big = [i for i in range(1, n) if st[i, 2] > f.shape[1] * 0.12 and st[i, 3] > H * 0.08]
        if not big:
            return None, None
        x, y, w, h = st[max(big, key=lambda i: st[i, 4]), :4]
        y += int(H * 0.6)
        # from the very edge: a 7-digit price starts right at it (x + 10 cut '4 400 000' to '400 000')
        return (x + w // 2, y + h // 2), white_number(f, (x, y + 10, x + int(w * 0.72), y + h - 10))

    def free_slots(self, frame, kind):
        """Normal builders / lab slots free. A goblin icon means only the (gem-costing) goblin is free = 0."""
        if goblin_icon(frame, kind):
            return 0
        c = read_counter(frame, top_bar(frame, kind)[1])
        return c[0] if c else None

    def account_done(self, frame):
        """True when rotation is on and every enabled builder/lab slot is busy on this account."""
        c = self.cfg
        kinds = [k for k in ("builder", "lab") if c[f"{k}_upgrades_enabled"]]
        if not c["rotate_accounts"] or not kinds or time.time() < self._rotate_pause_until:
            return False
        if any(self.free_slots(frame, k) != 0 and time.time() >= self._busy_until.get(k, 0) for k in kinds):
            self._switch_streak = 0  # this account still has work: stay and farm
            return False
        return True

    def list_accounts(self, frame):
        """Rows of the Supercell ID panel on screen: [{'sc': Supercell ID name, 'game': in-game name (rough OCR),
        'th': Town Hall, 'xy': where to tap}] - a row is the bold name with a 'Town Hall: N' line under it."""
        x0 = frame.shape[1] * 2 // 3
        try:
            d = pytesseract.image_to_data(cv2.cvtColor(frame[:, x0:], cv2.COLOR_BGR2GRAY), config="--psm 11",
                                          output_type=pytesseract.Output.DICT, timeout=10)
        except Exception:
            return []
        words = [(t.strip(), x0 + d["left"][i] + d["width"][i] // 2, d["top"][i] + d["height"][i] // 2)
                 for i, t in enumerate(d["text"]) if t.strip()]
        self._list_end = any(t.upper() == "OTHER" for t, _, _ in words)  # 'OTHER IDS': the list ends above it
        rows = []
        for tw, tx, ty in [(t, x, y) for t, x, y in words if t.lower() == "town"]:
            name = next(((t, x, y) for t, x, y in words if abs(tx - x) < 90 and 40 < ty - y < 75), None)
            if not name:
                continue
            th = next((t for t, x, y in words if abs(y - ty) < 6 and 0 < x - tx < 160 and t.isdigit()), None)
            game = next((t for t, x, y in words if 15 < y - name[2] < 40 and 0 < x - name[1] < 140
                         and len(t) > 2), "")
            rows.append({"sc": name[0], "game": game, "th": (int(th) if int(th) <= 20 else int(th[1:] or 0) or None) if th else None,  # ':' -> '7': '718'
                         "xy": (name[1], name[2])})
        return rows

    def all_accounts(self):
        """Every account on the Supercell ID panel, top to bottom, scrolling down for long lists (10+ accounts).
        Returns (rows, the panel's last view)."""
        seen, frame = {}, self.shot()
        k = frame.shape[1] / 1920
        for _ in range(8):
            new = [r for r in self.list_accounts(frame) if r["sc"] not in seen]
            for r in new:
                seen[r["sc"]] = r
            if not new or self._list_end:
                break
            self.adb.swipe(int(1620 * k), int(960 * k), int(1620 * k), int(620 * k), 700)  # inside the panel
            self.sleep(1.2)
            frame = self.shot()
        known = [{"sc": r["sc"], "game": r["game"], "th": r["th"]} for r in seen.values()]
        if known and known != self.cfg.get("sc_accounts"):  # for the phone view's account picker
            self.cfg["sc_accounts"] = known
            save_config(self.cfg)
        return list(seen.values())

    def tap_account(self, sc):
        """Scroll the Supercell ID panel back to the top, then down until that account is on screen; tap it."""
        f = self.shot()
        k = f.shape[1] / 1920
        if not any(r["sc"] == sc for r in self.list_accounts(f)):  # not on screen: back to the top first
            for _ in range(4):
                self.adb.swipe(int(1620 * k), int(600 * k), int(1620 * k), int(1000 * k), 400)
            self.sleep(1.0)
        for _ in range(8):
            row = next((r for r in self.list_accounts(self.shot()) if r["sc"] == sc), None)
            if row:
                self.tap(row["xy"], 4.0)
                return True
            self.adb.swipe(int(1620 * k), int(960 * k), int(1620 * k), int(620 * k), 700)
            self.sleep(1.2)
        return False

    @staticmethod
    def same_game_name(a, b):
        """Two OCR'd in-game names ('Geocoi2' / 'GeoCol2') are the same name: same digits, close spelling."""
        n = lambda s: re.sub(r"[^a-z0-9]", "", s.lower().replace("i", "l").replace("0", "o"))
        return bool(a and b) and re.sub(r"\D", "", a) == re.sub(r"\D", "", b) and \
            difflib.SequenceMatcher(None, n(a), n(b)).ratio() >= 0.7

    def account_key(self, row, rows, name):
        """What this account's plans / scans are filed under: its in-game name - or, when another account on the
        list has the same in-game name, 'name (Supercell ID)'. Moves old data filed under the bare name to it
        when the Town Hall matches."""
        if not any(r is not row and self.same_game_name(r["game"], row["game"]) for r in rows):
            return None
        key = f"{name} ({row['sc']})"
        old = ((self.cfg.get("scans") or {}).get(name) or {}).get("home") or {}
        if old and row["th"] and old.get("hall") == row["th"] and key not in (self.cfg.get("scans") or {}):
            for part in ("scans", "plans", "bb_bonus_days"):
                if name in (self.cfg.get(part) or {}):
                    self.cfg[part][key] = self.cfg[part].pop(name)
            for tag, n in list((self.cfg.get("account_tags") or {}).items()):
                if n == name:
                    self.cfg["account_tags"][tag] = key
            save_config(self.cfg)
            self.log(f"Two accounts are called '{name}': this one's planner data is now under '{key}'.", "ok")
        return key

    def switch_account(self, target=None):
        """Settings cog -> blue switch button -> tap the next account on the Supercell ID list (or `target`, a
        Supercell ID name - picked on the phone view)."""
        # _switch_streak = accounts already left because they were busy; this one is busy too
        if not target and self._n_accounts and self._switch_streak + 1 >= self._n_accounts:
            self._switch_streak = 0
            if self.cfg["stop_when_all_busy"]:
                self.log("Every account's builders and lab are busy - nothing left to do, stopping.", "ok")
                self.stop_evt.set()
                raise Abort()
            self._rotate_pause_until = time.time() + 1800
            self.log("Every account's builders/lab are busy - farming here, checking again in 30 min.", "ok")
            return False
        frame = self.shot()
        k = frame.shape[1] / 1920
        cog = self.find(frame, "settings_cog_button") or (int(1842 * k), int(765 * k))
        self.tap(cog, 2.0)
        sw = self.wait_for("switch_account_button", 5)
        tag = settings_tag(self.shot()) if sw else None
        sc_of = self.cfg.setdefault("sc_of_tag", {})
        if tag and getattr(self, "_cur_sc", None):
            if sc_of.get(tag) != self._cur_sc:
                sc_of[tag] = self._cur_sc  # this account = that Supercell ID (exact, unlike the in-game name)
                save_config(self.cfg)
        elif tag:
            self._cur_sc = next((sc for t, sc in sc_of.items() if same_tag(t, tag)), None)
        if not sw:
            return self.switch_fail("switch-account button not found")
        self.tap(sw, 2.5)
        if not self.wait_for("supercell_id_header", 6):
            return self.switch_fail("Supercell ID list didn't open")
        rows = self.all_accounts()
        if target:
            idx = next((i for i, r in enumerate(rows) if r["sc"] == target), None)
            if idx is None:
                return self.switch_fail(f"{target} isn't on the Supercell ID list")
            self._acc_idx, self._switch_streak = idx - 1, -1  # the pick below lands on it; a fresh rotation
        wanted = {a.strip().lower() for a in self.cfg["accounts"].split(",") if a.strip()} if not target else None
        if wanted:
            rows = [r for r in rows if r["sc"].lower() in wanted]
        self._n_accounts = len(rows)
        if len(rows) < 2 and not target:
            return self.switch_fail(f"need 2+ accounts to rotate, found {[r['sc'] for r in rows]}")
        # the one we're on: known exactly after a switch; at the start, the row whose in-game name (and Town Hall,
        # when two share a name) matches this account
        scans = self.cfg.get("scans") or {}
        acc = next((n for t, n in (self.cfg.get("account_tags") or {}).items() if same_tag(t, tag)), None)
        hall = ((scans.get(acc or self._last_name) or {}).get("home") or {}).get("hall")
        cur = next((i for i, r in enumerate(rows) if r["sc"] == getattr(self, "_cur_sc", None)), None)
        if cur is None:
            bare = re.sub(r" \(.*\)$", "", self._last_name or "")
            if tag and acc is None:  # an account not seen before: not one of the known accounts' rows
                known = {((scans.get(n) or {}).get("home") or {}).get("hall")
                         for n in (self.cfg.get("account_tags") or {}).values()}
                cur = next((i for i, r in enumerate(rows) if self.same_game_name(r["game"], bare)
                            and r["th"] not in known), None)
            else:
                cur = next((i for i, r in enumerate(rows) if self.same_game_name(r["game"], bare)
                            and (hall is None or r["th"] in (None, hall))), None)
        self._acc_idx = ((cur if cur is not None and not target else self._acc_idx) + 1) % len(rows)
        row = rows[self._acc_idx]
        name = row["sc"]
        self.log(f"Switching account -> {name}", "ok")
        self._last_name, self._pre, self._sc_key, self._tag_ok = None, None, None, None  # new account: re-read its name
        if not self.tap_account(name):
            return self.switch_fail(f"couldn't find {name} on the Supercell ID list")
        self._cur_sc = name
        end, backs = time.time() + 75, 0
        while time.time() < end:
            f = self.shot()
            if self.at_village(f):  # home OR Builder Base: an account opens on whichever village it was left on
                self._switch_streak += 1
                self._upgrade_backoff.clear()
                self._bank_backoff.clear()
                self._busy_until.clear()
                self.bump("switches")
                # plans / scans / Star Bonus follow the in-game name (top-left) - the Supercell ID list's name can
                # differ; it's only the fallback when the name can't be read yet
                self._last_name = None
                for _ in range(3):
                    if self.account_name(self.shot()) != "?":
                        break
                    self.sleep(1.0)
                self._last_name = self._last_name or name
                self._sc_key = self.account_key(row, rows, self._last_name)  # two accounts with one in-game name
                if self._sc_key:
                    self._last_name = self._sc_key
                self.emit("state", f"Home village ({self._last_name})")
                return True
            if self.find(f, "wall_okay_button") or time.time() > end - 60 + 6 * (backs + 1):
                if backs >= 2 and backs % 2 == 0 and self.groq_on("groq_supervisor"):
                    self.groq_rescue(f)  # e.g. an event character's speech bubble: a tap moves it on, Back doesn't
                else:
                    self.adb.back()  # 'Welcome back' / news popups; Back never confirms anything
                backs += 1
            self.sleep(2.0)
        return self.switch_fail(f"{name} didn't reach its village")

    def switch_fail(self, why):
        self._rotate_pause_until = time.time() + 900
        self.log(f"Account switch: {why} - staying on this account for 15 min.", "warn")
        self.back_to_village()
        return False

    def line(self):
        """Drop line: deploy_point -> deploy_line_end (if captured), else just the one point."""
        pts = self.cfg["fixed_points"]
        a = pts["deploy_point"]
        return a, pts.get("deploy_line_end") or a

    @staticmethod
    def along(a, b, k, n):
        """k-th of n points spread evenly from a to b (inclusive)."""
        f = k / (n - 1) if n > 1 else 0.5
        return int(a[0] + (b[0] - a[0]) * f), int(a[1] + (b[1] - a[1]) * f)

    def speed(self):
        """(pause between taps, pause after picking a card) for the chosen placing speed."""
        return DEPLOY_SPEEDS.get(self.cfg.get("deploy_speed"), DEPLOY_SPEEDS["Fastest"])

    def drop(self, a, b, n, card):
        """Deploy n of the selected unit as taps spread evenly along a->b. Never drags: a moving touch scrolls the
        view instead of placing troops. With a single spot (a == b) and hold-to-deploy, a still long-press is used."""
        c = self.cfg
        if a == b and c["hold_deploy"] and n >= 3 and card:
            ms = min(n * c["hold_ms_per_troop"], 8000)
            for _ in range(3):
                self.adb.swipe(a[0], a[1], a[0], a[1], ms)
                if icon_empty(self.shot(), *card):
                    break
            return
        pts = [self.along(a, b, k, n) for k in range(n)]
        gap = self.speed()[0]
        if fast_taps(self.adb, pts, gap):
            return
        gap = max(gap, 0.05)  # `input tap` fallback
        for i in range(0, n, 20):  # one shell call per 20 taps - fast, no round trip per troop
            chunk = pts[i:i + 20]
            self.adb.shell(f"; sleep {gap}; ".join(f"input tap {x} {y}" for x, y in chunk), timeout=10 + len(chunk))

    def auto_deploy(self, a, b, cards=None):
        """Read this account's troop bar and deploy it: spells first (if enabled), then every troop card (all of
        it), then every hero / siege machine / pet (one tap each)."""
        cards = cards or troop_bar(self.shot())  # the deploy's debug read, when there was one
        troops = [cd for cd in cards if cd[2] == "troop" and cd[3]]
        spells = [cd for cd in cards if cd[2] == "spell" and cd[3]] if self.cfg["deploy_spells"] else []
        singles = [cd for cd in cards if cd[2] in ("hero", "single")]
        if not troops and not singles and not spells:
            return False
        fp = self.cfg["fixed_points"]
        if fp.get("spell_point"):  # their own line, if set
            sa, sb = fp["spell_point"], fp.get("spell_line_end") or fp["spell_point"]
        else:  # else around the middle of the troop line
            sa, sb = self.along(a, b, 1, 4), self.along(a, b, 2, 4)
        for x, y, _, n in spells:  # spells FIRST, as taps spread along their line (a hold doesn't cast them)
            self.tap((x, y), self.speed()[1])
            self.drop(sa, sb, n, None)
        delay = self.speed()[1]
        for x, y, _, n in troops:  # every troop on the saved line - the camera pans to the same spot each battle
            self.tap((x, y), delay)
            self.drop(a, b, n, (x, y))
        for k, (x, y, _, _) in enumerate(singles):  # heroes / siege spread evenly along the same line
            if not fast_taps(self.adb, [(x, y)]) or not fast_taps(self.adb, [self.along(a, b, k, len(singles))]):
                self.tap((x, y), delay)
                self.adb.tap(*self.along(a, b, k, len(singles)))
            self.sleep(0.1)
        # tapping a deployed hero's card = its ability. Never the Clan Castle's: a siege machine's card would
        # break it open early
        self._ability_cards = [(x, y) for x, y, kind, _ in singles if kind == "hero"]
        self.log(f"Auto-deployed {sum(cd[3] for cd in troops)} troops ({len(troops)} types), "
                 f"{len(singles)} heroes/siege" + (f", {len(spells)} spell types." if spells else "."))
        return True

    def close_popups(self):
        """Only clear things that block the Attack button: an Okay/Cancel dialog (Back = Cancel) or the
        builder list (its icon toggles it). A selected wall's button bar doesn't block Attack, so it stays -
        pressing Back there would open the 'quit the game?' dialog."""
        for _ in range(3):
            f = self.shot()
            if self.find(f, "wall_okay_button"):
                self.adb.back()
            elif self.find_wall_rows(f):
                self.adb.tap(*top_bar(f, "builder")[0])
            else:
                return
            self.sleep(0.8)

    # --- recovery ---
    def emulator_restart_allowed(self):
        return self.cfg["watchdog_enabled"] and os.path.isfile(self.cfg["emulator_exe_path"])

    def launch_game(self):
        pkg, act = self.cfg["coc_package_name"], self.cfg["coc_activity_name"]
        self.adb.shell(f"am force-stop {pkg}")
        self.sleep(2)
        if act:
            self.adb.shell(f"am start -n {pkg}/{act}", timeout=20)
        else:
            self.adb.shell(f"monkey -p {pkg} -c android.intent.category.LAUNCHER 1", timeout=20)
        self._launched_at = time.time()
        self.sleep(self.cfg["game_launch_wait"])

    def recover_game(self, reason):
        self.bump("recoveries")
        self.game_relaunches += 1
        self.emit("state", "Recovering")
        if self.game_relaunches > 2 and self.emulator_restart_allowed():
            self.log(f"Recovery: {reason}. Game relaunch didn't help twice - restarting the emulator.", "err")
            self.restart_emulator()
            self.game_relaunches = 0
            return
        self.log(f"Recovery: {reason} - relaunching the game.", "err")
        self.launch_game()
        if self.game_relaunches > 2:  # can't escalate: back off so we don't hammer a broken setup
            self.sleep(min(600, 60 * self.game_relaunches))

    def reconnect(self):
        target = self.cfg["auto_connect_target"]
        if target:
            self.log(f"adb connect {target}: {self.adb.connect(target)}")
        devs = self.adb.devices()
        if devs and self.adb.device not in devs:
            self.adb.device = target if target in devs else devs[0]
            self.emit("devices", devs)
        return self.adb.ready()

    def emulator_crashed(self):
        """BlueStacks' window process is gone (crashed or closed). Restart it; two crashes within 30 min mean this
        graphics setup doesn't work on this PC, so the next one is tried (and kept once it stops crashing)."""
        now = time.time()
        self._crashes = [t for t in getattr(self, "_crashes", []) if now - t < 1800] + [now]
        edit = None
        idx = int(self.cfg.get("gfx_profile", 0))
        if len(self._crashes) >= 2 and idx + 1 < len(GFX_PROFILES):
            idx += 1
            name, values = GFX_PROFILES[idx]
            self.cfg["gfx_profile"] = idx
            save_config(self.cfg)
            self._crashes = []
            self.log(f"BlueStacks keeps crashing - switching its graphics to '{name}' and restarting.", "err")
            edit = lambda: bs_conf_set(values)
        else:
            self.log(f"BlueStacks crashed or was closed ({len(self._crashes)} in 30 min) - restarting it.", "err")
        self.bump("recoveries")
        self.restart_emulator(while_closed=edit)

    def recover_adb(self, fails):
        self.adb.close_shell()
        if self.emulator_restart_allowed() and not process_running(self.cfg["emulator_exe_path"]):
            return self.emulator_crashed()
        try:
            if fails >= 2:
                self.adb.host("kill-server", timeout=10)
                self.adb.host("start-server", timeout=20)
            if self.reconnect():
                self.log("ADB reconnected.", "ok")
                self.emit("device", True)
                return
        except ADBError as e:
            self.log(f"Reconnect failed: {e}", "warn")
        if fails >= 3 and self.emulator_restart_allowed():
            self.bump("recoveries")
            self.restart_emulator()
            return
        self.sleep(min(120, 3 * fails * fails))  # 3s, 12s, 27s... quick first retry

    def fix_resolution(self, frame):
        """Buttons, drop lines and text boxes are all 1920x1080 pixels. The monitor doesn't matter (screenshots
        come from inside the emulator), but BlueStacks' own resolution does: set it back and restart BlueStacks."""
        h, w = frame.shape[:2]
        conf = r"C:\ProgramData\BlueStacks_nxt\bluestacks.conf"
        if getattr(self, "_res_fixed", False) or not self.emulator_restart_allowed() or not os.path.exists(conf):
            self.log(f"The emulator is {w}x{h} but must be 1920x1080: BlueStacks Settings > Display > "
                     "1920x1080, DPI 240, then restart BlueStacks.", "err")
            self.sleep(60)
            return
        self._res_fixed = True
        self.log(f"The emulator is {w}x{h} - setting BlueStacks to 1920x1080 and restarting it.", "warn")

        self.restart_emulator(while_closed=lambda: bs_conf_set({"fb_width": "1920", "fb_height": "1080", "dpi": "240"}))

    def restart_emulator(self, while_closed=None):
        now = time.time()
        self._emu_restarts = [t for t in self._emu_restarts if now - t < 3600]
        if len(self._emu_restarts) >= 3:
            self.log("3 emulator restarts in the last hour - cooling down 15 min before the next one.", "err")
            self.sleep(900)
        self._emu_restarts.append(time.time())
        exe = self.cfg["emulator_exe_path"]
        self.log("Restarting the emulator...", "err")
        self.adb.close_shell()
        subprocess.run(["taskkill", "/IM", os.path.basename(exe), "/T", "/F"], capture_output=True,
                       timeout=20, creationflags=NO_WINDOW)
        self.sleep(5)
        try:  # BlueStacks rewrites its conf on exit, so settings are changed only while it's closed
            bs_conf_set(GFX_PROFILES[min(int(self.cfg.get("gfx_profile", 0)), len(GFX_PROFILES) - 1)][1])
            if while_closed:
                while_closed()
        except OSError as e:
            self.log(f"Couldn't change BlueStacks' settings: {e}", "err")
        subprocess.Popen([exe, *self.cfg["emulator_launch_args"].split()], creationflags=0x00000008)  # detached
        self.sleep(self.cfg["emulator_boot_wait"])
        end = time.time() + self.cfg["adb_ready_timeout"]
        while time.time() < end:
            try:
                if self.reconnect():
                    break
            except ADBError:
                pass
            self.sleep(5)
        else:
            self.log("Emulator didn't come back on ADB in time; will keep trying.", "warn")
            return
        self.emit("device", True)
        for i in range(4):  # Android can still be starting up for a while after ADB answers
            try:
                return self.launch_game()
            except ADBError as e:
                self.log(f"Game launch after the emulator restart failed ({e}) - retrying.", "warn")
                self.sleep(15)
                self.reconnect()


# ---------------------------------------------------------------------------
# Phone view: read-only web page (live screen + stats), shared through the Anywhere link
# ---------------------------------------------------------------------------
PHONE_PAGE = """<!doctype html><html><head><meta name="viewport" content="width=device-width,initial-scale=1">
<meta name="theme-color" content="#141414"><title>Loot Farmer</title><style>
*{box-sizing:border-box}body{margin:0;background:#1c1c1c;color:#e6e6e6;font:15px system-ui,-apple-system,"Segoe UI",sans-serif}
.wrap{max-width:760px;margin:0 auto;padding:14px}
header{display:flex;align-items:center;gap:10px;margin-bottom:12px}header img{height:42px}
h1{font-size:19px;margin:0}.sub{color:#9a9a9a;font-size:12px}
.pill{margin-left:auto;padding:6px 12px;border-radius:999px;font-weight:600;font-size:13px;background:#1f3a2c;color:#4cc38a;
white-space:nowrap;max-width:46%;overflow:hidden;text-overflow:ellipsis}
.pill.off{background:#3a1f1f;color:#ff6b6b}.pill.idle{background:#2b2b2b;color:#9a9a9a}
#f{width:100%;border-radius:12px;background:#141414;min-height:140px;display:block}
.row{display:grid;gap:8px;margin:10px 0}.r3{grid-template-columns:repeat(3,1fr)}.r2{grid-template-columns:repeat(2,1fr)}
.r4{grid-template-columns:repeat(4,1fr)}
.c{background:#2b2b2b;border-radius:12px;padding:10px;display:flex;align-items:center;gap:8px;min-width:0}
.c img{height:28px;flex:none}.c .v{font-weight:700;font-size:17px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.c .l{color:#9a9a9a;font-size:11px;text-transform:uppercase;letter-spacing:.03em}
.s{flex-direction:column;align-items:flex-start;gap:2px;padding:8px 10px}.s .v{font-size:16px}
.gold{color:#f5c542}.elixir{color:#d77bff}.dark{color:#b9a3ff}
h2{font-size:12px;color:#9a9a9a;text-transform:uppercase;letter-spacing:.05em;margin:16px 2px 6px}
.card{background:#2b2b2b;border-radius:12px;padding:10px 12px}
.acc{display:flex;align-items:center;gap:6px;padding:6px 0;border-bottom:1px solid #353535;flex-wrap:wrap}.acc:last-child{border:0}
.acc b{flex:1 1 100%;font-size:14px}.acc span{display:flex;align-items:center;gap:3px;font-weight:600;font-size:13px;margin-right:8px}
.acc img{height:16px}
.wall{padding:6px 0;border-bottom:1px solid #353535}.wall:last-child{border:0}.wall b{font-size:14px}
.wall .n{color:#f5c542;font-weight:600;font-size:13px}.wall .ok{color:#4cc38a;font-weight:600;font-size:13px}
.wall .m{color:#9a9a9a;font-size:12px}
.ctl{display:flex;flex-wrap:wrap;gap:8px;align-items:center;margin:10px 0}
.ctl select,.ctl button{font:inherit;font-size:14px;border:0;border-radius:10px;padding:10px 12px;background:#3a3a3a;color:#e6e6e6}
.ctl select{flex:1 1 140px}.ctl .go{background:#2f7d55;font-weight:700;min-width:90px}.ctl .go.stop{background:#a33a3a}
.ctl #cmsg{flex-basis:100%;color:#9a9a9a;font-size:12px}
#log{background:#141414;border-radius:12px;padding:10px;font:12px ui-monospace,Consolas,monospace;white-space:pre-wrap;
max-height:260px;overflow:auto}
@media(max-width:420px){.r4{grid-template-columns:repeat(2,1fr)}}
</style></head><body><div class="wrap">
<header><img id="logo"><div><h1>Loot Farmer</h1><div class="sub" id="mode">&hellip;</div></div>
<div class="pill idle" id="state">&hellip;</div></header>
<img id="f" alt="">
<div class="card ctl"><select id="m"></select><button id="go" class="go">Start</button>
<select id="pz"><option value="">Pause&hellip;</option><option value="15">15 min</option><option value="30">30 min</option>
<option value="60">1 hour</option><option value="120">2 hours</option></select><button id="rg">Restart game</button>
<select id="acc"></select><button id="sw">Switch account</button>
<div id="cmsg"></div></div>
<div class="row r3" id="rates"></div>
<div class="row r2" id="store"></div>
<div class="row r4" id="g"></div>
<h2>Accounts this session</h2><div class="card" id="loot"></div>
<h2>Walls</h2><div class="card" id="walls"></div>
<h2>Activity</h2><div id="log"></div>
</div><script>
const Q=location.search, ic=n=>"ui/"+n+".png"+Q, $=id=>document.getElementById(id);
$("logo").src=ic("king");
let RUN=false,MODE="";
async function cmd(o){$("cmsg").textContent="Sending…";try{const r=await fetch("cmd"+Q,{method:"POST",
headers:{"Content-Type":"application/json"},body:JSON.stringify(o)});$("cmsg").textContent=(await r.json()).msg||"";}
catch(e){$("cmsg").textContent="PC not reachable.";}setTimeout(tick,600);}
$("go").onclick=()=>RUN?confirm("Stop farming?")&&cmd({action:"stop"}):cmd({action:"start",mode:$("m").value});
$("m").onchange=()=>{if(RUN&&$("m").value!==MODE){confirm("Switch to "+$("m").selectedOptions[0].text+"?")?
cmd({action:"start",mode:$("m").value}):($("m").value=MODE);}};
$("pz").onchange=()=>{const v=$("pz").value;$("pz").value="";if(v&&confirm("Pause for "+v+" minutes?"))cmd({action:"pause",minutes:+v});};
$("rg").onclick=()=>confirm("Restart Clash of Clans?")&&cmd({action:"restart_game"});
$("sw").onclick=()=>{const a=$("acc").value;if(!a)return cmd({action:"load_accounts"});
if(confirm("Switch to "+a+"?"))cmd({action:"switch_account",account:a});};
const STATS=[["runtime","Runtime"],["attacks","Attacks","king"],["walls","Walls","wall"],["upgrades","Upgrades","hammer"],
["switches","Switches","builder_icon"],["skipped","Skipped","shield"],["recoveries","Restarts"],["battery","Battery"]];
async function tick(){try{const s=await (await fetch("status"+Q,{cache:"no-store"})).json();
const st=$("state");st.textContent=s.state;st.className="pill"+(/idle|stopped/i.test(s.state)?" idle":/recover/i.test(s.state)?" off":"");
$("mode").textContent=s.mode?"Mode: "+s.mode:"";
if(s.modes&&!$("m").options.length)$("m").innerHTML=s.modes.map(([k,l])=>`<option value="${k}">${l}</option>`).join("");
const A=s.accounts||[];if($("acc").options.length!==(A.length||1))$("acc").innerHTML=A.length?
A.map(([k,l])=>`<option value="${k}">${l}</option>`).join(""):'<option value="">No accounts saved yet</option>';
$("sw").textContent=A.length?"Switch account":"Load accounts";if(s.current_acc&&document.activeElement!==$("acc"))$("acc").value=s.current_acc;
RUN=!!s.running;MODE=s.mode_key||"";if(document.activeElement!==$("m"))$("m").value=MODE;
$("go").textContent=RUN?"Stop":"Start";$("go").className="go"+(RUN?" stop":"");
if(s.resume_in>0)$("cmsg").textContent="Paused - starts again in "+Math.ceil(s.resume_in/60)+" min.";
const B=s.bb,I=k=>B&&k!="dark"?"b"+k:k;$("rates").className="row "+(B?"r2":"r3");
const R=s.rates||{};$("rates").innerHTML=[["gold","gold"],["elixir","elixir"]].concat(B?[]:[["dark","dark"]]).map(([k,c])=>
`<div class="c"><img src="${ic(I(k))}"><div style="min-width:0"><div class="v ${c}">${((R[k]||["—"])[0]).replace(" / h","").replace(/(\\.\\d)\\dM/,"$1M")}</div><div class="l">per hour</div><div class="l" style="text-transform:none">${((R[k]||["",""])[1]).replace(" this session"," total")}</div></div></div>`).join("");
$("store").innerHTML=[["s_gold","gold","gold"],["s_elixir","elixir","elixir"]].map(([k,i,c])=>
`<div class="c"><img src="${ic(I(i))}"><div class="v ${c}">${s[k]??"—"}</div></div>`).join("");
$("g").innerHTML=STATS.map(([k,l,i])=>`<div class="c s"><div class="l">${i?`<img src="${ic(i)}" style="height:14px;vertical-align:-2px"> `:""}${l}</div><div class="v">${s[k]??"-"}</div></div>`).join("");
const L=s.loot||[];$("loot").innerHTML=L.length?L.map(r=>`<div class="acc"><b>${r[0]}</b>
<span class="gold"><img src="${ic(I("gold"))}">${r[1]}</span><span class="elixir"><img src="${ic(I("elixir"))}">${r[3]}</span>
${B?"":`<span class="dark"><img src="${ic("dark")}">${r[5]}</span>`}<span><img src="${ic("king")}">${r[7]}</span></div>`).join(""):'<div class="sub">Shows up once farming starts.</div>';
const W=s.walls_view||[];$("walls").innerHTML=W.length?W.map(w=>`<div class="wall"><b>${w[0]}</b><div class="${w[2]?"n":"ok"}">${w[1]}</div>${w[2]?`<div class="m">${w[2]}</div>`:""}</div>`).join(""):'<div class="sub">Scan an account in the planner to see its walls.</div>';
$("log").textContent=(s.log||[]).join("\\n");
$("f").src="frame.jpg"+Q+"&t="+Date.now();}catch(e){const st=$("state");st.textContent="PC not reachable";st.className="pill off";}}
tick();setInterval(tick,1500);</script></body></html>"""


PHONE_ACTIONS = ("start", "stop", "pause", "restart_game", "switch_account", "load_accounts")


class PhoneView:
    """Serves PHONE_PAGE, the latest frame and a status JSON, and takes the page's commands (POST /cmd: start /
    stop / pause / restart the game - nothing that taps the game or spends anything). The link's key is the only
    lock, so the link is as good as the controls."""

    def __init__(self, port, key, on_cmd=None):
        self.jpeg, self.status, self.last_seen = b"", {"state": "Idle", "log": []}, 0
        view = self

        class Handler(http.server.BaseHTTPRequestHandler):
            def do_POST(self):
                path, _, query = self.path.partition("?")
                if f"k={key}" not in query.split("&") or path != "/cmd" or not on_cmd:
                    self.send_error(403)
                    return
                try:
                    cmd = json.loads(self.rfile.read(min(int(self.headers.get("Content-Length") or 0), 2000)))
                    ok = isinstance(cmd, dict) and cmd.get("action") in PHONE_ACTIONS
                except (ValueError, TypeError):
                    ok = False
                if ok:
                    on_cmd(cmd)
                body = json.dumps({"ok": ok, "msg": "Sent to the PC." if ok else "Unknown command."}).encode()
                self.send_response(200 if ok else 400)
                self.send_header("Content-Type", "application/json")
                self.send_header("Content-Length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)

            def do_GET(self):
                path, _, query = self.path.partition("?")
                if f"k={key}" not in query.split("&"):
                    self.send_error(403, "Missing or wrong access key - use the full link shown in the app.")
                    return
                view.last_seen = time.time()  # someone has the page open (the idle view only runs then)
                if path == "/frame.jpg":
                    body, ctype = view.jpeg, "image/jpeg"
                elif re.fullmatch(r"/ui/[a-z_]+\.png", path):  # the page's Clash icons (wiki/ui)
                    try:
                        with open(os.path.join(WIKI_DIR, "ui", path[4:]), "rb") as fh:
                            body, ctype = fh.read(), "image/png"
                    except OSError:
                        self.send_error(404)
                        return
                elif path == "/status":
                    body, ctype = json.dumps(view.status).encode(), "application/json"
                else:
                    body, ctype = PHONE_PAGE.encode(), "text/html; charset=utf-8"
                self.send_response(200)
                self.send_header("Content-Type", ctype)
                self.send_header("Content-Length", str(len(body)))
                self.send_header("Cache-Control", "no-store")
                self.end_headers()
                self.wfile.write(body)

            def log_message(self, *a):
                pass

        self.server = http.server.ThreadingHTTPServer(("0.0.0.0", port), Handler)
        self.server.daemon_threads = True
        threading.Thread(target=self.server.serve_forever, daemon=True).start()


def _pid_image(pid):
    """Full exe path of a running process, or None if it isn't running (Windows)."""
    k32 = ctypes.windll.kernel32
    h = k32.OpenProcess(0x1000, False, int(pid))  # PROCESS_QUERY_LIMITED_INFORMATION
    if not h:
        return None
    try:
        code = ctypes.c_ulong()
        if not k32.GetExitCodeProcess(h, ctypes.byref(code)) or code.value != 259:  # STILL_ACTIVE
            return None
        buf, n = ctypes.create_unicode_buffer(1024), ctypes.c_ulong(1024)
        return buf.value if k32.QueryFullProcessImageNameW(h, 0, buf, ctypes.byref(n)) else None
    finally:
        k32.CloseHandle(h)


class Tunnel:
    """Cloudflare quick tunnel: a public https://....trycloudflare.com link to the phone view, no account.
    cloudflared runs DETACHED and is reused by the next app start (tunnel.json), so restarting the app keeps
    the same link. It only changes after a PC reboot or if the tunnel drops (then a new one starts)."""
    STATE = os.path.join(BASE_DIR, "tunnel.json")
    LOG = os.path.join(BASE_DIR, "cloudflared.log")

    def __init__(self, exe, port, on_url):
        self.exe, self.port, self.on_url = exe, port, on_url
        threading.Thread(target=self._run, daemon=True).start()

    def _alive(self, st):
        img = _pid_image(st.get("pid", 0)) if st else None
        return bool(img and img.lower().endswith("cloudflared.exe") and st.get("port") == self.port)

    def _start(self):
        """Start cloudflared; the link only counts once the tunnel has REGISTERED with Cloudflare - the address is
        printed before that, and a PC whose network blocks the connection would hand out a dead link. HTTP/2 over
        TCP 443 gets through routers / firewalls / VPNs that block QUIC (UDP), cloudflared's default."""
        if not self._local_ok():
            log_file.warning(f"Phone view server isn't answering on port {self.port} - the Anywhere link would show "
                             "a Cloudflare error. Is another program using that port?")
        with open(self.LOG, "w") as lf:
            proc = subprocess.Popen([self.exe, "tunnel", "--no-autoupdate", "--protocol", "http2",
                                     "--url", f"http://localhost:{self.port}"],
                                    stdout=lf, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL,
                                    creationflags=0x00000008 | 0x00000200)  # DETACHED | NEW_PROCESS_GROUP
        url = None
        for _ in range(90):
            time.sleep(1)
            try:
                text = open(self.LOG, errors="replace").read()
            except OSError:
                text = ""
            m = re.search(r"https://[a-z0-9-]+\.trycloudflare\.com", text)
            url = m.group() if m else url
            if url and "Registered tunnel connection" in text:
                st = {"pid": proc.pid, "url": url, "port": self.port}
                with open(self.STATE, "w") as f:
                    json.dump(st, f)
                return st
            if proc.poll() is not None:
                break
        log_file.warning(("cloudflared got a link but never connected (network blocking it?): " if url else
                          "cloudflared didn't give a link: ") + open(self.LOG, errors="replace").read()[-500:])
        proc.kill()
        return None

    def _local_ok(self):
        """The phone view server answers (403 without the key still means it's up)."""
        try:
            urllib.request.urlopen(f"http://127.0.0.1:{self.port}/status", timeout=5).close()
            return True
        except urllib.error.HTTPError:
            return True
        except Exception:
            return False

    def _run(self):
        unconfirmed = 0  # new links in a row that never answered a check
        try:
            st = json.load(open(self.STATE))
        except Exception:
            st = None
        while True:
            try:
                if self._alive(st) and self._link_works(st["url"]) is False:
                    # e.g. a saved tunnel Cloudflare has deleted: cloudflared keeps running ('Tunnel not found')
                    log_file.warning(f"Anywhere link {st['url']} is dead - starting a new one.")
                    self._kill(st)
                if not self._alive(st):
                    self.on_url(None)
                    try:
                        st = self._start()
                    except OSError as e:
                        log_file.warning(f"cloudflared failed: {e}")
                        st = None
                    # a brand-new name takes a few seconds to exist; opening it before that gets 'site can't be
                    # reached' cached in the browser, so only hand the link out once it answers
                    if st:
                        for _ in range(24):  # up to ~2 min
                            if self._link_works(st["url"]):
                                unconfirmed = 0
                                break
                            time.sleep(5)
                        else:  # never answered: don't post a dead link - a fresh tunnel (twice), then give up
                            unconfirmed += 1
                            if unconfirmed <= 2:
                                log_file.warning(f"New Anywhere link {st['url']} never answered - starting another.")
                                self._kill(st)
                                st = None
                            else:  # our own check may be what's failing (no internet?): hand it out anyway
                                log_file.warning(f"Anywhere link {st['url']} couldn't be confirmed - posting it "
                                                 "anyway.")
                                unconfirmed = 0
                    if not st:
                        time.sleep(30)
                        continue
                self.on_url(st["url"])
                checked = time.time()
                while self._alive(st):
                    time.sleep(10)
                    if time.time() - checked > 60:
                        checked = time.time()
                        if self._link_works(st["url"]) is False and self._link_works(st["url"]) is False:
                            log_file.warning(f"Anywhere link {st['url']} stopped working - starting a new one.")
                            self._kill(st)
                            break
            except Exception as e:  # the tunnel thread must never die
                log_file.warning(f"Tunnel: {e}")
                st = None
                time.sleep(30)

    @staticmethod
    def _kill(st):
        subprocess.run(["taskkill", "/PID", str(st["pid"]), "/F"], capture_output=True, creationflags=NO_WINDOW)
        time.sleep(1)

    @staticmethod
    def _link_works(url):
        """True: our server answers through the tunnel. False: Cloudflare says it's gone (name doesn't exist /
        530). None: can't tell (no internet, VPN reconnecting...) - never a reason to throw a working link away."""
        import socket
        host = url.split("//", 1)[-1].split("/")[0]
        try:  # ask Cloudflare's DNS directly: a lookup through Windows would cache 'no such name' for minutes
            r = json.load(urllib.request.urlopen(urllib.request.Request(
                f"https://cloudflare-dns.com/dns-query?name={host}&type=A",
                headers={"accept": "application/dns-json"}), timeout=10))
            if r.get("Status") == 3 or (r.get("Status") == 0 and not r.get("Answer")):  # 3 = no such name
                return False
        except Exception:
            pass  # that lookup service is blocked on some networks / antivirus: just try the link itself
        try:
            urllib.request.urlopen(url + "/status", timeout=15).close()
            return True
        except urllib.error.HTTPError as e:
            return e.code not in (502, 530, 1033)
        except urllib.error.URLError as e:
            return False if isinstance(e.reason, socket.gaierror) else None  # name doesn't exist = dead link
        except Exception:
            return None

    @staticmethod
    def kill_saved():
        """Stop a background tunnel left running (used when the public link is turned off)."""
        try:
            st = json.load(open(Tunnel.STATE))
            if (_pid_image(st["pid"]) or "").lower().endswith("cloudflared.exe"):
                subprocess.run(["taskkill", "/PID", str(st["pid"]), "/F"], capture_output=True,
                               creationflags=NO_WINDOW)
        except Exception:
            pass


PAN_DIRS = {"top-left": (1, 1), "top-right": (-1, 1), "bottom-left": (1, -1), "bottom-right": (-1, -1),
            "left": (1, 0), "right": (-1, 0), "top": (0, 1), "bottom": (0, -1)}


def pan_view(adb, where, frame_w=1920):
    """Drag the battle camera as far as it goes towards `where` (e.g. 'top-left' shows the map's top-left edge).
    The game stops at the map edge, so the view is identical every attack and saved drop points line up.
    Slow drags on the open map area (away from the buttons and troop bar) so nothing gets tapped or flung."""
    d = PAN_DIRS.get(where)
    if not d:
        return
    k = frame_w / 1920
    cx, cy, dx, dy = 960 * k, 460 * k, 450 * k * d[0], 270 * k * d[1]
    for _ in range(2):  # two long drags reach the edge (measured: same view as three short ones, in half the time)
        adb.swipe(cx - dx, cy - dy, cx + dx, cy + dy, 300)
        time.sleep(0.15)


BS_CONF = r"C:\ProgramData\BlueStacks_nxt\bluestacks.conf"
# Graphics setups to try, in order, when BlueStacks keeps crashing (typically on the game's loading clouds - a
# graphics-driver crash, e.g. NVIDIA + Vulkan). 0 = leave BlueStacks as the user set it.
GFX_PROFILES = [
    ("as set in BlueStacks", {}),
    ("OpenGL", {"graphics_renderer": "gl", "graphics_engine": "aga", "max_fps": "30"}),
    ("OpenGL + Compatibility", {"graphics_renderer": "gl", "graphics_engine": "legacy", "max_fps": "30"}),
    ("Vulkan + Compatibility", {"graphics_renderer": "vlcn", "graphics_engine": "legacy", "max_fps": "30"}),
]


def bs_conf_set(values):
    """Set bst.instance.<every instance>.<key> in bluestacks.conf. Only while BlueStacks is closed: it rewrites
    the file when it exits. A backup of the first original is kept next to it."""
    if not values or not os.path.exists(BS_CONF):
        return
    if not os.path.exists(BS_CONF + ".lootfarmer-original"):
        shutil.copy2(BS_CONF, BS_CONF + ".lootfarmer-original")
    s = open(BS_CONF, encoding="utf-8").read()
    for key, val in values.items():
        s = re.sub(rf'(bst\.instance\.[^.\n]+\.{key})="[^"]*"', rf'\1="{val}"', s)
    with open(BS_CONF, "w", encoding="utf-8", newline="") as f:
        f.write(s)


def process_running(exe):
    try:
        out = subprocess.run(["tasklist", "/FI", f"IMAGENAME eq {os.path.basename(exe)}", "/NH"], capture_output=True,
                             text=True, timeout=15, creationflags=NO_WINDOW).stdout
    except Exception:
        return True  # can't tell: assume it's running rather than kill a working emulator
    return os.path.basename(exe).lower() in out.lower()


def post_discord(cfg, text, files=()):
    """Best effort: a failed post is logged, never raised. files: [(filename, bytes)], up to 10."""
    hook = cfg.get("discord_webhook") or ""
    if not hook.startswith("http"):
        try:
            hook = base64.b64decode(hook).decode()
        except Exception:
            return
    if not hook.startswith("https://discord.com/api/webhooks/"):
        return
    payload = json.dumps({"content": text[:1900]})
    if files:  # multipart: the message as payload_json + each file as files[i]
        b = "----LootFarmer" + secrets.token_hex(8)
        nl = "\r\n"
        parts = [f'--{b}{nl}Content-Disposition: form-data; name="payload_json"{nl}'
                 f'Content-Type: application/json{nl}{nl}{payload}{nl}'.encode()]
        for i, (name, data) in enumerate(files[:10]):
            parts += [f'--{b}{nl}Content-Disposition: form-data; name="files[{i}]"; filename="{name}"{nl}'
                      f'Content-Type: application/octet-stream{nl}{nl}'.encode(), data, nl.encode()]
        body, ctype = b"".join(parts) + f"--{b}--{nl}".encode(), f"multipart/form-data; boundary={b}"
    else:
        body, ctype = payload.encode(), "application/json"
    for i in range(5):  # at start-up the network may not be up yet; Discord rate-limits with 429 + retry_after
        try:
            req = urllib.request.Request(hook, body, method="POST",
                                         headers={"Content-Type": ctype, "User-Agent": "LootFarmer"})
            urllib.request.urlopen(req, timeout=60).close()
            return True
        except urllib.error.HTTPError as e:
            if e.code not in (429, 500, 502, 503, 504):
                log_file.warning(f"Discord post refused: {e}")
                return
            wait = 5 * (i + 1)
            try:
                wait = float(json.loads(e.read()).get("retry_after", wait)) + 1
            except Exception:
                pass
        except Exception as e:
            log_file.info(f"Discord post failed (try {i + 1}): {e}")
            wait = 10 * (i + 1)
        time.sleep(min(wait, 60))
    log_file.warning("Discord post failed 5 times - giving up on this message.")


SHORTCUT_PS = r"""
param([string]$Bot, [string]$PyW, [string]$Ico, [string]$AppId)
Add-Type -TypeDefinition @'
using System; using System.Runtime.InteropServices;
[ComImport, Guid("886D8EEB-8CF2-4446-8D02-CDBA1DBDCF99"), InterfaceType(ComInterfaceType.InterfaceIsIUnknown)]
interface IPropertyStore { int GetCount(out uint c); int GetAt(uint i, out PROPERTYKEY k);
  int GetValue(ref PROPERTYKEY k, out PROPVARIANT v); int SetValue(ref PROPERTYKEY k, ref PROPVARIANT v); int Commit(); }
[StructLayout(LayoutKind.Sequential, Pack = 4)] public struct PROPERTYKEY { public Guid fmtid; public uint pid; }
[StructLayout(LayoutKind.Explicit)] public struct PROPVARIANT { [FieldOffset(0)] public ushort vt; [FieldOffset(8)] public IntPtr p; }
public static class Aumid {
  [DllImport("shell32.dll", CharSet = CharSet.Unicode)]
  static extern int SHGetPropertyStoreFromParsingName(string path, IntPtr bc, int flags, ref Guid iid, out IPropertyStore ps);
  public static void Set(string lnk, string id) {
    Guid iid = new Guid("886D8EEB-8CF2-4446-8D02-CDBA1DBDCF99"); IPropertyStore ps;
    if (SHGetPropertyStoreFromParsingName(lnk, IntPtr.Zero, 2, ref iid, out ps) != 0) return;
    PROPERTYKEY k = new PROPERTYKEY { fmtid = new Guid("9F4C2855-9F79-4B39-A8D0-E1D42DE1D5F3"), pid = 5 };
    PROPVARIANT v = new PROPVARIANT { vt = 31, p = Marshal.StringToCoTaskMemUni(id) };
    ps.SetValue(ref k, ref v); ps.Commit(); Marshal.ReleaseComObject(ps); } }
'@
$ws = New-Object -ComObject WScript.Shell
$pinned = Join-Path $env:APPDATA "Microsoft\Internet Explorer\Quick Launch\User Pinned\TaskBar"
$links = @((Join-Path ([Environment]::GetFolderPath("Desktop")) "Loot Farmer.lnk"),
           (Join-Path ([Environment]::GetFolderPath("Programs")) "Loot Farmer.lnk"))
if (Test-Path $pinned) { $links += Get-ChildItem $pinned -Filter *.lnk | ForEach-Object { $_.FullName } }
foreach ($l in $links) {
  $isOurs = $false
  if (Test-Path $l) { $s = $ws.CreateShortcut($l); $isOurs = ($s.Arguments -like "*bot.py*") -or ($s.TargetPath -like "*bot.py") }
  elseif ($l -notlike "$pinned*") { $isOurs = $true }  # desktop / Start menu: create it
  if (-not $isOurs) { continue }
  $s = $ws.CreateShortcut($l); $s.TargetPath = $PyW; $s.Arguments = '"' + $Bot + '"'
  $s.WorkingDirectory = Split-Path $Bot; $s.IconLocation = $Ico; $s.Description = "Loot Farmer"; $s.Save()
  [Aumid]::Set($l, $AppId); "ok $l"
}
"""


def fix_shortcuts():
    """Desktop + Start menu + pinned taskbar shortcuts that start this bot.py: the King icon and the app's taskbar
    identity (so the running window groups under it, not under Python). Windows only; quietly does nothing else."""
    pyw = os.path.join(os.path.dirname(sys.executable), "pythonw.exe")
    ico = os.path.join(WIKI_DIR, "ui", "app.ico")
    if os.name != "nt" or not os.path.isfile(pyw) or not os.path.isfile(ico):
        return False
    ps1 = os.path.join(tempfile.gettempdir(), "lootfarmer_shortcuts.ps1")
    with open(ps1, "w", encoding="utf-8-sig") as f:
        f.write(SHORTCUT_PS)
    r = subprocess.run(["powershell", "-NoProfile", "-ExecutionPolicy", "Bypass", "-File", ps1, "-Bot",
                        os.path.abspath(__file__), "-PyW", pyw, "-Ico", ico, "-AppId", APP_ID],
                       capture_output=True, text=True, timeout=90, creationflags=NO_WINDOW)
    log_file.info("shortcuts: " + (" | ".join(r.stdout.split()) or r.stderr.strip()[-300:]))
    return r.returncode == 0


def single_instance():
    """A machine-wide lock so only one Loot Farmer drives the emulator. Waits a few seconds first, so the
    Restart / Update buttons (new copy starts while the old one closes) still work. None = another is running."""
    if os.name != "nt":
        return True
    k32 = ctypes.WinDLL("kernel32", use_last_error=True)
    k32.CreateMutexW.restype = ctypes.c_void_p
    k32.CreateMutexW.argtypes = (ctypes.c_void_p, ctypes.c_bool, ctypes.c_wchar_p)
    k32.CloseHandle.argtypes = (ctypes.c_void_p,)
    for _ in range(20):
        h = k32.CreateMutexW(None, False, "Local\\LootFarmerBot")
        if h and ctypes.get_last_error() != 183:  # 183 = ERROR_ALREADY_EXISTS
            return h
        if h:
            k32.CloseHandle(h)
        time.sleep(0.5)
    return None


_TOUCH = {}


def touch_device(adb):
    """(path, max_x, max_y) of the emulator's multi-touch input device (BlueStacks: 'Virtual Touch'), or None."""
    if "dev" not in _TOUCH:
        dev = None
        try:
            out = adb.shell("getevent -p", timeout=10)
        except ADBError:
            return None  # try again next time
        for block in out.split("add device")[1:]:
            mx = re.search(r"0035\s*:.*?max (\d+)", block)
            my = re.search(r"0036\s*:.*?max (\d+)", block)
            if mx and my:
                dev = (block.split(":", 1)[1].split()[0], int(mx.group(1)), int(my.group(1)))
                break
        _TOUCH["dev"] = dev
    return _TOUCH["dev"]


def touch_ev(adb):
    """Packs one raw input event for this emulator. Its size depends on the Android image: 24 bytes on a 64-bit
    one (BlueStacks Pie64), 16 on a 32-bit one - the wrong size and every touch is garbage."""
    if "ev" not in _TOUCH:
        try:
            abi = adb.shell("getprop ro.product.cpu.abi", timeout=10).strip()
        except ADBError:
            abi = ""
        fmt = "<qqHHI" if "64" in abi or not abi else "<llHHI"
        _TOUCH["ev"] = lambda t, c, v: struct.pack(fmt, 0, 0, t, c, v & 0xFFFFFFFF)
        log_file.info(f"touch events: abi {abi!r} -> {struct.calcsize(fmt)} bytes")
    return _TOUCH["ev"]


def zoom_out(adb, times=3, W=1920, H=1080, spread=((460, 900), (1460, 1020))):
    """Two-finger pinch (fingers moving together) = the game's zoom-out, sent straight to the touch device.
    Stops at the game's limit, so extra pinches are harmless. Raw input_event structs are written in one shell
    call per pinch (sendevent costs ~50 ms per event: 3 pinches took 16 s, longer than half the scout timer).
    spread: each finger's start -> end x (swap them to zoom in)."""
    d = touch_device(adb)
    if not d:
        return False
    dev, mx, my = d
    ev = touch_ev(adb)
    for _ in range(times):
        steps = []
        for i in range(9):
            f, b = i / 8, b""
            for slot, (x0, x1) in enumerate(spread):
                b += ev(3, 47, slot) + (ev(3, 57, 100 + slot) if i == 0 else b"")
                b += ev(3, 53, int((x0 + (x1 - x0) * f) / W * mx)) + ev(3, 54, int(480 / H * my))
            b += (ev(1, 330, 1) if i == 0 else b"") + ev(0, 0, 0)  # BTN_TOUCH down with the first frame
            steps.append(b)
        steps.append(ev(3, 47, 0) + ev(3, 57, -1) + ev(3, 47, 1) + ev(3, 57, -1) + ev(1, 330, 0) + ev(0, 0, 0))
        adb.shell("; sleep 0.02; ".join(f"echo {base64.b64encode(s).decode()} | base64 -d > {dev}" for s in steps),
                  timeout=30)
        time.sleep(0.3)
    return True


def fast_taps(adb, pts, gap=0.0, W=1920, H=1080):
    """Taps as raw touch events written straight to the touch device - the device opened once, each tap held
    20 ms (with no hold the game drops some). ~0.05 s a tap instead of ~0.19 s for `input tap`, which starts a
    Java process every time. False if there's no touch device (the caller falls back to `input tap`)."""
    d = touch_device(adb)
    if not d or not pts:
        return False
    dev, mx, my = d
    ev = touch_ev(adb)
    raw = lambda bs: "".join(f"\\{x:03o}" for x in bs)  # printf escapes: exactly 3 octal digits a byte
    up = raw(ev(3, 47, 0) + ev(3, 57, -1) + ev(1, 330, 0) + ev(0, 0, 0))
    cmds = [f"printf '{raw(ev(3, 47, 0) + ev(3, 57, 200 + i % 100) + ev(3, 53, int(x / W * mx)) + ev(3, 54, int(y / H * my)) + ev(1, 330, 1) + ev(0, 0, 0))}' >&3; sleep 0.02; printf '{up}' >&3"
            for i, (x, y) in enumerate(pts)]
    for i in range(0, len(cmds), 30):
        sep = f"; sleep {gap}; " if gap else "; "
        adb.shell(f"exec 3> {dev}; " + sep.join(cmds[i:i + 30]) + "; exec 3>&-", timeout=20 + gap * 30)
    return True


def battery():
    """(percent, plugged_in) from Windows, or None on a PC without a battery."""

    class SPS(ctypes.Structure):
        _fields_ = [("ac", ctypes.c_ubyte), ("flag", ctypes.c_ubyte), ("pct", ctypes.c_ubyte),
                    ("saver", ctypes.c_ubyte), ("life", ctypes.c_ulong), ("full", ctypes.c_ulong)]
    sps = SPS()
    if not ctypes.windll.kernel32.GetSystemPowerStatus(ctypes.byref(sps)) or sps.pct == 255 or sps.flag & 128:
        return None
    return sps.pct, sps.ac == 1


# ---------------------------------------------------------------------------
# UI
# ---------------------------------------------------------------------------
BG, CARD, MUTED, TEXT = "#1c1c1c", "#2b2b2b", "#9a9a9a", "#e6e6e6"
SIDE, NAV_ON = "#141414", "#262b33"  # sidebar, selected page
# what the mode picker shows: mode -> (title, one line, icon in wiki/ui)
MODES = {"farm": ("Full farm", "Attacks + upgrades", "king"), "loot": ("Loot only", "Just attack", "gold"),
         "walls": ("Walls only", "Farm + buy walls", "wall"),
         "bb_loot": ("BB loot", "Builder Base attacks", "bgold"),
         "bb_farm": ("BB farm", "BB upgrades", "builderhall"),
         "bb_walls": ("BB walls", "Builder Base walls", "wall")}
GREEN, AMBER, RED, BLUE, GOLD, PINK = "#4cc38a", "#e5b454", "#ff6b6b", "#57a6ff", "#f5c542", "#d77bff"
LEVEL_COLORS = {"info": TEXT, "ok": GREEN, "warn": AMBER, "err": RED}
UI_SCALE = 1.0  # set from the real DPI at startup so the layout isn't tiny on 150-200% displays


def S(*v):
    r = tuple(int(round(x * UI_SCALE)) for x in v)
    return r if len(r) > 1 else r[0]



class DropLinePicker(tk.Toplevel):
    """Click to pin-point the troop drop line on a live screenshot. 1st click = start, 2nd = end, further clicks
    move whichever marker is nearer. Refresh grabs a new screenshot (e.g. once you're on the scouting screen)."""

    def __init__(self, app, frame, keys=("deploy_point", "deploy_line_end"), what="Troop"):
        super().__init__(app)
        self.app, self.keys, self.what = app, keys, what
        self.title(f"{what} drop line")
        self.configure(bg=BG)
        fp = app.cfg["fixed_points"]
        self.pts = [fp.get(keys[0]), fp.get(keys[1])]
        self.pts = [list(p) if p else None for p in self.pts]
        bar = ttk.Frame(self, padding=S(12, 10))
        bar.pack(fill="x")
        ttk.Label(bar, text="On the scouting screen: 'Zoom out + pan', then click where the line STARTS and ENDS "
                            "(grass outside the red border).").pack(side="left")
        ttk.Button(bar, text="Save", style="Accent.TButton", command=self.save).pack(side="right")
        ttk.Button(bar, text="Refresh screenshot", command=self.refresh).pack(side="right", padx=S(8))
        ttk.Button(bar, text="Zoom out + pan + refresh", command=self.pan).pack(side="right")
        ttk.Button(bar, text="Clear", command=self.clear).pack(side="right")
        self.info = ttk.Label(self, style="Muted.TLabel", padding=S(12, 0, 12, 6))
        self.info.pack(anchor="w")
        self.cv = tk.Canvas(self, highlightthickness=0, bg=BG, cursor="crosshair")
        self.cv.pack(padx=S(12), pady=S(0, 12))
        self.cv.bind("<Button-1>", self.click)
        self.bind("<Escape>", lambda e: self.destroy())
        self.show(frame)
        self.transient(app)
        self.focus_set()

    def show(self, frame):
        h, w = frame.shape[:2]
        self.scale = min(S(1200) / w, S(680) / h, 1.0)
        img = Image.fromarray(cv2.cvtColor(frame, cv2.COLOR_BGR2RGB)).resize(
            (int(w * self.scale), int(h * self.scale)), Image.LANCZOS)
        self.photo = ImageTk.PhotoImage(img)
        self.cv.config(width=img.width, height=img.height)
        self.draw()

    def draw(self):
        self.cv.delete("all")
        self.cv.create_image(0, 0, anchor="nw", image=self.photo)
        k = self.scale
        a, b = self.pts
        if a and b:
            for w, col in ((S(8), "black"), (S(4), "#ffd21f")):  # dark outline so it shows on grass
                self.cv.create_line(a[0] * k, a[1] * k, b[0] * k, b[1] * k, fill=col, width=w, capstyle="round")
        r = S(11)
        for p, label, col in ((a, "START", GREEN), (b, "END", BLUE)):
            if p:
                x, y = p[0] * k, p[1] * k
                self.cv.create_oval(x - r, y - r, x + r, y + r, outline="white", width=S(3), fill=col)
                for dx, dy, c in ((2, 2, "black"), (0, 0, "white")):
                    self.cv.create_text(x + r + 6 + dx, y - r - 6 + dy, text=label, fill=c, anchor="w",
                                        font=("Segoe UI", 12, "bold"))
        self.info.config(text=f"Start: {tuple(a) if a else '-'}     End: {tuple(b) if b else '- (one spot only)'}")

    def click(self, e):
        p = [int(e.x / self.scale), int(e.y / self.scale)]
        a, b = self.pts
        if not a:
            self.pts[0] = p
        elif not b:
            self.pts[1] = p
        else:  # move the nearer marker
            near = min((0, 1), key=lambda i: (self.pts[i][0] - p[0]) ** 2 + (self.pts[i][1] - p[1]) ** 2)
            self.pts[near] = p
        self.draw()

    def clear(self):
        self.pts = [None, None]
        self.draw()

    def refresh(self):
        self.app.with_screenshot(lambda f: self.winfo_exists() and self.show(f))

    def pan(self):
        """Pan exactly like the bot does before deploying, so the points are picked on the same view."""
        where = self.app.cfg.get("deploy_pan", "off")
        if where not in PAN_DIRS:
            return messagebox.showinfo("Pan", "Set 'Pan view before deploying' in Settings > Battle first.", parent=self)
        self.app.bg(lambda: (zoom_out(self.app.adb), pan_view(self.app.adb, where), time.sleep(0.6),
                             self.app.ui(self.refresh)))

    def save(self):
        a, b = self.pts
        if not a:
            return messagebox.showinfo("Drop line", "Click at least the start point.", parent=self)
        fp = self.app.cfg["fixed_points"]
        self.app.cfg["line_view"] = 2  # picked on the zoomed-out view the bot deploys on (v17+)
        fp[self.keys[0]] = a
        if b:
            fp[self.keys[1]] = b
        else:
            fp.pop(self.keys[1], None)
        save_config(self.app.cfg)
        self.app.log(f"{self.what} drop line saved: {tuple(a)} -> {tuple(b) if b else 'single spot'}.", "ok")
        self.app.refresh_setup()
        self.destroy()


PLAN_CATS = ("All", "Heroes", "Army", "Defences", "Guardians", "Traps", "Resources", "Other")


class PlannerTab(ttk.Frame):
    """Per-account upgrade planner: every upgrade the account has left (from its last scan) as a card with its picture,
    current level and the max for its Town Hall; click a level to queue it. The queue is this account's order."""

    def __init__(self, app, parent):
        super().__init__(parent)
        self.app, self.cfg = app, app.cfg
        self._img = {}
        top = ttk.Frame(self, padding=S(14, 12, 14, 6))
        top.pack(fill="x")
        ttk.Label(top, text="Account", style="CardTitle.TLabel").pack(side="left")
        self.acc = ttk.Combobox(top, state="readonly", width=16)
        self.acc.pack(side="left", padx=S(6, 14))
        self.acc.bind("<<ComboboxSelected>>", lambda e: self.refresh())
        self.base = tk.StringVar(value="home")
        for v, t in (("home", "Home village"), ("builder", "Builder Base")):
            ttk.Radiobutton(top, text=t, value=v, variable=self.base, command=self.refresh).pack(side="left",
                                                                                                padx=S(0, 8))
        ttk.Label(top, text="Hall level", style="CardTitle.TLabel").pack(side="left", padx=S(10, 4))
        self.hall = ttk.Spinbox(top, from_=1, to=18, width=4, command=self.set_hall)
        self.hall.pack(side="left")
        self.hall.bind("<Return>", lambda e: self.set_hall())
        ttk.Button(top, text="🔍  Scan the account in the game now", style="Accent.TButton",
                   command=self.scan).pack(side="right")
        self.info = ttk.Label(self, style="Sub.TLabel", padding=S(14, 0, 14, 6))
        self.info.pack(fill="x")

        body = ttk.Frame(self, padding=S(14, 0, 14, 14))
        body.pack(fill="both", expand=True)
        # left: this account's queue
        q = ttk.Frame(body, style="Card.TFrame", padding=S(10))
        q.pack(side="left", fill="y")
        self.qtitle = ttk.Label(q, style="CardTitle.TLabel")
        self.qtitle.pack(anchor="w")
        ttk.Label(q, text="Top = upgraded first. Done targets drop off\nby themselves.", style="Sub.TLabel").pack(
            anchor="w", pady=S(2, 6))
        self.qbox = self._scroller(q, S(290))
        ttk.Button(q, text="Clear this account's plan", command=self.clear).pack(anchor="w", pady=S(8, 0))
        # right: cards
        r = ttk.Frame(body)
        r.pack(side="left", fill="both", expand=True, padx=S(12, 0))
        bar = ttk.Frame(r)
        bar.pack(fill="x", pady=S(0, 6))
        self.cat = tk.StringVar(value="All")
        for c in PLAN_CATS:
            ttk.Radiobutton(bar, text=c, value=c, variable=self.cat, command=self.draw_cards).pack(
                side="left", padx=S(0, 6))
        self.search = ttk.Entry(bar, width=16)
        self.search.pack(side="right")
        self.search.bind("<KeyRelease>", lambda e: self.draw_cards())
        ttk.Label(bar, text="🔎", style="Sub.TLabel").pack(side="right")
        self.cards = self._scroller(r, None)
        self._rz = None
        self.cards.canvas.bind("<Configure>", self._resized, add="+")
        self.accounts()
        self.refresh()

    # --- helpers ---
    def _scroller(self, parent, width):
        wrap = ttk.Frame(parent)
        wrap.pack(fill="both", expand=True)
        cv = tk.Canvas(wrap, bg=CARD if width else BG, highlightthickness=0, **({"width": width} if width else {}))
        sb = ttk.Scrollbar(wrap, command=cv.yview)
        inner = ttk.Frame(cv, style="Card.TFrame" if width else "TFrame")
        inner.bind("<Configure>", lambda e: cv.configure(scrollregion=cv.bbox("all")))
        win = cv.create_window(0, 0, anchor="nw", window=inner)
        cv.bind("<Configure>", lambda e: cv.itemconfigure(win, width=e.width))
        cv.configure(yscrollcommand=sb.set)
        cv.pack(side="left", fill="both", expand=True)
        sb.pack(side="right", fill="y")
        wheel = lambda e: cv.yview_scroll(int(-e.delta / 120), "units")
        cv.bind("<Enter>", lambda e: cv.bind_all("<MouseWheel>", wheel))
        cv.bind("<Leave>", lambda e: cv.unbind_all("<MouseWheel>"))
        inner.canvas = cv
        return inner

    def icon(self, key, size):
        if (key, size) not in self._img:
            e = wiki_data().get(key) or {}
            try:
                im = Image.open(os.path.join(WIKI_DIR, e["icon"])).convert("RGBA")
                im.thumbnail((size, size))
                self._img[(key, size)] = ImageTk.PhotoImage(im)
            except Exception:
                self._img[(key, size)] = None
        return self._img[(key, size)]

    def accounts(self):
        names = sorted(set((self.cfg.get("scans") or {})) | set((self.cfg.get("plans") or {})) - {"?"})
        cur = getattr(getattr(self.app, "bot", None), "_last_name", None)
        self.acc["values"] = names
        pick = cur if cur in names else self.acc.get() if self.acc.get() in names else (names[0] if names else "")
        self.acc.set(pick)

    def scan_data(self):
        return ((self.cfg.get("scans") or {}).get(self.acc.get()) or {}).get(self.base.get()) or {}

    def plan(self):
        p = self.cfg.setdefault("plans", {}).setdefault(self.acc.get(), {})
        return p.setdefault(self.base.get(), [])

    def hall_level(self):
        sd = self.scan_data()
        if sd.get("hall"):
            return sd["hall"]
        # not on the list (maxed, or upgrading): at least what the list's next levels need
        reqs = [wiki_data()[r["key"]]["levels"][r["level"]]["req"] for r in sd.get("items", [])
                if r.get("key") and r.get("level") is not None and not r.get("upgrading")
                and r["level"] < len(wiki_data()[r["key"]]["levels"])
                and wiki_data()[r["key"]]["levels"][-1].get("hall") in ("town hall", "builder hall")]
        return max(reqs) if reqs else None

    def set_hall(self):
        try:
            v = int(self.hall.get())
        except ValueError:
            return
        sd = self.cfg.setdefault("scans", {}).setdefault(self.acc.get(), {}).setdefault(self.base.get(), {})
        sd["hall"] = v
        save_config(self.cfg)
        self.refresh()

    def groups(self):
        """{key: [(level, count), ...]} of what's left, from the scan (several levels per building possible)."""
        g = {}
        for r in self.scan_data().get("items", []):
            if r.get("key"):
                g.setdefault(r["key"], []).append((r.get("level"), r.get("count", 1), r.get("upgrading", False)))
        return g

    # --- drawing ---
    def refresh(self):
        if not self.winfo_exists():
            return
        self.accounts()
        sd, acc = self.scan_data(), self.acc.get()
        hall = self.hall_level()
        self.hall.set(hall or "")
        what = "Town Hall" if self.base.get() == "home" else "Builder Hall"
        if not acc:
            self.info.config(text="No account scanned yet - open the game on an account and click 'Scan the account"
                                  " in the game now' (farming also scans each account automatically).")
        elif not sd:
            self.info.config(text=f"{acc}: no {'Builder Base' if self.base.get() == 'builder' else 'home'} scan yet"
                                  " - click Scan while that village is showing in the game.")
        else:
            d = sd.get("discount", 1)
            secs, n, builders = time_to_max(sd, self.base.get())
            left = (f" · {n} upgrades to max this hall: {secs / 86400:,.0f} builder-days ≈ "
                    f"{secs / 86400 / builders:,.0f} days with {builders} builders" if n else " · ✓ everything max")
            self.info.config(text=f"{acc} · {what} {hall or '?'}{left} · scanned {sd.get('time', '?')}"
                                  + (" · exact levels from the game's data export" if sd.get("source") == "export"
                                     else "")
                                  + (f" · prices were {round((1 - d) * 100)}% off (Hammer Jam / Gold Pass) - "
                                     "levels worked out with that" if d < 1 else ""))
        self.qtitle.config(text=f"Upgrade order - {acc or 'no account'}")
        self.build_cards()
        self.draw_queue()

    # plain tk widgets inside the lists: themed ttk ones made each redraw take seconds
    def _lbl(self, parent, text="", bold=False, muted=False, size=10, **kw):
        return tk.Label(parent, text=text, bg=kw.pop("bg", CARD), fg=MUTED if muted else TEXT, anchor="w",
                        font=("Segoe UI", size, "bold" if bold else "normal"), justify="left", **kw)

    def _chip(self, parent, text, cmd):
        c = tk.Label(parent, text=text, bg="#3a3a3a", fg=TEXT, font=("Segoe UI", 9, "bold"), padx=S(7), pady=S(3),
                     cursor="hand2")
        c.bind("<Button-1>", lambda e: cmd())
        return c

    def draw_queue(self):
        for w in self.qbox.winfo_children():
            w.destroy()
        plan, g = self.plan(), self.groups()
        if not plan:
            self._lbl(self.qbox, "Nothing queued yet.\nClick a level on a building →", muted=True).pack(
                anchor="w", pady=S(6))
        for i, it in enumerate(plan):
            e = wiki_data().get(it["key"], {})
            left = sum(c for lv, c, up in g.get(it["key"], []) if lv is not None and lv < it["to"] and not up)
            row = tk.Frame(self.qbox, bg=CARD, pady=S(3))
            row.pack(fill="x")
            self._lbl(row, f"{i + 1}.", muted=True, width=3).pack(side="left")
            ic = self.icon(it["key"], S(34))
            if ic:
                tk.Label(row, image=ic, bg=CARD).pack(side="left")
            txt = tk.Frame(row, bg=CARD)
            txt.pack(side="left", fill="x", expand=True, padx=S(6, 0))
            self._lbl(txt, f"{e.get('name', it['key'])} → {it['to']}", bold=True).pack(anchor="w")
            self._lbl(txt, f"{left} to upgrade" if left else "✓ reached (or upgrading)", muted=True,
                      size=9).pack(anchor="w")
            for sym, cmd in (("✕", lambda i=i: self.remove(i)), ("▼", lambda i=i: self.move(i, 1)),
                             ("▲", lambda i=i: self.move(i, -1))):
                self._chip(row, sym, cmd).pack(side="right", padx=S(1))

    def build_cards(self):
        """One card per building this account can still upgrade - built once per account / village / scan."""
        g, hall = self.groups(), self.hall_level()
        hero_hall = self.scan_data().get("hero_hall")
        sig = (self.acc.get(), self.base.get(), self.scan_data().get("time"), hall, hero_hall,
               tuple(sorted((k, tuple(v)) for k, v in g.items())))
        if sig == getattr(self, "_sig", None):
            return self.draw_cards()
        self._sig = sig
        for w in self.cards.winfo_children():
            w.destroy()
        self._cards = {}
        self._empty = self._lbl(self.cards, "Nothing to show - scan the account first (or change the filter).",
                                muted=True, bg=BG)
        self.update_idletasks()
        avail = self.cards.canvas.winfo_width()
        self._ncols = 3 if avail >= S(1000) or avail <= 100 else 2  # 2 columns when the window is narrower
        for c in range(3):
            self.cards.columnconfigure(c, weight=1 if c < self._ncols else 0, uniform="card" if c < self._ncols else "")
        self._card_w = self._col_width(avail)  # chips wrap inside it
        for k in g:
            if k == "home:wall":
                continue  # bought with gold/elixir, not builders: the dashboard's Walls card
            e = wiki_data()[k]
            levels = sorted(((lv, c, up) for lv, c, up in g[k] if lv is not None), key=lambda x: x[0])
            cur = min((lv for lv, c, up in levels), default=None)
            mx = max_level(k, hall, hero_hall)
            have = ", ".join(("not built yet" if lv == 0 else f"lvl {lv}") + (f" ×{c}" if c > 1 else "")
                             + (" ⏳" if up else "") for lv, c, up in levels) or "level unknown"
            self._cards[k] = self._card(k, e, have, cur, mx)
        self.draw_cards()

    def draw_cards(self):
        """Filter / search: just show or hide the cards already built."""
        cards = getattr(self, "_cards", {})
        for c in cards.values():
            c["frame"].grid_remove()
        self._empty.grid_remove()
        cat, q = self.cat.get().lower(), self.search.get().strip().lower()
        order = [c.lower() for c in PLAN_CATS[1:]]
        keys = sorted((k for k, c in cards.items() if (cat == "all" or c["cat"] == cat) and (not q or q in c["name"])),
                      key=lambda k: (order.index(cards[k]["cat"]) if cards[k]["cat"] in order else 99,
                                     cards[k]["name"]))
        for n, k in enumerate(keys):
            cards[k]["frame"].grid(row=n // self._ncols, column=n % self._ncols, sticky="nsew", padx=S(4), pady=S(4))
        if not keys:
            self._empty.grid(row=0, column=0, columnspan=3, sticky="w", pady=S(10))
        self.update_chips()
        self.cards.canvas.yview_moveto(0)

    def _col_width(self, avail):
        cols = 3 if avail >= S(1000) or avail <= 100 else 2
        return max(S(220), avail // cols - S(12)) if avail > 100 else S(300)

    def _resized(self, e):
        """Window resized (or first laid out): rebuild the cards at the new column width, once it settles."""
        if abs(self._col_width(e.width) - getattr(self, "_card_w", 0)) > S(8):
            if self._rz:
                self.after_cancel(self._rz)
            self._rz = self.after(200, lambda: (setattr(self, "_sig", None), self.build_cards()))

    def _card(self, k, e, have, cur, mx):
        """One card = ONE canvas (icon, text and level chips are canvas items): a widget per label made the
        window take seconds to show 50 cards."""
        cv = tk.Canvas(self.cards, bg=CARD, highlightthickness=0, width=self._card_w, height=S(10))
        pad, right = S(10), self._card_w - S(10)
        ic = self.icon(k, S(56))
        if ic:
            cv.create_image(pad, pad, image=ic, anchor="nw")
        tx = pad + S(64)
        y = cv.bbox(cv.create_text(tx, pad, text=e["name"], anchor="nw", fill=TEXT,
                                   font=("Segoe UI", 11, "bold"), width=right - tx))[3]
        y = cv.bbox(cv.create_text(tx, y + S(2), text=have, anchor="nw", fill=MUTED, font=("Segoe UI", 9),
                                   width=right - tx))[3]
        if mx:
            y = cv.bbox(cv.create_text(tx, y + S(2), text=f"max {mx} at this hall", anchor="nw", fill=MUTED,
                                       font=("Segoe UI", 9)))[3]
        y = max(y, pad + S(56)) + S(8)
        info = {"frame": cv, "chips": [], "x": None, "name": e["name"].lower(), "cat": category_of(k.split(":", 1)[1])}
        if cur is None or mx is None or cur >= mx:
            y = cv.bbox(cv.create_text(pad, y, anchor="nw", fill=MUTED, font=("Segoe UI", 9), text=(
                "✓ maxed for this hall" if cur is not None and mx and cur >= mx else "(level couldn't be read)")))[3]
            cv.configure(height=y + pad)
            return info
        x, row = [pad], [0]

        def chip(text, cmd, line):
            line = max(line, row[0])  # stay on the row an earlier chip wrapped to
            t = cv.create_text(x[0] + S(7), line + S(3), text=text, anchor="nw", fill=TEXT,
                               font=("Segoe UI", 9, "bold"))
            x0, y0, x1, y1 = cv.bbox(t)
            if x1 + S(7) > right and x[0] > pad + S(60):  # no room left on this row: wrap under it
                cv.move(t, pad - x[0], y1 - y0 + S(12))
                row[0] = line + y1 - y0 + S(12)
                x0, y0, x1, y1 = cv.bbox(t)
            r = cv.create_rectangle(x0 - S(7), y0 - S(3), x1 + S(7), y1 + S(3), fill="#3a3a3a", width=0)
            cv.tag_lower(r, t)
            for item in (t, r):
                cv.tag_bind(item, "<Button-1>", lambda ev: cmd())
                cv.tag_bind(item, "<Enter>", lambda ev: cv.configure(cursor="hand2"))
                cv.tag_bind(item, "<Leave>", lambda ev: cv.configure(cursor=""))
            x[0] = x1 + S(11)
            return r, t
        line = y
        x[0] = cv.bbox(cv.create_text(pad, line + S(3), text="Up to:", anchor="nw", fill=MUTED,
                                      font=("Segoe UI", 9)))[2] + S(6)
        targets = list(range(cur + 1, mx + 1))
        many = len(targets) > 6  # heroes have dozens of levels: next few + max, plus a picker for any level
        if many:
            targets = targets[:4] + [mx]
        for lv in targets:
            info["chips"].append((lv, chip(("MAX " if lv == mx else "") + str(lv), lambda lv=lv: self.add(k, lv),
                                           line)))
        info["x"] = chip("✕", lambda: self.remove_key(k), line)
        y = cv.bbox("all")[3] + S(8)
        if many:
            x[0] = cv.bbox(cv.create_text(pad, y + S(3), text="or level", anchor="nw", fill=MUTED,
                                          font=("Segoe UI", 9)))[2] + S(6)
            sp = tk.Spinbox(cv, from_=cur + 1, to=mx, width=5, bg="#3a3a3a", fg=TEXT, buttonbackground=CARD,
                            relief="flat", insertbackground=TEXT)
            x[0] = cv.bbox(cv.create_window(x[0], y, window=sp, anchor="nw"))[2] + S(6)
            chip("Set", lambda: self.add(k, min(mx, max(cur + 1, int(sp.get())))) if sp.get().isdigit() else None, y)
            y = cv.bbox("all")[3] + S(4)
        cv.configure(height=y + pad)
        return info

    def update_chips(self, keys=None):
        """Highlight the chosen target levels (only the cards that changed)."""
        want = {it["key"]: it["to"] for it in self.plan()}
        cards = getattr(self, "_cards", {})
        for k in (keys if keys is not None else cards):
            c = cards.get(k)
            if not c:
                continue
            for lv, (r, t) in c["chips"]:
                on = want.get(k, 0) >= lv
                c["frame"].itemconfigure(r, fill=BLUE if on else "#3a3a3a")
                c["frame"].itemconfigure(t, fill="#0b1a2b" if on else TEXT)
            if c["x"] is not None:
                for item in c["x"]:
                    c["frame"].itemconfigure(item, state="normal" if k in want else "hidden")

    # --- editing (saved straight away; the bot reads it on its next builder check) ---
    def add(self, key, to):
        plan = self.plan()
        it = next((x for x in plan if x["key"] == key), None)
        if it:
            it["to"] = to
        else:
            plan.append({"key": key, "to": to})
        self.save([key])

    def remove(self, i):
        plan = self.plan()
        if 0 <= i < len(plan):
            key = plan.pop(i)["key"]
            self.save([key])

    def remove_key(self, key):
        plan = self.plan()
        plan[:] = [x for x in plan if x["key"] != key]
        self.save([key])

    def move(self, i, d):
        plan = self.plan()
        if 0 <= i + d < len(plan):
            plan[i], plan[i + d] = plan[i + d], plan[i]
            self.save([])

    def clear(self):
        if self.plan() and messagebox.askyesno("Clear", f"Remove every target for {self.acc.get()} "
                                                        f"({'Builder Base' if self.base.get() == 'builder' else 'home'})?",
                                               parent=self):
            self.plan().clear()
            self.save(None)

    def save(self, keys=None):
        save_config(self.cfg)
        self.draw_queue()
        self.update_chips(keys)

    def scan(self):
        if self.app.thread:
            return messagebox.showinfo("Scan", "Farming is running - the bot scans each account by itself whenever "
                                               "it checks the builders. Stop farming to scan right now.", parent=self)
        self.info.config(text="Scanning - reading the builder list in the game…")

        def work():
            try:
                acc, kind = Bot(self.cfg, self.app.adb, self.app.emit).scan_now()
            except Exception as e:
                msg = f"Scan failed: {e}"
                return self.app.ui(lambda: self.info.config(text=msg))

            def done():
                if self.winfo_exists():
                    self.accounts()
                    self.acc.set(acc)
                    self.base.set("builder" if kind.startswith("bb_") else "home")
                    self.refresh()
            self.app.ui(done)
        self.app.bg(work)


class CaptureWindow(tk.Toplevel):
    """Shows a screenshot; drag a box. Calls on_done(crop, center, bbox) in full-res coords."""

    def __init__(self, parent, frame, prompt, on_done):
        super().__init__(parent)
        self.title("Capture")
        self.configure(bg=BG)
        self.frame, self.on_done = frame, on_done
        h, w = frame.shape[:2]
        self.scale = min(S(1200) / w, S(680) / h, 1.0)
        ttk.Label(self, text=prompt + "   (Esc to cancel)", padding=S(12, 10)).pack(anchor="w")
        img = Image.fromarray(cv2.cvtColor(frame, cv2.COLOR_BGR2RGB)).resize(
            (int(w * self.scale), int(h * self.scale)), Image.LANCZOS)
        self.photo = ImageTk.PhotoImage(img)
        self.cv = tk.Canvas(self, width=img.width, height=img.height, cursor="crosshair",
                            highlightthickness=0, bg=BG)
        self.cv.pack(padx=S(12), pady=S(0, 12))
        self.cv.create_image(0, 0, anchor="nw", image=self.photo)
        self.start, self.rect = None, None
        self.cv.bind("<ButtonPress-1>", self._press)
        self.cv.bind("<B1-Motion>", self._drag)
        self.cv.bind("<ButtonRelease-1>", self._release)
        self.bind("<Escape>", lambda e: self.destroy())
        self.transient(parent)
        self.grab_set()
        self.focus_set()

    def _press(self, e):
        self.start = (e.x, e.y)
        if self.rect:
            self.cv.delete(self.rect)
        self.rect = self.cv.create_rectangle(e.x, e.y, e.x, e.y, outline=GREEN, width=2)

    def _drag(self, e):
        if self.start:
            self.cv.coords(self.rect, *self.start, e.x, e.y)

    def _release(self, e):
        if not self.start:
            return
        (x0, x1), (y0, y1) = sorted((self.start[0], e.x)), sorted((self.start[1], e.y))
        self.destroy()
        if x1 - x0 < 4 or y1 - y0 < 4:
            return
        b = [int(v / self.scale) for v in (x0, y0, x1, y1)]
        self.on_done(self.frame[b[1]:b[3], b[0]:b[2]].copy(), ((b[0] + b[2]) // 2, (b[1] + b[3]) // 2), b)


class App(tk.Tk):
    def __init__(self):
        super().__init__()
        global UI_SCALE
        UI_SCALE = self.winfo_fpixels("1i") / 96
        self.title("Loot Farmer")
        try:  # the King on the title bar + taskbar (same as the Start menu / desktop shortcut)
            self.iconbitmap(default=os.path.join(WIKI_DIR, "ui", "app.ico"))
        except tk.TclError:
            pass
        sw, sh = self.winfo_screenwidth(), self.winfo_screenheight()
        self.geometry(f"{min(S(1240), int(sw * .92))}x{min(S(800), int(sh * .85))}+{int(sw * .04)}+{int(sh * .03)}")
        self.minsize(min(S(1060), int(sw * .8)), min(S(680), int(sh * .7)))
        sv_ttk.set_theme("dark")
        for name in tkfont.names(self):  # the theme sizes fonts in pixels; scale them for high-DPI screens
            f = tkfont.nametofont(name, self)
            if name.startswith("SunValley") and f.cget("size") < 0:
                f.configure(size=int(f.cget("size") * UI_SCALE))
        self.configure(bg=BG)
        self.cfg, warn = load_config()
        self.adb = ADB(self.cfg["adb_path"], self.cfg["device"])
        self.q = queue.Queue()
        self.bot = self.thread = None
        self.started_at = None
        self.vision = Vision()
        self.recent = collections.deque(maxlen=10)
        self.phone, self.tunnel, self.public_url = None, None, ""
        self._resume = None  # (when, mode): start again then - a pause / mode switch from the phone
        if not self.cfg["phone_view_key"]:
            self.cfg["phone_view_key"] = secrets.token_urlsafe(9)
            save_config(self.cfg)
        if self.cfg["phone_view_enabled"]:
            key, port = self.cfg["phone_view_key"], self.cfg["phone_view_port"]
            try:
                self.phone = PhoneView(port, key, lambda cmd: self.emit("phone_cmd", cmd))
                exe = os.path.join(BASE_DIR, "cloudflared.exe")
                if self.cfg["public_link_enabled"] and os.path.isfile(exe):
                    self.tunnel = Tunnel(exe, port, lambda url: self.ui(lambda: self._public_url(url)))
                else:
                    Tunnel.kill_saved()
            except OSError as e:
                warn = f"Phone view couldn't start on port {self.cfg['phone_view_port']} ({e})."
        self._styles()
        self._build()
        self.refresh_setup()
        self.after(100, self._pump)
        self.protocol("WM_DELETE_WINDOW", self._close)
        if warn:
            self.log(warn, "warn")
        self.bg(self._initial_connect)
        if self.phone:
            threading.Thread(target=self._idle_frames, daemon=True).start()
        if self.cfg.get("shortcuts_v") != APP_VERSION:  # after an update: shortcuts get the King icon
            def shortcuts():
                if fix_shortcuts():
                    self.cfg["shortcuts_v"] = APP_VERSION
                    save_config(self.cfg)
            self.bg(shortcuts)
        self.after(3000, self._update_tick)

    # --- helpers ---
    def emit(self, kind, data):
        self.q.put((kind, data))

    def bg(self, fn, *a):
        """Run fn on a worker thread; exceptions go to the log instead of freezing the UI."""
        def wrap():
            try:
                fn(*a)
            except Exception as e:
                self.emit("log", ("err", f"{getattr(fn, '__name__', 'task')}: {e}"))
        threading.Thread(target=wrap, daemon=True).start()

    def ui(self, fn):
        self.q.put(("call", fn))

    def log(self, msg, level="info"):
        getattr(log_file, {"ok": "info", "warn": "warning", "err": "error"}.get(level, "info"))(msg)  # in reports too
        self.emit("log", (level, msg))

    def _styles(self):
        s = ttk.Style(self)
        f = "Segoe UI Variable Display" if "Segoe UI Variable Display" in self.tk.call("font", "families") else "Segoe UI"
        self._font = f
        s.layout("Hidden.TNotebook.Tab", [])  # pages switch from the sidebar, not a tab row
        s.configure("Hidden.TNotebook", borderwidth=0)
        s.configure("Title.TLabel", font=(f, 20, "bold"))
        s.configure("Sub.TLabel", font=("Segoe UI", 10), foreground=MUTED)
        s.configure("CardTitle.TLabel", font=("Segoe UI", 9, "bold"), foreground=MUTED)
        s.configure("CardValue.TLabel", font=(f, 22, "bold"))
        s.configure("Big.TLabel", font=(f, 15, "bold"))
        s.configure("Res.TLabel", font=(f, 17, "bold"))
        s.configure("Muted.TLabel", foreground=MUTED)
        s.configure("Pill.TLabel", font=("Segoe UI", 10, "bold"))
        s.configure("Start.Accent.TButton", font=("Segoe UI", 11, "bold"), padding=S(22, 9))
        s.configure("Treeview", rowheight=S(30))

    def card(self, parent, title, **grid):
        f = ttk.Frame(parent, style="Card.TFrame", padding=S(16, 12, 16, 14))
        f.grid(**grid, sticky="nsew")
        if title:
            ttk.Label(f, text=title.upper(), style="CardTitle.TLabel").pack(anchor="w", pady=S(0, 6))
        return f

    def text_widget(self, parent, height):
        t = tk.Text(parent, height=height, bg="#141414", fg=TEXT, insertbackground=TEXT, relief="flat",
                    font=("Cascadia Mono", 9) if "Cascadia Mono" in self.tk.call("font", "families")
                    else ("Consolas", 9), padx=S(10), pady=S(8), wrap="word", borderwidth=0, highlightthickness=0)
        for lvl, col in LEVEL_COLORS.items():
            t.tag_configure(lvl, foreground=col)
        t.tag_configure("ts", foreground="#6b6b6b")
        t.configure(state="disabled")
        return t

    # --- layout ---
    # --- layout ---
    def ui_icon(self, name, size):
        """A Clash icon from wiki/ui/ (from the wiki) at that height, cached; None if missing."""
        cache = self.__dict__.setdefault("_ui_icons", {})
        if (name, size) not in cache:
            try:
                im = Image.open(os.path.join(WIKI_DIR, "ui", f"{name}.png")).convert("RGBA")
                im = im.resize((max(1, round(im.width * size / im.height)), size), Image.LANCZOS)
                cache[(name, size)] = ImageTk.PhotoImage(im)
            except Exception:
                cache[(name, size)] = None
        return cache[(name, size)]

    def _build(self):
        """Sidebar (navigation + connection + links) | main area: mode picker + Start, then the page."""
        side = tk.Frame(self, bg=SIDE, width=S(236))
        side.pack(side="left", fill="y")
        side.pack_propagate(False)
        logo = tk.Frame(side, bg=SIDE)
        logo.pack(fill="x", padx=S(16), pady=S(18, 14))
        tk.Label(logo, image=self.ui_icon("king", S(44)), bg=SIDE).pack(side="left")
        lt = tk.Frame(logo, bg=SIDE)
        lt.pack(side="left", padx=S(10, 0))
        tk.Label(lt, text="Loot Farmer", bg=SIDE, fg=TEXT, font=(self._font, 15, "bold")).pack(anchor="w")
        tk.Label(lt, text=f"version {APP_VERSION}", bg=SIDE, fg=MUTED, font=("Segoe UI", 9)).pack(anchor="w")

        self.nav = {}
        for page, label, icon in (("Dashboard", "Dashboard", "trophy"), ("Upgrade planner", "Upgrade planner", "builder"),
                                  ("Setup", "Setup", "hammer"), ("Settings", "Settings", "lab"),
                                  ("Log", "Activity log", "xp")):
            row = tk.Frame(side, bg=SIDE, cursor="hand2", padx=S(12), pady=S(7))
            row.pack(fill="x", padx=S(8), pady=S(1))
            ic = tk.Label(row, image=self.ui_icon(icon, S(26)), bg=SIDE, width=S(30))
            ic.pack(side="left")
            tx = tk.Label(row, text=label, bg=SIDE, fg=TEXT, font=("Segoe UI", 11), anchor="w")
            tx.pack(side="left", padx=S(10, 0))
            for w in (row, ic, tx):
                w.bind("<Button-1>", lambda e, p=page: self.nb.select(self.tabs[p]))
            self.nav[page] = (row, ic, tx)

        foot = tk.Frame(side, bg=SIDE)
        foot.pack(side="bottom", fill="x", padx=S(16), pady=S(14))
        self.update_btn = ttk.Button(foot, text="⬆  Update available", style="Accent.TButton", command=self.do_update)
        self._update = None  # shown only when GitHub has a newer version

        def link(text, cmd, color=BLUE):
            lb = tk.Label(foot, text=text, bg=SIDE, fg=color, font=("Segoe UI", 9), cursor="hand2", anchor="w")
            lb.pack(fill="x", pady=S(1))
            lb.bind("<Button-1>", lambda e: cmd())
            return lb
        if self.phone:
            self.public_label = link("🌍  Anywhere link: starting…" if self.tunnel else "🌍  Anywhere link: off",
                                     lambda: self.public_url and self._copy(self.public_url, "Anywhere link"),
                                     BLUE if self.tunnel else MUTED)
        link("🐞  Send debug report", lambda: self.send_report("sent by hand"))
        link("🕘  Switch version", self.pick_version)
        link("⟳  Restart the app", self.restart_app)
        tk.Frame(foot, bg="#2a2a2a", height=1).pack(fill="x", pady=S(10))
        conn = tk.Frame(foot, bg=SIDE)
        conn.pack(fill="x")
        self.pill = tk.Label(conn, text="●  Connecting…", bg=SIDE, fg=AMBER, font=("Segoe UI", 10, "bold"))
        self.pill.pack(side="left")
        self.batt_label = tk.Label(conn, text="", bg=SIDE, fg=MUTED, font=("Segoe UI", 10, "bold"))
        self.batt_label.pack(side="right")
        self._batt_t, self._batt_warned = 0.0, False
        dev = tk.Frame(foot, bg=SIDE)
        dev.pack(fill="x", pady=S(6, 0))
        self.dev_combo = ttk.Combobox(dev, width=16, state="readonly")
        self.dev_combo.pack(side="left", fill="x", expand=True)
        self.dev_combo.bind("<<ComboboxSelected>>", self._device_chosen)
        ttk.Button(dev, text="↻", width=3, command=lambda: self.bg(self._initial_connect)).pack(side="left",
                                                                                             padx=S(6, 0))

        main = ttk.Frame(self)
        main.pack(side="left", fill="both", expand=True)
        top = ttk.Frame(main, padding=S(20, 16, 20, 4))
        top.pack(fill="x")
        self.start_btn = ttk.Button(top, text="▶  Start", style="Start.Accent.TButton", width=12,
                                    command=lambda: self.toggle(self.mode_var.get()))
        self.start_btn.pack(side="right", fill="y", padx=S(14, 0))
        modes = tk.Frame(top, bg=BG)
        modes.pack(side="left", fill="x", expand=True)
        self.mode_var = tk.StringVar(value=self.cfg.get("ui_mode") if self.cfg.get("ui_mode") in MODES else "farm")
        self.mode_cards = {}
        for i, (m, (title, sub, icon)) in enumerate(MODES.items()):
            modes.columnconfigure(i, weight=1, uniform="m")
            card = tk.Frame(modes, bg=CARD, cursor="hand2", padx=S(6), pady=S(6), highlightthickness=S(2),
                            highlightbackground=CARD, highlightcolor=CARD)
            card.grid(row=0, column=i, sticky="nsew", padx=S(0 if i == 0 else 8, 0))
            ic = tk.Label(card, image=self.ui_icon(icon, S(32)), bg=CARD)
            ic.pack()
            t = tk.Frame(card, bg=CARD)
            t.pack(fill="x")
            l1 = tk.Label(t, text=title, bg=CARD, fg=TEXT, font=("Segoe UI", 10, "bold"))
            l1.pack()
            l2 = tk.Label(t, text=sub, bg=CARD, fg=MUTED, font=("Segoe UI", 8))
            l2.pack()
            for w in (card, ic, t, l1, l2):
                w.bind("<Button-1>", lambda e, m=m: self.pick_mode(m))
            self.mode_cards[m] = card
        self.pick_mode(self.mode_var.get(), save=False)

        nb = self.nb = ttk.Notebook(main, style="Hidden.TNotebook")  # pages; the sidebar is the tab row
        nb.pack(fill="both", expand=True, padx=S(20), pady=S(8, 16))
        self.tabs = tabs = {}
        for name in ("Dashboard", "Upgrade planner", "Setup", "Settings", "Log"):
            tabs[name] = ttk.Frame(nb, padding=S(4) if name != "Upgrade planner" else 0)
            nb.add(tabs[name], text=name)
        self.planner_tab, self.planner = tabs["Upgrade planner"], None
        nb.bind("<<NotebookTabChanged>>", self._tab_changed)
        self._build_dashboard(tabs["Dashboard"])
        self._build_setup(tabs["Setup"])
        self._build_settings(tabs["Settings"])
        self._build_log(tabs["Log"])

    def pick_mode(self, m, save=True):
        if self.thread:  # can't change mode while running
            return
        self.mode_var.set(m)
        for k, card in self.mode_cards.items():
            on = k == m
            card.config(highlightbackground=BLUE if on else CARD, highlightcolor=BLUE if on else CARD)
        self.start_btn.config(text="▶  Start")
        if save and self.cfg.get("ui_mode") != m:
            self.cfg["ui_mode"] = m
            save_config(self.cfg)

    def _build_dashboard(self, tab):
        tab.columnconfigure(0, weight=3)
        tab.columnconfigure(1, weight=2)
        tab.rowconfigure(1, weight=1, minsize=S(200))  # the live view never gets squeezed out
        stats = ttk.Frame(tab)
        stats.grid(row=0, column=0, columnspan=2, sticky="ew", pady=S(0, 10))
        self.stat_labels = {}
        for i, (key, title, icon) in enumerate([("runtime", "Runtime", None), ("attacks", "Attacks", "king"),
                                                ("skipped", "Skipped", "shield"), ("walls", "Walls", "wall"),
                                                ("upgrades", "Upgrades", "hammer"), ("switches", "Switches", "builder_icon"),
                                                ("recoveries", "Restarts", "battlemachine"), ("errors", "Errors", None)]):
            stats.columnconfigure(i, weight=1, uniform="s")
            c = tk.Frame(stats, bg=CARD, padx=S(12), pady=S(8))
            c.grid(row=0, column=i, sticky="nsew", padx=S(0 if i == 0 else 6, 0))
            t = c
            hd = tk.Frame(c, bg=CARD)
            hd.pack(anchor="w")
            if icon:
                tk.Label(hd, image=self.ui_icon(icon, S(20)), bg=CARD).pack(side="left", padx=S(0, 5))
            tk.Label(hd, text=title.upper(), bg=CARD, fg=MUTED, font=("Segoe UI", 8, "bold")).pack(side="left")
            self.stat_labels[key] = tk.Label(t, text="0" if key != "runtime" else "—", bg=CARD, fg=TEXT,
                                             font=(self._font, 17, "bold"))
            self.stat_labels[key].pack(anchor="w")

        live = self.card(tab, "Live view", row=1, column=0, padx=S(0, 6))
        top = ttk.Frame(live, style="Card.TFrame")
        top.pack(fill="x", pady=S(0, 8))
        self.state_label = ttk.Label(top, text="Idle", style="Big.TLabel", foreground=MUTED)
        self.state_label.pack(side="left")
        self.bb_var = tk.BooleanVar(value=bool(self.cfg["builder_base_enabled"]))

        def bb_toggled():
            self.cfg["builder_base_enabled"] = self.bb_var.get()  # the running bot shares this dict: live
            if "builder_base_enabled" in getattr(self, "svars", {}):
                self.svars["builder_base_enabled"][0].set(self.bb_var.get())
            save_config(self.cfg)
            self.log("Builder Base " + ("on: each account gets a visit (collect, cart, upgrades, daily stars)."
                                        if self.bb_var.get() else "off."), "ok")
        ttk.Checkbutton(top, text="Full farm visits the Builder Base", variable=self.bb_var, command=bb_toggled,
                        style="Switch.TCheckbutton").pack(side="right")
        self.preview = tk.Canvas(live, bg="#141414", highlightthickness=0, height=S(240))
        self.preview.pack(fill="both", expand=True)
        self.preview.create_text(10, 10, anchor="nw", text="The emulator screen appears here while farming.",
                                 fill=MUTED, font=("Segoe UI", 10), tags="hint")
        self._photo = None

        side = ttk.Frame(tab)
        side.grid(row=1, column=1, sticky="nsew", padx=S(6, 0))
        side.columnconfigure(0, weight=1)
        side.rowconfigure(1, weight=1)
        res = self.card(side, "Your storage", row=0, column=0, pady=S(0, 12))
        self.res_card_title = res.winfo_children()[0]
        grid = tk.Frame(res, bg=CARD)
        grid.pack(fill="x")
        self.res_labels, self.res_icons = {}, {}
        for i, (key, col, icon) in enumerate([("s_gold", GOLD, "gold"), ("s_elixir", PINK, "elixir")]):
            grid.columnconfigure(i, weight=1, uniform="r")
            cell = tk.Frame(grid, bg=CARD)
            cell.grid(row=0, column=i, sticky="w")
            self.res_icons[key[2:]] = tk.Label(cell, image=self.ui_icon(icon, S(32)), bg=CARD)
            self.res_icons[key[2:]].pack(side="left", padx=S(0, 8))
            self.res_labels[key] = tk.Label(cell, text="—", bg=CARD, fg=col, font=(self._font, 16, "bold"))
            self.res_labels[key].pack(side="left")
        lc = self.card(side, "This session", row=1, column=0)
        rates = tk.Frame(lc, bg=CARD)
        rates.pack(fill="x")
        self.rate_labels, self.rate_icons, self.rate_cells, self.bb_view = {}, {}, {}, False
        for i, (key, col, icon) in enumerate([("gold", GOLD, "gold"), ("elixir", PINK, "elixir"),
                                              ("dark", "#b9a3ff", "dark")]):
            rates.columnconfigure(i, weight=1, uniform="rt")
            cell = self.rate_cells[key] = tk.Frame(rates, bg="#232323", padx=S(10), pady=S(8))
            cell.grid(row=0, column=i, sticky="nsew", padx=S(0 if i == 0 else 6, 0))
            self.rate_icons[key] = tk.Label(cell, image=self.ui_icon(icon, S(30)), bg="#232323")
            self.rate_icons[key].pack(side="left", padx=S(0, 8))
            t = tk.Frame(cell, bg="#232323")
            t.pack(side="left")
            per = tk.Label(t, text="—", bg="#232323", fg=col, font=(self._font, 15, "bold"))
            per.pack(anchor="w")
            tot = tk.Label(t, text="per hour", bg="#232323", fg=MUTED, font=("Segoe UI", 9))
            tot.pack(anchor="w")
            self.rate_labels[key] = (per, tot)
        self.acc_box = tk.Frame(lc, bg=CARD)  # one line per account
        self.acc_box.pack(fill="both", expand=True, pady=S(10, 0))
        self.render_loot()
        wc = self.card(tab, "Walls", row=2, column=0, padx=S(0, 6), pady=S(12, 0))
        self.walls_cv = tk.Canvas(wc, bg=CARD, highlightthickness=0, height=S(40))
        self.walls_cv.pack(fill="x")
        self.walls_cv.bind("<Configure>", lambda e: self.render_walls())
        act = self.card(tab, "Activity", row=2, column=1, padx=S(6, 0), pady=S(12, 0))
        self.mini_log = self.text_widget(act, 5)
        self.mini_log.pack(fill="both", expand=True)

    def _tree(self, parent, cols, widths, height):
        t = ttk.Treeview(parent, columns=cols, show="headings", height=height, selectmode="browse")
        for c, w in zip(cols, widths):
            t.heading(c, text=c)
            t.column(c, width=S(w), anchor="w", stretch=c == cols[0])
        t.tag_configure("ok", foreground=GREEN)
        t.tag_configure("missing", foreground=RED)
        t.tag_configure("optional", foreground=MUTED)
        return t

    def _build_setup(self, tab):
        tab.columnconfigure(0, weight=1)
        tab.columnconfigure(1, weight=1)
        tab.rowconfigure(1, weight=1)
        bar = ttk.Frame(tab)
        bar.grid(row=0, column=0, columnspan=2, sticky="ew", pady=S(0, 10))
        ttk.Label(bar, text="Put the game on the right screen, select a row, then Capture.",
                  style="Muted.TLabel").pack(side="left")
        ttk.Button(bar, text="Run setup check", style="Accent.TButton",
                   command=lambda: self.bg(self.setup_check)).pack(side="right")
        tools = ttk.Menubutton(bar, text="🧰  Tools")
        menu = tk.Menu(tools, tearoff=False)
        for label, cmd in (("Preview the emulator screen", self.preview_screen),
                           ("Read the troop bar (start a search first)", self.read_bar),
                           ("Test: builder upgrade", lambda: self.test_upgrade("builder")),
                           ("Test: lab research", lambda: self.test_upgrade("lab")),
                           ("Test: buy a wall with gold", lambda: self.test_wall("gold")),
                           ("Test: buy a wall with elixir", lambda: self.test_wall("elixir")),
                           ("Test: switch account", self.test_switch),
                           ("Ask Groq what's on screen", self.ask_groq)):
            menu.add_command(label=label, command=cmd)
        tools["menu"] = menu
        tools.pack(side="right", padx=S(8))

        body = ttk.Frame(tab)
        body.grid(row=1, column=0, columnspan=2, sticky="nsew")
        area = self._scroll_area(body)
        area.columnconfigure(0, weight=1, uniform="c")
        area.columnconfigure(1, weight=1, uniform="c")
        lcol = ttk.Frame(area)
        lcol.grid(row=0, column=0, sticky="new", padx=S(0, 6))
        rcol = ttk.Frame(area)
        rcol.grid(row=0, column=1, sticky="new", padx=S(6, 12))
        for col in (lcol, rcol):
            col.columnconfigure(0, weight=1)

        c = self.card(lcol, "Buttons", row=0, column=0, pady=S(0, 12))
        self.btn_tree = self._tree(c, ("Button", "Status", "Match"), (250, 110, 70), len(BUTTONS))
        self.btn_tree.pack(fill="x")
        row = ttk.Frame(c, style="Card.TFrame")
        row.pack(fill="x", pady=S(10, 0))
        ttk.Button(row, text="Capture", style="Accent.TButton", command=self.capture_button).pack(side="left")
        ttk.Button(row, text="Test match", command=self.test_button).pack(side="left", padx=S(8))

        c = self.card(rcol, "Text regions (OCR)", row=0, column=0, pady=S(0, 12))
        self.ocr_tree = self._tree(c, ("Region", "Status", "Last read"), (210, 100, 110), len(OCR_REGIONS))
        self.ocr_tree.pack(fill="x")
        row = ttk.Frame(c, style="Card.TFrame")
        row.pack(fill="x", pady=S(10, 0))
        ttk.Button(row, text="Capture", style="Accent.TButton", command=self.capture_region).pack(side="left")
        ttk.Button(row, text="Test read", command=self.test_region).pack(side="left", padx=S(8))

        c = self.card(rcol, "Screen points", row=1, column=0, pady=S(0, 12))
        self.pt_tree = self._tree(c, ("Point", "Position"), (230, 170), len(POINTS))
        self.pt_tree.pack(fill="x")
        row = ttk.Frame(c)
        row.pack(fill="x", pady=S(10, 0))
        ttk.Button(row, text="Capture", style="Accent.TButton", command=self.capture_point).pack(side="left")
        ttk.Button(row, text="Set troop line",
                   command=lambda: self.with_screenshot(lambda f: DropLinePicker(self, f))).pack(side="left", padx=S(8))
        ttk.Button(row, text="Set spell line", command=lambda: self.with_screenshot(lambda f: DropLinePicker(
            self, f, ("spell_point", "spell_line_end"), "Spell"))).pack(side="left")


    def _scroll_area(self, parent):
        canvas = tk.Canvas(parent, highlightthickness=0, bg=BG)
        sb = ttk.Scrollbar(parent, orient="vertical", command=canvas.yview)
        inner = ttk.Frame(canvas)
        inner.bind("<Configure>", lambda e: canvas.configure(scrollregion=canvas.bbox("all")))
        win = canvas.create_window((0, 0), window=inner, anchor="nw")
        canvas.bind("<Configure>", lambda e: canvas.itemconfigure(win, width=e.width))
        canvas.configure(yscrollcommand=sb.set)
        wheel = lambda e: canvas.yview_scroll(-int(e.delta / 120), "units")
        canvas.bind("<Enter>", lambda e: canvas.bind_all("<MouseWheel>", wheel))
        canvas.bind("<Leave>", lambda e: canvas.unbind_all("<MouseWheel>"))
        sb.pack(side="right", fill="y")
        canvas.pack(side="left", fill="both", expand=True)
        return inner

    def _build_settings(self, tab):
        foot = ttk.Frame(tab)
        foot.pack(side="bottom", fill="x", pady=S(10, 0))
        ttk.Button(foot, text="Save settings", style="Accent.TButton", command=self.save_settings).pack(side="right")
        ttk.Button(foot, text="Discard changes", command=self.load_settings_vars).pack(side="right", padx=S(8))
        ttk.Label(foot, text="Changes apply immediately, even while farming.", style="Muted.TLabel").pack(side="left")
        area = self._scroll_area(tab)
        area.columnconfigure(0, weight=1)
        self.svars = {}
        self._settings_cards(area, [(g, b, [f for f in fs if f[0] not in ADVANCED]) for g, b, fs in SETTINGS], 0)
        more = ttk.Button(area, text="▸  Show advanced settings  (timings, recognition, paths)")
        more.grid(row=1, column=0, sticky="w", padx=S(6), pady=S(10))

        def advanced():  # built on demand: ~40 rarely-touched fields made the tab slow to open
            more.destroy()
            groups = [(f"{g} - advanced", "", [f for f in fs if f[0] in ADVANCED]) for g, _, fs in SETTINGS]
            self.load_settings_vars(self._settings_cards(area, [x for x in groups if x[2]], 2))
        more.config(command=advanced)
        self.load_settings_vars()

    def _settings_cards(self, area, groups, row):
        """Settings cards in two balanced columns; returns the keys added."""
        holder = ttk.Frame(area)
        holder.grid(row=row, column=0, sticky="new")
        cols = [ttk.Frame(holder), ttk.Frame(holder)]
        for i, col in enumerate(cols):
            holder.columnconfigure(i, weight=1, uniform="g")
            col.grid(row=0, column=i, sticky="new")
        heights, added = [0, 0], []
        for group, blurb, fields in groups:
            if not fields:
                continue
            col = heights.index(min(heights))
            heights[col] += len(fields) + 2
            c = ttk.Frame(cols[col], style="Card.TFrame", padding=S(16, 12, 16, 14))
            c.pack(fill="x", padx=S(6), pady=S(6))
            c.columnconfigure(1, weight=1)
            ttk.Label(c, text=group, style="Big.TLabel").grid(row=0, column=0, columnspan=2, sticky="w")
            if blurb:
                ttk.Label(c, text=blurb, style="Muted.TLabel", wraplength=S(470)).grid(
                    row=1, column=0, columnspan=2, sticky="w", pady=S(0, 8))
            for r, (key, label, kind) in enumerate(fields, start=2):
                if kind is bool:
                    v = tk.BooleanVar()
                    ttk.Checkbutton(c, text=label, variable=v, style="Switch.TCheckbutton").grid(
                        row=r, column=0, columnspan=2, sticky="w", pady=S(3))
                else:
                    v = tk.StringVar()
                    ttk.Label(c, text=label).grid(row=r, column=0, sticky="w", pady=S(3), padx=S(0, 12))
                    (ttk.Combobox(c, textvariable=v, values=kind, state="readonly") if isinstance(kind, tuple) else
                     ttk.Entry(c, textvariable=v, show="•" if kind == "secret" else "")).grid(
                        row=r, column=1, sticky="ew", pady=S(3))
                self.svars[key] = (v, kind)
                added.append(key)
        return added

    def _build_log(self, tab):
        bar = ttk.Frame(tab)
        bar.pack(fill="x", pady=S(0, 10))
        ttk.Label(bar, text=f"Also saved to {LOG_FILE}", style="Muted.TLabel").pack(side="left")
        ttk.Button(bar, text="Open log file", command=lambda: os.startfile(LOG_FILE)).pack(side="right")
        ttk.Button(bar, text="Clear", command=self._clear_log).pack(side="right", padx=S(8))
        self.full_log = self.text_widget(tab, 20)
        sb = ttk.Scrollbar(tab, command=self.full_log.yview)
        self.full_log.configure(yscrollcommand=sb.set)
        sb.pack(side="right", fill="y")
        self.full_log.pack(fill="both", expand=True)

    # --- event pump (the only place the UI is updated from bot/background work) ---
    def report_callback_exception(self, exc, val, tb):
        """Tk errors would go to a console pythonw doesn't have: log them and keep the window alive."""
        log_file.error("UI error:\n" + "".join(traceback.format_exception(exc, val, tb)))

    def _pump(self):
        self.after(100, self._pump)  # re-arm first: one bad message must never freeze the window for good
        frame = None
        try:
            for _ in range(500):
                kind, data = self.q.get_nowait()
                if kind == "log":
                    self._append_log(*data)
                    if data[0] == "err" and time.time() - getattr(self, "_report_t", 0) > 900:
                        self.send_report(f"error: {data[1][:300]}", auto=True)
                elif kind == "state":
                    col = RED if data == "Recovering" else MUTED if data in ("Stopped", "Idle") else GREEN
                    self.state_label.config(text=data, foreground=col)
                elif kind == "stats":
                    for k, v in data.items():
                        self.stat_labels[k].config(text=f"{v:,}")
                elif kind == "frame":
                    frame = data
                elif kind == "device":
                    self._set_pill(data)
                elif kind == "phone_cmd":
                    self.phone_cmd(data)
                elif kind == "devices":
                    self.dev_combo["values"] = data
                    if self.adb.device in data:
                        self.dev_combo.set(self.adb.device)
                elif kind == "storage":
                    self.set_bb_view(data.pop("village", "home") == "builder")
                    for k, v in data.items():
                        if v is not None:
                            self.res_labels["s_" + k].config(text=f"{v:,}")
                elif kind == "loot":
                    self.loot_rows = data
                    self.render_loot()
                elif kind == "base":
                    for k, v in zip(("b_gold", "b_elixir"), data if "b_gold" in self.res_labels else ()):
                        self.res_labels[k].config(text="?" if v is None else f"{v:,}")
                elif kind == "call":
                    data()
                elif kind == "scan":
                    self.render_walls()
                    p = getattr(self, "planner", None)
                    if p is not None and p.winfo_exists():
                        p.refresh()
        except queue.Empty:
            pass
        if frame is not None:
            self._show_frame(frame)
            if self.phone:
                self.phone.jpeg = cv2.imencode(".jpg", frame, [cv2.IMWRITE_JPEG_QUALITY, 70])[1].tobytes()
        if time.time() - self._batt_t > 15:
            self._batt_t = time.time()
            b = battery()
            if b:
                pct, plugged = b
                self.batt_label.config(text=f"🔋 {pct}%" + (" ⚡" if plugged else ""),
                                       foreground=RED if pct <= 20 and not plugged else
                                       AMBER if not plugged else GREEN)
                if not plugged and pct <= 20 and not self._batt_warned:
                    self.log(f"Laptop battery at {pct}% and unplugged - plug it in or farming will stop.", "err")
                self._batt_warned = not plugged and pct <= 20
        if self.started_at and time.time() - getattr(self, "_loot_t", 0) > 5:  # keep the /hr rates current
            self._loot_t = time.time()
            self.render_loot()
        if self.phone:
            st = {k: lbl.cget("text") for k, lbl in {**self.stat_labels, **self.res_labels}.items()}
            st["battery"] = self.batt_label.cget("text").replace("🔋 ", "") or "-"
            st["loot"] = getattr(self, "loot_view", [])
            st["rates"] = {k: [a.cget("text"), b.cget("text")] for k, (a, b) in self.rate_labels.items()}
            st["walls_view"] = getattr(self, "walls_view", [])
            st["running"] = bool(self.thread)
            st["mode_key"] = self.bot.mode if self.bot else self.mode_var.get()
            st["modes"] = [[k, v[0]] for k, v in MODES.items()]
            st["resume_in"] = max(0, int(self._resume[0] - time.time())) if self._resume else 0
            st["accounts"] = [[a["sc"], a["sc"] + (f" - {a['game']}" if a.get("game") else "")
                               + (f" (TH{a['th']})" if a.get("th") else "")] for a in self.cfg.get("sc_accounts") or []]
            st["current_acc"] = getattr(self.bot, "_cur_sc", None) if self.bot else None
            st["bb"] = self.bb_view
            st["mode"] = MODES[self.bot.mode if self.bot else self.mode_var.get()][0]
            st.update(state=self.state_label.cget("text"), log=list(self.recent))
            self.phone.status = st
        if self.started_at:
            s = int(time.time() - self.started_at)
            self.stat_labels["runtime"].config(text=f"{s // 3600}h {s // 60 % 60:02d}m")
        if self.thread and not self.thread.is_alive():
            self.thread = self.bot = None
            self.started_at = None
            self.start_btn.config(state="normal")
            self.pick_mode(self.mode_var.get(), save=False)
        if self._resume and not self.thread and time.time() >= self._resume[0]:  # end of a phone pause / switch
            mode, self._resume = self._resume[1], None
            self.start_bot(mode, "phone")

    def _append_log(self, level, msg):
        ts = time.strftime("%H:%M:%S ")
        self.recent.append(ts + msg.splitlines()[0])
        for t, cap in ((self.full_log, 3000), (self.mini_log, 200)):
            t.configure(state="normal")
            t.insert("end", ts, "ts")
            t.insert("end", msg + "\n", level)
            n = int(t.index("end-1c").split(".")[0])
            if n > cap:
                t.delete("1.0", f"{n - cap}.0")
            t.see("end")
            t.configure(state="disabled")

    def _clear_log(self):
        self.full_log.configure(state="normal")
        self.full_log.delete("1.0", "end")
        self.full_log.configure(state="disabled")

    def _show_frame(self, frame):
        cw, ch = max(self.preview.winfo_width(), 50), max(self.preview.winfo_height(), 50)
        h, w = frame.shape[:2]
        s = min(cw / w, ch / h)
        img = Image.fromarray(cv2.cvtColor(frame, cv2.COLOR_BGR2RGB)).resize(
            (max(1, int(w * s)), max(1, int(h * s))), Image.BILINEAR)
        self._photo = ImageTk.PhotoImage(img)
        self.preview.delete("all")
        self.preview.create_image(cw // 2, ch // 2, image=self._photo)

    def _copy(self, text, what):
        self.clipboard_clear()
        self.clipboard_append(text)
        self.log(f"{what} copied - paste it to yourself and open it on your phone: {text}", "ok")

    def _public_url(self, url):
        if url:
            new = f"{url}/?k={self.cfg['phone_view_key']}"
            if new != self.public_url:
                self.log(f"Anywhere link ready: {new}", "ok")
                self.announce(f"🟢 **Loot Farmer v{APP_VERSION}** is running on "
                              f"**{os.environ.get('COMPUTERNAME', 'a PC')}**\n{new}")
            self.public_url = new
            self.public_label.config(text="🌍  Anywhere link  (click to copy)", foreground=BLUE)
        else:
            self.public_url = ""
            self.public_label.config(text="🌍  Anywhere link: reconnecting…", foreground=AMBER)

    def announce(self, text):
        """Post the link to Discord and keep at it - every minute for up to an hour (PC just woke up, network or
        Discord down...) - saying in the log whether it got there. A newer message replaces one still waiting."""
        self._announce_id = getattr(self, "_announce_id", 0) + 1
        my = self._announce_id

        def work():
            for i in range(60):
                if my != self._announce_id:
                    return  # superseded by a newer link / start message
                if post_discord(self.cfg, text):
                    return self.log("Anywhere link sent to Discord.", "ok")
                if i == 0:
                    self.log("Couldn't reach Discord to send the Anywhere link - retrying every minute.", "warn")
                time.sleep(60)
            self.log("Gave up sending the Anywhere link to Discord after an hour (check the webhook in Settings).",
                     "warn")
        threading.Thread(target=work, daemon=True).start()

    def _set_pill(self, ok):
        self.pill.config(text="●  Connected" if ok else "●  Offline", foreground=GREEN if ok else RED)

    # --- device ---
    def _initial_connect(self):
        devs = self.adb.devices()
        target = self.cfg["auto_connect_target"]
        if not devs and target:
            self.log(f"adb connect {target}: {self.adb.connect(target)}")
            devs = self.adb.devices()
        if devs and self.adb.device not in devs:
            self.adb.device = self.cfg["device"] if self.cfg["device"] in devs else devs[0]
        self.emit("devices", devs)
        self.emit("device", bool(devs) and self.adb.ready())
        self.log(f"Devices: {', '.join(devs) or 'none - is the emulator running with ADB enabled?'}",
                 "ok" if devs else "warn")

    def _device_chosen(self, _e=None):
        self.adb.device = self.cfg["device"] = self.dev_combo.get()
        self.adb.close_shell()
        save_config(self.cfg)
        self.bg(lambda: self.emit("device", self.adb.ready()))

    # --- start / stop ---
    def missing_setup(self):
        c = self.cfg
        miss = [f"Button: {d}" for n, d in BUTTONS if n in REQUIRED_BUTTONS and not os.path.exists(tpath(n))]
        need = ["damage_percent_region"] + ([] if c["loot_force_attack"] else ["loot_gold_region",
                                                                              "loot_elixir_region"])
        miss += [f"Text region: {d}" for n, d in OCR_REGIONS if n in need and n not in c["ocr_regions"]]
        if "deploy_point" not in c["fixed_points"]:
            miss.append("Screen point: troop drop point")
        return miss

    def toggle(self, mode="farm"):
        self._resume = None  # the PC's own Start / Stop overrides a pause set from the phone
        if self.thread:
            self.bot.stop_evt.set()
            self.start_btn.config(text="Stopping…", state="disabled")
            return
        miss = self.missing_setup()
        if miss:
            messagebox.showwarning("Setup not finished", "Finish these on the Setup tab first:\n\n"
                                   + "\n".join("•  " + m for m in miss))
            return
        if self.cfg["fixed_points"].get("deploy_point") and self.cfg.get("line_view") != 2:
            if not messagebox.askyesno("Check your troop line", "The bot now zooms fully out before it deploys "
                                       "(the view is then the same on every account).\n\nIf your troop/spell line "
                                       "was picked before this update, re-pick it: Setup > Set troop line > 'Zoom "
                                       "out + pan + refresh'.\n\nStart farming with the current line anyway?"):
                return
            self.cfg["line_view"] = 2
            save_config(self.cfg)
        self.start_bot(mode)

    def start_bot(self, mode, by=None):
        """Start farming in `mode` (setup already checked). by='phone': from the live view - no dialogs."""
        if by:
            miss = self.missing_setup()
            if miss:
                return self.log("📱 Phone: can't start - finish Setup first (" + "; ".join(miss) + ").", "warn")
            self.pick_mode(mode, save=False)
            self.log(f"📱 Phone: start ({MODES[mode][0]}).", "ok")
        self.reset_dashboard()
        self.bot = Bot(self.cfg, self.adb, self.emit, mode)
        self.thread = threading.Thread(target=self.bot.run, daemon=True)
        self.thread.start()
        self.started_at = time.time()
        if self.public_url:  # the start-up post can be missed (PC asleep, network not up yet): send it again
            url = self.public_url
            self.announce(f"▶️ Farming started on **{os.environ.get('COMPUTERNAME', 'a PC')}**\n{url}")
        self.start_btn.config(text="■  Stop")
        for k, card in self.mode_cards.items():
            if k != mode:
                card.config(highlightbackground=CARD)

    def _idle_frames(self):
        """While the bot is stopped (it sends its own frames when running) and someone has the phone view open:
        a fresh game screenshot every 2 s, so the live view isn't blank."""
        while True:
            time.sleep(2)
            if self.thread or time.time() - self.phone.last_seen > 20:
                continue
            try:
                self.emit("frame", self.adb.screenshot())
            except Exception:
                time.sleep(8)  # emulator not up: don't hammer adb

    def phone_cmd(self, c):
        """A button on the live view: start (a mode) / stop / pause N minutes / restart the game."""
        a, mode = c.get("action"), c.get("mode") if c.get("mode") in MODES else self.mode_var.get()
        running = bool(self.thread)
        if a == "start":
            if running and self.bot and self.bot.mode == mode:
                return self.log("📱 Phone: already farming.")
            self._resume = (time.time(), mode)  # starts as soon as the bot is stopped (now, if it isn't running)
            if running:
                self.log(f"📱 Phone: switching to {MODES[mode][0]}.", "ok")
                self.bot.stop_evt.set()
        elif a == "stop":
            self._resume = None
            if running:
                self.log("📱 Phone: stop.", "ok")
                self.bot.stop_evt.set()
        elif a == "pause":
            mins = max(5, min(int(c.get("minutes") or 30), 720))
            self._resume = (time.time() + mins * 60, self.bot.mode if self.bot else mode)
            self.log(f"📱 Phone: pause for {mins} min.", "ok")
            if running:
                self.bot.stop_evt.set()
        elif a == "load_accounts":
            self.log("📱 Phone: reading the account list.", "ok")
            if running:
                self.bot.list_req = True  # at the next village screen
            else:
                self.bg(lambda: Bot(self.cfg, self.adb, self.emit, mode).read_accounts())
        elif a == "switch_account":
            sc = c.get("account")
            if sc not in [x["sc"] for x in self.cfg.get("sc_accounts") or []]:
                return self.log("📱 Phone: switch - that account isn't on the saved list.", "warn")
            self.log(f"📱 Phone: switch to {sc} (at the next village screen).", "ok")
            if not running:
                self._resume = None
                self.start_bot(mode, "phone")
            if self.bot:
                self.bot.switch_req = sc
        elif a == "restart_game":
            if running:
                self.log("📱 Phone: restart the game.", "ok")
                self.bot.relaunch_req = True
            else:
                self.log("📱 Phone: restart the game - the bot isn't running.", "warn")

    def res_icon(self, k):
        """'gold' -> 'bgold' etc. while the bot is on the Builder Base."""
        return {"gold": "bgold", "elixir": "belixir"}.get(k, k) if self.bb_view else k

    def set_bb_view(self, bb):
        """Builder Base: Builder Gold / Builder Elixir icons everywhere, no Dark Elixir. Home: the normal ones."""
        if bb == self.bb_view:
            return
        self.bb_view = bb
        for k, lbl in self.res_icons.items():
            lbl.config(image=self.ui_icon(self.res_icon(k), S(32)))
        self.res_card_title.config(text="BUILDER BASE STORAGE" if bb else "YOUR STORAGE")
        for k, lbl in self.rate_icons.items():
            lbl.config(image=self.ui_icon(self.res_icon(k), S(30)))
        self.rate_cells["dark"].master.columnconfigure(2, weight=0 if bb else 1, uniform="" if bb else "rt")
        self.rate_cells["dark"].grid_remove() if bb else self.rate_cells["dark"].grid()
        self.render_loot()

    def render_loot(self):
        """Per-account session loot + per-hour rates (loot / time since Start), with an all-accounts total."""
        rows = getattr(self, "loot_rows", {})
        hrs = max((time.time() - self.started_at) / 3600, 1 / 60) if self.started_at else None
        short = lambda v: f"{v / 1e6:.2f}M" if v >= 1e6 else f"{v / 1e3:.0f}k" if v >= 1e3 else str(int(v))
        rate = lambda v: short(v / hrs) if hrs else "-"
        items = sorted(rows.items())
        if len(items) > 1:
            items.append(("All accounts", [sum(r[i] for _, r in items) for i in range(4)]))
        self.loot_view = [[acc, short(g), rate(g), short(e), rate(e), short(dk), rate(dk), n]
                          for acc, (g, e, dk, n) in items]
        tot = [sum(r[i] for r in rows.values()) for i in range(4)]
        for i, key in enumerate(("gold", "elixir", "dark")):
            per, total = self.rate_labels[key]
            per.config(text=f"{rate(tot[i])} / h" if hrs and rows else "—")
            total.config(text=f"{short(tot[i])} this session" if rows else "per hour")
        for w in self.acc_box.winfo_children():
            w.destroy()
        if not rows:
            tk.Label(self.acc_box, text="Loot per account shows here once farming starts.", bg=CARD, fg=MUTED,
                     font=("Segoe UI", 9)).pack(anchor="w")
        for acc, (g, e, dk, n) in sorted(rows.items()):
            row = tk.Frame(self.acc_box, bg=CARD, pady=S(3))
            row.pack(fill="x")
            tk.Label(row, text=acc, bg=CARD, fg=TEXT, font=("Segoe UI", 10, "bold"), width=12, anchor="w").pack(
                side="left")
            for v, icon, col in ((g, "gold", GOLD), (e, "elixir", PINK), (dk, "dark", "#b9a3ff"), (n, "king", TEXT)):
                if icon == "dark" and self.bb_view:
                    continue
                tk.Label(row, image=self.ui_icon(self.res_icon(icon), S(18)), bg=CARD).pack(side="left", padx=S(10, 3))
                tk.Label(row, text=str(v) if icon == "king" else short(v), bg=CARD, fg=col,
                         font=("Segoe UI", 10, "bold")).pack(side="left")
        if hrs and hrs >= 0.05 and rows:  # from the first attack (~3 min): rough, sharpens as the session goes
            self.cfg["loot_rate"] = int(sum(r[0] + r[1] for r in rows.values()) / hrs)
            self.render_walls()

    def render_walls(self):
        """Per account: a bar of its walls by level (green = max for its Town Hall), what's left to pay and how
        long that is at the farming rate."""
        cv = self.walls_cv
        cv.delete("all")
        W = max(cv.winfo_width(), S(300))
        rate = self.cfg.get("loot_rate")
        short = lambda v: f"{v / 1e9:.2f}B" if v >= 1e9 else f"{v / 1e6:.1f}M" if v >= 1e6 else f"{v / 1e3:.0f}k"
        if not hasattr(self, "_wall_icon"):
            try:
                im = Image.open(os.path.join(WIKI_DIR, wiki_data()["home:wall"]["icon"])).convert("RGBA")
                im.thumbnail((S(34), S(34)))
                self._wall_icon = ImageTk.PhotoImage(im)
            except Exception:
                self._wall_icon = None
        tagged = set((self.cfg.get("account_tags") or {}).values())
        y, views = 0, []
        self.walls_view = views  # the phone page shows the same lines
        for acc, bases in sorted((self.cfg.get("scans") or {}).items()):
            if tagged and acc not in tagged and difflib.get_close_matches(acc, tagged, 1, 0.75):
                continue
            sd = bases.get("home") or {}
            counts, mx, todo, cost = walls_left(sd)
            if not counts:
                continue
            total, x0 = sum(counts.values()), S(46)
            if self._wall_icon:
                cv.create_image(0, y + S(2), image=self._wall_icon, anchor="nw")
            cv.create_text(x0, y, anchor="nw", fill=TEXT, font=("Segoe UI", 10, "bold"),
                           text=f"{acc}   ·   Town Hall {sd.get('hall') or '?'}")
            by, bh, x = y + S(24), S(16), x0
            for lvl in sorted(counts):
                w = (W - x0 - S(4)) * counts[lvl] / total
                f = max(0.0, min(1.0, (lvl - (mx or lvl) + 6) / 6))  # older levels redder, nearly-max amber
                col = GREEN if mx and lvl >= mx else "#%02x%02x%02x" % (int(0xff - 0x1a * f), int(0x6b + 0x49 * f),
                                                                         int(0x6b - 0x17 * f))
                cv.create_rectangle(x, by, x + w, by + bh, fill=col, width=0)
                if w > S(26):
                    cv.create_text(x + w / 2, by + bh / 2, text=str(lvl), fill="#111", font=("Segoe UI", 8, "bold"))
                x += w
            hours = lambda v: f"≈ {v / rate:,.1f} h of farming" if rate else "start farming to estimate the hours"
            if todo:  # headline: the next step - every wall at the lowest level up one level
                low = min(counts)
                n_low, step = counts[low], wiki_data()["home:wall"]["levels"][low]["cost"]
                text = f"Next: {n_low} walls → level {low + 1}   ·   {short(n_low * step)}   ·   {hours(n_low * step)}"
            else:
                text = f"✓  all {total} walls at level {mx}"
            head = cv.create_text(x0, by + bh + S(6), anchor="nw", font=("Segoe UI", 10, "bold"),
                                  fill=GREEN if not todo else GOLD, width=W - x0, text=text)
            views.append([f"{acc} · Town Hall {sd.get('hall') or '?'}", text, f"All {todo} to level {mx}: {short(cost)}"
                          + (f" · {hours(cost)}" if rate else "") if todo else ""])
            if todo:
                cv.create_text(x0, cv.bbox(head)[3] + S(2), anchor="nw", fill=MUTED, font=("Segoe UI", 9),
                               width=W - x0, text=f"All {todo} to level {mx} (max for this Town Hall): {short(cost)}"
                               + (f"   ·   {hours(cost)}" if rate else "")
                               + (f"   ·   at {short(rate)} gold + elixir / h" if rate else ""))
            y = cv.bbox("all")[3] + S(12)
        if not y:
            cv.create_text(0, 0, anchor="nw", fill=MUTED, font=("Segoe UI", 9),
                           text="Scan an account in the Upgrade planner to see its walls here.")
            y = S(24)
        cv.configure(height=y)

    def reset_dashboard(self):
        for k, lbl in self.stat_labels.items():
            lbl.config(text="0" if k != "runtime" else "0h 00m")
        for lbl in self.res_labels.values():
            lbl.config(text="—")
        self.loot_rows, self.loot_view = {}, []
        self.render_loot()

    def _update_tick(self):
        """Check GitHub for a newer version now and every 30 minutes."""
        def work():
            man = check_update()
            if man:
                self.ui(lambda: self._show_update(man))
        self.bg(work)
        self.after(30 * 60 * 1000, self._update_tick)

    def _show_update(self, man):
        if not self._update:
            self.log(f"Update available: version {man['version']} (you have {APP_VERSION}). Click ⬆ Update.", "ok")
            self.update_btn.pack(fill="x", pady=S(0, 10), before=self.update_btn.master.winfo_children()[1])
        self._update = man

    def do_update(self):
        if not self._update:
            return
        msg = "Download the update and restart Loot Farmer?"
        if self.thread:
            msg = "Farming is running - stop it, download the update and restart?"
        if not messagebox.askyesno("Update", msg + "\n\nYour settings and drop lines are kept."):
            return
        if self.thread:
            self.bot.stop_evt.set()
        self.update_btn.config(text="Updating…", state="disabled")

        def work():
            try:
                n = apply_update(self._update)
            except Exception as e:
                self.log(f"Update failed: {e}", "err")
                return self.ui(lambda: self.update_btn.config(text="⬆  Update available - click to update",
                                                              state="normal"))
            self.log(f"Updated {n} files to version {self._update['version']} - restarting.", "ok")
            self.ui(lambda: self.after(800, self._restart_now))
        self.bg(work)

    def _tab_changed(self, _e=None):
        """The planner tab is built the first time it's opened (50+ cards: no need to slow the start-up)."""
        tab = self.nb.nametowidget(self.nb.select())
        for page, ws in self.nav.items():
            on = self.tabs[page] is tab
            for w in ws:
                w.config(bg=NAV_ON if on else SIDE)
            ws[2].config(font=("Segoe UI", 11, "bold" if on else "normal"))
        if tab is self.planner_tab:
            if self.planner is None:
                self.planner = PlannerTab(self, tab)
                self.planner.pack(fill="both", expand=True)

    def pick_version(self):
        """List the published versions and install the chosen one (older or newer). Settings are kept."""
        self.log("Loading the version list from GitHub…")

        def work():
            try:
                vs = list_versions()
            except Exception as e:
                return self.log(f"Couldn't load the version list: {e}", "err")
            self.ui(lambda: self._version_window(vs))
        self.bg(work)

    def _version_window(self, vs):
        if not vs:
            return self.log("No published versions found.", "warn")
        w = tk.Toplevel(self)
        w.title("Switch version")
        w.configure(bg=BG)
        w.transient(self)
        f = ttk.Frame(w, padding=S(14))
        f.pack(fill="both", expand=True)
        ttk.Label(f, text=f"You have version {APP_VERSION}. Pick one to install - your settings, drop lines and "
                          "accounts are kept.", style="Sub.TLabel").pack(anchor="w", pady=S(0, 8))
        tree = self._tree(f, ("Version", "Published", "Notes"), (80, 110, 360), min(len(vs), 12))
        tree.pack(fill="both", expand=True)
        for v, d, m, sha in vs:
            tree.insert("", "end", iid=sha, values=(f"v{v}" + ("  (current)" if v == APP_VERSION else ""), d, m))

        def go():
            sel = tree.selection()
            if not sel:
                return
            v = next(x[0] for x in vs if x[3] == sel[0])
            if not messagebox.askyesno("Switch version", f"Install version {v} and restart Loot Farmer?"
                                       + ("\n\nFarming will be stopped." if self.thread else "")
                                       + "\n\nAn 'Update available' button will offer the newest again."
                                       + ("\n\nWARNING: this is your publishing folder - changes you haven't "
                                          "published yet will be overwritten."
                                          if os.path.isdir(os.path.join(BASE_DIR, ".git")) else ""), parent=w):
                return
            if self.thread:
                self.bot.stop_evt.set()
            w.destroy()

            def work():
                try:
                    n = install_version(sel[0])
                except Exception as e:
                    return self.log(f"Switching version failed: {e}", "err")
                self.log(f"Installed version {v} ({n} files) - restarting.", "ok")
                self.ui(lambda: self.after(800, self._restart_now))
            self.bg(work)
        ttk.Button(f, text="Install selected version", style="Accent.TButton", command=go).pack(anchor="e", pady=S(10, 0))

    def _restart_now(self):
        self._close()
        exe = sys.executable
        if os.name == "nt" and exe.lower().endswith("python.exe") and os.path.exists(exe[:-10] + "pythonw.exe"):
            exe = exe[:-10] + "pythonw.exe"
        subprocess.Popen([exe, os.path.abspath(__file__)], cwd=BASE_DIR, creationflags=0x00000008)

    def send_report(self, reason, auto=False):
        """bot.log, the debug screenshots, the live screen and the non-secret settings to the Discord webhook.
        Automatic ones (on errors) at most every 15 min so a repeating error can't flood the channel."""
        if not self.cfg.get("discord_webhook"):
            if not auto:
                self.log("No Discord webhook set (discord_webhook in bot.py / config.json).", "warn")
            return
        self._report_t = time.time()

        def work():
            files, hide = [], re.compile(r"k=[\w-]+")
            try:
                with open(LOG_FILE, encoding="utf-8", errors="replace") as f:
                    files.append(("bot.log", hide.sub("k=<hidden>", "".join(f.readlines()[-400:])).encode()))
            except OSError:
                pass
            try:  # what the Anywhere link's tunnel did (link problems)
                with open(Tunnel.LOG, encoding="utf-8", errors="replace") as f:
                    files.append(("cloudflared.log", "".join(f.readlines()[-80:]).encode()))
            except OSError:
                pass
            for name in ("debug_deploy.png", "debug_wall.png", "debug_boat.png", "debug_export.png", "debug_upgrade.png"):
                path = os.path.join(BASE_DIR, name)
                if os.path.exists(path) and time.time() - os.path.getmtime(path) < 6 * 3600:
                    img = cv2.imread(path)
                    if img is not None:
                        files.append((name.replace(".png", ".jpg"), cv2.imencode(".jpg", img, [cv2.IMWRITE_JPEG_QUALITY, 85])[1].tobytes()))
            try:
                files.append(("screen_now.jpg", cv2.imencode(".jpg", self.adb.screenshot(),
                                                             [cv2.IMWRITE_JPEG_QUALITY, 85])[1].tobytes()))
            except Exception:
                pass
            secret = ("groq_api_key", "phone_view_key", "discord_webhook")
            files.append(("settings.json", json.dumps({k: v for k, v in self.cfg.items() if k not in secret},
                                                      indent=1).encode()))
            text = (f"🐞 **Debug report** from **{os.environ.get('COMPUTERNAME', 'a PC')}** (v{APP_VERSION}) - "
                    f"{reason}\nState: {self.state_label.cget('text')}")
            if post_discord(self.cfg, text, files):
                self.log(f"Debug report sent to Discord ({len(files)} files).", "ok")
            elif not auto:
                self.log("Couldn't send the debug report - details in bot.log.", "warn")
        self.bg(work)

    def restart_app(self):
        """Close and reopen the app so it picks up code changes (stops any farming first)."""
        if self.thread and not messagebox.askyesno("Restart", "Farming is running - stop it and restart the app?"):
            return
        self.log("Restarting…")
        self._close()
        exe = sys.executable
        if os.name == "nt" and exe.lower().endswith("python.exe") and os.path.exists(exe[:-10] + "pythonw.exe"):
            exe = exe[:-10] + "pythonw.exe"  # no console window
        subprocess.Popen([exe, os.path.abspath(__file__)], cwd=BASE_DIR, creationflags=0x00000008)  # detached

    def _close(self):
        if self.bot:
            self.bot.stop_evt.set()
            self.thread.join(timeout=3)
        self.adb.close_shell()
        if self.phone:
            self.phone.server.shutdown()
        # the Cloudflare tunnel is left running on purpose, so the next start reuses the same link
        self.destroy()

    # --- settings ---
    def load_settings_vars(self, keys=None):
        for key, (v, kind) in self.svars.items():
            if keys is not None and key not in keys:
                continue
            val = self.cfg.get(key, DEFAULTS.get(key))
            if kind is bool:
                v.set(bool(val))
            elif kind is int:
                v.set(str(int(float(val or 0))))
            else:
                v.set("" if val is None else str(val))

    def save_settings(self):
        new = {}
        for key, (v, kind) in self.svars.items():
            try:
                raw = v.get()
                new[key] = (bool(raw) if kind is bool else int(float(raw)) if kind is int
                            else float(raw) if kind is float else raw.strip())
            except (ValueError, tk.TclError):
                label = next(lbl for _, _, fs in SETTINGS for k, lbl, _ in fs if k == key)
                messagebox.showerror("Invalid value", f"'{label}' needs a number.")
                return
        self.cfg.update(new)
        if hasattr(self, "bb_var"):
            self.bb_var.set(bool(self.cfg["builder_base_enabled"]))
        self.adb.path = self.cfg["adb_path"]
        if HAVE_TESS:
            pytesseract.pytesseract.tesseract_cmd = self.cfg["tesseract_path"]
        save_config(self.cfg)
        self.log("Settings saved.", "ok")

    # --- setup tab ---
    def refresh_setup(self):
        for t in (self.btn_tree, self.ocr_tree, self.pt_tree):
            keep = {i: t.set(i) for i in t.get_children()}
            t.delete(*t.get_children())
            t.keep = keep
        for n, d in BUTTONS:
            ok = os.path.exists(tpath(n))
            tag = "ok" if ok else "missing" if n in REQUIRED_BUTTONS else "optional"
            self.btn_tree.insert("", "end", iid=n, tags=(tag,),
                                 values=(d, "✓ Ready" if ok else "✗ Missing" if tag == "missing" else "—  Not set",
                                         self.btn_tree.keep.get(n, {}).get("Match", "")))
        for n, d in OCR_REGIONS:
            ok = n in self.cfg["ocr_regions"]
            self.ocr_tree.insert("", "end", iid=n, tags=("ok" if ok else "optional",),
                                 values=(d, "✓ Set" if ok else "—  Not set",
                                         self.ocr_tree.keep.get(n, {}).get("Last read", "")))
        for n, d in POINTS:
            p = self.cfg["fixed_points"].get(n)
            self.pt_tree.insert("", "end", iid=n, tags=("ok" if p else "optional",),
                                values=(d, f"({p[0]}, {p[1]})" if p else "—  Not set"))

    def selected(self, tree, what):
        sel = tree.selection()
        if not sel:
            messagebox.showinfo("Select a row", f"Select a {what} in the list first.")
        return sel[0] if sel else None

    def with_screenshot(self, fn):
        """Screenshot off the UI thread, then fn(frame) back on it."""
        def work():
            try:
                frame = self.adb.screenshot()
            except ADBError as e:
                self.log(f"Screenshot failed: {e}", "err")
                return
            self.ui(lambda: fn(frame))
        self.bg(work)

    def capture_button(self):
        n = self.selected(self.btn_tree, "button")
        if n:
            self.with_screenshot(lambda f: CaptureWindow(
                self, f, f"Drag a tight box around: {dict(BUTTONS)[n]}", lambda c, ctr, b: self._save_button(n, c, ctr)))

    def _save_button(self, n, img, center):
        cv2.imwrite(tpath(n), img)
        self.cfg["coords"][n] = list(center)
        save_config(self.cfg)
        self.log(f"Saved button '{n}'.", "ok")
        self.refresh_setup()

    def test_button(self):
        n = self.selected(self.btn_tree, "button")
        if not n:
            return

        def done(frame):
            r = self.vision.score(frame, n)
            if r is None:
                return self.log(f"'{n}' has no image yet.", "warn")
            ok = r[0] >= self.cfg["match_confidence"]
            self.btn_tree.set(n, "Match", f"{r[0]:.2f}")
            self.log(f"'{n}': best match {r[0]:.2f} at ({r[1]}, {r[2]}) - "
                     + ("would be tapped." if ok else "below confidence, not on this screen?"),
                     "ok" if ok else "warn")
        self.with_screenshot(done)

    def capture_region(self):
        n = self.selected(self.ocr_tree, "region")
        if n:
            self.with_screenshot(lambda f: CaptureWindow(
                self, f, f"Drag a box around just the digits: {dict(OCR_REGIONS)[n]}",
                lambda c, ctr, b: self._save_region(n, b, f)))

    def _save_region(self, n, box, frame):
        self.cfg["ocr_regions"][n] = box
        save_config(self.cfg)
        self.refresh_setup()
        self._read_region(n, frame)

    def _read_region(self, n, frame):
        md = 1 if n == "damage_percent_region" else self.cfg["ocr_min_digits"]
        v = ocr_number(frame, self.cfg["ocr_regions"][n], self.cfg["ocr_region_padding_px"], md)
        self.ocr_tree.set(n, "Last read", "unreadable" if v is None else f"{v:,}")
        self.log(f"'{n}' reads: {'unreadable' if v is None else f'{v:,}'}", "warn" if v is None else "ok")

    def test_region(self):
        n = self.selected(self.ocr_tree, "region")
        if n and n not in self.cfg["ocr_regions"]:
            return self.log(f"Capture '{n}' first.", "warn")
        if n:
            self.with_screenshot(lambda f: self._read_region(n, f))

    def capture_point(self):
        n = self.selected(self.pt_tree, "point")
        if n:
            self.with_screenshot(lambda f: CaptureWindow(
                self, f, f"Drag a small box centred on: {dict(POINTS)[n]}",
                lambda c, ctr, b: self._save_point(n, ctr)))

    def _save_point(self, n, center):
        self.cfg["fixed_points"][n] = list(center)
        save_config(self.cfg)
        self.log(f"Saved point '{n}' at {center}.", "ok")
        self.refresh_setup()

    def preview_screen(self):
        def show(frame):
            win = tk.Toplevel(self)
            win.title("Emulator screen")
            win.configure(bg=BG)
            h, w = frame.shape[:2]
            s = min(S(1100) / w, S(640) / h, 1.0)
            win.photo = ImageTk.PhotoImage(Image.fromarray(cv2.cvtColor(frame, cv2.COLOR_BGR2RGB)).resize(
                (int(w * s), int(h * s)), Image.LANCZOS))
            ttk.Label(win, image=win.photo).pack(padx=S(12), pady=S(12))
            ttk.Label(win, text=f"{w} x {h}", style="Muted.TLabel").pack(pady=S(0, 10))
        self.with_screenshot(show)

    def read_bar(self):
        """Log what auto-deploy would do with the troop bar on screen (start a search first)."""
        def work():
            cards = troop_bar(self.adb.screenshot())
            if not cards:
                return self.log("No troop bar on screen - start a search (scouting screen) first.", "warn")
            for x, y, kind, n in cards:
                self.log(f"  card at x={x}: {kind}" + (f" x{n}" if n is not None else ""))
        self.bg(work)

    def test_switch(self):
        if self.thread:
            return messagebox.showinfo("Farming is running", "Stop farming first, then test.")
        if not messagebox.askyesno("Test account switch", "Switch to the next account now?\n\nStart from the "
                                   "home village."):
            return

        def work():
            b = Bot(self.cfg, self.adb, self.emit)
            b._acc_idx = self.cfg.get("_last_account_idx", -1)
            try:
                ok = b.switch_account()
            except (Abort, ADBError) as e:
                return self.log(f"Switch test stopped: {e}", "warn")
            self.cfg["_last_account_idx"] = b._acc_idx
            self.log("Switch test: done." if ok else "Switch test: failed (see above).", "ok" if ok else "warn")
        self.bg(work)

    def test_upgrade(self, kind):
        """Start one builder/lab upgrade now (most expensive affordable), ignoring the on/off switches."""
        if self.thread:
            return messagebox.showinfo("Farming is running", "Stop farming first, then test.")
        if not messagebox.askyesno("Test upgrade", f"Start the most expensive {kind} upgrade you can afford "
                                   "now?\n\nStart from the home village. Gems and magic items are never used."):
            return

        def work():
            self.log(f"Testing a {kind} upgrade…")
            try:
                Bot(self.cfg, self.adb, self.emit).upgrade_from_list(kind)
            except (Abort, ADBError) as e:
                self.log(f"Upgrade test stopped: {e}", "warn")
        self.bg(work)

    def test_wall(self, cur):
        """Buy exactly one wall upgrade now, ignoring the storage threshold."""
        if self.thread:
            return messagebox.showinfo("Farming is running", "Stop farming first, then test the wall upgrade.")
        if not messagebox.askyesno("Test wall upgrade", f"Buy ONE wall upgrade with {cur} now?\n\n"
                                   "Start from the home village. Gems are never spent."):
            return

        def work():
            self.log(f"Testing a {cur} wall upgrade…")
            try:
                Bot(self.cfg, self.adb, self.emit).buy_wall(cur)
            except (Abort, ADBError) as e:
                self.log(f"Wall test stopped: {e}", "warn")
        self.bg(work)

    def ask_groq(self):
        """Shows what the AI supervisor would decide on the current screen (it doesn't tap)."""
        def work():
            if not self.cfg.get("groq_api_key"):
                return self.log("Add your Groq API key in Settings > Engine first.", "warn")
            self.log("Asking Groq about the current screen…")
            t = time.time()
            r = groq_ask(self.cfg, self.adb.screenshot(), RESCUE_PROMPT)
            if r is None:
                return self.log("Groq didn't answer - check the key/model in Settings and bot.log.", "err")
            self.log(f"Groq ({time.time() - t:.1f}s): screen={r.get('screen')}, action={r.get('action')} "
                     f"{r.get('target')!r}, button={r.get('button')} - {r.get('reason')}", "ok")
        self.bg(work)

    def setup_check(self):
        self.log("Setup check…")
        for m in self.missing_setup():
            self.log(f"Missing - {m}", "warn")
        frame = self.adb.screenshot()
        h, w = frame.shape[:2]
        bad = [f"{n} {tuple(b)}" for n, b in self.cfg["ocr_regions"].items() if b[2] > w or b[3] > h]
        bad += [f"{n} {tuple(p)}" for n, p in self.cfg["fixed_points"].items() if p[0] > w or p[1] > h]
        for b in bad:
            self.log(f"Outside the current {w}x{h} screen (resolution changed?): {b}", "warn")
        state = next((s for n, s in STATES if self.vision.find(frame, n, self.cfg["match_confidence"])), None)
        self.log(f"Screen is {w}x{h}; the bot thinks it's on: {STATE_LABELS[state]}.", "ok")
        if not HAVE_TESS or not os.path.exists(self.cfg["tesseract_path"]):
            self.log("Tesseract not found - install it or fix its path in Settings > Engine.", "err")
        if not self.missing_setup() and not bad:
            self.log("Everything required is set up.", "ok")


# ---------------------------------------------------------------------------
# Self-check: python bot.py --selftest
# ---------------------------------------------------------------------------
def selftest():
    px = bytes(range(24)) * 2  # 4x3 RGBA
    for extra in (b"", b"\0\0\0\0"):
        img = decode_raw(struct.pack("<III", 4, 3, 1) + extra + px)
        assert img.shape == (3, 4, 3) and tuple(img[0, 0]) == (2, 1, 0), "raw screencap decode"
    assert decode_raw(b"\x89PNG not raw at all") is None
    assert panel_box(np.zeros((1080, 1920, 3), np.uint8)) is None, "no list open"
    # names as OCR reads them, and look-alikes that must not match
    assert name_match("Lonashot&", "Longshot") and name_match("New Hog Glider", "Hog Glider")
    assert name_match("0.T.T.0's Ouboost", "O.T.T.O's Outpost") and name_match("Scabbershot x2", "Scattershot")
    assert not name_match("Ricochet Cannon", "Cannon") and not name_match("Dark Elixir Storage", "Elixir Storage")
    assert not name_match("Hog Rider", "Hog Glider") and not name_match("Miner", "Mine")
    assert all(map(is_wall, ("Wall", "Wall x28", "': Wall x2", "Wall xI50"))) and not is_wall("Wall Wrecker")
    if wiki_data():  # price -> level, with the discount worked out from the whole list (Hammer Jam / Gold Pass)
        rows = [("Cannon x4", 3000000), ("Mortar x3", 21000000), ("Archer Queen", 380000), ("Laboratoru", 13000000)]
        for f in (1, 0.8, 0.5):
            got = [(n, int(p * f)) for n, p in rows]
            assert infer_discount(got, "home") == f, f
            assert level_for_price(wiki_key("Cannon x4", "home"), 3000000 * f, f) == 20

    frame = np.random.default_rng(0).integers(0, 255, (1080, 1920, 3), dtype=np.uint8)
    frame = cv2.GaussianBlur(frame, (5, 5), 0)
    d = tempfile.mkdtemp()
    try:
        cv2.imwrite(os.path.join(d, "btn.png"), frame[500:560, 800:900])
        v = Vision(d)
        sc, x, y = v.score(frame, "btn")
        assert sc > 0.9 and abs(x - 850) <= 2 and abs(y - 530) <= 2, f"template match {sc, x, y}"
        assert v.find(frame, "nope", 0.8) is None
    finally:
        shutil.rmtree(d)

    g = digit_glyphs()
    assert g is not None, "templates/digits.png missing"
    canvas = np.zeros((40, 12 + 26 * 7), bool)
    for j, ch in enumerate("9524837"):
        canvas[6:34, 6 + j * 26:26 + j * 26] = g[int(ch)] > 0.5
    assert read_digit_blobs(canvas) == 9524837, "digit reader"

    grey = np.full((60, 60, 3), 120, np.uint8)
    red = grey.copy()
    red[:, :] = (30, 30, 220)
    assert icon_empty(grey, 30, 30) and not icon_empty(red, 30, 30), "grey slot detection"

    # the game's data export: ids -> buildings, upgrading = next level, supercharged copies merged
    ex = export_items({"buildings": [{"data": 1000013, "lvl": 17, "timer": 5}, {"data": 1000002, "lvl": 17, "cnt": 2},
                                     {"data": 1000002, "lvl": 17, "cnt": 4, "supercharge": 1}, {"data": 1000010, "lvl": 9}],
                       "heroes2": [{"data": 28000003, "lvl": 35}]})
    assert sorted((r["key"], r["level"], r["count"], r["upgrading"]) for r in ex["home"]) == [
        ("home:elixir collector", 17, 6, False), ("home:mortar", 18, 1, True), ("home:wall", 9, 1, False)], ex
    # walls left: mixed levels, each priced up to the TH16 max (17): 2 x (16: 4M + 17: 5M) = 18M, maxed ones free
    w = walls_left({"hall": 16, "items": [{"key": "home:wall", "level": 15, "count": 2},
                                          {"key": "home:wall", "level": 17, "count": 3}]})
    assert w == ({15: 2, 17: 3}, 17, 2, 18_000_000), w
    assert [(r["key"], r["level"]) for r in ex["builder"]] == [("builder:battle machine", 35)], ex

    if HAVE_TESS and os.path.exists(DEFAULTS["tesseract_path"]):
        pytesseract.pytesseract.tesseract_cmd = DEFAULTS["tesseract_path"]
        img = np.zeros((80, 420, 3), np.uint8)
        cv2.putText(img, "1234567", (10, 60), cv2.FONT_HERSHEY_SIMPLEX, 2, (255, 255, 255), 4)
        got = ocr_number(img, (0, 0, 420, 80), 0, 3)
        assert got == 1234567, f"OCR read {got}"
    print("selftest ok")


PACKAGES = ("opencv-python", "Pillow", "numpy", "sv-ttk", "pytesseract", "groq")


def bundle_python():
    """A portable copy of this PC's Python (a normal Windows install runs from any folder) with only the bot's
    modules in it, built in the temp folder. Returns its path."""
    out = os.path.join(tempfile.gettempdir(), "lootfarmer_python")
    shutil.rmtree(out, ignore_errors=True)
    skip = {"site-packages", "test", "idlelib", "__pycache__", "Doc", "Scripts", "include", "libs", "Tools",
            "ensurepip", "lib2to3", "tkinter/test", "turtledemo"}
    shutil.copytree(sys.base_prefix, out, ignore=lambda d, names: [n for n in names if n in skip])
    subprocess.run([sys.executable, "-m", "pip", "install", "--quiet", "--no-warn-script-location", "--target",
                    os.path.join(out, "Lib", "site-packages"), "opencv-python-headless",  # no GUI/video: smaller
                    *(p for p in PACKAGES if p != "opencv-python")], check=True)
    for f in glob.glob(os.path.join(out, "Lib", "site-packages", "cv2", "opencv_videoio_ffmpeg*.dll")):
        os.remove(f)  # video decoding: never used (30 MB)
    return out


def make_package():
    """LootFarmer_share.zip for a friend: bot + templates + setup, with a config stripped of anything personal
    (API key, phone-link secret, device, paths, account names). Setup.bat fills the paths in on their PC."""
    cfg, _ = load_config()
    shared = {k: cfg.get(k, v) for k, v in DEFAULTS.items()}  # drops leftovers from the old bot
    shared.update(groq_api_key="", phone_view_key="", device="", accounts="", emulator_exe_path="",
                  adb_path="", tesseract_path="",  # -> the bundled copies in the folder
                  auto_connect_target=DEFAULTS["auto_connect_target"], watchdog_enabled=False)
    out = os.path.join(BASE_DIR, "LootFarmer_share.zip")
    with zipfile.ZipFile(out, "w", zipfile.ZIP_DEFLATED) as z:
        for f in ("bot.py", "setup.ps1", "Setup.bat", "README.txt"):
            z.write(os.path.join(BASE_DIR, f), f"LootFarmer/{f}")
        for folder in ("Tesseract-OCR", "platform-tools"):  # bundled tools: nothing to install
            for root, _, files in os.walk(os.path.join(BASE_DIR, folder)):
                for f in files:
                    full = os.path.join(root, f)
                    z.write(full, "LootFarmer/" + os.path.relpath(full, BASE_DIR).replace(os.sep, "/"))
        py = bundle_python()  # Python + the bot's modules inside the folder: no install, no pip on their PC
        for root, _, files in os.walk(py):
            for f in files:
                full = os.path.join(root, f)
                z.write(full, "LootFarmer/python/" + os.path.relpath(full, py).replace(os.sep, "/"))
        for f in sorted(os.listdir(TEMPLATE_DIR)):
            if f.endswith(".png") and not f.startswith("old_"):
                z.write(os.path.join(TEMPLATE_DIR, f), f"LootFarmer/templates/{f}")
        for f in published_files():
            if f.startswith("wiki/"):
                z.write(os.path.join(BASE_DIR, f), f"LootFarmer/{f}")
        z.writestr("LootFarmer/config.json", json.dumps(shared, indent=2))
    print(f"Created {out}")


PUBLISHED = ("bot.py", "setup.ps1", "Setup.bat", "README.txt", ".gitignore", ".gitattributes", "blocked.txt")
BLOCKED_PCS = ("elliots-macbook-air",)  # PCs not allowed to run Loot Farmer (also blocked.txt, here and on GitHub)


def pc_names():
    """This PC's names, normalised ('Elliots-MacBook-Air.local' -> 'elliots-macbook-air')."""
    names = {os.environ.get("COMPUTERNAME", ""), socket.gethostname(), platform.node()}
    return {re.sub(r"[\s_]+", "-", n.strip().lower()).removesuffix(".local") for n in names if n}


def pc_blocked():
    """True if this PC is on the blocklist: the built-in one, blocked.txt in the folder, or blocked.txt on GitHub
    (so a name can be added without a new version)."""
    lines = list(BLOCKED_PCS)
    try:
        lines += open(os.path.join(BASE_DIR, "blocked.txt"), encoding="utf-8").read().splitlines()
    except OSError:
        pass
    try:
        lines += fetch("blocked.txt", timeout=6).decode("utf-8", "replace").splitlines()
    except Exception:
        pass
    blocked = {re.sub(r"[\s_]+", "-", ln.split("#")[0].strip().lower()).removesuffix(".local") for ln in lines}
    return bool(pc_names() & (blocked - {""}))


def published_files():
    """Everything an update carries: the code, setup files and templates. Never config.json / logs / tools."""
    files = [f for f in PUBLISHED if os.path.exists(os.path.join(BASE_DIR, f))]
    files += sorted(f"templates/{f}" for f in os.listdir(TEMPLATE_DIR) if f.endswith(".png"))
    if os.path.isdir(WIKI_DIR):  # the upgrade planner's wiki data + building pictures
        files += ["wiki/buildings.json"] * os.path.exists(os.path.join(WIKI_DIR, "buildings.json"))
        icons = os.path.join(WIKI_DIR, "icons")
        files += sorted(f"wiki/icons/{f}" for f in (os.listdir(icons) if os.path.isdir(icons) else [])
                        if f.endswith(".png"))
        ui = os.path.join(WIKI_DIR, "ui")  # the app's own Clash icons (sidebar, modes, tiles)
        files += sorted(f"wiki/ui/{f}" for f in (os.listdir(ui) if os.path.isdir(ui) else [])
                        if f.endswith((".png", ".ico")))
    return files


def file_hash(path):
    with open(path, "rb") as f:
        return hashlib.sha256(f.read()).hexdigest()


def fetch(path, timeout=20, ref="main"):
    url = f"https://raw.githubusercontent.com/{UPDATE_REPO}/{ref}/{path}?t={int(time.time())}"
    with urllib.request.urlopen(urllib.request.Request(url, headers={"Cache-Control": "no-cache"}),
                                timeout=timeout) as r:
        return r.read()


def check_update():
    """The published manifest if GitHub has a newer version than this copy, else None."""
    try:
        man = json.loads(fetch("manifest.json"))
        return man if int(man.get("version", 0)) > APP_VERSION else None
    except Exception as e:
        log_file.info(f"Update check failed: {e}")
        return None


def apply_update(man):
    """Download only the files whose hash differs, check each against the manifest, then swap them in.
    config.json and anything not in the manifest are left alone. Returns the number of files updated."""
    changed = {}
    for path, digest in man["files"].items():
        if ".." in path or path.startswith(("/", "\\")) or path == "config.json":
            continue  # never write outside the bot folder or over the user's settings
        local = os.path.join(BASE_DIR, path)
        if os.path.exists(local) and file_hash(local) == digest:
            continue
        data = fetch(path.replace(" ", "%20"), ref=man.get("ref", "main"))
        if hashlib.sha256(data).hexdigest() != digest:
            raise RuntimeError(f"{path}: download didn't match the published file - try again")
        changed[path] = data
    for path, data in changed.items():  # all downloaded and verified first, then written
        local = os.path.join(BASE_DIR, path)
        os.makedirs(os.path.dirname(local), exist_ok=True)
        tmp = local + ".new"
        with open(tmp, "wb") as f:
            f.write(data)
        os.replace(tmp, local)
    return len(changed)


def list_versions(limit=30):
    """Published versions, newest first: [(version, date, message, commit)]. Every publish commits manifest.json,
    so its history is the version history."""
    url = f"https://api.github.com/repos/{UPDATE_REPO}/commits?path=manifest.json&per_page={limit}"
    with urllib.request.urlopen(urllib.request.Request(url, headers={"User-Agent": "LootFarmer"}), timeout=20) as r:
        commits = json.load(r)
    out = []
    for c in commits:
        try:
            man = json.loads(fetch("manifest.json", ref=c["sha"]))
        except Exception:
            continue
        out.append((int(man.get("version", 0)), c["commit"]["committer"]["date"][:10],
                    c["commit"]["message"].splitlines()[0][:60], c["sha"]))
    return out


def install_version(sha):
    """Put this folder's files back to a published snapshot (settings untouched). Returns files changed."""
    man = json.loads(fetch("manifest.json", ref=sha))
    man["ref"] = sha
    return apply_update(man)


def publish(message):
    """Bump APP_VERSION, write manifest.json and push the published files to GitHub (git must be signed in)."""
    src = open(__file__, encoding="utf-8").read()
    new_version = APP_VERSION + 1
    src = re.sub(r"^APP_VERSION = \d+", f"APP_VERSION = {new_version}", src, count=1, flags=re.M)
    with open(__file__, "w", encoding="utf-8") as f:
        f.write(src)
    man = {"version": new_version, "files": {p: file_hash(os.path.join(BASE_DIR, p)) for p in published_files()}}
    with open(os.path.join(BASE_DIR, "manifest.json"), "w", encoding="utf-8") as f:
        json.dump(man, f, indent=1)
    git = lambda *a: subprocess.run(["git", *a], cwd=BASE_DIR, check=True)
    if not os.path.isdir(os.path.join(BASE_DIR, ".git")):
        git("init", "-b", "main")
        git("remote", "add", "origin", f"https://github.com/{UPDATE_REPO}.git")
    git("add", "manifest.json", *published_files())
    git("commit", "-m", message or f"Update to version {new_version}")
    git("push", "-u", "origin", "main")
    print(f"Published version {new_version} ({len(man['files'])} files). Friends will see an Update button.")


def make_update():
    """LootFarmer_update.zip for a friend who's already set up: only the code + templates. No config.json (keeps
    their drop lines, settings and account setup; new settings get their defaults) and no bundled tools."""
    out = os.path.join(BASE_DIR, "LootFarmer_update.zip")
    with zipfile.ZipFile(out, "w", zipfile.ZIP_DEFLATED) as z:
        for f in ("bot.py", "setup.ps1", "Setup.bat", "README.txt"):
            z.write(os.path.join(BASE_DIR, f), f"LootFarmer/{f}")
        for f in sorted(os.listdir(TEMPLATE_DIR)):
            if f.endswith(".png") and not f.startswith("old_"):
                z.write(os.path.join(TEMPLATE_DIR, f), f"LootFarmer/templates/{f}")
        for f in published_files():
            if f.startswith("wiki/"):
                z.write(os.path.join(BASE_DIR, f), f"LootFarmer/{f}")
        z.writestr("LootFarmer/HOW TO UPDATE.txt", "\r\n".join([
            "1. Close Loot Farmer.",
            "2. Copy everything in this LootFarmer folder into your existing LootFarmer folder, and choose",
            "   'Replace the files in the destination'.",
            "   Your settings, drop lines and accounts (config.json) are NOT in this update, so they're kept.",
            "3. Open Loot Farmer again. New settings appear with sensible defaults - check the Settings tab.", ""]))
    print(f"Created {out}")


if __name__ == "__main__":
    if "--publish" in sys.argv:
        i = sys.argv.index("--publish")
        publish(" ".join(sys.argv[i + 1:]).strip())
    elif "--update" in sys.argv:
        make_update()
    elif "--package" in sys.argv:
        make_package()
    elif "--selftest" in sys.argv:
        selftest()
    else:
        try:  # crisp text on scaled (125-200%) Windows displays
            ctypes.windll.shcore.SetProcessDpiAwareness(1)
        except Exception:
            pass
        try:  # its own taskbar identity: the King icon, not Python's (the shortcuts carry the same ID)
            ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID(APP_ID)
        except Exception:
            pass
        if pc_blocked():
            log_file.warning(f"Blocked PC {sorted(pc_names())} - not starting.")
            tk.Tk().withdraw()
            messagebox.showerror("Loot Farmer", "Loot Farmer isn't available on this PC.")
            sys.exit()
        _instance = single_instance()
        if _instance is None:
            tk.Tk().withdraw()
            messagebox.showinfo("Loot Farmer", "Loot Farmer is already running (maybe from another folder).\n\n"
                                               "Two copies would fight over the same emulator - close the other one.")
            sys.exit()
        try:
            App().mainloop()
        except Exception:
            log_file.error("Loot Farmer crashed:\n" + traceback.format_exc())
            tk.Tk().withdraw()
            messagebox.showerror("Loot Farmer", "Loot Farmer hit an error and closed - details are in bot.log.\n\n"
                                                + traceback.format_exc(limit=2))
